/*
 * Row C (PR: ssz-contract-validation-binary) — pinned QEMU user-mode TCG plugin.
 *
 * Records, for the UNCHANGED production RV64 `zesu-ssz` ELF as it runs under `qemu-riscv64`, a
 * deterministic execution trace:
 *
 *   - every executed instruction PC (`E <pc>`), from which executed CFG edges are reconstructed; and
 *   - every load  `(pc, address, width, value)`      (`L <pc> <addr> <width> <value>`); and
 *   - every store `(pc, address, width, value, sp)`  (`S <pc> <addr> <width> <value> <sp>`); and
 *   - the whole integer register file `x1..x31` at each BOUNDARY pc  (`R <pc> <x1> … <x31>`).
 *
 * The stack pointer is read (via the plugin register API) at the moment of every store so that write
 * classification (stack vs heap vs input vs code vs …) is exact and self-contained: the scaled
 * per-function-instance checker needs no separate GDB register capture. Reads use `QEMU_PLUGIN_CB_R_REGS`.
 *
 * Boundary PCs (`bpc=<file>`, one decimal PC per line — the function instances' declared Row A entry and exit
 * PCs) additionally get a full `x1..x31` snapshot taken BEFORE the instruction at that PC executes, so
 * the checker can evaluate each function instance's declared DWARF entry bindings (`reg` / `breg` / `fbreg` /
 * `bregValue` / `addr` / `const`) and its exit register state against the real machine. `bcap=<n>`
 * bounds the snapshots per PC (default 256) so a hot boundary cannot blow the trace up; the cap keeps
 * the FIRST n hits, which is deterministic.
 *
 * The plugin only OBSERVES: it never modifies the guest, and the ELF is neither rebuilt, relinked,
 * patched, nor instrumented. Output is a plain append-only text log (one record per line), so a run
 * over a fixed input is byte-deterministic. An optional `[lo,hi)` PC window keeps the vertical-slice
 * trace small; with no window the whole run is captured.
 *
 * Args: out=<path> lo=<pc> hi=<pc> bpc=<path> bcap=<n>   (all but out= optional).
 * (`file=` is reserved by QEMU's own -plugin parsing for the plugin path, so the output uses `out=`.)
 * This is diagnostic-only evidence and is never part of the theorem dependency graph.
 */
#include <glib.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

#include <qemu-plugin.h>

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;

static FILE *trace_out;
static uint64_t pc_lo;               /* inclusive  */
static uint64_t pc_hi = UINT64_MAX;  /* exclusive  */

/* Handle to the stack-pointer register, resolved once per vCPU at init. */
static struct qemu_plugin_register *sp_handle;
static GByteArray *sp_buf;           /* reused scratch for register reads */

/*
 * Boundary-PC register capture. `x_handle[i]` is the handle for RISC-V `x{i}` (DWARF register number
 * i), resolved by ABI name at vCPU init; `boundary_pcs` maps a boundary PC to its remaining snapshot
 * budget.  x0 is hardwired zero and is never read.
 */
#define NXREG 32
static struct qemu_plugin_register *x_handle[NXREG];
static GHashTable *boundary_pcs;     /* uint64 pc -> remaining budget (as pointer-sized int) */
static uint64_t boundary_cap = 256;

/* DWARF x-register number -> RISC-V ABI name, as exposed by QEMU's register list. */
static const char *const XREG_NAMES[NXREG] = {
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
    "s0",   "s1", "a0", "a1", "a2", "a3", "a4", "a5",
    "a6",   "a7", "s2", "s3", "s4", "s5", "s6", "s7",
    "s8",   "s9", "s10", "s11", "t3", "t4", "t5", "t6",
};

static inline int in_window(uint64_t pc)
{
    return pc >= pc_lo && pc < pc_hi;
}

/* Current stack pointer, read from the vCPU register file (0 if unavailable). */
static uint64_t read_sp(void)
{
    if (!sp_handle || !sp_buf) {
        return 0;
    }
    g_byte_array_set_size(sp_buf, 0);
    if (!qemu_plugin_read_register(sp_handle, sp_buf) || sp_buf->len == 0) {
        return 0;
    }
    uint64_t sp = 0;
    /* target byte order is little-endian for RV64 */
    for (guint i = 0; i < sp_buf->len && i < 8; i++) {
        sp |= (uint64_t)sp_buf->data[i] << (8 * i);
    }
    return sp;
}

/* Read one integer register as a 64-bit little-endian value (0 if unavailable). */
static uint64_t read_xreg(int i)
{
    if (i <= 0 || i >= NXREG || !x_handle[i] || !sp_buf) {
        return 0;
    }
    g_byte_array_set_size(sp_buf, 0);
    if (!qemu_plugin_read_register(x_handle[i], sp_buf) || sp_buf->len == 0) {
        return 0;
    }
    uint64_t v = 0;
    for (guint j = 0; j < sp_buf->len && j < 8; j++) {
        v |= (uint64_t)sp_buf->data[j] << (8 * j);
    }
    return v;
}

/* Resolve the sp and x1..x31 register handles in vCPU context (required by the plugin API). */
static void vcpu_init(qemu_plugin_id_t id, unsigned int vcpu_index)
{
    (void)id;
    (void)vcpu_index;
    if (sp_handle) {
        return;
    }
    GArray *regs = qemu_plugin_get_registers();
    if (!regs) {
        return;
    }
    for (guint i = 0; i < regs->len; i++) {
        qemu_plugin_reg_descriptor *d =
            &g_array_index(regs, qemu_plugin_reg_descriptor, i);
        if (!d->name) {
            continue;
        }
        if (g_strcmp0(d->name, "sp") == 0) {
            sp_handle = d->handle;
        }
        for (int x = 1; x < NXREG; x++) {
            /* QEMU renders x8 as "s0" or "fp" depending on version; accept both. */
            if (g_strcmp0(d->name, XREG_NAMES[x]) == 0 ||
                (x == 8 && g_strcmp0(d->name, "fp") == 0)) {
                x_handle[x] = d->handle;
            }
        }
    }
    g_array_free(regs, TRUE);
    if (!sp_buf) {
        sp_buf = g_byte_array_new();
    }
}

/*
 * Snapshot x1..x31 at a boundary PC, BEFORE that instruction executes. Registered only on boundary
 * instructions, and budgeted per PC so a hot boundary cannot dominate the trace.
 */
static void boundary_regs(unsigned int vcpu_index, void *userdata)
{
    uint64_t pc = (uint64_t)(uintptr_t)userdata;
    (void)vcpu_index;
    gpointer key = (gpointer)(uintptr_t)pc;
    gpointer left = g_hash_table_lookup(boundary_pcs, key);
    uint64_t budget = (uint64_t)(uintptr_t)left;
    if (budget == 0) {
        return;
    }
    g_hash_table_insert(boundary_pcs, key, (gpointer)(uintptr_t)(budget - 1));
    fprintf(trace_out, "R %" PRIu64, pc);
    for (int i = 1; i < NXREG; i++) {
        fprintf(trace_out, " %" PRIu64, read_xreg(i));
    }
    fputc('\n', trace_out);
}

/* Load the boundary PC list (one decimal PC per line); absent file = no register capture. */
static void load_boundary_pcs(const char *path)
{
    boundary_pcs = g_hash_table_new(g_direct_hash, g_direct_equal);
    FILE *fh = fopen(path, "r");
    if (!fh) {
        return;
    }
    char line[64];
    while (fgets(line, sizeof(line), fh)) {
        char *end = NULL;
        uint64_t pc = g_ascii_strtoull(line, &end, 10);
        if (end != line) {
            g_hash_table_insert(boundary_pcs, (gpointer)(uintptr_t)pc,
                                (gpointer)(uintptr_t)boundary_cap);
        }
    }
    fclose(fh);
}

/* Extract the concrete integer value of a load/store from the plugin's tagged union. */
static uint64_t mem_value_u64(qemu_plugin_mem_value v)
{
    switch (v.type) {
    case QEMU_PLUGIN_MEM_VALUE_U8:
        return v.data.u8;
    case QEMU_PLUGIN_MEM_VALUE_U16:
        return v.data.u16;
    case QEMU_PLUGIN_MEM_VALUE_U32:
        return v.data.u32;
    case QEMU_PLUGIN_MEM_VALUE_U64:
        return v.data.u64;
    default:
        return 0;
    }
}

static void insn_exec(unsigned int vcpu_index, void *userdata)
{
    uint64_t pc = (uint64_t)(uintptr_t)userdata;
    (void)vcpu_index;
    if (in_window(pc)) {
        fprintf(trace_out, "E %" PRIu64 "\n", pc);
    }
}

static void mem_access(unsigned int vcpu_index, qemu_plugin_meminfo_t info,
                       uint64_t vaddr, void *userdata)
{
    uint64_t pc = (uint64_t)(uintptr_t)userdata;
    (void)vcpu_index;
    if (!in_window(pc)) {
        return;
    }
    unsigned int width = 1u << qemu_plugin_mem_size_shift(info);
    int is_store = qemu_plugin_mem_is_store(info);
    uint64_t value = mem_value_u64(qemu_plugin_mem_get_value(info));
    if (is_store) {
        /* Stores carry the stack pointer so writes can be classified without GDB. */
        fprintf(trace_out, "S %" PRIu64 " %" PRIu64 " %u %" PRIu64 " %" PRIu64 "\n",
                pc, vaddr, width, value, read_sp());
    } else {
        fprintf(trace_out, "L %" PRIu64 " %" PRIu64 " %u %" PRIu64 "\n",
                pc, vaddr, width, value);
    }
}

static void tb_translate(qemu_plugin_id_t id, struct qemu_plugin_tb *tb)
{
    size_t n = qemu_plugin_tb_n_insns(tb);
    (void)id;
    for (size_t i = 0; i < n; i++) {
        struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);
        uint64_t vaddr = qemu_plugin_insn_vaddr(insn);
        void *pc = (void *)(uintptr_t)vaddr;
        /* Boundary snapshot first, so the register file is the state ON ENTRY to this pc. */
        if (boundary_pcs && in_window(vaddr) &&
            g_hash_table_contains(boundary_pcs, (gpointer)(uintptr_t)vaddr)) {
            qemu_plugin_register_vcpu_insn_exec_cb(insn, boundary_regs,
                                                   QEMU_PLUGIN_CB_R_REGS, pc);
        }
        qemu_plugin_register_vcpu_insn_exec_cb(insn, insn_exec,
                                               QEMU_PLUGIN_CB_NO_REGS, pc);
        /* CB_R_REGS: the store branch reads sp via qemu_plugin_read_register. */
        qemu_plugin_register_vcpu_mem_cb(insn, mem_access,
                                         QEMU_PLUGIN_CB_R_REGS,
                                         QEMU_PLUGIN_MEM_RW, pc);
    }
}

static void plugin_exit(qemu_plugin_id_t id, void *userdata)
{
    (void)id;
    (void)userdata;
    if (trace_out) {
        fflush(trace_out);
        fclose(trace_out);
        trace_out = NULL;
    }
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id,
                                           const qemu_info_t *info,
                                           int argc, char **argv)
{
    const char *path = NULL;
    const char *bpath = NULL;
    (void)info;
    for (int i = 0; i < argc; i++) {
        if (g_str_has_prefix(argv[i], "out=")) {
            path = argv[i] + 4;
        } else if (g_str_has_prefix(argv[i], "lo=")) {
            pc_lo = g_ascii_strtoull(argv[i] + 3, NULL, 0);
        } else if (g_str_has_prefix(argv[i], "hi=")) {
            pc_hi = g_ascii_strtoull(argv[i] + 3, NULL, 0);
        } else if (g_str_has_prefix(argv[i], "bcap=")) {
            boundary_cap = g_ascii_strtoull(argv[i] + 5, NULL, 0);
        } else if (g_str_has_prefix(argv[i], "bpc=")) {
            bpath = argv[i] + 4;
        }
    }
    trace_out = path ? fopen(path, "w") : stderr;
    if (!trace_out) {
        return -1;
    }
    if (bpath) {
        load_boundary_pcs(bpath);   /* after bcap= is parsed: the budget uses it */
    }
    qemu_plugin_register_vcpu_init_cb(id, vcpu_init);
    qemu_plugin_register_vcpu_tb_trans_cb(id, tb_translate);
    qemu_plugin_register_atexit_cb(id, plugin_exit, NULL);
    return 0;
}
