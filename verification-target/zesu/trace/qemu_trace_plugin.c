/*
 * Pinned QEMU user-mode TCG plugin for production-binary evidence capture.
 *
 * Records, for the UNCHANGED production RV64 `zesu-ssz` ELF as it runs under `qemu-riscv64`, a
 * deterministic execution trace:
 *
 *   - every executed instruction PC (`E <pc>`), from which executed CFG edges are reconstructed; and
 *   - every load  `(pc, address, width, value)`      (`L <pc> <addr> <width> <value>`); and
 *   - every store `(pc, address, width, value, sp)`  (`S <pc> <addr> <width> <value> <sp>`); and
 *   - the `x2`, `x19`, and `x24` register snapshot at the reviewed fi:16 parent
 *     producer PC (`R <pc> <x2> <x19> <x24>`).
 *
 * The stack pointer is read (via the plugin register API) at the moment of every store so that write
 * classification (stack vs heap vs input vs code vs …) is exact and self-contained: the scaled
 * per-occurrence checker needs no separate GDB register capture. Reads use `QEMU_PLUGIN_CB_R_REGS`.
 *
 * The plugin only OBSERVES: it never modifies the guest, and the ELF is neither rebuilt, relinked,
 * patched, nor instrumented. Output is a plain append-only text log (one record per line), so a run
 * over a fixed input is byte-deterministic. An optional `[lo,hi)` PC window keeps the vertical-slice
 * trace small; with no window the whole run is captured.
 *
 * Args: out=<path> lo=<pc> hi=<pc>   (lo/hi optional; default: whole address space).
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

/* The fi:16 branch target whose producer values feed r7's stack-word loads. */
static uint64_t snapshot_pc = UINT64_C(0x10740);

/* Register handles are vCPU-local: QEMU resolves them in each vCPU init callback. */
struct register_handles {
    struct qemu_plugin_register *sp;
    struct qemu_plugin_register *x19;
    struct qemu_plugin_register *x24;
    GByteArray *buf;                 /* reused scratch for register reads */
};
static GPtrArray *vcpu_registers;

static inline int in_window(uint64_t pc)
{
    return pc >= pc_lo && pc < pc_hi;
}

static struct register_handles *registers_for_vcpu(unsigned int vcpu_index)
{
    if (!vcpu_registers || vcpu_index >= vcpu_registers->len) {
        return NULL;
    }
    return g_ptr_array_index(vcpu_registers, vcpu_index);
}

/* Read one RV64 integer register in callback context (0 if unavailable). */
static bool read_register(struct register_handles *registers,
                          struct qemu_plugin_register *handle, uint64_t *out)
{
    if (!registers || !handle || !registers->buf) {
        return false;
    }
    g_byte_array_set_size(registers->buf, 0);
    if (!qemu_plugin_read_register(handle, registers->buf) || registers->buf->len == 0) {
        return false;
    }
    *out = 0;
    /* target byte order is little-endian for RV64 */
    for (guint i = 0; i < registers->buf->len && i < 8; i++) {
        *out |= (uint64_t)registers->buf->data[i] << (8 * i);
    }
    return true;
}

static void free_register_handles(gpointer data)
{
    struct register_handles *handles = data;
    if (handles) {
        if (handles->buf) g_byte_array_free(handles->buf, TRUE);
        g_free(handles);
    }
}

static bool named(const char *name, const char *canonical, const char *abi)
{
    return name && (g_strcmp0(name, canonical) == 0 || g_strcmp0(name, abi) == 0);
}

/* Resolve RV64 register handles in vCPU context (required by the plugin API). */
static void vcpu_init(qemu_plugin_id_t id, unsigned int vcpu_index)
{
    (void)id;
    struct register_handles *handles = g_new0(struct register_handles, 1);
    GArray *regs = qemu_plugin_get_registers();
    if (!regs) {
        g_free(handles);
        return;
    }
    for (guint i = 0; i < regs->len; i++) {
        qemu_plugin_reg_descriptor *d =
            &g_array_index(regs, qemu_plugin_reg_descriptor, i);
        if (named(d->name, "x2", "sp")) handles->sp = d->handle;
        if (named(d->name, "x19", "s3")) handles->x19 = d->handle;
        if (named(d->name, "x24", "s8")) handles->x24 = d->handle;
    }
    g_array_free(regs, TRUE);
    handles->buf = g_byte_array_new();
    if (!vcpu_registers) {
        vcpu_registers = g_ptr_array_new_with_free_func(free_register_handles);
    }
    g_ptr_array_set_size(vcpu_registers, MAX(vcpu_registers->len, vcpu_index + 1));
    g_ptr_array_index(vcpu_registers, vcpu_index) = handles;
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
    if (in_window(pc)) {
        fprintf(trace_out, "E %" PRIu64 "\n", pc);
    }
    if (pc == snapshot_pc) {
        struct register_handles *registers = registers_for_vcpu(vcpu_index);
        uint64_t x2, x19, x24;
        if (read_register(registers, registers ? registers->sp : NULL, &x2)
            && read_register(registers, registers ? registers->x19 : NULL, &x19)
            && read_register(registers, registers ? registers->x24 : NULL, &x24)) {
            fprintf(trace_out, "R %" PRIu64 " %" PRIu64 " %" PRIu64 " %" PRIu64 "\n",
                    pc, x2, x19, x24);
        }
    }
}

static void mem_access(unsigned int vcpu_index, qemu_plugin_meminfo_t info,
                       uint64_t vaddr, void *userdata)
{
    uint64_t pc = (uint64_t)(uintptr_t)userdata;
    if (!in_window(pc)) {
        return;
    }
    unsigned int width = 1u << qemu_plugin_mem_size_shift(info);
    int is_store = qemu_plugin_mem_is_store(info);
    uint64_t value = mem_value_u64(qemu_plugin_mem_get_value(info));
    if (is_store) {
        struct register_handles *registers = registers_for_vcpu(vcpu_index);
        uint64_t sp = 0;
        /* Stores carry the stack pointer so writes can be classified without GDB. */
        (void)read_register(registers, registers ? registers->sp : NULL, &sp);
        fprintf(trace_out, "S %" PRIu64 " %" PRIu64 " %u %" PRIu64 " %" PRIu64 "\n",
                pc, vaddr, width, value, sp);
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
        void *pc = (void *)(uintptr_t)qemu_plugin_insn_vaddr(insn);
        qemu_plugin_register_vcpu_insn_exec_cb(insn, insn_exec,
                                               QEMU_PLUGIN_CB_R_REGS, pc);
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
    if (vcpu_registers) {
        g_ptr_array_free(vcpu_registers, TRUE);
        vcpu_registers = NULL;
    }
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id,
                                           const qemu_info_t *info,
                                           int argc, char **argv)
{
    const char *path = NULL;
    (void)info;
    for (int i = 0; i < argc; i++) {
        if (g_str_has_prefix(argv[i], "out=")) {
            path = argv[i] + 4;
        } else if (g_str_has_prefix(argv[i], "lo=")) {
            pc_lo = g_ascii_strtoull(argv[i] + 3, NULL, 0);
        } else if (g_str_has_prefix(argv[i], "hi=")) {
            pc_hi = g_ascii_strtoull(argv[i] + 3, NULL, 0);
        } else if (g_str_has_prefix(argv[i], "snapshot-pc=")) {
            snapshot_pc = g_ascii_strtoull(argv[i] + 12, NULL, 0);
        }
    }
    trace_out = path ? fopen(path, "w") : stderr;
    if (!trace_out) {
        return -1;
    }
    qemu_plugin_register_vcpu_init_cb(id, vcpu_init);
    qemu_plugin_register_vcpu_tb_trans_cb(id, tb_translate);
    qemu_plugin_register_atexit_cb(id, plugin_exit, NULL);
    return 0;
}
