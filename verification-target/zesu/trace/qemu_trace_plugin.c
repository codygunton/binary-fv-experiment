/*
 * Pinned QEMU user-mode TCG plugin for production-binary evidence capture.
 *
 * Records, for the UNCHANGED production RV64 `zesu-ssz` ELF as it runs under `qemu-riscv64`, a
 * deterministic execution trace:
 *
 *   - every executed instruction PC (`E <pc>`), from which executed CFG edges are reconstructed; and
 *   - every load  `(pc, address, width, value)`      (`L <pc> <addr> <width> <value>`); and
 *   - every store `(pc, address, width, value, sp)`  (`S <pc> <addr> <width> <value> <sp>`).
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

/* Handle to the stack-pointer register, resolved once per vCPU at init. */
static struct qemu_plugin_register *sp_handle;
static GByteArray *sp_buf;           /* reused scratch for register reads */

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

/* Resolve the sp register handle in vCPU context (required by the plugin API). */
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
        if (d->name && g_strcmp0(d->name, "sp") == 0) {
            sp_handle = d->handle;
            break;
        }
    }
    g_array_free(regs, TRUE);
    if (!sp_buf) {
        sp_buf = g_byte_array_new();
    }
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
        void *pc = (void *)(uintptr_t)qemu_plugin_insn_vaddr(insn);
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
    (void)info;
    for (int i = 0; i < argc; i++) {
        if (g_str_has_prefix(argv[i], "out=")) {
            path = argv[i] + 4;
        } else if (g_str_has_prefix(argv[i], "lo=")) {
            pc_lo = g_ascii_strtoull(argv[i] + 3, NULL, 0);
        } else if (g_str_has_prefix(argv[i], "hi=")) {
            pc_hi = g_ascii_strtoull(argv[i] + 3, NULL, 0);
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
