/*
 * Row C (PR: ssz-contract-validation-binary) — pinned QEMU user-mode TCG plugin.
 *
 * Records, for the UNCHANGED production RV64 `zesu-ssz` ELF as it runs under `qemu-riscv64`, a
 * deterministic execution trace:
 *
 *   - every executed instruction PC (`E <pc>`), from which executed CFG edges are reconstructed; and
 *   - every load/store `(pc, address, width, value)` (`L`/`S <pc> <addr> <width> <value>`).
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

static inline int in_window(uint64_t pc)
{
    return pc >= pc_lo && pc < pc_hi;
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
    char kind = qemu_plugin_mem_is_store(info) ? 'S' : 'L';
    uint64_t value = mem_value_u64(qemu_plugin_mem_get_value(info));
    fprintf(trace_out, "%c %" PRIu64 " %" PRIu64 " %u %" PRIu64 "\n",
            kind, pc, vaddr, width, value);
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
        qemu_plugin_register_vcpu_mem_cb(insn, mem_access,
                                         QEMU_PLUGIN_CB_NO_REGS,
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
    qemu_plugin_register_vcpu_tb_trans_cb(id, tb_translate);
    qemu_plugin_register_atexit_cb(id, plugin_exit, NULL);
    return 0;
}
