/* Observe-only RV64 trace plugin. Snapshot PCs are supplied as snapshots=pc,pc,... . */
#include <glib.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <qemu-plugin.h>

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;
static FILE *out;
static GHashTable *snapshot_pcs;
static GPtrArray *vcpu_registers;

struct registers { struct qemu_plugin_register *x[32]; GByteArray *buf; };

static uint64_t memory_value(qemu_plugin_mem_value value) {
  switch (value.type) {
  case QEMU_PLUGIN_MEM_VALUE_U8: return value.data.u8;
  case QEMU_PLUGIN_MEM_VALUE_U16: return value.data.u16;
  case QEMU_PLUGIN_MEM_VALUE_U32: return value.data.u32;
  case QEMU_PLUGIN_MEM_VALUE_U64: return value.data.u64;
  default: return 0;
  }
}

static bool read_register(struct registers *regs, unsigned index, uint64_t *value) {
  if (!regs || !regs->x[index]) return false;
  g_byte_array_set_size(regs->buf, 0);
  if (!qemu_plugin_read_register(regs->x[index], regs->buf)) return false;
  *value = 0;
  for (guint i = 0; i < regs->buf->len && i < 8; ++i)
    *value |= (uint64_t)regs->buf->data[i] << (8 * i);
  return true;
}

static void free_registers(gpointer data) {
  struct registers *regs = data;
  if (!regs) return;
  if (regs->buf) g_byte_array_free(regs->buf, TRUE);
  g_free(regs);
}

static void vcpu_init(qemu_plugin_id_t id, unsigned vcpu) {
  (void)id;
  struct registers *regs = g_new0(struct registers, 1);
  GArray *descriptors = qemu_plugin_get_registers();
  for (guint i = 0; descriptors && i < descriptors->len; ++i) {
    qemu_plugin_reg_descriptor *descriptor =
      &g_array_index(descriptors, qemu_plugin_reg_descriptor, i);
    if (descriptor->name && descriptor->name[0] == 'x') {
      char *end = NULL;
      unsigned long index = strtoul(descriptor->name + 1, &end, 10);
      if (end && *end == '\0' && index < 32) regs->x[index] = descriptor->handle;
    }
  }
  if (descriptors) g_array_free(descriptors, TRUE);
  regs->buf = g_byte_array_new();
  if (!vcpu_registers) vcpu_registers = g_ptr_array_new_with_free_func(free_registers);
  g_ptr_array_set_size(vcpu_registers, MAX(vcpu_registers->len, vcpu + 1));
  g_ptr_array_index(vcpu_registers, vcpu) = regs;
}

static struct registers *registers_for(unsigned vcpu) {
  return vcpu_registers && vcpu < vcpu_registers->len
    ? g_ptr_array_index(vcpu_registers, vcpu) : NULL;
}

static void execute(unsigned vcpu, void *data) {
  uint64_t pc = (uint64_t)(uintptr_t)data;
  fprintf(out, "E %" PRIu64 "\n", pc);
  if (!g_hash_table_contains(snapshot_pcs, &pc)) return;
  struct registers *regs = registers_for(vcpu);
  fprintf(out, "R %" PRIu64, pc);
  for (unsigned i = 0; i < 32; ++i) {
    uint64_t value = 0;
    if (!read_register(regs, i, &value)) value = UINT64_MAX;
    fprintf(out, " %" PRIu64, value);
  }
  fputc('\n', out);
}

static void memory(unsigned vcpu, qemu_plugin_meminfo_t info, uint64_t address, void *data) {
  (void)vcpu;
  uint64_t pc = (uint64_t)(uintptr_t)data;
  unsigned width = 1u << qemu_plugin_mem_size_shift(info);
  fprintf(out, "%c %" PRIu64 " %" PRIu64 " %u %" PRIu64 "\n",
          qemu_plugin_mem_is_store(info) ? 'S' : 'L', pc, address, width,
          memory_value(qemu_plugin_mem_get_value(info)));
}

static void translate(qemu_plugin_id_t id, struct qemu_plugin_tb *tb) {
  (void)id;
  for (size_t i = 0; i < qemu_plugin_tb_n_insns(tb); ++i) {
    struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);
    void *pc = (void *)(uintptr_t)qemu_plugin_insn_vaddr(insn);
    qemu_plugin_register_vcpu_insn_exec_cb(insn, execute, QEMU_PLUGIN_CB_R_REGS, pc);
    qemu_plugin_register_vcpu_mem_cb(insn, memory, QEMU_PLUGIN_CB_R_REGS,
                                     QEMU_PLUGIN_MEM_RW, pc);
  }
}

static void finish(qemu_plugin_id_t id, void *data) {
  (void)id; (void)data;
  if (out && out != stderr) fclose(out);
  if (snapshot_pcs) g_hash_table_destroy(snapshot_pcs);
  if (vcpu_registers) g_ptr_array_free(vcpu_registers, TRUE);
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id, const qemu_info_t *info,
                                            int argc, char **argv) {
  (void)info;
  const char *path = NULL;
  for (int i = 0; i < argc; ++i) {
    if (g_str_has_prefix(argv[i], "out=")) path = argv[i] + 4;
  }
  out = path ? fopen(path, "w") : stderr;
  if (!out) return -1;
  snapshot_pcs = g_hash_table_new_full(g_int64_hash, g_int64_equal, g_free, NULL);
  for (int i = 0; i < argc; ++i) {
    const char *value = NULL;
    if (g_str_has_prefix(argv[i], "snapshot=")) value = argv[i] + 9;
    if (value) {
      uint64_t *pc = g_new(uint64_t, 1);
      *pc = g_ascii_strtoull(value, NULL, 0);
      g_hash_table_add(snapshot_pcs, pc);
    }
  }
  qemu_plugin_register_vcpu_init_cb(id, vcpu_init);
  qemu_plugin_register_vcpu_tb_trans_cb(id, translate);
  qemu_plugin_register_atexit_cb(id, finish, NULL);
  return 0;
}
