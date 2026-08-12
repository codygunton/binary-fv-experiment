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
static uint64_t capture_write_pc;
static uint64_t input_address, context_address, terminal_pc;
static GByteArray *input_bytes;

struct registers { struct qemu_plugin_register *x[32]; GByteArray *buf; };

static int register_index(const char *name) {
  static const char *aliases[32] = {
    "zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2",
    "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5",
    "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7",
    "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"
  };
  if (!name) return -1;
  if (name[0] == 'x') {
    char *end = NULL;
    unsigned long index = strtoul(name + 1, &end, 10);
    if (end && *end == '\0' && index < 32) return (int)index;
  }
  for (int index = 0; index < 32; ++index)
    if (g_strcmp0(name, aliases[index]) == 0) return index;
  if (g_strcmp0(name, "fp") == 0) return 8;
  return -1;
}

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
  if (index == 0) { *value = 0; return true; }
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
    int index = register_index(descriptor->name);
    if (index >= 0) regs->x[index] = descriptor->handle;
  }
  if (descriptors) g_array_free(descriptors, TRUE);
  regs->buf = g_byte_array_new();
  if (!vcpu_registers) vcpu_registers = g_ptr_array_new_with_free_func(free_registers);
  g_ptr_array_set_size(vcpu_registers, MAX(vcpu_registers->len, vcpu + 1));
  g_ptr_array_index(vcpu_registers, vcpu) = regs;
  if (input_bytes) {
    GByteArray *length = g_byte_array_sized_new(8);
    uint64_t value = input_bytes->len;
    for (unsigned i = 0; i < 8; ++i) {
      uint8_t byte = (uint8_t)(value >> (8 * i));
      g_byte_array_append(length, &byte, 1);
    }
    if (!qemu_plugin_write_memory_vaddr(input_address, input_bytes) ||
        !qemu_plugin_write_memory_vaddr(context_address, length)) {
      fprintf(stderr, "failed to initialize bare-metal input memory\n");
      exit(2);
    }
    g_byte_array_free(length, TRUE);
  }
}

static struct registers *registers_for(unsigned vcpu) {
  return vcpu_registers && vcpu < vcpu_registers->len
    ? g_ptr_array_index(vcpu_registers, vcpu) : NULL;
}

static void execute(unsigned vcpu, void *data) {
  uint64_t pc = (uint64_t)(uintptr_t)data;
  fprintf(out, "E %" PRIu64 "\n", pc);
  struct registers *regs = registers_for(vcpu);
  if (pc == capture_write_pc) {
    uint64_t address = 0, length = 0;
    GByteArray *bytes = g_byte_array_new();
    if (!read_register(regs, 11, &address) || !read_register(regs, 12, &length) ||
        length > 64 * 1024 * 1024 ||
        (length != 0 && !qemu_plugin_read_memory_vaddr(address, bytes, (size_t)length))) {
      fprintf(out, "B %" PRIu64 " unreadable\n", pc);
    } else {
      fprintf(out, "B %" PRIu64 " %" PRIu64 " %" PRIu64 " ", pc, address, length);
      for (guint i = 0; i < bytes->len; ++i) fprintf(out, "%02x", bytes->data[i]);
      fputc('\n', out);
    }
    g_byte_array_free(bytes, TRUE);
  }
  if (!g_hash_table_contains(snapshot_pcs, &pc) && pc != terminal_pc) return;
  uint32_t available = 0;
  uint64_t values[32];
  for (unsigned i = 0; i < 32; ++i) {
    values[i] = 0;
    if (read_register(regs, i, &values[i])) available |= UINT32_C(1) << i;
  }
  fprintf(out, "R %" PRIu64 " %" PRIu32, pc, available);
  for (unsigned i = 0; i < 32; ++i) fprintf(out, " %" PRIu64, values[i]);
  fputc('\n', out);
  if (pc == terminal_pc) {
    GByteArray *context = g_byte_array_new();
    if (!qemu_plugin_read_memory_vaddr(context_address, context, 32)) exit(3);
    uint64_t address = 0, length = 0;
    for (unsigned i = 0; i < 8; ++i) {
      address |= (uint64_t)context->data[8 + i] << (8 * i);
      length |= (uint64_t)context->data[16 + i] << (8 * i);
    }
    GByteArray *bytes = g_byte_array_new();
    if (length > 64 * 1024 * 1024 ||
        (length && !qemu_plugin_read_memory_vaddr(address, bytes, (size_t)length))) exit(4);
    fprintf(out, "B %" PRIu64 " %" PRIu64 " %" PRIu64 " ", pc, address, length);
    for (guint i = 0; i < bytes->len; ++i) fprintf(out, "%02x", bytes->data[i]);
    fputc('\n', out);
    fflush(out);
    g_byte_array_free(bytes, TRUE);
    g_byte_array_free(context, TRUE);
    exit(0);
  }
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
  if (input_bytes) g_byte_array_free(input_bytes, TRUE);
}

QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id, const qemu_info_t *info,
                                            int argc, char **argv) {
  (void)info;
  const char *path = NULL;
  const char *input_path = NULL;
  for (int i = 0; i < argc; ++i) {
    if (g_str_has_prefix(argv[i], "out=")) path = argv[i] + 4;
    if (g_str_has_prefix(argv[i], "capture_write="))
      capture_write_pc = g_ascii_strtoull(argv[i] + 14, NULL, 0);
    if (g_str_has_prefix(argv[i], "input=")) input_path = argv[i] + 6;
    if (g_str_has_prefix(argv[i], "input_address="))
      input_address = g_ascii_strtoull(argv[i] + 14, NULL, 0);
    if (g_str_has_prefix(argv[i], "context_address="))
      context_address = g_ascii_strtoull(argv[i] + 16, NULL, 0);
    if (g_str_has_prefix(argv[i], "terminal="))
      terminal_pc = g_ascii_strtoull(argv[i] + 9, NULL, 0);
  }
  out = path ? fopen(path, "w") : stderr;
  if (!out) return -1;
  if (input_path) {
    gchar *contents = NULL;
    gsize length = 0;
    if (!g_file_get_contents(input_path, &contents, &length, NULL)) return -1;
    input_bytes = g_byte_array_new_take((guint8 *)contents, length);
  }
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
