#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <gmp.h>
#include "CodeGen.h"
#include "Netlist.h"

// Constructor
CodeGen::CodeGen() {
  outFile = stdout;
}

// Destructor
CodeGen::~CodeGen() {
  if (outFile != NULL && outFile != stdout) fclose(stdout);
}

// Exit with an error message
void CodeGen::genError(const char* fmt, ...)
{
  va_list args;
  va_start(args, fmt);
  fprintf(stderr, "Code gen error:\n");
  vfprintf(stderr, fmt, args);
  fprintf(stderr, "\n");
  va_end(args);
  exit(EXIT_FAILURE);
}

// Change destination file
void CodeGen::setOutputFile(char* filename) {
  outFile = fopen(filename, "wt");
  if (outFile == NULL)
    genError("Error opening file '%s'\n", filename);
}

// Generate code to declare wire
void CodeGen::declareWire(NetWire wire, unsigned width)
{
  if (isStdInt(width))
    emit("uint%d_t w%d_%d;\n", width, wire.id, wire.pin);
  else if (width <= 64)
    emit("uint64_t w%d_%d;\n", wire.id, wire.pin);
  else {
    unsigned numChunks = (width+31)/32;
    emit("uint32_t w%d_%d[%d];\n", wire.id, wire.pin, numChunks);
  }
}

// Generate code to initialise wire
void CodeGen::initWire(NetWire wire, unsigned width, char* init)
{
  if (width <= 64) {
    emit("w%d_%d = %s;\n", wire.id, wire.pin, init);
  }
  else {
    // Use a GNU big num to interpret the initial value
    mpz_t num;
    mpz_init_set_str(num, init, 10);
    // Initialise each 32-bit chunk
    unsigned numChunks = (width+31)/32;
    for (unsigned i = 0; i < numChunks; i++) {
      unsigned long bottom = mpz_get_ui(num) & 0xffffffff; // Bottom 32 bits
      emit("w%d_%d[%d] = %lu;\n", wire.id, wire.pin, i, bottom);
      mpz_fdiv_q_2exp(num, num, 32); // Shift right by 32
    }
    mpz_clear(num);
  }
}

inline bool isUnaryOp(char* op)
{
  return strcmp(op, "~") == 0;
}

// Generate code for unnary operator
void CodeGen::unaryOp(NetId r, char* op, NetWire a, unsigned width)
{
  if (isStdInt(width))
    emit("w%d_0 = %s(w%d_%d);\n", r, op, a.id, a.pin);
  else if (width <= 64)
    emit("w%d_0 = %s(w%d_%d) & ((1ul << %d)-1ul);\n",
      r, op, a.id, a.pin, width);
  else {
    const char* prim;
    if (strcmp(op, "~") == 0)
      prim = "notBU";
    else
      genError("Unknown primitive '%s'\n", op);

    emit("%s(w%d_%d, w%d_0, %d);\n",
        prim, a.id, a.pin, r, width);
  }
}

// Generate code for binary operator
void CodeGen::binOp(NetId r, NetWire a, char* op, NetWire b, unsigned width)
{
  if (isStdInt(width))
    emit("w%d_0 = w%d_%d %s w%d_%d;\n",
      r, a.id, a.pin, op, b.id, b.pin);
  else if (width <= 64)
    emit("w%d_0 = (w%d_%d %s w%d_%d) & ((1ul << %d)-1ul);\n",
      r, a.id, a.pin, op, b.id, b.pin, width);
  else {
    const char* prim;
    if (strcmp(op, "+") == 0)
      prim = "addBU";
    else if (strcmp(op, "-") == 0)
      prim = "subBU";
    else if (strcmp(op, "*") == 0)
      prim = "mulBU";
    else if (strcmp(op, "%") == 0)
      prim = "modBU";
    else if (strcmp(op, "/") == 0)
      prim = "divBU";
    else if (strcmp(op, "&") == 0)
      prim = "andBU";
    else if (strcmp(op, "|") == 0)
      prim = "orBU";
    else if (strcmp(op, "^") == 0)
      prim = "xorBU";
    else if (strcmp(op, "<<") == 0)
      prim = "leftBU";
    else if (strcmp(op, ">>") == 0)
      prim = "rightBU";
    else
      genError("Unknown primitive '%s'\n", op);

    emit("%s(w%d_%d, w%d_%d, w%d_0, %d);\n",
        prim, a.id, a.pin, b.id, b.pin, r, width);
  }
}

inline bool isBinOp(char* op)
{
  return strcmp(op, "+") == 0
      || strcmp(op, "-") == 0
      || strcmp(op, "*") == 0
      || strcmp(op, "%") == 0
      || strcmp(op, "/") == 0
      || strcmp(op, "&") == 0
      || strcmp(op, "|") == 0
      || strcmp(op, "^") == 0
      || strcmp(op, "<<") == 0
      || strcmp(op, ">>") == 0;
}

// Generate code for comparison operator
void CodeGen::cmpOp(NetId r, NetWire a, char* op, NetWire b, unsigned width)
{
  if (width <= 64)
    emit("w%d_0 = w%d_%d %s w%d_%d;\n", r, a.id, a.pin, op, b.id, b.pin);
  else {
    const char* prim;
    if (strcmp(op, "<") == 0)
      prim = "ltBU";
    else if (strcmp(op, "<=") == 0)
      prim = "leBU";
    else if (strcmp(op, ">") == 0)
      prim = "gtBU";
    else if (strcmp(op, ">=") == 0)
      prim = "geBU";
    else if (strcmp(op, "==") == 0)
      prim = "eqBU";
    else if (strcmp(op, "!=") == 0)
      prim = "neqBU";
    else
      genError("Unknown primitive '%s'\n", op);

    emit("w%d_0 = %s(w%d_%d, w%d_%d, %d);\n",
      r, prim, a.id, a.pin, b.id, b.pin, width);
  }
}

inline bool isCmpOp(char* op)
{
  return strcmp(op, "<")  == 0
      || strcmp(op, "<=") == 0
      || strcmp(op, ">")  == 0
      || strcmp(op, ">=") == 0
      || strcmp(op, "==") == 0
      || strcmp(op, "!=") == 0;
}

// Generate code for replication operator
void CodeGen::replicate(NetId r, NetWire a, unsigned width)
{
  if (width <= 32) {
    uint32_t ones = (1ul << width)-1;
    emit("w%d_0 = w%d_%d ? 0x%x : 0;\n", r, a.id, a.pin, ones);
  }
  else if (width <= 64) {
    uint64_t ones = (1ul << width)-1;
    emit("w%d_0 = w%d_%d ? 0x%lxul : 0ul;\n", r, a.id, a.pin, ones);
  }
  else
    emit("replicateBU(w%d_%d, w%d_0, %d);\n", a.id, a.pin, r, width);
}

// Generate code for register
void CodeGen::reg(NetId r, NetWire data, unsigned width)
{
  if (width <= 64)
    emit("w%d_0 = w%d_%d;\n", r, data.id, data.pin);
  else {
    unsigned numChunks = (width+31)/32;
    emit("memcpy(w%d_0, w%d_%d, %d);\n", r, data.id, data.pin, numChunks);
  }
}

// Generate code for register with enable
void CodeGen::regEn(NetId r, NetWire cond, NetWire data, unsigned width)
{
  emit("if (w%d_%d) ", cond.id, cond.pin);
  reg(r, data, width);
}

// Generate code for count-ones
void CodeGen::countOnes(NetId r, NetWire a, unsigned width)
{
  if (isStdInt(width))
    emit("w%d_0 = countOnes(w%d_%d);\n", r, a.id, a.pin);
  else if (width <= 64)
    emit("w%d_0 = countOnes(w%d_%d) & ((1ul << %d)-1ul);\n",
      r, a.id, a.pin, width);
  else {
    emit("w%d_0 = countOnesBU(w%d_%d, %d);\n",
        r, a.id, a.pin, width);
  }
}

// Generate code for zero extend operator
void CodeGen::zeroExtend(NetId r, NetWire a, unsigned rw, unsigned aw)
{
  if (rw <= 64)
    emit("w%d_0 = w%d_%d;\n", r, a.id, a.pin);
  else {
    if (aw <= 64)
      emit("toBU(w%d_%d, w%d_0, %d);\n", a.id, a.pin, r, rw);
    else
      emit("zeroExtBU(w%d_%d, w%d_0, %d, %d);\n", a.id, a.pin, r, aw, rw);
  }
}

// Generate code for display statement
void CodeGen::display(Seq<NetWire>* wires, Seq<NetParam>* params) {
  NetWire cond = wires->elems[0];
  emit("if (w%d_%d) {\n", cond.id, cond.pin);
  unsigned i = 0;
  unsigned pi = 0;
  unsigned wi = 1;
  while (pi < params->numElems || wi < wires->numElems) {
    if (pi < params->numElems) {
      NetParam p = params->elems[pi];
      if (i == atoi(p.key)) {
        emit("  printf(\"%%s\", \"%s\");\n", p.val);
        pi++;
        i++;
        continue;
      }
    }
    if (wi < wires->numElems) {
      NetWire w = wires->elems[wi];
      emit("  printf(\"%%d\", w%d_%d);\n", w.id, w.pin);
      wi++;
      i++;
    }
  }
  emit("  printf(\"\\n\");\n}\n");
}

// Generate declarations
void CodeGen::genDecls(Seq<Net*>* nets)
{
  for (unsigned i = 0; i < nets->numElems; i++) {
    Net* net = nets->elems[i];
    if (net == NULL) continue;
    if (strcmp(net->prim, "display") == 0 ||
        strcmp(net->prim, "finish") == 0) continue;
    NetWire wire;
    wire.id = net->id;
    wire.pin = 0;
    unsigned width = net->width;
    if (strcmp(net->prim, "<")  == 0 ||
        strcmp(net->prim, "<=") == 0 ||
        strcmp(net->prim, ">")  == 0 ||
        strcmp(net->prim, ">=") == 0 ||
        strcmp(net->prim, "==") == 0 ||
        strcmp(net->prim, "!=") == 0)
      width = 1;
    declareWire(wire, width);
  }
}

// Generate code
void CodeGen::gen(Netlist* netlist)
{
  // Perform register->register splitting pass
  // (So that there is an intermediate wire going into every register)
  netlist->splitRegReg();

  // Perform topological sort
  // (So that wires are assigned in data-flow order)
  Seq<Net*> sorted;
  netlist->topSort(&sorted);

  // Keep track of which nets we've handled
  bool* handled = new bool [sorted.numElems];
  for (unsigned i = 0; i < sorted.numElems; i++) handled[i] = false;

  // Includes
  emit("#include <stdio.h>\n");
  emit("#include <stdlib.h>\n");
  emit("#include <string.h>\n");
  emit("#include <BitVec.h>\n");

  // Main function
  emit("int main() {\n");

  // Generate declarations
  genDecls(&sorted);

  // Initialise registers and constant wires
  for (unsigned i = 0; i < sorted.numElems; i++) {
    Net* net = sorted.elems[i];
    NetWire wire;
    wire.name = net->name;
    wire.id = net->id;
    wire.pin = 0;
    if (!strcmp(net->prim, "const")) {
      handled[net->id] = true;
      initWire(wire, net->width, net->lookup("val"));
    }
    if (!strcmp(net->prim, "reg") ||
        !strcmp(net->prim, "regEn")) {
      initWire(wire, net->width, net->lookup("init"));
    }
  }

  // Begin the clock loop
  emit("while (1) {\n");

  // Data-flow
  for (unsigned i = 0; i < sorted.numElems; i++) {
    Net* net = sorted.elems[i];
    if (isUnaryOp(net->prim)) {
      NetWire a = net->inputs.elems[0];
      unaryOp(net->id, net->prim, a, net->width);
      handled[net->id] = true;
    }
    if (isBinOp(net->prim)) {
      NetWire a = net->inputs.elems[0];
      NetWire b = net->inputs.elems[1];
      binOp(net->id, a, net->prim, b, net->width);
      handled[net->id] = true;
    }
    if (isCmpOp(net->prim)) {
      NetWire a = net->inputs.elems[0];
      NetWire b = net->inputs.elems[1];
      cmpOp(net->id, a, net->prim, b, net->width);
      handled[net->id] = true;
    }
    if (strcmp(net->prim, "zeroExtend") == 0) {
      CodeGen::zeroExtend(net->id, net->inputs.elems[0],
        net->width+atoi(net->lookup("ext")), net->width);
      handled[net->id] = true;
    }
    if (strcmp(net->prim, "countOnes") == 0) {
      countOnes(net->id, net->inputs.elems[0], 1 << (net->width-1));
      handled[net->id] = true;
    }
    if (strcmp(net->prim, "display") == 0) {
      display(&net->inputs, &net->params);
      handled[net->id] = true;
    }
    if (strcmp(net->prim, "replicate") == 0) {
      replicate(net->id, net->inputs.elems[0], net->width);
      handled[net->id] = true;
    }
    if (strcmp(net->prim, "id") == 0) {
      NetWire data = net->inputs.elems[0];
      emit("w%d_0 = w%d_%d;\n", net->id, data.id, data.pin);
      handled[net->id] = true;
    }
  }

  // Finish statements
  for (unsigned i = 0; i < sorted.numElems; i++) {
    Net* net = sorted.elems[i];
    if (strcmp(net->prim, "finish") == 0) {
      NetWire cond = net->inputs.elems[0];
      emit("if (w%d_%d) break;\n", cond.id, cond.pin);
      handled[net->id] = true;
    }
  }

  // Register update
  for (unsigned i = 0; i < sorted.numElems; i++) {
    Net* net = sorted.elems[i];
    if (strcmp(net->prim, "regEn") == 0) {
      NetWire cond = net->inputs.elems[0];
      NetWire data = net->inputs.elems[1];
      regEn(net->id, cond, data, net->width);
      handled[net->id] = true;
    }
    if (strcmp(net->prim, "reg") == 0) {
      NetWire data = net->inputs.elems[0];
      reg(net->id, data, net->width);
      handled[net->id] = true;
    }
  }

  // End the clock loop
  emit("}\n");

  // End the main function
  emit ("return 0;\n}");

  // Check for unhandled nets
  for (unsigned i = 0; i < sorted.numElems; i++) {
    Net* net = sorted.elems[i];
    if (!handled[net->id])
      genError("Unhandled primitive '%s'\n", net->prim);
  }
  delete [] handled;
}
