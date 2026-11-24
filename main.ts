// A tiny stack VM for make.fun's tiny stack ISA (ISA.md, version 1), written to the letter of the spec:
// 32-bit wrapping arithmetic, a data stack of at most 256 values, a call stack of at most 64 return
// addresses, 256 words of memory, ten traps (exit codes 2-11), and the step and output limits.
// Every step checks, in the ISA's order: the step limit, the program counter, the opcode, the immediate's
// fit, the stack's needs, the instruction's own traps, and only then its effect.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

function run(p, inp) {
  const n = p.length;
  const D = new Int32Array(256); // data stack
  const C = new Int32Array(64); // call stack
  const M = new Int32Array(256); // memory
  const buf = new Uint8Array(65536); // output, capped by trap 11 below
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const end = (code) => ({ out: buf.slice(0, olen), code });
  // Opcode-validity lookup built once per run, so the hot loop does one array read instead of six range tests.
  const known = new Uint8Array(256);
  for (const [lo, hi] of [[0, 7], [16, 30], [32, 34], [48, 52], [64, 65], [80, 83]])
    for (let k = lo; k <= hi; k++) known[k] = 1;
  for (;;) {
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    if (!known[op]) return end(5);
    const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 48 && op <= 51 ? 2 : 0;
    if (pc + imm >= n) return end(9);
    steps++;
    pc += 1 + imm; // pc now sits past the instruction; jumps overwrite it
    switch (op) {
      case 0: // HALT
        return end(0);
      case 1: // PUSH8, sign-extended
        if (sp === 256) return end(3);
        D[sp++] = (p[pc - 1] << 24) >> 24;
        break;
      case 2: // PUSH32, little-endian
        if (sp === 256) return end(3);
        D[sp++] = p[pc - 4] | (p[pc - 3] << 8) | (p[pc - 2] << 16) | (p[pc - 1] << 24);
        break;
      case 3: // POP
        if (sp < 1) return end(2);
        sp--;
        break;
      case 4: // DUP
        if (sp < 1) return end(2);
        if (sp === 256) return end(3);
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 5: { // SWAP
        if (sp < 2) return end(2);
        const t = D[sp - 1];
        D[sp - 1] = D[sp - 2];
        D[sp - 2] = t;
        break;
      }
      case 6: // OVER
        if (sp < 2) return end(2);
        if (sp === 256) return end(3);
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 7: { // ROT: ( a b c -- b c a )
        if (sp < 3) return end(2);
        const a = D[sp - 3];
        D[sp - 3] = D[sp - 2];
        D[sp - 2] = D[sp - 1];
        D[sp - 1] = a;
        break;
      }
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: { // the binary operators: ( a b -- r ), b on top
        if (sp < 2) return end(2);
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b); // the low 32 bits of the exact product
        else if (op === 19) { // DIV, truncated toward zero
          if (b === 0) return end(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 20) { // MOD, the sign of a
          if (b === 0) return end(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 21) { // DIVU
          if (b === 0) return end(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 22) { // MODU
          if (b === 0) return end(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31); // only the low 5 bits of the count
        else if (op === 29) r = a >> (b & 31); // arithmetic
        else if (op === 30) r = (a >>> (b & 31)) | 0; // logical, read back as signed
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        D[sp - 2] = r;
        sp--;
        break;
      }
      case 23: // NEG, wrapping
        if (sp < 1) return end(2);
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 27: // NOT
        if (sp < 1) return end(2);
        D[sp - 1] = ~D[sp - 1];
        break;
      case 48: case 49: case 50: { // JMP, JZ, JNZ: target = next instruction + signed offset
        const rel = ((p[pc - 2] | (p[pc - 1] << 8)) << 16) >> 16;
        let take = op === 48;
        if (op !== 48) {
          if (sp < 1) return end(2);
          const v = D[--sp];
          take = op === 49 ? v === 0 : v !== 0;
        }
        if (take) pc += rel;
        break;
      }
      case 51: // CALL: the immediate is the absolute address, unsigned
        if (csp === 64) return end(7);
        C[csp++] = pc;
        pc = p[pc - 2] | (p[pc - 1] << 8);
        break;
      case 52: // RET
        if (csp === 0) return end(8);
        pc = C[--csp];
        break;
      case 64: { // LOAD
        if (sp < 1) return end(2);
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 65: { // STORE: ( v addr -- )
        if (sp < 2) return end(2);
        const a = D[sp - 1];
        if (a < 0 || a > 255) return end(6);
        M[a] = D[sp - 2];
        sp -= 2;
        break;
      }
      case 80: { // PRINT: v in decimal ASCII; a print that would pass the limit writes nothing
        if (sp < 1) return end(2);
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return end(11);
        for (let k = 0; k < s.length; k++) buf[olen++] = s.charCodeAt(k);
        sp--;
        break;
      }
      case 81: // PUTC: one byte, v AND 255
        if (sp < 1) return end(2);
        if (olen === 65536) return end(11);
        buf[olen++] = D[--sp] & 255;
        break;
      case 82: // IN: -1 once the input is used up, and every time after
        if (sp === 256) return end(3);
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 83: // EXIT: the low byte of v
        if (sp < 1) return end(2);
        return end(D[sp - 1] & 255);
      default:
        return end(5);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, 'program.bin')), readFileSync(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
