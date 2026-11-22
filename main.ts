// Tiny stack VM for make.fun's tiny-stack-vm-01 (ISA v1): runs every
// program in the input dir, writes each answer as stdout.bin +
// exit.txt. Follows ISA.md / the reference VM exactly, all ten
// traps and both limits. Deterministic. Usage: node main.ts
// (MAKEFUN_INPUT_DIR / MAKEFUN_OUTPUT_DIR override /input, /output).
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode table: byte -> [immediate bytes, pops, pushes]; absent traps 5.
// 0x10-0x22 share [0,2,1] except NEG/NOT [0,1,1]; 0x1f is no opcode.
const T = {
  0: [0, 0, 0], 1: [1, 0, 1], 2: [4, 0, 1], 3: [0, 1, 0],
  4: [0, 1, 2], 5: [0, 2, 2], 6: [0, 2, 3], 7: [0, 3, 3],
  0x17: [0, 1, 1], 0x1b: [0, 1, 1],
  0x30: [2, 0, 0], 0x31: [2, 1, 0], 0x32: [2, 1, 0],
  0x33: [2, 0, 0], 0x34: [0, 0, 0],
  0x40: [0, 1, 1], 0x41: [0, 2, 0],
  0x50: [0, 1, 0], 0x51: [0, 1, 0], 0x52: [0, 0, 1], 0x53: [0, 1, 0],
};
for (let o = 0x10; o <= 0x22; o++) if (o !== 0x17 && o !== 0x1b && o !== 0x1f) T[o] = [0, 2, 1];

function run(p, inp) {
  const n = p.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ipos = 0, pc = 0, steps = 0;
  const done = (c) => ({ out: out.subarray(0, olen), code: c });

  for (;;) {
    // Step limit, pc range, opcode, immediate fit — in that order.
    if (steps === 1e6) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const o = p[pc];
    const t = T[o];
    if (t === undefined) return done(5);
    if (pc + t[0] >= n) return done(9);
    steps++;
    const next = pc + 1 + t[0];
    if (sp < t[1]) return done(2); // underflow, then overflow
    if (sp - t[1] + t[2] > 256) return done(3);
    pc = next;

    switch (o) {
      case 0: return done(0); // HALT
      case 1: D[sp++] = (p[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 2: D[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24); break; // PUSH32
      case 3: sp--; break; // POP
      case 4: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 5: { const x = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = x; break; } // SWAP
      case 6: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break; // NEG (wraps)
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        // DIV, MOD, DIVU, MODU with b = 0 trap 4.
        if ((o === 0x13 || o === 0x14 || o === 0x15 || o === 0x16) && b === 0) return done(4);
        if (o === 0x10) r = (a + b) | 0;
        else if (o === 0x11) r = (a - b) | 0;
        else if (o === 0x12) r = Math.imul(a, b); // low 32 bits of exact product
        else if (o === 0x13) { // DIV, truncating; INT_MIN / -1 is INT_MIN
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (o === 0x14) { // MOD, sign of a; x % -1 is 0
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (o === 0x15) { // DIVU, unsigned
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (o === 0x16) { // MODU, unsigned
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (o === 0x18) r = a & b;
        else if (o === 0x19) r = a | b;
        else if (o === 0x1a) r = a ^ b;
        else if (o === 0x1c) r = a << (b & 31);
        else if (o === 0x1d) r = a >> (b & 31);
        else if (o === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (o === 0x20) r = a === b ? 1 : 0;
        else if (o === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ, signed offset from next
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (o !== 0x30) { const v = D[--sp]; take = o === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL: push return address, jump to unsigned target
        if (csp === 64) return done(7);
        C[csp++] = next;
        pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34: // RET
        if (csp === 0) return done(8);
        pc = C[--csp];
        break;
      case 0x40: { // LOAD
        const addr = D[sp - 1];
        if (addr < 0 || addr >= 256) return done(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: { // STORE: (v addr --)
        const addr = D[sp - 1], v = D[sp - 2];
        if (addr < 0 || addr >= 256) return done(6);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no newline; over-limit writes nothing
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC: low byte
        if (olen + 1 > 65536) return done(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: // IN: next byte, -1 once input is used up
        D[sp++] = ipos < inp.length ? inp[ipos++] : -1;
        break;
      case 0x53: return done(D[--sp] & 255); // EXIT: low byte of v
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
