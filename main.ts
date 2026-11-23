// main.ts is mend, the CLI SPEC.md specifies (MIT). It implements all of SPEC.md: the command line,
// output and exit codes, safe paths, format detection, line matching at three tiers, unified diffs,
// SEARCH/REPLACE blocks, V4A patches, JSON edits and the all-or-nothing write. Node 22, stdlib only.
//
// In a trial the grader runs `node main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to
// runner.ts (the last lines below): keep that hand-over and runner.ts as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

function checkSafe(p: string): void {
  if (!safe(p)) throw new Fail('unsafe', p);
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: [string, string][] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

// ---------- files and lines (section 3) ----------

interface FileParts {
  br: string;
  lines: string[];
  final: boolean;
}

function parseFile(text: string): FileParts {
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  if (text === '') return { br, lines: [], final: false };
  const lines = text.split(br);
  const final = text.endsWith(br);
  if (final) lines.pop();
  return { br, lines, final };
}

function serialize(parts: FileParts): string {
  if (parts.lines.length === 0) return '';
  return parts.lines.join(parts.br) + (parts.final ? parts.br : '');
}

// ---------- matching lines (section 5) ----------

const rtrimST = (s: string): string => s.replace(/[ \t]+$/, '');
const trimST = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadST = (s: string): string => /^[ \t]*/.exec(s)![0]!;

function lineMatch(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return rtrimST(a) === rtrimST(b);
  return trimST(a) === trimST(b);
}

function occurrences(lines: string[], o: string[], tier: number, from: number): number[] {
  const out: number[] = [];
  if (o.length === 0) return out;
  for (let i = Math.max(0, from); i + o.length <= lines.length; i += 1) {
    let ok = true;
    for (let k = 0; k < o.length; k += 1) {
      if (!lineMatch(lines[i + k]!, o[k]!, tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** First tier (0 only when strict) that has an occurrence at or after `from`, with its positions. */
function findTier(lines: string[], o: string[], strict: boolean, from: number): { tier: number; at: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    const at = occurrences(lines, o, tier, from);
    if (at.length > 0) return { tier, at };
  }
  return null;
}

/** A non-context new line, re-indented at tier 2 as section 5 says. */
function reindent(line: string, tier: number, fileFirst: string, oFirst: string): string {
  if (tier !== 2) return line;
  if (line === '' || trimST(line) === '') return line;
  const f = leadST(fileFirst);
  const p = leadST(oFirst);
  if (line.startsWith(p)) return f + line.slice(p.length);
  return line;
}

interface BodyItem {
  kind: 'context' | 'old' | 'new' | 'slash';
  text: string;
}

/** O (context+old) and N (context+new) of a hunk/chunk body, in body order. */
function bodyON(body: BodyItem[]): { o: string[]; n: { text: string; ctx: number }[] } {
  const o: string[] = [];
  const n: { text: string; ctx: number }[] = [];
  for (const it of body) {
    if (it.kind === 'context') {
      n.push({ text: it.text, ctx: o.length });
      o.push(it.text);
    } else if (it.kind === 'old') {
      o.push(it.text);
    } else if (it.kind === 'new') {
      n.push({ text: it.text, ctx: -1 });
    }
  }
  return { o, n };
}

/** Replacement lines for a match of O at `pos`: context lines are the file's own, new lines re-indented. */
function replacement(lines: string[], pos: number, o: string[], n: { text: string; ctx: number }[], tier: number): string[] {
  return n.map((e) => (e.ctx >= 0 ? lines[pos + e.ctx]! : reindent(e.text, tier, lines[pos]!, o[0]!)));
}

/** True when a `\` line follows the body's last context or `+` line. */
function slashAfterLast(body: BodyItem[]): boolean {
  let last = -1;
  for (let i = 0; i < body.length; i += 1) {
    if (body[i]!.kind === 'context' || body[i]!.kind === 'new') last = i;
  }
  return last >= 0 && last + 1 < body.length && body[last + 1]!.kind === 'slash';
}

// ---------- format detection (section 4) ----------

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---------- JSON edits (section 9) ----------

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const parts = parseFile(before);
      if (line < 0 || line > parts.lines.length) throw new Fail('no-match', p);
      parts.lines.splice(line, 0, ...add);
      tree.now.set(p, serialize(parts));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---------- unified diffs (section 6) ----------

interface Hunk {
  a: number;
  body: BodyItem[];
}

interface Section {
  oldP: string | null | undefined;
  newP: string | null | undefined;
  diffOld: string | undefined;
  diffNew: string | undefined;
  renameFrom: string | undefined;
  renameTo: string | undefined;
  isNew: boolean;
  isDel: boolean;
  hunks: Hunk[];
}

/** Path text of a ---/+++ line: after the prefix, up to a tab, spaces removed, /dev/null and a/ b/ handled. */
function headerPath(raw: string): string | null {
  let t = raw.split('\t')[0]!;
  t = t.replace(/^ +/, '').replace(/ +$/, '');
  if (t === '/dev/null') return null;
  if (t.startsWith('a/') || t.startsWith('b/')) t = t.slice(2);
  return t;
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: Section[] = [];
  let cur: Section | null = null;
  let i = 0;
  const newSection = (): Section => {
    const s: Section = { oldP: undefined, newP: undefined, diffOld: undefined, diffNew: undefined, renameFrom: undefined, renameTo: undefined, isNew: false, isDel: false, hunks: [] };
    sections.push(s);
    return s;
  };
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(.*) b\/(.*)$/.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      cur = newSection();
      cur.diffOld = m[1]!;
      cur.diffNew = m[2]!;
      i += 1;
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(line);
      if (m === null) throw new Exit2(`error: parse ${i + 1}`);
      const hunk: Hunk = { a: Number(m[1]), body: [] };
      cur.hunks.push(hunk);
      i += 1;
      while (i < lines.length) {
        const b = lines[i]!;
        if (b.startsWith('diff --git ')) break;
        if (b.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (b === '') hunk.body.push({ kind: 'context', text: '' });
        else if (b.startsWith(' ')) hunk.body.push({ kind: 'context', text: b.slice(1) });
        else if (b.startsWith('-')) hunk.body.push({ kind: 'old', text: b.slice(1) });
        else if (b.startsWith('+')) hunk.body.push({ kind: 'new', text: b.slice(1) });
        else if (b.startsWith('\\')) hunk.body.push({ kind: 'slash', text: b });
        else break;
        i += 1;
      }
      while (hunk.body.length > 0) {
        const last = hunk.body[hunk.body.length - 1]!;
        if (last.kind === 'context' && last.text === '') hunk.body.pop();
        else break;
      }
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur === null || cur.hunks.length > 0 || cur.oldP !== undefined) {
        cur = newSection();
      }
      cur.oldP = headerPath(line.slice(4));
      cur.newP = headerPath(lines[i + 1]!.slice(4));
      i += 2;
      continue;
    }
    if (cur !== null && cur.hunks.length === 0) {
      if (line.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      if (line.startsWith('rename from ')) cur.renameFrom = line.slice(12).replace(/^ +/, '').replace(/ +$/, '');
      else if (line.startsWith('rename to ')) cur.renameTo = line.slice(10).replace(/^ +/, '').replace(/ +$/, '');
      else if (line.startsWith('new file mode')) cur.isNew = true;
      else if (line.startsWith('deleted file mode')) cur.isDel = true;
    }
    i += 1;
  }
  return sections.map((s) => unifiedEdit(s, strict));
}

function unifiedEdit(s: Section, strict: boolean): Edit {
  const oldPath = s.oldP !== undefined ? s.oldP : s.renameFrom !== undefined ? s.renameFrom : s.diffOld;
  const newPath = s.newP !== undefined ? s.newP : s.renameTo !== undefined ? s.renameTo : s.diffNew;
  const creation = oldPath === null || s.isNew;
  const deletion = newPath === null || s.isDel;
  return (tree) => {
    if (!creation && oldPath !== undefined && oldPath !== null) checkSafe(oldPath);
    if (!deletion && newPath !== undefined && newPath !== null) checkSafe(newPath);
    if (creation) {
      const np = newPath!;
      if (tree.get(np) !== null) throw new Fail('exists', np);
      const plus: string[] = [];
      let lastPlusSlash = false;
      for (const h of s.hunks) {
        h.body.forEach((it, idx) => {
          if (it.kind === 'new') {
            plus.push(it.text);
            lastPlusSlash = idx + 1 < h.body.length && h.body[idx + 1]!.kind === 'slash';
          }
        });
      }
      tree.now.set(np, serialize({ br: '\n', lines: plus, final: !lastPlusSlash }));
      return;
    }
    const op = oldPath!;
    const before = tree.get(op);
    if (before === null) throw new Fail('missing', op);
    if (deletion) {
      tree.now.set(op, null);
      return;
    }
    const isMove = newPath !== undefined && newPath !== null && newPath !== op;
    const np = isMove ? newPath! : op;
    if (isMove && tree.get(np) !== null) throw new Fail('exists', np);
    const parts = parseFile(before);
    const fileLines = [...parts.lines];
    let final = parts.final;
    let d = 0;
    for (const h of s.hunks) {
      const { o, n } = bodyON(h.body);
      const slash = slashAfterLast(h.body);
      if (o.length === 0) {
        const at = Math.max(0, Math.min(h.a + d, fileLines.length));
        const ins = n.map((e) => e.text);
        if (at === fileLines.length) final = !slash;
        fileLines.splice(at, 0, ...ins);
        d += ins.length;
        continue;
      }
      const found = findTier(fileLines, o, strict, 0);
      if (found === null) throw new Fail('no-match', op);
      const target = h.a - 1 + d;
      let pos = found.at[0]!;
      for (const cand of found.at) {
        if (Math.abs(cand - target) < Math.abs(pos - target)) pos = cand;
      }
      const runsToEnd = pos + o.length === fileLines.length;
      const rep = replacement(fileLines, pos, o, n, found.tier);
      fileLines.splice(pos, o.length, ...rep);
      if (runsToEnd) final = !slash;
      d += rep.length - o.length;
    }
    tree.now.set(np, serialize({ br: parts.br, lines: fileLines, final }));
    if (isMove) {
      tree.now.set(op, null);
      tree.moves.push([op, np]);
    }
  };
}

// ---------- SEARCH/REPLACE blocks (section 7) ----------

function srEdits(lines: string[], strict: boolean): Edit[] {
  interface Block {
    path: string;
    oldL: string[];
    newL: string[];
  }
  const blocks: Block[] = [];
  let prevEnd = 0;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i += 1;
      continue;
    }
    const searchLine = i;
    let eq = -1;
    for (let j = i + 1; j < lines.length; j += 1) {
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') break;
    }
    let rep = -1;
    if (eq >= 0) {
      for (let j = eq + 1; j < lines.length; j += 1) {
        if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
          rep = j;
          break;
        }
      }
    }
    if (eq < 0 || rep < 0) throw new Exit2(`error: parse ${searchLine + 1}`);
    let path: string | null = null;
    for (let j = searchLine - 1; j >= prevEnd; j -= 1) {
      const l = lines[j]!;
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) path = prevPath;
    if (path === null) throw new Exit2(`error: parse ${searchLine + 1}`);
    blocks.push({ path, oldL: lines.slice(searchLine + 1, eq), newL: lines.slice(eq + 1, rep) });
    prevPath = path;
    prevEnd = rep + 1;
    i = rep + 1;
  }
  return blocks.map((b) => (tree: Tree) => {
    checkSafe(b.path);
    if (b.oldL.length === 0) {
      if (tree.get(b.path) !== null) throw new Fail('exists', b.path);
      tree.now.set(b.path, serialize({ br: '\n', lines: [...b.newL], final: true }));
      return;
    }
    const before = tree.get(b.path);
    if (before === null) throw new Fail('missing', b.path);
    const parts = parseFile(before);
    const found = findTier(parts.lines, b.oldL, strict, 0);
    if (found === null) throw new Fail('no-match', b.path);
    if (found.at.length > 1) throw new Fail('ambiguous', b.path);
    const pos = found.at[0]!;
    const rep = b.newL.map((l) => reindent(l, found.tier, parts.lines[pos]!, b.oldL[0]!));
    parts.lines.splice(pos, b.oldL.length, ...rep);
    tree.now.set(b.path, serialize(parts));
  });
}

// ---------- V4A patches (section 8) ----------

interface VChunk {
  anchor: string | null;
  body: BodyItem[];
  eof: boolean;
}

interface VSection {
  kind: 'add' | 'del' | 'update';
  path: string;
  line: number;
  addLines: string[];
  moveTo: string | null;
  chunks: VChunk[];
}

const trimSpaces = (s: string): string => s.replace(/^ +/, '').replace(/ +$/, '');

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k -= 1) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const sections: VSection[] = [];
  let cur: (VSection & { raw: { text: string; num: number }[] }) | null = null;
  const flush = (): void => {
    if (cur === null) return;
    const raw = cur.raw;
    while (raw.length > 0 && blank(raw[raw.length - 1]!.text)) raw.pop();
    if (cur.kind === 'add') {
      for (const r of raw) {
        if (r.text.startsWith('+')) cur.addLines.push(r.text.slice(1));
        else if (r.text === '') cur.addLines.push('');
        else throw new Exit2(`error: parse ${r.num}`);
      }
    } else if (cur.kind === 'del') {
      if (raw.length > 0) throw new Exit2(`error: parse ${raw[0]!.num}`);
    } else {
      let idx = 0;
      if (raw.length > 0 && raw[0]!.text.startsWith('*** Move to: ')) {
        cur.moveTo = trimSpaces(raw[0]!.text.slice(13));
        idx = 1;
      }
      let chunk: VChunk | null = null;
      for (; idx < raw.length; idx += 1) {
        const r = raw[idx]!;
        const t = r.text;
        if (t.startsWith('@@')) {
          chunk = { anchor: trimSpaces(t.slice(2)) || null, body: [], eof: false };
          cur.chunks.push(chunk);
        } else if (t === '*** End of File') {
          if (chunk === null) {
            chunk = { anchor: null, body: [], eof: false };
            cur.chunks.push(chunk);
          }
          chunk.eof = true;
          chunk = null;
        } else if (t.startsWith('*** Move to: ')) {
          throw new Exit2(`error: parse ${r.num}`);
        } else if (t.startsWith(' ') || t.startsWith('-') || t.startsWith('+') || t === '') {
          if (chunk === null) {
            chunk = { anchor: null, body: [], eof: false };
            cur.chunks.push(chunk);
          }
          if (t === '') chunk.body.push({ kind: 'context', text: '' });
          else if (t.startsWith(' ')) chunk.body.push({ kind: 'context', text: t.slice(1) });
          else if (t.startsWith('-')) chunk.body.push({ kind: 'old', text: t.slice(1) });
          else chunk.body.push({ kind: 'new', text: t.slice(1) });
        } else {
          throw new Exit2(`error: parse ${r.num}`);
        }
      }
      if (cur.chunks.length === 0 && cur.moveTo === null) throw new Exit2(`error: parse ${cur.line}`);
    }
    sections.push(cur);
    cur = null;
  };
  for (let k = first + 1; k < last; k += 1) {
    const line = lines[k]!;
    let kind: VSection['kind'] | null = null;
    let p = '';
    if (line.startsWith('*** Add File: ')) {
      kind = 'add';
      p = trimSpaces(line.slice(14));
    } else if (line.startsWith('*** Delete File: ')) {
      kind = 'del';
      p = trimSpaces(line.slice(17));
    } else if (line.startsWith('*** Update File: ')) {
      kind = 'update';
      p = trimSpaces(line.slice(17));
    }
    if (kind !== null) {
      flush();
      cur = { kind, path: p, line: k + 1, addLines: [], moveTo: null, chunks: [], raw: [] };
    } else if (cur === null) {
      if (!blank(line)) throw new Exit2(`error: parse ${k + 1}`);
    } else {
      cur.raw.push({ text: line, num: k + 1 });
    }
  }
  flush();
  return sections.map((s) => v4aEdit(s, strict));
}

function v4aEdit(s: VSection, strict: boolean): Edit {
  return (tree) => {
    checkSafe(s.path);
    if (s.kind === 'add') {
      if (tree.get(s.path) !== null) throw new Fail('exists', s.path);
      tree.now.set(s.path, serialize({ br: '\n', lines: [...s.addLines], final: true }));
      return;
    }
    const before = tree.get(s.path);
    if (before === null) throw new Fail('missing', s.path);
    if (s.kind === 'del') {
      tree.now.set(s.path, null);
      return;
    }
    if (s.moveTo !== null) checkSafe(s.moveTo);
    if (s.moveTo !== null && tree.get(s.moveTo) !== null) throw new Fail('exists', s.moveTo);
    const parts = parseFile(before);
    const fileLines = [...parts.lines];
    let cursor = 0;
    for (const chunk of s.chunks) {
      if (chunk.anchor !== null) {
        const tiers = strict ? [0] : [0, 1, 2];
        let at = -1;
        for (const tier of tiers) {
          at = -1;
          for (let k = cursor; k < fileLines.length; k += 1) {
            if (lineMatch(fileLines[k]!, chunk.anchor, tier)) {
              at = k;
              break;
            }
          }
          if (at >= 0) break;
        }
        if (at < 0) throw new Fail('no-match', s.path);
        cursor = at + 1;
      }
      const { o, n } = bodyON(chunk.body);
      if (o.length === 0) {
        const at = chunk.eof ? fileLines.length : Math.min(cursor, fileLines.length);
        const ins = n.map((e) => e.text);
        fileLines.splice(at, 0, ...ins);
        cursor = at + ins.length;
        continue;
      }
      const tiers = strict ? [0] : [0, 1, 2];
      let chosen: { tier: number; pos: number } | null = null;
      for (const tier of tiers) {
        const at = occurrences(fileLines, o, tier, cursor).filter((p) => !chunk.eof || p + o.length === fileLines.length);
        if (at.length > 0) {
          chosen = { tier, pos: at[0]! };
          break;
        }
      }
      if (chosen === null) throw new Fail('no-match', s.path);
      const rep = replacement(fileLines, chosen.pos, o, n, chosen.tier);
      fileLines.splice(chosen.pos, o.length, ...rep);
      cursor = chosen.pos + rep.length;
    }
    const dest = s.moveTo ?? s.path;
    tree.now.set(dest, serialize({ br: parts.br, lines: fileLines, final: parts.final }));
    if (s.moveTo !== null) {
      tree.now.set(s.path, null);
      tree.moves.push([s.path, s.moveTo]);
    }
  };
}

// ---------- invocation, output, atomicity (sections 1, 2, 10) ----------

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict);
    else if (kind === 'search-replace') edits = srEdits(lines, strict);
    else edits = v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesBefore = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = movesBefore;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  interface Row {
    key: string;
    text: string;
    path: string;
  }
  const rows: Row[] = [];
  const byPath = new Map<string, Row>();
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    const row: Row = { key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}`, path: p };
    rows.push(row);
    byPath.set(p, row);
  }
  for (const [o, n] of tree.moves) {
    const ro = byPath.get(o);
    const rn = byPath.get(n);
    if (ro === undefined || rn === undefined) continue;
    if (tree.original(o) === null || tree.now.get(o) !== null) continue;
    if (tree.original(n) !== null || tree.now.get(n) === null || tree.now.get(n) === undefined) continue;
    if (!ro.text.startsWith('D ') || !rn.text.startsWith('A ')) continue;
    rows.splice(rows.indexOf(ro), 1);
    rows.splice(rows.indexOf(rn), 1);
    byPath.delete(o);
    byPath.delete(n);
    rows.push({ key: n, text: `R ${o} -> ${n}`, path: n });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  if (!check) {
    for (const p of [...tree.now.keys()]) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  const outLines = rows.map((r) => r.text);
  return { code: 0, out: [...outLines, `ok: ${outLines.length} ${outLines.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
