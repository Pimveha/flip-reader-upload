// Tag reader uploader for the browser (and Node, for the tests).
//
// A JavaScript port of tools/tag_book.py (text cleanup, book header), tools/tag_compress.py
// (book format 1, compression version 2) and tools/tag_image.py (sleep image), plus the BLE
// upload protocol of tag_firmware/reader/tr_upload.h over Web Bluetooth.
// The host test (web/test_node.mjs) checks that books packed here are byte-identical to
// the Python tools' output.
(function (root) {
  "use strict";

  // ---------------------------------------------------------------- CRC-32 (zlib)
  const CRC_TABLE = (() => {
    const t = new Uint32Array(256);
    for (let n = 0; n < 256; n++) {
      let c = n;
      for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
      t[n] = c >>> 0;
    }
    return t;
  })();

  function crc32(bytes, crc = 0) {
    crc = ~crc >>> 0;
    for (let i = 0; i < bytes.length; i++) crc = CRC_TABLE[(crc ^ bytes[i]) & 0xff] ^ (crc >>> 8);
    return ~crc >>> 0;
  }

  const asciiBytes = (s) => {
    const b = new Uint8Array(s.length);
    for (let i = 0; i < s.length; i++) b[i] = s.charCodeAt(i);
    return b;
  };

  // ---------------------------------------------------------------- text cleanup (tag_book.py)
  const REPLACE = {
    "‘": "'", "’": "'", "‚": "'", "‛": "'", "′": "'",
    "“": '"', "”": '"', "„": '"', "‟": '"', "″": '"',
    "«": '"', "»": '"',
    "‐": "-", "‑": "-", "‒": "-", "–": "-", "−": "-",
    "—": "--", "―": "--",
    "…": "...", " ": " ", " ": " ", " ": " ", "­": "",
    "×": "x", "·": ".", "•": "*",
    "æ": "ae", "Æ": "AE", "œ": "oe", "Œ": "OE", "ß": "ss",
    "ø": "o", "Ø": "O", "ł": "l", "Ł": "L",
  };
  const isPrintable = (c) => c === "\n" || (c >= " " && c <= "~");

  function stripGutenberg(text) {
    const start = /^\*\*\* ?START OF (THE|THIS) PROJECT GUTENBERG.*$/m.exec(text);
    const end = /^\*\*\* ?END OF (THE|THIS) PROJECT GUTENBERG.*$/m.exec(text);
    if (start && end && start.index + start[0].length < end.index)
      return text.slice(start.index + start[0].length, end.index);
    return text;
  }

  function gutenbergCleanup(text) {
    text = text.replace(/^[ ]*\[Illustration(:[^\]]*)?\][ ]*$/gm, "");
    return text.replace(/_([^_\n]+(?:\n[^_\n]+)*)_/g, "$1");
  }

  function toAscii(text) {
    const out = [];
    const unknown = new Map();
    for (const ch of text) {
      if (isPrintable(ch)) out.push(ch);
      else if (ch === "\t") out.push(" ");
      else if (ch in REPLACE) out.push(REPLACE[ch]);
      else {
        const base = ch.normalize("NFKD").replace(/\p{M}/gu, "");
        if (base && [...base].every((c) => c >= " " && c <= "~")) out.push(base);
        else if (/^\p{C}$/u.test(ch)) {
          // control / format character: drop
        } else {
          out.push("?");
          unknown.set(ch, (unknown.get(ch) || 0) + 1);
        }
      }
    }
    return [out.join(""), unknown];
  }

  const WRAP_MIN = 55;

  function unwrap(text) {
    const paras = [];
    for (const block of text.split(/\n[ ]*\n/)) {
      const lines = block.split("\n").map((l) => l.trim()).filter((l) => l).map((l) => l.replace(/ {2,}/g, " "));
      if (!lines.length) continue;
      const prose = lines.length > 1 && Math.max(...lines.slice(0, -1).map((l) => l.length)) >= WRAP_MIN;
      paras.push(prose ? lines.join(" ") : lines.join("\n"));
    }
    return paras.join("\n\n") + "\n";
  }

  // raw: Uint8Array of the file. Returns {text (ASCII string), unknown (Map)}.
  function normalise(raw, keepLines = false) {
    if (raw[0] === 0xef && raw[1] === 0xbb && raw[2] === 0xbf) raw = raw.subarray(3);
    let text;
    try {
      text = new TextDecoder("utf-8", { fatal: true }).decode(raw);
    } catch (e) {
      text = new TextDecoder("windows-1252").decode(raw);
    }
    text = text.replace(/\r\n/g, "\n").replace(/\r/g, "\n");
    text = gutenbergCleanup(stripGutenberg(text));
    let unknown;
    [text, unknown] = toAscii(text);
    text = keepLines ? text.replace(/\n{3,}/g, "\n\n").replace(/^\n+|\n+$/g, "") + "\n" : unwrap(text);
    return { text, unknown };
  }

  function guessTitle(raw) {
    let head = new TextDecoder("utf-8").decode(raw.subarray(0, 4000));
    if (head.charCodeAt(0) === 0xfeff) head = head.slice(1);
    const m = /^Title: *(.+?)\s*$/m.exec(head);
    return m ? m[1] : null;
  }

  // ---------------------------------------------------------------- compression (tag_compress.py)
  const BLOCK = 2048, MAX_BITS = 24, CHDR = 0x54, MAX_STRINGS = 0xffff;
  const TOKEN = /( ?[A-Za-z']+|[\s\S])/g;

  function blocksOf(text) {
    const b = [];
    for (let i = 0; i < text.length; i += BLOCK) b.push(text.slice(i, i + BLOCK));
    return b;
  }

  function symbolCounts(tokens, vocab) {
    const c = new Map();
    const add = (s) => c.set(s, (c.get(s) || 0) + 1);
    for (const t of tokens) {
      if (vocab.has(t)) add(t);
      else for (const ch of t) add(ch);
    }
    return c;
  }

  function chooseWords(tokens, rounds = 3, entry = 4) {
    const words = new Map();
    for (const t of tokens) if (t.length > 1) words.set(t, (words.get(t) || 0) + 1);
    let vocab = new Set();
    for (let r = 0; r < rounds; r++) {
      const syms = symbolCounts(tokens, vocab);
      let n = 0;
      for (const v of syms.values()) n += v;
      const cost = new Map();
      for (const [c, v] of syms) if (c.length === 1) cost.set(c, -Math.log2(v / n));
      const next = new Set();
      for (const [w, c] of words) {
        let spell = 0;
        for (const ch of w) spell += cost.has(ch) ? cost.get(ch) : 12.0;
        if (c * (spell + Math.log2(c / n)) > (w.length + entry) * 8) next.add(w);
      }
      vocab = next;
    }
    let total = 256;
    for (const w of vocab) total += w.length;
    if (total > MAX_STRINGS) {
      const ranked = [...vocab].sort((a, b) => words.get(b) * b.length - words.get(a) * a.length || 0);
      vocab = new Set();
      total = 256;
      for (const w of ranked) {
        if (total + w.length > MAX_STRINGS) break;
        vocab.add(w);
        total += w.length;
      }
    }
    return vocab;
  }

  const cmpStr = (a, b) => (a < b ? -1 : a > b ? 1 : 0);

  // Min-heap ordered by (f, i), like Python's heapq on (f, i, ...) tuples.
  class Heap {
    constructor() { this.a = []; }
    less(x, y) { return x.f < y.f || (x.f === y.f && x.i < y.i); }
    push(x) {
      const a = this.a;
      a.push(x);
      let k = a.length - 1;
      while (k > 0) {
        const p = (k - 1) >> 1;
        if (!this.less(a[k], a[p])) break;
        [a[k], a[p]] = [a[p], a[k]];
        k = p;
      }
    }
    pop() {
      const a = this.a, top = a[0], last = a.pop();
      if (a.length) {
        a[0] = last;
        let k = 0;
        for (;;) {
          const l = 2 * k + 1, r = l + 1;
          let m = k;
          if (l < a.length && this.less(a[l], a[m])) m = l;
          if (r < a.length && this.less(a[r], a[m])) m = r;
          if (m === k) break;
          [a[k], a[m]] = [a[m], a[k]];
          k = m;
        }
      }
      return top;
    }
    get size() { return this.a.length; }
  }

  function codeLengths(freqIn) {
    let freq = new Map(freqIn);
    for (;;) {
      if (freq.size === 1) return new Map([...freq.keys()].map((s) => [s, 1]));
      const items = [...freq.entries()].sort((x, y) => cmpStr(x[0], y[0]) || x[1] - y[1]);
      const heap = new Heap();
      items.forEach(([s, f], i) => heap.push({ f, i, syms: [s] }));
      const lengths = new Map();
      let n = items.length;
      while (heap.size > 1) {
        const x = heap.pop(), y = heap.pop();
        const merged = x.syms.concat(y.syms);
        for (const s of merged) lengths.set(s, (lengths.get(s) || 0) + 1);
        heap.push({ f: x.f + y.f, i: n++, syms: merged });
      }
      let max = 0;
      for (const v of lengths.values()) max = Math.max(max, v);
      if (max <= MAX_BITS) return lengths;
      const flat = new Map();
      for (const [s, f] of freq) flat.set(s, Math.floor((f + 1) / 2));
      freq = flat;
    }
  }

  class Bytes {
    constructor() { this.a = []; }
    u8(v) { this.a.push(v & 255); }
    u16(v) { this.u8(v); this.u8(v >>> 8); }
    u32(v) { this.u16(v & 0xffff); this.u16(v >>> 16); }
    bytes(b) { for (const x of b) this.a.push(x); }
    get length() { return this.a.length; }
    out() { return Uint8Array.from(this.a); }
  }

  function compress(text) {
    const blocks = blocksOf(text);
    const blockTokens = blocks.map((b) => b.match(TOKEN) || []);
    const all = blockTokens.flat();
    const vocab = chooseWords(all);
    let freq = symbolCounts(all, vocab);
    if (!freq.size) freq = new Map([[" ", 1]]);
    const lengths = codeLengths(freq);
    let maxlen = 0;
    for (const v of lengths.values()) maxlen = Math.max(maxlen, v);
    const symbols = [...freq.keys()].sort(
      (a, b) => lengths.get(a) - lengths.get(b) || freq.get(b) - freq.get(a) || cmpStr(a, b));
    const sid = new Map(symbols.map((s, i) => [s, i]));
    const counts = new Array(MAX_BITS + 1).fill(0);
    for (const s of symbols) counts[lengths.get(s)]++;
    const codes = new Array(symbols.length);
    let code = 0, k = 0;
    for (let len = 1; len <= MAX_BITS; len++) {
      while (k < symbols.length && lengths.get(symbols[k]) === len) codes[k++] = code++;
      code *= 2;
    }

    const data = [];
    const table = [0];
    for (const bt of blockTokens) {
      let acc = 0, nbits = 0;  // at most 7 + 24 bits: use plain numbers (exact up to 2^53)
      const emit = (id) => {
        const len = lengths.get(symbols[id]);
        acc = acc * 2 ** len + codes[id];
        nbits += len;
        while (nbits >= 8) {
          nbits -= 8;
          data.push(Math.floor(acc / 2 ** nbits) & 255);
          acc %= 2 ** nbits;
        }
      };
      for (const t of bt) {
        if (vocab.has(t)) emit(sid.get(t));
        else for (const ch of t) emit(sid.get(ch));
      }
      if (nbits) data.push((acc * 2 ** (8 - nbits)) & 255);
      table.push(data.length);
    }

    const strings = symbols.join("");
    if (strings.length > MAX_STRINGS || symbols.length > 0xffff) throw new Error("dictionary too large");
    const strTab = new Bytes();
    let o = 0;
    for (const s of symbols) { strTab.u16(o); o += s.length; }
    strTab.u16(o);
    strTab.bytes(asciiBytes(strings));
    const blkTab = new Bytes();
    for (const v of table) blkTab.u32(v);
    const oStr = CHDR, oCode = oStr + strTab.length, oBlk = oCode, oData = oBlk + blkTab.length;
    const h = new Bytes();
    h.bytes(asciiBytes("TCMP"));
    h.u16(BLOCK); h.u8(maxlen); h.u8(2);
    h.u32(blocks.length); h.u32(symbols.length);
    h.u32(oStr); h.u32(oCode); h.u32(oBlk); h.u32(oData);
    for (let i = 1; i <= MAX_BITS; i++) h.u16(counts[i]);
    const hb = h.out();
    const out = new Bytes();
    out.bytes(hb);
    out.u32(crc32(hb));
    out.bytes(strTab.out());
    out.bytes(blkTab.out());
    out.bytes(data);
    return out.out();
  }

  // ---------------------------------------------------------------- book image (tag_book.py pack)
  const BOOK_AREA = 0x74000 - 0x30000, HEADER = 64, TITLE_SIZE = 44;

  function packBook(text, title, compressed = true) {
    for (let i = 0; i < text.length; i++) {
      const c = text.charCodeAt(i);
      if (!(c === 10 || (c >= 0x20 && c <= 0x7e))) throw new Error("text is not printable ASCII");
    }
    const body = compressed ? compress(text) : asciiBytes(text);
    if (body.length > BOOK_AREA - HEADER)
      throw new Error(`the book needs ${body.length} bytes, the tag holds ${BOOK_AREA - HEADER}`);
    const t = asciiBytes(toAscii(title.replace(/\n/g, " "))[0]).subarray(0, TITLE_SIZE - 1);
    const h = new Bytes();
    h.bytes(asciiBytes("TBOK"));
    h.u8(1); h.u8(compressed ? 1 : 0); h.u16(HEADER);
    const tb = asciiBytes(text);
    h.u32(tb.length); h.u32(crc32(tb));
    const tt = new Uint8Array(TITLE_SIZE);
    tt.set(t);
    h.bytes(tt);
    const hb = h.out();
    const img = new Uint8Array(HEADER + body.length);
    img.set(hb, 0);
    new DataView(img.buffer).setUint32(0x3c, crc32(hb), true);
    img.set(body, HEADER);
    return img;
  }

  // ---------------------------------------------------------------- sleep image (tag_image.py)
  const W = 122, H = 250, STRIDE = 16, FRAME = STRIDE * H;

  // gray: Float32Array(W*H), 0 (black) .. 255 (white). Floyd-Steinberg to 1 bit.
  function packSleepImage(gray, dither = true) {
    const g = Float32Array.from(gray);
    const data = new Uint8Array(FRAME).fill(0xff);
    for (let y = 0; y < H; y++) {
      for (let x = 0; x < W; x++) {
        const i = y * W + x, old = g[i], v = old < 128 ? 0 : 255;
        if (v === 0) data[y * STRIDE + (x >> 3)] &= ~(0x80 >> (x & 7)) & 0xff;
        if (!dither) continue;
        const e = old - v;
        if (x + 1 < W) g[i + 1] += (e * 7) / 16;
        if (y + 1 < H) {
          if (x > 0) g[i + W - 1] += (e * 3) / 16;
          g[i + W] += (e * 5) / 16;
          if (x + 1 < W) g[i + W + 1] += e / 16;
        }
      }
    }
    const h = new Bytes();
    h.bytes(asciiBytes("TIMG"));
    h.u8(1); h.u8(0); h.u16(W); h.u16(H); h.u16(STRIDE); h.u32(FRAME); h.u32(crc32(data));
    for (let i = 0; i < 8; i++) h.u8(0);
    const hb = h.out();
    const img = new Uint8Array(32 + FRAME);
    img.set(hb, 0);
    new DataView(img.buffer).setUint32(28, crc32(hb), true);
    img.set(data, 32);
    return img;
  }

  // ---------------------------------------------------------------- upload protocol (tr_upload.h)
  const SERVICE = "13187b10-eba9-a3ba-044e-83d3217d9a38";
  const CHAR = "4b646063-6264-f3a7-8941-e65356ea82fe";
  const TARGET_BOOK = 0, TARGET_IMAGE = 1;
  const STATES = ["idle", "receiving", "done", "failed"];
  const ERRORS = ["ok", "bad command", "bad target", "length", "no begin", "out of order",
    "flash write failed", "CRC mismatch", "incomplete", "not a book/image header", "connection lost"];

  function* commands(img, target, chunk) {
    const b = new Uint8Array(10);
    const dv = new DataView(b.buffer);
    b[0] = 0x20; b[1] = target;
    dv.setUint32(2, img.length, true);
    dv.setUint32(6, crc32(img), true);
    yield b;
    for (let off = 0; off < img.length; off += chunk) {
      const part = img.subarray(off, off + chunk);
      const c = new Uint8Array(5 + part.length);
      c[0] = 0x21;
      new DataView(c.buffer).setUint32(1, off, true);
      c.set(part, 5);
      yield c;
    }
    yield Uint8Array.of(0x22);
  }

  function parseStatus(dv) {
    if (dv.byteLength < 16 || dv.getUint8(0) !== 0x55) return { state: "?", error: "no status" };
    return {
      state: STATES[dv.getUint8(1)] || String(dv.getUint8(1)),
      error: ERRORS[dv.getUint8(2)] || String(dv.getUint8(2)),
      received: dv.getUint32(4, true), length: dv.getUint32(8, true), crc: dv.getUint32(12, true),
    };
  }

  const RESET_IMAGE = Uint8Array.of(0x24, TARGET_IMAGE);  // back to the default (moon) sleep screen

  // Upload over Web Bluetooth. img = null resets the sleep image instead.
  // onProgress(done, total), log(text). Chunk 176 fits an ATT MTU of 185 (macOS); the tag
  // accepts up to 250.
  async function upload(img, target, { onProgress = () => {}, log = () => {}, chunk = 176, acceptAll = false } = {}) {
    const options = acceptAll
      ? { acceptAllDevices: true, optionalServices: [SERVICE] }
      // "ESL", not "ESL_": iOS remembers a device by its GATT Device Name, which older tag
      // firmware sets to just "ESL" (the advertised name is ESL_xxxxxx).
      : { filters: [{ namePrefix: "ESL" }], optionalServices: [SERVICE] };
    const device = await navigator.bluetooth.requestDevice(options);
    log(`Connecting to ${device.name || "tag"}...`);
    const server = await device.gatt.connect();
    try {
      const ch = await (await server.getPrimaryService(SERVICE)).getCharacteristic(CHAR);
      const status = async () => parseStatus(await ch.readValue());
      const t0 = Date.now();
      let i = 0;
      const cmds = img ? commands(img, target, chunk) : [RESET_IMAGE];
      for (const c of cmds) {
        await ch.writeValueWithResponse(c);
        if (i === 0 || c[0] === 0x22 || c[0] === 0x24 || i % 32 === 0) {
          const st = await status();
          if (st.state === "failed" || st.error !== "ok") throw new Error(`the tag reports: ${st.error}`);
        }
        if (c[0] === 0x21) onProgress(Math.min(img.length, (i) * chunk), img.length);
        i++;
      }
      let st = await status();
      for (let k = 0; k < 40 && st.state !== "done" && st.state !== "failed"; k++) {
        await new Promise((r) => setTimeout(r, 250));
        st = await status();
      }
      if (st.state !== "done") throw new Error(`upload failed: ${st.error}`);
      if (!img) {
        log("Sleep screen reset to the default (moon).");
        return st;
      }
      onProgress(img.length, img.length);
      log(`Done in ${((Date.now() - t0) / 1000).toFixed(1)} s, CRC ${st.crc.toString(16).toUpperCase()} checked by the tag.`);
      return st;
    } finally {
      try { server.disconnect(); } catch (e) { /* already gone */ }
    }
  }

  root.TagUpload = {
    crc32, normalise, guessTitle, toAscii, compress, packBook, packSleepImage, commands, parseStatus, upload, RESET_IMAGE,
    W, H, TARGET_BOOK, TARGET_IMAGE,
  };
})(typeof globalThis !== "undefined" ? globalThis : this);
