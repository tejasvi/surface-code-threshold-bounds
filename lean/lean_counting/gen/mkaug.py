"""mkaug.py: Lean data and check modules for one augmented certificate of the rotated surface code (untrusted
generator; Lean checks everything). Streams the inputs, so it handles certificates of ~10^8 near states.

usage: python3 -I -B gen/mkaug.py NAME PREFIX K0DEN NEARCHUNKS IFCHUNKS BULKCHUNKS HEIGHTS_PER_DFS [key=value ...]
  per=N       records per data chunk (default 400000)
  hN=N        ParamsA.hN (default 0: the bottom side is checked strictly)
  dfsHi=N     start checks (dfsHA) from the heights 0..N-1 and bigH; the heights N..HC+K are covered by near
              consistency checks (consistOKA) instead; needs N >= K (from a height >= K a K-step walk stays at
              heights >= 0 and every window of m edges starts at height >= m, so a witness checked at bigH, inside
              the window's bounding box where x - y <= m, also passes the top check at the true height)
              (default HC + K + 1: dfsHA at every height)
  cons=N      number of consistency modules (default 1; used when dfsHi <= HC + K)
  dfsSplit=N  1 (default): D0 = dfsHA at bigH, D1.. = dfsHA over ranges of HEIGHTS_PER_DFS heights; N > 1: one module
              per height (bigH first) and per range of first steps (the 8 candidates in N parts), with dfsTopA

Reads the outputs of the certificate generator tm2d_aug_omp (PREFIX.json, PREFIX.near_keys, PREFIX.aug_H, PREFIX.bulk_states):
  near_keys    uint64 little endian, sorted: step i in bits 2i, 2i+1; label i (C = 1) in bit 32 + i; head height h
               (0 <= h < HC) from bit 48
  aug_H        int64 little endian, combined numbering [near | interface | bulk]: G of the near states (near_keys
               order), then H_bulk twice
  bulk_states  one line per bulk state: K step digits, a space, K labels E/C (H_bulk order)
Writes, relative to the project root (the current directory):
  QECCountComp/Data/NAME/C<j>.lean   hex records (KW digits key, 13 digits potential): near records, then bulk ones
  QECCountComp/Data/NAME.lean        nkNAME, nGNAME (near), bkNAME, bHNAME (bulk), PNAME : ParamsA
  QEC/Checks/NAME/N<j>.lean          near rows of a range of near states (native_decide)
  QEC/Checks/NAME/I<j>.lean          interface rows (head height HC) of a range of bulk states
  QEC/Checks/NAME/B<j>.lean          bulk rows (head height bigH) of a range of bulk states
  QEC/Checks/NAME/D<j>.lean          start completeness from a range of first-vertex heights (D0: height bigH)
  QEC/Checks/NAME/Q<j>.lean          near consistency for the heights dfsHi..HC+K (only if dfsHi <= HC + K)
  QEC/Checks/NAME/S.lean             sizes, and the start bounds (every first-vertex height)
  QEC/Checks/NAME/LIST.txt           the check modules
and prints a JSON summary (input sha256, counts, Hmin, start constants, the chosen bound K0n/K0d).
Keys (AugC.ckeyA): steps (step i = base-4 digit i) + 4^K * labels (label i = bit i) + 8^K * h; bulk states have
h = 0. This is an order-preserving compression of tm2d_aug_omp's uint64 key, so the near records keep the file order.
"""
import array
import hashlib
import json
import os
import sys
from fractions import Fraction


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def rat(s):
    """tm2d_aug_omp's decimal parser: digits with an optional point, no reduction."""
    num, den, fr = 0, 1, False
    for ch in s:
        if ch == ".":
            fr = True
            continue
        num = num * 10 + int(ch)
        if fr:
            den *= 10
    return num, den


DL2 = [1, -1, -1, 1]


def blocks(path, typecode, count, offset=0, blk=1 << 20):
    """Yield arrays of `count` items of `typecode` (8 bytes each) from `path`, starting at item `offset`."""
    with open(path, "rb") as f:
        f.seek(8 * offset)
        left = count
        while left > 0:
            a = array.array(typecode)
            a.frombytes(f.read(8 * min(blk, left)))
            assert len(a) > 0
            left -= len(a)
            yield a


def main():
    a = sys.argv[1:]
    name, pre = a[0], a[1]
    K0den, nnear, nif, nbulk, hper = int(a[2]), int(a[3]), int(a[4]), int(a[5]), int(a[6])
    opt = dict(kv.split("=", 1) for kv in a[7:])
    js = json.load(open(pre + ".json"))
    M, HC = js["M"], js["HC"]
    K = M - 1
    n = HC + K + 1
    per = int(opt.get("per", 400000))
    hN = int(opt.get("hN", 0))
    dfsHi = int(opt.get("dfsHi", n))
    ncons = int(opt.get("cons", 1))
    split = int(opt.get("dfsSplit", 1))
    assert 1 <= split <= 8
    assert HC >= 2 * K + 6 and js["verdict"] == "ALL ROWS HOLD" and K <= 16
    assert dfsHi >= n or dfsHi >= K
    Pn, Pd = rat(js["p"])
    Xn, Xd = rat(js["X"])
    Ln, Ld = rat(js["lam"])
    nn, nb = js["near_states"], js["bulk_states"]
    assert os.path.getsize(pre + ".near_keys") == 8 * nn and os.path.getsize(pre + ".aug_H") == 8 * (nn + 2 * nb)
    kw = max(1, (3 * K + max(1, HC.bit_length()) + 3) // 4)
    hw = 13
    m2, mK = (1 << (2 * K)) - 1, (1 << K) - 1
    allowed = m2 | (mK << 32) | (0xFFFF << 48)
    VD = [sum(DL2[(sc >> (2 * i)) & 3] for i in range(K)) for sc in range(1 << (2 * K))]
    PC = [bin(lc).count("1") for lc in range(1 << K)]
    wE, wC, Q = Pn * Xn * Xn, (Pd - Pn) * Xd * Xd, Pd * Xd * Xn
    ddir = os.path.join("QECCountComp", "Data", name)
    os.makedirs(ddir, exist_ok=True)
    chunks = []

    def flush(kind, recs, lo):
        cid = len(chunks)
        with open(os.path.join(ddir, "C%d.lean" % cid), "w") as f:
            f.write("-- Generated by gen/mkaug.py: augmented certificate %s, %s records %d..%d (%d hex digits key, "
                    "%d hex digits potential).\n" % (name, kind, lo, lo + len(recs) - 1, kw, hw))
            f.write("namespace QECComp.Data.%s\n\n" % name)
            f.write("/-- The %s records %d..%d of augmented certificate %s. -/\n" % (kind, lo, lo + len(recs) - 1, name))
            # noinline: otherwise the compiler copies every chunk's literal into the loader module's C code
            f.write("@[noinline] def c%d : String := \"" % cid)
            f.write("".join(recs))
            f.write("\"\n\nend QECComp.Data.%s\n" % name)
        chunks.append((kind, cid))

    fmt = "%%0%dx%%0%dx" % (kw, hw)
    # near records, streamed in file order; start sums S[h0][c] of G
    SG = [[0] * (K + 1) for _ in range(n + 1)]
    Hmin, prev, idx, recs, lo = None, -1, 0, [], 0
    gblocks = blocks(pre + ".aug_H", "q", nn)
    gbuf, gpos = array.array("q"), 0
    for kb in blocks(pre + ".near_keys", "Q", nn):
        for u in kb:
            if gpos == len(gbuf):
                gbuf, gpos = next(gblocks), 0
            g = gbuf[gpos]
            gpos += 1
            assert u & ~allowed == 0
            sc, lc, h = u & m2, (u >> 32) & mK, u >> 48
            assert h < HC and 1 <= g < 16 ** hw
            ck = sc | (lc << (2 * K)) | (h << (3 * K))
            assert ck > prev, "near keys not strictly increasing"
            prev = ck
            Hmin = g if Hmin is None or g < Hmin else Hmin
            h0 = h + VD[sc]
            if 0 <= h0 < n:
                SG[h0][PC[lc]] += g
            recs.append(fmt % (ck, g))
            idx += 1
            if len(recs) == per:
                flush("near", recs, lo)
                lo, recs = idx, []
    if recs:
        flush("near", recs, lo)
    assert idx == nn
    # bulk records: codes from bulk_states, sorted
    Hb = array.array("q")
    for b in blocks(pre + ".aug_H", "q", nb, offset=nn):
        Hb.extend(b)
    assert len(Hb) == nb
    bulk = []
    with open(pre + ".bulk_states") as f:
        for i, ln in enumerate(l for l in f if l.strip()):
            ds, ls = ln.split()
            assert len(ds) == K and len(ls) == K and set(ls) <= set("EC")
            sc = sum(int(d) << (2 * t) for t, d in enumerate(ds))
            lc = sum((1 << t) for t, c in enumerate(ls) if c == "C")
            bulk.append((sc | (lc << (2 * K)), Hb[i], VD[sc], PC[lc]))
    assert len(bulk) == nb
    bulk.sort(key=lambda r: r[0])
    assert all(bulk[i][0] < bulk[i + 1][0] for i in range(nb - 1)), "duplicate bulk keys"
    assert all(1 <= r[1] < 16 ** hw for r in bulk)
    Hmin = min(Hmin, min(r[1] for r in bulk))
    assert Hmin == js["H_min"]
    BG = {}
    for r in bulk:
        BG[(r[2], r[3])] = BG.get((r[2], r[3]), 0) + r[1]
    for (dv, c), s in BG.items():
        SG[n][c] += s
        for h0 in range(n):
            if h0 - dv >= HC:
                SG[h0][c] += s
    for j in range(0, nb, per):
        flush("bulk", [fmt % (r[0], r[1]) for r in bulk[j:j + per]], j)
    wpow = [wE ** (K - c) * wC ** c for c in range(K + 1)]
    S = [sum(wpow[c] * SG[h0][c] for c in range(K + 1)) for h0 in range(n + 1)]
    K0 = max(Fraction((wE + wC) ** 2 * s, Hmin * Q ** (K + 2)) for s in S)
    K0num = -((-K0.numerator * K0den) // K0.denominator)
    for s in S:
        assert (wE + wC) ** 2 * s * K0den <= K0num * Hmin * Q ** (K + 2)
    cn = ", ".join("%s.c%d" % (name, c) for k, c in chunks if k == "near")
    cb = ", ".join("%s.c%d" % (name, c) for k, c in chunks if k == "bulk")
    with open(os.path.join("QECCountComp", "Data", name + ".lean"), "w") as f:
        f.write("import QECCountComp.AugC\nimport QECCountComp.SeamLoad\n")
        for k, c in chunks:
            f.write("import QECCountComp.Data.%s.C%d\n" % (name, c))
        f.write("\n/-!\n# Augmented certificate %s (generated by gen/mkaug.py)\n\n" % name)
        for ext in ("json", "near_keys", "aug_H", "bulk_states"):
            f.write("- `%s.%s`, sha256 `%s`\n" % (os.path.basename(pre), ext, sha256(pre + "." + ext)))
        f.write("- M = %d (memory K = %d), HC = %d, hN = %d; %d near states, %d bulk states\n" % (M, K, HC, hN, nn, nb))
        f.write("- p** = %d/%d, X = %d/%d, lambda = %d/%d, Hmin = %d\n" % (Pn, Pd, Xn, Xd, Ln, Ld, Hmin))
        f.write("- start constant %.10g <= %d/%d (maximum over the first-vertex heights)\n-/\n\n" % (
            float(K0), K0num, K0den))
        f.write("namespace QECComp.Data\n\n")
        f.write("/-- The near records of augmented certificate %s. -/\n" % name)
        f.write("def ldn%s : Array Nat × Array Nat := loadDataW %d %d [%s]\n\n" % (name, kw, hw, cn))
        f.write("/-- The bulk records of augmented certificate %s. -/\n" % name)
        f.write("def ldb%s : Array Nat × Array Nat := loadDataW %d %d [%s]\n\n" % (name, kw, hw, cb))
        f.write("/-- The near keys of augmented certificate %s. -/\ndef nk%s : Array Nat := ldn%s.1\n\n" % (
            name, name, name))
        f.write("/-- The near potentials of augmented certificate %s. -/\ndef nG%s : Array Nat := ldn%s.2\n\n" % (
            name, name, name))
        f.write("/-- The bulk keys of augmented certificate %s. -/\ndef bk%s : Array Nat := ldb%s.1\n\n" % (
            name, name, name))
        f.write("/-- The bulk potentials of augmented certificate %s. -/\ndef bH%s : Array Nat := ldb%s.2\n\n" % (
            name, name, name))
        f.write("/-- The parameters of augmented certificate %s. -/\n" % name)
        f.write("def P%s : ParamsA where\n  K := %d\n  HC := %d\n  hN := %d\n  wE := %d\n  wC := %d\n  Q := %d\n"
                "  lamN := %d\n  lamD := %d\n  Hmin := %d\n  K0n := %d\n  K0d := %d\n\n" % (
                    name, K, HC, hN, wE, wC, Q, Ln, Ld, Hmin, K0num, K0den))
        f.write("end QECComp.Data\n")
    # check modules
    cdir = os.path.join("QEC", "Checks", name)
    os.makedirs(cdir, exist_ok=True)
    args = "P%s nk%s nG%s bk%s bH%s" % (name, name, name, name, name)
    hdr = "import QECCountComp.Data.%s\n\nnamespace QECChecks.%s\n\nopen QECComp QECComp.Data\n\n" % (name, name)
    mods = []
    bn = [nn * j // nnear for j in range(nnear + 1)]
    for j in range(nnear):
        with open(os.path.join(cdir, "N%d.lean" % j), "w") as f:
            f.write(hdr)
            f.write("/-- Rows of the near states %d..%d of augmented certificate %s. -/\n" % (
                bn[j], bn[j + 1] - 1, name))
            f.write("theorem near%d : nearRowsOKA %s %d %d = true := by\n  native_decide\n\nend QECChecks.%s\n" % (
                j, args, bn[j], bn[j + 1], name))
        mods.append("N%d" % j)
    for tag, fn, cnt, what in (("I", "ifRowsOKA", nif, "interface rows (head height HC)"),
                               ("B", "bulkRowsOKA", nbulk, "bulk rows (head height bigH)")):
        bb = [nb * j // cnt for j in range(cnt + 1)]
        for j in range(cnt):
            with open(os.path.join(cdir, "%s%d.lean" % (tag, j)), "w") as f:
                f.write(hdr)
                f.write("/-- The %s of the bulk states %d..%d of augmented certificate %s. -/\n" % (
                    what, bb[j], bb[j + 1] - 1, name))
                f.write("theorem %s%d : %s %s %d %d = true := by\n  native_decide\n\nend QECChecks.%s\n" % (
                    tag.lower(), j, fn, args, bb[j], bb[j + 1], name))
            mods.append("%s%d" % (tag, j))
    top = min(dfsHi, n)
    if split <= 1:
        with open(os.path.join(cdir, "D0.lean"), "w") as f:
            f.write(hdr)
            f.write("/-- Start completeness from the height bigH, augmented certificate %s. -/\n" % name)
            f.write("theorem dfs0 : dfsHA %s bigH = true := by\n  native_decide\n\nend QECChecks.%s\n" % (args, name))
        mods.append("D0")
        j = 1
        for s in range(0, top, hper):
            cnt = min(hper, top - s)
            with open(os.path.join(cdir, "D%d.lean" % j), "w") as f:
                f.write(hdr)
                f.write("/-- Start completeness from the heights %d..%d, augmented certificate %s. -/\n" % (
                    s, s + cnt - 1, name))
                f.write("theorem dfs%d : rangeAllA %d %d (dfsHA %s) = true := by\n  native_decide\n\n"
                        "end QECChecks.%s\n" % (j, s, cnt, args, name))
            mods.append("D%d" % j)
            j += 1
    else:
        # one module per (height, range of first steps): dfsHA = all first steps of dfsTopA (8 candidates)
        j = 0
        for h0 in ["bigH"] + [str(s) for s in range(top)]:
            pb = [8 * t // split for t in range(split + 1)]
            for t in range(split):
                with open(os.path.join(cdir, "D%d.lean" % j), "w") as f:
                    f.write(hdr)
                    f.write("/-- Start completeness from the height %s, first steps %d..%d, augmented certificate "
                            "%s. -/\n" % (h0, pb[t], pb[t + 1] - 1, name))
                    f.write("theorem dfs%d : (List.range' %d %d).all (dfsTopA %s %s) = true := by\n  native_decide\n\n"
                            "end QECChecks.%s\n" % (j, pb[t], pb[t + 1] - pb[t], args, h0, name))
                mods.append("D%d" % j)
                j += 1
    ndfs = j
    if dfsHi < n:
        bq = [nb * t // ncons for t in range(ncons + 1)]
        for t in range(ncons):
            with open(os.path.join(cdir, "Q%d.lean" % t), "w") as f:
                f.write(hdr)
                f.write("/-- Near consistency for the heights %d..%d, bulk states %d..%d, augmented certificate %s. "
                        "-/\n" % (dfsHi, n - 1, bq[t], bq[t + 1] - 1, name))
                f.write("theorem cons%d : consistOKA %s %d %d %d = true := by\n  native_decide\n\n"
                        "end QECChecks.%s\n" % (t, args, dfsHi, bq[t], bq[t + 1], name))
            mods.append("Q%d" % t)
    with open(os.path.join(cdir, "S.lean"), "w") as f:
        f.write(hdr)
        f.write("/-- The sizes of augmented certificate %s. -/\n" % name)
        f.write("theorem sizes : nk%s.size = %d ∧ nG%s.size = %d ∧ bk%s.size = %d ∧ bH%s.size = %d := by\n"
                "  native_decide\n\n" % (name, nn, name, nn, name, nb, name, nb))
        f.write("/-- The start bounds (every first-vertex height), augmented certificate %s. -/\n" % name)
        f.write("theorem start : startOKA %s = true := by\n  native_decide\n\nend QECChecks.%s\n" % (args, name))
    mods.append("S")
    with open(os.path.join(cdir, "LIST.txt"), "w") as f:
        f.write("\n".join(mods) + "\n")
    print(json.dumps(dict(name=name, M=M, K=K, HC=HC, hN=hN, dfsHi=dfsHi, near=nn, bulk=nb, Hmin=Hmin, K0=float(K0),
                          K0n=K0num, K0d=K0den, wE=wE, wC=wC, Q=Q, key_hex=kw, data_chunks=len(chunks),
                          near_chunks=nnear, if_chunks=nif, bulk_chunks=nbulk, dfs_modules=ndfs,
                          cons_modules=(ncons if dfsHi < n else 0),
                          start_by_height=[float(Fraction((wE + wC) ** 2 * s, Hmin * Q ** (K + 2))) for s in S],
                          sha256={ext: sha256(pre + "." + ext) for ext in ("json", "near_keys", "aug_H",
                                                                            "bulk_states")})))


main()
