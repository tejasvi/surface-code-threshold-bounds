"""mkseam.py: Lean data and check modules for one seam certificate of the toric code (untrusted generator; Lean
checks everything).

usage: python3 -I -B gen/mkseam.py NAME PREFIX K0DEN NEARCHUNKS BULKCHUNKS OFFS_PER_DFS [RECS_PER_DATA_CHUNK
       [OFFS_PER_START]]

Reads the outputs of the certificate generator tm2d_seam (PREFIX.json, PREFIX.near_keys, PREFIX.seam_H, PREFIX.bulk_states):
  near_keys    uint64 little endian, sorted: step i in bits 2i, 2i+1; label i (C = 1) in bit 32 + i; head offset o
               as (o + 1024) << 48
  seam_H       int64 little endian: G of the near states (near_keys order), then H_bulk three times
  bulk_states  one line per bulk state: K step digits, a space, K labels E/C (H_bulk order)
Writes, relative to the project root (the current directory):
  QECCountComp/Data/NAME/C<j>.lean   hex records (10 digits key, 13 digits potential): near records, then bulk ones
  QECCountComp/Data/NAME.lean        nkNAME, nGNAME (near), bkNAME, bHNAME (bulk), PNAME : ParamsT
  QEC/Checks/NAME/N<j>.lean          near rows of a range of near states (native_decide)
  QEC/Checks/NAME/B<j>.lean          bulk rows (offsets bigO, HC, -HC-1) of a range of bulk states
  QEC/Checks/NAME/D<j>.lean          start completeness from a range of offsets (D0: offset bigO)
  QEC/Checks/NAME/S.lean             sizes, and the start bound from the offset bigO
  QEC/Checks/NAME/S<j>.lean          the start bound from a range of near offsets
  QEC/Checks/NAME/LIST.txt           the check modules, for scripts/run_checks.sh
and prints a JSON summary (input sha256, counts, Hmin, start constants, the chosen bound K0n/K0d).
Keys: pattern key = digits 2*step + label in base 8, first step most significant (Core.keyOf 2); near key =
pattern key * 4096 + (o + 2048) (SeamC.nearKey); records sorted by key.
"""
import hashlib
import json
import os
import struct
import sys
from fractions import Fraction

BIGO = 1000000


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def rat(s):
    """tm2d_seam's decimal parser: digits with an optional point, no reduction."""
    num, den, fr = 0, 1, False
    for ch in s:
        if ch == ".":
            fr = True
            continue
        num = num * 10 + int(ch)
        if fr:
            den *= 10
    return num, den


def keyof(steps, labs):
    k = 0
    for d, l in zip(steps, labs):
        k = k * 8 + 2 * d + l
    return k


def xdisp(steps):
    return sum(1 if d == 0 else -1 if d == 1 else 0 for d in steps)


def main():
    a = sys.argv[1:]
    name, pre = a[0], a[1]
    K0den, nnear, nbulk, offper = int(a[2]), int(a[3]), int(a[4]), int(a[5])
    per = int(a[6]) if len(a) > 6 else 400000
    startper = int(a[7]) if len(a) > 7 else 1000
    js = json.load(open(pre + ".json"))
    M, HC, L0 = js["M"], js["HC"], js["L0"]
    K = M - 1
    assert HC == K + M + 1 and L0 == 4 * M * (HC + M) + 1 and js["verdict"] == "ALL ROWS HOLD"
    Pn, Pd = rat(js["p"])
    Xn, Xd = rat(js["X"])
    Ln, Ld = rat(js["lam"])
    nn, nb = js["near_states"], js["bulk_states"]
    rawk = open(pre + ".near_keys", "rb").read()
    assert len(rawk) == 8 * nn
    nkeys = struct.unpack("<%dQ" % nn, rawk)
    rawh = open(pre + ".seam_H", "rb").read()
    assert len(rawh) == 8 * (nn + 3 * nb)
    Hall = struct.unpack("<%dq" % (nn + 3 * nb), rawh)
    G, Hb = Hall[:nn], Hall[nn:nn + nb]
    assert Hall[nn + nb:nn + 2 * nb] == Hb and Hall[nn + 2 * nb:] == Hb
    near = []
    for u, g in zip(nkeys, G):
        steps = [(u >> (2 * i)) & 3 for i in range(K)]
        labs = [(u >> (32 + i)) & 1 for i in range(K)]
        o = (u >> 48) - 1024
        assert u & ~((1 << 48) - 1) == (o + 1024) << 48 and all(((u >> b) & 1) == 0 for b in range(2 * K, 32))
        assert all(((u >> b) & 1) == 0 for b in range(32 + K, 48)) and -HC <= o < HC
        near.append((keyof(steps, labs) * 4096 + (o + 2048), g, steps, labs, o))
    bulk = []
    with open(pre + ".bulk_states") as f:
        lines = [ln.split() for ln in f if ln.strip()]
    assert len(lines) == nb
    for (ds, ls), h in zip(lines, Hb):
        assert len(ds) == K and len(ls) == K and set(ls) <= set("EC")
        steps = [int(d) for d in ds]
        labs = [1 if l == "C" else 0 for l in ls]
        bulk.append((keyof(steps, labs), h, steps, labs))
    near.sort(key=lambda r: r[0])
    bulk.sort(key=lambda r: r[0])
    assert all(near[i][0] < near[i + 1][0] for i in range(nn - 1)), "duplicate near keys"
    assert all(bulk[i][0] < bulk[i + 1][0] for i in range(nb - 1)), "duplicate bulk keys"
    assert all(r[0] < 16 ** 10 and 1 <= r[1] < 16 ** 13 for r in near + bulk)
    Hmin = min(min(r[1] for r in near), min(r[1] for r in bulk))
    assert Hmin == js["H_min"]
    wE, wC, Q = Pn * Xn * Xn, (Pd - Pn) * Xd * Xd, Pd * Xd * Xn
    # start sums by first-vertex offset o0 (near offsets -HC-K .. HC+K-1, and bigO)
    wpow = [wE ** (K - c) * wC ** c for c in range(K + 1)]
    offs = list(range(-HC - K, HC + K)) + [BIGO]
    S = {o0: 0 for o0 in offs}
    for r in near:
        o0 = r[4] - xdisp(r[2])
        S[o0] += wpow[sum(r[3])] * r[1]
    for r in bulk:
        wh = wpow[sum(r[3])] * r[1]
        dx = xdisp(r[2])
        for o0 in offs:
            oh = o0 + dx
            if not (-HC <= oh < HC):
                S[o0] += wh
    K0 = max(Fraction((wE + wC) * S[o0], Hmin * Q ** (K + 1)) for o0 in offs)
    K0num = -((-K0.numerator * K0den) // K0.denominator)
    for o0 in offs:
        assert (wE + wC) * S[o0] * K0den <= K0num * Hmin * Q ** (K + 1)
    # data chunks: near records then bulk records
    recs = ["%010x%013x" % (r[0], r[1]) for r in near]
    nchunk_n = (nn + per - 1) // per
    recb = ["%010x%013x" % (r[0], r[1]) for r in bulk]
    nchunk_b = (nb + per - 1) // per
    ddir = os.path.join("QECCountComp", "Data", name)
    os.makedirs(ddir, exist_ok=True)
    chunks = []
    for kind, rs, nch in (("near", recs, nchunk_n), ("bulk", recb, nchunk_b)):
        for j in range(nch):
            lo, hi = j * per, min(len(rs), (j + 1) * per)
            cid = len(chunks)
            with open(os.path.join(ddir, "C%d.lean" % cid), "w") as f:
                f.write("-- Generated by gen/mkseam.py: seam certificate %s, %s records %d..%d (10 hex digits key, "
                        "13 hex digits potential).\n" % (name, kind, lo, hi - 1))
                f.write("namespace QECComp.Data.%s\n\n" % name)
                f.write("/-- The %s records %d..%d of seam certificate %s. -/\n" % (kind, lo, hi - 1, name))
                f.write("def c%d : String := \"%s\"\n\nend QECComp.Data.%s\n" % (cid, "".join(rs[lo:hi]), name))
            chunks.append((kind, cid))
    cn = ", ".join("%s.c%d" % (name, c) for k, c in chunks if k == "near")
    cb = ", ".join("%s.c%d" % (name, c) for k, c in chunks if k == "bulk")
    with open(os.path.join("QECCountComp", "Data", name + ".lean"), "w") as f:
        f.write("import QECCountComp.SeamC\nimport QECCountComp.SeamLoad\n")
        for k, c in chunks:
            f.write("import QECCountComp.Data.%s.C%d\n" % (name, c))
        f.write("\n/-!\n# Seam certificate %s (generated by gen/mkseam.py)\n\n" % name)
        for ext in ("json", "near_keys", "seam_H", "bulk_states"):
            f.write("- `%s.%s`, sha256 `%s`\n" % (os.path.basename(pre), ext, sha256(pre + "." + ext)))
        f.write("- M = %d (memory K = %d), HC = %d, L0 = %d; %d near states, %d bulk states\n" % (M, K, HC, L0, nn, nb))
        f.write("- p** = %d/%d, X = %d/%d, lambda = %d/%d, Hmin = %d\n" % (Pn, Pd, Xn, Xd, Ln, Ld, Hmin))
        f.write("- start constant %.10g <= %d/%d (maximum over the first-vertex offsets)\n-/\n\n" % (
            float(K0), K0num, K0den))
        f.write("namespace QECComp.Data\n\n")
        f.write("/-- The near records of seam certificate %s. -/\n" % name)
        f.write("def ldn%s : Array Nat × Array Nat := loadDataW 10 13 [%s]\n\n" % (name, cn))
        f.write("/-- The bulk records of seam certificate %s. -/\n" % name)
        f.write("def ldb%s : Array Nat × Array Nat := loadDataW 10 13 [%s]\n\n" % (name, cb))
        f.write("/-- The near keys of seam certificate %s. -/\ndef nk%s : Array Nat := ldn%s.1\n\n" % (name, name, name))
        f.write("/-- The near potentials of seam certificate %s. -/\ndef nG%s : Array Nat := ldn%s.2\n\n" % (
            name, name, name))
        f.write("/-- The bulk keys of seam certificate %s. -/\ndef bk%s : Array Nat := ldb%s.1\n\n" % (name, name, name))
        f.write("/-- The bulk potentials of seam certificate %s. -/\ndef bH%s : Array Nat := ldb%s.2\n\n" % (
            name, name, name))
        f.write("/-- The parameters of seam certificate %s. -/\n" % name)
        f.write("def P%s : ParamsT where\n  K := %d\n  HC := %d\n  L0 := %d\n  wE := %d\n  wC := %d\n  Q := %d\n"
                "  lamN := %d\n  lamD := %d\n  Hmin := %d\n  K0n := %d\n  K0d := %d\n\n" % (
                    name, K, HC, L0, wE, wC, Q, Ln, Ld, Hmin, K0num, K0den))
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
            f.write("/-- Rows of the near states %d..%d of seam certificate %s. -/\n" % (bn[j], bn[j + 1] - 1, name))
            f.write("theorem near%d : nearRowsOK %s %d %d = true := by\n  native_decide\n\nend QECChecks.%s\n" % (
                j, args, bn[j], bn[j + 1], name))
        mods.append("N%d" % j)
    bb = [nb * j // nbulk for j in range(nbulk + 1)]
    for j in range(nbulk):
        with open(os.path.join(cdir, "B%d.lean" % j), "w") as f:
            f.write(hdr)
            f.write("/-- Rows (offsets bigO, HC, -HC - 1) of the bulk states %d..%d of seam certificate %s. -/\n" % (
                bb[j], bb[j + 1] - 1, name))
            f.write("theorem bulk%d : bulkRowsOK %s %d %d = true := by\n  native_decide\n\nend QECChecks.%s\n" % (
                j, args, bb[j], bb[j + 1], name))
        mods.append("B%d" % j)
    with open(os.path.join(cdir, "D0.lean"), "w") as f:
        f.write(hdr)
        f.write("/-- Start completeness from the offset bigO, seam certificate %s. -/\n" % name)
        f.write("theorem dfs0 : dfsOffT %s bigO = true := by\n  native_decide\n\nend QECChecks.%s\n" % (args, name))
    mods.append("D0")
    lo0, nofs = -HC - K, 2 * (HC + K)
    j = 1
    for s in range(0, nofs, offper):
        cnt = min(offper, nofs - s)
        with open(os.path.join(cdir, "D%d.lean" % j), "w") as f:
            f.write(hdr)
            f.write("/-- Start completeness from the offsets %d..%d, seam certificate %s. -/\n" % (
                lo0 + s, lo0 + s + cnt - 1, name))
            f.write("theorem dfs%d : rangeAllT (%d) %d (dfsOffT %s) = true := by\n  native_decide\n\n"
                    "end QECChecks.%s\n" % (j, lo0 + s, cnt, args, name))
        mods.append("D%d" % j)
        j += 1
    ndfs = j
    with open(os.path.join(cdir, "S.lean"), "w") as f:
        f.write(hdr)
        f.write("/-- The sizes of seam certificate %s. -/\n" % name)
        f.write("theorem sizes : nk%s.size = %d ∧ nG%s.size = %d ∧ bk%s.size = %d ∧ bH%s.size = %d := by\n"
                "  native_decide\n\n" % (name, nn, name, nn, name, nb, name, nb))
        f.write("/-- The start bound from the offset bigO, seam certificate %s. -/\n" % name)
        f.write("theorem startBig : startOKT %s bigO = true := by\n  native_decide\n\nend QECChecks.%s\n" % (
            args, name))
    mods.append("S")
    j = 1
    for s in range(0, nofs, startper):
        cnt = min(startper, nofs - s)
        with open(os.path.join(cdir, "S%d.lean" % j), "w") as f:
            f.write(hdr)
            f.write("/-- The start bound from the offsets %d..%d, seam certificate %s. -/\n" % (
                lo0 + s, lo0 + s + cnt - 1, name))
            f.write("theorem start%d : rangeAllT (%d) %d (startOKT %s) = true := by\n  native_decide\n\n"
                    "end QECChecks.%s\n" % (j, lo0 + s, cnt, args, name))
        mods.append("S%d" % j)
        j += 1
    with open(os.path.join(cdir, "LIST.txt"), "w") as f:
        f.write("\n".join(mods) + "\n")
    print(json.dumps(dict(name=name, M=M, K=K, HC=HC, L0=L0, near=nn, bulk=nb, Hmin=Hmin, K0=float(K0), K0n=K0num,
                          K0d=K0den, wE=wE, wC=wC, Q=Q, data_chunks=len(chunks), near_chunks=nnear, bulk_chunks=nbulk,
                          dfs_modules=ndfs, start_modules=j, start_by_offset={str(o): float(Fraction((wE + wC) * S[o], Hmin * Q ** (K + 1)))
                                                          for o in offs},
                          sha256={ext: sha256(pre + "." + ext) for ext in ("json", "near_keys", "seam_H",
                                                                            "bulk_states")})))


main()
