"""mkseam2.py: streaming version of gen/mkseam.py for large seam certificates (~10^8 near states; untrusted
generator, Lean checks everything). Same outputs and module layout as mkseam.py, plus @[noinline] on the data chunks
(so the loader module's compiled code does not copy the string literals).

usage: python3 -I -B gen/mkseam2.py NAME PREFIX K0DEN NEARCHUNKS BULKCHUNKS OFFS_PER_DFS RECS_PER_DATA_CHUNK
       OFFS_PER_START TMPDIR

The near records are re-keyed (SeamC.nearKey = keyOf 2 sigma * 4096 + (o + 2048)) and sorted by an external merge
sort: runs of 8M records sorted in memory and written to TMPDIR (which must not exist yet; it is created, and the run
files are removed one by one at the end), then merged with heapq.merge.
"""
import hashlib
import heapq
import json
import os
import struct
import sys
from fractions import Fraction

BIGO = 1000000
RUN = 8_000_000


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for blk in iter(lambda: f.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def rat(s):
    num, den, fr = 0, 1, False
    for ch in s:
        if ch == ".":
            fr = True
            continue
        num = num * 10 + int(ch)
        if fr:
            den *= 10
    return num, den


def make_run(job):
    """One run of the external sort: decode records start..start+cnt-1 (tables for the step and label bits), write
    them sorted by near key to TMPDIR/run<r>.txt, and return the path, the sums of G by (x-displacement, number of
    C labels, head offset) for the start sums, and the least G."""
    pre, tmpdir, r, start, cnt, K, HC = job
    nsb = 1 << (2 * K)
    TS, DX = [0] * nsb, [0] * nsb
    for s in range(nsb):
        k = dx = 0
        for i in range(K):
            d = (s >> (2 * i)) & 3
            k = k * 8 + 2 * d
            dx += 1 if d == 0 else -1 if d == 1 else 0
        TS[s], DX[s] = k, dx
    nlb = 1 << K
    TL, NC = [0] * nlb, [0] * nlb
    for l in range(nlb):
        k = 0
        for i in range(K):
            k = k * 8 + ((l >> i) & 1)
        TL[l], NC[l] = k, bin(l).count("1")
    with open(pre + ".near_keys", "rb") as fk:
        fk.seek(8 * start)
        ks = struct.unpack("<%dQ" % cnt, fk.read(8 * cnt))
    with open(pre + ".seam_H", "rb") as fh:
        fh.seek(8 * start)
        gs = struct.unpack("<%dq" % cnt, fh.read(8 * cnt))
    ms, ml = nsb - 1, nlb - 1
    recs = []
    sums = {}
    hmin = None
    for u, g in zip(ks, gs):
        s, l, o = u & ms, (u >> 32) & ml, (u >> 48) - 1024
        assert -HC <= o < HC and (u >> (2 * K)) & 0x3FFF == 0 and (u >> (32 + K)) & 0xFFFF >> K == 0
        recs.append(((TS[s] + TL[l]) * 4096 + o + 2048, g))
        t = (DX[s], NC[l], o)
        sums[t] = sums.get(t, 0) + g
        if hmin is None or g < hmin:
            hmin = g
    recs.sort()
    rp = os.path.join(tmpdir, "run%d.txt" % r)
    with open(rp, "w") as f:
        f.write("".join("%010x%013x\n" % x for x in recs))
    return rp, sums, hmin


def main():
    a = sys.argv[1:]
    name, pre = a[0], a[1]
    K0den, nnear, nbulk, offper, per, startper = (int(x) for x in a[2:8])
    tmpdir = a[8]
    js = json.load(open(pre + ".json"))
    M, HC, L0 = js["M"], js["HC"], js["L0"]
    K = M - 1
    assert HC == K + M + 1 and L0 == 4 * M * (HC + M) + 1 and js["verdict"] == "ALL ROWS HOLD"
    Pn, Pd = rat(js["p"])
    Xn, Xd = rat(js["X"])
    Ln, Ld = rat(js["lam"])
    nn, nb = js["near_states"], js["bulk_states"]
    assert os.path.getsize(pre + ".near_keys") == 8 * nn
    assert os.path.getsize(pre + ".seam_H") == 8 * (nn + 3 * nb)
    wE, wC, Q = Pn * Xn * Xn, (Pd - Pn) * Xd * Xd, Pd * Xd * Xn
    wpow = [wE ** (K - c) * wC ** c for c in range(K + 1)]
    offs = list(range(-HC - K, HC + K))
    S = {o0: 0 for o0 in offs + [BIGO]}
    # digit tables for the 2K low bits (steps) and K label bits: keyOf digit i (first step most significant)
    os.makedirs(tmpdir)
    nruns = (nn + RUN - 1) // RUN
    jobs = [(pre, tmpdir, r, r * RUN, min(RUN, nn - r * RUN), K, HC) for r in range(nruns)]
    nproc = int(os.environ.get("NPROC", "1"))
    if nproc > 1:
        import multiprocessing
        with multiprocessing.Pool(nproc) as pool:
            results = pool.map(make_run, jobs)
    else:
        results = [make_run(j) for j in jobs]
    runs = [r[0] for r in results]
    hmin = min(r[2] for r in results)
    for r in results:
        for (dx, nc, o), g in r[1].items():
            S[o - dx] += wpow[nc] * g
    # bulk states (H_bulk follows the near potentials in seam_H)
    fh = open(pre + ".seam_H", "rb")
    fh.seek(8 * nn)
    Hb = struct.unpack("<%dq" % nb, fh.read(8 * nb))
    fh.close()
    bulk = []
    totdx = {}
    with open(pre + ".bulk_states") as f:
        for ln, h in zip(f, Hb):
            ds, ls = ln.split()
            k = 0
            dx = 0
            for d, l in zip(ds, ls):
                d = int(d)
                k = k * 8 + 2 * d + (1 if l == "C" else 0)
                dx += 1 if d == 0 else -1 if d == 1 else 0
            bulk.append((k, h))
            totdx[dx] = totdx.get(dx, 0) + wpow[ls.count("C")] * h
            if h < hmin:
                hmin = h
    assert len(bulk) == nb
    bulk.sort()
    assert all(bulk[i][0] < bulk[i + 1][0] for i in range(nb - 1)), "duplicate bulk keys"
    for o0 in offs + [BIGO]:
        for dx, t in totdx.items():
            oh = o0 + dx
            if not (-HC <= oh < HC):
                S[o0] += t
    assert hmin == js["H_min"]
    K0 = max(Fraction((wE + wC) * S[o0], hmin * Q ** (K + 1)) for o0 in offs + [BIGO])
    K0num = -((-K0.numerator * K0den) // K0.denominator)
    for o0 in offs + [BIGO]:
        assert (wE + wC) * S[o0] * K0den <= K0num * hmin * Q ** (K + 1)
    # merge the runs into the near data chunks
    ddir = os.path.join("QECCountComp", "Data", name)
    os.makedirs(ddir, exist_ok=True)
    chunks = []

    def write_chunk(kind, lo, body):
        cid = len(chunks)
        hi = lo + len(body) // 23
        with open(os.path.join(ddir, "C%d.lean" % cid), "w") as f:
            f.write("-- Generated by gen/mkseam2.py: seam certificate %s, %s records %d..%d (10 hex digits key, "
                    "13 hex digits potential).\n" % (name, kind, lo, hi - 1))
            f.write("namespace QECComp.Data.%s\n\n" % name)
            f.write("/-- The %s records %d..%d of seam certificate %s. -/\n" % (kind, lo, hi - 1, name))
            f.write("@[noinline] def c%d : String := \"%s\"\n\nend QECComp.Data.%s\n" % (cid, body, name))
        chunks.append((kind, cid))

    files = [open(rp) for rp in runs]
    buf, lo, n, prev = [], 0, 0, -1
    for line in heapq.merge(*files):
        key = int(line[:10], 16)
        assert key > prev, "duplicate or unsorted near keys"
        prev = key
        buf.append(line[:23])
        n += 1
        if len(buf) == per:
            write_chunk("near", lo, "".join(buf))
            lo += len(buf)
            buf = []
    if buf:
        write_chunk("near", lo, "".join(buf))
    for f in files:
        f.close()
    assert n == nn
    for rp in runs:
        os.remove(rp)
    os.rmdir(tmpdir)
    recb = ["%010x%013x" % r for r in bulk]
    for j in range(0, nb, per):
        write_chunk("bulk", j, "".join(recb[j:j + per]))
    cn = ", ".join("%s.c%d" % (name, c) for k, c in chunks if k == "near")
    cb = ", ".join("%s.c%d" % (name, c) for k, c in chunks if k == "bulk")
    with open(os.path.join("QECCountComp", "Data", name + ".lean"), "w") as f:
        f.write("import QECCountComp.SeamC\nimport QECCountComp.SeamLoad\n")
        for k, c in chunks:
            f.write("import QECCountComp.Data.%s.C%d\n" % (name, c))
        f.write("\n/-!\n# Seam certificate %s (generated by gen/mkseam2.py)\n\n" % name)
        for ext in ("json", "near_keys", "seam_H", "bulk_states"):
            f.write("- `%s.%s`, sha256 `%s`\n" % (os.path.basename(pre), ext, sha256(pre + "." + ext)))
        f.write("- M = %d (memory K = %d), HC = %d, L0 = %d; %d near states, %d bulk states\n" % (M, K, HC, L0, nn, nb))
        f.write("- p** = %d/%d, X = %d/%d, lambda = %d/%d, Hmin = %d\n" % (Pn, Pd, Xn, Xd, Ln, Ld, hmin))
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
                    name, K, HC, L0, wE, wC, Q, Ln, Ld, hmin, K0num, K0den))
        f.write("end QECComp.Data\n")
    # check modules (as gen/mkseam.py)
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
    print(json.dumps(dict(name=name, M=M, K=K, HC=HC, L0=L0, near=nn, bulk=nb, Hmin=hmin, K0=float(K0), K0n=K0num,
                          K0d=K0den, wE=wE, wC=wC, Q=Q, data_chunks=len(chunks), near_chunks=nnear, bulk_chunks=nbulk,
                          dfs_modules=ndfs, start_modules=j,
                          sha256={ext: sha256(pre + "." + ext) for ext in ("json", "near_keys", "seam_H",
                                                                            "bulk_states")})))


main()
