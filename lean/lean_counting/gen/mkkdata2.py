"""mkkdata2.py: kernel-route (version 2) data and check modules for one certificate (untrusted generator; Lean checks
everything). Unlike gen/mkkdata.py, every check walks one named subtree only (QECCountComp/Kern2.lean), so it scales
to millions of states.

usage: python3 -I -B gen/mkkdata2.py NAME STATES HFILE TRANS n K c1,c2,.. Pn Pd Xn Xd Ln Ld K0DEN DFSDEPTH
       [SUBS_PER_ROWMODULE [PREFIXES_PER_DFSMODULE [IROWS_PER_MODULE]]]

The listed states (keys ascending) form a binary search tree: subtrees of at most 512 entries are constants
NAME.t<j> (QECCountComp/KData/NAME/T<i>.lean, 40 per file); every internal node above them is a constant NAME.u<j>
(QECCountComp/KData/NAME/U.lean); tNAME = the root. mask bit i: as in mkkdata.py. Check modules (QEC/KChecks/NAME/):
  R<j>.lean   rows and totals of subtrees: `KTree.allE (rowCheckK P t) NAME.t<i> = true`, `totK P NAME.t<i> = [..]`
  I<j>.lean   rows of internal-node entries: `rowCheckK P t (k, h, m) = true`
  D<j>.lean   start completeness by prefixes of DFSDEPTH candidate indices: `dfsPreK P t [j1, ..] [] = true`
  LIST.txt    these modules
and writes QEC/KChecks/NAME/tree.json (the internal nodes and their children, for gen/mkkall2.py).
"""
import hashlib
import json
import os
import struct
import sys
from fractions import Fraction
from itertools import product


def walk_ok(steps, n):
    p = [0] * n
    seen = {tuple(p)}
    for d in steps:
        q = list(p)
        q[d // 2] += 1 if d % 2 == 0 else -1
        t = tuple(q)
        if t in seen:
            return False
        seen.add(t)
        p = q
    return True


def main():
    a = sys.argv[1:]
    name, sfile, hfile, tfile = a[0], a[1], a[2], a[3]
    n, K = int(a[4]), int(a[5])
    c = [int(x) for x in a[6].split(",")]
    Pn, Pd, Xn, Xd, Ln, Ld = (int(x) for x in a[7:13])
    K0den, depth = int(a[13]), int(a[14])
    subs_per = int(a[15]) if len(a) > 15 else 1
    pre_per = int(a[16]) if len(a) > 16 else 1
    irow_per = int(a[17]) if len(a) > 17 else 200
    B = 4 * n
    pats, keys, nCs = [], [], []
    for line in open(sfile):
        line = line.strip()
        if not line:
            continue
        ds, ls = line.split()
        p = [(int(d), l == "C") for d, l in zip(ds, ls)]
        k = 0
        for d, l in p:
            k = k * B + 2 * d + (1 if l else 0)
        pats.append(p)
        keys.append(k)
        nCs.append(ls.count("C"))
    N = len(keys)
    assert all(keys[i] < keys[i + 1] for i in range(N - 1))
    H = list(struct.unpack("<%dq" % N, open(hfile, "rb").read()))
    idx = {k: i for i, k in enumerate(keys)}
    incl = [0] * N
    cand = [(d, l) for d in range(2 * n) for l in (False, True)]
    cidx = {x: j for j, x in enumerate(cand)}
    raw = open(tfile, "rb").read()
    for r in range(len(raw) // 9):
        fr, to, isE = struct.unpack_from("<iiB", raw, 9 * r)
        d, l = pats[to][-1]
        assert l == (isE == 0)
        incl[fr] |= 1 << cidx[(d, l)]
    masks = []
    nmask = 0
    for i in range(N):
        m = 0
        for j, x in enumerate(cand):
            u = pats[i] + [x]
            if not walk_ok([y[0] for y in u], n):
                assert not (incl[i] >> j) & 1
                continue
            tk = 0
            for d, l in u[1:]:
                tk = tk * B + 2 * d + (1 if l else 0)
            if tk in idx:
                if not (incl[i] >> j) & 1:
                    m |= 1 << j
                    nmask += 1
            else:
                assert not (incl[i] >> j) & 1
        masks.append(m)
    Hmin = min(H)
    wE, wC, Q = Pn * Xn * Xn, (Pd - Pn) * Xd * Xd, Pd * Xd * Xn
    tot = [0] * (K + 1)
    for h, nc in zip(H, nCs):
        tot[nc] += h
    S = sum(tot[cc] * wE ** (K - cc) * wC ** cc for cc in range(K + 1))
    K0 = Fraction((wE + wC) ** 2 * S, Hmin * Q ** (K + 2))
    K0num = -((-K0.numerator * K0den) // K0.denominator)

    def lit(x):
        return "(nat_lit %d)" % x

    def full(lo, hi):
        if lo >= hi:
            return "KTree.leaf"
        mid = (lo + hi) // 2
        return "(KTree.node %s %s %s %s %s)" % (full(lo, mid), lit(keys[mid]), lit(H[mid]), lit(masks[mid]),
                                               full(mid + 1, hi))

    subs = []      # (lo, hi): subtree constants t<j>
    inner = []     # dicts: j, mid, left, right (refs "t<j>" or "u<j>"), level
    sys.setrecursionlimit(10000)

    def build(lo, hi):
        if hi - lo <= 512:
            subs.append((lo, hi))
            return "t%d" % (len(subs) - 1), 0
        mid = (lo + hi) // 2
        lref, llev = build(lo, mid)
        rref, rlev = build(mid + 1, hi)
        inner.append(dict(j=len(inner), mid=mid, left=lref, right=rref, level=max(llev, rlev) + 1))
        return "u%d" % (len(inner) - 1), max(llev, rlev) + 1

    root, _ = build(0, N)
    ddir = os.path.join("QECCountComp", "KData", name)
    os.makedirs(ddir, exist_ok=True)
    per = 40
    nT = (len(subs) + per - 1) // per
    for f_ in range(nT):
        with open(os.path.join(ddir, "T%d.lean" % f_), "w") as f:
            f.write("import QECCountComp.Kern2\n-- Generated by gen/mkkdata2.py: subtrees of certificate %s.\n" % name)
            f.write("namespace QECComp.KData.%s\n\n" % name)
            for j in range(f_ * per, min(len(subs), (f_ + 1) * per)):
                lo, hi = subs[j]
                f.write("/-- Entries %d..%d of certificate %s. -/\ndef t%d : KTree :=\n  %s\n\n" % (
                    lo, hi - 1, name, j, full(lo, hi)))
            f.write("end QECComp.KData.%s\n" % name)
    with open(os.path.join(ddir, "U.lean"), "w") as f:
        for f_ in range(nT):
            f.write("import QECCountComp.KData.%s.T%d\n" % (name, f_))
        f.write("-- Generated by gen/mkkdata2.py: internal nodes of certificate %s (children first).\n" % name)
        f.write("namespace QECComp.KData.%s\n\n" % name)
        for nd in inner:
            m = nd["mid"]
            f.write("/-- Internal node %d of certificate %s (entry %d). -/\ndef u%d : KTree :=\n  KTree.node %s %s %s %s %s\n\n"
                    % (nd["j"], name, m, nd["j"], nd["left"], lit(keys[m]), lit(H[m]), lit(masks[m]), nd["right"]))
        f.write("end QECComp.KData.%s\n" % name)
    with open(os.path.join("QECCountComp", "KData", name + ".lean"), "w") as f:
        f.write("import QECCountComp.KData.%s.U\n" % name)
        f.write("\n/-!\n# Certificate %s, kernel form, version 2 (generated by gen/mkkdata2.py)\n\n" % name)
        f.write("%d states (%d subtrees, %d internal nodes), K = %d, p** = %d/%d, X = %d/%d, lambda = %d/%d, Hmin = %d,\n"
                % (N, len(subs), len(inner), K, Pn, Pd, Xn, Xd, Ln, Ld, Hmin))
        f.write("start constant %.8f <= %d/%d; %d mask bits (claimed exclusions of full windows).\n\n" % (
            float(K0), K0num, K0den, nmask))
        for path in (sfile, hfile, tfile):
            h_ = hashlib.sha256()
            with open(path, "rb") as g:
                for blk in iter(lambda: g.read(1 << 20), b""):
                    h_.update(blk)
            f.write("- `%s`, sha256 `%s`\n" % (os.path.basename(path), h_.hexdigest()))
        f.write("-/\n\nnamespace QECComp.KData\n\n")
        f.write("/-- The listed states of certificate %s. -/\ndef t%s : KTree := %s.%s\n\n" % (name, name, name, root))
        f.write("/-- The parameters of certificate %s. -/\n" % name)
        f.write("def P%s : Params where\n  n := %d\n  c := [%s]\n  K := %d\n  wE := %d\n  wC := %d\n  Q := %d\n"
                "  lamN := %d\n  lamD := %d\n  Hmin := %d\n  K0n := %d\n  K0d := %d\n\nend QECComp.KData\n" % (
                    name, n, ", ".join(str(x) for x in c), K, wE, wC, Q, Ln, Ld, Hmin, K0num, K0den))
    # totals per subtree (for the R modules and the assembly)
    subtot = []
    for lo, hi in subs:
        t_ = [0] * (K + 1)
        for i in range(lo, hi):
            t_[nCs[i]] += H[i]
        subtot.append(t_)
    cdir = os.path.join("QEC", "KChecks", name)
    os.makedirs(cdir, exist_ok=True)
    hdr = ("import QECCountComp.KData.%s\n\nnamespace QECKChecks.%s\n\nopen QECComp QECComp.KData\n\n"
           "set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nset_option Elab.async false\n\n" % (name, name))
    mods = []
    for r, s0 in enumerate(range(0, len(subs), subs_per)):
        with open(os.path.join(cdir, "R%d.lean" % r), "w") as f:
            f.write(hdr)
            for j in range(s0, min(len(subs), s0 + subs_per)):
                f.write("theorem rows%d : KTree.allE (rowCheckK P%s t%s) %s.t%d = true := by\n  decide +kernel\n\n" % (
                    j, name, name, name, j))
                f.write("theorem tot%d : totK P%s %s.t%d = [%s] := by\n  decide +kernel\n\n" % (
                    j, name, name, j, ", ".join(str(x) for x in subtot[j])))
            f.write("end QECKChecks.%s\n" % name)
        mods.append("R%d" % r)
    for r, s0 in enumerate(range(0, len(inner), irow_per)):
        with open(os.path.join(cdir, "I%d.lean" % r), "w") as f:
            f.write(hdr)
            for nd in inner[s0:s0 + irow_per]:
                m = nd["mid"]
                f.write("theorem irow%d : rowCheckK P%s t%s ((nat_lit %d), (nat_lit %d), (nat_lit %d)) = true := by\n"
                        "  decide +kernel\n\n" % (
                    nd["j"], name, name, keys[m], H[m], masks[m]))
            f.write("end QECKChecks.%s\n" % name)
        mods.append("I%d" % r)
    prefixes = list(product(range(4 * n), repeat=depth))
    for r, s0 in enumerate(range(0, len(prefixes), pre_per)):
        with open(os.path.join(cdir, "D%d.lean" % r), "w") as f:
            f.write(hdr)
            for js in prefixes[s0:s0 + pre_per]:
                f.write("theorem dfs_%s : dfsPreK P%s t%s [%s] [] = true := by\n  decide +kernel\n\n" % (
                    "_".join(str(x) for x in js), name, name, ", ".join(str(x) for x in js)))
            f.write("end QECKChecks.%s\n" % name)
        mods.append("D%d" % r)
    with open(os.path.join(cdir, "LIST.txt"), "w") as f:
        f.write("\n".join(mods) + "\n")
    total = [sum(subtot[j][cc] for j in range(len(subs))) + sum(H[nd["mid"]] for nd in inner if nCs[nd["mid"]] == cc)
             for cc in range(K + 1)]
    assert total == tot
    with open(os.path.join(cdir, "tree.json"), "w") as f:
        json.dump(dict(name=name, K=K, n=n, root=root, depth=depth, subs=len(subs), subs_per=subs_per,
                       pre_per=pre_per, irow_per=irow_per, nprefix=len(prefixes),
                       inner=[dict(j=nd["j"], left=nd["left"], right=nd["right"], level=nd["level"],
                                   key=keys[nd["mid"]], H=H[nd["mid"]], mask=masks[nd["mid"]],
                                   nC=nCs[nd["mid"]]) for nd in inner],
                       subtot=subtot, Pn=Pn, Pd=Pd, Xn=Xn, Xd=Xd), f)
    print(json.dumps(dict(name=name, states=N, subtrees=len(subs), internal=len(inner), T_files=nT,
                          row_modules=len(range(0, len(subs), subs_per)), irow_modules=len(range(0, len(inner), irow_per)),
                          dfs_modules=len(range(0, len(prefixes), pre_per)), prefixes=len(prefixes), K0=float(K0),
                          K0n=K0num, K0d=K0den, Hmin=Hmin, mask_bits=nmask)))


main()
