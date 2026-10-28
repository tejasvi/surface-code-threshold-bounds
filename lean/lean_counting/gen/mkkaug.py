"""mkkaug.py: kernel-route data and check modules of an augmented certificate (untrusted generator; Lean checks
everything).

usage: python3 -I -B gen/mkkaug.py NAME OUT MASKDIR DFSDEPTH [SUBS_PER_ROWMODULE [IROWS_PER_MODULE]]

Reads the compiled-evaluation data of the augmented certificate NAME (QECCountComp/Data/NAME.lean and its chunks
QECCountComp/Data/NAME/C<i>.lean: near records (ckeyA K σ h, G), bulk records (ckeyA K σ 0, Hb), ascending keys, and
the parameters PNAME : ParamsA) and the exclusion hints MASKDIR/NAME_near.txt, MASKDIR/NAME_bulk.txt (one line per
entry, from gen/MaskA.lean.in), and writes, for the kernel certificate OUT:
  QECCountComp/KData/OUT/N<i>.lean, B<i>.lean   subtrees (at most 512 entries) of the near and the bulk tree
  QECCountComp/KData/OUT/U.lean                 the internal nodes above them (children first)
  QECCountComp/KData/OUT.lean                   roots tN<OUT>, tB<OUT>, parameters P<OUT> : ParamsA, input sha256
  QEC/KChecks/OUT/RN<j>, RB<j>                  rows and start totals of subtrees
  QEC/KChecks/OUT/IN<j>, IB<j>                  rows of internal-node entries
  QEC/KChecks/OUT/E<i>_<p>                      start completeness from the height offA P i, by prefixes of
                                                DFSDEPTH candidate indices (one module per parent prefix)
  QEC/KChecks/OUT/LIST.txt, tree.json           the modules; the trees and totals for the assembly generator
"""
import hashlib
import json
import os
import re
import sys
from itertools import product

BIGH = 1000000


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as g:
        for blk in iter(lambda: g.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def read_records(name, chunks, kw, hw):
    out = []
    for c in chunks:
        i = int(c[1:])
        src = open(os.path.join("QECCountComp", "Data", name, "C%d.lean" % i)).read()
        m = re.search(r'def c%d : String := "([0-9a-f]*)"' % i, src)
        s = m.group(1)
        w = kw + hw
        assert len(s) % w == 0
        for r in range(0, len(s), w):
            out.append((int(s[r:r + kw], 16), int(s[r + kw:r + w], 16)))
    return out


def decodeA(K, k):
    return [((k // 4 ** i) % 4, (k // 4 ** K // 2 ** i) % 2 == 1) for i in range(K)]


def heightOf(K, k):
    return k // 8 ** K


def dl2(d):
    return 1 if d == 0 else -1 if d == 1 else -1 if d == 2 else 1


def vdisp(s):
    return sum(dl2(d) for d, _ in s)


def main():
    a = sys.argv[1:]
    name, out, mdir, depth = a[0], a[1], a[2], int(a[3])
    subs_per = int(a[4]) if len(a) > 4 else 1
    # CHUNK: row theorems per packed leaf (pieces of the leaf); EGRP: prefix levels per start module
    chunk = int(os.environ.get("CHUNK", "1"))
    egrp = int(os.environ.get("EGRP", "1"))
    irow_per = int(a[5]) if len(a) > 5 else 200
    agg = open(os.path.join("QECCountComp", "Data", name + ".lean")).read()
    mn = re.search(r"def ldn%s : Array Nat × Array Nat := loadDataW (\d+) (\d+) \[([^\]]*)\]" % name, agg)
    mb = re.search(r"def ldb%s : Array Nat × Array Nat := loadDataW (\d+) (\d+) \[([^\]]*)\]" % name, agg)
    kwn, hwn = int(mn.group(1)), int(mn.group(2))
    kwb, hwb = int(mb.group(1)), int(mb.group(2))
    chn = [x.strip().split(".")[1] for x in mn.group(3).split(",")]
    chb = [x.strip().split(".")[1] for x in mb.group(3).split(",")]
    par = {}
    pblock = agg[agg.index("def P%s : ParamsA where" % name):]
    fields = ["K", "HC", "hN", "wE", "wC", "Q", "lamN", "lamD", "Hmin", "K0n", "K0d"]
    for f_ in fields:
        par[f_] = int(re.search(r"\n  %s := (\d+)" % f_, pblock).group(1))
    K, HC = par["K"], par["HC"]
    near = read_records(name, chn, kwn, hwn)
    bulk = read_records(name, chb, kwb, hwb)
    assert all(near[i][0] < near[i + 1][0] for i in range(len(near) - 1))
    assert all(bulk[i][0] < bulk[i + 1][0] for i in range(len(bulk) - 1))
    mN = [int(x) for x in open(os.path.join(mdir, name + "_near.txt")).read().split()]
    mB = [int(x) for x in open(os.path.join(mdir, name + "_bulk.txt")).read().split()]
    assert len(mN) == len(near) and len(mB) == len(bulk)
    ents = {"N": [(k, h, m) for (k, h), m in zip(near, mN)], "B": [(k, h, m) for (k, h), m in zip(bulk, mB)]}
    noff = HC + K + 2

    def wt(s):
        c = sum(1 for _, l in s if l)
        return par["wE"] ** (K - c) * par["wC"] ** c

    def contrib(kind, e):
        k, h, _ = e
        s = decodeA(K, k)
        if kind == "N":
            h0 = heightOf(K, k) + vdisp(s)
            return [wt(s) * h if (i < HC + K + 1 and h0 == i) else 0 for i in range(noff)]
        r = []
        for i in range(noff):
            if i == HC + K + 1:
                r.append(wt(s) * h)
            else:
                r.append(0 if i - vdisp(s) < HC else wt(s) * h)
        return r

    def addv(x, y):
        return [p + q for p, q in zip(x, y)]

    patc = {}

    def patinfo(k):
        # (weight, vdisp) of the pattern of key k, which depends only on k mod 8^K
        q = k % 8 ** K
        r = patc.get(q)
        if r is None:
            s = decodeA(K, q)
            r = (wt(s), vdisp(s))
            patc[q] = r
        return r

    def acc_contrib(kind, e, t_):
        # t_ += contrib(kind, e); a near entry contributes at the single index h0 = h + vdisp σ (if h0 ≤ HC + K)
        k, h, _ = e
        w_, vd = patinfo(k)
        v = w_ * h
        if kind == "N":
            h0 = heightOf(K, k) + vd
            if 0 <= h0 < HC + K + 1:
                t_[h0] += v
        else:
            t_[HC + K + 1] += v
            for i in range(HC + K + 1):
                if i - vd >= HC:
                    t_[i] += v

    trees = {}
    sys.setrecursionlimit(10000)
    for kind in ("N", "B"):
        E = ents[kind]
        subs, inner = [], []

        def build(lo, hi):
            if hi - lo <= int(os.environ.get("LEAF", "512")):
                subs.append((lo, hi))
                return "%s%d" % (kind.lower() + "t", len(subs) - 1), 0
            mid = (lo + hi) // 2
            lref, llev = build(lo, mid)
            rref, rlev = build(mid + 1, hi)
            inner.append(dict(j=len(inner), mid=mid, left=lref, right=rref, level=max(llev, rlev) + 1))
            return "%s%d" % (kind.lower() + "u", len(inner) - 1), max(llev, rlev) + 1

        root, _ = build(0, len(E)) if E else ("leaf", 0)
        subtot = []
        for lo, hi in subs:
            t_ = [0] * noff
            for i in range(lo, hi):
                acc_contrib(kind, E[i], t_)
            subtot.append(t_)
        tref = {"%st%d" % (kind.lower(), j): s for j, s in enumerate(subtot)}
        for nd in inner:
            nd["tot"] = addv(addv(tref[nd["left"]], contrib(kind, E[nd["mid"]])), tref[nd["right"]])
            tref["%su%d" % (kind.lower(), nd["j"])] = nd["tot"]
        trees[kind] = dict(E=E, subs=subs, inner=inner, root=root, subtot=subtot,
                           tot=tref[root] if root != "leaf" else [0] * noff)
    totN, totB = trees["N"]["tot"], trees["B"]["tot"]
    lhs = [(par["wE"] + par["wC"]) ** 2 * (x + y) * par["K0d"] for x, y in zip(totN, totB)]
    rhs = par["K0n"] * par["Hmin"] * par["Q"] ** (K + 2)
    assert all(v <= rhs for v in lhs), "start bound fails"

    def lit(x):
        return "(nat_lit %d)" % x

    def full(E, lo, hi):
        if lo >= hi:
            return "KTree.leaf"
        mid = (lo + hi) // 2
        k, h, m = E[mid]
        return "(KTree.node %s %s %s %s %s)" % (full(E, lo, mid), lit(k), lit(h), lit(m), full(E, mid + 1, hi))

    # PACK=1: packed trees (QECCountComp/KernP.lean), one literal per leaf
    pack = os.environ.get("PACK", "0") == "1"
    mbits = {"N": 8, "B": 16}
    pw = {kind: (max([1] + [e[0] for e in ents[kind]]).bit_length(), max([1] + [e[1] for e in ents[kind]]).bit_length(),
                 mbits[kind]) for kind in ("N", "B")}
    TT = "PTree" if pack else "KTree"
    NODE = "PTree.node" if pack else "KTree.node"
    EMPTY = "(PTree.pl 0 0)" if pack else "KTree.leaf"

    def leafdef(kind, E, lo, hi):
        if not pack:
            return full(E, lo, hi)
        kb, hb, mb = pw[kind]
        W = kb + hb + mb
        x = 0
        for i, (k, h, m) in enumerate(E[lo:hi]):
            x |= ((k << (hb + mb)) | (h << mb) | m) << (W * i)
        return "PTree.pl (nat_lit %d) (nat_lit 0x%x)" % (hi - lo, x)

    ddir = os.path.join("QECCountComp", "KData", out)
    os.makedirs(ddir, exist_ok=True)
    per = 40
    files = []
    for kind in ("N", "B"):
        T = trees[kind]
        nT = (len(T["subs"]) + per - 1) // per
        for f_ in range(nT):
            fn = "%s%d" % (kind, f_)
            files.append(fn)
            with open(os.path.join(ddir, fn + ".lean"), "w") as f:
                f.write("import QECCountComp.KernA\n%s-- Generated by gen/mkkaug.py: %s subtrees of certificate %s.\n"
                        % ("import QECCountComp.KernP\n" if pack else "", "near" if kind == "N" else "bulk", out))
                f.write("namespace QECComp.KData.%s\n\n" % out)
                for j in range(f_ * per, min(len(T["subs"]), (f_ + 1) * per)):
                    lo, hi = T["subs"][j]
                    f.write("/-- %s entries %d..%d of certificate %s. -/\ndef %st%d : %s :=\n  %s\n\n" % (
                        "Near" if kind == "N" else "Bulk", lo, hi - 1, out, kind.lower(), j, TT,
                        leafdef(kind, T["E"], lo, hi)))
                f.write("end QECComp.KData.%s\n" % out)
    with open(os.path.join(ddir, "U.lean"), "w") as f:
        for fn in files:
            f.write("import QECCountComp.KData.%s.%s\n" % (out, fn))
        f.write("-- Generated by gen/mkkaug.py: internal nodes of certificate %s (children first).\n" % out)
        f.write("namespace QECComp.KData.%s\n\n" % out)
        for kind in ("N", "B"):
            T = trees[kind]
            for nd in T["inner"]:
                k, h, m = T["E"][nd["mid"]]
                f.write("/-- Internal node %d of the %s tree of certificate %s. -/\ndef %su%d : %s :=\n"
                        "  %s %s %s %s %s %s\n\n" % (nd["j"], "near" if kind == "N" else "bulk", out,
                                                     kind.lower(), nd["j"], TT, NODE, nd["left"], lit(k), lit(h),
                                                     lit(m), nd["right"]))
        f.write("end QECComp.KData.%s\n" % out)
    nmask = sum(1 for e in ents["N"] for i in range(8) if (e[2] >> i) & 1) + \
        sum(1 for e in ents["B"] for i in range(16) if (e[2] >> i) & 1)
    srcs = [os.path.join("QECCountComp", "Data", name + ".lean")] + \
        [os.path.join("QECCountComp", "Data", name, "C%d.lean" % int(c[1:])) for c in chn + chb] + \
        [os.path.join(mdir, name + "_near.txt"), os.path.join(mdir, name + "_bulk.txt")]
    with open(os.path.join("QECCountComp", "KData", out + ".lean"), "w") as f:
        f.write("import QECCountComp.KData.%s.U\n" % out)
        f.write("\n/-!\n# Augmented certificate %s, kernel form (generated by gen/mkkaug.py from the data of %s)\n\n" % (
            out, name))
        f.write("%d near states, %d bulk states (%d and %d subtrees), K = %d, HC = %d, hN = %d; %d mask bits.\n\n" % (
            len(ents["N"]), len(ents["B"]), len(trees["N"]["subs"]), len(trees["B"]["subs"]), K, HC, par["hN"], nmask))
        f.write("Inputs (the data of %s records the sha256 of its own input files):\n" % name)
        for p in srcs:
            f.write("- `%s`, sha256 `%s`\n" % (p, sha(p)))
        f.write("-/\n\nnamespace QECComp.KData\n\n")
        for kind, nm in (("N", "tN"), ("B", "tB")):
            r = trees[kind]["root"]
            f.write("/-- The %s states of certificate %s. -/\ndef %s%s : %s := %s\n\n" % (
                "near" if kind == "N" else "bulk", out, nm, out, TT, ("%s.%s" % (out, r)) if r != "leaf" else EMPTY))
            if pack:
                f.write("/-- The record widths of the %s tree of certificate %s. -/\ndef pw%s%s : PW := ⟨%d, %d, %d⟩\n\n"
                        % (("near" if kind == "N" else "bulk", out, kind, out) + pw[kind]))
        f.write("/-- The parameters of certificate %s. -/\ndef P%s : ParamsA where\n" % (out, out))
        for f_ in fields:
            f.write("  %s := %d\n" % (f_, par[f_]))
        f.write("\nend QECComp.KData\n")
    cdir = os.path.join("QEC", "KChecks", out)
    os.makedirs(cdir, exist_ok=True)
    P = "P%s" % out
    if pack:
        fN, fB = "(tN%s.find pwN%s)" % (out, out), "(tB%s.find pwB%s)" % (out, out)
        ALLE = {kind: "PTree.allE pw%s%s" % (kind, out) for kind in ("N", "B")}
        TOT = {kind: "PTree.tot pw%s%s" % (kind, out) for kind in ("N", "B")}
    else:
        fN, fB = "tN%s.find" % out, "tB%s.find" % out
        ALLE = {kind: "KTree.allE" for kind in ("N", "B")}
        TOT = {kind: "totTK" for kind in ("N", "B")}
    hdr = ("import QECCountComp.KData.%s\n\nnamespace QECKChecks.%s\n\nopen QECComp QECComp.KData\n\n"
           "set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nset_option Elab.async false\n\n" % (out, out))
    mods = []
    for kind, rowf, contf in (("N", "nearRowAK", "nearContribA"), ("B", "bulkRowAK", "bulkContribA")):
        T = trees[kind]
        for r, s0 in enumerate(range(0, len(T["subs"]), subs_per)):
            mname = "R%s%d" % (kind, r)
            with open(os.path.join(cdir, mname + ".lean"), "w") as f:
                f.write(hdr)
                for j in range(s0, min(len(T["subs"]), s0 + subs_per)):
                    lo_, hi_ = T["subs"][j]
                    nj = hi_ - lo_
                    if pack and chunk > 1 and nj > 1:
                        # the rows of a packed leaf in `chunk` pieces, combined (PTree.allEr_append, allE_of_allEr)
                        cuts = sorted(set([nj * c_ // chunk for c_ in range(chunk + 1)]))
                        for c_ in range(len(cuts) - 1):
                            f.write("theorem rows%s%d_%d : PTree.allEr pw%s%s (%s %s %s %s) %s.%st%d %d %d = true := by\n"
                                    "  decide +kernel\n\n" % (kind, j, c_, kind, out, rowf, P, fN, fB, out,
                                                              kind.lower(), j, cuts[c_], cuts[c_ + 1]))
                        f.write("theorem rows%s%d : %s (%s %s %s %s) %s.%st%d = true := by\n" % (
                            kind, j, ALLE[kind], rowf, P, fN, fB, out, kind.lower(), j))
                        f.write("  have h0 := rows%s%d_0\n" % (kind, j))
                        for c_ in range(1, len(cuts) - 1):
                            f.write("  have h%d := PTree.allEr_append (by decide) (by decide) h%d rows%s%d_%d\n" % (
                                c_, c_ - 1, kind, j, c_))
                        f.write("  exact PTree.allE_of_allEr (by decide) h%d\n\n" % (len(cuts) - 2))
                    else:
                        f.write("theorem rows%s%d : %s (%s %s %s %s) %s.%st%d = true := by\n  decide +kernel\n\n"
                                % (kind, j, ALLE[kind], rowf, P, fN, fB, out, kind.lower(), j))
                    f.write("theorem tot%s%d : %s (%s %s) %s.%st%d = [%s] := by\n  decide +kernel\n\n" % (
                        kind, j, TOT[kind], contf, P, out, kind.lower(), j, ", ".join(str(x) for x in T["subtot"][j])))
                f.write("end QECKChecks.%s\n" % out)
            mods.append(mname)
        for r, s0 in enumerate(range(0, len(T["inner"]), irow_per)):
            mname = "I%s%d" % (kind, r)
            with open(os.path.join(cdir, mname + ".lean"), "w") as f:
                f.write(hdr)
                for nd in T["inner"][s0:s0 + irow_per]:
                    k, h, m = T["E"][nd["mid"]]
                    f.write("theorem irow%s%d : %s %s %s %s ((nat_lit %d), (nat_lit %d), (nat_lit %d)) = true := by\n"
                            "  decide +kernel\n\n" % (kind, nd["j"], rowf, P, fN, fB, k, h, m))
                f.write("end QECKChecks.%s\n" % out)
            mods.append(mname)
    # start modules: one per parent prefix of depth DEPTH - EGRP, holding the 8^EGRP prefixes of depth DEPTH below it
    parents = list(product(range(8), repeat=depth - egrp))
    for i in range(noff):
        for q, pp in enumerate(parents):
            mname = "E%d_%d" % (i, q)
            with open(os.path.join(cdir, mname + ".lean"), "w") as f:
                f.write(hdr)
                for tail in product(range(8), repeat=egrp):
                    js = list(pp) + list(tail)
                    f.write("theorem dfs_%d_%s : dfsPreAK %s %s %s (offA %s %d) [%s] [] = true := by\n"
                            "  decide +kernel\n\n" % (i, "_".join(map(str, js)), P, fN, fB, P, i,
                                                      ", ".join(map(str, js))))
                f.write("end QECKChecks.%s\n" % out)
            mods.append(mname)
    with open(os.path.join(cdir, "LIST.txt"), "w") as f:
        f.write("\n".join(mods) + "\n")
    with open(os.path.join(cdir, "tree.json"), "w") as f:
        json.dump(dict(name=out, src=name, kind="aug", pack=pack, chunk=chunk, egrp=egrp, K=K, HC=HC, noff=noff,
                       depth=depth, subs_per=subs_per,
                       irow_per=irow_per,
                       trees={kind: dict(root=T["root"], subs=len(T["subs"]), subtot=T["subtot"],
                                         inner=[dict(j=nd["j"], left=nd["left"], right=nd["right"],
                                                     level=nd["level"], e=list(T["E"][nd["mid"]]), tot=nd["tot"])
                                                for nd in T["inner"]])
                              for kind, T in trees.items()},
                       totN=totN, totB=totB), f)
    print(json.dumps(dict(name=out, near=len(ents["N"]), bulk=len(ents["B"]), subsN=len(trees["N"]["subs"]),
                          subsB=len(trees["B"]["subs"]), innerN=len(trees["N"]["inner"]),
                          innerB=len(trees["B"]["inner"]), modules=len(mods), offsets=noff,
                          dfs_modules=noff * len(parents), mask_bits=nmask, start_lhs_max=max(lhs), start_rhs=rhs)))


main()
