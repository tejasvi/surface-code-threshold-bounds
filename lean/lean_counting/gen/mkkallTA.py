"""mkkallTA.py: the assembly modules of a kernel seam (gen/mkkseam.py) or augmented (gen/mkkaug.py) certificate
(untrusted generator; Lean checks everything).

usage: python3 -I -B gen/mkkallTA.py OUT

Reads QEC/KChecks/OUT/tree.json and writes
  QEC/KChecks/OUT/A<j>.lean   the internal nodes of the near and the bulk tree (children first): `KTree.allE (row) u`
                              from its children and its own row, and `totTK (contrib) u = [..]` from its children's
  QEC/KChecks/OUT/P<i>.lean   for every start offset index i: the start check from offset i, from the start checks of
                              the prefixes of depth DEPTH - EGRP; these follow from the E modules by split1, in
                              QEC/KChecks/OUT/P<i>_<d>.lean (d = first index of the prefix) when EGRP >= 2, or in
                              P<i> itself when EGRP = 1 or PSPLIT=0 (environment)
  QEC/KChecks/OUT/All.lean    the certificate (CertOKTK or CertOKAK) and `bound` (tor_bound_of_certK or
                              rot_bound_of_certAK)
"""
import json
import os
import sys
from itertools import product

PER_A = 600


def main():
    out = sys.argv[1]
    cdir = os.path.join("QEC", "KChecks", out)
    T = json.load(open(os.path.join(cdir, "tree.json")))
    aug = T.get("kind") == "aug"
    K, HC, noff, depth = T["K"], T["HC"], T["noff"], T["depth"]
    subs_per, irow_per = T["subs_per"], T["irow_per"]
    tN, tB = "tN%s" % out, "tB%s" % out
    P = "P%s" % out
    pack = T.get("pack", False)
    if pack:
        fN, fB = "(tN%s.find pwN%s)" % (out, out), "(tB%s.find pwB%s)" % (out, out)
        ALLE = {k_: "PTree.allE pw%s%s" % (k_, out) for k_ in ("N", "B")}
        TOTF = {k_: "PTree.tot pw%s%s" % (k_, out) for k_ in ("N", "B")}
        LST = {"N": "(%s.toList pwN%s)" % (tN, out), "B": "(%s.toList pwB%s)" % (tB, out)}
        NODE, ALLEN, TOTUNF, IFF, TOTEQ, FMEM = "PTree.node", "allE_nodeP", "PTree.tot", "allE_iffP", "totP_eq", \
            "find_memP"
        EXTRA = ["import QEC.Count.ChunksP"]
    else:
        fN, fB = "tN%s.find" % out, "tB%s.find" % out
        ALLE = {k_: "KTree.allE" for k_ in ("N", "B")}
        TOTF = {k_: "totTK" for k_ in ("N", "B")}
        LST = {"N": "%s.toList" % tN, "B": "%s.toList" % tB}
        NODE, ALLEN, TOTUNF, IFF, TOTEQ, FMEM = "KTree.node", "allE_node", "totTK", "allE_iff", "totTK_eq", "find_mem"
        EXTRA = []
    if aug:
        rowf = {"N": "nearRowAK", "B": "bulkRowAK"}
        contf = {"N": "nearContribA", "B": "bulkContribA"}
        dfsPre, dfsF, off, startF = "dfsPreAK", "dfsAK", "offA", "startOKAK"
        split1, ofpre, certS = "dfsPreAK_split1", "dfsAK_of_prefixes", "CertOKAK"
        chunks, final = "QEC.Count.ChunksAK", "QEC.Count.RotFinalAK"
        offmax_expr, offmax = "%s.HC + %s.K + 1" % (P, P), HC + K + 1
        params = ["hK", "hHC", "hHC2", "hN0", "hQ", "hlamD", "hK0d"]
    else:
        rowf = {"N": "nearRowTK", "B": "bulkRowTK"}
        contf = {"N": "nearContribT", "B": "bulkContribT"}
        dfsPre, dfsF, off, startF = "dfsPreTK", "dfsTK", "offT", "startOKTK"
        split1, ofpre, certS = "dfsPreTK_split1", "dfsTK_of_prefixes", "CertOKTK"
        chunks, final = "QEC.Count.ChunksTK", "QEC.Count.TorFinalK"
        offmax_expr, offmax = "2 * (%s.HC + %s.K)" % (P, P), 2 * (HC + K)
        params = ["hK", "hHC", "hQ", "hlamD", "hK0d", "hHC2"]
    assert offmax + 1 == noff
    hdr0 = "set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nset_option Elab.async false\n\n"
    modsR = []
    for kind in ("N", "B"):
        tr = T["trees"][kind]
        nR = (tr["subs"] + subs_per - 1) // subs_per
        nI = (len(tr["inner"]) + irow_per - 1) // irow_per
        modsR += ["R%s%d" % (kind, r) for r in range(nR)] + ["I%s%d" % (kind, r) for r in range(nI)]

    def rows_ref(kind, ref):
        return ("rows%s%s" % (kind, ref[2:])) if ref[1] == "t" else ("arows%s%s" % (kind, ref[2:]))

    def tot_ref(kind, ref):
        return ("tot%s%s" % (kind, ref[2:])) if ref[1] == "t" else ("atot%s%s" % (kind, ref[2:]))

    order = []
    for kind in ("N", "B"):
        for d in T["trees"][kind]["inner"]:
            order.append((d["level"], kind, d))
    order.sort(key=lambda x: (x[0], x[1], x[2]["j"]))
    # A files: nodes grouped by level, PER_A per file; a file imports exactly the modules that hold its nodes'
    # children (row modules R, or A files of lower levels) and own rows (I modules), so the files of one level can be
    # compiled in parallel (ALEVELS.txt: the A files level by level)
    # ALAYOUT=chain: the earlier layout (consecutive files, A0 importing every row module, A<a> importing A<a-1>; the
    # layout of T8K's committed assembly)
    chain = os.environ.get("ALAYOUT", "levels") == "chain"
    files, levels, file_of = [], [], {}
    if chain:
        for s0 in range(0, len(order), PER_A):
            a = len(files)
            files.append(order[s0:s0 + PER_A])
            for _, kind, d in order[s0:s0 + PER_A]:
                file_of[(kind, d["j"])] = "A%d" % a
    else:
        for lev in sorted(set(x[0] for x in order)):
            nodes = [x for x in order if x[0] == lev]
            names = []
            for s0 in range(0, len(nodes), PER_A):
                a = len(files)
                files.append(nodes[s0:s0 + PER_A])
                names.append("A%d" % a)
                for _, kind, d in nodes[s0:s0 + PER_A]:
                    file_of[(kind, d["j"])] = "A%d" % a
            levels.append(names)
    na = len(files)

    def holder(kind, ref):
        # the module that proves the facts of the child ref (a subtree t<j> or an internal node u<j>)
        jj = int(ref[2:])
        return ("R%s%d" % (kind, jj // subs_per)) if ref[1] == "t" else file_of[(kind, jj)]

    if not chain:
        with open(os.path.join(cdir, "ALEVELS.txt"), "w") as f:
            f.write("".join(" ".join(names) + "\n" for names in levels))
    for a in range(na):
        part = files[a]
        with open(os.path.join(cdir, "A%d.lean" % a), "w") as f:
            f.write("import QEC.Count.ChunksK3\n" + "".join(x + "\n" for x in EXTRA))
            if chain:
                imps = modsR if a == 0 else ["A%d" % (a - 1)]
            else:
                imps = []
                for _, kind, d in part:
                    for m_ in (holder(kind, d["left"]), holder(kind, d["right"]),
                               "I%s%d" % (kind, d["j"] // irow_per)):
                        if m_ not in imps:
                            imps.append(m_)
            f.write("".join("import QEC.KChecks.%s.%s\n" % (out, m_) for m_ in imps))
            f.write("\nnamespace QECKChecks.%s\n\nopen QEC QECComp QECComp.KData\n\n%s" % (out, hdr0))
            for _, kind, d in part:
                j = d["j"]
                k, h, m = d["e"]
                node = "%s %s.%s (nat_lit %d) (nat_lit %d) (nat_lit %d) %s.%s" % (
                    NODE, out, d["left"], k, h, m, out, d["right"])
                me = "%su%d" % (kind.lower(), j)
                f.write("theorem arows%s%d : %s (%s %s %s %s) %s.%s = true := by\n" % (
                    kind, j, ALLE[kind], rowf[kind], P, fN, fB, out, me))
                f.write("  rw [show %s.%s = %s from rfl, %s, %s, irow%s%d, %s]\n  all_goals rfl\n\n" % (
                    out, me, node, ALLEN, rows_ref(kind, d["left"]), kind, j, rows_ref(kind, d["right"])))
                f.write("theorem atot%s%d : %s (%s %s) %s.%s = [%s] := by\n" % (
                    kind, j, TOTF[kind], contf[kind], P, out, me, ", ".join(map(str, d["tot"]))))
                f.write("  rw [show %s.%s = %s from rfl, %s, %s, %s]\n  decide +kernel\n\n" % (
                    out, me, node, TOTUNF, tot_ref(kind, d["left"]), tot_ref(kind, d["right"])))
            f.write("end QECKChecks.%s\n" % out)
    # P modules: one per offset index
    egrp = T.get("egrp", 1)
    top = depth - egrp
    parents = list(product(range(8), repeat=top))
    pmods = []

    def pname(i, pr):
        # the start fact of the prefix pr: E theorems at depth DEPTH, dfsl in between, dfsp at depth DEPTH - EGRP
        s = "_".join(map(str, pr))
        return ("dfs_%d_%s" if len(pr) == depth else "dfsp_%d_%s" if len(pr) == top else "dfsl_%d_%s") % (i, s)

    psplit = os.environ.get("PSPLIT", "1") == "1" and top >= 1 and egrp >= 2
    for i in range(noff):
        mname = "P%d" % i
        if psplit:
            # the split theorems of offset i in 8 modules, by the first candidate index of the prefix
            per = 8 ** (top - 1)
            for d in range(8):
                with open(os.path.join(cdir, "P%d_%d.lean" % (i, d)), "w") as f:
                    f.write("import %s\nimport Mathlib.Tactic.IntervalCases\n" % chunks)
                    f.write("".join("import QEC.KChecks.%s.E%d_%d\n" % (out, i, q) for q in range(d * per, (d + 1) * per)))
                    f.write("\nnamespace QECKChecks.%s\n\nopen QEC QECComp QECComp.KData\n\n%s" % (out, hdr0))
                    for lev in range(depth - 1, top - 1, -1):
                        for rest in product(range(8), repeat=lev - 1):
                            pp = [d] + list(rest)
                            f.write("theorem %s : %s %s %s %s (%s %s %d) [%s] [] = true := by\n" % (
                                pname(i, pp), dfsPre, P, fN, fB, off, P, i, ", ".join(map(str, pp))))
                            f.write("  apply %s (by decide)\n  intro j hj\n" % split1)
                            f.write("  have hl : (candList 2).length = 8 := by decide\n  rw [hl] at hj\n")
                            f.write("  interval_cases j\n  exacts [%s]\n\n" % ", ".join(
                                pname(i, pp + [j]) for j in range(8)))
                    f.write("end QECKChecks.%s\n" % out)
        with open(os.path.join(cdir, mname + ".lean"), "w") as f:
            f.write("import %s\nimport Mathlib.Tactic.IntervalCases\n" % chunks)
            if psplit:
                f.write("".join("import QEC.KChecks.%s.P%d_%d\n" % (out, i, d) for d in range(8)))
            else:
                f.write("".join("import QEC.KChecks.%s.E%d_%d\n" % (out, i, q) for q in range(len(parents))))
            f.write("\nnamespace QECKChecks.%s\n\nopen QEC QECComp QECComp.KData\n\n%s" % (out, hdr0))
            for lev in ([] if psplit else range(depth - 1, top - 1, -1)):
                for pp in product(range(8), repeat=lev):
                    f.write("theorem %s : %s %s %s %s (%s %s %d) [%s] [] = true := by\n" % (
                        pname(i, pp), dfsPre, P, fN, fB, off, P, i, ", ".join(map(str, pp))))
                    f.write("  apply %s (by decide)\n  intro j hj\n" % split1)
                    f.write("  have hl : (candList 2).length = 8 := by decide\n  rw [hl] at hj\n")
                    f.write("  interval_cases j\n  exacts [%s]\n\n" % ", ".join(
                        pname(i, list(pp) + [j]) for j in range(8)))
            js = ["j%d" % (q + 1) for q in range(top)]
            f.write("theorem dfsoff_%d : %s %s %s %s (%s %s %d) %s.K [] = true := by\n" % (
                i, dfsF, P, fN, fB, off, P, i, P))
            f.write("  apply %s (D := %d) (by decide)\n  intro js hlen hjs\n" % (ofpre, top))
            f.write("  have hl : (candList 2).length = 8 := by decide\n  rw [hl] at hjs\n")
            f.write("  match js, hlen with\n  | [%s], _ =>\n" % ", ".join(js))
            for v in js:
                f.write("    have h%s : %s < 8 := hjs %s (by simp)\n" % (v, v, v))
            f.write("    " + " <;> ".join("interval_cases %s" % v for v in js) + "\n")
            f.write("    exacts [%s]\n\n" % ", ".join("dfsp_%d_%s" % (i, "_".join(map(str, pp))) for pp in parents))
            f.write("end QECKChecks.%s\n" % out)
        pmods.append(mname)
    L = ["import QEC.Count.ChunksK3", "import QEC.Count.CertSoundK", "import QEC.Count.ChunksTK", "import %s" % chunks,
         "import %s" % final, "import Mathlib.Tactic.IntervalCases"] + EXTRA
    if chain:
        if na:
            L.append("import QEC.KChecks.%s.A%d" % (out, na - 1))
        else:
            L += ["import QEC.KChecks.%s.%s" % (out, m) for m in modsR]
    else:
        for kind in ("N", "B"):
            rt = T["trees"][kind]["root"]
            if rt != "leaf":
                m_ = holder(kind, rt)
                if "import QEC.KChecks.%s.%s" % (out, m_) not in L:
                    L.append("import QEC.KChecks.%s.%s" % (out, m_))
    L += ["import QEC.KChecks.%s.%s" % (out, m) for m in pmods]
    L += ["", "/-!\n# Certificate %s (kernel route): assembly (generated by gen/mkkallTA.py)\n-/" % out, "",
          "namespace QECKChecks.%s" % out, "", "open QEC QECComp QECComp.KData", "", hdr0.rstrip(), ""]
    rN, rB = T["trees"]["N"]["root"], T["trees"]["B"]["root"]
    L.append("theorem hnear : ∀ e ∈ %s, %s %s %s %s e = true :=" % (LST["N"], rowf["N"], P, fN, fB))
    L.append("  %s.mp (show %s (%s %s %s %s) %s.%s = true from %s)" % (
        IFF, ALLE["N"], rowf["N"], P, fN, fB, out, rN, rows_ref("N", rN)))
    L.append("")
    L.append("theorem hbulk : ∀ e ∈ %s, %s %s %s %s e = true :=" % (LST["B"], rowf["B"], P, fN, fB))
    L.append("  %s.mp (show %s (%s %s %s %s) %s.%s = true from %s)" % (
        IFF, ALLE["B"], rowf["B"], P, fN, fB, out, rB, rows_ref("B", rB)))
    L.append("")
    L.append("theorem hdfs : ∀ i, i ≤ %s → %s %s %s %s (%s %s i) %s.K [] = true := by" % (
        offmax_expr, dfsF, P, fN, fB, off, P, P))
    L.append("  intro i hi")
    L.append("  have hb : %s = %d := by decide" % (offmax_expr, offmax))
    L.append("  rw [hb] at hi")
    L.append("  interval_cases i")
    L.append("  exacts [%s]" % ", ".join("dfsoff_%d" % i for i in range(noff)))
    L.append("")
    L.append("theorem hstart : %s %s (sumL (%s.map (%s %s))) (sumL (%s.map (%s %s))) = true := by" % (
        startF, P, LST["N"], contf["N"], P, LST["B"], contf["B"], P))
    L.append("  rw [← %s, ← %s, show %s = %s.%s from rfl, show %s = %s.%s from rfl, %s, %s]" % (
        TOTEQ, TOTEQ, tN, out, rN, tB, out, rB, tot_ref("N", rN), tot_ref("B", rB)))
    L.append("  decide +kernel")
    L.append("")
    L.append("theorem cert : %s %s %s %s %s %s where" % (certS, P, fN, fB, LST["N"], LST["B"]))
    L.append("  memN := fun _ _ _ hf => %s hf" % FMEM)
    L.append("  memB := fun _ _ _ hf => %s hf" % FMEM)
    for p_ in params:
        L.append("  %s := by decide" % p_)
    L.append("  near := hnear")
    L.append("  bulk := hbulk")
    L.append("  dfs := hdfs")
    L.append("  start := hstart")
    L += ["", "end QECKChecks.%s" % out]
    with open(os.path.join(cdir, "All.lean"), "w") as f:
        f.write("\n".join(L) + "\n")
    print("wrote %s: %d assembly modules, %d prefix modules, All.lean (roots %s, %s)" % (cdir, na, len(pmods), rN, rB))


main()
