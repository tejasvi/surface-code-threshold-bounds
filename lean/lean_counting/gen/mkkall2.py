"""mkkall2.py: the assembly modules of a version-2 kernel certificate (untrusted generator; Lean checks everything).

usage: python3 -I -B gen/mkkall2.py NAME

Reads QEC/KChecks/NAME/tree.json (written by gen/mkkdata2.py) and writes
  QEC/KChecks/NAME/A<j>.lean   for every internal node u<i> (children first): `KTree.allE (rowCheckK P t) NAME.u<i>`
                               from its children and its own row, and `totK P NAME.u<i> = [..]` from its children's
  QEC/KChecks/NAME/All.lean    hrows, hst, hdfs and `bound` (box_bound_of_certK)
"""
import json
import os
import sys

PER_A = 600


def main():
    name = sys.argv[1]
    cdir = os.path.join("QEC", "KChecks", name)
    T = json.load(open(os.path.join(cdir, "tree.json")))
    K, n, depth = T["K"], T["n"], T["depth"]
    subs_per, pre_per, irow_per = T["subs_per"], T["pre_per"], T["irow_per"]
    inner = T["inner"]
    subtot = T["subtot"]
    P, t = "P%s" % name, "t%s" % name
    nR = (T["subs"] + subs_per - 1) // subs_per
    nI = (len(inner) + irow_per - 1) // irow_per
    nD = (T["nprefix"] + pre_per - 1) // pre_per
    tot_of = {}

    def rows_ref(ref):
        return ("rows%s" % ref[1:]) if ref[0] == "t" else ("arows%s" % ref[1:])

    def tot_ref(ref):
        return ("tot%s" % ref[1:]) if ref[0] == "t" else ("atot%s" % ref[1:])

    for j, s in enumerate(subtot):
        tot_of["t%d" % j] = s
    order = sorted(inner, key=lambda d: (d["level"], d["j"]))
    na = (len(order) + PER_A - 1) // PER_A
    hdr0 = "set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nset_option Elab.async false\n\n"
    for a in range(na):
        part = order[a * PER_A:(a + 1) * PER_A]
        with open(os.path.join(cdir, "A%d.lean" % a), "w") as f:
            f.write("import QEC.Count.ChunksK3\n")
            if a == 0:
                f.write("".join("import QEC.KChecks.%s.R%d\n" % (name, r) for r in range(nR)))
                f.write("".join("import QEC.KChecks.%s.I%d\n" % (name, r) for r in range(nI)))
            else:
                f.write("import QEC.KChecks.%s.A%d\n" % (name, a - 1))
            f.write("\nnamespace QECKChecks.%s\n\nopen QEC QECComp QECComp.KData\n\n%s" % (name, hdr0))
            for d in part:
                j = d["j"]
                node = "KTree.node %s.%s (nat_lit %d) (nat_lit %d) (nat_lit %d) %s.%s" % (
                    name, d["left"], d["key"], d["H"], d["mask"], name, d["right"])
                f.write("theorem arows%d : KTree.allE (rowCheckK %s %s) %s.u%d = true := by\n" % (j, P, t, name, j))
                f.write("  rw [show %s.u%d = %s from rfl, allE_node, %s, irow%d, %s]\n  all_goals rfl\n\n" % (
                    name, j, node, rows_ref(d["left"]), j, rows_ref(d["right"])))
                tl, tr = tot_of[d["left"]], tot_of[d["right"]]
                me = [0] * (K + 1)
                me[d["nC"]] = d["H"]
                tt = [x + y + z for x, y, z in zip(tl, me, tr)]
                tot_of["u%d" % j] = tt
                f.write("theorem atot%d : totK %s %s.u%d = [%s] := by\n" % (j, P, name, j, ", ".join(map(str, tt))))
                f.write("  rw [show %s.u%d = %s from rfl, totK_node, %s, %s]\n  decide +kernel\n\n" % (
                    name, j, node, tot_ref(d["left"]), tot_ref(d["right"])))
            f.write("end QECKChecks.%s\n" % name)
    root = T["root"]
    m = 4 * n
    from itertools import product
    edepth = T.get("edepth")
    pfx_imports = []
    if edepth:
        # prefix facts of depth edepth - 1 from the E modules (dfsPreK_split1), PER_P per file
        PER_P = 512
        parents = list(product(range(m), repeat=edepth - 1))
        npf = (len(parents) + PER_P - 1) // PER_P
        for q in range(npf):
            with open(os.path.join(cdir, "P%d.lean" % q), "w") as f:
                f.write("import QEC.Count.ChunksK4\nimport Mathlib.Tactic.IntervalCases\n")
                f.write("".join("import QEC.KChecks.%s.E%d\n" % (name, r)
                                for r in range(q * PER_P, min(len(parents), (q + 1) * PER_P))))
                f.write("\nnamespace QECKChecks.%s\n\nopen QEC QECComp QECComp.KData\n\n%s" % (name, hdr0))
                for par in parents[q * PER_P:(q + 1) * PER_P]:
                    s = "_".join(map(str, par))
                    f.write("theorem dfsp_%s : dfsPreK %s %s [%s] [] = true := by\n" % (
                        s, P, t, ", ".join(map(str, par))))
                    f.write("  apply dfsPreK_split1 (by decide)\n  intro j hj\n")
                    f.write("  have hl : (candList %s.n).length = %d := by decide\n  rw [hl] at hj\n" % (P, m))
                    f.write("  interval_cases j\n  exacts [%s]\n\n" % ", ".join("dfs_%s_%d" % (s, j) for j in range(m)))
                f.write("end QECKChecks.%s\n" % name)
            pfx_imports.append("import QEC.KChecks.%s.P%d" % (name, q))
        depth = edepth - 1
    L = ["import QEC.Count.ChunksK3", "import QEC.Count.FinalK", "import Mathlib.Tactic.IntervalCases"]
    if na:
        L.append("import QEC.KChecks.%s.A%d" % (name, na - 1))
    else:
        L += ["import QEC.KChecks.%s.R%d" % (name, r) for r in range(nR)]
    if edepth:
        L += pfx_imports
    else:
        L += ["import QEC.KChecks.%s.D%d" % (name, r) for r in range(nD)]
    L += ["", "/-!\n# Certificate %s (kernel route, version 2): assembly (generated by gen/mkkall2.py)\n-/" % name, "",
          "namespace QECKChecks.%s" % name, "", "open QEC QECComp QECComp.KData Finset", "", hdr0.rstrip(), ""]
    L.append("theorem hrows : ∀ e ∈ %s.toList, rowCheckK %s %s e = true :=" % (t, P, t))
    L.append("  allE_iff.mp (show KTree.allE (rowCheckK %s %s) %s.%s = true from %s)" % (P, t, name, root,
                                                                                   rows_ref(root)))
    L.append("")
    L.append("theorem hst : startOKK %s %s = true := by" % (P, t))
    L.append("  apply startOKK_of_totK")
    L.append("  rw [show %s = %s.%s from rfl, %s]" % (t, name, root, tot_ref(root)))
    L.append("  decide +kernel")
    L.append("")
    js = ["j%d" % (i + 1) for i in range(depth)]
    L.append("theorem hdfs : dfsOKK %s %s %s.K [] = true := by" % (P, t, P))
    L.append("  apply dfsOKK_of_prefixes (d := %d) (by decide)" % depth)
    L.append("  intro js hlen hjs")
    L.append("  have hl : (candList %s.n).length = %d := by decide" % (P, m))
    L.append("  rw [hl] at hjs")
    L.append("  match js, hlen with")
    L.append("  | [%s], _ =>" % ", ".join(js))
    for v in js:
        L.append("    have h%s : %s < %d := hjs %s (by simp)" % (v, v, m, v))
    L.append("    " + " <;> ".join("interval_cases %s" % v for v in js))
    names = [("dfsp_%s" if edepth else "dfs_%s") % "_".join(str(x) for x in p) for p in product(range(m), repeat=depth)]
    L.append("    exacts [%s]" % ", ".join(names))
    L.append("")
    Pn, Pd, Xn, Xd = T["Pn"], T["Pd"], T["Xn"], T["Xd"]
    L.append("/-- The bound of certificate %s (kernel route) for every box with `K + 1 ≤ N a` and `0 < p ≤ %d/%d`. -/"
             % (name, Pn, Pd))
    L.append("theorem bound (N : Fin %s.n → ℕ) (a : Fin %s.n) (hK : %s.K + 1 ≤ N a) {p : ℝ} (hp0 : 0 < p)" % (P, P, P))
    L.append("    (hp : p ≤ ((%d : ℕ) : ℝ) / (%d : ℕ)) :" % (Pn, Pd))
    L.append("    PfailMW (boxEdges %s.n N a) p ≤" % P)
    L.append("      #(univ.filter (fun u : BoxV %s.n N => (u a : ℕ) = 0)) * ((%s.K0n : ℝ) / %s.K0d) *" % (P, P, P))
    L.append("        ((%s.lamN : ℝ) / %s.lamD * rhoOf (((%d : ℕ) : ℝ) / (%d : ℕ)) p) ^ (N a - 1 - %s.K) /" % (
        P, P, Pn, Pd, P))
    L.append("          (1 - (%s.lamN : ℝ) / %s.lamD * rhoOf (((%d : ℕ) : ℝ) / (%d : ℕ)) p) :=" % (P, P, Pn, Pd))
    L.append("  box_bound_of_certK %s %s N a %d %d %d %d rfl rfl rfl (by norm_num) (by norm_num) (by norm_num)" % (
        P, t, Pn, Pd, Xn, Xd))
    L.append("    (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) hrows hdfs hst hK hp0 hp")
    L += ["", "end QECKChecks.%s" % name]
    with open(os.path.join(cdir, "All.lean"), "w") as f:
        f.write("\n".join(L) + "\n")
    print("wrote %s: %d assembly modules, All.lean (root %s, %d prefixes)" % (cdir, na, root, len(names)))


main()
