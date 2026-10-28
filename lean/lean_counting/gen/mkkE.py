"""mkkE.py: rewrite the start modules of a kernel seam or augmented certificate with a new prefix depth (untrusted
generator; Lean checks everything). The other modules and the kernel data do not depend on it.

usage: python3 -I -B gen/mkkE.py OUT DEPTH EGRP

Reads QEC/KChecks/OUT/tree.json (gen/mkkseam.py or gen/mkkaug.py) and writes QEC/KChecks/OUT/E<i>_<q>.lean for every
start offset i and parent prefix q of depth DEPTH - EGRP (index q in product order), each holding the 8^EGRP prefixes
of depth DEPTH below q; updates depth and egrp in tree.json. The module names are those of the generators, so
LIST.txt is unchanged when DEPTH - EGRP is unchanged.
"""
import json
import os
import sys
from itertools import product


def main():
    out, depth, egrp = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    cdir = os.path.join("QEC", "KChecks", out)
    tj = os.path.join(cdir, "tree.json")
    T = json.load(open(tj))
    aug = T.get("kind") == "aug"
    pack = T.get("pack", False)
    noff = T["noff"]
    assert depth <= T["K"], "the prefix depth must be at most K"
    P = "P%s" % out
    if pack:
        fN, fB = "(tN%s.find pwN%s)" % (out, out), "(tB%s.find pwB%s)" % (out, out)
    else:
        fN, fB = "tN%s.find" % out, "tB%s.find" % out
    dfsPre, off = ("dfsPreAK", "offA") if aug else ("dfsPreTK", "offT")
    hdr = ("import QECCountComp.KData.%s\n\nnamespace QECKChecks.%s\n\nopen QECComp QECComp.KData\n\n"
           "set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nset_option Elab.async false\n\n" % (out, out))
    parents = list(product(range(8), repeat=depth - egrp))
    for i in range(noff):
        for q, pp in enumerate(parents):
            with open(os.path.join(cdir, "E%d_%d.lean" % (i, q)), "w") as f:
                f.write(hdr)
                for tail in product(range(8), repeat=egrp):
                    js = list(pp) + list(tail)
                    f.write("theorem dfs_%d_%s : %s %s %s %s (%s %s %d) [%s] [] = true := by\n"
                            "  decide +kernel\n\n" % (i, "_".join(map(str, js)), dfsPre, P, fN, fB, off, P, i,
                                                      ", ".join(map(str, js))))
                f.write("end QECKChecks.%s\n" % out)
    T["depth"], T["egrp"] = depth, egrp
    with open(tj, "w") as f:
        json.dump(T, f)
    print("wrote %d start modules of %s (depth %d, %d prefixes each)" % (noff * len(parents), out, depth, 8 ** egrp))


main()
