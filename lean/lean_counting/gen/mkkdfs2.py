"""mkkdfs2.py: start-completeness modules of a version-2 kernel certificate at a finer prefix depth (untrusted
generator; Lean checks everything). Each module E<j>.lean holds the |candList| prefixes of depth DEPTH that extend
one prefix of depth DEPTH - 1, one theorem each (`dfsPreK P t [j1, .., jD] [] = true`), so the kernel's working
memory is that of one prefix. The assembly (gen/mkkall2.py) combines them with dfsPreK_split1 and
dfsOKK_of_prefixes at depth DEPTH - 1.

usage: python3 -I -B gen/mkkdfs2.py NAME n DEPTH
Writes QEC/KChecks/NAME/E<j>.lean, adds them to LIST_E.txt, and records {"edepth": DEPTH} in tree.json.
"""
import json
import os
import sys
from itertools import product


def main():
    name, n, depth = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    m = 4 * n
    cdir = os.path.join("QEC", "KChecks", name)
    tj = os.path.join(cdir, "tree.json")
    T = json.load(open(tj))
    hdr = ("import QECCountComp.KData.%s\n\nnamespace QECKChecks.%s\n\nopen QECComp QECComp.KData\n\n"
           "set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nset_option Elab.async false\n\n" % (name, name))
    mods = []
    for r, par in enumerate(product(range(m), repeat=depth - 1)):
        with open(os.path.join(cdir, "E%d.lean" % r), "w") as f:
            f.write(hdr)
            for j in range(m):
                js = list(par) + [j]
                f.write("theorem dfs_%s : dfsPreK P%s t%s [%s] [] = true := by\n  decide +kernel\n\n" % (
                    "_".join(map(str, js)), name, name, ", ".join(map(str, js))))
            f.write("end QECKChecks.%s\n" % name)
        mods.append("E%d" % r)
    with open(os.path.join(cdir, "LIST_E.txt"), "w") as f:
        f.write("\n".join(mods) + "\n")
    T["edepth"] = depth
    with open(tj, "w") as f:
        json.dump(T, f)
    print("wrote %d E modules (depth %d, %d prefixes each)" % (len(mods), depth, m))


main()
