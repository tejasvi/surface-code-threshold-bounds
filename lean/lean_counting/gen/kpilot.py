"""kpilot.py: a timing pilot of the kernel route for a large certificate (not part of the proofs).

usage: python3 -I -B gen/kpilot.py NAME STATES HFILE TRANS n K c1,c2,.. Pn Pd Xn Xd Ln Ld NPILOT

Picks NPILOT states spread over the certificate, keeps them and every listed successor state, builds the kernel tree
(key, H, mask) of that subset exactly as gen/mkkdata.py does (masks computed against the full state list), and writes
QECCountComp/KData/NAME{,/T<j>}.lean and QEC/KChecks/NAME/P.lean with one `rowsOKK P t i (i+1)` theorem per pilot
state (decide +kernel). The rows of the pilot states see exactly the lookups they would see in the full tree, so the
module's time divided by NPILOT is the kernel cost of one row.
"""
import json
import os
import struct
import sys


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
    npilot = int(a[13])
    B = 4 * n
    pats, keys = [], []
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
    N = len(keys)
    H = list(struct.unpack("<%dq" % N, open(hfile, "rb").read()))
    idx = {k: i for i, k in enumerate(keys)}
    pilot = sorted({N * j // npilot for j in range(npilot)})
    pset = set(pilot)
    incl = {i: set() for i in pilot}
    raw = open(tfile, "rb").read()
    for r in range(len(raw) // 9):
        fr, to, isE = struct.unpack_from("<iiB", raw, 9 * r)
        if fr in pset:
            d, l = pats[to][-1]
            incl[fr].add((d, l))
    cand = [(d, l) for d in range(2 * n) for l in (False, True)]
    sub = set(pilot)
    masks = {}
    for i in pilot:
        m = 0
        for j, x in enumerate(cand):
            u = pats[i] + [x]
            if not walk_ok([y[0] for y in u], n):
                continue
            tk = 0
            for d, l in u[1:]:
                tk = tk * B + 2 * d + (1 if l else 0)
            if tk in idx:
                sub.add(idx[tk])
                if x not in incl[i]:
                    m |= 1 << j
        masks[i] = m
    order = sorted(sub, key=lambda i: keys[i])
    pos = {i: q for q, i in enumerate(order)}
    wE, wC, Q = Pn * Xn * Xn, (Pd - Pn) * Xd * Xd, Pd * Xd * Xn

    def lit(x):
        return "(nat_lit %d)" % x

    def full(lo, hi):
        if lo >= hi:
            return "KTree.leaf"
        mid = (lo + hi) // 2
        i = order[mid]
        return "(KTree.node %s %s %s %s %s)" % (full(lo, mid), lit(keys[i]), lit(H[i]), lit(masks.get(i, 0)),
                                               full(mid + 1, hi))

    ddir = os.path.join("QECCountComp", "KData")
    os.makedirs(ddir, exist_ok=True)
    with open(os.path.join(ddir, name + ".lean"), "w") as f:
        f.write("import QECCountComp.Kern\n\n/-! Kernel timing pilot %s (gen/kpilot.py; not part of the proofs). -/\n\n"
                % name)
        f.write("namespace QECComp.KData\n\n/-- The pilot subset of certificate %s. -/\ndef t%s : KTree :=\n  %s\n\n"
                % (name, name, full(0, len(order))))
        f.write("/-- The parameters of certificate %s. -/\n" % name)
        f.write("def P%s : Params where\n  n := %d\n  c := [%s]\n  K := %d\n  wE := %d\n  wC := %d\n  Q := %d\n"
                "  lamN := %d\n  lamD := %d\n  Hmin := %d\n  K0n := 1\n  K0d := 1\n\nend QECComp.KData\n" % (
                    name, n, ", ".join(str(x) for x in c), K, wE, wC, Q, Ln, Ld, min(H)))
    cdir = os.path.join("QEC", "KChecks", name)
    os.makedirs(cdir, exist_ok=True)
    with open(os.path.join(cdir, "P.lean"), "w") as f:
        f.write("import QECCountComp.KData.%s\n\nnamespace QECKChecks.%s\n\nopen QECComp QECComp.KData\n\n"
                "set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nset_option Elab.async false\n\n"
                % (name, name))
        for j, i in enumerate(pilot):
            f.write("theorem row%d : rowsOKK P%s t%s %d %d = true := by\n  decide +kernel\n\n" % (
                j, name, name, pos[i], pos[i] + 1))
        f.write("end QECKChecks.%s\n" % name)
    print(json.dumps(dict(name=name, states=N, pilot=len(pilot), subset=len(order))))


main()
