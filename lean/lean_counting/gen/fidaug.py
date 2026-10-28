"""fidaug.py: compare the successors kept by the Lean rows of an augmented certificate (test/AugFid.lean output)
with the transitions of tm2d_aug_omp (PREFIX.aug_trans: int32 source, int32 target, uint8 isE; sources and targets
in the combined numbering [near | interface | bulk]). Every row is compared as a multiset of (target key, label);
keys are AugC.ckeyA (steps + 4^K labels + 8^K h; bulk states h = 0).

usage: python3 -I -B gen/fidaug.py PREFIX FIDFILE
"""
import json
import struct
import sys
from collections import Counter


def main():
    pre, fid = sys.argv[1:3]
    js = json.load(open(pre + ".json"))
    nn, nb, K = js["near_states"], js["bulk_states"], js["M"] - 1
    m2, mK = (1 << (2 * K)) - 1, (1 << K) - 1
    nkeys = struct.unpack("<%dQ" % nn, open(pre + ".near_keys", "rb").read())
    names = ["%d" % ((u & m2) | (((u >> 32) & mK) << (2 * K)) | ((u >> 48) << (3 * K))) for u in nkeys]
    bnames = []
    for ln in open(pre + ".bulk_states"):
        if ln.strip():
            ds, ls = ln.split()
            sc = sum(int(d) << (2 * t) for t, d in enumerate(ds))
            lc = sum((1 << t) for t, c in enumerate(ls) if c == "C")
            bnames.append("%d" % (sc | (lc << (2 * K))))
    assert len(bnames) == nb
    rows = {}
    for i in range(nn):
        rows[("N", names[i])] = Counter()
    for i in range(nb):
        rows[("I", bnames[i])] = Counter()
        rows[("B", bnames[i])] = Counter()
    raw = open(pre + ".aug_trans", "rb").read()
    assert len(raw) % 9 == 0
    ntr = len(raw) // 9
    for j in range(ntr):
        src, tgt, ie = struct.unpack_from("<iiB", raw, 9 * j)
        if src < nn:
            row = ("N", names[src])
        elif src < nn + nb:
            row = ("I", bnames[src - nn])
        else:
            row = ("B", bnames[src - nn - nb])
        tname = ("n" + names[tgt]) if tgt < nn else ("b" + bnames[tgt - nn - nb]) if tgt >= nn + nb \
            else ("b" + bnames[tgt - nn])
        rows[row]["%s:%s" % (tname, "E" if ie else "C")] += 1
    lean = {}
    nx = 0
    for ln in open(fid):
        f = ln.split()
        succ = Counter(f[2:])
        nx += succ.get("X", 0)
        lean[(f[0], f[1])] = succ
    assert set(lean) == set(rows), "row sets differ"
    bad = {"N": 0, "I": 0, "B": 0}
    ex = []
    for r in rows:
        if rows[r] != lean[r]:
            bad[r[0]] += 1
            if len(ex) < 10:
                ex.append([r[0], r[1], sorted((rows[r] - lean[r]).elements()), sorted((lean[r] - rows[r]).elements())])
    tot = {t: [sum(sum(rows[r].values()) for r in rows if r[0] == t), sum(sum(lean[r].values()) for r in lean
                                                                            if r[0] == t)] for t in "NIB"}
    print(json.dumps(dict(near=nn, bulk=nb, transitions=ntr, rows=len(rows), trans_by_kind_tm2d_lean=tot,
                          unlisted_unexcluded_X=nx, mismatched_rows=bad, examples_tm2d_only_lean_only=ex)))


main()
