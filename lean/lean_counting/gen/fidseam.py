"""fidseam.py: compare the successor counts of the Lean seam rows (test/SeamFid.lean output) with the transitions
of tm2d_seam (PREFIX.seam_trans: int32 source, int32 target, uint8 isE; sources numbered near | right interface |
left interface | bulk).

usage: python3 -I -B gen/fidseam.py PREFIX FIDFILE
"""
import json
import struct
import sys


def main():
    pre, fid = sys.argv[1:3]
    js = json.load(open(pre + ".json"))
    nn, nb, K = js["near_states"], js["bulk_states"], js["M"] - 1
    nkeys = struct.unpack("<%dQ" % nn, open(pre + ".near_keys", "rb").read())
    raw = open(pre + ".seam_trans", "rb").read()
    assert len(raw) % 9 == 0
    cnt = [0] * (nn + 3 * nb)
    for j in range(0, len(raw), 9):
        src = struct.unpack_from("<i", raw, j)[0]
        cnt[src] += 1

    def keyof(steps, labs):
        k = 0
        for d, l in zip(steps, labs):
            k = k * 8 + 2 * d + l
        return k
    tn = {}
    for i, u in enumerate(nkeys):
        steps = [(u >> (2 * t)) & 3 for t in range(K)]
        labs = [(u >> (32 + t)) & 1 for t in range(K)]
        o = (u >> 48) - 1024
        tn[keyof(steps, labs) * 4096 + o + 2048] = cnt[i]
    tb = {}
    for i, ln in enumerate(l for l in open(pre + ".bulk_states") if l.strip()):
        ds, ls = ln.split()
        k = keyof([int(d) for d in ds], [1 if c == "C" else 0 for c in ls])
        tb[k] = (cnt[nn + i], cnt[nn + nb + i], cnt[nn + 2 * nb + i])
    ln_, lb, bad = {}, {}, 0
    for ln in open(fid):
        f = ln.split()
        if f[0] == "N":
            ln_[int(f[1])] = int(f[2])
        else:
            lb[int(f[1])] = tuple(int(x) for x in f[2:5])
    assert set(ln_) == set(tn) and set(lb) == set(tb)
    for k in tn:
        if tn[k] != ln_[k]:
            bad += 1
    for k in tb:
        if tb[k] != lb[k]:
            bad += 1
    print(json.dumps(dict(near=len(tn), bulk=len(tb), near_trans_tm2d=sum(tn.values()), near_trans_lean=sum(ln_.values()),
                          bulk_trans_tm2d=[sum(v[i] for v in tb.values()) for i in range(3)],
                          bulk_trans_lean=[sum(v[i] for v in lb.values()) for i in range(3)], mismatched_rows=bad)))


main()
