"""mutseam.py: mutants of a tm2d_seam certificate, to check that the Lean seam checks reject bad data.

usage: python3 -I -B gen/mutseam.py SRC_PREFIX DST_PREFIX MODE
  halfG     halve G of the near state with the largest G (its row must fail)
  dropnear  remove the near state with the largest G (start completeness and its predecessors' rows must fail)
  dropbulk  remove the bulk state with the largest H (start completeness from bigO and bulk rows must fail)
Writes DST_PREFIX.{json,near_keys,seam_H,bulk_states}; prints the mutated entry.
"""
import json
import struct
import sys


def main():
    src, dst, mode = sys.argv[1:4]
    js = json.load(open(src + ".json"))
    nn, nb = js["near_states"], js["bulk_states"]
    nkeys = list(struct.unpack("<%dQ" % nn, open(src + ".near_keys", "rb").read()))
    H = list(struct.unpack("<%dq" % (nn + 3 * nb), open(src + ".seam_H", "rb").read()))
    G, Hb = H[:nn], H[nn:nn + nb]
    bulk = [ln for ln in open(src + ".bulk_states") if ln.strip()]
    if mode == "halfG":
        i = max(range(nn), key=lambda j: G[j])
        print("halfG near", i, hex(nkeys[i]), G[i], "->", G[i] // 2)
        G[i] //= 2
    elif mode == "dropnear":
        i = max(range(nn), key=lambda j: G[j])
        print("dropnear", i, hex(nkeys[i]), G[i])
        del nkeys[i], G[i]
    elif mode == "dropbulk":
        i = max(range(nb), key=lambda j: Hb[j])
        print("dropbulk", i, bulk[i].strip(), Hb[i])
        del bulk[i], Hb[i]
    else:
        raise SystemExit("unknown mode")
    js["near_states"], js["bulk_states"] = len(nkeys), len(bulk)
    js["H_min"] = min(G + Hb)
    json.dump(js, open(dst + ".json", "w"))
    open(dst + ".near_keys", "wb").write(struct.pack("<%dQ" % len(nkeys), *nkeys))
    open(dst + ".seam_H", "wb").write(struct.pack("<%dq" % (len(G) + 3 * len(Hb)), *(G + Hb + Hb + Hb)))
    open(dst + ".bulk_states", "w").write("".join(bulk))


main()
