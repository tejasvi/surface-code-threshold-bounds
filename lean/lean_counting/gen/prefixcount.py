"""prefixcount.py: number of listed states by prefix of candidate indices (digits 2*step + label), for sizing the
start-completeness chunks of the kernel route (untrusted helper).

usage: python3 -I -B gen/prefixcount.py STATES n DEPTH [TOP]
"""
import sys
from collections import Counter


def main():
    sfile, n, depth = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    top = int(sys.argv[4]) if len(sys.argv) > 4 else 10
    cnt = Counter()
    for line in open(sfile):
        line = line.strip()
        if not line:
            continue
        ds, ls = line.split()
        js = tuple(2 * int(d) + (1 if l == "C" else 0) for d, l in zip(ds[:depth], ls[:depth]))
        cnt[js] += 1
    tot = sum(cnt.values())
    print("prefixes with states:", len(cnt), "states:", tot, "max:", max(cnt.values()))
    for js, c in cnt.most_common(top):
        print(list(js), c)


main()
