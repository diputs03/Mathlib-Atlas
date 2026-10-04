import json, re, sys

path = sys.argv[1]
sizes = []
name_re = re.compile(r'"name"\s*:\s*"((?:[^"\\]|\\.)*)"')
kind_re = re.compile(r'"kind"\s*:\s*"([^"]*)"')
total = 0
with open(path, "rb") as fh:
    for i, raw in enumerate(fh):
        n = len(raw)
        total += n
        head = raw[:400].decode("utf-8", "replace")
        nm = name_re.search(head)
        kd = kind_re.search(head)
        sizes.append((n, nm.group(1) if nm else "?", kd.group(1) if kd else "?"))

sizes.sort(reverse=True)
print("records:", len(sizes), "total_MB: %.1f" % (total/1e6))
import statistics
vals = [s for s,_,_ in sizes]
print("min/median/mean/max bytes: %d / %d / %d / %d" % (
    min(vals), int(statistics.median(vals)), int(total/len(vals)), max(vals)))
# buckets
buckets = [(0,1e3),(1e3,1e4),(1e4,1e5),(1e5,1e6),(1e6,1e7),(1e7,1e9)]
for lo,hi in buckets:
    c = sum(1 for v in vals if lo <= v < hi)
    print(f"  {lo:>9.0f}..{hi:>9.0f}: {c}")
print("top 15 largest:")
for s,nm,kd in sizes[:15]:
    print(f"  {s/1e6:9.2f} MB  {kd:10} {nm[:90]}")
