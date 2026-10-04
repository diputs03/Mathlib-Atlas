import json, sys, statistics

path = sys.argv[1]
tot = 0
type_bytes = []
value_bytes = []
meta_bytes = []
full = []
no_value = []   # record size if inline value removed
inline_vals = 0
n = 0
buckets = [0,1e3,5e3,1e4,5e4,1e5,5e5,1e6,1e9]
bcount = [0]*(len(buckets))

with open(path, "rb") as fh:
    for raw in fh:
        r = json.loads(raw)
        full_b = len(raw)
        tb = len(r.get("typeStr","").encode()) + len(json.dumps(r.get("typeAst"),ensure_ascii=False).encode())
        if r.get("valueAst") is not None:
            vb = len(r.get("valueStr","").encode()) + len(json.dumps(r["valueAst"],ensure_ascii=False).encode())
            inline_vals += 1
        else:
            vb = 0
        full.append(full_b); type_bytes.append(tb); value_bytes.append(vb)
        no_value.append(full_b - vb)
        for i in range(len(buckets)-1):
            if buckets[i] <= full_b < buckets[i+1]:
                bcount[i]+=1; break
        n += 1

def pct(x,p):
    x=sorted(x); k=int(p/100*(len(x)-1)); return x[k]

print(f"records={n}  inline values={inline_vals} ({inline_vals/n:.1%})")
print(f"TOTAL full={sum(full)/1e6:.1f}MB  types={sum(type_bytes)/1e6:.1f}MB  inline values={sum(value_bytes)/1e6:.1f}MB")
print(f"types-only corpus would be {sum(no_value)/1e6:.1f}MB")
print("full record bytes: p50=%.0f p90=%.0f p99=%.0f max=%.0f" % (pct(full,50),pct(full,90),pct(full,99),max(full)))
print("type-only bytes:   p50=%.0f p90=%.0f p99=%.0f max=%.0f" % (pct(no_value,50),pct(no_value,90),pct(no_value,99),max(no_value)))
print("full-size buckets:")
for i in range(len(buckets)-1):
    print(f"  {buckets[i]:>9.0f}..{buckets[i+1]:>9.0f}: {bcount[i]}")
