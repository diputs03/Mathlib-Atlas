import json, sys

path = sys.argv[1]
TOTAL_MATHLIB = 574391  # from 06_module_statistics

caps = [8_000, 16_000, 32_000, 64_000]
proj = {c: 0 for c in caps}
fixed_tot = 0
n = 0
sidecar_true = 0  # bytes of all ast/str material NOT inline at 64k (approximation)
with open(path, "rb") as fh:
    for raw in fh:
        r = json.loads(raw)
        n += 1
        ta = r.get("typeAstBytes", 0) if r.get("typeAst") is not None else 0
        va = r.get("valueAstBytes", 0) if r.get("valueAst") is not None else 0
        # fixed = record size with both inline ASTs removed
        fixed = len(raw) - ta - va
        fixed_tot += fixed
        for c in caps:
            proj[c] += fixed
            if r.get("typeAst") is not None and r["typeAstBytes"] <= c:
                proj[c] += r["typeAstBytes"]
            if r.get("valueAst") is not None and r["valueAstBytes"] <= c:
                proj[c] += r["valueAstBytes"]

print(f"sample records: {n}")
for c in caps:
    sample_mb = proj[c]/1e6
    full_gb = proj[c]/n*TOTAL_MATHLIB/1e9
    print(f"astInlineCap={c:>6}: sample main {sample_mb:7.1f} MB  -> projected full main {full_gb:6.1f} GB")
fixed_full = fixed_tot/n*TOTAL_MATHLIB/1e9
print(f"fixed/metadata+strings only -> {fixed_full:.1f} GB")
