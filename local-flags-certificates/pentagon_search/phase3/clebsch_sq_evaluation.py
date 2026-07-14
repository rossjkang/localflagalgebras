#!/usr/bin/env python3
"""Evaluate ⟦f²⟧, ⟦g²⟧, ⟦h²⟧, ⟦ℓ²⟧ separately at Clebsch's profile.

These are the four "PSD-square" components of the BRRB size-5 cert:
- cs0 = 120⟦f²⟧ + 120⟦g²⟧ at type σ_6 = K_{1,2} BBR
- cs1 = 120⟦h²⟧ + 120⟦ℓ²⟧ at type σ_7 = K_{1,2} RBR

Each ⟦X²⟧ ≥ 0 by PSD structure. If any is near zero at Clebsch, the
corresponding PSD constraint is "tight" there (Clebsch saturates it);
if any is much above zero, there's a structural slack.
"""
fsq_x4 = [0,0,0,16,0,0,0,-4,0,0, -8,0,4,0,0,0,0,1,0,0,
          0,-4,0,0,0,0,0,0,0,0, -16,0,12,0,0,0,0,0,0,1,
          0,0,0,0,0,0,0,0,0,0, 0,0,0,0,1,0,0,0]

gsq_x4 = [0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,1,0,0,
          0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,-1,
          0,0,0,0,0,0,0,0,0,0, 0,0,0,0,-1,0,0,0]

hsq_x2 = [0,0,0,0,0,0,0,0,-4,0, 0,0,0,0,2,4,0,0,0,0,
          0,0,0,0,1,0,0,0,0,0, 0,0,0,3,0,0,-2,0,0,0,
          0,0,0,0,0,0,0,0,0,0, 0,0,0,0,-4,0,0,0]

lsq_x2 = [0,0,0,0,12,0,0,0,0,0, 0,-8,0,0,8,4,4,0,0,0,
          0,0,0,-8,4,0,0,0,0,0, 0,-16,0,12,0,0,-4,0,0,0,
          0,0,0,0,0,0,0,0,0,0, 0,0,0,0,-8,0,0,0]

# Densities from clebsch_profile.tsv (Δ=5 normalisation, φ(F1) = 1)
# Count: F_i count at Clebsch with v_star=0; φ(F_i) = count / 120.
counts = {
    1: 120, 4: 120, 5: 120, 6: 120, 8: 60, 9: 120, 12: 120, 14: 60, 15: 120,
    16: 120, 17: 120, 18: 120, 22: 120, 23: 120, 24: 120, 25: 120, 27: 60,
    29: 120, 35: 60, 36: 60, 37: 120, 40: 60, 42: 120, 43: 120, 44: 120,
    46: 120, 47: 120, 49: 120, 50: 120, 54: 120, 55: 120, 56: 120
}
densities = [counts.get(i, 0) / 120 for i in range(1, 59)]

def eval_vec(vec, scale_div, name):
    val = sum(vec[i] * densities[i] for i in range(58)) / scale_div
    contribs = [(i+1, vec[i], densities[i], vec[i]*densities[i]/scale_div) for i in range(58) if vec[i] != 0]
    return val, contribs, name

f, fc, _ = eval_vec(fsq_x4, 4.0, "120⟦f²⟧")
g, gc, _ = eval_vec(gsq_x4, 4.0, "120⟦g²⟧")
h, hc, _ = eval_vec(hsq_x2, 2.0, "120⟦h²⟧")
l, lc, _ = eval_vec(lsq_x2, 2.0, "120⟦ℓ²⟧")

print("=" * 78)
print("PSD-square components at Clebsch (φ(F_1) = 1 normalisation)")
print("=" * 78)
print(f"  120⟦f²⟧ (σ_6 BBR) = {f:+.6f}")
print(f"  120⟦g²⟧ (σ_6 BBR) = {g:+.6f}")
print(f"  120⟦h²⟧ (σ_7 RBR) = {h:+.6f}")
print(f"  120⟦ℓ²⟧ (σ_7 RBR) = {l:+.6f}")
print()
print(f"  cs0 = 120⟦f²⟧ + 120⟦g²⟧ = {f + g:+.6f}")
print(f"  cs1 = 120⟦h²⟧ + 120⟦ℓ²⟧ = {h + l:+.6f}")
print()
print("Interpretation:")
print("  Each ⟦X²⟧ ≥ 0 always (PSD-square structure).")
print("  Value ≈ 0 means Clebsch saturates that PSD constraint.")
print("  Large value = PSD has slack at Clebsch.")
print()

# Breakdown by flag
print("Per-flag breakdown of 120⟦f²⟧ at Clebsch:")
for fid, coef, d, contrib in fc:
    if d > 0 and contrib != 0:
        print(f"  F{fid}: coef={coef:>4}, φ={d:.3f}, contrib={contrib:+.4f}")

print()
print("Per-flag breakdown of 120⟦h²⟧ at Clebsch:")
for fid, coef, d, contrib in hc:
    if d > 0 and contrib != 0:
        print(f"  F{fid}: coef={coef:>4}, φ={d:.3f}, contrib={contrib:+.4f}")

print()
print("Per-flag breakdown of 120⟦ℓ²⟧ at Clebsch:")
for fid, coef, d, contrib in lc:
    if d > 0 and contrib != 0:
        print(f"  F{fid}: coef={coef:>4}, φ={d:.3f}, contrib={contrib:+.4f}")
