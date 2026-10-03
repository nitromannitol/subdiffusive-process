module

public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Frozen.Assumptions.PotentialSample

@[expose] public section

/-! Pointwise differences of the convergent infrared partial sums. -/

open Filter Topology

namespace SubdiffusiveProcess

/-- The anchored constant disappears when two spatial evaluations are subtracted. -/
theorem tendsto_infrared_tail_difference {d : ℕ} (omega : BilateralField d)
    (H : C(SpatialCoordinates d, ℝ))
    (hH : Tendsto (infraredPartialSum omega) atTop (nhds H))
    (x y : SpatialCoordinates d) :
    Tendsto (fun L : ℕ => ∑ n ∈ Finset.range L,
      (omega (Int.ofNat (n + 1)) x - omega (Int.ofNat (n + 1)) y))
      atTop (nhds (H x - H y)) := by
  have hx : Tendsto (fun L => infraredPartialSum omega L x) atTop (nhds (H x)) :=
    (continuous_eval_const x).tendsto H |>.comp hH
  have hy : Tendsto (fun L => infraredPartialSum omega L y) atTop (nhds (H y)) :=
    (continuous_eval_const y).tendsto H |>.comp hH
  convert hx.sub hy using 1
  funext L
  simp only [infraredPartialSum, ContinuousMap.sum_apply, Finset.sum_sub_distrib,
    ContinuousMap.sub_apply, ContinuousMap.const_apply]
  abel

/-- The same tail after relabelling the layers and scaling both spatial points. -/
theorem tendsto_relabelled_infrared_tail_difference {d : ℕ} (omega : BilateralField d)
    (H : C(SpatialCoordinates d, ℝ))
    (hH : Tendsto (infraredPartialSum omega) atTop (nhds H))
    (N : ℕ) (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ i v, eta i v = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • v))
    (x y : SpatialCoordinates d) :
    Tendsto (fun L : ℕ => ∑ n ∈ Finset.range L,
      (eta (N + n + 1) ((3 : ℝ) ^ N • x) -
        eta (N + n + 1) ((3 : ℝ) ^ N • y)))
      atTop (nhds (H x - H y)) := by
  convert tendsto_infrared_tail_difference omega H hH x y using 1
  funext L
  apply Finset.sum_congr rfl
  intro n hn
  rw [hEta, hEta]
  have hscale (v : SpatialCoordinates d) :
      ((3 : ℝ) ^ (-(N : ℤ))) • ((3 : ℝ) ^ N • v) = v := by
    rw [smul_smul, ← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    simp
  rw [hscale, hscale]
  have hi : ((N + n + 1 : ℕ) : ℤ) - (N : ℤ) = Int.ofNat (n + 1) := by
    simp only [Nat.cast_add, Nat.cast_one, Int.ofNat_eq_natCast]
    omega
  rw [hi]

end SubdiffusiveProcess
