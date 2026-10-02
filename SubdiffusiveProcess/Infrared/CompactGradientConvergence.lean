import SubdiffusiveProcess.Analysis.CompactGradientLipschitz
import SubdiffusiveProcess.Main.PositiveAnchoredInfraredTruncation
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.LipschitzLimit
import SubdiffusiveProcess.Frozen.Assumptions.IsAnchoredC11Limit
import Mathlib.Tactic

open Filter Set TopologicalSpace
open scoped Topology
open SubdiffusiveProcess
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section
namespace SubdiffusiveProcess.Infrared

/-- A Lipschitz certificate bounds the exact compact derivative observable. -/
theorem compactGradientLipschitzObservable_le {d : ℕ}
    (K : Compacts (SpatialCoordinates d)) (g : PotentialField d)
    (c : ℝ) (hc : 0 ≤ c)
    (h : LipschitzOnWith (Real.toNNReal c) (PotentialField.deriv g)
      (K : Set (SpatialCoordinates d))) :
    compactGradientLipschitzObservable K g ≤ c := by
  apply Real.sSup_le _ hc
  rintro a ⟨x, y, hxy, rfl⟩
  have hd : 0 < ‖(x : SpatialCoordinates d) - y‖ := by
    rw [← dist_eq_norm]
    exact dist_pos.mpr (fun he => hxy (Subtype.ext he))
  apply (div_le_iff₀ hd).2
  simpa only [dist_eq_norm, Real.coe_toNNReal _ hc] using
    h.dist_le_mul x x.property y y.property

/-- Anchored C11 convergence includes convergence of the derivative Lipschitz seminorm. -/
theorem tendsto_compactGradientLipschitzObservable {d : ℕ}
    (f : PotentialSample d) (g : PotentialField d)
    (h : IsAnchoredC11Limit f g) (K : Compacts (SpatialCoordinates d)) :
    Tendsto (fun L => compactGradientLipschitzObservable K
      (PotentialField.add (anchoredPartialSumField f L) (PotentialField.scale (-1) g)))
      atTop (nhds 0) := by
  have hscale (x : SpatialCoordinates d) :
      PotentialField.deriv (PotentialField.scale (-1) g) x = -PotentialField.deriv g x := by
    change ((-1 : ℝ) • ContinuousLinearMap.id ℝ
      (SpatialCoordinates d →L[ℝ] ℝ)) (PotentialField.deriv g x) = _
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, neg_one_smul]
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨N, hN⟩ := h.deriv_lipschitz_cauchy _ K.isCompact (eps / 2) (by positivity)
  refine ⟨N, fun L hL => ?_⟩
  have hLip : LipschitzOnWith (Real.toNNReal (eps / 2))
      (fun x => PotentialField.deriv (anchoredPartialSumField f L) x -
        PotentialField.deriv g x) (K : Set (SpatialCoordinates d)) := by
    apply SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.lipschitzOnWith_sub_limit
      (fun x hx => (h.deriv_tendsto _ K.isCompact).tendsto_at hx)
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hN L n hL hn
  have hLip' : LipschitzOnWith (Real.toNNReal (eps / 2))
      (PotentialField.deriv (PotentialField.add (anchoredPartialSumField f L)
        (PotentialField.scale (-1) g))) (K : Set (SpatialCoordinates d)) := by
    change LipschitzOnWith (Real.toNNReal (eps / 2))
      (fun x => PotentialField.deriv (anchoredPartialSumField f L) x +
        PotentialField.deriv (PotentialField.scale (-1) g) x) _
    simpa only [hscale, sub_eq_add_neg] using hLip
  have hbound := compactGradientLipschitzObservable_le K _ (eps / 2) (by positivity) hLip'
  have hnonneg : 0 ≤ compactGradientLipschitzObservable K
      (PotentialField.add (anchoredPartialSumField f L) (PotentialField.scale (-1) g)) := by
    apply Real.sSup_nonneg
    rintro a ⟨x, y, hxy, rfl⟩
    exact div_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith

/-- The exclusive native truncation is the inclusive anchored sum one index earlier. -/
theorem positiveAnchoredInfraredTruncation_succ {d : ℕ}
    (omega : NativeBilateralPotentialSample d) (L : ℕ) :
    positiveAnchoredInfraredTruncation omega (L + 1) =
      anchoredPartialSumField (positiveScaledNativeLayer omega) L := by
  apply PotentialField.ext
  intro x
  induction L with
  | zero =>
      change zeroNativePotentialField d x +
        PotentialField.anchor (positiveScaledNativeLayer omega 0) x =
          PotentialField.anchor (positiveScaledNativeLayer omega 0) x
      simp only [zeroNativePotentialField, ContinuousMap.zero_apply, zero_add]
  | succ L ih =>
      change positiveAnchoredInfraredTruncation omega (L + 1) x +
        PotentialField.anchor (positiveScaledNativeLayer omega (L + 1)) x =
          anchoredPartialSumField (positiveScaledNativeLayer omega) L x +
            PotentialField.anchor (positiveScaledNativeLayer omega (L + 1)) x
      rw [ih]

/-- Native infrared truncations converge in the derivative Lipschitz seminorm. -/
theorem tendsto_native_compactGradientLipschitzObservable {d : ℕ}
    (omega : NativeBilateralPotentialSample d) (g : PotentialField d)
    (h : IsAnchoredC11Limit (positiveScaledNativeLayer omega) g)
    (K : Compacts (SpatialCoordinates d)) :
    Tendsto (fun L => compactGradientLipschitzObservable K
      (PotentialField.add (positiveAnchoredInfraredTruncation omega L)
        (PotentialField.scale (-1) g))) atTop (nhds 0) := by
  have ht := tendsto_compactGradientLipschitzObservable _ _ h K
  rw [Metric.tendsto_atTop] at ht ⊢
  intro eps heps
  obtain ⟨N, hN⟩ := ht eps heps
  refine ⟨N + 1, fun L hL => ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  rw [positiveAnchoredInfraredTruncation_succ]
  exact hN n (by omega)

end SubdiffusiveProcess.Infrared
