import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import SubdiffusiveProcess.Lane1.WeightedIndep
import SubdiffusiveProcess.Lane1.ChaosBasic
import SubdiffusiveProcess.Lane1.TestFunctionMartingale

/-!
# The mean survives in the limit

A nonnegative sequence with constant positive mean, bounded in `L^p` for some
`p ≥ 2`, and converging almost surely, cannot converge to zero: the `L^p`
bound makes the truncation error uniformly small, and dominated convergence
applies to the truncations.  This is the uniform-integrability input of the
full-support argument, in the only form it is used.
-/

open Filter MeasureTheory

noncomputable section
namespace SubdiffusiveProcess

/-- The elementary truncation bound: `(x - c)⁺ ≤ x ^ p / c ^ (p-1)` for
nonnegative `x` and positive `c`. -/
theorem sub_min_le_pow_div {x c : ℝ} (hx : 0 ≤ x) (hc : 0 < c) {p : ℕ}
    (hp : 2 ≤ p) : x - min x c ≤ x ^ p / c ^ (p - 1) := by
  rcases le_or_gt x c with h | h
  · rw [min_eq_left h]
    simp only [sub_self]
    positivity
  · rw [min_eq_right h.le]
    have hcp : (0 : ℝ) < c ^ (p - 1) := by positivity
    rw [le_div_iff₀ hcp]
    have hxc : c ^ (p - 1) ≤ x ^ (p - 1) := by
      exact pow_le_pow_left₀ hc.le h.le _
    have hsucc : (p - 1) + 1 = p := by omega
    calc (x - c) * c ^ (p - 1) ≤ x * x ^ (p - 1) := by
          refine mul_le_mul (by linarith) hxc (by positivity) (by linarith)
      _ = x ^ p := by rw [← pow_succ', hsucc]

/-- A nonnegative, `L^p`-bounded sequence with constant positive mean does not
converge almost surely to zero. -/
theorem not_ae_eq_zero_of_mean_pos
    {Om : Type*} {m0 : MeasurableSpace Om} {P : Measure Om}
    [IsProbabilityMeasure P]
    (X : ℕ → Om → ℝ) (Xinf : Om → ℝ)
    (hXnn : ∀ (N : ℕ) (w : Om), 0 ≤ X N w)
    (hint : ∀ N, Integrable (X N) P)
    (hmeas : ∀ N, AEStronglyMeasurable (X N) P)
    (hmean : ∀ N, ∫ w, X N w ∂P = ∫ w, X 0 w ∂P)
    (hm0 : 0 < ∫ w, X 0 w ∂P)
    (p : ℕ) (hp : 2 ≤ p) (Cmom : ℝ)
    (hintp : ∀ N, Integrable (fun w => (X N w) ^ p) P)
    (hmom : ∀ N, ∫ w, (X N w) ^ p ∂P ≤ Cmom)
    (hconv : ∀ᵐ w ∂P, Tendsto (fun N => X N w) atTop (nhds (Xinf w))) :
    ¬ (∀ᵐ w ∂P, Xinf w = 0) := by
  intro hzero
  set m : ℝ := ∫ w, X 0 w ∂P with hmdef
  have hCmom : 0 ≤ Cmom :=
    le_trans (integral_nonneg fun w => pow_nonneg (hXnn 0 w) p) (hmom 0)
  set c : ℝ := 2 * Cmom / m + 1 with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    have : (0 : ℝ) ≤ 2 * Cmom / m := by positivity
    linarith
  have hc1 : (1 : ℝ) ≤ c := by
    rw [hcdef]
    have : (0 : ℝ) ≤ 2 * Cmom / m := by positivity
    linarith
  have hcp : (2 : ℝ) * Cmom / m ≤ c ^ (p - 1) := by
    have h1 : (2 : ℝ) * Cmom / m ≤ c := by rw [hcdef]; linarith
    have h2 : c ≤ c ^ (p - 1) := by
      calc c = c ^ 1 := (pow_one c).symm
        _ ≤ c ^ (p - 1) := pow_le_pow_right₀ hc1 (by omega)
    linarith
  have htrunc : ∀ N : ℕ, m / 2 ≤ ∫ w, min (X N w) c ∂P := by
    intro N
    have hminint : Integrable (fun w => min (X N w) c) P := by
      refine Integrable.mono' (integrable_const c) (((hmeas N).inf aestronglyMeasurable_const :
        AEStronglyMeasurable (fun w => min (X N w) c) P)) ?_
      filter_upwards with w
      rw [Real.norm_of_nonneg (le_min (hXnn N w) hcpos.le)]
      exact min_le_right _ _
    have hdiff : ∫ w, (X N w - min (X N w) c) ∂P ≤ Cmom / c ^ (p - 1) := by
      have hb : ∀ w, X N w - min (X N w) c ≤ (X N w) ^ p / c ^ (p - 1) :=
        fun w => sub_min_le_pow_div (hXnn N w) hcpos hp
      have hdivint : Integrable (fun w => (X N w) ^ p / c ^ (p - 1)) P :=
        (hintp N).div_const _
      refine le_trans (integral_mono ((hint N).sub hminint) hdivint hb) ?_
      rw [integral_div]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact hmom N
    have hsplit : ∫ w, (X N w - min (X N w) c) ∂P
        = m - ∫ w, min (X N w) c ∂P := by
      rw [integral_sub (hint N) hminint, hmean N]
    rw [hsplit] at hdiff
    have hCc : Cmom / c ^ (p - 1) ≤ m / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h2 : 2 * Cmom ≤ m * c ^ (p - 1) := by
        rw [div_le_iff₀ hm0] at hcp
        linarith
      linarith
    linarith
  have hlim : Tendsto (fun N => ∫ w, min (X N w) c ∂P) atTop (nhds 0) := by
    have hae : ∀ᵐ w ∂P, Tendsto (fun N => min (X N w) c) atTop (nhds 0) := by
      filter_upwards [hconv, hzero] with w hw hw0
      have hc' : Tendsto (fun _ : ℕ => c) atTop (nhds c) := tendsto_const_nhds
      have hmin := hw.min hc'
      rw [hw0] at hmin
      simpa [min_eq_left hcpos.le] using hmin
    have hdom := tendsto_integral_of_dominated_convergence (F := fun N w => min (X N w) c)
      (f := fun _ : Om => (0 : ℝ)) (bound := fun _ => c) ?_ ?_ ?_ hae
    · simpa using hdom
    · exact fun N => ((hmeas N).inf aestronglyMeasurable_const :
        AEStronglyMeasurable (fun w => min (X N w) c) P)
    · exact integrable_const c
    · intro N
      filter_upwards with w
      rw [Real.norm_of_nonneg (le_min (hXnn N w) hcpos.le)]
      exact min_le_right _ _
  have hge : (0 : ℝ) ≥ m / 2 := ge_of_tendsto hlim (Filter.Eventually.of_forall htrunc)
  linarith

/-- Every cutoff measure charges every cube: its density is continuous and
strictly positive. -/
theorem weightedChaosCutoff_centeredCube_pos
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    0 < ((weightedChaosCutoff M H N omega)
      (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  rw [weightedChaosCutoff_centeredCube_toReal_eq_integral M H N omega z r hr]
  have hgpos : ∀ x, 0 < Real.exp (H omega x) * fineDensity M N omega x :=
    fun x => mul_pos (Real.exp_pos _) (fineDensity_pos M N omega x)
  have hint := weightedFineDensity_integrableOn_cube M H N omega z r hr
  have hsupp : Function.support
      (fun x => Real.exp (H omega x) * fineDensity M N omega x) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true, ne_eq]
    exact ne_of_gt (hgpos x)
  refine (integral_pos_iff_support_of_nonneg (fun x => (hgpos x).le) hint).mpr ?_
  rw [hsupp, Measure.restrict_apply_univ]
  rw [centeredCube_volume z hr]
  exact ENNReal.ofReal_pos.mpr (pow_pos hr d)

end SubdiffusiveProcess
