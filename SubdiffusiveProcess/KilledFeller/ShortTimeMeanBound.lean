module

public import SubdiffusiveProcess.KilledFeller.ShortTimeNormalization
public import SubdiffusiveProcess.KilledFeller.BoundedMajorant

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Set MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal ZeroAtInfty BoundedContinuousFunction

noncomputable section
namespace SubdiffusiveProcess.KilledFeller

def killedResolventScalar {d : ℕ} (U : Set (SpatialCoordinates d))
    (g : SpatialCoordinates d →ᵇ ℝ) (lam : ℝ) (mu : Measure (DiffusionPath d)) : ℝ :=
  ∫ w, (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * killedTest U g w t) ∂mu

theorem abs_normalized_killedResolventScalar_le {d : ℕ}
    (U : Set (SpatialCoordinates d)) (_hU : IsOpen U)
    (g : SpatialCoordinates d →ᵇ ℝ) (lam : ℝ) (hlam : 0 < lam)
    (mu : Measure (DiffusionPath d)) [IsProbabilityMeasure mu] :
    |lam * killedResolventScalar U g lam mu| ≤ ‖g‖ := by
  rw [killedResolventScalar, ← integral_const_mul, ← Real.norm_eq_abs]
  have hb : ∀ w : DiffusionPath d,
      ‖lam * (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * killedTest U g w t)‖ ≤ ‖g‖ := by
    intro w
    rw [Real.norm_eq_abs]
    exact abs_normalized_killedLaplace_le U g w hlam
  calc
    ‖∫ w, lam * (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * killedTest U g w t) ∂mu‖ ≤
        ∫ _ : DiffusionPath d, ‖g‖ ∂mu :=
      norm_integral_le_of_norm_le (integrable_const ‖g‖) (Eventually.of_forall hb)
    _ = ‖g‖ := by simp only [integral_const, probReal_univ, one_smul]

theorem normalized_killedResolventScalar_bound {d : ℕ}
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (g : SpatialCoordinates d →ᵇ ℝ) (hzero : ∀ x ∉ U, g x = 0)
    (lam h r m : ℝ) (hlam : 0 < lam) (hh : 0 < h) (hr : 0 < r) (hm : 0 ≤ m)
    (hmod : ∀ x y, dist x y ≤ r → |g x - g y| ≤ m)
    (mu : Measure (DiffusionPath d)) [IsProbabilityMeasure mu]
    (x : SpatialCoordinates d) (hstart : ∀ᵐ w ∂mu, w 0 = x) :
    |lam * killedResolventScalar U g lam mu - g x| ≤ m + 2 * ‖g‖ *
      (Real.exp (-lam * h) + mu.real {w | ∃ t : ℝ≥0, (t : ℝ) ≤ h ∧ r < dist (w t) x}) := by
  have hb := SubdiffusiveProcess.KilledFeller.killed_resolvent_normalization_bound
    U hU g hzero lam h r m hlam hh hr hm hmod mu x hstart
  simpa only [indicator_exp_eq_exp_killedTest, killedResolventScalar] using hb

/-- Integrating the compact-path displacement bound gives the paper's short-time
normalization estimate for a C₀ resolvent test. -/
theorem integral_normalization_norm_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set (SpatialCoordinates d)) (hU : IsOpen U)
    (g : SpatialCoordinates d →ᵇ ℝ) (hzero : ∀ x ∉ U, g x = 0)
    (f : C₀(↥U, ℝ)) (hf : ∀ x : ↥U, f x = g x.1)
    (lam : ℝ) (hlam : 0 < lam) (h : ℝ≥0) (hh : 0 < h)
    (r m : ℝ) (hr : 0 < r) (hm : 0 ≤ m)
    (hmod : ∀ x y, dist x y ≤ r → |g x - g y| ≤ m)
    (K : Kernel (Ω × SpatialCoordinates d) (DiffusionPath d)) (hK : IsMarkovKernel K)
    (hstart : ∀ᵐ omega ∂P, ∀ x ∈ U, ∀ᵐ w ∂K (omega, x), w 0 = x)
    (Kset : Set (DiffusionPath d))
    (hsmall : ∀ w ∈ Kset, ∀ t : ℝ≥0, t ≤ h → dist (w t) (w 0) < r)
    (G : Ω → ℝ≥0∞) (hG : Measurable G) (eta : ℝ) (heta : 0 ≤ eta)
    (hmajorant : ∀ omega, ∀ x ∈ U, K (omega, x) Ksetᶜ ≤ G omega)
    (hmean : ∫⁻ omega, G omega ∂P ≤ ENNReal.ofReal eta)
    (V : Ω → C₀(↥U, ℝ)) (hVmeas : StronglyMeasurable V)
    (hV : ∀ᵐ omega ∂P, ∀ x : ↥U, V omega x = killedResolventScalar U g lam (K (omega, x.1))) :
    ∫ omega, ‖lam • V omega - f‖ ∂P ≤ m + 2 * ‖g‖ * (Real.exp (-lam * h) + eta) := by
  let : IsMarkovKernel K := hK
  have hEmeas : AEStronglyMeasurable (fun omega => ‖lam • V omega - f‖) P :=
    ((hVmeas.const_smul lam).sub stronglyMeasurable_const).norm.aestronglyMeasurable
  have hEbound : ∀ᵐ omega ∂P, ‖lam • V omega - f‖ ≤ 2 * ‖g‖ := by
    filter_upwards [hV] with omega hω
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    change ‖lam * V omega x - f x‖ ≤ 2 * ‖g‖
    rw [Real.norm_eq_abs, hω x, hf x]
    have h1 := abs_normalized_killedResolventScalar_le U hU g lam hlam (K (omega, x.1))
    have h2 : |g x.1| ≤ ‖g‖ := by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x.1
    exact (abs_sub _ _).trans (by linarith)
  have hEint : Integrable (fun omega => ‖lam • V omega - f‖) P := by
    apply (integrable_const (2 * ‖g‖)).mono' hEmeas
    simpa only [norm_norm] using hEbound
  let C : ℝ := m + 2 * ‖g‖ * Real.exp (-lam * h)
  have hBint := integrable_boundedMajorant P G hG
  have hMInt : Integrable (fun omega => C + 2 * ‖g‖ * boundedMajorant (G omega)) P :=
    (integrable_const C).add (hBint.const_mul _)
  have hcompare : ∀ᵐ omega ∂P,
      ‖lam • V omega - f‖ ≤ C + 2 * ‖g‖ * boundedMajorant (G omega) := by
    filter_upwards [hstart, hV] with omega hs hv
    have hBpos := boundedMajorant_nonneg (G omega)
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    apply (BoundedContinuousFunction.norm_le (by dsimp only [C]; positivity)).mpr
    intro x
    change ‖lam * V omega x - f x‖ ≤ C + 2 * ‖g‖ * boundedMajorant (G omega)
    rw [Real.norm_eq_abs, hv x, hf x]
    have hd := SubdiffusiveProcess.KilledFeller.displacement_measure_le_of_compact
      Kset r h hsmall (K (omega, x.1)) x.1 (hs x.1 x.2)
    have hd' : K (omega, x.1) {w | ∃ t : ℝ≥0, (t : ℝ) ≤ (h : ℝ) ∧ r < dist (w t) x.1}
        ≤ G omega := by
      simpa only [NNReal.coe_le_coe] using hd.trans (hmajorant omega x.1 x.2)
    have hdreal := measureReal_le_boundedMajorant (K (omega, x.1)) _ (G omega) hd'
    have hb := normalized_killedResolventScalar_bound U hU g hzero lam h r m hlam
      (NNReal.coe_pos.mpr hh) hr hm hmod (K (omega, x.1)) x.1 (hs x.1 x.2)
    calc
      _ ≤ m + 2 * ‖g‖ * (Real.exp (-lam * h) + boundedMajorant (G omega)) := by
        exact hb.trans (by gcongr)
      _ = _ := by dsimp only [C]; ring
  have hI := integral_mono_ae hEint hMInt hcompare
  rw [integral_add (integrable_const C) (hBint.const_mul _), integral_const,
    probReal_univ, one_smul, integral_const_mul] at hI
  have hB := integral_boundedMajorant_le P G hG eta heta hmean
  calc
    _ ≤ C + 2 * ‖g‖ * (∫ omega, boundedMajorant (G omega) ∂P) := hI
    _ ≤ C + 2 * ‖g‖ * eta := by gcongr
    _ = _ := by dsimp only [C]; ring

end SubdiffusiveProcess.KilledFeller
