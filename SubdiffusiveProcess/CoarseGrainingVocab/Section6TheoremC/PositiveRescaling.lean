module

public import SubdiffusiveProcess.Assumptions.Cutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.NormalizedL2
public import SubdiffusiveProcess.Frozen.Section6.Defs.AnchoredCutoff
public import SubdiffusiveProcess.Frozen.Section6.Defs.CoefficientAt

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration (normalizedL2On_const_mul)

noncomputable section

variable {d : ℕ}

/-! ### Pointwise algebra -/

/-- The Euclidean magnitude of a square-root-rescaled vector field. -/
theorem euclideanNorm_sqrt_mul_smul {c r : ℝ} (hc : 0 ≤ c)
    (v : Vec d) :
    euclideanNorm (Real.sqrt (c * r) • v) =
      Real.sqrt c * euclideanNorm (Real.sqrt r • v) := by
  rw [euclideanNorm_smul, euclideanNorm_smul, Real.sqrt_mul hc,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
    abs_of_nonneg (Real.sqrt_nonneg _), mul_assoc]

/-! ### Rescaling of the averaged seminorms -/

/-- The energy seminorm of `e.large.scale.energy.multifractal` scales by `√c`
when the coefficient is multiplied by `c ≥ 0`. -/
theorem vectorNormalizedL2On_sqrt_const_smul (W : Set (Vec d)) {c : ℝ}
    (hc : 0 ≤ c) (a : Vec d → ℝ) (g : Vec d → Vec d) :
    vectorNormalizedL2On W (fun x ↦ Real.sqrt (c * a x) • g x) =
      Real.sqrt c * vectorNormalizedL2On W (fun x ↦ Real.sqrt (a x) • g x) := by
  have hpt : (fun x : Vec d ↦ euclideanNorm (Real.sqrt (c * a x) • g x)) =
      fun x ↦ Real.sqrt c * euclideanNorm (Real.sqrt (a x) • g x) := by
    funext x
    exact euclideanNorm_sqrt_mul_smul hc (g x)
  rw [vectorNormalizedL2On, hpt, normalizedL2On_const_mul W (Real.sqrt c),
    abs_of_nonneg (Real.sqrt_nonneg c), vectorNormalizedL2On]

/-! ### Invariance of the weak equation -/

/-- Weak harmonicity is invariant under multiplying the coefficient by a
nonzero constant.  This is the "changes neither the equation" half. -/
theorem isWeaklyHarmonicOn_const_smul_iff {c : ℝ} (hc : c ≠ 0)
    (a : Vec d → ℝ) (W : Set (Vec d)) (u : H1Function W) :
    IsWeaklyHarmonicOn (fun x ↦ c * a x) W u ↔ IsWeaklyHarmonicOn a W u := by
  have hrw : ∀ φ : H10Function W,
      ∫ x in W, vecDot ((c * a x) • u.grad x)
          (φ.toH1Function.grad x) ∂volume =
        c * ∫ x in W, vecDot (a x • u.grad x)
          (φ.toH1Function.grad x) ∂volume := by
    intro φ
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [mul_smul, vecDot_smul_left]
  constructor
  · intro h φ
    have := h φ
    rw [hrw φ] at this
    exact (mul_eq_zero.1 this).resolve_left hc
  · intro h φ
    rw [hrw φ, h φ, mul_zero]

/-! ### Invariance of the energy estimate -/

/-- The two-sided energy estimate `e.large.scale.energy.multifractal` is
invariant under multiplying the coefficient by a positive constant: this is the
"nor the estimate" half. -/
theorem energyEstimate_const_smul_iff {c : ℝ} (hc : 0 < c)
    (a : Vec d → ℝ) (V W : Set (Vec d)) (K : ℝ)
    (g : Vec d → Vec d) :
    vectorNormalizedL2On V (fun x ↦ Real.sqrt (c * a x) • g x) ≤
        K * vectorNormalizedL2On W (fun x ↦ Real.sqrt (c * a x) • g x) ↔
      vectorNormalizedL2On V (fun x ↦ Real.sqrt (a x) • g x) ≤
        K * vectorNormalizedL2On W (fun x ↦ Real.sqrt (a x) • g x) := by
  rw [vectorNormalizedL2On_sqrt_const_smul V hc.le a,
    vectorNormalizedL2On_sqrt_const_smul W hc.le a]
  rw [show K * (Real.sqrt c * vectorNormalizedL2On W
      (fun x ↦ Real.sqrt (a x) • g x)) =
    Real.sqrt c * (K * vectorNormalizedL2On W
      (fun x ↦ Real.sqrt (a x) • g x)) by ring]
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  exact ⟨fun h ↦ le_of_mul_le_mul_left h hs,
    fun h ↦ mul_le_mul_of_nonneg_left h hs.le⟩

/-! ### The two normalizations of the finite cutoff -/

/-- At a finite cutoff, `coefficientAt` is the unnormalized coefficient. -/
@[simp]
theorem coefficientAt_natCast (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) :
    coefficientAt M (n : WithTop ℕ) ω =
      _root_.SubdiffusiveProcess.Model.aCutoff M n ω.1 :=
  rfl

/-- The anchored cutoff `ã_L` of `e.fixed.clock.coefficient` is positive. -/
theorem anchoredCutoff_pos (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (x : Vec d) :
    0 < anchoredCutoff M n ω x :=
  div_pos (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n ω x)
    (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n ω 0)

/-- `coefficientAt` at a finite cutoff is the positive multiple
`a_L(0) · ã_L` of the anchored cutoff appearing in
`l.finite.cutoff.coefficient.convergence`. -/
theorem coefficientAt_natCast_eq_const_mul_anchoredCutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) :
    coefficientAt M (n : WithTop ℕ) ω =
      fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M n ω.1 0 *
        anchoredCutoff M n ω.1 x := by
  funext x
  have hne : _root_.SubdiffusiveProcess.Model.aCutoff M n ω.1 0 ≠ 0 :=
    (_root_.SubdiffusiveProcess.Model.aCutoff_pos M n ω.1 0).ne'
  rw [coefficientAt_natCast, anchoredCutoff, mul_div_cancel₀ _ hne]

/-- The normalizing constant `a_L(0)` is positive. -/
theorem aCutoff_origin_pos (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 < _root_.SubdiffusiveProcess.Model.aCutoff M n ω 0 :=
  _root_.SubdiffusiveProcess.Model.aCutoff_pos M n ω 0

/-- A function is `coefficientAt M (n : ℕ) ω`-harmonic exactly when it is
`ã_n`-harmonic: the normalization  is invisible to
the equation. -/
theorem isWeaklyHarmonicOn_coefficientAt_iff_anchoredCutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) (W : Set (Vec d))
    (u : H1Function W) :
    IsWeaklyHarmonicOn (coefficientAt M (n : WithTop ℕ) ω) W u ↔
      IsWeaklyHarmonicOn (anchoredCutoff M n ω.1) W u := by
  rw [coefficientAt_natCast_eq_const_mul_anchoredCutoff]
  exact isWeaklyHarmonicOn_const_smul_iff
    (aCutoff_origin_pos M n ω.1).ne' _ _ _

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
