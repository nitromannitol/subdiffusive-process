module

public import SubdiffusiveProcess.Analysis.RawLp

public import SubdiffusiveProcess.CoarseGrainingVocab.Sensitivity

@[expose] public section

/-!
# Theta-perturbed cutoff Hölder ladder: coefficient response

This module supplies the local coefficient carrier and the direct
`l.J.sensitivity` specialization used.
The multiplier has already been normalized by its positive scalar `b`, so it
is written as a factor `t` satisfying `|t - 1| ≤ epsilon`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Filter MeasureTheory Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- A continuous near-one scalar multiplier preserves the coefficient package.

The explicit ellipticity constants are useful later when the same product
coefficient is passed to the deterministic excess theory. -/
noncomputable def scalarCoeffOnData_mul_nearOne
    {U : Ch02.Domain d} {a t : Vec d → ℝ}
    (ha : ScalarCoeffOnData U a)
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon < 1)
    (hmeasurable : AEStronglyMeasurable (fun x ↦ a x * t x)
      (volumeMeasureOn (U : Set (Vec d))))
    (ht : ∀ x ∈ (U : Set (Vec d)), |t x - 1| ≤ epsilon) :
    ScalarCoeffOnData U (fun x ↦ a x * t x) where
  lam := (1 - epsilon) * ha.lam
  Lam := (1 + epsilon) * ha.Lam
  lam_pos := mul_pos (sub_pos.mpr hepsilon1) ha.lam_pos
  lam_le_Lam := by
    have hlam0 : 0 ≤ ha.lam := ha.lam_pos.le
    have hLam0 : 0 ≤ ha.Lam := hlam0.trans ha.lam_le_Lam
    nlinarith [mul_le_mul_of_nonneg_left ha.lam_le_Lam
      (sub_nonneg.mpr hepsilon1.le)]
  aeStronglyMeasurable := by
    intro i j
    have hentry := hmeasurable.mul_const ((1 : Mat d) i j)
    refine hentry.congr ?_
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    simp only [scalarCoeffField, scalarMatrix, Matrix.smul_apply,
      smul_eq_mul, restrictCoeffField_apply_of_mem hx]
  aeBounds := by
    filter_upwards [ha.aeBounds, ae_restrict_mem U.measurableSet] with x hax hx
    have habs := abs_le.mp (ht x hx)
    have htBounds : 1 - epsilon ≤ t x ∧ t x ≤ 1 + epsilon := by
      constructor <;> linarith
    have ht0 : 0 ≤ t x := (sub_pos.mpr hepsilon1).le.trans htBounds.1
    have ha0 : 0 ≤ a x := ha.lam_pos.le.trans hax.1
    have hLam0 : 0 ≤ ha.Lam := ha0.trans hax.2
    constructor
    · calc
        (1 - epsilon) * ha.lam ≤ (1 - epsilon) * a x :=
          mul_le_mul_of_nonneg_left hax.1 (sub_nonneg.mpr hepsilon1.le)
        _ ≤ t x * a x := mul_le_mul_of_nonneg_right htBounds.1 ha0
        _ = a x * t x := mul_comm _ _
    · calc
        a x * t x ≤ ha.Lam * t x := mul_le_mul_of_nonneg_right hax.2 ht0
        _ ≤ ha.Lam * (1 + epsilon) :=
          mul_le_mul_of_nonneg_left htBounds.2 hLam0
        _ = (1 + epsilon) * ha.Lam := mul_comm _ _

/-- A pointwise bound controls the real essential-supremum ratio carrier. -/
theorem scalarRatioLInf_le_of_pointwise
    {U : Ch02.Domain d} {a b : Vec d → ℝ} {W : ℝ}
    (hW0 : 0 ≤ W)
    (h : ∀ x ∈ (U : Set (Vec d)), |a x / b x - 1| ≤ W) :
    scalarRatioLInf U a b ≤ W := by
  unfold scalarRatioLInf
  rw [SubdiffusiveProcess.RawLp.eLpNorm_top_exponent]
  have hae : ∀ᵐ x ∂volumeMeasureOn (U : Set (Vec d)),
      |a x / b x - 1| ≤ W := by
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    exact h x hx
  have hess : eLpNormEssSup (fun x ↦ a x / b x - 1)
      (volumeMeasureOn (U : Set (Vec d))) ≤ ENNReal.ofReal W :=
    eLpNormEssSup_le_of_ae_bound
      (by simpa only [Real.norm_eq_abs] using hae)
  calc
    (eLpNormEssSup (fun x ↦ a x / b x - 1)
        (volumeMeasureOn (U : Set (Vec d)))).toReal ≤
        (ENNReal.ofReal W).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
    _ = W := ENNReal.toReal_ofReal hW0

/-- Forward ratio error for multiplication by a near-one factor. -/
theorem scalarRatioLInf_mul_nearOne_le
    {U : Ch02.Domain d} {a t : Vec d → ℝ} {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon)
    (ha : ∀ x ∈ (U : Set (Vec d)), 0 < a x)
    (ht : ∀ x ∈ (U : Set (Vec d)), |t x - 1| ≤ epsilon) :
    scalarRatioLInf U (fun x ↦ a x * t x) a ≤ epsilon := by
  apply scalarRatioLInf_le_of_pointwise hepsilon0
  intro x hx
  have hax : a x ≠ 0 := (ha x hx).ne'
  convert ht x hx using 1
  field_simp

/-- Reverse ratio error.  The factor `2` is the convenient manuscript-small
regime price when `epsilon ≤ 1/2`. -/
theorem scalarRatioLInf_reverse_mul_nearOne_le
    {U : Ch02.Domain d} {a t : Vec d → ℝ} {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (ha : ∀ x ∈ (U : Set (Vec d)), 0 < a x)
    (ht : ∀ x ∈ (U : Set (Vec d)), |t x - 1| ≤ epsilon) :
    scalarRatioLInf U a (fun x ↦ a x * t x) ≤ 2 * epsilon := by
  apply scalarRatioLInf_le_of_pointwise (mul_nonneg (by norm_num) hepsilon0)
  intro x hx
  have htBounds := abs_le.mp (ht x hx)
  have htHalf : 1 / 2 ≤ t x := by linarith
  have htx : 0 < t x := lt_of_lt_of_le (by norm_num) htHalf
  have hax : a x ≠ 0 := (ha x hx).ne'
  have hrewrite : a x / (a x * t x) - 1 = (1 - t x) / t x := by
    field_simp
  rw [hrewrite, abs_div, abs_of_pos htx]
  apply (div_le_iff₀ htx).2
  have habs : |1 - t x| ≤ epsilon := by
    simpa [abs_sub_comm] using ht x hx
  have htwo : 1 ≤ 2 * t x := by nlinarith
  have hscale : epsilon ≤ epsilon * (2 * t x) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left htwo hepsilon0
  calc
    |1 - t x| ≤ epsilon := habs
    _ ≤ epsilon * (2 * t x) := hscale
    _ = 2 * epsilon * t x := by ring

/-- The normalized product response differs from the base response by the
printed linear-in-`epsilon` sensitivity row.

Taking square roots later turns the additive `15 * epsilon` probe term into
the required `C * epsilon^(1/2)` ladder perturbation. -/
theorem responseJ_mul_nearOne_le
    {U : Ch02.Domain d} {a t : Vec d → ℝ}
    (haData : ScalarCoeffOnData U a)
    (hatData : ScalarCoeffOnData U (fun x ↦ a x * t x))
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilonHalf : epsilon ≤ 1 / 2)
    (ha : ∀ x ∈ (U : Set (Vec d)), 0 < a x)
    (ht : ∀ x ∈ (U : Set (Vec d)), |t x - 1| ≤ epsilon)
    (p q : Vec d) (hpq : 0 ≤ vecDot p q) :
    J U hatData.toCoeffOn p q ≤
      (1 + 16 * epsilon) * J U haData.toCoeffOn p q +
        15 * epsilon * vecDot p q := by
  have hfwd := scalarRatioLInf_mul_nearOne_le hepsilon.le ha ht
  have hrev := scalarRatioLInf_reverse_mul_nearOne_le hepsilon.le
    hepsilonHalf ha ht
  have hmain := responseJ_sensitivity haData hatData
    (lambda := 1) (delta := epsilon) (by norm_num) hepsilon
    (hepsilonHalf.trans (by norm_num)) p q
  norm_num only [Real.sqrt_one, inv_one, one_smul] at hmain
  have hfwd0 : 0 ≤ scalarRatioLInf U (fun x ↦ a x * t x) a :=
    scalarRatioLInf_nonneg _ _ _
  have hrev0 : 0 ≤ scalarRatioLInf U a (fun x ↦ a x * t x) :=
    scalarRatioLInf_nonneg _ _ _
  have hratio :
      scalarRatioLInf U a (fun x ↦ a x * t x) ^ 2 +
          scalarRatioLInf U (fun x ↦ a x * t x) a ^ 2 ≤
        5 * epsilon ^ 2 := by
    nlinarith [
      (sq_le_sq₀ hrev0 (mul_nonneg (by norm_num) hepsilon.le)).2 hrev,
      (sq_le_sq₀ hfwd0 hepsilon.le).2 hfwd]
  have hJ0 : 0 ≤ J U haData.toCoeffOn p q :=
    Ch02.responseJ_nonneg U _ _ _
  have hfactor : 0 ≤ J U haData.toCoeffOn p q + vecDot p q := by
    exact add_nonneg hJ0 hpq
  have hthree : 0 ≤ 3 / epsilon := div_nonneg (by norm_num) hepsilon.le
  have hratioTerm := mul_le_mul_of_nonneg_left hratio hthree
  have hratioTerm' := mul_le_mul_of_nonneg_right hratioTerm hfactor
  have hsimplify :
      3 / epsilon * (5 * epsilon ^ 2) *
          (J U haData.toCoeffOn p q + vecDot p q) =
        15 * epsilon * (J U haData.toCoeffOn p q + vecDot p q) := by
    field_simp [hepsilon.ne']; ring
  rw [hsimplify] at hratioTerm'
  have hmain' : J U hatData.toCoeffOn p q ≤
      (1 + epsilon) * J U haData.toCoeffOn p q +
        3 / epsilon *
          (scalarRatioLInf U a (fun x ↦ a x * t x) ^ 2 +
            scalarRatioLInf U (fun x ↦ a x * t x) a ^ 2) *
          (J U haData.toCoeffOn p q + vecDot p q) := by
    simpa only [one_mul] using hmain
  nlinarith only [hmain', hratioTerm']

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
