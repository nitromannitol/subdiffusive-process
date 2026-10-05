module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.CoefficientResponse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

/-!
# Theta-perturbed cutoff Hölder ladder: normalization

The manuscript first divides the multiplier by a positive scalar.  This file
records that normalization on the literal weak-equation and coefficient
carriers, without importing the bounded-multiplier implementation argument.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open Filter MeasureTheory Homogenization Homogenization.Book

noncomputable section

variable {d : ℕ}

/-- The multiplier after division by the harmless positive scalar. -/
def normalizedMultiplier (b : ℝ) (theta : Vec d → ℝ) : Vec d → ℝ :=
  fun x ↦ b⁻¹ * theta x

/-- The cutoff coefficient with the normalized multiplier. -/
def normalizedThetaCutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (b : ℝ) (theta : Vec d → ℝ) : Vec d → ℝ :=
  fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x *
    normalizedMultiplier b theta x

/-- Multiplication of a homogeneous scalar weak equation by a constant. -/
theorem isWeaklyHarmonicOn_const_mul
    {s : Vec d → ℝ} {W : Set (Vec d)} {u : H1Function W}
    (c : ℝ) (hu : IsWeaklyHarmonicOn s W u) :
    IsWeaklyHarmonicOn (fun x ↦ c * s x) W u := by
  intro phi
  have hzero := hu phi
  calc
    ∫ x in W, vecDot ((c * s x) • u.grad x)
        (phi.toH1Function.grad x) ∂volume =
        c * ∫ x in W, vecDot (s x • u.grad x)
          (phi.toH1Function.grad x) ∂volume := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [mul_smul, vecDot_smul_left]
    _ = 0 := by rw [hzero, mul_zero]

/-- Dividing a homogeneous scalar coefficient by a nonzero constant does not
change its weak equation. -/
theorem isWeaklyHarmonicOn_iff_normalizedThetaCutoff
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {b : ℝ} (hb : 0 < b) (theta : Vec d → ℝ)
    {W : Set (Vec d)} {u : H1Function W} :
    IsWeaklyHarmonicOn
        (fun x ↦ _root_.SubdiffusiveProcess.Model.aCutoff M L omega x * theta x) W u ↔
      IsWeaklyHarmonicOn (normalizedThetaCutoff M L omega b theta) W u := by
  constructor
  · intro hu
    have hscaled := isWeaklyHarmonicOn_const_mul b⁻¹ hu
    convert hscaled using 1
    funext x
    simp only [normalizedThetaCutoff, normalizedMultiplier]
    ring
  · intro hu
    have hscaled := isWeaklyHarmonicOn_const_mul b hu
    have hb0 : b ≠ 0 := hb.ne'
    convert hscaled using 1
    funext x
    simp only [normalizedThetaCutoff, normalizedMultiplier]
    field_simp [hb0]

/-- Local coefficient package for the normalized product.  Only continuity
and near-one control on the ambient collar are required. -/
noncomputable def normalizedThetaCutoffCoeffOnData
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {B : Set (Vec d)} {U : Ch02.Domain d} (hUB : (U : Set (Vec d)) ⊆ B)
    {b epsilon : ℝ} (theta : Vec d → ℝ)
    (htheta : ContinuousOn theta B)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon < 1)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon) :
    ScalarCoeffOnData U (normalizedThetaCutoff M L omega b theta) := by
  let a : Vec d → ℝ := _root_.SubdiffusiveProcess.Model.aCutoff M L omega
  let t : Vec d → ℝ := normalizedMultiplier b theta
  let ha : ScalarCoeffOnData U a := aCutoffCoeffOnData M L omega U
  have htContinuous : ContinuousOn t (U : Set (Vec d)) := by
    exact continuousOn_const.mul (htheta.mono hUB)
  have hproductContinuous : ContinuousOn (fun x ↦ a x * t x)
      (U : Set (Vec d)) :=
    (_root_.SubdiffusiveProcess.Model.continuous_aCutoff M L omega).continuousOn.mul
      htContinuous
  have htNear : ∀ x ∈ (U : Set (Vec d)), |t x - 1| ≤ epsilon := by
    intro x hx
    exact hnear x (hUB hx)
  exact scalarCoeffOnData_mul_nearOne ha hepsilon0 hepsilon1
    (hproductContinuous.aestronglyMeasurable (μ := volume) U.measurableSet) htNear

/-- The two local response-ratio bounds in the normalized theta setting. -/
theorem normalizedThetaCutoff_ratio_bounds
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ)
    (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {B : Set (Vec d)} {U : Ch02.Domain d} (hUB : (U : Set (Vec d)) ⊆ B)
    {b epsilon : ℝ} (theta : Vec d → ℝ)
    (hepsilon0 : 0 ≤ epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (hnear : ∀ x ∈ B, |b⁻¹ * theta x - 1| ≤ epsilon) :
    scalarRatioLInf U (normalizedThetaCutoff M L omega b theta)
        (_root_.SubdiffusiveProcess.Model.aCutoff M L omega) ≤ epsilon ∧
      scalarRatioLInf U (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)
        (normalizedThetaCutoff M L omega b theta) ≤ 2 * epsilon := by
  let a : Vec d → ℝ := _root_.SubdiffusiveProcess.Model.aCutoff M L omega
  let t : Vec d → ℝ := normalizedMultiplier b theta
  have ha : ∀ x ∈ (U : Set (Vec d)), 0 < a x := by
    intro x _
    exact _root_.SubdiffusiveProcess.Model.aCutoff_pos M L omega x
  have ht : ∀ x ∈ (U : Set (Vec d)), |t x - 1| ≤ epsilon := by
    intro x hx
    exact hnear x (hUB hx)
  exact ⟨scalarRatioLInf_mul_nearOne_le hepsilon0 ha ht,
    scalarRatioLInf_reverse_mul_nearOne_le hepsilon0 hepsilonHalf ha ht⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
