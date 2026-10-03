module

public import SubdiffusiveProcess.DirichletForm.FOTCoreCalculusLocal
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

@[expose] public section

open MeasureTheory Filter Set Topology

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X]

/-- Integrability with respect to both parts of a signed measure. -/
def SignedIntegrable (ν : SignedMeasure X) (f : X → ℝ) : Prop :=
  Integrable f ν.toJordanDecomposition.posPart ∧ Integrable f ν.toJordanDecomposition.negPart

theorem signedIntegrable_iff (ν : SignedMeasure X) (f : X → ℝ) :
    SignedIntegrable ν f ↔ Integrable f ν.totalVariation := by
  change (Integrable f ν.toJordanDecomposition.posPart ∧
    Integrable f ν.toJordanDecomposition.negPart) ↔
      Integrable f (ν.toJordanDecomposition.posPart + ν.toJordanDecomposition.negPart)
  exact integrable_add_measure.symm

theorem signedIntegralOn_const (ν : SignedMeasure X) {B : Set X} (hB : MeasurableSet B)
    (c : ℝ) : _root_.DirichletForm.signedIntegralOn ν B (fun _ => c) = c * ν B := by
  have hν : ν B = (ν.toJordanDecomposition.posPart B).toReal -
      (ν.toJordanDecomposition.negPart B).toReal := by
    conv_lhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
    rw [JordanDecomposition.toSignedMeasure, VectorMeasure.sub_apply,
      Measure.toSignedMeasure_apply_measurable hB, Measure.toSignedMeasure_apply_measurable hB]
    rfl
  simp only [_root_.DirichletForm.signedIntegralOn, integral_const, measureReal_def,
    Measure.restrict_apply_univ, smul_eq_mul, hν]
  ring

theorem signedIntegralOn_add (ν : SignedMeasure X) {f g : X → ℝ}
    (hf : SignedIntegrable ν f) (hg : SignedIntegrable ν g) (B : Set X) :
    _root_.DirichletForm.signedIntegralOn ν B (fun x => f x + g x) =
      _root_.DirichletForm.signedIntegralOn ν B f + _root_.DirichletForm.signedIntegralOn ν B g := by
  rw [_root_.DirichletForm.signedIntegralOn, integral_add hf.1.integrableOn hg.1.integrableOn,
    integral_add hf.2.integrableOn hg.2.integrableOn]
  simp only [_root_.DirichletForm.signedIntegralOn]
  ring

theorem signedIntegralOn_const_mul (ν : SignedMeasure X) (B : Set X) (c : ℝ) (f : X → ℝ) :
    _root_.DirichletForm.signedIntegralOn ν B (fun x => c * f x) =
      c * _root_.DirichletForm.signedIntegralOn ν B f := by
  simp only [_root_.DirichletForm.signedIntegralOn, integral_const_mul]
  ring

theorem signedIntegralOn_union (ν : SignedMeasure X) {f : X → ℝ}
    (hf : SignedIntegrable ν f) {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : Disjoint A B) :
    _root_.DirichletForm.signedIntegralOn ν (A ∪ B) f =
      _root_.DirichletForm.signedIntegralOn ν A f + _root_.DirichletForm.signedIntegralOn ν B f := by
  simp only [_root_.DirichletForm.signedIntegralOn,
    setIntegral_union hAB hB hf.1.integrableOn hf.1.integrableOn,
    setIntegral_union hAB hB hf.2.integrableOn hf.2.integrableOn]
  ring

theorem abs_signedIntegralOn_le (ν : SignedMeasure X) {B : Set X} (hB : MeasurableSet B)
    {f : X → ℝ} {C : ℝ} (hf : ∀ x ∈ B, |f x| ≤ C) :
    |_root_.DirichletForm.signedIntegralOn ν B f| ≤ C * (ν.totalVariation B).toReal := by
  have hp := norm_integral_le_of_norm_le_const
    (μ := ν.toJordanDecomposition.posPart.restrict B) (f := f)
    (by filter_upwards [ae_restrict_mem hB] with x hx; exact hf x hx)
  have hn := norm_integral_le_of_norm_le_const
    (μ := ν.toJordanDecomposition.negPart.restrict B) (f := f)
    (by filter_upwards [ae_restrict_mem hB] with x hx; exact hf x hx)
  simp only [Real.norm_eq_abs, measureReal_def, Measure.restrict_apply_univ] at hp hn
  unfold _root_.DirichletForm.signedIntegralOn
  apply (abs_sub _ _).trans
  rw [SignedMeasure.totalVariation, Measure.add_apply,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  nlinarith only [hp, hn]

/-- Domination on all measurable subsets bounds total variation. -/
theorem signed_totalVariation_le {ν : SignedMeasure X} {μ : Measure X}
    [IsFiniteMeasure μ]
    (h : ∀ B : Set X, MeasurableSet B → |ν B| ≤ (μ B).toReal) : ν.totalVariation ≤ μ := by
  obtain ⟨S, hS, _, _, hpS, hnSc⟩ := ν.toJordanDecomposition.exists_compl_positive_negative
  have hpos : ∀ B : Set X, MeasurableSet B →
      (ν.toJordanDecomposition.posPart B).toReal = ν (B ∩ Sᶜ) := by
    intro B hB
    have hn : ν.toJordanDecomposition.negPart (B ∩ Sᶜ) = 0 :=
      (measure_mono inter_subset_right).trans_eq hnSc |>.antisymm bot_le
    have hp : ν.toJordanDecomposition.posPart (B ∩ Sᶜ) = ν.toJordanDecomposition.posPart B :=
      measure_inter_conull (by simpa only [compl_compl] using hpS)
    conv_rhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
    rw [JordanDecomposition.toSignedMeasure, VectorMeasure.sub_apply,
      Measure.toSignedMeasure_apply_measurable (hB.inter hS.compl),
      Measure.toSignedMeasure_apply_measurable (hB.inter hS.compl),
      measureReal_def, measureReal_def, hn, hp, ENNReal.toReal_zero, sub_zero]
  have hneg : ∀ B : Set X, MeasurableSet B →
      (ν.toJordanDecomposition.negPart B).toReal = -ν (B ∩ S) := by
    intro B hB
    have hp : ν.toJordanDecomposition.posPart (B ∩ S) = 0 :=
      (measure_mono inter_subset_right).trans_eq hpS |>.antisymm bot_le
    have hn : ν.toJordanDecomposition.negPart (B ∩ S) = ν.toJordanDecomposition.negPart B :=
      measure_inter_conull hnSc
    conv_rhs => rw [← ν.toSignedMeasure_toJordanDecomposition]
    rw [JordanDecomposition.toSignedMeasure, VectorMeasure.sub_apply,
      Measure.toSignedMeasure_apply_measurable (hB.inter hS),
      Measure.toSignedMeasure_apply_measurable (hB.inter hS),
      measureReal_def, measureReal_def, hp, hn, ENNReal.toReal_zero, zero_sub, neg_neg]
  apply Measure.le_iff.mpr
  intro B hB
  have hp := (le_abs_self (ν (B ∩ Sᶜ))).trans (h (B ∩ Sᶜ) (hB.inter hS.compl))
  have hn := (neg_le_abs (ν (B ∩ S))).trans (h (B ∩ S) (hB.inter hS))
  have hpart : (μ (B ∩ Sᶜ)).toReal + (μ (B ∩ S)).toReal = (μ B).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ← measure_union (disjoint_left.mpr fun x hx hy => hx.2 hy.2) (hB.inter hS),
      ← inter_union_distrib_left, compl_union_self, inter_univ]
  apply (ENNReal.toReal_le_toReal (by
    rw [SignedMeasure.totalVariation, Measure.add_apply]
    exact ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) (measure_ne_top μ B)).mp
  rw [SignedMeasure.totalVariation, Measure.add_apply,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hpos B hB, hneg B hB]
  linarith only [hp, hn, hpart]

section Topological

variable [TopologicalSpace X] [T2Space X] [BorelSpace X]

theorem signedIntegrable_of_compact_carrier (ν : SignedMeasure X) {K : Set X}
    (hK : IsCompact K) (hν : ν.totalVariation Kᶜ = 0) {f : X → ℝ}
    (hf : Continuous f) : SignedIntegrable ν f := by
  have hz : ν.toJordanDecomposition.posPart Kᶜ = 0 ∧
      ν.toJordanDecomposition.negPart Kᶜ = 0 := by
    simpa only [SignedMeasure.totalVariation, Measure.add_apply, add_eq_zero] using hν
  constructor
  · have hr : ν.toJordanDecomposition.posPart.restrict K = ν.toJordanDecomposition.posPart :=
      Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hz.1)
    have hh := hf.continuousOn.integrableOn_compact (μ := ν.toJordanDecomposition.posPart) hK
    change Integrable f (ν.toJordanDecomposition.posPart.restrict K) at hh
    rwa [hr] at hh
  · have hr : ν.toJordanDecomposition.negPart.restrict K = ν.toJordanDecomposition.negPart :=
      Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hz.2)
    have hh := hf.continuousOn.integrableOn_compact (μ := ν.toJordanDecomposition.negPart) hK
    change Integrable f (ν.toJordanDecomposition.negPart.restrict K) at hh
    rwa [hr] at hh

variable {m : Measure X} {F : _root_.DirichletForm m} {U : Set X}

theorem EnergyFamily.cross_variation_le (Γ : EnergyFamily F U) {u v : Lp ℝ 2 m}
    (hu : u ∈ F.domain) (hv : v ∈ F.domain) :
    (Γ.cross u v).totalVariation ≤ Γ.measure u + Γ.measure v := by
  letI : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu⟩
  letI : IsFiniteMeasure (Γ.measure v) := ⟨Γ.finite v hv⟩
  apply signed_totalVariation_le
  intro B hB
  have h := Γ.cross_le u hu v hv B hB
  rw [Measure.add_apply, ENNReal.toReal_add (Γ.measure_ne_top hu B) (Γ.measure_ne_top hv B)]
  have hAu := Real.sq_sqrt (ENNReal.toReal_nonneg (a := Γ.measure u B))
  have hAv := Real.sq_sqrt (ENNReal.toReal_nonneg (a := Γ.measure v B))
  nlinarith only [h, hAu, hAv,
    sq_nonneg (Real.sqrt (Γ.measure u B).toReal - Real.sqrt (Γ.measure v B).toReal),
    ENNReal.toReal_nonneg (a := Γ.measure u B), ENNReal.toReal_nonneg (a := Γ.measure v B)]

theorem EnergyFamily.cross_variation_ac_left (Γ : EnergyFamily F U) {u v : Lp ℝ 2 m}
    (hu : u ∈ F.domain) (hv : v ∈ F.domain) :
    (Γ.cross u v).totalVariation ≪ Γ.measure u := by
  have hac : Γ.cross u v ≪ᵥ (Γ.measure u).toENNRealVectorMeasure := by
    apply VectorMeasure.AbsolutelyContinuous.mk
    intro B hB hz
    rw [Measure.toENNRealVectorMeasure_apply_measurable hB] at hz
    have h := Γ.cross_le u hu v hv B hB
    rw [hz, ENNReal.toReal_zero, Real.sqrt_zero, zero_mul] at h
    exact abs_nonpos_iff.mp h
  rw [SignedMeasure.absolutelyContinuous_ennreal_iff,
    VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure] at hac
  exact hac

end Topological

end DirichletForm.FOTConstruction
