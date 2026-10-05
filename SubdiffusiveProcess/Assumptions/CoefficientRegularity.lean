module

public import SubdiffusiveProcess.Assumptions.AnchoredCoefficientC11
public import SubdiffusiveProcess.Assumptions.AnchoredCoefficient
public import SubdiffusiveProcess.Assumptions.Cutoff
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section

/-!
# Local regularity of the GMC coefficients

Exponentiation preserves a continuous derivative that is Lipschitz on compact
sets. This supplies the exact `CoefficientC11On` predicate used in Section 8
for every anchored sample and finite cutoff. Positive continuous coefficients
also satisfy `CoefficientOn` on every bounded set.

No openness or boundedness premise is needed for `CoefficientC11On`: its
Lipschitz condition already quantifies over compact subsets of the given set.
-/

set_option autoImplicit false
open Homogenization MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess.Assumptions.CoefficientRegularity

/-- A globally continuously differentiable function is Lipschitz on each compact set. -/
theorem exists_lipschitzOnWith_of_hasFDerivAt {d : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Vec d → F} {D : Vec d → (Vec d →L[ℝ] F)}
    (hD : ∀ x, HasFDerivAt f (D x) x) (hc : Continuous D) (K : Set (Vec d))
    (hK : IsCompact K) : ∃ C : NNReal, LipschitzOnWith C f K := by exact SubdiffusiveProcess.Assumptions.AnchoredCoefficientC11.aux_dedup_d117_exists_lipschitzOnWith_of_continuous_deriv (d := d) (F := F) (f := f) (D := D) (hD := hD) (hc := hc) (K := K) (hK := hK)

/-- A quantitative product estimate for bounded Lipschitz functions. -/
theorem lipschitzOnWith_smul_of_bounds {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {K : Set E} {f : E → ℝ} {g : E → F} {Lf Lg A B : NNReal}
    (hf : LipschitzOnWith Lf f K) (hg : LipschitzOnWith Lg g K)
    (hA : ∀ x ∈ K, ‖f x‖ ≤ (A : ℝ)) (hB : ∀ x ∈ K, ‖g x‖ ≤ (B : ℝ)) :
    LipschitzOnWith (A * Lg + B * Lf) (fun x => f x • g x) K := by exact SubdiffusiveProcess.Assumptions.AnchoredCoefficientC11.aux_dedup_d095_lipschitzOnWith_smul_of_bounds (E := E) (F := F) (K := K) (f := f) (g := g) (Lf := Lf) (Lg := Lg) (A := A) (B := B) (hf := hf) (hg := hg) (hA := hA) (hB := hB)

/-- Exponentiation preserves the compact Lipschitz bound on the first derivative. -/
theorem coefficientC11On_exp {d : ℕ} {f : Vec d → ℝ} {D : Vec d → (Vec d →L[ℝ] ℝ)}
    (hD : ∀ x, HasFDerivAt f (D x) x) (hc : Continuous D)
    (hlip : ∀ K : Set (Vec d), IsCompact K → ∃ C : NNReal, LipschitzOnWith C D K)
    (U : Set (Vec d)) : CoefficientC11On U (fun x => Real.exp (f x)) := by
  have hfc : Continuous f :=
    continuous_iff_continuousAt.2 fun x => (hD x).continuousAt
  have hec : Continuous (fun x => Real.exp (f x)) := Real.continuous_exp.comp hfc
  refine ⟨fun x => Real.exp (f x) • D x, fun x _ => (hD x).exp, ?_⟩
  intro K hK _
  obtain ⟨Lf, hLf⟩ := exists_lipschitzOnWith_of_hasFDerivAt (fun x => (hD x).exp)
    (hec.smul hc) K hK
  obtain ⟨Lg, hLg⟩ := hlip K hK
  obtain ⟨A0, hA0⟩ := hK.exists_bound_of_continuousOn hec.continuousOn
  obtain ⟨B0, hB0⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨⟨max A0 0, le_max_right _ _⟩ * Lg + ⟨max B0 0, le_max_right _ _⟩ * Lf, ?_⟩
  exact lipschitzOnWith_smul_of_bounds hLf hLg
    (fun x hx => (hA0 x hx).trans (le_max_left A0 0))
    (fun x hx => (hB0 x hx).trans (le_max_left B0 0))

/-- Positivity and continuity give two-sided coefficient bounds on every bounded set. -/
theorem coefficientOn_of_continuous_pos {d : ℕ} {a : Vec d → ℝ} (ha : Continuous a)
    (hpos : ∀ x, 0 < a x) {U : Set (Vec d)} (hU : Bornology.IsBounded U) :
    CoefficientOn U a := by
  classical
  let K : Set (Vec d) := insert 0 (closure U)
  have hK : IsCompact K := hU.isCompact_closure.insert 0
  have hKne : K.Nonempty := Set.insert_nonempty 0 (closure U)
  have hUK : U ⊆ K := fun x hx => Set.mem_insert_of_mem _ (subset_closure hx)
  have hKmeas : MeasurableSet K := hK.measurableSet
  obtain ⟨x, _hxK, hmin⟩ := hK.exists_isMinOn hKne ha.continuousOn
  obtain ⟨y, _hyK, hmax⟩ := hK.exists_isMaxOn hKne ha.continuousOn
  refine ⟨ha.aestronglyMeasurable, a x, a y, hpos x, ?_⟩
  have hforall : ∀ z ∈ K, a x ≤ a z ∧ a z ≤ a y := fun z hz => ⟨hmin hz, hmax hz⟩
  have haeK : ∀ᵐ z ∂(volume.restrict K), a x ≤ a z ∧ a z ≤ a y :=
    ae_restrict_of_forall_mem hKmeas hforall
  exact ae_restrict_of_ae_restrict_of_subset hUK haeK

end SubdiffusiveProcess.Assumptions.CoefficientRegularity

namespace SubdiffusiveProcess.Model

/-- The cutoff logarithm differs from the anchored finite potential by a spatial constant. -/
theorem aCutoff_eq_exp_anchoredPartialSumField_add {d : ℕ} (M : GMCModel d) (L : ℕ)
    (omega : PotentialSample d) :
    aCutoff M L omega =
      fun x => Real.exp (anchoredPartialSumField omega L x +
        ∑ k ∈ Finset.range (L + 1), (omega k 0 - tauSq M.P)) := by
  funext x
  unfold aCutoff
  congr 1
  rw [anchoredPartialSumField_apply, anchoredPartialSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

variable {d : ℕ}

/-- The derivative of the anchored coefficient is its value times the potential derivative. -/
theorem hasFDerivAt_aAnchored (M : GMCModel d) (omega : AnchoredC11Sample d)
    (x : Vec d) :
    HasFDerivAt (aAnchored M omega)
      (aAnchored M omega x • _root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredLog omega) x) x :=
  ((anchoredLog omega).hasFDerivAt x).exp

/-- The anchored coefficient is differentiable at every point. -/
theorem differentiable_aAnchored (M : GMCModel d) (omega : AnchoredC11Sample d) :
    Differentiable ℝ (aAnchored M omega) :=
  fun x => (hasFDerivAt_aAnchored M omega x).differentiableAt

/-- Every anchored sample supplies the exact local C¹ˑ¹ coefficient predicate. -/
theorem coefficientC11On_aAnchored (M : GMCModel d) (omega : AnchoredC11Sample d)
    (U : Set (Vec d)) : CoefficientC11On U (aAnchored M omega) :=
  SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientC11On_exp
    (anchoredLog omega).hasFDerivAt (_root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredLog omega)).continuous
    (anchoredLog omega).2.2 U

/-- The anchored coefficient is uniformly positive and bounded on each bounded set. -/
theorem coefficientOn_aAnchored (M : GMCModel d) (omega : AnchoredC11Sample d)
    {U : Set (Vec d)} (hU : Bornology.IsBounded U) : CoefficientOn U (aAnchored M omega) :=
  SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos
    (continuous_aAnchored M omega) (aAnchored_pos M omega) hU

/-- Finite cutoff and mean normalization preserve local C¹ˑ¹ regularity. -/
theorem coefficientC11On_aCutoff (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    (U : Set (Vec d)) : CoefficientC11On U (aCutoff M L omega) := by
  rw [aCutoff_eq_exp_anchoredPartialSumField_add]
  exact SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientC11On_exp
    (fun x => ((anchoredPartialSumField omega L).hasFDerivAt x).add_const _)
    (_root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredPartialSumField omega L)).continuous
    (anchoredPartialSumField omega L).2.2 U

/-- Every finite cutoff satisfies the local two-sided coefficient bounds. -/
theorem coefficientOn_aCutoff (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    {U : Set (Vec d)} (hU : Bornology.IsBounded U) : CoefficientOn U (aCutoff M L omega) :=
  SubdiffusiveProcess.Assumptions.CoefficientRegularity.coefficientOn_of_continuous_pos
    (continuous_aCutoff M L omega) (aCutoff_pos M L omega) hU

end SubdiffusiveProcess.Model
