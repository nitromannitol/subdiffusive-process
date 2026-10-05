module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6DerivedSupport

@[expose] public section

/-!
# The window-restricted coefficient sigma-field, and the ratio good event

`restrictedCoefficientSigma a B = ⨆ x : B, comap (fun ω ↦ a ω x) (borel ℝ)`
(`Section6SupportBase.lean`) is the sigma-field the section 6 anchors use to say
"an event measurable with respect to `a_L|_B`".  Before this module it carried no
API at all: no evaluation-measurability lemma, no comparison with the ambient
sigma-field, no monotonicity.  This module supplies that API and then builds, on
top of it, the first *good event* the tree can prove measurable in it.

## Contents

1. **The API.**  `measurable_eval_restrictedCoefficientSigma` (point evaluations
   inside the window are measurable), `restrictedCoefficientSigma_le` (comparison
   with the ambient sigma-field), `restrictedCoefficientSigma_mono`,
   `restrictedCoefficientSigma_univ` (it degenerates to the
   `coefficientSigma` on the full window).
2. **The countable-dense device.**  `CoefficientRatioGood a B K` is the event
   that the coefficient varies by a factor at most `K` across the window.  For a
   sample-wise continuous coefficient on an open window it is measurable in the
   *restricted* sigma-field: the uncountable pair quantifier is replaced by a
   countable dense pair quantifier, exactly as in
   `Section6Anchored/GoodSetMeasurable.lean` and `CutoffRatioSup.lean`, and each
   surviving atom is a two-point comparison, which is what the restricted
   sigma-field measures.
3. **The deterministic payoff.**  `exists_bounds_of_coefficientRatioGood` turns
   the good event into the ellipticity data `0 < lam ≤ a ≤ Lam` with
   `Lam ≤ K ^ 2 * lam` in the hypothesis shape the small-contrast Schauder
   consumers use.
4. **The cutoff specialization.**  `aCutoff` is `exp` of a shell sum, so its
   window ratio is `exp` of the shell sum's window oscillation and the `tauSq`
   normalization cancels: `coefficientRatioGood_aCutoff_of_shellSum_oscillation`.
   This is the interface at which the probabilistic input
   (`ShellSensitivity.sensitivity_field` and the `gammaSigma 2` machinery) plugs
   in; the tail estimate itself is not proved here.

-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory

noncomputable section

variable {d : ℕ} {Ω : Type*}

/-! ## 1. The API -/

private theorem real_measurableSpace_eq_borel :
    (Real.measurableSpace : MeasurableSpace ℝ) = borel ℝ :=
  BorelSpace.measurable_eq

/-- Point evaluations inside the window are measurable for the window-restricted
coefficient sigma-field.  This is the basic unfolder the whole module rests on;
it is the analogue of `measurable_potentialCoordinate_shellIndexSigma`. -/
theorem measurable_eval_restrictedCoefficientSigma {a : Ω → Vec d → ℝ}
    {B : Set (Vec d)} {x : Vec d} (hx : x ∈ B) :
    Measurable[restrictedCoefficientSigma a B] fun ω => a ω x := by
  refine Measurable.of_comap_le ?_
  rw [real_measurableSpace_eq_borel]
  exact le_iSup
    (fun y : B => MeasurableSpace.comap (fun ω => a ω (y : Vec d)) (borel ℝ))
    (⟨x, hx⟩ : B)

/-- If every evaluation inside the window is ambiently measurable, the restricted
sigma-field is coarser than the ambient one.  This is the analogue of
`potentialShellIndexSigma_le_borel`, and it is what converts a `bad` event
produced in the restricted sigma-field into an ambiently measurable set whose
measure can be estimated. -/
theorem restrictedCoefficientSigma_le [MeasurableSpace Ω] {a : Ω → Vec d → ℝ}
    {B : Set (Vec d)} (h : ∀ x ∈ B, Measurable fun ω => a ω x) :
    restrictedCoefficientSigma a B ≤ (inferInstance : MeasurableSpace Ω) := by
  refine iSup_le fun x => ?_
  have hx := (h (x : Vec d) x.2).comap_le
  rwa [real_measurableSpace_eq_borel] at hx

/-- Ambient measurability of an event produced in the restricted sigma-field. -/
theorem measurableSet_of_restrictedCoefficientSigma [MeasurableSpace Ω]
    {a : Ω → Vec d → ℝ} {B : Set (Vec d)} {s : Set Ω}
    (h : ∀ x ∈ B, Measurable fun ω => a ω x)
    (hs : MeasurableSet[restrictedCoefficientSigma a B] s) : MeasurableSet s :=
  restrictedCoefficientSigma_le h _ hs

/-- The restricted sigma-field is monotone in the window. -/
theorem restrictedCoefficientSigma_mono (a : Ω → Vec d → ℝ) {B B' : Set (Vec d)}
    (h : B ⊆ B') :
    restrictedCoefficientSigma a B ≤ restrictedCoefficientSigma a B' :=
  iSup_le fun x =>
    le_iSup
      (fun y : B' => MeasurableSpace.comap (fun ω => a ω (y : Vec d)) (borel ℝ))
      (⟨(x : Vec d), h x.2⟩ : B')

/-- On the full window the restricted sigma-field is the
`coefficientSigma`. -/
theorem restrictedCoefficientSigma_univ (a : Ω → Vec d → ℝ) :
    restrictedCoefficientSigma a Set.univ = coefficientSigma a := by
  refine le_antisymm (iSup_le fun x => ?_) (iSup_le fun x => ?_)
  · exact le_iSup
      (fun y : Vec d => MeasurableSpace.comap (fun ω => a ω y) (borel ℝ))
      (x : Vec d)
  · exact le_iSup
      (fun y : (Set.univ : Set (Vec d)) =>
        MeasurableSpace.comap (fun ω => a ω (y : Vec d)) (borel ℝ))
      (⟨x, Set.mem_univ x⟩ : (Set.univ : Set (Vec d)))

/-! ## 2. The ratio good event and the countable-dense device -/

/-- A countable dense subset of an open window.  Same construction as
`CutoffRatioSup.exists_countable_dense_domain`, stated for an arbitrary open
set. -/
theorem exists_countable_dense_subset_of_isOpen {B : Set (Vec d)} (hB : IsOpen B) :
    ∃ D : Set (Vec d), D.Countable ∧ D ⊆ B ∧ B ⊆ closure D := by
  obtain ⟨s, hs, hsdense⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  refine ⟨s ∩ B, hs.mono Set.inter_subset_left, Set.inter_subset_right, ?_⟩
  intro y hy
  rw [Metric.mem_closure_iff]
  intro eps heps
  have hopen : IsOpen (Metric.ball y eps ∩ B) := Metric.isOpen_ball.inter hB
  have hnonempty : (Metric.ball y eps ∩ B).Nonempty :=
    ⟨y, Metric.mem_ball_self heps, hy⟩
  obtain ⟨w, hws, hw⟩ := hsdense.exists_mem_open hopen hnonempty
  exact ⟨w, ⟨hws, hw.2⟩, by rw [dist_comm]; exact hw.1⟩

/-- **The ratio good event.**  The coefficient varies across the window by a
factor at most `K`.  This is the event the section 6 anchors need: it is exactly
what converts into the uniform ellipticity bounds of the De Giorgi–Nash–Moser
interior estimate. -/
def CoefficientRatioGood (a : Ω → Vec d → ℝ) (B : Set (Vec d)) (K : ℝ) : Set Ω :=
  {ω | ∀ x ∈ B, ∀ y ∈ B, a ω x ≤ K * a ω y}

theorem mem_coefficientRatioGood_iff {a : Ω → Vec d → ℝ} {B : Set (Vec d)}
    {K : ℝ} {ω : Ω} :
    ω ∈ CoefficientRatioGood a B K ↔ ∀ x ∈ B, ∀ y ∈ B, a ω x ≤ K * a ω y :=
  Iff.rfl

/-- **The good event is measurable in the restricted sigma-field.**

The pair quantifier `∀ x ∈ B, ∀ y ∈ B` is uncountable, so it cannot be assembled
from countable operations directly.  For a sample-wise continuous coefficient the
condition cuts out a *closed* set of pairs, so it propagates from a countable
dense pair family to all of `B × B`; the countable form is then a countable
intersection of two-point comparisons, and a two-point comparison is precisely
what `restrictedCoefficientSigma a B` measures.

This is the device of `Section6Anchored/GoodSetMeasurable.lean`
(`forall_mem_closedBall_pair_of_forall_densePt`), run in the restricted
sigma-field rather than the ambient one. -/
theorem measurableSet_coefficientRatioGood {a : Ω → Vec d → ℝ} {B : Set (Vec d)}
    (hB : IsOpen B) (hcont : ∀ ω, Continuous (a ω)) (K : ℝ) :
    MeasurableSet[restrictedCoefficientSigma a B] (CoefficientRatioGood a B K) := by
  classical
  obtain ⟨D, hDc, hDB, hDdense⟩ := exists_countable_dense_subset_of_isOpen hB
  have hEq : CoefficientRatioGood a B K
      = ⋂ x ∈ D, ⋂ y ∈ D, {ω : Ω | a ω x ≤ K * a ω y} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, mem_coefficientRatioGood_iff]
    constructor
    · intro hω x hx y hy
      exact hω x (hDB hx) y (hDB hy)
    · intro hω x hx y hy
      have hclosed : IsClosed {p : Vec d × Vec d | a ω p.1 ≤ K * a ω p.2} :=
        isClosed_le ((hcont ω).comp continuous_fst)
          (continuous_const.mul ((hcont ω).comp continuous_snd))
      have hsub : D ×ˢ D ⊆ {p : Vec d × Vec d | a ω p.1 ≤ K * a ω p.2} := by
        rintro ⟨u, v⟩ ⟨hu, hv⟩
        exact hω u hu v hv
      have hmem : (x, y) ∈ closure (D ×ˢ D) := by
        rw [closure_prod_eq]
        exact ⟨hDdense hx, hDdense hy⟩
      exact hclosed.closure_subset_iff.2 hsub hmem
  rw [hEq]
  refine MeasurableSet.biInter hDc fun x hx => MeasurableSet.biInter hDc fun y hy => ?_
  have h1 : Measurable[restrictedCoefficientSigma a B] fun ω => a ω x :=
    measurable_eval_restrictedCoefficientSigma (hDB hx)
  have h2 : Measurable[restrictedCoefficientSigma a B] fun ω => K * a ω y :=
    (measurable_eval_restrictedCoefficientSigma (hDB hy)).const_mul K
  exact measurableSet_le h1 h2

/-! ## 3. The deterministic payoff: uniform ellipticity on the window -/

/-- On a nonempty window carrying a positive coefficient, the ratio good event
forces `1 ≤ K`. -/
theorem one_le_of_coefficientRatioGood {a : Ω → Vec d → ℝ} {B : Set (Vec d)}
    {K : ℝ} {ω : Ω} (hne : B.Nonempty) (hpos : ∀ x ∈ B, 0 < a ω x)
    (hω : ω ∈ CoefficientRatioGood a B K) : 1 ≤ K := by
  obtain ⟨y₀, hy₀⟩ := hne
  have h := hω y₀ hy₀ y₀ hy₀
  have hp := hpos y₀ hy₀
  nlinarith

/-- **The ellipticity data.**  The ratio good event supplies the hypothesis
shape `0 < lam ≤ a ≤ Lam` used by the small-contrast Schauder consumers, with the ellipticity ratio `Lam / lam` bounded by `K ^ 2`. -/
theorem exists_bounds_of_coefficientRatioGood {a : Ω → Vec d → ℝ}
    {B : Set (Vec d)} {K : ℝ} {ω : Ω} (hne : B.Nonempty)
    (hpos : ∀ x ∈ B, 0 < a ω x) (hω : ω ∈ CoefficientRatioGood a B K) :
    ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧ Lam ≤ K ^ 2 * lam ∧
      ∀ x ∈ B, lam ≤ a ω x ∧ a ω x ≤ Lam := by
  obtain ⟨y₀, hy₀⟩ := hne
  have hK1 : 1 ≤ K := one_le_of_coefficientRatioGood ⟨y₀, hy₀⟩ hpos hω
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
  have hp0 : 0 < a ω y₀ := hpos y₀ hy₀
  have hKK : (1 : ℝ) ≤ K * K := by nlinarith
  refine ⟨a ω y₀ / K, K * a ω y₀, by positivity, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hK0, show K * a ω y₀ * K = K * K * a ω y₀ by ring]
    have h2 := mul_le_mul_of_nonneg_right hKK hp0.le
    rwa [one_mul] at h2
  · rw [show K ^ 2 * (a ω y₀ / K) = K * a ω y₀ by field_simp]
  · intro x hx
    refine ⟨?_, hω x hx y₀ hy₀⟩
    have h := hω y₀ hy₀ x hx
    rw [div_le_iff₀ hK0]
    linarith

/-! ## 4. The cutoff specialization -/

open _root_.SubdiffusiveProcess.Model

/-- The cutoff is `exp` of the shell sum, up to the `tauSq` normalization. -/
theorem aCutoff_eq_exp_sub (M : GMCModel d) (L : ℕ) (ω : PotentialSample d)
    (x : Vec d) :
    aCutoff M L ω x =
      Real.exp ((∑ k ∈ Finset.range (L + 1), ω k x) -
        ((L : ℝ) + 1) * tauSq M.P) := by
  unfold aCutoff
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  ring

/-- **The interface for the probabilistic half.**  A bound `t` on the window
oscillation of the shell sum is exactly a ratio good event at level `exp t` for
the cutoff: the `tauSq` normalization cancels between numerator and denominator.

The tail estimate for the left-hand hypothesis is the remaining probabilistic
input (`ShellSensitivity.sensitivity_field` bounds the corresponding
`cutoffLogRatioOscillationSup` in the `gammaSigma 2` class); it is *not* proved
here. -/
theorem coefficientRatioGood_aCutoff_of_shellSum_oscillation (M : GMCModel d)
    (L : ℕ) (ω : PotentialSample d) {B : Set (Vec d)} {t : ℝ}
    (h : ∀ x ∈ B, ∀ y ∈ B,
      (∑ k ∈ Finset.range (L + 1), ω k x) -
        (∑ k ∈ Finset.range (L + 1), ω k y) ≤ t) :
    ω ∈ CoefficientRatioGood (aCutoff M L) B (Real.exp t) := by
  intro x hx y hy
  rw [aCutoff_eq_exp_sub, aCutoff_eq_exp_sub, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  linarith [h x hx y hy]

/-- The cutoff's restricted sigma-field is coarser than the ambient one. -/
theorem restrictedCoefficientSigma_aCutoff_le (M : GMCModel d) (L : ℕ)
    (B : Set (Vec d)) :
    restrictedCoefficientSigma (aCutoff M L) B ≤
      (inferInstance : MeasurableSpace (PotentialSample d)) :=
  restrictedCoefficientSigma_le fun x _ => measurable_aCutoff M L x

/-- **The cutoff's ratio good event is measurable in the anchor's sigma-field.**
This is the shape the section 6 anchors demand of their `bad` event: an event
measurable with respect to `a_L|_B`. -/
theorem measurableSet_coefficientRatioGood_aCutoff (M : GMCModel d) (L : ℕ)
    {B : Set (Vec d)} (hB : IsOpen B) (K : ℝ) :
    MeasurableSet[restrictedCoefficientSigma (aCutoff M L) B]
      (CoefficientRatioGood (aCutoff M L) B K) :=
  measurableSet_coefficientRatioGood hB (continuous_aCutoff M L) K

/-- The complement of the good event — the anchor's `bad` — is measurable in the
same sigma-field. -/
theorem measurableSet_compl_coefficientRatioGood_aCutoff (M : GMCModel d) (L : ℕ)
    {B : Set (Vec d)} (hB : IsOpen B) (K : ℝ) :
    MeasurableSet[restrictedCoefficientSigma (aCutoff M L) B]
      (CoefficientRatioGood (aCutoff M L) B K)ᶜ :=
  (measurableSet_coefficientRatioGood_aCutoff M L hB K).compl

/-- **The cutoff's ellipticity data off the bad event.**  Positivity of `aCutoff`
is unconditional, so the good event alone delivers the uniform bounds. -/
theorem exists_bounds_of_coefficientRatioGood_aCutoff (M : GMCModel d) (L : ℕ)
    {ω : PotentialSample d} {B : Set (Vec d)} {K : ℝ} (hne : B.Nonempty)
    (hω : ω ∈ CoefficientRatioGood (aCutoff M L) B K) :
    ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧ Lam ≤ K ^ 2 * lam ∧
      ∀ x ∈ B, lam ≤ aCutoff M L ω x ∧ aCutoff M L ω x ≤ Lam :=
  exists_bounds_of_coefficientRatioGood hne
    (fun x _ => aCutoff_pos M L ω x) hω

end

end SubdiffusiveProcess.CoarseGrainingVocab
