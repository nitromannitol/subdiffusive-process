/-
# Comparing two finite Borel measures through compactly supported test functions
-/
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Separation.Regular

/-!
# Comparing finite Borel measures through test functions

If `∫ f dν ≤ C ∫ f dμ` for every continuous `0 ≤ f ≤ 1` compactly supported in an
open set `U`, then `ν B ≤ C μ B` for every measurable `B ⊆ U`.

This is the last step of the passage from a comparison of forms to a comparison
of energy measures: the sine/cosine argument produces an inequality between
integrals of test functions, and this lemma turns it into an inequality between
measures.

The standing assumptions are those of Fukushima–Oshima–Takeda: `X` is a locally
compact Hausdorff space carrying its Borel σ-algebra.  The two regularity
hypotheses used are exactly inner regularity of `ν` (to exhaust an open set by
compact sets) and outer regularity of `μ` (to shrink an open set onto a Borel
set); both hold for any finite Borel measure on the spaces this library is
instantiated at.

Nothing in this file mentions a Dirichlet form; it is a statement about
measures.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace DirichletForm

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [LocallyCompactSpace X]

omit [MeasurableSpace X] [BorelSpace X] [T2Space X] [LocallyCompactSpace X] in
/-- A continuous function vanishing outside the interior of a closed set `L` has
topological support inside `L`. -/
theorem tsupport_subset_of_eqOn_zero_compl_interior {f : X → ℝ} {L : Set X}
    (hL : IsClosed L) (hf : EqOn f 0 (interior L)ᶜ) : tsupport f ⊆ L := by
  have hsupp : Function.support f ⊆ interior L := by
    intro x hx
    by_contra hxL
    exact hx (hf hxL)
  exact (closure_mono hsupp).trans (by simpa using hL.closure_subset_iff.mpr interior_subset)



theorem exists_continuous_plateau {K U : Set X} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ ϑ : X → ℝ, Continuous ϑ ∧ HasCompactSupport ϑ ∧ tsupport ϑ ⊆ U ∧
      (∀ x : X, 0 ≤ ϑ x) ∧ (∀ x : X, ϑ x ≤ 1) ∧ (∀ x ∈ K, ϑ x = 1) := by
  obtain ⟨L, hLc, hLcl, hKL, hLU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨⟨ϑ, hϑc⟩, hϑ1, hϑ0, hϑcs, hϑIcc⟩ :=
    exists_continuous_one_zero_of_isCompact hK isOpen_interior.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hKL)
  exact ⟨ϑ, hϑc, hϑcs,
    (tsupport_subset_of_eqOn_zero_compl_interior hLcl hϑ0).trans hLU,
    fun x => (hϑIcc x).1, fun x => (hϑIcc x).2, fun x hx => hϑ1 hx⟩

/-- **Test functions compare open sets.**  If `∫ f dν ≤ C ∫ f dμ` for every
continuous `0 ≤ f ≤ 1` compactly supported in `U`, the same bound holds for the
measures of open subsets of `U`. -/
theorem measure_isOpen_le_of_integral_le {ν μ : Measure X} [IsFiniteMeasure ν]
    [IsFiniteMeasure μ] [ν.InnerRegularCompactLTTop] {C : ℝ≥0} {U : Set X}
    (h : ∀ f : X → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      (∀ x : X, 0 ≤ f x) → (∀ x : X, f x ≤ 1) → (∫ x, f x ∂ν) ≤ (C : ℝ) * ∫ x, f x ∂μ)
    {V : Set X} (hV : IsOpen V) (hVU : V ⊆ U) : ν V ≤ (C : ℝ≥0∞) * μ V := by
  refine le_of_forall_lt fun r hr => ?_
  obtain ⟨K, hKV, hKc, hrK⟩ :=
    hV.measurableSet.exists_lt_isCompact_of_ne_top (measure_ne_top ν V) hr
  obtain ⟨L, hLc, hLcl, hKL, hLV⟩ := exists_compact_closed_between hKc hV hKV
  obtain ⟨⟨f, hfc⟩, hf1, hf0, hfcs, hfIcc⟩ :=
    exists_continuous_one_zero_of_isCompact hKc isOpen_interior.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hKL)
  have hsuppL : tsupport f ⊆ L := tsupport_subset_of_eqOn_zero_compl_interior hLcl hf0
  have hint : Integrable f ν := hfc.integrable_of_hasCompactSupport hfcs
  have hintμ : Integrable f μ := hfc.integrable_of_hasCompactSupport hfcs
  have hle := h f hfc hfcs (hsuppL.trans (hLV.trans hVU)) (fun x => (hfIcc x).1)
    (fun x => (hfIcc x).2)
  have h1 : ν K ≤ ENNReal.ofReal (∫ x, f x ∂ν) :=
    hint.measure_le_integral (Filter.Eventually.of_forall fun x => (hfIcc x).1)
      fun x hx => le_of_eq (hf1 hx).symm
  have h2 : ENNReal.ofReal (∫ x, f x ∂μ) ≤ μ V := by
    refine integral_le_measure (fun x _ => (hfIcc x).2) fun x hx => ?_
    have : x ∉ interior L := fun hmem => hx (hLV (interior_subset hmem))
    exact le_of_eq (hf0 this)
  have h3 : ENNReal.ofReal (∫ x, f x ∂ν) ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∫ x, f x ∂μ) := by
    refine (ENNReal.ofReal_le_ofReal hle).trans ?_
    rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  calc r < ν K := hrK
    _ ≤ ENNReal.ofReal (∫ x, f x ∂ν) := h1
    _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∫ x, f x ∂μ) := h3
    _ ≤ (C : ℝ≥0∞) * μ V := by gcongr

/-- **Test functions compare measurable sets.**  If `∫ f dν ≤ C ∫ f dμ` for every
continuous `0 ≤ f ≤ 1` compactly supported in the open set `U`, then
`ν B ≤ C μ B` for every measurable `B ⊆ U`. -/
theorem measure_le_of_integral_le {ν μ : Measure X} [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    [ν.InnerRegularCompactLTTop] [μ.OuterRegular] {C : ℝ≥0} {U : Set X} (hU : IsOpen U)
    (h : ∀ f : X → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      (∀ x : X, 0 ≤ f x) → (∀ x : X, f x ≤ 1) → (∫ x, f x ∂ν) ≤ (C : ℝ) * ∫ x, f x ∂μ)
    {B : Set X} (hBU : B ⊆ U) : ν B ≤ (C : ℝ≥0∞) * μ B := by
  have key : ∀ ε : ℝ≥0, 0 < ε → ν B ≤ (C : ℝ≥0∞) * (μ B + (ε : ℝ≥0∞)) := by
    intro ε hε
    obtain ⟨V, hBV, hVopen, hVlt⟩ :=
      B.exists_isOpen_lt_add (measure_ne_top μ B) (ε := (ε : ℝ≥0∞))
        (ENNReal.coe_ne_zero.mpr hε.ne')
    calc ν B ≤ ν (V ∩ U) := measure_mono (subset_inter hBV hBU)
      _ ≤ (C : ℝ≥0∞) * μ (V ∩ U) :=
          measure_isOpen_le_of_integral_le h (hVopen.inter hU) inter_subset_right
      _ ≤ (C : ℝ≥0∞) * μ V := by gcongr; exact inter_subset_left
      _ ≤ (C : ℝ≥0∞) * (μ B + (ε : ℝ≥0∞)) := by gcongr
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  rcases eq_or_ne C 0 with rfl | hC0
  · simpa using (key 1 one_pos).trans (by simp)
  · have hCpos : (0 : ℝ≥0) < C := pos_iff_ne_zero.mpr hC0
    have hkey := key (δ / C) (by positivity)
    have hcancel : (C : ℝ≥0) * (δ / C) = δ := by field_simp
    calc ν B ≤ (C : ℝ≥0∞) * (μ B + ((δ / C : ℝ≥0) : ℝ≥0∞)) := hkey
      _ = (C : ℝ≥0∞) * μ B + ((C * (δ / C) : ℝ≥0) : ℝ≥0∞) := by
          rw [mul_add, ENNReal.coe_mul]
      _ = (C : ℝ≥0∞) * μ B + (δ : ℝ≥0∞) := by rw [hcancel]

end DirichletForm
