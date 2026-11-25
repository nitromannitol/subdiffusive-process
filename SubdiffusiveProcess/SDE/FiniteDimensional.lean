module

public import SubdiffusiveProcess.SDE.MarkovMeasurable
public import MarkovProcess.FiniteTime.Kernel

/-!
# The finite-dimensional laws of a solution of the stochastic differential equation

From the Markov identity for bounded measurable functions, by induction on the number of times:
for relative times `τ_0 < ⋯ < τ_{n-1}`, every `s` and every `A ∈ ℱ_s`, the law of
`(X_{s + τ_i})_i` restricted to `A` is the finite-time kernel of `Q` at `τ` composed with the law of
`X_s` restricted to `A` (`map_restrict_eq_finiteTimeKernel_comp`). For a solution started at `x`
the finite-dimensional laws are those of `Q` from `x` (`map_eq_finiteTimeKernel`), and the law of
the path is the unique measure on continuous paths with these marginals (`map_solutionPath_eq`).
-/

@[expose] public section

noncomputable section

namespace SubdiffusiveProcess.SDE

open MeasureTheory ProbabilityTheory Filter Set Real MarkovProcess
open scoped NNReal ENNReal Topology ContDiff

variable {d : ℕ}

universe u

/-- Every finite-time kernel of a sub-Markov kernel semigroup is a finite kernel. -/
theorem finiteTimeKernel_isFiniteKernel (Q : SubMarkovKernelSemigroup (Vec d)) {n : ℕ}
    (τ : FiniteOrderedTimes n) : IsFiniteKernel (SubMarkovKernelSemigroup.finiteTimeKernel Q τ) := by
  induction n with
  | zero =>
    rw [SubMarkovKernelSemigroup.finiteTimeKernel_zero]
    infer_instance
  | succ n ih =>
    have : IsFiniteKernel (Q (τ 0)) := (Q.isSubMarkovKernel (τ 0)).isFiniteKernel
    have : IsFiniteKernel (SubMarkovKernelSemigroup.finiteTimeKernel Q τ.relativeTail) :=
      ih τ.relativeTail
    rw [SubMarkovKernelSemigroup.finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map]
    infer_instance

/-- **The finite-dimensional laws, conditionally on `ℱ_s`.** -/
theorem map_restrict_eq_finiteTimeKernel_comp (hIto : ItoFormulaStopped.{u} d)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P ℱ] {σ : ℝ} {b : Vec d → Vec d}
    (hb : Continuous b) {W X : ℝ≥0 → Ω → Vec d} (hW : IsBrownianMotion W ℱ P)
    (hX : IsStrongSolution σ b W X ℱ) {Q : SubMarkovKernelSemigroup (Vec d)}
    (hQ : HasClassicalResolvent Q σ b)
    (hQc : ∀ h : Vec d → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → ∀ y,
      Continuous fun t : ℝ≥0 => ∫ z, h z ∂(Q t y)) :
    ∀ (n : ℕ) (τ : FiniteOrderedTimes n) (s : ℝ≥0) (A : Set Ω), MeasurableSet[ℱ s] A →
      (P.restrict A).map (fun w i => X (s + τ i) w) =
        SubMarkovKernelSemigroup.finiteTimeKernel Q τ ∘ₘ ((P.restrict A).map (X s)) := by
  have hXm : ∀ t, Measurable (X t) := fun t => (hX.adapted t).mono (ℱ.le t) le_rfl
  have hXF : ∀ t, Measurable[ℱ t] (X t) := fun t => hX.adapted t
  have hfin : ∀ t, IsFiniteKernel (Q t) := fun t =>
    ⟨⟨1, ENNReal.one_lt_top, fun y => Q.measure_univ_le_one t y⟩⟩
  intro n
  induction n with
  | zero =>
    intro τ s A hA
    ext S hS
    rw [Measure.map_apply (measurable_pi_iff.mpr fun i => hXm _) hS,
      Measure.bind_apply hS (Kernel.aemeasurable _)]
    simp only [SubMarkovKernelSemigroup.finiteTimeKernel_zero, Kernel.const_apply]
    rcases eq_empty_or_nonempty S with rfl | ⟨p, hp⟩
    · simp
    · have hS' : S = univ := eq_univ_of_forall fun q => by
        have hqp : q = p := funext fun i => i.elim0
        rwa [hqp]
      subst hS'
      simp only [preimage_univ, measure_univ, lintegral_one]
      rw [Measure.map_apply (hXm s) MeasurableSet.univ, preimage_univ]
  | succ n ih =>
    intro τ s A hA
    set t₀ : ℝ≥0 := s + τ 0 with ht₀
    have hst₀ : s ≤ t₀ := le_self_add
    have htail : ∀ i : Fin n, s + τ i.succ = t₀ + τ.relativeTail i := by
      intro i
      rw [ht₀, add_assoc, FiniteOrderedTimes.add_relativeTail]
    have hQ0 : IsFiniteKernel (Q (τ 0)) := hfin _
    have hKfin : IsFiniteKernel (SubMarkovKernelSemigroup.finiteTimeKernel Q τ.relativeTail) :=
      finiteTimeKernel_isFiniteKernel Q _
    set Y : Ω → (Fin n → Vec d) := fun w i => X (t₀ + τ.relativeTail i) w with hY
    have hYm : Measurable Y := measurable_pi_iff.mpr fun i => hXm _
    have hpair : Measurable fun w => (X t₀ w, Y w) := (hXm t₀).prodMk hYm
    have hpath : (fun w (i : Fin (n + 1)) => X (s + τ i) w) =
        (fun z : Vec d × (Fin n → Vec d) => @Fin.cons n (fun _ : Fin (n + 1) => Vec d) z.1 z.2) ∘
          (fun w => (X t₀ w, Y w)) := by
      funext w i
      simp only [Function.comp_apply]
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero]
      · rw [Fin.cons_succ, htail j]
    -- The joint law of `(X_{t₀}, Y)` on rectangles.
    have hrect : ∀ B, MeasurableSet B → ∀ C, MeasurableSet C →
        (P.restrict A).map (fun w => (X t₀ w, Y w)) (B ×ˢ C) =
          ((Q (τ 0) ⊗ₖ Kernel.prodMkLeft (Vec d)
            (SubMarkovKernelSemigroup.finiteTimeKernel Q τ.relativeTail)) ∘ₘ
              (P.restrict A).map (X s)) (B ×ˢ C) := by
      intro B hB C hC
      have hA' : MeasurableSet[ℱ t₀] (A ∩ X t₀ ⁻¹' B) :=
        (ℱ.mono hst₀ _ hA).inter (hXF t₀ hB)
      have hih : (P.restrict (A ∩ X t₀ ⁻¹' B)).map Y =
          SubMarkovKernelSemigroup.finiteTimeKernel Q τ.relativeTail ∘ₘ
            (P.restrict (A ∩ X t₀ ⁻¹' B)).map (X t₀) :=
        ih τ.relativeTail t₀ _ hA'
      have hmark : (P.restrict A).map (X t₀) = Q (τ 0) ∘ₘ (P.restrict A).map (X s) :=
        setIntegral_comp_add_eq_setIntegral_kernel_of_measurable hIto hb hW hX hQ hQc s (τ 0) hA
      have hKC : Measurable fun y =>
          SubMarkovKernelSemigroup.finiteTimeKernel Q τ.relativeTail y C :=
        Kernel.measurable_coe _ hC
      have hφ : Measurable (B.indicator fun y =>
          SubMarkovKernelSemigroup.finiteTimeKernel Q τ.relativeTail y C) := hKC.indicator hB
      calc (P.restrict A).map (fun w => (X t₀ w, Y w)) (B ×ˢ C)
          = (P.restrict (A ∩ X t₀ ⁻¹' B)).map Y C := by
            rw [Measure.map_apply hpair (hB.prod hC), Measure.map_apply hYm hC,
              Measure.restrict_apply (hpair (hB.prod hC)), Measure.restrict_apply (hYm hC)]
            congr 1
            ext w
            simp only [mem_inter_iff, mem_preimage, mem_prod]
            tauto
        _ = (SubMarkovKernelSemigroup.finiteTimeKernel Q τ.relativeTail ∘ₘ
              (P.restrict (A ∩ X t₀ ⁻¹' B)).map (X t₀)) C := by rw [hih]
        _ = ∫⁻ y, SubMarkovKernelSemigroup.finiteTimeKernel Q τ.relativeTail y C
              ∂((P.restrict (A ∩ X t₀ ⁻¹' B)).map (X t₀)) :=
            Measure.bind_apply hC (Kernel.aemeasurable _)
        _ = ∫⁻ y, B.indicator (fun y =>
              SubMarkovKernelSemigroup.finiteTimeKernel Q τ.relativeTail y C) y
              ∂((P.restrict A).map (X t₀)) := by
            rw [lintegral_map hKC (hXm t₀), lintegral_map hφ (hXm t₀)]
            have hfun : (fun w => B.indicator (fun y =>
                SubMarkovKernelSemigroup.finiteTimeKernel Q τ.relativeTail y C) (X t₀ w)) =
                (X t₀ ⁻¹' B).indicator (fun w =>
                  SubMarkovKernelSemigroup.finiteTimeKernel Q τ.relativeTail (X t₀ w) C) := by
              funext w
              by_cases hw : X t₀ w ∈ B <;> simp [hw]
            rw [hfun, lintegral_indicator (hXm t₀ hB), Measure.restrict_restrict (hXm t₀ hB),
              inter_comm]
        _ = ∫⁻ y, B.indicator (fun y =>
              SubMarkovKernelSemigroup.finiteTimeKernel Q τ.relativeTail y C) y
              ∂(Q (τ 0) ∘ₘ (P.restrict A).map (X s)) := by rw [hmark]
        _ = ∫⁻ x, ∫⁻ y, B.indicator (fun y =>
              SubMarkovKernelSemigroup.finiteTimeKernel Q τ.relativeTail y C) y ∂(Q (τ 0) x)
              ∂((P.restrict A).map (X s)) :=
            Measure.lintegral_bind (Kernel.aemeasurable _) hφ.aemeasurable
        _ = ∫⁻ x, (Q (τ 0) ⊗ₖ Kernel.prodMkLeft (Vec d)
              (SubMarkovKernelSemigroup.finiteTimeKernel Q τ.relativeTail)) x (B ×ˢ C)
              ∂((P.restrict A).map (X s)) := by
            refine lintegral_congr fun x => ?_
            rw [Kernel.compProd_apply_prod hB hC, lintegral_indicator hB]
            simp only [Kernel.prodMkLeft_apply]
        _ = _ := (Measure.bind_apply (hB.prod hC) (Kernel.aemeasurable _)).symm
    rw [hpath, ← Measure.map_map (measurable_finCons (α := Vec d) (n := n)) hpair,
      SubMarkovKernelSemigroup.finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
      ← Measure.map_comp _ _ (measurable_finCons (α := Vec d) (n := n))]
    congr 1
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨B, hB, C, hC, rfl⟩
      exact hrect B hB C hC
    · rw [← univ_prod_univ]
      exact hrect univ MeasurableSet.univ univ MeasurableSet.univ

/-- **The finite-dimensional laws of a solution started at `x`** are those of the semigroup `Q`
from `x`. -/
theorem map_eq_finiteTimeKernel (hIto : ItoFormulaStopped.{u} d)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P ℱ] {σ : ℝ} {b : Vec d → Vec d}
    (hb : Continuous b) {W X : ℝ≥0 → Ω → Vec d} (hW : IsBrownianMotion W ℱ P)
    (hX : IsStrongSolution σ b W X ℱ) {Q : SubMarkovKernelSemigroup (Vec d)}
    (hQ : HasClassicalResolvent Q σ b)
    (hQc : ∀ h : Vec d → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → ∀ y,
      Continuous fun t : ℝ≥0 => ∫ z, h z ∂(Q t y))
    {x : Vec d} (hX0 : ∀ w, X 0 w = x) {n : ℕ} (τ : FiniteOrderedTimes n) :
    P.map (fun w i => X (τ i) w) = SubMarkovKernelSemigroup.finiteTimeKernel Q τ x := by
  have h := map_restrict_eq_finiteTimeKernel_comp hIto hb hW hX hQ hQc n τ 0 univ
    MeasurableSet.univ
  simp only [zero_add, Measure.restrict_univ] at h
  have hX0' : X 0 = fun _ => x := funext hX0
  rw [h, hX0', Measure.map_const, measure_univ, one_smul,
    Measure.dirac_bind (Kernel.measurable _)]

/-- Simultaneous evaluation of a continuous path at a finite set of times is measurable. -/
theorem measurable_finsetEvaluation' (I : Finset ℝ≥0) :
    Measurable (ContinuousPath.finsetEvaluation (alpha := Vec d) I) :=
  measurable_pi_iff.mpr fun t => ContinuousPath.measurable_coordinateProcess (t : ℝ≥0)

/-- The path `t ↦ X_t(w)` of a solution, as a continuous path. -/
def solutionPath {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 mΩ} {σ : ℝ}
    {b : Vec d → Vec d} {W X : ℝ≥0 → Ω → Vec d} (hX : IsStrongSolution σ b W X ℱ) (w : Ω) :
    ContinuousPath (Vec d) :=
  ⟨fun t => X t w, hX.continuous w⟩

theorem measurable_solutionPath {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 mΩ}
    {σ : ℝ} {b : Vec d → Vec d} {W X : ℝ≥0 → Ω → Vec d} (hX : IsStrongSolution σ b W X ℱ) :
    Measurable (solutionPath hX) := by
  rw [← ContinuousPath.measurableEmbedding_denseRestriction.measurable_comp_iff]
  exact measurable_pi_iff.mpr fun q => (hX.adapted _).mono (ℱ.le _) le_rfl

/-- **The law of a solution started at `x`.** A finite measure on continuous paths whose
finite-dimensional distributions are those of `Q` from `x` is the law of every solution of
`dX = σ dW + b(X) dt` started at `x`. -/
theorem map_solutionPath_eq (hIto : ItoFormulaStopped.{u} d)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P ℱ] {σ : ℝ} {b : Vec d → Vec d}
    (hb : Continuous b) {W X : ℝ≥0 → Ω → Vec d} (hW : IsBrownianMotion W ℱ P)
    (hX : IsStrongSolution σ b W X ℱ) {Q : SubMarkovKernelSemigroup (Vec d)}
    (hQ : HasClassicalResolvent Q σ b)
    (hQc : ∀ h : Vec d → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → ∀ y,
      Continuous fun t : ℝ≥0 => ∫ z, h z ∂(Q t y))
    {x : Vec d} (hX0 : ∀ w, X 0 w = x) (ν : Measure (ContinuousPath (Vec d))) [IsFiniteMeasure ν]
    (hν : ∀ I : Finset ℝ≥0,
      ν.map (ContinuousPath.finsetEvaluation I) = SubMarkovKernelSemigroup.finiteSetKernel Q I x) :
    P.map (solutionPath hX) = ν := by
  have hXm : ∀ t, Measurable (X t) := fun t => (hX.adapted t).mono (ℱ.le t) le_rfl
  have hpm := measurable_solutionPath hX
  have hev := measurable_finsetEvaluation' (d := d)
  have hmarg : ∀ I : Finset ℝ≥0, (P.map (solutionPath hX)).map (ContinuousPath.finsetEvaluation I) =
      SubMarkovKernelSemigroup.finiteSetKernel Q I x := by
    intro I
    rw [Measure.map_map (hev I) hpm, SubMarkovKernelSemigroup.finiteSetKernel_eq_map,
      Kernel.map_apply _ (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I),
      ← map_eq_finiteTimeKernel hIto hb hW hX hQ hQc hX0
        (SubMarkovKernelSemigroup.finiteSetTimes I),
      Measure.map_map (SubMarkovKernelSemigroup.measurable_orderedPathToFiniteSet I)
        (measurable_pi_iff.mpr fun i => hXm _)]
    congr 1
    funext w t
    show X (t : ℝ≥0) w = X (I.orderEmbOfFin rfl ((I.orderIsoOfFin rfl).symm t)) w
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  have hconst := Kernel.eq_of_map_denseFiniteEvaluation_eq
    (Kernel.const Unit (P.map (solutionPath hX))) (Kernel.const Unit ν) fun I => by
      rw [Kernel.map_const _ (hev _), Kernel.map_const _ (hev _), hmarg, hν]
  simpa only [Kernel.const_apply] using congrArg (fun κ : Kernel Unit _ => κ ()) hconst

end SubdiffusiveProcess.SDE
