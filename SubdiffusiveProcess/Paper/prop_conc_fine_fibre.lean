module

public import SubdiffusiveProcess.Probability.ResampledLimit
public import SubdiffusiveProcess.Probability.CopyLayerBlock
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Tactic

@[expose] public section

/-! Fibrewise reduction of the resampling estimate on the product `μ = ⊗_i laws i`.  A bound on
`‖f(ω^y) - f(ω^{y'})‖_{L^p(y,y')}` for a.e. fixed `ω` (with `ω^y = update ω j y`), by measurable
envelopes evaluated along the fibre through `ω`, integrates to the bound on
`‖f(ω) - f(update ω j ω'_j)‖_{L^p(μ⊗μ)}` by envelopes evaluated at the pair `(ω, update ω j ω'_j)`.
No measurability of anything chosen along the fibre (references, pairs) is used: only the measurable
functions `f`, `E₁`, `E₂`.  The second part transfers the Efron--Stein inequality for one fixed base to
the layer variable. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators
namespace Paper
noncomputable section

section fibre
variable {I X : Type*} [MeasurableSpace X] (laws : I → Measure X) [∀ i, IsProbabilityMeasure (laws i)]

theorem aux_prop_conc_fine_fibre_lintegral_eval (j : I) (G : X → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ ω, G (ω j) ∂(Measure.infinitePi laws) = ∫⁻ y, G y ∂(laws j) := by
  rw [← Measure.infinitePi_map_eval laws j, lintegral_map hG (measurable_pi_apply j)]

/-- Integrating a function of `(ω, ω'_j)` over the product of two copies. -/
theorem aux_prop_conc_fine_fibre_prod (j : I) (G : (I → X) → X → ℝ≥0∞)
    (hG : Measurable (Function.uncurry G)) :
    ∫⁻ q, G q.1 (q.2 j) ∂((Measure.infinitePi laws).prod (Measure.infinitePi laws)) =
      ∫⁻ ω, ∫⁻ y, G ω y ∂(laws j) ∂(Measure.infinitePi laws) := by
  have hm : Measurable (fun q : (I → X) × (I → X) => G q.1 (q.2 j)) :=
    hG.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  rw [lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun ω => ?_
  exact aux_prop_conc_fine_fibre_lintegral_eval laws j (G ω) (hG.comp measurable_prodMk_left)

/-- The diagonal integral of a fibre-invariant function equals the integral over an independent copy. -/
theorem aux_prop_conc_fine_fibre_diag [DecidableEq I] (j : I) (A : (I → X) → X → ℝ≥0∞)
    (hA : Measurable (Function.uncurry A))
    (hinv : ∀ ω z y, A (Function.update ω j z) y = A ω y) :
    ∫⁻ ω, A ω (ω j) ∂(Measure.infinitePi laws) =
      ∫⁻ ω, ∫⁻ y, A ω y ∂(laws j) ∂(Measure.infinitePi laws) := by
  have hU := SubdiffusiveProcess.Probability.measurePreserving_update_infinitePi laws j
  have hF : Measurable (fun ω : I → X => A ω (ω j)) :=
    hA.comp (measurable_id.prodMk (measurable_pi_apply j))
  rw [← hU.lintegral_comp hF]
  have : (fun q : (I → X) × (I → X) => A (Function.update q.1 j (q.2 j))
      ((Function.update q.1 j (q.2 j)) j)) = fun q => A q.1 (q.2 j) := by
    funext q
    rw [Function.update_self, hinv]
  rw [this]
  exact aux_prop_conc_fine_fibre_prod laws j A hA

end fibre


theorem aux_prop_conc_fine_fibre_smul_rpow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (c : ℝ≥0∞)
    (g : Ω → ℝ≥0∞) (hg : AEMeasurable g P) {p : ℝ} (hp : 0 < p) :
    (∫⁻ ω, (c * g ω ^ (1 / p)) ^ p ∂P) ^ (1 / p) = c * (∫⁻ ω, g ω ∂P) ^ (1 / p) := by
  have h1 : ∀ ω, (c * g ω ^ (1 / p)) ^ p = c ^ p * g ω := by
    intro ω
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne',
      ENNReal.rpow_one]
  simp only [h1]
  rw [lintegral_const_mul'' _ hg, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- A null set of the product law is avoided by the resampled configuration of almost every sample and
almost every resampled layer value. -/
theorem aux_prop_conc_fine_fibre_null {I X Ω : Type*} [DecidableEq I] [MeasurableSpace X]
    [MeasurableSpace Ω] (laws : I → Measure X) [∀ i, IsProbabilityMeasure (laws i)] (j : I)
    (P₀ : Measure Ω) [IsProbabilityMeasure P₀] (field : Ω → (I → X)) (hfield : Measurable field)
    (hlaw : P₀.map field = Measure.infinitePi laws) (N : Set (I → X)) (hN : MeasurableSet N)
    (h0 : Measure.infinitePi laws N = 0) :
    ∀ᵐ ω ∂P₀, ∀ᵐ y ∂(laws j), Function.update (field ω) j y ∉ N := by
  set μ := Measure.infinitePi laws with hμ
  set W : (I → X) × X → (I → X) := fun w => Function.update w.1 j w.2 with hW
  have hWm : Measurable W := measurable_update'
  have hh : MeasurePreserving (Prod.map (id : (I → X) → (I → X)) (fun η : I → X => η j))
      (μ.prod μ) (μ.prod (laws j)) :=
    (MeasurePreserving.id μ).prod ⟨measurable_pi_apply j, Measure.infinitePi_map_eval laws j⟩
  have hWL : (μ.prod (laws j)).map W = μ := by
    have hU := SubdiffusiveProcess.Probability.measurePreserving_update_infinitePi laws j
    have hcomp : (W ∘ Prod.map (id : (I → X) → (I → X)) (fun η : I → X => η j)) =
        fun z : (I → X) × (I → X) => Function.update z.1 j (z.2 j) := rfl
    calc (μ.prod (laws j)).map W = ((μ.prod μ).map (Prod.map id fun η : I → X => η j)).map W := by
          rw [hh.map_eq]
      _ = (μ.prod μ).map (W ∘ Prod.map id fun η : I → X => η j) :=
          Measure.map_map hWm hh.measurable
      _ = μ := by rw [hcomp]; exact hU.map_eq
  have hfL : (P₀.prod (laws j)).map (Prod.map field (id : X → X)) = μ.prod (laws j) := by
    rw [← Measure.map_prod_map _ _ hfield measurable_id, hlaw, Measure.map_id]
  set g : Ω × X → (I → X) := fun w => Function.update (field w.1) j w.2 with hg
  have hgm : Measurable g := hWm.comp (hfield.comp measurable_fst |>.prodMk measurable_snd)
  have hgmap : (P₀.prod (laws j)).map g = μ := by
    have : g = W ∘ Prod.map field (id : X → X) := rfl
    rw [this, ← Measure.map_map hWm (hfield.prodMap measurable_id), hfL, hWL]
  have hnull : (P₀.prod (laws j)) (g ⁻¹' N) = 0 := by
    rw [← Measure.map_apply hgm hN, hgmap]; exact h0
  have hmeas : MeasurableSet (g ⁻¹' N) := hgm hN
  rw [Measure.measure_prod_null hmeas] at hnull
  filter_upwards [hnull] with ω hω
  have : (laws j) {y | Function.update (field ω) j y ∈ N} = 0 := hω
  exact measure_eq_zero_iff_ae_notMem.mp this

/-- **Fibre reduction.** -/
theorem prop_conc_fine_fibre {I X Ω : Type*} [DecidableEq I] [MeasurableSpace X] [MeasurableSpace Ω]
    (laws : I → Measure X) [∀ i, IsProbabilityMeasure (laws i)] (j : I)
    (P₀ : Measure Ω) (field : Ω → (I → X)) (hfield : Measurable field)
    (hlaw : P₀.map field = Measure.infinitePi laws)
    (f : (I → X) → ℝ) (hf : Measurable f) (p : ℝ) (hp : 1 ≤ p)
    (E1 E2 : (I → X) → (I → X) → ℝ)
    (hE1 : Measurable (Function.uncurry E1)) (hE2 : Measurable (Function.uncurry E2))
    (c1 c2 : ℝ≥0∞)
    (hfib : ∀ᵐ ω ∂P₀,
      eLpNorm (fun yy : X × X => f (Function.update (field ω) j yy.1) - f (Function.update (field ω) j yy.2))
          (ENNReal.ofReal p) ((laws j).prod (laws j)) ≤
        c1 * eLpNorm (fun y => E1 (field ω) (Function.update (field ω) j y)) (ENNReal.ofReal p) (laws j) +
        c2 * eLpNorm (fun y => E2 (field ω) (Function.update (field ω) j y)) (ENNReal.ofReal p) (laws j)) :
    eLpNorm (fun q : (I → X) × (I → X) => f q.1 - f (Function.update q.1 j (q.2 j)))
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤
      c1 * eLpNorm (fun q : (I → X) × (I → X) => E1 q.1 (Function.update q.1 j (q.2 j)))
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) +
      c2 * eLpNorm (fun q : (I → X) × (I → X) => E2 q.1 (Function.update q.1 j (q.2 j)))
        (ENNReal.ofReal p) ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) := by
  set P := Measure.infinitePi laws with hP
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hpne0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hpne : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hpt : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hp1 : (0 : ℝ) ≤ 1 / p := by positivity
  -- measurability of the fibre integrands
  have hfu : Measurable (fun w : (I → X) × X => f (Function.update w.1 j w.2)) :=
    hf.comp (measurable_update'.comp ((measurable_fst).prodMk (measurable_snd)))
  set Fq : ((I → X) × X) × X → ℝ≥0∞ := fun w =>
    ‖f (Function.update w.1.1 j w.1.2) - f (Function.update w.1.1 j w.2)‖ₑ ^ p with hFq
  have hFqm : Measurable Fq := by
    have h1 : Measurable (fun w : ((I → X) × X) × X => f (Function.update w.1.1 j w.1.2)) :=
      hfu.comp measurable_fst
    have h2 : Measurable (fun w : ((I → X) × X) × X => f (Function.update w.1.1 j w.2)) :=
      hfu.comp (measurable_fst.comp measurable_fst |>.prodMk measurable_snd)
    exact ((h1.sub h2).enorm).pow_const p
  -- G ω y := ∫⁻ y', ‖f(ω^y) - f(ω^y')‖^p
  set G : (I → X) → X → ℝ≥0∞ := fun ω y =>
    ∫⁻ y', ‖f (Function.update ω j y) - f (Function.update ω j y')‖ₑ ^ p ∂(laws j) with hG
  have hGm : Measurable (Function.uncurry G) := by
    have : Function.uncurry G = fun w : (I → X) × X =>
        ∫⁻ y', Fq ((w.1, w.2), y') ∂(laws j) := by
      funext w; rfl
    rw [this]
    exact hFqm.lintegral_prod_right'
  -- the left side as an iterated integral
  have hLHS : ∫⁻ q, ‖f q.1 - f (Function.update q.1 j (q.2 j))‖ₑ ^ p ∂(P.prod P) =
      ∫⁻ ω, ∫⁻ yy, ‖f (Function.update ω j yy.1) - f (Function.update ω j yy.2)‖ₑ ^ p
        ∂((laws j).prod (laws j)) ∂P := by
    have hH : Measurable (Function.uncurry (fun (ω : I → X) (y' : X) =>
        ‖f ω - f (Function.update ω j y')‖ₑ ^ p)) := by
      have h1 : Measurable (fun w : (I → X) × X => f w.1) := hf.comp measurable_fst
      exact ((h1.sub hfu).enorm).pow_const p
    have e1 := aux_prop_conc_fine_fibre_prod laws j
      (fun ω y' => ‖f ω - f (Function.update ω j y')‖ₑ ^ p) hH
    rw [e1]
    have e2 : ∀ ω : I → X, ∫⁻ y', ‖f ω - f (Function.update ω j y')‖ₑ ^ p ∂(laws j) = G ω (ω j) := by
      intro ω
      simp only [hG, Function.update_eq_self]
    simp only [e2]
    have hinv : ∀ (ω : I → X) (z y : X), G (Function.update ω j z) y = G ω y := by
      intro ω z y
      simp only [hG, Function.update_idem]
    rw [aux_prop_conc_fine_fibre_diag laws j G hGm hinv]
    refine lintegral_congr fun ω => ?_
    have hmeas : Measurable (fun yy : X × X =>
        ‖f (Function.update ω j yy.1) - f (Function.update ω j yy.2)‖ₑ ^ p) :=
      hFqm.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    rw [lintegral_prod _ hmeas.aemeasurable]
  -- the fibre quantities
  set aF : (I → X) → ℝ≥0∞ := fun ω => ∫⁻ yy, ‖f (Function.update ω j yy.1) -
    f (Function.update ω j yy.2)‖ₑ ^ p ∂((laws j).prod (laws j)) with haF
  have hEm : ∀ (E : (I → X) → (I → X) → ℝ), Measurable (Function.uncurry E) →
      Measurable (Function.uncurry (fun (ω : I → X) (y : X) =>
        ‖E ω (Function.update ω j y)‖ₑ ^ p)) := by
    intro E hE
    have h : Measurable (fun w : (I → X) × X => E w.1 (Function.update w.1 j w.2)) :=
      hE.comp (measurable_fst.prodMk (measurable_update'.comp (measurable_fst.prodMk measurable_snd)))
    exact (h.enorm).pow_const p
  set b1 : (I → X) → ℝ≥0∞ := fun ω => ∫⁻ y, ‖E1 ω (Function.update ω j y)‖ₑ ^ p ∂(laws j) with hb1
  set b2 : (I → X) → ℝ≥0∞ := fun ω => ∫⁻ y, ‖E2 ω (Function.update ω j y)‖ₑ ^ p ∂(laws j) with hb2
  have hb1m : Measurable b1 := (hEm E1 hE1).lintegral_prod_right'
  have hb2m : Measurable b2 := (hEm E2 hE2).lintegral_prod_right'
  have hRHS1 : ∫⁻ ω, b1 ω ∂P = ∫⁻ q, ‖E1 q.1 (Function.update q.1 j (q.2 j))‖ₑ ^ p ∂(P.prod P) :=
    (aux_prop_conc_fine_fibre_prod laws j (fun ω y => ‖E1 ω (Function.update ω j y)‖ₑ ^ p)
      (hEm E1 hE1)).symm
  have hRHS2 : ∫⁻ ω, b2 ω ∂P = ∫⁻ q, ‖E2 q.1 (Function.update q.1 j (q.2 j))‖ₑ ^ p ∂(P.prod P) :=
    (aux_prop_conc_fine_fibre_prod laws j (fun ω y => ‖E2 ω (Function.update ω j y)‖ₑ ^ p)
      (hEm E2 hE2)).symm
  have haFm : Measurable aF := by
    have hmeas : Measurable (fun w : (I → X) × (X × X) =>
        ‖f (Function.update w.1 j w.2.1) - f (Function.update w.1 j w.2.2)‖ₑ ^ p) := by
      have h1 : Measurable (fun w : (I → X) × (X × X) => f (Function.update w.1 j w.2.1)) :=
        hf.comp (measurable_update'.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
      have h2 : Measurable (fun w : (I → X) × (X × X) => f (Function.update w.1 j w.2.2)) :=
        hf.comp (measurable_update'.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
      exact ((h1.sub h2).enorm).pow_const p
    exact hmeas.lintegral_prod_right'
  have hfibre0 : ∀ᵐ ω ∂P₀, aF (field ω) ^ (1 / p) ≤
      c1 * b1 (field ω) ^ (1 / p) + c2 * b2 (field ω) ^ (1 / p) := by
    filter_upwards [hfib] with ω hω
    have hfm : Measurable (fun yy : X × X =>
        f (Function.update (field ω) j yy.1) - f (Function.update (field ω) j yy.2)) :=
      (hf.comp (measurable_update'.comp (measurable_const.prodMk measurable_fst))).sub
        (hf.comp (measurable_update'.comp (measurable_const.prodMk measurable_snd)))
    have hE1m : Measurable (fun y => E1 (field ω) (Function.update (field ω) j y)) :=
      hE1.comp (measurable_const.prodMk
        (measurable_update'.comp (measurable_const.prodMk measurable_id)))
    have hE2m : Measurable (fun y => E2 (field ω) (Function.update (field ω) j y)) :=
      hE2.comp (measurable_const.prodMk
        (measurable_update'.comp (measurable_const.prodMk measurable_id)))
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne0 hpne hfm.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hpne0 hpne hE1m.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hpne0 hpne hE2m.aestronglyMeasurable, hpt] at hω
    exact hω
  have hfibre : ∀ᵐ ω ∂P, aF ω ^ (1 / p) ≤ c1 * b1 ω ^ (1 / p) + c2 * b2 ω ^ (1 / p) := by
    have hSm : MeasurableSet {ω : I → X | aF ω ^ (1 / p) ≤ c1 * b1 ω ^ (1 / p) + c2 * b2 ω ^ (1 / p)} :=
      measurableSet_le (haFm.pow_const _)
        ((measurable_const.mul (hb1m.pow_const _)).add (measurable_const.mul (hb2m.pow_const _)))
    have := (ae_map_iff hfield.aemeasurable hSm).mpr hfibre0
    rwa [hlaw] at this
  have hstep : ∫⁻ ω, aF ω ∂P ≤ ∫⁻ ω, (c1 * b1 ω ^ (1 / p) + c2 * b2 ω ^ (1 / p)) ^ p ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [hfibre] with ω hω
    calc aF ω = (aF ω ^ (1 / p)) ^ p := by
          rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
      _ ≤ _ := ENNReal.rpow_le_rpow hω hp0.le
  have hu : AEMeasurable (fun ω => c1 * b1 ω ^ (1 / p)) P :=
    (measurable_const.mul (hb1m.pow_const _)).aemeasurable
  have hv : AEMeasurable (fun ω => c2 * b2 ω ^ (1 / p)) P :=
    (measurable_const.mul (hb2m.pow_const _)).aemeasurable
  have hmink := ENNReal.lintegral_Lp_add_le (μ := P) hu hv hp
  have hUm : Measurable (fun q : (I → X) × (I → X) => Function.update q.1 j (q.2 j)) :=
    measurable_update'.comp
      (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))
  have hfm : Measurable (fun q : (I → X) × (I → X) =>
      f q.1 - f (Function.update q.1 j (q.2 j))) :=
    (hf.comp measurable_fst).sub (hf.comp hUm)
  have hE1m : Measurable (fun q : (I → X) × (I → X) =>
      E1 q.1 (Function.update q.1 j (q.2 j))) :=
    hE1.comp (measurable_fst.prodMk hUm)
  have hE2m : Measurable (fun q : (I → X) × (I → X) =>
      E2 q.1 (Function.update q.1 j (q.2 j))) :=
    hE2.comp (measurable_fst.prodMk hUm)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne0 hpne hfm.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpne0 hpne hE1m.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpne0 hpne hE2m.aestronglyMeasurable,
    hpt, hLHS, ← hRHS1, ← hRHS2]
  calc (∫⁻ ω, aF ω ∂P) ^ (1 / p) ≤ (∫⁻ ω, (c1 * b1 ω ^ (1 / p) + c2 * b2 ω ^ (1 / p)) ^ p ∂P) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hstep hp1
    _ ≤ (∫⁻ ω, (c1 * b1 ω ^ (1 / p)) ^ p ∂P) ^ (1 / p) +
          (∫⁻ ω, (c2 * b2 ω ^ (1 / p)) ^ p ∂P) ^ (1 / p) := hmink
    _ = c1 * (∫⁻ ω, b1 ω ∂P) ^ (1 / p) + c2 * (∫⁻ ω, b2 ω ∂P) ^ (1 / p) := by
        rw [aux_prop_conc_fine_fibre_smul_rpow P c1 b1 hb1m.aemeasurable hp0,
          aux_prop_conc_fine_fibre_smul_rpow P c2 b2 hb2m.aemeasurable hp0]

end
end Paper
