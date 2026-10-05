module

public import SubdiffusiveProcess.Frozen.Main.AnomalousHolderRegularity

@[expose] public section

/-!
# Theorem C: large-scale regularity and Liouville constancy

A given small-disorder `GMCModel d` supplies the law on `AnchoredC11Sample d`.
The cutoff index is `WithTop ℕ`: finite values select cutoff coefficients and
`⊤` selects the anchored uncut coefficient. Harmonic functions on cubes belong
to `H1Function`; harmonicity is the weak divergence-form equation.

For each deterministic exponent `gamma` between `1/2` and `gammaReg`, the
conclusion supplies random integer scales indexed by cutoff and observation
scale. Their tail bound has deterministic constants chosen before the model
and is uniform in the cutoff. One full-measure event handles all cutoffs,
observation cubes, harmonic functions and admissible subcubes. The estimates
control normalized `L²` oscillation and the coefficient-weighted gradient
energy at scales above the random minimum. They do not assert microscopic
pointwise Hölder continuity.

The Liouville clause assumes entire weak harmonicity through local `H¹`
representatives and a subcritical liminf growth condition. It produces a
continuous representative agreeing almost everywhere with the original
function, and proves that representative constant. Agreement on each local
cube repeats the global a.e. agreement to expose the local `H¹` interface.
`SubdiffusiveProcess.Paper.t_C` additionally makes every minimal-scale random variable measurable.
The dimension argument repeats the dimension stored in `GMCModel`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter SubdiffusiveProcess _root_.SubdiffusiveProcess.Model MeasureTheory ProbabilityTheory
open Homogenization hiding Vec
open Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Section9 (centeredAxisCube)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
open scoped ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- A measurable `ℕ`-valued majorant with the same tail bound (used to make the minimal-scale
random variable of Theorem C a genuine random variable). -/
theorem aux_t_C_measurable_majorant {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (f : Ω → ℕ) (b : ℕ → ℝ≥0∞) (hb : ∀ k, 0 < k → mu {ω | k < f ω} ≤ b k)
    (hb0 : Tendsto b atTop (𝓝 0)) :
    ∃ g : Ω → ℕ, Measurable g ∧ (∀ k, 0 < k → mu {ω | k < g ω} ≤ b k) ∧
      ∀ᵐ ω ∂mu, f ω ≤ g ω := by
  classical
  have hex : ∀ k : ℕ, ∃ T : Set Ω, {ω | k < f ω} ⊆ T ∧ MeasurableSet T ∧
      mu T = mu {ω | k < f ω} := fun k => exists_measurable_superset mu _
  choose T hT1 hT2 hT3 using hex
  let S : ℕ → Set Ω := fun k => ⋂ j ∈ Finset.range (k + 1), T j
  have hSmeas : ∀ k, MeasurableSet (S k) := fun k =>
    Finset.measurableSet_biInter _ fun j _ => hT2 j
  have hSsub : ∀ k, {ω | k < f ω} ⊆ S k := by
    intro k ω hω
    simp only [S, Set.mem_iInter, Finset.mem_range]
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp hj
    exact hT1 j (show j < f ω from lt_of_le_of_lt hjk hω)
  have hSanti : ∀ j k, j ≤ k → S k ⊆ S j := by
    intro j k hjk ω hω
    simp only [S, Set.mem_iInter, Finset.mem_range] at hω ⊢
    intro i hi
    exact hω i (by omega)
  have hSle : ∀ k, mu (S k) ≤ mu {ω | k < f ω} := by
    intro k
    calc mu (S k) ≤ mu (T k) := by
          refine measure_mono ?_
          intro ω hω
          simp only [S, Set.mem_iInter, Finset.mem_range] at hω
          exact hω k (by omega)
      _ = mu {ω | k < f ω} := hT3 k
  let E : Set Ω := ⋂ k, S k
  have hEmeas : MeasurableSet E := MeasurableSet.iInter hSmeas
  have hE0 : mu E = 0 := by
    have h1 : ∀ᶠ k in atTop, mu E ≤ b k := by
      filter_upwards [eventually_gt_atTop 0] with k hk
      exact (measure_mono (Set.iInter_subset _ k)).trans ((hSle k).trans (hb k hk))
    exact le_antisymm (ge_of_tendsto hb0 h1) bot_le
  let g : Ω → ℕ := fun ω => sInf {k : ℕ | ω ∉ S k}
  have hg_iff : ∀ ω, ω ∉ E → ∀ k, k < g ω ↔ ω ∈ S k := by
    intro ω hωE k
    have hne : {k : ℕ | ω ∉ S k}.Nonempty := by
      by_contra h
      apply hωE
      simp only [E, Set.mem_iInter]
      intro k
      by_contra hk
      exact h ⟨k, hk⟩
    constructor
    · intro hk
      have : k ∉ {k : ℕ | ω ∉ S k} := Nat.notMem_of_lt_sInf hk
      simpa using this
    · intro hk
      by_contra hlt
      push Not at hlt
      have hmem : ω ∉ S (sInf {k : ℕ | ω ∉ S k}) := Nat.sInf_mem hne
      exact hmem (hSanti _ _ hlt hk)
  have hg_set : ∀ k, {ω | k < g ω} = S k \ E := by
    intro k
    ext ω
    by_cases hωE : ω ∈ E
    · have hA : {k : ℕ | ω ∉ S k} = ∅ := by
        ext j
        simp only [mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
        exact Set.mem_iInter.mp hωE j
      simp [g, hA, hωE]
    · simp only [mem_ofPred_eq, Set.mem_sdiff, hωE, not_false_eq_true, and_true]
      exact hg_iff ω hωE k
  refine ⟨g, ?_, ?_, ?_⟩
  · refine measurable_of_Ioi fun k => ?_
    have : g ⁻¹' Set.Ioi k = {ω | k < g ω} := rfl
    rw [this, hg_set k]
    exact (hSmeas k).diff hEmeas
  · intro k hk
    rw [hg_set k]
    exact (measure_mono sdiff_subset).trans ((hSle k).trans (hb k hk))
  · refine measure_mono_null (t := E) ?_ hE0
    intro ω hω
    by_contra hωE
    have hlt : g ω < f ω := by
      by_contra h
      exact hω (not_lt.mp h)
    have hmemS : ω ∈ S (g ω) := hSsub (g ω) hlt
    exact absurd ((hg_iff ω hωE (g ω)).mpr hmemS) (lt_irrefl _)

/-- The Gaussian-type tail bound of Theorem C tends to `0`. -/
theorem aux_t_C_tail_tendsto (C gamma delta : ℝ) (hC : 0 < C) (hg : gamma < 1)
    (hd0 : 0 < delta) (hd1 : delta < 1) :
    Tendsto (fun k : ℕ => ENNReal.ofReal (C * Real.exp
      (-((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) / (C * delta ^ 2 * |Real.log delta|))))
      atTop (𝓝 0) := by
  have hlog : Real.log delta < 0 := Real.log_neg hd0 hd1
  have hDn : 0 < C * delta ^ 2 * |Real.log delta| := by
    have : 0 < |Real.log delta| := abs_pos.mpr hlog.ne
    positivity
  have hkap : 0 < (1 - gamma) ^ 2 / (C * delta ^ 2 * |Real.log delta|) := by
    have : 0 < 1 - gamma := by linarith
    positivity
  have hmax : Tendsto (fun k : ℕ => max ((k : ℝ) - C) 0) atTop atTop := by
    refine tendsto_atTop_mono (fun k => le_max_left _ _) ?_
    have := tendsto_atTop_add_const_right atTop (-C) (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [sub_eq_add_neg] using this
  have hexp : Tendsto (fun k : ℕ => Real.exp (-(((1 - gamma) ^ 2 / (C * delta ^ 2 * |Real.log delta|)) *
      max ((k : ℝ) - C) 0))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (hmax.const_mul_atTop hkap))
  have hreal : Tendsto (fun k : ℕ => C * Real.exp
      (-((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) / (C * delta ^ 2 * |Real.log delta|)))
      atTop (𝓝 0) := by
    have heq : ∀ k : ℕ, -((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) / (C * delta ^ 2 * |Real.log delta|) =
        -(((1 - gamma) ^ 2 / (C * delta ^ 2 * |Real.log delta|)) * max ((k : ℝ) - C) 0) := by
      intro k
      field_simp
    simp only [heq]
    simpa using hexp.const_mul C
  have := (ENNReal.tendsto_ofReal hreal)
  simpa using this

/-- Theorem C: cutoff-uniform large-scale oscillation and weighted-energy
estimates for weakly harmonic `H¹` functions, with measurable random minimal
scales and an exponential tail. Under subcritical liminf growth, an entire
harmonic function has a constant continuous representative. The common
environment event covers all cutoffs and all admissible cubes and data. -/
theorem t_C (d : ℕ) (hd : 2 ≤ d) :
    ∃ delta0 C0 C : ℝ, 0 < delta0 ∧ 0 < C0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
        let mu := (anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
          (measure_anchoredC11GoodSet_eq_one M)).toMeasure
        gammaReg C0 M.delta ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
        ∀ gamma ∈ Set.Icc (1 / 2 : ℝ) (gammaReg C0 M.delta),
          ∃ Lscale : WithTop ℕ → ℕ → AnchoredC11Sample d → ℕ,
            (∀ (L : WithTop ℕ) (m : ℕ), Measurable (Lscale L m)) ∧
            (∀ (L : WithTop ℕ) (m k : ℕ), 0 < k →
              mu {omega | k < Lscale L m omega} ≤
                ENNReal.ofReal (C * Real.exp (
                  -((1 - gamma) ^ 2 * max ((k : ℝ) - C) 0) /
                    (C * M.delta ^ 2 * |Real.log M.delta|)))) ∧
            ∀ᵐ omega ∂mu,
              (∀ (L : WithTop ℕ) (m : ℕ), 0 < m →
                ∀ u : H1Function (openCubeSet (originCube d m)),
                  IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) u →
                  ∀ n : ℕ, (n : ℤ) ≤ (m : ℤ) - (Lscale L m omega : ℤ) →
                    ∀ z : Vec d, OnTriadicGrid n z →
                    translatedCube d n z ⊆ cube d (m - 1) →
                      normalizedL2On (translatedCube d n z)
                          (fun x => u.toFun x - averageOn (translatedCube d n z) u.toFun) ≤
                        C * (3 : ℝ) ^ (-gamma * ((m : ℝ) - (n : ℝ))) *
                          normalizedL2On (cube d m)
                            (fun x => u.toFun x - averageOn (cube d m) u.toFun) ∧
                      vectorNormalizedL2On (translatedCube d n z)
                          (fun x => Real.sqrt (coefficientAt M L omega x) • u.grad x) ≤
                        C * (3 : ℝ) ^ ((1 - gamma) * ((m : ℝ) - (n : ℝ))) *
                          vectorNormalizedL2On (cube d m)
                            (fun x => Real.sqrt (coefficientAt M L omega x) • u.grad x)) ∧
              (∀ (L : WithTop ℕ) (u : Vec d → ℝ),
                (∀ m : ℤ, ∃ um : H1Function (openCubeSet (originCube d m)),
                  (∀ x, um.toFun x = u x) ∧
                    IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) um) →
                (∀ eps > 0, ∃ᶠ R : ℝ in atTop, R ^ (-gammaReg C0 M.delta) *
                    sInf {r : ℝ | ∃ c : ℝ,
                      r = normalizedL2On (Metric.ball (0 : Vec d) R) (fun x => u x - c)} < eps) →
                ∃ uRep : Vec d → ℝ,
                  Continuous uRep ∧ uRep =ᵐ[volume] u ∧
                  (∀ m : ℤ, ∀ um : H1Function (openCubeSet (originCube d m)),
                    (∀ x, um.toFun x = u x) →
                    IsWeaklyHarmonicOn (coefficientAt M L omega) (cube d m) um →
                    uRep =ᵐ[volume.restrict (openCubeSet (originCube d m))] um.toFun) ∧
                  ∃ c : ℝ, ∀ x, uRep x = c) := by
  obtain ⟨delta0, C0, C, hd0, hC0, hC, h⟩ := SubdiffusiveProcess.Frozen.Main.anomalous_holder_regularity d hd
  refine ⟨delta0, C0, C, hd0, hC0, hC, ?_⟩
  intro M hM
  obtain ⟨hreg, hγ⟩ := h M hM
  refine ⟨hreg, ?_⟩
  intro gamma hgamma
  obtain ⟨Ls, htail, hae⟩ := hγ gamma hgamma
  have hb0 := aux_t_C_tail_tendsto C gamma M.delta hC
    (lt_of_le_of_lt hgamma.2 hreg.2) M.shellPrefix.delta_pos
    (by have := M.shellPrefix.delta_le_half; linarith)
  choose g hgm hgtail hgle using fun (L : WithTop ℕ) (m : ℕ) =>
    aux_t_C_measurable_majorant _ (Ls L m) _ (htail L m) hb0
  refine ⟨g, hgm, fun L m k hk => hgtail L m k hk, ?_⟩
  have hall : ∀ᵐ ω ∂(anchoredC11SampleLaw M (measurableSet_anchoredC11GoodSet d)
      (measure_anchoredC11GoodSet_eq_one M)).toMeasure,
      ∀ (L : WithTop ℕ) (m : ℕ), Ls L m ω ≤ g L m ω := by
    rw [ae_all_iff]
    intro L
    rw [ae_all_iff]
    intro m
    exact hgle L m
  filter_upwards [hae, hall] with ω hω hle
  refine ⟨?_, hω.2⟩
  intro L m hm u hu n hn z hz hsub
  refine hω.1 L m hm u hu n ?_ z hz hsub
  have := hle L m
  omega

end SubdiffusiveProcess.Paper
