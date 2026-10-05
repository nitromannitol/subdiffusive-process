module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.in_common_scale_coupling
public import SubdiffusiveProcess.Sobolev.GMCAnchoredOrlicz
public import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment
public import SubdiffusiveProcess.Probability.OrliczFiniteSum
public import SubdiffusiveProcess.Probability.OrliczExponentialMoment
public import SubdiffusiveProcess.Main.InfraredAdmissible

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter Metric TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper

noncomputable section

def aux_reference_oscillation_moments_Kball {d : ℕ}
    (x : SpatialCoordinates d) (r : ℝ) : Compacts (SpatialCoordinates d) :=
  ⟨closedBall x r, isCompact_closedBall x r⟩

def aux_reference_oscillation_moments_localA {d : ℕ}
    (y : SpatialCoordinates d) (r : ℝ) (f : C(SpatialCoordinates d, ℝ)) : ℝ :=
  ‖f.restrict
      (aux_reference_oscillation_moments_Kball y r : Set (SpatialCoordinates d)) -
    ContinuousMap.const (aux_reference_oscillation_moments_Kball y r) (f y)‖

def aux_reference_oscillation_moments_rootA {d : ℕ} (c : ℝ)
    (f : C(SpatialCoordinates d, ℝ)) : ℝ :=
  ‖(f.comp (⟨fun x : SpatialCoordinates d => c • x,
      (by fun_prop)⟩ : C(SpatialCoordinates d, SpatialCoordinates d))).restrict
        (aux_reference_oscillation_moments_Kball
          (0 : SpatialCoordinates d) (3 / 2 : ℝ) : Set (SpatialCoordinates d)) -
    ContinuousMap.const
      (aux_reference_oscillation_moments_Kball
        (0 : SpatialCoordinates d) (3 / 2 : ℝ)) (f 0)‖

def aux_reference_oscillation_moments_trans {d : ℕ}
    (z : SpatialCoordinates d) (f : C(SpatialCoordinates d, ℝ)) :
    C(SpatialCoordinates d, ℝ) :=
  f.comp (⟨fun x : SpatialCoordinates d => x + z,
    continuous_id.add continuous_const⟩ : C(SpatialCoordinates d, SpatialCoordinates d))

theorem aux_reference_oscillation_moments_geometry
    {d k j : ℕ} (hj : j < k) (y : SpatialCoordinates d)
    (f : C(SpatialCoordinates d, ℝ)) :
    aux_reference_oscillation_moments_localA y
        ((3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ)))
        (layerScaling d (-(j : ℤ)) f) ≤
      aux_reference_oscillation_moments_rootA
        ((3 : ℝ) ^ ((j : ℤ) - (k : ℤ)))
        (aux_reference_oscillation_moments_trans
          ((3 : ℝ) ^ (j : ℤ) • y) f) := by
  let r : ℝ := (3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))
  let c : ℝ := (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))
  let K := aux_reference_oscillation_moments_Kball y r
  let K0 := aux_reference_oscillation_moments_Kball
    (0 : SpatialCoordinates d) (3 / 2 : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    rw [show (j : ℤ) - (k : ℤ) = -((k : ℤ) - (j : ℤ)) by ring, zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ (by norm_num) (by omega))
  have hnorm : ∀ x : SpatialCoordinates d, x ∈ (K : Set (SpatialCoordinates d)) →
      (3 : ℝ) ^ (k : ℤ) • (x - y) ∈ (K0 : Set (SpatialCoordinates d)) := by
    intro x hx
    change x ∈ closedBall y r at hx
    change (3 : ℝ) ^ (k : ℤ) • (x - y) ∈ closedBall 0 (3 / 2 : ℝ)
    rw [mem_closedBall] at hx ⊢
    rw [dist_eq_norm] at hx ⊢
    have hx' : ‖x - y‖ ≤ r := by
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm] using hx
    simp only [sub_zero]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hpow : (3 : ℝ) ^ (k : ℤ) * r = 3 / 2 := by
      dsimp [r]
      calc
        (3 : ℝ) ^ (k : ℤ) * ((3 / 2 : ℝ) * 3 ^ (-(k : ℤ))) =
            (3 / 2 : ℝ) * ((3 : ℝ) ^ (k : ℤ) * 3 ^ (-(k : ℤ))) := by ring
        _ = 3 / 2 := by
          rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
          simp
    nlinarith [mul_le_mul_of_nonneg_left hx'
      (by positivity : 0 ≤ (3 : ℝ) ^ (k : ℤ))]
  have hrootnonneg : 0 ≤
      aux_reference_oscillation_moments_rootA c
        (aux_reference_oscillation_moments_trans
          ((3 : ℝ) ^ (j : ℤ) • y) f) := by
    unfold aux_reference_oscillation_moments_rootA
    exact norm_nonneg _
  have hnorm_le : ∀ x : SpatialCoordinates d, x ∈ (K : Set (SpatialCoordinates d)) →
      ‖(layerScaling d (-(j : ℤ)) f) x -
          (layerScaling d (-(j : ℤ)) f) y‖ ≤
        aux_reference_oscillation_moments_rootA c
          (aux_reference_oscillation_moments_trans
            ((3 : ℝ) ^ (j : ℤ) • y) f) := by
    intro x hx
    let u : SpatialCoordinates d := (3 : ℝ) ^ (k : ℤ) • (x - y)
    have hu : u ∈ (K0 : Set (SpatialCoordinates d)) := hnorm x hx
    have hpoint := ContinuousMap.norm_coe_le_norm
      (((aux_reference_oscillation_moments_trans
          ((3 : ℝ) ^ (j : ℤ) • y) f).comp
        (⟨fun v : SpatialCoordinates d => c • v,
          (by fun_prop)⟩ : C(SpatialCoordinates d, SpatialCoordinates d))).restrict
          (K0 : Set (SpatialCoordinates d)) -
        ContinuousMap.const K0
          (aux_reference_oscillation_moments_trans
            ((3 : ℝ) ^ (j : ℤ) • y) f 0)) ⟨u, hu⟩
    change ‖(aux_reference_oscillation_moments_trans
          ((3 : ℝ) ^ (j : ℤ) • y) f) (c • u) -
        (aux_reference_oscillation_moments_trans
          ((3 : ℝ) ^ (j : ℤ) • y) f) 0‖ ≤ _ at hpoint
    calc
      ‖(layerScaling d (-(j : ℤ)) f) x -
          (layerScaling d (-(j : ℤ)) f) y‖ =
          ‖f ((3 : ℝ) ^ (j : ℤ) • x) -
            f ((3 : ℝ) ^ (j : ℤ) • y)‖ := by
            congr 2
            · simp [layerScaling]
            · simp [layerScaling]
      _ = ‖f (c • u + (3 : ℝ) ^ (j : ℤ) • y) -
            f ((3 : ℝ) ^ (j : ℤ) • y)‖ := by
            congr 2
            dsimp [u, c]
            simp only [smul_sub, smul_smul]
            have hck : c * (3 : ℝ) ^ (k : ℤ) = (3 : ℝ) ^ (j : ℤ) := by
              dsimp [c]
              rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
              congr 1 ; omega
            rw [hck]
            rw [sub_add_cancel]
      _ = ‖(aux_reference_oscillation_moments_trans
          ((3 : ℝ) ^ (j : ℤ) • y) f) (c • u) -
            (aux_reference_oscillation_moments_trans
              ((3 : ℝ) ^ (j : ℤ) • y) f) 0‖ := by
            simp [aux_reference_oscillation_moments_trans]
      _ ≤ _ := hpoint
  have hnormK : ‖(layerScaling d (-(j : ℤ)) f).restrict (K : Set _) -
      ContinuousMap.const K ((layerScaling d (-(j : ℤ)) f) y)‖ ≤
      aux_reference_oscillation_moments_rootA c
        (aux_reference_oscillation_moments_trans
          ((3 : ℝ) ^ (j : ℤ) • y) f) := by
    apply (ContinuousMap.norm_le _ hrootnonneg).2
    intro x
    exact hnorm_le x x.property
  simpa [aux_reference_oscillation_moments_localA,
    aux_reference_oscillation_moments_rootA,
    aux_reference_oscillation_moments_trans, K, K0, r, c] using hnormK

theorem aux_reference_oscillation_moments_layer_exp
    {d : ℕ} (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ m : ℕ, 0 < m ∧ ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (y : SpatialCoordinates d) (k j : ℕ), j < k →
      let r : ℝ := (3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))
      let c : ℝ := (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))
      let P := (chaosSampleLaw M).toMeasure
      (∫⁻ omega, ENNReal.ofReal (Real.exp
        (((2 * aux_reference_oscillation_moments_localA y r
            (omega (-(j : ℤ)))) /
          (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2)) ∂P) ≤ 2 := by
  obtain ⟨m, hm, hmom⟩ :=
    exists_gmc_anchored_contraction_exp_square (d := d) (3 / 2 : ℝ) (by norm_num)
  refine ⟨m, hm, ?_⟩
  intro M y k j hj
  dsimp only
  let r : ℝ := (3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))
  let c : ℝ := (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))
  let K0 := aux_reference_oscillation_moments_Kball
    (0 : SpatialCoordinates d) (3 / 2 : ℝ)
  let ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) := chaosRootFieldLaw M
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun n => (scaledLayerLaw d ν n : Measure C(SpatialCoordinates d, ℝ))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    rw [show (j : ℤ) - (k : ℤ) = -((k : ℤ) - (j : ℤ)) by ring, zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ (by norm_num) (by omega))
  have hK0 : ∀ x ∈ (K0 : Set (SpatialCoordinates d)), ‖x‖ ≤ (3 / 2 : ℝ) := by
    intro x hx
    change x ∈ closedBall (0 : SpatialCoordinates d) (3 / 2 : ℝ) at hx
    simpa [mem_closedBall, dist_eq_norm] using hx
  have hroot := hmom M K0 hK0 c hc hc1
  dsimp only at hroot
  let T : C(SpatialCoordinates d, ℝ) → C(SpatialCoordinates d, ℝ) :=
    fun f => aux_reference_oscillation_moments_trans
      ((3 : ℝ) ^ (j : ℤ) • y) f
  let Φ : C(SpatialCoordinates d, ℝ) → ℝ≥0∞ := fun f =>
    ENNReal.ofReal (Real.exp
      ((aux_reference_oscillation_moments_rootA c (T f) /
        (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
  have hrootAcont : Continuous
      (aux_reference_oscillation_moments_rootA c :
        C(SpatialCoordinates d, ℝ) → ℝ) := by
    let dil : C(SpatialCoordinates d, SpatialCoordinates d) :=
      ⟨fun x => c • x, (by fun_prop)⟩
    have hc1 : Continuous (fun f : C(SpatialCoordinates d, ℝ) => f.comp dil) :=
      ContinuousMap.continuous_precomp dil
    have hc2 : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        (f.comp dil).restrict
          (aux_reference_oscillation_moments_Kball
            (0 : SpatialCoordinates d) (3 / 2 : ℝ) : Set (SpatialCoordinates d))) :=
      (ContinuousMap.continuous_restrict _).comp hc1
    have hc3 : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        ContinuousMap.const
          (aux_reference_oscillation_moments_Kball
            (0 : SpatialCoordinates d) (3 / 2 : ℝ)) (f 0)) :=
      ContinuousMap.continuous_const'.comp (continuous_eval_const 0)
    exact continuous_norm.comp (hc2.sub hc3)
  have hTcont : Continuous T := by
    dsimp [T, aux_reference_oscillation_moments_trans]
    exact ContinuousMap.continuous_precomp _
  have hΦ : Measurable Φ := by
    have hcΦ : Continuous Φ := by
      dsimp [Φ]
      apply ENNReal.continuous_ofReal.comp
      apply Real.continuous_exp.comp
      exact (((hrootAcont.comp hTcont).div_const _).pow 2)
    exact hcΦ.measurable
  have hstat : MeasurePreserving T (ν : Measure C(SpatialCoordinates d, ℝ))
      (ν : Measure C(SpatialCoordinates d, ℝ)) := by
    simpa [T, ν, aux_reference_oscillation_moments_trans,
      chaosRootFieldLaw] using
      (gmc_zero_field_law_stationary M ((3 : ℝ) ^ (j : ℤ) • y))
  have hrootT : (∫⁻ f, Φ f ∂(ν : Measure C(SpatialCoordinates d, ℝ))) ≤ 2 := by
    have hbase : Measurable (fun f : C(SpatialCoordinates d, ℝ) =>
        ENNReal.ofReal (Real.exp
          ((aux_reference_oscillation_moments_rootA c f /
            (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))) := by
      have hcbase : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
          ENNReal.ofReal (Real.exp
            ((aux_reference_oscillation_moments_rootA c f /
              (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))) := by
        apply ENNReal.continuous_ofReal.comp
        apply Real.continuous_exp.comp
        exact ((hrootAcont.div_const _).pow 2)
      exact hcbase.measurable
    calc
      (∫⁻ f, Φ f ∂(ν : Measure C(SpatialCoordinates d, ℝ))) =
          ∫⁻ f, ENNReal.ofReal (Real.exp
            ((aux_reference_oscillation_moments_rootA c f /
              (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
            ∂Measure.map T (ν : Measure C(SpatialCoordinates d, ℝ)) := by
              change (∫⁻ f, ENNReal.ofReal (Real.exp
                ((aux_reference_oscillation_moments_rootA c (T f) /
                  (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
                  ∂(ν : Measure _)) = _
              exact (lintegral_map hbase hstat.measurable).symm
      _ = ∫⁻ f, ENNReal.ofReal (Real.exp
            ((aux_reference_oscillation_moments_rootA c f /
              (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
            ∂(ν : Measure C(SpatialCoordinates d, ℝ)) := by rw [hstat.map_eq]
      _ ≤ 2 := by
        simpa [aux_reference_oscillation_moments_rootA, T,
          aux_reference_oscillation_moments_trans, K0, ν, chaosRootFieldLaw] using! hroot
  have hlocalAcont : Continuous
      (aux_reference_oscillation_moments_localA y r :
        C(SpatialCoordinates d, ℝ) → ℝ) := by
    have hc1 : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        f.restrict
          (aux_reference_oscillation_moments_Kball y r : Set (SpatialCoordinates d))) :=
      ContinuousMap.continuous_restrict _
    have hc2 : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        ContinuousMap.const
          (aux_reference_oscillation_moments_Kball y r) (f y)) :=
      ContinuousMap.continuous_const'.comp (continuous_eval_const y)
    exact continuous_norm.comp (hc1.sub hc2)
  have htarget : Measurable (fun f : C(SpatialCoordinates d, ℝ) =>
      ENNReal.ofReal (Real.exp
        ((2 * aux_reference_oscillation_moments_localA y r f /
          (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))) := by
    have hcTarget : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        ENNReal.ofReal (Real.exp
          ((2 * aux_reference_oscillation_moments_localA y r f /
            (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))) := by
      apply ENNReal.continuous_ofReal.comp
      apply Real.continuous_exp.comp
      exact (((continuous_const.mul hlocalAcont).div_const _).pow 2)
    exact hcTarget.measurable
  have hP : (chaosSampleLaw M).toMeasure = Measure.infinitePi laws := by
    rfl
  rw [hP]
  have heval := measurePreserving_eval_infinitePi laws (-(j : ℤ))
  calc
    (∫⁻ omega, ENNReal.ofReal (Real.exp
        ((2 * aux_reference_oscillation_moments_localA y r
            (omega (-(j : ℤ))) /
          (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
        ∂Measure.infinitePi laws) =
      ∫⁻ f, ENNReal.ofReal (Real.exp
        ((2 * aux_reference_oscillation_moments_localA y r f /
          (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
        ∂laws (-(j : ℤ)) := by
          exact heval.lintegral_comp htarget
    _ = ∫⁻ f, ENNReal.ofReal (Real.exp
        ((2 * aux_reference_oscillation_moments_localA y r
            (layerScaling d (-(j : ℤ)) f) /
          (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2))
        ∂(ν : Measure C(SpatialCoordinates d, ℝ)) := by
          dsimp [laws, scaledLayerLaw]
          exact (lintegral_map htarget
            (layerScaling d (-(j : ℤ))).continuous.measurable)
    _ ≤ ∫⁻ f, Φ f ∂(ν : Measure C(SpatialCoordinates d, ℝ)) := by
      apply lintegral_mono
      intro f
      apply ENNReal.ofReal_mono
      rw [Real.exp_le_exp]
      have hδ : 0 < M.delta := M.shellPrefix.delta_pos
      have hden : 0 < c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta) := by
        positivity
      have hleft0 : 0 ≤
          2 * aux_reference_oscillation_moments_localA y r
              ((layerScaling d (-(j : ℤ))) f) /
            (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) := by
        exact div_nonneg (mul_nonneg (by positivity) (norm_nonneg _)) (by positivity)
      have hright0 : 0 ≤
          aux_reference_oscillation_moments_rootA c (T f) /
            (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) := by
        exact div_nonneg (by
          unfold aux_reference_oscillation_moments_rootA
          exact norm_nonneg _) hden.le
      apply (sq_le_sq₀ hleft0 hright0).2
      calc
        2 * aux_reference_oscillation_moments_localA y r
              ((layerScaling d (-(j : ℤ))) f) /
              (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) =
            aux_reference_oscillation_moments_localA y r
              ((layerScaling d (-(j : ℤ))) f) /
              (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) := by
                field_simp
        _ ≤ aux_reference_oscillation_moments_rootA c (T f) /
              (c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) := by
                exact div_le_div_of_nonneg_right
                  (aux_reference_oscillation_moments_geometry hj y f) hden.le
    _ ≤ 2 := hrootT

end

theorem aux_reference_oscillation_moments_measurable_sup_open
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    [SecondCountableTopology E] {W : Set E} (hWopen : IsOpen W)
    {F : Ω → E → ℝ} (hcont : ∀ ω, Continuous (F ω))
    (hmeas : ∀ x : E, Measurable fun ω => F ω x)
    (hbdd : ∀ ω, BddAbove {r : ℝ | ∃ x ∈ W, r = F ω x}) :
    Measurable fun ω => sSup {r : ℝ | ∃ x ∈ W, r = F ω x} := by
  rcases Set.eq_empty_or_nonempty W with hW | hWne
  · subst hW
    simp
  · obtain ⟨Q, hQcount, hQdense⟩ := TopologicalSpace.exists_countable_dense E
    let D := W ∩ Q
    let : Countable D := (hQcount.mono Set.inter_subset_right).to_subtype
    refine Measurable.isLUB (f := fun i : D => fun ω => F ω i) (fun i => hmeas _) ?_
    intro ω
    have hne : {r : ℝ | ∃ x ∈ W, r = F ω x}.Nonempty := by
      obtain ⟨x, hx⟩ := hWne
      exact ⟨F ω x, x, hx, rfl⟩
    have hdense : W ⊆ closure D := by
      exact hQdense.open_subset_closure_inter hWopen
    constructor
    · rintro a ⟨i, rfl⟩
      exact le_csSup (hbdd ω) ⟨(i : E), i.property.1, rfl⟩
    · intro c hc
      refine csSup_le hne ?_
      rintro r ⟨x, hx, rfl⟩
      have hclosed : IsClosed {z : E | F ω z ≤ c} :=
        isClosed_le (hcont ω) continuous_const
      have hsub : D ⊆ {z : E | F ω z ≤ c} := by
        intro z hz
        exact hc ⟨⟨z, hz⟩, rfl⟩
      exact hclosed.closure_subset_iff.mpr hsub (hdense hx)

theorem aux_reference_oscillation_moments_sup_closed_eq_sup_open
    {E : Type*} [TopologicalSpace E] [SecondCountableTopology E]
    {U K : Set E} (hUsub : U ⊆ K) (hKsub : K ⊆ closure U)
    (hKne : K.Nonempty) {f : E → ℝ} (hf : Continuous f)
    (hAbdd : BddAbove {r : ℝ | ∃ x ∈ K, r = f x}) :
    sSup {r : ℝ | ∃ x ∈ K, r = f x} =
      sSup {r : ℝ | ∃ x ∈ U, r = f x} := by
  let A : Set ℝ := {r : ℝ | ∃ x ∈ K, r = f x}
  let B : Set ℝ := {r : ℝ | ∃ x ∈ U, r = f x}
  have hBdd : BddAbove B := hAbdd.mono (by
    rintro r ⟨x, hx, rfl⟩
    exact ⟨x, hUsub hx, rfl⟩)
  have hAne : A.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    exact ⟨f x, x, hx, rfl⟩
  have hUne : U.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    by_contra h
    have : U = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [this, closure_empty] at hKsub
    exact (hKsub hx).elim
  have hBne : B.Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    exact ⟨f x, x, hx, rfl⟩
  apply le_antisymm
  · refine csSup_le hAne ?_
    rintro r ⟨x, hx, rfl⟩
    have hclosed : IsClosed {z : E | f z ≤ sSup B} :=
      isClosed_le hf continuous_const
    have hsub : U ⊆ {z : E | f z ≤ sSup B} := by
      intro z hz
      exact le_csSup hBdd ⟨z, hz, rfl⟩
    exact hclosed.closure_subset_iff.mpr hsub (hKsub hx)
  · refine csSup_le hBne ?_
    rintro r ⟨x, hx, rfl⟩
    exact le_csSup hAbdd ⟨x, hUsub hx, rfl⟩

theorem aux_reference_oscillation_moments_integral_mono_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : f ≤ᵐ[μ] g) : (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ := by
  exact integral_mono_ae hf hg hfg

theorem aux_reference_oscillation_moments_integral_add_div_two
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, (f x + g x) / 2 ∂μ) =
      ((∫ x, f x ∂μ) + ∫ x, g x ∂μ) / 2 := by
  have heq : (fun x => (f x + g x) / 2) =
      (fun x => (1 / 2 : ℝ) * (f x + g x)) := by
    funext x
    ring
  rw [heq, integral_const_mul, integral_add hf hg]
  ring

theorem aux_reference_oscillation_moments_add_div_two_mono
    {a b c e : ℝ} (ha : a ≤ c) (hb : b ≤ e) :
    (a + b) / 2 ≤ (c + e) / 2 := by
  exact div_le_div_of_nonneg_right (add_le_add ha hb) (by norm_num)

theorem aux_reference_oscillation_moments_add_div_two_mono_self_right
    {a b c : ℝ} (ha : a ≤ c) (hb : b ≤ c) :
    (a + b) / 2 ≤ c := by
  calc
    (a + b) / 2 ≤ (c + c) / 2 :=
      aux_reference_oscillation_moments_add_div_two_mono ha hb
    _ = c := by ring

theorem aux_reference_oscillation_moments_add_div_two_self
    (a : ℝ) : (a + a) / 2 = a := by
  ring

theorem aux_reference_oscillation_moments_integral_add_div_two_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} {a b : ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfa : (∫ x, f x ∂μ) ≤ a) (hgb : (∫ x, g x ∂μ) ≤ b) :
    (∫ x, (f x + g x) / 2 ∂μ) ≤ (a + b) / 2 := by
  calc
    (∫ x, (f x + g x) / 2 ∂μ) =
        ((∫ x, f x ∂μ) + ∫ x, g x ∂μ) / 2 :=
      aux_reference_oscillation_moments_integral_add_div_two hf hg
    _ ≤ (a + b) / 2 :=
      aux_reference_oscillation_moments_add_div_two_mono hfa hgb

theorem aux_reference_oscillation_moments_integrable_add_div_two
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => (f x + g x) / 2) μ := by
  have hh := hf.add hg
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    hh.const_mul (1 / 2)

theorem aux_reference_oscillation_moments_integrable_of_norm_le
    {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → ℝ} {μ : Measure Ω}
    (hg : Integrable g μ) (hf : Measurable f)
    (hfg : ∀ x, ‖f x‖ ≤ g x) : Integrable f μ := by
  exact hg.mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hfg)

theorem aux_reference_oscillation_moments_measurable_exp_mul
    {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ} (c : ℝ)
    (hf : Measurable f) : Measurable (fun x => Real.exp (c * f x)) := by
  exact (measurable_const.mul hf).exp

theorem aux_reference_oscillation_moments_integrable_exp_of_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (c : ℝ) (hf : Measurable f) (hg : Integrable g μ)
    (hfg : ∀ x, Real.exp (c * f x) ≤ g x) :
    Integrable (fun x => Real.exp (c * f x)) μ := by
  apply aux_reference_oscillation_moments_integrable_of_norm_le hg
    (aux_reference_oscillation_moments_measurable_exp_mul c hf)
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hfg x

theorem aux_reference_oscillation_moments_norm_exp_le
    {x y : ℝ} (h : Real.exp x ≤ y) : ‖Real.exp x‖ ≤ y := by
  simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using h

theorem aux_reference_oscillation_moments_le_trans_four
    {a b c e f : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e)
    (hef : e ≤ f) : a ≤ f := by
  exact hab.trans (hbc.trans (hce.trans hef))

theorem aux_reference_oscillation_moments_le_trans_three
    {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : a ≤ d := by
  exact hab.trans (hbc.trans hcd)

theorem aux_reference_oscillation_moments_exp_add_le_avg
    (a b : ℝ) : Real.exp (a + b) ≤
      (Real.exp (2 * a) + Real.exp (2 * b)) / 2 := by
  rw [Real.exp_add]
  have hEa : Real.exp (2 * a) = (Real.exp a) ^ 2 := by
    rw [show 2 * a = a + a by ring, Real.exp_add]
    ring
  have hEb : Real.exp (2 * b) = (Real.exp b) ^ 2 := by
    rw [show 2 * b = b + b by ring, Real.exp_add]
    ring
  rw [hEa, hEb]
  have hs : 0 ≤ (Real.exp a) ^ 2 + (Real.exp b) ^ 2 -
      2 * (Real.exp a * Real.exp b) := by
    calc
      0 ≤ (Real.exp a - Real.exp b) ^ 2 := sq_nonneg _
      _ = (Real.exp a) ^ 2 + (Real.exp b) ^ 2 -
          2 * (Real.exp a * Real.exp b) := by ring
  linarith

theorem aux_reference_oscillation_moments_exp_scaled_eq
    (q a b : ℝ) :
    (Real.exp (2 * ((2 * q) * (2 * a))) + Real.exp (2 * ((2 * q) * b))) / 2 =
      (Real.exp ((4 * (2 * q)) * a) +
        Real.exp ((2 * (2 * q)) * b)) / 2 := by
  congr 1 ; ring

theorem aux_reference_oscillation_moments_exp_scaled_amgm
    (q a b : ℝ) :
    Real.exp ((2 * q) * (2 * a + b)) ≤
      (Real.exp ((4 * (2 * q)) * a) +
        Real.exp ((2 * (2 * q)) * b)) / 2 := by
  calc
    Real.exp ((2 * q) * (2 * a + b)) =
        Real.exp ((2 * q) * (2 * a) + (2 * q) * b) := by
          congr 1 ; ring
    _ ≤ (Real.exp (2 * ((2 * q) * (2 * a))) +
        Real.exp (2 * ((2 * q) * b))) / 2 :=
      aux_reference_oscillation_moments_exp_add_le_avg
        ((2 * q) * (2 * a)) ((2 * q) * b)
    _ = (Real.exp ((4 * (2 * q)) * a) +
        Real.exp ((2 * (2 * q)) * b)) / 2 :=
      aux_reference_oscillation_moments_exp_scaled_eq q a b

theorem aux_reference_oscillation_moments_exp_osc_envelope
    (q o a b : ℝ) (ho : o ≤ 2 * a + b) (hq : 0 ≤ 2 * q) :
    Real.exp ((2 * q) * o) ≤
      (Real.exp ((4 * (2 * q)) * a) +
        Real.exp ((2 * (2 * q)) * b)) / 2 := by
  calc
    Real.exp ((2 * q) * o) ≤ Real.exp ((2 * q) * (2 * a + b)) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ho hq)
    _ ≤ (Real.exp ((4 * (2 * q)) * a) +
        Real.exp ((2 * (2 * q)) * b)) / 2 :=
      aux_reference_oscillation_moments_exp_scaled_amgm q a b

theorem aux_reference_oscillation_moments_exp_le_exp_add
    (a b : ℝ) (hb : 0 ≤ b) : 2 * Real.exp a ≤ 2 * Real.exp (a + b) := by
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  linarith

theorem aux_reference_oscillation_moments_integral_add_div_two_exp_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} {a b e : ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfa : (∫ x, f x ∂μ) ≤ 2 * Real.exp a)
    (hgb : (∫ x, g x ∂μ) ≤ 2 * Real.exp b)
    (he : e = a + b) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ x, (f x + g x) / 2 ∂μ) ≤ 2 * Real.exp e := by
  rw [he]
  calc
    (∫ x, (f x + g x) / 2 ∂μ) ≤
        (2 * Real.exp a + 2 * Real.exp b) / 2 :=
      aux_reference_oscillation_moments_integral_add_div_two_le
        hf hg hfa hgb
    _ ≤ (2 * Real.exp (a + b) + 2 * Real.exp (a + b)) / 2 :=
      aux_reference_oscillation_moments_add_div_two_mono
        (aux_reference_oscillation_moments_exp_le_exp_add a b hb)
        (by simpa [add_comm] using
          aux_reference_oscillation_moments_exp_le_exp_add b a ha)
    _ = 2 * Real.exp (a + b) := by ring

def aux_reference_oscillation_moments_HmomP (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Pd : _root_.SubdiffusiveProcess.Model.GMCModel d → (BilateralField d → C(SpatialCoordinates d, ℝ)) → Prop)
    (CH : Compacts (SpatialCoordinates d) → ℝ) : Prop :=
  ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_hH : Pd M H)
    (K : Compacts (SpatialCoordinates d)) (lambda : ℝ), 0 ≤ lambda →
      Integrable (fun omega => Real.exp
        (lambda * ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖))
        (chaosSampleLaw M).toMeasure ∧
      (∫ omega, Real.exp
        (lambda * ‖(H omega).restrict (K : Set (SpatialCoordinates d))‖)
        ∂(chaosSampleLaw M).toMeasure) ≤
        2 * Real.exp (CH K * lambda ^ 2 * M.delta ^ 2)

def aux_reference_oscillation_moments_Hmom (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (CH : Compacts (SpatialCoordinates d) → ℝ) : Prop :=
  aux_reference_oscillation_moments_HmomP d
    (fun M H => InfraredCharacterization M H) CH

def aux_reference_oscillation_moments_Layer (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (m : ℕ) : Prop :=
  ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (y : SpatialCoordinates d) (k j : ℕ), j < k →
    let r : ℝ := (3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ))
    let c : ℝ := (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))
    let P := (chaosSampleLaw M).toMeasure
    (∫⁻ omega, ENNReal.ofReal (Real.exp
      (((2 * aux_reference_oscillation_moments_localA y r
          (omega (-(j : ℤ)))) /
        (2 * c * (3 / 2 : ℝ) * ((m : ℝ) * M.delta))) ^ 2)) ∂P) ≤ 2

theorem aux_reference_oscillation_moments_final
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (q : ℝ) (hq : 1 ≤ q) (O YH S : Ω → ℝ) (a b E Cosc : ℝ)
    (hOmeas : Measurable O)
    (hOexp_int : Integrable (fun omega => Real.exp ((2 * q) * O omega)) P)
    (hHint : Integrable (fun omega => Real.exp ((4 * (2 * q)) * YH omega)) P)
    (hSint : Integrable (fun omega => Real.exp ((2 * (2 * q)) * S omega)) P)
    (hHbound :
      (∫ omega, Real.exp ((4 * (2 * q)) * YH omega) ∂P) ≤
        2 * Real.exp a)
    (hSbound :
      (∫ omega, Real.exp ((2 * (2 * q)) * S omega) ∂P) ≤
        2 * Real.exp b)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hO_le : ∀ omega, O omega ≤ 2 * YH omega + S omega)
    (hE : E = a + b) (hCosc : Cosc = (2 * Real.exp E) ^ (1 / (2 * q))) :
    MemLp (fun omega => Real.exp (O omega))
        (ENNReal.ofReal (2 * q)) P ∧
      eLpNorm (fun omega => Real.exp (O omega))
        (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc := by
  have hdom : Integrable
      (fun omega =>
        (Real.exp ((4 * (2 * q)) * YH omega) +
          Real.exp ((2 * (2 * q)) * S omega)) / 2) P :=
    aux_reference_oscillation_moments_integrable_add_div_two
      hHint hSint
  have hpoint : ∀ omega,
      Real.exp ((2 * q) * O omega) ≤
        (Real.exp ((4 * (2 * q)) * YH omega) +
          Real.exp ((2 * (2 * q)) * S omega)) / 2 := by
    intro omega
    exact aux_reference_oscillation_moments_exp_osc_envelope q
      (O omega) (YH omega) (S omega) (hO_le omega) (by positivity)
  have hmono_ae :
      (fun omega => Real.exp ((2 * q) * O omega)) ≤ᵐ[P]
        (fun omega =>
          (Real.exp ((4 * (2 * q)) * YH omega) +
            Real.exp ((2 * (2 * q)) * S omega)) / 2) :=
    Filter.Eventually.of_forall hpoint
  have hIntMono :
      (∫ omega, Real.exp ((2 * q) * O omega) ∂P) ≤
        ∫ omega, (Real.exp ((4 * (2 * q)) * YH omega) +
          Real.exp ((2 * (2 * q)) * S omega)) / 2 ∂P :=
    aux_reference_oscillation_moments_integral_mono_ae
      hOexp_int hdom hmono_ae
  have hAvgToE :
      (∫ omega, (Real.exp ((4 * (2 * q)) * YH omega) +
        Real.exp ((2 * (2 * q)) * S omega)) / 2 ∂P) ≤
        2 * Real.exp E := by
    exact aux_reference_oscillation_moments_integral_add_div_two_exp_le
      (μ := P)
      (f := fun omega => Real.exp ((4 * (2 * q)) * YH omega))
      (g := fun omega => Real.exp ((2 * (2 * q)) * S omega))
      (a := a) (b := b) (e := E) hHint hSint hHbound hSbound hE ha hb
  have hOexp_bound :
      (∫ omega, Real.exp ((2 * q) * O omega) ∂P) ≤ 2 * Real.exp E :=
    hIntMono.trans hAvgToE
  have hconvert :
      MemLp (fun omega => Real.exp (O omega))
          (ENNReal.ofReal (2 * q)) P ∧
        eLpNorm (fun omega => Real.exp (O omega))
          (ENNReal.ofReal (2 * q)) P ≤
          ENNReal.ofReal ((2 * Real.exp E) ^ (1 / (2 * q))) := by
    have hp : 0 < 2 * q := by linarith
    have hp0 : ENNReal.ofReal (2 * q) ≠ 0 :=
      (ENNReal.ofReal_eq_zero.not).2 (not_le.mpr hp)
    have hptop : ENNReal.ofReal (2 * q) ≠ ∞ := ENNReal.ofReal_ne_top
    have heq : ∀ omega, ‖Real.exp (O omega)‖ ^
        (ENNReal.ofReal (2 * q)).toReal =
          Real.exp ((2 * q) * O omega) := by
      intro omega
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ENNReal.toReal_ofReal hp.le]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    have hpow : Integrable (fun omega =>
        ‖Real.exp (O omega)‖ ^ (ENNReal.ofReal (2 * q)).toReal) P := by
      simpa only [heq] using hOexp_int
    have hexpm : Measurable (fun omega => Real.exp (O omega)) := hOmeas.exp
    have hmem :=
      (integrable_norm_rpow_iff hexpm.aestronglyMeasurable hp0 hptop).mp hpow
    refine ⟨hmem, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hexpm.aestronglyMeasurable]
    have hlin :
        ∫⁻ omega, ‖Real.exp (O omega)‖ₑ ^
            (ENNReal.ofReal (2 * q)).toReal ∂P =
          ENNReal.ofReal (∫ omega, Real.exp ((2 * q) * O omega) ∂P) := by
      rw [ofReal_integral_eq_lintegral_ofReal hOexp_int
        (Filter.Eventually.of_forall fun omega => (Real.exp_pos _).le)]
      apply lintegral_congr_ae
      filter_upwards [] with omega
      rw [← ofReal_norm]
      rw [ENNReal.ofReal_rpow_of_nonneg
        (norm_nonneg (Real.exp (O omega)))
        ENNReal.toReal_nonneg]
      rw [heq]
    rw [hlin]
    calc
      (ENNReal.ofReal
        (∫ omega, Real.exp ((2 * q) * O omega) ∂P)) ^
          (1 / (ENNReal.ofReal (2 * q)).toReal) ≤
          (ENNReal.ofReal (2 * Real.exp E)) ^ (1 / (2 * q)) := by
            rw [ENNReal.toReal_ofReal hp.le]
            exact ENNReal.rpow_le_rpow
              ((ENNReal.ofReal_le_ofReal_iff (by positivity)).2 hOexp_bound)
              (by positivity)
      _ = ENNReal.ofReal ((2 * Real.exp E) ^ (1 / (2 * q))) := by
            rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  rw [hCosc]
  exact hconvert



theorem aux_reference_oscillation_moments_sup_measurable
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hHmeas : Measurable H) (k : ℕ)
    (y : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    Measurable (fun omega : BilateralField d =>
      sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r,
          v = |(H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
            (H omega x' + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x')|}) := by
  let g : BilateralField d → SpatialCoordinates d → ℝ :=
    fun omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
  let U : Set (SpatialCoordinates d × SpatialCoordinates d) :=
    Metric.ball y r ×ˢ Metric.ball y r
  let Kpair : Set (SpatialCoordinates d × SpatialCoordinates d) :=
    Metric.closedBall y r ×ˢ Metric.closedBall y r
  let F : BilateralField d → SpatialCoordinates d × SpatialCoordinates d → ℝ :=
    fun omega z => |g omega z.1 - g omega z.2|
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_ball.prod isOpen_ball
  have hUsub : U ⊆ Kpair := by
    intro z hz
    exact ⟨mem_ball.mp hz.1 |>.le, mem_ball.mp hz.2 |>.le⟩
  have hKsub : Kpair ⊆ closure U := by
    intro z hz
    change z ∈ closure (Metric.ball y r ×ˢ Metric.ball y r)
    rw [closure_prod_eq, closure_ball y hr.ne']
    exact ⟨hz.1, hz.2⟩
  have hKne : Kpair.Nonempty := by
    exact ⟨(y, y), ⟨Metric.mem_closedBall_self hr.le, Metric.mem_closedBall_self hr.le⟩⟩
  have hFcont : ∀ omega, Continuous (F omega) := by
    intro omega
    have hsum : Continuous (fun x : SpatialCoordinates d =>
        ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) :=
      continuous_finsetSum (Finset.range k) (by
        intro j hj
        exact (omega (-(j : ℤ))).continuous)
    have hg : Continuous (g omega) := by
      dsimp [g]
      exact (H omega).continuous.add hsum
    exact continuous_abs.comp ((hg.comp continuous_fst).sub (hg.comp continuous_snd))
  have hFmeas : ∀ z : SpatialCoordinates d × SpatialCoordinates d,
      Measurable (fun omega => F omega z) := by
    intro z
    have hH1 : Measurable (fun omega => H omega z.1) :=
      (continuous_eval_const z.1).measurable.comp hHmeas
    have hH2 : Measurable (fun omega => H omega z.2) :=
      (continuous_eval_const z.2).measurable.comp hHmeas
    have hsum1 : Measurable (fun omega : BilateralField d =>
        ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) z.1) :=
      Finset.measurable_sum (Finset.range k) (by
        intro j hj
        have heval : Measurable (fun omega : BilateralField d =>
            omega (-(j : ℤ))) := measurable_pi_apply _
        simpa only [Function.comp_def, Pi.mul_apply] using!
          ((continuous_eval_const z.1).measurable.comp heval))
    have hsum2 : Measurable (fun omega : BilateralField d =>
        ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) z.2) :=
      Finset.measurable_sum (Finset.range k) (by
        intro j hj
        have heval : Measurable (fun omega : BilateralField d =>
            omega (-(j : ℤ))) := measurable_pi_apply _
        simpa only [Function.comp_def, Pi.mul_apply] using!
          ((continuous_eval_const z.2).measurable.comp heval))
    have hsub : Measurable (fun omega => g omega z.1 - g omega z.2) := by
      exact (hH1.add hsum1).sub (hH2.add hsum2)
    exact measurable_norm.comp hsub
  have hAbdd : ∀ omega, BddAbove {v : ℝ | ∃ z ∈ Kpair, v = F omega z} := by
    intro omega
    have hcompact : IsCompact Kpair := by
      dsimp [Kpair]
      exact (isCompact_closedBall y r).prod (isCompact_closedBall y r)
    have himage := hcompact.bddAbove_image (hFcont omega).continuousOn
    apply himage.mono
    rintro v ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  have hSupOpen : Measurable (fun omega =>
      sSup {v : ℝ | ∃ z ∈ U, v = F omega z}) :=
    aux_reference_oscillation_moments_measurable_sup_open
      hUopen hFcont hFmeas (by
        intro omega
        have himage := hAbdd omega
        exact himage.mono (by
          rintro v ⟨z, hz, rfl⟩
          exact ⟨z, hUsub hz, rfl⟩))
  have hSupMeas : Measurable (fun omega =>
      sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r, v = F omega (x, x')}) := by
    have heq : (fun omega => sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r, v = F omega (x, x')}) =
        (fun omega => sSup {v : ℝ | ∃ z ∈ U, v = F omega z}) := by
      funext omega
      calc
        sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
            ∃ x' ∈ Metric.closedBall y r, v = F omega (x, x')} =
            sSup {v : ℝ | ∃ z ∈ Kpair, v = F omega z} := by
              apply congrArg sSup
              ext v
              constructor
              · rintro ⟨x, hx, x', hx', hv⟩
                exact ⟨(x, x'), ⟨hx, hx'⟩, hv⟩
              · rintro ⟨z, hz, hv⟩
                exact ⟨z.1, hz.1, z.2, hz.2, hv⟩
        _ = sSup {v : ℝ | ∃ z ∈ U, v = F omega z} :=
          aux_reference_oscillation_moments_sup_closed_eq_sup_open
            hUsub hKsub hKne (hFcont omega) (hAbdd omega)
    rw [heq]
    exact hSupOpen
  exact hSupMeas

theorem aux_reference_oscillation_moments_point
    (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q)
    (Pd : _root_.SubdiffusiveProcess.Model.GMCModel d → (BilateralField d → C(SpatialCoordinates d, ℝ)) → Prop)
    (hPmeas : ∀ M H, Pd M H → Measurable H)
    (CH : Compacts (SpatialCoordinates d) → ℝ)
    (hCH : ∀ K, 0 ≤ CH K)
    (hHmom : aux_reference_oscillation_moments_HmomP d Pd CH)
    (m : ℕ) (hm : 0 < m)
    (hLayer : aux_reference_oscillation_moments_Layer d m)
    (Kbig : Compacts (SpatialCoordinates d))
    (E Cosc : ℝ)
    (hKbig_def : Kbig =
      aux_reference_oscillation_moments_Kball
        (0 : SpatialCoordinates d) (3 : ℝ))
    (hE : E = CH Kbig * (4 * (2 * q)) ^ 2 +
      (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2)
    (hCosc : Cosc = (2 * Real.exp E) ^ (1 / (2 * q)))
        (delta0 : ℝ) (_hdelta0 : 0 < delta0) (hdelta1 : delta0 ≤ 1)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : Pd M H) (hM : M.delta ≤ delta0)
    (k : ℕ) (y : SpatialCoordinates d)
    (hy : y ∈ {x : SpatialCoordinates d | ∀ i, 0 ≤ x i ∧ x i ≤ 1}) :
      let P := (chaosSampleLaw M).toMeasure
    let r : ℝ := (3 : ℝ) * ((3 : ℝ) ^ (-(k : ℤ)) / 2)
    let g : BilateralField d → SpatialCoordinates d → ℝ :=
      fun omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
    let O : BilateralField d → ℝ := fun omega =>
      sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r, v = |g omega x - g omega x'|}
    MemLp (fun omega => Real.exp (O omega))
        (ENNReal.ofReal (2 * q)) P ∧
      eLpNorm (fun omega => Real.exp (O omega))
        (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc := by
  classical
  dsimp only
  let r : ℝ := (3 : ℝ) * ((3 : ℝ) ^ (-(k : ℤ)) / 2)
  let g : BilateralField d → SpatialCoordinates d → ℝ :=
    fun omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
  let U : Set (SpatialCoordinates d × SpatialCoordinates d) :=
    Metric.ball y r ×ˢ Metric.ball y r
  let Kpair : Set (SpatialCoordinates d × SpatialCoordinates d) :=
    Metric.closedBall y r ×ˢ Metric.closedBall y r
  let F : BilateralField d → SpatialCoordinates d × SpatialCoordinates d → ℝ :=
    fun omega z => |g omega z.1 - g omega z.2|
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hSupMeas : Measurable (fun omega =>
      sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r, v = F omega (x, x')}) :=
    aux_reference_oscillation_moments_sup_measurable d H (hPmeas M H hH) k y r hr
  let O : BilateralField d → ℝ := fun omega =>
    sSup {v : ℝ | ∃ x ∈ Metric.closedBall y r,
      ∃ x' ∈ Metric.closedBall y r, v = F omega (x, x')}
  have hOmeas : Measurable O := by
    exact hSupMeas
  have hr_le : (3 : ℝ) ^ (-(k : ℤ)) ≤ 1 := by
    rw [zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ (by norm_num) (by omega))
  have hy_norm : ‖y‖ ≤ 1 := by
    have hy' : ∀ i : Fin d, 0 ≤ y i ∧ y i ≤ 1 := by
      simpa using hy
    rw [Pi.norm_def]
    have hsup : (Finset.univ.sup fun b : Fin d => ‖y b‖₊) ≤ (1 : ℝ≥0) := by
      apply Finset.sup_le
      intro i hi
      apply NNReal.coe_le_coe.mp
      simpa [Real.norm_eq_abs, abs_of_nonneg (hy' i).1] using (hy' i).2
    exact_mod_cast hsup
  have hKbig : ∀ x ∈ Metric.closedBall y r,
      x ∈ (Kbig : Set (SpatialCoordinates d)) := by
    intro x hx
    rw [hKbig_def]
    change x ∈ Metric.closedBall (0 : SpatialCoordinates d) 3
    rw [mem_closedBall, dist_eq_norm]
    have hx' : ‖x - y‖ ≤ r := by
      simpa [mem_closedBall, dist_eq_norm, sub_eq_add_neg, add_comm] using hx
    have hr_le' : r ≤ 3 / 2 := by
      dsimp [r]
      calc
        3 * (3 ^ (-(k : ℤ)) / 2) ≤ 3 * ((1 : ℝ) / 2) := by
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hr_le (by norm_num)) (by norm_num)
        _ = 3 / 2 := by ring
    have hxy : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
      simpa only [sub_add_cancel] using (norm_add_le (x - y) y)
    have : ‖x‖ ≤ (3 / 2 : ℝ) + 1 := hxy.trans
      (add_le_add (hx'.trans hr_le') hy_norm)
    have hx3 : ‖x‖ ≤ 3 := by nlinarith
    simpa only [sub_zero] using hx3
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let X : ℕ → BilateralField d → ℝ := fun j omega =>
    2 * aux_reference_oscillation_moments_localA y r (omega (-(j : ℤ)))
  let A : ℕ → ℝ := fun j =>
    2 * (3 : ℝ) ^ ((j : ℤ) - (k : ℤ)) * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)
  let S : BilateralField d → ℝ := fun omega => ∑ j ∈ Finset.range k, X j omega
  have hlocalAcont : Continuous
      (aux_reference_oscillation_moments_localA y r :
        C(SpatialCoordinates d, ℝ) → ℝ) := by
    have hc1 : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        f.restrict
          (aux_reference_oscillation_moments_Kball y r : Set (SpatialCoordinates d))) :=
      ContinuousMap.continuous_restrict _
    have hc2 : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        ContinuousMap.const
          (aux_reference_oscillation_moments_Kball y r) (f y)) :=
      ContinuousMap.continuous_const'.comp (continuous_eval_const y)
    exact continuous_norm.comp (hc1.sub hc2)
  have hXmeas : ∀ j, Measurable (X j) := by
    intro j
    dsimp [X]
    have heval : Measurable (fun omega : BilateralField d => omega (-(j : ℤ))) :=
      measurable_pi_apply _
    simpa only [Function.comp_def, Pi.mul_apply] using!
      (measurable_const.mul (hlocalAcont.measurable.comp heval))
  have hX0 : ∀ j omega, 0 ≤ X j omega := by
    intro j omega
    dsimp [X, aux_reference_oscillation_moments_localA]
    positivity
  have hA : ∀ j, 0 < A j := by
    intro j
    dsimp [A]
    have hδ : 0 < M.delta := M.shellPrefix.delta_pos
    positivity
  have hXexp : ∀ j, j < k →
      (∫⁻ omega, ENNReal.ofReal (Real.exp ((X j omega / A j) ^ 2)) ∂P) ≤ 2 := by
    intro j hj
    have hh := hLayer M y k j hj
    dsimp only at hh
    have hr_eq : r = (3 / 2 : ℝ) * (3 : ℝ) ^ (-(k : ℤ)) := by
      dsimp [r]
      ring
    simpa [P, X, A, hr_eq] using hh
  have hSmeas : Measurable S := by
    dsimp [S]
    exact Finset.measurable_sum (Finset.range k) (by
      intro j hj
      exact hXmeas j)
  have hS0 : ∀ omega, 0 ≤ S omega := by
    intro omega
    dsimp [S]
    exact Finset.sum_nonneg (fun j hj => hX0 j omega)
  have hsumc : (∑ j ∈ Finset.range k, (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))) ≤ 1 / 2 := by
    have hsum : (∑ j ∈ Finset.range k, (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))) =
        (1 - 3 ^ (-(k : ℤ))) / 2 := by
      calc
        (∑ j ∈ Finset.range k, (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))) =
            (∑ j ∈ Finset.range k, 3 ^ (j : ℤ)) * 3 ^ (-(k : ℤ)) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j hj
              rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
              congr 1
        _ = (1 - 3 ^ (-(k : ℤ))) / 2 := by
              have hg := geom_sum_mul (3 : ℝ) k
              have hz : (∑ j ∈ Finset.range k, (3 : ℝ) ^ (j : ℤ)) =
                  ∑ j ∈ Finset.range k, (3 : ℝ) ^ j := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [zpow_natCast (3 : ℝ) j]
              rw [hz]
              rw [zpow_neg, zpow_natCast]
              field_simp [show (3 : ℝ) ^ k ≠ 0 by positivity]
              nlinarith [hg]
    rw [hsum]
    have hpos : 0 < (3 : ℝ) ^ (-(k : ℤ)) := by positivity
    linarith
  have hAsum_eq : (∑ j ∈ Finset.range k, A j) =
      (2 * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) *
        (∑ j ∈ Finset.range k, (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))) := by
    dsimp [A]
    calc
      (∑ j ∈ Finset.range k,
          2 * (3 : ℝ) ^ ((j : ℤ) - (k : ℤ)) * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) =
          ∑ j ∈ Finset.range k,
            (2 * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) *
              (3 : ℝ) ^ ((j : ℤ) - (k : ℤ)) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
      _ = (2 * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) *
          (∑ j ∈ Finset.range k, (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))) := by
            rw [Finset.mul_sum]
  have hAsum_bound : (∑ j ∈ Finset.range k, A j) ≤
      (3 / 2 : ℝ) * ((m : ℝ) * M.delta) := by
    rw [hAsum_eq]
    calc
      (2 * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) *
          (∑ j ∈ Finset.range k, (3 : ℝ) ^ ((j : ℤ) - (k : ℤ))) ≤
          (2 * (3 / 2 : ℝ) * ((m : ℝ) * M.delta)) * (1 / 2 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hsumc (by
              have hδ : 0 < M.delta := M.shellPrefix.delta_pos
              positivity)
      _ = (3 / 2 : ℝ) * ((m : ℝ) * M.delta) := by ring
  have hAsum_bound' : (∑ j ∈ Finset.range k, A j) ≤
      (3 / 2 : ℝ) * (m : ℝ) := by
    have hδle1' : M.delta ≤ 1 := hM.trans hdelta1
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    have hmd : (m : ℝ) * M.delta ≤ (m : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hδle1' hm0
    have hmd' : (3 / 2 : ℝ) * ((m : ℝ) * M.delta) ≤
        (3 / 2 : ℝ) * ((m : ℝ) * 1) :=
      mul_le_mul_of_nonneg_left hmd (by norm_num)
    calc
      (∑ j ∈ Finset.range k, A j) ≤
          (3 / 2 : ℝ) * ((m : ℝ) * M.delta) := hAsum_bound
      _ ≤ (3 / 2 : ℝ) * (m : ℝ) := by simpa only [mul_one] using hmd'
  have hSlin :
      Integrable (fun omega => Real.exp ((2 * (2 * q)) * S omega)) P ∧
        (∫ omega, Real.exp ((2 * (2 * q)) * S omega) ∂P) ≤
          2 * Real.exp ((((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2) := by
    by_cases hk : k = 0
    · subst k
      refine ⟨?_, ?_⟩
      · simp [S]
      · simp [S]
        nlinarith [Real.one_le_exp (by positivity :
          0 ≤ ((3 / 2 : ℝ) * (m : ℝ) * (2 * q)) ^ 2)]
    · have hkne : (Finset.range k).Nonempty := by
        exact ⟨0, by simp; omega⟩
      have hOr := lintegral_exp_sq_finset_sum_le P (Finset.range k) X A hkne
        (by intro j hj; exact (hXmeas j).aestronglyMeasurable)
        (by intro j hj; exact Filter.Eventually.of_forall (fun omega => hX0 j omega))
        (by intro j hj; exact hA j)
        (by intro j hj; exact hXexp j (Finset.mem_range.mp hj))
      have hraw := orlicz_exp_linear_integrable_integral_le P S
        (∑ j ∈ Finset.range k, A j) (2 * (2 * q)) hSmeas hS0
        (Finset.sum_pos (fun j hj => hA j) hkne) (by positivity) hOr
      refine ⟨hraw.1, ?_⟩
      have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.range k, A j := by
        exact Finset.sum_nonneg (fun j hj => (hA j).le)
      have hqpos : 0 ≤ 2 * q := by positivity
      have hprod :
          (∑ j ∈ Finset.range k, A j) * (2 * q) ≤
            ((3 / 2 : ℝ) * (m : ℝ)) * (2 * q) :=
        mul_le_mul_of_nonneg_right hAsum_bound' hqpos
      calc
        (∫ omega, Real.exp ((2 * (2 * q)) * S omega) ∂P) ≤
            2 * Real.exp
              ((∑ j ∈ Finset.range k, A j) ^ 2 * (2 * (2 * q)) ^ 2 / 4) := by
                simpa using hraw.2
        _ ≤ 2 * Real.exp
              ((((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2) := by
                apply mul_le_mul_of_nonneg_left
                  (Real.exp_le_exp.mpr ?_) (by positivity)
                calc
                  (∑ j ∈ Finset.range k, A j) ^ 2 * (2 * (2 * q)) ^ 2 / 4 =
                      ((∑ j ∈ Finset.range k, A j) * (2 * q)) ^ 2 := by ring
                  _ ≤ (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2 := by
                    have htarget0 : 0 ≤
                        ((3 / 2 : ℝ) * (m : ℝ)) * (2 * q) := by
                      have hm0 : 0 ≤ (m : ℝ) := by positivity
                      exact mul_nonneg
                        (mul_nonneg (by norm_num) hm0) hqpos
                    exact (sq_le_sq₀ (mul_nonneg hsum_nonneg hqpos) htarget0).2 hprod
  let YH : BilateralField d → ℝ := fun omega =>
    ‖(H omega).restrict (Kbig : Set (SpatialCoordinates d))‖
  let U : BilateralField d → ℝ := fun omega =>
    Real.exp ((2 * q) * O omega)
  have hU : U = fun omega => Real.exp ((2 * q) * O omega) := by
    rfl
  let V : BilateralField d → ℝ := fun omega =>
    (Real.exp ((4 * (2 * q)) * YH omega) +
      Real.exp ((2 * (2 * q)) * S omega)) / 2
  have hV : V = fun omega =>
      (Real.exp ((4 * (2 * q)) * YH omega) +
        Real.exp ((2 * (2 * q)) * S omega)) / 2 := by
    rfl
  have hYHmeas : Measurable YH := by
    have hcont : Continuous (fun f : C(SpatialCoordinates d, ℝ) =>
        ‖f.restrict (Kbig : Set (SpatialCoordinates d))‖) :=
      continuous_norm.comp (ContinuousMap.continuous_restrict _)
    simpa only [YH, Function.comp_def] using! hcont.measurable.comp (hPmeas M H hH)
  have hHraw := hHmom M H hH Kbig (4 * (2 * q)) (by positivity)
  have hHint : Integrable (fun omega => Real.exp ((4 * (2 * q)) * YH omega)) P := by
    simpa [P, YH] using hHraw.1
  have hδle1 : M.delta ≤ 1 := hM.trans hdelta1
  have hδsq : M.delta ^ 2 ≤ 1 := by
    have hδ0 : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
    have hh := mul_self_le_mul_self hδ0 hδle1
    simpa [pow_two] using hh
  have hHbound :
      (∫ omega, Real.exp ((4 * (2 * q)) * YH omega) ∂P) ≤
        2 * Real.exp (CH Kbig * (4 * (2 * q)) ^ 2) := by
    have hcoef : 0 ≤ CH Kbig * (4 * (2 * q)) ^ 2 := by
      exact mul_nonneg (hCH Kbig) (sq_nonneg _)
    have hexp : CH Kbig * (4 * (2 * q)) ^ 2 * M.delta ^ 2 ≤
        CH Kbig * (4 * (2 * q)) ^ 2 := by
      calc
        CH Kbig * (4 * (2 * q)) ^ 2 * M.delta ^ 2 ≤
            CH Kbig * (4 * (2 * q)) ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hδsq hcoef
        _ = CH Kbig * (4 * (2 * q)) ^ 2 := by ring
    calc
      (∫ omega, Real.exp ((4 * (2 * q)) * YH omega) ∂P) ≤
          2 * Real.exp (CH Kbig * (4 * (2 * q)) ^ 2 * M.delta ^ 2) := by
            simpa [P, YH] using hHraw.2
      _ ≤ 2 * Real.exp (CH Kbig * (4 * (2 * q)) ^ 2) := by
            exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)
  have hlocal_pair : ∀ (f : C(SpatialCoordinates d, ℝ))
      (x : SpatialCoordinates d) (x' : SpatialCoordinates d),
      x ∈ Metric.closedBall y r → x' ∈ Metric.closedBall y r →
      |f x - f x'| ≤
        2 * aux_reference_oscillation_moments_localA y r f := by
    intro f x x' hx hx'
    have hxA := ContinuousMap.norm_coe_le_norm
      (f.restrict (aux_reference_oscillation_moments_Kball y r :
        Set (SpatialCoordinates d)) -
        ContinuousMap.const (aux_reference_oscillation_moments_Kball y r) (f y))
      ⟨x, hx⟩
    have hxA2 := ContinuousMap.norm_coe_le_norm
      (f.restrict (aux_reference_oscillation_moments_Kball y r :
        Set (SpatialCoordinates d)) -
        ContinuousMap.const (aux_reference_oscillation_moments_Kball y r) (f y))
      ⟨x', hx'⟩
    have hx1 : |f x - f y| ≤
        aux_reference_oscillation_moments_localA y r f := by
      change ‖f x - f y‖ ≤
        aux_reference_oscillation_moments_localA y r f at hxA
      simpa only [Real.norm_eq_abs] using hxA
    have hx2 : |f x' - f y| ≤
        aux_reference_oscillation_moments_localA y r f := by
      change ‖f x' - f y‖ ≤
        aux_reference_oscillation_moments_localA y r f at hxA2
      simpa only [Real.norm_eq_abs] using hxA2
    calc
      |f x - f x'| = |(f x - f y) - (f x' - f y)| := by congr 1 ; ring
      _ ≤ |f x - f y| + |f x' - f y| := by
        exact abs_sub _ _
      _ ≤ 2 * aux_reference_oscillation_moments_localA y r f := by
        calc
          |f x - f y| + |f x' - f y| ≤
              aux_reference_oscillation_moments_localA y r f +
                aux_reference_oscillation_moments_localA y r f :=
            add_le_add hx1 hx2
          _ = 2 * aux_reference_oscillation_moments_localA y r f := by ring
  have hHpair : ∀ omega x, x ∈ Metric.closedBall y r →
      ∀ x', x' ∈ Metric.closedBall y r →
      |H omega x - H omega x'| ≤ 2 * YH omega := by
    intro omega x hx x' hx'
    have hxH := ContinuousMap.norm_coe_le_norm
      ((H omega).restrict (Kbig : Set (SpatialCoordinates d)))
      ⟨x, hKbig x hx⟩
    have hxH' := ContinuousMap.norm_coe_le_norm
      ((H omega).restrict (Kbig : Set (SpatialCoordinates d)))
      ⟨x', hKbig x' hx'
      ⟩
    calc
      |H omega x - H omega x'| ≤ |H omega x| + |H omega x'| := abs_sub _ _
      _ ≤ YH omega + YH omega := by
        exact add_le_add hxH hxH'
      _ = 2 * YH omega := by ring
  have hsum_pair : ∀ omega x, x ∈ Metric.closedBall y r →
      ∀ x', x' ∈ Metric.closedBall y r →
      |(∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
        (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x')| ≤ S omega := by
    intro omega x hx x' hx'
    calc
      |(∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
          (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x')| =
          ‖∑ j ∈ Finset.range k,
            ((omega (-(j : ℤ))) x - (omega (-(j : ℤ))) x')‖ := by
              rw [Finset.sum_sub_distrib, Real.norm_eq_abs]
      _ ≤ ∑ j ∈ Finset.range k,
          ‖(omega (-(j : ℤ))) x - (omega (-(j : ℤ))) x'‖ :=
            norm_sum_le _ _
      _ = ∑ j ∈ Finset.range k,
          |(omega (-(j : ℤ))) x - (omega (-(j : ℤ))) x'| := by
            simp only [Real.norm_eq_abs]
      _ ≤ ∑ j ∈ Finset.range k, X j omega := by
            apply Finset.sum_le_sum
            intro j hj
            have hh := hlocal_pair (omega (-(j : ℤ))) x x' hx hx'
            simpa [X] using hh
      _ = S omega := by rfl
  have hO_le : ∀ omega, O omega ≤ 2 * YH omega + S omega := by
    intro omega
    dsimp [O]
    have hne : {v : ℝ | ∃ x ∈ Metric.closedBall y r,
        ∃ x' ∈ Metric.closedBall y r, v = F omega (x, x')}.Nonempty := by
      refine ⟨F omega (y, y), y, Metric.mem_closedBall_self hr.le,
        y, Metric.mem_closedBall_self hr.le, rfl⟩
    refine csSup_le hne ?_
    rintro v ⟨x, hx, x', hx', rfl⟩
    calc
      F omega (x, x') =
          |(H omega x - H omega x') +
            ((∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
              (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x'))| := by
            change |(H omega x +
                ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
              (H omega x' +
                ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x')| = _
            congr 1
            ring
      _ ≤ |H omega x - H omega x'| +
          |(∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
            (∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x')| := by
            exact abs_add_le _ _
      _ ≤ 2 * YH omega + S omega :=
            add_le_add (hHpair omega x hx x' hx') (hsum_pair omega x hx x' hx')
  have hpoint : ∀ omega,
      Real.exp ((2 * q) * O omega) ≤
        (Real.exp ((4 * (2 * q)) * YH omega) +
          Real.exp ((2 * (2 * q)) * S omega)) / 2 := by
    intro omega
    have hq0 : 0 ≤ 2 * q := by positivity
    exact aux_reference_oscillation_moments_exp_osc_envelope q
      (O omega) (YH omega) (S omega) (hO_le omega) hq0
  have hdom : Integrable V P := by
    rw [hV]
    exact aux_reference_oscillation_moments_integrable_add_div_two
      hHint hSlin.1
  rw [hV] at hdom
  have hOexp_meas' : Measurable (fun omega => Real.exp ((2 * q) * O omega)) := by
    exact aux_reference_oscillation_moments_measurable_exp_mul
      (2 * q) hOmeas
  have hOexp_int :=
    aux_reference_oscillation_moments_integrable_exp_of_le
      (f := O)
      (g := fun omega =>
        (Real.exp ((4 * (2 * q)) * YH omega) +
          Real.exp ((2 * (2 * q)) * S omega)) / 2)
      (2 * q) hOmeas hdom hpoint
  /-
  have hOexp_bound :
      (∫ omega, Real.exp ((2 * q) * O omega) ∂P) ≤ 2 * Real.exp E := by
    have hmono :
        (fun omega => Real.exp ((2 * q) * O omega)) ≤
          (fun omega =>
            (Real.exp ((4 * (2 * q)) * YH omega) +
              Real.exp ((2 * (2 * q)) * S omega)) / 2) := by
      intro omega
      exact hpoint omega
    have hmono_ae :
        (fun omega => Real.exp ((2 * q) * O omega)) ≤ᵐ[P]
          (fun omega =>
            (Real.exp ((4 * (2 * q)) * YH omega) +
              Real.exp ((2 * (2 * q)) * S omega)) / 2) :=
      Filter.Eventually.of_forall hmono
    have hIntMono' :
        (∫ omega, Real.exp ((2 * q) * O omega) ∂P) ≤
          ∫ omega, (Real.exp ((4 * (2 * q)) * YH omega) +
            Real.exp ((2 * (2 * q)) * S omega)) / 2 ∂P := by
      exact aux_reference_oscillation_moments_integral_mono_ae
        hOexp_int hdom hmono_ae
    have hA : 0 ≤ CH Kbig * (4 * (2 * q)) ^ 2 :=
      mul_nonneg (hCH Kbig) (sq_nonneg _)
    have hB : 0 ≤ (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2 :=
      sq_nonneg _
    have hAvgToE :
        (∫ omega, (Real.exp ((4 * (2 * q)) * YH omega) +
          Real.exp ((2 * (2 * q)) * S omega)) / 2 ∂P) ≤ 2 * Real.exp E := by
      exact aux_reference_oscillation_moments_integral_add_div_two_exp_le
        (μ := P)
        (f := fun omega => Real.exp ((4 * (2 * q)) * YH omega))
        (g := fun omega => Real.exp ((2 * (2 * q)) * S omega))
        (a := CH Kbig * (4 * (2 * q)) ^ 2)
        (b := (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2)
        (e := E) hHint hSlin.1 hHbound hSlin.2 hE hA hB
    exact hIntMono'.trans hAvgToE
  have hconvert :
      MemLp (fun omega => Real.exp (O omega))
          (ENNReal.ofReal (2 * q)) P ∧
        eLpNorm (fun omega => Real.exp (O omega))
          (ENNReal.ofReal (2 * q)) P ≤
          ENNReal.ofReal ((2 * Real.exp E) ^ (1 / (2 * q))) := by
    have hp : 0 < 2 * q := by linarith
    have hp0 : ENNReal.ofReal (2 * q) ≠ 0 :=
      (ENNReal.ofReal_eq_zero.not).2 (not_le.mpr hp)
    have hptop : ENNReal.ofReal (2 * q) ≠ ∞ := ENNReal.ofReal_ne_top
    have heq : ∀ omega, ‖Real.exp (O omega)‖ ^
        (ENNReal.ofReal (2 * q)).toReal =
          Real.exp ((2 * q) * O omega) := by
      intro omega
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ENNReal.toReal_ofReal hp.le]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    have hpow : Integrable (fun omega =>
        ‖Real.exp (O omega)‖ ^
          (ENNReal.ofReal (2 * q)).toReal) P := by
      simpa only [heq] using hOexp_int
    have hexpm : Measurable (fun omega => Real.exp (O omega)) := hOmeas.exp
    have hmem :=
      (integrable_norm_rpow_iff hexpm.aestronglyMeasurable hp0 hptop).mp hpow
    refine ⟨hmem, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hexpm.aestronglyMeasurable]
    have hlin :
        ∫⁻ omega, ‖Real.exp (O omega)‖ₑ ^
            (ENNReal.ofReal (2 * q)).toReal ∂P =
          ENNReal.ofReal (∫ omega, Real.exp ((2 * q) * O omega) ∂P) := by
      rw [ofReal_integral_eq_lintegral_ofReal hOexp_int
        (Filter.Eventually.of_forall fun omega => (Real.exp_pos _).le)]
      apply lintegral_congr_ae
      filter_upwards [] with omega
      rw [← ofReal_norm_eq_enorm]
      rw [ENNReal.ofReal_rpow_of_nonneg
        (norm_nonneg (Real.exp (O omega)))
        ENNReal.toReal_nonneg]
      rw [heq]
    rw [hlin]
    calc
      (ENNReal.ofReal
        (∫ omega, Real.exp ((2 * q) * O omega) ∂P)) ^
          (1 / (ENNReal.ofReal (2 * q)).toReal) ≤
          (ENNReal.ofReal (2 * Real.exp E)) ^ (1 / (2 * q)) := by
            rw [ENNReal.toReal_ofReal hp.le]
            exact ENNReal.rpow_le_rpow
              ((ENNReal.ofReal_le_ofReal_iff (by positivity)).2 hOexp_bound)
              (by positivity)
      _ = ENNReal.ofReal ((2 * Real.exp E) ^ (1 / (2 * q))) := by
            rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  change MemLp (fun omega => Real.exp (O omega)) (ENNReal.ofReal (2 * q)) P ∧
    eLpNorm (fun omega => Real.exp (O omega)) (ENNReal.ofReal (2 * q)) P ≤
      ENNReal.ofReal Cosc
  rw [hCosc]
  exact hconvert
  -/
  exact aux_reference_oscillation_moments_final
    P q hq O YH S
    (CH Kbig * (4 * (2 * q)) ^ 2)
    ((((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2) E Cosc
    hOmeas hOexp_int hHint hSlin.1 hHbound hSlin.2
    (mul_nonneg (hCH Kbig) (sq_nonneg _)) (sq_nonneg _)
    hO_le hE hCosc







theorem aux_reference_oscillation_moments_delta
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q)
    (Pd : _root_.SubdiffusiveProcess.Model.GMCModel d → (BilateralField d → C(SpatialCoordinates d, ℝ)) → Prop)
    (hPmeas : ∀ M H, Pd M H → Measurable H)
    (CH : Compacts (SpatialCoordinates d) → ℝ)
    (hCH : ∀ K, 0 ≤ CH K)
    (hHmom : aux_reference_oscillation_moments_HmomP d Pd CH)
    (m : ℕ) (hm : 0 < m)
    (hLayer : aux_reference_oscillation_moments_Layer d m)
    (Kbig : Compacts (SpatialCoordinates d))
    (E Cosc : ℝ)
    (hKbig_def : Kbig =
      aux_reference_oscillation_moments_Kball
        (0 : SpatialCoordinates d) (3 : ℝ))
    (hE : E = CH Kbig * (4 * (2 * q)) ^ 2 +
      (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2)
    (hCosc : Cosc = (2 * Real.exp E) ^ (1 / (2 * q)))
    (delta0 : ℝ) (hdelta0 : 0 < delta0) (hdelta1 : delta0 ≤ 1)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : Pd M H) (hM : M.delta ≤ delta0) :
        let P := (chaosSampleLaw M).toMeasure
        let K : Set (SpatialCoordinates d) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k omega x - G k omega x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega y => sSup (oscSet k omega y)
        ∀ (k : ℕ) (y : SpatialCoordinates d), y ∈ K →
          MemLp (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ∧
        eLpNorm (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc := by
  classical
  dsimp only
  intro k y hy
  exact aux_reference_oscillation_moments_point
    d hd q hq Pd hPmeas CH hCH hHmom m hm hLayer Kbig E Cosc
    hKbig_def hE hCosc delta0 hdelta0 hdelta1 M H hH hM k y hy

theorem aux_reference_oscillation_moments_inner
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q)
    (Pd : _root_.SubdiffusiveProcess.Model.GMCModel d → (BilateralField d → C(SpatialCoordinates d, ℝ)) → Prop)
    (hPmeas : ∀ M H, Pd M H → Measurable H)
    (CH : Compacts (SpatialCoordinates d) → ℝ)
    (hCH : ∀ K, 0 ≤ CH K)
    (hHmom : aux_reference_oscillation_moments_HmomP d Pd CH)
    (m : ℕ) (hm : 0 < m)
    (hLayer : aux_reference_oscillation_moments_Layer d m)
    (Kbig : Compacts (SpatialCoordinates d))
    (E Cosc : ℝ)
    (hKbig_def : Kbig =
      aux_reference_oscillation_moments_Kball
        (0 : SpatialCoordinates d) (3 : ℝ))
    (hE : E = CH Kbig * (4 * (2 * q)) ^ 2 +
      (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2)
    (hCosc : Cosc = (2 * Real.exp E) ^ (1 / (2 * q))) :
      ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        Pd M H → M.delta ≤ delta0 →
        let P := (chaosSampleLaw M).toMeasure
        let K : Set (SpatialCoordinates d) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k omega x - G k omega x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega y => sSup (oscSet k omega y)
        ∀ (k : ℕ) (y : SpatialCoordinates d), y ∈ K →
          MemLp (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ∧
        eLpNorm (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc := by
  classical
  intro delta0 hdelta0 hdelta1 M H hH hM
  exact aux_reference_oscillation_moments_delta
    d hd q hq Pd hPmeas CH hCH hHmom m hm hLayer Kbig E Cosc
    hKbig_def hE hCosc delta0 hdelta0 hdelta1 M H hH hM

theorem aux_reference_oscillation_moments_core_P
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q)
    (Pd : _root_.SubdiffusiveProcess.Model.GMCModel d → (BilateralField d → C(SpatialCoordinates d, ℝ)) → Prop)
    (hPmeas : ∀ M H, Pd M H → Measurable H)
    (CH : Compacts (SpatialCoordinates d) → ℝ)
    (hCH : ∀ K, 0 ≤ CH K)
    (hHmom : aux_reference_oscillation_moments_HmomP d Pd CH)
    (m : ℕ) (hm : 0 < m)
    (hLayer : aux_reference_oscillation_moments_Layer d m) :
    ∃ Cosc : ℝ, 0 < Cosc ∧
      ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        Pd M H → M.delta ≤ delta0 →
        let P := (chaosSampleLaw M).toMeasure
        let K : Set (SpatialCoordinates d) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k omega x - G k omega x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega y => sSup (oscSet k omega y)
        ∀ (k : ℕ) (y : SpatialCoordinates d), y ∈ K →
          MemLp (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ∧
        eLpNorm (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc := by
  classical
  let Kbig := aux_reference_oscillation_moments_Kball
    (0 : SpatialCoordinates d) (3 : ℝ)
  let E : ℝ := CH Kbig * (4 * (2 * q)) ^ 2 +
    (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2
  let Cosc : ℝ := (2 * Real.exp E) ^ (1 / (2 * q))
  have hKbig_def : Kbig =
      aux_reference_oscillation_moments_Kball
        (0 : SpatialCoordinates d) (3 : ℝ) := by
    rfl
  have hE : E = CH Kbig * (4 * (2 * q)) ^ 2 +
      (((3 / 2 : ℝ) * (m : ℝ)) * (2 * q)) ^ 2 := by
    rfl
  have hCosc : Cosc = (2 * Real.exp E) ^ (1 / (2 * q)) := by
    rfl
  refine ⟨Cosc, by
    dsimp [Cosc]
    positivity, ?_⟩
  exact aux_reference_oscillation_moments_inner
    d hd q hq Pd hPmeas CH hCH hHmom m hm hLayer Kbig E Cosc
    hKbig_def hE hCosc

theorem aux_reference_oscillation_moments_core
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q)
    (CH : Compacts (SpatialCoordinates d) → ℝ)
    (hCH : ∀ K, 0 ≤ CH K)
    (hHmom : aux_reference_oscillation_moments_Hmom d CH)
    (m : ℕ) (hm : 0 < m)
    (hLayer : aux_reference_oscillation_moments_Layer d m) :
    ∃ Cosc : ℝ, 0 < Cosc ∧
      ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let P := (chaosSampleLaw M).toMeasure
        let K : Set (SpatialCoordinates d) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k omega x - G k omega x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega y => sSup (oscSet k omega y)
        ∀ (k : ℕ) (y : SpatialCoordinates d), y ∈ K →
          MemLp (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ∧
        eLpNorm (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc := by
  exact aux_reference_oscillation_moments_core_P d hd q hq
    (fun M H => InfraredCharacterization M H) (fun M H hH => hH.1) CH hCH hHmom m hm hLayer

theorem aux_reference_oscillation_moments_core_adm
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q)
    (CH : Compacts (SpatialCoordinates d) → ℝ)
    (hCH : ∀ K, 0 ≤ CH K)
    (hHmom : aux_reference_oscillation_moments_HmomP d
      (fun M H => InfraredAdmissible M H) CH)
    (m : ℕ) (hm : 0 < m)
    (hLayer : aux_reference_oscillation_moments_Layer d m) :
    ∃ Cosc : ℝ, 0 < Cosc ∧
      ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H → M.delta ≤ delta0 →
        let P := (chaosSampleLaw M).toMeasure
        let K : Set (SpatialCoordinates d) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k omega x - G k omega x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega y => sSup (oscSet k omega y)
        ∀ (k : ℕ) (y : SpatialCoordinates d), y ∈ K →
          MemLp (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ∧
        eLpNorm (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc := by
  exact aux_reference_oscillation_moments_core_P d hd q hq
    (fun M H => InfraredAdmissible M H) (fun M H hH => hH.measurable) CH hCH hHmom m hm hLayer

theorem reference_oscillation_moments
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ Cosc : ℝ, 0 < Cosc ∧
      ∀ delta0 : ℝ, 0 < delta0 → delta0 ≤ 1 →
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H → M.delta ≤ delta0 →
        let P := (chaosSampleLaw M).toMeasure
        let K : Set (SpatialCoordinates d) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G k omega x - G k omega x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega y => sSup (oscSet k omega y)
        ∀ (k : ℕ) (y : SpatialCoordinates d), y ∈ K →
          MemLp (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ∧
        eLpNorm (fun omega => Real.exp (osc k omega y))
              (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cosc := by
  classical
  obtain ⟨CH, hCH, hHmom⟩ :=
    exists_uniform_compactExponentialMoment_of_admissible hd
  obtain ⟨m, hm, hLayer⟩ :=
    aux_reference_oscillation_moments_layer_exp hd
  exact aux_reference_oscillation_moments_core_adm
    d hd q hq CH hCH hHmom m hm hLayer

end SubdiffusiveProcess.Paper
