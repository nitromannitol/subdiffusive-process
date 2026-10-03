module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerDensity

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower

variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)} {U : Set (Vec d)}
  {p : ℝ → Vec d → Vec d → ℝ}

/-- The weight of a local diffusion is elliptic on every bounded set. -/
theorem coefficientOn_of_localDiffusion (hD : LocalDiffusion c rho law)
    (hUb : Bornology.IsBounded U) : CoefficientOn U rho :=
  coefficientOn_mono subset_closure (hD.2.1 (closure U) hUb.isCompact_closure).2

/-- The restricted weighted measure of a domain of finite mass is finite. -/
theorem isFiniteMeasure_restrict (hfin : (weightedMeasure rho) U ≠ ∞) :
    IsFiniteMeasure ((weightedMeasure rho).restrict U) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact lt_of_le_of_ne le_top hfin

/-- Every point of the domain is the limit of a sequence in any set of full measure. -/
theorem exists_seq_tendsto_of_ae (hU : IsOpen U) (hrho : CoefficientOn U rho)
    {S : Set (Vec d)} (hS : ∀ᵐ y ∂((weightedMeasure rho).restrict U), y ∈ S)
    {w : Vec d} (hw : w ∈ U) :
    ∃ ws : ℕ → Vec d, (∀ n, ws n ∈ S) ∧ (∀ n, ws n ∈ U) ∧ Tendsto ws atTop (𝓝 w) := by
  have hmemSU : ∀ᵐ y ∂((weightedMeasure rho).restrict U), y ∈ S ∩ U := by
    filter_upwards [hS, ae_restrict_mem hU.measurableSet] with y h1 h2 using ⟨h1, h2⟩
  have hnull : ((weightedMeasure rho).restrict U) (S ∩ U)ᶜ = 0 := ae_iff.mp hmemSU
  have hne : ∀ n : ℕ, (Metric.ball w (1 / (n + 1 : ℝ)) ∩ (S ∩ U)).Nonempty := by
    intro n
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    have hsub : Metric.ball w (1 / (n + 1 : ℝ)) ⊆ (S ∩ U)ᶜ := by
      intro z hz
      exact fun hz' => (Set.eq_empty_iff_forall_notMem.mp hcon z) ⟨hz, hz'⟩
    have hzero : ((weightedMeasure rho).restrict U) (Metric.ball w (1 / (n + 1 : ℝ))) = 0 :=
      measure_mono_null hsub hnull
    have hpos : 0 < ((weightedMeasure rho).restrict U) (Metric.ball w (1 / (n + 1 : ℝ))) :=
      weightedMeasure_restrict_open_pos hU hrho _ Metric.isOpen_ball
        ⟨w, Metric.mem_ball_self (by positivity), hw⟩
    exact absurd hzero hpos.ne'
  choose ws hws using hne
  refine ⟨ws, fun n => (hws n).2.1, fun n => (hws n).2.2, Metric.tendsto_atTop.mpr ?_⟩
  intro eps heps
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt heps
  refine ⟨N, fun n hn => ?_⟩
  have hball := (hws n).1
  rw [Metric.mem_ball] at hball
  refine hball.trans_le (le_trans ?_ hN.le)
  apply one_div_le_one_div_of_le (by positivity)
  have : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  linarith

/-- Sequential continuity of the killed density in the endpoint. -/
theorem tendsto_density_endpoint
    (hpc : ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ U ×ˢ U))
    {t : ℝ} (ht : 0 < t) {x w : Vec d} (hx : x ∈ U) (hw : w ∈ U) {ws : ℕ → Vec d}
    (hws : ∀ n, ws n ∈ U) (hlim : Tendsto ws atTop (𝓝 w)) :
    Tendsto (fun n => p t x (ws n)) atTop (𝓝 (p t x w)) := by
  have hwithin : Tendsto (fun n => ((t, x, ws n) : ℝ × Vec d × Vec d)) atTop
      (𝓝[Ioi 0 ×ˢ U ×ˢ U] (t, x, w)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ⟨ht, hx, hws n⟩⟩
    exact tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.prodMk_nhds hlim)
  exact ((hpc (t, x, w) ⟨ht, hx, hw⟩).tendsto).comp hwithin

/-- The Chapman–Kolmogorov lower bound for the killed density, at every pair of points. -/
theorem ofReal_density_lintegral_le (hD : LocalDiffusion c rho law) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U)
    (hp : IsKilledDensity law rho U p)
    (hpc : ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ U ×ˢ U))
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) {x w : Vec d} (hx : x ∈ U) (hw : w ∈ U) :
    (∫⁻ y, ENNReal.ofReal (p t₁ x y) * ENNReal.ofReal (p t₂ y w)
        ∂((weightedMeasure rho).restrict U))
      ≤ ENNReal.ofReal (p (t₁ + t₂) x w) := by
  classical
  set mu := (weightedMeasure rho).restrict U with hmu
  obtain ⟨ws, hwsS, hwsU, hwslim⟩ :=
    exists_seq_tendsto_of_ae hU (coefficientOn_of_localDiffusion hD hUb)
      (density_semigroup_ae hD hU hUb hp ht₁ ht₂ hx) hw
  have hstep : ∀ n, ENNReal.ofReal (p (t₁ + t₂) x (ws n))
      = ∫⁻ y, ENNReal.ofReal (p t₁ x y) * ENNReal.ofReal (p t₂ y (ws n)) ∂mu := hwsS
  have hlim : Tendsto (fun n => ENNReal.ofReal (p (t₁ + t₂) x (ws n))) atTop
      (𝓝 (ENNReal.ofReal (p (t₁ + t₂) x w))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_density_endpoint hpc (by linarith) hx hw hwsU hwslim)
  have hliminf : liminf (fun n => ∫⁻ y, ENNReal.ofReal (p t₁ x y) *
      ENNReal.ofReal (p t₂ y (ws n)) ∂mu) atTop = ENNReal.ofReal (p (t₁ + t₂) x w) := by
    have : (fun n => ∫⁻ y, ENNReal.ofReal (p t₁ x y) *
        ENNReal.ofReal (p t₂ y (ws n)) ∂mu)
        = fun n => ENNReal.ofReal (p (t₁ + t₂) x (ws n)) := funext fun n => (hstep n).symm
    rw [this]
    exact hlim.liminf_eq
  have hpoint : ∀ᵐ y ∂mu, liminf (fun n => ENNReal.ofReal (p t₁ x y) *
      ENNReal.ofReal (p t₂ y (ws n))) atTop
        = ENNReal.ofReal (p t₁ x y) * ENNReal.ofReal (p t₂ y w) := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
    refine Tendsto.liminf_eq ?_
    exact ENNReal.Tendsto.const_mul
      ((ENNReal.continuous_ofReal.tendsto _).comp
        (tendsto_density_endpoint hpc ht₂ hy hw hwsU hwslim))
      (Or.inr ENNReal.ofReal_ne_top)
  calc
    (∫⁻ y, ENNReal.ofReal (p t₁ x y) * ENNReal.ofReal (p t₂ y w) ∂mu)
        = ∫⁻ y, liminf (fun n => ENNReal.ofReal (p t₁ x y) *
            ENNReal.ofReal (p t₂ y (ws n))) atTop ∂mu := (lintegral_congr_ae hpoint).symm
    _ ≤ liminf (fun n => ∫⁻ y, ENNReal.ofReal (p t₁ x y) *
            ENNReal.ofReal (p t₂ y (ws n)) ∂mu) atTop :=
      lintegral_liminf_le fun n =>
        (measurable_density hp ht₁ x).mul (measurable_density_left hp ht₂ (ws n))
    _ = ENNReal.ofReal (p (t₁ + t₂) x w) := hliminf

/-- Pointwise symmetry of the killed density on the domain. -/
theorem density_symm (hD : LocalDiffusion c rho law) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U)
    (hp : IsKilledDensity law rho U p)
    (hpc : ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ U ×ˢ U))
    {t : ℝ} (ht : 0 < t) {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) : p t x y = p t y x := by
  have hfin : (weightedMeasure rho) U ≠ ∞ :=
    KilledDensityExistence.weightedMeasure_ne_top_of_localDiffusion hD hU hUb
  classical
  haveI : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD
  haveI hfinite : IsFiniteMeasure ((weightedMeasure rho).restrict U) :=
    isFiniteMeasure_restrict hfin
  set mu := (weightedMeasure rho).restrict U with hmu
  set F : Vec d × Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal (p t z.1 z.2) with hF
  set G : Vec d × Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal (p t z.2 z.1) with hG
  have hFm : Measurable F := measurable_density_prod hp ht
  have hGm : Measurable G := (measurable_density_prod hp ht).comp measurable_swap
  -- rectangle identity for the density
  have hrow : ∀ (B : Set (Vec d)), MeasurableSet B → ∀ᵐ z ∂mu,
      killedKernel law U hU (Real.toNNReal t) z B
        = ∫⁻ y in B, ENNReal.ofReal (p t z y) ∂mu := by
    intro B hB
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    exact killedKernel_apply_eq_density hU hp t ht z hz B hB
  have hrect : ∀ C D : Set (Vec d), MeasurableSet C → MeasurableSet D →
      (∫⁻ z in C ×ˢ D, F z ∂(mu.prod mu)) = ∫⁻ z in C ×ˢ D, G z ∂(mu.prod mu) := by
    intro C D hC hD'
    have hsym := killedKernel_rectangle_symmetry hD hU hUb (Real.toNNReal t) C D hC hD'
    have hFint : (∫⁻ z in C ×ˢ D, F z ∂(mu.prod mu))
        = ∫⁻ a, ∫⁻ b, F (a, b) ∂(mu.restrict D) ∂(mu.restrict C) := by
      rw [← Measure.prod_restrict, lintegral_prod _ hFm.aemeasurable]
    have hGint : (∫⁻ z in C ×ˢ D, G z ∂(mu.prod mu))
        = ∫⁻ b, ∫⁻ a, G (a, b) ∂(mu.restrict C) ∂(mu.restrict D) := by
      rw [← Measure.prod_restrict, lintegral_prod _ hGm.aemeasurable,
        lintegral_lintegral_swap hGm.aemeasurable]
    have hCside : (∫⁻ a in C, ∫⁻ b in D, F (a, b) ∂mu ∂mu)
        = ∫⁻ a in C, killedKernel law U hU (Real.toNNReal t) a D ∂mu :=
      lintegral_congr_ae ((ae_restrict_of_ae (hrow D hD')).mono fun a ha => ha.symm)
    have hDside : (∫⁻ b in D, ∫⁻ a in C, G (a, b) ∂mu ∂mu)
        = ∫⁻ b in D, killedKernel law U hU (Real.toNNReal t) b C ∂mu :=
      lintegral_congr_ae ((ae_restrict_of_ae (hrow C hC)).mono fun b hb => hb.symm)
    rw [hFint, hGint, hCside, hDside, hsym]
  -- the two densities define the same finite measure
  have hmass : ∀ (H : Vec d × Vec d → ℝ≥0∞), Measurable H →
      ((mu.prod mu).withDensity H) univ = ∫⁻ z, H z ∂(mu.prod mu) := by
    intro H hH
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hFfin : (∫⁻ z, F z ∂(mu.prod mu)) ≤ mu univ := by
    rw [lintegral_prod _ hFm.aemeasurable]
    have hrow1 : ∀ᵐ a ∂mu, (∫⁻ b, F (a, b) ∂mu) ≤ 1 := by
      filter_upwards [ae_restrict_mem hU.measurableSet] with a ha
      have hkey := killedKernel_apply_eq_density hU hp t ht a ha univ MeasurableSet.univ
      rw [Measure.restrict_univ] at hkey
      rw [show (∫⁻ b, F (a, b) ∂mu) = ∫⁻ b, ENNReal.ofReal (p t a b) ∂mu from rfl, ← hkey]
      exact killedKernel_subMarkov law U hU (Real.toNNReal t) a
    calc (∫⁻ a, ∫⁻ b, F (a, b) ∂mu ∂mu) ≤ ∫⁻ _a, (1 : ℝ≥0∞) ∂mu := lintegral_mono_ae hrow1
      _ = mu univ := by simp
  have huniv : (∫⁻ z, F z ∂(mu.prod mu)) = ∫⁻ z, G z ∂(mu.prod mu) := by
    have := hrect univ univ MeasurableSet.univ MeasurableSet.univ
    rwa [Set.univ_prod_univ, Measure.restrict_univ] at this
  haveI hν₁ : IsFiniteMeasure ((mu.prod mu).withDensity F) := by
    refine ⟨?_⟩
    rw [hmass F hFm]
    exact lt_of_le_of_lt hFfin (measure_lt_top _ _)
  haveI hν₂ : IsFiniteMeasure ((mu.prod mu).withDensity G) := by
    refine ⟨?_⟩
    rw [hmass G hGm, ← huniv]
    exact lt_of_le_of_lt hFfin (measure_lt_top _ _)
  have hmeaseq : (mu.prod mu).withDensity F = (mu.prod mu).withDensity G := by
    refine MeasureTheory.ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro s ⟨C, hC, D, hD', rfl⟩
      simp only [Set.mem_setOf_eq] at hC hD'
      rw [withDensity_apply _ (hC.prod hD'), withDensity_apply _ (hC.prod hD')]
      exact hrect C D hC hD'
    · rw [hmass F hFm, hmass G hGm, huniv]
  have hae : F =ᵐ[mu.prod mu] G := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hFm hGm (fun s hs _ => ?_)
    rw [← withDensity_apply _ hs, ← withDensity_apply _ hs, hmeaseq]
  -- upgrade to a pointwise identity by continuity
  have hslice : ContinuousOn (fun z : Vec d × Vec d => p t z.1 z.2) (U ×ˢ U) :=
    hpc.comp (continuous_const.prodMk continuous_id).continuousOn fun z hz => ⟨ht, hz⟩
  have hswap : ContinuousOn (fun z : Vec d × Vec d => p t z.2 z.1) (U ×ˢ U) :=
    hslice.comp continuous_swap.continuousOn fun z hz => ⟨hz.2, hz.1⟩
  have haediff : ∀ᵐ z ∂(mu.prod mu), p t z.1 z.2 - p t z.2 z.1 = 0 := by
    have hUc : mu Uᶜ = 0 := by
      rw [hmu, Measure.restrict_apply hU.measurableSet.compl, compl_inter_self]
      exact measure_empty
    have hmem : ∀ᵐ z ∂(mu.prod mu), z ∈ U ×ˢ U := by
      rw [ae_iff]
      refine measure_mono_null
        (t := (Uᶜ ×ˢ (univ : Set (Vec d))) ∪ ((univ : Set (Vec d)) ×ˢ Uᶜ)) ?_ ?_
      · rintro z hz
        by_cases h1 : z.1 ∈ U
        · exact Or.inr ⟨mem_univ _, fun h2 => hz ⟨h1, h2⟩⟩
        · exact Or.inl ⟨h1, mem_univ _⟩
      · refine le_antisymm ((measure_union_le _ _).trans ?_) bot_le
        rw [Measure.prod_prod, Measure.prod_prod, hUc]
        simp
    filter_upwards [hae, hmem] with z hz hzU
    have h1 : (0 : ℝ) ≤ p t z.1 z.2 := hp.2.1 t ht z.1 hzU.1 z.2 hzU.2
    have h2 : (0 : ℝ) ≤ p t z.2 z.1 := hp.2.1 t ht z.2 hzU.2 z.1 hzU.1
    have := (ENNReal.ofReal_eq_ofReal_iff h1 h2).mp hz
    linarith
  have hle : ∀ z ∈ U ×ˢ U, p t z.1 z.2 - p t z.2 z.1 ≤ 0 :=
    continuousOn_le_of_ae_weightedMeasure_prod hU (coefficientOn_of_localDiffusion hD hUb) _
      (hslice.sub hswap) 0 (haediff.mono fun z hz => le_of_eq hz)
  have hge : ∀ z ∈ U ×ˢ U, p t z.2 z.1 - p t z.1 z.2 ≤ 0 :=
    continuousOn_le_of_ae_weightedMeasure_prod hU (coefficientOn_of_localDiffusion hD hUb) _
      (hswap.sub hslice) 0 (haediff.mono fun z hz => by change p t z.2 z.1 - p t z.1 z.2 ≤ 0; linarith [hz])
  have h1 := hle (x, y) ⟨hx, hy⟩
  have h2 := hge (x, y) ⟨hx, hy⟩
  dsimp only at h1 h2
  linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
