module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeMeanExitLower

@[expose] public section

/-!
# Every-start early-exit estimates for the supplied lifetime laws

The same killed-density/right-continuity argument used by Section 9 for mean exit
applies to every excessive function of the killed semigroup. In particular survival
to a fixed time is excessive. Hence an almost-everywhere early-exit bound on an open
interior set holds at every starting point there, without a nonexplosion assumption.
This is the pointwise passage in paper §8, proof of `tight:prop-tightness`, Step 1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open scoped ENNReal NNReal Topology BoundedContinuousFunction
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalTightness

/-- A bounded continuous nonnegative lower bound transfers from almost everywhere to every point. -/
theorem excessive_ge_continuous_of_ae {d : ℕ}
    {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusionData c rho law) {U : Set (Vec d)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (F : Vec d → ENNReal)
    (hexcess : ∀ t : NNReal, ∀ x,
      (∫⁻ y, F y ∂killedKernel law U hU t x) ≤ F x)
    (g : Vec d →ᵇ ℝ) (hg : ∀ y, 0 ≤ g y)
    (hlower : ∀ᵐ y ∂(weightedMeasure rho).restrict U,
      ENNReal.ofReal (g y) ≤ F y) :
    ∀ x ∈ U, ENNReal.ofReal (g x) ≤ F x := by
  obtain ⟨p, hpk, -⟩ := hD.2 U hU hUb
  have hM : StrongMarkov law := hD.1.1
  haveI hmk : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD.1
  have hbound : ∀ t : ℝ, 0 < t → ∀ x ∈ U,
      ENNReal.ofReal (kernelIntegral (killedKernel law U hU (Real.toNNReal t)) g x)
        ≤ F x := by
    intro t ht x hx
    have habs : killedKernel law U hU (Real.toNNReal t) x
        ≪ (weightedMeasure rho).restrict U := by
      rw [SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower.killedKernel_eq_withDensity
        hU hpk ht hx]
      exact withDensity_absolutelyContinuous _ _
    have hae : (fun y : Vec d => ENNReal.ofReal (g y)) ≤ᵐ[killedKernel law U hU
        (Real.toNNReal t) x] fun y => F y := habs.ae_le hlower
    have hfin : (killedKernel law U hU (Real.toNNReal t) x) univ < ∞ := by
      have hsub : (killedKernel law U hU (Real.toNNReal t) x) univ ≤ law x univ := by
        rw [killed_apply law U hU (Real.toNNReal t) x univ MeasurableSet.univ]
        exact measure_mono (subset_univ _)
      exact lt_of_le_of_lt hsub (by rw [hM.1 x]; exact ENNReal.one_lt_top)
    haveI : IsFiniteMeasure (killedKernel law U hU (Real.toNNReal t) x) := ⟨hfin⟩
    have hnn : 0 ≤ᵐ[killedKernel law U hU (Real.toNNReal t) x] fun y => g y :=
      Filter.Eventually.of_forall fun y => hg y
    have hint := ofReal_integral_eq_lintegral_ofReal
      (BoundedContinuousFunction.integrable (killedKernel law U hU (Real.toNNReal t) x) g) hnn
    calc ENNReal.ofReal (kernelIntegral (killedKernel law U hU (Real.toNNReal t)) g x)
        = ∫⁻ y, ENNReal.ofReal (g y) ∂(killedKernel law U hU (Real.toNNReal t) x) := hint
      _ ≤ ∫⁻ y, F y ∂(killedKernel law U hU (Real.toNNReal t) x) :=
          lintegral_mono_ae hae
      _ ≤ F x :=
          hexcess (Real.toNNReal t) x
  intro x hx
  have hcont := continuousWithinAt_killedKernel_integral law U hU g x 0
  have h1 : Tendsto
      (fun r : ℝ => ENNReal.ofReal
        (kernelIntegral (killedKernel law U hU (Real.toNNReal r)) g x))
      (nhdsWithin 0 (Set.Ici 0))
      (nhds (ENNReal.ofReal
        (kernelIntegral (killedKernel law U hU (Real.toNNReal 0)) g x))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hcont
  have hten : Tendsto
      (fun r : ℝ => ENNReal.ofReal
        (kernelIntegral (killedKernel law U hU (Real.toNNReal r)) g x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ENNReal.ofReal
        (kernelIntegral (killedKernel law U hU (Real.toNNReal 0)) g x))) :=
    h1.mono_left (nhdsWithin_mono (0:ℝ) (Set.Ioi_subset_Ici_self : Set.Ioi (0:ℝ) ⊆ Set.Ici 0))
  have hle : ENNReal.ofReal
      (kernelIntegral (killedKernel law U hU (Real.toNNReal 0)) g x) ≤ F x := by
    refine le_of_tendsto hten ?_
    have hmem : (Set.Ioi (0:ℝ)) ∈ (𝓝 0 ⊓ 𝓟 (Set.Ioi 0) : Filter ℝ) :=
      Filter.mem_inf_of_right (Filter.mem_principal_self _)
    filter_upwards [hmem] with r hr
    exact hbound r hr x hx
  rw [Real.toNNReal_zero, goodCube_killedKernel_integral_zero_of_start law hM U hU g
    g.continuous.measurable hx] at hle
  exact hle

/-- An almost-everywhere constant lower bound on an open interior set holds at every point there. -/
theorem excessive_lower_of_ae_on_open {d : ℕ}
    {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusionData c rho law) {U W : Set (Vec d)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (F : Vec d → ENNReal)
    (hexcess : ∀ t : NNReal, ∀ x,
      (∫⁻ y, F y ∂killedKernel law U hU t x) ≤ F x)
    (hW : IsOpen W) (hWU : W ⊆ U) {k : ℝ} (hk : 0 ≤ k)
    (hlower : ∀ᵐ y ∂(weightedMeasure rho).restrict U,
      y ∈ W → ENNReal.ofReal k ≤ F y) :
    ∀ x ∈ W, ENNReal.ofReal k ≤ F x := by
  intro x hx
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed
    (hW.isClosed_compl) (isClosed_singleton (x := x))
    (Set.disjoint_left.2 fun y hyW hyx =>
      have hyx' : y = x := Set.mem_singleton_iff.mp hyx
      hyW (hyx'.symm ▸ hx))
  set g0 : Vec d →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound f 1 (by
      intro y z
      rcases hf01 y with ⟨_, hay⟩
      rcases hf01 z with ⟨_, haz⟩
      have hy : f y - f z ≤ 1 := by linarith
      have hz : f z - f y ≤ 1 := by linarith
      rw [Real.dist_eq]
      exact abs_le.mpr ⟨by linarith, by linarith⟩) with hg0def
  have hg0 : ∀ y, g0 y = f y := fun y => rfl
  set g : Vec d →ᵇ ℝ := k • g0 with hgdef
  have hgy : ∀ y, g y = k * f y := fun _ => rfl
  have hgnn : ∀ y, 0 ≤ g y := by
    intro y
    rw [hgy]
    exact mul_nonneg hk (hf01 y).1
  have hgle : ∀ y, g y ≤ k := by
    intro y
    rw [hgy]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf01 y).2 hk
  have hae : ∀ᵐ y ∂((weightedMeasure rho).restrict U),
      ENNReal.ofReal (g y) ≤ F y := by
    filter_upwards [hlower] with y hy
    by_cases hyW : y ∈ W
    · calc ENNReal.ofReal (g y) ≤ ENNReal.ofReal k :=
        ENNReal.ofReal_le_ofReal (hgle y)
      _ ≤ F y := hy hyW
    · have hfy : f y = 0 := hf0 hyW
      have hgy0 : g y = 0 := by rw [hgy, hfy]; ring
      rw [hgy0]
      simp
  have hres := excessive_ge_continuous_of_ae hD hU hUb F hexcess g hgnn hae x (hWU hx)
  have hgx : g x = k := by
    have hfx : f x = 1 := hf1 (Set.mem_singleton x)
    rw [hgy, hfx, mul_one]
  rw [hgx] at hres
  exact hres

/-- Survival to a fixed time is excessive for the killed semigroup. -/
theorem survival_excessive {d : ℕ}
    (law : Kernel (Vec d) (Path d)) (hM : StrongMarkov law)
    (U : Set (Vec d)) (hU : IsOpen U) (s t : NNReal) (x : Vec d) :
    (∫⁻ y, killedKernel law U hU t y univ ∂killedKernel law U hU s x) ≤
      killedKernel law U hU t x univ := by
  rw [← Kernel.comp_apply' _ _ _ MeasurableSet.univ, ← semigroup law hM U hU s t]
  rw [killed_apply law U hU (s + t) x univ MeasurableSet.univ,
    killed_apply law U hU t x univ MeasurableSet.univ]
  apply measure_mono
  rintro w ⟨-, hw⟩
  exact ⟨mem_univ _, lt_of_le_of_lt (ENNReal.coe_le_coe.mpr le_add_self) hw⟩

/-- Every interior start inherits the almost-everywhere early-exit bound, at the
same time and with the same constant. Finite lifetime is allowed throughout. -/
theorem exit_probability_le_of_ae {d : ℕ}
    {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusionData c rho law) {U W : Set (Vec d)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hW : IsOpen W) (hWU : W ⊆ U) (t : NNReal) (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ᵐ y ∂(weightedMeasure rho).restrict U, y ∈ W →
      law y {w | LifetimePath.exitTime U w ≤ (t : ENNReal)} ≤ ENNReal.ofReal b) :
    ∀ x ∈ W, law x {w | LifetimePath.exitTime U w ≤ (t : ENNReal)} ≤
      ENNReal.ofReal b := by
  haveI : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD.1
  by_cases hb1 : 1 ≤ b
  · intro x hx
    exact (prob_le_one).trans (by simpa using ENNReal.ofReal_le_ofReal hb1)
  have hb1' : b ≤ 1 := (not_le.mp hb1).le
  have hsurv : ∀ y, killedKernel law U hU t y univ =
      1 - law y {w | LifetimePath.exitTime U w ≤ (t : ENNReal)} := by
    intro y
    rw [killed_apply law U hU t y univ MeasurableSet.univ]
    have hevent : {w : Path d | position t w ∈ univ ∧
        (t : ENNReal) < LifetimePath.exitTime U w} =
        {w : Path d | LifetimePath.exitTime U w ≤ (t : ENNReal)}ᶜ := by
      ext w
      simp
    rw [hevent, measure_compl (measurableSet_le
      (localTorsion_exitTime_measurable U hU) measurable_const) (measure_ne_top _ _)]
    simp
  have hae : ∀ᵐ y ∂(weightedMeasure rho).restrict U, y ∈ W →
      ENNReal.ofReal (1 - b) ≤ killedKernel law U hU t y univ := by
    filter_upwards [hbound] with y hy
    intro hyW
    rw [hsurv y, ENNReal.ofReal_sub 1 hb]
    simpa using tsub_le_tsub_left (hy hyW) (1 : ENNReal)
  have hpoint := excessive_lower_of_ae_on_open hD hU hUb
    (fun y => killedKernel law U hU t y univ)
    (fun s x => survival_excessive law hD.1.1 U hU s t x)
    hW hWU (sub_nonneg.mpr hb1') hae
  intro x hx
  have h := hpoint x hx
  rw [hsurv x, ENNReal.ofReal_sub 1 hb, ENNReal.ofReal_one] at h
  have he : ENNReal.ofReal b ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal hb1'
  have hp : law x {w | LifetimePath.exitTime U w ≤ (t : ENNReal)} ≤ 1 :=
    prob_le_one
  exact (ENNReal.sub_le_sub_iff_left hp (by simp)).mp h

end SubdiffusiveProcess.Section10.PhysicalTightness
