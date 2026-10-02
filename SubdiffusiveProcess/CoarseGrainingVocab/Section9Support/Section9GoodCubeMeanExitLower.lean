import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalTorsionSurvival
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationContinuity
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerDensity
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.UrysohnsLemma




set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.CommonSemigroupCrossing
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationSemigroup
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationUltra
open scoped ENNReal NNReal Topology BoundedContinuousFunction
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A live path starting inside an open set has a positive exit time. -/
theorem goodCube_exitTime_pos_of_start {d : ℕ} (U : Set (Vec d)) (hU : IsOpen U)
    (w : Path d) {x : Vec d} (hx : x ∈ U)
    (hstart : LifetimePath.coordinate 0 w = Cemetery.alive x) :
    0 < LifetimePath.exitTime U w := by
  have hlt : (0 : ℝ≥0∞) < w.lifetime := by
    by_contra h
    rw [not_lt] at h
    have hd := LifetimePath.coordinate_of_le w 0 h
    rw [hstart] at hd
    exact Sum.inl_ne_inr hd
  have hopen : IsOpen (Cemetery.alive '' U) := isOpenMap_inl U hU
  have hmem : (fun s : NNReal => LifetimePath.coordinate s w) ⁻¹' (Cemetery.alive '' U) ∈
      nhds (0 : NNReal) :=
    (coordinate_continuous_at w 0 hlt).preimage_mem_nhds
      (by rw [hstart]; exact hopen.mem_nhds (Set.mem_image_of_mem _ hx))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
  have hre : ((Real.toNNReal ε : NNReal) : ℝ≥0∞) ≤ LifetimePath.exitTime U w := by
    rw [le_exit U w]
    intro t ht
    by_contra hcon
    have h2 : (t : NNReal) < Real.toNNReal ε :=
      ENNReal.coe_lt_coe.mp (not_le.mp hcon)
    have htr : ((t : NNReal) : ℝ) < ε := by
      have hr : ((t : NNReal) : ℝ) < ((Real.toNNReal ε : NNReal) : ℝ) := by
        exact_mod_cast h2
      simpa only [Real.coe_toNNReal ε hε.le] using hr
    exact ht (hball (by
      simpa only [Metric.mem_ball, NNReal.dist_eq, NNReal.coe_zero, sub_zero,
        NNReal.abs_eq] using htr))
  have hpos0 : (0 : ℝ≥0∞) < ((Real.toNNReal ε : NNReal) : ℝ≥0∞) := by
    rw [coe_real_toNNReal_eq_ofReal]
    exact ENNReal.ofReal_pos.mpr hε
  exact lt_of_lt_of_le hpos0 hre

/-- The killed kernel at time zero evaluates its test at the interior starting point. -/
theorem goodCube_killedKernel_integral_zero_of_start {d : ℕ}
    (law : Kernel (Vec d) (Path d)) (hM : StrongMarkov law)
    (U : Set (Vec d)) (hU : IsOpen U) (g : Vec d → ℝ) (hg : Measurable g)
    {x : Vec d} (hx : x ∈ U) :
    kernelIntegral (killedKernel law U hU 0) g x = g x := by
  haveI : IsProbabilityMeasure (law x) := ⟨hM.1 x⟩
  have hzero : (Real.toNNReal (0 : ℝ) : NNReal) = 0 := by
    refine ENNReal.coe_injective ?_
    calc ((Real.toNNReal (0 : ℝ) : NNReal) : ℝ≥0∞)
        = ENNReal.ofReal (0 : ℝ) := coe_real_toNNReal_eq_ofReal 0
      _ = ((0 : NNReal) : ℝ≥0∞) := by simp
  have hkey := killedKernel_integral_eq_pathTest law U hU g hg (0 : ℝ) x
  rw [hzero] at hkey
  rw [hkey]
  have hae : ∀ᵐ w ∂law x, killedPathTest U g 0 w = g x := by
    filter_upwards [hM.2.1 x] with w hw
    have hpos : (0 : ℝ≥0∞) < LifetimePath.exitTime U w :=
      goodCube_exitTime_pos_of_start U hU w hx hw
    have hpx : position (Real.toNNReal (0 : ℝ)) w = x := by
      calc position (Real.toNNReal (0 : ℝ)) w
          = (LifetimePath.coordinate (Real.toNNReal (0 : ℝ)) w).elim id (fun _ => 0) := rfl
        _ = (Cemetery.alive x).elim id (fun _ => 0) := by rw [hzero, hw]
        _ = x := rfl
    unfold killedPathTest
    rw [if_pos (show ENNReal.ofReal (0 : ℝ) < LifetimePath.exitTime U w by simpa using hpos),
      hpx]
  calc ∫ w, killedPathTest U g 0 w ∂law x = ∫ w, g x ∂law x :=
      integral_congr_ae hae
    _ = g x := by simp

/-- The mean exit time is excessive for its killed semigroup, also when infinite. -/
theorem goodCube_lintegral_meanExit_killed_le {d : ℕ}
    (law : Kernel (Vec d) (Path d)) (hM : StrongMarkov law)
    (U : Set (Vec d)) (hU : IsOpen U) (t : NNReal) (x : Vec d) :
    (∫⁻ y, meanExit law U y ∂killedKernel law U hU t x) ≤ meanExit law U x := by
  have hmeas : Measurable (meanExit law U) :=
    (localTorsion_exitTime_measurable U hU).lintegral_kernel
  have hS : MeasurableSet {w : Path d | (t : ℝ≥0∞) < LifetimePath.exitTime U w} :=
    localTorsion_survival_measurable U hU t
  have key : ∀ w : Path d, (t : ℝ≥0∞) < LifetimePath.exitTime U w →
      LifetimePath.exitTime U (LifetimePath.shift t w) ≤ LifetimePath.exitTime U w := by
    intro w hw
    rw [← shift_add U w t hw]
    exact le_self_add
  have hae : (fun w : Path d => if (t : ℝ≥0∞) < LifetimePath.exitTime U w then
      LifetimePath.exitTime U w else LifetimePath.exitTime U (LifetimePath.shift t w))
      =ᵐ[(law x).restrict {w : Path d | (t : ℝ≥0∞) < LifetimePath.exitTime U w}]
      LifetimePath.exitTime U := by
    filter_upwards [ae_restrict_mem hS] with w hw
    show (if (t : ℝ≥0∞) < LifetimePath.exitTime U w then LifetimePath.exitTime U w
      else LifetimePath.exitTime U (LifetimePath.shift t w)) = LifetimePath.exitTime U w
    have hw' : (t : ℝ≥0∞) < LifetimePath.exitTime U w := hw
    rw [if_pos hw']
  have step1 : (∫⁻ w in {w : Path d | (t : ℝ≥0∞) < LifetimePath.exitTime U w},
      LifetimePath.exitTime U (LifetimePath.shift t w) ∂law x) ≤
      ∫⁻ w, (if (t : ℝ≥0∞) < LifetimePath.exitTime U w then LifetimePath.exitTime U w
        else LifetimePath.exitTime U (LifetimePath.shift t w)) ∂((law x).restrict
        {w : Path d | (t : ℝ≥0∞) < LifetimePath.exitTime U w}) := by
    refine lintegral_mono ?_
    intro w
    show LifetimePath.exitTime U (LifetimePath.shift t w) ≤
      (if (t : ℝ≥0∞) < LifetimePath.exitTime U w then LifetimePath.exitTime U w
        else LifetimePath.exitTime U (LifetimePath.shift t w))
    by_cases hw : (t : ℝ≥0∞) < LifetimePath.exitTime U w
    · rw [if_pos hw]
      exact key w hw
    · rw [if_neg hw]
  have key2 : (∫⁻ w in {w : Path d | (t : ℝ≥0∞) < LifetimePath.exitTime U w},
      LifetimePath.exitTime U (LifetimePath.shift t w) ∂law x) ≤
      (∫⁻ w in {w : Path d | (t : ℝ≥0∞) < LifetimePath.exitTime U w},
        LifetimePath.exitTime U w ∂law x) :=
    le_trans step1 (le_of_eq (lintegral_congr_ae hae))
  calc ∫⁻ y, meanExit law U y ∂killedKernel law U hU t x
      = ∫⁻ w in {w : Path d | (t : ℝ≥0∞) < LifetimePath.exitTime U w},
          meanExit law U (position t w) ∂law x :=
        lintegral_killed law U hU t x (meanExit law U) hmeas
    _ = ∫⁻ w in {w : Path d | (t : ℝ≥0∞) < LifetimePath.exitTime U w},
          LifetimePath.exitTime U (LifetimePath.shift t w) ∂law x :=
        (localTorsion_markov_restart law hM U hU x t).symm
    _ ≤ ∫⁻ w in {w : Path d | (t : ℝ≥0∞) < LifetimePath.exitTime U w},
          LifetimePath.exitTime U w ∂law x := key2
    _ ≤ ∫⁻ w, LifetimePath.exitTime U w ∂law x :=
        setLIntegral_le_lintegral _ _
    _ = meanExit law U x := rfl

/-- A bounded continuous nonnegative lower bound transfers from almost everywhere to every point. -/
theorem goodCube_meanExit_ge_continuous_of_ae {d : ℕ}
    {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusionData c rho law) {U : Set (Vec d)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (g : Vec d →ᵇ ℝ) (hg : ∀ y, 0 ≤ g y)
    (hlower : ∀ᵐ y ∂(weightedMeasure rho).restrict U,
      ENNReal.ofReal (g y) ≤ meanExit law U y) :
    ∀ x ∈ U, ENNReal.ofReal (g x) ≤ meanExit law U x := by
  obtain ⟨p, hpk, -⟩ := hD.2 U hU hUb
  have hM : StrongMarkov law := hD.1.1
  haveI hmk : IsMarkovKernel law := isMarkovKernel_of_localDiffusion hD.1
  have hbound : ∀ t : ℝ, 0 < t → ∀ x ∈ U,
      ENNReal.ofReal (kernelIntegral (killedKernel law U hU (Real.toNNReal t)) g x)
        ≤ meanExit law U x := by
    intro t ht x hx
    have habs : killedKernel law U hU (Real.toNNReal t) x
        ≪ (weightedMeasure rho).restrict U := by
      rw [SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower.killedKernel_eq_withDensity
        hU hpk ht hx]
      exact withDensity_absolutelyContinuous _ _
    have hae : (fun y : Vec d => ENNReal.ofReal (g y)) ≤ᵐ[killedKernel law U hU
        (Real.toNNReal t) x] fun y => meanExit law U y := habs.ae_le hlower
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
      _ ≤ ∫⁻ y, meanExit law U y ∂(killedKernel law U hU (Real.toNNReal t) x) :=
          lintegral_mono_ae hae
      _ ≤ meanExit law U x :=
          goodCube_lintegral_meanExit_killed_le law hM U hU (Real.toNNReal t) x
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
      (kernelIntegral (killedKernel law U hU (Real.toNNReal 0)) g x) ≤ meanExit law U x := by
    refine le_of_tendsto hten ?_
    have hmem : (Set.Ioi (0:ℝ)) ∈ (𝓝 0 ⊓ 𝓟 (Set.Ioi 0) : Filter ℝ) :=
      Filter.mem_inf_of_right (Filter.mem_principal_self _)
    filter_upwards [hmem] with r hr
    exact hbound r hr x hx
  rw [Real.toNNReal_zero, goodCube_killedKernel_integral_zero_of_start law hM U hU g
    g.continuous.measurable hx] at hle
  exact hle

/-- An almost-everywhere constant lower bound on an open interior set holds at every point there. -/
theorem goodCube_meanExit_lower_of_ae_on_open {d : ℕ}
    {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusionData c rho law) {U W : Set (Vec d)}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hW : IsOpen W) (hWU : W ⊆ U) {k : ℝ} (hk : 0 ≤ k)
    (hlower : ∀ᵐ y ∂(weightedMeasure rho).restrict U,
      y ∈ W → ENNReal.ofReal k ≤ meanExit law U y) :
    ∀ x ∈ W, ENNReal.ofReal k ≤ meanExit law U x := by
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
      ENNReal.ofReal (g y) ≤ meanExit law U y := by
    filter_upwards [hlower] with y hy
    by_cases hyW : y ∈ W
    · calc ENNReal.ofReal (g y) ≤ ENNReal.ofReal k :=
        ENNReal.ofReal_le_ofReal (hgle y)
      _ ≤ meanExit law U y := hy hyW
    · have hfy : f y = 0 := hf0 hyW
      have hgy0 : g y = 0 := by rw [hgy, hfy]; ring
      rw [hgy0]
      simp
  have hres := goodCube_meanExit_ge_continuous_of_ae hD hU hUb g hgnn hae x (hWU hx)
  have hgx : g x = k := by
    have hfx : f x = 1 := hf1 (Set.mem_singleton x)
    rw [hgy, hfx, mul_one]
  rw [hgx] at hres
  exact hres

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
