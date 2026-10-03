module

public import SubdiffusiveProcess.Section10.PhysicalTightnessAssembly
public import SubdiffusiveProcess.Model.LifetimeProcess
public import MarkovProcess.Path.RandomShiftMeasurability
public import MarkovProcess.Path.ExitTimeShift

@[expose] public section




open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal
noncomputable section
namespace SubdiffusiveProcess.Section10.PhysicalExitChaining

open Classical

theorem strongMarkov_transport {d : ℕ}
    (K : Vec d → Measure (ContinuousPath (Vec d)))
    (L : Kernel (Vec d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (K z) = L z)
    (hSM : StrongMarkov L)
    (x : Vec d) (T : Path d → ℝ≥0∞)
    (hT : IsStoppingTime LifetimePath.canonicalFiltration T)
    (B : Set (Path d)) (hB : MeasurableSet[hT.measurableSpace] B)
    (g : Path d → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ p in LifetimePath.ofContinuousPath ⁻¹' (B ∩ {w | T w < w.lifetime}),
        g (LifetimePath.ofContinuousPath
          (ContinuousPath.shift (T (LifetimePath.ofContinuousPath p)).toNNReal p)) ∂K x =
      ∫⁻ p in LifetimePath.ofContinuousPath ⁻¹' (B ∩ {w | T w < w.lifetime}),
        (∫⁻ q, g (LifetimePath.ofContinuousPath q)
          ∂K (p (T (LifetimePath.ofContinuousPath p)).toNNReal)) ∂K x := by
  haveI : BorelSpace (MarkovProcess.Cemetery (Vec d)) :=
    SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  have hemb := LifetimePath.measurableEmbedding_ofContinuousPath (α := Vec d)
  have hTm : Measurable T := by simpa using! hT.measurable'
  have hS : MeasurableSet (B ∩ {w : Path d | T w < w.lifetime}) :=
    (hT.measurableSpace_le _ hB).inter
      (measurableSet_lt hTm LifetimePath.measurable_lifetime)
  have h := hSM.2.2 x T hT B hB g hg
  rw [← hL x, Measure.restrict_map hemb.measurable hS, hemb.lintegral_map,
    hemb.lintegral_map] at h
  simp only [SubdiffusiveProcess.Model.LifetimeProcess.shift_ofContinuousPath,
    SubdiffusiveProcess.Model.LifetimeProcess.position_ofContinuousPath] at h
  rw [h]
  refine setLIntegral_congr_fun_ae (hemb.measurable hS) (ae_of_all _ fun p _ => ?_)
  rw [← hL, hemb.lintegral_map]

/-- Random time shift by a measurable time is measurable on path space. -/

theorem measurable_randomShift {d : ℕ}
    (τ : ContinuousPath (Vec d) → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun p : ContinuousPath (Vec d) => ContinuousPath.shift (τ p) p) :=
  ContinuousPath.continuous_shift.measurable.comp (hτ.prodMk measurable_id)

theorem strongMarkov_weighted_restart {d : ℕ}
    (k : Kernel (Vec d) (ContinuousPath (Vec d)))
    (L : Kernel (Vec d) (Path d))
    (hL : ∀ z, Measure.map LifetimePath.ofContinuousPath (k z) = L z)
    (hSM : StrongMarkov L)
    (U : Set (Vec d)) (hU : IsOpen U) (x : Vec d)
    (W : ContinuousPath (Vec d) → ℝ≥0∞)
    (hW : Measurable[MeasurableSpace.comap LifetimePath.ofContinuousPath
      (LifetimePath.isStoppingTime_exitTime (alpha := Vec d) U hU).measurableSpace] W)
    (g : ContinuousPath (Vec d) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ p in {p | ContinuousPath.exitTime U p < ⊤},
        W p * g (ContinuousPath.shift (ContinuousPath.exitTime U p).toNNReal p) ∂k x =
      ∫⁻ p in {p | ContinuousPath.exitTime U p < ⊤},
        W p * ∫⁻ q, g q ∂k (p (ContinuousPath.exitTime U p).toNNReal) ∂k x := by
  classical
  haveI : BorelSpace (MarkovProcess.Cemetery (Vec d)) :=
    SubdiffusiveProcess.Model.LifetimeProcess.borelSpace_sum
  have hemb := LifetimePath.measurableEmbedding_ofContinuousPath (α := Vec d)
  set hT := LifetimePath.isStoppingTime_exitTime (alpha := Vec d) U hU with hTdef
  set f := LifetimePath.ofContinuousPath (α := Vec d) with hfdef
  set τ : ContinuousPath (Vec d) → ℝ≥0∞ := ContinuousPath.exitTime U with hτdef
  set S : Set (ContinuousPath (Vec d)) := {p | τ p < ⊤} with hSdef
  have hm : MeasurableSpace.comap f hT.measurableSpace ≤
      (inferInstance : MeasurableSpace (ContinuousPath (Vec d))) :=
    (MeasurableSpace.comap_mono hT.measurableSpace_le).trans hemb.measurable.comap_le
  set g' : Path d → ℝ≥0∞ := Function.extend f g (fun _ => 0) with hg'def
  have hg' : Measurable g' := hemb.measurable_extend hg measurable_const
  have hg'f : ∀ p, g' (LifetimePath.ofContinuousPath p) = g p := fun p =>
    hemb.injective.extend_apply _ _ p
  have hτmeas : Measurable τ := ContinuousPath.measurable_exitTime U hU
  have hτnn : Measurable fun p => (τ p).toNNReal := ENNReal.measurable_toNNReal.comp hτmeas
  set F : ContinuousPath (Vec d) → ℝ≥0∞ :=
    fun p => g (ContinuousPath.shift (τ p).toNNReal p) with hFdef
  set G : ContinuousPath (Vec d) → ℝ≥0∞ :=
    fun p => ∫⁻ q, g q ∂k (p (τ p).toNNReal) with hGdef
  have hF : Measurable F := hg.comp (measurable_randomShift _ hτnn)
  have hG : Measurable G :=
    (hg.lintegral_kernel (κ := k)).comp (ContinuousPath.measurable_eval_of_measurable _ hτnn)
  have hSm : MeasurableSet S := measurableSet_lt hτmeas measurable_const
  have hid : ∀ A, MeasurableSet[MeasurableSpace.comap f hT.measurableSpace] A → ∫⁻ p in A ∩ S, F p ∂k x = ∫⁻ p in A ∩ S, G p ∂k x := by
    rintro A ⟨B, hB, rfl⟩
    have h := strongMarkov_transport (fun z => k z) L hL hSM x _ hT B hB g' hg'
    have hpre : f ⁻¹' (B ∩ {w | LifetimePath.exitTime U w < w.lifetime}) = f ⁻¹' B ∩ S := by
      ext p
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, hfdef, hSdef, hτdef,
        LifetimePath.exitTime_ofContinuousPath, LifetimePath.lifetime_ofContinuousPath]
    rw [hpre] at h
    simp only [hfdef, LifetimePath.exitTime_ofContinuousPath] at h
    simp only [hg'f] at h
    exact h
  have hWm : Measurable W := hW.mono hm le_rfl
  have e1 : ∫⁻ p in S, W p * F p ∂k x = ∫⁻ p, W p ∂(((k x).restrict S).withDensity F) := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hF hWm]
    refine lintegral_congr fun p => ?_
    simp only [Pi.mul_apply]
    ring
  have e2 : ∫⁻ p in S, W p * G p ∂k x = ∫⁻ p, W p ∂(((k x).restrict S).withDensity G) := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hG hWm]
    refine lintegral_congr fun p => ?_
    simp only [Pi.mul_apply]
    ring
  have htrim : (((k x).restrict S).withDensity F).trim hm =
      (((k x).restrict S).withDensity G).trim hm := by
    refine @Measure.ext _ (MeasurableSpace.comap f hT.measurableSpace) _ _ fun A hA => ?_
    rw [trim_measurableSet_eq hm hA, trim_measurableSet_eq hm hA,
      withDensity_apply _ (hm _ hA), withDensity_apply _ (hm _ hA),
      Measure.restrict_restrict (hm _ hA)]
    exact hid A hA
  change ∫⁻ p in S, W p * F p ∂k x = ∫⁻ p in S, W p * G p ∂k x
  rw [e1, e2, ← lintegral_trim hm hW, ← lintegral_trim hm hW, htrim]

/-- Exit from the ball centred at the path's initial position. -/

def localExit {d : ℕ} (ρ : ℝ) (p : ContinuousPath (Vec d)) : ℝ≥0∞ :=
  ContinuousPath.exitTime (Metric.ball (p 0) ρ) p

def stoppedLocalExit {d : ℕ} (C : Set (Vec d)) (ρ : ℝ)
    (p : ContinuousPath (Vec d)) : ℝ≥0∞ :=
  if p 0 ∈ C then localExit ρ p else ⊤

/-- Successive exit epochs: `σ₀ = 0`, `σ_{j+1} = σ_j + τ̃ ∘ θ_{σ_j}` (`⊤` absorbs). -/

def exitEpoch {d : ℕ} (C : Set (Vec d)) (ρ : ℝ) :
    ℕ → ContinuousPath (Vec d) → ℝ≥0∞
  | 0, _ => 0
  | j + 1, p => exitEpoch C ρ j p + stoppedLocalExit C ρ
        (ContinuousPath.shift (exitEpoch C ρ j p).toNNReal p)

theorem localExit_eq {d : ℕ} (ρ : ℝ) (p : ContinuousPath (Vec d)) :
    localExit ρ p = ContinuousPath.exitTime (Metric.ball 0 ρ)
      (p - ContinuousMap.const ℝ≥0 (p 0)) := by
  unfold localExit ContinuousPath.exitTime
  congr 1
  ext s
  simp only [Set.mem_setOf_eq, Metric.mem_ball, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, dist_eq_norm, sub_zero]

theorem measurable_localExit {d : ℕ} (ρ : ℝ) :
    Measurable (localExit (d := d) ρ) := by
  have hΔ : Continuous (fun p : ContinuousPath (Vec d) => p - ContinuousMap.const ℝ≥0 (p 0)) :=
    continuous_id.sub (ContinuousMap.continuous_const'.comp (ContinuousPath.continuous_eval 0))
  have h := (ContinuousPath.measurable_exitTime (Metric.ball (0 : Vec d) ρ)
    Metric.isOpen_ball).comp hΔ.measurable
  have heq : localExit (d := d) ρ =
      (ContinuousPath.exitTime (Metric.ball (0 : Vec d) ρ)) ∘
        (fun p : ContinuousPath (Vec d) => p - ContinuousMap.const ℝ≥0 (p 0)) := by
    funext p; exact localExit_eq ρ p
  rw [heq]; exact h

theorem measurable_stoppedLocalExit {d : ℕ} (C : Set (Vec d))
    (hC : MeasurableSet C) (ρ : ℝ) :
    Measurable (stoppedLocalExit C ρ) := by
  classical
  unfold stoppedLocalExit
  exact Measurable.ite (hC.preimage (ContinuousPath.continuous_eval 0).measurable)
    (measurable_localExit ρ) measurable_const

theorem measurable_exitEpoch {d : ℕ} (C : Set (Vec d))
    (hC : MeasurableSet C) (ρ : ℝ) (j : ℕ) :
    Measurable (exitEpoch C ρ j) := by
  classical
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have hs : Measurable (fun p : ContinuousPath (Vec d) => ContinuousPath.shift
        (exitEpoch C ρ j p).toNNReal p) :=
      measurable_randomShift _ (ENNReal.measurable_toNNReal.comp ih)
    exact ih.add ((measurable_stoppedLocalExit C hC ρ).comp hs)

theorem exitEpoch_zero {d : ℕ} (C : Set (Vec d)) (ρ : ℝ)
    (p : ContinuousPath (Vec d)) : exitEpoch C ρ 0 p = 0 := rfl

theorem exitEpoch_succ {d : ℕ} (C : Set (Vec d)) (ρ : ℝ)
    (j : ℕ) (p : ContinuousPath (Vec d)) :
    exitEpoch C ρ (j + 1) p = exitEpoch C ρ j p +
      stoppedLocalExit C ρ
        (ContinuousPath.shift (exitEpoch C ρ j p).toNNReal p) := rfl

theorem exitEpoch_succ_top {d : ℕ} (C : Set (Vec d))
    (ρ : ℝ) (j : ℕ) (p : ContinuousPath (Vec d)) (hj : exitEpoch C ρ j p = ⊤) :
    exitEpoch C ρ (j + 1) p = ⊤ := by
  rw [exitEpoch_succ, hj, top_add]

theorem exitEpoch_mono_succ {d : ℕ} (C : Set (Vec d))
    (ρ : ℝ) (j : ℕ) (p : ContinuousPath (Vec d)) :
    exitEpoch C ρ j p ≤ exitEpoch C ρ (j + 1) p := by
  rw [exitEpoch_succ]; exact le_self_add

/-- **Front recursion** for the successive exit epochs. -/

theorem exitEpoch_front {d : ℕ} (C : Set (Vec d))
    (ρ : ℝ) (j : ℕ) (p : ContinuousPath (Vec d)) (ha : stoppedLocalExit C ρ p ≠ ⊤) :
    exitEpoch C ρ (j + 1) p = stoppedLocalExit C ρ p +
      exitEpoch C ρ j
        (ContinuousPath.shift (stoppedLocalExit C ρ p).toNNReal p) := by
  induction j generalizing p with
  | zero =>
    rw [exitEpoch_succ]
    simp [exitEpoch_zero, ContinuousPath.shift_zero]
  | succ j ih =>
    set a := stoppedLocalExit C ρ p with hadef
    set q := ContinuousPath.shift a.toNNReal p with hqdef
    have hIH := ih p ha
    by_cases hb : exitEpoch C ρ j q = ⊤
    · have h1 : exitEpoch C ρ (j + 1) p = ⊤ := by
        rw [hIH, hb, add_top]
      rw [exitEpoch_succ_top C ρ (j + 1) p h1,
        exitEpoch_succ_top C ρ j q hb, add_top]
    · have hne : exitEpoch C ρ (j + 1) p ≠ ⊤ := by
        rw [hIH]; exact ENNReal.add_ne_top.mpr ⟨ha, hb⟩
      rw [exitEpoch_succ C ρ (j + 1) p,
        exitEpoch_succ C ρ j q, hIH, add_assoc]
      congr 2
      rw [hqdef, ContinuousPath.shift_add, ENNReal.toNNReal_add ha hb]

theorem exitEpoch_one {d : ℕ} (C : Set (Vec d)) (ρ : ℝ)
    (p : ContinuousPath (Vec d)) :
    exitEpoch C ρ 1 p = stoppedLocalExit C ρ p := by
  rw [exitEpoch_succ, exitEpoch_zero, zero_add]
  simp [ContinuousPath.shift_zero]

theorem exitEpoch_mono {d : ℕ} (C : Set (Vec d)) (ρ : ℝ)
    (p : ContinuousPath (Vec d)) : Monotone (fun j => exitEpoch C ρ j p) :=
  monotone_nat_of_le_succ fun j => exitEpoch_mono_succ C ρ j p

theorem exitEpoch_succ_eq_top {d : ℕ} (C : Set (Vec d))
    (ρ : ℝ) (j : ℕ) (p : ContinuousPath (Vec d)) (ha : stoppedLocalExit C ρ p = ⊤) :
    exitEpoch C ρ (j + 1) p = ⊤ := by
  have h1 : exitEpoch C ρ 1 p ≤ exitEpoch C ρ (j + 1) p :=
    exitEpoch_mono C ρ p (by omega)
  rw [exitEpoch_one, ha] at h1
  exact top_le_iff.mp h1

/-- Exponential weight `e^{-s/h}` of an extended time, `0` at `⊤`. -/

def exitWeight (h : ℝ) (s : ℝ≥0∞) : ℝ≥0∞ :=
  if s = ⊤ then 0 else ENNReal.ofReal (Real.exp (-s.toReal / h))

theorem exitWeight_top (h : ℝ) : exitWeight h ⊤ = 0 := by
  simp [exitWeight]

theorem exitWeight_zero (h : ℝ) : exitWeight h 0 = 1 := by
  simp [exitWeight]

theorem exitWeight_add (h : ℝ) (a b : ℝ≥0∞) :
    exitWeight h (a + b) =
      exitWeight h a * exitWeight h b := by
  by_cases ha : a = ⊤
  · simp [ha, exitWeight_top]
  by_cases hb : b = ⊤
  · simp [hb, exitWeight_top]
  have hab : a + b ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ha, hb⟩
  simp only [exitWeight, if_neg ha, if_neg hb, if_neg hab]
  rw [ENNReal.toReal_add ha hb, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

theorem measurable_exitWeight (h : ℝ) :
    Measurable (exitWeight h) := by
  unfold exitWeight
  exact Measurable.ite (measurableSet_singleton ⊤) measurable_const
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (ENNReal.measurable_toReal.neg.div_const h)))

theorem exitWeight_le_one {h : ℝ} (hh : 0 < h) (s : ℝ≥0∞) :
    exitWeight h s ≤ 1 := by
  unfold exitWeight
  split_ifs
  · exact zero_le_one
  · rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_one_iff.mpr ?_)
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ENNReal.toReal_nonneg) hh.le

theorem exitWeight_le_split {h : ℝ} (hh : 0 < h) {h1 : ℝ} (hh1 : 0 ≤ h1)
    (s : ℝ≥0∞) :
    exitWeight h s ≤
      {s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1}.indicator 1 s + ENNReal.ofReal (Real.exp (-h1 / h)) := by
  by_cases hs : s ≤ ENNReal.ofReal h1
  · rw [Set.indicator_of_mem (show s ∈ {s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1} from hs), Pi.one_apply]
    exact (exitWeight_le_one hh s).trans le_self_add
  · rw [Set.indicator_of_notMem (show s ∉ {s : ℝ≥0∞ | s ≤ ENNReal.ofReal h1} from hs), zero_add]
    unfold exitWeight
    split_ifs with htop
    · exact zero_le
    · refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      rw [not_le] at hs
      have : h1 < s.toReal := by
        rw [← ENNReal.ofReal_lt_iff_lt_toReal hh1 htop]; exact hs
      exact div_le_div_of_nonneg_right (by linarith) hh.le

theorem exitWeight_ge {h : ℝ} (hh : 0 < h) {T : ℝ} (hT : 0 ≤ T) {s : ℝ≥0∞}
    (hs : s ≤ ENNReal.ofReal T) :
    ENNReal.ofReal (Real.exp (-T / h)) ≤ exitWeight h s := by
  have htop : s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
  unfold exitWeight
  rw [if_neg htop]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  have : s.toReal ≤ T := ENNReal.toReal_le_of_le_ofReal hT hs
  exact div_le_div_of_nonneg_right (by linarith) hh.le

theorem measurable_exitTime_stopped {d : ℕ}
    (U : Set (Vec d)) (hU : IsOpen U) :
    Measurable[(LifetimePath.isStoppingTime_exitTime (alpha := Vec d) U hU).measurableSpace]
      (LifetimePath.exitTime U : LifetimePath (Vec d) → ℝ≥0∞) := by
  refine measurable_of_Iic fun x => ?_
  induction x with
  | top =>
    have : (LifetimePath.exitTime U : LifetimePath (Vec d) → ℝ≥0∞) ⁻¹'
        Set.Iic ⊤ = Set.univ := by ext w; simp
    rw [this]; exact MeasurableSet.univ
  | coe t =>
    exact (LifetimePath.isStoppingTime_exitTime (alpha := Vec d) U hU).measurableSet_le' t

/-- Weights read off the exit time are measurable for the stopped σ-algebra trace. -/

theorem measurable_stopped_comp {d : ℕ}
    (U : Set (Vec d)) (hU : IsOpen U) (F : ℝ≥0∞ → ℝ≥0∞) (hF : Measurable F) :
    Measurable[MeasurableSpace.comap LifetimePath.ofContinuousPath
      (LifetimePath.isStoppingTime_exitTime (alpha := Vec d) U hU).measurableSpace]
      (fun p : ContinuousPath (Vec d) => F (ContinuousPath.exitTime U p)) := by
  have hc : Measurable[MeasurableSpace.comap LifetimePath.ofContinuousPath
      (LifetimePath.isStoppingTime_exitTime (alpha := Vec d) U hU).measurableSpace,
      (LifetimePath.isStoppingTime_exitTime (alpha := Vec d) U hU).measurableSpace]
      (LifetimePath.ofContinuousPath (α := Vec d)) := fun s hs => ⟨s, hs, rfl⟩
  have h := hF.comp ((measurable_exitTime_stopped U hU).comp hc)
  have heq : (fun p : ContinuousPath (Vec d) => F (ContinuousPath.exitTime U p)) =
      F ∘ (LifetimePath.exitTime U ∘ LifetimePath.ofContinuousPath) := by
    funext p; simp [LifetimePath.exitTime_ofContinuousPath]
  rw [heq]; exact h

theorem stoppedLocalExit_of_start {d : ℕ} (C : Set (Vec d))
    (ρ : ℝ) (p : ContinuousPath (Vec d)) (z : Vec d) (hp0 : p 0 = z) :
    stoppedLocalExit C ρ p =
      if z ∈ C then ContinuousPath.exitTime (Metric.ball z ρ) p else ⊤ := by
  classical
  unfold stoppedLocalExit localExit
  subst hp0
  rfl

end SubdiffusiveProcess.Section10.PhysicalExitChaining
