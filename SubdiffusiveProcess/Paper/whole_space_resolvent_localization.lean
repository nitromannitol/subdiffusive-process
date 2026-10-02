import SubdiffusiveProcess.Paper.in_crossing
import SubdiffusiveProcess.Main.CutoffSpeedMeasure
import MarkovProcess.Path.ExitTime
import MarkovProcess.Path.ExitTimeShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess
open scoped ENNReal NNReal

namespace Paper



theorem whole_space_resolvent_localization
    {d : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : Nat → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : Nat → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (N : Nat) (omega : BilateralField d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (x : SpatialCoordinates d)
    (hx : x ∈ (centeredCube z r hr : Set _))
    (lam : ℝ) (hlam : 0 < lam) (T : ℝ) (hT : 0 ≤ T)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (RN RQ : ℝ)
    (hRN : RN = ∫ path, (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
    (hRQ : RQ = ∫ path, (∫ t in Set.Ioi (0 : ℝ),
      Set.indicator
        {s : ℝ | ENNReal.ofReal s <
          ContinuousPath.exitTime (centeredCube z r hr : Set _) path}
        (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
      ∂(KN N (omega, x))) :
    |RN - RQ| ≤ (‖f‖ / lam) *
      (((KN N (omega, x)) {path |
        ContinuousPath.exitTime (centeredCube z r hr : Set _) path ≤
          ENNReal.ofReal T}).toReal + Real.exp (-lam * T)) := by
  let μ : Measure (DiffusionPath d) := KN N (omega, x)
  letI : IsProbabilityMeasure μ := (hKN N).isProbabilityMeasure (omega, x)
  have hU : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen
  have hfull_meas : StronglyMeasurable (fun p : ℝ × DiffusionPath d ↦
      Real.exp (-lam * p.1) * f (p.2 (Real.toNNReal p.1))) := by
    have heval : Measurable (fun p : ℝ × DiffusionPath d ↦
        p.2 (Real.toNNReal p.1)) :=
      (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
        ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
    exact (((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).measurable.mul
      (f.measurable.comp heval)).stronglyMeasurable)
  have hkill_meas : StronglyMeasurable (fun p : ℝ × DiffusionPath d ↦
      Real.exp (-lam * p.1) *
        {p : ℝ × DiffusionPath d |
          ENNReal.ofReal p.1 < ContinuousPath.exitTime
            (centeredCube z r hr : Set _) p.2}.indicator
        (fun p ↦ f (p.2 (Real.toNNReal p.1))) p) := by
    have heval : Measurable (fun p : ℝ × DiffusionPath d ↦
        p.2 (Real.toNNReal p.1)) :=
      (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
        ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
    have hset : MeasurableSet {p : ℝ × DiffusionPath d |
        ENNReal.ofReal p.1 < ContinuousPath.exitTime
          (centeredCube z r hr : Set _) p.2} :=
      let hτ : Measurable (ContinuousPath.exitTime
          (centeredCube z r hr : Set (SpatialCoordinates d)) :
          DiffusionPath d → ℝ≥0∞) :=
        ContinuousPath.measurable_exitTime (centeredCube z r hr : Set (SpatialCoordinates d)) hU
      measurableSet_lt
        (measurable_coe_nnreal_ennreal.comp
          (measurable_real_toNNReal.comp measurable_fst))
        (hτ.comp measurable_snd)
    exact (((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).measurable.mul
      ((f.measurable.comp heval).indicator hset)).stronglyMeasurable)
  have hfull_int : Integrable (fun p : ℝ × DiffusionPath d ↦
      Real.exp (-lam * p.1) * f (p.2 (Real.toNNReal p.1)))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ) := by
    have hdom : Integrable (fun p : ℝ × DiffusionPath d ↦
        ‖f‖ * Real.exp (-lam * p.1))
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ) := by
      have ht : Integrable (fun t : ℝ ↦ ‖f‖ * Real.exp (-lam * t))
          (volume.restrict (Set.Ioi (0 : ℝ))) :=
        (exp_neg_integrableOn_Ioi 0 hlam).const_mul ‖f‖
      have hp : Integrable (fun _ : DiffusionPath d ↦ (1 : ℝ)) μ :=
        integrable_const 1
      simpa only [mul_one] using ht.mul_prod hp
    apply hdom.mono' hfull_meas.aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-lam * p.1) * ‖f (p.2 (Real.toNNReal p.1))‖ ≤
          Real.exp (-lam * p.1) * ‖f‖ :=
        mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (Real.exp_pos _).le
      _ = ‖f‖ * Real.exp (-lam * p.1) := by ring
  have hkill_int : Integrable (fun p : ℝ × DiffusionPath d ↦
      Real.exp (-lam * p.1) *
        {p : ℝ × DiffusionPath d |
          ENNReal.ofReal p.1 < ContinuousPath.exitTime
            (centeredCube z r hr : Set _) p.2}.indicator
        (fun p ↦ f (p.2 (Real.toNNReal p.1))) p)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ) := by
    have hdom : Integrable (fun p : ℝ × DiffusionPath d ↦
        ‖f‖ * Real.exp (-lam * p.1))
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod μ) := by
      have ht : Integrable (fun t : ℝ ↦ ‖f‖ * Real.exp (-lam * t))
          (volume.restrict (Set.Ioi (0 : ℝ))) :=
        (exp_neg_integrableOn_Ioi 0 hlam).const_mul ‖f‖
      have hp : Integrable (fun _ : DiffusionPath d ↦ (1 : ℝ)) μ :=
        integrable_const 1
      simpa only [mul_one] using ht.mul_prod hp
    apply hdom.mono' hkill_meas.aestronglyMeasurable
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    by_cases hp : ENNReal.ofReal p.1 <
        ContinuousPath.exitTime (centeredCube z r hr : Set _) p.2
    · have hp' : p ∈ {p : ℝ × DiffusionPath d |
          ENNReal.ofReal p.1 < ContinuousPath.exitTime
            (centeredCube z r hr : Set _) p.2} := hp
      rw [Set.indicator_of_mem hp']
      calc
        Real.exp (-lam * p.1) * |f (p.2 (Real.toNNReal p.1))| =
            Real.exp (-lam * p.1) * ‖f (p.2 (Real.toNNReal p.1))‖ := by
              rw [Real.norm_eq_abs]
        _ ≤ Real.exp (-lam * p.1) * ‖f‖ :=
          mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _)
            (Real.exp_pos _).le
        _ = ‖f‖ * Real.exp (-lam * p.1) := by ring
    · have hp' : p ∉ {p : ℝ × DiffusionPath d |
          ENNReal.ofReal p.1 < ContinuousPath.exitTime
            (centeredCube z r hr : Set _) p.2} := hp
      rw [Set.indicator_of_notMem hp']
      simp only [abs_zero, mul_zero]
      exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hfull_outer : Integrable (fun path : DiffusionPath d ↦
      ∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-lam * t) * f (path (Real.toNNReal t))) μ := by
    simpa only [MeasureTheory.integral_smul_measure] using hfull_int.integral_prod_right
  have hkill_outer : Integrable (fun path : DiffusionPath d ↦
      ∫ t in Set.Ioi (0 : ℝ),
        Set.indicator
          {s : ℝ | ENNReal.ofReal s <
            ContinuousPath.exitTime (centeredCube z r hr : Set _) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t) μ := by
    refine hkill_int.integral_prod_right.congr ?_
    filter_upwards with path
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : ENNReal.ofReal t <
        ContinuousPath.exitTime (centeredCube z r hr : Set _) path
    · have htp : (t, path) ∈ {p : ℝ × DiffusionPath d |
          ENNReal.ofReal p.1 < ContinuousPath.exitTime
            (centeredCube z r hr : Set _) p.2} := ht
      have htt : t ∈ {s : ℝ | ENNReal.ofReal s <
          ContinuousPath.exitTime (centeredCube z r hr : Set _) path} := ht
      rw [Set.indicator_of_mem htp, Set.indicator_of_mem htt]
    · have htp : (t, path) ∉ {p : ℝ × DiffusionPath d |
          ENNReal.ofReal p.1 < ContinuousPath.exitTime
            (centeredCube z r hr : Set _) p.2} := ht
      have htt : t ∉ {s : ℝ | ENNReal.ofReal s <
          ContinuousPath.exitTime (centeredCube z r hr : Set _) path} := ht
      rw [Set.indicator_of_notMem htp, Set.indicator_of_notMem htt, mul_zero]
  have hpath_bound : ∀ path : DiffusionPath d,
      |(∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-lam * t) * f (path (Real.toNNReal t))) -
        (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s <
              ContinuousPath.exitTime (centeredCube z r hr : Set _) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)| ≤
      (‖f‖ / lam) *
        (if ContinuousPath.exitTime (centeredCube z r hr : Set _) path ≤
            ENNReal.ofReal T then 1 else Real.exp (-lam * T)) := by
    intro path
    let τ : ℝ≥0∞ := ContinuousPath.exitTime
      (centeredCube z r hr : Set (SpatialCoordinates d)) path
    let a : ℝ → ℝ := fun t ↦ Real.exp (-lam * t) * f (path (Real.toNNReal t))
    let S : Set ℝ := {t : ℝ | ENNReal.ofReal t < τ}
    have hpath_eval : Measurable (fun t : ℝ ↦ path (Real.toNNReal t)) := by
      exact (path.continuous.comp continuous_real_toNNReal).measurable
    have ha_meas : AEStronglyMeasurable a (volume.restrict (Set.Ioi (0 : ℝ))) := by
      have hmeas : Measurable a := by
        exact (Real.continuous_exp.measurable.comp
          (continuous_const.mul continuous_id).measurable).mul
          (f.measurable.comp hpath_eval)
      exact hmeas.aestronglyMeasurable
    have hS : MeasurableSet S := by
      exact measurableSet_lt
        (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal)
        measurable_const
    have ha_int : Integrable a (volume.restrict (Set.Ioi (0 : ℝ))) := by
      apply ((exp_neg_integrableOn_Ioi 0 hlam).mul_const ‖f‖).mono' ha_meas
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-lam * t) * ‖f (path (Real.toNNReal t))‖ ≤
            Real.exp (-lam * t) * ‖f‖ :=
          mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _)
            (Real.exp_pos _).le
        _ = Real.exp (-lam * t) * ‖f‖ := by ring
    have hkill_int_path : Integrable (S.indicator a)
        (volume.restrict (Set.Ioi (0 : ℝ))) := ha_int.indicator hS
    have hdiff_int : Integrable (a - S.indicator a)
        (volume.restrict (Set.Ioi (0 : ℝ))) := ha_int.sub hkill_int_path
    have hfull_norm (t : ℝ) : ‖a t‖ ≤ ‖f‖ * Real.exp (-lam * t) := by
      dsimp only [a]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-lam * t) * ‖f (path (Real.toNNReal t))‖ ≤
            Real.exp (-lam * t) * ‖f‖ :=
          mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _)
            (Real.exp_pos _).le
        _ = ‖f‖ * Real.exp (-lam * t) := by ring
    have hdiff_norm (t : ℝ) :
        ‖a t - S.indicator a t‖ ≤ ‖f‖ * Real.exp (-lam * t) := by
      by_cases htS : t ∈ S
      · rw [Set.indicator_of_mem htS, sub_self, norm_zero]
        exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
      · rw [Set.indicator_of_notMem htS, sub_zero]
        exact hfull_norm t
    have hfull_exp : ∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-lam * t) = lam⁻¹ :=
      MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero hlam
    have hfull_bound : ∫ t in Set.Ioi (0 : ℝ),
        ‖f‖ * Real.exp (-lam * t) = ‖f‖ / lam := by
      rw [integral_const_mul, hfull_exp, div_eq_mul_inv]
    have hdiff_eq : |(∫ t in Set.Ioi (0 : ℝ), a t) -
        ∫ t in Set.Ioi (0 : ℝ), S.indicator a t| =
        ‖∫ t in Set.Ioi (0 : ℝ), (a - S.indicator a) t‖ := by
      rw [← integral_sub ha_int hkill_int_path, Real.norm_eq_abs]
      simp only [Pi.sub_apply]
    have h_exp_tail (hT' : 0 ≤ T) :
        ∫ t in Set.Ioi T, Real.exp (-lam * t) =
          Real.exp (-lam * T) * lam⁻¹ := by
      have hshift :=
        (measurePreserving_add_right volume T).setIntegral_preimage_emb
          (measurableEmbedding_addRight T)
          (fun t : ℝ ↦ Real.exp (-lam * t)) (Set.Ioi T)
      have hpre : (fun t : ℝ ↦ t + T) ⁻¹' Set.Ioi T = Set.Ioi (0 : ℝ) := by
        ext t
        simp only [Set.mem_preimage, Set.mem_Ioi]
        constructor <;> intro ht
        · linarith
        · linarith
      rw [hpre] at hshift
      rw [← hshift]
      rw [setIntegral_congr_fun measurableSet_Ioi]
      · rw [integral_const_mul, hfull_exp]
      · intro t ht
        change Real.exp (-lam * (t + T)) =
          Real.exp (-lam * T) * Real.exp (-lam * t)
        rw [show -lam * (t + T) = (-lam * T) + (-lam * t) by ring,
          Real.exp_add]
    have htail_int : Integrable
        ((Set.Ioi T).indicator (fun t : ℝ ↦ ‖f‖ * Real.exp (-lam * t)))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      exact ((exp_neg_integrableOn_Ioi 0 hlam).const_mul ‖f‖).indicator
        measurableSet_Ioi
    have htail_bound : ∫ t in Set.Ioi (0 : ℝ),
        (Set.Ioi T).indicator (fun t : ℝ ↦ ‖f‖ * Real.exp (-lam * t)) t =
        (‖f‖ / lam) * Real.exp (-lam * T) := by
      rw [integral_indicator measurableSet_Ioi]
      rw [Measure.restrict_restrict measurableSet_Ioi]
      have hinter : Set.Ioi T ∩ Set.Ioi (0 : ℝ) = Set.Ioi T := by
        exact Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi hT)
      rw [hinter, integral_const_mul, h_exp_tail hT, div_eq_mul_inv]
      ring
    change |(∫ t in Set.Ioi (0 : ℝ), a t) -
        ∫ t in Set.Ioi (0 : ℝ), S.indicator a t| ≤
      (‖f‖ / lam) *
        (if τ ≤ ENNReal.ofReal T then 1 else Real.exp (-lam * T))
    by_cases hτ : τ ≤ ENNReal.ofReal T
    · simp only [if_pos hτ]
      rw [hdiff_eq]
      calc
        ‖∫ t in Set.Ioi (0 : ℝ), (a - S.indicator a) t‖ ≤
            ∫ t in Set.Ioi (0 : ℝ), ‖f‖ * Real.exp (-lam * t) := by
              apply norm_integral_le_of_norm_le
                ((exp_neg_integrableOn_Ioi 0 hlam).const_mul ‖f‖)
              filter_upwards with t
              exact hdiff_norm t
        _ = ‖f‖ / lam := hfull_bound
        _ = (‖f‖ / lam) * 1 := by ring
    · have hτ' : ENNReal.ofReal T < τ := lt_of_not_ge hτ
      simp only [if_neg hτ]
      rw [hdiff_eq]
      calc
        ‖∫ t in Set.Ioi (0 : ℝ), (a - S.indicator a) t‖ ≤
            ∫ t in Set.Ioi (0 : ℝ),
              (Set.Ioi T).indicator (fun t : ℝ ↦
                ‖f‖ * Real.exp (-lam * t)) t := by
              apply norm_integral_le_of_norm_le htail_int
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              by_cases htS : ENNReal.ofReal t < τ
              · have htS' : t ∈ S := htS
                change ‖a t - S.indicator a t‖ ≤ _
                rw [Set.indicator_of_mem htS']
                simp only [sub_self, norm_zero]
                by_cases hTt : t ∈ Set.Ioi T
                · rw [Set.indicator_of_mem hTt]
                  exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
                · rw [Set.indicator_of_notMem hTt]
              · have htS' : t ∉ S := htS
                change ‖a t - S.indicator a t‖ ≤ _
                rw [Set.indicator_of_notMem htS']
                have hle : τ ≤ ENNReal.ofReal t := le_of_not_gt htS
                have hltENN : ENNReal.ofReal T < ENNReal.ofReal t :=
                  hτ'.trans_le hle
                have htpos : 0 < t := ht
                have hTt : T < t := by
                  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hltENN
                rw [Set.indicator_of_mem (show t ∈ Set.Ioi T from hTt)]
                simpa only [sub_zero] using hfull_norm t
        _ = (‖f‖ / lam) * Real.exp (-lam * T) := htail_bound
  have houter_bound : ∫ path : DiffusionPath d,
      |(∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-lam * t) * f (path (Real.toNNReal t))) -
        (∫ t in Set.Ioi (0 : ℝ),
          Set.indicator
            {s : ℝ | ENNReal.ofReal s <
              ContinuousPath.exitTime (centeredCube z r hr : Set _) path}
            (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)| ∂μ ≤
      (‖f‖ / lam) *
        ((μ {path | ContinuousPath.exitTime (centeredCube z r hr : Set _) path ≤
            ENNReal.ofReal T}).toReal + Real.exp (-lam * T)) := by
    let E : Set (DiffusionPath d) := {path |
      ContinuousPath.exitTime (centeredCube z r hr : Set _) path ≤ ENNReal.ofReal T}
    have hE : MeasurableSet E := by
      have hτ : Measurable (ContinuousPath.exitTime
          (centeredCube z r hr : Set (SpatialCoordinates d)) :
          DiffusionPath d → ℝ≥0∞) :=
        ContinuousPath.measurable_exitTime (centeredCube z r hr : Set (SpatialCoordinates d)) hU
      exact measurableSet_le
        hτ
        measurable_const
    have hleft : Integrable (fun path : DiffusionPath d ↦
        |(∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-lam * t) * f (path (Real.toNNReal t))) -
          (∫ t in Set.Ioi (0 : ℝ),
            Set.indicator
              {s : ℝ | ENNReal.ofReal s <
                ContinuousPath.exitTime (centeredCube z r hr : Set _) path}
              (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)|) μ := by
      simpa only [Real.norm_eq_abs] using (hfull_outer.sub hkill_outer).abs
    have hright : Integrable (fun path : DiffusionPath d ↦
        (‖f‖ / lam) *
          (E.indicator (fun _ : DiffusionPath d ↦ (1 : ℝ)) path +
            Real.exp (-lam * T))) μ := by
      have hEi : Integrable (E.indicator (fun _ : DiffusionPath d ↦ (1 : ℝ))) μ :=
        (integrable_const 1).indicator hE
      exact hEi.add (integrable_const _ ) |>.const_mul _
    have hpoint : ∀ path : DiffusionPath d,
        |(∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-lam * t) * f (path (Real.toNNReal t))) -
          (∫ t in Set.Ioi (0 : ℝ),
            Set.indicator
              {s : ℝ | ENNReal.ofReal s <
                ContinuousPath.exitTime (centeredCube z r hr : Set _) path}
              (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)| ≤
        (‖f‖ / lam) *
          (E.indicator (fun _ : DiffusionPath d ↦ (1 : ℝ)) path +
            Real.exp (-lam * T)) := by
      intro path
      by_cases he : path ∈ E
      · have hp := hpath_bound path
        have he' : ContinuousPath.exitTime (centeredCube z r hr : Set _) path ≤
            ENNReal.ofReal T := by simpa only [E, Set.mem_setOf_eq] using he
        rw [if_pos he'] at hp
        rw [Set.indicator_of_mem he]
        calc
          _ ≤ (‖f‖ / lam) * 1 := by simpa using hp
          _ ≤ (‖f‖ / lam) * (1 + Real.exp (-lam * T)) := by
            gcongr
            linarith only [Real.exp_pos (-lam * T)]
      · have hp := hpath_bound path
        have he' : ¬ ContinuousPath.exitTime (centeredCube z r hr : Set _) path ≤
            ENNReal.ofReal T := by
          intro h
          exact he (by simpa only [E, Set.mem_setOf_eq] using h)
        rw [if_neg he'] at hp
        rw [Set.indicator_of_notMem he]
        simpa only [zero_add] using hp
    have hcalc : ∫ path : DiffusionPath d,
        (‖f‖ / lam) *
          (E.indicator (fun _ : DiffusionPath d ↦ (1 : ℝ)) path +
            Real.exp (-lam * T)) ∂μ =
        (‖f‖ / lam) * ((μ E).toReal + Real.exp (-lam * T)) := by
      have hEi : Integrable (E.indicator (fun _ : DiffusionPath d ↦ (1 : ℝ))) μ :=
        (integrable_const 1).indicator hE
      rw [integral_const_mul, integral_add hEi (integrable_const _),
        integral_indicator_const (1 : ℝ) hE, integral_const]
      simp only [smul_eq_mul, mul_one]
      have huniv : μ.real Set.univ = 1 := by
        rw [measureReal_def, IsProbabilityMeasure.measure_univ, ENNReal.toReal_one]
      rw [huniv]
      simp only [one_mul, measureReal_def]
    exact (integral_mono hleft hright hpoint).trans_eq hcalc
  rw [hRN, hRQ]
  rw [← integral_sub hfull_outer hkill_outer]
  exact (abs_integral_le_integral_abs.trans houter_bound)

end Paper
