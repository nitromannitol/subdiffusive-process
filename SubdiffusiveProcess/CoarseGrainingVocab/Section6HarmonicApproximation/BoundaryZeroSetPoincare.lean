module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.ScaledPoincare

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem volumeMeasureOn_eq_restrict (U : Set (Vec d)) :
    volumeMeasureOn U = volume.restrict U := rfl

private theorem enorm_average_mul_le {A E : Set (Vec d)} (u : Vec d → ℝ)
    (hEsub : E ⊆ A) (hEmeas : MeasurableSet E) (hE0 : volume E ≠ 0) {a : ℝ}
    (hzero : ∀ y ∈ E, u y = 0) :
    ‖a‖ₑ * volume E ^ (1 / 2 : ℝ) ≤
      eLpNorm (fun x => u x - a) 2 (volume.restrict A) := by
  have hrestr : volume.restrict E ≠ 0 := by
    intro h
    exact hE0 (by simpa using congrArg (fun μ => μ E) h)
  have hae : (fun x => u x - a) =ᵐ[volume.restrict E] (fun _ => -a) := by
    refine (ae_restrict_iff' hEmeas).2 ?_
    filter_upwards with x hx
    rw [hzero x hx, zero_sub]
  have hcongr : eLpNorm (fun x => u x - a) 2 (volume.restrict E) =
      eLpNorm (fun _ : Vec d => -a) 2 (volume.restrict E) :=
    eLpNorm_congr_ae hae
  have hconst : eLpNorm (fun _ : Vec d => -a) 2 (volume.restrict E) =
      ‖a‖ₑ * volume E ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_const (-a) (by norm_num) hrestr, Measure.restrict_apply_univ,
      enorm_neg]
    norm_num
  have hmono : eLpNorm (fun x => u x - a) 2 (volume.restrict E) ≤
      eLpNorm (fun x => u x - a) 2 (volume.restrict A) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hEsub le_rfl)
  rw [← hconst, ← hcongr]
  exact hmono

private theorem eLpNorm_le_of_zeroSet_of_meanZeroBound {U E : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] {K C S : ℝ} (u : H1Function U)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hS : 0 ≤ S) (hEsub : E ⊆ U)
    (hEmeas : MeasurableSet E) (hzero : ∀ y ∈ E, u.toFun y = 0)
    (hvol : volume U ≤ ENNReal.ofReal K * volume E)
    (hmeanZero : (eLpNorm u.subAverage.toFun 2 (volumeMeasureOn U)).toReal ≤
      C * S) :
    (eLpNorm u.toFun 2 (volumeMeasureOn U)).toReal ≤
      (1 + Real.sqrt K) * C * S := by
  classical
  have hsqrtK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg K
  have hone : 0 ≤ 1 + Real.sqrt K := by linarith only [hsqrtK]
  have hsubfun : u.subAverage.toFun =
      fun x => u.toFun x - integralAverage U u.toFun := by
    funext x
    exact H1Function.subAverage_apply u x
  rw [hsubfun] at hmeanZero
  by_cases hU0 : volume U = 0
  · have hzeroμ : volumeMeasureOn U = 0 := by
      rw [volumeMeasureOn_eq_restrict]
      exact Measure.restrict_eq_zero.2 hU0
    rw [hzeroμ, eLpNorm_measure_zero, ENNReal.toReal_zero]
    exact mul_nonneg (mul_nonneg hone hC) hS
  · have hE0 : volume E ≠ 0 := by
      intro h
      exact hU0 (le_antisymm (by simpa [h] using hvol) zero_le)
    have hrestrU : volume.restrict U ≠ 0 := by
      intro h
      exact hU0 (by simpa using congrArg (fun μ => μ U) h)
    have hmem : MemLp (fun x => u.toFun x - integralAverage U u.toFun) 2
        (volume.restrict U) := by
      have h := u.subAverage.memL2
      rwa [hsubfun] at h
    have hNtop : eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
        (volume.restrict U) ≠ ⊤ := hmem.ne
    have hmean := enorm_average_mul_le (A := U) (E := E) u.toFun hEsub hEmeas hE0
      (a := integralAverage U u.toFun) hzero
    have hratio : volume U ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (Real.sqrt K) * volume E ^ (1 / 2 : ℝ) := by
      have h1 : volume U ^ (1 / 2 : ℝ) ≤
          (ENNReal.ofReal K * volume E) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hvol (by norm_num)
      rwa [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ENNReal.ofReal_rpow_of_nonneg hK (by norm_num : (0 : ℝ) ≤ 1 / 2),
        ← Real.sqrt_eq_rpow] at h1
    have hbig : ‖integralAverage U u.toFun‖ₑ * volume U ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (Real.sqrt K) *
          eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
            (volume.restrict U) := by
      calc
        ‖integralAverage U u.toFun‖ₑ * volume U ^ (1 / 2 : ℝ) ≤
            ‖integralAverage U u.toFun‖ₑ *
              (ENNReal.ofReal (Real.sqrt K) * volume E ^ (1 / 2 : ℝ)) :=
          mul_le_mul' le_rfl hratio
        _ = ENNReal.ofReal (Real.sqrt K) *
              (‖integralAverage U u.toFun‖ₑ * volume E ^ (1 / 2 : ℝ)) := by ring
        _ ≤ ENNReal.ofReal (Real.sqrt K) *
              eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
                (volume.restrict U) := mul_le_mul' le_rfl hmean
    have hconstU : eLpNorm (fun _ : Vec d => integralAverage U u.toFun) 2
        (volume.restrict U) =
        ‖integralAverage U u.toFun‖ₑ * volume U ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_const _ (by norm_num) hrestrU, Measure.restrict_apply_univ]
      norm_num
    have htri : eLpNorm u.toFun 2 (volume.restrict U) ≤
        eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
            (volume.restrict U) +
          ‖integralAverage U u.toFun‖ₑ * volume U ^ (1 / 2 : ℝ) := by
      have hadd := eLpNorm_add_le (p := 2) (μ := volume.restrict U)
        (f := fun x => u.toFun x - integralAverage U u.toFun)
        (g := fun _ => integralAverage U u.toFun) (by norm_num)
      rw [hconstU] at hadd
      calc
        eLpNorm u.toFun 2 (volume.restrict U) =
            eLpNorm ((fun x => u.toFun x - integralAverage U u.toFun) +
              (fun _ : Vec d => integralAverage U u.toFun)) 2
              (volume.restrict U) := by
                congr 1
                funext x
                simp
        _ ≤ _ := hadd
    have hchain : eLpNorm u.toFun 2 (volume.restrict U) ≤
        (1 + ENNReal.ofReal (Real.sqrt K)) *
          eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
            (volume.restrict U) := by
      refine htri.trans ?_
      rw [add_mul, one_mul]
      exact add_le_add le_rfl hbig
    have hRtop : (1 + ENNReal.ofReal (Real.sqrt K)) *
        eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
          (volume.restrict U) ≠ ⊤ :=
      ENNReal.mul_ne_top
        (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩) hNtop
    have hreal : (eLpNorm u.toFun 2 (volume.restrict U)).toReal ≤
        (1 + Real.sqrt K) *
          (eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
            (volume.restrict U)).toReal := by
      have h := ENNReal.toReal_mono hRtop hchain
      rwa [ENNReal.toReal_mul, ENNReal.toReal_add ENNReal.one_ne_top
        ENNReal.ofReal_ne_top, ENNReal.toReal_one,
        ENNReal.toReal_ofReal hsqrtK] at h
    rw [volumeMeasureOn_eq_restrict]
    refine hreal.trans ?_
    rw [volumeMeasureOn_eq_restrict] at hmeanZero
    calc
      (1 + Real.sqrt K) *
          (eLpNorm (fun x => u.toFun x - integralAverage U u.toFun) 2
            (volume.restrict U)).toReal ≤
          (1 + Real.sqrt K) * (C * S) :=
        mul_le_mul_of_nonneg_left hmeanZero hone
      _ = (1 + Real.sqrt K) * C * S := by ring

/-- Zero-set Poincare on an axis cube. -/
theorem eLpNorm_le_of_zeroSet_of_volume_le (z : Vec d) {L K : ℝ} (hL : 0 < L)
    (hK : 0 ≤ K) (u : H1Function (axisCube z L)) {E : Set (Vec d)}
    (hEsub : E ⊆ axisCube z L) (hEmeas : MeasurableSet E)
    (hzero : ∀ y ∈ E, u.toFun y = 0)
    (hvol : volume (axisCube z L) ≤ ENNReal.ofReal K * volume E) :
    (eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L))).toReal ≤
      (1 + Real.sqrt K) * (unitMeanZeroPoincareConst d * L) *
        ∑ i : Fin d,
          (eLpNorm (fun x => u.grad x i) 2
            (volumeMeasureOn (axisCube z L))).toReal := by
  refine eLpNorm_le_of_zeroSet_of_meanZeroBound (K := K)
    (C := unitMeanZeroPoincareConst d * L)
    (S := ∑ i : Fin d,
      (eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal)
    u hK (mul_nonneg (unitMeanZeroPoincareConst_nonneg d) hL.le)
    (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg) hEsub hEmeas hzero hvol ?_
  exact scaled_meanZero_poincare (d := d) z hL u

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
