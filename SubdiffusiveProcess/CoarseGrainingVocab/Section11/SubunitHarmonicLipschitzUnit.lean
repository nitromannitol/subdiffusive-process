module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitHarmonicLipschitzIteration

@[expose] public section

/-! Uniform gradient averages and a Lipschitz representative on the unit ball. -/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section11.HarmonicLipschitz
open MeasureTheory Homogenization Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
noncomputable section

theorem gradient_bound_of_dyadic {d : ℕ} [NeZero d]
 (z : Vec d) {R K : ℝ} (hR : 0 < R) {g : Vec d → Vec d}
 (hg : MemVectorL2 (euclideanBall z R) g)
 (hd : ∀ n : ℕ, vectorNormalizedL2On (euclideanBall z (smallContrastDyadicRadius R n)) g ≤ K) :
 ∀ s : ℝ, 0 < s → s ≤ R →
 vectorNormalizedL2On (euclideanBall z s) g ≤ (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) * K := by
  intro s hs hsR
  obtain ⟨n, hnlow, hnhigh⟩ :=
    exists_smallContrastDyadicRadius_bracket hR hs hsR
  let t : ℝ := smallContrastDyadicRadius R n
  have ht : 0 < t := smallContrastDyadicRadius_pos hR n
  have hst : s ≤ t := hnhigh
  have hts : t ≤ 2 * s := by
    have hsucc := smallContrastDyadicRadius_succ R n
    rw [hsucc] at hnlow
    linarith
  have hsub : euclideanBall z s ⊆ euclideanBall z t := by
    rcases eq_or_lt_of_le hst with heq | hlt
    · rw [heq]
    · exact euclideanBall_subset_euclideanBall hs.le hlt
  have htg : MemLp (fun x => HilbertVec.ofVec (g x)) 2
      (volume.restrict (euclideanBall z t)) := by
    have htR : t ≤ R := smallContrastDyadicRadius_le hR.le n
    have hsubTR : euclideanBall z t ⊆ euclideanBall z R := by
      rcases eq_or_lt_of_le htR with heq | hlt
      · rw [heq]
      · exact euclideanBall_subset_euclideanBall ht.le hlt
    exact (memHilbertVectorL2_hilbertifyVecField hg).mono_measure
      (Measure.restrict_mono hsubTR le_rfl)
  have hvolR : 0 < (volume (euclideanBall z t)).toReal := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero z ht))
  have hvols : 0 < (volume (euclideanBall z s)).toReal := by
    exact lt_of_le_of_ne ENNReal.toReal_nonneg
      (Ne.symm (Homogenization.Book.Ch01.volume_euclideanBall_toReal_ne_zero z hs))
  have hnorm := vectorNormalizedL2On_le_of_subset hsub hvolR hvols htg
  have hratio := sqrt_volume_ratio_euclideanBall_le_half_rpow z hs ht hst hts
  have hgnonneg : 0 ≤ vectorNormalizedL2On (euclideanBall z t) g := Real.sqrt_nonneg _
  have hnorm' : vectorNormalizedL2On (euclideanBall z s) g ≤
      (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) *
        vectorNormalizedL2On (euclideanBall z t) g :=
    hnorm.trans (mul_le_mul_of_nonneg_right hratio hgnonneg)
  exact hnorm'.trans (mul_le_mul_of_nonneg_left (hd n)
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) _))
theorem dyadic_gradient_bound_of_linear_contrast {d : ℕ} [NeZero d]
 {U : Set (Vec d)} (hU : IsOpen U) {s : Vec d → ℝ} (hs : ContinuousOn s U)
 {u : H1Function U} (hu : IsWeaklyHarmonicOn s U u)
 (z : Vec d) {D : ℝ} (hD : 0 ≤ D) (hDsmall : D ≤ smallContrastThreshold d (1/2:ℝ))
 (houter : euclideanBall z (1/2) ⊆ U)
 (hc : ∀ r : ℝ, 0 < r → r ≤ 1/2 → ∀ y ∈ euclideanBall z r,
 |(s z)⁻¹ * s y - 1| ≤ 2 * D * r) (n : ℕ) :
 vectorNormalizedL2On (euclideanBall z (smallContrastDyadicRadius (1/2) n)) u.grad ≤
 Real.exp (4 * (1/2:ℝ)^(-(d:ℝ)/2)) *
 vectorNormalizedL2On (euclideanBall z (1/2)) u.grad  := by
  let A : ℕ → ℝ := fun m => vectorNormalizedL2On
    (euclideanBall z (smallContrastDyadicRadius (1/2) m)) u.grad
  let q : ℝ := (1/2:ℝ)^(-(d:ℝ)/2)
  have hq : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hrec : ∀ m, A (m+1) ≤ (1+(2*D*q)*(1/2:ℝ)^m)*A m := by
    intro m
    let r : ℝ := smallContrastDyadicRadius (1/2) m
    have hr : 0 < r := smallContrastDyadicRadius_pos (by norm_num) m
    have hrh : r ≤ 1/2 := smallContrastDyadicRadius_le (by norm_num) m
    have hVU : euclideanBall z r ⊆ U := by
      rcases eq_or_lt_of_le hrh with heq | hlt
      · simpa only [heq] using! houter
      · exact (euclideanBall_subset_euclideanBall hr.le hlt).trans houter
    let uV := u.restrict (isOpen_euclideanBall z r) hVU
    have huV : IsWeaklyHarmonicOn s (euclideanBall z r) uV :=
      Section6BoundaryL2.isWeaklyHarmonicOn_restrict hU (isOpen_euclideanBall z r) hVU hu
    have hd := linear_dyadic_contrast_le hD hDsmall m
    have hd1 : D*(1/2:ℝ)^m < 1 := by
      linarith [smallContrastThreshold_half_le_sixteenth d]
    have hclose : ∀ y ∈ euclideanBall z r, |(s z)⁻¹*s y-1| ≤ D*(1/2:ℝ)^m := by
      intro y hy
      have hc0 := hc r hr hrh y hy
      have heq : 2*D*r = D*(1/2:ℝ)^m := by
        dsimp only [r, smallContrastDyadicRadius]
        rw [Real.rpow_natCast]
        ring
      rwa [heq] at hc0
    have hstep := oneStep_scalar_normalizedGradient_half hr (hs.mono hVU) huV
      hd.1 hd.2 hd1 hclose
    change A (m+1) ≤ _
    dsimp only [A]
    rw [smallContrastDyadicRadius_succ]
    dsimp only [uV, H1Function.restrict] at hstep
    convert hstep using 1
    dsimp only [r, q]
    ring
  have hraw := le_exp_of_dyadic_mul_recursion
    (a := A) (M := 2*D*q) (fun _ => Real.sqrt_nonneg _)
    (by positivity) hrec n
  have hDone : D ≤ 1 := by linarith [smallContrastThreshold_half_le_sixteenth d]
  have he : Real.exp (2*(2*D*q)) ≤ Real.exp (4*q) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hDone hq]
  have hfin := hraw.trans (mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg _))
  simpa only [A, q, smallContrastDyadicRadius_zero] using! hfin
theorem half_ball_gradient_le_global_lp {d : ℕ} [NeZero d]
  {u : H1Function (smallContrastUnitBall d)} {z : Vec d}
  (hz : z ∈ smallContrastBall d (1/2)) :
  vectorNormalizedL2On (euclideanBall z (1/2)) u.grad ≤
    smallContrastUnitBallVolumePrice d * (1/2:ℝ)^(-(d:ℝ)/2) *
    vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad := by
  have hf : MemVectorLpOn (smallContrastUnitBall d) 2 u.grad := by
    change MemLp (fun x => HilbertVec.ofVec (u.grad x)) (ENNReal.ofReal 2)
      (volume.restrict (smallContrastUnitBall d))
    simpa only [ENNReal.ofReal_ofNat] using!
      (memHilbertVectorL2_hilbertifyVecField u.grad_memVectorL2)
  exact vectorNormalizedL2On_euclideanBall_le_price_mul_rpow_mul_globalLp z
    (by norm_num) (by norm_num) (euclideanBall_half_subset_unit_of_mem_half hz) hf

def unitGradientPrice (d : ℕ) : ℝ :=
  ((1/2:ℝ)^(-(d:ℝ)/2))^2 * Real.exp (4*(1/2:ℝ)^(-(d:ℝ)/2)) *
    smallContrastUnitBallVolumePrice d

def unitLipschitzPrice (d : ℕ) : ℝ :=
  (smallContrastHolderChainLength d:ℝ)*smallContrastLocalHolderConstant d*unitGradientPrice d

theorem unitGradientPrice_nonneg (d : ℕ) : 0 ≤ unitGradientPrice d := by
  unfold unitGradientPrice
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    (smallContrastUnitBallVolumePrice_nonneg d)

theorem unitLipschitzPrice_nonneg (d : ℕ) : 0 ≤ unitLipschitzPrice d := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (smallContrastLocalHolderConstant_nonneg d))
    (unitGradientPrice_nonneg d)

theorem uniform_gradient_of_log_lipschitz {d : ℕ} [NeZero d]
 {s : Vec d → ℝ} {L : ℝ} {u : H1Function (smallContrastUnitBall d)}
 (hL : 0 ≤ L) (hLs : L ≤ smallContrastThreshold d (1/2:ℝ))
 (hs : ContinuousOn s (smallContrastUnitBall d))
 (hpos : ∀ z ∈ smallContrastUnitBall d, 0 < s z)
 (hlog : ∀ z ∈ smallContrastUnitBall d, ∀ y ∈ smallContrastUnitBall d,
 |Real.log (s y)-Real.log (s z)| ≤ L*‖y-z‖)
 (hu : IsWeaklyHarmonicOn s (smallContrastUnitBall d) u) :
 ∀ z ∈ smallContrastBall d (1/2), ∀ r : ℝ, 0 < r → r ≤ 1/2 →
 vectorNormalizedL2On (euclideanBall z r) u.grad ≤
 (((1/2:ℝ)^(-(d:ℝ)/2))^2 * Real.exp (4*(1/2:ℝ)^(-(d:ℝ)/2)) *
 smallContrastUnitBallVolumePrice d) * vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad := by
  intro z hz r hr hrhalf
  have hqpos : 0 < (1/2:ℝ)^(-(d:ℝ)/2) :=
    Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < (1/2:ℝ)) (-(d:ℝ)/2)
  have hexp : 0 ≤ Real.exp (4*(1/2:ℝ)^(-(d:ℝ)/2)) := Real.exp_nonneg _
  have hqexp : 0 ≤ (1/2:ℝ)^(-(d:ℝ)/2) * Real.exp (4*(1/2:ℝ)^(-(d:ℝ)/2)) :=
    mul_nonneg hqpos.le hexp
  have houter := euclideanBall_half_subset_unit_of_mem_half hz
  have hzunit : z ∈ smallContrastUnitBall d :=
    euclideanBall_subset_euclideanBall (by norm_num : (0:ℝ) ≤ (1/2:ℝ))
      (by norm_num : (1/2:ℝ) < (1:ℝ)) hz
  -- contrast control at every radius t ≤ 1/2
  have hc : ∀ t : ℝ, 0 < t → t ≤ (1/2:ℝ) → ∀ y ∈ euclideanBall z t,
      |(s z)⁻¹ * s y - 1| ≤ 2*L*t := by
    intro t ht htle y hy
    have hsub : euclideanBall z t ⊆ smallContrastUnitBall d := by
      rcases eq_or_lt_of_le htle with he | hlt
      · subst he; exact houter
      · exact (euclideanBall_subset_euclideanBall (le_of_lt ht) hlt).trans houter
    have hLle : L ≤ (1/16:ℝ) := hLs.trans (smallContrastThreshold_half_le_sixteenth d)
    have hsmall : L*t ≤ 1 := by
      refine le_trans (le_trans (mul_le_mul_of_nonneg_right hLle (le_of_lt ht))
        (mul_le_mul_of_nonneg_left htle (by norm_num : (0:ℝ) ≤ (1/16:ℝ)))) ?_
      norm_num
    exact abs_normalized_sub_one_le_twice_log_lipschitz ht hL hsmall
      (hpos z hzunit) (fun w hw => hpos w (hsub hw))
      (fun y hy => hlog z hzunit y (hsub hy)) y hy
  -- dyadic improvement around z
  have hU : IsOpen (smallContrastUnitBall d) := isOpen_euclideanBall (0:Vec d) 1
  have hgHalf := u.grad_memVectorL2.mono_measure (Measure.restrict_mono houter le_rfl)
  have hread := gradient_bound_of_dyadic z (by norm_num : (0:ℝ) < (1/2:ℝ)) hgHalf
    (fun n => dyadic_gradient_bound_of_linear_contrast hU hs hu z hL hLs houter hc n)
    r hr hrhalf
  have hinit := half_ball_gradient_le_global_lp (u:=u) hz
  calc vectorNormalizedL2On (euclideanBall z r) u.grad
      ≤ (1/2:ℝ)^(-(d:ℝ)/2) * (Real.exp (4*(1/2:ℝ)^(-(d:ℝ)/2)) *
        vectorNormalizedL2On (euclideanBall z (1/2)) u.grad) := hread
    _ ≤ (1/2:ℝ)^(-(d:ℝ)/2) * (Real.exp (4*(1/2:ℝ)^(-(d:ℝ)/2)) *
        (smallContrastUnitBallVolumePrice d * (1/2:ℝ)^(-(d:ℝ)/2) *
          vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinit hexp) hqpos.le
    _ = (((1/2:ℝ)^(-(d:ℝ)/2))^2 * Real.exp (4*(1/2:ℝ)^(-(d:ℝ)/2)) *
        smallContrastUnitBallVolumePrice d) * vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad := by
      ring

theorem exists_lipschitz_representative_of_log_lipschitz {d : ℕ} [NeZero d]
 {s : Vec d → ℝ} {L : ℝ} {u : H1Function (smallContrastUnitBall d)}
 (hL : 0 ≤ L) (hLs : L ≤ smallContrastThreshold d (1/2:ℝ))
 (hs : ContinuousOn s (smallContrastUnitBall d))
 (hpos : ∀ z ∈ smallContrastUnitBall d, 0 < s z)
 (hlog : ∀ z ∈ smallContrastUnitBall d, ∀ y ∈ smallContrastUnitBall d,
 |Real.log (s y)-Real.log (s z)| ≤ L*‖y-z‖)
 (hu : IsWeaklyHarmonicOn s (smallContrastUnitBall d) u) :
 ∃ g : Vec d → ℝ, ContinuousOn g (smallContrastBall d (1/2)) ∧
 g =ᵐ[volume.restrict (smallContrastUnitBall d)] u.toFun ∧
 EuclideanHolderBoundOn (smallContrastBall d (1/2)) 1
 (unitLipschitzPrice d * vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad) g := by
  have hgrad := uniform_gradient_of_log_lipschitz hL hLs hs hpos hlog hu
  have h1 : 0 ≤ unitGradientPrice d := unitGradientPrice_nonneg d
  have h2 : 0 ≤ vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad := ENNReal.toReal_nonneg
  have hK : 0 ≤ unitGradientPrice d * vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad :=
    mul_nonneg h1 h2
  simpa only [unitLipschitzPrice, unitGradientPrice, mul_assoc] using!
    exists_lipschitz_representative_of_uniform_gradient hK hgrad

end
end SubdiffusiveProcess.CoarseGrainingVocab.Section11.HarmonicLipschitz
