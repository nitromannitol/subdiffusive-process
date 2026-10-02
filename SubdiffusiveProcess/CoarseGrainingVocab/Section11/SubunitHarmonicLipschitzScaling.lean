import SubdiffusiveProcess.CoarseGrainingVocab.Section11.SubunitHarmonicLipschitzUnit

/-! Transport the Lipschitz representative to physical balls and apply Caccioppoli. -/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section11.HarmonicLipschitz
open MeasureTheory Homogenization Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.WeightedLocalHarmonic
noncomputable section


theorem isWeaklyHarmonicOn_ballToUnit {d : ℕ}
  {s : Vec d → ℝ} {x : Vec d} {rho : ℝ} (hrho : 0 < rho)
  {u : H1Function (euclideanBall x rho)}
  (hu : IsWeaklyHarmonicOn s (euclideanBall x rho) u) :
  IsWeaklyHarmonicOn (fun y => s (rho • y + x)) (smallContrastUnitBall d)
    (ballToUnitH1 x hrho u) := by
  have htrans := isWeaklyHarmonicOn_translate (-x) hu
  have hdilate := isWeaklyHarmonicOn_dilate (inv_pos.mpr hrho) htrans
  have hcoeff : (fun y => s ((rho⁻¹)⁻¹ • y - -x)) = (fun y => s (rho • y + x)) := by
    funext y
    simp [sub_eq_add_neg]
  rw [hcoeff] at hdilate
  exact IsWeaklyHarmonicOn.castDomain
    (inv_smul_translateSet_neg_euclideanBall_eq_unitBall x hrho) hdilate

theorem log_lipschitz_affine {d : ℕ}
  {s : Vec d → ℝ} {U : Set (Vec d)} {x : Vec d} {rho L : ℝ}
  (hrho : 0 < rho) (hm : Set.MapsTo (fun y : Vec d => rho • y + x) (smallContrastUnitBall d) U)
  (hl : ∀ z ∈ U, ∀ y ∈ U, |Real.log (s y) - Real.log (s z)| ≤ L * ‖y-z‖) :
  ∀ z ∈ smallContrastUnitBall d, ∀ y ∈ smallContrastUnitBall d,
    |Real.log (s (rho • y + x)) - Real.log (s (rho • z + x))| ≤
      (L * rho) * ‖y-z‖ := by
  intro z hz y hy
  have h1 := hl (rho • z + x) (hm hz) (rho • y + x) (hm hy)
  have hsub : (rho • y + x) - (rho • z + x) = rho • (y - z) := by
    rw [smul_sub]; abel
  rw [hsub] at h1
  calc |Real.log (s (rho • y + x)) - Real.log (s (rho • z + x))|
      ≤ L * ‖rho • (y - z)‖ := h1
    _ = L * (rho * ‖y - z‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrho]
    _ = (L * rho) * ‖y - z‖ := by ring

theorem smallContrastDataSize_zero {d : ℕ} (u : H1Function (smallContrastUnitBall d)) (alpha : ℝ) :
 smallContrastDataSize d alpha u (fun _ => 0) =
 vectorLpSizeOn (smallContrastUnitBall d) 2 u.grad := by
  simp [smallContrastDataSize, vectorLpSizeOn]

theorem exists_physical_lipschitz_representative {d : ℕ} [NeZero d]
 {s : Vec d → ℝ} {x : Vec d} {rho L : ℝ} (hrho : 0 < rho)
 {u : H1Function (euclideanBall x rho)} (hL : 0 ≤ L)
 (hLs : L*rho ≤ smallContrastThreshold d (1/2:ℝ))
 (hs : ContinuousOn s (euclideanBall x rho))
 (hpos : ∀ z ∈ euclideanBall x rho, 0 < s z)
 (hlog : ∀ z ∈ euclideanBall x rho, ∀ y ∈ euclideanBall x rho,
 |Real.log (s y)-Real.log (s z)| ≤ L*‖y-z‖)
 (hu : IsWeaklyHarmonicOn s (euclideanBall x rho) u) :
 ∃ g : Vec d → ℝ, ContinuousOn g (euclideanBall x (rho/2)) ∧
 g =ᵐ[volume.restrict (euclideanBall x (rho/2))] u.toFun ∧
 EuclideanHolderBoundOn (euclideanBall x (rho/2)) 1
 (unitLipschitzPrice d * vectorLpSizeOn (smallContrastUnitBall d) 2
 (ballToUnitH1 x hrho u).grad) g := by
  have hm : MapsTo (fun y : Vec d => rho • y + x)
      (smallContrastUnitBall d) (euclideanBall x rho) := by
    intro y hy
    exact (affine_mem_euclideanBall_iff_of_pos x y hrho).2 hy
  have hc : Continuous (fun y : Vec d => rho • y + x) := by fun_prop
  have hlogUnit := log_lipschitz_affine hrho hm hlog
  have huUnit := isWeaklyHarmonicOn_ballToUnit hrho hu
  obtain ⟨g, hgcont, hgae, hholder⟩ :=
    exists_lipschitz_representative_of_log_lipschitz
      (mul_nonneg hL hrho.le) hLs (hs.comp hc.continuousOn hm)
      (fun z hz => hpos _ (hm hz)) hlogUnit huUnit
  refine ⟨physicalBallRepresentative x rho g,
    continuousOn_physicalBallRepresentative hrho hgcont,
    physicalBallRepresentative_ae_eq hrho hgae, ?_⟩
  simpa only [sub_self, Real.rpow_zero, mul_one] using
    (euclideanHolderBoundOn_physicalBallRepresentative hrho hholder)

theorem exists_lipschitz_representative_of_log_lipschitz_caccioppoli {d : ℕ} [NeZero d]
 {s : Vec d → ℝ} {x : Vec d} {R L : ℝ} (hR : 0 < R)
 {u : H1Function (euclideanBall x R)} (hL : 0 ≤ L)
 (hLs : L*R ≤ smallContrastThreshold d (1/2:ℝ)/8)
 (hs : ContinuousOn s (euclideanBall x R))
 (hpos : ∀ z ∈ euclideanBall x R, 0 < s z)
 (hlog : ∀ z ∈ euclideanBall x R, ∀ y ∈ euclideanBall x R,
 |Real.log (s y)-Real.log (s z)| ≤ L*‖y-z‖)
 (hu : IsWeaklyHarmonicOn s (euclideanBall x R) u) (c : ℝ) :
 ∃ g : Vec d → ℝ, ContinuousOn g (euclideanBall x (R/2/2)) ∧
 g =ᵐ[volume.restrict (euclideanBall x (R/2/2))] u.toFun ∧
 EuclideanHolderBoundOn (euclideanBall x (R/2/2)) 1
 (unitLipschitzPrice d * halfBallCaccioppoliDataPrice d x R u.toFun c) g := by
  have hdpos : 0 < smallContrastThreshold d (1/2:ℝ) :=
    Section9Support.WeightedLocalHarmonic.smallContrastThreshold_half_pos d
  have hd16 := smallContrastThreshold_half_le_sixteenth d
  have hx : x ∈ euclideanBall x R := Section6Schauder.mem_euclideanBall_self hR
  have htwoLR : 2*L*R ≤ smallContrastThreshold d (1/2:ℝ) := by linarith
  have hclose : ∀ y ∈ euclideanBall x R,
      |(s x)⁻¹ * s y - 1| ≤ smallContrastThreshold d (1/2:ℝ) := by
    intro y hy
    exact (abs_normalized_sub_one_le_twice_log_lipschitz hR hL (by linarith)
      (hpos x hx) hpos (fun z hz => hlog x hx z hz) y hy).trans htwoLR
  have hrho : 0 < R/2 := by positivity
  have hsub : euclideanBall x (R/2) ⊆ euclideanBall x R :=
    euclideanBall_subset_euclideanBall (by positivity) (by linarith)
  let uV : H1Function (euclideanBall x (R/2)) :=
    u.restrict (isOpen_euclideanBall x (R/2)) hsub
  have huV : IsWeaklyHarmonicOn s (euclideanBall x (R/2)) uV :=
    Section6BoundaryL2.isWeaklyHarmonicOn_restrict (isOpen_euclideanBall x R)
      (isOpen_euclideanBall x (R/2)) hsub hu
  obtain ⟨g, hgcont, hgae, hholder⟩ :=
    exists_physical_lipschitz_representative hrho hL (by nlinarith)
      (hs.mono hsub) (fun z hz => hpos z (hsub hz))
      (fun z hz y hy => hlog z (hsub hz) y (hsub hy)) huV
  have hdata := smallContrastDataSize_halfBall_le_caccioppoli
    (isOpen_euclideanBall x R) hs hu hR (Set.Subset.rfl) hd16 hclose c
  have hLp : vectorLpSizeOn (smallContrastUnitBall d) 2 (ballToUnitH1 x hrho uV).grad
      ≤ halfBallCaccioppoliDataPrice d x R u.toFun c := by
    rw [smallContrastDataSize_zero] at hdata
    exact hdata
  refine ⟨g, hgcont, hgae, ?_⟩
  intro y hy w hw
  have hh := hholder y hy w hw
  rw [Real.rpow_one] at hh ⊢
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hLp (unitLipschitzPrice_nonneg d))
    (euclideanNorm_nonneg (y-w)))
end
end SubdiffusiveProcess.CoarseGrainingVocab.Section11.HarmonicLipschitz
