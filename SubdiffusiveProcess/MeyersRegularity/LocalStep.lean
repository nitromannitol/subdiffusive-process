module

public import SubdiffusiveProcess.MeyersRegularity.CutoffBound
public import SubdiffusiveProcess.MeyersRegularity.LocalWeak
public import SubdiffusiveProcess.MeyersRegularity.MomentStep
public import SubdiffusiveProcess.MeyersRegularity.LpBounds
public import SubdiffusiveProcess.MeyersRegularity.Stopping
public import SubdiffusiveProcess.MeyersRegularity.TailIntegration
public import SubdiffusiveProcess.MeyersRegularity.BallGeometry
public import SubdiffusiveProcess.MeyersRegularity.Perturbation
public import SubdiffusiveProcess.MeyersRegularity.Parameters

@[expose] public section

/-! Interior Meyers regularity: LocalStep. -/

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity

theorem exists_local_truncated_estimate (d : ℕ) (hd : 2 ≤ d) (p θ : ℝ)
    (hp : 2 < p) (hθ : 0 < θ) :
    ∃ epsilon C : ℝ, 0 < epsilon ∧ epsilon ≤ 1/2 ∧ 0 < C ∧
      ∀ (a : Vec d → ℝ) (F : Vec d → Vec d),
        AEMeasurable a (volume.restrict (unitBall d (3/2))) →
        (∀ᵐ x ∂volume.restrict (unitBall d (3/2)), |a x-1| ≤ epsilon) →
        MemLp (hilbertifyVecField F) (ENNReal.ofReal p)
          (volume.restrict (unitBall d (3/2))) →
        ∀ u : H1Function (unitBall d (3/2)), VectorEquation a F u →
          ∀ r s T : ℝ, 1 ≤ r → r < s → s ≤ 3/2 → 0 ≤ T →
            (truncatedMoment (volume.restrict (unitBall d r)) (gradientField u) p T).toReal ≤
              θ * (truncatedMoment (volume.restrict (unitBall d s))
                (gradientField u) p T).toReal +
              C * (s-r)^(-spatialPower d p) * (vectorDataSize p u F)^p := by
  let : NeZero d := ⟨by omega⟩
  let μO := volume.restrict (unitBall d (3/2))
  have hOmeas : MeasurableSet (unitBall d (3/2)) := Meyers.measurableSet_eBall 0 _
  let : IsFiniteMeasure μO := isFiniteMeasure_restrict.mpr
    (unitBall_volume_lt_top d (by norm_num : (0 : ℝ) < 3/2)).ne
  let V : ℝ := (μO univ ^ (1/2-1/p)).toReal
  let B : ℝ := 1+V
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hB : 0 < B := by dsimp only [B]; linarith
  obtain ⟨q, depth, G, M, eps, δ, hpq, hM, heps, heps1, hδ, hδhalf, hsmall⟩ :=
    exists_absorption_parameters d hd p θ hp hθ
  let κ := CubeCalderonZygmund.oneStoppingBallCoefficient depth G *
    (ENNReal.ofReal ((M/2)^(2-q.exponent.toReal)) + ENNReal.ofReal (eps^2))
  have hκ : κ ≠ ⊤ := ENNReal.mul_ne_top (CubeCalderonZygmund.oneStoppingBallCoefficient_ne_top G)
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
  let K : ℝ := Real.sqrt ((5*(d : ℝ)*(3 : ℝ)^depth)^d * (1+eps⁻¹^2*B^2))
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hK : 0 < K := by dsimp only [K]; apply Real.sqrt_pos.2; positivity
  let L : ℝ := ((2*M/eps)^(p-2)*eps⁻¹^2)*κ.toReal*(2 : ℝ)^p
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  let C : ℝ := (2*M*K)^(p-2)+L+1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨δ, C, hδ, hδhalf, hC, ?_⟩
  intro a F ha hclose hF u heq r s T hr hrs hs hT
  let f := gradientField u
  let H := hilbertifyVecField F
  let g : Vec d → Vec d := fun x => (a x-1) • u.grad x + F x
  let gg := hilbertifyVecField g
  let D := vectorDataSize p u F
  have hD : 0 ≤ D := by dsimp only [D, vectorDataSize]; positivity
  have hf : MemLp f 2 μO := gradientField_memLp_two u
  have hHD : (eLpNorm H (ENNReal.ofReal p) μO).toReal ≤ D := by
    dsimp only [D, vectorDataSize, H, μO]
    exact le_add_of_nonneg_left ENNReal.toReal_nonneg
  have hfD : (eLpNorm f 2 μO).toReal ≤ D := by
    dsimp only [D, vectorDataSize, f, μO]
    exact le_add_of_nonneg_right ENNReal.toReal_nonneg
  have hpENN : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    have hh := ENNReal.ofReal_le_ofReal hp.le
    norm_num only [ENNReal.ofReal_ofNat] at hh
    exact hh
  have hFtwo : MemLp H 2 μO := hF.mono_exponent hpENN
  have hFraw := memVectorL2_of_hilbert_memLp hFtwo
  obtain ⟨hgraw, hgweak⟩ := smoothEquation_of_vectorEquation (Meyers.isOpen_eBall 0 (3/2))
    u a F ha hδ.le hclose hFraw heq
  have hg : MemLp gg 2 μO := memHilbertVectorL2_hilbertifyVecField hgraw
  have hbound : ∀ᵐ x ∂μO, ‖gg x‖ ≤ δ*‖f x‖ + ‖H x‖ := by
    filter_upwards [hclose] with x hx
    change ‖(a x-1) • HilbertVec.ofVec (u.grad x) + HilbertVec.ofVec (F x)‖ ≤ _
    calc
      _ ≤ ‖(a x-1) • HilbertVec.ofVec (u.grad x)‖ + ‖HilbertVec.ofVec (F x)‖ := norm_add_le _ _
      _ = |a x-1| *‖f x‖ + ‖H x‖ := by rw [norm_smul, Real.norm_eq_abs]; rfl
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hx (norm_nonneg _)) le_rfl
  have hgD : (eLpNorm gg 2 μO).toReal ≤ B*D := by
    have htri := two_norm_le_of_norm_bound hf hg hFtwo hδ.le hbound
    have hdown := two_norm_le_lp_norm hp.le hF
    change (eLpNorm H 2 μO).toReal ≤ (eLpNorm H (ENNReal.ofReal p) μO).toReal*V at hdown
    have hδone : δ ≤ 1 := by linarith
    have hfirst := mul_le_mul_of_nonneg_right hδone
      (ENNReal.toReal_nonneg : 0 ≤ (eLpNorm f 2 μO).toReal)
    have hfn : 0 ≤ (eLpNorm f 2 μO).toReal := ENNReal.toReal_nonneg
    have hHn : 0 ≤ (eLpNorm H (ENNReal.ofReal p) μO).toReal := ENNReal.toReal_nonneg
    change (eLpNorm gg 2 μO).toReal ≤
      (1+V)*((eLpNorm f 2 μO).toReal+(eLpNorm H (ENNReal.ofReal p) μO).toReal)
    nlinarith only [htri, hdown, hfirst, hV, hfn, hHn]
  have hgap : 0 < s-r := by linarith
  have hsubS : unitBall d s ⊆ unitBall d (3/2) := Meyers.eBall_mono 0 (by linarith) hs
  have hsubR : unitBall d r ⊆ unitBall d s := Meyers.eBall_mono 0 (by linarith) hrs.le
  let μr := volume.restrict (unitBall d r)
  let μs := volume.restrict (unitBall d s)
  have hsO : μs ≤ μO := Measure.restrict_mono hsubS le_rfl
  have hrsM : μr ≤ μs := Measure.restrict_mono hsubR le_rfl
  have hrO : μr ≤ μO := hrsM.trans hsO
  have hfr : MemLp f 2 μr := hf.mono_measure hrO
  have hfs : MemLp f 2 μs := hf.mono_measure hsO
  have hgs : MemLp gg 2 μs := hg.mono_measure hsO
  have hHs : MemLp H (ENNReal.ofReal p) μs := hF.mono_measure hsO
  have hfsD : (eLpNorm f 2 μs).toReal ≤ D :=
    (ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure f hsO)).trans hfD
  have hHsD : (eLpNorm H (ENNReal.ofReal p) μs).toReal ≤ D :=
    (ENNReal.toReal_mono hF.eLpNorm_ne_top (eLpNorm_mono_measure H hsO)).trans hHD
  by_cases hDpos : 0 < D
  · let us := u.restrict (Meyers.isOpen_eBall 0 s) hsubS
    let lambda0 := 2*K*(s-r)^(-(d : ℝ)/2)*D
    have hlambda0 : 0 < lambda0 := by dsimp only [lambda0]; positivity
    have hSmeas : MeasurableSet (unitBall d s) := Meyers.measurableSet_eBall 0 s
    have hRpos : 0 < (s-r)/(d : ℝ) := div_pos hgap hd0
    have hgrawS : MemVectorL2 (unitBall d s) g := hgraw.mono_measure hsO
    have hgweakS : SmoothEquation g us :=
      smoothEquation_restrict (Meyers.isOpen_eBall 0 s) hsubS u g hgweak
    have hgSnorm : (eLpNorm gg 2 μs).toReal ≤ B*D :=
      (ENNReal.toReal_mono hg.eLpNorm_ne_top (eLpNorm_mono_measure gg hsO)).trans hgD
    have henergyf : (∫ y, ‖CubeCalderonZygmund.openParentGradientExtension (unitBall d s) us y‖^2) ≤ D^2 := by
      rw [show CubeCalderonZygmund.openParentGradientExtension (unitBall d s) us =
        (unitBall d s).indicator f by rfl, indicator_energy_eq hSmeas hfs]
      exact (sq_le_sq₀ ENNReal.toReal_nonneg hD).mpr hfsD
    have henergyg : (∫ y, ‖hilbertifyVecField (CubeCalderonZygmund.openParentDatumExtension (unitBall d s) g) y‖^2) ≤ B^2*D^2 := by
      rw [CubeCalderonZygmund.hilbertifyVecField_openParentDatumExtension,
        indicator_energy_eq hSmeas hgs, ← mul_pow]
      exact (sq_le_sq₀ ENNReal.toReal_nonneg (mul_nonneg hB.le hD)).mpr hgSnorm
    have hcutoff : Real.sqrt (((2*(((s-r)/(d : ℝ))/(10*(3 : ℝ)^depth)))^d)⁻¹ *
        ((∫ y, ‖CubeCalderonZygmund.openParentGradientExtension (unitBall d s) us y‖^2) +
          eps⁻¹^2 * ∫ y, ‖hilbertifyVecField (CubeCalderonZygmund.openParentDatumExtension (unitBall d s) g) y‖^2)) < lambda0 := by
      have hh := large_scale_cutoff_le (d := d) (depth := depth) (by omega) hgap heps hD hB.le
        (integral_nonneg (fun y => sq_nonneg _)) (integral_nonneg (fun y => sq_nonneg _))
        henergyf henergyg
      change _ ≤ K*(s-r)^(-(d : ℝ)/2)*D at hh
      have hpos : 0 < K*(s-r)^(-(d : ℝ)/2)*D := by positivity
      exact hh.trans_lt (by dsimp only [lambda0]; nlinarith only [hpos])
    have htail : ∀ t : ℝ, lambda0 ≤ t →
        CubeCalderonZygmund.sqWeightedMeasure f μr {x | M*t < ‖f x‖} ≤ κ *
          (CubeCalderonZygmund.sqWeightedMeasure f μs {x | t/2 < ‖f x‖} +
            ENNReal.ofReal (eps⁻¹^2) * CubeCalderonZygmund.sqWeightedMeasure gg μs
              {x | eps*t/2 < ‖gg x‖}) := by
      intro t ht
      exact one_level_tail G (by linarith : 2 < q.exponent.toReal) (Meyers.isOpen_eBall 0 s)
        (Meyers.measurableSet_eBall 0 r) hsubR heps heps1 hM.le hRpos us g hgrawS hgweakS
        (by intro x hx ρ hρ hρle; exact comparison_parent_subset_ball hd hr hrs hs depth hx hρ hρle)
        (hcutoff.trans_le ht)
    have hh := truncatedMoment_absorption hfs hgs hHs hrsM hp hM.le heps heps1 hδ.le
      (by linarith : δ ≤ 1) hlambda0 hT hκ hD hfsD hHsD
      (hbound.filter_mono (ae_mono hsO)) hsmall htail
    have hlow : (M*lambda0)^(p-2)*D^2 = (2*M*K)^(p-2)*(s-r)^(-spatialPower d p)*D^p :=
      scaled_low_moment_eq hp (by linarith) hK.le hgap hD
    have hsep : 1 ≤ (s-r)^(-spatialPower d p) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hgap (by linarith)
        (by unfold spatialPower; exact neg_nonpos.mpr (div_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hp.le)) (by norm_num)))
    change (truncatedMoment μr f p T).toReal ≤ θ*(truncatedMoment μs f p T).toReal +
      (M*lambda0)^(p-2)*D^2+L*D^p at hh
    rw [hlow] at hh
    calc
      (truncatedMoment μr f p T).toReal ≤ θ*(truncatedMoment μs f p T).toReal +
          (2*M*K)^(p-2)*(s-r)^(-spatialPower d p)*D^p+L*D^p := hh
      _ ≤ θ*(truncatedMoment μs f p T).toReal + C*(s-r)^(-spatialPower d p)*D^p := by
        have hpD : 0 ≤ D^p := Real.rpow_nonneg hD _
        have hJL : L*D^p ≤ L*(s-r)^(-spatialPower d p)*D^p :=
          by simpa only [mul_one] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsep hL) hpD
        have hJP : 0 ≤ (s-r)^(-spatialPower d p)*D^p :=
          mul_nonneg (Real.rpow_nonneg hgap.le _) hpD
        dsimp only [C]
        nlinarith only [hJL, hJP]
  · have hDzero : D = 0 := le_antisymm (le_of_not_gt hDpos) hD
    have hfzero : (eLpNorm f 2 μO).toReal = 0 := by linarith only [hfD, hDzero, (ENNReal.toReal_nonneg : 0 ≤ (eLpNorm f 2 μO).toReal)]
    have hfzero' : eLpNorm f 2 μO = 0 := by
      rw [← ENNReal.ofReal_toReal hf.eLpNorm_ne_top, hfzero, ENNReal.ofReal_zero]
    have hfrzero : eLpNorm f 2 μr = 0 := by
      apply le_antisymm _ bot_le
      simpa only [hfzero'] using! eLpNorm_mono_measure (p := (2 : ℝ≥0∞)) f hrO
    have hmoment : truncatedMoment μr f p T = 0 := by
      apply le_antisymm _ bot_le
      simpa only [hfrzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using!
        truncatedMoment_le_energy hfr hp hT
    change (truncatedMoment μr f p T).toReal ≤ _
    rw [hmoment, ENNReal.toReal_zero]
    positivity


end SubdiffusiveProcess.MeyersRegularity
