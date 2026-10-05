module

public import SubdiffusiveProcess.MeyersRegularity.TailIntegration

@[expose] public section

/-! Absorption of the perturbation term at a finite moment cutoff. -/

open MeasureTheory Filter Set Homogenization
open scoped ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess.MeyersRegularity
open CubeCalderonZygmund

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]

theorem truncatedMoment_absorption {μ ν : Measure α} {f g H : α → E}
    {p M eps δ lambda0 T θ D : ℝ} {κ : ℝ≥0∞}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) (hH : MemLp H (ENNReal.ofReal p) ν)
    (hμν : μ ≤ ν) (hp : 2 < p) (hM : 1 ≤ M) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hlambda0 : 0 < lambda0) (hT : 0 ≤ T) (hκ : κ ≠ ⊤)
    (hD : 0 ≤ D) (hfD : (eLpNorm f 2 ν).toReal ≤ D)
    (hHD : (eLpNorm H (ENNReal.ofReal p) ν).toReal ≤ D)
    (hbound : ∀ᵐ x ∂ν, ‖g x‖ ≤ δ*‖f x‖ + ‖H x‖)
    (hsmall : (2*M)^(p-2)*κ.toReal +
      ((2*M/eps)^(p-2)*eps⁻¹^2)*κ.toReal*(2 : ℝ)^p*δ^2 ≤ θ)
    (htail : ∀ t : ℝ, lambda0 ≤ t →
      sqWeightedMeasure f μ {x | M*t < ‖f x‖} ≤ κ *
        (sqWeightedMeasure f ν {x | t/2 < ‖f x‖} + ENNReal.ofReal (eps⁻¹^2) *
          sqWeightedMeasure g ν {x | eps*t/2 < ‖g x‖})) :
    (truncatedMoment μ f p T).toReal ≤
      θ*(truncatedMoment ν f p T).toReal + (M*lambda0)^(p-2)*D^2 +
        ((2*M/eps)^(p-2)*eps⁻¹^2)*κ.toReal*(2 : ℝ)^p*D^p := by
  have hMpos : 0 < M := by linarith
  have hfμ : MemLp f 2 μ := hf.mono_measure hμν
  have hfμtop := hfμ.eLpNorm_ne_top
  have hf_top := hf.eLpNorm_ne_top
  have hH_top := hH.eLpNorm_ne_top
  have hfT := truncatedMoment_ne_top hf hp hT
  have hgT := truncatedMoment_ne_top hg hp hT
  have hHpow := ENNReal.rpow_ne_top_of_nonneg (by linarith : 0 ≤ p) hH_top
  let c0 := (M*lambda0)^(p-2)
  let c1 := (2*M)^(p-2)
  let c2 := (2*M/eps)^(p-2)*eps⁻¹^2
  let c3 := (2 : ℝ)^p
  have hc0 : 0 ≤ c0 := by dsimp only [c0]; positivity
  have hc1 : 0 ≤ c1 := by dsimp only [c1]; positivity
  have hc2 : 0 ≤ c2 := by dsimp only [c2]; positivity
  have hc3 : 0 ≤ c3 := by dsimp only [c3]; positivity
  have hmain := truncatedMoment_le_of_tail hf.aestronglyMeasurable hg.aestronglyMeasurable
    hμν hp hM heps heps1 hlambda0 hT htail
  rw [sqWeightedMeasure_univ_eq, SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hfμ.aestronglyMeasurable] at hmain
  change truncatedMoment μ f p T ≤ ENNReal.ofReal c0*(eLpNorm f 2 μ)^2 +
    ENNReal.ofReal c1*κ*truncatedMoment ν f p T +
    ENNReal.ofReal c2*κ*truncatedMoment ν g p T at hmain
  have hr := ENNReal.toReal_mono (by finiteness) hmain
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hc0,
    ENNReal.toReal_ofReal hc1, ENNReal.toReal_ofReal hc2] at hr
  have hgmain := truncatedMoment_perturbation hf.aestronglyMeasurable hg.aestronglyMeasurable
    hH.aestronglyMeasurable hp hT hδ hδ1 hbound
  have hgr := ENNReal.toReal_mono (by finiteness) hgmain
  change (truncatedMoment ν g p T).toReal ≤
    (ENNReal.ofReal c3*(ENNReal.ofReal (δ^2)*truncatedMoment ν f p T +
      eLpNorm H (ENNReal.ofReal p) ν ^ p)).toReal at hgr
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)] at hgr
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hc3, ENNReal.toReal_ofReal (sq_nonneg δ)] at hgr
  have hfnorm := ENNReal.toReal_mono hf_top (eLpNorm_mono_measure (p := (2 : ℝ≥0∞)) f hμν)
  have hfD' : (eLpNorm f 2 μ).toReal ≤ D := hfnorm.trans hfD
  have henergy : (eLpNorm f 2 μ).toReal^2 ≤ D^2 :=
    (sq_le_sq₀ ENNReal.toReal_nonneg hD).mpr hfD'
  have hsource : (eLpNorm H (ENNReal.ofReal p) ν).toReal^p ≤ D^p :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hHD (by linarith)
  have hgfinal : (truncatedMoment ν g p T).toReal ≤
      c3*(δ^2*(truncatedMoment ν f p T).toReal+D^p) :=
    hgr.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsource) hc3)
  calc
    (truncatedMoment μ f p T).toReal ≤
        c0*D^2 + c1*κ.toReal*(truncatedMoment ν f p T).toReal +
          c2*κ.toReal*(c3*(δ^2*(truncatedMoment ν f p T).toReal+D^p)) := by
      exact hr.trans (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left henergy hc0) le_rfl)
        (mul_le_mul_of_nonneg_left hgfinal (mul_nonneg hc2 ENNReal.toReal_nonneg)))
    _ = (c1*κ.toReal+c2*κ.toReal*c3*δ^2)*(truncatedMoment ν f p T).toReal +
        c0*D^2+c2*κ.toReal*c3*D^p := by ring
    _ ≤ θ*(truncatedMoment ν f p T).toReal + c0*D^2+c2*κ.toReal*c3*D^p := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hsmall (ENNReal.toReal_nonneg : 0 ≤ (truncatedMoment ν f p T).toReal)) le_rfl) le_rfl
    _ = _ := rfl


end SubdiffusiveProcess.MeyersRegularity
