import SubdiffusiveProcess.Analysis.SmallOscillationHolder
import SubdiffusiveProcess.Analysis.HolderEnergyScaling
import SubdiffusiveProcess.Sobolev.WeakEquationRestrict

/-! An interior Meyers--Morrey estimate with the physical energy scaling.
The coefficient oscillation and reference comparisons are explicit caller obligations. -/

open MeasureTheory Set TopologicalSpace SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess

/-- A small-oscillation coefficient yields the full Holder estimate with its reference-normalized energy. -/
theorem smallOscillation_holder_energy {d : ℕ}
    (W : SmallPerturbationInput d) (p alpha : ℝ) (hp : 2 ≤ p)
    (halpha : 0 < alpha) (halpha1 : alpha < 1) (halphap : alpha < 1 - (d : ℝ) / p)
    (z : SpatialCoordinates d) (l : ℝ) (hl : 0 < 4 * l)
    (a : PositiveCoefficient (centeredCube z (4 * l) hl)) (a0 b s B : ℝ)
    (ha0 : 0 < a0) (hb : 0 < b) (hs : 0 < s) (hB : 1 ≤ B)
    (hcompA : s ≤ B * a0) (hcompB : s ≤ B * b)
    (hosc : ∀ᵐ x ∂volume.restrict (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)),
      |Real.log (a.val x) - Real.log a0| ≤ W.osc p)
    (hlow : ∀ᵐ x ∂volume.restrict (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)),
      b ≤ a.val x)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ)
    (hF : AEMeasurable F (volume.restrict
      (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)))) (hKf : 0 ≤ Kf)
    (hbound : ∀ᵐ x ∂volume.restrict (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)),
      |F x| ≤ Kf)
    (u : weakSobolevGraph (centeredCube z (4 * l) hl))
    (heq : ∀ psi : killedSobolevGraph (centeredCube z (4 * l) hl),
      sobolevCoefficientForm a u.val psi.val =
        ∫ x in (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)), F x * psi.val.1 x) :
    let C := (((d : ℝ) + 1) ^ alpha + 1) * W.CMorrey p alpha * W.C p * B
    ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Metric.ball z l)] U) ∧
      IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + (2 * l) • x) - U z) ∧
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + (2 * l) • x) - U z) ≤
          C * (2 * l) ^ ((2 - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) *
            Real.sqrt (sobolevCoefficientForm a u.val u.val) +
          C * (2 * l) ^ (2 : ℝ) * s⁻¹ * Kf := by
  obtain ⟨U, hU, htie, hHolder, hnorm⟩ :=
    smallOscillation_scaled_cAlphaNorm_energy W p alpha hp halpha halphap z l hl a a0 b
      ha0 hb hosc hlow F Kf hF hKf hbound u heq
  have hl0 : 0 < l := by linarith only [hl]
  have hscale := holder_energy_scaling_le d (2 * l) alpha (((d : ℝ) + 1) ^ alpha + 1)
    (W.CMorrey p alpha) (W.C p) B s a0 b (sobolevCoefficientForm a u.val u.val) Kf
    (by positivity) halpha1.le (by positivity) (W.CMorrey_pos p alpha).le (W.C_pos p).le
    hB hs ha0 hb hKf hcompA hcompB
  rw [show 2 * l / 2 = l by ring, show 2 * (2 * l) = 4 * l by ring] at hscale
  exact ⟨U, hU, htie, hHolder, hnorm.trans hscale⟩

/-- Restriction of the equation makes the interior estimate depend on the larger domain's energy. -/
theorem smallOscillation_holder_parent_energy {d : ℕ}
    (W : SmallPerturbationInput d) (p alpha : ℝ) (hp : 2 ≤ p)
    (halpha : 0 < alpha) (halpha1 : alpha < 1) (halphap : alpha < 1 - (d : ℝ) / p)
    (z : SpatialCoordinates d) (l : ℝ) (hl : 0 < 4 * l)
    (Ω : Opens (SpatialCoordinates d)) (hsub : centeredCube z (4 * l) hl ≤ Ω)
    (aΩ : PositiveCoefficient Ω) (a : PositiveCoefficient (centeredCube z (4 * l) hl))
    (hab : (aΩ.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z (4 * l) hl : Set (SpatialCoordinates d))] a.val)
    (a0 b s B : ℝ) (ha0 : 0 < a0) (hb : 0 < b) (hs : 0 < s) (hB : 1 ≤ B)
    (hcompA : s ≤ B * a0) (hcompB : s ≤ B * b)
    (hosc : ∀ᵐ x ∂volume.restrict (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)),
      |Real.log (a.val x) - Real.log a0| ≤ W.osc p)
    (hlow : ∀ᵐ x ∂volume.restrict (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)),
      b ≤ a.val x)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hF : Measurable F) (hKf : 0 ≤ Kf)
    (hbound : ∀ x ∈ Ω, |F x| ≤ Kf)
    (u : weakSobolevGraph Ω)
    (heq : ∀ psi : killedSobolevGraph Ω,
      sobolevCoefficientForm aΩ u.val psi.val = ∫ x in (Ω : Set (SpatialCoordinates d)), F x * psi.val.1 x) :
    let C := (((d : ℝ) + 1) ^ alpha + 1) * W.CMorrey p alpha * W.C p * B
    ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Metric.ball z l)] U) ∧
      IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + (2 * l) • x) - U z) ∧
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + (2 * l) • x) - U z) ≤
          C * (2 * l) ^ ((2 - (d : ℝ)) / 2) * s ^ (-(1 : ℝ) / 2) *
            Real.sqrt (sobolevCoefficientForm aΩ u.val u.val) +
          C * (2 * l) ^ (2 : ℝ) * s⁻¹ * Kf := by
  let uV : weakSobolevGraph (centeredCube z (4 * l) hl) :=
    ⟨sobolevDataRestrict hsub u.val, sobolevDataRestrict_mem_weak hsub u.property⟩
  have hFbound : ∀ᵐ x ∂volume.restrict (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)),
      |F x| ≤ Kf := by
    filter_upwards [ae_restrict_mem (centeredCube z (4 * l) hl).isOpen.measurableSet] with x hx
    exact hbound x (hsub hx)
  have hVeq := weakEquation_restrict hsub aΩ a hab u.val F heq
  obtain ⟨U, hU, htie, hHolder, hnorm⟩ := smallOscillation_holder_energy W p alpha hp halpha
    halpha1 halphap z l hl a a0 b s B ha0 hb hs hB hcompA hcompB hosc hlow F Kf
      hF.aemeasurable hKf hFbound uV hVeq
  have hl0 : 0 < l := by linarith only [hl]
  have hinner : Metric.ball z l ⊆
      (centeredCube z (4 * l) hl : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_ball (by linarith only [hl0])
  have htie0 : ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Metric.ball z l)] U) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hinner
      (domainLpRestrict_coeFn hsub u.val.1), htie] with x hx hu
    exact hx.symm.trans hu
  refine ⟨U, hU, htie0, hHolder, hnorm.trans ?_⟩
  refine add_le_add ?_ (le_refl _)
  apply mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (sobolevCoefficientForm_restrict_le hsub aΩ a hab u.val))
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hC := (W.C_pos p).le
  have hCM := (W.CMorrey_pos p alpha).le
  positivity

end SubdiffusiveProcess
