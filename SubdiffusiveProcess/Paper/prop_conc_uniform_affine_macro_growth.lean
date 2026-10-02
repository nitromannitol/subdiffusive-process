import SubdiffusiveProcess.Paper.prop_conc_affine_macro_bound
import SubdiffusiveProcess.Paper.prop_conc_uniform_infrared_prefix
import SubdiffusiveProcess.Paper.prop_conc_uniform_infrared_moments
import SubdiffusiveProcess.Paper.prop_conc_uniform_response_moments
import SubdiffusiveProcess.Probability.UniformProductMoments

/-! # Uniform affine growth at resolved radii

The regularity prefix, infrared multiplier, and native response moment banks
give one growth majorant with its moment constant chosen before the model.
The bound applies above the cutoff wavelength; no concentration is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4 SubdiffusiveProcess.Probability
open scoped ENNReal NNReal Topology BigOperators

namespace Paper
noncomputable section

/-- Affine minimizers have uniform moment growth bounds above their cutoff wavelength. -/
theorem prop_conc_uniform_affine_macro_growth
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t q : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < d) (hq : 1 ≤ q)
    (u : Fin d → ℝ) :
    ∃ delta0 B : ℝ, 0 < delta0 ∧ 0 ≤ B ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∃ K : ℕ → BilateralField d → ℝ,
        (∀ N, Measurable (K N)) ∧ (∀ N om, 0 ≤ K N om) ∧
        (∀ N, eLpNorm (K N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (hP : ∃ C : ℝ≥0, ∀ v : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
          ‖(v : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
            C * ‖subspaceGradient (killedSobolevGraph
              (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) v‖)
          (N : ℕ) (x : SpatialCoordinates d) (rho : ℝ),
          x ∈ centeredCube (0 : SpatialCoordinates d) 1 one_pos → 0 < rho → rho ≤ 1 →
          (3 : ℝ) ^ (-(N : ℤ)) ≤ rho →
          localGradientEnergy (cutoffPositiveCoefficient M H om N 0 one_pos)
            (s := Metric.ball x rho ∩ (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
            (Metric.isOpen_ball.measurableSet.inter (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet)
            (sobolevGradient (dirichletMinimizer (killedResponseSpace hP)
              (cutoffPositiveCoefficient M H om N 0 one_pos)
              (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0)).val) ≤
            K N om * rho ^ t := by
  letI hdim : NeZero d := ⟨by omega⟩
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0 : 0 < t := by linarith only [ht, hdR]
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hq2 : 1 ≤ 2 * q := by linarith only [hq]
  have hq4 : 1 ≤ 4 * q := by linarith only [hq]
  obtain ⟨deltaL, BL, hdeltaL, hBL, hpref⟩ :=
    prop_conc_uniform_infrared_prefix d t (4 * q) ht htd ht0 hq4
  obtain ⟨deltaR, BR, hdeltaR, hBR, hresponse⟩ := prop_conc_uniform_response_moments d (2 * q) hq2
  obtain ⟨BI, hBI, hinfrared⟩ := prop_conc_uniform_infrared_moments d hd
    (closedCube (0 : SpatialCoordinates d) 1 one_pos) (4 * q) (by linarith only [hq])
  obtain ⟨Cp, _hCp, hFE⟩ := aux_aux_macro_energy_recurrence_finite_estimate (d := d) hd
  let Cd : ℝ := ((d : ℝ) + 1) ^ 2 *
    max 1 (Classical.choose (SubdiffusiveProcess.Frozen.Section6.cutoff_holder_regularity d))
  let Cphi := max 1 (c2Norm
    (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
    (fun x => affineSlope u x + 0))
  let coeff := 2 * aux_aux_macro_energy_recurrence_Z Cd Cp t d * (0 + Cphi) ^ 2
  let cu := 2 * volume.real
    (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) *
      ∑ i : Fin d, (u i) ^ 2
  have hcoeff : 0 ≤ coeff := mul_nonneg
    (mul_nonneg (by norm_num) (aux_aux_macro_energy_recurrence_Z_nonneg _ _ _ _)) (sq_nonneg _)
  have hcu : 0 ≤ cu := mul_nonneg (mul_nonneg (by norm_num) measureReal_nonneg)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  let B := coeff * (BL * BI * (1 + cu * BR))
  have hB : 0 ≤ B := mul_nonneg hcoeff
    (mul_nonneg (mul_nonneg hBL.le hBI.le) (add_nonneg zero_le_one (mul_nonneg hcu hBR)))
  refine ⟨min deltaL deltaR, B, lt_min hdeltaL hdeltaR, hB, ?_⟩
  intro M Sreg H hIR hdelta
  obtain ⟨hdeltaC, halpha, hprefix⟩ := hpref M Sreg (hdelta.trans (min_le_left _ _))
  obtain ⟨Lmac, hLm, hLn, hLpre⟩ := hprefix 0
  have hRn := hresponse M (hdelta.trans (min_le_right _ _))
  obtain ⟨hIm, hIn⟩ := hinfrared M H hIR
  let X : ℕ → BilateralField d → ℝ := fun N om => (3 : ℝ) ^ (t * (Lmac N om : ℝ))
  let Y : BilateralField d → ℝ := fun om =>
    Real.exp ‖(H om).restrict (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))‖
  let K : ℕ → BilateralField d → ℝ := fun N om =>
    coeff * (X N om * Y om * (1 + cu * aux_lem_prefix_limit_atom_extraction_Rf M N om))
  have hXm (N : ℕ) : Measurable (X N) :=
    (measurable_from_nat (f := fun n : ℕ => (3 : ℝ) ^ (t * (n : ℝ)))).comp (hLm N)
  have hYm : Measurable Y := ((ContinuousMap.continuous_restrict
    (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))).norm.measurable.comp hIR.1).exp
  have hKm (N : ℕ) : Measurable (K N) :=
    (((hXm N).mul hYm).mul (((aux_lem_prefix_limit_atom_extraction_Rf_measurable M N).const_mul cu).const_add 1)).const_mul coeff
  have hK0 (N : ℕ) (om : BilateralField d) : 0 ≤ K N om := mul_nonneg hcoeff
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_pos _).le)
      (add_nonneg zero_le_one (mul_nonneg hcu (aux_lem_prefix_limit_atom_extraction_eval_nonneg _))))
  refine ⟨K, hKm, hK0, ?_, ?_⟩
  · intro N
    have hfour : ENNReal.ofReal (4 * q) = 4 * ENNReal.ofReal q := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
    have htwo : ENNReal.ofReal (2 * q) = 2 * ENNReal.ofReal q := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
    have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
    have hprod := eLpNorm_mul_mul_one_add_le hp ENNReal.ofReal_ne_top
      (hXm N).aestronglyMeasurable hYm.aestronglyMeasurable (hRn N).1.1
      hcu hBL.le hBI.le hBR
      (by simpa only [← hfour] using hLn N)
      (by simpa only [← hfour] using hIn)
      (by simpa only [← htwo] using (hRn N).2)
    change eLpNorm (coeff • (fun om => X N om * Y om *
      (1 + cu * aux_lem_prefix_limit_atom_extraction_Rf M N om))) _ _ ≤ _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hcoeff]
    exact (mul_le_mul_right hprod _).trans_eq (ENNReal.ofReal_mul hcoeff).symm
  · filter_upwards [hIR.2, hLpre] with om hom hpre
    intro hP N x rho hx hrho hrho1 hcutoff
    have h := prop_conc_affine_macro_bound hd Cp hFE t ht htd M Sreg hdeltaC halpha
      H om hom N (Lmac N om) (hpre N) u hP x rho hx hrho hrho1 hcutoff
    refine h.trans_eq ?_
    dsimp only [K, coeff, X, Y, cu, Cphi]
    rw [Sreg.C_eq_dimensional]
    dsimp only [Cd]
    ring

end
end Paper
