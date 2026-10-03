module

public import Mathlib
public import SubdiffusiveProcess.Paper.calib3_HT
public import SubdiffusiveProcess.Paper.calib3_reference
public import SubdiffusiveProcess.Paper.prop_growth_trunc_bank
public import SubdiffusiveProcess.Paper.aux_macro_moment_bank
public import SubdiffusiveProcess.Paper.prop_growth_macro_energy
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Probability.InfraredCharacterizationExistence

@[expose] public section

/-! Stage 3 (calibration): the global-energy bank for the top-block-removed potential `HT_j` on the unit cube.
Analogue of `prop_growth_trunc_bank` (unit cube, `H = HT_j`); the reference factor of `HT_j` is `calib3_reference`. -/

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem calib3_bank :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E)
    (_S : SobolevFoundationalInput d hd) (Q : ℝ), 1 ≤ Q →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M), M.delta ≤ delta0 →
    ∀ (j : ℕ), 0 < j → ∀ (z : SpatialCoordinates d),
    ∃ (Kg : ℕ → BilateralField d → ℝ) (Cg : ℝ),
      (∀ N om, 0 ≤ Kg N om) ∧
      (∀ N, MemLp (Kg N) (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure) ∧
      (∀ N, eLpNorm (Kg N) (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal Cg) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z 1 one_pos : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z 1 one_pos : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z 1 one_pos)),
          ((b : SobolevData (centeredCube z 1 one_pos)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet
            (cutoffPositiveCoefficient M (calib3_HT d j) om N z one_pos) F b u →
          sobolevCoefficientForm
              (cutoffPositiveCoefficient M (calib3_HT d j) om N z one_pos)
              (u : SobolevData (centeredCube z 1 one_pos))
              (u : SobolevData (centeredCube z 1 one_pos)) ≤
            Kg N om * (Kf + Cphi) ^ 2 := by
  intro d hd _ _ E P X S Q hQ
  have hQ2 : 1 ≤ 2 * Q := by linarith
  obtain ⟨Cext, hCext, hext⟩ := (lem_extension d hd E X S).1 (3 / 4) ⟨by norm_num, by norm_num⟩
  obtain ⟨dE, hdE, hgrid⟩ := (lem_extension d hd E X S).2 (1 / 8) (2 * Q) (by norm_num) hQ2
    (5 / 8) ⟨by norm_num, by norm_num⟩
  obtain ⟨dc, hdc, hcoer⟩ := aux_lem_coercivity_compat d hd E P S
  obtain ⟨cdr, hcdr, href⟩ := calib3_reference d hd (2 * (2 * Q)) (by linarith)
  refine ⟨min (min (dc (2 * Q)) dE) cdr, lt_min (lt_min (hdc _ hQ2) hdE) hcdr, ?_⟩
  intro M Rm hδ j hj z
  obtain ⟨H, hH⟩ := exists_infraredCharacterization hd M
  obtain ⟨Kco, hKco, hKmom⟩ := hcoer M Rm H hH z 1 one_pos le_rfl
  obtain ⟨CK, hKmem, hKbd⟩ := hKmom (2 * Q) hQ2 (hδ.trans ((min_le_left _ _).trans (min_le_left _ _)))
  obtain ⟨K, Cb, hKm, hKb, hae⟩ := hgrid M Rm H hH (hδ.trans ((min_le_left _ _).trans (min_le_right _ _))) z 1 one_pos 1
    (fun _ => z)
  have hC0 := aux_aux_macro_moment_bank_Cstar_nonneg d Cext hCext.le
  have hmom := fun N => aux_aux_macro_moment_bank_const_mul_moment (chaosSampleLaw M).toMeasure
    (ENNReal.ofReal (2 * Q)) _ hC0 (K N) Cb (hKm N) (hKb N)
  have hBd := aux_aux_macro_moment_bank_hBd hd E Cext hCext hext M H z 1 one_pos le_rfl K hae
  have hPc := aux_aux_macro_moment_bank_killed_poincare hd z 1 one_pos
  have hRT : MemLp (fun om => aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om) z 1 one_pos)
      (ENNReal.ofReal (2 * (2 * Q))) (chaosSampleLaw M).toMeasure :=
    (href M (hδ.trans (min_le_right _ _)) j hj z).2.2
  have hRH : MemLp (fun om => aux_prop_growth_trunc_bank_refFactor (H om) z 1 one_pos)
      (ENNReal.ofReal (2 * (2 * Q))) (chaosSampleLaw M).toMeasure :=
    (aux_aux_macro_moment_bank_reference hd M H hH (closedCube z 1 one_pos) (2 * (2 * Q))
      (by linarith)).2.2
  have hKgm := fun N => aux_prop_growth_trunc_bank_moment (chaosSampleLaw M).toMeasure Q hQ
    (fun om => aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om) z 1 one_pos)
    (fun om => aux_prop_growth_trunc_bank_refFactor (H om) z 1 one_pos) hRT hRH
    (fun om => aux_aux_macro_moment_bank_Cstar d Cext * K N om) (Kco N) (aux_prop_growth_trunc_bank_c2 z 1 one_pos)
    (aux_prop_growth_trunc_bank_c2_nonneg z 1 one_pos) (aux_aux_macro_moment_bank_Cstar d Cext * Cb) CK
    (hmom N).1 (hmom N).2 (hKmem N) (hKbd N)
  obtain ⟨BG, hBG⟩ : ∃ BG : ℝ≥0∞, BG =
      eLpNorm (fun om => aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om) z 1 one_pos)
          (ENNReal.ofReal (2 * (2 * Q))) (chaosSampleLaw M).toMeasure *
        eLpNorm (fun om => aux_prop_growth_trunc_bank_refFactor (H om) z 1 one_pos)
          (ENNReal.ofReal (2 * (2 * Q))) (chaosSampleLaw M).toMeasure *
        (ENNReal.ofReal (aux_aux_macro_moment_bank_Cstar d Cext * Cb) +
          ENNReal.ofReal (aux_prop_growth_trunc_bank_c2 z 1 one_pos) * ENNReal.ofReal CK) := ⟨_, rfl⟩
  have hBGfin : BG ≠ ⊤ := by
    rw [hBG]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hRT.eLpNorm_lt_top.ne hRH.eLpNorm_lt_top.ne)
      (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩)
  refine ⟨fun N om => aux_prop_growth_trunc_bank_refFactor (calib3_HT d j om) z 1 one_pos *
      aux_prop_growth_trunc_bank_refFactor (H om) z 1 one_pos *
        (|aux_aux_macro_moment_bank_Cstar d Cext * K N om| + aux_prop_growth_trunc_bank_c2 z 1 one_pos * |Kco N om|),
    BG.toReal, ?_, fun N => (hKgm N).1, ?_, ?_⟩
  · intro N om
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (add_nonneg (abs_nonneg _) (mul_nonneg (aux_prop_growth_trunc_bank_c2_nonneg z 1 one_pos) (abs_nonneg _)))
  · intro N
    rw [ENNReal.ofReal_toReal hBGfin, hBG]
    exact (hKgm N).2
  · filter_upwards [hBd] with om hom
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsolve
    exact aux_prop_growth_trunc_bank_energy_bound hd M H (calib3_HT d j) om N z 1 one_pos
      le_rfl hPc (Kco N om) (fun v => ((hKco N om).1 v).2) F Kf hKf hFm hFb phi Cphi hphi hCphi b u
      hsolve (aux_aux_macro_moment_bank_Cstar d Cext * K N om)
      (hom N hPc phi Cphi hphi hCphi b hb)

end Paper
