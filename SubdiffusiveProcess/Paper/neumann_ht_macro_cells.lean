module

public import SubdiffusiveProcess.Paper.neumann_ht_micro_campanato
public import SubdiffusiveProcess.Paper.neumann_ht_energy
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.lane4_lambda_inv_cell_moment

@[expose] public section

/-! Campanato decay above the wavelength for the top-block-removed coefficient, cell by cell
(transplant of `aux_cor_neumann_source_macro_cells`): the cell Poincaré inequality is applied to the
infrared-free coefficient `A^0_{N+j}` (whose discounted ellipticity series has the moments of
`aux_cor_neumann_source_Z_moments`), the energy of `A^0_{N+j}` on the cell is compared to the energy of the
top-block-removed solution (`A^0 ≤ W_j A^{HT_j}`), and the latter is `neumann_ht_energy`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

noncomputable section
namespace Paper

/-- **One cell at one sample.**  The per-cell variance bound for the solution of the coefficient
`aH`, from the cell Poincaré inequality for the comparable coefficient `a0`
(`a0 ≤ Wv aH`), the energy bound of `aH` on the cell, and the discounted ellipticity series of `a0`. -/
theorem aux_neumann_ht_macro_cell_step (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Np : ℕ)
    (om : BilateralField d)
    (aH : PositiveCoefficient (unitNeumannCube d)) (Wv Kv Zv Kf t alpha e e' Cg A : ℝ)
    (hWv : 0 ≤ Wv) (hKv : 0 ≤ Kv) (hZv : 0 ≤ Zv) (ht0 : 0 ≤ t) (hA1 : 1 ≤ A)
    (hAC : P.C ^ 2 * Cg ≤ A) (hexp : 2 + t = e + 2 * alpha + d)
    (he' : 0 < e') (he'e : e' ≤ e) (he'1 : e' ≤ 1)
    (hCgdef : Cg = (1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e')))
    (hab : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om Np
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val y ≤ Wv * aH.val y)
    (hZdef : Zv = ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight e' 1 n *
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ))
        (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
          (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om Np
            (fun _ => (1 / 2 : ℝ)) one_pos) (fun _ => (1 / 2 : ℝ)) 1))
    (hsumm : Summable (fun n : ℕ => Homogenization.Book.Ch02.geometricWeight e' 1 n *
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(n : ℤ))
          (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
            (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om
              Np (fun _ => (1 / 2 : ℝ)) one_pos) (fun _ => (1 / 2 : ℝ)) 1)))
    (v : meanZeroSobolevGraph (unitNeumannCube d))
    (hen : ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ unitNeumannCube d → 0 < rad → rad ≤ 1 →
      localGradientEnergy aH
        (s := Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
        (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤ Kv * Kf ^ 2 * rad ^ t)
    (l : ℕ) (kk : Fin d → ℤ) (hkk : aux_prop_growth_holder_macro_campanato_Adm l kk) :
    aux_prop_growth_holder_macro_campanato_var
        (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) l kk)
        ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
      (aux_prop_growth_holder_macro_campanato_side l ^ alpha *
        ((1 + A * (Wv * Kv + Zv)) * Kf)) ^ 2 *
        volume.real (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) l kk) := by
  set c := aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) l kk with hc
  set s := aux_prop_growth_holder_macro_campanato_side l with hsdef
  have hs0 : 0 < s := aux_prop_growth_holder_macro_campanato_side_pos l
  have hs1 : s ≤ 1 := aux_prop_growth_holder_macro_campanato_side_le_one l
  have hcellT : aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) l kk =
      (centeredCube c s hs0 : Set (SpatialCoordinates d)) :=
    (centeredCube_coe_eq_ball c s hs0).symm
  have hQball : (unitNeumannCube d : Set (SpatialCoordinates d)) =
      ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) := by
    rw [unitNeumannCube, centeredCube_coe_eq_ball]
  have hTQ : (centeredCube c s hs0 : Set (SpatialCoordinates d)) ⊆
      (unitNeumannCube d : Set (SpatialCoordinates d)) := by
    rw [← hcellT, hQball]
    exact aux_prop_growth_holder_macro_campanato_cell_subset _ hkk
  have hle : centeredCube c s hs0 ≤ unitNeumannCube d := hTQ
  have hcQ : c ∈ unitNeumannCube d := by
    apply hTQ
    rw [centeredCube_coe_eq_ball]
    exact mem_ball_self (half_pos hs0)
  have hcoef : ∀ᵐ y ∂volume.restrict (centeredCube c s hs0 : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om Np c
          hs0).val y =
        (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om Np
          (fun _ => (1 / 2 : ℝ)) one_pos).val y := by
    filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae M
        (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om Np c hs0,
      ae_restrict_of_ae_restrict_of_subset hTQ
        (aux_prop_growth_holder_micro_campanato_coeff_ae M
          (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om Np (fun _ => (1 / 2 : ℝ))
          one_pos)] with y h1 h2
    rw [h1, h2]
  have hPc := aux_cor_neumann_source_cell_poincare hd E P c s hs0 hle
    (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om Np
      (fun _ => (1 / 2 : ℝ)) one_pos)
    (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om Np c hs0)
    hcoef
    ⟨(v : SobolevData (unitNeumannCube d)),
      (inf_le_left : meanZeroSobolevGraph (unitNeumannCube d) ≤
        weakSobolevGraph (unitNeumannCube d)) v.property⟩
  have hE1 := hen c (s / 2) hcQ (half_pos hs0) (by linarith)
  have hset : Metric.ball c (s / 2) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)) =
      (centeredCube c s hs0 : Set (SpatialCoordinates d)) := by
    rw [← centeredCube_coe_eq_ball c s hs0]; exact Set.inter_eq_left.2 hTQ
  have hE2 : localGradientEnergy aH (s := (centeredCube c s hs0 : Set (SpatialCoordinates d)))
      (centeredCube c s hs0).isOpen.measurableSet
      (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤ Kv * Kf ^ 2 * (s / 2) ^ t := by
    rw [← aux_cor_neumann_source_energy_congr _ hset
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)]
    exact hE1
  -- the energy of the infrared-free coefficient on the cell
  have hE0 : localGradientEnergy
      (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om Np
        (fun _ => (1 / 2 : ℝ)) one_pos)
      (s := (centeredCube c s hs0 : Set (SpatialCoordinates d)))
      (centeredCube c s hs0).isOpen.measurableSet
      (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
      (Wv * Kv) * Kf ^ 2 * (s / 2) ^ t := by
    have h := localGradientEnergy_le_mul
      (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om Np
        (fun _ => (1 / 2 : ℝ)) one_pos) aH Wv hab
      (centeredCube c s hs0).isOpen.measurableSet
      (sobolevGradient (v : SobolevData (unitNeumannCube d)))
    calc _ ≤ Wv * localGradientEnergy aH (s := (centeredCube c s hs0 : Set (SpatialCoordinates d)))
          (centeredCube c s hs0).isOpen.measurableSet
          (sobolevGradient (v : SobolevData (unitNeumannCube d))) := h
      _ ≤ Wv * (Kv * Kf ^ 2 * (s / 2) ^ t) := mul_le_mul_of_nonneg_left hE2 hWv
      _ = (Wv * Kv) * Kf ^ 2 * (s / 2) ^ t := by ring
  have hlam := aux_cor_neumann_source_lam_cell E M
    (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om Np l kk hkk e e' he' he'e he'1 hsumm
  have hV := aux_prop_growth_holder_macro_campanato_cell_volume (fun _ : Fin d => (1 / 2 : ℝ)) l kk
  rw [hV, hcellT]
  exact aux_cor_neumann_source_cell_alg d _ P.C s _ _ (Wv * Kv) Kf t e alpha Zv Cg A
    hs0 (inv_nonneg.2 (E.lam_pos _ _ _ _ _ _ _ _).le) (mul_nonneg hWv hKv) hZv ht0 hA1 hAC hexp
    hPc hE0 (by rw [← hCgdef] at hlam; rw [hZdef]; exact hlam)

/-! Per-cell Campanato variance bound for the top-block-removed coefficient: model-level assembly and
the smallness threshold (chosen before `j`). -/

/-- **Model-level assembly of the per-cell variance bound.** -/
theorem aux_neumann_ht_macro_cells_model (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (j k : ℕ)
    (ps : Fin k → ℝ) (t alpha e e' : ℝ) (hps : ∀ i, 1 ≤ ps i)
    (ht0 : 0 ≤ t) (he' : 0 < e') (he'e : e' ≤ e) (he'1 : e' ≤ 1)
    (hexp : 2 + t = e + 2 * alpha + d)
    (K : ℕ → BilateralField d → ℝ) (CK : Fin k → ℝ) (hK0 : ∀ N om, 0 ≤ K N om)
    (hKL : ∀ i N, MemLp (K N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure)
    (hKB : ∀ i N, eLpNorm (K N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CK i))
    (hen : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
        AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
        (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
        SolvesNeumann (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j)
          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) F v →
        ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ unitNeumannCube d → 0 < rad → rad ≤ 1 →
          localGradientEnergy
            (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j)
              (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
            (s := Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
            (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
          K N om * Kf ^ 2 * rad ^ t)
    (W : BilateralField d → ℝ) (hW1 : ∀ om, 1 ≤ W om)
    (hWpt : ∀ om (x : SpatialCoordinates d), (∀ i, -(1 / 2 : ℝ) ≤ x i ∧ x i ≤ 3 / 2) →
      Real.exp |calib3_HT d j om x| ≤ W om)
    (CW : Fin k → ℝ) (hCW0 : ∀ i, 0 ≤ CW i)
    (hWL : ∀ i, MemLp W (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure)
    (hWB : ∀ i, eLpNorm W (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CW i))
    (Z : ℕ → BilateralField d → ℝ) (CZ : ℝ)
    (hZdef : ∀ N om, Z N om = ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight e' 1 n *
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ))
        (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
          (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om
            (N + j) (fun _ => (1 / 2 : ℝ)) one_pos) (fun _ => (1 / 2 : ℝ)) 1))
    (hZL : ∀ i N, MemLp (Z N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure)
    (hZB : ∀ i N, eLpNorm (Z N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal CZ)
    (hsumm : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      Summable (fun n : ℕ => Homogenization.Book.Ch02.geometricWeight e' 1 n *
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(n : ℤ))
          (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
            (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om
              (N + j) (fun _ => (1 / 2 : ℝ)) one_pos) (fun _ => (1 / 2 : ℝ)) 1))) :
    ∃ (Xc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
      (∀ N om, 0 ≤ Xc N om) ∧
      (∀ i N, MemLp (Xc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
      (∀ i N, eLpNorm (Xc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cbound i)) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
          AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j)
            (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) F v →
          ∀ l : ℕ, l ≤ N + j → ∀ kk : Fin d → ℤ, aux_prop_growth_holder_macro_campanato_Adm l kk →
            aux_prop_growth_holder_macro_campanato_var
                (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) l kk)
                ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
              (aux_prop_growth_holder_macro_campanato_side l ^ alpha * (Xc N om * Kf)) ^ 2 *
                volume.real
                  (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) l kk) := by
  have hW0 : ∀ om, 0 ≤ W om := fun om => le_trans zero_le_one (hW1 om)
  have hZ0 : ∀ N om, 0 ≤ Z N om := by
    intro N om; rw [hZdef]
    exact tsum_nonneg fun n => mul_nonneg ((aux_lane4_lambda_inv_moments_weight_sum e' he').2.2 n)
      (aux_lane4_lambda_inv_moments_Y_nonneg _ _)
  obtain ⟨Cg, hCgdef⟩ : ∃ Cg : ℝ, Cg = (1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e')) :=
    ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = max 1 (P.C ^ 2 * Cg) := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hAC : P.C ^ 2 * Cg ≤ A := by rw [hAdef]; exact le_max_right _ _
  have hA0 : 0 ≤ A := by linarith
  -- the weighted energy constant
  obtain ⟨WK, hWKdef⟩ : ∃ WK : ℕ → BilateralField d → ℝ,
      WK = fun N om => W om * (1 + K N om) := ⟨_, rfl⟩
  have hWKmom : ∀ (i : Fin k) (N : ℕ),
      MemLp (WK N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (WK N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (max (CW i) (max (CK i) 0) * (1 + max (CW i) (max (CK i) 0))) := by
    intro i N
    have hCp0 : 0 ≤ max (CW i) (max (CK i) 0) := le_trans (hCW0 i) (le_max_left _ _)
    have h := aux_rem_resolved_UV_moment (chaosSampleLaw M).toMeasure (ps i)
      (max (CW i) (max (CK i) 0)) (hps i) hCp0 W (K N) (hWL i) (hKL i N)
      ((hWB i).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      ((hKB i N).trans (ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_right _ _))))
    rw [hWKdef]
    exact h
  obtain ⟨Xc, hXcdef⟩ : ∃ Xc : ℕ → BilateralField d → ℝ,
      Xc = fun N om => 1 + A * (WK N om + Z N om) := ⟨_, rfl⟩
  have hWK0 : ∀ N om, 0 ≤ WK N om := by
    intro N om; rw [hWKdef]
    exact mul_nonneg (hW0 om) (by linarith [hK0 N om])
  have hXc0 : ∀ N om, 0 ≤ Xc N om := by
    intro N om; rw [hXcdef]
    have := mul_nonneg hA0 (add_nonneg (hWK0 N om) (hZ0 N om))
    linarith
  have hXcmom := fun (i : Fin k) (N : ℕ) =>
    aux_prop_growth_holder_assembly_moment (chaosSampleLaw M).toMeasure (hps i) (WK N) (Z N) hA0
      (hWKmom i N).1 (hZL i N) (hWKmom i N).2 (hZB i N)
  refine ⟨Xc, fun i => 1 + A * (max (max (CW i) (max (CK i) 0) * (1 + max (CW i) (max (CK i) 0))) 0
      + max CZ 0), hXc0, fun i N => by rw [hXcdef]; exact (hXcmom i N).1,
    fun i N => by rw [hXcdef]; exact (hXcmom i N).2, ?_⟩
  filter_upwards [hen, hsumm] with om hom hsumm'
  intro N F Kf hKf hFm hFb hmean v hsol l _hl kk hkk
  have hab := aux_neumann_ht_coeff_compare M j (N + j) om (W om) (hWpt om)
  have hstep := aux_neumann_ht_macro_cell_step d hd E P M (N + j) om
    (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) (fun _ => (1 / 2 : ℝ)) one_pos)
    (W om) (K N om) (Z N om) Kf t alpha e e' Cg A (hW0 om) (hK0 N om) (hZ0 N om) ht0 hA1 hAC hexp
    he' he'e he'1 hCgdef hab (hZdef N om) (hsumm' N) v
    (fun x rad hx hrad hrad1 => hom N F Kf hKf hFm hFb hmean v hsol x rad hx hrad hrad1) l kk hkk
  refine hstep.trans ?_
  have hle : 1 + A * (W om * K N om + Z N om) ≤ Xc N om := by
    rw [hXcdef, hWKdef]
    have : W om * K N om ≤ W om * (1 + K N om) := by nlinarith [hW0 om]
    have := mul_le_mul_of_nonneg_left (add_le_add_right this (Z N om)) hA0
    linarith
  have hs : 0 ≤ aux_prop_growth_holder_macro_campanato_side l ^ alpha :=
    Real.rpow_nonneg (aux_prop_growth_holder_macro_campanato_side_pos l).le _
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (mul_nonneg hs (mul_nonneg (by nlinarith [mul_nonneg hA0 (add_nonneg
      (mul_nonneg (hW0 om) (hK0 N om)) (hZ0 N om))]) hKf))
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle hKf) hs) 2)
    measureReal_nonneg

/-! Per-cell variance bound (thresholds) and the macro Campanato estimate for the top-block-removed
coefficient. -/

theorem neumann_ht_macro_cells (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg),
        M.delta ≤ delta0 → ∀ j : ℕ, 0 < j →
        ∃ (Xc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
          (∀ N om, 0 ≤ Xc N om) ∧
          (∀ i N, MemLp (Xc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
          (∀ i N, eLpNorm (Xc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cbound i)) ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
            ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
              AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
              (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
                |F x| ≤ Kf) →
              (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
            ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
              SolvesNeumann (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j)
                (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) F v →
              ∀ l : ℕ, l ≤ N + j → ∀ kk : Fin d → ℤ,
                aux_prop_growth_holder_macro_campanato_Adm l kk →
                aux_prop_growth_holder_macro_campanato_var
                    (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) l kk)
                    ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
                  (aux_prop_growth_holder_macro_campanato_side l ^ alpha * (Xc N om * Kf)) ^ 2 *
                    volume.real
                      (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) l kk) := by
  obtain ⟨t, e, ht1, htd, he, hexp⟩ := aux_neumann_ht_micro_campanato_exponents d alpha ha1
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨e', he'def⟩ : ∃ e' : ℝ, e' = min e 1 := ⟨_, rfl⟩
  have he' : 0 < e' := by rw [he'def]; exact lt_min he one_pos
  have he'e : e' ≤ e := by rw [he'def]; exact min_le_left _ _
  have he'1 : e' ≤ 1 := by rw [he'def]; exact min_le_right _ _
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => le_trans zero_le_one (hps i)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = 2 * (d : ℝ) / e' + ∑ i, ps i + 1 := ⟨_, rfl⟩
  have hdq0 : 0 ≤ 2 * (d : ℝ) / e' := div_nonneg (by positivity) he'.le
  have hQ1 : 1 ≤ Q := by rw [hQdef]; linarith
  have hDQ : 2 * (d : ℝ) ≤ e' * Q := by
    rw [hQdef, mul_add, mul_add, mul_div_cancel₀ _ he'.ne']
    have : 0 ≤ e' * ∑ i, ps i := mul_nonneg he'.le hsum0
    linarith
  have hpQ : ∀ i, ps i ≤ Q := by
    intro i
    have := Finset.single_le_sum (fun j _ => le_trans zero_le_one (hps j)) (Finset.mem_univ i)
    rw [hQdef]; linarith
  have hps2 : ∀ i : Fin k, 1 ≤ 2 * ps i := fun i => by linarith [hps i]
  obtain ⟨Q2, hQ2def⟩ : ∃ Q2 : ℝ, Q2 = 2 * (1 + ∑ i, ps i) := ⟨_, rfl⟩
  have hQ21 : 1 ≤ Q2 := by rw [hQ2def]; linarith
  have hq2i : ∀ i : Fin k, 2 * ps i ≤ Q2 := by
    intro i
    have := Finset.single_le_sum (fun j _ => le_trans zero_le_one (hps j)) (Finset.mem_univ i)
    rw [hQ2def]; linarith
  obtain ⟨deltaE, hdeltaE, hEA⟩ :=
    neumann_ht_energy d hd E _P _X _W D t k (fun i => 2 * ps i) ht1 htd hps2
  obtain ⟨deltaZ, hdeltaZ, hZ⟩ := aux_cor_neumann_source_Z_moments d hd E e' Q he' hQ1 hDQ
  obtain ⟨cdw, hcdw, hWeight⟩ := aux_neumann_ht_weight d hd Q2 hQ21
  refine ⟨min deltaE (min deltaZ cdw), lt_min hdeltaE (lt_min hdeltaZ hcdw), ?_⟩
  intro M Rm Sreg It hdelta j hj
  have hdE : M.delta ≤ deltaE := hdelta.trans (min_le_left _ _)
  have hdZ : M.delta ≤ deltaZ := hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdW : M.delta ≤ cdw := hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨K, CK, hK0, hKL, hKB, hen⟩ := hEA M Rm Sreg It hdE j hj
  obtain ⟨CZ, hZN⟩ := hZ M Rm (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
    (InfraredAdmissible.zero M) hdZ
  obtain ⟨W, hWm, hW1, hWmem, hWpt⟩ := hWeight M hdW j hj
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℕ → BilateralField d → ℝ, ∀ N om, Z N om =
      ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight e' 1 n *
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(n : ℤ))
          (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
            (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om
              (N + j) (fun _ => (1 / 2 : ℝ)) one_pos) (fun _ => (1 / 2 : ℝ)) 1) :=
    ⟨fun N om => ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight e' 1 n *
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(n : ℤ))
          (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
            (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om
              (N + j) (fun _ => (1 / 2 : ℝ)) one_pos) (fun _ => (1 / 2 : ℝ)) 1),
      fun _ _ => rfl⟩
  have hZfun : ∀ N, Z N = fun om => ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight e' 1 n *
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(n : ℤ))
          (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
            (cutoffPositiveCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om
              (N + j) (fun _ => (1 / 2 : ℝ)) one_pos) (fun _ => (1 / 2 : ℝ)) 1) :=
    fun N => funext (hZdef N)
  have hWL : ∀ i : Fin k, MemLp W (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure :=
    fun i => hWmem.mono_exponent (ENNReal.ofReal_le_ofReal (hq2i i))
  exact aux_neumann_ht_macro_cells_model d hd E _P M j k ps t alpha e e' hps ht0 he' he'e he'1
    (by linarith [hexp]) K CK hK0 hKL hKB hen W hW1 hWpt
    (fun i => (eLpNorm W (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure).toReal)
    (fun i => ENNReal.toReal_nonneg) hWL
    (fun i => le_of_eq (ENNReal.ofReal_toReal (hWL i).eLpNorm_lt_top.ne).symm) Z CZ hZdef
    (fun i N => by
      rw [hZfun N]; exact (hZN (N + j)).1.mono_exponent (ENNReal.ofReal_le_ofReal (hpQ i)))
    (fun i N => by
      rw [hZfun N]
      exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (hpQ i))).trans (hZN (N + j)).2.1)
    (ae_all_iff.2 fun N => (hZN (N + j)).2.2)

end Paper
