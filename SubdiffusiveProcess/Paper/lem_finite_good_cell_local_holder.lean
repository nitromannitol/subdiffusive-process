module

public import SubdiffusiveProcess.Paper.lfgc_above_holder
public import SubdiffusiveProcess.Paper.lfgc_padded_poincare
public import SubdiffusiveProcess.Paper.lfgc_below_holder

@[expose] public section

/-! The finite-cutoff local Holder estimate on a good padded cell (eq:mfd-finite-good-holder).
The hypotheses are the explicit tests of the finite good event at the cell: the prefix tests
of the cell and of its padded enlargement, one layer bound at the padded root, and the coarse
lower ellipticity of the padded root in its reference. No probability statement is made. -/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The anchored Holder bound (eq:mfd-finite-good-holder) with constant `Cfin` on the cell of
side `3^{-k}` centred at `z`, for a solution on the parent cube `centeredCube zP R hR`. -/
def aux_lem_finite_good_cell_local_holder_bound {d : ℕ} [NeZero d] (alpha : ℝ)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (m k : ℕ) (z zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (Kf : ℝ)
    (u : weakSobolevGraph (centeredCube zP R hR)) (Cfin : ℝ) : Prop :=
  ∃ (U : SpatialCoordinates d → ℝ) (c : ℝ),
    ContinuousOn U (closedCube z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) :
      Set (SpatialCoordinates d)) ∧
    ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d))] U) ∧
    IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => U (z + (3 : ℝ) ^ (-(k : ℤ)) • x) - c) ∧
    cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => U (z + (3 : ℝ) ^ (-(k : ℤ)) • x) - c) ≤
      Cfin * ((3 : ℝ) ^ (-(k : ℤ))) ^ (((2 : ℝ) - (d : ℝ)) / 2) *
          (aux_in_deterministic_onestep_sref M H omega (m + k) k z) ^ (-(1 : ℝ) / 2) *
          Real.sqrt (sobolevCoefficientForm (cutoffPositiveCoefficient M H omega (m + k) zP hR)
            u.val u.val) +
        Cfin * ((3 : ℝ) ^ (-(k : ℤ))) ^ (2 : ℝ) *
          (aux_in_deterministic_onestep_sref M H omega (m + k) k z)⁻¹ * Kf

/-- The bound is monotone in its constant. -/
theorem aux_lem_finite_good_cell_local_holder_bound_mono {d : ℕ} [NeZero d] (alpha : ℝ)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (m k : ℕ) (z zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (u : weakSobolevGraph (centeredCube zP R hR)) (C C' : ℝ) (hCC : C ≤ C')
    (hb : aux_lem_finite_good_cell_local_holder_bound alpha M H omega m k z zP R hR Kf u C) :
    aux_lem_finite_good_cell_local_holder_bound alpha M H omega m k z zP R hR Kf u C' := by
  obtain ⟨U, c, hU, htie, hHol, hnorm⟩ := hb
  refine ⟨U, c, hU, htie, hHol, hnorm.trans ?_⟩
  have hs := aux_in_deterministic_onestep_sref_pos M H omega (m + k) k z
  have hr : 0 < (3 : ℝ) ^ (-(k : ℤ)) := by positivity
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hs.le _)
    exact mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg hr.le _)
  · apply mul_le_mul_of_nonneg_right _ hKf
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 hs.le)
    exact mul_le_mul_of_nonneg_right hCC (Real.rpow_nonneg hr.le _)

/-- A Meyers exponent above the Holder threshold exists. -/
theorem aux_lem_finite_good_cell_local_holder_exponent (d : ℕ) [NeZero d] (alpha : ℝ)
    (halpha : alpha < 1) : ∃ p : ℝ, 2 ≤ p ∧ alpha < 1 - (d : ℝ) / p := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have h1a : 0 < 1 - alpha := by linarith only [halpha]
  refine ⟨2 * (d : ℝ) / (1 - alpha) + 2, ?_, ?_⟩
  · have : 0 ≤ 2 * (d : ℝ) / (1 - alpha) := div_nonneg (by positivity) h1a.le
    linarith only [this]
  · have hp : 0 < 2 * (d : ℝ) / (1 - alpha) + 2 := by positivity
    have hkey : (d : ℝ) < (1 - alpha) * (2 * (d : ℝ) / (1 - alpha) + 2) := by
      rw [mul_add, mul_div_cancel₀ _ h1a.ne']
      linarith only [hd0, h1a]
    have : (d : ℝ) / (2 * (d : ℝ) / (1 - alpha) + 2) < 1 - alpha := by
      rw [div_lt_iff₀ hp]; linarith only [hkey]
    linarith only [this]

/-- At the last wavelength the padded prefix test and the small-oscillation input give the bound. -/
theorem aux_lem_finite_good_cell_local_holder_below {d : ℕ} [NeZero d]
    (W : SmallPerturbationInput d) (p alpha : ℝ) (hp : 2 ≤ p)
    (halpha : 0 < alpha) (halpha1 : alpha < 1) (halphap : alpha < 1 - (d : ℝ) / p)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (k : ℕ)
    (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    (hEta : ∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - ((0 + k : ℕ) : ℤ)) (((3 : ℝ) ^ (-((0 + k : ℕ) : ℤ))) • y))
    (hIR : Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∨ H = 0)
    (sigma eps : ℝ) (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal)
    (Zsc : ℕ → Vec d → ℝ) (goodEvt : ℕ → Vec d → Prop)
    (hPS : primitive_scores d M sigma eps eta Fsc Psc Rsc Dsc Zsc goodEvt)
    (hfin : ∀ (n : ℕ) (y : Vec d), Dsc n y ≠ ⊤)
    (z : SpatialCoordinates d) (lam : ℝ) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hlamSmall : (d : ℝ) * lam ≤ W.osc p) (hdelta1 : M.delta ≤ 1)
    (hpad : ∀ (D : ℕ) (pword : Fin D → OddGridIndex d 1), D = 0 + 1 →
      (Dsc 0 (((3 : ℝ) ^ (0 + k)) •
        descendantCenter 1 z (3 * (3 : ℝ) ^ (-(k : ℤ))) D pword)).toReal ≤ lam * (D : ℝ))
    (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hsub : Metric.closedBall z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2) ⊆
      (centeredCube zP R hR : Set (SpatialCoordinates d)))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hF : Measurable F) (hKf : 0 ≤ Kf)
    (hbound : ∀ x ∈ (centeredCube zP R hR : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (u : weakSobolevGraph (centeredCube zP R hR))
    (heq : ∀ psi : killedSobolevGraph (centeredCube zP R hR),
      sobolevCoefficientForm (cutoffPositiveCoefficient M H omega (0 + k) zP hR) u.val psi.val =
        ∫ x in (centeredCube zP R hR : Set (SpatialCoordinates d)), F x * psi.val.1 x) :
    aux_lem_finite_good_cell_local_holder_bound alpha M H omega 0 k z zP R hR Kf u
      ((((d : ℝ) + 1) ^ alpha + 1) * W.CMorrey p alpha * W.C p * Real.exp ((d : ℝ) + 2)) := by
  have hrN : (3 : ℝ) ^ (-(k : ℤ)) = (3 : ℝ) ^ (-((0 + k : ℕ) : ℤ)) := by rw [Nat.zero_add]
  have hpad1 : ∀ w : Fin 1 → OddGridIndex d 1,
      Dsc 0 (((3 : ℝ) ^ (0 + k)) • descendantCenter 1 z (3 * (3 : ℝ) ^ (-(k : ℤ))) 1 w) ≠ ⊤ ∧
      (Dsc 0 (((3 : ℝ) ^ (0 + k)) •
        descendantCenter 1 z (3 * (3 : ℝ) ^ (-(k : ℤ))) 1 w)).toReal ≤ lam := by
    intro w
    refine ⟨hfin _ _, ?_⟩
    simpa only [Nat.cast_one, mul_one] using hpad 1 w rfl
  have hbelow := lfgc_below_holder W p alpha hp halpha halpha1 halphap M H omega (0 + k) eta hEta
    hIR sigma eps Fsc Psc Rsc Dsc Zsc goodEvt hPS ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) hrN z
    lam hlam hlam1 hlamSmall hdelta1 hpad1 zP R hR hsub F Kf hF hKf hbound u heq
  have hsEq : aux_in_deterministic_onestep_sref M H omega (0 + k) ((0 + k : ℕ) : ℤ) z =
      aux_in_deterministic_onestep_sref M H omega (0 + k) (k : ℤ) z := by
    simp only [Nat.zero_add]
  obtain ⟨U, c, hU, htie, hHol, hnorm⟩ := hbelow
  refine ⟨U, c, hU, htie, hHol, ?_⟩
  rw [hsEq] at hnorm
  exact hnorm

/-- Scalar bookkeeping for the above-wavelength bound after the padded Poincare conversion. -/
theorem aux_lem_finite_good_cell_local_holder_scalar (Ca Cp X osc A B : ℝ) (hCa : 0 ≤ Ca)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hX : X ≤ Ca * (osc + B)) (hosc : osc ≤ Cp * A) :
    X ≤ Ca * max Cp 1 * A + Ca * max Cp 1 * B := by
  have h1 : Ca * Cp ≤ Ca * max Cp 1 := mul_le_mul_of_nonneg_left (le_max_left _ _) hCa
  have h2 : Ca ≤ Ca * max Cp 1 := le_mul_of_one_le_right hCa (le_max_right _ _)
  calc X ≤ Ca * (osc + B) := hX
    _ ≤ Ca * (Cp * A + B) := mul_le_mul_of_nonneg_left (add_le_add hosc le_rfl) hCa
    _ = (Ca * Cp) * A + Ca * B := by ring
    _ ≤ Ca * max Cp 1 * A + Ca * max Cp 1 * B :=
      add_le_add (mul_le_mul_of_nonneg_right h1 hA) (mul_le_mul_of_nonneg_right h2 hB)

/-- Above the wavelength, the iteration bound and the padded Poincare bound give the estimate. -/
theorem aux_lem_finite_good_cell_local_holder_above {d : ℕ} [NeZero d] (alpha Ca Cp : ℝ)
    (hCa : 0 ≤ Ca) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (m k : ℕ) (z zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (u : weakSobolevGraph (centeredCube zP R hR)) (U : SpatialCoordinates d → ℝ)
    (hsub : Metric.closedBall z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2) ⊆
      (centeredCube zP R hR : Set (SpatialCoordinates d)))
    (hU : ContinuousOn U (centeredCube zP R hR : Set (SpatialCoordinates d)))
    (huU : (u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube zP R hR : Set (SpatialCoordinates d))] U)
    (hHol : IsHolderOn alpha
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => U (z + (3 : ℝ) ^ (-(k : ℤ)) • x) - U z))
    (hnorm : cAlphaNorm alpha
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => U (z + (3 : ℝ) ^ (-(k : ℤ)) • x) - U z) ≤
        Ca * (normalizedL2On (Metric.ball z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2))
              (fun y => U y - (volume.real (Metric.ball z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2)))⁻¹ *
                ∫ v in Metric.ball z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2), U v) +
            ((3 : ℝ) ^ (-(k : ℤ))) ^ 2 *
              (aux_in_deterministic_onestep_sref M H omega (m + k) k z)⁻¹ * Kf))
    (hosc : normalizedL2On (Metric.ball z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2))
        (fun y => U y - (volume.real (Metric.ball z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2)))⁻¹ *
          ∫ v in Metric.ball z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2), U v) ≤
        Cp * ((3 : ℝ) ^ (-(k : ℤ))) ^ (((2 : ℝ) - d) / 2) *
          (aux_in_deterministic_onestep_sref M H omega (m + k) (k : ℤ) z) ^ (-(1 : ℝ) / 2) *
          Real.sqrt (sobolevCoefficientForm (cutoffPositiveCoefficient M H omega (m + k) zP hR)
            u.val u.val)) :
    aux_lem_finite_good_cell_local_holder_bound alpha M H omega m k z zP R hR Kf u
      (Ca * max Cp 1) := by
  have hr : 0 < (3 : ℝ) ^ (-(k : ℤ)) := by positivity
  have hs := aux_in_deterministic_onestep_sref_pos M H omega (m + k) k z
  have hball : Metric.closedBall z ((3 : ℝ) ^ (-(k : ℤ)) / 2) ⊆
      (centeredCube zP R hR : Set (SpatialCoordinates d)) :=
    (Metric.closedBall_subset_closedBall (by linarith only [hr])).trans hsub
  have hopen : (centeredCube z ((3 : ℝ) ^ (-(k : ℤ))) hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube zP R hR : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_closedBall.trans hball
  refine ⟨U, U z, hU.mono hball, ae_restrict_of_ae_restrict_of_subset hopen huU, hHol, ?_⟩
  rw [Real.rpow_two]
  have hscal := aux_lem_finite_good_cell_local_holder_scalar Ca Cp _ _ _ _ hCa
    (mul_nonneg (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hs.le _))
      (Real.sqrt_nonneg _))
    (mul_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.2 hs.le)) hKf) hnorm
    (hosc.trans_eq (by ring))
  exact hscal.trans_eq (by ring)

/-- **eq:mfd-finite-good-holder.** On a cell whose padded enlargement lies in the parent and
which passes the finite good-event tests, every bounded-source finite-cutoff solution on the
parent has an anchored `C^α` representative on the cell, bounded by the parent energy and the
source with a deterministic constant. -/
theorem lem_finite_good_cell_local_holder
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (Poincare : _root_.SubdiffusiveProcess.Paper.in_poincare d hd I)
    (MeyersMorrey : SmallPerturbationInput d)
    (Det : _root_.SubdiffusiveProcess.Paper.deterministic_good_scale_input d)
    (alpha sigma cell : ℝ) (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (hsigma32 : sigma ≤ 1 / 32) (hcell : 0 < cell) :
    ∃ Cfin t0 delta1 : ℝ, 0 < Cfin ∧ 0 < t0 ∧ 0 < delta1 ∧
    ∀ (eps lam lamDet : ℝ), eps ∈ Set.Ioo (0 : ℝ) 1 → eps ≤ t0 → 0 ≤ lam → lam ≤ lamDet →
      lamDet ≤ t0 →
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), in_responses d M → M.delta ≤ delta1 →
    ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
      (m k : ℕ) (z : SpatialCoordinates d) (eta : _root_.SubdiffusiveProcess.Model.PotentialSample d),
      (∀ (i : ℕ) (y : SpatialCoordinates d),
        eta i y = omega ((i : ℤ) - ((m + k : ℕ) : ℤ)) (((3 : ℝ) ^ (-((m + k : ℕ) : ℤ))) • y)) →
      (Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∨ H = 0) →
    ∀ (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
      (goodEvt : ℕ → Vec d → Prop),
      primitive_scores d M sigma eps eta Fsc Psc Rsc Dsc Zsc goodEvt →
      (∀ (n : ℕ) (y : Vec d), Dsc n y ≠ ⊤) →
      (∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), 1 ≤ DA → k + DA ≤ m + k →
        ∑ l ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA),
            Zsc (((m + k : ℕ) : ℤ) - l).toNat
              (((3 : ℝ) ^ (m + k)) • descendantCenter 1 z ((3 : ℝ) ^ (-(k : ℤ))) DA dword) <
          lam * DA ∧
        ∑ l ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA),
            (Dsc (((m + k : ℕ) : ℤ) - l).toNat
              (((3 : ℝ) ^ (m + k)) • descendantCenter 1 z ((3 : ℝ) ^ (-(k : ℤ))) DA dword)).toReal <
          lam * DA) →
      (∀ (D : ℕ) (pword : Fin D → OddGridIndex d 1), D = m + 1 →
        (Dsc 0 (((3 : ℝ) ^ (m + k)) •
          descendantCenter 1 z (3 * (3 : ℝ) ^ (-(k : ℤ))) D pword)).toReal ≤ lam * (D : ℝ)) →
      |omega (-((k : ℤ) - 1)) z| ≤ 1 →
      (∀ h3 : 0 < 3 * (3 : ℝ) ^ (-(k : ℤ)),
        cell * aux_in_deterministic_onestep_sref M H omega (m + k) ((k : ℤ) - 1) z ≤
          I.lam z (3 * (3 : ℝ) ^ (-(k : ℤ))) h3
            (cutoffPositiveCoefficient M H omega (m + k) z h3)
            z (3 * (3 : ℝ) ^ (-(k : ℤ))) sigma 2) →
    ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
      Metric.closedBall z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2) ⊆
        (centeredCube zP R hR : Set (SpatialCoordinates d)) →
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), Measurable F → 0 ≤ Kf →
      (∀ x ∈ (centeredCube zP R hR : Set (SpatialCoordinates d)), |F x| ≤ Kf) →
    ∀ u : weakSobolevGraph (centeredCube zP R hR),
      (∀ psi : killedSobolevGraph (centeredCube zP R hR),
        sobolevCoefficientForm (cutoffPositiveCoefficient M H omega (m + k) zP hR) u.val psi.val =
          ∫ x in (centeredCube zP R hR : Set (SpatialCoordinates d)), F x * psi.val.1 x) →
    ∃ (U : SpatialCoordinates d → ℝ) (c : ℝ),
      ContinuousOn U (closedCube z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) :
        Set (SpatialCoordinates d)) ∧
      ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d))] U) ∧
      IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + (3 : ℝ) ^ (-(k : ℤ)) • x) - c) ∧
      cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
        (fun x => U (z + (3 : ℝ) ^ (-(k : ℤ)) • x) - c) ≤
        Cfin * ((3 : ℝ) ^ (-(k : ℤ))) ^ (((2 : ℝ) - (d : ℝ)) / 2) *
            (aux_in_deterministic_onestep_sref M H omega (m + k) k z) ^ (-(1 : ℝ) / 2) *
            Real.sqrt (sobolevCoefficientForm (cutoffPositiveCoefficient M H omega (m + k) zP hR)
              u.val u.val) +
          Cfin * ((3 : ℝ) ^ (-(k : ℤ))) ^ (2 : ℝ) *
            (aux_in_deterministic_onestep_sref M H omega (m + k) k z)⁻¹ * Kf := by
  obtain ⟨p, hp2, hp⟩ := aux_lem_finite_good_cell_local_holder_exponent d alpha halpha.2
  obtain ⟨Ca, ta, deltaA, hCa, hta, hdeltaA, hAbove⟩ :=
    lfgc_above_holder d hd I Det alpha sigma halpha hsigma hsigma32
  obtain ⟨Cp, hCp, hPad⟩ := lfgc_padded_poincare hd I Poincare sigma cell hsigma.1
    (by linarith only [hsigma32]) hcell
  have hCb : 0 < (((d : ℝ) + 1) ^ alpha + 1) * MeyersMorrey.CMorrey p alpha *
      MeyersMorrey.C p * Real.exp ((d : ℝ) + 2) := by
    have := MeyersMorrey.CMorrey_pos p alpha
    have := MeyersMorrey.C_pos p
    positivity
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hosc0 : 0 < MeyersMorrey.osc p / d := div_pos (MeyersMorrey.osc_pos p) hd0
  have hCa0 : 0 ≤ Ca := zero_le_one.trans hCa
  refine ⟨max ((((d : ℝ) + 1) ^ alpha + 1) * MeyersMorrey.CMorrey p alpha *
      MeyersMorrey.C p * Real.exp ((d : ℝ) + 2)) (Ca * max Cp 1),
    min ta (min 1 (MeyersMorrey.osc p / d)), min deltaA 1,
    lt_max_of_lt_left hCb, lt_min hta (lt_min one_pos hosc0), lt_min hdeltaA one_pos, ?_⟩
  intro eps lam lamDet heps hepst hlam0 hlamlt hlamDet M Rm hdelta H omega m k z eta hEta hIR
    Fsc Psc Rsc Dsc Zsc goodEvt hPS hfin hpre hpad hlayer hell zP R hR hsub F Kf hF hKf hbound
    u heq
  suffices hb : aux_lem_finite_good_cell_local_holder_bound alpha M H omega m k z zP R hR Kf u
      (max ((((d : ℝ) + 1) ^ alpha + 1) * MeyersMorrey.CMorrey p alpha *
        MeyersMorrey.C p * Real.exp ((d : ℝ) + 2)) (Ca * max Cp 1)) from hb
  have hdelta1 : M.delta ≤ 1 := hdelta.trans (min_le_right _ _)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hlamt : lam ≤ min ta (min 1 (MeyersMorrey.osc p / d)) := hlamlt.trans hlamDet
    have hlam1 : lam ≤ 1 := hlamt.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hlamSmall : (d : ℝ) * lam ≤ MeyersMorrey.osc p := by
      have h := hlamt.trans ((min_le_right _ _).trans (min_le_right _ _))
      rw [le_div_iff₀ hd0] at h
      linarith only [h]
    exact aux_lem_finite_good_cell_local_holder_bound_mono alpha M H omega 0 k z zP R hR Kf hKf
      u _ _ (le_max_left _ _)
      (aux_lem_finite_good_cell_local_holder_below MeyersMorrey p alpha hp2 halpha.1 halpha.2 hp
        M H omega k eta hEta hIR sigma eps Fsc Psc Rsc Dsc Zsc goodEvt hPS hfin z lam hlam0 hlam1
        hlamSmall hdelta1 hpad zP R hR hsub F Kf hF hKf hbound u heq)
  · obtain ⟨U, hU, huU, hHol, hnorm⟩ := hAbove eps lam lamDet heps
      (hepst.trans (min_le_left _ _)) hlam0 hlamlt (hlamDet.trans (min_le_left _ _)) M
      (hdelta.trans (min_le_left _ _)) H omega m k hm eta hEta hIR Fsc Psc Rsc Dsc Zsc goodEvt
      hPS hfin z hpre hpad zP R hR hsub F Kf hF hKf hbound u heq
    have hr : 0 < (3 : ℝ) ^ (-(k : ℤ)) := by positivity
    have hballP : Metric.ball z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2) ⊆
        (centeredCube zP R hR : Set (SpatialCoordinates d)) :=
      Metric.ball_subset_closedBall.trans hsub
    have hosc := hPad M Rm hdelta1 H omega m k z ((3 : ℝ) ^ (-(k : ℤ))) hr (by positivity)
      hlayer (hell _) zP R hR hballP u U (ae_restrict_of_ae_restrict_of_subset hballP huU)
    exact aux_lem_finite_good_cell_local_holder_bound_mono alpha M H omega m k z zP R hR Kf hKf
      u _ _ (le_max_right _ _)
      (aux_lem_finite_good_cell_local_holder_above alpha Ca Cp hCa0 M H omega m k z zP R hR Kf
        hKf u U hsub hU huU hHol hnorm hosc)

end SubdiffusiveProcess.Paper
