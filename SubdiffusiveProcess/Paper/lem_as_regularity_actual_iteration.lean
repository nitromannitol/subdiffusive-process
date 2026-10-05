module

public import SubdiffusiveProcess.Paper.lem_as_regularity_translated_iteration
public import SubdiffusiveProcess.Paper.lem_as_regularity_actual_native_error
public import SubdiffusiveProcess.Paper.lem_as_regularity_native_reference
public import SubdiffusiveProcess.Analysis.NativeScoreAllowance

@[expose] public section

/-! Rooted deterministic iteration for the actual cutoff coefficient, folded
at a physical root. The original native score allowance supplies the count,
error and reference budgets. This does not assert a mesh or global PDE bound.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Set SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Fixed positive thresholds can make the deterministic baseline as small as required. -/
theorem aux_lem_as_regularity_actual_iteration_parameters (lam tau : ℝ)
    (hlam : 0 < lam) (htau : 0 < tau) :
    ∃ eps : ℝ, eps ∈ Ioo (0 : ℝ) 1 ∧ ∀ delta : ℝ,
      0 ≤ delta → delta ≤ min 1 eps →
      delta ^ 2 + eps ^ 8 ≤ min (2 * lam) tau := by
  let eps := min (1 / 2 : ℝ) (min (lam / 2) (tau / 2))
  have heps : 0 < eps := lt_min (by norm_num) (lt_min (half_pos hlam) (half_pos htau))
  have heps1 : eps ≤ 1 / 2 := min_le_left _ _
  have hepsl : eps ≤ lam / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hepst : eps ≤ tau / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨eps, ⟨heps, by linarith only [heps1]⟩, ?_⟩
  intro delta hd hdmax
  have hd1 := hdmax.trans (min_le_left _ _)
  have hde := hdmax.trans (min_le_right _ _)
  have he8 : eps ^ 8 ≤ eps := pow_le_of_le_one heps.le (by linarith only [heps1]) (by norm_num)
  apply le_min
  · nlinarith only [hd, hd1, hde, he8, hepsl, hlam]
  · nlinarith only [hd, hd1, hde, he8, hepst]

/-- The fixed cost of folding the two-exponent error is positive. -/
theorem aux_lem_as_regularity_actual_iteration_fold_pos (d : ℕ) :
    0 < 1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) := by
  have hden : 0 < (3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) (by norm_num))
  positivity

/-- The actual original-score allowance supplies a rooted folded energy estimate. -/
theorem lem_as_regularity_actual_iteration (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (D : lane4_deterministic_good_scale_input d)
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    ∃ eps rate delta0 C : ℝ,
      eps ∈ Ioo (0 : ℝ) 1 ∧ 0 < rate ∧ 0 < delta0 ∧ 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (F P R Draw : ℕ → ℕ → Vec d → BilateralField d → ℝ≥0∞)
        (Z : ℕ → ℕ → Vec d → BilateralField d → ℝ)
        (good : ℕ → ℕ → Vec d → BilateralField d → Prop),
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (N i : ℕ) (y : Vec d),
        eta N omega i y = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
        primitive_scores d M (1 / 32) eps (eta N omega)
          (fun m y => F N m y omega) (fun m y => P N m y omega)
          (fun m y => R N m y omega) (fun m y => Draw N m y omega)
          (fun m y => Z N m y omega) (fun m y => good N m y omega)) →
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N m n : ℕ) (hnm : n ≤ m) (w : SpatialCoordinates d) (I J : Finset (Fin d)),
        nativeScoreAllowance (fun j => Z N j ((3 : ℝ) ^ N • w) omega)
          (fun j => Draw N j ((3 : ℝ) ^ N • w) omega) m rate ≤ m - n →
      ∀ (hR : (0 : ℝ) < 3 ^ m) (g : SpatialCoordinates d → Fin d → ℝ),
        MemHolder (centeredCube ((3 : ℝ) ^ N • w) ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))
          (1 / 2) g →
      ∀ _data : ScalarTriadicCoeffData (fun y => cutoffCoefficient M H omega N
          (coordinateFold w I J ((3 : ℝ) ^ (-(N : ℤ)) • (y + 0) + w))),
      ∀ fc : PositiveCoefficient (centeredCube ((3 : ℝ) ^ N • w) ((3 : ℝ) ^ m) hR),
        (∀ᵐ y ∂volume.restrict (openCubeSet (originCube d (m : ℤ))),
          cutoffCoefficient M H omega N (coordinateFold w I J ((3 : ℝ) ^ (-(N : ℤ)) • y + w)) =
            fc.val (fun i => ((3 : ℝ) ^ N • w) i + y i)) →
      ∀ (u : weakSobolevGraph (centeredCube ((3 : ℝ) ^ N • w) ((3 : ℝ) ^ m) hR))
        (hgrad : HilbertGradient (centeredCube ((3 : ℝ) ^ N • w) ((3 : ℝ) ^ m) hR)),
        (∀ i, (hgrad i : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube ((3 : ℝ) ^ N • w) ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
            fun x => g x i) →
        (∀ φ : killedSobolevGraph (centeredCube ((3 : ℝ) ^ N • w) ((3 : ℝ) ^ m) hR),
          sobolevCoefficientForm fc (u : SobolevData _) (φ : SobolevData _) =
            -inner ℝ hgrad (subspaceGradient (killedSobolevGraph
              (centeredCube ((3 : ℝ) ^ N • w) ((3 : ℝ) ^ m) hR)) φ)) →
        normalizedEnergyNorm fc (centeredCube ((3 : ℝ) ^ N • w) ((3 : ℝ) ^ n) (by positivity)).isOpen.measurableSet
          (sobolevGradient (u : SobolevData _)) ≤
          C * (3 : ℝ) ^ (rho * ((m : ℝ) - n)) *
            (normalizedEnergyNorm fc (centeredCube ((3 : ℝ) ^ N • w) ((3 : ℝ) ^ m) hR).isOpen.measurableSet
              (sobolevGradient (u : SobolevData _)) +
              (Real.sqrt (aux_in_deterministic_onestep_sref M H omega N ((N : ℤ) - m) w))⁻¹ *
                ((3 : ℝ) ^ ((m : ℝ) / 2) * halfHolderSeminorm
                  (centeredCube ((3 : ℝ) ^ N • w) ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g)) := by
  obtain ⟨Cg, dg, hCg, hdg, hgood⟩ := in_deterministic_good_scale_transfer d E (1 / 32)
    (by norm_num) le_rfl
  let Cf : ℝ := 1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1)
  have hCf : 0 < Cf := aux_lem_as_regularity_actual_iteration_fold_pos d
  obtain ⟨lam, tau, C, hlam, htau, htau1, hC, hiter⟩ :=
    lem_as_regularity_translated_iteration d hd D (Cf * Cg) rho (mul_pos hCf hCg) hrho hrho1
  obtain ⟨eps, heps, hbase⟩ := aux_lem_as_regularity_actual_iteration_parameters lam tau hlam htau
  refine ⟨eps, lam * tau / 2, min dg (min 1 eps), C, heps, by positivity,
    lt_min hdg (lt_min zero_lt_one heps.1), hC, ?_⟩
  intro M Rm H hIR hdelta eta F P R Draw Z good hEta hPS
  let sN := fun (N : ℕ) (k : ℤ) (w : SpatialCoordinates d) (omega : BilateralField d) =>
    if k ≤ (N : ℤ) then aux_in_deterministic_onestep_sref M H omega N k w else 1
  have hsN := hgood M H hIR (hdelta.trans (min_le_left _ _)) eps heps
    eta F P R Draw Z good hEta hPS sN (fun N k w omega => by rfl)
  have hb := hbase M.delta M.shellPrefix.delta_pos.le (hdelta.trans (min_le_right _ _))
  have hdl : M.delta ^ 2 ≤ 2 * lam :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ eps ^ 8)).trans (hb.trans (min_le_left _ _))
  filter_upwards [hsN, hEta, hPS] with omega hgoodw hEtaw hPSw
  intro N m n hnm w I J hallow hR g hg data fc hae u hgrad hgae hweak
  obtain ⟨hgap, hfin, hZsum, hDsum⟩ := nativeScoreAllowance_window
    (fun j => Z N j ((3 : ℝ) ^ N • w) omega)
    (fun j => Draw N j ((3 : ℝ) ^ N • w) omega) m n (lam * tau / 2) hnm hallow
  let a := fun y => cutoffCoefficient M H omega N
    (coordinateFold w I J ((3 : ℝ) ^ (-(N : ℤ)) • y + w))
  have hac : Continuous a := (cutoffCoefficient_continuous M H omega N).comp
    ((coordinateFold_continuous w I J).comp
      (by fun_prop : Continuous (fun y : Vec d => (3 : ℝ) ^ (-(N : ℤ)) • y + w)))
  have hap : ∀ y, 0 < a y := fun y => cutoffCoefficient_pos M H omega N _
  let ref := fun j : ℕ => aux_in_deterministic_onestep_sref M H omega N ((N : ℤ) - (j + 2 : ℕ)) w
  have hroot : ref (m - 2) = aux_in_deterministic_onestep_sref M H omega N ((N : ℤ) - m) w := by
    dsimp only [ref]
    rw [show m - 2 + 2 = m by omega]
  have hlen : 0 ≤ (m : ℝ) - n := sub_nonneg.mpr (by exact_mod_cast hnm)
  have hsum' : (∑ j ∈ Finset.Icc n m, (Draw N j ((3 : ℝ) ^ N • w) omega).toReal) ≤
      lam * ((m : ℝ) - n) := by
    have hh := mul_le_mul_of_nonneg_left htau1 hlam.le
    have hh2 : lam * tau / 2 ≤ lam := by nlinarith only [hh, hlam]
    exact hDsum.trans (mul_le_mul_of_nonneg_right hh2 hlen)
  have hest := hiter (M.delta ^ 2 + eps ^ 8) (by positivity) hb m n hgap _ hR g hg a hac hap
    data fc hae u hgrad hgae hweak ref
    (fun j => Z N j ((3 : ℝ) ^ N • w) omega)
    (fun j => (Draw N j ((3 : ℝ) ^ N • w) omega).toReal)
    (fun j => aux_in_deterministic_onestep_sref_pos M H omega N _ w)
    (fun j => aux_in_deterministic_onestep_Z_nonneg M (1 / 32) eps (eta N omega)
      _ _ _ _ _ _ (hPSw N) j _) (fun j => ENNReal.toReal_nonneg) hZsum hDsum ?_ ?_
  · rw [hroot] at hest
    exact hest
  · intro j hj hZj
    have hlev : (N : ℤ) - (j + 2 : ℕ) ≤ N := by omega
    have hidx : ((N : ℤ) - ((N : ℤ) - (j + 2 : ℕ))).toNat = j + 2 := by omega
    have he := hgoodw N ((N : ℤ) - (j + 2 : ℕ)) w hlev
    rw [hidx] at he
    have he' := he (hfin _ hj) hZj
    simp only [sN, ite_eq_left hlev] at he'
    have hbnd := lem_as_regularity_actual_native_error d hd E M H omega N (j + 2) w I J
      (ref j) (Cg * (M.delta ^ 2 + eps ^ 8 + (Draw N (j + 2) ((3 : ℝ) ^ N • w) omega).toReal))
      (aux_in_deterministic_onestep_sref_pos M H omega N _ w) he' data
    simpa only [Nat.cast_add, Nat.cast_ofNat, mul_assoc, Cf] using hbnd
  · intro j hnj hjm
    rw [hroot]
    exact lem_as_regularity_native_reference M Rm H omega N m n j hnj hjm (eta N omega)
      (hEtaw N) (1 / 32) eps (by norm_num) _ _ _ _ _ _ (hPSw N) w lam hlam.le hdl hfin hsum'

end SubdiffusiveProcess.Paper
