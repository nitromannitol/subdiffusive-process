import SubdiffusiveProcess.Paper.stationary_family
import SubdiffusiveProcess.Paper.annealed_limit_identity
import SubdiffusiveProcess.Paper.annealed_limit_response_transport
import SubdiffusiveProcess.Paper.in_J
import Homogenization.Book.Ch02.Theorems.MatrixExtractionProofs
import Homogenization.Book.Ch02.Theorems.MatrixPositivity
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Lane4.Bridge
import Homogenization.Book.Ch02.MultiscaleEllipticity
import Homogenization.Book.Ch02.Matrices
import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedProviders
import SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.DualAnnealedMonotone
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace Paper

theorem aux_lem_fmono_annealed_subadditivity_scale_quadratic
    {d : ℕ} (c : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (p : Fin d → ℝ) :
    p ⬝ᵥ (c • A).mulVec p = c * (p ⬝ᵥ A.mulVec p) := by
  simp [dotProduct, Matrix.mulVec, Matrix.smul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro x_1 hx_1
  ring

theorem aux_lem_fmono_annealed_subadditivity_quadratic_of_matLoewnerLE
    {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ}
    (h : Homogenization.MatLoewnerLE A B) (p : Fin d → ℝ) :
    p ⬝ᵥ A.mulVec p ≤ p ⬝ᵥ B.mulVec p := by
  have hp := h p
  simp only [Homogenization.matVecMul, Homogenization.vecDot,
    Matrix.mulVec, dotProduct] at hp ⊢
  linarith

theorem aux_lem_fmono_annealed_subadditivity_cutoff_data
    (d : ℕ) (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (omega : BilateralField d) (k : ℕ) :
    Nonempty (SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData
        (cubeDomain (originCube d (k : ℤ)))
        (fun x => cutoffCoefficient model
          (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x)) := by
  exact ⟨SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos
      (SubdiffusiveProcess.Lane4.cutoffCoefficient_continuous model
        (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N)
      (fun x => SubdiffusiveProcess.Lane4.cutoffCoefficient_pos model
        (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x)
      (cubeDomain (originCube d (k : ℤ)))⟩



theorem lem_fmono_annealed_subadditivity (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (family : ℕ → BilateralField d → TriadicCoeffFamily d)
    (hfamily : ∀ (N : ℕ) (ω : BilateralField d) (Q : TriadicCube d),
      ∀ᵐ x ∂volume.restrict (openCubeSet Q),
        ((family N ω).coeffOn Q).toCoeffField x =
          scalarMatrix (cutoffCoefficient model
            (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N x)) :
    let Qk : ℕ → TriadicCube d := fun k => originCube d (k : ℤ)
    let Pmat : ℕ → ℕ → BilateralField d →
        Matrix (Fin d) (Fin d) ℝ :=
      fun N k ω =>
        Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (Qk k))
          ((family N ω).coeffOn (Qk k))
    let Rmat : ℕ → ℕ → BilateralField d →
        Matrix (Fin d) (Fin d) ℝ :=
      fun N k ω =>
        Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (Qk k))
          ((family N ω).coeffOn (Qk k))
    let EP : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ :=
      fun N k i j =>
        ∫ ω, Pmat N k ω i j ∂(chaosSampleLaw model).toMeasure
    let ER : ℕ → ℕ → Matrix (Fin d) (Fin d) ℝ :=
      fun N k i j =>
        ∫ ω, Rmat N k ω i j ∂(chaosSampleLaw model).toMeasure
    (∀ (N k : ℕ) (i j : Fin d),
      Integrable (fun ω => Pmat N k ω i j) (chaosSampleLaw model).toMeasure ∧
      Integrable (fun ω => Rmat N k ω i j) (chaosSampleLaw model).toMeasure) ∧
    (∀ (N k : ℕ) (pvec : Fin d → ℝ),
      pvec ⬝ᵥ (EP N (k + 1)).mulVec pvec ≤ pvec ⬝ᵥ (EP N k).mulVec pvec) ∧
    (∀ (N k : ℕ) (pvec : Fin d → ℝ),
      pvec ⬝ᵥ (ER N (k + 1)).mulVec pvec ≤ pvec ⬝ᵥ (ER N k).mulVec pvec) ∧
    (∀ (N : ℕ) (i j : Fin d),
      Filter.Tendsto (fun k => EP N k i j) Filter.atTop
        (nhds ((1 : Matrix (Fin d) (Fin d) ℝ) i j)) ∧
      Filter.Tendsto (fun k => ER N k i j) Filter.atTop
        (nhds ((1 : Matrix (Fin d) (Fin d) ℝ) i j))) := by
  dsimp
  let Qk : ℕ → TriadicCube d := fun k => originCube d (k : ℤ)
  let U : ℕ → Homogenization.Book.Ch02.Domain d := fun k =>
    cubeDomain (Qk k)
  let a0 : (N k : ℕ) → BilateralField d →
      Homogenization.Book.Ch02.CoeffOn (U k) := fun N k omega =>
    (Classical.choice
      (aux_lem_fmono_annealed_subadditivity_cutoff_data d model N omega k)).toCoeffOn
  have hU : ∀ k, (U k : Set (Homogenization.Vec d)) =
      (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
        (pow_pos (by norm_num) k) : Set (Homogenization.Vec d)) := by
    intro k
    change Homogenization.openCubeSet (Qk k) = _
    rw [show (Qk k) = originCube d (k : ℤ) by rfl]
    symm
    exact SubdiffusiveProcess.Lane4.centeredCube_zero_eq_openCubeSet_originCube
      (k : ℤ) (pow_pos (by norm_num) k)
  have hcut : ∀ (N : ℕ) (omega : BilateralField d)
      (x : SpatialCoordinates d),
      cutoffCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x =
        (Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
          Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x) := by
    simpa using (stationary_family d hd model).1
  have ha0 : ∀ N k omega x, (a0 N k omega).toCoeffField x =
      ((Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
        Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)) •
          (1 : Homogenization.Mat d) := by
    intro N k omega x
    change Homogenization.scalarMatrix
      (cutoffCoefficient model (fun _ => (0 : C(SpatialCoordinates d, ℝ))) omega N x) = _
    rw [hcut N omega x]
  have hcoeff : ∀ (N k : ℕ) (omega : BilateralField d),
      Homogenization.Book.Ch02.CoeffOn.AEEq
        ((family N omega).coeffOn (Qk k)) (a0 N k omega) := by
    intro N k omega
    change ((family N omega).coeffOn (Qk k)).toCoeffField =ᵐ[
      Homogenization.volumeMeasureOn (U k : Set (Homogenization.Vec d))]
      (a0 N k omega).toCoeffField
    simpa [U, a0, SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData.toCoeffOn,
      SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField,
      Homogenization.Book.Ch02.cubeDomain_coe, volumeMeasureOn] using
      hfamily N omega (Qk k)
  have hP_eq : ∀ (N k : ℕ) (omega : BilateralField d),
      Homogenization.Book.Ch02.sigmaCoarse
          (cubeDomain (Qk k)) ((family N omega).coeffOn (Qk k)) =
        Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) := by
    intro N k omega
    exact Homogenization.Book.Ch02.sigmaCoarse_eq_ofAEEq (hcoeff N k omega)
  have hR_eq : ∀ (N k : ℕ) (omega : BilateralField d),
      Homogenization.Book.Ch02.sigmaStarInvCoarse
          (cubeDomain (Qk k)) ((family N omega).coeffOn (Qk k)) =
        Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) := by
    intro N k omega
    exact Homogenization.Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq (hcoeff N k omega)
  have hPfun : ∀ (N k : ℕ) (i j : Fin d),
      (fun omega =>
        Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (Qk k))
          ((family N omega).coeffOn (Qk k)) i j) =
        (fun omega => Homogenization.Book.Ch02.sigmaCoarse (U k)
          (a0 N k omega) i j) := by
    intro N k i j
    funext omega
    rw [hP_eq N k omega]
  have hRfun : ∀ (N k : ℕ) (i j : Fin d),
      (fun omega =>
        Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (Qk k))
          ((family N omega).coeffOn (Qk k)) i j) =
        (fun omega => Homogenization.Book.Ch02.sigmaStarInvCoarse (U k)
          (a0 N k omega) i j) := by
    intro N k i j
    funext omega
    rw [hR_eq N k omega]
  have htransport := annealed_limit_response_transport d hd model U hU a0 ha0
  have hlimit := annealed_limit_identity d hd model U hU a0 ha0
  have hEP_transport : ∀ (N k : ℕ),
      (fun i j => ∫ omega,
        Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (Qk k))
          ((family N omega).coeffOn (Qk k)) i j
          ∂(chaosSampleLaw model).toMeasure) =
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ •
          SubdiffusiveProcess.CoarseGrainingVocab.abar model N
            (Homogenization.Book.Ch02.cubeDomain
              (Homogenization.originCube d ((N + k : ℕ) : ℤ))) := by
    intro N k
    funext i j
    calc
      (∫ omega,
          Homogenization.Book.Ch02.sigmaCoarse (cubeDomain (Qk k))
            ((family N omega).coeffOn (Qk k)) i j
            ∂(chaosSampleLaw model).toMeasure) =
          ∫ omega, Homogenization.Book.Ch02.sigmaCoarse (U k)
            (a0 N k omega) i j ∂(chaosSampleLaw model).toMeasure := by
              apply integral_congr_ae
              filter_upwards [] with omega
              rw [hP_eq N k omega]
      _ = (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
          SubdiffusiveProcess.CoarseGrainingVocab.abar model N
            (Homogenization.Book.Ch02.cubeDomain
              (Homogenization.originCube d ((N + k : ℕ) : ℤ))) i j :=
            (htransport N k).2.1 i j
      _ = ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ •
          SubdiffusiveProcess.CoarseGrainingVocab.abar model N
            (Homogenization.Book.Ch02.cubeDomain
              (Homogenization.originCube d ((N + k : ℕ) : ℤ)))) i j := by
            rfl
  have hER_transport : ∀ (N k : ℕ),
      (fun i j => ∫ omega,
        Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (Qk k))
          ((family N omega).coeffOn (Qk k)) i j
          ∂(chaosSampleLaw model).toMeasure) =
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N) •
          SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
            (Homogenization.Book.Ch02.cubeDomain
              (Homogenization.originCube d ((N + k : ℕ) : ℤ))) := by
    intro N k
    funext i j
    calc
      (∫ omega,
          Homogenization.Book.Ch02.sigmaStarInvCoarse (cubeDomain (Qk k))
            ((family N omega).coeffOn (Qk k)) i j
            ∂(chaosSampleLaw model).toMeasure) =
          ∫ omega, Homogenization.Book.Ch02.sigmaStarInvCoarse (U k)
            (a0 N k omega) i j ∂(chaosSampleLaw model).toMeasure := by
              apply integral_congr_ae
              filter_upwards [] with omega
              rw [hR_eq N k omega]
      _ = SubdiffusiveProcess.CoarseGrainingVocab.ahom model N *
          SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
            (Homogenization.Book.Ch02.cubeDomain
              (Homogenization.originCube d ((N + k : ℕ) : ℤ))) i j :=
            (htransport N k).2.2 i j
      _ = (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N •
          SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N
            (Homogenization.Book.Ch02.cubeDomain
              (Homogenization.originCube d ((N + k : ℕ) : ℤ)))) i j := by
            rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N k i j
    constructor
    · rw [hPfun N k i j]
      exact (htransport N k).1 i j |>.1
    · rw [hRfun N k i j]
      exact (htransport N k).1 i j |>.2
  · intro N k pvec
    have hnext := hEP_transport N (k + 1)
    have hcurr := hEP_transport N k
    simp only [Qk, Nat.cast_add, Nat.cast_one, Int.natCast_add, Int.ofNat_one]
      at hnext hcurr
    rw [hnext, hcurr]
    rw [aux_lem_fmono_annealed_subadditivity_scale_quadratic,
      aux_lem_fmono_annealed_subadditivity_scale_quadratic]
    have hmono := SubdiffusiveProcess.CoarseGrainingVocab.matLoewnerLE_abar_originCube_succ
      model N (N + k)
    have hnonneg : 0 ≤ (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ :=
      (inv_nonneg.mpr (le_of_lt
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N)))
    apply mul_le_mul_of_nonneg_left
    · have hq :=
        aux_lem_fmono_annealed_subadditivity_quadratic_of_matLoewnerLE
          hmono pvec
      simpa [Nat.add_assoc, Int.natCast_add, Int.ofNat_one] using hq
    · exact hnonneg
  · intro N k pvec
    have hnext := hER_transport N (k + 1)
    have hcurr := hER_transport N k
    simp only [Qk, Nat.cast_add, Nat.cast_one, Int.natCast_add, Int.ofNat_one]
      at hnext hcurr
    rw [hnext, hcurr]
    rw [aux_lem_fmono_annealed_subadditivity_scale_quadratic,
      aux_lem_fmono_annealed_subadditivity_scale_quadratic]
    have hmono := SubdiffusiveProcess.CoarseGrainingVocab.Section6FixedCutoffBridge.matLoewnerLE_abarStarInv_originCube_succ
      model N (N + k)
    have hnonneg : 0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.ahom model N :=
      le_of_lt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N)
    apply mul_le_mul_of_nonneg_left
    · have hq :=
        aux_lem_fmono_annealed_subadditivity_quadratic_of_matLoewnerLE
          hmono pvec
      simpa [Nat.add_assoc, Int.natCast_add, Int.ofNat_one] using hq
    · exact hnonneg
  · intro N i j
    constructor
    · have hP := (hlimit N).1 i j
      refine Filter.Tendsto.congr' ?_ hP
      filter_upwards [] with k
      rw [hPfun N k i j]
    · have hR := (hlimit N).2 i j
      refine Filter.Tendsto.congr' ?_ hR
      filter_upwards [] with k
      rw [hRfun N k i j]

end Paper
