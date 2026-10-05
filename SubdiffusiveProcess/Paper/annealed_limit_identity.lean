module

public import SubdiffusiveProcess.Paper.stationary_family
public import SubdiffusiveProcess.Paper.annealed_limit_response_transport
public import SubdiffusiveProcess.CoarseGrainingVocab.AhomStarCharacterization
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Homogenization.Book.Ch02.Matrices
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter SubdiffusiveProcess Homogenization Homogenization.Book.Ch02
open scoped ENNReal NNReal BigOperators Topology

namespace SubdiffusiveProcess.Paper
noncomputable section

/--
- stationary_family supplies actual coefficient law ahom_N^-1 a_N(3^N dot), stationarity and range.
- annealed_limit_response_transport CONCLUDES entrywise integrability and both finite-volume expectation identities for every pinned a0; no measurability or transport hypothesis is added here.
- manuscript e.annealed.matrices.def (M ), e.ahom.ahomstar.defs and its following identification (M ) are supplied by the imported GMC theorems tendsto_abar_originCube_ahom and tendsto_abarStarInv_originCube. Their audited axiom closures are standard. Before normalization their limits are ahom_N I and ahom_N^-1 I, respectively.
- The transport uses the cube of side 3^(N+k), multiplying Dirichlet expectations by ahom_N^-1 and inverse-Neumann expectations by ahom_N. ahom_pos supplies positivity. The remaining fixed-N limit and scalar cancellations are proof obligations, not assumptions.
- resulting hom=I is encoded by both characterizing limits, not a free function hom.
- units/cubes side3^k and N as family index are concrete.
- all models admitted by GMCModel; no further disorder reduction for this qualitative fixed-member normalization. Neither rate nor uniformity in N is concluded here. (in_moments later needs small disorder for UNIFORM moments, a distinct claim.)
-/
theorem annealed_limit_identity (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    ∀ (U : ℕ → Homogenization.Book.Ch02.Domain d)
      (hU : ∀ k, (U k : Set (Homogenization.Vec d)) =
        (centeredCube (0 : SpatialCoordinates d) ((3 : ℝ) ^ k)
          (pow_pos (by norm_num) k) : Set (SpatialCoordinates d)))
      (a0 : (N k : ℕ) → BilateralField d → Homogenization.Book.Ch02.CoeffOn (U k))
      (ha0 : ∀ N k omega x, (a0 N k omega).toCoeffField x =
        ((Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
          Real.exp (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) x)) •
          (1 : Homogenization.Mat d)),
    ∀ N : ℕ,
      (∀ i j : Fin d, Tendsto
        (fun k : ℕ => ∫ omega,
          Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) i j
            ∂(chaosSampleLaw model).toMeasure)
        atTop (𝓝 ((1 : Matrix (Fin d) (Fin d) ℝ) i j))) ∧
      (∀ i j : Fin d, Tendsto
        (fun k : ℕ => ∫ omega,
          Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) i j
            ∂(chaosSampleLaw model).toMeasure)
        atTop (𝓝 ((1 : Matrix (Fin d) (Fin d) ℝ) i j))) := by
  intro U hU a0 ha0 N
  have htr := _root_.SubdiffusiveProcess.Paper.annealed_limit_response_transport d hd model U hU a0 ha0
  constructor <;> intro i j
  · have hEq : (fun k : ℕ => ∫ omega, Homogenization.Book.Ch02.sigmaCoarse (U k) (a0 N k omega) i j ∂(chaosSampleLaw model).toMeasure)
        = (fun k : ℕ => (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
            SubdiffusiveProcess.CoarseGrainingVocab.abar model N (cubeDomain (originCube d (N + k))) i j) := by
      funext k
      exact (htr N k).2.1 i j
    rw [hEq]
    have hlim0 : Tendsto (fun k : ℕ => SubdiffusiveProcess.CoarseGrainingVocab.abar model N (cubeDomain (originCube d (N + k)))) atTop
        (𝓝 (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N • (1 : Matrix (Fin d) (Fin d) ℝ))) := by
      have h := (SubdiffusiveProcess.CoarseGrainingVocab.tendsto_abar_originCube_ahom model N).comp (tendsto_add_atTop_nat N)
      simpa only [Nat.add_comm] using! h
    have hlim1 : Tendsto (fun k : ℕ => (SubdiffusiveProcess.CoarseGrainingVocab.abar model N (cubeDomain (originCube d (N + k)))) i j) atTop
        (𝓝 ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N • (1 : Matrix (Fin d) (Fin d) ℝ)) i j)) :=
      (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim0 i) j)
    have hlim2 : Tendsto (fun k : ℕ => (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
        (SubdiffusiveProcess.CoarseGrainingVocab.abar model N (cubeDomain (originCube d (N + k)))) i j) atTop
        (𝓝 ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
          ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N • (1 : Matrix (Fin d) (Fin d) ℝ)) i j))) :=
      Tendsto.const_mul _ hlim1
    have hval : (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ *
        ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N • (1 : Matrix (Fin d) (Fin d) ℝ)) i j)
        = (1 : Matrix (Fin d) (Fin d) ℝ) i j := by
      rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N)), one_mul]
    rw [hval] at hlim2
    exact hlim2
  · have hEq : (fun k : ℕ => ∫ omega, Homogenization.Book.Ch02.sigmaStarInvCoarse (U k) (a0 N k omega) i j ∂(chaosSampleLaw model).toMeasure)
        = (fun k : ℕ => SubdiffusiveProcess.CoarseGrainingVocab.ahom model N *
            SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N (cubeDomain (originCube d (N + k))) i j) := by
      funext k
      exact (htr N k).2.2 i j
    rw [hEq]
    have hlim0 : Tendsto (fun k : ℕ => SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N (cubeDomain (originCube d (N + k)))) atTop
        (𝓝 ((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ))) := by
      have h := (SubdiffusiveProcess.CoarseGrainingVocab.tendsto_abarStarInv_originCube model N).comp (tendsto_add_atTop_nat N)
      simpa only [Nat.add_comm] using! h
    have hlim1 : Tendsto (fun k : ℕ => (SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N (cubeDomain (originCube d (N + k)))) i j) atTop
        (𝓝 (((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) i j)) :=
      (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim0 i) j)
    have hlim2 : Tendsto (fun k : ℕ => SubdiffusiveProcess.CoarseGrainingVocab.ahom model N *
        (SubdiffusiveProcess.CoarseGrainingVocab.abarStarInv model N (cubeDomain (originCube d (N + k)))) i j) atTop
        (𝓝 (SubdiffusiveProcess.CoarseGrainingVocab.ahom model N *
          (((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) i j))) :=
      Tendsto.const_mul _ hlim1
    have hval : SubdiffusiveProcess.CoarseGrainingVocab.ahom model N *
        (((SubdiffusiveProcess.CoarseGrainingVocab.ahom model N)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)) i j)
        = (1 : Matrix (Fin d) (Fin d) ℝ) i j := by
      rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N)), one_mul]
    rw [hval] at hlim2
    exact hlim2


end
end SubdiffusiveProcess.Paper
