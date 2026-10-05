module

public import SubdiffusiveProcess.Paper.lem_as_regularity_capped_iteration

@[expose] public section

/-! Rooted iteration in the translated physical Sobolev carrier. The proof
uses the existing weak-equation and exact normalized-energy bridges; no score
budget or stochastic regularity bound is postulated as already available.
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

/-- The native score-budget iteration transports to the physical root Sobolev solution. -/
theorem lem_as_regularity_translated_iteration (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (D : deterministic_good_scale_input d) (Cg w : ℝ) (hCg : 0 < Cg)
    (hw : 0 < w) (hw1 : w ≤ 1) :
    ∃ lam tau C : ℝ, 0 < lam ∧ 0 < tau ∧ tau ≤ 1 ∧ 0 < C ∧
      ∀ base : ℝ, 0 ≤ base → base ≤ min (2 * lam) tau →
      ∀ (m n : ℕ), n + 26 ≤ m →
      ∀ (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
        (g : SpatialCoordinates d → Fin d → ℝ),
        MemHolder (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) (1 / 2) g →
      ∀ a : Vec d → ℝ, Continuous a → (∀ y, 0 < a y) →
      ∀ data : ScalarTriadicCoeffData (fun y => a (y + 0)),
      ∀ fc : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR),
        (∀ᵐ y ∂volume.restrict (openCubeSet (originCube d (m : ℤ))),
          a y = fc.val (fun i => z i + y i)) →
      ∀ (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR))
        (hgrad : HilbertGradient (centeredCube z ((3 : ℝ) ^ m) hR)),
        (∀ i, (hgrad i : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))] fun x => g x i) →
        (∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR),
          sobolevCoefficientForm fc (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))
            (φ : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)) =
              -inner ℝ hgrad (subspaceGradient
                (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)) φ)) →
      ∀ ref Z score : ℕ → ℝ, (∀ j, 0 < ref j) → (∀ j, 0 ≤ Z j) → (∀ j, 0 ≤ score j) →
        (∑ j ∈ Finset.Icc n m, Z j) ≤ (lam * tau / 2) * ((m : ℝ) - n) →
        (∑ j ∈ Finset.Icc n m, score j) ≤ (lam * tau / 2) * ((m : ℝ) - n) →
        (∀ j : ℕ, j + 2 ≤ m → Z (j + 2) < 1 →
          paperHomogenizationError (originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2) (1 / 32)
            Ch02.MultiscaleExponent.infinity (Ch02.MultiscaleExponent.finite 2)
            data.toTriadicCoeffFamily (ref j) ≤ ENNReal.ofReal (Cg * (base + score (j + 2)))) →
        (∀ j : ℕ, n ≤ j → j + 5 ≤ m →
          Real.exp (-(4 * (lam * ((m : ℝ) - n)))) ≤ ref j / ref (m - 2) ∧
          ref j / ref (m - 2) ≤ Real.exp (4 * (lam * ((m : ℝ) - n)))) →
        normalizedEnergyNorm fc (centeredCube z ((3 : ℝ) ^ n) (by positivity)).isOpen.measurableSet
          (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) ≤
          C * (3 : ℝ) ^ (w * ((m : ℝ) - n)) *
            (normalizedEnergyNorm fc (centeredCube z ((3 : ℝ) ^ m) hR).isOpen.measurableSet
              (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) +
              (Real.sqrt (ref (m - 2)))⁻¹ * ((3 : ℝ) ^ ((m : ℝ) / 2) *
                halfHolderSeminorm (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g)) := by
  obtain ⟨lam, tau, C, hlam, htau, htau1, hC, hiter⟩ :=
    lem_as_regularity_capped_iteration d hd D Cg w hCg hw hw1
  refine ⟨lam, tau, C, hlam, htau, htau1, hC, ?_⟩
  intro base hb0 hb m n hnm z hR g hg a ha hapos data fc hae u hgrad hgae hweak
    ref Z score hrf hZ hsc hZsum hscsum herr hrat
  obtain ⟨u', -, hu'2, hu'w⟩ := aux_prop_folded_iteration_weak_transfer
    m z hR fc a hae g hgrad u hgae hweak
  have h := hiter base hb0 hb m n hnm z hR g hg a ha hapos data u' hu'w
    ref Z score hrf hZ hsc hZsum hscsum herr hrat
  rw [← aux_prop_folded_iteration_energy_bridge m n (by omega) z hR fc a
      (fun y => (hapos y).le) hae _ u' hu'2 (by positivity),
    ← aux_prop_folded_iteration_energy_bridge m m le_rfl z hR fc a
      (fun y => (hapos y).le) hae _ u' hu'2 hR] at h
  exact h

end SubdiffusiveProcess.Paper
