import SubdiffusiveProcess.Lane2.CellDirichlet
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Sobolev.FiniteResponses
import SubdiffusiveProcess.Sobolev.DomainPoincare

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_inputs_extension_split_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt hy
  have h3 := Real.sq_sqrt (add_nonneg hx hy)
  have h4 := Real.sqrt_nonneg x
  have h5 := Real.sqrt_nonneg y
  nlinarith [mul_nonneg h4 h5, Real.sqrt_nonneg (x+y)]

theorem aux_inputs_extension_split_generic {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (K : ℝ≥0) (hK : ∀ u : killedSobolevGraph Ω,
      ‖(u : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) u‖)
      (a : PositiveCoefficient (Ω)) (g : HilbertGradient (Ω))
      (hDatum v : weakSobolevGraph (Ω))
      (hv :       (∀ φ : killedSobolevGraph (Ω),
        sobolevCoefficientForm a (v : SobolevData (Ω)) (φ : SobolevData (Ω)) =
          -inner ℝ g (subspaceGradient (killedSobolevGraph (Ω)) φ)))
      (htrace : ((v : SobolevData (Ω)) - (hDatum : SobolevData (Ω))) ∈ killedSobolevGraph (Ω)) :
      ∃ (w : killedSobolevGraph (Ω)) (t : weakSobolevGraph (Ω)),
        (∀ φ : killedSobolevGraph (Ω),
          sobolevCoefficientForm a (w : SobolevData (Ω)) (φ : SobolevData (Ω)) =
            -inner ℝ g (subspaceGradient (killedSobolevGraph (Ω)) φ)) ∧
        (∀ φ : killedSobolevGraph (Ω),
          sobolevCoefficientForm a (t : SobolevData (Ω)) (φ : SobolevData (Ω)) = 0) ∧
        ((t : SobolevData (Ω)) - (hDatum : SobolevData (Ω))) ∈ killedSobolevGraph (Ω) ∧
        normalizedEnergyNorm a (Ω).isOpen.measurableSet (sobolevGradient (v : SobolevData (Ω))) ≤
          normalizedEnergyNorm a (Ω).isOpen.measurableSet (sobolevGradient (w : SobolevData (Ω))) +
          normalizedEnergyNorm a (Ω).isOpen.measurableSet (sobolevGradient (t : SobolevData (Ω))) := by
  obtain ⟨c, hc, ha⟩ := a.property
  let L : killedSobolevGraph Ω →L[ℝ] ℝ :=
    -((innerSL ℝ g).comp (subspaceGradient (killedSobolevGraph Ω)))
  obtain ⟨w, hw, _⟩ := existsUnique_gradient_subspace_solution
    (killedSobolevGraph Ω) isClosed_killedSobolevGraph K hK a.val hc ha L
  have hw' : ∀ φ : killedSobolevGraph Ω,
      sobolevCoefficientForm a (w : SobolevData Ω) (φ : SobolevData Ω) =
        -inner ℝ g (subspaceGradient (killedSobolevGraph Ω) φ) := by
    intro φ
    exact hw φ
  let t : weakSobolevGraph Ω := ⟨(v : SobolevData Ω) - (w : SobolevData Ω),
    (weakSobolevGraph Ω).sub_mem v.property
      (killedSobolevGraph_le_weakSobolevGraph w.property)⟩
  have ht : ∀ φ : killedSobolevGraph Ω,
      sobolevCoefficientForm a (t : SobolevData Ω) (φ : SobolevData Ω) = 0 := by
    intro φ
    change sobolevCoefficientForm a ((v : SobolevData Ω) - (w : SobolevData Ω))
      (φ : SobolevData Ω) = 0
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    rw [hv φ, hw' φ, sub_self]
  refine ⟨w, t, hw', ht, ?_, ?_⟩
  · change ((v : SobolevData Ω) - (w : SobolevData Ω)) -
        (hDatum : SobolevData Ω) ∈ killedSobolevGraph Ω
    rw [sub_right_comm]
    exact (killedSobolevGraph Ω).sub_mem htrace w.property
  · have hsum : (v : SobolevData Ω) = (w : SobolevData Ω) + (t : SobolevData Ω) := by
      dsimp [t]
      abel
    have horth := ht w
    have horth' : sobolevCoefficientForm a (w : SobolevData Ω) (t : SobolevData Ω) = 0 := by
      rw [sobolevCoefficientForm_symm]
      exact horth
    have henergy : sobolevCoefficientForm a (v : SobolevData Ω) (v : SobolevData Ω) =
        sobolevCoefficientForm a (w : SobolevData Ω) (w : SobolevData Ω) +
        sobolevCoefficientForm a (t : SobolevData Ω) (t : SobolevData Ω) := by
      rw [hsum]
      simp only [map_add, ContinuousLinearMap.add_apply, horth, horth', add_zero, zero_add]
    simp only [normalizedEnergyNorm,
      localGradientEnergy_domain_eq_sobolevCoefficientForm]
    rw [henergy, add_div]
    have hw0 := div_nonneg (sobolevCoefficientForm_nonneg a (w : SobolevData Ω))
      (measureReal_nonneg : 0 ≤ volume.real (Ω : Set (SpatialCoordinates d)))
    have ht0 := div_nonneg (sobolevCoefficientForm_nonneg a (t : SobolevData Ω))
      (measureReal_nonneg : 0 ≤ volume.real (Ω : Set (SpatialCoordinates d)))
    exact aux_inputs_extension_split_sqrt hw0 ht0

theorem inputs_extension_split (d : ℕ) (hd : 2 ≤ d) :
    (∀ (z : SpatialCoordinates d) (m : ℕ) (hr : (0 : ℝ) < 3 ^ m)
      (a : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hr)) (g : HilbertGradient (centeredCube z ((3 : ℝ) ^ m) hr))
      (hDatum v : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr)),
      (∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr),
        sobolevCoefficientForm a (v : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) (φ : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) =
          -inner ℝ g (subspaceGradient (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr)) φ)) →
      ((v : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) - (hDatum : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr))) ∈ killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr) →
      ∃ (w : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr)) (t : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr)),
        (∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr),
          sobolevCoefficientForm a (w : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) (φ : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) =
            -inner ℝ g (subspaceGradient (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr)) φ)) ∧
        (∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr),
          sobolevCoefficientForm a (t : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) (φ : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) = 0) ∧
        ((t : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) - (hDatum : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr))) ∈ killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr) ∧
        normalizedEnergyNorm a (centeredCube z ((3 : ℝ) ^ m) hr).isOpen.measurableSet (sobolevGradient (v : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr))) ≤
          normalizedEnergyNorm a (centeredCube z ((3 : ℝ) ^ m) hr).isOpen.measurableSet (sobolevGradient (w : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr))) +
          normalizedEnergyNorm a (centeredCube z ((3 : ℝ) ^ m) hr).isOpen.measurableSet (sobolevGradient (t : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)))) := by
  letI : NeZero d := ⟨by omega⟩
  intro z m hr a g hDatum v hv htrace
  obtain ⟨K, hK⟩ := (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    (centeredCube z ((3 : ℝ) ^ m) hr)
    (lane2_isOpenBoundedConvexDomain_centeredCube z hr)).1
  exact aux_inputs_extension_split_generic K hK a g hDatum v hv htrace

end Paper

