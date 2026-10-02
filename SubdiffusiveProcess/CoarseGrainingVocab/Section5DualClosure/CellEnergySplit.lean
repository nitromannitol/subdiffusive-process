import SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure.CellCrossTerm
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.OneStepRetainedNeumannGluing




open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- A cell average splits along a pointwise three-term decomposition. -/
theorem volumeAverage_eq_add_three
    (U : Set (Vec d)) (hU : MeasurableSet U) (f g1 g2 g3 : Vec d → ℝ)
    (heq : ∀ x ∈ U, f x = g1 x + g2 x + g3 x)
    (h1 : IntegrableOn g1 U) (h2 : IntegrableOn g2 U)
    (h3 : IntegrableOn g3 U) :
    volumeAverage U f =
      volumeAverage U g1 + volumeAverage U g2 + volumeAverage U g3 := by
  unfold volumeAverage
  have hcong : ∫ x in U, f x ∂volume =
      ∫ x in U, (g1 x + g2 x + g3 x) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hU] with x hx
    exact heq x hx
  rw [hcong,
    integral_add (f := fun x ↦ g1 x + g2 x) (g := g3) (h1.add h2) h3,
    integral_add (f := g1) (g := g2) h1 h2]
  ring



theorem le_normalized_cellSum_add_boundary
    {Q : TriadicCube d} {j : ℕ} {s : Finset (TriadicCube d)}
    (hs : s ⊆ descendantsAtDepth Q j) (hsne : s.Nonempty)
    (g : Vec d → ℝ) (T : TriadicCube d → ℝ)
    (hgInt : IntegrableOn g (openCubeSet Q))
    (hg0 : ∀ R ∈ s, 0 ≤ volumeAverage (openCubeSet R) g)
    (hsplit : ∀ R ∈ s, volumeAverage (openCubeSet R) g = T R)
    {target : ℝ}
    (hcompetitor : target ≤ volumeAverage (openCubeSet Q) g) :
    target ≤ ((s.card : ℝ)⁻¹) * ∑ R ∈ s, T R +
      (cubeVolume Q)⁻¹ *
        ∫ x in openCubeSet Q \ oneStepRetainedOpenSet s, g x ∂volume := by
  calc
    target ≤ volumeAverage (openCubeSet Q) g := hcompetitor
    _ = (cubeVolume Q)⁻¹ *
            ∫ x in oneStepRetainedOpenSet s, g x ∂volume +
          (cubeVolume Q)⁻¹ *
            ∫ x in openCubeSet Q \ oneStepRetainedOpenSet s, g x ∂volume :=
      volumeAverage_openCubeSet_eq_retained_add_complement hs g hgInt
    _ ≤ ((s.card : ℝ)⁻¹) * ∑ R ∈ s, volumeAverage (openCubeSet R) g +
          (cubeVolume Q)⁻¹ *
            ∫ x in openCubeSet Q \ oneStepRetainedOpenSet s, g x ∂volume :=
      by
        have hret :=
          inv_cubeVolume_mul_integral_retained_le_normalized_cellAverage
            hs hsne g hgInt hg0
        linarith
    _ = ((s.card : ℝ)⁻¹) * ∑ R ∈ s, T R +
          (cubeVolume Q)⁻¹ *
            ∫ x in openCubeSet Q \ oneStepRetainedOpenSet s, g x ∂volume := by
      rw [Finset.sum_congr rfl hsplit]

/-- The cell average of the glued competitor's half energy is the three-term
majorant sum, for any retained cell.  Direct averaging of
`oneStepSelectedRetainedGluedNeumannTwoFlux_half_energy_eq_of_mem`. -/
theorem volumeAverage_half_gluedNeumannTwoFlux_energy_eq
    {Q R : TriadicCube d} {j : ℕ} {s : Finset (TriadicCube d)}
    (a : CoeffField d) (P F : TriadicCube d → Vec d → Vec d)
    (background : Vec d → Vec d) {lam Lam : ℝ}
    (hs : s ⊆ descendantsAtDepth Q j)
    (hEll : ∀ S ∈ descendantsAtDepth Q j,
      IsEllipticFieldOn lam Lam (openCubeSet S) a)
    (hP : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (P S))
    (hF : ∀ S ∈ descendantsAtDepth Q j,
      MemVectorL2 (openCubeSet S) (F S))
    (hR : R ∈ s)
    (hbackground : ∀ x ∈ openCubeSet R, background x = P R x + F R x)
    (hprincipalInt : IntegrableOn (fun x ↦
      (1 / 2 : ℝ) * vecDot
        ((oneStepSelectedNeumannCell a P hEll hP R (hs hR)).flux x)
        (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
          ((oneStepSelectedNeumannCell a P hEll hP R (hs hR)).flux x)))
      (openCubeSet R))
    (hcrossInt : IntegrableOn (fun x ↦ vecDot
        ((oneStepSelectedNeumannCell a P hEll hP R (hs hR)).flux x)
        (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
          ((oneStepSelectedNeumannCell a F hEll hF R (hs hR)).flux x)))
      (openCubeSet R))
    (hoscInt : IntegrableOn (fun x ↦
      (1 / 2 : ℝ) * vecDot
        ((oneStepSelectedNeumannCell a F hEll hF R (hs hR)).flux x)
        (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
          ((oneStepSelectedNeumannCell a F hEll hF R (hs hR)).flux x)))
      (openCubeSet R)) :
    volumeAverage (openCubeSet R) (fun x ↦
        (1 / 2 : ℝ) * vecDot
          (oneStepSelectedRetainedGluedNeumannTwoFlux Q j s a P F background
            hEll hP hF x)
          (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
            (oneStepSelectedRetainedGluedNeumannTwoFlux Q j s a P F background
              hEll hP hF x))) =
      volumeAverage (openCubeSet R) (fun x ↦
          (1 / 2 : ℝ) * vecDot
            ((oneStepSelectedNeumannCell a P hEll hP R (hs hR)).flux x)
            (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
              ((oneStepSelectedNeumannCell a P hEll hP R (hs hR)).flux x))) +
        volumeAverage (openCubeSet R) (fun x ↦ vecDot
            ((oneStepSelectedNeumannCell a P hEll hP R (hs hR)).flux x)
            (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
              ((oneStepSelectedNeumannCell a F hEll hF R (hs hR)).flux x))) +
        volumeAverage (openCubeSet R) (fun x ↦
          (1 / 2 : ℝ) * vecDot
            ((oneStepSelectedNeumannCell a F hEll hF R (hs hR)).flux x)
            (matVecMul ((blockMatrixOfCoeff (a x)).lowerRight)
              ((oneStepSelectedNeumannCell a F hEll hF R (hs hR)).flux x))) := by
  refine volumeAverage_eq_add_three _ (measurableSet_openCubeSet R) _ _ _ _
    ?_ hprincipalInt hcrossInt hoscInt
  intro x hx
  exact oneStepSelectedRetainedGluedNeumannTwoFlux_half_energy_eq_of_mem
    a P F background hs hEll hP hF hR hx (hbackground x hx)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5DualClosure
