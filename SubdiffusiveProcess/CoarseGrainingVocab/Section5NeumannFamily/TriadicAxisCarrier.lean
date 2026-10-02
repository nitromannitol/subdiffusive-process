import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.TriadicTwoRadiusPieces

/-!
# The axis realization of a triadic parent cube

The arbitrary-centre harmonic `B_z` package
`exists_axisCube_harmonic_cellB_bound` is stated on `axisCube z L`.  A triadic
cube is exactly such an axis cube, with the corner supplied by
`oneStepCenteredAxisCorner` at the cube's own translation vector.  This module
records that identification, the three domain casts it forces (`H1Function`,
`WeakPoissonEquationOn`, `HasWeakHessianOn`), and the gradient-congruence
transfer of a weak Hessian.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-! ## Domain casts -/

/-- Move an `H¹` function along a propositional equality of domains. -/
def nfCastH1Domain {U V : Set (Vec d)} (hUV : U = V) (u : H1Function U) :
    H1Function V :=
  hUV ▸ u

@[simp] theorem nfCastH1Domain_grad {U V : Set (Vec d)} (hUV : U = V)
    (u : H1Function U) : (nfCastH1Domain hUV u).grad = u.grad := by
  subst V
  rfl

/-- Move a weak Poisson equation along a propositional equality of domains. -/
theorem nfCastWeakPoisson {U V : Set (Vec d)} (hUV : U = V)
    {u : H1Function U} {f : Vec d → ℝ}
    (hu : WeakPoissonEquationOn U u f) :
    WeakPoissonEquationOn V (nfCastH1Domain hUV u) f := by
  subst V
  exact hu

/-- Move a weak Hessian witness along a propositional equality of domains. -/
def nfCastWeakHessian {U V : Set (Vec d)} (hUV : U = V)
    {u : H1Function U} (H : HasWeakHessianOn U u) :
    HasWeakHessianOn V (nfCastH1Domain hUV u) := by
  subst V
  exact H

/-- A weak Hessian depends on its `H¹` argument only through the gradient. -/
def nfWeakHessianOfGradEq {U : Set (Vec d)} {u v : H1Function U}
    (hgrad : u.grad = v.grad) (H : HasWeakHessianOn U v) :
    HasWeakHessianOn U u where
  hess := H.hess
  hess_memL2 := H.hess_memL2
  weak_second := by
    simp only [hgrad]
    exact H.weak_second

@[simp] theorem nfWeakHessianOfGradEq_hess {U : Set (Vec d)}
    {u v : H1Function U} (hgrad : u.grad = v.grad)
    (H : HasWeakHessianOn U v) :
    (nfWeakHessianOfGradEq hgrad H).hess = H.hess := rfl

/-! ## The axis realization -/

/-- Lower corner of the axis realization of a triadic cube. -/
def twoRadiusAxisCorner (Q : TriadicCube d) : Vec d :=
  oneStepCenteredAxisCorner (triadicCubeShift Q) Q.scale

/-- A triadic cube is the axis cube at its own corner and side. -/
theorem openCubeSet_eq_axisCube_twoRadius (Q : TriadicCube d) :
    openCubeSet Q =
      axisCube (twoRadiusAxisCorner Q) (cubeScaleFactor Q) := by
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
    translateSet_openCubeSet_originCube_eq_axisCube]
  rfl

/-- Inner half of the axis realization of a triadic parent. -/
def twoRadiusInnerHalf (Q : TriadicCube d) : Set (Vec d) :=
  axisCubeInnerHalf (twoRadiusAxisCorner Q) (cubeScaleFactor Q)

/-- The fixed concentric high-exponent region of a triadic parent. -/
def twoRadiusConcentric (Q : TriadicCube d) (depth : ℕ) : Set (Vec d) :=
  axisCube
    (CubeCalderonZygmund.axisCubeConcentricDepthCorner
      (twoRadiusAxisCorner Q) (cubeScaleFactor Q) (depth + 1))
    (CubeCalderonZygmund.axisCubeConcentricDepthSide
      (cubeScaleFactor Q) (depth + 1))

/-- The parent side length is positive. -/
theorem twoRadius_cubeScaleFactor_pos (Q : TriadicCube d) :
    0 < cubeScaleFactor Q := by
  simpa [cubeScaleFactor] using
    (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)

/-! ## Normalized parent readout and the harmonic cell factor -/

/-- Normalized parent-gradient coordinate sum on the axis realization. -/
def twoRadiusParentCoordinateSum (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) : ℝ :=
  ∑ k : Fin d,
    (eLpNorm (fun x => u.grad x k) 2
      (CubeCalderonZygmund.axisCubeNormalizedMeasure
        (twoRadiusAxisCorner Q) (cubeScaleFactor Q))).toReal

theorem twoRadiusParentCoordinateSum_nonneg (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) :
    0 ≤ twoRadiusParentCoordinateSum Q u :=
  Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

/-- The purely geometric prefactor of the harmonic cell estimate. -/
def twoRadiusHarmonicCellFactor (d : ℕ) (hd : 3 ≤ d) (depth : ℕ)
    (Q R : TriadicCube d) : ℝ :=
  cubeScaleFactor R * (d : ℝ) ^ 2 *
    ((triadicAxisNormalizedMeasureRatio R
      (CubeCalderonZygmund.axisCubeConcentricDepthSide
        (cubeScaleFactor Q) (depth + 1))) ^
      (1 / (oneStepHarmonicExponent d hd).exponent).toReal).toReal

/-- Harmonic cell `B` bound on a cell inside the inner half of a triadic
parent, for an arbitrary weakly harmonic parent field. -/
theorem exists_twoRadius_harmonic_cell_hessian
    (d : ℕ) (hd : 3 ≤ d) :
    ∃ depth : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (Q : TriadicCube d) (u : H1Function (openCubeSet Q)),
        WeakPoissonEquationOn (openCubeSet Q) u (fun _ ↦ 0) →
        ∀ (R : TriadicCube d),
          openCubeSet R ⊆ twoRadiusInnerHalf Q →
          openCubeSet R ⊆ twoRadiusConcentric Q depth →
          ∃ (w : H1Function (openCubeSet R))
            (H : HasWeakHessianOn (openCubeSet R) w),
            w.grad = u.grad ∧
            oneStepCellB R H ≤
              twoRadiusHarmonicCellFactor d hd depth Q R *
                (C * (cubeScaleFactor Q)⁻¹ *
                  twoRadiusParentCoordinateSum Q u) := by
  obtain ⟨depth, C, hC, haxis⟩ := exists_axisCube_harmonic_cellB_bound d hd
  refine ⟨depth, C, hC, ?_⟩
  intro Q u hu R hRhalf hRinner
  have hcast := openCubeSet_eq_axisCube_twoRadius Q
  let uA : H1Function (axisCube (twoRadiusAxisCorner Q) (cubeScaleFactor Q)) :=
    nfCastH1Domain hcast u
  have huA : WeakPoissonEquationOn
      (axisCube (twoRadiusAxisCorner Q) (cubeScaleFactor Q)) uA (fun _ ↦ 0) :=
    nfCastWeakPoisson hcast hu
  obtain ⟨uS, _huSfun, huSgrad, H, hbound⟩ :=
    haxis (twoRadiusAxisCorner Q) (cubeScaleFactor Q)
      (twoRadius_cubeScaleFactor_pos Q) uA huA R hRhalf hRinner
  refine ⟨uS.restrict (isOpen_openCubeSet R) hRhalf,
    H.restrict (isOpen_openCubeSet R) hRhalf, ?_, ?_⟩
  · change uS.grad = u.grad
    rw [huSgrad]
    exact nfCastH1Domain_grad hcast u
  · refine hbound.trans_eq ?_
    unfold twoRadiusHarmonicCellFactor twoRadiusParentCoordinateSum
    rw [nfCastH1Domain_grad hcast u]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
