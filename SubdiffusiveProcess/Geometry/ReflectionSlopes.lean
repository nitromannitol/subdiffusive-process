import SubdiffusiveProcess.Geometry.ReflectionCalculus

/-! # Reflected slopes and their Euclidean squared length

Affine response slopes transform by the same diagonal map as derivatives.
The relevant squared length is the sum of coordinate squares, independently
of the supremum norm used for the spatial cube carrier.
-/
noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- The reflection derivative multiplies each slope coordinate by its sign. -/
theorem coordinateReflectionDerivative_apply (I : Finset (Fin d))
    (p : Fin d → ℝ) (i : Fin d) :
    coordinateReflectionDerivative I p i = coordinateReflectionSign I i * p i := rfl

/-- Reflecting a slope twice restores it. -/
theorem coordinateReflectionDerivative_involutive (I : Finset (Fin d)) :
    Function.Involutive (coordinateReflectionDerivative I) := by
  intro p
  funext i
  rw [coordinateReflectionDerivative_apply, coordinateReflectionDerivative_apply,
    ← mul_assoc, ← pow_two, coordinateReflectionSign_sq, one_mul]

/-- The Euclidean squared slope length is preserved by coordinate reflection. -/
theorem coordinateReflectionDerivative_sum_sq (I : Finset (Fin d)) (p : Fin d → ℝ) :
    (∑ i : Fin d, (coordinateReflectionDerivative I p i) ^ 2) =
      ∑ i : Fin d, (p i) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinateReflectionDerivative_apply, mul_pow, coordinateReflectionSign_sq, one_mul]

end SubdiffusiveProcess
