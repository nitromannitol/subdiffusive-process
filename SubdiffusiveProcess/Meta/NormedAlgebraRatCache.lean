module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

/-!
# The rational normed-algebra structure induced by a real one

`NormedSpace.exp` and its continuity lemmas are stated for a normed algebra over `ℚ`.  For a normed
`ℝ`-algebra `A` this instance restricts scalars along `ℚ ↪ ℝ`, so that the structure is found on `A`
by instance resolution.  It is the same instance that the `MarkovProcess` library keeps private.
-/

namespace SubdiffusiveProcess

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- A normed `ℝ`-algebra is a normed `ℚ`-algebra by restriction of scalars along `ℚ ↪ ℝ`. -/
public noncomputable instance cacheNormedAlgebraRatA : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℝ A

end SubdiffusiveProcess
