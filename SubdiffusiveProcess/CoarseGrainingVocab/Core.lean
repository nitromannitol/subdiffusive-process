module

public import SubdiffusiveProcess.Assumptions.CoefficientPackaging
public import Homogenization.Book.Ch02.Theorems
public import Homogenization.Book.Ch04.Internal.CoarseObservableMeasurability.Basic

@[expose] public section

/-!
# Core coarse-graining vocabulary

Thin names for the deterministic objects already supplied by CoarseGraining,
together with the scalar triadic packaging used by the GMC model.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Filter Homogenization.Book

noncomputable section

abbrev Mat (d : ℕ) := Homogenization.Mat d
abbrev TriadicCube (d : ℕ) := Homogenization.TriadicCube d

/-- Cube-by-cube certificates for one global scalar representative. -/
structure ScalarTriadicCoeffData {d : ℕ} (a : Vec d → ℝ) where
  onCube : ∀ Q : TriadicCube d, ScalarCoeffOnData (Ch02.cubeDomain Q) a



/-- Package a global scalar representative as a triadic coefficient family. -/
noncomputable def ScalarTriadicCoeffData.toTriadicCoeffFamily {d : ℕ}
    {a : Vec d → ℝ} (h : ScalarTriadicCoeffData a) : Ch02.TriadicCoeffFamily d where
  coeffOn Q := (h.onCube Q).toCoeffOn
  restrictsTo_of_subset := by
    intro Q R _hRQ
    exact EventuallyEq.rfl

/-- Scalar coefficient objects are symmetric almost everywhere. -/
theorem ScalarCoeffOnData.isSymmetric {d : ℕ} {U : Ch02.Domain d}
    {a : Vec d → ℝ} (h : ScalarCoeffOnData U a) :
    Ch02.CoeffOn.IsSymmetric h.toCoeffOn :=
  Eventually.of_forall fun x => Homogenization.scalarMatrix_isSymm (a x)

/-- Two certificates for the same scalar field yield a.e.-equal coefficients. -/
theorem ScalarCoeffOnData.toCoeffOn_aeEq {d : ℕ} {U : Ch02.Domain d}
    {a : Vec d → ℝ} (h₁ h₂ : ScalarCoeffOnData U a) :
    Ch02.CoeffOn.AEEq h₁.toCoeffOn h₂.toCoeffOn :=
  EventuallyEq.rfl

/-- Two cube-wise certificate packages for the same scalar field agree a.e. -/
theorem ScalarTriadicCoeffData.toTriadicCoeffFamily_aeEq {d : ℕ}
    {a : Vec d → ℝ} (h₁ h₂ : ScalarTriadicCoeffData a) :
    Ch02.TriadicCoeffFamily.AEEq h₁.toTriadicCoeffFamily h₂.toTriadicCoeffFamily :=
  fun Q => (h₁.onCube Q).toCoeffOn_aeEq (h₂.onCube Q)

/-- Paper response functional `J(U,p,q;a)`. -/
noncomputable abbrev J {d : ℕ} (U : Ch02.Domain d) (a : Ch02.CoeffOn U)
    (p q : Vec d) : ℝ :=
  Ch02.responseJ U a p q

/-- The primal coarse matrix. -/
noncomputable abbrev aMatrix {d : ℕ} (U : Ch02.Domain d) (a : Ch02.CoeffOn U) :
    Mat d :=
  Ch02.aCoarse U a

/-- The dual coarse matrix. -/
noncomputable abbrev aStarMatrix {d : ℕ} (U : Ch02.Domain d)
    (a : Ch02.CoeffOn U) : Mat d :=
  Ch02.aStarCoarse U a

/-- `J` is independent of the ellipticity certificate. -/
theorem responseJ_toCoeffOn_eq {d : ℕ} {U : Ch02.Domain d}
    {a : Vec d → ℝ} (h₁ h₂ : ScalarCoeffOnData U a) (p q : Vec d) :
    J U h₁.toCoeffOn p q = J U h₂.toCoeffOn p q :=
  Ch02.responseJ_eq_ofAEEq (h₁.toCoeffOn_aeEq h₂) p q

/-- `aMatrix` is independent of the ellipticity certificate. -/
theorem aMatrix_toCoeffOn_eq {d : ℕ} {U : Ch02.Domain d}
    {a : Vec d → ℝ} (h₁ h₂ : ScalarCoeffOnData U a) :
    aMatrix U h₁.toCoeffOn = aMatrix U h₂.toCoeffOn :=
  Ch02.aCoarse_eq_ofAEEq (h₁.toCoeffOn_aeEq h₂)

/-- `aStarMatrix` is independent of the ellipticity certificate. -/
theorem aStarMatrix_toCoeffOn_eq {d : ℕ} {U : Ch02.Domain d}
    {a : Vec d → ℝ} (h₁ h₂ : ScalarCoeffOnData U a) :
    aStarMatrix U h₁.toCoeffOn = aStarMatrix U h₂.toCoeffOn :=
  Ch02.aStarCoarse_eq_ofAEEq (h₁.toCoeffOn_aeEq h₂)

/-- Paper `λ_{s,q}`. -/
noncomputable abbrev lambda {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (q : Ch02.MultiscaleExponent) (a : Ch02.TriadicCoeffFamily d) : ℝ :=
  Ch02.lambdaSq Q s q a

/-- Paper `Λ_{s,q}`. -/
noncomputable abbrev Lambda {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (q : Ch02.MultiscaleExponent) (a : Ch02.TriadicCoeffFamily d) : ℝ :=
  Ch02.LambdaSq Q s q a

/-- Paper default `λ_s = λ_{s,1}`. -/
noncomputable abbrev lambdaDefault {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : Ch02.TriadicCoeffFamily d) : ℝ :=
  lambda Q s (.finite 1) a

/-- Paper default `Λ_s = Λ_{s,1}`. -/
noncomputable abbrev LambdaDefault {d : ℕ} (Q : TriadicCube d) (s : ℝ)
    (a : Ch02.TriadicCoeffFamily d) : ℝ :=
  Lambda Q s (.finite 1) a

/-- The paper's scalar-normalized one-vector response probe. -/
noncomputable def paperScalarProbe {d : ℕ} (Q : TriadicCube d)
    (a : Ch02.TriadicCoeffFamily d) (alpha : ℝ) (e : Vec d) : ℝ :=
  J (Ch02.cubeDomain Q) (a.coeffOn Q)
    ((Real.sqrt alpha)⁻¹ • e) (Real.sqrt alpha • e)

end

end SubdiffusiveProcess.CoarseGrainingVocab
