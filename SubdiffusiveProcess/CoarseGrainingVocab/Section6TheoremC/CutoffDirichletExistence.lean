module

public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.EnergyBound
public import SubdiffusiveProcess.Section6.Defs.CoefficientAt

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### Ellipticity of a bounded scalar coefficient -/

/-- A two-sided scalar bound makes the scalar matrix elliptic. -/
theorem isEllipticMatrix_scalarMatrix_of_le {lam Lam s : ℝ} (hlam : 0 < lam)
    (hs1 : lam ≤ s) (hs2 : s ≤ Lam) :
    IsEllipticMatrix lam Lam (scalarMatrix (d := d) s) := by
  have hs : 0 < s := lt_of_lt_of_le hlam hs1
  refine ⟨hlam, le_trans hs1 hs2, fun xi ↦ ?_, fun xi ↦ ?_⟩
  · rw [matVecMul_scalarMatrix, vecDot_smul_right]
    exact mul_le_mul_of_nonneg_right hs1 (vecNormSq_nonneg _)
  · have hInv : ((scalarMatrix (d := d) s)⁻¹ : Mat d) = s⁻¹ • (1 : Mat d) := by
      rw [scalarMatrix, nonsing_inv_smul s (ne_of_gt hs) (by simp)]
      simp
    rw [hInv, matVecMul_scalarMatrix, vecDot_smul_right]
    refine mul_le_mul_of_nonneg_right ?_ (vecNormSq_nonneg _)
    have hinv := one_div_le_one_div_of_le hs hs2
    rwa [one_div, one_div] at hinv

/-- A measurably-restricted scalar coefficient bounded between `λ > 0` and `Λ`
gives the matrix ellipticity carrier the Dirichlet theory expects. -/
theorem isEllipticFieldOn_scalarCoeffField_of_bounds {lam Lam : ℝ}
    {W : Set (Vec d)} {s : Vec d → ℝ} (hlam : 0 < lam)
    (hmeas : Measurable fun x ↦ if x ∈ W then s x else 0)
    (hlow : ∀ x ∈ W, lam ≤ s x) (hhigh : ∀ x ∈ W, s x ≤ Lam) :
    IsEllipticFieldOn lam Lam W (scalarCoeffField s) := by
  classical
  refine ⟨?_, fun x hx ↦ isEllipticMatrix_scalarMatrix_of_le hlam (hlow x hx)
    (hhigh x hx)⟩
  have hfun : (fun (x : Vec d) (i j : Fin d) ↦
      if x ∈ W then scalarCoeffField s x i j else 0) =
      fun (x : Vec d) (i j : Fin d) ↦
        (if x ∈ W then s x else 0) * (if i = j then 1 else 0) := by
    funext x i j
    by_cases hx : x ∈ W <;>
      by_cases hij : i = j <;>
        simp [hx, hij, scalarCoeffField, scalarMatrix]
  rw [hfun]
  exact measurable_pi_iff.mpr fun i ↦ measurable_pi_iff.mpr fun j ↦
    hmeas.mul measurable_const

/-! ### Geometry of the centered cube -/

/-- The centre of a triadic cube lies in its open realization. -/
theorem nonempty_openCubeSet (Q : TriadicCube d) :
    Set.Nonempty (openCubeSet Q) := by
  refine ⟨fun i ↦ (Q.index i : ℝ) * cubeScaleFactor Q, fun i ↦ ?_⟩
  have hsf : (0 : ℝ) < cubeScaleFactor Q := by
    rw [cubeScaleFactor]; positivity
  constructor <;> nlinarith [hsf]

/-- The centered paper cube is a bounded open convex domain. -/
theorem isOpenBoundedConvexDomain_cube (d : ℕ) (m : ℤ) :
    IsOpenBoundedConvexDomain (cube d m) :=
  isOpenBoundedConvexDomain_openCubeSet (originCube d m)

/-- The centered paper cube is nonempty. -/
theorem nonempty_cube (d : ℕ) (m : ℤ) : Set.Nonempty (cube d m) :=
  nonempty_openCubeSet (originCube d m)

/-! ### The comparison solution -/

/-- **S4.**  On the centered paper cube, every `H¹` function admits a
`b`-harmonic comparison solution with the same boundary data.

This is the construction of `u_N`  specialized
from `exists_isWeaklyHarmonicOn_and_hasZeroTraceDifferenceOn` to the window
Theorem C uses. -/
theorem exists_comparisonSolution_cube [NeZero d] {m : ℤ} {b : Vec d → ℝ}
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cube d m) (scalarCoeffField b))
    (u : H1Function (cube d m)) :
    ∃ v : H1Function (cube d m),
      IsWeaklyHarmonicOn b (cube d m) v ∧
        HasZeroTraceDifferenceOn (cube d m) v u :=
  exists_isWeaklyHarmonicOn_and_hasZeroTraceDifferenceOn
    (isOpenBoundedConvexDomain_cube d m) (nonempty_cube d m) hEll u

/-- The comparison solution is unique up to almost-everywhere equality, so the
family `u_N` is well defined.  Reused from `DirichletUniqueness`. -/
theorem comparisonSolution_cube_ae_unique [NeZero d] {m : ℤ} {b : Vec d → ℝ}
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cube d m) (scalarCoeffField b))
    {v v' u : H1Function (cube d m)}
    (hv : IsWeaklyHarmonicOn b (cube d m) v)
    (hvu : HasZeroTraceDifferenceOn (cube d m) v u)
    (hv' : IsWeaklyHarmonicOn b (cube d m) v')
    (hv'u : HasZeroTraceDifferenceOn (cube d m) v' u) :
    v.toFun =ᵐ[volume.restrict (cube d m)] v'.toFun ∧
      v.grad =ᵐ[volume.restrict (cube d m)] v'.grad :=
  ae_eq_of_isWeaklyHarmonicOn_of_hasZeroTraceDifferenceOn
    (isOpenBoundedConvexDomain_cube d m) (nonempty_cube d m) hEll
    hv hvu hv' hv'u

/-- **S4 at a finite cutoff.**  The comparison solution for the coefficient
`coefficientAt M (N : ℕ) ω` of the statement, which at a finite cutoff is
the paper's `a_N`.  Together with `PositiveRescaling`, whose invariance lemmas
show the equation is unchanged by the normalization `a_N ↦ a_N/a_N(0) = ã_N`,
this is exactly the `u_N`. -/
theorem exists_comparisonSolution_coefficientAt [NeZero d]
    {M : _root_.SubdiffusiveProcess.Model.GMCModel d} {N : ℕ}
    {ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d} {m : ℤ} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cube d m)
      (scalarCoeffField (coefficientAt M (N : WithTop ℕ) ω)))
    (u : H1Function (cube d m)) :
    ∃ v : H1Function (cube d m),
      IsWeaklyHarmonicOn (coefficientAt M (N : WithTop ℕ) ω) (cube d m) v ∧
        HasZeroTraceDifferenceOn (cube d m) v u :=
  exists_comparisonSolution_cube hEll u

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
