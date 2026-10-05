module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.CutoffDirichletExistence
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.PositiveRescaling

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### Compactness of the cube closure -/

/-- The centered paper cube has compact closure. -/
theorem isCompact_closure_cube (d : ℕ) (m : ℤ) :
    IsCompact (closure (cube d m)) :=
  (isBounded_openCubeSet (originCube d m)).isCompact_closure

/-- The closure of the centered paper cube is nonempty. -/
theorem nonempty_closure_cube (d : ℕ) (m : ℤ) :
    (closure (cube d m)).Nonempty :=
  (nonempty_cube d m).mono subset_closure

/-! ### Positive continuous functions on the cube -/

/-- A positive continuous function attains strictly positive lower and finite
upper bounds on the centered paper cube. -/
theorem exists_bounds_of_continuous_of_pos {b : Vec d → ℝ}
    (hcont : Continuous b) (hpos : ∀ x, 0 < b x) (m : ℤ) :
    ∃ lam Lam : ℝ, 0 < lam ∧
      (∀ x ∈ cube d m, lam ≤ b x) ∧ (∀ x ∈ cube d m, b x ≤ Lam) := by
  obtain ⟨xmin, hxmin, hmin⟩ :=
    (isCompact_closure_cube d m).exists_isMinOn (nonempty_closure_cube d m)
      hcont.continuousOn
  obtain ⟨xmax, hxmax, hmax⟩ :=
    (isCompact_closure_cube d m).exists_isMaxOn (nonempty_closure_cube d m)
      hcont.continuousOn
  refine ⟨b xmin, b xmax, hpos xmin, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · exact hmin (subset_closure hx)
  · exact hmax (subset_closure hx)

/-! ### The ellipticity carrier for the cutoff coefficient -/



theorem exists_isEllipticFieldOn_coefficientAt
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) (m : ℤ) :
    ∃ lam Lam : ℝ, 0 < lam ∧
      IsEllipticFieldOn lam Lam (cube d m)
        (scalarCoeffField (coefficientAt M (N : WithTop ℕ) ω)) := by
  have hcont : Continuous (coefficientAt M (N : WithTop ℕ) ω) := by
    rw [coefficientAt_natCast]
    exact _root_.SubdiffusiveProcess.Model.continuous_aCutoff M N ω.1
  have hpos : ∀ x, 0 < coefficientAt M (N : WithTop ℕ) ω x := by
    intro x
    rw [coefficientAt_natCast]
    exact _root_.SubdiffusiveProcess.Model.aCutoff_pos M N ω.1 x
  obtain ⟨lam, Lam, hlam, hlow, hhigh⟩ :=
    exists_bounds_of_continuous_of_pos hcont hpos m
  refine ⟨lam, Lam, hlam, ?_⟩
  refine isEllipticFieldOn_scalarCoeffField_of_bounds hlam ?_ hlow hhigh
  exact hcont.measurable.ite (measurableSet_openCubeSet (originCube d m))
    measurable_const

/-- **S4 with the ellipticity discharged.**  Every `H¹` function on `𝔠_m` admits
a `coefficientAt M N ω`-harmonic comparison solution with the same boundary
data, unconditionally.  This is the `u_N`  with no
remaining side condition. -/
theorem exists_comparisonSolution_coefficientAt' [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.AnchoredC11Sample d) {m : ℤ}
    (u : H1Function (cube d m)) :
    ∃ v : H1Function (cube d m),
      IsWeaklyHarmonicOn (coefficientAt M (N : WithTop ℕ) ω) (cube d m) v ∧
        HasZeroTraceDifferenceOn (cube d m) v u := by
  obtain ⟨lam, Lam, _, hEll⟩ := exists_isEllipticFieldOn_coefficientAt M N ω m
  exact exists_comparisonSolution_coefficientAt hEll u

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
