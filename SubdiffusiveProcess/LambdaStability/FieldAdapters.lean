import SubdiffusiveProcess.LambdaStability.Transport
import SubdiffusiveProcess.CoarseGrainingVocab.SharpCompareJ
import Homogenization.CoarseGraining.Symmetric.CoarseMatrices

/-! Pointwise field extensions and the canonical set-level carriers. -/
open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube

noncomputable section
namespace SubdiffusiveProcess.LambdaStability

variable {d : ℕ}

/-- A pointwise elliptic field gives the standard a.e. coefficient on a domain. -/
def coeffOn (U : Ch02.Domain d) (g : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) g) : Ch02.CoeffOn U where
  toCoeffField := g
  lam := lam
  Lam := Lam
  lam_pos := (hEll.2 (Classical.choose U.nonempty) (Classical.choose_spec U.nonempty)).1
  lam_le_Lam := (hEll.2 (Classical.choose U.nonempty) (Classical.choose_spec U.nonempty)).2.1
  aeStronglyMeasurable := by
    intro i j
    have hentry : Measurable fun x : Vec d => restrictCoeffField (U : Set (Vec d)) g x i j := by
      have hij := (measurable_pi_iff.1 (measurable_pi_iff.1 hEll.1 i) j)
      convert hij using 1
      funext x
      by_cases hx : x ∈ (U : Set (Vec d)) <;> simp [restrictCoeffField, hx]
    exact hentry.aestronglyMeasurable
  aeElliptic := by
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    exact hEll.2 x hx

/-- Extend by an elliptic scalar matrix outside the root domain. -/
def extendField (U : Set (Vec d)) (g : CoeffField d) (lam : ℝ) : CoeffField d :=
  by
    classical
    exact fun x => if x ∈ U then g x else lam • (1 : Mat d)

theorem extendField_eqOn (U : Set (Vec d)) (g : CoeffField d) (lam : ℝ) :
    Set.EqOn (extendField U g lam) g U := by
  intro x hx
  simp only [extendField, if_pos hx]

theorem extendField_measurable (U : Ch02.Domain d) (g : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) g) :
    Measurable (extendField U g lam) := by
  classical
  apply measurable_pi_iff.2
  intro i
  apply measurable_pi_iff.2
  intro j
  have hij := (measurable_pi_iff.1 (measurable_pi_iff.1 hEll.1 i) j)
  have hc : Measurable (fun x : Vec d =>
      if x ∈ (U : Set (Vec d)) then (0 : ℝ) else (lam • (1 : Mat d)) i j) :=
    Measurable.ite U.measurableSet measurable_const measurable_const
  convert hij.add hc using 1
  funext x
  by_cases hx : x ∈ (U : Set (Vec d)) <;> simp [extendField, hx]

theorem extendField_elliptic (U : Ch02.Domain d) (g : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) g) :
    IsEllipticFieldOn lam Lam Set.univ (extendField U g lam) := by
  classical
  refine ⟨?_, ?_⟩
  · simpa only [Set.mem_univ, if_true] using extendField_measurable U g hEll
  · intro x _
    by_cases hx : x ∈ (U : Set (Vec d))
    · simpa only [extendField, if_pos hx] using hEll.2 x hx
    · simp only [extendField, if_neg hx]
      exact Homogenization.Internal.Ch02.BookCh02.isEllipticMatrix_smul_one
        (coeffOn U g hEll).lam_pos (coeffOn U g hEll).lam_le_Lam

theorem extendField_symm (U : Set (Vec d)) (g : CoeffField d) (lam : ℝ)
    (hsym : ∀ x ∈ U, (g x).IsSymm) :
    IsSymmetricCoeffField (extendField U g lam) := by
  intro x
  by_cases hx : x ∈ U
  · simpa only [extendField, if_pos hx] using hsym x hx
  · simp only [extendField, if_neg hx]
    exact (Matrix.isSymm_one : (1 : Mat d).IsSymm).smul lam

/-- The global extension has one identical representative on every cube. -/
def fieldFamily (g : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam Set.univ g) : Ch02.TriadicCoeffFamily d where
  coeffOn := fun Q => coeffOn (Ch02.cubeDomain Q) g
    (hEll.mono (measurableSet_openCubeSet Q) (Set.subset_univ _))
  restrictsTo_of_subset := fun _ => Filter.EventuallyEq.rfl

variable [NeZero d]

/-- The symmetry specialization identifies the primal matrix with the upper response matrix. -/
theorem aCoarse_eq_bCoarse (U : Ch02.Domain d) {g : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) g)
    (hsym : IsSymmetricCoeffField g) :
    Homogenization.aCoarse (sigmaCoarse U g) (kappaCoarse U g) =
      Homogenization.bCoarse (sigmaCoarse U g) (sigmaStarCoarse U g) (kappaCoarse U g) := by
  have hv := Homogenization.Internal.Ch02.BookCh02.domain_volume_pos U
  obtain ⟨_, _, _, hA, _, _, _, _, _⟩ :=
    Homogenization.Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
      U.isDomain hEll hv
  rw [Homogenization.aCoarse_canonical_eq_sigmaCoarse_of_isSymmetricCoeffField_of_isCoarseBlockMatrix hsym hA,
    Homogenization.bCoarse_canonical_eq_sigmaCoarse_of_isSymmetricCoeffField_of_isCoarseBlockMatrix hsym hA]

omit [NeZero d] in
/-- Equality on a domain implies equality of its response and all canonical matrices. -/
theorem carriers_eq_of_eqOn (U : Ch02.Domain d) {g h : CoeffField d}
    {lam Lam lam' Lam' : ℝ}
    (hg : IsEllipticFieldOn lam Lam (U : Set (Vec d)) g)
    (hh : IsEllipticFieldOn lam' Lam' (U : Set (Vec d)) h)
    (heq : Set.EqOn g h (U : Set (Vec d))) :
    (∀ p q, ResponseJ U p q g = ResponseJ U p q h) ∧
    Homogenization.sigmaStarInvCoarse U g = Homogenization.sigmaStarInvCoarse U h ∧
    sigmaCoarse U g = sigmaCoarse U h ∧ kappaCoarse U g = kappaCoarse U h := by
  let a := coeffOn U g hg
  let b := coeffOn U h hh
  have hab : Ch02.CoeffOn.AEEq a b := by
    filter_upwards [ae_restrict_mem U.measurableSet] with x hx
    exact heq hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p q
    simpa only [Homogenization.Internal.Ch02.book_responseJ_eq_ResponseJ] using
      Ch02.responseJ_eq_ofAEEq hab p q
  · simpa only [Homogenization.Internal.Ch02.book_sigmaStarInvCoarse_eq_sigmaStarInvCoarse] using
      Ch02.sigmaStarInvCoarse_eq_ofAEEq hab
  · simpa only [Homogenization.Internal.Ch02.book_sigmaCoarse_eq_sigmaCoarse] using
      Ch02.sigmaCoarse_eq_ofAEEq hab
  · simpa only [Homogenization.Internal.Ch02.book_kappaCoarse_eq_kappaCoarse] using
      Ch02.kappaCoarse_eq_ofAEEq hab

end SubdiffusiveProcess.LambdaStability
