module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.StationaryRepresentativeMollification
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

@[expose] public section

/-!
# Spatial primitives of smooth curl-free realizations

This is the deterministic Poincare-lemma endpoint used after realizing a
mollified stationary potential field.  It mirrors the primitive construction
in Superdiffusion's `PotentialApproximation.lean`, but is dimension-free and
is stated directly for the Euclidean vector carrier used by SubdiffusiveProcess.
-/

open Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-- The Euclidean pairing as a continuous linear map into the dual. -/
def euclideanDotCLM (d : ℕ) : Vec d →L[ℝ] (Vec d →L[ℝ] ℝ) :=
  ∑ i : Fin d,
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).smulRight
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)

@[simp] theorem euclideanDotCLM_apply {d : ℕ} (v w : Vec d) :
    euclideanDotCLM d v w = vecDot v w := by
  simp [euclideanDotCLM, vecDot]

/-- The one-form dual to a Euclidean vector field. -/
def euclideanDualForm {d : ℕ} (F : Vec d → Vec d) :
    Vec d → (Vec d →L[ℝ] ℝ) :=
  fun x => euclideanDotCLM d (F x)

theorem hasFDerivAt_euclideanDualForm {d : ℕ}
    {F : Vec d → Vec d} {a : Vec d} {A : Vec d →L[ℝ] Vec d}
    (hF : HasFDerivAt F A a) :
    HasFDerivAt (euclideanDualForm F) ((euclideanDotCLM d).comp A) a :=
  (euclideanDotCLM d).hasFDerivAt.comp a hF

theorem fderiv_euclideanDualForm_apply {d : ℕ}
    {F : Vec d → Vec d} {a : Vec d}
    (hF : DifferentiableAt ℝ F a) (x y : Vec d) :
    fderiv ℝ (euclideanDualForm F) a x y =
      vecDot (fderiv ℝ F a x) y := by
  rw [(hasFDerivAt_euclideanDualForm hF.hasFDerivAt).fderiv]
  simp

/-- A differentiable Euclidean vector field with symmetric derivative has a
global scalar primitive. -/
theorem exists_globalPrimitive_of_fderiv_symmetric {d : ℕ}
    {F : Vec d → Vec d} (hF : Differentiable ℝ F)
    (hsymm : ∀ a x y : Vec d,
      vecDot (fderiv ℝ F a x) y = vecDot (fderiv ℝ F a y) x) :
    ∃ phi : Vec d → ℝ, ∀ a : Vec d,
      HasFDerivAt phi (euclideanDualForm F a) a := by
  obtain ⟨phi, hphi⟩ :=
    (convex_univ : Convex ℝ (Set.univ : Set (Vec d)))
      |>.exists_forall_hasFDerivAt_of_fderiv_symmetric isOpen_univ
        (fun a _ => by
          simpa only [euclideanDualForm] using
            (euclideanDotCLM d).differentiableAt.comp a (hF a) |>.differentiableWithinAt)
        (fun a _ x y => by
          change fderiv ℝ (euclideanDualForm F) a x y =
            fderiv ℝ (euclideanDualForm F) a y x
          rw [fderiv_euclideanDualForm_apply (hF a),
            fderiv_euclideanDualForm_apply (hF a)]
          exact hsymm a x y)
  exact ⟨phi, fun a => hphi a (Set.mem_univ a)⟩

/-- Coordinate form of the global primitive identity. -/
theorem exists_globalPrimitive_coordinate_gradient {d : ℕ}
    {F : Vec d → Vec d} (hF : Differentiable ℝ F)
    (hsymm : ∀ a x y : Vec d,
      vecDot (fderiv ℝ F a x) y = vecDot (fderiv ℝ F a y) x) :
    ∃ phi : Vec d → ℝ,
      ∀ (a : Vec d) (i : Fin d),
        fderiv ℝ phi a (basisVec i) = F a i := by
  obtain ⟨phi, hphi⟩ := exists_globalPrimitive_of_fderiv_symmetric hF hsymm
  refine ⟨phi, fun a i => ?_⟩
  rw [(hphi a).fderiv]
  simpa [euclideanDualForm, euclideanDotCLM_apply] using
    vecDot_basisVec_right (F a) i

/-- Smooth version of the Euclidean Poincare lemma.  When the curl-free
vector field is smooth, its global primitive may be retained together with
the smoothness needed by the quantitative boundary cutoff. -/
theorem exists_contDiff_globalPrimitive_coordinate_gradient {d : ℕ}
    {F : Vec d → Vec d} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsymm : ∀ a x y : Vec d,
      vecDot (fderiv ℝ F a x) y = vecDot (fderiv ℝ F a y) x) :
    ∃ phi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) phi ∧
      ∀ (a : Vec d) (i : Fin d),
        fderiv ℝ phi a (basisVec i) = F a i := by
  obtain ⟨phi, hphi⟩ :=
    exists_globalPrimitive_of_fderiv_symmetric
      (hF.differentiable (by simp)) hsymm
  have hdiff : Differentiable ℝ phi := fun a => (hphi a).differentiableAt
  have hfderiv : fderiv ℝ phi = euclideanDualForm F := by
    funext a
    exact (hphi a).fderiv
  have hdual : ContDiff ℝ (⊤ : ℕ∞) (euclideanDualForm F) :=
    (euclideanDotCLM d).contDiff.comp hF
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) phi := by
    rw [contDiff_infty_iff_fderiv]
    exact ⟨hdiff, by simpa only [hfderiv] using hdual⟩
  refine ⟨phi, hsmooth, fun a i => ?_⟩
  rw [(hphi a).fderiv]
  simpa [euclideanDualForm, euclideanDotCLM_apply] using
    vecDot_basisVec_right (F a) i

private theorem sum_smul_basisVec {d : ℕ} (x : Vec d) :
    ∑ i : Fin d, x i • (basisVec i : Vec d) = x := by
  funext j
  simp [basisVec, Pi.single_apply]

private theorem fderiv_symmetric_of_basis_symmetric {d : ℕ}
    {F : Vec d → Vec d}
    (hsymm : ∀ a : Vec d, ∀ i j : Fin d,
      fderiv ℝ F a (basisVec i) j =
        fderiv ℝ F a (basisVec j) i) :
    ∀ a x y : Vec d,
      vecDot (fderiv ℝ F a x) y = vecDot (fderiv ℝ F a y) x := by
  intro a x y
  have hx : fderiv ℝ F a x =
      ∑ i : Fin d, x i • fderiv ℝ F a (basisVec i) := by
    calc
      fderiv ℝ F a x = fderiv ℝ F a
          (∑ i : Fin d, x i • (basisVec i : Vec d)) := by
        rw [sum_smul_basisVec]
      _ = ∑ i : Fin d,
          fderiv ℝ F a (x i • (basisVec i : Vec d)) := map_sum _ _ _
      _ = ∑ i : Fin d, x i • fderiv ℝ F a (basisVec i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul]
  have hy : fderiv ℝ F a y =
      ∑ j : Fin d, y j • fderiv ℝ F a (basisVec j) := by
    calc
      fderiv ℝ F a y = fderiv ℝ F a
          (∑ j : Fin d, y j • (basisVec j : Vec d)) := by
        rw [sum_smul_basisVec]
      _ = ∑ j : Fin d,
          fderiv ℝ F a (y j • (basisVec j : Vec d)) := map_sum _ _ _
      _ = ∑ j : Fin d, y j • fderiv ℝ F a (basisVec j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul]
  rw [hx, hy]
  simp only [vecDot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hsymm a j i]
  ring

/-- It suffices to check symmetry of the derivative on coordinate vectors.
This is the form delivered directly by the stationary curl calculation. -/
theorem exists_globalPrimitive_of_fderiv_basis_symmetric {d : ℕ}
    {F : Vec d → Vec d} (hF : Differentiable ℝ F)
    (hsymm : ∀ a : Vec d, ∀ i j : Fin d,
      fderiv ℝ F a (basisVec i) j =
        fderiv ℝ F a (basisVec j) i) :
    ∃ phi : Vec d → ℝ,
      ∀ (a : Vec d) (i : Fin d),
        fderiv ℝ phi a (basisVec i) = F a i := by
  exact exists_globalPrimitive_coordinate_gradient hF
    (fderiv_symmetric_of_basis_symmetric hsymm)

/-- Smooth coordinate version used by the stationary-potential cutoff. -/
theorem exists_contDiff_globalPrimitive_of_fderiv_basis_symmetric {d : ℕ}
    {F : Vec d → Vec d} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsymm : ∀ a : Vec d, ∀ i j : Fin d,
      fderiv ℝ F a (basisVec i) j =
        fderiv ℝ F a (basisVec j) i) :
    ∃ phi : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) phi ∧
      ∀ (a : Vec d) (i : Fin d),
        fderiv ℝ phi a (basisVec i) = F a i := by
  exact exists_contDiff_globalPrimitive_coordinate_gradient hF
    (fderiv_symmetric_of_basis_symmetric hsymm)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
