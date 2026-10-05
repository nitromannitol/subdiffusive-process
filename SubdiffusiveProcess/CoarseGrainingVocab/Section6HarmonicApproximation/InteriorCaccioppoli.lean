module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCellGeometry
public import SubdiffusiveProcess.CoarseGrainingVocab.CaccioppoliRHS

@[expose] public section

/-!
# Mean-subtracted interior Caccioppoli

The established interior endpoint is stated for the solution itself.  Interior
equations are invariant under constants, so this module records the exact
mean-subtracted form consumed by harmonic approximation.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03

noncomputable section

variable {d : ℕ}

private def constH1 (Q : TriadicCube d) (c : ℝ) :
    H1Function (openCubeSet Q) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q)
    (contDiff_const : ContDiff ℝ 1 fun _ : Vec d => c)

private theorem constH1_toFun (Q : TriadicCube d) (c : ℝ) :
    (constH1 Q c).toFun = fun _ => c := rfl

private theorem constH1_grad (Q : TriadicCube d) (c : ℝ) :
    (constH1 Q c).grad = fun _ => (0 : Vec d) := by
  funext y i
  show (fderiv ℝ (fun _ : Vec d => c) y) (basisVec i) = 0
  rw [fderiv_fun_const]
  rfl

private theorem sub_constH1_grad (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) (c : ℝ) :
    (u - constH1 Q c).grad = u.grad := by
  rw [H1Function.sub_grad, constH1_grad]
  funext y
  exact sub_zero (u.grad y)

private theorem sub_constH1_toFun (Q : TriadicCube d)
    (u : H1Function (openCubeSet Q)) (c : ℝ) :
    (u - constH1 Q c).toFun = fun y => u.toFun y - c := by
  funext y
  rw [H1Function.sub_toFun, constH1_toFun]

private theorem isForcedEquation_sub_constH1
    {Q : TriadicCube d} {A : CoeffFamily d} {g : Vec d → Vec d}
    (u : H1Function (openCubeSet Q)) (c : ℝ)
    (hu : IsForcedEquation Q A u g) :
    IsForcedEquation Q A (u - constH1 Q c) g := by
  intro phi
  rw [sub_constH1_grad]
  exact hu phi

private theorem localizedCoeffEnergyValue_congr_grad
    (V : Set (Vec d)) {Q : TriadicCube d} (A : CoeffFamily d)
    {u v : H1Function (openCubeSet Q)} (hgrad : v.grad = u.grad) :
    localizedCoeffEnergyValue V (A.coeffOn Q) v =
      localizedCoeffEnergyValue V (A.coeffOn Q) u := by
  unfold localizedCoeffEnergyValue
  rw [hgrad]

variable [NeZero d]

/-- Interior Caccioppoli with an arbitrary constant subtracted from the
parent `L²` term. -/
theorem exists_interior_caccioppoli_quarter_subConst (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {A : CoeffFamily d} {s t : ℝ}
        {x : Vec d} {g : Vec d → Vec d}
        (u : H1Function (openCubeSet Q)) (c : ℝ),
        IsForcedEquation Q A u g →
        0 < s → s < 1 → 0 < t → t ≤ 1 / 4 → s + t < 1 →
        openCubeAtScale x (Q.scale - 1) ⊆ openCubeSet Q →
        ForceBesovRegularity Q (2 * t) g →
          localizedCoeffEnergyValue (caccioppoliCoreSet Q x) (A.coeffOn Q) u ≤
            caccioppoliWithRHSPrefactor C Q A s t *
              (Ch02.lambdaS Q t A *
                  Real.rpow (3 : ℝ) (-2 * (((Q.scale : ℤ) : ℝ))) *
                  normalizedL2SqOnSet (openCubeSet Q)
                    (fun y => u.toFun y - c) +
                Real.rpow t (-11 : ℝ) *
                  Real.rpow (Ch02.lambdaS Q t A) (-1 : ℝ) *
                  scaleNormalizedPositiveBesovVectorSeminormTwo Q (2 * t) g ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_interior_caccioppoli_quarter d
  refine ⟨C, hC, ?_⟩
  intro Q A s t x g u c hu hs hs1 ht ht4 hst hpatch hg
  let uc := u - constH1 Q c
  have heq : IsForcedEquation Q A uc g :=
    isForcedEquation_sub_constH1 u c hu
  have hmain := hbound uc heq hs hs1 ht ht4 hst hpatch hg
  rw [localizedCoeffEnergyValue_congr_grad
      (caccioppoliCoreSet Q x) A (sub_constH1_grad Q u c),
    sub_constH1_toFun] at hmain
  exact hmain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
