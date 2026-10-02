import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.CellBTranslation

/-!
# The cell observable does not depend on the Hessian witness

`oneStepCellB R H` is defined from `H.hess`, and a weak Hessian witness is
chosen, not canonical.  Weak derivatives are a.e. unique on open sets
(`HasWeakPartialDerivOn.ae_eq`), so any two witnesses for the same `H¹`
function give the same observable.  This is what lets the committed family
(whose Dirichlet Hessian is a `Nonempty.some`) be evaluated through the
*explicit* Calderon--Zygmund witness, which is the one the descendant budget
controls.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- Two weak Hessian witnesses of the same `H¹` function on an open cell give
the same cell observable. -/
theorem oneStepCellB_congr_hessian (R : TriadicCube d)
    {u : H1Function (openCubeSet R)}
    (H₁ H₂ : HasWeakHessianOn (openCubeSet R) u) :
    oneStepCellB R H₁ = oneStepCellB R H₂ := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
    isFiniteMeasure_volumeMeasureOn_openCubeSet R
  have hloc : ∀ (H : HasWeakHessianOn (openCubeSet R) u) (i j : Fin d),
      LocallyIntegrableOn (H.hess i j) (openCubeSet R) volume := by
    intro H i j
    have hint : IntegrableOn (H.hess i j) (openCubeSet R) volume := by
      have := (H.hess_memL2 i j).integrable (by norm_num)
      simpa [IntegrableOn, volumeMeasureOn] using this
    exact hint.locallyIntegrableOn
  rw [oneStepCellB_eq_sum_eLpNorm, oneStepCellB_eq_sum_eLpNorm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine eLpNorm_congr_ae ?_
  exact HasWeakPartialDerivOn.ae_eq (isOpen_openCubeSet R)
    (hloc H₁ i j) (hloc H₂ i j) (H₁.weak_second i j) (H₂.weak_second i j)

/-- The `hess` field is unchanged by a domain cast. -/
theorem nfCastWeakHessian_hess {U V : Set (Vec d)} (hUV : U = V)
    {u : H1Function U} (H : HasWeakHessianOn U u) :
    (nfCastWeakHessian hUV H).hess = H.hess := by
  subst hUV
  rfl

/-! ## The explicit Calderon--Zygmund Dirichlet witness on a concentric
parent -/

/-- The Calderon--Zygmund weak Hessian of the local Dirichlet solution on the
concentric parent, built explicitly from the origin-cube `W^{1,4}`
representatives at the translated sample. -/
def nfAxisDirichletHessianOf [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p z : Vec d) (m : ℤ)
    (hh : 0 < h)
    (V : NFSample d → CubeVectorW1pFunction (originCube d m)
      oneStepFourExponent)
    (hV : ∀ omega, (V omega).toField =
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad)
    (omega : NFSample d) :
    HasWeakHessianOn (nfAxisParent d z m)
      (oneStepDirichletAxisLocalSolution M n h omega p z m hh) :=
  nfWeakHessianOfGradEq
    (by
      rw [nfCastH1Domain_grad]
      exact nfAxisDirichletLocal_grad_translate M n h omega p z m hh)
    (nfCastWeakHessian (translateSet_openCubeSet_originCube_eq_axisCube z m)
      ((weakHessianOfCubeVectorW1pFour
        (V (translatePotentialSequence z omega))
        (hV (translatePotentialSequence z omega))).translate z))

theorem nfAxisDirichletHessianOf_hess [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p z : Vec d) (m : ℤ)
    (hh : 0 < h)
    (V : NFSample d → CubeVectorW1pFunction (originCube d m)
      oneStepFourExponent)
    (hV : ∀ omega, (V omega).toField =
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad)
    (omega : NFSample d) (i j : Fin d) (x : Vec d) :
    (nfAxisDirichletHessianOf M n h p z m hh V hV omega).hess i j x =
      (V (translatePotentialSequence z omega)).jacobian (x - z) i j := by
  unfold nfAxisDirichletHessianOf
  rw [nfWeakHessianOfGradEq_hess, nfCastWeakHessian_hess]
  rfl

/-- The origin-cube Calderon--Zygmund witness, as a weak Hessian of the
canonical origin Dirichlet solution. -/
def nfOriginDirichletHessianOf [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (m : ℤ)
    (hh : 0 < h)
    (V : NFSample d → CubeVectorW1pFunction (originCube d m)
      oneStepFourExponent)
    (hV : ∀ omega, (V omega).toField =
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad)
    (omega : NFSample d) :
    HasWeakHessianOn (openCubeSet (originCube d m))
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function :=
  weakHessianOfCubeVectorW1pFour (V omega) (hV omega)

@[simp] theorem nfOriginDirichletHessianOf_hess [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n h : ℕ) (p : Vec d) (m : ℤ)
    (hh : 0 < h)
    (V : NFSample d → CubeVectorW1pFunction (originCube d m)
      oneStepFourExponent)
    (hV : ∀ omega, (V omega).toField =
      (oneStepOriginDirichletSolution M n h p m omega hh).toH1Function.grad)
    (omega : NFSample d) (i j : Fin d) (x : Vec d) :
    (nfOriginDirichletHessianOf M n h p m hh V hV omega).hess i j x =
      (V omega).jacobian x i j := rfl

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
