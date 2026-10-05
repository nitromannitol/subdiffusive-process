module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.NestedFamilyDirichlet

@[expose] public section

/-!
# The complete nested two-radius family: all three budgets

The cell family is
`Σ`-free — a product of the retained overlap centres and the descendants of
the origin inner parent — every cell lies in the fixed concentric interior of
its parent (so the two harmonic estimates are untouched), and the Dirichlet
member becomes a genuine descendant average, controlled by the canonical
descendant budget up to the `N`-independent constant `(3^d)^a`.
-/

open MeasureTheory Homogenization
open scoped ENNReal

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- Translation covariance of the nested family's Dirichlet cell
observable. -/
theorem nfNested_dirichletB_eq [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (K mm : ℤ) (j N : ℕ) (hh : 0 < h) (hN : 1 ≤ N)
    (V : NFSample d → CubeVectorW1pFunction (originCube d mm)
      oneStepFourExponent)
    (hV : ∀ omega, (V omega).toField =
      (oneStepOriginDirichletSolution M n h p mm omega hh).toH1Function.grad)
    {P₀ : TriadicCube d} {k : ℕ} (q : NFNestedIndex d K j P₀ k)
    (hSscale : (q.1.1).scale + 1 = mm)
    (hRscale : (q.2.1).scale = mm - (N : ℤ))
    (hRmem : q.2.1 ∈ descendantsAtDepth (originCube d mm) N)
    (omega : NFSample d)
    {u : H1Function (openCubeSet (nfNestedCell N q))}
    (H : HasWeakHessianOn (openCubeSet (nfNestedCell N q)) u)
    (hu : u.grad =
      (oneStepDirichletAxisLocalSolution M n h omega p
        (cubeCenter q.1.1) mm hh).grad) :
    oneStepCellB (nfNestedCell N q) H =
      nfOriginCellB M n h p mm hh N V hV q.2.1
        (translatePotentialSequence (cubeCenter q.1.1) omega) := by
  classical
  set z : Vec d := cubeCenter q.1.1 with hz
  set omegaZ : NFSample d := translatePotentialSequence z omega with homegaZ
  -- the explicit Calderon--Zygmund witness on the parent, restricted
  have hcellParent : openCubeSet (nfNestedCell N q) ⊆ nfAxisParent d z mm := by
    rw [nfNestedCell, openCubeSet_nfCell_eq q.1.1 hN hSscale q.2.1 hRscale]
    have hsub := translateSet_mono z
      (openCubeSet_subset_of_mem_descendantsAtDepth hRmem)
    rw [nfAxisParent_eq_translateSet]
    exact hsub
  let HP : HasWeakHessianOn (nfAxisParent d z mm)
      (oneStepDirichletAxisLocalSolution M n h omega p z mm hh) :=
    nfAxisDirichletHessianOf M n h p z mm hh V hV omega
  let HC : HasWeakHessianOn (openCubeSet (nfNestedCell N q))
      ((oneStepDirichletAxisLocalSolution M n h omega p z mm hh).restrict
        (isOpen_openCubeSet (nfNestedCell N q)) hcellParent) :=
    HP.restrict (isOpen_openCubeSet (nfNestedCell N q)) hcellParent
  let HU : HasWeakHessianOn (openCubeSet (nfNestedCell N q)) u :=
    nfWeakHessianOfGradEq hu HC
  -- the origin-side witness at the translated sample
  have hR₀sub : openCubeSet q.2.1 ⊆ openCubeSet (originCube d mm) :=
    openCubeSet_subset_of_mem_descendantsAtDepth hRmem
  let HO : HasWeakHessianOn (openCubeSet q.2.1)
      ((oneStepOriginDirichletSolution M n h p mm omegaZ hh
        ).toH1Function.restrict (isOpen_openCubeSet q.2.1) hR₀sub) :=
    (nfOriginDirichletHessianOf M n h p mm hh V hV omegaZ).restrict
      (isOpen_openCubeSet q.2.1) hR₀sub
  have hstep₁ : oneStepCellB (nfNestedCell N q) H =
      oneStepCellB (nfNestedCell N q) HU :=
    oneStepCellB_congr_hessian (nfNestedCell N q) H HU
  have hstep₂ : oneStepCellB (nfNestedCell N q) HU =
      oneStepCellB q.2.1 HO := by
    refine oneStepCellB_translate_eq (R := q.2.1) (R' := nfNestedCell N q)
      z ?_ (nfNestedCell_scale N q) HO HU ?_
    · rw [nfNestedCell, openCubeSet_nfCell_eq q.1.1 hN hSscale q.2.1 hRscale]
    · intro i j' x
      show (HU.hess) i j' x = (HO.hess) i j' (x - z)
      erw [nfWeakHessianOfGradEq_hess]
      show (HP.hess) i j' x =
        (nfOriginDirichletHessianOf M n h p mm hh V hV omegaZ).hess i j' (x - z)
      erw [nfAxisDirichletHessianOf_hess, nfOriginDirichletHessianOf_hess]
  have hstep₃ : nfOriginCellB M n h p mm hh N V hV q.2.1 omegaZ =
      oneStepCellB q.2.1 HO := by
    unfold nfOriginCellB
    rw [dite_eq_left hRmem]
  rw [hstep₁, hstep₂, hstep₃]

/-- Product-index average, rewritten as an iterated average with the second
factor outermost. -/
theorem nfProd_average_swap {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (g : ι₁ → ι₂ → ℝ≥0∞) :
    (((Finset.univ : Finset (ι₁ × ι₂)).card : ℝ≥0∞))⁻¹ *
        ∑ q : ι₁ × ι₂, g q.1 q.2 =
      ∑ y : ι₂, (((Finset.univ : Finset ι₂).card : ℝ≥0∞))⁻¹ *
        ((((Finset.univ : Finset ι₁).card : ℝ≥0∞))⁻¹ * ∑ x : ι₁, g x y) := by
  classical
  have h1top : (((Finset.univ : Finset ι₁).card : ℝ≥0∞)) ≠ ∞ := by finiteness
  have h2top : (((Finset.univ : Finset ι₂).card : ℝ≥0∞)) ≠ ∞ := by finiteness
  have hcard : ((Finset.univ : Finset (ι₁ × ι₂)).card : ℝ≥0∞) =
      ((Finset.univ : Finset ι₁).card : ℝ≥0∞) *
        ((Finset.univ : Finset ι₂).card : ℝ≥0∞) := by
    simp [Finset.card_univ, Fintype.card_prod]
  rw [hcard, Fintype.sum_prod_type, Finset.sum_comm,
    ENNReal.mul_inv (Or.inr h2top) (Or.inl h1top), Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
