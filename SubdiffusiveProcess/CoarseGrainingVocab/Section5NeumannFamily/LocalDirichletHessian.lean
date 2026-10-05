module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily.TriadicAxisCarrier

@[expose] public section

/-!
# The persistent Dirichlet member has a weak Hessian on every triadic parent

`exists_measurable_oneStepCanonicalDirichlet_cellB` supplies Calderon--Zygmund
`W^{1,4}` representatives for the *literal* canonical origin-cube Dirichlet
solution at every scale and every sample.  Translating that witness by the
cube's own shift vector and casting the domain gives a weak Hessian for
`twoRadiusLocalDirichletPiece` on an arbitrary triadic parent cube.

Only the existence of a samplewise witness is needed: measurability of the
induced `B` observable is a consequence of gradient measurability alone
(`measurable_oneStepCellB`), never of how the Hessian representatives are
chosen.
-/

open MeasureTheory Homogenization

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily

open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

variable {d : ℕ}

/-- The gradient of a domain-cast zero-trace Sobolev function. -/
theorem nfGradCastH10 {U V : Set (Vec d)} (hUV : U = V) (u : H10Function U) :
    ((hUV ▸ u : H10Function V)).toH1Function.grad = u.toH1Function.grad := by
  subst V
  rfl

/-- The gradient of a domain-cast mean-zero Sobolev function. -/
theorem nfGradCastMeanZero {U V : Set (Vec d)} (hUV : U = V)
    (u : H1MeanZeroFunction U) :
    ((hUV ▸ u : H1MeanZeroFunction V)).toH1Function.grad =
      u.toH1Function.grad := by
  subst V
  rfl

/-- The triadic parent shift identification. -/
theorem twoRadius_translateSet_eq (Q : TriadicCube d) :
    translateSet (triadicCubeShift Q) (openCubeSet (originCube d Q.scale)) =
      openCubeSet Q :=
  (openCubeSet_eq_translateSet_originCube_of_triadicCube Q).symm

/-- Gradient readout of the local Dirichlet piece through the translated
canonical origin solution. -/
theorem twoRadiusLocalDirichletPiece_grad [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : NFSample d) (hh : 0 < h) :
    (twoRadiusLocalDirichletPiece M n h p Q omega hh).grad =
      ((oneStepOriginDirichletSolution M n h p Q.scale
        (translatePotentialSequence (triadicCubeShift Q) omega)
          hh).toH1Function.translate (triadicCubeShift Q)).grad := by
  have hcast := nfGradCastH10 (twoRadius_translateSet_eq Q)
    (oneStepTranslatedDirichletSolution M n h p (triadicCubeShift Q)
      Q.scale omega hh)
  refine hcast.trans ?_
  unfold oneStepTranslatedDirichletSolution
  rw [H10Function.translate_toH1Function]

/-- Gradient readout of the local Neumann piece through the translated
canonical origin solution. -/
theorem twoRadiusLocalNeumannPiece_grad [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (omega : NFSample d) (hh : 0 < h) :
    (twoRadiusLocalNeumannPiece M n h p Q omega hh).grad =
      ((oneStepOriginNeumannSolution M n h p Q.scale
        (translatePotentialSequence (triadicCubeShift Q) omega)
          hh).toH1Function.translate (triadicCubeShift Q)).grad := by
  have hcast := nfGradCastMeanZero (twoRadius_translateSet_eq Q)
    (oneStepTranslatedNeumannSolution M n h p (triadicCubeShift Q)
      Q.scale omega hh)
  refine hcast.trans ?_
  unfold oneStepTranslatedNeumannSolution
  rw [H1MeanZeroFunction.translate_toH1Function]

/-- Samplewise weak Hessian for the persistent Dirichlet member on an
arbitrary triadic parent cube. -/
theorem nonempty_twoRadiusLocalDirichletPiece_parentHessian
    (d : ℕ) [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n h : ℕ) (p : Vec d)
    (Q : TriadicCube d) (hh : 0 < h) :
    Nonempty (∀ omega : NFSample d, HasWeakHessianOn (openCubeSet Q)
      (twoRadiusLocalDirichletPiece M n h p Q omega hh)) := by
  obtain ⟨_C, _hCtop, hpack⟩ :=
    exists_measurable_oneStepCanonicalDirichlet_cellB d
  obtain ⟨V, hV, _hmeas, _hbound⟩ := hpack M n h p Q.scale hh
  refine ⟨fun omega => ?_⟩
  set z : Vec d := triadicCubeShift Q with hz
  let HO : HasWeakHessianOn (openCubeSet (originCube d Q.scale))
      (oneStepOriginDirichletSolution M n h p Q.scale
        (translatePotentialSequence z omega) hh).toH1Function :=
    weakHessianOfCubeVectorW1pFour
      (V (translatePotentialSequence z omega))
      (hV (translatePotentialSequence z omega))
  let HT := HO.translate z
  refine nfWeakHessianOfGradEq ?_
    (nfCastWeakHessian (twoRadius_translateSet_eq Q) HT)
  rw [nfCastH1Domain_grad]
  exact twoRadiusLocalDirichletPiece_grad M n h p Q omega hh

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5NeumannFamily
