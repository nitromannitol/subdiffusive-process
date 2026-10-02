import MarkovProcess.Trajectory.Equivariance
import MarkovProcess.Parameterized.ContinuousProcessProperties
import Mathlib.Tactic

/-! # Positive clock transport of the supplied continuous realization's full FDDs -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory ProbabilityTheory MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
open scoped NNReal

namespace SubdiffusiveProcess.Examples
noncomputable section

variable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Multiply the time parameter of an actual semigroup. -/
def clockSemigroup (P : SubMarkovKernelSemigroup E) (c : NNReal) : SubMarkovKernelSemigroup E where
  kernel t := P (c * t)
  measurable_kernel := P.measurable_kernel.comp
    ((measurable_const.mul measurable_fst).prodMk measurable_snd)
  kernel_zero := by rw [mul_zero, P.zero]
  kernel_add s t := by rw [mul_add, P.add]
  isSubMarkovKernel t := P.isSubMarkovKernel _

/-- Push the SAME continuous realization by a deterministic clock. -/
def clockKernel (K : Kernel E (ContinuousPath E)) (c : NNReal) : Kernel E (ContinuousPath E) :=
  K.map (ContinuousPath.rescale (Homeomorph.refl E) c)

/-- Arbitrary ordered finite-time marginals follow from the given finite-set marginals. -/
theorem ordered_fdd_of_fdd (P : SubMarkovKernelSemigroup E) (hP : P.IsConservative)
    (K : Kernel E (ContinuousPath E))
    (hfdd : ∀ I, K.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    {n : ℕ} (times : FiniteOrderedTimes n) :
    K.map (ContinuousPath.finiteEvaluation times) = finiteTimeKernel P times := by
  classical
  let I : Finset NNReal := Finset.univ.map times.toEmbedding
  have hmem (i : Fin n) : times i ∈ I := by
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let j : Fin n ↪o Fin I.card :=
    (OrderEmbedding.ofStrictMono (fun i => (⟨times i, hmem i⟩ : I))
      (fun _ _ h => times.strictMono h)).trans (I.orderIsoOfFin rfl).symm.toOrderEmbedding
  let read : (I → E) → (Fin n → E) := fun w i => w ⟨times i, hmem i⟩
  have hread : Measurable read := measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have hcomp : read ∘ ContinuousPath.finsetEvaluation I =
      ContinuousPath.finiteEvaluation times := rfl
  have horder : read ∘ orderedPathToFiniteSet I = FiniteOrderedTimes.restrictPath j := rfl
  have htimes : (finiteSetTimes I).restrict j = times := by
    apply DFunLike.ext
    intro i
    change (((I.orderIsoOfFin rfl) ((I.orderIsoOfFin rfl).symm ⟨times i, hmem i⟩) : I) : NNReal) = times i
    rw [OrderIso.apply_symm_apply]
  rw [← hcomp, Kernel.map_comp_right _ (ContinuousPath.measurable_finsetEvaluation I) hread,
    hfdd, finiteSetKernel_eq_map, ← Kernel.map_comp_right _ (measurable_orderedPathToFiniteSet I) hread,
    horder, hP.finiteTimeKernel_map_restrictPath P (finiteSetTimes I) j, htimes]

/-- Full original-start FDDs are transported to the clocked realization, not merely a.e. starts. -/
theorem clockKernel_fdd (P : SubMarkovKernelSemigroup E) (hP : P.IsConservative)
    (K : Kernel E (ContinuousPath E))
    (hfdd : ∀ I, K.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (c : NNReal) (hc : 0 < c) :
    ∀ I, (clockKernel K c).map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel (clockSemigroup P c) I := by
  intro I
  have hconj : IsRescaledConjugate P (clockSemigroup P c) (Homeomorph.refl E) c := by
    intro t x
    change P (c * t) x = Measure.map id (P (c * t) x)
    rw [Measure.map_id]
  have hcomp : ContinuousPath.finsetEvaluation I ∘ ContinuousPath.rescale (Homeomorph.refl E) c =
      orderedPathToFiniteSet I ∘ ContinuousPath.finiteEvaluation ((finiteSetTimes I).rescale c hc) := by
    funext w t
    change w (c * (t : NNReal)) = w (c * finiteSetTimes I ((I.orderIsoOfFin rfl).symm t))
    rw [finiteSetTimes_orderIsoOfFin_symm_apply]
  rw [clockKernel, ← Kernel.map_comp_right _ (ContinuousPath.measurable_rescale _ _)
    (ContinuousPath.measurable_finsetEvaluation I), hcomp,
    Kernel.map_comp_right _ (ContinuousPath.measurable_finiteEvaluation _) (measurable_orderedPathToFiniteSet I),
    ordered_fdd_of_fdd P hP K hfdd, hconj.finiteSetKernel_eq hc hP]
  simp only [Homeomorph.refl_symm, Homeomorph.refl_apply, Function.comp_def, Kernel.comap_id]
  congr 1

end
end SubdiffusiveProcess.Examples
