module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.WeakSequentialCompactness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.MassiveSolver
public import Homogenization.Sobolev.Truncation.WeakGradientLimit

@[expose] public section

/-!
# Strong-value/weak-gradient closure of the local `H¹` graph

The cube exhaustion supplies strong local `L²` convergence of the values but
only weak compactness of the gradients.  This file packages the corresponding
closed-graph argument for `H1Function`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory Topology
open Homogenization

noncomputable section

variable {d : ℕ} {W : Set (Vec d)}

/-- A sequence of `H¹` functions whose values converge strongly in local
`L²` and whose gradients are norm bounded has a subsequence with an `H¹`
limit.  The gradient convergence is weak against every vector in the Hilbert
`L²` carrier. -/
theorem exists_h1Function_of_tendsto_value_of_gradient_norm_le
    (w : ℕ → H1Function W) {u : Vec d → ℝ} (hu : MemL2On W u)
    (hvalue : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ (w n).toFun x - u x) 2 (volumeMeasureOn W))
      atTop (𝓝 0))
    (C : ℝ) (hgradient : ∀ n, ‖(w n).gradToHilbertVectorL2‖ ≤ C) :
    ∃ v : H1Function W, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      v.toFun =ᵐ[volumeMeasureOn W] u ∧
      Tendsto (fun n ↦ (w (phi n)).toScalarL2) atTop (𝓝 v.toScalarL2) ∧
      ∀ z : HilbertVectorL2 W,
        Tendsto (fun n ↦ inner ℝ (w (phi n)).gradToHilbertVectorL2 z) atTop
          (𝓝 (inner ℝ v.gradToHilbertVectorL2 z)) := by
  obtain ⟨G, phi, hphi, hG⟩ :=
    exists_subseq_tendsto_inner_hilbertVectorL2_of_norm_le W
      (fun n ↦ (w n).gradToHilbertVectorL2) C hgradient
  have hvalueL2 : Tendsto (fun n ↦ (w n).toScalarL2) atTop
      (𝓝 (toScalarL2 hu)) :=
    tendsto_toScalarL2_of_tendsto_eLpNorm (fun n ↦ (w n).memL2) hu hvalue
  have hvalueSub : Tendsto (fun n ↦ (w (phi n)).toScalarL2) atTop
      (𝓝 (toScalarL2 hu)) := by
    simpa only [Function.comp_def] using! hvalueL2.comp hphi.tendsto_atTop
  have hgraph : (toScalarL2 hu, G) ∈ h1GraphClosedSubmodule (U := W) := by
    rw [mem_h1GraphClosedSubmodule_iff]
    intro i psi
    let L : ScalarL2 W × HilbertVectorL2 W →L[ℝ] ℝ :=
      h1WeakConstraintCLM (U := W) i psi
    let Lvalue : ScalarL2 W →L[ℝ] ℝ :=
      L.comp (ContinuousLinearMap.inl ℝ (ScalarL2 W) (HilbertVectorL2 W))
    let Lgradient : HilbertVectorL2 W →L[ℝ] ℝ :=
      L.comp (ContinuousLinearMap.inr ℝ (ScalarL2 W) (HilbertVectorL2 W))
    let z : HilbertVectorL2 W :=
      (InnerProductSpace.toDual ℝ (HilbertVectorL2 W)).symm Lgradient
    have hinner (H : HilbertVectorL2 W) :
        inner ℝ H z = Lgradient H := by
      calc
        inner ℝ H z = inner ℝ z H := (real_inner_comm H z).symm
        _ = Lgradient H := InnerProductSpace.toDual_symm_apply
    have hvaluePair : Tendsto
        (fun n ↦ Lvalue (w (phi n)).toScalarL2) atTop
        (𝓝 (Lvalue (toScalarL2 hu))) :=
      Lvalue.continuous.continuousAt.tendsto.comp hvalueSub
    have hgradientPair : Tendsto
        (fun n ↦ Lgradient (w (phi n)).gradToHilbertVectorL2) atTop
        (𝓝 (Lgradient G)) := by
      simpa only [hinner] using hG z
    have hpair_eq (F : ScalarL2 W) (H : HilbertVectorL2 W) :
        L (F, H) = L (F, 0) + L (0, H) := by
      rw [show (F, H) = (F, 0) + (0, H) from
        Prod.ext (add_zero F).symm (zero_add H).symm, map_add]
    have hconstraint : Tendsto
        (fun n ↦ L ((w (phi n)).toScalarL2,
          (w (phi n)).gradToHilbertVectorL2)) atTop
        (𝓝 (L (toScalarL2 hu, G))) := by
      have hsum := hvaluePair.add hgradientPair
      have hsource :
          (fun n ↦ L ((w (phi n)).toScalarL2,
            (w (phi n)).gradToHilbertVectorL2)) =
          fun n ↦ L ((w (phi n)).toScalarL2, 0) +
            L (0, (w (phi n)).gradToHilbertVectorL2) := by
        funext n
        exact hpair_eq _ _
      rw [hsource, hpair_eq]
      simpa only [Lvalue, Lgradient, ContinuousLinearMap.coe_comp',
        Function.comp_apply, ContinuousLinearMap.inl_apply,
        ContinuousLinearMap.inr_apply] using hsum
    have hzero : (fun n ↦ L ((w (phi n)).toScalarL2,
        (w (phi n)).gradToHilbertVectorL2)) = fun _ ↦ 0 := by
      funext n
      exact (mem_h1GraphClosedSubmodule_iff (U := W) _).1
        (h1_pair_mem_h1GraphClosedSubmodule (U := W) (w (phi n))) i psi
    have hconstant : Tendsto
        (fun n ↦ L ((w (phi n)).toScalarL2,
          (w (phi n)).gradToHilbertVectorL2)) atTop (𝓝 0) := by
      rw [hzero]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hconstraint hconstant
  let v := toH1FunctionOfMemH1Graph (U := W) (toScalarL2 hu, G) hgraph
  refine ⟨v, phi, hphi, ?_, ?_, ?_⟩
  · have hv := v.coeFn_toScalarL2
    have huCoe := coeFn_toScalarL2 hu
    filter_upwards [hv, huCoe] with x hvx hux
    rw [← hvx, toH1FunctionOfMemH1Graph_toScalarL2, hux]
  · simpa only [v, toH1FunctionOfMemH1Graph_toScalarL2] using hvalueSub
  · intro z'
    simpa only [v, toH1FunctionOfMemH1Graph_gradToHilbertVectorL2] using hG z'

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
