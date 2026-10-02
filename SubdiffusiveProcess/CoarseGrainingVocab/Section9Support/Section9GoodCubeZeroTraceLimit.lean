import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.MassiveZeroMassLimit
import Mathlib.Analysis.LocallyConvex.Separation




set_option autoImplicit false
open Filter MeasureTheory Topology Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped RealInnerProductSpace
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A closed subspace retains a limit with strong values and weak gradients. -/
theorem goodCube_mem_closedSubmodule_of_tendsto_value_of_tendsto_inner_gradient
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : ClosedSubmodule ℝ (E × H)) (x : ℕ → E) (g : ℕ → H)
    (v : E) (G : H) (hmem : ∀ n, (x n, g n) ∈ K)
    (hv : Tendsto x atTop (𝓝 v))
    (hG : ∀ z : H, Tendsto (fun n => inner ℝ (g n) z) atTop (𝓝 (inner ℝ G z))) :
    (v, G) ∈ K := by
  by_contra hnot
  obtain ⟨L, a, hLa, haL⟩ := geometric_hahn_banach_closed_point
    K.toSubmodule.convex K.isClosed hnot
  let Lv : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E H)
  let Lg : H →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inr ℝ E H)
  let z : H := (InnerProductSpace.toDual ℝ H).symm Lg
  have hz (y : H) : inner ℝ y z = Lg y := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hv' : Tendsto (fun n => Lv (x n)) atTop (𝓝 (Lv v)) :=
    Lv.continuous.continuousAt.tendsto.comp hv
  have hg' : Tendsto (fun n => Lg (g n)) atTop (𝓝 (Lg G)) := by
    simpa only [hz] using hG z
  have hsplit (b : E) (c : H) : L (b,c) = Lv b + Lg c := by
    change L (b,c) = L (b,0) + L (0,c)
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  have hlim : Tendsto (fun n => L (x n,g n)) atTop (𝓝 (L (v,G))) := by
    simp only [hsplit]
    exact hv'.add hg'
  have hbound : L (v,G) ≤ a := le_of_tendsto hlim
    (Filter.Eventually.of_forall fun n => (hLa _ (hmem n)).le)
  exact haL.not_ge hbound

/-- The strong-value, bounded-gradient subsequence retains zero trace. -/
theorem goodCube_exists_h10_of_tendsto_value_of_gradient_norm_le
    {d : ℕ} [NeZero d] {W : Set (Vec d)} (hW : IsOpenBoundedConvexDomain W)
    (w : ℕ → H10Function W) {u : Vec d → ℝ} (hu : MemL2On W u)
    (hvalue : Tendsto
      (fun n => eLpNorm (fun x => (w n).toH1Function.toFun x - u x) 2 (volumeMeasureOn W))
      atTop (𝓝 0))
    (C : ℝ) (hgradient : ∀ n, ‖(w n).toH1Function.gradToHilbertVectorL2‖ ≤ C) :
    ∃ v : H10Function W, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      v.toH1Function.toFun =ᵐ[volumeMeasureOn W] u ∧
      Tendsto (fun n => (w (phi n)).toH1Function.toScalarL2) atTop
        (𝓝 v.toH1Function.toScalarL2) ∧
      ∀ z : HilbertVectorL2 W,
        Tendsto (fun n => inner ℝ (w (phi n)).toH1Function.gradToHilbertVectorL2 z) atTop
          (𝓝 (inner ℝ v.toH1Function.gradToHilbertVectorL2 z)) := by
  obtain ⟨G, phi, hphi, hG⟩ :=
    exists_subseq_tendsto_inner_hilbertVectorL2_of_norm_le W
      (fun n ↦ (w n).toH1Function.gradToHilbertVectorL2) C hgradient
  have hvalueL2 : Tendsto (fun n ↦ (w n).toH1Function.toScalarL2) atTop
      (𝓝 (toScalarL2 hu)) :=
    tendsto_toScalarL2_of_tendsto_eLpNorm (fun n ↦ (w n).toH1Function.memL2) hu hvalue
  have hvalueSub : Tendsto (fun n ↦ (w (phi n)).toH1Function.toScalarL2) atTop
      (𝓝 (toScalarL2 hu)) := by
    simpa only [Function.comp_apply] using hvalueL2.comp hphi.tendsto_atTop
  have hmem : ∀ n, ((w n).toH1Function.toScalarL2,
      (w n).toH1Function.gradToHilbertVectorL2) ∈ h10GraphClosedSubmodule W := by
    intro n
    exact Submodule.le_topologicalClosure (h10GraphSubmodule W) (h10_pair_mem_h10GraphSubmodule (w n))
  obtain ⟨v, hval, hgrad⟩ :=
    exists_h10Function_of_mem_h10GraphClosedSubmodule hW
      (goodCube_mem_closedSubmodule_of_tendsto_value_of_tendsto_inner_gradient
        (h10GraphClosedSubmodule W)
        (fun n ↦ (w (phi n)).toH1Function.toScalarL2)
        (fun n ↦ (w (phi n)).toH1Function.gradToHilbertVectorL2)
        (toScalarL2 hu) G (fun n => hmem (phi n)) hvalueSub hG)
  have hval' : v.toH1Function.toScalarL2 = toScalarL2 hu := by
    exact hval
  have hgrad' : v.toH1Function.gradToHilbertVectorL2 = G := by
    exact hgrad
  refine ⟨v, phi, hphi, ?_, ?_, ?_⟩
  · have hv := H1Function.coeFn_toScalarL2 v.toH1Function
    have huCoe := coeFn_toScalarL2 hu
    filter_upwards [hv, huCoe] with x hvx hux
    rw [← hvx, hval', hux]
  · rw [hval']
    exact hvalueSub
  · intro z
    rw [hgrad']
    exact hG z

/-- Bounded zero-trace massive solutions converge to a zero-trace Poisson solution. -/
theorem goodCube_exists_h10_zero_mass_of_bounded_pointwise_limit
    {d : ℕ} [NeZero d] {W : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn W)]
    (hW : IsOpenBoundedConvexDomain W)
    {c rho : Vec d → ℝ} {lam Lam rhoMax C Cgrad : ℝ} {mu : ℕ → ℝ}
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    {f u : Vec d → ℝ} (hf : MemL2On W f)
    (w : ℕ → H10Function W)
    (hbound : ∀ n, ∀ᵐ x ∂(volumeMeasureOn W), |(w n).toH1Function.toFun x| ≤ C)
    (hpoint : ∀ᵐ x ∂(volumeMeasureOn W),
      Tendsto (fun n => (w n).toH1Function.toFun x) atTop (𝓝 (u x)))
    (hgradient : ∀ n, ‖(w n).toH1Function.gradToHilbertVectorL2‖ ≤ Cgrad)
    (hmu : Tendsto mu atTop (𝓝 0))
    (hw : ∀ n, IsMassiveWeakSolutionOn c rho (mu n) W (w n).toH1Function f) :
    ∃ v : H10Function W,
      v.toH1Function.toFun =ᵐ[volumeMeasureOn W] u ∧
        IsMassiveWeakSolutionOn c rho 0 W v.toH1Function f := by
  have hwMeas : ∀ n, AEStronglyMeasurable (w n).toH1Function.toFun
      (volumeMeasureOn W) := fun n ↦ (w n).toH1Function.memL2.1
  have huMeas : AEStronglyMeasurable u (volumeMeasureOn W) :=
    aestronglyMeasurable_of_tendsto_ae atTop hwMeas hpoint
  have huBound : ∀ᵐ x ∂(volumeMeasureOn W), ‖u x‖ ≤ C := by
    filter_upwards [hpoint, ae_all_iff.2 hbound] with x hx hxb
    have hmem : u x ∈ Set.Icc (-C) C := by
      apply isClosed_Icc.mem_of_tendsto hx
      exact Filter.Eventually.of_forall fun n ↦ (abs_le.mp (hxb n))
    simpa only [Real.norm_eq_abs] using (abs_le.mpr hmem)
  have hu : MemL2On W u := MemLp.of_bound huMeas C huBound
  have hvalue : Tendsto
      (fun n ↦ eLpNorm (fun x ↦ (w n).toH1Function.toFun x - u x) 2
        (volumeMeasureOn W)) atTop (𝓝 0) :=
    tendsto_eLpNorm_two_of_tendsto_ae_of_dominated hwMeas hu
      (memLp_const C) hbound hpoint
  obtain ⟨v, phi, hphi, hvu, hvalueSub, hgradientSub⟩ :=
    goodCube_exists_h10_of_tendsto_value_of_gradient_norm_le hW w hu hvalue
      Cgrad hgradient
  refine ⟨v, hvu, ?_⟩
  exact isMassiveWeakSolutionOn_zero_of_tendsto_value_of_tendsto_inner_gradient
    hEll hrhoMeas hrhoBdd hf (fun n ↦ (w n).toH1Function) v.toH1Function phi
    (by simpa only [Function.comp_def] using hmu.comp hphi.tendsto_atTop)
    hvalueSub hgradientSub hw

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
