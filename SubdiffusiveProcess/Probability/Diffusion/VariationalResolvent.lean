module

public import SubdiffusiveProcess.Probability.Diffusion.SobolevClosure
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.MassiveSolver
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab (scalarCoeffField isEllipticFieldOn_scalarCoeffField_const)
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ENNReal NNReal Topology RealInnerProductSpace

noncomputable section

namespace SubdiffusiveProcess.Probability.Diffusion

variable {d : ℕ}

/-- Massive variational solvability on every open set, with the stated uniform
coefficient bounds. Boundedness and boundary smoothness are not needed. -/
theorem exists_isMassiveDirichletSolutionOn_of_isOpen
    {W : Set (Vec d)} (hW : IsOpen W)
    {c rho : Vec d → ℝ} {mu lam Lam rhoMin rhoMax : ℝ}
    (hmu : 0 < mu) (hrhoMin : 0 < rhoMin) (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField c))
    (hrhoMeas : AEStronglyMeasurable rho (volumeMeasureOn W))
    (hrhoLow : ∀ x ∈ W, rhoMin ≤ rho x)
    (hrhoBdd : ∀ᵐ x ∂(volumeMeasureOn W), |rho x| ≤ rhoMax)
    (hD : H1Function W) {f : Vec d → ℝ} (hf : MemL2On W f) :
    ∃ u : H1Function W,
      IsMassiveDirichletSolutionOn c rho mu W u hD f := by
  classical
  have hmemW : ∀ᵐ x ∂(volumeMeasureOn W), x ∈ W := by
    exact (ae_restrict_iff' hW.measurableSet).2
      (Filter.Eventually.of_forall fun _ hx ↦ hx)
  have hrhoLowAE : ∀ᵐ x ∂(volumeMeasureOn W), rhoMin ≤ rho x := by
    filter_upwards [hmemW] with x hx
    exact hrhoLow x hx
  let B := MassiveH1Hilbert.massiveBilin (mu := mu) hEll hrhoMeas hrhoBdd
  let K := MassiveH1Hilbert.zeroTraceSubmodule (W := W)
  let ell := MassiveH1Hilbert.forcingFunctional hrhoMeas hrhoBdd hf
  have hB : IsCoercive B := by
    exact MassiveH1Hilbert.isCoercive_massiveBilin
      hmu hrhoMin hlam hEll hrhoMeas hrhoBdd hrhoLowAE
  let q := linearQuadraticResponseMaximizer B hB ell
  let x := MassiveH1Hilbert.ofH1Function hD - q
  let m := affineMinimizerMap K B hB x
  let z := m + q
  have hzFirst (phi : H10Function W) :
      B z (MassiveH1Hilbert.ofH1Function phi.toH1Function) =
        ell (MassiveH1Hilbert.ofH1Function phi.toH1Function) := by
    let wp : K.toSubmodule :=
      ⟨MassiveH1Hilbert.ofH1Function phi.toH1Function,
        MassiveH1Hilbert.ofH10Function_mem_zeroTraceSubmodule phi⟩
    change B z (wp : MassiveH1Hilbert.Space (W := W)) =
      ell (wp : MassiveH1Hilbert.Space (W := W))
    calc
      B z (wp : MassiveH1Hilbert.Space (W := W)) = B m wp + B q wp := by
        rw [show z = m + q from rfl, B.map_add₂]
      _ = 0 + ell wp := by
        rw [show m = affineMinimizerMap K B hB x from rfl,
          affineMinimizerMap_firstVariation K B hB x wp,
          show q = linearQuadraticResponseMaximizer B hB ell from rfl,
          linearQuadraticResponseMaximizer_firstVariation]
      _ = ell wp := zero_add _
  have hzMem :
      z - MassiveH1Hilbert.ofH1Function hD ∈ K := by
    have hm := sub_affineMinimizerMap_apply_mem K B hB x
    convert hm using 1
    all_goals
      dsimp [z, m, x]
      abel
  have hzPair :
      (MassiveH1Hilbert.value z - hD.toScalarL2,
          MassiveH1Hilbert.gradient z - hD.gradToHilbertVectorL2) ∈
        h10GraphClosedSubmodule W :=
    (MassiveH1Hilbert.sub_ofH1Function_mem_zeroTraceSubmodule_iff z hD).1 hzMem
  obtain ⟨w, hwVal, hwGrad⟩ :=
    exists_h10Function_of_mem_h10GraphClosedSubmodule_of_isOpen hW hzPair
  let u : H1Function W := hD + w.toH1Function
  have huGraph : MassiveH1Hilbert.ofH1Function u = z := by
    apply Subtype.ext
    apply (MassiveH1Hilbert.ambientEquiv (W := W)).injective
    change (u.toScalarL2, u.gradToHilbertVectorL2) =
      (MassiveH1Hilbert.value z, MassiveH1Hilbert.gradient z)
    apply Prod.ext
    · rw [show u = hD + w.toH1Function from rfl,
        H1Function.toScalarL2_add, hwVal]
      simp only
      abel
    · rw [show u = hD + w.toH1Function from rfl,
        H1Function.gradToHilbertVectorL2_add, hwGrad]
      simp only
      abel
  refine ⟨u, ?_, ?_⟩
  · exact ⟨w, fun _ ↦ rfl, fun _ ↦ rfl⟩
  · intro phi
    have hfirst :
        B (MassiveH1Hilbert.ofH1Function u)
            (MassiveH1Hilbert.ofH1Function phi.toH1Function) =
          ell (MassiveH1Hilbert.ofH1Function phi.toH1Function) := by
      calc
        B (MassiveH1Hilbert.ofH1Function u)
            (MassiveH1Hilbert.ofH1Function phi.toH1Function) =
            B z (MassiveH1Hilbert.ofH1Function phi.toH1Function) := by
          exact congrArg
            (fun y ↦ B y (MassiveH1Hilbert.ofH1Function phi.toH1Function))
            huGraph
        _ = ell (MassiveH1Hilbert.ofH1Function phi.toH1Function) := hzFirst phi
    calc
      mu * ∫ x in W, rho x * u.toFun x * phi.toH1Function.toFun x ∂volume +
          ∫ x in W, vecDot (c x • u.grad x) (phi.toH1Function.grad x) ∂volume =
          MassiveH1Hilbert.massiveBilin (mu := mu) hEll hrhoMeas hrhoBdd
            (MassiveH1Hilbert.ofH1Function u)
            (MassiveH1Hilbert.ofH1Function phi.toH1Function) :=
        (MassiveH1Hilbert.massiveBilin_apply_ofH1Function
          hEll hrhoMeas hrhoBdd u phi.toH1Function).symm
      _ = B (MassiveH1Hilbert.ofH1Function u)
            (MassiveH1Hilbert.ofH1Function phi.toH1Function) := rfl
      _ = ell (MassiveH1Hilbert.ofH1Function phi.toH1Function) := hfirst
      _ = MassiveH1Hilbert.forcingFunctional hrhoMeas hrhoBdd hf
            (MassiveH1Hilbert.ofH1Function phi.toH1Function) := rfl
      _ = ∫ x in W, rho x * f x * phi.toH1Function.toFun x ∂volume :=
        MassiveH1Hilbert.forcingFunctional_apply_ofH1Function
          hrhoMeas hrhoBdd hf phi.toH1Function


/-- The normalized variational Dirichlet resolvent exists for every open set
and every `L²` datum, including nonsmooth and disconnected domains. -/
theorem exists_variationalResolvent {U : Set (Vec d)} (hU : IsOpen U)
    {s : ℝ} (hs : 0 < s) {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U)) :
    ∃ u : H10Function U,
      IsMassiveWeakSolutionOn (fun _ => 1) (fun _ => 1) s⁻¹ U u.toH1Function
        (fun x => s⁻¹ * f x) := by
  have hEll := isEllipticFieldOn_scalarCoeffField_const hU.measurableSet one_pos
  obtain ⟨v, ⟨u, huf, hug⟩, hsol⟩ :=
    exists_isMassiveDirichletSolutionOn_of_isOpen hU (inv_pos.mpr hs) one_pos one_pos hEll
      aestronglyMeasurable_const (fun _ _ => le_rfl)
      (Eventually.of_forall fun _ => (show |(1 : ℝ)| ≤ 1 by norm_num))
      (0 : H1Function U) (hf.const_mul s⁻¹)
  have hfun : v.toFun = u.toH1Function.toFun := by
    funext x
    simpa only [H1Function.zero_toFun, Pi.zero_apply, zero_add] using huf x
  have hgrad : v.grad = u.toH1Function.grad := by
    funext x
    simpa only [H1Function.zero_grad, Pi.zero_apply, zero_add] using hug x
  refine ⟨u, ?_⟩
  intro φ
  simpa only [hfun, hgrad] using hsol φ

/-- The canonical variational resolvent, chosen from the proved existence theorem.
It has no probabilistic premise. -/
def variationalResolvent {U : Set (Vec d)} (hU : IsOpen U)
    {s : ℝ} (hs : 0 < s) {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U)) :
    H10Function U :=
  Classical.choose (exists_variationalResolvent hU hs hf)

/-- The chosen representative satisfies the exact full-Laplacian normalization. -/
theorem variationalResolvent_spec {U : Set (Vec d)} (hU : IsOpen U)
    {s : ℝ} (hs : 0 < s) {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U)) :
    IsMassiveWeakSolutionOn (fun _ => 1) (fun _ => 1) s⁻¹ U
      (variationalResolvent hU hs hf).toH1Function (fun x => s⁻¹ * f x) :=
  Classical.choose_spec (exists_variationalResolvent hU hs hf)

/-- The variational construction is independent of its choice of representative:
every zero-boundary solution agrees in value and gradient almost everywhere. -/
theorem variationalResolvent_unique {U : Set (Vec d)} (hU : IsOpen U)
    {s : ℝ} (hs : 0 < s) {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict U))
    (u : H10Function U)
    (hu : IsMassiveWeakSolutionOn (fun _ => 1) (fun _ => 1) s⁻¹ U u.toH1Function
      (fun x => s⁻¹ * f x)) :
    u.toH1Function.toFun =ᵐ[volume.restrict U]
        (variationalResolvent hU hs hf).toH1Function.toFun ∧
      u.toH1Function.grad =ᵐ[volume.restrict U]
        (variationalResolvent hU hs hf).toH1Function.grad := by
  have htrace (v : H10Function U) :
      SubdiffusiveProcess.CoarseGrainingVocab.HasZeroTraceDifferenceOn U v.toH1Function 0 := by
    refine ⟨v, fun _ => ?_, fun _ => ?_⟩ <;>
      simp only [H1Function.zero_toFun, H1Function.zero_grad, Pi.zero_apply, zero_add]
  exact ae_eq_of_isMassiveDirichletSolutionOn hU.measurableSet (inv_pos.mpr hs) one_pos
    (isEllipticFieldOn_scalarCoeffField_const hU.measurableSet one_pos)
    one_pos (fun _ _ => le_rfl) aestronglyMeasurable_const (fun _ _ => le_rfl)
    (Eventually.of_forall fun _ => (show |(1 : ℝ)| ≤ 1 by norm_num))
    ⟨htrace u, hu⟩ ⟨htrace _, variationalResolvent_spec hU hs hf⟩

end SubdiffusiveProcess.Probability.Diffusion
