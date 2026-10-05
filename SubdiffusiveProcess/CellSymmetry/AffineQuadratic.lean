module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import Mathlib.Tactic
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.TestSubmodule
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import Mathlib.Analysis.Matrix.Normed
public import SubdiffusiveProcess.ResponseMoments.RelativeConcentration
public import SubdiffusiveProcess.Sobolev.CompactResponses
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import Mathlib.Probability.ProductMeasure
public import SubdiffusiveProcess.Sobolev.ReflectionResponses
public import SubdiffusiveProcess.EllipticRegularity.Scaling
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimumCovariance
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import SubdiffusiveProcess.Sobolev.DomainPoincare

@[expose] public section




open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators Pointwise ContDiff Distributions

noncomputable section
namespace SubdiffusiveProcess
namespace CellSymmetry

section
variable {d : ℕ}

theorem cs_quadratic_of_linear {d : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (M : (Fin d → ℝ) → V)
    (hMadd : ∀ p q, M (p + q) = M p + M q)
    (hMsmul : ∀ (r : ℝ) (p : Fin d → ℝ), M (r • p) = r • M p)
    (bil : V → V → ℝ)
    (hbil_add_l : ∀ u v w, bil (u + v) w = bil u w + bil v w)
    (hbil_smul_l : ∀ (r : ℝ) u w, bil (r • u) w = r * bil u w)
    (hbil_add_r : ∀ u v w, bil u (v + w) = bil u v + bil u w)
    (hbil_smul_r : ∀ (r : ℝ) u w, bil u (r • w) = r * bil u w)
    (e : Fin d → ℝ) :
    bil (M e) (M e) =
      ∑ i : Fin d, ∑ j : Fin d, bil (M ((Pi.single i 1 : Fin d → ℝ))) (M ((Pi.single j 1 : Fin d → ℝ))) * e i * e j := by
  classical
  have hM0 : M 0 = 0 := by simpa using hMsmul 0 0
  have hbil0l : ∀ w, bil 0 w = 0 := by
    intro w
    have h := hbil_add_l 0 0 w
    simpa using h
  have hbil0r : ∀ u, bil u 0 = 0 := by
    intro u
    have h := hbil_add_r u 0 0
    simpa using h
  have hMsum : ∀ (s : Finset (Fin d)) (c : Fin d → ℝ),
      M (∑ i ∈ s, c i • (Pi.single i 1 : Fin d → ℝ)) = ∑ i ∈ s, c i • M ((Pi.single i 1 : Fin d → ℝ)) := by
    intro s c
    induction s using Finset.induction with
    | empty => simpa using hM0
    | insert a s' hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, hMadd, hMsmul, ih]
  have hbilsum_l : ∀ (s : Finset (Fin d)) (v : Fin d → V) (w : V),
      bil (∑ i ∈ s, v i) w = ∑ i ∈ s, bil (v i) w := by
    intro s v w
    induction s using Finset.induction with
    | empty => simpa using hbil0l w
    | insert a s' hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, hbil_add_l, ih]
  have hbilsum_r : ∀ (s : Finset (Fin d)) (u : V) (v : Fin d → V),
      bil u (∑ j ∈ s, v j) = ∑ j ∈ s, bil u (v j) := by
    intro s u v
    induction s using Finset.induction with
    | empty => simpa using hbil0r u
    | insert a s' hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, hbil_add_r, ih]
  have he : e = ∑ i : Fin d, e i • Pi.single (M := fun _ : Fin d => ℝ) i 1 := pi_eq_sum_univ' e
  have hMe : M e = ∑ i : Fin d, e i • M ((Pi.single i 1 : Fin d → ℝ)) := by
    conv_lhs => rw [he]
    exact hMsum Finset.univ e
  rw [hMe, hbilsum_l Finset.univ (fun i => e i • M ((Pi.single i 1 : Fin d → ℝ))) (∑ j, e j • M ((Pi.single j 1 : Fin d → ℝ)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hbil_smul_l, hbilsum_r Finset.univ (M ((Pi.single i 1 : Fin d → ℝ))) (fun j => e j • M ((Pi.single j 1 : Fin d → ℝ)))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hbil_smul_r]
  ring

end

section
variable {d : ℕ}
variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
  [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

theorem cs_domainConstantL2_add (c1 c2 : ℝ) :
    domainConstantL2 (Ω := Ω) (c1 + c2) = domainConstantL2 c1 + domainConstantL2 c2 := by
  unfold domainConstantL2
  have hfun : (fun _ : SpatialCoordinates d => c1 + c2) =
      (fun _ : SpatialCoordinates d => c1) + (fun _ : SpatialCoordinates d => c2) := by
    funext x; simp
  rw [MemLp.toLp_congr (memLp_const (c1 + c2)) ((memLp_const c1).add (memLp_const c2))
    (Filter.EventuallyEq.of_eq hfun), MemLp.toLp_add]

theorem cs_domainConstantL2_smul (r c : ℝ) :
    domainConstantL2 (Ω := Ω) (r * c) = r • domainConstantL2 c := by
  unfold domainConstantL2
  have hfun : (fun _ : SpatialCoordinates d => r * c) = r • (fun _ : SpatialCoordinates d => c) := by
    funext x; simp
  rw [MemLp.toLp_congr (memLp_const (r * c)) ((memLp_const c).const_smul r)
    (Filter.EventuallyEq.of_eq hfun), MemLp.toLp_const_smul]

theorem cs_affineL2_add (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (p q : Fin d → ℝ) :
    affineL2 hΩ (p + q) 0 = affineL2 hΩ p 0 + affineL2 hΩ q 0 := by
  unfold affineL2
  have hfun : (fun x => affineSlope (p + q) x + 0) =
      (fun x => affineSlope p x + 0) + (fun x => affineSlope q x + 0) := by
    funext x
    simp only [Pi.add_apply, affineSlope_apply, add_zero]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [MemLp.toLp_congr (affine_memLp hΩ (p + q) 0) ((affine_memLp hΩ p 0).add (affine_memLp hΩ q 0))
    (Filter.EventuallyEq.of_eq hfun), MemLp.toLp_add]

theorem cs_affineL2_smul (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (r : ℝ) (p : Fin d → ℝ) :
    affineL2 hΩ (r • p) 0 = r • affineL2 hΩ p 0 := by
  unfold affineL2
  have hfun : (fun x => affineSlope (r • p) x + 0) = r • (fun x => affineSlope p x + 0) := by
    funext x
    simp only [Pi.smul_apply, affineSlope_apply, add_zero, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [MemLp.toLp_congr (affine_memLp hΩ (r • p) 0) ((affine_memLp hΩ p 0).const_smul r)
    (Filter.EventuallyEq.of_eq hfun), MemLp.toLp_const_smul]

theorem cs_affineSobolev_add
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d))) (p q : Fin d → ℝ) :
    affineSobolev hΩ (p + q) 0 = affineSobolev hΩ p 0 + affineSobolev hΩ q 0 := by
  apply Subtype.ext
  show affineSobolevData hΩ (p + q) 0 =
      (affineSobolev hΩ p 0 : SobolevData Ω) + (affineSobolev hΩ q 0 : SobolevData Ω)
  show affineSobolevData hΩ (p + q) 0 = affineSobolevData hΩ p 0 + affineSobolevData hΩ q 0
  unfold affineSobolevData
  apply Prod.ext
  · exact cs_affineL2_add hΩ p q
  · funext i
    show domainConstantL2 ((p + q) i) = domainConstantL2 (p i) + domainConstantL2 (q i)
    rw [Pi.add_apply]
    exact cs_domainConstantL2_add (p i) (q i)

theorem cs_affineSobolev_smul
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d))) (r : ℝ) (p : Fin d → ℝ) :
    affineSobolev hΩ (r • p) 0 = r • affineSobolev hΩ p 0 := by
  apply Subtype.ext
  show affineSobolevData hΩ (r • p) 0 = r • (affineSobolev hΩ p 0 : SobolevData Ω)
  show affineSobolevData hΩ (r • p) 0 = r • affineSobolevData hΩ p 0
  unfold affineSobolevData
  apply Prod.ext
  · exact cs_affineL2_smul hΩ r p
  · funext i
    show domainConstantL2 (Ω := Ω) ((r • p) i) = r • domainConstantL2 (Ω := Ω) (p i)
    rw [Pi.smul_apply, smul_eq_mul]
    exact cs_domainConstantL2_smul r (p i)

theorem cs_dirichlet_quadratic
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) :
    ∃ A : Fin d → Fin d → ℝ, (∀ i j, A i j = A j i) ∧
      ∀ e : Fin d → ℝ,
        affineDirichletResponse hΩ hP a e = ∑ i : Fin d, ∑ j : Fin d, A i j * e i * e j := by
  set S := killedResponseSpace hP with hSdef
  let Mv : (Fin d → ℝ) → SobolevData Ω :=
    fun p => (dirichletMinimizer S a (affineSobolev hΩ p 0) : SobolevData Ω)
  have hMvadd : ∀ p q, Mv (p + q) = Mv p + Mv q := by
    intro p q
    show (dirichletMinimizer S a (affineSobolev hΩ (p + q) 0) : SobolevData Ω) = _
    rw [cs_affineSobolev_add hΩ, dirichletMinimizer_add]
    rfl
  have hMvsmul : ∀ (r : ℝ) p, Mv (r • p) = r • Mv p := by
    intro r p
    show (dirichletMinimizer S a (affineSobolev hΩ (r • p) 0) : SobolevData Ω) = _
    rw [cs_affineSobolev_smul hΩ, dirichletMinimizer_smul]
    rfl
  have hbil_add_l : ∀ u v w : SobolevData Ω, sobolevCoefficientForm a (u + v) w =
      sobolevCoefficientForm a u w + sobolevCoefficientForm a v w := by
    intro u v w; simp only [map_add, add_apply]
  have hbil_smul_l : ∀ (r : ℝ) (u w : SobolevData Ω),
      sobolevCoefficientForm a (r • u) w = r * sobolevCoefficientForm a u w := by
    intro r u w; simp only [map_smul, smul_apply, smul_eq_mul]
  have hbil_add_r : ∀ u v w : SobolevData Ω, sobolevCoefficientForm a u (v + w) =
      sobolevCoefficientForm a u v + sobolevCoefficientForm a u w := by
    intro u v w; simp only [map_add]
  have hbil_smul_r : ∀ (r : ℝ) (u w : SobolevData Ω),
      sobolevCoefficientForm a u (r • w) = r * sobolevCoefficientForm a u w := by
    intro r u w; simp only [map_smul, smul_eq_mul]
  refine ⟨fun i j => sobolevCoefficientForm a (Mv (Pi.single i 1)) (Mv (Pi.single j 1)),
    fun i j => ?_, fun e => ?_⟩
  · exact sobolevCoefficientForm_symm a _ _
  · have hq := cs_quadratic_of_linear Mv hMvadd hMvsmul
      (fun u v => sobolevCoefficientForm a u v) hbil_add_l hbil_smul_l hbil_add_r hbil_smul_r e
    unfold affineDirichletResponse dirichletResponse
    exact hq

end

end CellSymmetry
end SubdiffusiveProcess
