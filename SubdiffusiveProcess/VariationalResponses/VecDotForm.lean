module

public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology Distributions ContDiff

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}

/-- **Adapter B, the integral identity.**  The project's coefficient form on the
Sobolev data of two native `H1Function`s is GMC's divergence-form integrand
`∫ vecDot (a • ∇u) ∇v`, which is the integrand of `IsDivFormWeakSolutionOn`.
The coordinatewise integrability is a side condition, discharged by the caller
from the `L²` gradients and the `L^∞` coefficient. -/
theorem sobolevCoefficientForm_eq_integral_vecDot
    (a : PositiveCoefficient Ω)
    (u v : H1Function (Ω : Set (SpatialCoordinates d)))
    (hint : ∀ i : Fin d, IntegrableOn
      (fun x => a.val x * (u.grad x i * v.grad x i))
      (Ω : Set (SpatialCoordinates d)) volume) :
    sobolevCoefficientForm a (sobolevDataOfH1 u) (sobolevDataOfH1 v) =
      ∫ x in (Ω : Set (SpatialCoordinates d)),
        vecDot (a.val x • u.grad x) (v.grad x) ∂volume := by
  have hform : sobolevCoefficientForm a (sobolevDataOfH1 u) (sobolevDataOfH1 v) =
      ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        a.val x * (((sobolevDataOfH1 u).2 i) x * ((sobolevDataOfH1 v).2 i) x) := by
    exact weightedGradientForm_apply a.val _ _
  rw [hform]
  have hcoord : ∀ i : Fin d,
      (∫ x in (Ω : Set (SpatialCoordinates d)),
        a.val x * (((sobolevDataOfH1 u).2 i) x * ((sobolevDataOfH1 v).2 i) x)) =
      ∫ x in (Ω : Set (SpatialCoordinates d)),
        a.val x * (u.grad x i * v.grad x i) := by
    intro i
    refine integral_congr_ae ?_
    filter_upwards [sobolevDataOfH1_snd_coeFn u i, sobolevDataOfH1_snd_coeFn v i]
      with x hxu hxv
    rw [hxu, hxv]
  rw [Finset.sum_congr rfl (fun i _ => hcoord i)]
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [vecDot, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Adapter B, assembled.**  A weak equation stated with the project's
`sobolevCoefficientForm` against the native Sobolev data of every `H¹₀` test is
GMC's `IsDivFormWeakSolutionOn`, the hypothesis of
`exists_physicalBallRepresentative_smallContrast_inhomogeneous`.  Nothing is lost
in the test class: `IsDivFormWeakSolutionOn` quantifies over `H10Function`, and
`sobolevDataOfH1_mem_weak` places each such test in `weakSobolevGraph`, over
which `lane2_oddExtension_weak_equation` already quantifies. -/
theorem isDivFormWeakSolutionOn_of_weak_equation
    (a : PositiveCoefficient Ω) (u : H1Function (Ω : Set (SpatialCoordinates d)))
    (g : SpatialCoordinates d → SpatialCoordinates d)
    (hint : ∀ (v : H1Function (Ω : Set (SpatialCoordinates d))) (i : Fin d),
      IntegrableOn (fun x => a.val x * (u.grad x i * v.grad x i))
        (Ω : Set (SpatialCoordinates d)) volume)
    (heq : ∀ φ : H10Function (Ω : Set (SpatialCoordinates d)),
      sobolevCoefficientForm a (sobolevDataOfH1 u)
          (sobolevDataOfH1 φ.toH1Function) =
        -∫ x in (Ω : Set (SpatialCoordinates d)),
          vecDot (g x) (φ.toH1Function.grad x) ∂volume) :
    IsDivFormWeakSolutionOn a.val (Ω : Set (SpatialCoordinates d)) u g := by
  intro φ
  rw [← sobolevCoefficientForm_eq_integral_vecDot a u φ.toH1Function
    (fun i => hint φ.toH1Function i)]
  exact heq φ

end SubdiffusiveProcess
