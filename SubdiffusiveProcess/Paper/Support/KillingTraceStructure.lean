module

public import SubdiffusiveProcess.Paper.Support.UniformResolventTraceLinearity
public import SubdiffusiveProcess.Paper.car_variational
public import SubdiffusiveProcess.Section9.KilledDualNormCoercivity

@[expose] public section

/-! Supports: mfd_lem_killing.
Actual finite-energy algebra, linear trace and coercivity; no analytic premise.
-/
open MeasureTheory SubdiffusiveProcess SubdiffusiveProcess.Section9
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_mfd_lem_killing_trace_structure
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hsym : ∀ x y, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (G x))
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
    (hsupp : ∀ᵐ x ∂nu, x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)))
    (Ktr Ctr : ℝ)
    (T : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder → Lp ℝ 2 nu)
    (hT : CubeTraceCharacterization hd z hr nu Ktr Ctr T)
    (lift : ∀ u : DomainL2 (centeredCube z r hr), (limitFormEnergy G u).toENNReal ≠ ⊤ →
      CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
    (hlift : ∀ u hu, (lift u hu).val 0 = u)
 :
    let E := fun u : DomainL2 (centeredCube z r hr) => (limitFormEnergy G u).toENNReal
    let A := fun u => if hu : E u ≠ ⊤ then T (lift u hu) else 0
    E 0 = 0 ∧
    (∀ (c : ℝ) (a b : DomainL2 (centeredCube z r hr)),
      E a ≠ ⊤ → E b ≠ ⊤ → E (c • a + b) ≠ ⊤) ∧
    (∀ a b, E a ≠ ⊤ → E b ≠ ⊤ →
      (E (a + b)).toReal + (E (a - b)).toReal = 2 * (E a).toReal + 2 * (E b).toReal) ∧
    (∀ (c : ℝ) a, E a ≠ ⊤ → E (c • a) = ENNReal.ofReal (c ^ 2) * E a) ∧
    (∀ (c : ℝ) a b, E a ≠ ⊤ → E b ≠ ⊤ → A (c • a + b) = c • A a + A b) ∧
    (∀ v, E v ≠ ⊤ → ‖v‖ ^ 2 ≤ max 1 ‖G‖ * (E v).toReal) := by
  classical
  let E := fun u : DomainL2 (centeredCube z r hr) => (limitFormEnergy G u).toENNReal
  let A := fun u : DomainL2 (centeredCube z r hr) => if hu : E u ≠ ⊤ then T (lift u hu) else 0
  have hE0 : E 0 = 0 := (aux_car_variational_energy_algebra z r hr G hsym hpos).1
  obtain ⟨hclosed, hparaG, hscale⟩ := aux_car_variational_energy_properties z r hr G hsym hpos
  refine ⟨hE0, hclosed, ?_, hscale, ?_, ?_⟩
  · intro a b ha hb
    simpa only [E, EReal.toReal_toENNReal (limitFormEnergy_nonneg _ _)] using hparaG a b ha hb
  · intro c a b ha hb
    exact aux_mfd_prop_uniform_resolvent_trace_energy_linear hd z r hr nu (ae_iff.mp hsupp)
      Ktr Ctr T hT E hclosed lift hlift c a b ha hb
  · intro v hv
    exact killed_dual_norm_coercivity _ G v hv

end SubdiffusiveProcess.Paper
