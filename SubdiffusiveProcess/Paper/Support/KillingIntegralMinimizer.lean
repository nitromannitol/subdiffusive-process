module

public import SubdiffusiveProcess.Paper.Support.KillingFormContinuity
public import SubdiffusiveProcess.Paper.Support.KillingTraceObjective
public import SubdiffusiveProcess.Analysis.ClosedSourceLp

@[expose] public section

/-! Supports: mfd_lem_killing.
Continuity of the minimizer with its literal integral objective. The actual
inverse and trace supply the algebra/coercivity data in the application. -/
open MeasureTheory Topology SubdiffusiveProcess SubdiffusiveProcess.Analysis
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

theorem aux_mfd_lem_killing_integral_minimizer_continuous
    {d : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (Q : Set (SpatialCoordinates d)) [CompactSpace (closure Q)]
    (nu : Measure (SpatialCoordinates d)) [IsFiniteMeasure nu]
    (hsupp : ∀ᵐ x ∂nu, x ∈ closure Q)
    (E : V → ℝ≥0∞) (A : V → Lp ℝ 2 nu) (J : V → SpatialCoordinates d → ℝ)
    (hE0 : E 0 = 0)
    (hclosed : ∀ (c : ℝ) (a b : V), E a ≠ ⊤ → E b ≠ ⊤ → E (c • a + b) ≠ ⊤)
    (hpara : ∀ a b, E a ≠ ⊤ → E b ≠ ⊤ →
      (E (a + b)).toReal + (E (a - b)).toReal = 2 * (E a).toReal + 2 * (E b).toReal)
    (hscale : ∀ (c : ℝ) a, E a ≠ ⊤ → E (c • a) = ENNReal.ofReal (c ^ 2) * E a)
    (hAlin : ∀ (c : ℝ) a b, E a ≠ ⊤ → E b ≠ ⊤ → A (c • a + b) = c • A a + A b)
    (C : ℝ) (hC : 0 < C) (hcoer : ∀ v, E v ≠ ⊤ → ‖v‖ ^ 2 ≤ C * (E v).toReal)
    (hJA : ∀ v, E v ≠ ⊤ → J v =ᵐ[nu] (A v : SpatialCoordinates d → ℝ))
    (ustar : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ → V)
    (hdata : ∀ lam, 0 < lam → ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      E (ustar lam f) ≠ ⊤ ∧
      ∀ v, E v ≠ ⊤ →
        (E (ustar lam f)).toReal + lam * (∫ x, J (ustar lam f) x ^ 2 ∂nu) -
            2 * (∫ x, f x * J (ustar lam f) x ∂nu) ≤
          (E v).toReal + lam * (∫ x, J v x ^ 2 ∂nu) - 2 * (∫ x, f x * J v x ∂nu)) :
    Continuous (fun a : Set.Ioi (0 : ℝ) × C(closure Q, ℝ) =>
      ustar a.1.1 (closedSourceExtension Q a.2)) := by
  let X := Set.Ioi (0 : ℝ) × C(closure Q, ℝ)
  let lam : X → ℝ := fun a => a.1.1
  let g : X → Lp ℝ 2 nu := fun a => closedSourceLp Q nu a.2
  let u : X → V := fun a => ustar a.1.1 (closedSourceExtension Q a.2)
  have hkey (a : X) (v : V) (hv : E v ≠ ⊤) :
      (E v).toReal + lam a * (∫ x, J v x ^ 2 ∂nu) -
          2 * (∫ x, closedSourceExtension Q a.2 x * J v x ∂nu) =
        (E v).toReal + lam a * ‖A v‖ ^ 2 - 2 * ⟪g a, A v⟫_ℝ :=
    aux_mfd_lem_killing_trace_objective nu (closedSourceExtension Q a.2)
      (J v) (A v) (hJA v hv) (E v).toReal (lam a)
  have hu (a : X) : E (u a) ≠ ⊤ := (hdata a.1.1 a.1.2 _).1
  have humin : ∀ a v, E v ≠ ⊤ →
      (E (u a)).toReal + lam a * ‖A (u a)‖ ^ 2 - 2 * ⟪g a, A (u a)⟫_ℝ ≤
        (E v).toReal + lam a * ‖A v‖ ^ 2 - 2 * ⟪g a, A v⟫_ℝ := by
    intro a v hv
    rw [← hkey a (u a) (hu a), ← hkey a v hv]
    exact (hdata a.1.1 a.1.2 _).2 v hv
  exact aux_mfd_lem_killing_continuous_form_minimizer
    (X := X) (V := V) (W := Lp ℝ 2 nu)
    E A hE0 hclosed hpara hscale hAlin C hC hcoer lam g u
    (fun a => a.1.2) (continuous_subtype_val.comp continuous_fst)
    ((continuous_closedSourceLp Q nu hsupp).comp continuous_snd) hu humin

end Paper
