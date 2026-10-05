module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.GMCResolventInterface
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumRepresentative
public import Mathlib.Tactic

@[expose] public section

/-! # Positive constant clock normalization of a C₀ resolvent datum -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory MarkovProcess MarkovProcess.Semigroup Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open scoped ZeroAtInfty

namespace SubdiffusiveProcess.Examples
noncomputable section

/-- The shift of the original generator corresponding to a normalized shift. -/
def clockShift (k : ℝ) (hk : 0 < k) (mu : PositiveShift) : PositiveShift :=
  ⟨k * mu, mul_pos hk mu.property⟩

/-- If the old generator is `k L`, this is the datum of `L` on the same state space. -/
def clockResolvent {E : Type*} [TopologicalSpace E]
    (D : C0ResolventDatum E) (k : ℝ) (hk : 0 < k) : C0ResolventDatum E where
  solution mu f := k • D.solution (clockShift k hk mu) f
  solution_add mu f g := by
    rw [D.solution_add]
    ext x
    change k * (_ + _) = k * _ + k * _
    ring
  solution_smul mu c f := by
    rw [D.solution_smul]
    ext x
    change k * (c * _) = c * (k * _)
    ring
  solution_nonneg mu f hf x := mul_nonneg hk.le (D.solution_nonneg _ f hf x)
  norm_solution_le mu f := by
    rw [norm_smul, Real.norm_of_nonneg hk.le]
    calc
      k * ‖D.solution (clockShift k hk mu) f‖ ≤
          k * ((k * (mu : ℝ))⁻¹ * ‖f‖) :=
        mul_le_mul_of_nonneg_left (D.norm_solution_le _ f) hk.le
      _ = (mu : ℝ)⁻¹ * ‖f‖ := by rw [mul_inv_rev]; field_simp
  solution_sub_solution mu nu f := by
    rw [D.solution_smul]
    ext x
    have h := congrArg (fun g : C₀(E, ℝ) => g x)
      (D.solution_sub_solution (clockShift k hk mu) (clockShift k hk nu) f)
    change D.solution (clockShift k hk mu) f x - D.solution (clockShift k hk nu) f x =
      (k * (nu : ℝ) - k * (mu : ℝ)) *
        D.solution (clockShift k hk mu) (D.solution (clockShift k hk nu) f) x at h
    change k * D.solution (clockShift k hk mu) f x - k * D.solution (clockShift k hk nu) f x =
      ((nu : ℝ) - (mu : ℝ)) * (k * (k *
        D.solution (clockShift k hk mu) (D.solution (clockShift k hk nu) f) x))
    linear_combination k * h


@[simp] theorem clockResolvent_solution {E : Type*} [TopologicalSpace E]
    (D : C0ResolventDatum E) (k : ℝ) (hk : 0 < k) (mu : PositiveShift) (f : C₀(E, ℝ)) :
    (clockResolvent D k hk).solution mu f = k • D.solution (clockShift k hk mu) f := rfl

/-- Clock normalization retains the actual dense range, not an added density hypothesis. -/
theorem clockResolvent_denseRange {E : Type*} [TopologicalSpace E]
    (D : C0ResolventDatum E) (hdense : ∀ mu, DenseRange (D.operator mu))
    (k : ℝ) (hk : 0 < k) (mu : PositiveShift) :
    DenseRange ((clockResolvent D k hk).operator mu) := by
  have hrange : Set.range ((clockResolvent D k hk).operator mu) =
      Set.range (D.operator (clockShift k hk mu)) := by
    ext g
    constructor
    · rintro ⟨f, rfl⟩
      refine ⟨k • f, ?_⟩
      exact D.solution_smul _ k f
    · rintro ⟨f, rfl⟩
      refine ⟨k⁻¹ • f, ?_⟩
      change k • D.solution _ (k⁻¹ • f) = D.solution _ f
      rw [D.solution_smul, _root_.smul_smul, mul_inv_cancel₀ hk.ne', _root_.one_smul]
  change Dense (Set.range _)
  rw [hrange]
  exact hdense _

/-- Normalize both the massive shift and the actual H¹ solution of `(k rho,rho)`. -/
theorem clockResolvent_weak {d : ℕ} (rho : (Fin d → ℝ) → ℝ)
    (D : C0ResolventDatum (Fin d → ℝ)) (k : ℝ) (hk : 0 < k)
    (hweak : IsWeakEllipticResolvent (fun x => k * rho x) rho D) :
    IsWeakEllipticResolvent rho rho (clockResolvent D k hk) := by
  intro mu f W hW
  obtain ⟨u, hu, hsol⟩ := hweak (clockShift k hk mu) f W hW
  refine ⟨k • u, fun x hx => ?_, ?_⟩
  · change k * u.toFun x = k * D.solution _ f x
    rw [hu x hx]
  · intro phi
    have hmass : (∫ x in W, rho x * (k • u).toFun x * phi.toH1Function.toFun x) =
        k * ∫ x in W, rho x * u.toFun x * phi.toH1Function.toFun x := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by change _ * (k * _) * _ = _; ring
    have hen : (∫ x in W, vecDot (rho x • (k • u).grad x) (phi.toH1Function.grad x)) =
        ∫ x in W, vecDot ((k * rho x) • u.grad x) (phi.toH1Function.grad x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change vecDot (rho x • (k • u.grad x)) _ = _
        rw [_root_.smul_smul, mul_comm (rho x) k]
    rw [hmass, hen]
    have h := hsol phi
    dsimp only [clockShift] at h
    nlinarith only [h]

end
end SubdiffusiveProcess.Examples
