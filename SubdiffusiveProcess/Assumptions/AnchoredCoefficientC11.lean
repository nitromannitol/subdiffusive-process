import SubdiffusiveProcess.Assumptions.AnchoredCoefficient
import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

/-!
# Local C¹ˑ¹ regularity of the anchored coefficient

Exponentiating a potential field preserves its compact-set Lipschitz derivative
certificate. In particular, the anchored coefficient satisfies `CoefficientC11On`
on every set, without an openness or boundedness assumption.
-/

namespace SubdiffusiveProcess.Assumptions.AnchoredCoefficientC11

open Homogenization Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

noncomputable section

theorem aux_dedup_d117_exists_lipschitzOnWith_of_continuous_deriv {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Vec d → F} {D : Vec d → (Vec d →L[ℝ] F)}
    (hD : ∀ x, HasFDerivAt f (D x) x) (hc : Continuous D)
    (K : Set (Vec d)) (hK : IsCompact K) :
    ∃ C : NNReal, LipschitzOnWith C f K := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Vec d)
  obtain ⟨B, hB⟩ :=
    (isCompact_closedBall (0 : Vec d) r).exists_bound_of_continuousOn hc.continuousOn
  have hLip : LipschitzOnWith ⟨max B 0, le_max_right _ _⟩ f
      (Metric.closedBall (0 : Vec d) r) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (𝕜 := ℝ) (f' := D) _ _ (convex_closedBall (0 : Vec d) r)
    · intro x _
      exact (hD x).hasFDerivWithinAt
    · intro x hx
      have hle := hB x hx
      exact_mod_cast le_trans hle (le_max_left _ _)
  exact ⟨_, hLip.mono hr⟩

private theorem exists_lipschitzOnWith_of_continuous_deriv {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Vec d → F} {D : Vec d → (Vec d →L[ℝ] F)}
    (hD : ∀ x, HasFDerivAt f (D x) x) (hc : Continuous D)
    (K : Set (Vec d)) (hK : IsCompact K) :
    ∃ C : NNReal, LipschitzOnWith C f K := by exact SubdiffusiveProcess.Assumptions.AnchoredCoefficientC11.aux_dedup_d117_exists_lipschitzOnWith_of_continuous_deriv (d := d) (F := F) (f := f) (D := D) (hD := hD) (hc := hc) (K := K) (hK := hK)

theorem aux_dedup_d095_lipschitzOnWith_smul_of_bounds {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {f : E → ℝ} {g : E → F} {Lf Lg A B : NNReal}
    (hf : LipschitzOnWith Lf f K) (hg : LipschitzOnWith Lg g K)
    (hA : ∀ x ∈ K, ‖f x‖ ≤ (A : ℝ)) (hB : ∀ x ∈ K, ‖g x‖ ≤ (B : ℝ)) :
    LipschitzOnWith (A * Lg + B * Lf) (fun x => f x • g x) K := by
  rw [lipschitzOnWith_iff_norm_sub_le] at hf hg ⊢
  intro x hx y hy
  have h1 : ‖f x‖ * ‖g x - g y‖ ≤ (A : ℝ) * (Lg : ℝ) * ‖x - y‖ := by
    calc
      ‖f x‖ * ‖g x - g y‖ ≤ (A : ℝ) * ‖g x - g y‖ :=
        mul_le_mul_of_nonneg_right (hA x hx) (norm_nonneg _)
      _ ≤ (A : ℝ) * ((Lg : ℝ) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (hg hx hy) (NNReal.coe_nonneg A)
      _ = (A : ℝ) * (Lg : ℝ) * ‖x - y‖ := (mul_assoc _ _ _).symm
  have h2 : ‖f x - f y‖ * ‖g y‖ ≤ (B : ℝ) * (Lf : ℝ) * ‖x - y‖ := by
    calc
      ‖f x - f y‖ * ‖g y‖ ≤ (Lf : ℝ) * ‖x - y‖ * ‖g y‖ :=
        mul_le_mul_of_nonneg_right (hf hx hy) (norm_nonneg _)
      _ ≤ ((Lf : ℝ) * ‖x - y‖) * (B : ℝ) :=
        mul_le_mul_of_nonneg_left (hB y hy)
          (mul_nonneg (NNReal.coe_nonneg Lf) (norm_nonneg _))
      _ = (B : ℝ) * (Lf : ℝ) * ‖x - y‖ := by ring
  calc
    ‖f x • g x - f y • g y‖ = ‖f x • (g x - g y) + (f x - f y) • g y‖ := by
      rw [smul_sub, sub_smul, sub_add_sub_cancel]
    _ ≤ ‖f x • (g x - g y)‖ + ‖(f x - f y) • g y‖ := norm_add_le _ _
    _ = ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ (A : ℝ) * (Lg : ℝ) * ‖x - y‖ + (B : ℝ) * (Lf : ℝ) * ‖x - y‖ :=
      add_le_add h1 h2
    _ = ((A : ℝ) * (Lg : ℝ) + (B : ℝ) * (Lf : ℝ)) * ‖x - y‖ := by ring

private theorem lipschitzOnWith_smul_of_bounds {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E} {f : E → ℝ} {g : E → F} {Lf Lg A B : NNReal}
    (hf : LipschitzOnWith Lf f K) (hg : LipschitzOnWith Lg g K)
    (hA : ∀ x ∈ K, ‖f x‖ ≤ (A : ℝ)) (hB : ∀ x ∈ K, ‖g x‖ ≤ (B : ℝ)) :
    LipschitzOnWith (A * Lg + B * Lf) (fun x => f x • g x) K := by exact SubdiffusiveProcess.Assumptions.AnchoredCoefficientC11.aux_dedup_d095_lipschitzOnWith_smul_of_bounds (E := E) (F := F) (K := K) (f := f) (g := g) (Lf := Lf) (Lg := Lg) (A := A) (B := B) (hf := hf) (hg := hg) (hA := hA) (hB := hB)

private theorem exp_derivative_regular {d : ℕ} (g : PotentialField d) :
    (∀ x, HasFDerivAt (fun y => Real.exp (g y)) (Real.exp (g x) • g.deriv x) x) ∧
      Continuous (fun x => Real.exp (g x) • g.deriv x) := by
  constructor
  · intro x
    exact (g.hasFDerivAt x).exp
  · exact (Real.continuous_exp.comp g.1.1.continuous).smul g.deriv.continuous

/-- The exponential of a potential field has a Lipschitz derivative on every
compact subset of any set `U`. -/
theorem coefficientC11On_exp {d : ℕ} (g : PotentialField d)
    (U : Set (Vec d)) : CoefficientC11On U (fun x => Real.exp (g x)) := by
  have hreg := exp_derivative_regular g
  refine ⟨fun x => Real.exp (g x) • g.deriv x, fun x _ => hreg.1 x, ?_⟩
  intro K hK _
  obtain ⟨Lf, hf⟩ := exists_lipschitzOnWith_of_continuous_deriv hreg.1 hreg.2 K hK
  obtain ⟨Lg, hg⟩ := g.property.2 K hK
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn
    (Real.continuous_exp.comp g.1.1.continuous).continuousOn
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn g.deriv.continuous.continuousOn
  refine ⟨_, lipschitzOnWith_smul_of_bounds (A := ⟨max A 0, le_max_right _ _⟩)
    (B := ⟨max B 0, le_max_right _ _⟩) hf hg ?_ ?_⟩
  · intro x hx
    exact (hA x hx).trans (le_max_left _ _)
  · intro x hx
    exact (hB x hx).trans (le_max_left _ _)

/-- The derivative of the anchored coefficient is the coefficient times the
stored derivative of its anchored logarithmic potential. -/
theorem hasFDerivAt_aAnchored {d : ℕ} (M : GMCModel d) (omega : AnchoredC11Sample d)
    (x : Vec d) :
    HasFDerivAt (aAnchored M omega)
      (aAnchored M omega x • (anchoredLog omega).deriv x) x :=
  ((anchoredLog omega).hasFDerivAt x).exp

/-- The GMC model supplies the local C¹ˑ¹ coefficient hypothesis for every
anchored sample, with no restriction on the set `U`. -/
theorem coefficientC11On_aAnchored {d : ℕ} (M : GMCModel d)
    (omega : AnchoredC11Sample d) (U : Set (Vec d)) :
    CoefficientC11On U (aAnchored M omega) :=
  coefficientC11On_exp (anchoredLog omega) U

end

end SubdiffusiveProcess.Assumptions.AnchoredCoefficientC11
