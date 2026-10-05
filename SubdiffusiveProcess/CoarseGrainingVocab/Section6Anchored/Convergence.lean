module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.Algebra
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.LipschitzLimit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.UniformCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-!
# Local `C¹ˑ¹` convergence of the anchored coefficients

Everything in this module is deterministic: it lives on one sample of the
canonical anchored good event, where the defining local `C¹ˑ¹` limit property
is available, and turns that property into the convergence statements printed
in paper label `e.finite.cutoff.coefficient.C11.convergence`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open Filter _root_.SubdiffusiveProcess.Model Homogenization Topology

noncomputable section

variable {d : ℕ}

/-- The anchored cutoff coefficient read on the potential-field partial sums. -/
theorem anchoredCutoff_eq_exp_field (M : GMCModel d) (L : ℕ)
    (omega : PotentialSample d) (x : Vec d) :
    anchoredCutoff M L omega x =
      Real.exp (anchoredPartialSumField omega L x) := by
  rw [anchoredCutoff_eq_exp, anchoredPartialSumField_apply]

variable (M : GMCModel d) (omega : AnchoredC11Sample d)

/-! ### Uniform bounds on a compact window -/

/-- A nonnegative sup bound for the limiting logarithm on a compact window. -/
theorem exists_bound_anchoredLog {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, |anchoredLog omega x| ≤ B := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (anchoredLog omega).1.1.continuous.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x hx => ?_⟩
  exact le_trans (by simpa only [Real.norm_eq_abs] using hB x hx) (le_max_left _ _)

/-- A nonnegative sup bound for the limiting derivative on a compact window. -/
theorem exists_bound_anchoredLog_deriv {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredLog omega) x‖ ≤ B := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (_root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredLog omega)).continuous.continuousOn
  exact ⟨max B 0, le_max_right _ _,
    fun x hx => le_trans (hB x hx) (le_max_left _ _)⟩

/-- A nonnegative sup bound for the limiting coefficient on a compact window. -/
theorem exists_bound_aAnchored {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ K, ‖aAnchored M omega x‖ ≤ A := by
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn
    (continuous_aAnchored M omega).continuousOn
  exact ⟨max A 0, le_max_right _ _,
    fun x hx => le_trans (hA x hx) (le_max_left _ _)⟩

/-! ### The three uniform limits -/

/-- The anchored cutoff coefficients converge uniformly on compact sets. -/
theorem tendstoUniformlyOn_anchoredCutoff {K : Set (Vec d)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun L x => anchoredCutoff M L omega.1 x)
      (aAnchored M omega) atTop K := by
  obtain ⟨B, _, hB⟩ := exists_bound_anchoredLog omega hK
  have hval := (anchoredLog_spec omega).value_tendsto K hK
  have hexp := tendstoUniformlyOn_exp (B := B) hB hval
  have h1 : (fun (L : ℕ) (x : Vec d) => anchoredCutoff M L omega.1 x) =
      fun L x => Real.exp (anchoredPartialSum omega.1 L x) := by
    funext L x
    exact anchoredCutoff_eq_exp M L omega.1 x
  rw [h1]
  exact hexp

/-- The stored derivatives of the anchored sums converge uniformly on compact
sets; This is the defining property, restated for readability. -/
theorem tendstoUniformlyOn_deriv {K : Set (Vec d)} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun L x => _root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredPartialSumField omega.1 L) x)
      (_root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredLog omega)) atTop K :=
  (anchoredLog_spec omega).deriv_tendsto K hK

/-- The coordinate gradients of the anchored sums converge uniformly on
compact sets. -/
theorem tendstoUniformlyOn_shellGradient {K : Set (Vec d)} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun L x => shellGradient (anchoredPartialSumField omega.1 L) x)
      (shellGradient (anchoredLog omega)) atTop K :=
  tendstoUniformlyOn_comp_of_norm_sub_le gradOfCLM
    (fun a b => by rw [← gradOfCLM_sub]; exact norm_gradOfCLM_le _)
    (tendstoUniformlyOn_deriv omega hK)

/-! ### The coefficient gradient -/

/-- The derivative of the finite anchored coefficient, stored as a continuous
linear functional. -/
def cutoffDeriv (L : ℕ) (x : Vec d) : Vec d →L[ℝ] ℝ :=
  anchoredCutoff M L omega.1 x •
    _root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredPartialSumField omega.1 L) x

/-- The derivative of the limiting anchored coefficient. -/
def limitDeriv (x : Vec d) : Vec d →L[ℝ] ℝ :=
  aAnchored M omega x • _root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredLog omega) x

theorem hasFDerivAt_anchoredCutoff (L : ℕ) (x : Vec d) :
    HasFDerivAt (fun y => anchoredCutoff M L omega.1 y) (cutoffDeriv M omega L x) x := by
  have hbase :
      HasFDerivAt (fun y => Real.exp (anchoredPartialSumField omega.1 L y))
        (Real.exp (anchoredPartialSumField omega.1 L x) •
          _root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredPartialSumField omega.1 L) x) x :=
    ((anchoredPartialSumField omega.1 L).hasFDerivAt x).exp
  have hfun : (fun y => anchoredCutoff M L omega.1 y) =
      fun y => Real.exp (anchoredPartialSumField omega.1 L y) := by
    funext y
    exact anchoredCutoff_eq_exp_field M L omega.1 y
  rw [hfun, cutoffDeriv, anchoredCutoff_eq_exp_field]
  exact hbase

theorem hasFDerivAt_aAnchored (x : Vec d) :
    HasFDerivAt (fun y => aAnchored M omega y) (limitDeriv M omega x) x :=
  ((anchoredLog omega).hasFDerivAt x).exp

/-- The coefficient gradients converge uniformly on compact sets. -/
theorem tendstoUniformlyOn_cutoffDeriv {K : Set (Vec d)} (hK : IsCompact K) :
    TendstoUniformlyOn (cutoffDeriv M omega) (limitDeriv M omega) atTop K := by
  obtain ⟨A, hA0, hA⟩ := exists_bound_aAnchored M omega hK
  obtain ⟨B, hB0, hB⟩ := exists_bound_anchoredLog_deriv omega hK
  exact tendstoUniformlyOn_smul hA0 hB0 hA hB
    (tendstoUniformlyOn_anchoredCutoff M omega hK)
    (tendstoUniformlyOn_deriv omega hK)

theorem gradOfCLM_cutoffDeriv (L : ℕ) (x : Vec d) :
    gradOfCLM (cutoffDeriv M omega L x) =
      anchoredCutoff M L omega.1 x •
        shellGradient (anchoredPartialSumField omega.1 L) x :=
  rfl

theorem gradOfCLM_limitDeriv (x : Vec d) :
    gradOfCLM (limitDeriv M omega x) =
      aAnchored M omega x • shellGradient (anchoredLog omega) x :=
  rfl

/-- The coordinate coefficient gradients converge uniformly on compact sets. -/
theorem tendstoUniformlyOn_coefficientGradient {K : Set (Vec d)}
    (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun L x => anchoredCutoff M L omega.1 x •
        shellGradient (anchoredPartialSumField omega.1 L) x)
      (fun x => aAnchored M omega x • shellGradient (anchoredLog omega) x)
      atTop K :=
  tendstoUniformlyOn_comp_of_norm_sub_le gradOfCLM
    (fun a b => by rw [← gradOfCLM_sub]; exact norm_gradOfCLM_le _)
    (tendstoUniformlyOn_cutoffDeriv M omega hK)

/-! ### Lipschitz seminorm convergence of the derivatives -/

/-- A `gradOfCLM` image inherits any Lipschitz bound. -/
theorem lipschitzOnWith_gradOfCLM_comp {D : Vec d → (Vec d →L[ℝ] ℝ)}
    {K : Set (Vec d)} {c : NNReal} (h : LipschitzOnWith c D K) :
    LipschitzOnWith c (fun x => gradOfCLM (D x)) K := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  calc dist (gradOfCLM (D x)) (gradOfCLM (D y))
      = ‖gradOfCLM (D x) - gradOfCLM (D y)‖ := dist_eq_norm _ _
    _ = ‖gradOfCLM (D x - D y)‖ := by rw [gradOfCLM_sub]
    _ ≤ ‖D x - D y‖ := norm_gradOfCLM_le _
    _ = dist (D x) (D y) := (dist_eq_norm _ _).symm
    _ ≤ c * dist x y := h.dist_le_mul x hx y hy

/-- The stored derivatives of the anchored sums converge to the limiting
derivative in the Lipschitz seminorm of every compact window. -/
theorem exists_lipschitzOnWith_deriv_sub {K : Set (Vec d)} (hK : IsCompact K)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ N : ℕ, ∀ L : ℕ, N ≤ L →
      LipschitzOnWith (Real.toNNReal eps)
        (fun x => _root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredPartialSumField omega.1 L) x -
          _root_.SubdiffusiveProcess.Model.PotentialField.deriv (anchoredLog omega) x) K := by
  obtain ⟨N, hN⟩ := (anchoredLog_spec omega).deriv_lipschitz_cauchy K hK eps heps
  refine ⟨N, fun L hL => ?_⟩
  refine lipschitzOnWith_sub_limit
    (fun x hx => (tendstoUniformlyOn_deriv omega hK).tendsto_at hx) ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN L n hL hn

/-- The coordinate gradients converge in the Lipschitz seminorm of every
compact window. -/
theorem exists_lipschitzOnWith_shellGradient_sub {K : Set (Vec d)}
    (hK : IsCompact K) {eps : ℝ} (heps : 0 < eps) :
    ∃ N : ℕ, ∀ L : ℕ, N ≤ L →
      LipschitzOnWith (Real.toNNReal eps)
        (fun x => shellGradient (anchoredPartialSumField omega.1 L) x -
          shellGradient (anchoredLog omega) x) K := by
  obtain ⟨N, hN⟩ := exists_lipschitzOnWith_deriv_sub omega hK heps
  exact ⟨N, fun L hL => lipschitzOnWith_gradOfCLM_comp (hN L hL)⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
