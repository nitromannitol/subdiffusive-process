module

public import SubdiffusiveProcess.CoarseGrainingVocab.CutoffMoments
public import Mathlib.Order.Filter.CountableSeparatingOn
public import Mathlib.Probability.Independence.ZeroOne

@[expose] public section

/-!
# Rigidity endgame for the one-layer simplex gap

The strict-decay proposition  proves the strict
one-cell gap `q_* < 1` by contradiction.  After the Euler equation and the
stationarity/regularity sweep, the argument reaches a purely probabilistic
endgame:

> The independent random variables `B_0(0)` and `B_0(tp)` coincide almost
> surely; hence each is deterministic.  It follows that `g_0(0)` is
> deterministic and, since it has mean zero, that `tau^2 = 0`, contrary to
> Assumption (g4).

This file proves that endgame against the assumptions.  The two
ingredients are kept separate:

* `ae_eq_const_of_indepFun_ae_eq` is the generic probability statement that a
  real random variable which agrees almost surely with an independent copy is
  almost surely constant;
* `tauSq_eq_zero_of_shell_ae_const` converts almost-sure constancy of a shell
  evaluation into `tau^2 = 0`, using only mean zero from (g1) and the exact
  shell scaling law.

Their composition, `not_ae_eq_shell_of_indepFun`, is the exact contradiction
consumed by Step 1 of the strict-decay proof.  Upstream of it lie the
simplex Dirichlet minimization, the
Euler equation, and the passage from the equality case to the pointwise
identity `g_0(0) = g_0(tp)`.
-/

open MeasureTheory ProbabilityTheory Filter

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

noncomputable section

/-! ## The generic zero-one endgame -/

section Generic

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- If `f` and `g` are independent and almost surely equal, then every
measurable event of `f` is trivial. -/
theorem measure_preimage_eq_zero_or_one_of_indepFun_ae_eq
    [IsProbabilityMeasure mu] {f g : Omega → ℝ}
    (hindep : IndepFun f g mu) (heq : f =ᵐ[mu] g) {s : Set ℝ}
    (hs : MeasurableSet s) :
    mu (f ⁻¹' s) = 0 ∨ mu (f ⁻¹' s) = 1 := by
  have hsets : (f ⁻¹' s) =ᵐ[mu] (g ⁻¹' s) := by
    rw [eventuallyEqSet_iff]
    filter_upwards [heq] with x hx
    simp only [Set.mem_preimage, hx]
  have hmeas : mu (g ⁻¹' s) = mu (f ⁻¹' s) := (measure_congr hsets).symm
  have hinter : mu (f ⁻¹' s ∩ g ⁻¹' s) = mu (f ⁻¹' s) := by
    refine measure_congr ?_
    exact (EventuallyEqSet.inter (Filter.EventuallyEq.refl _ _) hsets.symm).trans
      (by simp)
  have hprod :=
    (ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul.1 hindep) s s hs hs
  rw [hinter, hmeas] at hprod
  by_cases h0 : mu (f ⁻¹' s) = 0
  · exact Or.inl h0
  refine Or.inr ?_
  have htop : mu (f ⁻¹' s) ≠ ⊤ := measure_ne_top mu _
  have : mu (f ⁻¹' s) * 1 = mu (f ⁻¹' s) * mu (f ⁻¹' s) := by
    rw [mul_one]; exact hprod
  exact ((ENNReal.mul_right_inj h0 htop).1 this).symm

/-- **The paper's rigidity endgame, generic form.**  A real random variable
that agrees almost surely with an independent copy is almost surely constant.
This is "the independent random variables
`B_0(0)` and `B_0(tp)` coincide almost surely; hence each is
deterministic". -/
theorem ae_eq_const_of_indepFun_ae_eq [IsProbabilityMeasure mu]
    {f g : Omega → ℝ} (hf : Measurable f)
    (hindep : IndepFun f g mu) (heq : f =ᵐ[mu] g) :
    ∃ c : ℝ, f =ᵐ[mu] fun _ => c := by
  refine Filter.exists_eventuallyEq_const_of_forall_separating
    (l := ae mu) (f := f) (fun s : Set ℝ => MeasurableSet s) ?_
  intro s hs
  rcases measure_preimage_eq_zero_or_one_of_indepFun_ae_eq hindep heq hs with
    h0 | h1
  · exact Or.inr (measure_eq_zero_iff_ae_notMem.1 h0)
  · refine Or.inl ?_
    have hcompl : mu ((f ⁻¹' s)ᶜ) = 0 := by
      rw [measure_compl (hf hs) (measure_ne_top mu _), h1, measure_univ]
      simp
    simpa [Set.mem_preimage] using measure_eq_zero_iff_ae_notMem.1 hcompl

end Generic

/-! ## Almost-sure constancy of a shell evaluation forces `tauSq = 0` -/

section Model

variable {d : ℕ}

open _root_.SubdiffusiveProcess.Model

/-- Every shell evaluation is measurable. -/
theorem measurable_shell_eval (k : ℕ) (x : Vec d) :
    Measurable (fun omega : PotentialSample d => omega k x) :=
  (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval x).comp (measurable_potentialCoordinate k)

/-- The exponential moment defining `tauSq` may be read off any shell
evaluation, by the exact scaling law of the layer marginals. -/
theorem integral_exp_shell_eval (M : GMCModel d) (k : ℕ) (x : Vec d) :
    ∫ omega : PotentialSample d, Real.exp (omega k x) ∂M.P.toMeasure =
      ∫ g : PotentialField d, Real.exp (g 0)
        ∂(zeroPotentialLaw M.P).toMeasure := by
  have hexp : Measurable (fun z : ℝ => Real.exp z) := Real.measurable_exp
  have heval0 : Measurable (fun g : PotentialField d => g 0) :=
    _root_.SubdiffusiveProcess.Model.PotentialField.measurable_eval 0
  calc
    ∫ omega : PotentialSample d, Real.exp (omega k x) ∂M.P.toMeasure =
        ∫ z : ℝ, Real.exp z
          ∂Measure.map (fun omega : PotentialSample d => omega k x)
            M.P.toMeasure :=
      (integral_map (measurable_shell_eval k x).aemeasurable
        hexp.aestronglyMeasurable).symm
    _ = ∫ z : ℝ, Real.exp z
          ∂Measure.map (fun g : PotentialField d => g 0)
            (zeroPotentialLaw M.P).toMeasure := by
      rw [map_potentialCoordinate_apply_eq_zero M k x]
    _ = ∫ g : PotentialField d, Real.exp (g 0)
          ∂(zeroPotentialLaw M.P).toMeasure :=
      integral_map heval0.aemeasurable hexp.aestronglyMeasurable

/-- **Mean zero plus almost-sure constancy forces zero disorder.**  This is
"it follows that `g_0(0)` is deterministic and,
since it has mean zero, that `tau^2 = 0`". -/
theorem tauSq_eq_zero_of_shell_ae_const (M : GMCModel d) (x : Vec d) {c : ℝ}
    (hconst : (fun omega : PotentialSample d => omega 0 x) =ᵐ[M.P.toMeasure]
      fun _ => c) :
    tauSq M.P = 0 := by
  have : IsProbabilityMeasure M.P.toMeasure := M.P.prop
  have hzero : c = 0 := by
    have hmean := M.G1.mean_zero x
    rw [integral_congr_ae hconst] at hmean
    simpa using hmean
  subst hzero
  have hexp : ∫ omega : PotentialSample d, Real.exp (omega 0 x) ∂M.P.toMeasure
      = 1 := by
    have hae : (fun omega : PotentialSample d => Real.exp (omega 0 x))
        =ᵐ[M.P.toMeasure] fun _ => (1 : ℝ) := by
      filter_upwards [hconst] with omega homega
      simp [homega]
    rw [integral_congr_ae hae]
    simp
  have hmoment : ∫ g : PotentialField d, Real.exp (g 0)
      ∂(zeroPotentialLaw M.P).toMeasure = 1 := by
    rw [← integral_exp_shell_eval M 0 x]
    exact hexp
  unfold tauSq
  rw [hmoment, Real.log_one]

/-- **No shell evaluation is deterministic.**  Assumption (g4) gives
`tauSq > 0`, so the contradiction  is
available at every point. -/
theorem shell_not_ae_const (M : GMCModel d) (x : Vec d) :
    ¬ ∃ c : ℝ, (fun omega : PotentialSample d => omega 0 x)
      =ᵐ[M.P.toMeasure] fun _ => c := by
  rintro ⟨c, hc⟩
  have := tauSq_eq_zero_of_shell_ae_const M x hc
  have hpos := M.G4.tauSq_pos
  rw [this] at hpos
  exact lt_irrefl 0 hpos

/-- **The exact Step 1 contradiction.**  Two independent shell evaluations of
the unit-scale layer cannot agree almost surely.  This is the sole
probabilistic content; the geometric input
that produces the almost-sure identity from the Euler equation remains the
open analytic boundary. -/
theorem not_ae_eq_shell_of_indepFun (M : GMCModel d) (x y : Vec d)
    (hindep : IndepFun (fun omega : PotentialSample d => omega 0 x)
      (fun omega : PotentialSample d => omega 0 y) M.P.toMeasure) :
    ¬ ((fun omega : PotentialSample d => omega 0 x) =ᵐ[M.P.toMeasure]
      fun omega : PotentialSample d => omega 0 y) := by
  intro heq
  have : IsProbabilityMeasure M.P.toMeasure := M.P.prop
  exact shell_not_ae_const M x
    (ae_eq_const_of_indepFun_ae_eq (measurable_shell_eval 0 x) hindep heq)

end Model

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
