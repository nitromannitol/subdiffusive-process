module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity
public import Mathlib.Analysis.InnerProductSpace.Dual

@[expose] public section

/-!
# (RRK) in the manuscript's own form gives the whole datum

hypothesis
‖(I + sH)^{-N} f‖_{C^α(K)} ≤ C_K ‖f‖_{L²(μ)}   for every K ⋐ Ω.       (RRK)

`HeatKernelRegularity.ResolventRegularityDatum` records (RRK) in the *dual* form
that its proof consumes: a map `repr : X → L²(μ)` with

    `(I+sH)^{-N} f (x) = ⟪repr x, f⟫`  a.e.  and  `‖repr x - repr y‖ ≤ C_K |x-y|^α`.

This file proves that the manuscript's own form implies that dual form.  Suppose
that for every `f ∈ L²(μ)` the function `(I+sH)^{-N} f` has a representative
continuous on the carrier — as a `C^α(K)` bound for every `K ⋐ Ω` asserts — and
that `‖(I+sH)^{-N}f‖_∞ ≤ C‖f‖₂`.  Then:

* `exists_repr_of_continuousOn_representative` builds `repr` **directly**, with no
  separability and no measurable-selection argument: for `x` in the carrier the
  continuous representatives are *unique* (`eqOn_of_ae_eq_of_fullSupport`), so
  `f ↦ (I+sH)^{-N}f (x)` is an honest linear functional, bounded by `C` because
  the almost-everywhere sup bound upgrades to a pointwise one on the carrier
  (`le_of_ae_le`).  Fréchet–Riesz then gives `repr x`.
* `norm_repr_sub_le` converts a `C^α(K)` bound on those representatives into the
  datum's `holder_repr`.  The duality is a one-liner: testing `‖repr x - repr y‖²
  = ⟪repr x - repr y, repr x - repr y⟫` against `f := repr x - repr y` itself
  turns the Hölder bound for the representative of `T f` into the bound for
  `repr`.

So the *only* mathematical input the datum still needs, for the library killed
forms, is the `C^α` half of (RRK) for the killed resolvent powers:
`SubdiffusiveProcess/CoarseGrainingVocab/Section8Support/RRKDatumUltracontractive.lean` supplies
the sup-norm half and
`SubdiffusiveProcess/CoarseGrainingVocab/Section8Support/RRKHolderKilled.lean` the Riesz
representative, unconditionally; the Hölder modulus is not available in the
library, and `RRKHolderKilled.resolventRegularityDatum_of_holder_repr` isolates
it as the single open field.

Nothing here proves any regularity: every statement takes the `C^α` estimate as a
hypothesis.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped RealInnerProductSpace ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderContinuous

open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity

variable {X : Type*} [MeasurableSpace X] [MetricSpace X] {mu : Measure X} {Om : Set X}

/-! ## The Riesz representative of a pointwise-defined evaluation -/

/-- **The (RRK) representative from continuous representatives.**

If every `T f` has a representative continuous on the carrier and `|T f| ≤ C‖f‖`
almost everywhere, then evaluation at a point of the carrier is a bounded linear
functional and Fréchet–Riesz represents it.  The second conclusion is pointwise
at *every* point of the carrier, which is what the Hölder half needs. -/
theorem exists_repr_of_continuousOn_representative
    (hOm : IsOpen Om) (hsupp : FullSupportOn mu Om) (hcompl : mu Omᶜ = 0)
    (T : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu) {C : ℝ}
    (hsup : ∀ f : Lp ℝ 2 mu, ∀ᵐ x ∂mu, |(T f) x| ≤ C * ‖f‖)
    (hcont : ∀ f : Lp ℝ 2 mu, ∃ u : X → ℝ, ContinuousOn u Om ∧
      (fun x => (T f) x) =ᵐ[mu] u) :
    ∃ g : X → Lp ℝ 2 mu,
      (∀ f : Lp ℝ 2 mu, (fun x => (T f) x) =ᵐ[mu] fun x => ⟪g x, f⟫) ∧
      (∀ (f : Lp ℝ 2 mu) (u : X → ℝ), ContinuousOn u Om →
        (fun x => (T f) x) =ᵐ[mu] u → ∀ x ∈ Om, ⟪g x, f⟫ = u x) := by
  classical
  choose u hucont huae using hcont
  -- a continuous representative on the carrier is unique
  have huniq : ∀ (f : Lp ℝ 2 mu) (w : X → ℝ), ContinuousOn w Om →
      (fun x => (T f) x) =ᵐ[mu] w → EqOn w (u f) Om := by
    intro f w hw hwae
    refine eqOn_of_ae_eq_of_fullSupport hOm hsupp hw (hucont f) ?_
    filter_upwards [hwae, huae f] with x h1 h2 _
    rw [← h1, h2]
  -- additivity and homogeneity of `f ↦ u f x` on the carrier
  have hadd : ∀ (f f' : Lp ℝ 2 mu), EqOn (fun x => u f x + u f' x) (u (f + f')) Om := by
    intro f f'
    refine huniq (f + f') _ ((hucont f).add (hucont f')) ?_
    filter_upwards [Lp.coeFn_add (T f) (T f'), huae f, huae f'] with x h0 h1 h2
    show ((T (f + f')) x) = u f x + u f' x
    rw [map_add, h0]
    simp only [Pi.add_apply]
    rw [h1, h2]
  have hsmul : ∀ (a : ℝ) (f : Lp ℝ 2 mu), EqOn (fun x => a * u f x) (u (a • f)) Om := by
    intro a f
    refine huniq (a • f) _ (continuousOn_const.mul (hucont f)) ?_
    filter_upwards [Lp.coeFn_smul a (T f), huae f] with x h0 h1
    show ((T (a • f)) x) = a * u f x
    rw [map_smul, h0]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1]
  -- the sup bound at every point of the carrier
  have hbdd : ∀ (f : Lp ℝ 2 mu), ∀ x ∈ Om, |u f x| ≤ C * ‖f‖ := by
    intro f
    refine le_of_ae_le hOm hsupp (hucont f).abs ?_
    filter_upwards [hsup f, huae f] with x h1 h2 _
    rw [← h2]
    exact h1
  -- the representative
  refine ⟨fun x =>
    if hx : x ∈ Om then
      (InnerProductSpace.toDual ℝ (Lp ℝ 2 mu)).symm
        (LinearMap.mkContinuous
          ({ toFun := fun f => u f x
             map_add' := fun f f' => (hadd f f' hx).symm
             map_smul' := fun a f => (hsmul a f hx).symm } : Lp ℝ 2 mu →ₗ[ℝ] ℝ)
          C (fun f => by
            rw [Real.norm_eq_abs]
            exact hbdd f x hx))
    else 0, ?_, ?_⟩
  · intro f
    have hOmae : ∀ᵐ x ∂mu, x ∈ Om := by
      rw [ae_iff]
      simpa only [Set.compl_def] using hcompl
    filter_upwards [huae f, hOmae] with x hx hxOm
    rw [hx]
    simp only [dite_eq_left hxOm]
    rw [InnerProductSpace.toDual_symm_apply, LinearMap.mkContinuous_apply]
    rfl
  · intro f w hw hwae x hx
    simp only [dite_eq_left hx]
    rw [InnerProductSpace.toDual_symm_apply, LinearMap.mkContinuous_apply]
    exact (huniq f w hw hwae hx).symm

/-! ## The Hölder half, by duality -/

/-- **A `C^α` bound on the representatives is the datum's `holder_repr`.**

Testing `‖repr x - repr y‖² = ⟪repr x - repr y, repr x - repr y⟫` against
`f := repr x - repr y` turns the `C^α(K)` bound for the representative of `T f`
into the `L²`-valued Hölder bound.  Only the value of the hypothesis at that one
`f` is used. -/
theorem norm_repr_sub_le {T : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu} {g : X → Lp ℝ 2 mu}
    (hg : ∀ (f : Lp ℝ 2 mu) (w : X → ℝ), ContinuousOn w Om →
      (fun x => (T f) x) =ᵐ[mu] w → ∀ x ∈ Om, ⟪g x, f⟫ = w x)
    {K : Set X} (hKOm : K ⊆ Om) {Ck a : ℝ} (hCk : 0 ≤ Ck)
    (hK : ∀ f : Lp ℝ 2 mu, ∃ w : X → ℝ, ContinuousOn w Om ∧
      (fun x => (T f) x) =ᵐ[mu] w ∧
      ∀ x ∈ K, ∀ y ∈ K, |w x - w y| ≤ Ck * ‖f‖ * dist x y ^ a) :
    ∀ x ∈ K, ∀ y ∈ K, ‖g x - g y‖ ≤ Ck * dist x y ^ a := by
  intro x hx y hy
  obtain ⟨w, hwcont, hwae, hwbd⟩ := hK (g x - g y)
  have hxOm : x ∈ Om := hKOm hx
  have hyOm : y ∈ Om := hKOm hy
  have hsq : ‖g x - g y‖ ^ 2 = w x - w y := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left,
      hg (g x - g y) w hwcont hwae x hxOm, hg (g x - g y) w hwcont hwae y hyOm]
  have hle : ‖g x - g y‖ ^ 2 ≤ Ck * ‖g x - g y‖ * dist x y ^ a := by
    rw [hsq]
    exact (le_abs_self _).trans (hwbd x hx y hy)
  rcases eq_or_lt_of_le (norm_nonneg (g x - g y)) with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg hCk (Real.rpow_nonneg dist_nonneg a)
  · nlinarith [hle, hpos]

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKHolderContinuous
