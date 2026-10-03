module

public import SubdiffusiveProcess.DirichletForm.FOTProduct
public import SubdiffusiveProcess.DirichletForm.Resolvent
public import SubdiffusiveProcess.Variational.DualEnergy
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

@[expose] public section

/-! Finite killed-cell decompositions identify two harmonic form-domain functions.
These deterministic helpers are used after localized recovery and truncation have
been proved; they make no claim that those proof steps are principal hypotheses. -/

open MeasureTheory Filter Set
open scoped Topology BigOperators

noncomputable section
namespace SubdiffusiveProcess.Section9

variable {X I : Type*} [MeasurableSpace X] [Fintype I]
  {mu : Measure X}

/-- A finite disjoint partition decomposes an L2 class into its cell indicators. -/
theorem eq_sum_of_ae_indicator_partition
    (cell : I → Set X) (hdisj : Pairwise fun i j => Disjoint (cell i) (cell j))
    (hcover : ∀ᵐ x ∂mu, ∃ i, x ∈ cell i)
    (w : Lp ℝ 2 mu) (wc : X → ℝ) (hw : (w : X → ℝ) =ᵐ[mu] wc)
    (wi : I → Lp ℝ 2 mu)
    (hwi : ∀ i, (wi i : X → ℝ) =ᵐ[mu] (cell i).indicator wc) :
    w = ∑ i, wi i := by
  classical
  apply Lp.ext
  filter_upwards [hw, hcover,
    DirichletForm.coeFn_finset_sum (Finset.univ : Finset I) wi
      (fun i => (cell i).indicator wc) (fun i _ => hwi i)] with x hx hcx hsum
  obtain ⟨i, hi⟩ := hcx
  rw [hx, hsum]
  rw [Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem hi]
  · intro j _ hji
    rw [Set.indicator_of_notMem]
    exact fun hj => Set.disjoint_left.mp (hdisj hji) hj hi
  · simp

/-- Orthogonality to every killed cell makes the energy of a decomposed difference zero. -/
theorem form_sub_self_eq_zero_of_finite_decomposition
    (E : DirichletForm.ClosedForm mu)
    (D : I → Submodule ℝ (Lp ℝ 2 mu)) (hD : ∀ i, D i ≤ E.domain)
    (u v : Lp ℝ 2 mu) (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hui : ∀ i w, w ∈ D i → E.form u w = 0)
    (hvi : ∀ i w, w ∈ D i → E.form v w = 0)
    (wi : I → Lp ℝ 2 mu) (hwi : ∀ i, wi i ∈ D i)
    (hsub : u - v = ∑ i, wi i) :
    E.form (u - v) (u - v) = 0 := by
  have hwdom : ∀ i, wi i ∈ E.domain := fun i => hD i (hwi i)
  rw [congrArg (E.form (u - v)) hsub]
  rw [E.form_sum_right Finset.univ (fun i _ => hwdom i) (E.domain.sub_mem hu hv)]
  apply Finset.sum_eq_zero
  intro i _
  rw [E.form_sub_left hu hv (hwdom i), hui i (wi i) (hwi i), hvi i (wi i) (hwi i)]
  exact sub_self _

/-- A form defined by the bounded inverse's dual energy has no nonzero zero-energy element. -/
theorem eq_zero_of_form_self_eq_zero_of_dual_energy
    (E : DirichletForm.ClosedForm mu) (G : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (hE : ∀ w, E.energy w = DirichletForm.dualEnergy G w)
    (u : Lp ℝ 2 mu) (hu : u ∈ E.domain) (hzero : E.form u u = 0) : u = 0 := by
  have hdual : (⨆ f : Lp ℝ 2 mu,
      ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) =
      (E.form u u : EReal) := by
    change DirichletForm.dualEnergy G u = (E.form u u : EReal)
    rw [← hE u, E.energy_of_mem hu]
  have hnorm := SubdiffusiveProcess.norm_sq_le_operatorNorm_mul_quadraticDual
    G u (E.form u u) hdual
  rw [hzero, mul_zero] at hnorm
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg u]

/-- Finite cellwise harmonicity and the killed decomposition identify two limits. -/
theorem eq_of_orthogonal_finite_decomposition
    (E : DirichletForm.ClosedForm mu) (G : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu)
    (hE : ∀ w, E.energy w = DirichletForm.dualEnergy G w)
    (D : I → Submodule ℝ (Lp ℝ 2 mu)) (hD : ∀ i, D i ≤ E.domain)
    (u v : Lp ℝ 2 mu) (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hui : ∀ i w, w ∈ D i → E.form u w = 0)
    (hvi : ∀ i w, w ∈ D i → E.form v w = 0)
    (wi : I → Lp ℝ 2 mu) (hwi : ∀ i, wi i ∈ D i)
    (hsub : u - v = ∑ i, wi i) : u = v := by
  apply sub_eq_zero.mp
  exact eq_zero_of_form_self_eq_zero_of_dual_energy E G hE (u - v)
    (E.domain.sub_mem hu hv)
    (form_sub_self_eq_zero_of_finite_decomposition E D hD u v hu hv hui hvi wi hwi hsub)

end SubdiffusiveProcess.Section9
