/-
# Lipschitz calculus and products on a Dirichlet form (Fukushima–Oshima–Takeda 1.4.1, 1.4.2)
-/
import SubdiffusiveProcess.DirichletForm.Regular
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Lipschitz calculus and products on a Dirichlet form

A `DirichletForm` only assumes that the unit contraction `t ↦ (t ∧ 1) ∨ 0` operates.  This file
derives from that single Markov clause and closedness the calculus of Fukushima–Oshima–Takeda
§1.4, with no regularity, locality or resolvent input:

* `DirichletForm.lipschitz_comp_mem`: if `G` is `L`-Lipschitz with `G 0 = 0` and `u ∈ D(E)`,
  then `G ∘ u ∈ D(E)` and `E(G ∘ u) ≤ L² E(u)` (Theorem 1.4.1 for `L = 1`;
  `DirichletForm.hasNormalContractions`).
* `DirichletForm.exists_mul_mem`: products of bounded elements of `D(E)` lie in `D(E)`
  (Theorem 1.4.2(ii)).
* `DirichletForm.exists_memCoreOn_mul_comp`, `DirichletForm.mul_comp_mem`,
  `DirichletForm.mul_mem`, `DirichletForm.comp_mem`, `DirichletForm.mul_mem_of_bounded`: the
  core `D(E) ∩ C_c` is stable under products and `C¹` functions (Theorem 1.4.2), in the exact
  shapes of the four closure clauses of `DirichletForm.IsCoreAlgebra`.

## Method

1. *Cross energies.*  If the ramp at level `h` returns `f` from `f + t g` for all `t > 0`,
   then `E(f, g) ≥ 0` (`form_nonneg_of_ramp_eq`).  Hence the slices of `u` over the cells
   `[i h, (i + 1) h]`, the reflected slices and the tail beyond `N h` have pairwise
   nonnegative cross energies.
2. *Piecewise-linear functions.*  A combination of these slices with coefficients of size at
   most `L` has energy at most `L² E(u)` (`sliceSum_mem_and_form_le`).
3. *Lower semicontinuity.*  A closed form is lower semicontinuous along `L²`-convergent
   sequences of bounded energy (`ClosedForm.mem_domain_of_tendsto_of_form_le`): the
   minimal-energy points of the convex hulls of the tails form an energy-Cauchy sequence by
   the parallelogram identity.
4. *Limit.*  The interpolants of `G` on finer and longer grids converge to `G ∘ u` in `L²` by
   dominated convergence (`tendsto_Lp_of_tendsto_comp`).
5. *Products* follow by polarization with a clamped square; *`C¹` functions* of bounded
   elements by clamping to the range, where they are Lipschitz.

## References

* M. Fukushima, Y. Oshima, M. Takeda, *Dirichlet Forms and Symmetric Markov Processes*,
  2nd edition, de Gruyter, 2011, Theorems 1.4.1 and 1.4.2.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal

noncomputable section

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

namespace DirichletForm

/-! ### Ramps -/

/-- The ramp `s ↦ (s ∧ c) ∨ 0`.  It vanishes at `0` for every `c`. -/
def ramp (c s : ℝ) : ℝ := max 0 (min s c)

@[simp] theorem ramp_zero (c : ℝ) : ramp c 0 = 0 := by
  simp only [ramp]
  exact max_eq_left (min_le_left 0 c)

theorem lipschitzWith_ramp (c : ℝ) : LipschitzWith 1 (ramp c) := by
  simpa [ramp] using
    (LipschitzWith.const (0 : ℝ)).max (LipschitzWith.id.min (LipschitzWith.const c))

theorem ramp_nonneg (c s : ℝ) : 0 ≤ ramp c s := le_max_left _ _

theorem ramp_of_nonpos {c s : ℝ} (hs : s ≤ 0) : ramp c s = 0 :=
  max_eq_left ((min_le_left s c).trans hs)

theorem ramp_of_le {c s : ℝ} (hs0 : 0 ≤ s) (hsc : s ≤ c) : ramp c s = s := by
  simp only [ramp, min_eq_left hsc, max_eq_right hs0]

theorem ramp_of_ge {c s : ℝ} (hc : 0 ≤ c) (hcs : c ≤ s) : ramp c s = c := by
  simp only [ramp, min_eq_right hcs, max_eq_right hc]

theorem ramp_le {c s : ℝ} (hc : 0 ≤ c) : ramp c s ≤ c :=
  max_le hc (min_le_right _ _)

/-- The ramp as a map of `L²`. -/
def rampLp (c : ℝ) (u : Lp ℝ 2 m) : Lp ℝ 2 m :=
  (lipschitzWith_ramp c).compLp (ramp_zero c) u

theorem coeFn_rampLp (c : ℝ) (u : Lp ℝ 2 m) :
    ⇑(rampLp c u) =ᵐ[m] fun x => ramp c (u x) :=
  LipschitzWith.coeFn_compLp _ _ _

/-- **Every ramp operates** on a Dirichlet form: for `c > 0` it is `c · unitTruncation (·/c)`,
and for `c ≤ 0` it vanishes identically. -/
theorem rampLp_mem (E : DirichletForm m) {c : ℝ} {w : Lp ℝ 2 m} (hw : w ∈ E.domain) :
    rampLp c w ∈ E.domain ∧ E.form (rampLp c w) (rampLp c w) ≤ E.form w w := by
  rcases le_or_gt c 0 with hc | hc
  · have h0 : rampLp c w = 0 := by
      refine Lp.ext ((coeFn_rampLp c w).trans ?_)
      filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx
      rw [hx, Pi.zero_apply]
      exact max_eq_left ((min_le_right _ _).trans hc)
    rw [h0, E.form_zero_left E.domain.zero_mem]
    exact ⟨E.domain.zero_mem, E.form_nonneg w hw⟩
  · have hw' : c⁻¹ • w ∈ E.domain := E.domain.smul_mem _ hw
    set v : Lp ℝ 2 m := lipschitzWith_unitTruncation.compLp unitTruncation_zero (c⁻¹ • w)
    have hv : ⇑v =ᵐ[m] fun x => unitTruncation ((c⁻¹ • w : Lp ℝ 2 m) x) :=
      LipschitzWith.coeFn_compLp _ _ _
    obtain ⟨hvdom, hvE⟩ := E.markov _ hw' v hv
    have heq : rampLp c w = c • v := by
      refine Lp.ext ?_
      filter_upwards [coeFn_rampLp c w, Lp.coeFn_smul c v, hv, Lp.coeFn_smul c⁻¹ w]
        with x h1 h2 h3 h4
      rw [h1, h2, Pi.smul_apply, h3, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      simp only [ramp, unitTruncation]
      rw [mul_max_of_nonneg _ _ hc.le, mul_min_of_nonneg _ _ hc.le, mul_zero, mul_one,
        ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul, max_comm]
    rw [heq]
    refine ⟨E.domain.smul_mem c hvdom, ?_⟩
    rw [E.form_smul_left c v hvdom _ (E.domain.smul_mem c hvdom),
      E.form_smul_right c hvdom hvdom]
    rw [E.form_smul_left c⁻¹ w hw _ hw', E.form_smul_right c⁻¹ hw hw] at hvE
    have hc2 : c * c * c⁻¹ * c⁻¹ = 1 := by field_simp
    calc c * (c * E.form v v) ≤ c * (c * (c⁻¹ * (c⁻¹ * E.form w w))) := by
          gcongr
      _ = (c * c * c⁻¹ * c⁻¹) * E.form w w := by ring
      _ = E.form w w := by rw [hc2, one_mul]

/-! ### Nonnegative cross energies -/

/-- **Positivity of a cross energy from the Markov property.**  If the ramp at level `h`
returns `f` from `f + t g` for every `t > 0`, then `E(f, g) ≥ 0`: the ramp does not increase
energy, so `E(f) ≤ E(f + t g) = E(f) + 2t E(f, g) + t² E(g)`. -/
theorem form_nonneg_of_ramp_eq (E : DirichletForm m) {f g : Lp ℝ 2 m} (hf : f ∈ E.domain)
    (hg : g ∈ E.domain) {h : ℝ}
    (hramp : ∀ t : ℝ, 0 < t → ∀ᵐ x ∂m, ramp h (f x + t * g x) = f x) :
    0 ≤ E.form f g := by
  have key : ∀ t : ℝ, 0 < t → 0 ≤ 2 * E.form f g + t * E.form g g := by
    intro t ht
    have hft : f + t • g ∈ E.domain := E.domain.add_mem hf (E.domain.smul_mem t hg)
    have heq : rampLp h (f + t • g) = f := by
      refine Lp.ext ?_
      filter_upwards [coeFn_rampLp h (f + t • g), Lp.coeFn_add f (t • g), Lp.coeFn_smul t g,
        hramp t ht] with x h1 h2 h3 h4
      rw [h1, h2, Pi.add_apply, h3, Pi.smul_apply, smul_eq_mul, h4]
    have hle := (rampLp_mem E (c := h) hft).2
    rw [heq, E.form_add_smul_self t hf hg] at hle
    have h2 : 0 ≤ t * (2 * E.form f g + t * E.form g g) := by
      have hexp : t * (2 * E.form f g + t * E.form g g) =
          2 * t * E.form f g + t ^ 2 * E.form g g := by ring
      rw [hexp]
      linarith
    exact (mul_nonneg_iff_of_pos_left ht).mp h2
  by_contra hneg
  push_neg at hneg
  have hgg := E.form_nonneg g hg
  set t : ℝ := -E.form f g / (E.form g g + 1) with htdef
  have ht : 0 < t := div_pos (by linarith) (by linarith)
  have h1 := key t ht
  have h2 : t * E.form g g < -E.form f g := by
    rw [htdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    exact mul_lt_mul_of_pos_left (lt_add_one _) (by linarith)
  linarith

/-! ### Lower semicontinuity of a closed form -/

namespace ClosedForm

variable (E : ClosedForm m)

/-- `E(a - b) = E(a) - 2 E(a, b) + E(b)`. -/
theorem form_sub_self {a b : Lp ℝ 2 m} (ha : a ∈ E.domain) (hb : b ∈ E.domain) :
    E.form (a - b) (a - b) = E.form a a - 2 * E.form a b + E.form b b := by
  rw [E.form_sub_left ha hb (E.domain.sub_mem ha hb), E.form_sub_right ha ha hb,
    E.form_sub_right hb ha hb, E.form_symm b hb a ha]
  ring

/-- The parallelogram identity for the quadratic form `E`. -/
theorem form_sub_self_add_four_mul_midpoint {a b : Lp ℝ 2 m} (ha : a ∈ E.domain)
    (hb : b ∈ E.domain) :
    E.form (a - b) (a - b) +
        4 * E.form ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) =
      2 * E.form a a + 2 * E.form b b := by
  have hmid : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b = (1 / 2 : ℝ) • (a + b) := by
    rw [smul_add]
  have hab := E.domain.add_mem ha hb
  rw [hmid, E.form_smul_left _ _ hab _ (E.domain.smul_mem _ hab), E.form_smul_right _ hab hab,
    E.form_add_self ha hb, E.form_sub_self ha hb]
  ring

/-- **Lower semicontinuity of a closed form.**  If `uₙ ∈ D(E)` converge to `z` in `L²` with
`E(uₙ) ≤ K`, then `z ∈ D(E)` and `E(z) ≤ K`.

The proof uses only closedness: the minimal-energy points `wₙ` of the convex hulls of the tails
`{u_k : k ≥ n}` form an energy-Cauchy sequence by the parallelogram identity, and they converge
to `z` in `L²` because each tail hull lies in a small ball around `z`. -/
theorem mem_domain_of_tendsto_of_form_le {u : ℕ → Lp ℝ 2 m} (hu : ∀ n, u n ∈ E.domain)
    {z : Lp ℝ 2 m} (hz : Tendsto u atTop (𝓝 z)) {K : ℝ}
    (hK : ∀ n, E.form (u n) (u n) ≤ K) :
    z ∈ E.domain ∧ E.form z z ≤ K := by
  classical
  set C : ℕ → Set (Lp ℝ 2 m) := fun n => convexHull ℝ (u '' Ici n) with hCdef
  have hCD : ∀ n, C n ⊆ E.domain := fun n =>
    convexHull_min (image_subset_iff.2 fun k _ => hu k) E.domain.convex
  have hCanti : ∀ {n p : ℕ}, n ≤ p → C p ⊆ C n := fun hnp =>
    convexHull_mono (image_mono (Ici_subset_Ici.2 hnp))
  have huC : ∀ n, u n ∈ C n := fun n => subset_convexHull ℝ _ ⟨n, left_mem_Ici, rfl⟩
  set q : Lp ℝ 2 m → ℝ := fun w => E.form w w with hqdef
  have hne : ∀ n, (q '' C n).Nonempty := fun n => ⟨q (u n), mem_image_of_mem q (huC n)⟩
  have hbdd : ∀ n, BddBelow (q '' C n) := fun n => by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact E.form_nonneg w (hCD n hw)
  set δ : ℕ → ℝ := fun n => sInf (q '' C n) with hδdef
  have hδle : ∀ n, ∀ w ∈ C n, δ n ≤ q w := fun n w hw =>
    csInf_le (hbdd n) (mem_image_of_mem q hw)
  have hδK : ∀ n, δ n ≤ K := fun n => (hδle n (u n) (huC n)).trans (hK n)
  have hδmono : Monotone δ := fun n p hnp =>
    csInf_le_csInf (hbdd n) (hne p) (image_mono (hCanti hnp))
  have hεpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hex : ∀ n, ∃ w ∈ C n, q w < δ n + 1 / ((n : ℝ) + 1) := fun n => by
    obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ :=
      exists_lt_of_csInf_lt (hne n) (lt_add_of_pos_right (δ n) (hεpos n))
    exact ⟨w, hw, hlt⟩
  choose w hwC hwlt using hex
  have hwD : ∀ n, w n ∈ E.domain := fun n => hCD n (hwC n)
  -- the infima converge
  have hδbdd : BddAbove (range δ) := ⟨K, by rintro _ ⟨n, rfl⟩; exact hδK n⟩
  set δ' : ℝ := ⨆ n, δ n with hδ'def
  have hδlim : Tendsto δ atTop (𝓝 δ') := tendsto_atTop_ciSup hδmono hδbdd
  have hδle' : ∀ n, δ n ≤ δ' := fun n => le_ciSup hδbdd n
  -- `w` is Cauchy for the form
  have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ r ≥ N,
      E.form (w p - w r) (w p - w r) < ε := by
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.1 hδlim) (ε / 8) (by positivity)
    obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.1 (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
      (ε / 8) (by positivity)
    refine ⟨max N₁ N₂, fun p hp r hr => ?_⟩
    set n := max N₁ N₂
    have hsmall : ∀ k ≥ n, 1 / ((k : ℝ) + 1) < ε / 8 := fun k hk => by
      have := hN₂ k (le_of_max_le_right hk)
      rw [Real.dist_eq, sub_zero, abs_of_pos (hεpos k)] at this
      exact this
    have hδn : δ' - δ n < ε / 8 := by
      have := hN₁ n (le_max_left _ _)
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hδle' n))] at this
      exact this
    have hmid : (1 / 2 : ℝ) • w p + (1 / 2 : ℝ) • w r ∈ C n :=
      convex_convexHull ℝ _ (hCanti hp (hwC p)) (hCanti hr (hwC r)) (by norm_num) (by norm_num)
        (by norm_num)
    have h1 := hδle n _ hmid
    have hpar := E.form_sub_self_add_four_mul_midpoint (hwD p) (hwD r)
    have hp' : q (w p) < δ' + ε / 8 := by
      have := hwlt p; have := hδle' p; have := hsmall p hp; linarith
    have hr' : q (w r) < δ' + ε / 8 := by
      have := hwlt r; have := hδle' r; have := hsmall r hr; linarith
    simp only [hqdef] at h1 hp' hr'
    linarith
  -- `w` converges to `z` in `L²`
  have hwz : Tendsto w atTop (𝓝 z) := by
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hz ε hε
    refine ⟨N, fun n hn => ?_⟩
    have hball : C N ⊆ Metric.ball z ε :=
      convexHull_min (image_subset_iff.2 fun k hk => hN k hk) (convex_ball z ε)
    exact hball (hCanti hn (hwC n))
  obtain ⟨hzD, hE1⟩ := E.mem_domain_of_tendsto_of_formCauchy w hwD z hwz hcauchy
  refine ⟨hzD, ?_⟩
  have hq : Tendsto (fun n => q (w n)) atTop (𝓝 (q z)) :=
    E.tendsto_form_self_of_tendsto_energyNormSq hwD hzD hE1
  have hq' : Tendsto (fun n => q (w n) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (q z - 0)) :=
    hq.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [sub_zero] at hq'
  refine le_of_tendsto' hq' fun n => ?_
  have := hwlt n; have := hδK n
  linarith

end ClosedForm

/-! ### Slices of the real line -/

theorem ramp_of_le_right {c s : ℝ} (hsc : s ≤ c) : ramp c s = max 0 s := by
  simp only [ramp, min_eq_left hsc]

theorem ramp_mono_left {c c' : ℝ} (hcc' : c ≤ c') (s : ℝ) : ramp c s ≤ ramp c' s :=
  max_le_max le_rfl (min_le_min_left s hcc')

/-- The `i`-th slice of height `h`: `s ↦ ramp ((i + 1) h) s - ramp (i h) s`, which rises with
slope `1` on `[i h, (i + 1) h]` and is constant elsewhere. -/
def slice (h : ℝ) (i : ℕ) (s : ℝ) : ℝ := ramp (((i : ℝ) + 1) * h) s - ramp ((i : ℝ) * h) s

section SliceReal

variable {h : ℝ} {i : ℕ} {s : ℝ}

theorem mul_le_add_one_mul (hh : 0 ≤ h) (a : ℝ) : a * h ≤ (a + 1) * h := by
  rw [add_mul, one_mul]
  linarith

theorem slice_nonneg (hh : 0 ≤ h) : 0 ≤ slice h i s :=
  sub_nonneg.2 (ramp_mono_left (mul_le_add_one_mul hh _) s)

theorem slice_of_le (hh : 0 ≤ h) (hs : s ≤ (i : ℝ) * h) : slice h i s = 0 := by
  have hb : s ≤ ((i : ℝ) + 1) * h := hs.trans (mul_le_add_one_mul hh _)
  simp only [slice, ramp_of_le_right hs, ramp_of_le_right hb, sub_self]

theorem slice_of_ge (hh : 0 ≤ h) (hs : ((i : ℝ) + 1) * h ≤ s) : slice h i s = h := by
  have ha0 : 0 ≤ (i : ℝ) * h := by positivity
  have ha : (i : ℝ) * h ≤ s := (mul_le_add_one_mul hh _).trans hs
  simp only [slice, ramp_of_ge (by positivity) hs, ramp_of_ge ha0 ha]
  ring

theorem slice_le (hh : 0 ≤ h) : slice h i s ≤ h := by
  rcases le_total s ((i : ℝ) * h) with hs | hs
  · rw [slice_of_le hh hs]; exact hh
  · have ha0 : 0 ≤ (i : ℝ) * h := by positivity
    simp only [slice, ramp_of_ge ha0 hs]
    have := ramp_le (c := ((i : ℝ) + 1) * h) (s := s) (by positivity)
    linarith

theorem slice_of_nonpos (hh : 0 ≤ h) (hs : s ≤ 0) : slice h i s = 0 :=
  slice_of_le hh (hs.trans (by positivity))

/-- A slice is returned by the ramp at its own height from `slice + t · g` whenever `g` is
positive only above the slice and negative only below `0`. -/
theorem ramp_slice_add_mul {g : ℝ} (hh : 0 ≤ h) {t : ℝ} (ht : 0 < t)
    (hpos : 0 < g → ((i : ℝ) + 1) * h ≤ s) (hneg : g < 0 → s ≤ 0) :
    ramp h (slice h i s + t * g) = slice h i s := by
  rcases lt_trichotomy g 0 with hg | hg | hg
  · rw [slice_of_nonpos hh (hneg hg), zero_add]
    exact ramp_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ht.le hg.le)
  · rw [hg, mul_zero, add_zero]
    exact ramp_of_le (slice_nonneg hh) (slice_le hh)
  · rw [slice_of_ge hh (hpos hg)]
    exact ramp_of_ge hh (le_add_of_nonneg_right (mul_nonneg ht.le hg.le))

/-- The tail `s ↦ s - ramp R s + ramp R (-s)`, i.e. `s - clamp(s, -R, R)`. -/
def tail (R s : ℝ) : ℝ := s - ramp R s + ramp R (-s)

theorem tail_pos {R s : ℝ} (hR : 0 ≤ R) (h : 0 < tail R s) : R ≤ s := by
  by_contra hlt
  push_neg at hlt
  rcases le_total 0 s with h0 | h0
  · simp only [tail, ramp_of_le h0 hlt.le, ramp_of_nonpos (neg_nonpos.2 h0)] at h
    linarith
  · have := ramp_le (c := R) (s := -s) hR
    simp only [tail, ramp_of_nonpos h0] at h
    rcases le_total (-s) R with h1 | h1
    · rw [ramp_of_le (neg_nonneg.2 h0) h1] at h; linarith
    · linarith

theorem tail_neg {R s : ℝ} (hR : 0 ≤ R) (h : tail R s < 0) : s ≤ 0 := by
  by_contra hlt
  push_neg at hlt
  simp only [tail, ramp_of_nonpos (by linarith : -s ≤ 0), add_zero] at h
  have := ramp_le (c := R) (s := s) hR
  rcases le_total s R with h1 | h1
  · rw [ramp_of_le hlt.le h1] at h; linarith
  · rw [ramp_of_ge hR h1] at h; linarith

end SliceReal

/-! ### Slices in `L²` -/

theorem rampLp_of_nonpos {c : ℝ} (hc : c ≤ 0) (u : Lp ℝ 2 m) : rampLp c u = 0 := by
  refine Lp.ext ((coeFn_rampLp c u).trans ?_)
  filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx
  rw [hx, Pi.zero_apply]
  exact max_eq_left ((min_le_right _ _).trans hc)

/-- The `i`-th slice of `u`. -/
def sliceLp (h : ℝ) (i : ℕ) (u : Lp ℝ 2 m) : Lp ℝ 2 m :=
  rampLp (((i : ℝ) + 1) * h) u - rampLp ((i : ℝ) * h) u

theorem coeFn_sliceLp (h : ℝ) (i : ℕ) (u : Lp ℝ 2 m) :
    ⇑(sliceLp h i u) =ᵐ[m] fun x => slice h i (u x) := by
  filter_upwards [Lp.coeFn_sub (rampLp (((i : ℝ) + 1) * h) u) (rampLp ((i : ℝ) * h) u),
    coeFn_rampLp (((i : ℝ) + 1) * h) u, coeFn_rampLp ((i : ℝ) * h) u] with x h1 h2 h3
  rw [sliceLp, h1, Pi.sub_apply, h2, h3]
  rfl

theorem sliceLp_mem (E : DirichletForm m) (h : ℝ) (i : ℕ) {u : Lp ℝ 2 m}
    (hu : u ∈ E.domain) : sliceLp h i u ∈ E.domain :=
  E.domain.sub_mem (rampLp_mem E hu).1 (rampLp_mem E hu).1

theorem sum_sliceLp (h : ℝ) (N : ℕ) (u : Lp ℝ 2 m) :
    ∑ i ∈ Finset.range N, sliceLp h i u = rampLp ((N : ℝ) * h) u := by
  have := Finset.sum_range_sub (fun i : ℕ => rampLp ((i : ℝ) * h) u) N
  simp only [Nat.cast_add_one, Nat.cast_zero, zero_mul,
    rampLp_of_nonpos le_rfl u, sub_zero] at this
  exact this

/-- The tail of `u` beyond the level `R`. -/
def tailLp (R : ℝ) (u : Lp ℝ 2 m) : Lp ℝ 2 m := u - rampLp R u + rampLp R (-u)

theorem coeFn_tailLp (R : ℝ) (u : Lp ℝ 2 m) :
    ⇑(tailLp R u) =ᵐ[m] fun x => tail R (u x) := by
  filter_upwards [Lp.coeFn_add (u - rampLp R u) (rampLp R (-u)), Lp.coeFn_sub u (rampLp R u),
    coeFn_rampLp R u, coeFn_rampLp R (-u), Lp.coeFn_neg u] with x h1 h2 h3 h4 h5
  rw [tailLp, h1, Pi.add_apply, h2, Pi.sub_apply, h3, h4, h5]
  rfl

theorem tailLp_mem (E : DirichletForm m) (R : ℝ) {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    tailLp R u ∈ E.domain :=
  E.domain.add_mem (E.domain.sub_mem hu (rampLp_mem E hu).1)
    (rampLp_mem E (E.domain.neg_mem hu)).1

theorem tailLp_neg (R : ℝ) (u : Lp ℝ 2 m) : tailLp R (-u) = -tailLp R u := by
  simp only [tailLp, neg_neg]
  abel

/-! ### Signs of the cross energies of slices -/

section Cross

variable (E : DirichletForm m) {u : Lp ℝ 2 m} (hu : u ∈ E.domain) {h : ℝ} (hh : 0 ≤ h)
include hu hh

/-- Two slices of the same function have nonnegative cross energy. -/
theorem form_sliceLp_sliceLp_nonneg {i j : ℕ} (hij : i < j) :
    0 ≤ E.form (sliceLp h i u) (sliceLp h j u) := by
  refine form_nonneg_of_ramp_eq E (h := h) (sliceLp_mem E h i hu) (sliceLp_mem E h j hu)
    fun t ht => ?_
  filter_upwards [coeFn_sliceLp h i u, coeFn_sliceLp h j u] with x h1 h2
  rw [h1, h2]
  refine ramp_slice_add_mul hh ht (fun hpos => ?_) (fun hneg => absurd hneg
    (not_lt.2 (slice_nonneg hh)))
  by_contra hlt
  push_neg at hlt
  have hj : ((i : ℝ) + 1) * h ≤ (j : ℝ) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hh
  exact hpos.ne' (slice_of_le hh (hlt.le.trans hj))

/-- A slice of `u` and a (negated) slice of `-u` have nonnegative cross energy. -/
theorem form_sliceLp_neg_sliceLp_nonneg (i j : ℕ) :
    0 ≤ E.form (sliceLp h i u) (-sliceLp h j (-u)) := by
  refine form_nonneg_of_ramp_eq E (h := h) (sliceLp_mem E h i hu)
    (E.domain.neg_mem (sliceLp_mem E h j (E.domain.neg_mem hu))) fun t ht => ?_
  filter_upwards [coeFn_sliceLp h i u, Lp.coeFn_neg (sliceLp h j (-u)),
    coeFn_sliceLp h j (-u), Lp.coeFn_neg u] with x h1 h2 h3 h4
  rw [h1, h2, Pi.neg_apply, h3, h4, Pi.neg_apply]
  refine ramp_slice_add_mul hh ht (fun hpos => absurd hpos
    (not_lt.2 (neg_nonpos.2 (slice_nonneg hh)))) (fun hneg => ?_)
  by_contra hlt
  push_neg at hlt
  exact (neg_neg_iff_pos.1 hneg).ne' (slice_of_nonpos hh (by linarith))

/-- A slice below the level `N h` and the tail beyond `N h` have nonnegative cross energy. -/
theorem form_sliceLp_tailLp_nonneg {i N : ℕ} (hiN : i < N) :
    0 ≤ E.form (sliceLp h i u) (tailLp ((N : ℝ) * h) u) := by
  refine form_nonneg_of_ramp_eq E (h := h) (sliceLp_mem E h i hu) (tailLp_mem E _ hu) fun t ht => ?_
  filter_upwards [coeFn_sliceLp h i u, coeFn_tailLp ((N : ℝ) * h) u] with x h1 h2
  rw [h1, h2]
  have hR : 0 ≤ (N : ℝ) * h := by positivity
  refine ramp_slice_add_mul hh ht (fun hpos => ?_) (tail_neg hR)
  have hiN' : ((i : ℝ) + 1) * h ≤ (N : ℝ) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hiN) hh
  exact hiN'.trans (tail_pos hR hpos)

end Cross

/-! ### Finite sums with nonnegative cross energies -/

namespace ClosedForm

variable (E : ClosedForm m)

theorem form_sum_left {ι : Type*} (s : Finset ι) {F : ι → Lp ℝ 2 m}
    (hF : ∀ i ∈ s, F i ∈ E.domain) {y : Lp ℝ 2 m} (hy : y ∈ E.domain) :
    E.form (∑ i ∈ s, F i) y = ∑ i ∈ s, E.form (F i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [E.form_zero_left hy]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, F i ∈ E.domain := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      E.form_add_left _ (hF a (Finset.mem_insert_self a s)) _ (E.domain.sum_mem hs) y hy, ih hs]

theorem form_sum_right {ι : Type*} (s : Finset ι) {F : ι → Lp ℝ 2 m}
    (hF : ∀ i ∈ s, F i ∈ E.domain) {x : Lp ℝ 2 m} (hx : x ∈ E.domain) :
    E.form x (∑ i ∈ s, F i) = ∑ i ∈ s, E.form x (F i) := by
  rw [E.form_symm x hx _ (E.domain.sum_mem hF), E.form_sum_left s hF hx]
  exact Finset.sum_congr rfl fun i hi => E.form_symm _ (hF i hi) x hx

/-- **Comonotone families.**  If the members of a finite family have pairwise nonnegative
cross energies, then weighting them by coefficients of size at most `L` multiplies the energy
of the sum by at most `L²`. -/
theorem form_sum_smul_le {ι : Type*} (s : Finset ι) {F : ι → Lp ℝ 2 m} (c : ι → ℝ) {L : ℝ}
    (hF : ∀ i ∈ s, F i ∈ E.domain) (hc : ∀ i ∈ s, |c i| ≤ L)
    (hpos : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 0 ≤ E.form (F i) (F j)) :
    E.form (∑ i ∈ s, c i • F i) (∑ i ∈ s, c i • F i) ≤
      L ^ 2 * E.form (∑ i ∈ s, F i) (∑ i ∈ s, F i) := by
  have hcF : ∀ i ∈ s, c i • F i ∈ E.domain := fun i hi => E.domain.smul_mem _ (hF i hi)
  have hexp : ∀ (a : ι → ℝ), E.form (∑ i ∈ s, a i • F i) (∑ i ∈ s, a i • F i) =
      ∑ i ∈ s, ∑ j ∈ s, a i * a j * E.form (F i) (F j) := by
    intro a
    have haF : ∀ i ∈ s, a i • F i ∈ E.domain := fun i hi => E.domain.smul_mem _ (hF i hi)
    rw [E.form_sum_left s haF (E.domain.sum_mem haF)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [E.form_sum_right s haF (haF i hi)]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [E.form_smul_left _ _ (hF i hi) _ (haF j hj), E.form_smul_right _ (hF i hi) (hF j hj)]
    ring
  have h1 := hexp c
  have h2 := hexp fun _ => 1
  simp only [one_smul, one_mul] at h2
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hci := hc i hi
  have hcj := hc j hj
  have hL : 0 ≤ L := (abs_nonneg _).trans hci
  by_cases hij : i = j
  · subst hij
    have he := E.form_nonneg _ (hF i hi)
    have hsq : c i * c i ≤ L ^ 2 := by
      rw [← abs_mul_abs_self, sq]
      exact mul_le_mul hci hci (abs_nonneg _) hL
    exact mul_le_mul_of_nonneg_right hsq he
  · have he := hpos i hi j hj hij
    have hprod : c i * c j ≤ L ^ 2 := by
      calc c i * c j ≤ |c i * c j| := le_abs_self _
        _ = |c i| * |c j| := abs_mul _ _
        _ ≤ L * L := mul_le_mul hci hcj (abs_nonneg _) hL
        _ = L ^ 2 := (sq L).symm
    exact mul_le_mul_of_nonneg_right hprod he

/-- Adding a domain element with nonnegative cross energy does not decrease the energy. -/
theorem form_le_form_add {a b : Lp ℝ 2 m} (ha : a ∈ E.domain) (hb : b ∈ E.domain)
    (hab : 0 ≤ E.form a b) : E.form a a ≤ E.form (a + b) (a + b) := by
  rw [E.form_add_self ha hb]
  have := E.form_nonneg b hb
  linarith

end ClosedForm

/-! ### Energy of a weighted sum of slices -/

/-- The weighted slice sum `∑ aᵢ · slice_i(u) - ∑ bᵢ · slice_i(-u)`: a piecewise-linear
function of `u` with slopes `aᵢ` on `[i h, (i+1) h]` and `bᵢ` on `[-(i+1) h, -i h]`. -/
def sliceSum (h : ℝ) (N : ℕ) (a b : ℕ → ℝ) (u : Lp ℝ 2 m) : Lp ℝ 2 m :=
  ∑ i ∈ Finset.range N, a i • sliceLp h i u + ∑ i ∈ Finset.range N, b i • (-sliceLp h i (-u))

/-- **A piecewise-linear function with slopes bounded by `L` multiplies the energy by at most
`L²`.**  The slices of `u` together with its tail have pairwise nonnegative cross energies
(`form_sliceLp_sliceLp_nonneg`, `form_sliceLp_neg_sliceLp_nonneg`,
`form_sliceLp_tailLp_nonneg`); this uses only the unit contraction. -/
theorem sliceSum_mem_and_form_le (E : DirichletForm m) {u : Lp ℝ 2 m} (hu : u ∈ E.domain)
    {h : ℝ} (hh : 0 ≤ h) (N : ℕ) (a b : ℕ → ℝ) {L : ℝ} (ha : ∀ i < N, |a i| ≤ L)
    (hb : ∀ i < N, |b i| ≤ L) :
    sliceSum h N a b u ∈ E.domain ∧
      E.form (sliceSum h N a b u) (sliceSum h N a b u) ≤ L ^ 2 * E.form u u := by
  classical
  have hnu : -u ∈ E.domain := E.domain.neg_mem hu
  set s : Finset (Bool × ℕ) := Finset.univ ×ˢ Finset.range N with hsdef
  set F : Bool × ℕ → Lp ℝ 2 m := fun p =>
    if p.1 then sliceLp h p.2 u else -sliceLp h p.2 (-u) with hFdef
  set c : Bool × ℕ → ℝ := fun p => if p.1 then a p.2 else b p.2 with hcdef
  have hsum : ∀ g : Bool × ℕ → Lp ℝ 2 m, ∑ p ∈ s, g p =
      ∑ i ∈ Finset.range N, g (true, i) + ∑ i ∈ Finset.range N, g (false, i) := by
    intro g
    rw [hsdef, Finset.sum_product, Fintype.sum_bool]
  have hv : sliceSum h N a b u = ∑ p ∈ s, c p • F p := by
    rw [hsum]
    rfl
  have hFD : ∀ p ∈ s, F p ∈ E.domain := by
    rintro ⟨_ | _, i⟩ _
    · exact E.domain.neg_mem (sliceLp_mem E h i hnu)
    · exact sliceLp_mem E h i hu
  have hcL : ∀ p ∈ s, |c p| ≤ L := by
    rintro ⟨_ | _, i⟩ hp
    · exact hb i (Finset.mem_range.1 (Finset.mem_product.1 hp).2)
    · exact ha i (Finset.mem_range.1 (Finset.mem_product.1 hp).2)
  have hneg2 : ∀ {x y : Lp ℝ 2 m}, x ∈ E.domain → y ∈ E.domain →
      E.form (-x) (-y) = E.form x y := fun hx hy => by
    rw [E.form_neg_left hx (E.domain.neg_mem hy), E.form_neg_right hx hy, neg_neg]
  have hpos : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → 0 ≤ E.form (F p) (F q) := by
    rintro ⟨_ | _, i⟩ _ ⟨_ | _, j⟩ _ hpq
    · have hij : i ≠ j := fun h' => hpq (by rw [h'])
      simp only [hFdef, Bool.false_eq_true, ↓reduceIte]
      rw [hneg2 (sliceLp_mem E h i hnu) (sliceLp_mem E h j hnu)]
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · exact form_sliceLp_sliceLp_nonneg E hnu hh hlt
      · rw [E.form_symm _ (sliceLp_mem E h i hnu) _ (sliceLp_mem E h j hnu)]
        exact form_sliceLp_sliceLp_nonneg E hnu hh hlt
    · simp only [hFdef, Bool.false_eq_true, ↓reduceIte]
      rw [E.form_symm _ (E.domain.neg_mem (sliceLp_mem E h i hnu)) _ (sliceLp_mem E h j hu)]
      exact form_sliceLp_neg_sliceLp_nonneg E hu hh j i
    · simp only [hFdef, Bool.false_eq_true, ↓reduceIte]
      exact form_sliceLp_neg_sliceLp_nonneg E hu hh i j
    · have hij : i ≠ j := fun h' => hpq (by rw [h'])
      simp only [hFdef, ↓reduceIte]
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · exact form_sliceLp_sliceLp_nonneg E hu hh hlt
      · rw [E.form_symm _ (sliceLp_mem E h i hu) _ (sliceLp_mem E h j hu)]
        exact form_sliceLp_sliceLp_nonneg E hu hh hlt
  -- the slices and the tail add up to `u`
  set T : Lp ℝ 2 m := tailLp ((N : ℝ) * h) u with hTdef
  have hTD : T ∈ E.domain := tailLp_mem E _ hu
  have hdecomp : (∑ p ∈ s, F p) + T = u := by
    rw [hsum]
    simp only [hFdef, Bool.false_eq_true, ↓reduceIte, Finset.sum_neg_distrib, sum_sliceLp,
      hTdef, tailLp]
    abel
  have hFT : 0 ≤ E.form (∑ p ∈ s, F p) T := by
    rw [E.form_sum_left s hFD hTD]
    refine Finset.sum_nonneg ?_
    rintro ⟨_ | _, i⟩ hp
    · have hiN : i < N := Finset.mem_range.1 (Finset.mem_product.1 hp).2
      simp only [hFdef, Bool.false_eq_true, ↓reduceIte]
      rw [← hneg2 (E.domain.neg_mem (sliceLp_mem E h i hnu)) hTD, neg_neg, hTdef,
        ← tailLp_neg]
      exact form_sliceLp_tailLp_nonneg E hnu hh hiN
    · have hiN : i < N := Finset.mem_range.1 (Finset.mem_product.1 hp).2
      exact form_sliceLp_tailLp_nonneg E hu hh hiN
  have hL : 0 ≤ L ^ 2 := sq_nonneg L
  have hmain := E.form_sum_smul_le s c hFD hcL hpos
  have hle := E.form_le_form_add (E.domain.sum_mem hFD) hTD hFT
  rw [hdecomp] at hle
  rw [hv]
  refine ⟨E.domain.sum_mem fun p hp => E.domain.smul_mem _ (hFD p hp), ?_⟩
  exact hmain.trans (mul_le_mul_of_nonneg_left hle hL)

/-! ### Piecewise-linear interpolation -/

section Interp

variable {Γ : ℝ → ℝ} {L : ℝ≥0} {h : ℝ}

/-- The slope of `Γ` on the `i`-th cell `[i h, (i + 1) h]`. -/
def slopeCoeff (Γ : ℝ → ℝ) (h : ℝ) (i : ℕ) : ℝ :=
  (Γ (((i : ℝ) + 1) * h) - Γ ((i : ℝ) * h)) / h

/-- The interpolant `∑_{i < M} slope_i · slice_i` of `Γ` on `[0, M h]`. -/
def sliceInterp (Γ : ℝ → ℝ) (h : ℝ) (M : ℕ) (r : ℝ) : ℝ :=
  ∑ i ∈ Finset.range M, slopeCoeff Γ h i * slice h i r

theorem abs_slopeCoeff_le (hΓ : LipschitzWith L Γ) (hh : 0 < h) (i : ℕ) :
    |slopeCoeff Γ h i| ≤ L := by
  have hd := hΓ.dist_le_mul (((i : ℝ) + 1) * h) ((i : ℝ) * h)
  rw [Real.dist_eq, Real.dist_eq, show ((i : ℝ) + 1) * h - (i : ℝ) * h = h by ring,
    abs_of_pos hh] at hd
  rw [slopeCoeff, abs_div, abs_of_pos hh, div_le_iff₀ hh]
  exact hd

theorem slice_of_mem {i : ℕ} {s : ℝ} (hh : 0 ≤ h) (h1 : (i : ℝ) * h ≤ s)
    (h2 : s ≤ ((i : ℝ) + 1) * h) : slice h i s = s - (i : ℝ) * h := by
  have ha0 : 0 ≤ (i : ℝ) * h := by positivity
  simp only [slice, ramp_of_ge ha0 h1, ramp_of_le (ha0.trans h1) h2]

theorem sliceInterp_of_nonpos (hh : 0 ≤ h) (M : ℕ) {r : ℝ} (hr : r ≤ 0) :
    sliceInterp Γ h M r = 0 :=
  Finset.sum_eq_zero fun i _ => by rw [slice_of_nonpos hh hr, mul_zero]

theorem sum_slice (M : ℕ) (r : ℝ) :
    ∑ i ∈ Finset.range M, slice h i r = ramp ((M : ℝ) * h) r := by
  have := Finset.sum_range_sub (fun i : ℕ => ramp ((i : ℝ) * h) r) M
  simp only [Nat.cast_add_one, Nat.cast_zero, zero_mul] at this
  rw [show ramp 0 r = 0 from max_eq_left (min_le_right r 0), sub_zero] at this
  exact this

theorem abs_sliceInterp_le (hΓ : LipschitzWith L Γ) (hh : 0 < h) (M : ℕ) (r : ℝ) :
    |sliceInterp Γ h M r| ≤ L * |r| := by
  calc |sliceInterp Γ h M r| ≤ ∑ i ∈ Finset.range M, |slopeCoeff Γ h i * slice h i r| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range M, (L : ℝ) * slice h i r := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (slice_nonneg hh.le)]
        exact mul_le_mul_of_nonneg_right (abs_slopeCoeff_le hΓ hh i) (slice_nonneg hh.le)
    _ = L * ramp ((M : ℝ) * h) r := by rw [← Finset.mul_sum, sum_slice]
    _ ≤ L * |r| := by
        refine mul_le_mul_of_nonneg_left ?_ L.coe_nonneg
        exact max_le (abs_nonneg r) ((min_le_left _ _).trans (le_abs_self r))

/-- **The interpolation estimate.**  On `[0, M h]` the interpolant is within `2 L h` of an
`L`-Lipschitz `Γ` with `Γ 0 = 0`, and beyond `M h` it is frozen at `Γ (M h)`. -/
theorem sliceInterp_spec (hΓ : LipschitzWith L Γ) (hΓ0 : Γ 0 = 0) (hh : 0 < h) (M : ℕ)
    {r : ℝ} (hr : 0 ≤ r) :
    ((M : ℝ) * h ≤ r → sliceInterp Γ h M r = Γ ((M : ℝ) * h)) ∧
      (r ≤ (M : ℝ) * h → |sliceInterp Γ h M r - Γ r| ≤ 2 * L * h) := by
  induction M with
  | zero =>
    simp only [sliceInterp, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul]
    refine ⟨fun _ => hΓ0.symm, fun hr0 => ?_⟩
    rw [le_antisymm hr0 hr, hΓ0, sub_zero, abs_zero]
    positivity
  | succ M ih =>
    have hsucc : sliceInterp Γ h (M + 1) r =
        sliceInterp Γ h M r + slopeCoeff Γ h M * slice h M r := Finset.sum_range_succ _ _
    push_cast
    rw [hsucc]
    constructor
    · intro hMr
      have hMr' : (M : ℝ) * h ≤ r := (mul_le_add_one_mul hh.le _).trans hMr
      rw [(ih.1 hMr'), slice_of_ge hh.le hMr, slopeCoeff, div_mul_cancel₀ _ hh.ne']
      ring
    · intro hrM
      rcases le_total r ((M : ℝ) * h) with hle | hle
      · rw [slice_of_le hh.le hle, mul_zero, add_zero]
        exact ih.2 hle
      · rw [ih.1 hle, slice_of_mem hh.le hle hrM]
        have hc := abs_slopeCoeff_le hΓ hh M
        have hd := hΓ.dist_le_mul ((M : ℝ) * h) r
        rw [Real.dist_eq, Real.dist_eq, abs_sub_comm ((M : ℝ) * h) r,
          abs_of_nonneg (sub_nonneg.2 hle)] at hd
        have hrh : r - (M : ℝ) * h ≤ h := by linarith
        have hnn : 0 ≤ r - (M : ℝ) * h := sub_nonneg.2 hle
        calc |Γ ((M : ℝ) * h) + slopeCoeff Γ h M * (r - (M : ℝ) * h) - Γ r|
            ≤ |Γ ((M : ℝ) * h) - Γ r| + |slopeCoeff Γ h M * (r - (M : ℝ) * h)| := by
              rw [show Γ ((M : ℝ) * h) + slopeCoeff Γ h M * (r - (M : ℝ) * h) - Γ r =
                (Γ ((M : ℝ) * h) - Γ r) + slopeCoeff Γ h M * (r - (M : ℝ) * h) by ring]
              exact abs_add_le _ _
          _ ≤ L * (r - (M : ℝ) * h) + L * (r - (M : ℝ) * h) := by
              rw [abs_mul, abs_of_nonneg hnn]
              exact add_le_add hd (mul_le_mul_of_nonneg_right hc hnn)
          _ ≤ 2 * L * h := by
              have := mul_le_mul_of_nonneg_left hrh L.coe_nonneg
              linarith

/-- The two-sided interpolant of `Γ`: `Γ` is interpolated on `[0, N h]` and
`r ↦ -Γ (-r)` on `[0, N h]` after reflection. -/
def twoSidedInterp (Γ : ℝ → ℝ) (h : ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  sliceInterp Γ h N s - sliceInterp (fun r => -Γ (-r)) h N (-s)

theorem lipschitzWith_neg_comp_neg (hΓ : LipschitzWith L Γ) :
    LipschitzWith L (fun r => -Γ (-r)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have := hΓ.dist_le_mul (-x) (-y)
  rw [dist_neg_neg] at this
  rwa [dist_neg_neg]

theorem abs_twoSidedInterp_sub_le (hΓ : LipschitzWith L Γ) (hΓ0 : Γ 0 = 0) (hh : 0 < h)
    (N : ℕ) {s : ℝ} (hs : |s| ≤ (N : ℝ) * h) : |twoSidedInterp Γ h N s - Γ s| ≤ 2 * L * h := by
  rcases le_total 0 s with h0 | h0
  · rw [twoSidedInterp, sliceInterp_of_nonpos hh.le N (neg_nonpos.2 h0), sub_zero]
    exact (sliceInterp_spec hΓ hΓ0 hh N h0).2 ((le_abs_self s).trans hs)
  · have hΓ' := lipschitzWith_neg_comp_neg hΓ
    have hΓ'0 : (fun r => -Γ (-r)) 0 = 0 := by simp [hΓ0]
    have := (sliceInterp_spec hΓ' hΓ'0 hh N (neg_nonneg.2 h0)).2 ((neg_le_abs s).trans hs)
    rw [twoSidedInterp, sliceInterp_of_nonpos hh.le N h0, zero_sub]
    simp only [neg_neg] at this
    rw [← abs_neg]
    convert this using 2
    ring

theorem abs_twoSidedInterp_sub_le_mul (hΓ : LipschitzWith L Γ) (hΓ0 : Γ 0 = 0) (hh : 0 < h)
    (N : ℕ) (s : ℝ) : |twoSidedInterp Γ h N s - Γ s| ≤ 3 * L * |s| := by
  have h1 := abs_sliceInterp_le hΓ hh N s
  have h2 := abs_sliceInterp_le (lipschitzWith_neg_comp_neg hΓ) hh N (-s)
  have h3 : |Γ s| ≤ L * |s| := by
    have := hΓ.dist_le_mul s 0
    rwa [Real.dist_eq, Real.dist_eq, hΓ0, sub_zero, sub_zero] at this
  rw [abs_neg] at h2
  calc |twoSidedInterp Γ h N s - Γ s|
      ≤ |sliceInterp Γ h N s| + |sliceInterp (fun r => -Γ (-r)) h N (-s)| + |Γ s| := by
        rw [twoSidedInterp]
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ 3 * L * |s| := by linarith

end Interp

/-! ### Convergence in `L²` of compositions -/

theorem coeFn_finset_sum {ι : Type*} (s : Finset ι) (F : ι → Lp ℝ 2 m) (f : ι → X → ℝ)
    (hF : ∀ i ∈ s, ⇑(F i) =ᵐ[m] f i) :
    ⇑(∑ i ∈ s, F i) =ᵐ[m] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx
    rw [Finset.sum_empty, hx, Finset.sum_empty, Pi.zero_apply]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, ⇑(F i) =ᵐ[m] f i := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), hF a (Finset.mem_insert_self a s),
      ih hs] with x h1 h2 h3
    rw [Finset.sum_insert ha, h1, Pi.add_apply, h2, h3, Finset.sum_insert ha]

theorem coeFn_sliceSum (h : ℝ) (N : ℕ) (a b : ℕ → ℝ) (u : Lp ℝ 2 m) :
    ⇑(sliceSum h N a b u) =ᵐ[m] fun x =>
      ∑ i ∈ Finset.range N, a i * slice h i (u x) -
        ∑ i ∈ Finset.range N, b i * slice h i (-u x) := by
  have h1 := coeFn_finset_sum (Finset.range N) (fun i => a i • sliceLp h i u)
    (fun i x => a i * slice h i (u x)) fun i _ => by
      filter_upwards [Lp.coeFn_smul (a i) (sliceLp h i u), coeFn_sliceLp h i u] with x e1 e2
      rw [e1, Pi.smul_apply, e2, smul_eq_mul]
  have h2 := coeFn_finset_sum (Finset.range N) (fun i => b i • (-sliceLp h i (-u)))
    (fun i x => -(b i * slice h i (-u x))) fun i _ => by
      filter_upwards [Lp.coeFn_smul (b i) (-sliceLp h i (-u)), Lp.coeFn_neg (sliceLp h i (-u)),
        coeFn_sliceLp h i (-u), Lp.coeFn_neg u] with x e1 e2 e3 e4
      rw [e1, Pi.smul_apply, e2, Pi.neg_apply, e3, e4, Pi.neg_apply, smul_eq_mul, mul_neg]
  filter_upwards [Lp.coeFn_add (∑ i ∈ Finset.range N, a i • sliceLp h i u)
    (∑ i ∈ Finset.range N, b i • (-sliceLp h i (-u))), h1, h2] with x e1 e2 e3
  rw [sliceSum, e1, Pi.add_apply, e2, e3, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- `‖f‖² = ∫ f²` in `L²`. -/
theorem norm_sq_eq_integral (f : Lp ℝ 2 m) : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂m := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [sq]

/-- **Dominated convergence for compositions in `L²`.**  If `Gₙ → G` pointwise with
`|Gₙ s - G s| ≤ K |s|`, then `Gₙ ∘ u → G ∘ u` in `L²`. -/
theorem tendsto_Lp_of_tendsto_comp {u : Lp ℝ 2 m} {Gs : ℕ → ℝ → ℝ} {G : ℝ → ℝ}
    {v : ℕ → Lp ℝ 2 m} {w : Lp ℝ 2 m} (hv : ∀ n, ⇑(v n) =ᵐ[m] fun x => Gs n (u x))
    (hw : ⇑w =ᵐ[m] fun x => G (u x)) (hlim : ∀ s, Tendsto (fun n => Gs n s) atTop (𝓝 (G s)))
    {K : ℝ} (hbd : ∀ n s, |Gs n s - G s| ≤ K * |s|) :
    Tendsto v atTop (𝓝 w) := by
  have hdiff : ∀ n, ⇑(v n - w) =ᵐ[m] fun x => Gs n (u x) - G (u x) := fun n => by
    filter_upwards [Lp.coeFn_sub (v n) w, hv n, hw] with x e1 e2 e3
    rw [e1, Pi.sub_apply, e2, e3]
  have hnorm : ∀ n, ‖v n - w‖ ^ 2 = ∫ x, (Gs n (u x) - G (u x)) ^ 2 ∂m := fun n => by
    rw [norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hdiff n] with x hx
    rw [hx]
  have hint : Tendsto (fun n => ∫ x, (Gs n (u x) - G (u x)) ^ 2 ∂m) atTop
      (𝓝 (∫ _x, (0 : ℝ) ∂m)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => K ^ 2 * u x ^ 2) (fun n => ?_)
      (((Lp.memLp u).integrable_sq).const_mul (K ^ 2)) (fun n => ?_) ?_
    · exact ((Lp.aestronglyMeasurable (v n - w)).pow 2).congr
        (by filter_upwards [hdiff n] with x hx; rw [Pi.pow_apply, hx])
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      show _ ≤ K ^ 2 * u x ^ 2
      rw [← sq_abs (u x), ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hbd n (u x)) 2
    · refine Eventually.of_forall fun x => ?_
      have := ((hlim (u x)).sub_const (G (u x))).pow 2
      rwa [sub_self, zero_pow two_ne_zero] at this
  rw [integral_zero] at hint
  have hsq : Tendsto (fun n => ‖v n - w‖ ^ 2) atTop (𝓝 0) := hint.congr fun n => (hnorm n).symm
  have hn : Tendsto (fun n => ‖v n - w‖) atTop (𝓝 0) := by
    have hc : Tendsto Real.sqrt (𝓝 0) (𝓝 0) := by simpa using Real.continuous_sqrt.tendsto 0
    refine (hc.comp hsq).congr fun n => ?_
    simp [Real.sqrt_sq (norm_nonneg _)]
  exact tendsto_iff_norm_sub_tendsto_zero.2 hn

/-! ### Lipschitz calculus (Fukushima–Oshima–Takeda, Theorem 1.4.1) -/

/-- **Lipschitz functions operate on a Dirichlet form.**  If `G` is `L`-Lipschitz with
`G 0 = 0` and `u ∈ D(E)`, then `G ∘ u ∈ D(E)` and `E(G ∘ u) ≤ L² E(u)`.

Only the unit contraction (the field `DirichletForm.markov`) and closedness are used:
`G` is interpolated on the grid of mesh `1/(n+1)` over `[-(n+1), n+1]`
(`sliceSum_mem_and_form_le`), the interpolants converge in `L²` by dominated convergence, and
closedness passes the uniform energy bound to the limit
(`ClosedForm.mem_domain_of_tendsto_of_form_le`).  For `L = 1` this is
Fukushima–Oshima–Takeda Theorem 1.4.1. -/
theorem lipschitz_comp_mem (E : DirichletForm m) {G : ℝ → ℝ} {L : ℝ≥0}
    (hG : LipschitzWith L G) (hG0 : G 0 = 0) {u : Lp ℝ 2 m} (hu : u ∈ E.domain)
    {w : Lp ℝ 2 m} (hw : ⇑w =ᵐ[m] fun x => G (u x)) :
    w ∈ E.domain ∧ E.form w w ≤ (L : ℝ) ^ 2 * E.form u u := by
  set G' : ℝ → ℝ := fun r => -G (-r) with hG'def
  have hG' : LipschitzWith L G' := lipschitzWith_neg_comp_neg hG
  set hn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hndef
  have hnpos : ∀ n, 0 < hn n := fun n => by positivity
  set Nn : ℕ → ℕ := fun n => (n + 1) ^ 2 with hNdef
  have hNh : ∀ n, ((Nn n : ℕ) : ℝ) * hn n = (n : ℝ) + 1 := fun n => by
    simp only [hNdef, hndef]
    push_cast
    field_simp
  set v : ℕ → Lp ℝ 2 m := fun n =>
    sliceSum (hn n) (Nn n) (slopeCoeff G (hn n)) (slopeCoeff G' (hn n)) u with hvdef
  have hvE : ∀ n, v n ∈ E.domain ∧ E.form (v n) (v n) ≤ (L : ℝ) ^ 2 * E.form u u := fun n =>
    sliceSum_mem_and_form_le E hu (hnpos n).le (Nn n) _ _
      (fun i _ => abs_slopeCoeff_le hG (hnpos n) i) (fun i _ => abs_slopeCoeff_le hG' (hnpos n) i)
  have hv : ∀ n, ⇑(v n) =ᵐ[m] fun x => twoSidedInterp G (hn n) (Nn n) (u x) := fun n => by
    filter_upwards [coeFn_sliceSum (hn n) (Nn n) (slopeCoeff G (hn n))
      (slopeCoeff G' (hn n)) u] with x hx
    rw [hx]
    rfl
  have hlim : ∀ s, Tendsto (fun n => twoSidedInterp G (hn n) (Nn n) s) atTop (𝓝 (G s)) := by
    intro s
    rw [tendsto_iff_dist_tendsto_zero]
    have hb : Tendsto (fun n : ℕ => 2 * (L : ℝ) * hn n) atTop (𝓝 (2 * L * 0)) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul _
    rw [mul_zero] at hb
    refine squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) ?_ hb
    filter_upwards [eventually_ge_atTop ⌈|s|⌉₊] with n hn'
    rw [Real.dist_eq]
    refine abs_twoSidedInterp_sub_le hG hG0 (hnpos n) (Nn n) ?_
    rw [hNh n]
    have := (Nat.le_ceil |s|).trans (Nat.cast_le.2 hn' : (⌈|s|⌉₊ : ℝ) ≤ n)
    linarith
  have hconv : Tendsto v atTop (𝓝 w) :=
    tendsto_Lp_of_tendsto_comp hv hw hlim fun n s =>
      abs_twoSidedInterp_sub_le_mul hG hG0 (hnpos n) (Nn n) s
  exact E.toClosedForm.mem_domain_of_tendsto_of_form_le (fun n => (hvE n).1) hconv
    fun n => (hvE n).2

/-- **Fukushima–Oshima–Takeda, Theorem 1.4.1.**  Every normal contraction operates on a
Dirichlet form; the library's input `HasNormalContractions` is therefore a theorem. -/
theorem hasNormalContractions (E : DirichletForm m) : HasNormalContractions E where
  operatesOn T hT u hu v hv := by
    have h := lipschitz_comp_mem E hT.lipschitzWith hT.map_zero hu hv
    simpa using h

/-! ### Products of bounded elements (Fukushima–Oshima–Takeda, Theorem 1.4.2(ii)) -/

/-- The clamped square `t ↦ (clamp(t, -K, K))²`. -/
def sqClamp (K : ℝ) (t : ℝ) : ℝ := max (-K) (min t K) ^ 2

theorem sqClamp_zero {K : ℝ} (hK : 0 ≤ K) : sqClamp K 0 = 0 := by
  simp [sqClamp, min_eq_left hK, max_eq_right (neg_nonpos.2 hK)]

theorem sqClamp_of_abs_le {K t : ℝ} (ht : |t| ≤ K) : sqClamp K t = t ^ 2 := by
  obtain ⟨h1, h2⟩ := abs_le.1 ht
  simp only [sqClamp, min_eq_left h2, max_eq_right h1]

theorem lipschitzWith_sqClamp (K : ℝ≥0) : LipschitzWith (2 * K) (sqClamp K) := by
  have hcl : LipschitzWith 1 fun t : ℝ => max (-(K : ℝ)) (min t K) :=
    by simpa using (LipschitzWith.const (-(K : ℝ))).max (LipschitzWith.id.min
      (LipschitzWith.const (K : ℝ)))
  have hbd : ∀ t : ℝ, |max (-(K : ℝ)) (min t K)| ≤ K := fun t =>
    abs_le.2 ⟨le_max_left _ _, max_le (neg_le_self K.coe_nonneg) (min_le_right _ _)⟩
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  have hd := hcl.dist_le_mul a b
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at hd
  rw [Real.dist_eq, Real.dist_eq, sqClamp, sqClamp, sq_sub_sq, abs_mul]
  push_cast
  have hsum : |max (-(K : ℝ)) (min a K) + max (-(K : ℝ)) (min b K)| ≤ 2 * K :=
    (abs_add_le _ _).trans (by linarith [hbd a, hbd b])
  exact mul_le_mul hsum hd (abs_nonneg _) (by positivity)

/-- **Products of bounded elements of the domain stay in the domain** (Fukushima–Oshima–Takeda
Theorem 1.4.2(ii)), by polarization `f g = ((f + g)² - (f - g)²) / 4` and the Lipschitz
calculus applied to a clamped square. -/
theorem exists_mul_mem (E : DirichletForm m) {f g : Lp ℝ 2 m} (hf : f ∈ E.domain)
    (hg : g ∈ E.domain) {M : ℝ} (hfM : ∀ᵐ x ∂m, |f x| ≤ M) (hgM : ∀ᵐ x ∂m, |g x| ≤ M) :
    ∃ w : Lp ℝ 2 m, w ∈ E.domain ∧ ⇑w =ᵐ[m] fun x => f x * g x := by
  set K : ℝ≥0 := ⟨2 * |M|, by positivity⟩ with hKdef
  have hK0 : sqClamp K 0 = 0 := sqClamp_zero K.coe_nonneg
  have hfg : ∀ᵐ x ∂m, |f x| ≤ |M| ∧ |g x| ≤ |M| := by
    filter_upwards [hfM, hgM] with x h1 h2
    exact ⟨h1.trans (le_abs_self M), h2.trans (le_abs_self M)⟩
  set A : Lp ℝ 2 m := (lipschitzWith_sqClamp K).compLp hK0 (f + g) with hAdef
  set B : Lp ℝ 2 m := (lipschitzWith_sqClamp K).compLp hK0 (f - g) with hBdef
  have hAe : ⇑A =ᵐ[m] fun x => sqClamp K ((f + g : Lp ℝ 2 m) x) :=
    LipschitzWith.coeFn_compLp _ _ _
  have hBe : ⇑B =ᵐ[m] fun x => sqClamp K ((f - g : Lp ℝ 2 m) x) :=
    LipschitzWith.coeFn_compLp _ _ _
  have hA := (lipschitz_comp_mem E (lipschitzWith_sqClamp K) hK0 (E.domain.add_mem hf hg)
    hAe).1
  have hB := (lipschitz_comp_mem E (lipschitzWith_sqClamp K) hK0 (E.domain.sub_mem hf hg)
    hBe).1
  refine ⟨(1 / 4 : ℝ) • (A - B), E.domain.smul_mem _ (E.domain.sub_mem hA hB), ?_⟩
  filter_upwards [Lp.coeFn_smul (1 / 4 : ℝ) (A - B), Lp.coeFn_sub A B, hAe, hBe,
    Lp.coeFn_add f g, Lp.coeFn_sub f g, hfg] with x e1 e2 e3 e4 e5 e6 hx
  have hsum : |f x + g x| ≤ (K : ℝ) := by
    show _ ≤ 2 * |M|
    exact (abs_add_le _ _).trans (by linarith [hx.1, hx.2])
  have hdiff : |f x - g x| ≤ (K : ℝ) := by
    show _ ≤ 2 * |M|
    exact (abs_sub _ _).trans (by linarith [hx.1, hx.2])
  rw [e1, Pi.smul_apply, e2, Pi.sub_apply, e3, e4, e5, e6, Pi.add_apply, Pi.sub_apply,
    sqClamp_of_abs_le hsum, sqClamp_of_abs_le hdiff, smul_eq_mul]
  ring

/-! ### `C¹` functions of bounded elements -/

/-- A `C¹` function of a bounded element of the domain, recentred to vanish at `0`, lies in the
domain: on the range of `u` the function is Lipschitz, and outside it is frozen by a clamp. -/
theorem exists_comp_sub_mem_of_contDiff (E : DirichletForm m) {Φ : ℝ → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) {u : Lp ℝ 2 m} (hu : u ∈ E.domain) {R : ℝ}
    (huR : ∀ᵐ x ∂m, |u x| ≤ R) :
    ∃ a : Lp ℝ 2 m, a ∈ E.domain ∧ ⇑a =ᵐ[m] fun x => Φ (u x) - Φ 0 := by
  set R₀ : ℝ := max R 0 with hR₀def
  have hR₀ : 0 ≤ R₀ := le_max_right _ _
  set cl : ℝ → ℝ := fun t => max (-R₀) (min t R₀) with hcldef
  have hclmem : ∀ t, cl t ∈ Icc (-R₀) R₀ := fun t =>
    ⟨le_max_left _ _, max_le (neg_le_self hR₀) (min_le_right _ _)⟩
  have hcl : LipschitzWith 1 cl := by
    simpa [hcldef] using (LipschitzWith.const (-R₀)).max (LipschitzWith.id.min
      (LipschitzWith.const R₀))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-R₀) R₀) (hΦ.continuous_deriv le_rfl).continuousOn
  set Ψ : ℝ → ℝ := fun t => Φ (cl t) - Φ 0 with hΨdef
  have hΨ : LipschitzWith (Real.toNNReal C) Ψ := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
      (fun x _ => (hΦ.differentiable le_rfl) x) hC (convex_Icc (-R₀) R₀) (hclmem b) (hclmem a)
    have hd := hcl.dist_le_mul a b
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at hd
    rw [Real.dist_eq, Real.dist_eq, show Ψ a - Ψ b = Φ (cl a) - Φ (cl b) by
      simp only [hΨdef]; ring]
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    calc |Φ (cl a) - Φ (cl b)| ≤ C * |cl a - cl b| := hmv
      _ ≤ Real.toNNReal C * |a - b| :=
        mul_le_mul (Real.le_coe_toNNReal C) hd (abs_nonneg _) (NNReal.coe_nonneg _)
  have hcl0 : cl 0 = 0 := by simp [hcldef, min_eq_left hR₀, max_eq_right (neg_nonpos.2 hR₀)]
  have hΨ0 : Ψ 0 = 0 := by simp [hΨdef, hcl0]
  set a : Lp ℝ 2 m := hΨ.compLp hΨ0 u
  have hae : ⇑a =ᵐ[m] fun x => Ψ (u x) := LipschitzWith.coeFn_compLp _ _ _
  refine ⟨a, (lipschitz_comp_mem E hΨ hΨ0 hu hae).1, ?_⟩
  filter_upwards [hae, huR] with x h1 h2
  obtain ⟨h3, h4⟩ := abs_le.1 (h2.trans (le_max_left R 0) : |u x| ≤ R₀)
  rw [h1]
  simp only [hΨdef, hcldef, min_eq_left h4, max_eq_right h3]

/-! ### The core algebra (Fukushima–Oshima–Takeda, Theorem 1.4.2) -/

section Core

variable [TopologicalSpace X]

theorem ae_abs_le_of_memCoreOn {E : ClosedForm m} {U : Set X} {u : Lp ℝ 2 m}
    (hu : E.MemCoreOn U u) : ∃ R : ℝ, ∀ᵐ x ∂m, |u x| ≤ R := by
  obtain ⟨-, f, hf, hfcs, -, hfae⟩ := hu
  obtain ⟨R, hR⟩ := hfcs.exists_bound_of_continuous hf
  refine ⟨R, ?_⟩
  filter_upwards [hfae] with x hx
  rw [hx, ← Real.norm_eq_abs]
  exact hR x

/-- **`v · Φ(u)` is a core function supported where `v` is** (Fukushima–Oshima–Takeda
Theorem 1.4.2; the form consumed by `mfd:lem-sincos`).  For every Dirichlet form, no
regularity needed: `Φ(u) - Φ(0)` lies in the domain by the Lipschitz calculus, its product with
the bounded `v` by polarization, and `vc · Φ(uc)` has a continuous representative supported in
`tsupport v ⊆ U`. -/
theorem exists_memCoreOn_mul_comp (E : DirichletForm m) (U : Set X) {u v : Lp ℝ 2 m}
    (hu : E.toClosedForm.MemCore u) (hv : E.toClosedForm.MemCoreOn U v) {uc vc : X → ℝ}
    (huae : ⇑u =ᵐ[m] uc) (hvae : ⇑v =ᵐ[m] vc) {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ) :
    ∃ w : Lp ℝ 2 m, E.toClosedForm.MemCoreOn U w ∧ ⇑w =ᵐ[m] fun x => vc x * Φ (uc x) := by
  obtain ⟨Ru, hRu⟩ := ae_abs_le_of_memCoreOn hu
  obtain ⟨Rv, hRv⟩ := ae_abs_le_of_memCoreOn hv
  obtain ⟨huD, fu, hfu, hfucs, -, hfuae⟩ := hu
  obtain ⟨hvD, fv, hfv, hfvcs, hfvU, hfvae⟩ := hv
  obtain ⟨a, haD, hae⟩ := exists_comp_sub_mem_of_contDiff E hΦ huD hRu
  -- `Φ(u) - Φ(0)` is bounded: it has a continuous compactly supported representative
  have hcs : HasCompactSupport fun x => Φ (fu x) - Φ 0 :=
    hfucs.comp_left (g := fun t => Φ t - Φ 0) (sub_self _)
  obtain ⟨Ra, hRa⟩ := hcs.exists_bound_of_continuous
    ((hΦ.continuous.comp hfu).sub continuous_const)
  have haR : ∀ᵐ x ∂m, |a x| ≤ max Rv Ra := by
    filter_upwards [hae, hfuae] with x h1 h2
    rw [h1, h2, ← Real.norm_eq_abs]
    exact (hRa x).trans (le_max_right _ _)
  have hvR : ∀ᵐ x ∂m, |v x| ≤ max Rv Ra := by
    filter_upwards [hRv] with x hx
    exact hx.trans (le_max_left _ _)
  obtain ⟨p, hpD, hpae⟩ := exists_mul_mem E hvD haD hvR haR
  set w : Lp ℝ 2 m := p + Φ 0 • v with hwdef
  have hwrep : ⇑w =ᵐ[m] fun x => fv x * Φ (fu x) := by
    filter_upwards [Lp.coeFn_add p (Φ 0 • v), Lp.coeFn_smul (Φ 0) v, hpae, hae, hfvae, hfuae]
      with x e1 e2 e3 e4 e5 e6
    rw [e1, Pi.add_apply, e2, Pi.smul_apply, e3, e4, smul_eq_mul, e5, e6]
    ring
  refine ⟨w, ⟨E.domain.add_mem hpD (E.domain.smul_mem _ hvD), fun x => fv x * Φ (fu x),
    hfv.mul (hΦ.continuous.comp hfu), hfvcs.mul_right, tsupport_mul_subset_left.trans hfvU,
    hwrep⟩, ?_⟩
  filter_upwards [hwrep, hfvae, hvae, hfuae, huae] with x e1 e2 e3 e4 e5
  rw [e1, ← e2, e3, ← e4, e5]

/-- `exists_memCoreOn_mul_comp` in exactly the shape of the `mul_comp_mem` clause of
`DirichletForm.IsCoreAlgebra` (and of the premise `hmul` of the `mfd:lem-sincos` argument);
continuity of the representatives and boundedness of `Φ` are not needed. -/
theorem mul_comp_mem (E : DirichletForm m) :
    ∀ (U : Set X) (u v : Lp ℝ 2 m), E.toClosedForm.MemCore u → E.toClosedForm.MemCoreOn U v →
    ∀ uc vc : X → ℝ, Continuous uc → Continuous vc → (⇑u =ᵐ[m] uc) → (⇑v =ᵐ[m] vc) →
    ∀ Φ : ℝ → ℝ, ContDiff ℝ 1 Φ → (∃ M : ℝ, ∀ t : ℝ, |Φ t| ≤ M) →
    ∃ w : Lp ℝ 2 m, E.toClosedForm.MemCoreOn U w ∧ (⇑w =ᵐ[m] fun x => vc x * Φ (uc x)) :=
  fun U _ _ hu hv _ _ _ _ huae hvae _ hΦ _ => exists_memCoreOn_mul_comp E U hu hv huae hvae hΦ

/-- The core `D(E) ∩ C_c(X)` is stable under products. -/
theorem mul_mem (E : DirichletForm m) :
    ∀ u v : Lp ℝ 2 m, E.toClosedForm.MemCore u → E.toClosedForm.MemCore v →
    ∃ w : Lp ℝ 2 m, E.toClosedForm.MemCore w ∧ (⇑w =ᵐ[m] fun x => u x * v x) := by
  intro u v hu hv
  obtain ⟨Ru, hRu⟩ := ae_abs_le_of_memCoreOn hu
  obtain ⟨Rv, hRv⟩ := ae_abs_le_of_memCoreOn hv
  obtain ⟨huD, fu, hfu, hfucs, -, hfuae⟩ := hu
  obtain ⟨hvD, fv, hfv, -, -, hfvae⟩ := hv
  obtain ⟨w, hwD, hwae⟩ := exists_mul_mem E huD hvD (M := max Ru Rv)
    (by filter_upwards [hRu] with x hx; exact hx.trans (le_max_left _ _))
    (by filter_upwards [hRv] with x hx; exact hx.trans (le_max_right _ _))
  refine ⟨w, ⟨hwD, fun x => fu x * fv x, hfu.mul hfv, hfucs.mul_right, subset_univ _, ?_⟩, hwae⟩
  filter_upwards [hwae, hfuae, hfvae] with x e1 e2 e3
  rw [e1, e2, e3]

/-- The core `D(E) ∩ C_c(X)` is stable under `C¹` functions vanishing at `0`. -/
theorem comp_mem (E : DirichletForm m) :
    ∀ u : Lp ℝ 2 m, E.toClosedForm.MemCore u → ∀ Φ : ℝ → ℝ, ContDiff ℝ 1 Φ → Φ 0 = 0 →
    ∃ w : Lp ℝ 2 m, E.toClosedForm.MemCore w ∧ (⇑w =ᵐ[m] fun x => Φ (u x)) := by
  intro u hu Φ hΦ hΦ0
  obtain ⟨Ru, hRu⟩ := ae_abs_le_of_memCoreOn hu
  obtain ⟨huD, fu, hfu, hfucs, -, hfuae⟩ := hu
  obtain ⟨a, haD, hae⟩ := exists_comp_sub_mem_of_contDiff E hΦ huD hRu
  have hae' : ⇑a =ᵐ[m] fun x => Φ (u x) := by
    filter_upwards [hae] with x hx
    rw [hx, hΦ0, sub_zero]
  refine ⟨a, ⟨haD, fun x => Φ (fu x), hΦ.continuous.comp hfu, hfucs.comp_left hΦ0,
    subset_univ _, ?_⟩, hae'⟩
  filter_upwards [hae', hfuae] with x e1 e2
  rw [e1, e2]

/-- Fukushima–Oshima–Takeda Theorem 1.4.2(ii): a bounded element of the domain times a core
function supported in `U` is a core function supported in `U`. -/
theorem mul_mem_of_bounded (E : DirichletForm m) :
    ∀ (U : Set X) (u v : Lp ℝ 2 m), u ∈ E.domain →
    ∀ uc : X → ℝ, Continuous uc → (⇑u =ᵐ[m] uc) → (∃ M : ℝ, ∀ x : X, |uc x| ≤ M) →
    E.toClosedForm.MemCoreOn U v → ∀ vc : X → ℝ, Continuous vc → (⇑v =ᵐ[m] vc) →
    ∃ w : Lp ℝ 2 m, E.toClosedForm.MemCoreOn U w ∧ (⇑w =ᵐ[m] fun x => uc x * vc x) := by
  intro U u v huD uc huc huae ⟨M, hM⟩ hv vc _ hvae
  obtain ⟨Rv, hRv⟩ := ae_abs_le_of_memCoreOn hv
  obtain ⟨hvD, fv, hfv, hfvcs, hfvU, hfvae⟩ := hv
  obtain ⟨w, hwD, hwae⟩ := exists_mul_mem E huD hvD (M := max M Rv)
    (by filter_upwards [huae] with x hx; rw [hx]; exact (hM x).trans (le_max_left _ _))
    (by filter_upwards [hRv] with x hx; exact hx.trans (le_max_right _ _))
  refine ⟨w, ⟨hwD, fun x => uc x * fv x, huc.mul hfv, hfvcs.mul_left,
    tsupport_mul_subset_right.trans hfvU, ?_⟩, ?_⟩
  · filter_upwards [hwae, huae, hfvae] with x e1 e2 e3
    rw [e1, e2, e3]
  · filter_upwards [hwae, huae, hvae] with x e1 e2 e3
    rw [e1, e2, e3]

end Core

end DirichletForm
