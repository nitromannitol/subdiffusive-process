module

public import SubdiffusiveProcess.Section7.Defs.PerStartKolmogorovRegular

@[expose] public section

/-!
# Mass loss away from the starting point is incompatible with Kolmogorov regularity

The frozen Section 7 statement specifies the process by two clauses on a kernel
`law` into `MarkovProcess.LifetimePath (State d)`:

* `coordinateLaw`, which pins every **one-time** marginal of `law` to the
  cemetery extension of the transition kernel, and
* `kolmogorovRegularAt`, which asks for a Kolmogorov--Chentsov moment bound with
  time exponent `q > 1` on the process `t ↦ lifetimeValue x t path`, that is on
  the live position with the cemetery replaced by the starting point `x`.

This module proves that the two clauses interact: the second one **forbids** the
semigroup from losing mass at a positive rate at a time at which its live mass
sits at a positive distance from the starting point.  The mechanism is that a
path which dies between `s` and `t` contributes `dist (X_s) x` to the increment
`lifetimeValue x s - lifetimeValue x t`, so the probability of dying in a short
window is paid at the first power of the window length, whereas the Kolmogorov
condition prices it at the power `q > 1`.

## Main declarations

* `ofReal_rpow_mul_le_lintegral_edist_lifetimeValue` — the quantitative lower
  bound on the Kolmogorov integrand from the one-time marginals alone.
* `mass_bound_of_isKolmogorovProcess` — the resulting necessary condition on the
  transition kernels.
* `not_isKolmogorovProcess_of_massLoss` — no Kolmogorov process at all when the
  mass is lost at a linear rate away from the starting point.

Nothing here needs a semigroup structure: the statements are about two
transition kernels, read at the two times `s` and `t`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section7Process

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open _root_.SubdiffusiveProcess.Section7
open scoped ENNReal NNReal Topology

noncomputable section

variable {d : ℕ}

/-- The live states at distance at least `r` from the starting point. -/
def farSet (x : State d) (r : ℝ) : Set (State d) := {y | r ≤ dist y x}

theorem measurableSet_farSet (x : State d) (r : ℝ) : MeasurableSet (farSet x r) :=
  (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet

/-- The live value of a lifetime path at a time at which it is alive. -/
theorem lifetimeValue_of_coordinate_eq_alive {x : State d} {t : NNReal}
    {path : LifetimePath (State d)} {y : State d}
    (h : LifetimePath.coordinate t path = Cemetery.alive y) :
    lifetimeValue x t path = y := by
  simp only [lifetimeValue, h]

/-- The live value of a lifetime path at a time at which it is dead is the
fallback state. -/
theorem lifetimeValue_of_coordinate_eq_delta {x : State d} {t : NNReal}
    {path : LifetimePath (State d)}
    (h : LifetimePath.coordinate t path = Cemetery.delta) :
    lifetimeValue x t path = x := by
  simp only [lifetimeValue, h]

/-- **The quantitative lower bound.**  If the one-time marginals of `mu` at the
two times `s` and `t` are the cemetery extensions of `nus` and `nut` started at
`x`, then the `p`-th moment of the increment of `lifetimeValue x · path` between
`s` and `t` is at least `r ^ p` times the mass which is alive far from `x` at
time `s` and dead at time `t`. -/
theorem ofReal_rpow_mul_le_lintegral_edist_lifetimeValue
    (mu : Measure (LifetimePath (State d))) [IsProbabilityMeasure mu]
    (nus nut : Kernel (State d) (State d)) (x : State d) {s t : NNReal} {r p : ℝ}
    (hp : 0 ≤ p)
    (hsmarg : mu.map (LifetimePath.coordinate s) =
      Kernel.cemeteryExtension nus (Cemetery.alive x))
    (htmarg : mu.map (LifetimePath.coordinate t) =
      Kernel.cemeteryExtension nut (Cemetery.alive x)) :
    ENNReal.ofReal r ^ p * (nus x (farSet x r) - nut x Set.univ)
      ≤ ∫⁻ path, edist (lifetimeValue x s path) (lifetimeValue x t path) ^ p ∂mu := by
  classical
  set A : Set (LifetimePath (State d)) :=
    LifetimePath.coordinate s ⁻¹' (Cemetery.alive '' farSet x r) with hA
  set B : Set (LifetimePath (State d)) :=
    LifetimePath.coordinate t ⁻¹' (Cemetery.alive '' (Set.univ : Set (State d))) with hB
  have hAmeas : MeasurableSet A :=
    (LifetimePath.measurable_coordinate s) (measurableSet_farSet x r).inl_image
  have hBmeas : MeasurableSet B :=
    (LifetimePath.measurable_coordinate t) MeasurableSet.univ.inl_image
  have hAmass : mu A = nus x (farSet x r) := by
    rw [hA, ← Measure.map_apply (LifetimePath.measurable_coordinate s)
      (measurableSet_farSet x r).inl_image, hsmarg]
    exact Kernel.cemeteryExtension_alive_image nus x (measurableSet_farSet x r)
  have hBmass : mu B = nut x Set.univ := by
    rw [hB, ← Measure.map_apply (LifetimePath.measurable_coordinate t)
      MeasurableSet.univ.inl_image, htmarg]
    exact Kernel.cemeteryExtension_alive_image nut x MeasurableSet.univ
  -- the far-alive-then-dead event
  have hsub : mu A ≤ mu (A ∩ Bᶜ) + mu B := by
    refine le_trans (measure_mono (?_ : A ⊆ (A ∩ Bᶜ) ∪ B)) (measure_union_le _ _)
    intro path hpath
    by_cases hb : path ∈ B
    · exact Or.inr hb
    · exact Or.inl ⟨hpath, hb⟩
  have hdiff : nus x (farSet x r) - nut x Set.univ ≤ mu (A ∩ Bᶜ) := by
    rw [← hAmass, ← hBmass]
    exact tsub_le_iff_right.mpr hsub
  -- the pointwise bound on the event
  have hpoint : ∀ path : LifetimePath (State d), path ∈ A ∩ Bᶜ →
      ENNReal.ofReal r ^ p ≤ edist (lifetimeValue x s path) (lifetimeValue x t path) ^ p := by
    rintro path ⟨hpA, hpB⟩
    obtain ⟨y, hy, hyeq⟩ := hpA
    have hs' : lifetimeValue x s path = y := lifetimeValue_of_coordinate_eq_alive hyeq.symm
    have hdelta : LifetimePath.coordinate t path = Cemetery.delta := by
      rcases hcoord : LifetimePath.coordinate t path with z | u
      · exact absurd (show path ∈ B from ⟨z, Set.mem_univ z, hcoord.symm⟩) hpB
      · cases u; rfl
    have ht' : lifetimeValue x t path = x := lifetimeValue_of_coordinate_eq_delta hdelta
    rw [hs', ht']
    refine ENNReal.rpow_le_rpow ?_ hp
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hy
  -- integrate
  calc ENNReal.ofReal r ^ p * (nus x (farSet x r) - nut x Set.univ)
      ≤ ENNReal.ofReal r ^ p * mu (A ∩ Bᶜ) := by gcongr
    _ = ∫⁻ path, (A ∩ Bᶜ).indicator (fun _ ↦ ENNReal.ofReal r ^ p) path ∂mu := by
        rw [lintegral_indicator_const (hAmeas.inter hBmeas.compl)]
    _ ≤ ∫⁻ path, edist (lifetimeValue x s path) (lifetimeValue x t path) ^ p ∂mu := by
        refine lintegral_mono fun path ↦ ?_
        by_cases hpath : path ∈ A ∩ Bᶜ
        · rw [Set.indicator_of_mem hpath]
          exact hpoint path hpath
        · rw [Set.indicator_of_notMem hpath]
          exact bot_le

/-- **The necessary condition on the transition kernels.**  A Kolmogorov process
with the prescribed one-time marginals prices the mass which is alive far from
`x` at time `s` and dead at time `t` at the Kolmogorov rate. -/
theorem mass_bound_of_isKolmogorovProcess
    (mu : Measure (LifetimePath (State d))) [IsProbabilityMeasure mu]
    (nus nut : Kernel (State d) (State d)) (x : State d) {s t : NNReal} {r p q : ℝ} {M : ℝ≥0}
    (hp : 0 ≤ p)
    (hsmarg : mu.map (LifetimePath.coordinate s) =
      Kernel.cemeteryExtension nus (Cemetery.alive x))
    (htmarg : mu.map (LifetimePath.coordinate t) =
      Kernel.cemeteryExtension nut (Cemetery.alive x))
    (hKol : IsKolmogorovProcess (fun u path ↦ lifetimeValue x u path) mu p q M) :
    ENNReal.ofReal r ^ p * (nus x (farSet x r) - nut x Set.univ) ≤ M * edist s t ^ q :=
  le_trans
    (ofReal_rpow_mul_le_lintegral_edist_lifetimeValue mu nus nut x hp hsmarg htmarg)
    (hKol.kolmogorovCondition s t)

/-! ### Infinite lifetime under conservativity -/

/-- **A conservative family forces an infinite lifetime.**  If every one-time
marginal is the cemetery extension of a *Markov* transition kernel started at the
live point, then almost every path is nonexplosive.  This is the exact sense in
which the frozen `coordinateLaw` clause, together with the manuscript's
conservativity theorem, makes the cemetery presentation of Section 7 vacuous. -/
theorem ae_lifetime_eq_top_of_conservative
    (mu : Measure (LifetimePath (State d))) (nu : NNReal → Kernel (State d) (State d))
    (x : State d)
    (hmarg : ∀ t : NNReal, mu.map (LifetimePath.coordinate t) =
      Kernel.cemeteryExtension (nu t) (Cemetery.alive x))
    (hcons : ∀ t : NNReal, nu t x Set.univ = 1) :
    ∀ᵐ path ∂mu, path.lifetime = ∞ := by
  have hdelta : MeasurableSet ({Cemetery.delta} : Set (Cemetery (State d))) := by
    simpa only [Set.range_unique] using!
      (measurableSet_range_inr :
        MeasurableSet (Set.range (Sum.inr : Unit → State d ⊕ Unit)))
  have hnull : ∀ t : NNReal,
      mu (LifetimePath.coordinate t ⁻¹' ({Cemetery.delta} : Set (Cemetery (State d)))) = 0 := by
    intro t
    rw [← Measure.map_apply (LifetimePath.measurable_coordinate t) hdelta, hmarg t,
      Kernel.cemeteryExtension_alive_singleton_delta, hcons t, tsub_self]
  rw [Filter.eventually_iff, mem_ae_iff]
  refine measure_mono_null (fun path hpath ↦ ?_)
    (measure_iUnion_null (fun n : ℕ ↦ hnull (n : NNReal)))
  have hne : path.lifetime ≠ ∞ := by
    simpa using! hpath
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hne
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  refine LifetimePath.coordinate_of_le path (n : NNReal) ?_
  simpa using! hn.le

/-- **The no-go.**  If, at some parameter and some starting point `x`, the
transition kernels lose mass at a linear rate along a sequence of times shrinking
to `s`, while at time `s` a fixed positive amount of live mass sits at distance
at least `r > 0` from `x`, then no kernel with the prescribed one-time marginals
can be per-start Kolmogorov regular.

This is the exact tension between the two frozen clauses: dying costs the full
displacement `dist (X_s) x`, and dying in a window of length `h` has probability
of order `h`, whereas the Kolmogorov condition prices increments at `h ^ q` with
`q > 1`. -/
theorem not_perStartKolmogorovRegular_of_massLoss
    {Theta : Type*} [MeasurableSpace Theta]
    (K : Kernel (Theta × State d) (LifetimePath (State d))) [IsMarkovKernel K]
    (nu : NNReal → Kernel (State d) (State d)) (theta : Theta) (x : State d)
    (hmarg : ∀ t : NNReal, (K (theta, x)).map (LifetimePath.coordinate t) =
        Kernel.cemeteryExtension (nu t) (Cemetery.alive x))
    {r c : ℝ} (hr : 0 < r) (hc : 0 < c) (s : NNReal)
    (u : ℕ → NNReal) (hupos : ∀ n, 0 < u n)
    (hulim : Tendsto (fun n ↦ ((u n : ℝ))) atTop (nhds 0))
    (hloss : ∀ n, ENNReal.ofReal (c * (u n : ℝ)) ≤
      nu s x (farSet x r) - nu (s + u n) x Set.univ) :
    ¬ PerStartKolmogorovRegular K := by
  intro hreg
  obtain ⟨p, q, gamma, M, hKol, hgamma0, hgamma⟩ := hreg theta x
  have hp : 0 < p := hKol.p_pos
  have hquot : 0 < (q - 1) / p := lt_trans hgamma0 hgamma
  have hq1 : 0 < q - 1 := by
    have hmul := mul_pos hquot hp
    rwa [div_mul_cancel₀ _ (ne_of_gt hp)] at hmul
  set K0 : ℝ≥0∞ := ENNReal.ofReal r ^ p * ENNReal.ofReal c with hK0
  have hK0pos : 0 < K0 := by
    refine ENNReal.mul_pos (ne_of_gt ?_) (ne_of_gt (ENNReal.ofReal_pos.mpr hc))
    exact ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hr) ENNReal.ofReal_ne_top
  have hK0top : K0 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  -- the Kolmogorov price of dying between `s` and `s + u n`
  have hstep : ∀ n, K0 ≤ (M : ℝ≥0∞) * (u n : ℝ≥0∞) ^ (q - 1) := by
    intro n
    have hbase : (u n : ℝ≥0∞) ≠ 0 := by
      simpa using! (hupos n).ne'
    have hbasetop : (u n : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have hmain :=
      mass_bound_of_isKolmogorovProcess (K (theta, x)) (nu s) (nu (s + u n)) x
        (r := r) (q := q) (M := M) hp.le (hmarg s) (hmarg (s + u n)) hKol
    have hedist : edist s (s + u n) = (u n : ℝ≥0∞) := by
      rw [edist_dist, NNReal.dist_eq]
      push_cast
      rw [abs_of_nonpos (by linarith [(u n).coe_nonneg] : (s : ℝ) - ((s : ℝ) + (u n : ℝ)) ≤ 0)]
      simp
    rw [hedist] at hmain
    have hleft : K0 * (u n : ℝ≥0∞) ≤ ENNReal.ofReal r ^ p *
        (nu s x (farSet x r) - nu (s + u n) x Set.univ) := by
      have hrewrite : K0 * (u n : ℝ≥0∞) =
          ENNReal.ofReal r ^ p * ENNReal.ofReal (c * (u n : ℝ)) := by
        rw [hK0, ENNReal.ofReal_mul hc.le, ENNReal.ofReal_coe_nnreal, mul_assoc]
      rw [hrewrite]
      gcongr
      exact hloss n
    have hsplit : (u n : ℝ≥0∞) ^ q = (u n : ℝ≥0∞) ^ (q - 1) * (u n : ℝ≥0∞) := by
      conv_lhs => rw [show q = (q - 1) + 1 by ring]
      rw [ENNReal.rpow_add _ _ hbase hbasetop, ENNReal.rpow_one]
    have hchain : K0 * (u n : ℝ≥0∞) ≤ ((M : ℝ≥0∞) * (u n : ℝ≥0∞) ^ (q - 1)) * (u n : ℝ≥0∞) := by
      refine le_trans (le_trans hleft hmain) (le_of_eq ?_)
      rw [hsplit, mul_assoc]
    exact (ENNReal.mul_le_mul_iff_left hbase hbasetop).mp hchain
  -- pass to the real line and let the window shrink
  have hstepreal : ∀ n, K0.toReal ≤ (M : ℝ) * (u n : ℝ) ^ (q - 1) := by
    intro n
    have h := hstep n
    have hcoe : ((M : ℝ≥0∞) * (u n : ℝ≥0∞) ^ (q - 1)) =
        ENNReal.ofReal ((M : ℝ) * (u n : ℝ) ^ (q - 1)) := by
      rw [ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_rpow_of_nonneg (u n).coe_nonneg hq1.le,
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
    rw [hcoe] at h
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
  have hlim : Tendsto (fun n ↦ (M : ℝ) * (u n : ℝ) ^ (q - 1)) atTop (nhds 0) := by
    have hrpow : Tendsto (fun n ↦ ((u n : ℝ)) ^ (q - 1)) atTop (nhds 0) := by
      have hcont : ContinuousAt (fun y : ℝ ↦ y ^ (q - 1)) 0 :=
        Real.continuousAt_rpow_const 0 (q - 1) (Or.inr hq1.le)
      have := hcont.tendsto.comp hulim
      simpa [Real.zero_rpow (ne_of_gt hq1)] using! this
    simpa using! hrpow.const_mul (M : ℝ)
  have hle : K0.toReal ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hstepreal)
  have hpos : 0 < K0.toReal := ENNReal.toReal_pos (ne_of_gt hK0pos) hK0top
  exact absurd hle (not_le.mpr hpos)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section7Process
