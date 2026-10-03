module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKDatumCarrier

@[expose] public section

/-!
# The whole-space killed density, from the killed densities on a ball exhaustion

`LocalDiffusionData c rho law` carries `HasContinuousKilledDensityOn rho law U` for every
**bounded** open `U`, while the amended Section 10 kernel anchors
(`t.heat.kernel.upper`, `t.weighted.heat.kernel.diagonal.lower`,
`t.fixed.clock.heat.kernel.offdiag`, `t.weighted.heat.kernel.offdiag.lower`,
`l.weighted.near.diagonal.lower`, `l.weighted.overlapping.cubes.semigroup`) quantify over
`p` with `IsKilledDensity law rho Set.univ p` **and** joint continuity on
`Ioi 0 ×ˢ univ ×ˢ univ`.  Nothing in the tree produced such a `p`, so those statements were
non-vacuous only on paper.  This file builds it, as the monotone limit of the killed
densities on an exhaustion by balls.

## What is proved here, from the tree alone

* `exitTime_univ_eq_lifetime`, `exitTime_mono_set` and `iSup_exitTime_eq_lifetime` — the path
  layer.  The last is the nonexplosion step, and it needs **no** hypothesis: a `LifetimePath`
  is continuous on `[0, lifetime)`, so the image of `[0, T]` is compact for every
  `T < lifetime`, hence bounded, hence inside some member of the exhaustion.  The exit times
  therefore rise to the lifetime, which `exitTime_univ_eq_lifetime` identifies with the exit
  time from `Set.univ`.
* `killedZeroExt` and its lemmas — the killed densities normalized to vanish off `U × U`, so
  that the family can be compared and summed pointwise.  `IsKilledDensity` constrains a
  density only on `U`, so this normalization is free.
* `killedZeroExt_mono` — **domain monotonicity**, from the tree alone: the killed law of the
  smaller set is dominated by that of the larger one because `exitTime` is monotone in the
  set, so the two densities are ordered almost everywhere
  (`ae_le_of_forall_setLIntegral_le_of_sigmaFinite`), and continuity plus full support
  (`HeatKernelRegularity.le_of_ae_le`, `RRKDatumCarrier.fullSupportOn_weightedMeasure_restrict`)
  raise that to every point.
* `exists_monotoneKilledFamily` — the package the tree delivers with no extra input at all:
  a ball exhaustion and a monotone family of killed densities on it, each jointly continuous
  and vanishing off its own box.
* `exists_isKilledDensity_univ_of_family` — the limit.  Given the family and the regularity
  input below, `p := ⨆ j, q j` is a whole-space killed density, jointly continuous on
  `Ioi 0 ×ˢ univ ×ˢ univ`.
* `exists_wholeSpaceKilledDensity` — the two combined, as an existence lemma a provider can
  `obtain` from.

## The one input the tree does not have

`LocallyEquicontinuousKilledFamily` — the family `q` is locally bounded and
**equicontinuous** on `Ioi 0 ×ˢ univ ×ˢ univ`, uniformly in `j`.  This cannot be dispensed
with and cannot be derived from what is here: an increasing limit of continuous functions is
only lower semicontinuous, and the two clauses are exactly what turns pointwise convergence
into continuity of the limit (`continuousAt_of_equicontinuous_of_tendsto`).  Its analytic
content is interior parabolic regularity for `∂_t u = a^{-1} ∇·(a ∇u)` with constants
depending only on a compact neighbourhood — available for a locally `C^{1,1}` coefficient
with locally two-sided ellipticity, which `CoefficientC11On` and `CoefficientOn` supply on
each ball, but not yet formalized in this tree or in `CoarseGraining`.  It is stated here in
its weakest usable form: no modulus, no rate, no uniformity beyond a neighbourhood of each
point.

The *boundedness* clause is the finiteness of the whole-space kernel and is equally absent:
the tree's on-diagonal upper bound `t.heat.kernel.upper` is itself `DRAFT_SORRY`.
-/

set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.HeatKernelRegularity
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.KilledDensityExistence
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.RRKDatumCarrier
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section10

variable {d : ℕ} {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}

/-! ## The path layer -/

/-- The exit time from the whole space is the lifetime. -/
theorem exitTime_univ_eq_lifetime (w : Path d) :
    LifetimePath.exitTime (Set.univ : Set (Vec d)) w = w.lifetime := by
  refine le_antisymm (LifetimePath.exitTime_le_lifetime _ w) ?_
  refine le_sInf ?_
  rintro s ⟨t, rfl, ht⟩
  by_contra hlt
  push_neg at hlt
  exact ht ⟨w.livePath ⟨t, hlt⟩, Set.mem_univ _, (LifetimePath.coordinate_of_lt w t hlt).symm⟩

/-- Exit times are monotone in the set. -/
theorem exitTime_mono_set {U V : Set (Vec d)} (hUV : U ⊆ V) (w : Path d) :
    LifetimePath.exitTime U w ≤ LifetimePath.exitTime V w := by
  refine sInf_le_sInf ?_
  rintro s ⟨t, rfl, ht⟩
  refine ⟨t, rfl, fun hmem => ht ?_⟩
  obtain ⟨z, hz, hzeq⟩ := hmem
  exact ⟨z, hUV hz, hzeq⟩

/-- A family of sets absorbing every bounded set. -/
def AbsorbsBounded (D : ℕ → Set (Vec d)) : Prop :=
  ∀ S : Set (Vec d), Bornology.IsBounded S → ∃ j, S ⊆ D j

/-- **Nonexplosion along an exhaustion.**  The exit times of a lifetime path from the members
of a family absorbing every bounded set rise to its lifetime: the live path is continuous on
`[0, lifetime)`, so the image of any `[0, T]` with `T < lifetime` is compact, hence bounded,
hence inside one member. -/
theorem iSup_exitTime_eq_lifetime {D : ℕ → Set (Vec d)} (habs : AbsorbsBounded D)
    (w : Path d) :
    ⨆ j, LifetimePath.exitTime (D j) w = w.lifetime := by
  refine le_antisymm (iSup_le fun j => LifetimePath.exitTime_le_lifetime _ w) ?_
  refine ENNReal.le_of_forall_nnreal_lt fun T hT => ?_
  set phi : Set.Icc (0 : NNReal) T → Vec d :=
    fun u => w.livePath ⟨u.1, lt_of_le_of_lt (by exact_mod_cast u.2.2) hT⟩ with hphi
  have hcont : Continuous phi :=
    w.continuous_livePath.comp (Continuous.subtype_mk continuous_subtype_val _)
  have hcompact : IsCompact (Set.range phi) := isCompact_range hcont
  obtain ⟨j, hj⟩ := habs _ hcompact.isBounded
  refine le_iSup_of_le j (le_sInf ?_)
  rintro s ⟨t, rfl, ht⟩
  by_contra hlt
  push_neg at hlt
  have htT : t ≤ T := by exact_mod_cast hlt.le
  have htlife : (t : ENNReal) < w.lifetime := lt_of_le_of_lt (by exact_mod_cast htT) hT
  exact ht ⟨w.livePath ⟨t, htlife⟩, hj ⟨⟨t, ⟨bot_le, htT⟩⟩, rfl⟩,
    (LifetimePath.coordinate_of_lt w t htlife).symm⟩

/-! ## The ball exhaustion -/

/-- The exhaustion of `Vec d` by the balls of integer radius about the origin. -/
def ballFamily (d : ℕ) (j : ℕ) : Set (Vec d) := Metric.ball (0 : Vec d) (j + 1)

theorem isOpen_ballFamily (j : ℕ) : IsOpen (ballFamily d j) := Metric.isOpen_ball

theorem isBounded_ballFamily (j : ℕ) : Bornology.IsBounded (ballFamily d j) :=
  Metric.isBounded_ball

theorem monotone_ballFamily : Monotone (ballFamily d) := by
  intro i j hij
  refine Metric.ball_subset_ball ?_
  exact_mod_cast Nat.add_le_add_right hij 1

theorem absorbsBounded_ballFamily : AbsorbsBounded (ballFamily d) := by
  intro S hS
  obtain ⟨r, hr⟩ := hS.subset_ball (0 : Vec d)
  obtain ⟨j, hj⟩ := exists_nat_gt r
  exact ⟨j, hr.trans (Metric.ball_subset_ball (by linarith))⟩

theorem iUnion_ballFamily : ⋃ j, ballFamily d j = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨j, hj⟩ := absorbsBounded_ballFamily {x} (Bornology.isBounded_singleton)
  exact Set.mem_iUnion.2 ⟨j, hj rfl⟩

/-! ## The killed densities, normalized off their own box -/

/-- A killed density extended by zero off `U × U`. -/
def killedZeroExt (U : Set (Vec d)) (p : ℝ → Vec d → Vec d → ℝ) (t : ℝ) (x y : Vec d) : ℝ :=
  (U ×ˢ U).indicator (fun z : Vec d × Vec d => p t z.1 z.2) (x, y)

theorem killedZeroExt_of_mem {U : Set (Vec d)} {p : ℝ → Vec d → Vec d → ℝ} {t : ℝ}
    {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) : killedZeroExt U p t x y = p t x y :=
  Set.indicator_of_mem (Set.mk_mem_prod hx hy) _

theorem killedZeroExt_of_notMem {U : Set (Vec d)} {p : ℝ → Vec d → Vec d → ℝ} {t : ℝ}
    {x y : Vec d} (h : x ∉ U ∨ y ∉ U) : killedZeroExt U p t x y = 0 := by
  refine Set.indicator_of_notMem ?_ _
  rcases h with h | h
  · exact fun hmem => h hmem.1
  · exact fun hmem => h hmem.2

theorem measurable_uncurry_killedZeroExt {U : Set (Vec d)} (hU : MeasurableSet U)
    {p : ℝ → Vec d → Vec d → ℝ} {t : ℝ} (hp : Measurable (Function.uncurry (p t))) :
    Measurable (Function.uncurry (killedZeroExt U p t)) := by
  have h : Function.uncurry (killedZeroExt U p t)
      = (U ×ˢ U).indicator (Function.uncurry (p t)) := rfl
  rw [h]
  exact hp.indicator (hU.prod hU)

theorem isKilledDensity_killedZeroExt {U : Set (Vec d)} (hU : MeasurableSet U)
    {p : ℝ → Vec d → Vec d → ℝ} (hp : IsKilledDensity law rho U p) :
    IsKilledDensity law rho U (killedZeroExt U p) := by
  refine ⟨fun t ht => measurable_uncurry_killedZeroExt hU (hp.1 t ht), ?_, ?_⟩
  · intro t ht x hx y hy
    rw [killedZeroExt_of_mem hx hy]
    exact hp.2.1 t ht x hx y hy
  · intro t ht x hx B hB
    rw [hp.2.2 t ht x hx B hB]
    refine setLIntegral_congr_fun (hB.inter hU) (fun y hy => ?_)
    rw [killedZeroExt_of_mem hx hy.2]

theorem continuousOn_killedZeroExt {U : Set (Vec d)} {p : ℝ → Vec d → Vec d → ℝ}
    (hp : ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ U ×ˢ U)) :
    ContinuousOn (fun z : ℝ × Vec d × Vec d => killedZeroExt U p z.1 z.2.1 z.2.2)
      (Ioi 0 ×ˢ U ×ˢ U) :=
  hp.congr fun _ hz => killedZeroExt_of_mem hz.2.1 hz.2.2

theorem killedZeroExt_nonneg {U : Set (Vec d)} {p : ℝ → Vec d → Vec d → ℝ}
    (hp : IsKilledDensity law rho U p) {t : ℝ} (ht : 0 < t) (x y : Vec d) :
    0 ≤ killedZeroExt U p t x y := by
  by_cases hx : x ∈ U
  · by_cases hy : y ∈ U
    · rw [killedZeroExt_of_mem hx hy]; exact hp.2.1 t ht x hx y hy
    · rw [killedZeroExt_of_notMem (Or.inr hy)]
  · rw [killedZeroExt_of_notMem (Or.inl hx)]

/-- The slice of a jointly continuous kernel at a fixed time and starting point. -/
theorem continuousOn_slice {U : Set (Vec d)} {p : ℝ → Vec d → Vec d → ℝ}
    (hc : ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ U ×ˢ U))
    {t : ℝ} (ht : 0 < t) {x : Vec d} (hx : x ∈ U) :
    ContinuousOn (fun y => p t x y) U := by
  have hmap : Continuous fun y : Vec d => ((t, x, y) : ℝ × Vec d × Vec d) := by fun_prop
  exact hc.comp hmap.continuousOn (fun y hy => ⟨ht, hx, hy⟩)

/-! ## Domain monotonicity -/

/-- **Domain monotonicity of the killed densities**, from the tree alone.  The killed law of
the smaller set is dominated by that of the larger, so the densities are ordered almost
everywhere; continuity and full support raise that to every point. -/
theorem killedZeroExt_mono {U V : Set (Vec d)} (hUV : U ⊆ V)
    (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hLD : LocalDiffusion c rho law)
    {pU pV : ℝ → Vec d → Vec d → ℝ}
    (hpU : IsKilledDensity law rho U pU) (hpV : IsKilledDensity law rho V pV)
    (hcU : ContinuousOn (fun z : ℝ × Vec d × Vec d => pU z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ U ×ˢ U))
    (hcV : ContinuousOn (fun z : ℝ × Vec d × Vec d => pV z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ V ×ˢ V))
    {t : ℝ} (ht : 0 < t) (x y : Vec d) :
    killedZeroExt U pU t x y ≤ killedZeroExt V pV t x y := by
  classical
  by_cases hx : x ∈ U
  · by_cases hy : y ∈ U
    · rw [killedZeroExt_of_mem hx hy, killedZeroExt_of_mem (hUV hx) (hUV hy)]
      have hrhoU : CoefficientOn U rho := coefficientOn_of_localDiffusion hLD hUbdd
      have hfin : (weightedMeasure rho) U ≠ ∞ := weightedMeasure_ne_top hrhoU hUopen hUbdd
      haveI : IsFiniteMeasure ((weightedMeasure rho).restrict U) := isFiniteMeasure_restrict hfin
      set mu := (weightedMeasure rho).restrict U with hmu
      have hmeasU : MeasurableSet U := hUopen.measurableSet
      have hfU : Measurable fun y => ENNReal.ofReal (pU t x y) := by
        have h1 : Measurable fun y : Vec d => ((x, y) : Vec d × Vec d) :=
          measurable_const.prodMk measurable_id
        exact ENNReal.measurable_ofReal.comp ((hpU.1 t ht).comp h1)
      have hae : (fun y => ENNReal.ofReal (pU t x y)) ≤ᵐ[mu]
          fun y => ENNReal.ofReal (pV t x y) := by
        refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hfU ?_
        intro s hs _
        have hsU : MeasurableSet (s ∩ U) := hs.inter hmeasU
        have e1 : ∫⁻ y in s, ENNReal.ofReal (pU t x y) ∂mu
            = ∫⁻ y in (s ∩ U) ∩ U, ENNReal.ofReal (pU t x y)
                ∂(volume.withDensity fun y => ENNReal.ofReal (rho y)) := by
          rw [hmu, Measure.restrict_restrict hs, Set.inter_assoc, Set.inter_self]
          rfl
        have e2 : ∫⁻ y in s, ENNReal.ofReal (pV t x y) ∂mu
            = ∫⁻ y in (s ∩ U) ∩ V, ENNReal.ofReal (pV t x y)
                ∂(volume.withDensity fun y => ENNReal.ofReal (rho y)) := by
          rw [hmu, Measure.restrict_restrict hs,
            Set.inter_eq_self_of_subset_left (Set.inter_subset_right.trans hUV)]
          rfl
        rw [e1, e2, ← hpU.2.2 t ht x hx (s ∩ U) hsU, ← hpV.2.2 t ht x (hUV hx) (s ∩ U) hsU]
        exact measure_mono fun w hw => ⟨lt_of_lt_of_le hw.1 (exitTime_mono_set hUV w), hw.2⟩
      have hsupp : FullSupportOn mu U := fullSupportOn_weightedMeasure_restrict hUopen hrhoU
      have hcont : ContinuousOn (fun y => pU t x y - pV t x y) U :=
        (continuousOn_slice hcU ht hx).sub ((continuousOn_slice hcV ht (hUV hx)).mono hUV)
      have hkey : ∀ z ∈ U, pU t x z - pV t x z ≤ 0 := by
        refine le_of_ae_le hUopen hsupp hcont ?_
        filter_upwards [hae] with z hz
        intro hzU
        have hnn : 0 ≤ pV t x z := hpV.2.1 t ht x (hUV hx) z (hUV hzU)
        have := (ENNReal.ofReal_le_ofReal_iff hnn).mp hz
        linarith
      linarith [hkey y hy]
    · rw [killedZeroExt_of_notMem (Or.inr hy)]
      exact killedZeroExt_nonneg hpV ht x y
  · rw [killedZeroExt_of_notMem (Or.inl hx)]
    exact killedZeroExt_nonneg hpV ht x y

/-! ## The family the tree delivers -/

/-- **What `LocalDiffusionData` gives with no further input**: a monotone family of jointly
continuous killed densities on the ball exhaustion, each vanishing off its own box. -/
theorem exists_monotoneKilledFamily (hD : LocalDiffusionData c rho law) :
    ∃ q : ℕ → ℝ → Vec d → Vec d → ℝ,
      (∀ j, IsKilledDensity law rho (ballFamily d j) (q j)) ∧
      (∀ j, ContinuousOn (fun z : ℝ × Vec d × Vec d => q j z.1 z.2.1 z.2.2)
        (Ioi 0 ×ˢ ballFamily d j ×ˢ ballFamily d j)) ∧
      (∀ j t x y, (x ∉ ballFamily d j ∨ y ∉ ballFamily d j) → q j t x y = 0) ∧
      (∀ j t, 0 < t → ∀ x y, q j t x y ≤ q (j + 1) t x y) := by
  choose p hp hpc using fun j =>
    hD.2 (ballFamily d j) (isOpen_ballFamily j) (isBounded_ballFamily j)
  refine ⟨fun j => killedZeroExt (ballFamily d j) (p j), ?_, ?_, ?_, ?_⟩
  · exact fun j => isKilledDensity_killedZeroExt (isOpen_ballFamily j).measurableSet (hp j)
  · exact fun j => continuousOn_killedZeroExt (hpc j)
  · exact fun j t x y h => killedZeroExt_of_notMem h
  · intro j t ht x y
    exact killedZeroExt_mono (monotone_ballFamily (Nat.le_succ j)) (isOpen_ballFamily j)
      (isBounded_ballFamily j) hD.1 (hp j) (hp (j + 1)) (hpc j) (hpc (j + 1)) ht x y

/-! ## The regularity input the tree does not have -/

/-- **The one input this construction cannot supply.**  The killed family is locally bounded
and equicontinuous on `Ioi 0 ×ˢ univ ×ˢ univ`, uniformly in the exhaustion index.

Both clauses are needed and neither follows from what is above: an increasing limit of
continuous functions is only lower semicontinuous, and the supremum of an unbounded family of
reals is Mathlib's junk value.  Their analytic content is interior parabolic regularity for
`∂_t u = a⁻¹ ∇·(a ∇u)`, with constants depending only on a compact neighbourhood, together
with the local finiteness of the whole-space kernel. -/
structure LocallyEquicontinuousKilledFamily (q : ℕ → ℝ → Vec d → Vec d → ℝ) : Prop where
  /-- The values at a point are bounded along the exhaustion. -/
  bddAbove : ∀ t : ℝ, 0 < t → ∀ x y : Vec d, BddAbove (Set.range fun j => q j t x y)
  /-- The family is equicontinuous at each point of the open domain. -/
  equicontinuous : ∀ t : ℝ, 0 < t → ∀ x y : Vec d, ∀ ε : ℝ, 0 < ε →
    ∀ᶠ z : ℝ × Vec d × Vec d in 𝓝 (t, x, y),
      ∀ j : ℕ, |q j z.1 z.2.1 z.2.2 - q j t x y| ≤ ε

/-! ## The limit -/

/-- Two monotone sequences agreeing on a tail have the same supremum. -/
theorem iSup_eq_iSup_of_eventually_eq {f g : ℕ → ENNReal} (hf : Monotone f) (hg : Monotone g)
    {j0 : ℕ} (h : ∀ j, j0 ≤ j → f j = g j) : ⨆ j, f j = ⨆ j, g j := by
  refine le_antisymm (iSup_le fun j => ?_) (iSup_le fun j => ?_)
  · refine le_trans (hf (le_max_left j j0)) ?_
    rw [h _ (le_max_right j j0)]
    exact le_iSup g _
  · refine le_trans (hg (le_max_left j j0)) ?_
    rw [← h _ (le_max_right j j0)]
    exact le_iSup f _

/-- **An equicontinuous family with a pointwise limit has a continuous limit.**  The
three-term estimate, with the index chosen after the point. -/
theorem continuousOn_of_equicontinuous_of_tendsto
    {q : ℕ → ℝ × Vec d × Vec d → ℝ} {F : ℝ × Vec d × Vec d → ℝ}
    {dom : Set (ℝ × Vec d × Vec d)} (hdom : IsOpen dom)
    (hconv : ∀ z ∈ dom, Tendsto (fun j => q j z) atTop (𝓝 (F z)))
    (hequi : ∀ z ∈ dom, ∀ ε : ℝ, 0 < ε → ∀ᶠ z' in 𝓝 z, ∀ j, |q j z' - q j z| ≤ ε) :
    ContinuousOn F dom := by
  intro z hz
  refine ContinuousAt.continuousWithinAt ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hquarter : (0 : ℝ) < ε / 4 := by linarith
  filter_upwards [hequi z hz (ε / 4) hquarter, hdom.mem_nhds hz] with z' hz' hz'dom
  have e1 : ∀ᶠ j in atTop, dist (q j z') (F z') ≤ ε / 4 :=
    (hconv z' hz'dom).eventually (Metric.closedBall_mem_nhds (F z') hquarter)
  have e2 : ∀ᶠ j in atTop, dist (q j z) (F z) ≤ ε / 4 :=
    (hconv z hz).eventually (Metric.closedBall_mem_nhds (F z) hquarter)
  obtain ⟨j, hj1, hj2⟩ := (e1.and e2).exists
  rw [Real.dist_eq] at hj1 hj2 ⊢
  have h3 := hz' j
  have hsplit : |F z' - F z|
      ≤ |F z' - q j z'| + |q j z' - q j z| + |q j z - F z| := by
    have := abs_sub_abs_le_abs_sub (F z' - q j z') (F z - q j z)
    calc |F z' - F z| = |(F z' - q j z') + (q j z' - q j z) + (q j z - F z)| := by ring_nf
      _ ≤ |(F z' - q j z') + (q j z' - q j z)| + |q j z - F z| := abs_add_le _ _
      _ ≤ |F z' - q j z'| + |q j z' - q j z| + |q j z - F z| := by
          have := abs_add_le (F z' - q j z') (q j z' - q j z)
          linarith
  rw [abs_sub_comm (F z') (q j z')] at hsplit
  linarith

/-- **The whole-space killed density, from a monotone killed family on an exhaustion.**  The
limit is a killed density at `Set.univ` and is jointly continuous on `Ioi 0 ×ˢ univ ×ˢ univ`,
which is exactly what the amended Section 10 kernel anchors quantify over. -/
theorem exists_isKilledDensity_univ_of_family
    {D : ℕ → Set (Vec d)} (hDopen : ∀ j, IsOpen (D j)) (hDmono : Monotone D)
    (hDabs : AbsorbsBounded D)
    {q : ℕ → ℝ → Vec d → Vec d → ℝ}
    (hq : ∀ j, IsKilledDensity law rho (D j) (q j))
    (hqz : ∀ j t x y, (x ∉ D j ∨ y ∉ D j) → q j t x y = 0)
    (hqm : ∀ j t, 0 < t → ∀ x y, q j t x y ≤ q (j + 1) t x y)
    (hreg : LocallyEquicontinuousKilledFamily q) :
    ∃ p : ℝ → Vec d → Vec d → ℝ,
      IsKilledDensity law rho Set.univ p ∧
      ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2)
        (Ioi 0 ×ˢ (Set.univ : Set (Vec d)) ×ˢ (Set.univ : Set (Vec d))) := by
  classical
  set p : ℝ → Vec d → Vec d → ℝ := fun t x y => ⨆ j, q j t x y with hpdef
  have hmonoj : ∀ t : ℝ, 0 < t → ∀ x y : Vec d, Monotone fun j => q j t x y :=
    fun t ht x y => monotone_nat_of_le_succ fun j => hqm j t ht x y
  have htend : ∀ t : ℝ, 0 < t → ∀ x y : Vec d,
      Tendsto (fun j => q j t x y) atTop (𝓝 (p t x y)) :=
    fun t ht x y => tendsto_atTop_ciSup (hmonoj t ht x y) (hreg.bddAbove t ht x y)
  have hle : ∀ (j : ℕ) (t : ℝ), 0 < t → ∀ x y : Vec d, q j t x y ≤ p t x y :=
    fun j t ht x y => le_ciSup (hreg.bddAbove t ht x y) j
  refine ⟨p, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- measurability
    intro t ht
    refine measurable_of_tendsto_metrizable (fun j => (hq j).1 t ht) ?_
    exact tendsto_pi_nhds.mpr fun z => htend t ht z.1 z.2
  · -- nonnegativity
    intro t ht x _ y _
    obtain ⟨j, hj⟩ := hDabs {x, y} (Set.toFinite _).isBounded
    exact le_trans ((hq j).2.1 t ht x (hj (by simp)) y (hj (by simp))) (hle j t ht x y)
  · -- the killed identity at `Set.univ`
    intro t ht x _ B hB
    obtain ⟨j0, hj0⟩ := hDabs {x} (Set.finite_singleton x).isBounded
    have hxj : ∀ j, j0 ≤ j → x ∈ D j := fun j hj => hDmono hj (hj0 rfl)
    set mu : Measure (Vec d) := volume.withDensity (fun y => ENNReal.ofReal (rho y)) with hmu
    set E : ℕ → Set (Path d) := fun j =>
      {w | ENNReal.ofReal t < LifetimePath.exitTime (D j) w ∧
        LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' B} with hE
    have hEmono : Monotone E := by
      intro i j hij w hw
      exact ⟨lt_of_lt_of_le hw.1 (exitTime_mono_set (hDmono hij) w), hw.2⟩
    have hEunion : ⋃ j, E j =
        {w | ENNReal.ofReal t < LifetimePath.exitTime Set.univ w ∧
          LifetimePath.coordinate (Real.toNNReal t) w ∈ Cemetery.alive '' B} := by
      ext w
      simp only [hE, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨j, hlt, hcoord⟩
        exact ⟨lt_of_lt_of_le hlt (exitTime_mono_set (Set.subset_univ _) w), hcoord⟩
      · rintro ⟨hlt, hcoord⟩
        rw [exitTime_univ_eq_lifetime, ← iSup_exitTime_eq_lifetime hDabs w, lt_iSup_iff] at hlt
        obtain ⟨j, hj⟩ := hlt
        exact ⟨j, hj, hcoord⟩
    -- the left side is the increasing limit of the killed masses
    have hLHS : law x (⋃ j, E j) = ⨆ j, law x (E j) := by
      refine tendsto_nhds_unique (tendsto_measure_iUnion_atTop hEmono) ?_
      exact tendsto_atTop_iSup fun i j hij => measure_mono (hEmono hij)
    -- the right side is the increasing limit of the killed integrals
    have hofReal : ∀ y : Vec d,
        ENNReal.ofReal (p t x y) = ⨆ j, ENNReal.ofReal (q j t x y) := by
      intro y
      refine tendsto_nhds_unique ((ENNReal.continuous_ofReal.tendsto _).comp (htend t ht x y)) ?_
      exact tendsto_atTop_iSup fun i j hij => ENNReal.ofReal_le_ofReal (hmonoj t ht x y hij)
    have hmeasq : ∀ j : ℕ, Measurable fun y : Vec d => ENNReal.ofReal (q j t x y) := by
      intro j
      have h1 : Measurable fun y : Vec d => ((x, y) : Vec d × Vec d) :=
        measurable_const.prodMk measurable_id
      exact ENNReal.measurable_ofReal.comp (((hq j).1 t ht).comp h1)
    have hRHS : ∫⁻ y in B ∩ Set.univ, ENNReal.ofReal (p t x y) ∂mu
        = ⨆ j, ∫⁻ y in B, ENNReal.ofReal (q j t x y) ∂mu := by
      rw [Set.inter_univ]
      have : ∀ y : Vec d, ENNReal.ofReal (p t x y)
          = ⨆ j, (fun j : ℕ => fun y : Vec d => ENNReal.ofReal (q j t x y)) j y :=
        fun y => hofReal y
      simp only [this]
      exact lintegral_iSup hmeasq fun i j hij y => ENNReal.ofReal_le_ofReal (hmonoj t ht x y hij)
    -- and the two agree from `j0` on
    have hstep : ∀ j, j0 ≤ j → law x (E j) = ∫⁻ y in B, ENNReal.ofReal (q j t x y) ∂mu := by
      intro j hj
      have hind : (fun y : Vec d => ENNReal.ofReal (q j t x y))
          = (D j).indicator fun y : Vec d => ENNReal.ofReal (q j t x y) := by
        funext y
        by_cases hy : y ∈ D j
        · rw [Set.indicator_of_mem hy]
        · rw [Set.indicator_of_notMem hy, hqz j t x y (Or.inr hy), ENNReal.ofReal_zero]
      rw [hind, lintegral_indicator (hDopen j).measurableSet,
        Measure.restrict_restrict (hDopen j).measurableSet, Set.inter_comm (D j) B]
      exact (hq j).2.2 t ht x (hxj j hj) B hB
    rw [← hEunion, hLHS, hRHS]
    exact iSup_eq_iSup_of_eventually_eq (fun i j hij => measure_mono (hEmono hij))
      (fun i j hij => lintegral_mono fun y =>
        ENNReal.ofReal_le_ofReal (hmonoj t ht x y hij)) hstep
  · -- joint continuity of the limit
    refine continuousOn_of_equicontinuous_of_tendsto
      (q := fun j z => q j z.1 z.2.1 z.2.2) (F := fun z => p z.1 z.2.1 z.2.2)
      (isOpen_Ioi.prod (isOpen_univ.prod isOpen_univ)) (fun z hz => htend z.1 hz.1 z.2.1 z.2.2)
      (fun z hz ε hε => hreg.equicontinuous z.1 hz.1 z.2.1 z.2.2 ε hε)

/-- **The packaged existence lemma.**  From `LocalDiffusionData` and the regularity input on
the ball exhaustion, a whole-space killed density that is jointly continuous on
`Ioi 0 ×ˢ univ ×ˢ univ`. -/
theorem exists_wholeSpaceKilledDensity (hD : LocalDiffusionData c rho law)
    (hreg : ∀ q : ℕ → ℝ → Vec d → Vec d → ℝ,
      (∀ j, IsKilledDensity law rho (ballFamily d j) (q j)) →
      (∀ j, ContinuousOn (fun z : ℝ × Vec d × Vec d => q j z.1 z.2.1 z.2.2)
        (Ioi 0 ×ˢ ballFamily d j ×ˢ ballFamily d j)) →
      LocallyEquicontinuousKilledFamily q) :
    ∃ p : ℝ → Vec d → Vec d → ℝ,
      IsKilledDensity law rho Set.univ p ∧
      ContinuousOn (fun z : ℝ × Vec d × Vec d => p z.1 z.2.1 z.2.2)
        (Ioi 0 ×ˢ (Set.univ : Set (Vec d)) ×ˢ (Set.univ : Set (Vec d))) := by
  obtain ⟨q, hq, hqc, hqz, hqm⟩ := exists_monotoneKilledFamily hD
  exact exists_isKilledDensity_univ_of_family isOpen_ballFamily monotone_ballFamily
    absorbsBounded_ballFamily hq hqz hqm (hreg q hq hqc)


end SubdiffusiveProcess.CoarseGrainingVocab.Section10

end
