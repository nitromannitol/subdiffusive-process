import SubdiffusiveProcess.Probability.Diffusion.Packet452Stationarity

/-!
# P-452 route, target (iv): `relativeExhaustionGoal`, discharged

`ledger/reports/P-452-agent1.md` §2.5 and §4.  This is the fourth of the six targets in the
report's proof order, and it is the one that needs no stochastic analysis at all.

* `exitTime_mono` — the exit time is monotone in the domain, directly from its `sInf` definition.
  (The tree had this only for `LifetimePath`, in `Section10.exitTime_mono_set`.)
* `le_exitTime_of_forall_mem` — a path that stays in `W` up to `T` has exit time at least `T`.
* `iSup_exitTime_eq_of_exhaustion` — for any increasing family absorbing the compact subsets of
  `U`, the exit times rise to the exit time from `U`.  This is the **relative-domain** version of
  `Section10.iSup_exitTime_eq_lifetime`, which the report's §5 lists as the missing piece (A7 in
  the old route); the argument is the same one: the path image on `[0,T]` is compact and inside
  `U`, hence inside some member of the family.
* `relativeExhaustion`, `relativeExhaustionGoal_holds` — the construction.  `U` bounded open is
  exhausted by `{x | (n+1)⁻¹ < dist(x, Uᶜ)} ∩ ball 0 (n+1)`.  The degenerate case `Uᶜ = ∅` is
  handled separately: it forces `U = univ` with `univ` bounded, so the ambient space is compact and
  the constant family works.  That case is real only in dimension zero, but the target quantifies
  over all `d`.

Convergence of the exit times is then monotone convergence to the `iSup`, so no continuity of the
exit-time functional and no regularity of `∂U` is used anywhere.
-/

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter Metric
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Probability.Diffusion.Packet452Route

variable {d : ℕ}

/-! ## Exit-time monotonicity and the exhaustion limit -/

/-- The exit time is monotone in the domain. -/
theorem exitTime_mono {V U : Set (Vec d)} (hVU : V ⊆ U) (w : ContinuousPath (Vec d)) :
    ContinuousPath.exitTime V w ≤ ContinuousPath.exitTime U w := by
  refine sInf_le_sInf fun s hs => ?_
  obtain ⟨t, rfl, ht⟩ := hs
  exact ⟨t, rfl, fun hmem => ht (hVU hmem)⟩

/-- If the path stays in `W` up to `T`, its exit time from `W` is at least `T`. -/
theorem le_exitTime_of_forall_mem {W : Set (Vec d)} {w : ContinuousPath (Vec d)} {T : NNReal}
    (h : ∀ t : NNReal, t ≤ T → w t ∈ W) :
    (T : ℝ≥0∞) ≤ ContinuousPath.exitTime W w := by
  refine le_sInf ?_
  rintro s ⟨t, rfl, ht⟩
  by_contra hlt
  push_neg at hlt
  exact ht (h t (by exact_mod_cast hlt.le))

/-- **The exhaustion limit.**  For an increasing family absorbing the compact subsets of `U`, the
exit times rise to the exit time from `U`.  The argument is the relative-domain version of
`Section10.iSup_exitTime_eq_lifetime`: the path image on `[0, T]` is compact and inside `U`, hence
inside some member. -/
theorem iSup_exitTime_eq_of_exhaustion {U : Set (Vec d)} {V : ℕ → Set (Vec d)}
    (hsub : ∀ n, V n ⊆ U)
    (habs : ∀ K : Set (Vec d), IsCompact K → K ⊆ U → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ⊆ V n)
    (w : ContinuousPath (Vec d)) :
    ⨆ n, ContinuousPath.exitTime (V n) w = ContinuousPath.exitTime U w := by
  refine le_antisymm (iSup_le fun n => exitTime_mono (hsub n) w) ?_
  refine ENNReal.le_of_forall_nnreal_lt fun T hT => ?_
  have hmem : ∀ t : NNReal, t ≤ T → w t ∈ U := by
    intro t htT
    refine ContinuousPath.mem_of_lt_exitTime U w t (lt_of_le_of_lt ?_ hT)
    exact_mod_cast htT
  set K : Set (Vec d) := w '' (Icc 0 T) with hK
  have hKcompact : IsCompact K := (isCompact_Icc (a := (0:NNReal)) (b := T)).image w.continuous
  have hKU : K ⊆ U := by
    rintro z ⟨t, ht, rfl⟩
    exact hmem t ht.2
  obtain ⟨N, hN⟩ := habs K hKcompact hKU
  refine le_iSup_of_le N (le_exitTime_of_forall_mem fun t htT => ?_)
  exact hN N le_rfl ⟨t, ⟨bot_le, htT⟩, rfl⟩

/-! ## The relative exhaustion -/

/-- **`relativeExhaustionGoal`.**  Every bounded open set carries an increasing exhaustion by open
sets with compact closure inside it, absorbing every compact subset, along which the exit times
converge.  No regularity of the frontier is used. -/
theorem relativeExhaustion (U : Set (Vec d)) (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ V : ℕ → Set (Vec d),
      (∀ n, IsOpen (V n) ∧ IsCompact (closure (V n)) ∧ closure (V n) ⊆ U ∧
        closure (V n) ⊆ V (n + 1)) ∧
      (∀ K : Set (Vec d), IsCompact K → K ⊆ U →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ⊆ V n) ∧
      ∀ w : ContinuousPath (Vec d),
        Tendsto (fun n => ContinuousPath.exitTime (V n) w) atTop
          (𝓝 (ContinuousPath.exitTime U w)) := by
  classical
  by_cases hUc : (Uᶜ : Set (Vec d)) = ∅
  · have hUuniv : U = univ := by rwa [Set.compl_empty_iff] at hUc
    refine ⟨fun _ => univ, fun n => ⟨isOpen_univ, ?_, ?_, ?_⟩,
      fun K _ _ => ⟨0, fun n _ => subset_univ K⟩, fun w => ?_⟩
    · rw [closure_univ]
      refine Metric.isCompact_of_isClosed_isBounded isClosed_univ ?_
      rw [← hUuniv]
      exact hUb
    · simp [hUuniv]
    · simp
    · rw [hUuniv]
      exact tendsto_const_nhds
  · have hUcne : (Uᶜ : Set (Vec d)).Nonempty := Set.nonempty_iff_ne_empty.mpr hUc
    have hUcclosed : IsClosed (Uᶜ : Set (Vec d)) := hU.isClosed_compl
    set f : Vec d → ℝ := fun x => Metric.infDist x (Uᶜ : Set (Vec d)) with hf
    have hfcont : Continuous f := Metric.continuous_infDist_pt _
    set V : ℕ → Set (Vec d) := fun n =>
      {x | ((n : ℝ) + 1)⁻¹ < f x} ∩ Metric.ball (0 : Vec d) ((n : ℝ) + 1) with hV
    have hinv : ∀ n : ℕ, (((n : ℝ) + 1) + 1)⁻¹ < ((n : ℝ) + 1)⁻¹ := by
      intro n
      have h := one_div_lt_one_div_of_lt (by positivity : (0:ℝ) < (n : ℝ) + 1)
        (by linarith : ((n : ℝ) + 1) < ((n : ℝ) + 1) + 1)
      rwa [one_div, one_div] at h
    have hVball : ∀ n, closure (V n) ⊆ Metric.closedBall (0 : Vec d) ((n : ℝ) + 1) :=
      fun n => closure_minimal (fun x hx => Metric.ball_subset_closedBall hx.2)
        Metric.isClosed_closedBall
    have hVlevel : ∀ n, closure (V n) ⊆ {x | ((n : ℝ) + 1)⁻¹ ≤ f x} := by
      intro n
      refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_const hfcont)
      have h : ((n : ℝ) + 1)⁻¹ < f x := hx.1
      exact le_of_lt h
    have hVU : ∀ n, closure (V n) ⊆ U := by
      intro n x hx
      by_contra hxU
      have hzero : f x = 0 := Metric.infDist_zero_of_mem (show x ∈ (Uᶜ : Set (Vec d)) from hxU)
      have hle : ((n : ℝ) + 1)⁻¹ ≤ f x := hVlevel n hx
      rw [hzero] at hle
      have : (0:ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      linarith
    have hstep : ∀ n, closure (V n) ⊆ V (n + 1) := by
      intro n x hx
      have h1 : ((n : ℝ) + 1)⁻¹ ≤ f x := hVlevel n hx
      have h2 : dist x 0 ≤ (n : ℝ) + 1 := Metric.mem_closedBall.mp (hVball n hx)
      refine ⟨?_, ?_⟩
      · show (((n + 1 : ℕ) : ℝ) + 1)⁻¹ < f x
        push_cast
        exact lt_of_lt_of_le (hinv n) h1
      · rw [Metric.mem_ball]
        push_cast
        linarith
    have habs : ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ⊆ V n := by
      intro K hKcompact hKU
      rcases K.eq_empty_or_nonempty with rfl | hKne
      · exact ⟨0, fun n _ => Set.empty_subset _⟩
      obtain ⟨x0, hx0K, hx0min⟩ := hKcompact.exists_isMinOn hKne hfcont.continuousOn
      have hm : 0 < f x0 :=
        (hUcclosed.notMem_iff_infDist_pos hUcne).mp (by simpa using hKU hx0K)
      obtain ⟨R, hR⟩ := hKcompact.isBounded.subset_closedBall (0 : Vec d)
      obtain ⟨N, hN⟩ := exists_nat_gt (max ((f x0)⁻¹) R)
      refine ⟨N, fun n hn x hxK => ?_⟩
      have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h1 : ((f x0)⁻¹) < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
      have h2 : ((f x0)⁻¹) < (n : ℝ) + 1 := by linarith
      have hinvlt : ((n : ℝ) + 1)⁻¹ < f x0 := by
        have h3 := one_div_lt_one_div_of_lt (by positivity : (0:ℝ) < (f x0)⁻¹) h2
        rwa [one_div, one_div, inv_inv] at h3
      refine ⟨lt_of_lt_of_le hinvlt (hx0min hxK), ?_⟩
      rw [Metric.mem_ball]
      have hRx : dist x 0 ≤ R := Metric.mem_closedBall.mp (hR hxK)
      have hRN : R < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN
      linarith
    refine ⟨V, fun n => ⟨(isOpen_lt continuous_const hfcont).inter Metric.isOpen_ball,
      IsCompact.of_isClosed_subset (isCompact_closedBall _ _) isClosed_closure (hVball n),
      hVU n, hstep n⟩, habs, fun w => ?_⟩
    have hmono : Monotone fun n => ContinuousPath.exitTime (V n) w :=
      monotone_nat_of_le_succ fun n => exitTime_mono (subset_closure.trans (hstep n)) w
    rw [← iSup_exitTime_eq_of_exhaustion (fun n => subset_closure.trans (hVU n)) habs w]
    exact tendsto_atTop_iSup hmono

/-- The exact open target `relativeExhaustionGoal`, copied from
`ledger/reports/P-452-agent1.md` §4. -/
def relativeExhaustionGoal (d : ℕ) : Prop :=
  ∀ U : Set (Vec d), IsOpen U → Bornology.IsBounded U →
    ∃ V : ℕ → Set (Vec d),
      (∀ n, IsOpen (V n) ∧ IsCompact (closure (V n)) ∧ closure (V n) ⊆ U ∧
        closure (V n) ⊆ V (n + 1)) ∧
      (∀ K : Set (Vec d), IsCompact K → K ⊆ U →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ⊆ V n) ∧
      ∀ omega : ContinuousPath (Vec d),
        Tendsto (fun n => ContinuousPath.exitTime (V n) omega) atTop
          (𝓝 (ContinuousPath.exitTime U omega))

/-- **`relativeExhaustionGoal` is discharged.** -/
theorem relativeExhaustionGoal_holds (d : ℕ) : relativeExhaustionGoal d :=
  fun U hU hUb => relativeExhaustion U hU hUb

end SubdiffusiveProcess.Probability.Diffusion.Packet452Route
