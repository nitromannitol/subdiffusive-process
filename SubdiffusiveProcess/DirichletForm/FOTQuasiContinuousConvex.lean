module

public import SubdiffusiveProcess.DirichletForm.FOTCapacity

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

noncomputable section
namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

/-- Energy-bounded L² approximations admit energy-convergent convex tail averages. -/
theorem exists_convex_tail_energy_approx (E : ClosedForm m)
    {u : ℕ → Lp ℝ 2 m} (hu : ∀ n, u n ∈ E.domain)
    {z : Lp ℝ 2 m} (hz : Tendsto u atTop (𝓝 z)) {K : ℝ}
    (hK : ∀ n, E.form (u n) (u n) ≤ K) :
    ∃ w : ℕ → Lp ℝ 2 m, (∀ n, w n ∈ convexHull ℝ (u '' Ici n)) ∧
      Tendsto (fun n => E.energyNormSq (w n - z)) atTop (𝓝 0) := by
  classical
  set C : ℕ → Set (Lp ℝ 2 m) := fun n => convexHull ℝ (u '' Ici n) with hCdef
  have hCD : ∀ n, C n ⊆ E.domain := fun n =>
    convexHull_min (image_subset_iff.2 fun k _ => hu k) E.domain.convex
  have hCanti : ∀ {n p : ℕ}, n ≤ p → C p ⊆ C n := fun hnp =>
    convexHull_mono (image_mono (Ici_subset_Ici.2 hnp))
  have huC : ∀ n, u n ∈ C n := fun n => subset_convexHull ℝ _ ⟨n, self_mem_Ici, rfl⟩
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
  exact ⟨w, hwC, hE1⟩

variable [TopologicalSpace X]

/-- A core supplies strong energy approximations with chosen continuous representatives. -/
theorem exists_core_energy_approx (F : _root_.DirichletForm m) {U : Set X}
    (h : Data F U) {u : Lp ℝ 2 m} (hu : u ∈ F.domain) :
    ∃ (v : ℕ → Lp ℝ 2 m) (f : ℕ → X → ℝ),
      (∀ n, F.toClosedForm.MemCoreOn U (v n)) ∧
      (∀ n, Continuous (f n) ∧ HasCompactSupport (f n) ∧ tsupport (f n) ⊆ U ∧ ⇑(v n) =ᵐ[m] f n) ∧
      Tendsto (fun n => F.energyNormSq (v n - u)) atTop (𝓝 0) ∧
      Tendsto v atTop (𝓝 u) ∧ (∀ n, F.form (v n) (v n) ≤ 2 * F.form u u + 2) := by
  obtain ⟨C, hcore⟩ := h.core
  choose v hvC hvε using fun n : ℕ =>
    hcore.denseEnergy u hu ((1 / ((n : ℝ) + 1)) ^ 2) (by positivity)
  have hv : ∀ n, F.toClosedForm.MemCoreOn U (v n) := fun n => hcore.memCoreOn _ (hvC n)
  choose f hf hfc hfU hfae using fun n => (hv n).2
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hδ1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨v, f, hv, fun n => ⟨hf n, hfc n, hfU n, hfae n⟩, ?_, ?_, ?_⟩
  · have hconv : Tendsto (fun n => F.energyNormSq (u - v n)) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => F.energyNormSq_nonneg (F.domain.sub_mem hu (hv n).1))
        (fun n => (hvε n).le)
      simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using!
        tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ) |>.pow 2
    simpa only [F.energyNormSq_sub_comm (hv _).1 hu] using! hconv
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    have hh := F.sq_norm_le_energyNormSq (F.domain.sub_mem hu (hv n).1)
    rw [norm_sub_rev] at hh
    nlinarith [hvε n, norm_nonneg (v n - u), hδ n]
  · intro n
    have he := (F.form_le_energyNormSq (u := u - v n)).trans (hvε n).le
    have hh := F.form_sub_self_le hu (F.domain.sub_mem hu (hv n).1)
    rw [sub_sub_cancel] at hh
    nlinarith [hδ n, hδ1 n]

/-- Convex core averages have representatives lying pointwise in the same tail hull. -/
theorem core_rep_of_convexHull (F : _root_.DirichletForm m) {U : Set X}
    (u : ℕ → Lp ℝ 2 m) (f : ℕ → X → ℝ)
    (hu : ∀ n, F.toClosedForm.MemCoreOn U (u n))
    (hf : ∀ n, Continuous (f n) ∧ HasCompactSupport (f n) ∧ tsupport (f n) ⊆ U ∧ ⇑(u n) =ᵐ[m] f n)
    {N : ℕ} {z : Lp ℝ 2 m} (hz : z ∈ convexHull ℝ (u '' Ici N)) :
    F.toClosedForm.MemCoreOn U z ∧ ∃ g : X → ℝ, Continuous g ∧ HasCompactSupport g ∧
      tsupport g ⊆ U ∧ ⇑z =ᵐ[m] g ∧ ∀ x, g x ∈ convexHull ℝ ((fun k => f k x) '' Ici N) := by
  let S : Set (Lp ℝ 2 m) := {z | F.toClosedForm.MemCoreOn U z ∧
    ∃ g : X → ℝ, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      ⇑z =ᵐ[m] g ∧ ∀ x, g x ∈ convexHull ℝ ((fun k => f k x) '' Ici N)}
  have hS : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    obtain ⟨hxD, fx, hxcont, hxc, hxU, hxae, hxpoint⟩ := hx
    obtain ⟨hyD, fy, hycont, hyc, hyU, hyae, hypoint⟩ := hy
    refine ⟨(hxD.smul a).add (hyD.smul b), a • fx + b • fy,
      (hxcont.const_smul a).add (hycont.const_smul b),
      hxc.smul_left.add hyc.smul_left, ?_, ?_, ?_⟩
    · exact (tsupport_add (a • fx) (b • fy)).trans (union_subset
        ((tsupport_smul_subset_right (fun _ => a) fx).trans hxU)
        ((tsupport_smul_subset_right (fun _ => b) fy).trans hyU))
    · exact (Lp.coeFn_add (a • x) (b • y)).trans
        (((Lp.coeFn_smul a x).trans (hxae.const_smul a)).add
          ((Lp.coeFn_smul b y).trans (hyae.const_smul b)))
    · intro t
      exact convex_convexHull ℝ _ (hxpoint t) (hypoint t) ha hb hab
  have hinc : u '' Ici N ⊆ S := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨hu n, f n, (hf n).1, (hf n).2.1, (hf n).2.2.1, (hf n).2.2.2, ?_⟩
    intro x
    exact subset_convexHull ℝ _ ⟨n, hn, rfl⟩
  exact convexHull_min hinc hS hz

/-- Averages supported in later and later tails have the same pointwise limit. -/
theorem tendsto_of_mem_pointwise_tail_hull {f : ℕ → X → ℝ} {g : X → ℝ}
    {v : ℕ → X → ℝ} (hv : ∀ n x, v n x ∈ convexHull ℝ ((fun k => f k x) '' Ici n))
    {x : X} (hx : Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => v n x) atTop (𝓝 (g x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hinc : (fun k => f k x) '' Ici n ⊆ Metric.ball (g x) ε := by
    rintro _ ⟨k, hk, rfl⟩
    exact hN k (hn.trans hk)
  exact convexHull_min hinc (convex_ball (g x) ε) (hv n x)

end DirichletForm.FOTConstruction
