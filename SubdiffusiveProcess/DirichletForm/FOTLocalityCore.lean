import SubdiffusiveProcess.DirichletForm.FOTLocalityClosure
import Mathlib.Topology.UrysohnsLemma

open MeasureTheory Filter Set Topology
open scoped NNReal

noncomputable section

namespace DirichletForm

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- A regular core provides energy-bounded continuous core approximations in `L²`. -/
theorem IsCoreOn.exists_approx (F : _root_.DirichletForm m) {U : Set X}
    {C : Set (Lp ℝ 2 m)} (hcore : IsCoreOn F.toClosedForm U C)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) :
    ∃ v : ℕ → Lp ℝ 2 m,
      (∀ n, F.toClosedForm.MemCoreOn U (v n)) ∧
      Tendsto v atTop (𝓝 u) ∧
      (∀ n, F.form (v n) (v n) ≤ 2 * F.form u u + 2) := by
  choose v hvC hvε using fun n : ℕ =>
    hcore.denseEnergy u hu ((1 / ((n : ℝ) + 1)) ^ 2) (by positivity)
  have hv : ∀ n, F.toClosedForm.MemCoreOn U (v n) :=
    fun n => hcore.memCoreOn _ (hvC n)
  have hδ : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hδ1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨v, hv, ?_, ?_⟩
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    have h := F.toClosedForm.sq_norm_le_energyNormSq (F.domain.sub_mem hu (hv n).1)
    rw [norm_sub_rev] at h
    nlinarith [hvε n, norm_nonneg (v n - u), hδ n]
  · intro n
    have he := (F.toClosedForm.form_le_energyNormSq (u := u - v n)).trans (hvε n).le
    have h := F.toClosedForm.form_sub_self_le hu (F.domain.sub_mem hu (hv n).1)
    rw [sub_sub_cancel] at h
    nlinarith [hδ n, hδ1 n]

/-- When the target is bounded, its core approximations can have the same bound. -/
theorem IsCoreOn.exists_bounded_approx (F : _root_.DirichletForm m) {U : Set X}
    {C : Set (Lp ℝ 2 m)} (hcore : IsCoreOn F.toClosedForm U C)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) {R : ℝ≥0}
    (huR : ∀ᵐ x ∂m, |u x| ≤ R) :
    ∃ v : ℕ → Lp ℝ 2 m, ∃ f : ℕ → X → ℝ,
      (∀ n, F.toClosedForm.MemCoreOn U (v n)) ∧
      (∀ n, Continuous (f n)) ∧ (∀ n, HasCompactSupport (f n)) ∧
      (∀ n, tsupport (f n) ⊆ U) ∧ (∀ n, ⇑(v n) =ᵐ[m] f n) ∧
      (∀ n x, |f n x| ≤ R) ∧ Tendsto v atTop (𝓝 u) ∧
      (∀ n, F.form (v n) (v n) ≤ 2 * F.form u u + 2) := by
  obtain ⟨v, hv, hlim, hE⟩ := hcore.exists_approx F hu
  choose f hf hfc hfU hfae using fun n => (hv n).2
  refine ⟨fun n => clipLp R (v n), fun n => clip R ∘ f n,
    fun n => memCoreOn_compLp F (hv n) (lipschitzWith_clip R) (clip_zero R.coe_nonneg),
    fun n => (lipschitzWith_clip R).continuous.comp (hf n),
    fun n => (hfc n).comp_left (clip_zero R.coe_nonneg),
    fun n => (tsupport_comp_subset (clip_zero R.coe_nonneg) (f n)).trans (hfU n),
    fun n => (coeFn_clipLp R (v n)).trans ((hfae n).fun_comp (clip R)),
    fun n x => abs_clip_le R.coe_nonneg (f n x), ?_, ?_⟩
  · have h := ((lipschitzWith_clip R).continuous_compLp
    (μ := m) (p := 2) (clip_zero R.coe_nonneg)).tendsto u |>.comp hlim
    change Tendsto (fun n => clipLp R (v n)) atTop (𝓝 (clipLp R u)) at h
    rwa [clipLp_eq_self huR] at h
  · intro n
    exact (clipLp_mem F R (hv n).1).2.trans (hE n)

/-- Core cutoffs equal to one on a neighborhood of a compact set. -/
theorem IsCoreOn.exists_cutoff [T2Space X] [LocallyCompactSpace X]
    (F : _root_.DirichletForm m) {U : Set X} {C : Set (Lp ℝ 2 m)}
    (hcore : IsCoreOn F.toClosedForm U C)
    {K O : Set X} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) (hOU : O ⊆ U) :
    ∃ w : Lp ℝ 2 m, ∃ f : X → ℝ, ∃ V : Set X,
      F.toClosedForm.MemCoreOn U w ∧ Continuous f ∧ HasCompactSupport f ∧
      tsupport f ⊆ O ∧ ⇑w =ᵐ[m] f ∧
      (∀ x, f x ∈ Icc 0 1) ∧ IsOpen V ∧ K ⊆ V ∧
      (∀ x ∈ V, f x = 1) := by
  obtain ⟨b, hbK, hbc, hbO, hb01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hO hKO
  obtain ⟨w, hwC, g, hg, hgc, hgU, hwae, hclose⟩ :=
    hcore.denseUniform b b.continuous hbc (hbO.trans hOU) (1 / 4) (by norm_num)
  let T : ℝ → ℝ := fun t => ramp 1 (4 * t - 1)
  have hT : LipschitzWith 4 T := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    have h := (lipschitzWith_ramp 1).dist_le_mul (4 * a - 1) (4 * b - 1)
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] at h
    change |T a - T b| ≤ 4 * |a - b|
    calc
      _ ≤ |4 * a - 1 - (4 * b - 1)| := h
      _ = 4 * |a - b| := by
        rw [show 4 * a - 1 - (4 * b - 1) = 4 * (a - b) by ring, abs_mul]
        norm_num
  have hT0 : T 0 = 0 := by exact ramp_of_nonpos (by norm_num)
  let f := T ∘ g
  have hfcont : Continuous f := hT.continuous.comp hg
  have hfO : tsupport f ⊆ O := by
    apply Subset.trans _ hbO
    apply closure_mono
    intro x hx
    by_contra hxb
    have hb0 : b x = 0 := by simpa [Function.mem_support] using hxb
    have hglt : g x < 1 / 4 := by
      have := (abs_lt.mp (hclose x)).2
      rw [hb0, sub_zero] at this
      exact this
    have hf0 : f x = 0 := ramp_of_nonpos (by linarith)
    exact hx hf0
  let V : Set X := {x | 1 / 2 < g x}
  refine ⟨hT.compLp hT0 w, f, V,
    memCoreOn_compLp F (hcore.memCoreOn _ hwC) hT hT0,
    hfcont, hgc.comp_left hT0, hfO,
    (hT.coeFn_compLp hT0 w).trans (hwae.fun_comp T),
    fun x => ⟨ramp_nonneg _ _, ramp_le (by norm_num)⟩,
    isOpen_lt continuous_const hg, ?_, ?_⟩
  · intro x hx
    have h := (abs_lt.mp (hclose x)).1
    have hb1 : b x = 1 := hbK hx
    rw [hb1] at h
    change 1 / 2 < g x
    linarith
  · intro x hx
    exact ramp_of_ge (by norm_num) (by change 1 / 2 < g x at hx; linarith)

end DirichletForm
