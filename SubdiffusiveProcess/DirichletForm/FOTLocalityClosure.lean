module

public import SubdiffusiveProcess.DirichletForm.FOTProduct

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal

noncomputable section

namespace DirichletForm

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

namespace ClosedForm

theorem form_add_self_le (E : ClosedForm m) {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form (u + v) (u + v) ≤ 2 * E.form u u + 2 * E.form v v := by
  have h := E.form_nonneg (u - v) (E.domain.sub_mem hu hv)
  rw [E.form_sub_self hu hv] at h
  rw [E.form_add_self hu hv]
  linarith

theorem form_sub_self_le (E : ClosedForm m) {u v : Lp ℝ 2 m}
    (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    E.form (u - v) (u - v) ≤ 2 * E.form u u + 2 * E.form v v := by
  have h := E.form_nonneg (u + v) (E.domain.add_mem hu hv)
  rw [E.form_add_self hu hv] at h
  rw [E.form_sub_self hu hv]
  linarith

theorem form_smul_self (E : ClosedForm m) (c : ℝ) {u : Lp ℝ 2 m}
    (hu : u ∈ E.domain) : E.form (c • u) (c • u) = c ^ 2 * E.form u u := by
  rw [E.form_smul_left c u hu _ (E.domain.smul_mem c hu), E.form_smul_right c hu hu]
  ring

/-- Bounded-energy `L²` limits preserve energy orthogonality. -/
theorem form_eq_zero_of_tendsto_of_form_le (E : ClosedForm m)
    {u : ℕ → Lp ℝ 2 m} {z a : Lp ℝ 2 m}
    (hu : ∀ n, u n ∈ E.domain) (hz : z ∈ E.domain) (ha : a ∈ E.domain)
    (hlim : Tendsto u atTop (𝓝 z)) {B : ℝ}
    (hB : ∀ n, E.form (u n) (u n) ≤ B) (horth : ∀ n, E.form (u n) a = 0) :
    E.form z a = 0 := by
  have hlin : ∀ t : ℝ, E.form z z + 2 * t * E.form z a ≤ B := by
    intro t
    have hd : ∀ n, u n + t • a ∈ E.domain :=
      fun n => E.domain.add_mem (hu n) (E.domain.smul_mem t ha)
    have ht : Tendsto (fun n => u n + t • a) atTop (𝓝 (z + t • a)) :=
      hlim.add tendsto_const_nhds
    have hb : ∀ n, E.form (u n + t • a) (u n + t • a) ≤ B + t ^ 2 * E.form a a := by
      intro n
      rw [E.form_add_smul_self t (hu n) ha, horth n]
      simpa using hB n
    have h := (E.mem_domain_of_tendsto_of_form_le hd ht hb).2
    rw [E.form_add_smul_self t hz ha] at h
    linarith
  by_contra hne
  have h := hlin ((B - E.form z z + 1) / (2 * E.form z a))
  have heq : 2 * ((B - E.form z z + 1) / (2 * E.form z a)) * E.form z a =
      B - E.form z z + 1 := by
    field_simp
  rw [heq] at h
  linarith

end ClosedForm

/-- A coarse product bound, sufficient for passing locality through bounded-energy limits. -/
theorem exists_mul_mem_form_le (F : _root_.DirichletForm m) {u v : Lp ℝ 2 m}
    (hu : u ∈ F.domain) (hv : v ∈ F.domain) {M : ℝ}
    (huM : ∀ᵐ x ∂m, |u x| ≤ M) (hvM : ∀ᵐ x ∂m, |v x| ≤ M) :
    ∃ w : Lp ℝ 2 m, w ∈ F.domain ∧
      ⇑w =ᵐ[m] (fun x => u x * v x) ∧
      F.form w w ≤ 8 * M ^ 2 * (F.form u u + F.form v v) := by
  let K : ℝ≥0 := ⟨2 * |M|, by positivity⟩
  have hK0 : sqClamp K 0 = 0 := sqClamp_zero K.coe_nonneg
  let A := (lipschitzWith_sqClamp K).compLp hK0 (u + v)
  let B := (lipschitzWith_sqClamp K).compLp hK0 (u - v)
  have hAe : ⇑A =ᵐ[m] fun x => sqClamp K ((u + v : Lp ℝ 2 m) x) :=
    LipschitzWith.coeFn_compLp _ _ _
  have hBe : ⇑B =ᵐ[m] fun x => sqClamp K ((u - v : Lp ℝ 2 m) x) :=
    LipschitzWith.coeFn_compLp _ _ _
  have hA := lipschitz_comp_mem F (lipschitzWith_sqClamp K) hK0
    (F.domain.add_mem hu hv) hAe
  have hB := lipschitz_comp_mem F (lipschitzWith_sqClamp K) hK0
    (F.domain.sub_mem hu hv) hBe
  let w : Lp ℝ 2 m := (1 / 4 : ℝ) • (A - B)
  refine ⟨w, F.domain.smul_mem _ (F.domain.sub_mem hA.1 hB.1), ?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul (1 / 4 : ℝ) (A - B), Lp.coeFn_sub A B,
      hAe, hBe, Lp.coeFn_add u v, Lp.coeFn_sub u v, huM, hvM]
      with x e1 e2 e3 e4 e5 e6 hx hy
    have hsum : |u x + v x| ≤ (K : ℝ) :=
      (abs_add_le _ _).trans (by change |u x| + |v x| ≤ 2 * |M|; linarith [le_abs_self M])
    have hdiff : |u x - v x| ≤ (K : ℝ) :=
      (abs_sub _ _).trans (by change |u x| + |v x| ≤ 2 * |M|; linarith [le_abs_self M])
    change ((1 / 4 : ℝ) • (A - B) : Lp ℝ 2 m) x = _
    rw [e1, Pi.smul_apply, e2, Pi.sub_apply, e3, e4, e5, e6, Pi.add_apply,
      Pi.sub_apply, sqClamp_of_abs_le hsum, sqClamp_of_abs_le hdiff, smul_eq_mul]
    ring
  · change F.form ((1 / 4 : ℝ) • (A - B)) ((1 / 4 : ℝ) • (A - B)) ≤ _
    rw [F.toClosedForm.form_smul_self _ (F.domain.sub_mem hA.1 hB.1)]
    have h1 := F.toClosedForm.form_sub_self_le hA.1 hB.1
    have h2 := F.toClosedForm.form_add_self_le hu hv
    have h3 := F.toClosedForm.form_sub_self_le hu hv
    have h4 : F.form A A ≤ 16 * M ^ 2 * F.form (u + v) (u + v) := by
      convert hA.2 using 1
      have hKcoe : (K : ℝ) = 2 * |M| := rfl
      simp only [NNReal.coe_mul, NNReal.coe_ofNat, hKcoe, mul_pow, sq_abs]
      ring
    have h5 : F.form B B ≤ 16 * M ^ 2 * F.form (u - v) (u - v) := by
      convert hB.2 using 1
      have hKcoe : (K : ℝ) = 2 * |M| := rfl
      simp only [NNReal.coe_mul, NNReal.coe_ofNat, hKcoe, mul_pow, sq_abs]
      ring
    have h6 : F.form A A + F.form B B ≤
        64 * M ^ 2 * (F.form u u + F.form v v) := by
      calc
        _ ≤ 16 * M ^ 2 * (F.form (u + v) (u + v) +
            F.form (u - v) (u - v)) := by linarith
        _ ≤ 16 * M ^ 2 * (4 * (F.form u u + F.form v v)) := by
          gcongr
          linarith
        _ = _ := by ring
    nlinarith

/-- Symmetric clipping of a real function. -/
def clip (R t : ℝ) : ℝ := max (-R) (min t R)

theorem lipschitzWith_clip (R : ℝ) : LipschitzWith 1 (clip R) := by
  simpa [clip] using!
    (LipschitzWith.const (-R)).max (LipschitzWith.id.min (LipschitzWith.const R))

theorem clip_zero {R : ℝ} (hR : 0 ≤ R) : clip R 0 = 0 := by
  simp [clip, min_eq_left hR, max_eq_right (neg_nonpos.mpr hR)]

theorem clip_eq_self {R t : ℝ} (ht : |t| ≤ R) : clip R t = t := by
  rcases abs_le.mp ht with ⟨hlo, hhi⟩
  simp [clip, min_eq_left hhi, max_eq_right hlo]

theorem abs_clip_le {R : ℝ} (hR : 0 ≤ R) (t : ℝ) : |clip R t| ≤ R := by
  exact abs_le.mpr ⟨le_max_left _ _, max_le (neg_le_self hR) (min_le_right _ _)⟩

def clipLp (R : ℝ≥0) (u : Lp ℝ 2 m) : Lp ℝ 2 m :=
  (lipschitzWith_clip R).compLp (clip_zero R.coe_nonneg) u

theorem coeFn_clipLp (R : ℝ≥0) (u : Lp ℝ 2 m) :
    ⇑(clipLp R u) =ᵐ[m] (fun x => clip R (u x)) := by
  exact LipschitzWith.coeFn_compLp _ _ _

theorem clipLp_mem (F : _root_.DirichletForm m) (R : ℝ≥0) {u : Lp ℝ 2 m}
    (hu : u ∈ F.domain) :
    clipLp R u ∈ F.domain ∧ F.form (clipLp R u) (clipLp R u) ≤ F.form u u := by
  simpa using lipschitz_comp_mem F (lipschitzWith_clip R) (clip_zero R.coe_nonneg) hu
    (coeFn_clipLp R u)

theorem clipLp_eq_self {R : ℝ≥0} {u : Lp ℝ 2 m}
    (hu : ∀ᵐ x ∂m, |u x| ≤ R) : clipLp R u = u := by
  exact Lp.ext ((coeFn_clipLp R u).trans (hu.mono fun x hx => clip_eq_self hx))

theorem tendsto_clipLp (u : Lp ℝ 2 m) :
    Tendsto (fun n : ℕ => clipLp (n + 1) u) atTop (𝓝 u) := by
  apply tendsto_Lp_of_tendsto_comp (G := fun t => t) (K := 2)
    (fun n => coeFn_clipLp (n + 1) u)
    (Filter.EventuallyEq.rfl)
  · intro t
    have h : ∀ᶠ n : ℕ in atTop, |t| ≤ (n : ℝ) + 1 := by
      filter_upwards [eventually_ge_atTop (Nat.ceil |t|)] with n hn
      exact (Nat.le_ceil _).trans (by exact_mod_cast (by omega : Nat.ceil |t| ≤ n + 1))
    apply tendsto_const_nhds.congr'
    filter_upwards [h] with n hn
    simpa using (clip_eq_self hn).symm
  · intro n t
    change |clip ((n : ℝ) + 1) t - t| ≤ 2 * |t|
    have h := (lipschitzWith_clip (n + 1 : ℝ)).dist_le_mul t 0
    rw [Real.dist_eq, Real.dist_eq, clip_zero (by positivity), sub_zero, sub_zero,
      NNReal.coe_one, one_mul] at h
    exact (abs_sub _ _).trans (by linarith)

variable [TopologicalSpace X]

theorem memCoreOn_compLp (F : _root_.DirichletForm m) {U : Set X}
    {u : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    {G : ℝ → ℝ} {L : ℝ≥0} (hG : LipschitzWith L G) (hG0 : G 0 = 0) :
    F.toClosedForm.MemCoreOn U (hG.compLp hG0 u) := by
  rcases hu.2 with ⟨f, hf, hfc, hfU, hueq⟩
  refine ⟨(lipschitz_comp_mem F hG hG0 hu.1 (hG.coeFn_compLp hG0 u)).1,
    G ∘ f, hG.continuous.comp hf, ?_, ?_, ?_⟩
  · exact hfc.comp_left hG0
  · exact (tsupport_comp_subset hG0 f).trans hfU
  · exact (hG.coeFn_compLp hG0 u).trans (hueq.fun_comp G)

end DirichletForm
