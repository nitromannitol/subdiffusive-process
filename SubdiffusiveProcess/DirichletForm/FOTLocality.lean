module

public import SubdiffusiveProcess.DirichletForm.FOTLocalityApproximation

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped NNReal

noncomputable section

namespace SubdiffusiveProcess.DirichletForm

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] {m : Measure X}

/-- Strong locality tested on continuous compactly supported representatives in `U`. -/
def IsStronglyLocalOnCoreOn (E : ClosedForm m) (U : Set X) : Prop :=
  ∀ u v : Lp ℝ 2 m, E.MemCoreOn U u → E.MemCoreOn U v →
    ∀ uc vc : X → ℝ, ⇑u =ᵐ[m] uc → ⇑v =ᵐ[m] vc →
      Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
      tsupport uc ⊆ U → tsupport vc ⊆ U →
      ∀ (c : ℝ) (W : Set X), IsOpen W → tsupport vc ⊆ W →
        (∀ x ∈ W, uc x = c) → E.form u v = 0

/-- Core locality extends to bounded domain elements with separated support conditions. -/
theorem form_eq_zero_of_core_locality_of_bounded
    (F : _root_.SubdiffusiveProcess.DirichletForm m) {U : Set X} (hU : IsOpen U)
    {C : Set (Lp ℝ 2 m)} (hcore : IsCoreOn F.toClosedForm U C)
    (hloc : IsStronglyLocalOnCoreOn F.toClosedForm U)
    {u v : Lp ℝ 2 m} (hu : u ∈ F.domain) (hv : v ∈ F.domain)
    {Ru Rv : ℝ≥0} (huR : ∀ᵐ x ∂m, |u x| ≤ Ru) (hvR : ∀ᵐ x ∂m, |v x| ≤ Rv)
    {c : ℝ} {W : Set X} (hW : IsOpen W) {K : Set X} (hK : IsCompact K)
    (hKUW : K ⊆ U ∩ W) (hvK : ∀ᵐ x ∂m, x ∉ K → v x = 0)
    (hc : ∀ᵐ x ∂m, x ∈ W → u x = c) : F.form u v = 0 := by
  obtain ⟨w, f, V, hw, hf, hfc, hfUW, hwae, hf01, hV, hKV, hfV⟩ :=
    hcore.exists_cutoff F hK (hU.inter hW) hKUW inter_subset_left
  obtain ⟨z, g, T, hz, hg, hgc, hgUV, hzae, hg01, hT, hKT, hgT⟩ :=
    hcore.exists_cutoff F hK (hU.inter hV)
      (fun x hx => ⟨(hKUW hx).1, hKV hx⟩) inter_subset_left
  have hfu : ∀ᵐ x ∂m, (c - u x) * f x = 0 := by
    filter_upwards [hc] with x hx
    by_cases hf0 : f x = 0
    · simp [hf0]
    · have hxW : x ∈ W := (hfUW (subset_closure hf0)).2
      simp [hx hxW]
  have hgv : ∀ᵐ x ∂m, v x * g x = v x := by
    filter_upwards [hvK] with x hx
    by_cases hxK : x ∈ K
    · rw [hgT x (hKT hxK), mul_one]
    · simp [hx hxK]
  obtain ⟨a₀, haR⟩ := hcore.exists_bounded_coreApproximation F hu huR
  obtain ⟨b₀, hbR⟩ := hcore.exists_bounded_coreApproximation F hv hvR
  obtain ⟨a, haV⟩ := a₀.exists_plateau haR hw.1 hf hfc
    (hfUW.trans inter_subset_left) hwae hf01 hfu
  obtain ⟨b, hbV⟩ := b₀.exists_supported hbR hz.1 hg hgc
    (hgUV.trans inter_subset_left) hzae hg01 hgv
  have hab : ∀ n k, F.form (a.seq n) (b.seq k) = 0 := by
    intro n k
    exact hloc _ _ (a.memCoreOn n) (b.memCoreOn k) (a.rep n) (b.rep k)
      (a.ae_rep n) (b.ae_rep k) (a.continuous n) (b.continuous k)
      (a.compact n) (b.compact k) (a.support n) (b.support k) c V hV
      ((hbV k).trans (hgUV.trans inter_subset_right))
      (fun x hx => haV n x (hfV x hx))
  have hav : ∀ n, F.form (a.seq n) v = 0 := by
    intro n
    have h := F.toClosedForm.form_eq_zero_of_tendsto_of_form_le b.mem_domain hv
      (a.mem_domain n) b.tendsto b.energy_le (fun k => by
        rw [F.form_symm _ (b.mem_domain k) _ (a.mem_domain n)]
        exact hab n k)
    rwa [F.form_symm _ hv _ (a.mem_domain n)] at h
  exact F.toClosedForm.form_eq_zero_of_tendsto_of_form_le a.mem_domain hu hv
    a.tendsto a.energy_le hav

/-- A regular core and strong locality on that core imply strong locality on the whole domain. -/
theorem stronglyLocalOn_of_core_locality
    (F : _root_.SubdiffusiveProcess.DirichletForm m) {U : Set X} (hU : IsOpen U)
    (hcore : ∃ C, IsCoreOn F.toClosedForm U C)
    (hloc : IsStronglyLocalOnCoreOn F.toClosedForm U) :
    ∀ u ∈ F.domain, ∀ v ∈ F.domain,
      (∃ K : Set X, IsCompact K ∧ K ⊆ U ∧ ∀ᵐ x ∂m, x ∉ K → u x = 0) →
      ∀ (c : ℝ) (W : Set X), IsOpen W →
        (∃ K : Set X, IsCompact K ∧ K ⊆ U ∩ W ∧ ∀ᵐ x ∂m, x ∉ K → v x = 0) →
        (∀ᵐ x ∂m, x ∈ W → u x = c) → F.form u v = 0 := by
  obtain ⟨C, hC⟩ := hcore
  intro u hu v hv _ c W hW hvcompact hc
  obtain ⟨K, hK, hKUW, hvK⟩ := hvcompact
  let un : ℕ → Lp ℝ 2 m := fun n => clipLp (n + 1) u
  let vn : ℕ → Lp ℝ 2 m := fun n => clipLp (n + 1) v
  have huD : ∀ n, un n ∈ F.domain := fun n => (clipLp_mem F (n + 1) hu).1
  have hvD : ∀ n, vn n ∈ F.domain := fun n => (clipLp_mem F (n + 1) hv).1
  have hun : ∀ n, ⇑(un n) =ᵐ[m] fun x => clip (n + 1) (u x) :=
    fun n => coeFn_clipLp (n + 1) u
  have hvn : ∀ n, ⇑(vn n) =ᵐ[m] fun x => clip (n + 1) (v x) :=
    fun n => coeFn_clipLp (n + 1) v
  have huR : ∀ n, ∀ᵐ x ∂m, |un n x| ≤ ((n + 1 : ℝ≥0) : ℝ) := by
    intro n
    filter_upwards [hun n] with x hx
    rw [hx]
    exact abs_clip_le (by positivity) _
  have hvR : ∀ n, ∀ᵐ x ∂m, |vn n x| ≤ ((n + 1 : ℝ≥0) : ℝ) := by
    intro n
    filter_upwards [hvn n] with x hx
    rw [hx]
    exact abs_clip_le (by positivity) _
  have hvnK : ∀ n, ∀ᵐ x ∂m, x ∉ K → vn n x = 0 := by
    intro n
    filter_upwards [hvn n, hvK] with x hx hy hxK
    rw [hx, hy hxK, clip_zero (by positivity)]
  have hcn : ∀ n, ∀ᵐ x ∂m, x ∈ W → un n x = clip (n + 1) c := by
    intro n
    filter_upwards [hun n, hc] with x hx hy hxW
    rw [hx, hy hxW]
  have huv : ∀ n k, F.form (un n) (vn k) = 0 := fun n k =>
    form_eq_zero_of_core_locality_of_bounded F hU hC hloc (huD n) (hvD k)
      (huR n) (hvR k) hW hK hKUW (hvnK k) (hcn n)
  have hunv : ∀ n, F.form (un n) v = 0 := by
    intro n
    have h := F.toClosedForm.form_eq_zero_of_tendsto_of_form_le hvD hv (huD n)
      (tendsto_clipLp v) (fun k => (clipLp_mem F (k + 1) hv).2) (fun k => by
        rw [F.form_symm _ (hvD k) _ (huD n)]
        exact huv n k)
    rwa [F.form_symm _ hv _ (huD n)] at h
  exact F.toClosedForm.form_eq_zero_of_tendsto_of_form_le huD hu hv
    (tendsto_clipLp u) (fun n => (clipLp_mem F (n + 1) hu).2) hunv

end SubdiffusiveProcess.DirichletForm
