module

public import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousRepresentative
public import SubdiffusiveProcess.DirichletForm.FOTEnergyMeasureAssemblyProducts
public import SubdiffusiveProcess.DirichletForm.FOTLocalityCore
public import Mathlib.Topology.Compactness.Lindelof

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal
noncomputable section
namespace DirichletForm.FOTConstruction
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] {m : Measure X}

lemma CoreRepresentative.core_agree {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {u : Lp ℝ 2 m}
    (q : CoreRepresentative F U u) (hu : F.toClosedForm.MemCoreOn U u)
    {f : X → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (hfae : ⇑u =ᵐ[m] f) : ∀ v ∈ F.domain, q.toFun =ᵐ[Γ.measure v] f := by
  have hzero : F.energyNormSq (u - u) = 0 := by
    simp only [sub_self, ClosedForm.energyNormSq, F.form_zero_left F.domain.zero_mem,
      norm_zero, zero_pow two_ne_zero, add_zero]
  obtain ⟨s, hs, hp⟩ := q.approx_ae h Γ (fun _ => u) (fun _ => hu) (fun _ => f)
    (fun _ => ⟨hf, hfc, hfU, hfae⟩) (by simpa only [hzero] using tendsto_const_nhds)
  intro v hv
  filter_upwards [hp v hv] with x hx
  exact tendsto_nhds_unique hx tendsto_const_nhds

lemma CoreRepresentative.weak_approx_agree {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {u : Lp ℝ 2 m} (q : CoreRepresentative F U u)
    (un : ℕ → Lp ℝ 2 m) (hun : ∀ n, F.toClosedForm.MemCoreOn U (un n))
    (fn : ℕ → X → ℝ)
    (hfn : ∀ n, Continuous (fn n) ∧ HasCompactSupport (fn n) ∧ tsupport (fn n) ⊆ U ∧
      ⇑(un n) =ᵐ[m] fn n)
    (hlim : Tendsto un atTop (𝓝 u)) {C : ℝ} (hbound : ∀ n, F.form (un n) (un n) ≤ C)
    (g : X → ℝ)
    (hg : ∀ v ∈ F.domain, ∀ᵐ x ∂Γ.measure v, Tendsto (fun n => fn n x) atTop (𝓝 (g x))) :
    ∀ v ∈ F.domain, q.toFun =ᵐ[Γ.measure v] g := by
  obtain ⟨zn, hzn, hzlim⟩ := exists_convex_tail_energy_approx F.toClosedForm
    (fun n => (hun n).1) hlim hbound
  have hzrep := fun n => core_rep_of_convexHull F un fn hun hfn (hzn n)
  choose hzcore fnz hfz hfzc hfzU hfzae hfzhull using hzrep
  obtain ⟨s, hs, hsae⟩ := q.approx_ae h Γ zn hzcore fnz
    (fun n => ⟨hfz n, hfzc n, hfzU n, hfzae n⟩) hzlim
  intro v hv
  filter_upwards [hsae v hv, hg v hv] with x hx hy
  have hp := tendsto_of_mem_pointwise_tail_hull (g := g) (x := x) hfzhull hy
  exact tendsto_nhds_unique hx (hp.comp hs.tendsto_atTop)

/-- Localizing a clipped representative by a core cutoff identifies it with any continuous version. -/
lemma CoreRepresentative.continuous_cutoff_agree {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {u : Lp ℝ 2 m} (hu : u ∈ F.domain)
    (q : CoreRepresentative F U u) {f : X → ℝ} (hf : Continuous f) (hfae : ⇑u =ᵐ[m] f)
    {b : Lp ℝ 2 m} (hb : F.toClosedForm.MemCoreOn U b) {bc : X → ℝ}
    (hbc : Continuous bc) (hbcc : HasCompactSupport bc) (hbcU : tsupport bc ⊆ U)
    (hbcae : ⇑b =ᵐ[m] bc) (hbc01 : ∀ x, bc x ∈ Icc 0 1) (R : ℝ≥0) :
    ∀ v ∈ F.domain, (fun x => clip R (q.toFun x) * bc x) =ᵐ[Γ.measure v]
      (fun x => clip R (f x) * bc x) := by
  classical
  obtain ⟨un, fn, hun, hfn, henergy, hlp, hbound⟩ := exists_core_energy_approx F h hu
  obtain ⟨s, hs, hsae⟩ := q.approx_ae h Γ un hun fn hfn henergy
  let an : ℕ → Lp ℝ 2 m := fun n => clipLp R (un (s n))
  let ac : ℕ → X → ℝ := fun n x => clip R (fn (s n) x)
  let a : Lp ℝ 2 m := clipLp R u
  have haD : a ∈ F.domain := (clipLp_mem F R hu).1
  have han : ∀ n, F.toClosedForm.MemCoreOn U (an n) := fun n =>
    memCoreOn_compLp F (hun (s n)) (lipschitzWith_clip R) (clip_zero R.coe_nonneg)
  have hanae : ∀ n, ⇑(an n) =ᵐ[m] ac n := fun n =>
    (coeFn_clipLp R (un (s n))).trans ((hfn (s n)).2.2.2.fun_comp (clip R))
  let M : ℝ := max (R : ℝ) 1
  have hanM : ∀ n, ∀ᵐ x ∂m, |an n x| ≤ M := fun n => (hanae n).mono fun x hx =>
    hx ▸ (abs_clip_le R.coe_nonneg _).trans (le_max_left _ _)
  have haM : ∀ᵐ x ∂m, |a x| ≤ M := (coeFn_clipLp R u).mono fun x hx =>
    hx ▸ (abs_clip_le R.coe_nonneg _).trans (le_max_left _ _)
  have hbM : ∀ᵐ x ∂m, |b x| ≤ M := hbcae.mono fun x hx => by
    rw [hx, abs_of_nonneg (hbc01 x).1]
    exact (hbc01 x).2.trans (le_max_right _ _)
  obtain ⟨p, hp, hpae⟩ := exists_mul_mem F haD hb.1 haM hbM
  choose pn hpn hpnae hpnE using fun n =>
    exists_mul_mem_form_le F (han n).1 hb.1 (hanM n) hbM
  let pc : X → ℝ := fun x => clip R (f x) * bc x
  let pnc : ℕ → X → ℝ := fun n x => ac n x * bc x
  have hpcae : ⇑p =ᵐ[m] pc := hpae.trans
    (((coeFn_clipLp R u).trans (hfae.fun_comp (clip R))).mul hbcae)
  have hpc : Continuous pc := ((lipschitzWith_clip R).continuous.comp hf).mul hbc
  have hpcc : HasCompactSupport pc := hbcc.mul_left
  have hpcU : tsupport pc ⊆ U := tsupport_mul_subset_right.trans hbcU
  have hpcore : F.toClosedForm.MemCoreOn U p := ⟨hp, pc, hpc, hpcc, hpcU, hpcae⟩
  have hpnc : ∀ n, Continuous (pnc n) ∧ HasCompactSupport (pnc n) ∧ tsupport (pnc n) ⊆ U ∧
      ⇑(pn n) =ᵐ[m] pnc n := by
    intro n
    exact ⟨((lipschitzWith_clip R).continuous.comp (hfn (s n)).1).mul hbc,
      hbcc.mul_left, tsupport_mul_subset_right.trans hbcU,
      (hpnae n).trans ((hanae n).mul hbcae)⟩
  have hpncore : ∀ n, F.toClosedForm.MemCoreOn U (pn n) := fun n =>
    ⟨hpn n, pnc n, (hpnc n).1, (hpnc n).2.1, (hpnc n).2.2.1, (hpnc n).2.2.2⟩
  have hanlim : Tendsto an atTop (𝓝 a) :=
    ((lipschitzWith_clip R).continuous_compLp (clip_zero R.coe_nonneg)).tendsto u
      |>.comp (hlp.comp hs.tendsto_atTop)
  have hpnlim : Tendsto pn atTop (𝓝 p) := assembly_product_tendsto F
    (fun n => (han n).1) (fun _ => hb.1) haD hb.1 M hanM (fun _ => hbM) haM hbM
    hpae pn hpnae hanlim tendsto_const_nhds
  have hpnBound : ∀ n, F.form (pn n) (pn n) ≤
      8 * M ^ 2 * ((2 * F.form u u + 2) + F.form b b) := by
    intro n
    have hanE : F.form (an n) (an n) ≤ 2 * F.form u u + 2 := by
      exact (clipLp_mem F R (hun (s n)).1).2.trans (hbound (s n))
    exact (hpnE n).trans (mul_le_mul_of_nonneg_left (add_le_add hanE le_rfl) (by positivity))
  obtain ⟨qp⟩ := exists_coreRepresentative F h hp
  have hweak := qp.weak_approx_agree h Γ pn hpncore pnc hpnc hpnlim hpnBound
    (fun x => clip R (q.toFun x) * bc x) (by
      intro v hv
      filter_upwards [hsae v hv] with x hx
      exact (((lipschitzWith_clip R).continuous.tendsto (q.toFun x)).comp hx).mul_const (bc x))
  intro v hv
  exact (hweak v hv).symm.trans (qp.core_agree h Γ hpcore hpc hpcc hpcU hpcae v hv)

/-- A countable family of core cutoff plateaus covers the open core region. -/
lemma CoreRepresentative.continuous_agree [SecondCountableTopology X]
    {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) {u : Lp ℝ 2 m} (hu : u ∈ F.domain)
    (q : CoreRepresentative F U u) {f : X → ℝ} (hf : Continuous f) (hfae : ⇑u =ᵐ[m] f) :
    ∀ v ∈ F.domain, q.toFun =ᵐ[Γ.measure v] f := by
  classical
  obtain ⟨C, hC⟩ := h.core
  have hchoice := fun x : U => hC.exists_cutoff F (K := {(x : X)}) (O := U)
    isCompact_singleton h.isOpen (singleton_subset_iff.mpr x.2) subset_rfl
  choose b bc V hb hbc hbcc hbcU hbcae hbc01 hV hcover hplateau using hchoice
  have hcoverU : U ⊆ ⋃ x : U, V x := fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, hcover ⟨x, hx⟩ (mem_singleton x)⟩
  obtain ⟨c, hc, hcov⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover V hV hcoverU
  intro v hv
  have hUae : ∀ᵐ x ∂Γ.measure v, x ∈ U := ae_iff.mpr (Γ.carried v hv)
  have heach : ∀ n : ℕ, ∀ i ∈ c, ∀ᵐ x ∂Γ.measure v,
      clip (n : ℝ) (q.toFun x) * bc i x = clip (n : ℝ) (f x) * bc i x := by
    intro n i _
    exact q.continuous_cutoff_agree h Γ hu hf hfae (hb i) (hbc i) (hbcc i)
      (hbcU i) (hbcae i) (hbc01 i) ⟨(n : ℝ), Nat.cast_nonneg n⟩ v hv
  have hall : ∀ᵐ x ∂Γ.measure v, ∀ n : ℕ, ∀ i ∈ c,
      clip (n : ℝ) (q.toFun x) * bc i x = clip (n : ℝ) (f x) * bc i x :=
    ae_all_iff.mpr (fun n => (ae_ball_iff hc).mpr (heach n))
  filter_upwards [hUae, hall] with x hxu hx
  obtain ⟨i, hic, hxi⟩ := mem_iUnion₂.mp (hcov hxu)
  obtain ⟨n, hn⟩ := exists_nat_gt (max |q.toFun x| |f x|)
  have hq : |q.toFun x| ≤ (n : ℝ) := (le_max_left _ _).trans hn.le
  have hfx : |f x| ≤ (n : ℝ) := (le_max_right _ _).trans hn.le
  simpa only [hplateau i x hxi, mul_one, clip_eq_self hq, clip_eq_self hfx] using hx n i hic

end DirichletForm.FOTConstruction
