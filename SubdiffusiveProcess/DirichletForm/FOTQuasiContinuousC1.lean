import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuous
import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousConvex
import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousC1Strong

open MeasureTheory Filter Set Topology
open scoped ContDiff NNReal

noncomputable section

namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X] [SecondCountableTopology X] {m : Measure X}

theorem EnergyFamily.quasiContinuous_chain {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) (q : RepresentativeFamily Γ)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 1 Φ)
    {L : ℝ≥0} (hL : LipschitzWith L Φ) (hΦ0 : Φ 0 = 0)
    {w : Lp ℝ 2 m} (hw : w ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => Φ (q.rep u hu x)) {B : Set X} (hB : MeasurableSet B) :
    (Γ.measure w B).toReal =
      ∫ x in B, (deriv Φ (q.rep u hu x)) ^ 2 ∂(Γ.measure u) := by
  exact Γ.quasiContinuous_chain_eq_of_c1 h q hu Φ hΦ hL hΦ0 hw hwae hB

theorem RepresentativeFamily.compose_agree {F : _root_.DirichletForm m} {U : Set X}
    (h : Data F U) (Γ : EnergyFamily F U) (q : RepresentativeFamily Γ)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 1 Φ)
    {L : ℝ≥0} (hL : LipschitzWith L Φ) (hΦ0 : Φ 0 = 0)
    {w : Lp ℝ 2 m} (hw : w ∈ F.domain)
    (hwae : ⇑w =ᵐ[m] fun x => Φ (q.rep u hu x)) :
    ∀ v ∈ F.domain, q.rep w hw =ᵐ[Γ.measure v] fun x => Φ (q.rep u hu x) := by
  classical
  obtain ⟨un, fn, hun, hfn, henergy, hLp, hbound⟩ := exists_core_energy_approx F h hu
  obtain ⟨s, hs, hsae⟩ := q.approx_ae u hu un hun fn hfn henergy
  let vn : ℕ → Lp ℝ 2 m := fun n => hL.compLp hΦ0 (un (s n))
  let gn : ℕ → X → ℝ := fun n x => Φ (fn (s n) x)
  have hvn : ∀ n, F.toClosedForm.MemCoreOn U (vn n) := fun n =>
    memCoreOn_compLp F (hun (s n)) hL hΦ0
  have hgn : ∀ n, Continuous (gn n) ∧ HasCompactSupport (gn n) ∧ tsupport (gn n) ⊆ U ∧
      ⇑(vn n) =ᵐ[m] gn n := by
    intro n
    exact ⟨hL.continuous.comp (hfn (s n)).1, (hfn (s n)).2.1.comp_left hΦ0,
      (tsupport_comp_subset hΦ0 (fn (s n))).trans (hfn (s n)).2.2.1,
      (hL.coeFn_compLp hΦ0 (un (s n))).trans ((hfn (s n)).2.2.2.fun_comp Φ)⟩
  have heq : hL.compLp hΦ0 u = w := by
    apply Lp.ext
    exact ((hL.coeFn_compLp hΦ0 u).trans ((q.ae_rep u hu).fun_comp Φ)).trans hwae.symm
  have hvlim : Tendsto vn atTop (𝓝 w) := by
    have hh := (hL.continuous_compLp hΦ0).tendsto u |>.comp (hLp.comp hs.tendsto_atTop)
    simpa only [heq] using hh
  have hvbound : ∀ n, F.form (vn n) (vn n) ≤ (L : ℝ) ^ 2 * (2 * F.form u u + 2) := by
    intro n
    exact (lipschitz_comp_mem F hL hΦ0 (hun (s n)).1
      (hL.coeFn_compLp hΦ0 (un (s n)))).2.trans
        (mul_le_mul_of_nonneg_left (hbound (s n)) (sq_nonneg _))
  obtain ⟨zn, hzn, hzlim⟩ := exists_convex_tail_energy_approx F.toClosedForm
    (fun n => (hvn n).1) hvlim hvbound
  have hzrep := fun n => core_rep_of_convexHull F vn gn hvn hgn (hzn n)
  choose hzcore fnz hfz hfzc hfzU hfzae hfzhull using hzrep
  obtain ⟨t, ht, htae⟩ := q.approx_ae w hw zn hzcore fnz
    (fun n => ⟨hfz n, hfzc n, hfzU n, hfzae n⟩) hzlim
  intro v hv
  filter_upwards [htae v hv, hsae v hv] with x hxz hxu
  have hgx : Tendsto (fun n => gn n x) atTop (𝓝 (Φ (q.rep u hu x))) :=
    (hL.continuous.tendsto (q.rep u hu x)).comp hxu
  have hzpoint := tendsto_of_mem_pointwise_tail_hull (g := fun x => Φ (q.rep u hu x)) (x := x) hfzhull hgx
  exact tendsto_nhds_unique hxz (hzpoint.comp ht.tendsto_atTop)

end DirichletForm.FOTConstruction
