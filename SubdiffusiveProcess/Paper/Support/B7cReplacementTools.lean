module

public import SubdiffusiveProcess.Paper.Support.B7cKilledGamma
public import SubdiffusiveProcess.Paper.prop_gluing_replacement
public import SubdiffusiveProcess.Paper.prop_gluing_face_mass
public import SubdiffusiveProcess.Sobolev.ContinuousZeroExtension
public import Mathlib.Topology.Piecewise
public import SubdiffusiveProcess.DirichletForm.KilledCoreClosure

@[expose] public section





set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Almost-everywhere representatives pass through the actual zero extension. -/
theorem aux_mfd_prop_gluing_zeroExtension_rep
    {d : ℕ} {q Q : Opens (SpatialCoordinates d)} (hqQ : q ≤ Q)
    (u : DomainL2 q) (uc : SpatialCoordinates d → ℝ)
    (hrep : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (q : Set (SpatialCoordinates d))] uc) :
    (zeroExtensionLp hqQ u : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        (q : Set (SpatialCoordinates d)).indicator uc := by
  classical
  have h := (ae_restrict_iff' q.isOpen.measurableSet).mp hrep
  filter_upwards [zeroExtensionLp_coeFn hqQ u, ae_restrict_of_ae h] with x hx hux
  rw [hx]
  by_cases hxq : x ∈ (q : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem hxq, Set.indicator_of_mem hxq]
    exact hux hxq
  · rw [Set.indicator_of_notMem hxq, Set.indicator_of_notMem hxq]

/-- Zero extension through an intermediate cube is the same L2 element. -/
theorem aux_mfd_prop_gluing_zeroExtension_trans
    {d : ℕ} {q p Q : Opens (SpatialCoordinates d)}
    (hqp : q ≤ p) (hpQ : p ≤ Q) (hqQ : q ≤ Q) (u : DomainL2 q) :
    zeroExtensionLp hpQ (zeroExtensionLp hqp u) = zeroExtensionLp hqQ u := by
  classical
  apply Lp.ext
  have hrep := aux_mfd_prop_gluing_zeroExtension_rep hpQ (zeroExtensionLp hqp u)
    ((q : Set (SpatialCoordinates d)).indicator u) (zeroExtensionLp_coeFn hqp u)
  filter_upwards [hrep, zeroExtensionLp_coeFn hqQ u] with x h1 h2
  rw [h1, h2]
  by_cases hxq : x ∈ (q : Set (SpatialCoordinates d))
  · rw [Set.indicator_of_mem (hqp hxq), Set.indicator_of_mem hxq]
  · by_cases hxp : x ∈ (p : Set (SpatialCoordinates d))
    · rw [Set.indicator_of_mem hxp]
    · rw [Set.indicator_of_notMem hxp, Set.indicator_of_notMem hxq]

/-- The full uniform trace limit preserves the parent zero boundary. -/
theorem aux_mfd_prop_gluing_limit_frontier_zero
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (uN : ℕ → SpatialCoordinates d → ℝ) (u : SpatialCoordinates d → ℝ)
    (hu : TendstoUniformlyOn uN u atTop (closure (Q : Set (SpatialCoordinates d))))
    (hzero : ∀ n, ∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), uN n x = 0) :
    ∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), u x = 0 := by
  intro x hx
  have hlim := hu.tendsto_at (frontier_subset_closure hx)
  have hlim0 : Tendsto (fun n => uN n x) atTop (𝓝 0) := by
    simpa only [hzero _ x hx] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hlim hlim0

/-- The literal indicator representative extends continuously when the frontier is zero. -/
theorem aux_mfd_prop_gluing_indicator_continuous
    {d : ℕ} (Q : Opens (SpatialCoordinates d)) (u : SpatialCoordinates d → ℝ)
    (hu : ContinuousOn u (closure (Q : Set (SpatialCoordinates d))))
    (hzero : ∀ x ∈ frontier (Q : Set (SpatialCoordinates d)), u x = 0) :
    Continuous ((Q : Set (SpatialCoordinates d)).indicator u) := by
  classical
  exact continuous_piecewise hzero hu continuousOn_const

/-- Transfer local harmonic orthogonality through two actual killed-domain images. -/
theorem aux_mfd_prop_gluing_transfer_orthogonality
    {d : ℕ} {q p Q : Opens (SpatialCoordinates d)}
    (hqp : q ≤ p) (hpQ : p ≤ Q) (hqQ : q ≤ Q)
    (EQ : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Ep : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (p : Set (SpatialCoordinates d))))
    (Eq : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (q : Set (SpatialCoordinates d))))
    (DQq : Submodule ℝ (DomainL2 Q)) (Dpq : Submodule ℝ (DomainL2 p))
    (hDQq : ∀ phi : DomainL2 Q, phi ∈ DQq ↔
      ∃ v : DomainL2 q, v ∈ Eq.domain ∧ zeroExtensionLp hqQ v = phi)
    (hDpq : _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain Ep (q : Set (SpatialCoordinates d)) Dpq)
    (hDpqImage : ∀ phi : DomainL2 p, phi ∈ Dpq ↔
      ∃ v : DomainL2 q, v ∈ Eq.domain ∧ zeroExtensionLp hqp v = phi)
    (hform : ∀ u ∈ Ep.domain, ∀ v ∈ Ep.domain,
      EQ.form (zeroExtensionLp hpQ u) (zeroExtensionLp hpQ v) = Ep.form u v)
    (u : DomainL2 p) (hu : u ∈ Ep.domain)
    (horth : ∀ phi ∈ Ep.killedCoreClosure (q : Set (SpatialCoordinates d)),
      Ep.form u phi = 0) :
    ∀ phi ∈ DQq, EQ.form (zeroExtensionLp hpQ u) phi = 0 := by
  intro phi hphi
  obtain ⟨v, hv, rfl⟩ := (hDQq phi).mp hphi
  have hvp : zeroExtensionLp hqp v ∈ Dpq :=
    (hDpqImage _).mpr ⟨v, hv, rfl⟩
  have hEq : Dpq = Ep.killedCoreClosure (q : Set (SpatialCoordinates d)) :=
    _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain.eq_of_isKilledDomain hDpq
      (Ep.isKilledDomain_killedCoreClosure _)
  have hvpc : zeroExtensionLp hqp v ∈ Ep.killedCoreClosure (q : Set (SpatialCoordinates d)) :=
    hEq ▸ hvp
  rw [← aux_mfd_prop_gluing_zeroExtension_trans hqp hpQ hqQ v,
    hform u hu _ (hDpq.le_domain hvp)]
  exact horth _ hvpc

end SubdiffusiveProcess.Paper
