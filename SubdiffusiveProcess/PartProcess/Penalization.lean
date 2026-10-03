module

public import SubdiffusiveProcess.PartProcess.PartForm
public import SubdiffusiveProcess.PartProcess.BoundedPerturbation
public import SubdiffusiveProcess.PartProcess.GraphResolvent
public import SubdiffusiveProcess.PartProcess.QuadraticPenalty
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.PartProcess
open SubdiffusiveProcess.E7
variable {X : Type*} [MeasurableSpace X] {m : Measure X}

def supportedDomain (E : DirichletForm.ClosedForm m) (A : Set X) :
    Submodule ℝ (Lp ℝ 2 m) where
  carrier := {u | u ∈ E.domain ∧ ZeroOutside A u}
  zero_mem' := by
    refine ⟨E.domain.zero_mem, ?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 m] with x hx _
    exact hx
  add_mem' := by
    rintro u v ⟨hu, hzu⟩ ⟨hv, hzv⟩
    refine ⟨E.domain.add_mem hu hv, ?_⟩
    filter_upwards [hzu, hzv, Lp.coeFn_add u v] with x h1 h2 h3 hx
    simp only [h3, Pi.add_apply, h1 hx, h2 hx, add_zero]
  smul_mem' := by
    rintro a u ⟨hu, hzu⟩
    refine ⟨E.domain.smul_mem a hu, ?_⟩
    filter_upwards [hzu, Lp.coeFn_smul a u] with x h1 h2 hx
    simp only [h2, Pi.smul_apply, h1 hx, smul_zero]

theorem graphClosed_supportedDomain (E : DirichletForm.ClosedForm m) (A : Set X) :
    GraphClosed E (supportedDomain E A) := by
  refine ⟨fun _ hu => hu.1, fun u v hu hv hlim => ⟨hv, ?_⟩⟩
  exact zeroOutside_of_tendsto (fun n => (hu n).2)
    (tendsto_Lp_of_energy E (fun n => (hu n).1) hv hlim)

def penalty (A : Set X) (n : ℕ) : X → ℝ :=
  fun x => (n : ℝ) * Aᶜ.indicator (fun _ => (1 : ℝ)) x

theorem zeroOutside_iff_restriction_eq_zero (A : Set X) (hA : MeasurableSet A)
    (u : Lp ℝ 2 m) : ZeroOutside A u ↔ restriction Aᶜ u = 0 := by
  constructor
  · intro hu
    apply Lp.ext
    filter_upwards [restrictLp_coe Aᶜ u, ae_restrict_of_ae hu,
      ae_restrict_mem hA.compl, Lp.coeFn_zero ℝ 2 (m.restrict Aᶜ)] with x h1 h2 hx h3
    change restrictLp Aᶜ u x = (0 : Lp ℝ 2 (m.restrict Aᶜ)) x
    simpa only [Pi.zero_apply] using (h1.trans (h2 hx)).trans h3.symm
  · intro hu
    have heq : ⇑u =ᵐ[m.restrict Aᶜ] (fun _ => (0 : ℝ)) := by
      filter_upwards [restrictLp_coe Aᶜ u, Lp.coeFn_zero ℝ 2 (m.restrict Aᶜ)] with x h1 h2
      change restrictLp Aᶜ u x = u x at h1
      change restriction Aᶜ u x = u x at h1
      rw [hu, h2] at h1
      exact h1.symm
    exact ae_imp_of_ae_restrict heq

theorem integral_penalty_mul (A : Set X) (hA : MeasurableSet A) (n : ℕ)
    (u v : Lp ℝ 2 m) :
    (∫ x, penalty A n x * u x * v x ∂m) =
      (n : ℝ) * inner ℝ (restriction Aᶜ u) (restriction Aᶜ v) := by
  classical
  rw [L2.inner_def]
  calc
    (∫ x, penalty A n x * u x * v x ∂m) =
        ∫ x, (n : ℝ) * Aᶜ.indicator (fun x => u x * v x) x ∂m := by
      congr 1
      funext x
      by_cases hx : x ∈ Aᶜ <;> simp [penalty, hx, mul_assoc]
    _ = (n : ℝ) * ∫ x in Aᶜ, u x * v x ∂m := by
      rw [integral_const_mul, integral_indicator hA.compl]
    _ = (n : ℝ) * ∫ x in Aᶜ,
        inner ℝ (restriction Aᶜ u x) (restriction Aᶜ v x) ∂m := by
      congr 1
      apply integral_congr_ae
      filter_upwards [restrictLp_coe Aᶜ u, restrictLp_coe Aᶜ v] with x h1 h2
      change u x * v x = inner ℝ (restrictLp Aᶜ u x) (restrictLp Aᶜ v x)
      rw [h1, h2]
      simp [RCLike.inner_apply, mul_comm]

/-- Large bounded potentials converge to the variational resolvent supported on `A`. -/
theorem penalized_resolvent_tendsto (E : DirichletForm.ClosedForm m)
    (A : Set X) (hA : MeasurableSet A) (α : ℝ) (hα : 0 < α)
    (F : ℕ → DirichletForm.ClosedForm m)
    (hFdom : ∀ n, (F n).domain = E.domain)
    (hFform : ∀ n u v, (F n).form u v =
      E.form u v + ∫ x, penalty A n x * u x * v x ∂m)
    (G : ℕ → Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hG : ∀ n, DirichletForm.IsResolvent (F n) α (G n))
    (H : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m)
    (hH : IsDomainResolvent E (supportedDomain E A) α H) :
    ∀ f, Tendsto (fun n => G n f) atTop (𝓝 (H f)) := by
  intro f
  apply quadratic_penalty_tendsto E (restriction Aᶜ) α hα f (fun n => G n f)
    (fun n => by simpa only [← hFdom n] using (hG n f).1)
  · intro n v hv
    have he := (hG n f).2 v (by simpa only [hFdom n] using hv)
    rw [hFform, integral_penalty_mul A hA] at he
    linarith
  · exact (hH f).1.1
  · exact (zeroOutside_iff_restriction_eq_zero A hA _).1 (hH f).1.2
  · intro v hv hTv
    exact (hH f).2 v ⟨hv, (zeroOutside_iff_restriction_eq_zero A hA v).2 hTv⟩

end SubdiffusiveProcess.PartProcess
