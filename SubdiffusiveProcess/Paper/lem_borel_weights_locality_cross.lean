module

public import SubdiffusiveProcess.Paper.obl_FOT
public import SubdiffusiveProcess.Paper.conv_energy_measure_normalization
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import Mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
open _root_.SubdiffusiveProcess.DirichletForm

variable {m : Measure X} {E : ClosedForm m}

omit [TopologicalSpace X] in
theorem aux_lem_borel_weights_locality_cross_form_zero_left {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X}
    (E : ClosedForm m) {v : Lp ℝ 2 m}
    (hv : v ∈ E.domain) : E.form 0 v = 0 := by
  simpa only [zero_smul, zero_mul] using
    E.form_smul_left 0 0 E.domain.zero_mem v hv

theorem aux_lem_borel_weights_locality_cross_toReal_measure_le_form (Gamma : EnergyMeasure E)
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain) (B : Set X) :
    (Gamma.measure u B).toReal ≤ E.form u u := by
  rw [← Gamma.measure_univ u hu]
  exact ENNReal.toReal_mono (ne_of_lt (Gamma.measure_univ_lt_top u hu))
    (measure_mono (Set.subset_univ B))

theorem aux_lem_borel_weights_locality_cross_cross_add_left (Gamma : EnergyMeasure E)
    {u v w : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hw : w ∈ E.domain) :
    Gamma.cross (u + v) w = Gamma.cross u w + Gamma.cross v w := by
  rw [Gamma.cross_symm (u + v) (E.domain.add_mem hu hv) w hw,
    Gamma.cross_add_right w hw u hu v hv,
    Gamma.cross_symm w hw u hu, Gamma.cross_symm w hw v hv]

theorem aux_lem_borel_weights_locality_cross_cross_smul_left (Gamma : EnergyMeasure E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) (a : ℝ) :
    Gamma.cross (a • u) v = a • Gamma.cross u v := by
  rw [Gamma.cross_symm (a • u) (E.domain.smul_mem a hu) v hv,
    Gamma.cross_smul_right a v hv u hu, Gamma.cross_symm v hv u hu]

theorem aux_lem_borel_weights_locality_cross_cross_neg_right (Gamma : EnergyMeasure E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    Gamma.cross u (-v) = -Gamma.cross u v := by
  ext B
  simpa only [neg_one_smul, smul_apply, neg_apply, smul_eq_mul, neg_one_mul] using!
    congrArg (fun ν : VectorMeasure X ℝ => ν B) (Gamma.cross_smul_right (-1) u hu v hv)

theorem aux_lem_borel_weights_locality_cross_cross_neg_left (Gamma : EnergyMeasure E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) :
    Gamma.cross (-u) v = -Gamma.cross u v := by
  ext B
  simpa only [neg_one_smul, smul_apply, neg_apply, smul_eq_mul, neg_one_mul] using!
    congrArg (fun ν : VectorMeasure X ℝ => ν B)
      (aux_lem_borel_weights_locality_cross_cross_smul_left Gamma hu hv (-1))

theorem aux_lem_borel_weights_locality_cross_cross_neg_self (Gamma : EnergyMeasure E)
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain) :
    Gamma.cross (-u) (-u) = Gamma.cross u u := by
  rw [aux_lem_borel_weights_locality_cross_cross_neg_left Gamma hu (E.domain.neg_mem hu),
    aux_lem_borel_weights_locality_cross_cross_neg_right Gamma hu hu, neg_neg]

theorem aux_lem_borel_weights_locality_cross_cross_sub_right (Gamma : EnergyMeasure E)
    {u v w : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hw : w ∈ E.domain) :
    Gamma.cross u (v - w) = Gamma.cross u v - Gamma.cross u w := by
  rw [sub_eq_add_neg, Gamma.cross_add_right u hu v hv (-w) (E.domain.neg_mem hw),
    aux_lem_borel_weights_locality_cross_cross_neg_right Gamma hu hw, sub_eq_add_neg]

theorem aux_lem_borel_weights_locality_cross_cross_sub_left (Gamma : EnergyMeasure E)
    {u v w : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hw : w ∈ E.domain) :
    Gamma.cross (u - v) w = Gamma.cross u w - Gamma.cross v w := by
  rw [Gamma.cross_symm (u - v) (E.domain.sub_mem hu hv) w hw,
    aux_lem_borel_weights_locality_cross_cross_sub_right Gamma hw hu hv,
    Gamma.cross_symm w hw u hu, Gamma.cross_symm w hw v hv]

theorem aux_lem_borel_weights_locality_cross_cross_sub_self_apply (Gamma : EnergyMeasure E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) (B : Set X) :
    Gamma.cross (u - v) (u - v) B =
      Gamma.cross u u B - 2 * Gamma.cross u v B + Gamma.cross v v B := by
  rw [aux_lem_borel_weights_locality_cross_cross_sub_left Gamma hu hv (E.domain.sub_mem hu hv),
    aux_lem_borel_weights_locality_cross_cross_sub_right Gamma hu hu hv, aux_lem_borel_weights_locality_cross_cross_sub_right Gamma hv hu hv]
  simp only [sub_apply]
  rw [Gamma.cross_symm v hv u hu]
  ring

theorem aux_lem_borel_weights_locality_cross_cross_add_self_apply (Gamma : EnergyMeasure E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain) (B : Set X) :
    Gamma.cross (u + v) (u + v) B =
      Gamma.cross u u B + 2 * Gamma.cross u v B + Gamma.cross v v B := by
  rw [aux_lem_borel_weights_locality_cross_cross_add_left Gamma hu hv (E.domain.add_mem hu hv),
    Gamma.cross_add_right u hu u hu v hv,
    Gamma.cross_add_right v hv u hu v hv]
  simp only [add_apply]
  rw [Gamma.cross_symm v hv u hu]
  ring

theorem aux_lem_borel_weights_locality_cross_cross_smul_self_apply (Gamma : EnergyMeasure E)
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain) (a : ℝ) (B : Set X) :
    Gamma.cross (a • u) (a • u) B = a ^ 2 * Gamma.cross u u B := by
  rw [aux_lem_borel_weights_locality_cross_cross_smul_left Gamma hu (E.domain.smul_mem a hu) a,
    Gamma.cross_smul_right a u hu u hu]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem aux_lem_borel_weights_locality_cross_cross_self_nonneg (Gamma : EnergyMeasure E)
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain) (B : Set X) (hB : MeasurableSet B) :
    0 ≤ Gamma.cross u u B := by
  rw [Gamma.cross_self u hu B hB]
  exact ENNReal.toReal_nonneg

theorem aux_lem_borel_weights_locality_cross_core_on_memCore {U : Set X} {u : Lp ℝ 2 m}
    (hu : E.MemCoreOn U u) : E.MemCore u := by
  rcases hu with ⟨hud, f, hf, hfc, hfU, huf⟩
  exact ⟨hud, f, hf, hfc, Set.subset_univ _, huf⟩

def aux_lem_borel_weights_locality_cross_EnergySpace (E : ClosedForm m) : Type _ := E.domain

instance aux_lem_borel_weights_locality_cross_energyAddCommGroup (E : ClosedForm m) :
    AddCommGroup (aux_lem_borel_weights_locality_cross_EnergySpace E) :=
  inferInstanceAs (AddCommGroup E.domain)

instance aux_lem_borel_weights_locality_cross_energyModule (E : ClosedForm m) : Module ℝ (aux_lem_borel_weights_locality_cross_EnergySpace E) :=
  inferInstanceAs (Module ℝ E.domain)

instance aux_lem_borel_weights_locality_cross_energyCore (E : ClosedForm m) :
    InnerProductSpace.Core ℝ (aux_lem_borel_weights_locality_cross_EnergySpace E) where
  inner u v := E.form u.1 v.1 + inner ℝ u.1 v.1
  conj_inner_symm u v := by
    change E.form v.1 u.1 + inner ℝ v.1 u.1 =
      E.form u.1 v.1 + inner ℝ u.1 v.1
    rw [E.form_symm v.1 v.2 u.1 u.2, real_inner_comm v.1 u.1]
  re_inner_nonneg u := by
    change 0 ≤ E.form u.1 u.1 + inner ℝ u.1 u.1
    rw [real_inner_self_eq_norm_sq]
    exact add_nonneg (E.form_nonneg u.1 u.2) (sq_nonneg ‖u.1‖)
  add_left u v w := by
    change E.form (u.1 + v.1) w.1 + inner ℝ (u.1 + v.1) w.1 =
      (E.form u.1 w.1 + inner ℝ u.1 w.1) +
        (E.form v.1 w.1 + inner ℝ v.1 w.1)
    rw [E.form_add_left u.1 u.2 v.1 v.2 w.1 w.2, inner_add_left]
    ring
  smul_left u v a := by
    change E.form (a • u.1) v.1 + inner ℝ (a • u.1) v.1 =
      a * (E.form u.1 v.1 + inner ℝ u.1 v.1)
    rw [E.form_smul_left a u.1 u.2 v.1 v.2, real_inner_smul_left]
    ring
  definite u hu := by
    change E.form u.1 u.1 + inner ℝ u.1 u.1 = 0 at hu
    rw [real_inner_self_eq_norm_sq] at hu
    have hsq : ‖u.1‖ ^ 2 = 0 := by
      nlinarith [E.form_nonneg u.1 u.2, sq_nonneg ‖u.1‖]
    have hz : u.1 = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    exact Subtype.ext hz

instance aux_lem_borel_weights_locality_cross_energyNormedAddCommGroup (E : ClosedForm m) :
    NormedAddCommGroup (aux_lem_borel_weights_locality_cross_EnergySpace E) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance aux_lem_borel_weights_locality_cross_energyInnerProductSpace (E : ClosedForm m) :
    InnerProductSpace ℝ (aux_lem_borel_weights_locality_cross_EnergySpace E) :=
  InnerProductSpace.ofCore (aux_lem_borel_weights_locality_cross_energyCore E).toCore

omit [TopologicalSpace X] in
theorem aux_lem_borel_weights_locality_cross_energy_coe_sub {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X} {E : ClosedForm m}
    (u v : aux_lem_borel_weights_locality_cross_EnergySpace E) : (u - v).1 = u.1 - v.1 := rfl
omit [TopologicalSpace X] in
theorem aux_lem_borel_weights_locality_cross_energy_coe_add {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X} {E : ClosedForm m}
    (u v : aux_lem_borel_weights_locality_cross_EnergySpace E) : (u + v).1 = u.1 + v.1 := rfl
omit [TopologicalSpace X] in
theorem aux_lem_borel_weights_locality_cross_energy_coe_smul {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X} {E : ClosedForm m}
    (a : ℝ) (u : aux_lem_borel_weights_locality_cross_EnergySpace E) : (a • u).1 = a • u.1 := rfl

omit [TopologicalSpace X] in
theorem aux_lem_borel_weights_locality_cross_energy_norm_sq {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X} {E : ClosedForm m}
    (u : aux_lem_borel_weights_locality_cross_EnergySpace E) :
    ‖u‖ ^ 2 = E.form u.1 u.1 + ‖u.1‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  change E.form u.1 u.1 + inner ℝ u.1 u.1 = E.form u.1 u.1 + ‖u.1‖ ^ 2
  rw [real_inner_self_eq_norm_sq]

theorem aux_lem_borel_weights_locality_cross_energy_val_norm_le (u : aux_lem_borel_weights_locality_cross_EnergySpace E) : ‖u.1‖ ≤ ‖u‖ := by
  have hsq : ‖u‖ ^ 2 = E.form u.1 u.1 + ‖u.1‖ ^ 2 := aux_lem_borel_weights_locality_cross_energy_norm_sq u
  nlinarith [E.form_nonneg u.1 u.2, norm_nonneg u, norm_nonneg u.1]

def aux_lem_borel_weights_locality_cross_energyIncl (E : ClosedForm m) : aux_lem_borel_weights_locality_cross_EnergySpace E →L[ℝ] Lp ℝ 2 m :=
  LinearMap.mkContinuous
    { toFun := fun u => u.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => by simp only [RingHom.id_apply]; rfl }
    1 (fun u => by
      simpa only [one_mul] using! aux_lem_borel_weights_locality_cross_energy_val_norm_le u)

@[simp] theorem aux_lem_borel_weights_locality_cross_energyIncl_apply (u : aux_lem_borel_weights_locality_cross_EnergySpace E) : aux_lem_borel_weights_locality_cross_energyIncl E u = u.1 := rfl

instance aux_lem_borel_weights_locality_cross_energyCompleteSpace (E : ClosedForm m) :
    CompleteSpace (aux_lem_borel_weights_locality_cross_EnergySpace E) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro s hs
  have hCauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      E.form ((s p).1 - (s q).1) ((s p).1 - (s q).1) +
        ‖(s p).1 - (s q).1‖ ^ 2 < ε := by
    intro ε hε
    rcases Metric.cauchySeq_iff.mp hs (Real.sqrt ε) (Real.sqrt_pos.mpr hε) with
      ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro p hp q hq
    have hdist : ‖s p - s q‖ < Real.sqrt ε := by
      simpa only [dist_eq_norm] using hN p hp q hq
    have hsq : ‖s p - s q‖ ^ 2 =
        E.form ((s p).1 - (s q).1) ((s p).1 - (s q).1) +
          ‖(s p).1 - (s q).1‖ ^ 2 := by
      have h := aux_lem_borel_weights_locality_cross_energy_norm_sq (s p - s q)
      rw [aux_lem_borel_weights_locality_cross_energy_coe_sub] at h
      exact h
    have hsqrt : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε.le
    nlinarith [norm_nonneg (s p - s q), Real.sqrt_nonneg ε]
  rcases E.complete (fun n : ℕ => (s n).1) (fun n : ℕ => (s n).2) hCauchy with
    ⟨w, hw, hlim⟩
  let z : aux_lem_borel_weights_locality_cross_EnergySpace E := ⟨w, hw⟩
  refine ⟨z, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hsq : Tendsto (fun n : ℕ => ‖s n - z‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [aux_lem_borel_weights_locality_cross_energy_norm_sq, aux_lem_borel_weights_locality_cross_energy_coe_sub] using hlim
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (‖s n - z‖ ^ 2))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Real.sqrt_sq_eq_abs, abs_norm] using hsqrt

theorem aux_lem_borel_weights_locality_cross_energy_core_sequence (halg : IsCoreAlgebra E) (u : aux_lem_borel_weights_locality_cross_EnergySpace E) :
    ∃ s : ℕ → aux_lem_borel_weights_locality_cross_EnergySpace E,
      (∀ n : ℕ, E.MemCore (s n).1) ∧ Tendsto s atTop (𝓝 u) := by
  rcases halg.isRegular with ⟨U, hU, hmU, C, hC⟩
  have hclosure : u ∈ closure {z : aux_lem_borel_weights_locality_cross_EnergySpace E | E.MemCore z.1} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    rcases hC.denseEnergy u.1 u.2 (ε ^ 2) (sq_pos_of_pos hε) with
      ⟨w, hwC, hsmall⟩
    have hwcore : E.MemCore w := aux_lem_borel_weights_locality_cross_core_on_memCore (hC.memCoreOn w hwC)
    let z : aux_lem_borel_weights_locality_cross_EnergySpace E := ⟨w, hwcore.1⟩
    refine ⟨z, hwcore, ?_⟩
    have hsq : ‖u - z‖ ^ 2 < ε ^ 2 := by
      simpa only [aux_lem_borel_weights_locality_cross_energy_norm_sq, aux_lem_borel_weights_locality_cross_energy_coe_sub, _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq] using hsmall
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (u - z)]
  exact mem_closure_iff_seq_limit.mp hclosure

theorem aux_lem_borel_weights_locality_cross_gamma_sqrt_le_norm (Gamma : EnergyMeasure E) (u : aux_lem_borel_weights_locality_cross_EnergySpace E)
    (B : Set X) : Real.sqrt (Gamma.measure u.1 B).toReal ≤ ‖u‖ := by
  calc
    Real.sqrt (Gamma.measure u.1 B).toReal ≤ Real.sqrt (‖u‖ ^ 2) := by
      apply Real.sqrt_le_sqrt
      rw [aux_lem_borel_weights_locality_cross_energy_norm_sq]
      exact (aux_lem_borel_weights_locality_cross_toReal_measure_le_form Gamma u.2 B).trans
        (le_add_of_nonneg_right (sq_nonneg ‖u.1‖))
    _ = ‖u‖ := Real.sqrt_sq (norm_nonneg u)

theorem aux_lem_borel_weights_locality_cross_gamma_norm_bound (Gamma : EnergyMeasure E) (B : Set X)
    (hB : MeasurableSet B) (u v : aux_lem_borel_weights_locality_cross_EnergySpace E) :
    ‖Gamma.cross u.1 v.1 B‖ ≤ ‖u‖ * ‖v‖ := by
  rw [Real.norm_eq_abs]
  exact (Gamma.abs_cross_le u.1 u.2 v.1 v.2 B hB).trans
    (mul_le_mul (aux_lem_borel_weights_locality_cross_gamma_sqrt_le_norm Gamma u B)
      (aux_lem_borel_weights_locality_cross_gamma_sqrt_le_norm Gamma v B)
      (Real.sqrt_nonneg _) (norm_nonneg u))

def aux_lem_borel_weights_locality_cross_gammaBilinearLinear (Gamma : EnergyMeasure E) (B : Set X) :
    aux_lem_borel_weights_locality_cross_EnergySpace E →ₗ[ℝ] aux_lem_borel_weights_locality_cross_EnergySpace E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v : aux_lem_borel_weights_locality_cross_EnergySpace E => Gamma.cross u.1 v.1 B)
    (fun u v w => by
      show Gamma.cross (u + v).1 w.1 B = Gamma.cross u.1 w.1 B + Gamma.cross v.1 w.1 B
      rw [aux_lem_borel_weights_locality_cross_energy_coe_add, aux_lem_borel_weights_locality_cross_cross_add_left Gamma u.2 v.2 w.2, add_apply])
    (fun a u v => by
      show Gamma.cross (a • u).1 v.1 B = a • Gamma.cross u.1 v.1 B
      rw [aux_lem_borel_weights_locality_cross_energy_coe_smul, aux_lem_borel_weights_locality_cross_cross_smul_left Gamma u.2 v.2 a, smul_apply])
    (fun u v w => by
      show Gamma.cross u.1 (v + w).1 B = Gamma.cross u.1 v.1 B + Gamma.cross u.1 w.1 B
      rw [aux_lem_borel_weights_locality_cross_energy_coe_add, Gamma.cross_add_right u.1 u.2 v.1 v.2 w.1 w.2,
        add_apply])
    (fun a u v => by
      show Gamma.cross u.1 (a • v).1 B = a • Gamma.cross u.1 v.1 B
      rw [aux_lem_borel_weights_locality_cross_energy_coe_smul, Gamma.cross_smul_right a u.1 u.2 v.1 v.2,
        smul_apply])

def aux_lem_borel_weights_locality_cross_gammaBilinear (Gamma : EnergyMeasure E) (B : Set X)
    (hB : MeasurableSet B) :
    aux_lem_borel_weights_locality_cross_EnergySpace E →L[ℝ] aux_lem_borel_weights_locality_cross_EnergySpace E →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (aux_lem_borel_weights_locality_cross_gammaBilinearLinear Gamma B) 1 (fun u v => by
    rw [one_mul]
    exact aux_lem_borel_weights_locality_cross_gamma_norm_bound Gamma B hB u v)

def aux_lem_borel_weights_locality_cross_gammaFunctional (Gamma : EnergyMeasure E) (B : Set X)
    (hB : MeasurableSet B) (u : aux_lem_borel_weights_locality_cross_EnergySpace E) : aux_lem_borel_weights_locality_cross_EnergySpace E →L[ℝ] ℝ :=
  aux_lem_borel_weights_locality_cross_gammaBilinear Gamma B hB u

@[simp] theorem aux_lem_borel_weights_locality_cross_gammaFunctional_apply (Gamma : EnergyMeasure E) (B : Set X)
    (hB : MeasurableSet B) (u v : aux_lem_borel_weights_locality_cross_EnergySpace E) :
    aux_lem_borel_weights_locality_cross_gammaFunctional Gamma B hB u v = Gamma.cross u.1 v.1 B := rfl

theorem aux_lem_borel_weights_locality_cross_gamma_quadratic_continuous (Gamma : EnergyMeasure E) (B : Set X)
    (hB : MeasurableSet B) :
    Continuous (fun u : aux_lem_borel_weights_locality_cross_EnergySpace E => Gamma.cross u.1 u.1 B) := by
  exact (aux_lem_borel_weights_locality_cross_gammaBilinear Gamma B hB).continuous.clm_apply continuous_id

theorem aux_lem_borel_weights_locality_cross_weak_limit_of_bounded {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (s : ℕ → H) (R : ℝ) (hR : ∀ᶠ n : ℕ in atTop, ‖s n‖ ≤ R) :
    ∃ p : Filter ℕ, p.NeBot ∧ p ≤ atTop ∧ ∃ z : H,
      ∀ f : H →L[ℝ] ℝ, Tendsto (fun n : ℕ => f (s n)) p (𝓝 (f z)) := by
  let L : Ultrafilter ℕ := Ultrafilter.of atTop
  have hL : (L : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  let a : ℕ → WeakDual ℝ H := fun n : ℕ =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (s n))
  let K : Set (WeakDual ℝ H) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) R
  have hK : IsCompact K := WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) R
  have hmem : K ∈ Ultrafilter.map a L := by
    change ∀ᶠ n : ℕ in (L : Filter ℕ), a n ∈ K
    filter_upwards [hL hR] with n hn
    change WeakDual.toStrongDual (a n) ∈ Metric.closedBall (0 : StrongDual ℝ H) R
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖InnerProductSpace.toDual ℝ H (s n)‖ ≤ R
    rw [(InnerProductSpace.toDual ℝ H).norm_map]
    exact hn
  rcases hK.ultrafilter_le_nhds' (Ultrafilter.map a L) hmem with ⟨ell, hell, hlim⟩
  have hlim' : Tendsto a (L : Filter ℕ) (𝓝 ell) := hlim
  let z : H := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual ell)
  refine ⟨(L : Filter ℕ), inferInstance, hL, z, ?_⟩
  intro f
  let y : H := (InnerProductSpace.toDual ℝ H).symm f
  have hy : ∀ x : H, inner ℝ y x = f x := fun x =>
    InnerProductSpace.toDual_symm_apply
  have hz : ∀ x : H, inner ℝ z x = ell x := fun x =>
    InnerProductSpace.toDual_symm_apply
  have heval : Tendsto (fun n : ℕ => a n y) (L : Filter ℕ) (𝓝 (ell y)) :=
    ((WeakDual.eval_continuous y).tendsto ell).comp hlim'
  have hfun : (fun n : ℕ => a n y) = (fun n : ℕ => f (s n)) := by
    funext n
    change inner ℝ (s n) y = f (s n)
    rw [real_inner_comm, hy]
  have hvalue : ell y = f z := by
    rw [← hz y, real_inner_comm, hy]
  rw [hfun, hvalue] at heval
  exact heval

theorem aux_lem_borel_weights_locality_cross_energy_weak_limit (s : ℕ → aux_lem_borel_weights_locality_cross_EnergySpace E) (R : ℝ)
    (hR : ∀ᶠ n : ℕ in atTop, ‖s n‖ ≤ R) (v : Lp ℝ 2 m)
    (hv : Tendsto (fun n : ℕ => (s n).1) atTop (𝓝 v)) :
    ∃ z : aux_lem_borel_weights_locality_cross_EnergySpace E, z.1 = v ∧ ∃ p : Filter ℕ,
      p.NeBot ∧ p ≤ atTop ∧
        ∀ f : aux_lem_borel_weights_locality_cross_EnergySpace E →L[ℝ] ℝ,
          Tendsto (fun n : ℕ => f (s n)) p (𝓝 (f z)) := by
  rcases aux_lem_borel_weights_locality_cross_weak_limit_of_bounded s R hR with ⟨p, hp, hpTop, z, hweak⟩
  let : p.NeBot := hp
  let y : Lp ℝ 2 m := z.1 - v
  have hleft : Tendsto (fun n : ℕ => inner ℝ y (s n).1) p (𝓝 (inner ℝ y z.1)) := by
    simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, aux_lem_borel_weights_locality_cross_energyIncl_apply] using
      hweak ((innerSL ℝ y).comp (aux_lem_borel_weights_locality_cross_energyIncl E))
  have hrightTop : Tendsto (fun n : ℕ => inner ℝ y (s n).1) atTop
      (𝓝 (inner ℝ y v)) := ((innerSL ℝ y).continuous.tendsto v).comp hv
  have hright : Tendsto (fun n : ℕ => inner ℝ y (s n).1) p
      (𝓝 (inner ℝ y v)) := hrightTop.mono_left hpTop
  have heq : inner ℝ y z.1 = inner ℝ y v := tendsto_nhds_unique hleft hright
  have hzero : inner ℝ y y = 0 := by
    change inner ℝ y (z.1 - v) = 0
    rw [inner_sub_right, heq, sub_self]
  have hz : z.1 = v := sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
  exact ⟨z, hz, p, hp, hpTop, hweak⟩

theorem aux_lem_borel_weights_locality_cross_gamma_weak_lower (Gamma : EnergyMeasure E) (B : Set X)
    (hB : MeasurableSet B) (s : ℕ → aux_lem_borel_weights_locality_cross_EnergySpace E) (z : aux_lem_borel_weights_locality_cross_EnergySpace E)
    (p : Filter ℕ) (hp : p.NeBot) (hpTop : p ≤ atTop)
    (hweak : ∀ f : aux_lem_borel_weights_locality_cross_EnergySpace E →L[ℝ] ℝ,
      Tendsto (fun n : ℕ => f (s n)) p (𝓝 (f z)))
    (b : ℕ → ℝ) (a : ℝ) (hb : Tendsto b atTop (𝓝 a))
    (hbound : ∀ n : ℕ, Gamma.cross (s n).1 (s n).1 B ≤ b n) :
    Gamma.cross z.1 z.1 B ≤ a := by
  let : p.NeBot := hp
  let f : aux_lem_borel_weights_locality_cross_EnergySpace E →L[ℝ] ℝ := aux_lem_borel_weights_locality_cross_gammaFunctional Gamma B hB z
  have hpoint : ∀ n : ℕ,
      2 * f (s n) - Gamma.cross z.1 z.1 B ≤ b n := by
    intro n
    have hnonneg : 0 ≤ Gamma.cross ((s n).1 - z.1) ((s n).1 - z.1) B :=
      aux_lem_borel_weights_locality_cross_cross_self_nonneg Gamma (E.domain.sub_mem (s n).2 z.2) B hB
    rw [aux_lem_borel_weights_locality_cross_cross_sub_self_apply Gamma (s n).2 z.2 B,
      Gamma.cross_symm (s n).1 (s n).2 z.1 z.2] at hnonneg
    rw [aux_lem_borel_weights_locality_cross_gammaFunctional_apply]
    linarith [hbound n]
  have hleft : Tendsto
      (fun n : ℕ => 2 * f (s n) - Gamma.cross z.1 z.1 B) p
      (𝓝 (2 * f z - Gamma.cross z.1 z.1 B)) :=
    (tendsto_const_nhds.mul (hweak f)).sub tendsto_const_nhds
  have hle : 2 * f z - Gamma.cross z.1 z.1 B ≤ a :=
    le_of_tendsto_of_tendsto hleft (hb.mono_left hpTop) (Eventually.of_forall hpoint)
  rw [aux_lem_borel_weights_locality_cross_gammaFunctional_apply] at hle
  linarith

theorem aux_lem_borel_weights_locality_cross_energy_norm_le_of_form_norm_le (u v : aux_lem_borel_weights_locality_cross_EnergySpace E)
    (hform : E.form u.1 u.1 ≤ E.form v.1 v.1) (hnorm : ‖u.1‖ ≤ ‖v.1‖) :
    ‖u‖ ≤ ‖v‖ := by
  have hsq : ‖u.1‖ ^ 2 ≤ ‖v.1‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnorm)
      (add_nonneg (norm_nonneg v.1) (norm_nonneg u.1))]
  have hu : ‖u‖ ^ 2 = E.form u.1 u.1 + ‖u.1‖ ^ 2 := aux_lem_borel_weights_locality_cross_energy_norm_sq u
  have hv : ‖v‖ ^ 2 = E.form v.1 v.1 + ‖v.1‖ ^ 2 := aux_lem_borel_weights_locality_cross_energy_norm_sq v
  nlinarith [norm_nonneg u, norm_nonneg v]

def aux_lem_borel_weights_locality_cross_MeasureContraction (Gamma : EnergyMeasure E) (T : ℝ → ℝ) : Prop :=
  ∀ u ∈ E.domain, ∀ v : Lp ℝ 2 m, (⇑v =ᵐ[m] fun x => T (u x)) →
    v ∈ E.domain ∧ ∀ B : Set X, MeasurableSet B →
      Gamma.cross v v B ≤ Gamma.cross u u B

theorem aux_lem_borel_weights_locality_cross_core_smooth_contraction (Gamma : EnergyMeasure E) (halg : IsCoreAlgebra E)
    (T : ℝ → ℝ) (hT : ContDiff ℝ 1 T) (hT0 : T 0 = 0)
    (hderiv : ∀ t : ℝ, |deriv T t| ≤ 1)
    (u : Lp ℝ 2 m) (hu : E.MemCore u) (v : Lp ℝ 2 m)
    (hvrep : ⇑v =ᵐ[m] fun x => T (u x)) :
    v ∈ E.domain ∧ ∀ B : Set X, MeasurableSet B →
      Gamma.cross v v B ≤ Gamma.cross u u B := by
  rcases halg.comp_mem u hu T hT hT0 with ⟨w, hw, hwrep⟩
  have hvw : v = w := by
    apply Lp.ext
    exact hvrep.trans hwrep.symm
  subst v
  rcases hu.2 with ⟨uc, huc, hucc, hucU, hurep⟩
  have hwuc : ⇑w =ᵐ[m] fun x => T (uc x) := by
    filter_upwards [hwrep, hurep] with x hxw hxu
    exact hxw.trans (congrArg T hxu)
  let : IsFiniteMeasure (Gamma.measure u) := ⟨Gamma.measure_univ_lt_top u hu.1⟩
  refine ⟨hw.1, ?_⟩
  intro B hB
  rw [Gamma.cross_self w hw.1 B hB, Gamma.cross_self u hu.1 B hB,
    Gamma.chain_rule u hu.1 uc huc hurep T hT hT0 w hw.1 hwuc B hB]
  by_cases hint : Integrable (fun x : X => (deriv T (uc x)) ^ 2)
      ((Gamma.measure u).restrict B)
  · calc
      (∫ x in B, (deriv T (uc x)) ^ 2 ∂(Gamma.measure u)) ≤
          ∫ x in B, (1 : ℝ) ∂(Gamma.measure u) := by
        apply integral_mono_ae hint (integrable_const (1 : ℝ))
        exact Eventually.of_forall (fun x => by
          have hd : -1 ≤ deriv T (uc x) ∧ deriv T (uc x) ≤ 1 :=
            abs_le.mp (hderiv (uc x))
          nlinarith [mul_nonneg (sub_nonneg.mpr hd.2)
            (by linarith : 0 ≤ 1 + deriv T (uc x))])
      _ = (Gamma.measure u B).toReal := by
        simp only [setIntegral_const, smul_eq_mul, mul_one, Measure.real]
  · rw [integral_undef hint]
    exact ENNReal.toReal_nonneg

theorem aux_lem_borel_weights_locality_cross_measureContraction_smooth (Gamma : EnergyMeasure E) (halg : IsCoreAlgebra E)
    (T : ℝ → ℝ) (hT : ContDiff ℝ 1 T) (hT0 : T 0 = 0)
    (hLip : LipschitzWith 1 T) (hderiv : ∀ t : ℝ, |deriv T t| ≤ 1) :
    aux_lem_borel_weights_locality_cross_MeasureContraction Gamma T := by
  intro u hu v hvrep
  let uE : aux_lem_borel_weights_locality_cross_EnergySpace E := ⟨u, hu⟩
  rcases aux_lem_borel_weights_locality_cross_energy_core_sequence halg uE with ⟨s, hscore, hslim⟩
  let t : ℕ → Lp ℝ 2 m := fun n : ℕ => hLip.compLp hT0 (s n).1
  have ht : ∀ n : ℕ, t n ∈ E.domain ∧ ∀ B : Set X, MeasurableSet B →
      Gamma.cross (t n) (t n) B ≤ Gamma.cross (s n).1 (s n).1 B := by
    intro n
    apply aux_lem_borel_weights_locality_cross_core_smooth_contraction Gamma halg T hT hT0 hderiv (s n).1
      (hscore n) (t n)
    simpa only [Function.comp_def] using hLip.coeFn_compLp hT0 (s n).1
  let sT : ℕ → aux_lem_borel_weights_locality_cross_EnergySpace E := fun n : ℕ => ⟨t n, (ht n).1⟩
  have hnorm : ∀ n : ℕ, ‖sT n‖ ≤ ‖s n‖ := by
    intro n
    apply aux_lem_borel_weights_locality_cross_energy_norm_le_of_form_norm_le
    · have hE : Gamma.cross (t n) (t n) Set.univ ≤
          Gamma.cross (s n).1 (s n).1 Set.univ :=
        (ht n).2 Set.univ MeasurableSet.univ
      rw [Gamma.cross_univ (t n) (ht n).1 (t n) (ht n).1,
        Gamma.cross_univ (s n).1 (s n).2 (s n).1 (s n).2] at hE
      exact hE
    · simpa only [NNReal.coe_one, one_mul] using hLip.norm_compLp_le hT0 (s n).1
  have htail : ∀ᶠ n : ℕ in atTop, ‖s n‖ < ‖uE‖ + 1 :=
    hslim.norm.eventually (gt_mem_nhds (lt_add_one ‖uE‖))
  have hbound : ∀ᶠ n : ℕ in atTop, ‖sT n‖ ≤ ‖uE‖ + 1 :=
    htail.mono (fun n hn => (hnorm n).trans hn.le)
  have hvcomp : hLip.compLp hT0 u = v := by
    apply Lp.ext
    exact (hLip.coeFn_compLp hT0 u).trans hvrep.symm
  have hslp : Tendsto (fun n : ℕ => (s n).1) atTop (𝓝 u) := by
    simpa only [Function.comp_def, aux_lem_borel_weights_locality_cross_energyIncl_apply] using
      ((aux_lem_borel_weights_locality_cross_energyIncl E).continuous.tendsto uE).comp hslim
  have htlim : Tendsto (fun n : ℕ => (sT n).1) atTop (𝓝 v) := by
    have hcomp : Tendsto (fun n : ℕ => hLip.compLp hT0 (s n).1) atTop
        (𝓝 (hLip.compLp hT0 u)) :=
      ((hLip.continuous_compLp hT0).tendsto u).comp hslp
    simpa only [hvcomp] using hcomp
  rcases aux_lem_borel_weights_locality_cross_energy_weak_limit sT (‖uE‖ + 1) hbound v htlim with
    ⟨z, hz, p, hp, hpTop, hweak⟩
  refine ⟨hz ▸ z.2, ?_⟩
  intro B hB
  have hblim : Tendsto (fun n : ℕ => Gamma.cross (s n).1 (s n).1 B) atTop
      (𝓝 (Gamma.cross u u B)) :=
    ((aux_lem_borel_weights_locality_cross_gamma_quadratic_continuous Gamma B hB).tendsto uE).comp hslim
  have hle : Gamma.cross z.1 z.1 B ≤ Gamma.cross u u B :=
    aux_lem_borel_weights_locality_cross_gamma_weak_lower Gamma B hB sT z p hp hpTop hweak
      (fun n : ℕ => Gamma.cross (s n).1 (s n).1 B) (Gamma.cross u u B) hblim
      (fun n : ℕ => (ht n).2 B hB)
  simpa only [hz] using hle

theorem aux_lem_borel_weights_locality_cross_abs_contraction_le (T : ℝ → ℝ) (hT : LipschitzWith 1 T)
    (hT0 : T 0 = 0) (t : ℝ) : |T t| ≤ |t| := by
  have h : ‖T t - T 0‖ ≤ (1 : ℝ≥0) * ‖t - 0‖ := hT.norm_sub_le t 0
  simpa only [hT0, sub_zero, NNReal.coe_one, one_mul, Real.norm_eq_abs] using h

omit [TopologicalSpace X] in
theorem aux_lem_borel_weights_locality_cross_compLp_tendsto_of_pointwise {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X}
    (Tn : ℕ → ℝ → ℝ) (T : ℝ → ℝ)
    (hTn : ∀ n : ℕ, LipschitzWith 1 (Tn n)) (hT : LipschitzWith 1 T)
    (hTn0 : ∀ n : ℕ, Tn n 0 = 0) (hT0 : T 0 = 0)
    (hpoint : ∀ t : ℝ, Tendsto (fun n : ℕ => Tn n t) atTop (𝓝 (T t)))
    (u : Lp ℝ 2 m) :
    Tendsto (fun n : ℕ => (hTn n).compLp (hTn0 n) u) atTop
      (𝓝 (hT.compLp hT0 u)) := by
  let s : ℕ → Lp ℝ 2 m := fun n : ℕ => (hTn n).compLp (hTn0 n) u
  let v : Lp ℝ 2 m := hT.compLp hT0 u
  let F : ℕ → X → ℝ := fun n : ℕ => fun x : X => (Tn n (u x) - T (u x)) ^ 2
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (F n) m := by
    intro n
    exact (((hTn n).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).sub
      (hT.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))).pow 2
  have hboundint : Integrable (fun x : X => 4 * (u x) ^ 2) m :=
    (Lp.memLp u).integrable_sq.const_mul 4
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂m, ‖F n x‖ ≤ 4 * (u x) ^ 2 := by
    intro n
    exact Eventually.of_forall (fun x => by
      have ha : |Tn n (u x)| ≤ |u x| :=
        aux_lem_borel_weights_locality_cross_abs_contraction_le (Tn n) (hTn n) (hTn0 n) (u x)
      have hb : |T (u x)| ≤ |u x| := aux_lem_borel_weights_locality_cross_abs_contraction_le T hT hT0 (u x)
      have hab : |Tn n (u x) - T (u x)| ≤ 2 * |u x| := by
        calc
          |Tn n (u x) - T (u x)| ≤ |Tn n (u x)| + |T (u x)| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              abs_add_le (Tn n (u x)) (-T (u x))
          _ ≤ 2 * |u x| := by linarith
      change ‖(Tn n (u x) - T (u x)) ^ 2‖ ≤ 4 * (u x) ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hprod : 0 ≤
          (2 * |u x| - |Tn n (u x) - T (u x)|) *
            (2 * |u x| + |Tn n (u x) - T (u x)|) :=
        mul_nonneg (sub_nonneg.mpr hab)
          (add_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (abs_nonneg _))
      nlinarith [sq_abs (u x), sq_abs (Tn n (u x) - T (u x))])
  have hpointF : ∀ᵐ x ∂m,
      Tendsto (fun n : ℕ => F n x) atTop (𝓝 ((fun _ : X => (0 : ℝ)) x)) := by
    exact Eventually.of_forall (fun x => by
      have h : Tendsto (fun n : ℕ => (Tn n (u x) - T (u x)) ^ 2)
          atTop (𝓝 ((T (u x) - T (u x)) ^ 2)) :=
        ((hpoint (u x)).sub tendsto_const_nhds).pow 2
      simpa only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using h)
  have hint : Tendsto (fun n : ℕ => ∫ x, F n x ∂m) atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using
      tendsto_integral_of_dominated_convergence (fun x : X => 4 * (u x) ^ 2)
        hmeas hboundint hbound hpointF
  have hsq : ∀ n : ℕ, ‖s n - v‖ ^ 2 = ∫ x, F n x ∂m := by
    intro n
    rw [← real_inner_self_eq_norm_sq (s n - v), L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (s n) v,
      (hTn n).coeFn_compLp (hTn0 n) u, hT.coeFn_compLp hT0 u] with x hsub hs hv
    change inner ℝ ((s n - v) x) ((s n - v) x) =
      (Tn n (u x) - T (u x)) ^ 2
    have hx : (s n - v) x = Tn n (u x) - T (u x) := by
      calc
        (s n - v) x = (s n) x - v x := hsub
        _ = Tn n (u x) - T (u x) := by
          rw [hs, hv]
          rfl
    rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have hsqLim : Tendsto (fun n : ℕ => ‖s n - v‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hsq] using hint
  have hnormLim : Tendsto (fun n : ℕ => ‖s n - v‖) atTop (𝓝 (0 : ℝ)) := by
    have hroot : Tendsto (fun n : ℕ => Real.sqrt (‖s n - v‖ ^ 2))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_def, Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto 0).comp hsqLim
    simpa only [Real.sqrt_sq_eq_abs, abs_norm] using hroot
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnormLim

theorem aux_lem_borel_weights_locality_cross_measureContraction_limit (Gamma : EnergyMeasure E)
    (Tn : ℕ → ℝ → ℝ) (T : ℝ → ℝ)
    (hTn : ∀ n : ℕ, LipschitzWith 1 (Tn n)) (hT : LipschitzWith 1 T)
    (hTn0 : ∀ n : ℕ, Tn n 0 = 0) (hT0 : T 0 = 0)
    (hpoint : ∀ t : ℝ, Tendsto (fun n : ℕ => Tn n t) atTop (𝓝 (T t)))
    (hCn : ∀ n : ℕ, aux_lem_borel_weights_locality_cross_MeasureContraction Gamma (Tn n)) :
    aux_lem_borel_weights_locality_cross_MeasureContraction Gamma T := by
  intro u hu v hvrep
  let uE : aux_lem_borel_weights_locality_cross_EnergySpace E := ⟨u, hu⟩
  let t : ℕ → Lp ℝ 2 m := fun n : ℕ => (hTn n).compLp (hTn0 n) u
  have ht : ∀ n : ℕ, t n ∈ E.domain ∧ ∀ B : Set X, MeasurableSet B →
      Gamma.cross (t n) (t n) B ≤ Gamma.cross u u B := by
    intro n
    apply hCn n u hu (t n)
    simpa only [Function.comp_def] using (hTn n).coeFn_compLp (hTn0 n) u
  let s : ℕ → aux_lem_borel_weights_locality_cross_EnergySpace E := fun n : ℕ => ⟨t n, (ht n).1⟩
  have hnorm : ∀ n : ℕ, ‖s n‖ ≤ ‖uE‖ := by
    intro n
    apply aux_lem_borel_weights_locality_cross_energy_norm_le_of_form_norm_le
    · have hE : Gamma.cross (t n) (t n) Set.univ ≤ Gamma.cross u u Set.univ :=
        (ht n).2 Set.univ MeasurableSet.univ
      rw [Gamma.cross_univ (t n) (ht n).1 (t n) (ht n).1,
        Gamma.cross_univ u hu u hu] at hE
      exact hE
    · simpa only [NNReal.coe_one, one_mul] using (hTn n).norm_compLp_le (hTn0 n) u
  have hvcomp : hT.compLp hT0 u = v := by
    apply Lp.ext
    exact (hT.coeFn_compLp hT0 u).trans hvrep.symm
  have hslim : Tendsto (fun n : ℕ => (s n).1) atTop (𝓝 v) := by
    simpa only [hvcomp] using
      aux_lem_borel_weights_locality_cross_compLp_tendsto_of_pointwise Tn T hTn hT hTn0 hT0 hpoint u
  rcases aux_lem_borel_weights_locality_cross_energy_weak_limit s ‖uE‖ (Eventually.of_forall hnorm) v hslim with
    ⟨z, hz, p, hp, hpTop, hweak⟩
  refine ⟨hz ▸ z.2, ?_⟩
  intro B hB
  have hle : Gamma.cross z.1 z.1 B ≤ Gamma.cross u u B :=
    aux_lem_borel_weights_locality_cross_gamma_weak_lower Gamma B hB s z p hp hpTop hweak
      (fun _ : ℕ => Gamma.cross u u B) (Gamma.cross u u B) tendsto_const_nhds
      (fun n : ℕ => (ht n).2 B hB)
  simpa only [hz] using hle

def aux_lem_borel_weights_locality_cross_smoothCap (c ε t : ℝ) : ℝ :=
  (t - Real.sqrt ((t - c) ^ 2 + ε ^ 2) + Real.sqrt (c ^ 2 + ε ^ 2)) / 2

theorem aux_lem_borel_weights_locality_cross_smoothCap_zero (c ε : ℝ) : aux_lem_borel_weights_locality_cross_smoothCap c ε 0 = 0 := by
  simp only [aux_lem_borel_weights_locality_cross_smoothCap, zero_sub, neg_sq, neg_add_cancel, zero_div]

theorem aux_lem_borel_weights_locality_cross_smoothCap_contDiff (c ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ 1 (aux_lem_borel_weights_locality_cross_smoothCap c ε) := by
  have hq : ContDiff ℝ 1 (fun t : ℝ => (t - c) ^ 2 + ε ^ 2) :=
    ((contDiff_id.sub contDiff_const).pow 2).add contDiff_const
  have hqne : ∀ t : ℝ, (t - c) ^ 2 + ε ^ 2 ≠ 0 := by
    intro t
    exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε))
  exact ((contDiff_id.sub (hq.sqrt hqne)).add contDiff_const).div_const 2

theorem aux_lem_borel_weights_locality_cross_smoothCap_deriv (c ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    deriv (aux_lem_borel_weights_locality_cross_smoothCap c ε) t =
      (1 - (t - c) / Real.sqrt ((t - c) ^ 2 + ε ^ 2)) / 2 := by
  have hqpos : 0 < (t - c) ^ 2 + ε ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  have hroot : Real.sqrt ((t - c) ^ 2 + ε ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hqpos)
  have hq : HasDerivAt (fun s : ℝ => (s - c) ^ 2 + ε ^ 2) (2 * (t - c)) t := by
    convert (((hasDerivAt_id t).sub_const c).pow 2).add_const (ε ^ 2) using 1 <;>
      norm_num
  have hs : HasDerivAt (fun s : ℝ => Real.sqrt ((s - c) ^ 2 + ε ^ 2))
      ((2 * (t - c)) / (2 * Real.sqrt ((t - c) ^ 2 + ε ^ 2))) t :=
    hq.sqrt (ne_of_gt hqpos)
  have hratio : (2 * (t - c)) / (2 * Real.sqrt ((t - c) ^ 2 + ε ^ 2)) =
      (t - c) / Real.sqrt ((t - c) ^ 2 + ε ^ 2) := by
    field_simp [hroot]
  have hcap : HasDerivAt (aux_lem_borel_weights_locality_cross_smoothCap c ε)
      ((1 - (t - c) / Real.sqrt ((t - c) ^ 2 + ε ^ 2)) / 2) t := by
    simpa only [aux_lem_borel_weights_locality_cross_smoothCap, hratio] using!
      (((hasDerivAt_id t).sub hs).add_const (Real.sqrt (c ^ 2 + ε ^ 2))).div_const 2
  exact hcap.deriv

theorem aux_lem_borel_weights_locality_cross_smoothCap_deriv_bound (c ε : ℝ) (hε : 0 < ε) (t : ℝ) :
    |deriv (aux_lem_borel_weights_locality_cross_smoothCap c ε) t| ≤ 1 := by
  have hroot : 0 < Real.sqrt ((t - c) ^ 2 + ε ^ 2) :=
    Real.sqrt_pos.mpr
      (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε))
  have habs : |t - c| ≤ Real.sqrt ((t - c) ^ 2 + ε ^ 2) := by
    calc
      |t - c| = Real.sqrt ((t - c) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((t - c) ^ 2 + ε ^ 2) :=
        Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))
  have hupper : (t - c) / Real.sqrt ((t - c) ^ 2 + ε ^ 2) ≤ 1 := by
    apply (div_le_iff₀ hroot).2
    simpa only [one_mul] using! (le_abs_self (t - c)).trans habs
  have hlower : -1 ≤ (t - c) / Real.sqrt ((t - c) ^ 2 + ε ^ 2) := by
    apply (le_div_iff₀ hroot).2
    have hneg : -Real.sqrt ((t - c) ^ 2 + ε ^ 2) ≤ t - c :=
      (neg_le_neg habs).trans (neg_abs_le (t - c))
    simpa only [neg_one_mul] using hneg
  rw [aux_lem_borel_weights_locality_cross_smoothCap_deriv c ε hε t]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem aux_lem_borel_weights_locality_cross_smoothCap_lipschitz (c ε : ℝ) (hε : 0 < ε) :
    LipschitzWith 1 (aux_lem_borel_weights_locality_cross_smoothCap c ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    ((aux_lem_borel_weights_locality_cross_smoothCap_contDiff c ε hε).differentiable (by norm_num))
  intro t
  change ‖deriv (aux_lem_borel_weights_locality_cross_smoothCap c ε) t‖ ≤ (1 : ℝ)
  simpa only [Real.norm_eq_abs] using aux_lem_borel_weights_locality_cross_smoothCap_deriv_bound c ε hε t

theorem aux_lem_borel_weights_locality_cross_smoothCap_limit_value (c : ℝ) (hc : 0 ≤ c) (t : ℝ) :
    aux_lem_borel_weights_locality_cross_smoothCap c 0 t = min t c := by
  simp only [aux_lem_borel_weights_locality_cross_smoothCap, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero,
    Real.sqrt_sq_eq_abs, abs_of_nonneg hc]
  by_cases ht : t ≤ c
  · rw [abs_of_nonpos (sub_nonpos.mpr ht), min_eq_left ht]
    ring
  · have hct : c ≤ t := (le_of_not_ge ht)
    rw [abs_of_nonneg (sub_nonneg.mpr hct), min_eq_right hct]
    ring

theorem aux_lem_borel_weights_locality_cross_smoothCap_continuous_parameter (c t : ℝ) :
    Continuous (fun ε : ℝ => aux_lem_borel_weights_locality_cross_smoothCap c ε t) := by
  exact ((continuous_const.sub
    ((continuous_const.add (continuous_id.pow 2)).sqrt)).add
      ((continuous_const.add (continuous_id.pow 2)).sqrt)).div_const 2

theorem aux_lem_borel_weights_locality_cross_measureContraction_min (Gamma : EnergyMeasure E) (halg : IsCoreAlgebra E)
    (c : ℝ) (hc : 0 ≤ c) :
    aux_lem_borel_weights_locality_cross_MeasureContraction Gamma (fun t : ℝ => min t c) := by
  let ε : ℕ → ℝ := fun n : ℕ => (1 / 2 : ℝ) ^ n
  have hε : ∀ n : ℕ, 0 < ε n := fun n : ℕ => pow_pos (by norm_num) n
  have hεlim : Tendsto ε atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hpoint : ∀ t : ℝ,
      Tendsto (fun n : ℕ => aux_lem_borel_weights_locality_cross_smoothCap c (ε n) t) atTop (𝓝 (min t c)) := by
    intro t
    simpa only [Function.comp_def, aux_lem_borel_weights_locality_cross_smoothCap_limit_value c hc t] using
      ((aux_lem_borel_weights_locality_cross_smoothCap_continuous_parameter c t).tendsto 0).comp hεlim
  apply aux_lem_borel_weights_locality_cross_measureContraction_limit Gamma (fun n : ℕ => aux_lem_borel_weights_locality_cross_smoothCap c (ε n))
    (fun t : ℝ => min t c)
    (fun n : ℕ => aux_lem_borel_weights_locality_cross_smoothCap_lipschitz c (ε n) (hε n))
    (LipschitzWith.id.min_const c)
    (fun n : ℕ => aux_lem_borel_weights_locality_cross_smoothCap_zero c (ε n)) (min_eq_left hc) hpoint
  intro n
  exact aux_lem_borel_weights_locality_cross_measureContraction_smooth Gamma halg (aux_lem_borel_weights_locality_cross_smoothCap c (ε n))
    (aux_lem_borel_weights_locality_cross_smoothCap_contDiff c (ε n) (hε n)) (aux_lem_borel_weights_locality_cross_smoothCap_zero c (ε n))
    (aux_lem_borel_weights_locality_cross_smoothCap_lipschitz c (ε n) (hε n))
    (aux_lem_borel_weights_locality_cross_smoothCap_deriv_bound c (ε n) (hε n))

theorem aux_lem_borel_weights_locality_cross_measureContraction_pos (Gamma : EnergyMeasure E) (halg : IsCoreAlgebra E) :
    aux_lem_borel_weights_locality_cross_MeasureContraction Gamma (fun t : ℝ => max t 0) := by
  intro u hu v hvrep
  have hrep : ⇑(-v) =ᵐ[m] fun x : X => min ((-u) x) 0 := by
    filter_upwards [hvrep, Lp.coeFn_neg v, Lp.coeFn_neg u] with x hx hvx hux
    simp only [Pi.neg_apply] at hvx hux
    rw [hvx, hux, hx]
    by_cases ht : 0 ≤ u x
    · rw [max_eq_left ht, min_eq_left (neg_nonpos.mpr ht)]
    · have ht' : u x ≤ 0 := le_of_not_ge ht
      rw [max_eq_right ht', neg_zero, min_eq_right (neg_nonneg.mpr ht')]
  have hc : (-v) ∈ E.domain ∧ ∀ B : Set X, MeasurableSet B →
      Gamma.cross (-v) (-v) B ≤ Gamma.cross (-u) (-u) B :=
    aux_lem_borel_weights_locality_cross_measureContraction_min Gamma halg 0 le_rfl (-u) (E.domain.neg_mem hu) (-v) hrep
  have hv : v ∈ E.domain := by
    simpa only [neg_neg] using E.domain.neg_mem hc.1
  refine ⟨hv, ?_⟩
  intro B hB
  simpa only [aux_lem_borel_weights_locality_cross_cross_neg_self Gamma hv, aux_lem_borel_weights_locality_cross_cross_neg_self Gamma hu] using hc.2 B hB

theorem aux_lem_borel_weights_locality_cross_nonpositive_of_linear_bound (a b : ℝ)
    (h : ∀ t : ℝ, 0 < t → t * b ≤ a) : b ≤ 0 := by
  by_contra hb
  have hbpos : 0 < b := lt_of_not_ge hb
  have ht : 0 < (|a| + 1) / b := div_pos (by linarith [abs_nonneg a]) hbpos
  have hineq : ((|a| + 1) / b) * b ≤ a := h ((|a| + 1) / b) ht
  have heq : ((|a| + 1) / b) * b = |a| + 1 := by
    field_simp [ne_of_gt hbpos]
  rw [heq] at hineq
  linarith [le_abs_self a]

theorem aux_lem_borel_weights_locality_cross_compact_of_ae_comp {u v : Lp ℝ 2 m}
    (hu : HasCompactSupportAE m u) (T : ℝ → ℝ) (hT0 : T 0 = 0)
    (hrep : ⇑v =ᵐ[m] fun x : X => T (u x)) : HasCompactSupportAE m v := by
  rcases hu with ⟨K, hK, huK⟩
  refine ⟨K, hK, ?_⟩
  filter_upwards [huK, hrep] with x hx hrepX
  intro hxK
  rw [hrepX, hx hxK, hT0]

theorem aux_lem_borel_weights_locality_cross_compact_neg {u : Lp ℝ 2 m} (hu : HasCompactSupportAE m u) :
    HasCompactSupportAE m (-u) := by
  apply aux_lem_borel_weights_locality_cross_compact_of_ae_comp hu (fun t : ℝ => -t) (neg_zero)
  simpa only [Pi.neg_apply] using! Lp.coeFn_neg u

theorem aux_lem_borel_weights_locality_cross_compact_sub {u v : Lp ℝ 2 m}
    (hu : HasCompactSupportAE m u) (hv : HasCompactSupportAE m v) :
    HasCompactSupportAE m (u - v) := by
  rcases hu with ⟨K, hK, huK⟩
  rcases hv with ⟨L, hL, hvL⟩
  refine ⟨K ∪ L, hK.union hL, ?_⟩
  filter_upwards [huK, hvL, Lp.coeFn_sub u v] with x hux hvx hsub
  intro hx
  have hxK : x ∉ K := fun hxK => hx (Or.inl hxK)
  have hxL : x ∉ L := fun hxL => hx (Or.inr hxL)
  simpa only [Pi.sub_apply, hux hxK, hvx hxL, sub_self] using hsub

theorem aux_lem_borel_weights_locality_cross_pos_mem (Gamma : EnergyMeasure E) (halg : IsCoreAlgebra E)
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain) : Lp.posPart u ∈ E.domain :=
  (aux_lem_borel_weights_locality_cross_measureContraction_pos Gamma halg u hu (Lp.posPart u) (Lp.coeFn_posPart u)).1

theorem aux_lem_borel_weights_locality_cross_neg_mem (Gamma : EnergyMeasure E) (halg : IsCoreAlgebra E)
    {u : Lp ℝ 2 m} (hu : u ∈ E.domain) : Lp.negPart u ∈ E.domain :=
  aux_lem_borel_weights_locality_cross_pos_mem Gamma halg (E.domain.neg_mem hu)

omit [TopologicalSpace X] in
theorem aux_lem_borel_weights_locality_cross_parts_nonnegative {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X}
    (u : Lp ℝ 2 m) :
    (∀ᵐ x ∂m, 0 ≤ Lp.posPart u x) ∧ (∀ᵐ x ∂m, 0 ≤ Lp.negPart u x) := by
  constructor
  · filter_upwards [Lp.coeFn_posPart u] with x hx
    rw [hx]
    exact le_max_right _ _
  · filter_upwards [Lp.coeFn_negPart_eq_max u] with x hx
    rw [hx]
    exact le_max_right _ _

theorem aux_lem_borel_weights_locality_cross_parts_compact {u : Lp ℝ 2 m} (hu : HasCompactSupportAE m u) :
    HasCompactSupportAE m (Lp.posPart u) ∧ HasCompactSupportAE m (Lp.negPart u) := by
  constructor
  · exact aux_lem_borel_weights_locality_cross_compact_of_ae_comp hu (fun t : ℝ => max t 0)
      (max_self 0) (Lp.coeFn_posPart u)
  · exact aux_lem_borel_weights_locality_cross_compact_of_ae_comp hu (fun t : ℝ => max (-t) 0)
      (by simp only [neg_zero, max_self]) (Lp.coeFn_negPart_eq_max u)

omit [TopologicalSpace X] in
theorem aux_lem_borel_weights_locality_cross_parts_zero {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X}
    (u : Lp ℝ 2 m) (P : X → Prop)
    (hu : ∀ᵐ x ∂m, P x → u x = 0) :
    (∀ᵐ x ∂m, P x → Lp.posPart u x = 0) ∧
      (∀ᵐ x ∂m, P x → Lp.negPart u x = 0) := by
  constructor
  · filter_upwards [hu, Lp.coeFn_posPart u] with x hx hpos
    intro hP
    rw [hpos, hx hP, max_self]
  · filter_upwards [hu, Lp.coeFn_negPart_eq_max u] with x hx hneg
    intro hP
    rw [hneg, hx hP, neg_zero, max_self]

omit [TopologicalSpace X] in
theorem aux_lem_borel_weights_locality_cross_parts_decomposition {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X] {m : Measure X}
    (u : Lp ℝ 2 m) : Lp.posPart u - Lp.negPart u = u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (Lp.posPart u) (Lp.negPart u),
    Lp.coeFn_posPart u, Lp.coeFn_negPart_eq_max u] with x hsub hpos hneg
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hpos, hneg]
  by_cases hx : 0 ≤ u x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
  · have hx' : u x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'), zero_sub, neg_neg]

omit [TopologicalSpace X] in
theorem aux_lem_borel_weights_locality_cross_signed_univ_split {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    (ν : SignedMeasure X) (B : Set X) (hB : MeasurableSet B) :
    ν Set.univ = ν B + ν Bᶜ := by
  have hd : Disjoint B Bᶜ := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hy hx
  calc
    ν Set.univ = ν (B ∪ Bᶜ) := congrArg (fun S : Set X => ν S) (Set.union_compl_self B).symm
    _ = ν B + ν Bᶜ := VectorMeasure.of_union hd hB hB.compl

theorem aux_lem_borel_weights_locality_cross_signed_eq_zero_of_nonpos (ν : SignedMeasure X)
    (huniv : ν Set.univ = 0) (hnonpos : ∀ B : Set X, MeasurableSet B → ν B ≤ 0) :
    ν = 0 := by
  apply VectorMeasure.ext
  intro B hB
  change ν B = 0
  have hsplit : ν Set.univ = ν B + ν Bᶜ := aux_lem_borel_weights_locality_cross_signed_univ_split ν B hB
  have hleft : ν B ≤ 0 := hnonpos B hB
  have hright : ν Bᶜ ≤ 0 := hnonpos Bᶜ hB.compl
  linarith

theorem aux_lem_borel_weights_locality_cross_signed_eq_zero_of_nonneg (ν : SignedMeasure X)
    (huniv : ν Set.univ = 0) (hnonneg : ∀ B : Set X, MeasurableSet B → 0 ≤ ν B) :
    ν = 0 := by
  apply VectorMeasure.ext
  intro B hB
  change ν B = 0
  have hsplit : ν Set.univ = ν B + ν Bᶜ := aux_lem_borel_weights_locality_cross_signed_univ_split ν B hB
  have hleft : 0 ≤ ν B := hnonneg B hB
  have hright : 0 ≤ ν Bᶜ := hnonneg Bᶜ hB.compl
  linarith

theorem aux_lem_borel_weights_locality_cross_cross_nonpos_disjoint (Gamma : EnergyMeasure E) (halg : IsCoreAlgebra E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hunonneg : ∀ᵐ x ∂m, 0 ≤ u x) (hvnonneg : ∀ᵐ x ∂m, 0 ≤ v x)
    (hdisjoint : ∀ᵐ x ∂m, u x = 0 ∨ v x = 0)
    (B : Set X) (hB : MeasurableSet B) : Gamma.cross u v B ≤ 0 := by
  have hbound : ∀ t : ℝ, 0 < t → t * (2 * Gamma.cross u v B) ≤ Gamma.cross u u B := by
    intro t ht
    have htv : t • v ∈ E.domain := E.domain.smul_mem t hv
    have hw : t • v - u ∈ E.domain := E.domain.sub_mem htv hu
    have hrep : ⇑(t • v) =ᵐ[m] fun x : X => max ((t • v - u) x) 0 := by
      filter_upwards [Lp.coeFn_smul t v, Lp.coeFn_sub (t • v) u,
        hunonneg, hvnonneg, hdisjoint] with x hsmul hsub hux hvx hdis
      simp only [Pi.smul_apply, smul_eq_mul] at hsmul
      simp only [Pi.sub_apply] at hsub
      rw [hsub, hsmul]
      rcases hdis with hxu | hxv
      · rw [hxu, sub_zero, max_eq_left (mul_nonneg ht.le hvx)]
      · rw [hxv, mul_zero, zero_sub, max_eq_right (neg_nonpos.mpr hux)]
    have hq : Gamma.cross (t • v) (t • v) B ≤
        Gamma.cross (t • v - u) (t • v - u) B :=
      (aux_lem_borel_weights_locality_cross_measureContraction_pos Gamma halg (t • v - u) hw (t • v) hrep).2 B hB
    rw [aux_lem_borel_weights_locality_cross_cross_smul_self_apply Gamma hv t B,
      aux_lem_borel_weights_locality_cross_cross_sub_self_apply Gamma htv hu B,
      aux_lem_borel_weights_locality_cross_cross_smul_self_apply Gamma hv t B,
      aux_lem_borel_weights_locality_cross_cross_smul_left Gamma hv hu t, smul_apply, smul_eq_mul,
      Gamma.cross_symm v hv u hu] at hq
    nlinarith
  have hsign : 2 * Gamma.cross u v B ≤ 0 :=
    aux_lem_borel_weights_locality_cross_nonpositive_of_linear_bound (Gamma.cross u u B) (2 * Gamma.cross u v B) hbound
  linarith

theorem aux_lem_borel_weights_locality_cross_cross_zero_nonnegative_disjoint (Gamma : EnergyMeasure E)
    (halg : IsCoreAlgebra E) (hloc : IsStronglyLocal E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hucompact : HasCompactSupportAE m u) (hvcompact : HasCompactSupportAE m v)
    (hunonneg : ∀ᵐ x ∂m, 0 ≤ u x) (hvnonneg : ∀ᵐ x ∂m, 0 ≤ v x)
    (W : Set X) (hW : IsOpen W)
    (hvzero : ∀ᵐ x ∂m, x ∉ W → v x = 0)
    (huzero : ∀ᵐ x ∂m, x ∈ W → u x = 0) : Gamma.cross u v = 0 := by
  have huniv : Gamma.cross u v Set.univ = 0 := by
    rw [Gamma.cross_univ u hu v hv]
    exact hloc u hu v hv hucompact hvcompact 0 W hW hvzero huzero
  apply aux_lem_borel_weights_locality_cross_signed_eq_zero_of_nonpos (Gamma.cross u v) huniv
  intro B hB
  apply aux_lem_borel_weights_locality_cross_cross_nonpos_disjoint Gamma halg hu hv hunonneg hvnonneg _ B hB
  filter_upwards [hvzero, huzero] with x hvx hux
  by_cases hx : x ∈ W
  · exact Or.inl (hux hx)
  · exact Or.inr (hvx hx)

theorem aux_lem_borel_weights_locality_cross_cross_zero_of_ae_zero_on_open (Gamma : EnergyMeasure E)
    (halg : IsCoreAlgebra E) (hloc : IsStronglyLocal E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hucompact : HasCompactSupportAE m u) (hvcompact : HasCompactSupportAE m v)
    (W : Set X) (hW : IsOpen W)
    (hvzero : ∀ᵐ x ∂m, x ∉ W → v x = 0)
    (huzero : ∀ᵐ x ∂m, x ∈ W → u x = 0) : Gamma.cross u v = 0 := by
  have hup : Lp.posPart u ∈ E.domain := aux_lem_borel_weights_locality_cross_pos_mem Gamma halg hu
  have hun : Lp.negPart u ∈ E.domain := aux_lem_borel_weights_locality_cross_neg_mem Gamma halg hu
  have hvp : Lp.posPart v ∈ E.domain := aux_lem_borel_weights_locality_cross_pos_mem Gamma halg hv
  have hvn : Lp.negPart v ∈ E.domain := aux_lem_borel_weights_locality_cross_neg_mem Gamma halg hv
  have huc : HasCompactSupportAE m (Lp.posPart u) ∧ HasCompactSupportAE m (Lp.negPart u) :=
    aux_lem_borel_weights_locality_cross_parts_compact hucompact
  have hvc : HasCompactSupportAE m (Lp.posPart v) ∧ HasCompactSupportAE m (Lp.negPart v) :=
    aux_lem_borel_weights_locality_cross_parts_compact hvcompact
  have hu0 : (∀ᵐ x ∂m, x ∈ W → Lp.posPart u x = 0) ∧
      (∀ᵐ x ∂m, x ∈ W → Lp.negPart u x = 0) :=
    aux_lem_borel_weights_locality_cross_parts_zero u (fun x : X => x ∈ W) huzero
  have hv0 : (∀ᵐ x ∂m, x ∉ W → Lp.posPart v x = 0) ∧
      (∀ᵐ x ∂m, x ∉ W → Lp.negPart v x = 0) :=
    aux_lem_borel_weights_locality_cross_parts_zero v (fun x : X => x ∉ W) hvzero
  have hpp : Gamma.cross (Lp.posPart u) (Lp.posPart v) = 0 :=
    aux_lem_borel_weights_locality_cross_cross_zero_nonnegative_disjoint Gamma halg hloc hup hvp huc.1 hvc.1
      (aux_lem_borel_weights_locality_cross_parts_nonnegative u).1 (aux_lem_borel_weights_locality_cross_parts_nonnegative v).1 W hW hv0.1 hu0.1
  have hpn : Gamma.cross (Lp.posPart u) (Lp.negPart v) = 0 :=
    aux_lem_borel_weights_locality_cross_cross_zero_nonnegative_disjoint Gamma halg hloc hup hvn huc.1 hvc.2
      (aux_lem_borel_weights_locality_cross_parts_nonnegative u).1 (aux_lem_borel_weights_locality_cross_parts_nonnegative v).2 W hW hv0.2 hu0.1
  have hnp : Gamma.cross (Lp.negPart u) (Lp.posPart v) = 0 :=
    aux_lem_borel_weights_locality_cross_cross_zero_nonnegative_disjoint Gamma halg hloc hun hvp huc.2 hvc.1
      (aux_lem_borel_weights_locality_cross_parts_nonnegative u).2 (aux_lem_borel_weights_locality_cross_parts_nonnegative v).1 W hW hv0.1 hu0.2
  have hnn : Gamma.cross (Lp.negPart u) (Lp.negPart v) = 0 :=
    aux_lem_borel_weights_locality_cross_cross_zero_nonnegative_disjoint Gamma halg hloc hun hvn huc.2 hvc.2
      (aux_lem_borel_weights_locality_cross_parts_nonnegative u).2 (aux_lem_borel_weights_locality_cross_parts_nonnegative v).2 W hW hv0.2 hu0.2
  calc
    Gamma.cross u v =
        Gamma.cross (Lp.posPart u - Lp.negPart u) (Lp.posPart v - Lp.negPart v) := by
      rw [aux_lem_borel_weights_locality_cross_parts_decomposition u, aux_lem_borel_weights_locality_cross_parts_decomposition v]
    _ = 0 := by
      rw [aux_lem_borel_weights_locality_cross_cross_sub_left Gamma hup hun (E.domain.sub_mem hvp hvn),
        aux_lem_borel_weights_locality_cross_cross_sub_right Gamma hup hvp hvn,
        aux_lem_borel_weights_locality_cross_cross_sub_right Gamma hun hvp hvn, hpp, hpn, hnp, hnn]
      simp only [sub_self]

theorem aux_lem_borel_weights_locality_cross_cross_nonneg_capped (Gamma : EnergyMeasure E) (halg : IsCoreAlgebra E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (c : ℝ) (hc : 0 ≤ c) (hucap : ∀ᵐ x ∂m, u x ≤ c)
    (hvnonneg : ∀ᵐ x ∂m, 0 ≤ v x) (W : Set X)
    (hvzero : ∀ᵐ x ∂m, x ∉ W → v x = 0)
    (huconst : ∀ᵐ x ∂m, x ∈ W → u x = c)
    (B : Set X) (hB : MeasurableSet B) : 0 ≤ Gamma.cross u v B := by
  have hbound : ∀ t : ℝ, 0 < t → t * (-2 * Gamma.cross u v B) ≤ Gamma.cross v v B := by
    intro t ht
    have htu : t • u ∈ E.domain := E.domain.smul_mem t hu
    have hw : t • u + v ∈ E.domain := E.domain.add_mem htu hv
    have hrep : ⇑(t • u) =ᵐ[m] fun x : X => min ((t • u + v) x) (t * c) := by
      filter_upwards [Lp.coeFn_smul t u, Lp.coeFn_add (t • u) v,
        hucap, hvnonneg, hvzero, huconst] with x hsmul hadd hcap hvx hv0 hu0
      simp only [Pi.smul_apply, smul_eq_mul] at hsmul
      simp only [Pi.add_apply] at hadd
      rw [hadd, hsmul]
      by_cases hx : x ∈ W
      · rw [hu0 hx, min_eq_right (le_add_of_nonneg_right hvx)]
      · rw [hv0 hx, add_zero, min_eq_left (mul_le_mul_of_nonneg_left hcap ht.le)]
    have hq : Gamma.cross (t • u) (t • u) B ≤
        Gamma.cross (t • u + v) (t • u + v) B :=
      (aux_lem_borel_weights_locality_cross_measureContraction_min Gamma halg (t * c) (mul_nonneg ht.le hc)
        (t • u + v) hw (t • u) hrep).2 B hB
    rw [aux_lem_borel_weights_locality_cross_cross_smul_self_apply Gamma hu t B,
      aux_lem_borel_weights_locality_cross_cross_add_self_apply Gamma htu hv B,
      aux_lem_borel_weights_locality_cross_cross_smul_self_apply Gamma hu t B,
      aux_lem_borel_weights_locality_cross_cross_smul_left Gamma hu hv t, smul_apply, smul_eq_mul] at hq
    nlinarith
  have hsign : -2 * Gamma.cross u v B ≤ 0 :=
    aux_lem_borel_weights_locality_cross_nonpositive_of_linear_bound (Gamma.cross v v B) (-2 * Gamma.cross u v B) hbound
  linarith

theorem aux_lem_borel_weights_locality_cross_cross_zero_capped_nonnegative (Gamma : EnergyMeasure E)
    (halg : IsCoreAlgebra E) (hloc : IsStronglyLocal E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hucompact : HasCompactSupportAE m u) (hvcompact : HasCompactSupportAE m v)
    (c : ℝ) (hc : 0 ≤ c) (hucap : ∀ᵐ x ∂m, u x ≤ c)
    (hvnonneg : ∀ᵐ x ∂m, 0 ≤ v x) (W : Set X) (hW : IsOpen W)
    (hvzero : ∀ᵐ x ∂m, x ∉ W → v x = 0)
    (huconst : ∀ᵐ x ∂m, x ∈ W → u x = c) : Gamma.cross u v = 0 := by
  have huniv : Gamma.cross u v Set.univ = 0 := by
    rw [Gamma.cross_univ u hu v hv]
    exact hloc u hu v hv hucompact hvcompact c W hW hvzero huconst
  exact aux_lem_borel_weights_locality_cross_signed_eq_zero_of_nonneg (Gamma.cross u v) huniv
    (aux_lem_borel_weights_locality_cross_cross_nonneg_capped Gamma halg hu hv c hc hucap hvnonneg W hvzero huconst)

theorem aux_lem_borel_weights_locality_cross_cross_zero_capped (Gamma : EnergyMeasure E)
    (halg : IsCoreAlgebra E) (hloc : IsStronglyLocal E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hucompact : HasCompactSupportAE m u) (hvcompact : HasCompactSupportAE m v)
    (c : ℝ) (hc : 0 ≤ c) (hucap : ∀ᵐ x ∂m, u x ≤ c)
    (W : Set X) (hW : IsOpen W)
    (hvzero : ∀ᵐ x ∂m, x ∉ W → v x = 0)
    (huconst : ∀ᵐ x ∂m, x ∈ W → u x = c) : Gamma.cross u v = 0 := by
  have hvp : Lp.posPart v ∈ E.domain := aux_lem_borel_weights_locality_cross_pos_mem Gamma halg hv
  have hvn : Lp.negPart v ∈ E.domain := aux_lem_borel_weights_locality_cross_neg_mem Gamma halg hv
  have hvc : HasCompactSupportAE m (Lp.posPart v) ∧ HasCompactSupportAE m (Lp.negPart v) :=
    aux_lem_borel_weights_locality_cross_parts_compact hvcompact
  have hv0 : (∀ᵐ x ∂m, x ∉ W → Lp.posPart v x = 0) ∧
      (∀ᵐ x ∂m, x ∉ W → Lp.negPart v x = 0) :=
    aux_lem_borel_weights_locality_cross_parts_zero v (fun x : X => x ∉ W) hvzero
  have hp : Gamma.cross u (Lp.posPart v) = 0 :=
    aux_lem_borel_weights_locality_cross_cross_zero_capped_nonnegative Gamma halg hloc hu hvp hucompact hvc.1
      c hc hucap (aux_lem_borel_weights_locality_cross_parts_nonnegative v).1 W hW hv0.1 huconst
  have hn : Gamma.cross u (Lp.negPart v) = 0 :=
    aux_lem_borel_weights_locality_cross_cross_zero_capped_nonnegative Gamma halg hloc hu hvn hucompact hvc.2
      c hc hucap (aux_lem_borel_weights_locality_cross_parts_nonnegative v).2 W hW hv0.2 huconst
  calc
    Gamma.cross u v = Gamma.cross u (Lp.posPart v - Lp.negPart v) := by
      rw [aux_lem_borel_weights_locality_cross_parts_decomposition v]
    _ = 0 := by
      rw [aux_lem_borel_weights_locality_cross_cross_sub_right Gamma hu hvp hvn, hp, hn, sub_self]

theorem aux_lem_borel_weights_locality_cross_cross_zero_nonnegative_constant (Gamma : EnergyMeasure E)
    (halg : IsCoreAlgebra E) (hloc : IsStronglyLocal E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hucompact : HasCompactSupportAE m u) (hvcompact : HasCompactSupportAE m v)
    (c : ℝ) (hc : 0 ≤ c) (W : Set X) (hW : IsOpen W)
    (hvzero : ∀ᵐ x ∂m, x ∉ W → v x = 0)
    (huconst : ∀ᵐ x ∂m, x ∈ W → u x = c) : Gamma.cross u v = 0 := by
  have hLip : LipschitzWith 1 (fun t : ℝ => min t c) := LipschitzWith.id.min_const c
  let a : Lp ℝ 2 m := hLip.compLp (min_eq_left hc) u
  have harep : ⇑a =ᵐ[m] fun x : X => min (u x) c := by
    simpa only [Function.comp_def] using hLip.coeFn_compLp (min_eq_left hc) u
  have ha : a ∈ E.domain := (aux_lem_borel_weights_locality_cross_measureContraction_min Gamma halg c hc u hu a harep).1
  have hacompact : HasCompactSupportAE m a :=
    aux_lem_borel_weights_locality_cross_compact_of_ae_comp hucompact (fun t : ℝ => min t c) (min_eq_left hc) harep
  have hacap : ∀ᵐ x ∂m, a x ≤ c := by
    filter_upwards [harep] with x hx
    rw [hx]
    exact min_le_right _ _
  have haconst : ∀ᵐ x ∂m, x ∈ W → a x = c := by
    filter_upwards [harep, huconst] with x hx hu0
    intro hxW
    rw [hx, hu0 hxW, min_self]
  have hd0 : ∀ᵐ x ∂m, x ∈ W → (u - a) x = 0 := by
    filter_upwards [Lp.coeFn_sub u a, huconst, haconst] with x hsub hu0 ha0
    intro hxW
    simpa only [Pi.sub_apply, hu0 hxW, ha0 hxW, sub_self] using hsub
  have hd : Gamma.cross (u - a) v = 0 :=
    aux_lem_borel_weights_locality_cross_cross_zero_of_ae_zero_on_open Gamma halg hloc (E.domain.sub_mem hu ha) hv
      (aux_lem_borel_weights_locality_cross_compact_sub hucompact hacompact) hvcompact W hW hvzero hd0
  have ha0 : Gamma.cross a v = 0 :=
    aux_lem_borel_weights_locality_cross_cross_zero_capped Gamma halg hloc ha hv hacompact hvcompact c hc hacap
      W hW hvzero haconst
  rw [aux_lem_borel_weights_locality_cross_cross_sub_left Gamma hu ha hv, ha0, sub_zero] at hd
  exact hd

theorem aux_lem_borel_weights_locality_cross_cross_eq_zero_of_strong_locality (Gamma : EnergyMeasure E)
    (halg : IsCoreAlgebra E) (hloc : IsStronglyLocal E)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (hucompact : HasCompactSupportAE m u) (hvcompact : HasCompactSupportAE m v)
    (c : ℝ) (W : Set X) (hW : IsOpen W)
    (hvzero : ∀ᵐ x ∂m, x ∉ W → v x = 0)
    (huconst : ∀ᵐ x ∂m, x ∈ W → u x = c) : Gamma.cross u v = 0 := by
  by_cases hc : 0 ≤ c
  · exact aux_lem_borel_weights_locality_cross_cross_zero_nonnegative_constant Gamma halg hloc hu hv hucompact hvcompact
      c hc W hW hvzero huconst
  · have hnc : 0 ≤ -c := neg_nonneg.mpr (le_of_not_ge hc)
    have hnegconst : ∀ᵐ x ∂m, x ∈ W → (-u) x = -c := by
      filter_upwards [Lp.coeFn_neg u, huconst] with x hneg hx
      intro hxW
      simpa only [Pi.neg_apply, hx hxW] using hneg
    have hcross : Gamma.cross (-u) v = 0 :=
      aux_lem_borel_weights_locality_cross_cross_zero_nonnegative_constant Gamma halg hloc (E.domain.neg_mem hu) hv
        (aux_lem_borel_weights_locality_cross_compact_neg hucompact) hvcompact (-c) hnc W hW hvzero hnegconst
    rw [aux_lem_borel_weights_locality_cross_cross_neg_left Gamma hu hv] at hcross
    exact neg_eq_zero.mp hcross

omit [TopologicalSpace X] in
theorem aux_lem_borel_weights_locality_cross_signed_integral_zero {X : Type*} [MeasurableSpace X] [_top : TopologicalSpace X]
    (B : Set X) (f : X → ℝ) :
    signedIntegralOn (0 : SignedMeasure X) B f = 0 := by
  simp [signedIntegralOn, SignedMeasure.toJordanDecomposition_zero]

theorem lem_borel_weights_locality_cross
    (E : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Gamma : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E.toClosedForm)
    (halg : _root_.SubdiffusiveProcess.DirichletForm.IsCoreAlgebra E.toClosedForm)
    (g : SpatialCoordinates d → ℝ) (_hg : Measurable g)
    (M : ℝ) (_hgbdd : ∀ x : SpatialCoordinates d, |g x| ≤ M)
    (hloc : _root_.SubdiffusiveProcess.DirichletForm.IsStronglyLocal E.toClosedForm)
    (u v : Lp ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d))))
    (hu : u ∈ E.toClosedForm.domain) (hv : v ∈ E.toClosedForm.domain)
    (hucompact : _root_.SubdiffusiveProcess.DirichletForm.HasCompactSupportAE
      (volume.restrict (Q : Set (SpatialCoordinates d))) u)
    (hvcompact : _root_.SubdiffusiveProcess.DirichletForm.HasCompactSupportAE
      (volume.restrict (Q : Set (SpatialCoordinates d))) v)
    (c : ℝ) (W : Set (SpatialCoordinates d)) (hW : IsOpen W)
    (hvzero : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      x ∉ W → v x = 0)
    (huconst : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      x ∈ W → u x = c) :
    _root_.SubdiffusiveProcess.DirichletForm.signedIntegralOn (Gamma.cross u v) Set.univ
      (fun x => Real.exp (g x)) = 0 := by
  have hcross : Gamma.cross u v = 0 :=
    aux_lem_borel_weights_locality_cross_cross_eq_zero_of_strong_locality Gamma halg hloc hu hv
      hucompact hvcompact c W hW hvzero huconst
  rw [hcross]
  exact aux_lem_borel_weights_locality_cross_signed_integral_zero Set.univ
    (fun x => Real.exp (g x))


end SubdiffusiveProcess.Paper

