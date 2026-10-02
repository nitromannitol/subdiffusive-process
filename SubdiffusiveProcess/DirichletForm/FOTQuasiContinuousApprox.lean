import SubdiffusiveProcess.DirichletForm.FOTQuasiContinuousConvex
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal
noncomputable section
namespace DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

def qcRate (n : ℕ) : ℝ := (1 / 2) ^ n

lemma qcRate_pos (n : ℕ) : 0 < qcRate n := pow_pos (by norm_num) _
lemma qcRate_nonneg (n : ℕ) : 0 ≤ qcRate n := (qcRate_pos n).le
lemma qcRate_next (n : ℕ) : qcRate (n + 1) ≤ qcRate n := by
  unfold qcRate
  rw [pow_succ]
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) n]
lemma qcRate_tendsto : Tendsto qcRate atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
lemma qcRate_summable : Summable qcRate := summable_geometric_two
lemma qcRate_capacity_summable : (∑' n, ENNReal.ofReal (2 * qcRate n)) ≠ ⊤ := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (by norm_num) (qcRate_nonneg n)) (qcRate_summable.mul_left 2)]
  exact ENNReal.ofReal_ne_top

/-- Summably small exceptional sets have a capacity-null tail intersection. -/
lemma qc_capacity_tail {F : _root_.DirichletForm m} {U : Set X} (A : ℕ → Set X)
    (hA : ∀ n, coreCapacity F U (A n) ≤ ENNReal.ofReal (2 * qcRate n)) :
    coreCapacity F U (⋂ N, ⋃ k, A (k + N)) = 0 ∧
      Tendsto (fun N => coreCapacity F U (⋃ k, A (k + N))) atTop (𝓝 0) := by
  have hbound : ∀ N, coreCapacity F U (⋃ k, A (k + N)) ≤
      ∑' k, ENNReal.ofReal (2 * qcRate (k + N)) := fun N =>
    (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun k => hA (k + N))
  have ht := ENNReal.tendsto_sum_nat_add _ qcRate_capacity_summable
  have hlim := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun N => zero_le _) hbound
  refine ⟨le_antisymm ?_ (zero_le _), hlim⟩
  exact ge_of_tendsto hlim (Eventually.of_forall fun N =>
    (coreCapacity F U).mono (iInter_subset _ N))

lemma qc_small_difference {A : ℕ → Set X} {f g : ℕ → X → ℝ}
    (hA : ∀ n, A n = {x | qcRate n < |f n x - g n x|}) {x : X}
    (hx : x ∉ ⋂ N, ⋃ k, A (k + N)) :
    Tendsto (fun n => f n x - g n x) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := not_forall.mp (fun hh => hx (mem_iInter.mpr hh))
  have hbound : ∀ᶠ n in atTop, ‖f n x - g n x‖ ≤ qcRate n := by
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [Real.norm_eq_abs]
    apply le_of_not_gt
    intro hh
    apply hN
    exact mem_iUnion.mpr ⟨n - N, by simpa [Nat.sub_add_cancel hn, hA] using hh⟩
  exact squeeze_zero_norm' hbound qcRate_tendsto

lemma qc_fast_core_approx (F : _root_.DirichletForm m) {U : Set X} (h : Data F U)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) :
    ∃ (un : ℕ → Lp ℝ 2 m) (fn : ℕ → X → ℝ),
      (∀ n, F.toClosedForm.MemCoreOn U (un n)) ∧
      (∀ n, Continuous (fn n) ∧ HasCompactSupport (fn n) ∧ tsupport (fn n) ⊆ U ∧
        ⇑(un n) =ᵐ[m] fn n) ∧
      (∀ n, Real.sqrt (F.energyNormSq (un n - u)) ≤ qcRate n ^ 2) ∧
      Tendsto (fun n => F.energyNormSq (un n - u)) atTop (𝓝 0) ∧
      Tendsto un atTop (𝓝 u) := by
  obtain ⟨C, hC⟩ := h.core
  choose un hun hgap using fun n => hC.denseEnergy u hu (qcRate n ^ 4) (pow_pos (qcRate_pos n) 4)
  have hcore := fun n => hC.memCoreOn _ (hun n)
  choose fn hf hfc hfU hfae using fun n => (hcore n).2
  have he : ∀ n, F.energyNormSq (un n - u) ≤ qcRate n ^ 4 := by
    intro n
    rw [F.energyNormSq_sub_comm (hcore n).1 hu]
    exact (hgap n).le
  have hs : ∀ n, Real.sqrt (F.energyNormSq (un n - u)) ≤ qcRate n ^ 2 := by
    intro n
    apply (Real.sqrt_le_iff).mpr
    refine ⟨sq_nonneg _, ?_⟩
    calc
      _ ≤ qcRate n ^ 4 := he n
      _ = _ := by ring
  have ht : Tendsto (fun n => F.energyNormSq (un n - u)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => F.energyNormSq_nonneg (F.domain.sub_mem (hcore n).1 hu)) he
    simpa using qcRate_tendsto.pow 4
  have hlp : Tendsto un atTop (𝓝 u) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hh : Tendsto (fun n => ‖un n - u‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun n => sq_nonneg _) (fun n => F.sq_norm_le_energyNormSq
        (F.domain.sub_mem (hcore n).1 hu)) ht
    have hh' := Real.continuous_sqrt.tendsto 0 |>.comp hh
    simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hh'
  exact ⟨un, fn, hcore, fun n => ⟨hf n, hfc n, hfU n, hfae n⟩, hs, ht, hlp⟩

lemma qc_fast_subsequence (F : _root_.DirichletForm m) {u : Lp ℝ 2 m}
    (un : ℕ → Lp ℝ 2 m)
    (he : Tendsto (fun n => F.energyNormSq (un n - u)) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∀ n, Real.sqrt (F.energyNormSq (un (s n) - u)) ≤ qcRate n ^ 2 := by
  obtain ⟨s, hs, hse⟩ := he.subseq_mem (V := fun n => Iio (qcRate n ^ 4))
    (fun n => Iio_mem_nhds (pow_pos (qcRate_pos n) 4))
  refine ⟨s, hs, fun n => Real.sqrt_le_iff.mpr ⟨sq_nonneg _, ?_⟩⟩
  have hh : F.energyNormSq (un (s n) - u) ≤ qcRate n ^ 4 := (hse n).le
  change F.energyNormSq (un (s n) - u) ≤ qcRate n ^ 4 at hh
  nlinarith only [hh]

lemma qc_level_difference {F : _root_.DirichletForm m} {U : Set X}
    {u p r : Lp ℝ 2 m} (hu : u ∈ F.domain)
    (hp : F.toClosedForm.MemCoreOn U p) (hr : F.toClosedForm.MemCoreOn U r)
    {pc rc : X → ℝ}
    (hpc : Continuous pc ∧ HasCompactSupport pc ∧ tsupport pc ⊆ U ∧ ⇑p =ᵐ[m] pc)
    (hrc : Continuous rc ∧ HasCompactSupport rc ∧ tsupport rc ⊆ U ∧ ⇑r =ᵐ[m] rc)
    (n : ℕ) (hep : Real.sqrt (F.energyNormSq (p - u)) ≤ qcRate n ^ 2)
    (her : Real.sqrt (F.energyNormSq (r - u)) ≤ qcRate n ^ 2) :
    coreCapacity F U {x | qcRate n < |pc x - rc x|} ≤ ENNReal.ofReal (2 * qcRate n) := by
  have hcost : Real.sqrt (F.energyNormSq (p - r)) ≤ 2 * qcRate n ^ 2 :=
    (F.sqrt_energyNormSq_sub_le hp.1 hu hr.1).trans (by
      rw [F.energyNormSq_sub_comm hu hr.1]
      linarith)
  have hlevel := coreCapacity_level F (by simpa only [sub_eq_add_neg, neg_one_smul] using hp.add (hr.smul (-1))) (hpc.1.sub hrc.1) (hpc.2.1.sub hrc.2.1)
    ((tsupport_sub pc rc).trans (union_subset hpc.2.2.1 hrc.2.2.1))
    ((Lp.coeFn_sub p r).trans (hpc.2.2.2.sub hrc.2.2.2)) (qcRate_pos n)
  refine hlevel.trans (ENNReal.ofReal_le_ofReal ?_)
  apply (div_le_iff₀ (qcRate_pos n)).mpr
  nlinarith only [hcost]

end DirichletForm.FOTConstruction
