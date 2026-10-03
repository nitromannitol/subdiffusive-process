module

public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

/-!
# Common majorant from decaying moments

Paper lines 1985--1988 (`lem_cutoffs`). Represented variables whose `L^q` norms
decay geometrically along a strictly increasing cutoff sequence, pushed forward
from one fixed law, are eventually below one almost surely (Markov and
Borel--Cantelli). Adding finitely many represented constants gives one
measurable majorant with uniform moments of every requested order and pathwise
boundedness on one measurable full-measure event.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal BigOperators Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Finite sums of absolute values keep a uniform moment bound at every
exponent (the quasi-triangle constant `LpAddConst` covers exponents below one). -/
theorem aux_cutoffs_finset_abs_sum_moment
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ℝ≥0∞)
    (c : ι → ℕ → Ω → ℝ) (F : Finset ι)
    (hmem : ∀ i ∈ F, ∀ n, MemLp (c i n) p P)
    (hbd : ∀ i ∈ F, ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ n, eLpNorm (c i n) p P ≤ B) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ n,
      MemLp (fun om => ∑ i ∈ F, |c i n om|) p P ∧
        eLpNorm (fun om => ∑ i ∈ F, |c i n om|) p P ≤ B := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨0, ENNReal.zero_ne_top, fun n => ?_⟩
    simp only [Finset.sum_empty]
    exact ⟨MemLp.zero', by simp⟩
  | @insert a s ha ih =>
    obtain ⟨Bs, hBs, hs⟩ := ih (fun i hi => hmem i (Finset.mem_insert_of_mem hi))
      (fun i hi => hbd i (Finset.mem_insert_of_mem hi))
    obtain ⟨Ba, hBa, ha'⟩ := hbd a (Finset.mem_insert_self a s)
    refine ⟨ENNReal.LpAddConst p * (Ba + Bs),
      ENNReal.mul_ne_top (ENNReal.LpAddConst_lt_top p).ne (ENNReal.add_ne_top.2 ⟨hBa, hBs⟩),
      fun n => ?_⟩
    have hma : MemLp (fun om => |c a n om|) p P := by
      have h := (hmem a (Finset.mem_insert_self a s) n).norm
      simpa only [Real.norm_eq_abs] using h
    have hea : eLpNorm (fun om => |c a n om|) p P = eLpNorm (c a n) p P := by
      have h := eLpNorm_norm (p := p) (μ := P) (c a n)
        (hmem a (Finset.mem_insert_self a s) n).aestronglyMeasurable
      simpa only [Real.norm_eq_abs] using h
    have hfun : (fun om => ∑ i ∈ insert a s, |c i n om|) =
        (fun om => |c a n om|) + (fun om => ∑ i ∈ s, |c i n om|) := by
      funext om
      simp only [Pi.add_apply, Finset.sum_insert ha]
    rw [hfun]
    refine ⟨hma.add (hs n).1, ?_⟩
    calc eLpNorm ((fun om => |c a n om|) + (fun om => ∑ i ∈ s, |c i n om|)) p P
        ≤ ENNReal.LpAddConst p * (eLpNorm (fun om => |c a n om|) p P +
            eLpNorm (fun om => ∑ i ∈ s, |c i n om|) p P) :=
          eLpNorm_add_le' p
      _ ≤ ENNReal.LpAddConst p * (Ba + Bs) := by
          rw [hea]
          exact mul_le_mul_of_nonneg_left (add_le_add (ha' n) (hs n).2) bot_le

/-- Markov and Borel--Cantelli: geometrically decaying `L^q` norms force
`|Y n| < 1` eventually, almost surely. -/
theorem aux_cutoffs_eventually_lt_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, AEStronglyMeasurable (Y n) P)
    (q : ℝ) (hq : 0 < q) (A r : ℝ) (hA : 0 ≤ A) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hbound : ∀ n, eLpNorm (Y n) (ENNReal.ofReal q) P ≤ ENNReal.ofReal (A * r ^ n)) :
    ∀ᵐ om ∂P, ∀ᶠ n in atTop, |Y n om| < 1 := by
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.2 hq).ne'
  let s : ℕ → Set Ω := fun n => {om | (1 : ℝ≥0∞) ≤ ‖Y n om‖ₑ}
  have hs : ∀ n, P (s n) ≤ ENNReal.ofReal (A ^ q) * ENNReal.ofReal (r ^ q) ^ n := by
    intro n
    have h := meas_ge_le_mul_pow_eLpNorm_enorm (f := Y n) P hq0 ENNReal.ofReal_ne_top
      (ε := 1) one_ne_zero (fun h => absurd h ENNReal.one_ne_top)
    rw [inv_one, ENNReal.one_rpow, one_mul, ENNReal.toReal_ofReal hq.le] at h
    have hArn : 0 ≤ A * r ^ n := mul_nonneg hA (pow_nonneg hr0 n)
    calc P (s n) ≤ eLpNorm (Y n) (ENNReal.ofReal q) P ^ q := h
      _ ≤ ENNReal.ofReal (A * r ^ n) ^ q := ENNReal.rpow_le_rpow (hbound n) hq.le
      _ = ENNReal.ofReal ((A * r ^ n) ^ q) := ENNReal.ofReal_rpow_of_nonneg hArn hq.le
      _ = ENNReal.ofReal (A ^ q * (r ^ q) ^ n) := by
          congr 1
          rw [Real.mul_rpow hA (pow_nonneg hr0 n), ← Real.rpow_natCast r n,
            ← Real.rpow_natCast (r ^ q) n, ← Real.rpow_mul hr0, ← Real.rpow_mul hr0,
            mul_comm (n : ℝ) q]
      _ = ENNReal.ofReal (A ^ q) * ENNReal.ofReal (r ^ q) ^ n := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hA q),
            ENNReal.ofReal_pow (Real.rpow_nonneg hr0 q)]
  have hlt : ENNReal.ofReal (r ^ q) < 1 :=
    ENNReal.ofReal_lt_one.2 (Real.rpow_lt_one hr0 hr1 hq)
  have hsum : ∑' n, P (s n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hs)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hlt).ne')
  filter_upwards [ae_eventually_notMem hsum] with om hom
  filter_upwards [hom] with n hn
  have hn' : ‖Y n om‖ₑ < 1 := not_le.1 hn
  rw [Real.enorm_eq_ofReal_abs] at hn'
  exact ENNReal.ofReal_lt_one.1 hn'

/-- An eventually small real sequence is bounded. -/
theorem aux_cutoffs_bound_of_eventually
    (y : ℕ → ℝ) (h : ∀ᶠ n in atTop, |y n| < 1) :
    ∃ B : ℝ, ∀ n, |y n| ≤ B := by
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.1 h
  refine ⟨(∑ m ∈ Finset.range n0, |y m|) + 1, fun n => ?_⟩
  have hsum : 0 ≤ ∑ m ∈ Finset.range n0, |y m| :=
    Finset.sum_nonneg (fun m _ => abs_nonneg _)
  by_cases hn : n < n0
  · have := Finset.single_le_sum (f := fun m => |y m|) (fun m _ => abs_nonneg (y m))
      (Finset.mem_range.2 hn)
    linarith
  · have := hn0 n (not_lt.1 hn)
    linarith

/-- Generic common majorant. The represented environments `env n` push `P`
forward to `nu`; `X N` has geometrically decaying `L^q` norms under `nu`; the
cutoffs are strictly increasing. Then one measurable majorant dominates the
finitely many selected represented constants and the represented damped
variable `X (cutoff n) ∘ env n`, with uniform moments of every order in
`orders` and pathwise boundedness on one measurable full-measure subevent of
`G`. -/
theorem aux_cutoffs_common_majorant_core
    {Ω β Index : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P] (nu : Measure β)
    (cutoff : ℕ → ℕ) (hcut : StrictMono cutoff)
    (env : ℕ → Ω → β) (henv : ∀ n, Measurable (env n))
    (hlaw : ∀ n, Measure.map (env n) P = nu)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω) (hG : P Gᶜ = 0)
    (hcm : ∀ i n, Measurable (constants i n))
    (orders : Finset ℝ)
    (hmom : ∀ i : Index, ∀ p ∈ orders, ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      MemLp (constants i n) (ENNReal.ofReal p) P ∧
        eLpNorm (constants i n) (ENNReal.ofReal p) P ≤ ENNReal.ofReal B)
    (hbdd : ∀ i : Index, ∀ om ∈ G, ∃ Mb : ℝ, ∀ N : ℕ, |constants i N om| ≤ Mb)
    (F : Finset Index)
    (good : ℕ → β → Prop) (hgood : ∀ᵐ b ∂nu, ∀ N, good N b)
    (X : ℕ → β → ℝ) (q : ℝ) (hq : 1 ≤ q) (hqord : ∀ p ∈ orders, p ≤ q)
    (A r : ℝ) (hA : 0 ≤ A) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hXmem : ∀ N, MemLp (X N) (ENNReal.ofReal q) nu)
    (hXbd : ∀ N, eLpNorm (X N) (ENNReal.ofReal q) nu ≤ ENNReal.ofReal (A * r ^ N)) :
    ∃ KN : ℕ → Ω → ℝ, ∃ Ggood : Set Ω,
      MeasurableSet Ggood ∧ Ggood ⊆ G ∧ P (Ggoodᶜ) = 0 ∧
      (∀ n : ℕ, Measurable (KN n)) ∧
      (∀ n : ℕ, ∀ om : Ω, 1 ≤ KN n om) ∧
      (∀ p ∈ orders, ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ n : ℕ,
        MemLp (KN n) (ENNReal.ofReal p) P ∧
          eLpNorm (KN n) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cp) ∧
      (∀ om ∈ Ggood, BddAbove (Set.range (fun n : ℕ => KN n om))) ∧
      (∀ om ∈ Ggood, ∀ n : ℕ, ∀ i ∈ F, constants i n om ≤ KN n om) ∧
      (∀ om ∈ Ggood, ∀ n : ℕ,
        (∀ N, good N (env n om)) ∧ X (cutoff n) (env n om) ≤ KN n om) := by
  classical
  have hmp : ∀ n, MeasurePreserving (env n) P nu := fun n => ⟨henv n, hlaw n⟩
  -- the represented damped variable and a strongly measurable version
  let Y : ℕ → Ω → ℝ := fun n om => X (cutoff n) (env n om)
  have hYmem : ∀ n, MemLp (Y n) (ENNReal.ofReal q) P := fun n =>
    (hXmem (cutoff n)).comp_measurePreserving (hmp n)
  have hYnorm : ∀ n, eLpNorm (Y n) (ENNReal.ofReal q) P ≤ ENNReal.ofReal (A * r ^ n) := by
    intro n
    have heq : eLpNorm (Y n) (ENNReal.ofReal q) P =
        eLpNorm (X (cutoff n)) (ENNReal.ofReal q) nu :=
      eLpNorm_comp_measurePreserving (hXmem (cutoff n)).aestronglyMeasurable (hmp n)
    rw [heq]
    refine (hXbd (cutoff n)).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0 hr1.le (hcut.id_le n)) hA
  let Yv : ℕ → Ω → ℝ := fun n => (hYmem n).aestronglyMeasurable.mk (Y n)
  have hYv_sm : ∀ n, StronglyMeasurable (Yv n) := fun n => (hYmem n).aestronglyMeasurable.stronglyMeasurable_mk
  have hYv_ae : ∀ n, Y n =ᵐ[P] Yv n := fun n => (hYmem n).aestronglyMeasurable.ae_eq_mk
  have hYvmem : ∀ n, MemLp (Yv n) (ENNReal.ofReal q) P := fun n =>
    (hYmem n).ae_eq (hYv_ae n)
  have hYvnorm : ∀ n, eLpNorm (Yv n) (ENNReal.ofReal q) P ≤ ENNReal.ofReal (A * r ^ n) := by
    intro n
    rw [← eLpNorm_congr_ae (hYv_ae n)]
    exact hYnorm n
  -- Markov and Borel--Cantelli along the represented sequence
  have hsmall : ∀ᵐ om ∂P, ∀ᶠ n in atTop, |Yv n om| < 1 :=
    aux_cutoffs_eventually_lt_one P Yv (fun n => (hYv_sm n).aestronglyMeasurable) q
      (by linarith) A r hA hr0 hr1 hYvnorm
  -- the transported almost-sure event of the extrema
  have hgoodP : ∀ᵐ om ∂P, ∀ n, ∀ N, good N (env n om) := by
    rw [ae_all_iff]
    intro n
    exact ae_of_ae_map (henv n).aemeasurable (by rw [hlaw n]; exact hgood)
  have hYvall : ∀ᵐ om ∂P, ∀ n, Y n om = Yv n om := ae_all_iff.2 hYv_ae
  have hGae : ∀ᵐ om ∂P, om ∈ G :=
    (measure_eq_zero_iff_ae_notMem.1 hG).mono (fun om h => not_not.1 h)
  let Aset : Set Ω := {om | om ∈ G ∧ (∀ n, ∀ N, good N (env n om)) ∧
    (∀ n, Y n om = Yv n om) ∧ (∀ᶠ n in atTop, |Yv n om| < 1)}
  have hAae : ∀ᵐ om ∂P, om ∈ Aset := by
    filter_upwards [hGae, hgoodP, hYvall, hsmall] with om h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hAc : P Asetᶜ = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (hAae.mono fun om h hc => hc h)
  have hGgoodA : (toMeasurable P Asetᶜ)ᶜ ⊆ Aset := by
    intro om hom
    by_contra hna
    exact hom (subset_toMeasurable P Asetᶜ hna)
  -- the majorant
  let KN : ℕ → Ω → ℝ := fun n om => 1 + (∑ i ∈ F, |constants i n om|) + |Yv n om|
  have hsum_nonneg : ∀ n om, 0 ≤ ∑ i ∈ F, |constants i n om| := fun n om =>
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨KN, (toMeasurable P Asetᶜ)ᶜ, (measurableSet_toMeasurable P _).compl,
    fun om hom => (hGgoodA hom).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [compl_compl, measure_toMeasurable]
    exact hAc
  · intro n
    have hs : Measurable (fun om => ∑ i ∈ F, |constants i n om|) :=
      Finset.measurable_sum F (fun i _ => (hcm i n).abs)
    exact (measurable_const.add hs).add (hYv_sm n).measurable.abs
  · intro n om
    have h1 := hsum_nonneg n om
    have h2 := abs_nonneg (Yv n om)
    show 1 ≤ 1 + (∑ i ∈ F, |constants i n om|) + |Yv n om|
    linarith
  · -- uniform moments of every requested order
    intro p hp
    have hpq : ENNReal.ofReal p ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal (hqord p hp)
    have h1mem : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal p) P := memLp_const 1
    obtain ⟨B1, hB1ne, hB1⟩ : ∃ B1 : ℝ≥0∞, B1 ≠ ⊤ ∧
        eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal p) P ≤ B1 :=
      ⟨_, h1mem.eLpNorm_lt_top.ne, le_rfl⟩
    obtain ⟨BS, hBS, hS⟩ := aux_cutoffs_finset_abs_sum_moment P (ENNReal.ofReal p)
      constants F (fun i _ n => ((hmom i p hp).choose_spec.2 n).1)
      (fun i _ => ⟨ENNReal.ofReal (hmom i p hp).choose, ENNReal.ofReal_ne_top,
        fun n => ((hmom i p hp).choose_spec.2 n).2⟩)
    have hYp : ∀ n, MemLp (fun om => |Yv n om|) (ENNReal.ofReal p) P ∧
        eLpNorm (fun om => |Yv n om|) (ENNReal.ofReal p) P ≤ ENNReal.ofReal A := by
      intro n
      have hm : MemLp (Yv n) (ENNReal.ofReal p) P := (hYvmem n).mono_exponent hpq
      refine ⟨by simpa only [Real.norm_eq_abs] using hm.norm, ?_⟩
      have he : eLpNorm (fun om => |Yv n om|) (ENNReal.ofReal p) P =
          eLpNorm (Yv n) (ENNReal.ofReal p) P := by
        simpa only [Real.norm_eq_abs] using
          eLpNorm_norm (p := ENNReal.ofReal p) (μ := P) (Yv n)
            (hYv_sm n).aestronglyMeasurable
      rw [he]
      calc eLpNorm (Yv n) (ENNReal.ofReal p) P ≤ eLpNorm (Yv n) (ENNReal.ofReal q) P :=
            eLpNorm_le_eLpNorm_of_exponent_le hpq
        _ ≤ ENNReal.ofReal (A * r ^ n) := hYvnorm n
        _ ≤ ENNReal.ofReal A :=
            ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hA (pow_le_one₀ hr0 hr1.le))
    have hL : ENNReal.LpAddConst (ENNReal.ofReal p) ≠ ⊤ := (ENNReal.LpAddConst_lt_top _).ne
    have hBtot_ne : ENNReal.LpAddConst (ENNReal.ofReal p) *
        (ENNReal.LpAddConst (ENNReal.ofReal p) * (B1 + BS) + ENNReal.ofReal A) ≠ ⊤ :=
      ENNReal.mul_ne_top hL (ENNReal.add_ne_top.2
        ⟨ENNReal.mul_ne_top hL (ENNReal.add_ne_top.2 ⟨hB1ne, hBS⟩), ENNReal.ofReal_ne_top⟩)
    refine ⟨(ENNReal.LpAddConst (ENNReal.ofReal p) *
        (ENNReal.LpAddConst (ENNReal.ofReal p) * (B1 + BS) + ENNReal.ofReal A)).toReal,
      ENNReal.toReal_nonneg, fun n => ?_⟩
    rw [ENNReal.ofReal_toReal hBtot_ne]
    have hfun : KN n = ((fun _ : Ω => (1 : ℝ)) + fun om => ∑ i ∈ F, |constants i n om|) +
        fun om => |Yv n om| := rfl
    rw [hfun]
    have hm12 : MemLp ((fun _ : Ω => (1 : ℝ)) + fun om => ∑ i ∈ F, |constants i n om|)
        (ENNReal.ofReal p) P := h1mem.add (hS n).1
    refine ⟨hm12.add (hYp n).1, ?_⟩
    calc eLpNorm (((fun _ : Ω => (1 : ℝ)) + fun om => ∑ i ∈ F, |constants i n om|) +
          fun om => |Yv n om|) (ENNReal.ofReal p) P
        ≤ ENNReal.LpAddConst (ENNReal.ofReal p) *
            (eLpNorm ((fun _ : Ω => (1 : ℝ)) + fun om => ∑ i ∈ F, |constants i n om|)
              (ENNReal.ofReal p) P +
              eLpNorm (fun om => |Yv n om|) (ENNReal.ofReal p) P) :=
          eLpNorm_add_le' _
      _ ≤ ENNReal.LpAddConst (ENNReal.ofReal p) *
            (ENNReal.LpAddConst (ENNReal.ofReal p) * (B1 + BS) + ENNReal.ofReal A) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ (hYp n).2) bot_le
          calc eLpNorm ((fun _ : Ω => (1 : ℝ)) + fun om => ∑ i ∈ F, |constants i n om|)
                (ENNReal.ofReal p) P
              ≤ ENNReal.LpAddConst (ENNReal.ofReal p) *
                  (eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal p) P +
                    eLpNorm (fun om => ∑ i ∈ F, |constants i n om|) (ENNReal.ofReal p) P) :=
                eLpNorm_add_le' _
            _ ≤ ENNReal.LpAddConst (ENNReal.ofReal p) * (B1 + BS) :=
                mul_le_mul_of_nonneg_left (add_le_add hB1 (hS n).2) bot_le
  · -- pathwise boundedness on the common event
    intro om hom
    obtain ⟨hG', -, -, hsm⟩ := hGgoodA hom
    choose Mb hMb using fun i => hbdd i om hG'
    obtain ⟨BY, hBY⟩ := aux_cutoffs_bound_of_eventually (fun n => Yv n om) hsm
    refine ⟨1 + (∑ i ∈ F, Mb i) + BY, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 : ∑ i ∈ F, |constants i n om| ≤ ∑ i ∈ F, Mb i :=
      Finset.sum_le_sum (fun i _ => hMb i n)
    have h2 := hBY n
    show 1 + (∑ i ∈ F, |constants i n om|) + |Yv n om| ≤ _
    linarith
  · -- domination of the selected represented constants
    intro om _ n i hi
    have h1 : constants i n om ≤ |constants i n om| := le_abs_self _
    have h2 : |constants i n om| ≤ ∑ j ∈ F, |constants j n om| :=
      Finset.single_le_sum (f := fun j => |constants j n om|) (fun j _ => abs_nonneg _) hi
    have h3 := abs_nonneg (Yv n om)
    show constants i n om ≤ 1 + (∑ j ∈ F, |constants j n om|) + |Yv n om|
    linarith
  · -- the extrema event and domination of the damped extrema
    intro om hom n
    obtain ⟨-, hgd, hYeq, -⟩ := hGgoodA hom
    refine ⟨hgd n, ?_⟩
    have h1 : X (cutoff n) (env n om) = Yv n om := hYeq n
    have h2 := hsum_nonneg n om
    have h3 := le_abs_self (Yv n om)
    show X (cutoff n) (env n om) ≤ 1 + (∑ j ∈ F, |constants j n om|) + |Yv n om|
    linarith

end Paper




