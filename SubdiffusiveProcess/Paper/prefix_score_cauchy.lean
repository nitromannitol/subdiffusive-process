import SubdiffusiveProcess.Paper.branch_candidate_setup
import SubdiffusiveProcess.Paper.layer_regularity_moments
import SubdiffusiveProcess.Paper.in_responses
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import SubdiffusiveProcess.Probability.FiniteBankMoment
import SubdiffusiveProcess.Probability.GeometricSeriesLp
import SubdiffusiveProcess.Lane3.QueueHelpers
import SubdiffusiveProcess.Lane3.Elementary
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_prefix_score_cauchy_iSup_toReal_le_norm
    {I : Type} [Fintype I] (f : I → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (⨆ i : I, ENNReal.ofReal (f i)).toReal ≤ ‖f‖ := by
  rw [ENNReal.toReal_iSup (fun i => ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_ofReal (hf _)]
  classical
  rcases isEmpty_or_nonempty I with hI | hI
  · letI := hI
    simp
  · letI := hI
    refine ciSup_le fun i => ?_
    rw [Pi.norm_def]
    exact le_trans (le_abs_self _) (by
      exact_mod_cast Finset.le_sup (f := fun b : I => ‖f b‖₊) (Finset.mem_univ i))

theorem aux_prefix_score_cauchy_finite_sup_bound
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {I : Type} [Fintype I] (q K κ Cgeom : ℝ) (d j : ℕ)
    (hq : 1 ≤ q) (hK : 0 ≤ K) (hκ : 0 ≤ κ) (hCgeom : 1 ≤ Cgeom)
    (hcard : (Fintype.card I : ℝ) ≤
      Cgeom * (3 : ℝ) ^ ((d * j : ℕ) : ℝ))
    (X : I → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) (ENNReal.ofReal q) P)
    (hX0 : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω)
    (hXb : ∀ i, eLpNorm (X i) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal (K * Real.exp (κ * (j : ℝ)))) :
    eLpNorm (fun ω => (⨆ i : I, ENNReal.ofReal (X i ω)).toReal)
        (ENNReal.ofReal q) P ≤
      ENNReal.ofReal
        (Cgeom ^ (1 / q) * K * (3 : ℝ) ^ ((d * j : ℝ) / q) *
          Real.exp (κ * (j : ℝ))) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  have hqtop : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hqreal : (ENNReal.ofReal q).toReal = q :=
    ENNReal.toReal_ofReal hq0.le
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let F : Fin (Fintype.card I) → Ω → ℝ := fun i => X (e.symm i)
  have hFmem : ∀ i, MemLp (F i) (ENNReal.ofReal q) P := by
    intro i
    exact hX (e.symm i)
  have hFmeas : ∀ i, AEStronglyMeasurable (F i) P := fun i => (hFmem i).1
  have hFbound : ∀ i, eLpNorm (F i) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal (K * Real.exp (κ * (j : ℝ))) := by
    intro i
    exact hXb (e.symm i)
  have hbank := SubdiffusiveProcess.eLpNorm_finite_bank_le P hqE hqtop
    F hFmeas (ENNReal.ofReal (K * Real.exp (κ * (j : ℝ))) ) hFbound
  have hmono : ∀ᵐ ω ∂P,
      (⨆ i : I, ENNReal.ofReal (X i ω)).toReal ≤
        ‖fun i : Fin (Fintype.card I) => F i ω‖ := by
    filter_upwards [ae_all_iff.2 hX0] with ω hω
    have hv : ∀ i : I, 0 ≤ X i ω := fun i => hω i
    rw [ENNReal.toReal_iSup (fun i => ENNReal.ofReal_ne_top)]
    simp_rw [ENNReal.toReal_ofReal (hv _)]
    rcases isEmpty_or_nonempty I with hI | hI
    · letI := hI
      simp
    · letI := hI
      refine ciSup_le fun i => ?_
      calc
        X i ω ≤ |X i ω| := le_abs_self _
        _ = ‖F (e i) ω‖ := by simp [F, Real.norm_eq_abs]
        _ ≤ ‖fun k : Fin (Fintype.card I) => F k ω‖ := by
          rw [Pi.norm_def]
          have hle : ‖F (e i) ω‖₊ ≤
              Finset.univ.sup (fun b : Fin (Fintype.card I) => ‖F b ω‖₊) :=
            Finset.le_sup (f := fun b : Fin (Fintype.card I) => ‖F b ω‖₊)
              (Finset.mem_univ (e i))
          exact_mod_cast hle
  have hs0 : eLpNorm (fun ω => (⨆ i : I, ENNReal.ofReal (X i ω)).toReal)
      (ENNReal.ofReal q) P ≤
        eLpNorm (fun ω => ‖fun i : Fin (Fintype.card I) => F i ω‖)
          (ENNReal.ofReal q) P :=
    eLpNorm_mono_ae (hmono.mono fun ω hω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
        abs_of_nonneg (norm_nonneg _)] using hω)
  have hC0 : 0 ≤ Cgeom := by linarith
  have hcard0 : 0 ≤ Cgeom * (3 : ℝ) ^ ((d * j : ℕ) : ℝ) := by
    exact mul_nonneg hC0 (Real.rpow_nonneg (by norm_num) _)
  have hcardE : (Fintype.card I : ℝ≥0∞) ≤
      ENNReal.ofReal (Cgeom * (3 : ℝ) ^ ((d * j : ℕ) : ℝ)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcard
  have hrpow := ENNReal.rpow_le_rpow hcardE (by positivity : 0 ≤ (1 / q : ℝ))
  have hrpow' :
      (ENNReal.ofReal (Cgeom * (3 : ℝ) ^ ((d * j : ℕ) : ℝ))) ^ (1 / q : ℝ) =
        ENNReal.ofReal (Cgeom ^ (1 / q) *
          (3 : ℝ) ^ ((d * j : ℝ) / q)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hcard0 (by positivity)]
    rw [Real.mul_rpow hC0
      (Real.rpow_nonneg (by norm_num) _)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 2
    push_cast
    ring
  rw [hqreal] at hbank
  calc
    eLpNorm (fun ω => (⨆ i : I, ENNReal.ofReal (X i ω)).toReal)
        (ENNReal.ofReal q) P ≤
        (Fintype.card I : ℝ≥0∞) ^ (1 / q : ℝ) *
          ENNReal.ofReal (K * Real.exp (κ * (j : ℝ))) := hs0.trans hbank
    _ ≤ ENNReal.ofReal (Cgeom ^ (1 / q) *
          (3 : ℝ) ^ ((d * j : ℝ) / q)) *
          ENNReal.ofReal (K * Real.exp (κ * (j : ℝ))) := by
      exact mul_le_mul_of_nonneg_right (hrpow.trans_eq hrpow')
        (by positivity)
    _ = ENNReal.ofReal
        (Cgeom ^ (1 / q) * K * (3 : ℝ) ^ ((d * j : ℝ) / q) *
          Real.exp (κ * (j : ℝ))) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring_nf

theorem aux_prefix_score_cauchy_iSup_sub_le_sum_abs
    {I : Type} [Fintype I] (f g : I → ℝ) :
    |(⨆ i : I, f i) - (⨆ i : I, g i)| ≤ ∑ i : I, |f i - g i| := by
  classical
  rcases isEmpty_or_nonempty I with hI | hI
  · letI := hI
    simp
  · letI := hI
    have hbf : BddAbove (Set.range f) := by
      refine ⟨∑ i : I, |f i|, ?_⟩
      rintro _ ⟨i, rfl⟩
      exact (le_abs_self _).trans (Finset.single_le_sum
        (fun j _ => abs_nonneg (f j)) (Finset.mem_univ i))
    have hbg : BddAbove (Set.range g) := by
      refine ⟨∑ i : I, |g i|, ?_⟩
      rintro _ ⟨i, rfl⟩
      exact (le_abs_self _).trans (Finset.single_le_sum
        (fun j _ => abs_nonneg (g j)) (Finset.mem_univ i))
    have hS0 : 0 ≤ ∑ i : I, |f i - g i| :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)
    apply abs_sub_le_iff.mpr
    constructor
    · apply sub_le_iff_le_add.mpr
      refine ciSup_le fun i => ?_
      calc
        f i ≤ g i + |f i - g i| := by
          have := le_abs_self (f i - g i)
          linarith
        _ ≤ (⨆ i : I, g i) + ∑ i : I, |f i - g i| := by
          exact (add_le_add (le_ciSup hbg i) le_rfl).trans
            (add_le_add le_rfl (Finset.single_le_sum
              (fun j _ => abs_nonneg (f j - g j)) (Finset.mem_univ i)))
        _ ≤ (∑ i : I, |f i - g i|) + (⨆ i : I, g i) :=
          le_of_eq (add_comm _ _)
    · apply sub_le_iff_le_add.mpr
      refine ciSup_le fun i => ?_
      calc
        g i ≤ f i + |f i - g i| := by
          have h := le_abs_self (g i - f i)
          rw [show g i - f i = -(f i - g i) by ring, abs_neg] at h
          have := h
          linarith
        _ ≤ (⨆ i : I, f i) + ∑ i : I, |f i - g i| := by
          exact (add_le_add (le_ciSup hbf i) le_rfl).trans
            (add_le_add le_rfl (Finset.single_le_sum
              (fun j _ => abs_nonneg (f j - g j)) (Finset.mem_univ i)))
        _ ≤ (∑ i : I, |f i - g i|) + (⨆ i : I, f i) :=
          le_of_eq (add_comm _ _)

theorem aux_prefix_score_cauchy_finite_sup_diff_tendsto
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {I : Type} [Fintype I] (p q : ℝ)
    (hp : 1 ≤ p) (hpq : p ≤ q)
    (X : ℕ → I → Ω → ℝ) (Xlim : I → Ω → ℝ)
    (hX : ∀ N i, MemLp (X N i) (ENNReal.ofReal q) P)
    (hL : ∀ i, MemLp (Xlim i) (ENNReal.ofReal q) P)
    (hX0 : ∀ N i, ∀ᵐ ω ∂P, 0 ≤ X N i ω)
    (hL0 : ∀ i, ∀ᵐ ω ∂P, 0 ≤ Xlim i ω)
    (hconv : ∀ i, Tendsto
      (fun N => eLpNorm (fun ω => X N i ω - Xlim i ω)
        (ENNReal.ofReal q) P) atTop (𝓝 0)) :
    Tendsto
      (fun N => eLpNorm
        (fun ω =>
          (⨆ i : I, ENNReal.ofReal (X N i ω)).toReal -
            (⨆ i : I, ENNReal.ofReal (Xlim i ω)).toReal)
        (ENNReal.ofReal p) P) atTop (𝓝 0) := by
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hpqE : ENNReal.ofReal p ≤ ENNReal.ofReal q :=
    ENNReal.ofReal_le_ofReal hpq
  have hcoord : ∀ i, Tendsto
      (fun N => eLpNorm (fun ω => |X N i ω - Xlim i ω|)
        (ENNReal.ofReal p) P) atTop (𝓝 0) := by
    intro i
    have hmem : ∀ N, MemLp (fun ω => X N i ω - Xlim i ω)
        (ENNReal.ofReal p) P := by
      intro N
      have hN : MemLp (X N i) (ENNReal.ofReal p) P :=
        (hX N i).mono_exponent hpqE
      have hLi : MemLp (Xlim i) (ENNReal.ofReal p) P :=
        (hL i).mono_exponent hpqE
      exact hN.sub hLi
    have hle : ∀ N, eLpNorm (fun ω => |X N i ω - Xlim i ω|)
        (ENNReal.ofReal p) P ≤
        eLpNorm (fun ω => X N i ω - Xlim i ω)
          (ENNReal.ofReal q) P := by
      intro N
      calc
        eLpNorm (fun ω => |X N i ω - Xlim i ω|) (ENNReal.ofReal p) P =
            eLpNorm (fun ω => X N i ω - Xlim i ω)
              (ENNReal.ofReal p) P :=
          eLpNorm_norm (fun ω => X N i ω - Xlim i ω)
        _ ≤ eLpNorm (fun ω => X N i ω - Xlim i ω)
              (ENNReal.ofReal q) P :=
          eLpNorm_le_eLpNorm_of_exponent_le hpqE ((hmem N).1)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
      (hconv i)
      (Eventually.of_forall (fun _ => zero_le _)) (Eventually.of_forall hle)
  let R : ℕ → Ω → ℝ := fun N =>
    ∑ i : I, (fun ω => |X N i ω - Xlim i ω|)
  have hRbound : ∀ N, eLpNorm (R N) (ENNReal.ofReal p) P ≤
      ∑ i : I, eLpNorm (fun ω => |X N i ω - Xlim i ω|)
        (ENNReal.ofReal p) P := by
    intro N
    dsimp [R]
    apply eLpNorm_sum_le
    · intro i hi
      have hN : MemLp (X N i) (ENNReal.ofReal p) P :=
        (hX N i).mono_exponent hpqE
      have hLi : MemLp (Xlim i) (ENNReal.ofReal p) P :=
        (hL i).mono_exponent hpqE
      have hm : MemLp (fun ω => X N i ω - Xlim i ω)
          (ENNReal.ofReal p) P := hN.sub hLi
      exact (hm.norm).1
    · exact hpE
  have hRlim : Tendsto (fun N => eLpNorm (R N) (ENNReal.ofReal p) P)
      atTop (𝓝 0) := by
    have hs : Tendsto (fun N => ∑ i : I,
        eLpNorm (fun ω => |X N i ω - Xlim i ω|)
          (ENNReal.ofReal p) P) atTop (𝓝 0) := by
      simpa using (tendsto_finset_sum (s := (Finset.univ : Finset I))
        (f := fun i N => eLpNorm (fun ω => |X N i ω - Xlim i ω|)
          (ENNReal.ofReal p) P)
        (a := fun _ : I => (0 : ℝ≥0∞)) (x := atTop) (fun i hi => by
          simpa using hcoord i))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) hs
      (Eventually.of_forall (fun _ => zero_le _)) (Eventually.of_forall hRbound)
  have hVbound : ∀ N, ∀ᵐ ω ∂P,
      |(⨆ i : I, ENNReal.ofReal (X N i ω)).toReal -
          (⨆ i : I, ENNReal.ofReal (Xlim i ω)).toReal| ≤ R N ω := by
    intro N
    filter_upwards [ae_all_iff.2 (hX0 N), ae_all_iff.2 hL0] with ω hω hωL
    have hXN : ∀ i : I, 0 ≤ X N i ω := fun i => hω i
    have hXL : ∀ i : I, 0 ≤ Xlim i ω := fun i => hωL i
    have hV1 : (⨆ i : I, ENNReal.ofReal (X N i ω)).toReal =
        ⨆ i : I, X N i ω := by
      rw [ENNReal.toReal_iSup (fun i => ENNReal.ofReal_ne_top)]
      simp_rw [ENNReal.toReal_ofReal (hXN _)]
    have hV2 : (⨆ i : I, ENNReal.ofReal (Xlim i ω)).toReal =
        ⨆ i : I, Xlim i ω := by
      rw [ENNReal.toReal_iSup (fun i => ENNReal.ofReal_ne_top)]
      simp_rw [ENNReal.toReal_ofReal (hXL _)]
    rw [hV1, hV2]
    simpa [R] using aux_prefix_score_cauchy_iSup_sub_le_sum_abs
      (fun i => X N i ω) (fun i => Xlim i ω)
  have hupper : ∀ N, eLpNorm (fun ω =>
      (⨆ i : I, ENNReal.ofReal (X N i ω)).toReal -
        (⨆ i : I, ENNReal.ofReal (Xlim i ω)).toReal)
      (ENNReal.ofReal p) P ≤ eLpNorm (R N) (ENNReal.ofReal p) P := by
    intro N
    apply eLpNorm_mono_ae
    filter_upwards [hVbound N] with ω hω
    have hR0 : 0 ≤ R N ω := by
      dsimp [R]
      simpa only [Finset.sum_apply] using
        (Finset.sum_nonneg (s := (Finset.univ : Finset I))
          (fun i hi => abs_nonneg (X N i ω - Xlim i ω)))
    simpa only [Real.norm_eq_abs, abs_of_nonneg hR0] using hω
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) hRlim
    (Eventually.of_forall (fun _ => zero_le _)) (Eventually.of_forall hupper)

theorem aux_prefix_score_cauchy_tsum_tendsto
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (F : ℕ → ℕ → Ω → ℝ)
    (B r : ℝ) (hB : 0 ≤ B) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hmem : ∀ N j, MemLp (F N j) p P)
    (hbound : ∀ N j, eLpNorm (F N j) p P ≤ ENNReal.ofReal (B * r ^ j))
    (hcoord : ∀ j, Tendsto
      (fun N => eLpNorm (F N j) p P) atTop (𝓝 0)) :
    Tendsto (fun N => eLpNorm (fun ω => ∑' j, F N j ω) p P)
      atTop (𝓝 0) := by
  have hgeom : ∀ N, (∀ᵐ ω ∂P, Summable (fun j => ‖F N j ω‖)) ∧
      ∀ H, MemLp (fun ω => ∑' j, F N (j + H) ω) p P ∧
        eLpNorm (fun ω => ∑' j, F N (j + H) ω) p P ≤
          ENNReal.ofReal (B * r ^ H / (1 - r)) := by
    intro N
    exact SubdiffusiveProcess.memLp_geometric_tsum_tails P hp hpt
      (fun j => F N j) (fun j => hmem N j) hB hr0 hr1
      (fun j => hbound N j)
  have hpartial : ∀ H, Tendsto
      (fun N => eLpNorm (fun ω => ∑ j ∈ Finset.range H, F N j ω) p P)
      atTop (𝓝 0) := by
    intro H
    have hs : Tendsto (fun N => ∑ j ∈ Finset.range H,
        eLpNorm (F N j) p P) atTop (𝓝 0) := by
      simpa using (tendsto_finset_sum (s := Finset.range H)
        (f := fun j N => eLpNorm (F N j) p P)
        (a := fun _ : ℕ => (0 : ℝ≥0∞)) (x := atTop)
        (fun j hj => by simpa using hcoord j))
    have hle : ∀ N, eLpNorm (fun ω => ∑ j ∈ Finset.range H, F N j ω) p P ≤
        ∑ j ∈ Finset.range H, eLpNorm (F N j) p P := by
      intro N
      have hfun : (∑ j ∈ Finset.range H, fun ω => F N j ω) =
          (fun ω => ∑ j ∈ Finset.range H, F N j ω) := by
        funext ω
        simp
      rw [← hfun]
      exact eLpNorm_sum_le (p := p) (μ := P)
        (s := Finset.range H)
        (f := fun j ω => F N j ω)
        (fun j hj => (hmem N j).1) hp
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) hs
      (Eventually.of_forall (fun _ => zero_le _)) (Eventually.of_forall hle)
  have htail : Tendsto (fun H : ℕ =>
      ENNReal.ofReal (B * r ^ H / (1 - r))) atTop (𝓝 0) := by
    have hpw : Tendsto (fun H : ℕ => (r : ℝ) ^ H) atTop (𝓝 0) := by
      exact tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hreal : Tendsto (fun H : ℕ => B * r ^ H / (1 - r))
        atTop (𝓝 0) := by
      convert ((hpw.const_mul B).div_const (1 - r)) using 1 <;> simp
    simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hfull : ∀ N H, eLpNorm (fun ω => ∑' j, F N j ω) p P ≤
      eLpNorm (fun ω => ∑ j ∈ Finset.range H, F N j ω) p P +
        ENNReal.ofReal (B * r ^ H / (1 - r)) := by
    intro N H
    obtain ⟨hsum, htailmem⟩ := hgeom N
    have hsumtail : MemLp (fun ω => ∑' j, F N (j + H) ω) p P :=
      (htailmem H).1
    have heq : (fun ω => ∑' j, F N j ω) =ᵐ[ P ]
        (fun ω => (∑ j ∈ Finset.range H, F N j ω) +
          ∑' j, F N (j + H) ω) := by
      filter_upwards [hsum] with ω hω
      have hω' : Summable (fun j => F N j ω) := hω.of_norm
      simpa only [Finset.sum_apply] using (hω'.sum_add_tsum_nat_add H).symm
    have hfun : (∑ j ∈ Finset.range H, fun ω => F N j ω) =
        (fun ω => ∑ j ∈ Finset.range H, F N j ω) := by
      funext ω
      simp
    have hadd : (∑ j ∈ Finset.range H, fun ω => F N j ω) +
          (fun ω => ∑' j, F N (j + H) ω) =
        (fun ω => (∑ j ∈ Finset.range H, F N j ω) +
          ∑' j, F N (j + H) ω) := by
      funext ω
      simp
    rw [eLpNorm_congr_ae heq]
    rw [← hfun]
    rw [← hadd]
    exact ((eLpNorm_add_le
      (memLp_finset_sum' (Finset.range H) fun j hj => hmem N j).1
      hsumtail.1 hp).trans (add_le_add le_rfl (htailmem H).2))
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
  have ht := (ENNReal.tendsto_nhds_zero.mp htail) (ε / 2) hε2
  obtain ⟨H, hH⟩ := eventually_atTop.1 ht
  have hp' := (ENNReal.tendsto_nhds_zero.mp (hpartial H)) (ε / 2) hε2
  obtain ⟨N, hN⟩ := eventually_atTop.1 hp'
  refine eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  calc
    eLpNorm (fun ω => ∑' j, F n j ω) p P ≤
        eLpNorm (fun ω => ∑ j ∈ Finset.range H, F n j ω) p P +
          ENNReal.ofReal (B * r ^ H / (1 - r)) := hfull n H
    _ ≤ ε / 2 + ε / 2 := add_le_add (hN n hn) (hH H le_rfl)
    _ = ε := ENNReal.add_halves ε

theorem aux_prefix_score_cauchy_cutoff_sup_tendsto
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ≥0∞) (U : ℕ → ℕ → Ω → ℝ) (UL : ℕ → Ω → ℝ)
    (b : ℕ → ℝ≥0∞)
    (hfin : ∀ H, Tendsto
      (fun N => eLpNorm (fun ω =>
        (∑ j ∈ Finset.range H, U N j ω) -
          ∑ j ∈ Finset.range H, UL j ω) p P) atTop (𝓝 0))
    (hbound : ∀ N H, eLpNorm (fun ω => ∑' j, U N (j + H) ω) p P ≤ b H)
    (hboundL : ∀ H, eLpNorm (fun ω => ∑' j, UL (j + H) ω) p P ≤ b H)
    (hb : Tendsto b atTop (𝓝 0))
    (hdom : ∀ N H, eLpNorm (fun ω =>
      (⨆ j : ℕ, ENNReal.ofReal (U N j ω)).toReal -
        (⨆ j : ℕ, ENNReal.ofReal (UL j ω)).toReal) p P ≤
      eLpNorm (fun ω =>
        (∑ j ∈ Finset.range H, U N j ω) -
          ∑ j ∈ Finset.range H, UL j ω) p P + b H + b H) :
    Tendsto (fun N => eLpNorm (fun ω =>
      (⨆ j : ℕ, ENNReal.ofReal (U N j ω)).toReal -
        (⨆ j : ℕ, ENNReal.ofReal (UL j ω)).toReal) p P)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨H, hH⟩ := eventually_atTop.1
    ((ENNReal.tendsto_nhds_zero.mp hb) (ε / 3) hε3)
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((ENNReal.tendsto_nhds_zero.mp (hfin H)) (ε / 3) hε3)
  refine eventually_atTop.2 ⟨N, ?_⟩
  intro n hn
  calc
    eLpNorm (fun ω =>
        (⨆ j : ℕ, ENNReal.ofReal (U n j ω)).toReal -
          (⨆ j : ℕ, ENNReal.ofReal (UL j ω)).toReal) p P ≤
    eLpNorm (fun ω =>
          (∑ j ∈ Finset.range H, U n j ω) -
            ∑ j ∈ Finset.range H, UL j ω)
        p P + b H + b H := hdom n H
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
      exact add_le_add (add_le_add (hN n hn) (hH H le_rfl)) (hH H le_rfl)
    _ = ε := by simpa [add_assoc] using ENNReal.add_thirds ε


theorem aux_prefix_score_cauchy_sqrt_sub_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  rcases le_total x y with hxy | hyx
  · have hs : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hs)]
    apply Real.le_sqrt_of_sq_le
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    have hm : Real.sqrt x * Real.sqrt x ≤ Real.sqrt x * Real.sqrt y :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]
  · have hs : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hs)]
    apply Real.le_sqrt_of_sq_le
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    have hm : Real.sqrt y * Real.sqrt y ≤ Real.sqrt y * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

theorem aux_prefix_score_cauchy_pospart_lipschitz (x y : ℝ) :
    |max 0 x - max 0 y| ≤ |x - y| := by
  rcases le_total x y with hxy | hyx
  · by_cases hx : 0 ≤ x
    · rw [max_eq_right hx, max_eq_right (hx.trans hxy)]
    · have hx' : x ≤ 0 := le_of_not_ge hx
      by_cases hy : 0 ≤ y
      · rw [max_eq_left hx', max_eq_right hy]
        rw [abs_of_nonpos (sub_nonpos.mpr hy), abs_of_nonpos (sub_nonpos.mpr hxy)]
        linarith
      · have hy' : y ≤ 0 := le_of_not_ge hy
        simp [max_eq_left hx', max_eq_left hy']
  · by_cases hy : 0 ≤ y
    · rw [max_eq_right hy, max_eq_right (hy.trans hyx)]
    · have hy' : y ≤ 0 := le_of_not_ge hy
      by_cases hx : 0 ≤ x
      · rw [max_eq_left hy', max_eq_right hx]
        rw [abs_of_nonneg (sub_nonneg.mpr hx), abs_of_nonneg (sub_nonneg.mpr hyx)]
        linarith
      · have hx' : x ≤ 0 := le_of_not_ge hx
        simp [max_eq_left hx', max_eq_left hy']



theorem prefix_score_cauchy
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Pos : Type) (d : ℕ) (p q a kappa Cgeom : ℝ)
    (hp : 1 ≤ p) (hpq : p ≤ q) (ha : 0 < a) (hkappa : 0 ≤ kappa)
    (hCgeom : 1 ≤ Cgeom)
    (heta : 0 < a - (d : ℝ) / q - kappa / Real.log 3) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : ℝ), 0 ≤ K →
        ∀ (I : ℕ → Type) [∀ j, Fintype (I j)],
          (∀ j : ℕ, (Fintype.card (I j) : ℝ) ≤
            Cgeom * (3 : ℝ) ^ ((d * j : ℕ) : ℝ)) →
          ∀ (X : ℕ → Pos → (j : ℕ) → I j → Ω → ℝ)
            (Xlim : Pos → (j : ℕ) → I j → Ω → ℝ),
            (∀ N z j i, ∀ᵐ ω ∂P, 0 ≤ X N z j i ω) →
            (∀ z j i, ∀ᵐ ω ∂P, 0 ≤ Xlim z j i ω) →
            (∀ N z j i,
              MemLp (X N z j i) (ENNReal.ofReal q) P) →
            (∀ z j i, MemLp (Xlim z j i) (ENNReal.ofReal q) P) →
            (∀ N z j i,
              eLpNorm (X N z j i) (ENNReal.ofReal q) P ≤
                ENNReal.ofReal (K * Real.exp (kappa * (j : ℝ)))) →
            (∀ z j i,
              Tendsto
                (fun N => eLpNorm (fun ω => X N z j i ω - Xlim z j i ω)
                  (ENNReal.ofReal q) P)
                atTop (𝓝 0)) →
            let eta : ℝ := a - (d : ℝ) / q - kappa / Real.log 3
            let V : ℕ → Pos → ℕ → Ω → ℝ := fun N z j ω =>
              (⨆ i : I j, ENNReal.ofReal (X N z j i ω)).toReal
            let VL : Pos → ℕ → Ω → ℝ := fun z j ω =>
              (⨆ i : I j, ENNReal.ofReal (Xlim z j i ω)).toReal
            let w : ℕ → ℝ := fun j =>
              (3 : ℝ) ^ (-(a * (j : ℝ)))
            let SN : ℕ → Pos → Ω → ℝ := fun N z ω =>
              ∑' j : ℕ, w j * V N z j ω
            let SL : Pos → Ω → ℝ := fun z ω =>
              ∑' j : ℕ, w j * VL z j ω
            let EN : ℕ → Pos → Ω → ℝ≥0∞ := fun N z ω =>
              ⨆ j : ℕ, ENNReal.ofReal (w j * V N z j ω)
            let EL : Pos → Ω → ℝ≥0∞ := fun z ω =>
              ⨆ j : ℕ, ENNReal.ofReal (w j * VL z j ω)
            let TN : ℕ → Pos → Ω → ℝ := fun N z ω => (EN N z ω).toReal
            let TL : Pos → Ω → ℝ := fun z ω => (EL z ω).toReal
            let PartialSum : ℕ → Pos → ℕ → Ω → ℝ := fun N z H ω =>
              ∑ j ∈ Finset.range H, w j * V N z j ω
            (∀ z,
              ∀ᵐ ω ∂P,
                (∀ N, Summable (fun j : ℕ => w j * V N z j ω)) ∧
                Summable (fun j : ℕ => w j * VL z j ω) ∧
                (∀ N, EN N z ω ≠ ⊤) ∧ EL z ω ≠ ⊤) ∧
            (∀ N z,
              MemLp (SN N z) (ENNReal.ofReal p) P ∧
              MemLp (TN N z) (ENNReal.ofReal p) P) ∧
            (∀ z,
              MemLp (SL z) (ENNReal.ofReal p) P ∧
              MemLp (TL z) (ENNReal.ofReal p) P) ∧
            (∀ N z H,
              eLpNorm (fun ω => SN N z ω - PartialSum N z H ω)
                  (ENNReal.ofReal p) P ≤
                ENNReal.ofReal (C * K * (3 : ℝ) ^ (-(eta * (H : ℝ))))) ∧
            (∀ N z H,
              eLpNorm
                  (fun ω =>
                    (⨆ j : {j : ℕ // H ≤ j},
                      ENNReal.ofReal (w j.1 * V N z j.1 ω)).toReal)
                  (ENNReal.ofReal p) P ≤
                ENNReal.ofReal (C * K * (3 : ℝ) ^ (-(eta * (H : ℝ))))) ∧
            (∀ z,
              Tendsto
                (fun N => eLpNorm (fun ω => SN N z ω - SL z ω)
                  (ENNReal.ofReal p) P)
                atTop (𝓝 0) ∧
              Tendsto
                (fun N => eLpNorm (fun ω => TN N z ω - TL z ω)
                  (ENNReal.ofReal p) P)
                atTop (𝓝 0)) ∧
            (∀ z,
              Tendsto
                (fun N => eLpNorm
                  (fun ω => Real.sqrt (max 0 (SN N z ω)) -
                    Real.sqrt (max 0 (SL z ω)))
                  (ENNReal.ofReal p) P)
                atTop (𝓝 0) ∧
              Tendsto
                (fun N => eLpNorm
                  (fun ω => Real.sqrt (max 0 (TN N z ω)) -
                    Real.sqrt (max 0 (TL z ω)))
                  (ENNReal.ofReal p) P)
                atTop (𝓝 0)) ∧
            (∀ z l u, l < u →
              Tendsto
                (fun N => eLpNorm
                  (fun ω =>
                    min 1 (max 0 ((SN N z ω - l) / (u - l))) -
                    min 1 (max 0 ((SL z ω - l) / (u - l))))
                  (ENNReal.ofReal p) P)
                atTop (𝓝 0) ∧
              Tendsto
                (fun N => eLpNorm
                  (fun ω =>
                    min 1 (max 0 ((TN N z ω - l) / (u - l))) -
                    min 1 (max 0 ((TL z ω - l) / (u - l))))
                  (ENNReal.ofReal p) P)
                atTop (𝓝 0)) := by

  have hq0 : 0 < q := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hp) hpq
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let eta : ℝ := a - (d : ℝ) / q - kappa / Real.log 3
  let r : ℝ := (3 : ℝ) ^ (-eta)
  let A : ℝ := Cgeom ^ (1 / q)
  have heta0 : 0 < eta := by simpa [eta] using heta
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg (by linarith [hCgeom]) _
  have hC0 : 0 < A / (1 - r) + 1 := by
    have : 0 < 1 - r := sub_pos.mpr hr1
    positivity
  have hweight (j : ℕ) :
      (3 : ℝ) ^ (-(a * (j : ℝ))) *
          (A * (3 : ℝ) ^ ((d * j : ℝ) / q) *
            Real.exp (kappa * (j : ℝ))) = A * r ^ j := by
    have hpow (x : ℝ) : (3 : ℝ) ^ x =
        Real.exp (Real.log 3 * x) :=
      Real.rpow_def_of_pos (by norm_num) x
    have hj : (3 : ℝ) ^ (-eta * (j : ℝ)) = r ^ j := by
      calc
        (3 : ℝ) ^ (-eta * (j : ℝ)) =
            ((3 : ℝ) ^ (-eta)) ^ (j : ℝ) :=
          Real.rpow_mul (x := (3 : ℝ)) (by norm_num : (0 : ℝ) ≤ 3)
            (-eta) (j : ℝ)
        _ = ((3 : ℝ) ^ (-eta)) ^ j := Real.rpow_natCast _ _
        _ = r ^ j := by rfl
    rw [hpow, hpow, ← hj]
    rw [hpow]
    calc
      Real.exp (Real.log 3 * -(a * (j : ℝ))) *
          (A * Real.exp (Real.log 3 * ((d * j : ℝ) / q)) *
            Real.exp (kappa * (j : ℝ))) =
          A * (Real.exp (Real.log 3 * -(a * (j : ℝ))) *
            Real.exp (Real.log 3 * ((d * j : ℝ) / q)) *
              Real.exp (kappa * (j : ℝ))) := by ring
      _ = A * (Real.exp (Real.log 3 * -(a * (j : ℝ)) +
            Real.log 3 * ((d * j : ℝ) / q)) *
              Real.exp (kappa * (j : ℝ))) := by
            rw [← Real.exp_add]
      _ = A * Real.exp (Real.log 3 * -(a * (j : ℝ)) +
            Real.log 3 * ((d * j : ℝ) / q) + kappa * (j : ℝ)) := by
            rw [← Real.exp_add]
      _ = A * Real.exp (Real.log 3 * (-eta * (j : ℝ))) := by
            congr 2
            dsimp [eta]
            field_simp [ne_of_gt hlog]
            ring
  refine ⟨A / (1 - r) + 1, hC0, ?_⟩
  intro K hK I hI hcard X Xlim hX0 hL0 hXmem hLmem hXbound hconv
  dsimp
  have hq1 : 1 ≤ q := hp.trans hpq
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hpqE : ENNReal.ofReal p ≤ ENNReal.ofReal q :=
    ENNReal.ofReal_le_ofReal hpq
  have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq1
  have hpEtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hqEtop : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  have hqE0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq0).ne'
  have hXlimbound : ∀ z j i,
      eLpNorm (Xlim z j i) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (K * Real.exp (kappa * (j : ℝ))) := by
    intro z j i
    obtain ⟨ns, hns, hae⟩ :=
      SubdiffusiveProcess.Lane3.exists_ae_subseq_of_eLpNorm_tendsto
        Ω P (fun N => X N z j i) (Xlim z j i) (ENNReal.ofReal q) hqE0
        (fun N => (hXmem N z j i).1) (hLmem z j i).1 (hconv z j i)
    exact Lp.eLpNorm_le_of_ae_tendsto
      (Eventually.of_forall (fun n => hXbound (ns n) z j i))
      (fun n => (hXmem (ns n) z j i).1) hae
  let V : ℕ → Pos → ℕ → Ω → ℝ := fun N z j ω =>
    (⨆ i : I j, ENNReal.ofReal (X N z j i ω)).toReal
  let VL : Pos → ℕ → Ω → ℝ := fun z j ω =>
    (⨆ i : I j, ENNReal.ofReal (Xlim z j i ω)).toReal
  let w : ℕ → ℝ := fun j => (3 : ℝ) ^ (-(a * (j : ℝ)))
  let F : ℕ → Pos → ℕ → Ω → ℝ := fun N z j ω => w j * V N z j ω
  let FL : Pos → ℕ → Ω → ℝ := fun z j ω => w j * VL z j ω
  have hVmem : ∀ N z j, MemLp (V N z j) (ENNReal.ofReal p) P := by
    intro N z j
    have hAE : AEMeasurable (fun ω =>
        ⨆ i : I j, ENNReal.ofReal (X N z j i ω)) P :=
      AEMeasurable.iSup (fun i =>
        ENNReal.measurable_ofReal.comp_aemeasurable
          ((hXmem N z j i).1.aemeasurable))
    have hmeas : AEStronglyMeasurable (V N z j) P := by
      exact hAE.ennreal_toReal.aestronglyMeasurable
    have hqbound : eLpNorm (V N z j) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (Cgeom ^ (1 / q) * K *
          (3 : ℝ) ^ ((d * j : ℝ) / q) * Real.exp (kappa * (j : ℝ))) := by
      dsimp [V]
      exact aux_prefix_score_cauchy_finite_sup_bound P q K kappa Cgeom d j
        hq1 hK hkappa hCgeom (hcard j)
        (fun i => X N z j i) (fun i => hXmem N z j i)
        (fun i => hX0 N z j i) (fun i => hXbound N z j i)
    refine ⟨hmeas, ?_⟩
    exact (eLpNorm_le_eLpNorm_of_exponent_le hpqE hmeas).trans_lt
      (hqbound.trans_lt (by simp))
  have hVLmem : ∀ z j, MemLp (VL z j) (ENNReal.ofReal p) P := by
    intro z j
    have hAE : AEMeasurable (fun ω =>
        ⨆ i : I j, ENNReal.ofReal (Xlim z j i ω)) P :=
      AEMeasurable.iSup (fun i =>
        ENNReal.measurable_ofReal.comp_aemeasurable
          ((hLmem z j i).1.aemeasurable))
    have hmeas : AEStronglyMeasurable (VL z j) P := by
      exact hAE.ennreal_toReal.aestronglyMeasurable
    have hqbound : eLpNorm (VL z j) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (Cgeom ^ (1 / q) * K *
          (3 : ℝ) ^ ((d * j : ℝ) / q) * Real.exp (kappa * (j : ℝ))) := by
      dsimp [VL]
      exact aux_prefix_score_cauchy_finite_sup_bound P q K kappa Cgeom d j
        hq1 hK hkappa hCgeom (hcard j)
        (fun i => Xlim z j i) (fun i => hLmem z j i)
        (fun i => hL0 z j i) (fun i => hXlimbound z j i)
    refine ⟨hmeas, ?_⟩
    exact (eLpNorm_le_eLpNorm_of_exponent_le hpqE hmeas).trans_lt
      (hqbound.trans_lt (by simp))
  have hFmem : ∀ N z j, MemLp (F N z j) (ENNReal.ofReal p) P := by
    intro N z j
    have hw : 0 ≤ w j := by
      dsimp [w]
      exact Real.rpow_nonneg (by norm_num) _
    simpa [F, smul_eq_mul] using (hVmem N z j).const_mul (w j)
  have hFLmem : ∀ z j, MemLp (FL z j) (ENNReal.ofReal p) P := by
    intro z j
    have hw : 0 ≤ w j := by
      dsimp [w]
      exact Real.rpow_nonneg (by norm_num) _
    simpa [FL, smul_eq_mul] using (hVLmem z j).const_mul (w j)
  have hFbound : ∀ N z j, eLpNorm (F N z j) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (A * K * r ^ j) := by
    intro N z j
    have hw : 0 ≤ w j := by
      dsimp [w]
      exact Real.rpow_nonneg (by norm_num) _
    have hB : 0 ≤ A * (3 : ℝ) ^ ((d * j : ℝ) / q) *
        Real.exp (kappa * (j : ℝ)) * K := by positivity
    have hvq := aux_prefix_score_cauchy_finite_sup_bound P q K kappa Cgeom d j
      hq1 hK hkappa hCgeom (hcard j)
      (fun i => X N z j i) (fun i => hXmem N z j i)
      (fun i => hX0 N z j i) (fun i => hXbound N z j i)
    have hscaled : eLpNorm (F N z j) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (w j) * ENNReal.ofReal
          (A * K * (3 : ℝ) ^ ((d * j : ℝ) / q) *
            Real.exp (kappa * (j : ℝ))) := by
      calc
        eLpNorm (F N z j) (ENNReal.ofReal p) P =
            eLpNorm (w j • V N z j) (ENNReal.ofReal p) P := by
              congr 1
        _ = ENNReal.ofReal (w j) * eLpNorm (V N z j)
              (ENNReal.ofReal p) P := by
              rw [eLpNorm_const_smul]
              simp [Real.enorm_eq_ofReal hw]
        _ ≤ ENNReal.ofReal (w j) * eLpNorm (V N z j)
              (ENNReal.ofReal q) P := by
              gcongr
              exact eLpNorm_le_eLpNorm_of_exponent_le hpqE (hVmem N z j).1
        _ ≤ ENNReal.ofReal (w j) * ENNReal.ofReal
            (A * K * (3 : ℝ) ^ ((d * j : ℝ) / q) *
              Real.exp (kappa * (j : ℝ))) := by
              gcongr
              
    calc
      eLpNorm (F N z j) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (w j) * ENNReal.ofReal
            (A * K * (3 : ℝ) ^ ((d * j : ℝ) / q) *
              Real.exp (kappa * (j : ℝ))) := hscaled
      _ = ENNReal.ofReal (w j *
            (A * K * (3 : ℝ) ^ ((d * j : ℝ) / q) *
              Real.exp (kappa * (j : ℝ)))) :=
            (ENNReal.ofReal_mul hw).symm
      _ = ENNReal.ofReal (A * K * r ^ j) := by
        congr 1
        dsimp [w]
        calc
          (3 : ℝ) ^ (-(a * (j : ℝ))) *
              (A * K * (3 : ℝ) ^ ((d * j : ℝ) / q) *
                Real.exp (kappa * (j : ℝ))) =
              K * ((3 : ℝ) ^ (-(a * (j : ℝ))) *
                (A * (3 : ℝ) ^ ((d * j : ℝ) / q) *
                  Real.exp (kappa * (j : ℝ)))) := by ring
          _ = K * (A * r ^ j) := by rw [hweight j]
          _ = A * K * r ^ j := by ring
  have hFLbound : ∀ z j, eLpNorm (FL z j) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (A * K * r ^ j) := by
    intro z j
    have hw : 0 ≤ w j := by
      dsimp [w]
      exact Real.rpow_nonneg (by norm_num) _
    have hvq := aux_prefix_score_cauchy_finite_sup_bound P q K kappa Cgeom d j
      hq1 hK hkappa hCgeom (hcard j)
      (fun i => Xlim z j i) (fun i => hLmem z j i)
      (fun i => hL0 z j i) (fun i => hXlimbound z j i)
    calc
      eLpNorm (FL z j) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (w j) * ENNReal.ofReal
            (A * K * (3 : ℝ) ^ ((d * j : ℝ) / q) *
              Real.exp (kappa * (j : ℝ))) := by
        calc
          eLpNorm (FL z j) (ENNReal.ofReal p) P =
              eLpNorm (w j • VL z j) (ENNReal.ofReal p) P := by
                congr 1
          _ = ENNReal.ofReal (w j) * eLpNorm (VL z j)
                (ENNReal.ofReal p) P := by
                rw [eLpNorm_const_smul]
                simp [Real.enorm_eq_ofReal hw]
          _ ≤ ENNReal.ofReal (w j) * eLpNorm (VL z j)
                (ENNReal.ofReal q) P := by
                gcongr
                exact eLpNorm_le_eLpNorm_of_exponent_le hpqE (hVLmem z j).1
          _ ≤ ENNReal.ofReal (w j) * ENNReal.ofReal
              (A * K * (3 : ℝ) ^ ((d * j : ℝ) / q) *
                Real.exp (kappa * (j : ℝ))) := by
                gcongr
                
      _ = ENNReal.ofReal (w j *
            (A * K * (3 : ℝ) ^ ((d * j : ℝ) / q) *
              Real.exp (kappa * (j : ℝ)))) :=
            (ENNReal.ofReal_mul hw).symm
      _ = ENNReal.ofReal (A * K * r ^ j) := by
        congr 1
        dsimp [w]
        calc
          (3 : ℝ) ^ (-(a * (j : ℝ))) *
              (A * K * (3 : ℝ) ^ ((d * j : ℝ) / q) *
                Real.exp (kappa * (j : ℝ))) =
              K * ((3 : ℝ) ^ (-(a * (j : ℝ))) *
                (A * (3 : ℝ) ^ ((d * j : ℝ) / q) *
                  Real.exp (kappa * (j : ℝ)))) := by ring
          _ = K * (A * r ^ j) := by rw [hweight j]
          _ = A * K * r ^ j := by ring
  have hF0 : ∀ N z j ω, 0 ≤ F N z j ω := by
    intro N z j ω
    have hw : 0 ≤ w j := by
      dsimp [w]
      exact Real.rpow_nonneg (by norm_num) _
    exact mul_nonneg hw (ENNReal.toReal_nonneg)
  have hFL0 : ∀ z j ω, 0 ≤ FL z j ω := by
    intro z j ω
    have hw : 0 ≤ w j := by
      dsimp [w]
      exact Real.rpow_nonneg (by norm_num) _
    exact mul_nonneg hw (ENNReal.toReal_nonneg)
  have hgeomN : ∀ N z,
      (∀ᵐ ω ∂P, Summable (fun j => F N z j ω)) ∧
        (∀ H, MemLp (fun ω => ∑' j, F N z (j + H) ω)
            (ENNReal.ofReal p) P ∧
          eLpNorm (fun ω => ∑' j, F N z (j + H) ω)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (A * K * r ^ H / (1 - r))) := by
    intro N z
    obtain ⟨hs, ht⟩ := SubdiffusiveProcess.memLp_geometric_tsum_tails P
      hpE hpEtop (fun j => F N z j) (fun j => hFmem N z j)
      (mul_nonneg hA0 hK) hr0 hr1 (fun j => hFbound N z j)
    refine ⟨?_, ?_⟩
    · filter_upwards [hs] with ω hω
      exact hω.of_norm
    · intro H
      simpa using ht H
  have hgeomL : ∀ z,
      (∀ᵐ ω ∂P, Summable (fun j => FL z j ω)) ∧
        (∀ H, MemLp (fun ω => ∑' j, FL z (j + H) ω)
            (ENNReal.ofReal p) P ∧
          eLpNorm (fun ω => ∑' j, FL z (j + H) ω)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (A * K * r ^ H / (1 - r))) := by
    intro z
    obtain ⟨hs, ht⟩ := SubdiffusiveProcess.memLp_geometric_tsum_tails P
      hpE hpEtop (fun j => FL z j) (fun j => hFLmem z j)
      (mul_nonneg hA0 hK) hr0 hr1 (fun j => hFLbound z j)
    refine ⟨?_, ?_⟩
    · filter_upwards [hs] with ω hω
      exact hω.of_norm
    · intro H
      simpa using ht H
  have hnormN : ∀ N z, ∀ᵐ ω ∂P, Summable (fun j => ‖F N z j ω‖) := by
    intro N z
    exact (SubdiffusiveProcess.memLp_geometric_tsum_tails P hpE hpEtop
      (fun j => F N z j) (fun j => hFmem N z j)
      (mul_nonneg hA0 hK) hr0 hr1 (fun j => hFbound N z j)).1
  have hnormL : ∀ z, ∀ᵐ ω ∂P, Summable (fun j => ‖FL z j ω‖) := by
    intro z
    exact (SubdiffusiveProcess.memLp_geometric_tsum_tails P hpE hpEtop
      (fun j => FL z j) (fun j => hFLmem z j)
      (mul_nonneg hA0 hK) hr0 hr1 (fun j => hFLbound z j)).1
  have hSNmem : ∀ N z, MemLp
      (fun ω => ∑' j, F N z j ω) (ENNReal.ofReal p) P := by
    intro N z
    simpa using (hgeomN N z).2 0 |>.1
  have hSLmem : ∀ z, MemLp
      (fun ω => ∑' j, FL z j ω) (ENNReal.ofReal p) P := by
    intro z
    simpa using (hgeomL z).2 0 |>.1
  have hENtop : ∀ N z, ∀ᵐ ω ∂P,
      (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)) ≠ ⊤ := by
    intro N z
    filter_upwards [hnormN N z] with ω hω
    have hle : (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)) ≤
        ENNReal.ofReal (∑' j, ‖F N z j ω‖) := by
      apply iSup_le
      intro j
      exact ENNReal.ofReal_le_ofReal
        ((le_abs_self (F N z j ω)).trans
          (hω.le_tsum j (fun _ _ => norm_nonneg _)))
    exact (lt_top_iff_ne_top.mp (hle.trans_lt ENNReal.ofReal_lt_top))
  have hELtop : ∀ z, ∀ᵐ ω ∂P,
      (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)) ≠ ⊤ := by
    intro z
    filter_upwards [hnormL z] with ω hω
    have hle : (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)) ≤
        ENNReal.ofReal (∑' j, ‖FL z j ω‖) := by
      apply iSup_le
      intro j
      exact ENNReal.ofReal_le_ofReal
        ((le_abs_self (FL z j ω)).trans
          (hω.le_tsum j (fun _ _ => norm_nonneg _)))
    exact (lt_top_iff_ne_top.mp (hle.trans_lt ENNReal.ofReal_lt_top))
  have hfirst : ∀ z, ∀ᵐ ω ∂P,
      (∀ N, Summable (fun j => F N z j ω)) ∧
      Summable (fun j => FL z j ω) ∧
      (∀ N, (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)) ≠ ⊤) ∧
      (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)) ≠ ⊤ := by
    intro z
    filter_upwards [ae_all_iff.2 (fun N => (hgeomN N z).1),
      (hgeomL z).1, ae_all_iff.2 (fun N => hENtop N z), hELtop z]
      with ω hN hL hEN hEL
    exact ⟨hN, hL, hEN, hEL⟩
  have hrpow (H : ℕ) : r ^ H = (3 : ℝ) ^ (-(eta * (H : ℝ))) := by
    calc
      r ^ H = ((3 : ℝ) ^ (-eta)) ^ H := by rfl
      _ = ((3 : ℝ) ^ (-eta)) ^ (H : ℝ) := by
        rw [Real.rpow_natCast]
      _ = (3 : ℝ) ^ (-eta * (H : ℝ)) := by
        rw [Real.rpow_mul (x := (3 : ℝ)) (by norm_num : (0 : ℝ) ≤ 3)]
      _ = (3 : ℝ) ^ (-(eta * (H : ℝ))) := by ring_nf
  have htailreal (H : ℕ) : A * K * r ^ H / (1 - r) ≤
      (A / (1 - r) + 1) * K * (3 : ℝ) ^ (-(eta * (H : ℝ))) := by
    rw [← hrpow H]
    have hden : 0 < 1 - r := sub_pos.mpr hr1
    calc
      A * K * r ^ H / (1 - r) = (A / (1 - r)) * K * r ^ H := by
        field_simp
      _ ≤ (A / (1 - r) + 1) * K * r ^ H := by
        gcongr
        exact le_add_of_nonneg_right (by norm_num)
  have hpartialbound : ∀ N z H,
      eLpNorm (fun ω =>
        (∑' j, F N z j ω) - ∑ j ∈ Finset.range H, F N z j ω)
          (ENNReal.ofReal p) P ≤
        ENNReal.ofReal ((A / (1 - r) + 1) * K *
          (3 : ℝ) ^ (-(eta * (H : ℝ)))) := by
    intro N z H
    have heq : (fun ω =>
        (∑' j, F N z j ω) - ∑ j ∈ Finset.range H, F N z j ω) =ᵐ[ P ]
        (fun ω => ∑' j, F N z (j + H) ω) := by
      filter_upwards [(hgeomN N z).1] with ω hω
      have hsum := hω.sum_add_tsum_nat_add H
      rw [← hsum]
      ring
    rw [eLpNorm_congr_ae heq]
    exact ((hgeomN N z).2 H).2.trans
      (ENNReal.ofReal_le_ofReal (htailreal H))
  have hsupbound : ∀ N z H,
      eLpNorm (fun ω =>
        (⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (F N z j.1 ω)).toReal)
          (ENNReal.ofReal p) P ≤
        ENNReal.ofReal ((A / (1 - r) + 1) * K *
          (3 : ℝ) ^ (-(eta * (H : ℝ)))) := by
    intro N z H
    have htailmem := (hgeomN N z).2 H
    have hmono : ∀ᵐ ω ∂P, ∀ j : {j : ℕ // H ≤ j},
        ENNReal.ofReal (F N z j.1 ω) ≤
          ENNReal.ofReal (∑' k, F N z (k + H) ω) := by
      filter_upwards [hnormN N z] with ω hω
      intro j
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le j.property
      have hshiftNorm : Summable (fun k : ℕ => ‖F N z (k + H) ω‖) := by
        simpa only [Function.comp_apply] using
          hω.comp_injective (fun x y h => Nat.add_right_cancel h)
      have hshift : Summable (fun k : ℕ => F N z (k + H) ω) :=
        hshiftNorm.of_norm
      apply ENNReal.ofReal_le_ofReal
      rw [hk, Nat.add_comm]
      exact hshift.le_tsum k (fun _ _ => hF0 N z _ ω)
    have hpoint : ∀ᵐ ω ∂P,
        (⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (F N z j.1 ω)).toReal ≤
          ∑' k, F N z (k + H) ω := by
      filter_upwards [hmono, hnormN N z] with ω hω hnorm
      have hsup : (⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (F N z j.1 ω)) ≤
          ENNReal.ofReal (∑' k, F N z (k + H) ω) := by
        exact iSup_le hω
      have hshiftNorm : Summable (fun k : ℕ => ‖F N z (k + H) ω‖) := by
        simpa only [Function.comp_apply] using
          hnorm.comp_injective (fun x y h => Nat.add_right_cancel h)
      have hshift : Summable (fun k : ℕ => F N z (k + H) ω) :=
        hshiftNorm.of_norm
      have hnonneg : 0 ≤ ∑' k, F N z (k + H) ω :=
        tsum_nonneg (fun k => hF0 N z (k + H) ω)
      calc
        (⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (F N z j.1 ω)).toReal ≤
            (ENNReal.ofReal (∑' k, F N z (k + H) ω)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hsup
        _ = ∑' k, F N z (k + H) ω := ENNReal.toReal_ofReal hnonneg
    have hle : eLpNorm (fun ω =>
        (⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (F N z j.1 ω)).toReal)
          (ENNReal.ofReal p) P ≤
        eLpNorm (fun ω => ∑' k, F N z (k + H) ω)
          (ENNReal.ofReal p) P := by
      apply eLpNorm_mono_ae
      filter_upwards [hpoint] with ω hω
      have hnonneg : 0 ≤ ∑' k, F N z (k + H) ω :=
        tsum_nonneg (fun k => hF0 N z (k + H) ω)
      simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
        abs_of_nonneg hnonneg] using hω
    exact hle.trans ((htailmem.2).trans (ENNReal.ofReal_le_ofReal (htailreal H)))
  have hVdiff : ∀ z j, Tendsto (fun N => eLpNorm (fun ω =>
      V N z j ω - VL z j ω) (ENNReal.ofReal p) P) atTop (𝓝 0) := by
    intro z j
    simpa [V, VL] using
      (aux_prefix_score_cauchy_finite_sup_diff_tendsto P p q hp hpq
        (fun N i ω => X N z j i ω) (fun i ω => Xlim z j i ω)
        (fun N i => hXmem N z j i) (fun i => hLmem z j i)
        (fun N i => hX0 N z j i) (fun i => hL0 z j i)
        (fun i => hconv z j i))
  have hcoordF : ∀ z j, Tendsto (fun N => eLpNorm (fun ω =>
      F N z j ω - FL z j ω) (ENNReal.ofReal p) P) atTop (𝓝 0) := by
    intro z j
    have hw : 0 ≤ w j := by
      dsimp [w]
      exact Real.rpow_nonneg (by norm_num) _
    have hmul : Tendsto (fun N => ENNReal.ofReal (w j) *
        eLpNorm (fun ω => V N z j ω - VL z j ω) (ENNReal.ofReal p) P)
        atTop (𝓝 0) := by
      simpa using ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).tendsto 0).comp
        (hVdiff z j)
    apply hmul.congr'
    filter_upwards [] with N
    have heq : eLpNorm (fun ω => F N z j ω - FL z j ω)
          (ENNReal.ofReal p) P =
        ENNReal.ofReal (w j) * eLpNorm (fun ω =>
          V N z j ω - VL z j ω) (ENNReal.ofReal p) P := by
      calc
        eLpNorm (fun ω => F N z j ω - FL z j ω)
            (ENNReal.ofReal p) P =
            eLpNorm (w j • (fun ω => V N z j ω - VL z j ω))
              (ENNReal.ofReal p) P := by
          congr 1
          funext ω
          simp [F, FL, smul_eq_mul]
          ring
        _ = ENNReal.ofReal (w j) * eLpNorm (fun ω =>
            V N z j ω - VL z j ω) (ENNReal.ofReal p) P := by
          rw [eLpNorm_const_smul]
          simp [Real.enorm_eq_ofReal hw]
    exact heq.symm
  have hDmem : ∀ N z j, MemLp (fun ω =>
      F N z j ω - FL z j ω) (ENNReal.ofReal p) P := by
    intro N z j
    exact (hFmem N z j).sub (hFLmem z j)
  have hDbound : ∀ N z j, eLpNorm (fun ω =>
      F N z j ω - FL z j ω) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (2 * A * K * r ^ j) := by
    intro N z j
    calc
      eLpNorm (fun ω => F N z j ω - FL z j ω)
          (ENNReal.ofReal p) P ≤
          eLpNorm (F N z j) (ENNReal.ofReal p) P +
            eLpNorm (FL z j) (ENNReal.ofReal p) P :=
        eLpNorm_sub_le (hFmem N z j).1 (hFLmem z j).1 hpE
      _ ≤ ENNReal.ofReal (A * K * r ^ j) +
          ENNReal.ofReal (A * K * r ^ j) :=
        add_le_add (hFbound N z j) (hFLbound z j)
      _ = ENNReal.ofReal (2 * A * K * r ^ j) := by
        rw [← ENNReal.ofReal_add]
        · congr 1
          ring
        · positivity
        · positivity
  have hSNconv : ∀ z, Tendsto (fun N => eLpNorm (fun ω =>
      (∑' j, F N z j ω) - ∑' j, FL z j ω)
        (ENNReal.ofReal p) P) atTop (𝓝 0) := by
    intro z
    have hDsum := aux_prefix_score_cauchy_tsum_tendsto P
      (ENNReal.ofReal p) hpE hpEtop
      (fun N j ω => F N z j ω - FL z j ω) (2 * A * K) r
      (by positivity) hr0 hr1 (fun N j => hDmem N z j)
      (fun N j => hDbound N z j) (fun j => hcoordF z j)
    apply hDsum.congr'
    filter_upwards [] with N
    have heq : (fun ω => ∑' j, (F N z j ω - FL z j ω)) =ᵐ[ P ]
        (fun ω => (∑' j, F N z j ω) - ∑' j, FL z j ω) := by
      filter_upwards [(hgeomN N z).1, (hgeomL z).1] with ω hF hL
      exact hF.tsum_sub hL
    exact eLpNorm_congr_ae heq
  have hfiniteSum : ∀ z H, Tendsto (fun N => eLpNorm (fun ω =>
      (∑ j ∈ Finset.range H, F N z j ω) -
        ∑ j ∈ Finset.range H, FL z j ω) (ENNReal.ofReal p) P)
      atTop (𝓝 0) := by
    intro z H
    let R : ℕ → Ω → ℝ := fun N =>
      ∑ j ∈ Finset.range H, (F N z j - FL z j)
    have hRle : ∀ N, eLpNorm (R N) (ENNReal.ofReal p) P ≤
        ∑ j ∈ Finset.range H, eLpNorm (fun ω =>
          F N z j ω - FL z j ω) (ENNReal.ofReal p) P := by
      intro N
      dsimp [R]
      apply eLpNorm_sum_le
      · intro j hj
        exact (hDmem N z j).1
      · exact hpE
    have hRlim : Tendsto (fun N => eLpNorm (R N) (ENNReal.ofReal p) P)
        atTop (𝓝 0) := by
      have hs : Tendsto (fun N => ∑ j ∈ Finset.range H,
          eLpNorm (fun ω => F N z j ω - FL z j ω)
            (ENNReal.ofReal p) P) atTop (𝓝 0) := by
        simpa using (tendsto_finset_sum (s := Finset.range H)
          (f := fun j N => eLpNorm (fun ω => F N z j ω - FL z j ω)
            (ENNReal.ofReal p) P)
          (a := fun _ : ℕ => (0 : ℝ≥0∞)) (x := atTop)
          (fun j hj => by simpa using hcoordF z j))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) hs
        (Eventually.of_forall (fun _ => zero_le _)) (Eventually.of_forall hRle)
    convert hRlim using 1
    funext N
    dsimp [R]
    congr 1
    funext ω
    simp only [Finset.sum_apply, Pi.sub_apply]
    exact (Finset.sum_sub_distrib (s := Finset.range H)
      (fun j => F N z j ω) (fun j => FL z j ω)).symm
  have hb : Tendsto (fun H : ℕ =>
      ENNReal.ofReal ((A / (1 - r) + 1) * K *
        (3 : ℝ) ^ (-(eta * (H : ℝ))))) atTop (𝓝 0) := by
    have hrpow0 : Tendsto (fun H : ℕ => r ^ H) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have hreal : Tendsto (fun H : ℕ =>
        (A / (1 - r) + 1) * K * r ^ H) atTop (𝓝 0) := by
      simpa using hrpow0.const_mul ((A / (1 - r) + 1) * K)
    have hreal' : Tendsto (fun H : ℕ =>
        (A / (1 - r) + 1) * K *
          (3 : ℝ) ^ (-(eta * (H : ℝ)))) atTop (𝓝 0) := by
      simpa [hrpow] using hreal
    simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal'
  have hfull_le_tail : ∀ N z H, ∀ᵐ ω ∂P,
      (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal ≤
        (∑ j ∈ Finset.range H, F N z j ω) +
          ∑' j, F N z (j + H) ω := by
    intro N z H
    filter_upwards [hENtop N z, (hgeomN N z).1] with ω htop hsum
    have hshift : Summable (fun k : ℕ => F N z (k + H) ω) := by
      exact hsum.comp_injective (fun x y h => Nat.add_right_cancel h)
    have hupper : ∀ j, F N z j ω ≤
        (∑ j ∈ Finset.range H, F N z j ω) +
          ∑' j, F N z (j + H) ω := by
      intro j
      by_cases hj : j < H
      · exact (Finset.single_le_sum (fun k hk => hF0 N z k ω)
          (Finset.mem_range.mpr hj)).trans
          (le_add_of_nonneg_right (tsum_nonneg (fun k => hF0 N z (k + H) ω)))
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_gt hj)
        simpa [add_comm] using le_add_of_le_of_nonneg
          (hshift.le_tsum k (fun _ _ => hF0 N z _ ω))
          (Finset.sum_nonneg (fun k hk => hF0 N z k ω))
    rw [ENNReal.toReal_iSup (fun j => ENNReal.ofReal_ne_top)]
    simp_rw [ENNReal.toReal_ofReal (hF0 N z _ ω)]
    exact ciSup_le hupper
  have hfull_le_tailL : ∀ z H, ∀ᵐ ω ∂P,
      (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal ≤
        (∑ j ∈ Finset.range H, FL z j ω) +
          ∑' j, FL z (j + H) ω := by
    intro z H
    filter_upwards [hELtop z, (hgeomL z).1] with ω htop hsum
    have hshift : Summable (fun k : ℕ => FL z (k + H) ω) :=
      hsum.comp_injective (fun x y h => Nat.add_right_cancel h)
    have hupper : ∀ j, FL z j ω ≤
        (∑ j ∈ Finset.range H, FL z j ω) +
          ∑' j, FL z (j + H) ω := by
      intro j
      by_cases hj : j < H
      · exact (Finset.single_le_sum (fun k hk => hFL0 z k ω)
          (Finset.mem_range.mpr hj)).trans
          (le_add_of_nonneg_right (tsum_nonneg (fun k => hFL0 z (k + H) ω)))
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_gt hj)
        simpa [add_comm] using le_add_of_le_of_nonneg
          (hshift.le_tsum k (fun _ _ => hFL0 z _ ω))
          (Finset.sum_nonneg (fun k hk => hFL0 z k ω))
    rw [ENNReal.toReal_iSup (fun j => ENNReal.ofReal_ne_top)]
    simp_rw [ENNReal.toReal_ofReal (hFL0 z _ ω)]
    exact ciSup_le hupper

  have hfiniteSup : ∀ z H, Tendsto (fun N => eLpNorm (fun ω =>
      (⨆ j : Fin H, ENNReal.ofReal (F N z j.1 ω)).toReal -
        (⨆ j : Fin H, ENNReal.ofReal (FL z j.1 ω)).toReal)
      (ENNReal.ofReal p) P) atTop (𝓝 0) := by
    intro z H
    simpa using
      (aux_prefix_score_cauchy_finite_sup_diff_tendsto (I := Fin H) P p p hp le_rfl
        (fun N j ω => F N z j.1 ω) (fun j ω => FL z j.1 ω)
        (fun N j => hFmem N z j.1) (fun j => hFLmem z j.1)
        (fun N j => Eventually.of_forall (hF0 N z j.1))
        (fun j => Eventually.of_forall (hFL0 z j.1))
        (fun j => hcoordF z j.1))
  have hfiniteMeas : ∀ N z H, AEStronglyMeasurable (fun ω =>
      (⨆ j : Fin H, ENNReal.ofReal (F N z j.1 ω)).toReal) P := by
    intro N z H
    have hAE : AEMeasurable (fun ω =>
        ⨆ j : Fin H, ENNReal.ofReal (F N z j.1 ω)) P :=
      AEMeasurable.iSup (fun j =>
        ENNReal.measurable_ofReal.comp_aemeasurable
          ((hFmem N z j.1).1.aemeasurable))
    exact hAE.ennreal_toReal.aestronglyMeasurable
  have hfiniteMeasL : ∀ z H, AEStronglyMeasurable (fun ω =>
      (⨆ j : Fin H, ENNReal.ofReal (FL z j.1 ω)).toReal) P := by
    intro z H
    have hAE : AEMeasurable (fun ω =>
        ⨆ j : Fin H, ENNReal.ofReal (FL z j.1 ω)) P :=
      AEMeasurable.iSup (fun j =>
        ENNReal.measurable_ofReal.comp_aemeasurable
          ((hFLmem z j.1).1.aemeasurable))
    exact hAE.ennreal_toReal.aestronglyMeasurable
  let FinF : ∀ N z H, Ω → ℝ := fun N z H ω =>
    (⨆ j : Fin H, ENNReal.ofReal (F N z j.1 ω)).toReal
  let FinL : ∀ z H, Ω → ℝ := fun z H ω =>
    (⨆ j : Fin H, ENNReal.ofReal (FL z j.1 ω)).toReal
  let TailF : ∀ N z H, Ω → ℝ := fun N z H ω =>
    (⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (F N z j.1 ω)).toReal
  let TailL : ∀ z H, Ω → ℝ := fun z H ω =>
    (⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (FL z j.1 ω)).toReal
  have htailMeasF : ∀ N z H, AEStronglyMeasurable (TailF N z H) P := by
    intro N z H
    have hAE : AEMeasurable (fun ω =>
        ⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (F N z j.1 ω)) P :=
      AEMeasurable.iSup (fun j =>
        ENNReal.measurable_ofReal.comp_aemeasurable
          ((hFmem N z j.1).1.aemeasurable))
    exact hAE.ennreal_toReal.aestronglyMeasurable
  have htailMeasL : ∀ z H, AEStronglyMeasurable (TailL z H) P := by
    intro z H
    have hAE : AEMeasurable (fun ω =>
        ⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (FL z j.1 ω)) P :=
      AEMeasurable.iSup (fun j =>
        ENNReal.measurable_ofReal.comp_aemeasurable
          ((hFLmem z j.1).1.aemeasurable))
    exact hAE.ennreal_toReal.aestronglyMeasurable
  have htailMemF : ∀ N z H, MemLp (TailF N z H) (ENNReal.ofReal p) P := by
    intro N z H
    refine ⟨htailMeasF N z H, ?_⟩
    exact lt_of_le_of_lt (hsupbound N z H) ENNReal.ofReal_lt_top
  have htailMemL : ∀ z H, MemLp (TailL z H) (ENNReal.ofReal p) P := by
    intro z H
    refine ⟨htailMeasL z H, ?_⟩
    have htailbound : eLpNorm (TailL z H) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal ((A / (1 - r) + 1) * K *
          (3 : ℝ) ^ (-(eta * (H : ℝ)))) := by
      dsimp [TailL]
      have htailmem := (hgeomL z).2 H
      have hmono : ∀ᵐ ω ∂P, ∀ j : {j : ℕ // H ≤ j},
          ENNReal.ofReal (FL z j.1 ω) ≤
            ENNReal.ofReal (∑' k, FL z (k + H) ω) := by
        filter_upwards [hnormL z] with ω hω
        intro j
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le j.property
        have hshiftNorm : Summable (fun k : ℕ => ‖FL z (k + H) ω‖) := by
          simpa only [Function.comp_apply] using
            hω.comp_injective (fun x y h => Nat.add_right_cancel h)
        have hshift : Summable (fun k : ℕ => FL z (k + H) ω) :=
          hshiftNorm.of_norm
        apply ENNReal.ofReal_le_ofReal
        rw [hk, Nat.add_comm]
        exact hshift.le_tsum k (fun _ _ => hFL0 z _ ω)
      have hpoint : ∀ᵐ ω ∂P,
          (⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (FL z j.1 ω)).toReal ≤
            ∑' k, FL z (k + H) ω := by
        filter_upwards [hmono, hnormL z] with ω hω hnorm
        have hsup : (⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (FL z j.1 ω)) ≤
            ENNReal.ofReal (∑' k, FL z (k + H) ω) := iSup_le hω
        have hshiftNorm : Summable (fun k : ℕ => ‖FL z (k + H) ω‖) := by
          simpa only [Function.comp_apply] using
            hnorm.comp_injective (fun x y h => Nat.add_right_cancel h)
        have hshift : Summable (fun k : ℕ => FL z (k + H) ω) :=
          hshiftNorm.of_norm
        have hnonneg : 0 ≤ ∑' k, FL z (k + H) ω :=
          tsum_nonneg (fun k => hFL0 z (k + H) ω)
        calc
          (⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (FL z j.1 ω)).toReal ≤
              (ENNReal.ofReal (∑' k, FL z (k + H) ω)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hsup
          _ = ∑' k, FL z (k + H) ω := ENNReal.toReal_ofReal hnonneg
      have hle : eLpNorm (TailL z H) (ENNReal.ofReal p) P ≤
          eLpNorm (fun ω => ∑' k, FL z (k + H) ω)
            (ENNReal.ofReal p) P := by
        apply eLpNorm_mono_ae
        filter_upwards [hpoint] with ω hω
        have hnonneg : 0 ≤ ∑' k, FL z (k + H) ω :=
          tsum_nonneg (fun k => hFL0 z (k + H) ω)
        simpa only [TailL, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
          abs_of_nonneg hnonneg] using hω
      exact hle.trans ((htailmem.2).trans (ENNReal.ofReal_le_ofReal (htailreal H)))
    exact lt_of_le_of_lt htailbound ENNReal.ofReal_lt_top
  have hfiniteMemF : ∀ N z H, MemLp (FinF N z H) (ENNReal.ofReal p) P := by
    intro N z H
    refine ⟨hfiniteMeas N z H, ?_⟩
    have hle : ∀ᵐ ω ∂P, FinF N z H ω ≤
        (∑' j, F N z j ω) := by
      filter_upwards [hENtop N z, (hgeomN N z).1] with ω htop hsum
      have hsup : (⨆ j : Fin H, ENNReal.ofReal (F N z j.1 ω)) ≤
          (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)) := by
        exact iSup_le (fun j => le_iSup (fun k : ℕ => ENNReal.ofReal (F N z k ω)) j.1)
      calc
        FinF N z H ω ≤
            (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal := by
          dsimp [FinF]
          exact ENNReal.toReal_mono htop hsup
        _ ≤ ∑' j, F N z j ω := by
          have hnonneg : 0 ≤ ∑' j, F N z j ω :=
            tsum_nonneg (fun j => hF0 N z j ω)
          have hsum' : Summable (fun j => F N z j ω) := hsum
          rw [ENNReal.toReal_iSup (fun j => ENNReal.ofReal_ne_top)]
          simp_rw [ENNReal.toReal_ofReal (hF0 N z _ ω)]
          exact ciSup_le (fun j => hsum'.le_tsum j (fun _ _ => hF0 N z _ ω))
    exact lt_of_le_of_lt
      (eLpNorm_mono_ae (hle.mono fun ω h => by
        have h0 : 0 ≤ FinF N z H ω := ENNReal.toReal_nonneg
        have hs0 : 0 ≤ ∑' j, F N z j ω :=
          tsum_nonneg (fun j => hF0 N z j ω)
        simpa only [Real.norm_eq_abs, abs_of_nonneg h0,
          abs_of_nonneg hs0] using h))
      (hSNmem N z).2
  have hfiniteMemL : ∀ z H, MemLp (FinL z H) (ENNReal.ofReal p) P := by
    intro z H
    refine ⟨hfiniteMeasL z H, ?_⟩
    have hle : ∀ᵐ ω ∂P, FinL z H ω ≤
        (∑' j, FL z j ω) := by
      filter_upwards [hELtop z, (hgeomL z).1] with ω htop hsum
      have hsup : (⨆ j : Fin H, ENNReal.ofReal (FL z j.1 ω)) ≤
          (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)) := by
        exact iSup_le (fun j => le_iSup (fun k : ℕ => ENNReal.ofReal (FL z k ω)) j.1)
      calc
        FinL z H ω ≤
            (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal := by
          dsimp [FinL]
          exact ENNReal.toReal_mono htop hsup
        _ ≤ ∑' j, FL z j ω := by
          have hnonneg : 0 ≤ ∑' j, FL z j ω :=
            tsum_nonneg (fun j => hFL0 z j ω)
          rw [ENNReal.toReal_iSup (fun j => ENNReal.ofReal_ne_top)]
          simp_rw [ENNReal.toReal_ofReal (hFL0 z _ ω)]
          exact ciSup_le (fun j => hsum.le_tsum j (fun _ _ => hFL0 z _ ω))
    exact lt_of_le_of_lt
      (eLpNorm_mono_ae (hle.mono fun ω h => by
        have h0 : 0 ≤ FinL z H ω := ENNReal.toReal_nonneg
        have hs0 : 0 ≤ ∑' j, FL z j ω :=
          tsum_nonneg (fun j => hFL0 z j ω)
        simpa only [Real.norm_eq_abs, abs_of_nonneg h0,
          abs_of_nonneg hs0] using h))
      (hSLmem z).2
  have hfullsupF : ∀ N z H, ∀ᵐ ω ∂P,
      (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal ≤
        FinF N z H ω + TailF N z H ω := by
    intro N z H
    filter_upwards [hENtop N z, (hgeomN N z).1] with ω htop hsum
    have hupper : ∀ j : ℕ, F N z j ω ≤
        FinF N z H ω + TailF N z H ω := by
      intro j
      by_cases hj : j < H
      · have hle' : F N z j ω ≤ FinF N z H ω := by
          have hleE : ENNReal.ofReal (F N z j ω) ≤
              (⨆ k : Fin H, ENNReal.ofReal (F N z k.1 ω)) :=
            le_iSup (fun k : Fin H => ENNReal.ofReal (F N z k.1 ω))
              (⟨j, hj⟩ : Fin H)
          have hsmall : (⨆ k : Fin H, ENNReal.ofReal (F N z k.1 ω)) ≤
              (⨆ k : ℕ, ENNReal.ofReal (F N z k ω)) := iSup_le (fun k =>
                le_iSup (fun k : ℕ => ENNReal.ofReal (F N z k ω)) k.1)
          dsimp [FinF]
          have hsmalltop : (⨆ k : Fin H, ENNReal.ofReal (F N z k.1 ω)) ≠ ⊤ := by
            intro hs
            exact htop (eq_top_mono hsmall hs)
          simpa only [ENNReal.toReal_ofReal (hF0 N z j ω)] using
            (ENNReal.toReal_mono hsmalltop hleE)
        exact hle'.trans (le_add_of_nonneg_right (by
          exact ENNReal.toReal_nonneg))
      · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (le_of_not_gt hj)
        have hle' : F N z j ω ≤ TailF N z H ω := by
          have hleE : ENNReal.ofReal (F N z j ω) ≤
              (⨆ k : {j : ℕ // H ≤ j}, ENNReal.ofReal (F N z k.1 ω)) :=
            le_iSup (fun k : {j : ℕ // H ≤ j} => ENNReal.ofReal (F N z k.1 ω))
              (⟨j, le_of_not_gt hj⟩ : {j : ℕ // H ≤ j})
          have hsmall : (⨆ k : {j : ℕ // H ≤ j}, ENNReal.ofReal (F N z k.1 ω)) ≤
              (⨆ k : ℕ, ENNReal.ofReal (F N z k ω)) := iSup_le (fun k =>
                le_iSup (fun k : ℕ => ENNReal.ofReal (F N z k ω)) k.1)
          dsimp [TailF]
          have hsmalltop : (⨆ k : {j : ℕ // H ≤ j}, ENNReal.ofReal (F N z k.1 ω)) ≠ ⊤ := by
            intro hs
            exact htop (eq_top_mono hsmall hs)
          simpa only [ENNReal.toReal_ofReal (hF0 N z j ω)] using
            (ENNReal.toReal_mono hsmalltop hleE)
        exact le_add_of_nonneg_of_le ENNReal.toReal_nonneg hle'
    rw [ENNReal.toReal_iSup (fun j => ENNReal.ofReal_ne_top)]
    simp_rw [ENNReal.toReal_ofReal (hF0 N z _ ω)]
    exact ciSup_le hupper
  have hfullsupL : ∀ z H, ∀ᵐ ω ∂P,
      (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal ≤
        FinL z H ω + TailL z H ω := by
    intro z H
    filter_upwards [hELtop z, (hgeomL z).1] with ω htop hsum
    have hupper : ∀ j : ℕ, FL z j ω ≤
        FinL z H ω + TailL z H ω := by
      intro j
      by_cases hj : j < H
      · have hle' : FL z j ω ≤ FinL z H ω := by
          have hleE : ENNReal.ofReal (FL z j ω) ≤
              (⨆ k : Fin H, ENNReal.ofReal (FL z k.1 ω)) :=
            le_iSup (fun k : Fin H => ENNReal.ofReal (FL z k.1 ω))
              (⟨j, hj⟩ : Fin H)
          have hsmall : (⨆ k : Fin H, ENNReal.ofReal (FL z k.1 ω)) ≤
              (⨆ k : ℕ, ENNReal.ofReal (FL z k ω)) := iSup_le (fun k =>
                le_iSup (fun k : ℕ => ENNReal.ofReal (FL z k ω)) k.1)
          dsimp [FinL]
          have hsmalltop : (⨆ k : Fin H, ENNReal.ofReal (FL z k.1 ω)) ≠ ⊤ := by
            intro hs
            exact htop (eq_top_mono hsmall hs)
          simpa only [ENNReal.toReal_ofReal (hFL0 z j ω)] using
            (ENNReal.toReal_mono hsmalltop hleE)
        exact hle'.trans (le_add_of_nonneg_right ENNReal.toReal_nonneg)
      · have hle' : FL z j ω ≤ TailL z H ω := by
          have hleE : ENNReal.ofReal (FL z j ω) ≤
              (⨆ k : {j : ℕ // H ≤ j}, ENNReal.ofReal (FL z k.1 ω)) :=
            le_iSup (fun k : {j : ℕ // H ≤ j} => ENNReal.ofReal (FL z k.1 ω))
              (⟨j, le_of_not_gt hj⟩ : {j : ℕ // H ≤ j})
          have hsmall : (⨆ k : {j : ℕ // H ≤ j}, ENNReal.ofReal (FL z k.1 ω)) ≤
              (⨆ k : ℕ, ENNReal.ofReal (FL z k ω)) := iSup_le (fun k =>
                le_iSup (fun k : ℕ => ENNReal.ofReal (FL z k ω)) k.1)
          dsimp [TailL]
          have hsmalltop : (⨆ k : {j : ℕ // H ≤ j}, ENNReal.ofReal (FL z k.1 ω)) ≠ ⊤ := by
            intro hs
            exact htop (eq_top_mono hsmall hs)
          simpa only [ENNReal.toReal_ofReal (hFL0 z j ω)] using
            (ENNReal.toReal_mono hsmalltop hleE)
        exact le_add_of_nonneg_of_le ENNReal.toReal_nonneg hle'
    rw [ENNReal.toReal_iSup (fun j => ENNReal.ofReal_ne_top)]
    simp_rw [ENNReal.toReal_ofReal (hFL0 z _ ω)]
    exact ciSup_le hupper
  have hfinlefullF : ∀ N z H, ∀ᵐ ω ∂P, FinF N z H ω ≤
      (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal := by
    intro N z H
    filter_upwards [hENtop N z] with ω htop
    dsimp [FinF]
    exact ENNReal.toReal_mono htop (iSup_le (fun j =>
      le_iSup (fun k : ℕ => ENNReal.ofReal (F N z k ω)) j.1))
  have hfinlefullL : ∀ z H, ∀ᵐ ω ∂P, FinL z H ω ≤
      (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal := by
    intro z H
    filter_upwards [hELtop z] with ω htop
    dsimp [FinL]
    exact ENNReal.toReal_mono htop (iSup_le (fun j =>
      le_iSup (fun k : ℕ => ENNReal.ofReal (FL z k ω)) j.1))
  have hdom : ∀ z N H, eLpNorm (fun ω =>
      (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal -
        (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal)
      (ENNReal.ofReal p) P ≤
      eLpNorm (fun ω => FinF N z H ω - FinL z H ω)
        (ENNReal.ofReal p) P +
        eLpNorm (TailF N z H) (ENNReal.ofReal p) P +
        eLpNorm (TailL z H) (ENNReal.ofReal p) P := by
    intro z N H
    have hpt : ∀ᵐ ω ∂P,
        |(⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal -
            (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal| ≤
          |FinF N z H ω - FinL z H ω| + TailF N z H ω + TailL z H ω := by
      filter_upwards [hfullsupF N z H, hfullsupL z H,
        hfinlefullF N z H, hfinlefullL z H] with ω hF hL hFF hLL
      have hupper : (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal -
          (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal ≤
          (FinF N z H ω - FinL z H ω) + TailF N z H ω + TailL z H ω := by linarith
      have htF : 0 ≤ TailF N z H ω := ENNReal.toReal_nonneg
      have htL : 0 ≤ TailL z H ω := ENNReal.toReal_nonneg
      have hlower : -(|FinF N z H ω - FinL z H ω| + TailF N z H ω + TailL z H ω) ≤
          (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal -
            (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal := by
        linarith [neg_abs_le (FinF N z H ω - FinL z H ω)]
      have hupper' : (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal -
          (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal ≤
          |FinF N z H ω - FinL z H ω| + TailF N z H ω + TailL z H ω := by
        linarith [le_abs_self (FinF N z H ω - FinL z H ω)]
      exact (abs_le).2 ⟨hlower, hupper'⟩
    have hmono : eLpNorm (fun ω =>
        (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal -
          (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal)
        (ENNReal.ofReal p) P ≤
        eLpNorm (fun ω => |FinF N z H ω - FinL z H ω| +
          TailF N z H ω + TailL z H ω) (ENNReal.ofReal p) P := by
      apply eLpNorm_mono_ae
      filter_upwards [hpt] with ω hω
      have hnonneg : 0 ≤ |FinF N z H ω - FinL z H ω| +
          TailF N z H ω + TailL z H ω := by positivity
      simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hω
    have hDmem : MemLp (fun ω => FinF N z H ω - FinL z H ω)
        (ENNReal.ofReal p) P := (hfiniteMemF N z H).sub (hfiniteMemL z H)
    have hDmeas : AEStronglyMeasurable (fun ω =>
        |FinF N z H ω - FinL z H ω|) P := by
      simpa only [Real.norm_eq_abs] using hDmem.norm.1
    calc
      _ ≤ eLpNorm (fun ω => |FinF N z H ω - FinL z H ω| +
          TailF N z H ω + TailL z H ω) (ENNReal.ofReal p) P := hmono
      _ ≤ eLpNorm (fun ω => |FinF N z H ω - FinL z H ω| +
            TailF N z H ω) (ENNReal.ofReal p) P +
            eLpNorm (TailL z H) (ENNReal.ofReal p) P := by
        exact eLpNorm_add_le
          (hDmeas.add (htailMemF N z H).1)
          (htailMemL z H).1 hpE
      _ ≤ eLpNorm (fun ω => |FinF N z H ω - FinL z H ω|)
            (ENNReal.ofReal p) P + eLpNorm (TailF N z H)
            (ENNReal.ofReal p) P + eLpNorm (TailL z H)
            (ENNReal.ofReal p) P := by
        exact add_le_add_left
          (eLpNorm_add_le hDmeas (htailMemF N z H).1 hpE) _
      _ = eLpNorm (fun ω => FinF N z H ω - FinL z H ω)
            (ENNReal.ofReal p) P + eLpNorm (TailF N z H)
            (ENNReal.ofReal p) P + eLpNorm (TailL z H)
            (ENNReal.ofReal p) P := by
        have hnormEq : eLpNorm (fun ω =>
            |FinF N z H ω - FinL z H ω|) (ENNReal.ofReal p) P =
            eLpNorm (fun ω => FinF N z H ω - FinL z H ω)
              (ENNReal.ofReal p) P := by
          calc
            eLpNorm (fun ω => |FinF N z H ω - FinL z H ω|)
                (ENNReal.ofReal p) P =
                eLpNorm (fun ω => ‖FinF N z H ω - FinL z H ω‖)
                  (ENNReal.ofReal p) P :=
              eLpNorm_congr_ae (Eventually.of_forall (fun ω =>
                (Real.norm_eq_abs _).symm))
            _ = eLpNorm (fun ω => FinF N z H ω - FinL z H ω)
                (ENNReal.ofReal p) P := eLpNorm_norm _
        rw [hnormEq]

  have htailFbound : ∀ N z H, eLpNorm (TailF N z H)
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal ((A / (1 - r) + 1) * K *
        (3 : ℝ) ^ (-(eta * (H : ℝ)))) := by
    intro N z H
    simpa [TailF] using hsupbound N z H
  have htailLbound : ∀ z H, eLpNorm (TailL z H)
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal ((A / (1 - r) + 1) * K *
        (3 : ℝ) ^ (-(eta * (H : ℝ)))) := by
    intro z H
    have htailmem := (hgeomL z).2 H
    have hmono : ∀ᵐ ω ∂P, ∀ j : {j : ℕ // H ≤ j},
        ENNReal.ofReal (FL z j.1 ω) ≤
          ENNReal.ofReal (∑' k, FL z (k + H) ω) := by
      filter_upwards [hnormL z] with ω hω
      intro j
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le j.property
      have hshiftNorm : Summable (fun k : ℕ => ‖FL z (k + H) ω‖) := by
        simpa only [Function.comp_apply] using
          hω.comp_injective (fun x y h => Nat.add_right_cancel h)
      have hshift : Summable (fun k : ℕ => FL z (k + H) ω) := hshiftNorm.of_norm
      apply ENNReal.ofReal_le_ofReal
      rw [hk, Nat.add_comm]
      exact hshift.le_tsum k (fun _ _ => hFL0 z _ ω)
    have hpoint : ∀ᵐ ω ∂P,
        (⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (FL z j.1 ω)).toReal ≤
          ∑' k, FL z (k + H) ω := by
      filter_upwards [hmono, hnormL z] with ω hω hnorm
      have hsup : (⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (FL z j.1 ω)) ≤
          ENNReal.ofReal (∑' k, FL z (k + H) ω) := iSup_le hω
      have hnonneg : 0 ≤ ∑' k, FL z (k + H) ω :=
        tsum_nonneg (fun k => hFL0 z (k + H) ω)
      calc
        (⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (FL z j.1 ω)).toReal ≤
            (ENNReal.ofReal (∑' k, FL z (k + H) ω)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hsup
        _ = ∑' k, FL z (k + H) ω := ENNReal.toReal_ofReal hnonneg
    have hle : eLpNorm (TailL z H) (ENNReal.ofReal p) P ≤
        eLpNorm (fun ω => ∑' k, FL z (k + H) ω)
          (ENNReal.ofReal p) P := by
      apply eLpNorm_mono_ae
      filter_upwards [hpoint] with ω hω
      have hnonneg : 0 ≤ ∑' k, FL z (k + H) ω :=
        tsum_nonneg (fun k => hFL0 z (k + H) ω)
      simpa only [TailL, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
        abs_of_nonneg hnonneg] using hω
    exact hle.trans ((htailmem.2).trans (ENNReal.ofReal_le_ofReal (htailreal H)))
  let Btail : ℕ → ℝ≥0∞ := fun H => ENNReal.ofReal ((A / (1 - r) + 1) * K *
    (3 : ℝ) ^ (-(eta * (H : ℝ))))
  have hBtail : Tendsto Btail atTop (𝓝 0) := by simpa [Btail] using hb
  have hENconv : ∀ z, Tendsto (fun N => eLpNorm (fun ω =>
      (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal -
        (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal)
      (ENNReal.ofReal p) P) atTop (𝓝 0) := by
    intro z
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    have hε3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
    obtain ⟨H, hH⟩ := eventually_atTop.1
      ((ENNReal.tendsto_nhds_zero.mp hBtail) (ε / 3) hε3)
    obtain ⟨N, hN⟩ := eventually_atTop.1
      ((ENNReal.tendsto_nhds_zero.mp (hfiniteSup z H)) (ε / 3) hε3)
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hTF : eLpNorm (TailF n z H) (ENNReal.ofReal p) P ≤ ε / 3 := by
      exact (htailFbound n z H).trans (hH H le_rfl)
    have hTL : eLpNorm (TailL z H) (ENNReal.ofReal p) P ≤ ε / 3 := by
      exact (htailLbound z H).trans (hH H le_rfl)
    calc
      eLpNorm (fun ω =>
          (⨆ j : ℕ, ENNReal.ofReal (F n z j ω)).toReal -
            (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal)
          (ENNReal.ofReal p) P ≤
        eLpNorm (fun ω => FinF n z H ω - FinL z H ω)
            (ENNReal.ofReal p) P + eLpNorm (TailF n z H)
            (ENNReal.ofReal p) P + eLpNorm (TailL z H)
            (ENNReal.ofReal p) P := hdom z n H
      _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        exact add_le_add (add_le_add (by simpa [FinF, FinL] using hN n hn)
          hTF) hTL
      _ = ε := by simpa [add_assoc] using ENNReal.add_thirds ε
  have hTNmeas : ∀ N z, AEStronglyMeasurable (fun ω =>
      (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal) P := by
    intro N z
    exact (AEMeasurable.iSup (fun j =>
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((hFmem N z j).1.aemeasurable))).ennreal_toReal.aestronglyMeasurable
  have hTLmeas : ∀ z, AEStronglyMeasurable (fun ω =>
      (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal) P := by
    intro z
    exact (AEMeasurable.iSup (fun j =>
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((hFLmem z j).1.aemeasurable))).ennreal_toReal.aestronglyMeasurable
  have hTNmem : ∀ N z, MemLp (fun ω =>
      (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal)
      (ENNReal.ofReal p) P := by
    intro N z
    refine ⟨hTNmeas N z, ?_⟩
    have hle : ∀ᵐ ω ∂P, (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal ≤
        ∑' j, F N z j ω := by
      simpa using hfull_le_tail N z 0
    exact lt_of_le_of_lt
      (eLpNorm_mono_ae (hle.mono fun ω h => by
        have hs0 : 0 ≤ ∑' j, F N z j ω := tsum_nonneg (fun j => hF0 N z j ω)
        simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
          abs_of_nonneg hs0] using h))
      (hSNmem N z).2
  have hTLmem : ∀ z, MemLp (fun ω =>
      (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal)
      (ENNReal.ofReal p) P := by
    intro z
    refine ⟨hTLmeas z, ?_⟩
    have hle : ∀ᵐ ω ∂P, (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal ≤
        ∑' j, FL z j ω := by
      simpa using hfull_le_tailL z 0
    exact lt_of_le_of_lt
      (eLpNorm_mono_ae (hle.mono fun ω h => by
        have hs0 : 0 ≤ ∑' j, FL z j ω := tsum_nonneg (fun j => hFL0 z j ω)
        simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
          abs_of_nonneg hs0] using h))
      (hSLmem z).2
  have hmainconv : ∀ z, Tendsto (fun N => eLpNorm (fun ω =>
      (∑' j, F N z j ω) - ∑' j, FL z j ω) (ENNReal.ofReal p) P)
      atTop (𝓝 0) ∧ Tendsto (fun N => eLpNorm (fun ω =>
      (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal -
        (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal)
      (ENNReal.ofReal p) P) atTop (𝓝 0) := by
    intro z
    exact ⟨hSNconv z, hENconv z⟩
  have hsqrt_transfer : ∀ (f : ℕ → Ω → ℝ) (g : Ω → ℝ),
      (∀ N, MemLp (f N) (ENNReal.ofReal p) P) →
      MemLp g (ENNReal.ofReal p) P →
      (∀ N, ∀ᵐ ω ∂P, 0 ≤ f N ω) → (∀ᵐ ω ∂P, 0 ≤ g ω) →
      Tendsto (fun N => eLpNorm (fun ω => f N ω - g ω)
        (ENNReal.ofReal p) P) atTop (𝓝 (0 : ℝ≥0∞)) →
      Tendsto (fun N => eLpNorm (fun ω =>
        Real.sqrt (max 0 (f N ω)) - Real.sqrt (max 0 (g ω)))
        (ENNReal.ofReal p) P) atTop (𝓝 0) := by
    intro f g hf hg hfa hga hlim
    have hD : ∀ N, MemLp (fun ω => f N ω - g ω) (ENNReal.ofReal p) P :=
      fun N => (hf N).sub hg
    have hmono : ∀ N, eLpNorm (fun ω =>
        Real.sqrt (max 0 (f N ω)) - Real.sqrt (max 0 (g ω)))
        (ENNReal.ofReal p) P ≤
        eLpNorm (fun ω => Real.sqrt |f N ω - g ω|)
          (ENNReal.ofReal p) P := by
      intro N
      apply eLpNorm_mono_ae
      filter_upwards [hfa N, hga] with ω hωf hωg
      have hs := aux_prefix_score_cauchy_sqrt_sub_le (f N ω) (g ω) hωf hωg
      simpa only [max_eq_right hωf, max_eq_right hωg, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)] using hs
    have hhalf : ENNReal.ofReal p * ENNReal.ofReal (1 / 2 : ℝ) ≤
        ENNReal.ofReal p := by
      have hh : ENNReal.ofReal (1 / 2 : ℝ) ≤ (1 : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by norm_num)
      simpa using
        (mul_le_mul_of_nonneg_left hh
          (by positivity : 0 ≤ ENNReal.ofReal p))
    have hpow : ∀ N, eLpNorm (fun ω => Real.sqrt |f N ω - g ω|)
        (ENNReal.ofReal p) P =
        (eLpNorm (fun ω => f N ω - g ω)
          (ENNReal.ofReal p * ENNReal.ofReal (1 / 2 : ℝ)) P) ^ (1 / 2 : ℝ) := by
      intro N
      simpa only [Real.sqrt_eq_rpow, Real.norm_eq_abs] using
        (eLpNorm_norm_rpow (fun ω => f N ω - g ω) (p := ENNReal.ofReal p)
          (q := (1 / 2 : ℝ)) (by norm_num))
    have hbound : ∀ _N : ℕ, eLpNorm (fun ω =>
        Real.sqrt (max 0 (f _N ω)) - Real.sqrt (max 0 (g ω)))
        (ENNReal.ofReal p) P ≤
        (eLpNorm (fun ω => f _N ω - g ω) (ENNReal.ofReal p) P) ^ (1 / 2 : ℝ) := by
      intro N
      calc
        _ ≤ eLpNorm (fun ω => Real.sqrt |f N ω - g ω|)
            (ENNReal.ofReal p) P := hmono N
        _ = (eLpNorm (fun ω => f N ω - g ω)
            (ENNReal.ofReal p * ENNReal.ofReal (1 / 2 : ℝ)) P) ^ (1 / 2 : ℝ) := hpow N
        _ ≤ (eLpNorm (fun ω => f N ω - g ω)
            (ENNReal.ofReal p) P) ^ (1 / 2 : ℝ) := by
          exact ENNReal.rpow_le_rpow
            (eLpNorm_le_eLpNorm_of_exponent_le hhalf (hD N).1) (by norm_num)
    have hpowlim : Tendsto (fun N =>
        (eLpNorm (fun ω => f N ω - g ω) (ENNReal.ofReal p) P) ^
          (1 / 2 : ℝ)) atTop (𝓝 0) := by
      simpa using
        ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hlim
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
      hpowlim
      (Eventually.of_forall (fun _ => zero_le _))
      (Eventually.of_forall hbound)
  have hramp_transfer : ∀ (f : ℕ → Ω → ℝ) (g : Ω → ℝ),
      (∀ N, MemLp (f N) (ENNReal.ofReal p) P) →
      MemLp g (ENNReal.ofReal p) P →
      Tendsto (fun N => eLpNorm (fun ω => f N ω - g ω)
        (ENNReal.ofReal p) P) atTop (𝓝 0) →
      ∀ l u : ℝ, l < u →
      Tendsto (fun N => eLpNorm (fun ω =>
        min 1 (max 0 ((f N ω - l) / (u - l))) -
          min 1 (max 0 ((g ω - l) / (u - l))))
        (ENNReal.ofReal p) P) atTop (𝓝 0) := by
    intro f g hf hg hlim l u hlu
    let c : ℝ := 1 / (u - l)
    have hc : 0 < c := by
      dsimp [c]
      exact one_div_pos.mpr (sub_pos.mpr hlu)
    have hpoint : ∀ N, ∀ᵐ ω ∂P, |min 1 (max 0 ((f N ω - l) / (u - l))) -
        min 1 (max 0 ((g ω - l) / (u - l)))| ≤
        c * |f N ω - g ω| := by
      intro N
      filter_upwards [] with ω
      calc
        _ ≤ max |(1 : ℝ) - 1| (abs (max 0 ((f N ω - l) / (u - l)) -
              max 0 ((g ω - l) / (u - l)))) :=
          abs_min_sub_min_le_max _ _ _ _
        _ ≤ |(f N ω - l) / (u - l) - (g ω - l) / (u - l)| := by
          simp only [sub_self, abs_zero]
          rw [max_eq_right (abs_nonneg _)]
          exact aux_prefix_score_cauchy_pospart_lipschitz _ _
        _ = c * |f N ω - g ω| := by
          rw [div_sub_div_same, abs_div, abs_of_pos (sub_pos.mpr hlu)]
          simp [c, div_eq_mul_inv, mul_comm]
    have hD : ∀ N, MemLp (fun ω => f N ω - g ω) (ENNReal.ofReal p) P :=
      fun N => (hf N).sub hg
    have hbound : ∀ _N : ℕ, eLpNorm (fun ω =>
        min 1 (max 0 ((f _N ω - l) / (u - l))) -
          min 1 (max 0 ((g ω - l) / (u - l))))
        (ENNReal.ofReal p) P ≤
        ENNReal.ofReal c * eLpNorm (fun ω => f _N ω - g ω)
          (ENNReal.ofReal p) P := by
      intro N
      calc
        _ ≤ eLpNorm (fun ω => c • (f N ω - g ω))
            (ENNReal.ofReal p) P := by
          apply eLpNorm_mono_ae
          filter_upwards [hpoint N] with ω hω
          simpa only [Real.norm_eq_abs, smul_eq_mul, abs_mul, abs_of_pos hc] using hω
        _ = ENNReal.ofReal c * eLpNorm (fun ω => f N ω - g ω)
            (ENNReal.ofReal p) P := by
          change eLpNorm (c • (fun ω => f N ω - g ω))
            (ENNReal.ofReal p) P = _
          rw [eLpNorm_const_smul]
          simp [Real.enorm_eq_ofReal hc.le]
    have hscaled : Tendsto (fun N => ENNReal.ofReal c *
        eLpNorm (fun ω => f N ω - g ω) (ENNReal.ofReal p) P)
        atTop (𝓝 0) := by
      simpa using ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).tendsto 0).comp hlim
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
      hscaled (Eventually.of_forall (fun _ => zero_le _))
      (Eventually.of_forall hbound)

  have hsum0N : ∀ N z, ∀ᵐ ω ∂P, 0 ≤ ∑' j : ℕ, F N z j ω := by
    intro N z
    filter_upwards [(hgeomN N z).1] with ω hω
    exact tsum_nonneg (fun j => hF0 N z j ω)
  have hsum0L : ∀ z, ∀ᵐ ω ∂P, 0 ≤ ∑' j : ℕ, FL z j ω := by
    intro z
    filter_upwards [(hgeomL z).1] with ω hω
    exact tsum_nonneg (fun j => hFL0 z j ω)
  have hmemNout : ∀ N z, MemLp (fun ω => ∑' j : ℕ, F N z j ω)
      (ENNReal.ofReal p) P ∧
      MemLp (fun ω => (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal)
        (ENNReal.ofReal p) P := by
    intro N z
    exact ⟨hSNmem N z, hTNmem N z⟩
  have hmemLout : ∀ z, MemLp (fun ω => ∑' j : ℕ, FL z j ω)
      (ENNReal.ofReal p) P ∧
      MemLp (fun ω => (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal)
        (ENNReal.ofReal p) P := by
    intro z
    exact ⟨hSLmem z, hTLmem z⟩
  have hsqrtOut : ∀ z, Tendsto (fun N => eLpNorm (fun ω =>
      Real.sqrt (max 0 (∑' j : ℕ, F N z j ω)) -
        Real.sqrt (max 0 (∑' j : ℕ, FL z j ω)))
      (ENNReal.ofReal p) P) atTop (𝓝 0) ∧
      Tendsto (fun N => eLpNorm (fun ω =>
        Real.sqrt (max 0 ((⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal)) -
          Real.sqrt (max 0 ((⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal)))
        (ENNReal.ofReal p) P) atTop (𝓝 0) := by
    intro z
    constructor
    · exact hsqrt_transfer
        (fun N ω => ∑' j : ℕ, F N z j ω)
        (fun ω => ∑' j : ℕ, FL z j ω)
        (fun N => hSNmem N z) (hSLmem z)
        (fun N => hsum0N N z) (hsum0L z) (hSNconv z)
    · exact hsqrt_transfer
        (fun N ω => (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal)
        (fun ω => (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal)
        (fun N => hTNmem N z) (hTLmem z)
        (fun N => Eventually.of_forall (fun ω => ENNReal.toReal_nonneg))
        (Eventually.of_forall (fun ω => ENNReal.toReal_nonneg)) (hmainconv z).2
  have hrampOut : ∀ z l u, l < u →
      Tendsto (fun N => eLpNorm (fun ω =>
        min 1 (max 0 (((∑' j : ℕ, F N z j ω) - l) / (u - l))) -
          min 1 (max 0 (((∑' j : ℕ, FL z j ω) - l) / (u - l))))
        (ENNReal.ofReal p) P) atTop (𝓝 0) ∧
      Tendsto (fun N => eLpNorm
        (fun ω =>
          min 1 (max 0 (((⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal - l) /
            (u - l))) -
            min 1 (max 0 (((⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal - l) /
              (u - l))))
        (ENNReal.ofReal p) P) atTop (𝓝 0) := by
    intro z l u hlu
    constructor
    · exact hramp_transfer
        (fun N ω => ∑' j : ℕ, F N z j ω)
        (fun ω => ∑' j : ℕ, FL z j ω)
        (fun N => hSNmem N z) (hSLmem z) (hSNconv z) l u hlu
    · exact hramp_transfer
        (fun N ω => (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal)
        (fun ω => (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal)
        (fun N => hTNmem N z) (hTLmem z) (hmainconv z).2 l u hlu
  exact
    (show
      (∀ z, ∀ᵐ ω ∂P,
        (∀ N, Summable (fun j : ℕ => F N z j ω)) ∧
        Summable (fun j : ℕ => FL z j ω) ∧
        (∀ N, (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)) ≠ ⊤) ∧
        (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)) ≠ ⊤) ∧
      (∀ N z, MemLp (fun ω => ∑' j : ℕ, F N z j ω) (ENNReal.ofReal p) P ∧
        MemLp (fun ω => (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal)
          (ENNReal.ofReal p) P) ∧
      (∀ z, MemLp (fun ω => ∑' j : ℕ, FL z j ω) (ENNReal.ofReal p) P ∧
        MemLp (fun ω => (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal)
          (ENNReal.ofReal p) P) ∧
      (∀ N z H, eLpNorm (fun ω => ∑' j : ℕ, F N z j ω -
          ∑ j ∈ Finset.range H, F N z j ω) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal ((A / (1 - r) + 1) * K * 3 ^ (-(eta * (H : ℝ))))) ∧
      (∀ (N : ℕ) (z : Pos) (H : ℕ), eLpNorm (fun ω =>
          (⨆ j : {j : ℕ // H ≤ j}, ENNReal.ofReal (F N z j.1 ω)).toReal)
        (ENNReal.ofReal p) P ≤
        ENNReal.ofReal ((A / (1 - r) + 1) * K * 3 ^ (-(eta * (H : ℝ))))) ∧
      (∀ z, Tendsto (fun N => eLpNorm (fun ω => ∑' j : ℕ, F N z j ω -
          ∑' j : ℕ, FL z j ω) (ENNReal.ofReal p) P) atTop (𝓝 0) ∧
        Tendsto (fun N => eLpNorm (fun ω =>
          (⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal -
            (⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal)
          (ENNReal.ofReal p) P) atTop (𝓝 0)) ∧
      (∀ z, Tendsto (fun N => eLpNorm (fun ω =>
          Real.sqrt (max 0 (∑' j : ℕ, F N z j ω)) -
            Real.sqrt (max 0 (∑' j : ℕ, FL z j ω)))
          (ENNReal.ofReal p) P) atTop (𝓝 0) ∧
        Tendsto (fun N => eLpNorm (fun ω =>
          Real.sqrt (max 0 ((⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal)) -
            Real.sqrt (max 0 ((⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal)))
          (ENNReal.ofReal p) P) atTop (𝓝 0)) ∧
      (∀ z l u, l < u →
        Tendsto (fun N => eLpNorm (fun ω =>
          min 1 (max 0 (((∑' j : ℕ, F N z j ω) - l) / (u - l))) -
            min 1 (max 0 (((∑' j : ℕ, FL z j ω) - l) / (u - l))))
          (ENNReal.ofReal p) P) atTop (𝓝 0) ∧
        Tendsto (fun N => eLpNorm (fun ω =>
          min 1 (max 0 (((⨆ j : ℕ, ENNReal.ofReal (F N z j ω)).toReal - l) /
            (u - l))) -
            min 1 (max 0 (((⨆ j : ℕ, ENNReal.ofReal (FL z j ω)).toReal - l) /
              (u - l))))
          (ENNReal.ofReal p) P) atTop (𝓝 0))
      from ⟨hfirst, hmemNout, hmemLout, hpartialbound, hsupbound,
        hmainconv, hsqrtOut, hrampOut⟩)

end Paper
