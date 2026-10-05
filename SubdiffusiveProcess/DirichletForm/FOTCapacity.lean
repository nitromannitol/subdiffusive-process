module

public import SubdiffusiveProcess.DirichletForm.FOTCapacityEnergyEstimate
public import Mathlib.MeasureTheory.OuterMeasure.OfFunction

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

noncomputable section

namespace SubdiffusiveProcess.DirichletForm.FOTConstruction

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {m : Measure X}

/-- A cutoff's energy norm cost; countable covers remove the compact-support restriction. -/
def cutoffCost (F : _root_.SubdiffusiveProcess.DirichletForm m) (U A : Set X) : ℝ≥0∞ :=
  ⨅ (u : Lp ℝ 2 m) (_hu : F.toClosedForm.MemCoreOn U u)
    (f : X → ℝ) (_hf : Continuous f) (_hc : HasCompactSupport f)
    (_hU : tsupport f ⊆ U) (_hae : ⇑u =ᵐ[m] f)
    (_h01 : ∀ x, f x ∈ Icc 0 1) (_hA : ∀ x ∈ A, f x = 1),
      ENNReal.ofReal (Real.sqrt (F.energyNormSq u))

theorem cutoffCost_empty (F : _root_.SubdiffusiveProcess.DirichletForm m) (U : Set X) :
    cutoffCost F U ∅ = 0 := by
  apply le_antisymm _ zero_le
  unfold cutoffCost
  refine iInf_le_of_le (0 : Lp ℝ 2 m) (iInf_le_of_le
    (F.toClosedForm.memCoreOn_zero U) (iInf_le_of_le (0 : X → ℝ)
      (iInf_le_of_le continuous_const (iInf_le_of_le ?_ (iInf_le_of_le ?_
        (iInf_le_of_le (Lp.coeFn_zero ℝ 2 m) (iInf_le_of_le ?_
          (iInf_le_of_le ?_ ?_))))))))
  · simp only [HasCompactSupport, tsupport_zero, isCompact_empty]
  · simp only [tsupport_zero, empty_subset]
  · intro x
    exact ⟨le_rfl, zero_le_one⟩
  · intro x hx
    exact False.elim hx
  · simp only [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq, F.form_zero_left F.domain.zero_mem,
      norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero,
      Real.sqrt_zero, ENNReal.ofReal_zero, le_refl]

def coreCapacity (F : _root_.SubdiffusiveProcess.DirichletForm m) (U : Set X) : OuterMeasure X :=
  OuterMeasure.ofFunction (cutoffCost F U) (cutoffCost_empty F U)

/-- Truncating the absolute value gives a cutoff of a superlevel set. -/
theorem capacityCutoff_exists (F : _root_.SubdiffusiveProcess.DirichletForm m) {U : Set X}
    {u : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    {f : X → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hfU : tsupport f ⊆ U) (hae : ⇑u =ᵐ[m] f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (v : Lp ℝ 2 m) (g : X → ℝ),
      F.toClosedForm.MemCoreOn U v ∧ Continuous g ∧ HasCompactSupport g ∧
      tsupport g ⊆ U ∧ ⇑v =ᵐ[m] g ∧ (∀ x, g x ∈ Icc 0 1) ∧
      (∀ x, ε ≤ |f x| → g x = 1) ∧
      Real.sqrt (F.energyNormSq v) ≤ Real.sqrt (F.energyNormSq u) / ε := by
  let L : ℝ≥0 := ⟨ε⁻¹, inv_nonneg.mpr hε.le⟩
  have hAbs : LipschitzWith L (fun t : ℝ => ε⁻¹ * |t|) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hε)]
    exact mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub s t) L.coe_nonneg
  let G : ℝ → ℝ := fun t => unitTruncation (ε⁻¹ * |t|)
  have hG : LipschitzWith L G := by
    simpa only [Function.comp_def, G, one_mul] using! lipschitzWith_unitTruncation.comp hAbs
  have hG0 : G 0 = 0 := by simp only [G, abs_zero, mul_zero, unitTruncation_zero]
  let v : Lp ℝ 2 m := hG.compLp hG0 u
  let g : X → ℝ := G ∘ f
  have hv : ⇑v =ᵐ[m] g := (hG.coeFn_compLp hG0 u).trans (hae.fun_comp G)
  have hvD := lipschitz_comp_mem F hG hG0 hu.1 (hG.coeFn_compLp hG0 u)
  refine ⟨v, g, memCoreOn_compLp F hu hG hG0, hG.continuous.comp hf,
    hc.comp_left hG0, (tsupport_comp_subset hG0 f).trans hfU, hv, ?_, ?_, ?_⟩
  · intro x
    change max (min (ε⁻¹ * |f x|) 1) 0 ∈ Icc 0 1
    exact ⟨le_max_right _ _, max_le (min_le_right _ _) zero_le_one⟩
  · intro x hx
    have h : 1 ≤ ε⁻¹ * |f x| := by
      rw [inv_mul_eq_div, le_div_iff₀ hε, one_mul]
      exact hx
    simp only [g, Function.comp_apply, G, unitTruncation, min_eq_right h,
      max_eq_left zero_le_one]
  · have hn := hG.norm_compLp_le hG0 u
    have hnsq : ‖v‖ ^ 2 ≤ (L : ℝ) ^ 2 * ‖u‖ ^ 2 := by
      calc
        ‖v‖ ^ 2 ≤ ((L : ℝ) * ‖u‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg v) hn 2
        _ = (L : ℝ) ^ 2 * ‖u‖ ^ 2 := mul_pow _ _ _
    have hE : F.energyNormSq v ≤ (L : ℝ) ^ 2 * F.energyNormSq u := by
      unfold _root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq
      nlinarith [hvD.2]
    calc
      Real.sqrt (F.energyNormSq v) ≤
          Real.sqrt ((L : ℝ) ^ 2 * F.energyNormSq u) := Real.sqrt_le_sqrt hE
      _ = (L : ℝ) * Real.sqrt (F.energyNormSq u) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq L.coe_nonneg]
      _ = Real.sqrt (F.energyNormSq u) / ε := by
        change ε⁻¹ * Real.sqrt (F.energyNormSq u) = Real.sqrt (F.energyNormSq u) / ε
        rw [div_eq_mul_inv, mul_comm]

theorem coreCapacity_level (F : _root_.SubdiffusiveProcess.DirichletForm m) {U : Set X}
    {u : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u)
    {f : X → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (hae : ⇑u =ᵐ[m] f) {ε : ℝ} (hε : 0 < ε) :
    coreCapacity F U {x | ε < |f x|} ≤
      ENNReal.ofReal (Real.sqrt (F.energyNormSq u) / ε) := by
  obtain ⟨v, g, hv, hg, hgc, hgU, hgae, hg01, hg1, hcost⟩ :=
    capacityCutoff_exists F hu hf hc hfU hae hε
  refine (OuterMeasure.ofFunction_le _).trans ?_
  unfold cutoffCost
  refine iInf_le_of_le v (iInf_le_of_le hv (iInf_le_of_le g
    (iInf_le_of_le hg (iInf_le_of_le hgc (iInf_le_of_le hgU
      (iInf_le_of_le hgae (iInf_le_of_le hg01 (iInf_le_of_le ?_ ?_))))))))
  · intro x hx
    exact hg1 x hx.le
  · exact ENNReal.ofReal_le_ofReal hcost

theorem coreCapacity_zero_cover (F : _root_.SubdiffusiveProcess.DirichletForm m) {U A : Set X}
    (hA : coreCapacity F U A = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (u : ℕ → Lp ℝ 2 m) (f : ℕ → X → ℝ) (O : ℕ → Set X),
      (∀ n, F.toClosedForm.MemCoreOn U (u n)) ∧
      (∀ n, Continuous (f n) ∧ HasCompactSupport (f n) ∧ tsupport (f n) ⊆ U ∧
        ⇑(u n) =ᵐ[m] f n ∧ (∀ x, f n x ∈ Icc 0 1)) ∧
      (∀ n, IsOpen (O n) ∧ O n ⊆ U ∧ ∀ x ∈ O n, f n x = 1) ∧
      A ⊆ ⋃ n, O n ∧
      ∑' n, ENNReal.ofReal (Real.sqrt (F.energyNormSq (u n))) < ENNReal.ofReal ε := by
  classical
  let δ : ℝ≥0∞ := ENNReal.ofReal (ε / 4)
  have hδ : 0 < δ := ENNReal.ofReal_pos.mpr (by positivity)
  have hcover : ∃ S : ℕ → Set X, A ⊆ ⋃ n, S n ∧
      ∑' n, cutoffCost F U (S n) < δ := by
    have hlt : coreCapacity F U A < δ := by rw [hA]; exact hδ
    simp only [coreCapacity, OuterMeasure.ofFunction_apply, iInf_lt_iff] at hlt
    obtain ⟨S, hAS, hS⟩ := hlt
    exact ⟨S, hAS, hS⟩
  obtain ⟨S, hAS, hS⟩ := hcover
  obtain ⟨η, hη, hηsum⟩ := ENNReal.exists_pos_sum_of_countable hδ.ne' ℕ
  have hchoice : ∀ n, ∃ (u : Lp ℝ 2 m), F.toClosedForm.MemCoreOn U u ∧
      ∃ f : X → ℝ, Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ U ∧
        ⇑u =ᵐ[m] f ∧ (∀ x, f x ∈ Icc 0 1) ∧ (∀ x ∈ S n, f x = 1) ∧
        ENNReal.ofReal (Real.sqrt (F.energyNormSq u)) <
          cutoffCost F U (S n) + η n := by
    intro n
    have hfin : cutoffCost F U (S n) ≠ ⊤ :=
      ne_top_of_le_ne_top (ne_top_of_lt hS) (ENNReal.le_tsum (f := fun n => cutoffCost F U (S n)) n)
    have hlt := ENNReal.lt_add_right hfin
      (by exact_mod_cast (hη n).ne' : (η n : ℝ≥0∞) ≠ 0)
    simp only [cutoffCost, iInf_lt_iff] at hlt
    obtain ⟨u, hu, f, hf, hfc, hfU, hfae, hf01, hfS, hcost⟩ := hlt
    exact ⟨u, hu, f, hf, hfc, hfU, hfae, hf01, hfS, hcost⟩
  choose u hu f hf hfc hfU hfae hf01 hfS hcost using hchoice
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  choose v g hv hg hgc hgU hgae hg01 hg1 hvcost using
    fun n => capacityCutoff_exists F (hu n) (hf n) (hfc n) (hfU n) (hfae n) hhalf
  let O : ℕ → Set X := fun n => {x | (1 / 2 : ℝ) < f n x}
  refine ⟨v, g, O, hv, fun n => ⟨hg n, hgc n, hgU n, hgae n, hg01 n⟩, ?_, ?_, ?_⟩
  · intro n
    refine ⟨isOpen_lt continuous_const (hf n), ?_, ?_⟩
    · intro x hx
      exact hfU n (subset_tsupport (f n) (by
        change f n x ≠ 0
        have hx' : (1 / 2 : ℝ) < f n x := hx
        linarith))
    · intro x hx
      apply hg1 n x
      exact (by
        have hx' : (1 / 2 : ℝ) < f n x := hx
        exact hx'.le.trans (le_abs_self _))
  · intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hAS hx)
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change (1 / 2 : ℝ) < f n x
    rw [hfS n x hn]
    norm_num
  · have hs : (∑' n, ENNReal.ofReal (Real.sqrt (F.energyNormSq (u n)))) < δ + δ :=
      lt_of_le_of_lt (ENNReal.tsum_le_tsum fun n => (hcost n).le) (by
        rw [ENNReal.tsum_add]
        exact ENNReal.add_lt_add hS hηsum)
    calc
      (∑' n, ENNReal.ofReal (Real.sqrt (F.energyNormSq (v n)))) ≤
          ∑' n, (2 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt (F.energyNormSq (u n))) := by
        apply ENNReal.tsum_le_tsum
        intro n
        have hh : Real.sqrt (F.energyNormSq (u n)) / (1 / 2) =
            2 * Real.sqrt (F.energyNormSq (u n)) := by ring
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← hh]
        exact ENNReal.ofReal_le_ofReal (hvcost n)
      _ = 2 * ∑' n, ENNReal.ofReal (Real.sqrt (F.energyNormSq (u n))) :=
        ENNReal.tsum_mul_left
      _ < 2 * (δ + δ) := by
        simpa only [mul_comm] using! ENNReal.mul_lt_mul_left (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hs
      _ = ENNReal.ofReal ε := by
        dsimp only [δ]
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ ε / 4) (by positivity : 0 ≤ ε / 4),
          ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring

theorem measure_zero_of_coreCapacity_zero (F : _root_.SubdiffusiveProcess.DirichletForm m) {U A : Set X}
    (_h : Data F U) (hA : coreCapacity F U A = 0) : m A = 0 := by
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hδ : 0 < min (ε : ℝ) 1 := lt_min (by exact_mod_cast hε) zero_lt_one
  obtain ⟨u, f, O, hu, hf, hO, hAO, hcost⟩ :=
    coreCapacity_zero_cover F hA hδ
  have hbound : ∀ n, m (O n) ≤ ENNReal.ofReal (Real.sqrt (F.energyNormSq (u n))) := by
    intro n
    have hmarkov : m {x | (1 : ℝ≥0∞) ≤ ‖u n x‖ₑ} ≤ ‖u n‖ₑ ^ (2 : ℕ) := by
      simpa only [inv_one, ENNReal.one_rpow, one_pow, one_mul, ENNReal.toReal_ofNat,
        ENNReal.rpow_two, ← Lp.enorm_def] using!
        meas_ge_le_mul_pow_eLpNorm_enorm m (f := fun x => u n x) (ε := 1) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
          (by norm_num : (1 : ℝ≥0∞) ≠ 0) (fun hh => by norm_num at hh)
    have hnorm : ‖u n‖ₑ ≤ ENNReal.ofReal (Real.sqrt (F.energyNormSq (u n))) := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal
        (Real.le_sqrt_of_sq_le (F.sq_norm_le_energyNormSq (hu n).1))
    have hc1 : ENNReal.ofReal (Real.sqrt (F.energyNormSq (u n))) ≤ 1 := by
      calc
        _ ≤ ∑' k, ENNReal.ofReal (Real.sqrt (F.energyNormSq (u k))) := ENNReal.le_tsum n
        _ ≤ ENNReal.ofReal (min (ε : ℝ) 1) := hcost.le
        _ ≤ 1 := ENNReal.ofReal_le_one.mpr (min_le_right _ _)
    calc
      m (O n) ≤ m {x | (1 : ℝ≥0∞) ≤ ‖u n x‖ₑ} := by
        apply measure_mono_ae
        filter_upwards [(hf n).2.2.2.1] with x hx hxO
        rw [hx, (hO n).2.2 x hxO]
        simp only [enorm_one, le_refl]
      _ ≤ ‖u n‖ₑ ^ (2 : ℕ) := hmarkov
      _ ≤ ENNReal.ofReal (Real.sqrt (F.energyNormSq (u n))) ^ (2 : ℕ) :=
        pow_le_pow_left' hnorm 2
      _ ≤ ENNReal.ofReal (Real.sqrt (F.energyNormSq (u n))) := by
        rw [pow_two]
        exact mul_le_of_le_one_right zero_le hc1
  calc
    m A ≤ m (⋃ n, O n) := measure_mono hAO
    _ ≤ ∑' n, m (O n) := measure_iUnion_le O
    _ ≤ ∑' n, ENNReal.ofReal (Real.sqrt (F.energyNormSq (u n))) := ENNReal.tsum_le_tsum hbound
    _ ≤ ENNReal.ofReal (min (ε : ℝ) 1) := hcost.le
    _ ≤ (0 : ℝ≥0∞) + ε := by
      rw [zero_add, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (min_le_left _ _)

/-- An admissible cutoff bounds the generated outer capacity. -/
theorem coreCapacity_le_cutoff (F : _root_.SubdiffusiveProcess.DirichletForm m) {U A : Set X}
    {u : Lp ℝ 2 m} (hu : F.toClosedForm.MemCoreOn U u) {f : X → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (hae : ⇑u =ᵐ[m] f) (hf01 : ∀ x, f x ∈ Icc 0 1) (hfA : ∀ x ∈ A, f x = 1) :
    coreCapacity F U A ≤ ENNReal.ofReal (Real.sqrt (F.energyNormSq u)) := by
  refine (OuterMeasure.ofFunction_le _).trans ?_
  unfold cutoffCost
  exact iInf_le_of_le u (iInf_le_of_le hu (iInf_le_of_le f
    (iInf_le_of_le hf (iInf_le_of_le hc (iInf_le_of_le hfU
      (iInf_le_of_le hae (iInf_le_of_le hf01 (iInf_le_of_le hfA le_rfl))))))))

/-- Every capacity-null set has a Borel capacity-null superset. -/
theorem coreCapacity_zero_borel_hull [BorelSpace X] (F : _root_.SubdiffusiveProcess.DirichletForm m) {U A : Set X}
    (hA : coreCapacity F U A = 0) :
    ∃ B : Set X, MeasurableSet B ∧ A ⊆ B ∧ coreCapacity F U B = 0 := by
  classical
  choose u f O hu hf hO hAO hcost using
    fun n : ℕ => coreCapacity_zero_cover F hA
      (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  let V : ℕ → Set X := fun n => ⋃ j, O n j
  have hAV : ∀ n, A ⊆ V n := hAO
  have hV : ∀ n, coreCapacity F U (V n) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    intro n
    calc
      _ ≤ ∑' j, coreCapacity F U (O n j) := measure_iUnion_le (O n)
      _ ≤ ∑' j, ENNReal.ofReal (Real.sqrt (F.energyNormSq (u n j))) := by
        apply ENNReal.tsum_le_tsum
        intro j
        exact coreCapacity_le_cutoff F (hu n j) (hf n j).1 (hf n j).2.1
          (hf n j).2.2.1 (hf n j).2.2.2.1 (hf n j).2.2.2.2 (hO n j).2.2
      _ ≤ _ := (hcost n).le
  refine ⟨⋂ n, V n, MeasurableSet.iInter (fun n => MeasurableSet.iUnion (fun j => (hO n j).1.measurableSet)),
    subset_iInter hAV, ?_⟩
  apply le_antisymm _ zero_le
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using! ENNReal.continuous_ofReal.tendsto 0 |>.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact ge_of_tendsto hlim (Eventually.of_forall fun n =>
    ((coreCapacity F U).mono (iInter_subset V n)).trans (hV n))

/-- Finite sums of chosen core representatives, with the energy triangle inequality. -/
theorem capacity_core_sum (F : _root_.SubdiffusiveProcess.DirichletForm m) {U : Set X}
    (u : ℕ → Lp ℝ 2 m) (f : ℕ → X → ℝ)
    (hu : ∀ n, F.toClosedForm.MemCoreOn U (u n))
    (hf : ∀ n, Continuous (f n) ∧ HasCompactSupport (f n) ∧ tsupport (f n) ⊆ U ∧ ⇑(u n) =ᵐ[m] f n)
    (s : Finset ℕ) :
    F.toClosedForm.MemCoreOn U (∑ n ∈ s, u n) ∧
      Continuous (fun x => ∑ n ∈ s, f n x) ∧ HasCompactSupport (fun x => ∑ n ∈ s, f n x) ∧
      tsupport (fun x => ∑ n ∈ s, f n x) ⊆ U ∧
      ⇑(∑ n ∈ s, u n) =ᵐ[m] (fun x => ∑ n ∈ s, f n x) ∧
      Real.sqrt (F.energyNormSq (∑ n ∈ s, u n)) ≤
        ∑ n ∈ s, Real.sqrt (F.energyNormSq (u n)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨F.toClosedForm.memCoreOn_zero U, continuous_const, ?_, ?_, Lp.coeFn_zero ℝ 2 m, ?_⟩
    · change HasCompactSupport (0 : X → ℝ)
      simp only [HasCompactSupport, tsupport_zero, isCompact_empty]
    · change tsupport (0 : X → ℝ) ⊆ U
      simp only [tsupport_zero, empty_subset]
    · simp only [_root_.SubdiffusiveProcess.DirichletForm.ClosedForm.energyNormSq, F.form_zero_left F.domain.zero_mem,
        norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero, Real.sqrt_zero, le_refl]
  | @insert a s ha ih =>
    obtain ⟨hs, hcont, hc, hU, hae, hcost⟩ := ih
    simp only [Finset.sum_insert ha]
    refine ⟨(hu a).add hs, (hf a).1.add hcont, (hf a).2.1.add hc, ?_, ?_, ?_⟩
    · exact (tsupport_add (f a) (fun x => ∑ n ∈ s, f n x)).trans
        (union_subset (hf a).2.2.1 hU)
    · exact (Lp.coeFn_add (u a) (∑ n ∈ s, u n)).trans ((hf a).2.2.2.add hae)
    · exact (F.sqrt_energyNormSq_add_le (hu a).1 hs.1).trans (add_le_add le_rfl hcost)

/-- Core energy measures vanish on sets of zero cutoff capacity. -/
theorem EnergyFamily.zero_of_coreCapacity_zero_core [BorelSpace X]
    {F : _root_.SubdiffusiveProcess.DirichletForm m} {U A : Set X} (Γ : EnergyFamily F U)
    (hA : coreCapacity F U A = 0) {u : Lp ℝ 2 m}
    (hu : F.toClosedForm.MemCoreOn U u) : Γ.measure u A = 0 := by
  classical
  have : IsFiniteMeasure (Γ.measure u) := ⟨Γ.finite u hu.1⟩
  obtain ⟨uc, huc, _, _, huae⟩ := hu.2
  apply le_antisymm _ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨δ, hδ, hsmall⟩ := Γ.cutoff_integral_small hu huc huae (by exact_mod_cast hε)
  obtain ⟨v, f, O, hv, hf, hO, hAO, hcost⟩ := coreCapacity_zero_cover F hA hδ
  have hfinite : ∀ s : Finset ℕ, Γ.measure u (⋃ n ∈ s, O n) ≤ ε := by
    intro s
    obtain ⟨hs, hscont, hsc, hsU, hsae, hscost⟩ := capacity_core_sum F v f hv
      (fun n => ⟨(hf n).1, (hf n).2.1, (hf n).2.2.1, (hf n).2.2.2.1⟩) s
    obtain ⟨w, g, hw, hg, hgc, hgU, hgae, hg01, hg1, hwcost⟩ :=
      capacityCutoff_exists F hs hscont hsc hsU hsae zero_lt_one
    have hsum : (∑ n ∈ s, Real.sqrt (F.energyNormSq (v n))) < δ := by
      have he : ENNReal.ofReal (∑ n ∈ s, Real.sqrt (F.energyNormSq (v n))) ≤
          ∑' n, ENNReal.ofReal (Real.sqrt (F.energyNormSq (v n))) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.sqrt_nonneg _)]
        exact ENNReal.sum_le_tsum s
      exact (ENNReal.ofReal_lt_ofReal_iff hδ).mp (he.trans_lt hcost)
    have hws : Real.sqrt (F.energyNormSq w) < δ := by
      rw [div_one] at hwcost
      exact hwcost.trans_lt (hscost.trans_lt hsum)
    have hint := hsmall w hw g hg hgae hg01 hws
    have hgint : Integrable g (Γ.measure u) :=
      (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hg01 x).1]; exact (hg01 x).2)
    have hB : MeasurableSet (⋃ n ∈ s, O n) :=
      MeasurableSet.biUnion (s.countable_toSet) (fun n _ => (hO n).1.measurableSet)
    have hmeasure : (Γ.measure u (⋃ n ∈ s, O n)).toReal ≤ ∫ x, g x ∂Γ.measure u := by
      rw [← measureReal_def, ← integral_indicator_one hB]
      apply integral_mono_ae ((integrable_const (1 : ℝ)).indicator hB) hgint
      apply Eventually.of_forall
      intro x
      by_cases hx : x ∈ ⋃ n ∈ s, O n
      · rw [indicator_of_mem hx]
        obtain ⟨n, hn, hxO⟩ := mem_iUnion₂.mp hx
        have hsum1 : 1 ≤ ∑ k ∈ s, f k x := by
          rw [← (hO n).2.2 x hxO]
          exact Finset.single_le_sum (fun k _ => (hf k).2.2.2.2 x |>.1) hn
        have heq := hg1 x (hsum1.trans (le_abs_self _))
        simp only [heq, le_refl]
      · rw [indicator_of_notMem hx]
        exact (hg01 x).1
    apply (ENNReal.toReal_le_toReal
      (ne_top_of_le_ne_top (Γ.finite u hu.1).ne (measure_mono (subset_univ _))) ENNReal.coe_ne_top).mp
    exact hmeasure.trans hint.le
  have hmono : Monotone (fun s : Finset ℕ => ⋃ n ∈ s, O n) := by
    intro s t hst
    exact biUnion_mono hst (fun _ _ => subset_rfl)
  have hwhole : (⋃ s : Finset ℕ, ⋃ n ∈ s, O n) = ⋃ n, O n := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨s, n, _, hx⟩
      exact ⟨n, hx⟩
    · rintro ⟨n, hx⟩
      exact ⟨{n}, n, Finset.mem_singleton_self n, hx⟩
  calc
    Γ.measure u A ≤ Γ.measure u (⋃ n, O n) := measure_mono hAO
    _ = ⨆ s : Finset ℕ, Γ.measure u (⋃ n ∈ s, O n) := by
      rw [← hwhole, hmono.measure_iUnion]
    _ ≤ ε := iSup_le hfinite
    _ = 0 + ε := (zero_add _).symm

theorem EnergyFamily.zero_of_coreCapacity_zero [T2Space X] [LocallyCompactSpace X]
    [BorelSpace X] {F : _root_.SubdiffusiveProcess.DirichletForm m} {U A : Set X} (h : Data F U)
    (Γ : EnergyFamily F U) (hA : coreCapacity F U A = 0)
    {u : Lp ℝ 2 m} (hu : u ∈ F.domain) : Γ.measure u A = 0 := by
  obtain ⟨B, hB, hAB, hcapB⟩ := coreCapacity_zero_borel_hull F hA
  suffices hzero : Γ.measure u B = 0 by
    exact le_antisymm ((measure_mono hAB).trans hzero.le) zero_le
  obtain ⟨C, hC⟩ := h.core
  have hchoice : ∀ n : ℕ, ∃ v ∈ C, F.energyNormSq (u - v) < 1 / ((n : ℝ) + 1) :=
    fun n => hC.denseEnergy u hu _ (by positivity)
  choose v hv hgap using hchoice
  have hvD : ∀ n, v n ∈ F.domain := fun n => (hC.memCoreOn (v n) (hv n)).1
  have hvzero : ∀ n, Γ.measure (v n) B = 0 :=
    fun n => Γ.zero_of_coreCapacity_zero_core hcapB (hC.memCoreOn (v n) (hv n))
  have hlim : Tendsto (fun n => F.energyNormSq (u - v n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => F.energyNormSq_nonneg (F.domain.sub_mem hu (hvD n)))
      (fun n => (hgap n).le) (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlimrev : Tendsto (fun n => F.energyNormSq (v n - u)) atTop (𝓝 0) := by
    simpa only [F.energyNormSq_sub_comm (hvD _) hu] using! hlim
  have hform : Tendsto (fun n => F.form (u - v n) (u - v n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => F.form_nonneg _ (F.domain.sub_mem hu (hvD n)))
      (fun n => F.form_le_energyNormSq) hlim
  have hself := F.tendsto_form_self_of_tendsto_energyNormSq hvD hu hlimrev
  have hrhs : Tendsto (fun n => Real.sqrt (F.form (u - v n) (u - v n)) *
      (Real.sqrt (F.form u u) + Real.sqrt (F.form (v n) (v n)))) atTop (𝓝 0) := by
    have h1 := (Real.continuous_sqrt.tendsto 0).comp hform
    have h2 := (Real.continuous_sqrt.tendsto (F.form u u)).comp hself
    simpa only [Function.comp_def, Real.sqrt_zero, zero_mul] using! h1.mul (h2.const_add (Real.sqrt (F.form u u)))
  have hbound : ∀ n, |(Γ.measure u B).toReal| ≤ Real.sqrt (F.form (u - v n) (u - v n)) *
      (Real.sqrt (F.form u u) + Real.sqrt (F.form (v n) (v n))) := by
    intro n
    simpa only [hvzero n, ENNReal.toReal_zero, sub_zero] using! Γ.difference_bound hu (hvD n) hB
  have hle : |(Γ.measure u B).toReal| ≤ 0 := ge_of_tendsto hrhs (Eventually.of_forall hbound)
  have heq : (Γ.measure u B).toReal = 0 := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  exact (ENNReal.toReal_eq_zero_iff _).mp heq |>.resolve_right
    (ne_top_of_le_ne_top (Γ.finite u hu).ne (measure_mono (subset_univ B)))

end SubdiffusiveProcess.DirichletForm.FOTConstruction
