module

public import SubdiffusiveProcess.Paper.lem_band
public import SubdiffusiveProcess.Paper.lem_witness_common_ae_limit
public import SubdiffusiveProcess.Paper.lem_witness_prefix_band_measurability
public import Mathlib

@[expose] public section

open MeasureTheory Filter Set Topology SubdiffusiveProcess
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

def aux_increment (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => u 0
  | k + 1 => u (k + 1) - u k

theorem aux_increment_witness
    (u : ℕ → ℝ) (t lam r : ℝ)
    (hlam : 0 < lam) (hr : 0 ≤ r)
    (hlim : Tendsto u atTop (𝓝 t)) (hbad : lam ≤ t) :
    ∃ k : ℕ, lam * (1 - r) / 2 * r ^ k ≤ |aux_increment u k| := by
  by_contra hnone
  have hsmall : ∀ k : ℕ,
      |aux_increment u k| < lam * (1 - r) / 2 * r ^ k := by
    intro k
    exact lt_of_not_ge (fun hk => hnone ⟨k, hk⟩)
  have hbound : ∀ k : ℕ, u k ≤ lam / 2 * (1 - r ^ (k + 1)) := by
    intro k
    induction k with
    | zero =>
        have h0 : u 0 ≤ lam * (1 - r) / 2 := by
          calc
            u 0 ≤ |u 0| := le_abs_self _
            _ ≤ lam * (1 - r) / 2 := by
              simpa only [aux_increment, pow_zero, mul_one] using (hsmall 0).le
        calc
          u 0 ≤ lam * (1 - r) / 2 := h0
          _ = lam / 2 * (1 - r ^ (0 + 1)) := by
            simp only [zero_add, pow_one]
            ring
    | succ k ih =>
        have hstep : u (k + 1) - u k ≤
            lam * (1 - r) / 2 * r ^ (k + 1) := by
          calc
            u (k + 1) - u k ≤ |u (k + 1) - u k| := le_abs_self _
            _ ≤ lam * (1 - r) / 2 * r ^ (k + 1) := (hsmall (k + 1)).le
        calc
          u (k + 1) = u k + (u (k + 1) - u k) := by ring
          _ ≤ lam / 2 * (1 - r ^ (k + 1)) +
              lam * (1 - r) / 2 * r ^ (k + 1) := add_le_add ih hstep
          _ = lam / 2 * (1 - r ^ ((k + 1) + 1)) := by
            rw [pow_succ r (k + 1)]
            ring
  have hhalf : ∀ k : ℕ, u k ≤ lam / 2 := by
    intro k
    have hnonneg : 0 ≤ lam / 2 * r ^ (k + 1) :=
      mul_nonneg (by positivity) (pow_nonneg hr _)
    have hk := hbound k
    nlinarith
  have ht : t ≤ lam / 2 := le_of_tendsto hlim (Eventually.of_forall hhalf)
  linarith

theorem aux_lp_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (p t s : ℝ)
    (hp : 0 < p) (ht : 0 < t) (hs : 0 ≤ s)
    (hf : AEStronglyMeasurable f P)
    (hnorm : eLpNorm f (ENNReal.ofReal p) P ≤ ENNReal.ofReal s) :
    P {om | t ≤ |f om|} ≤ ENNReal.ofReal ((s / t) ^ p) := by
  have hp0 : ENNReal.ofReal p ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have ht0 : ENNReal.ofReal t ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr ht)
  have hmarkov := meas_ge_le_mul_pow_eLpNorm_enorm (f := f)
    P hp0 ENNReal.ofReal_ne_top ht0 (by simp)
  have hcast : (ENNReal.ofReal t)⁻¹ * ENNReal.ofReal s =
      ENNReal.ofReal (s / t) := by
    rw [ENNReal.ofReal_div_of_pos ht, div_eq_mul_inv]
    exact mul_comm _ _
  calc
    P {om | t ≤ |f om|} ≤ P {om | ENNReal.ofReal t ≤ ‖f om‖ₑ} := by
      apply measure_mono
      intro om hom
      change ENNReal.ofReal t ≤ ‖f om‖ₑ
      rw [← ofReal_norm_eq_enorm]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.norm_eq_abs]
      exact hom
    _ ≤ (ENNReal.ofReal t)⁻¹ ^ (ENNReal.ofReal p).toReal *
        eLpNorm f (ENNReal.ofReal p) P ^ (ENNReal.ofReal p).toReal := hmarkov
    _ = (ENNReal.ofReal t)⁻¹ ^ p * eLpNorm f (ENNReal.ofReal p) P ^ p := by
      rw [ENNReal.toReal_ofReal hp.le]
    _ ≤ (ENNReal.ofReal t)⁻¹ ^ p * (ENNReal.ofReal s) ^ p :=
      mul_le_mul_right (ENNReal.rpow_le_rpow hnorm hp.le) _
    _ = ((ENNReal.ofReal t)⁻¹ * ENNReal.ofReal s) ^ p :=
      (ENNReal.mul_rpow_of_nonneg _ _ hp.le).symm
    _ = (ENNReal.ofReal (s / t)) ^ p := by rw [hcast]
    _ = ENNReal.ofReal ((s / t) ^ p) :=
      ENNReal.ofReal_rpow_of_nonneg (div_nonneg hs ht.le) hp.le

theorem aux_lp_sub_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f g : Ω → ℝ) (p t s : ℝ)
    (hp : 0 < p) (ht : 0 < t) (hs : 0 ≤ s)
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P)
    (hnf : eLpNorm f (ENNReal.ofReal p) P ≤ ENNReal.ofReal s)
    (hng : eLpNorm g (ENNReal.ofReal p) P ≤ ENNReal.ofReal s) :
    P {om | t ≤ |f om - g om|} ≤
      ENNReal.ofReal (2 * ((2 * s / t) ^ p)) := by
  have ht2 : 0 < t / 2 := by positivity
  have hbf := aux_lp_tail P f p (t / 2) s hp ht2 hs hf hnf
  have hbg := aux_lp_tail P g p (t / 2) s hp ht2 hs hg hng
  have hsub : {om | t ≤ |f om - g om|} ⊆
      {om | t / 2 ≤ |f om|} ∪ {om | t / 2 ≤ |g om|} := by
    intro om hom
    by_cases hleft : t / 2 ≤ |f om|
    · exact Or.inl hleft
    · apply Or.inr
      by_contra hright
      have hfsmall := lt_of_not_ge hleft
      have hgsmall : |g om| < t / 2 := lt_of_not_ge (fun h => hright h)
      have htriangle : |f om - g om| ≤ |f om| + |g om| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le (f om) (g om)
      have hom' : t ≤ |f om - g om| := hom
      linarith
  have hpow : 0 ≤ (s / (t / 2)) ^ p :=
    Real.rpow_nonneg (div_nonneg hs ht2.le) p
  have hdiv : s / (t / 2) = 2 * s / t := by
    field_simp [ne_of_gt ht]
    <;> ring
  calc
    P {om | t ≤ |f om - g om|} ≤
        P ({om | t / 2 ≤ |f om|} ∪ {om | t / 2 ≤ |g om|}) := measure_mono hsub
    _ ≤ P {om | t / 2 ≤ |f om|} + P {om | t / 2 ≤ |g om|} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal ((s / (t / 2)) ^ p) +
        ENNReal.ofReal ((s / (t / 2)) ^ p) := add_le_add hbf hbg
    _ = ENNReal.ofReal (2 * ((2 * s / t) ^ p)) := by
      rw [← ENNReal.ofReal_add hpow hpow]
      congr 1
      rw [hdiv]
      ring

theorem aux_increment_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (p M q : ℝ)
    (hp : 0 < p) (hM : 0 ≤ M) (hq : 0 < q) (hq1 : q ≤ 1)
    (T : Ω → ℝ) (Tb : ℕ → Ω → ℝ)
    (hT : AEStronglyMeasurable T P)
    (hTb : ∀ k, AEStronglyMeasurable (Tb k) P)
    (hnT : eLpNorm T (ENNReal.ofReal p) P ≤ ENNReal.ofReal M)
    (herr : ∀ k, eLpNorm (fun om => T om - Tb k om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (M * q ^ k))
    (k : ℕ) (t : ℝ) (ht : 0 < t) :
    P {om | t ≤ |aux_increment (fun H => Tb H om) k|} ≤
      ENNReal.ofReal (2 * ((2 * (M / q * q ^ k) / t) ^ p)) := by
  cases k with
  | zero =>
      have hMle : M ≤ M / q * q ^ 0 := by
        simp only [pow_zero, mul_one]
        apply (le_div_iff₀ hq).2
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hq1 hM
      have hn0 : eLpNorm (fun om => T om - Tb 0 om) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal M := by
        simpa only [pow_zero, mul_one] using herr 0
      have htail := aux_lp_sub_tail P T (fun om => T om - Tb 0 om)
        p t (M / q * q ^ 0) hp ht (by positivity)
        hT (hT.sub (hTb 0))
        (hnT.trans (ENNReal.ofReal_le_ofReal hMle))
        (hn0.trans (ENNReal.ofReal_le_ofReal hMle))
      have hid : ∀ om, T om - (T om - Tb 0 om) = Tb 0 om := by
        intro om
        ring
      simpa only [aux_increment, hid] using htail
  | succ k =>
      have hs : M / q * q ^ (k + 1) = M * q ^ k := by
        rw [pow_succ]
        field_simp [ne_of_gt hq]
        <;> ring
      have hdec : M * q ^ (k + 1) ≤ M * q ^ k := by
        calc
          M * q ^ (k + 1) = (M * q ^ k) * q := by rw [pow_succ]; ring
          _ ≤ (M * q ^ k) * 1 :=
            mul_le_mul_of_nonneg_left hq1 (mul_nonneg hM (pow_nonneg hq.le _))
          _ = M * q ^ k := mul_one _
      have hnprev : eLpNorm (fun om => T om - Tb k om) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (M / q * q ^ (k + 1)) := by
        rw [hs]
        exact herr k
      have hnnext : eLpNorm (fun om => T om - Tb (k + 1) om)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal (M / q * q ^ (k + 1)) := by
        rw [hs]
        exact (herr (k + 1)).trans (ENNReal.ofReal_le_ofReal hdec)
      have htail := aux_lp_sub_tail P
        (fun om => T om - Tb k om) (fun om => T om - Tb (k + 1) om)
        p t (M / q * q ^ (k + 1)) hp ht (by positivity)
        (hT.sub (hTb k)) (hT.sub (hTb (k + 1))) hnprev hnnext
      have hid : ∀ om, (T om - Tb k om) - (T om - Tb (k + 1) om) =
          Tb (k + 1) om - Tb k om := by
        intro om
        ring
      simpa only [aux_increment, hid] using htail

theorem aux_fin_union_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (J : ℕ) (E : Fin J → Set Ω)
    (b : ℝ) (hb : 0 ≤ b)
    (hE : ∀ i, P (E i) ≤ ENNReal.ofReal b) :
    P (⋃ i : Fin J, E i) ≤ ENNReal.ofReal ((J : ℝ) * b) := by
  classical
  calc
    P (⋃ i : Fin J, E i) ≤ ∑' i : Fin J, P (E i) := measure_iUnion_le E
    _ = ∑ i : Fin J, P (E i) := tsum_fintype _
    _ ≤ ∑ i : Fin J, ENNReal.ofReal b := Finset.sum_le_sum (fun i _ => hE i)
    _ = ENNReal.ofReal ((J : ℝ) * b) := by
      simp [ENNReal.ofReal_mul, hb, nsmul_eq_mul]

theorem aux_exp_nat_pow (x : ℝ) (k : ℕ) :
    (Real.exp x) ^ k = Real.exp (x * (k : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      simp only [Nat.cast_succ]
      ring

theorem aux_geometric_rate
    (a b p : ℝ) (ha : 0 < a) (hp : 0 < p)
    (hgap : b < a * p * Real.log 3) :
    ∃ q r : ℝ, q = (3 : ℝ) ^ (-a) ∧
      0 < q ∧ q < 1 ∧ 0 < r ∧ r < 1 ∧
      (q / r) ^ p = Real.exp (-b) := by
  let A : ℝ := a * Real.log 3
  let q : ℝ := Real.exp (-A)
  let r : ℝ := Real.exp (b / p - A)
  have hA : 0 < A := mul_pos ha (Real.log_pos (by norm_num))
  have hgap' : b / p < A := by
    apply (div_lt_iff₀ hp).2
    calc
      b < a * p * Real.log 3 := hgap
      _ = A * p := by dsimp [A]; ring
  have hqeq : q = (3 : ℝ) ^ (-a) := by
    dsimp [q, A]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hqr : q / r = Real.exp (-(b / p)) := by
    dsimp [q, r]
    rw [← Real.exp_sub]
    congr 1
    ring
  have hrate : (q / r) ^ p = Real.exp (-b) := by
    rw [hqr, ← Real.exp_mul]
    congr 1
    field_simp [ne_of_gt hp]
    <;> ring
  refine ⟨q, r, hqeq, Real.exp_pos _, ?_, Real.exp_pos _, ?_, hrate⟩
  · exact Real.exp_lt_one_iff.mpr (by linarith)
  · exact Real.exp_lt_one_iff.mpr (sub_neg.mpr hgap')

theorem aux_geometric_budget
    (J : ℕ) (p b Cp q r K : ℝ)
    (hp : 0 < p) (hCp : 0 < Cp) (hq : 0 < q)
    (hr : 0 < r) (hK : 0 < K)
    (hrate : (q / r) ^ p = Real.exp (-b)) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 → ∀ k : ℕ,
        (J : ℝ) * (2 * ((2 * (Cp * eta / q * q ^ k) / (K * r ^ k)) ^ p)) ≤
          Real.exp (-(b * ((k : ℝ) + 1))) := by
  let B : ℝ := Real.exp (-b) / (2 * ((J : ℝ) + 1))
  let c : ℝ := B ^ p⁻¹
  let eta0 : ℝ := c * (q * K) / (2 * Cp)
  have hJ : 0 < (J : ℝ) + 1 := by positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hc : 0 < c := Real.rpow_pos_of_pos hB _
  have hcp : c ^ p = B := Real.rpow_inv_rpow hB.le (ne_of_gt hp)
  have heta0 : 0 < eta0 := by dsimp [eta0]; positivity
  refine ⟨eta0, heta0, ?_⟩
  intro eta heta hetale k
  let x : ℝ := 2 * Cp * eta / (q * K)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxc : x ≤ c := by
    apply (div_le_iff₀ (mul_pos hq hK)).2
    calc
      2 * Cp * eta ≤ 2 * Cp * eta0 :=
        mul_le_mul_of_nonneg_left hetale (by positivity)
      _ = c * (q * K) := by
        dsimp [eta0]
        field_simp [ne_of_gt hCp]
        <;> ring
  have hratio : 2 * (Cp * eta / q * q ^ k) / (K * r ^ k) =
      x * (q / r) ^ k := by
    dsimp [x]
    rw [div_pow]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hqp : 0 ≤ q / r := (div_pos hq hr).le
  have hepow : 0 ≤ (Real.exp (-b)) ^ k := pow_nonneg (Real.exp_pos _).le _
  have hpow : (x * (q / r) ^ k) ^ p ≤ c ^ p * (Real.exp (-b)) ^ k := by
    calc
      (x * (q / r) ^ k) ^ p = x ^ p * ((q / r) ^ k) ^ p :=
        Real.mul_rpow hx (pow_nonneg hqp _)
      _ = x ^ p * ((q / r) ^ p) ^ k := by
        rw [Real.rpow_pow_comm hqp p k]
      _ = x ^ p * (Real.exp (-b)) ^ k := by rw [hrate]
      _ ≤ c ^ p * (Real.exp (-b)) ^ k :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx hxc hp.le) hepow
  calc
    (J : ℝ) * (2 * ((2 * (Cp * eta / q * q ^ k) / (K * r ^ k)) ^ p)) =
        (2 * (J : ℝ)) * (x * (q / r) ^ k) ^ p := by rw [hratio]; ring
    _ ≤ (2 * (J : ℝ)) * (c ^ p * (Real.exp (-b)) ^ k) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ (2 * ((J : ℝ) + 1)) * (c ^ p * (Real.exp (-b)) ^ k) := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact mul_nonneg (Real.rpow_nonneg hc.le _) hepow
    _ = Real.exp (-b) * (Real.exp (-b)) ^ k := by
      rw [hcp]
      dsimp [B]
      field_simp [ne_of_gt hJ]
      <;> ring
    _ = Real.exp (-(b * ((k : ℝ) + 1))) := by
      rw [aux_exp_nat_pow, ← Real.exp_add]
      congr 1
      ring

theorem aux_reindex_cover
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℕ+ → MeasurableSpace Ω)
    (bound : ℕ+ → ℝ≥0∞) (S : Set Ω)
    (w : ℕ → ℕ+) (hw : Function.Injective w)
    (E : ℕ → Set Ω)
    (hEmeas : ∀ k, MeasurableSet[B (w k)] (E k))
    (hEprob : ∀ k, P (E k) ≤ bound (w k))
    (hcover : S ⊆ ⋃ k : ℕ, E k) :
    ∃ W : ℕ+ → Set Ω,
      (∀ h, MeasurableSet[B h] (W h)) ∧
      (∀ h, P (W h) ≤ bound h) ∧ S ⊆ ⋃ h : ℕ+, W h := by
  classical
  let W : ℕ+ → Set Ω := fun h => ⋃ k : ℕ, ⋃ (_ : w k = h), E k
  have hW : ∀ k, W (w k) = E k := by
    intro k
    ext om
    simp only [W, Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj, hom⟩
      have hjk : j = k := hw hj
      subst j
      exact hom
    · intro hom
      exact ⟨k, rfl, hom⟩
  have hWempty : ∀ h, (¬ ∃ k, w k = h) → W h = ∅ := by
    intro h hn
    apply Set.Subset.antisymm
    · intro om hom
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hom
      obtain ⟨heq, hmem⟩ := Set.mem_iUnion.mp hk
      exact (hn ⟨k, heq⟩).elim
    · exact Set.empty_subset _
  refine ⟨W, ?_, ?_, ?_⟩
  · intro h
    by_cases hex : ∃ k, w k = h
    · obtain ⟨k, rfl⟩ := hex
      rw [hW]
      exact hEmeas k
    · rw [hWempty h hex]
      letI : MeasurableSpace Ω := B h
      exact MeasurableSet.empty
  · intro h
    by_cases hex : ∃ k, w k = h
    · obtain ⟨k, rfl⟩ := hex
      rw [hW]
      exact hEprob k
    · simpa only [hWempty h hex, measure_empty] using (zero_le)
  · intro om hom
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hcover hom)
    apply Set.mem_iUnion.mpr
    refine ⟨w k, ?_⟩
    rwa [hW]



theorem lem_witness_test_dyadic_cover
    (d : ℕ) (hd : 1 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
    (Bsig : ℤ → ℤ → MeasurableSpace (BilateralField d))
    (Cband k0 : ℕ) (hCband : 0 < Cband) (hk0 : 1 ≤ k0) (J : ℕ)
    (beta a lam Cp : ℝ)
    (hbeta : 0 < beta) (ha : 0 < a) (hlam : 0 < lam) (hCp : 0 < Cp)
    (p : ℝ) (hp : 2 ≤ p)
    (hBsig_interval_mono : ∀ l₁ r₁ l₂ r₂ : ℤ,
      l₂ ≤ l₁ → r₁ ≤ r₂ → Bsig l₁ r₁ ≤ Bsig l₂ r₂)
    (hdecay_strict : beta * (Cband : ℝ) < a * p * Real.log 3) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
        ∀ (T : ℤ → Fin J → BilateralField d → ℝ),
        ∀ (Tb : ℤ → Fin J → ℕ → BilateralField d → ℝ),
        (∀ n i, MemLp (T n i) (ENNReal.ofReal p) P) →
        (∀ n i, eLpNorm (T n i) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (Cp * eta)) →
        (∀ n i H,
          StronglyMeasurable[
            Bsig (n - ((Cband * (H + 1) : ℕ) : ℤ))
              (n + ((Cband * (H + 1) : ℕ) : ℤ))]
            (Tb n i H)) →
        (∀ n i H, AEStronglyMeasurable (Tb n i H) P) →
        (∀ n i H,
          eLpNorm (fun om => T n i om - Tb n i H om)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal
              (Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
        (Sigma : Set (BilateralField d)) →
        MeasurableSet Sigma → P Sigma = 1 →
        (∀ om, om ∈ Sigma → ∀ n i,
          Tendsto (fun H => Tb n i H om) atTop (𝓝 (T n i om))) →
        ∀ n : ℤ, ∃ W : ℕ+ → Set (BilateralField d),
          (∀ h : ℕ+,
            MeasurableSet[
              Bsig (n - (h : ℤ)) (n + 2 * (h : ℤ))] (W h)) ∧
          (∀ h : ℕ+,
            P (W h) ≤
              ENNReal.ofReal (Real.exp (-(beta * (h : ℝ))))) ∧
          Sigma ∩ {om | ∃ i : Fin J, lam ≤ T n i om} ⊆
            ⋃ h : ℕ+, W h := by
  classical
  have hp0 : 0 < p := by linarith
  obtain ⟨q, r, hqeq, hq, hq1, hr, hr1, hrate⟩ :=
    aux_geometric_rate a (beta * (Cband : ℝ)) p ha hp0 hdecay_strict
  let K : ℝ := lam * (1 - r) / 2
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos (mul_pos hlam (sub_pos.mpr hr1)) (by norm_num)
  obtain ⟨eta0, heta0, hbudget⟩ :=
    aux_geometric_budget J p (beta * (Cband : ℝ)) Cp q r K
      hp0 hCp hq hr hK hrate
  refine ⟨eta0, heta0, ?_⟩
  intro eta heta hetale T Tb hTmem hTnorm hTbband hTbae happrox
    Sigma hSigma hSigmaP hlimit n
  let w : ℕ → ℕ+ := fun k =>
    ⟨Cband * (k + 1), Nat.mul_pos hCband (Nat.succ_pos k)⟩
  have hw : Function.Injective w := by
    intro j k hjk
    have heq : Cband * (j + 1) = Cband * (k + 1) :=
      congrArg (fun h : ℕ+ => (h : ℕ)) hjk
    have hsucc : j + 1 = k + 1 := mul_left_cancel₀ (ne_of_gt hCband) heq
    omega
  have hwr : ∀ k : ℕ, (w k : ℝ) = (Cband : ℝ) * ((k : ℝ) + 1) := by
    intro k
    change ((Cband * (k + 1) : ℕ) : ℝ) = (Cband : ℝ) * ((k : ℝ) + 1)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hgeom : ∀ H : ℕ, (3 : ℝ) ^ (-(a * (H : ℝ))) = q ^ H := by
    intro H
    calc
      (3 : ℝ) ^ (-(a * (H : ℝ))) = (3 : ℝ) ^ ((-a) * (H : ℝ)) := by
        congr 1
        ring
      _ = ((3 : ℝ) ^ (-a)) ^ H :=
        Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3) (-a) H
      _ = q ^ H := by rw [hqeq]
  have herror : ∀ i H,
      eLpNorm (fun om => T n i om - Tb n i H om) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Cp * eta * q ^ H) := by
    intro i H
    simpa only [hgeom H] using happrox n i H
  have hTbwindow : ∀ (i : Fin J) (k j : ℕ), j ≤ k →
      StronglyMeasurable[Bsig (n - (w k : ℤ)) (n + 2 * (w k : ℤ))]
        (Tb n i j) := by
    intro i k j hj
    have hrad : ((Cband * (j + 1) : ℕ) : ℤ) ≤
        ((Cband * (k + 1) : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_le_mul_left Cband (Nat.add_le_add_right hj 1)
    have hrad0 : (0 : ℤ) ≤ ((Cband * (k + 1) : ℕ) : ℤ) := by positivity
    apply (hTbband n i j).mono
    apply hBsig_interval_mono
    · change n - ((Cband * (k + 1) : ℕ) : ℤ) ≤
        n - ((Cband * (j + 1) : ℕ) : ℤ)
      omega
    · change n + ((Cband * (j + 1) : ℕ) : ℤ) ≤
        n + 2 * ((Cband * (k + 1) : ℕ) : ℤ)
      omega
  have hYmeas : ∀ (i : Fin J) (k : ℕ),
      StronglyMeasurable[Bsig (n - (w k : ℤ)) (n + 2 * (w k : ℤ))]
        (fun om => aux_increment (fun H => Tb n i H om) k) := by
    intro i k
    cases k with
    | zero => exact hTbwindow i 0 0 le_rfl
    | succ k =>
        exact (hTbwindow i (k + 1) (k + 1) le_rfl).sub
          (hTbwindow i (k + 1) k (Nat.le_succ k))
  let E : ℕ → Set (BilateralField d) := fun k =>
    ⋃ i : Fin J, {om | K * r ^ k ≤ |aux_increment (fun H => Tb n i H om) k|}
  have hEmeas : ∀ k : ℕ,
      MeasurableSet[Bsig (n - (w k : ℤ)) (n + 2 * (w k : ℤ))] (E k) := by
    intro k
    apply MeasurableSet.iUnion
    intro i
    letI : MeasurableSpace (BilateralField d) := Bsig (n - (w k : ℤ)) (n + 2 * (w k : ℤ))
    exact measurableSet_le measurable_const ((hYmeas i k).measurable.abs)
  have hEprob : ∀ k : ℕ, P (E k) ≤
      ENNReal.ofReal (Real.exp (-(beta * (w k : ℝ)))) := by
    intro k
    have hthreshold : 0 < K * r ^ k := mul_pos hK (pow_pos hr _)
    have htail : ∀ i : Fin J,
        P {om | K * r ^ k ≤ |aux_increment (fun H => Tb n i H om) k|} ≤
          ENNReal.ofReal
            (2 * ((2 * (Cp * eta / q * q ^ k) / (K * r ^ k)) ^ p)) := by
      intro i
      exact aux_increment_tail P p (Cp * eta) q hp0 (mul_pos hCp heta).le hq hq1.le
        (T n i) (Tb n i) (hTmem n i).aestronglyMeasurable (hTbae n i)
        (hTnorm n i) (herror i) k (K * r ^ k) hthreshold
    calc
      P (E k) ≤ ENNReal.ofReal
          ((J : ℝ) * (2 * ((2 * (Cp * eta / q * q ^ k) / (K * r ^ k)) ^ p))) :=
        aux_fin_union_bound P J
          (fun i => {om | K * r ^ k ≤ |aux_increment (fun H => Tb n i H om) k|})
          (2 * ((2 * (Cp * eta / q * q ^ k) / (K * r ^ k)) ^ p))
          (by positivity) htail
      _ ≤ ENNReal.ofReal (Real.exp (-((beta * (Cband : ℝ)) * ((k : ℝ) + 1)))) :=
        ENNReal.ofReal_le_ofReal (hbudget eta heta hetale k)
      _ = ENNReal.ofReal (Real.exp (-(beta * (w k : ℝ)))) := by
        rw [hwr]
        congr 2
        ring
  have hcover : Sigma ∩ {om | ∃ i : Fin J, lam ≤ T n i om} ⊆ ⋃ k : ℕ, E k := by
    intro om hom
    obtain ⟨i, hi⟩ := hom.2
    obtain ⟨k, hk⟩ := aux_increment_witness
      (fun H => Tb n i H om) (T n i om) lam r hlam hr.le
      (hlimit om hom.1 n i) hi
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    exact hk
  exact aux_reindex_cover P
    (fun h => Bsig (n - (h : ℤ)) (n + 2 * (h : ℤ)))
    (fun h => ENNReal.ofReal (Real.exp (-(beta * (h : ℝ)))))
    (Sigma ∩ {om | ∃ i : Fin J, lam ≤ T n i om})
    w hw E hEmeas hEprob hcover

end Paper
