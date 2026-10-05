module

public import SubdiffusiveProcess.Paper.in_prefix
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
namespace SubdiffusiveProcess.Paper

def aux_prefix_increment (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => u 0
  | k + 1 => u (k + 1) - u k

theorem aux_prefix_increment_witness_base
    (u : ℕ → ℝ) (t lam r : ℝ)
    (hlam : 0 < lam) (hr : 0 ≤ r)
    (hlim : Tendsto u atTop (𝓝 t)) (hbad : lam ≤ t) :
    ∃ k : ℕ, lam * (1 - r) / 2 * r ^ k ≤ |aux_prefix_increment u k| := by
  by_contra hnone
  have hsmall : ∀ k : ℕ,
      |aux_prefix_increment u k| < lam * (1 - r) / 2 * r ^ k := by
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
              simpa only [aux_prefix_increment, pow_zero, mul_one] using (hsmall 0).le
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

theorem aux_prefix_lp_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (p t s : ℝ)
    (hp : 0 < p) (ht : 0 < t) (hs : 0 ≤ s)
    (_hf : AEStronglyMeasurable f P)
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
      rw [← ofReal_norm]
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

theorem aux_prefix_lp_sub_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f g : Ω → ℝ) (p t s : ℝ)
    (hp : 0 < p) (ht : 0 < t) (hs : 0 ≤ s)
    (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P)
    (hnf : eLpNorm f (ENNReal.ofReal p) P ≤ ENNReal.ofReal s)
    (hng : eLpNorm g (ENNReal.ofReal p) P ≤ ENNReal.ofReal s) :
    P {om | t ≤ |f om - g om|} ≤
      ENNReal.ofReal (2 * ((2 * s / t) ^ p)) := by
  have ht2 : 0 < t / 2 := by positivity
  have hbf := aux_prefix_lp_tail P f p (t / 2) s hp ht2 hs hf hnf
  have hbg := aux_prefix_lp_tail P g p (t / 2) s hp ht2 hs hg hng
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

theorem aux_prefix_exp_nat_pow (x : ℝ) (k : ℕ) :
    (Real.exp x) ^ k = Real.exp (x * (k : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      simp only [Nat.cast_succ]
      ring

theorem aux_prefix_geometric_rate
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

  refine ⟨q, r, hqeq, Real.exp_pos _, ?_, Real.exp_pos _, ?_, hrate⟩
  · exact Real.exp_lt_one_iff.mpr (by linarith)
  · exact Real.exp_lt_one_iff.mpr (sub_neg.mpr hgap')

theorem aux_prefix_reindex_cover
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
      let : MeasurableSpace Ω := B h
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

theorem aux_prefix_finite_union
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (P : Measure Ω) (E : J → Set Ω) (b : ℝ) (_hb : 0 ≤ b)
    (hE : ∀ i, P (E i) ≤ ENNReal.ofReal b) :
    P (⋃ i, E i) ≤ ENNReal.ofReal ((Fintype.card J : ℝ) * b) := by
  classical
  calc
    P (⋃ i, E i) ≤ ∑' i, P (E i) := measure_iUnion_le E
    _ = ∑ i, P (E i) := tsum_fintype _
    _ ≤ ∑ _i : J, ENNReal.ofReal b :=
      Finset.sum_le_sum (fun i _ => hE i)
    _ = ENNReal.ofReal ((Fintype.card J : ℝ) * b) := by
      simp [ENNReal.ofReal_mul, nsmul_eq_mul]

theorem aux_prefix_ae_sum
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : ℕ → Ω → ℝ)
    (hf : ∀ j, AEStronglyMeasurable (f j) P) (D : ℕ) :
    AEStronglyMeasurable (fun om => ∑ j ∈ Finset.range D, f j om) P := by
  induction D with
  | zero =>
      simpa only [Finset.range_zero, Finset.sum_empty] using
        (aestronglyMeasurable_const :
          AEStronglyMeasurable (fun _ : Ω => (0 : ℝ)) P)
  | succ D ih =>
      simp_rw [Finset.sum_range_succ]
      exact ih.add (hf D)

theorem aux_prefix_limit_sum
    (f : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hf : ∀ j, Tendsto (f j) atTop (𝓝 (g j))) (D : ℕ) :
    Tendsto (fun H => ∑ j ∈ Finset.range D, f j H)
      atTop (𝓝 (∑ j ∈ Finset.range D, g j)) := by
  induction D with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact tendsto_const_nhds
  | succ D ih =>
      simp_rw [Finset.sum_range_succ]
      exact ih.add (hf D)

theorem aux_prefix_norm_sum
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f g : ℕ → Ω → ℝ) (D : ℕ) (p s : ℝ)
    (hp : 1 ≤ p) (_hs : 0 ≤ s)
    (_hf : ∀ j, AEStronglyMeasurable (f j) P)
    (_hg : ∀ j, AEStronglyMeasurable (g j) P)
    (hn : ∀ j, eLpNorm (fun om => f j om - g j om)
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal s) :
    eLpNorm (fun om =>
        (∑ j ∈ Finset.range D, f j om) - ∑ j ∈ Finset.range D, g j om)
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal ((D : ℝ) * s) := by
  classical
  have hp' : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  calc
    eLpNorm (fun om =>
        (∑ j ∈ Finset.range D, f j om) - ∑ j ∈ Finset.range D, g j om)
        (ENNReal.ofReal p) P =
        eLpNorm (∑ j ∈ Finset.range D, fun om => f j om - g j om)
          (ENNReal.ofReal p) P := by
      congr 1
      funext om
      simp only [Finset.sum_apply, Finset.sum_sub_distrib]
    _ ≤ ∑ j ∈ Finset.range D,
        eLpNorm (fun om => f j om - g j om) (ENNReal.ofReal p) P :=
      eLpNorm_sum_le hp'
    _ ≤ ∑ _j ∈ Finset.range D, ENNReal.ofReal s :=
      Finset.sum_le_sum (fun j _ => hn j)
    _ = ENNReal.ofReal ((D : ℝ) * s) := by
      simp [ENNReal.ofReal_mul, nsmul_eq_mul]

theorem aux_prefix_increment_witness
    (u : ℕ → ℝ) (t lam r : ℝ) (D : ℕ)
    (hlam : 0 < lam) (hr : 0 < r) (hr1 : r < 1)
    (hlim : Tendsto u atTop (𝓝 t)) (hbad : lam ≤ t) :
    lam / 2 ≤ u D ∨
      ∃ H : ℕ, D < H ∧
        lam * (1 - r) / 4 * r ^ H ≤ |u H - u (H - 1)| := by
  by_cases hbase : lam / 2 ≤ u D
  · exact Or.inl hbase
  apply Or.inr
  let z : ℕ → ℝ := fun H => if H ≤ D then 0 else u H - u D
  have hzlim : Tendsto z atTop (𝓝 (t - u D)) := by
    have hlim' : Tendsto (fun H => u H - u D) atTop (𝓝 (t - u D)) :=
      hlim.sub tendsto_const_nhds
    apply hlim'.congr'
    filter_upwards [eventually_gt_atTop D] with H hH
    simp only [z, ite_eq_right (not_le_of_gt hH)]
  have hbad' : lam / 2 ≤ t - u D := by
    have hu := lt_of_not_ge hbase
    linarith
  obtain ⟨H, hH⟩ := aux_prefix_increment_witness_base z (t - u D) (lam / 2) r
    (by positivity) hr.le hzlim hbad'
  have hcoef : (lam / 2) * (1 - r) / 2 = lam * (1 - r) / 4 := by ring
  rw [hcoef] at hH
  have hpositive : 0 < lam * (1 - r) / 4 * r ^ H := by
    exact mul_pos
      (div_pos (mul_pos hlam (sub_pos.mpr hr1)) (by norm_num))
      (pow_pos hr H)
  cases H with
  | zero =>
      have hz : aux_prefix_increment z 0 = 0 := by simp [aux_prefix_increment, z]
      rw [hz, abs_zero] at hH
      exact (not_le_of_gt hpositive hH).elim
  | succ k =>
      have hDk : D < k + 1 := by
        by_contra hn
        have hk1 : k + 1 ≤ D := le_of_not_gt hn
        have hk : k ≤ D := (Nat.le_succ k).trans hk1
        have hz : aux_prefix_increment z (k + 1) = 0 := by
          simp [aux_prefix_increment, z, hk1, hk]
        rw [hz, abs_zero] at hH
        exact not_le_of_gt hpositive hH
      have hznext : z (k + 1) = u (k + 1) - u D := by
        simp only [z, ite_eq_right (not_le_of_gt hDk)]
      have hzprev : z k = u k - u D := by
        by_cases hk : k ≤ D
        · have heq : k = D := by omega
          subst k
          simp [z]
        · simp only [z, ite_eq_right hk]
      have hid : aux_prefix_increment z (k + 1) = u (k + 1) - u k := by
        rw [aux_prefix_increment, hznext, hzprev]
        ring
      refine ⟨k + 1, hDk, ?_⟩
      simpa only [hid, Nat.add_sub_cancel] using hH

def aux_prefix_error (p M q r K : ℝ) (H : ℕ) : ℝ :=
  2 * ((2 * (M / q * q ^ H) / (K * r ^ H)) ^ p)

theorem aux_prefix_error_nonneg
    (p M q r K : ℝ) (H : ℕ)
    (hM : 0 ≤ M) (hq : 0 < q) (hr : 0 < r) (hK : 0 < K) :
    0 ≤ aux_prefix_error p M q r K H := by
  unfold aux_prefix_error
  positivity

theorem aux_prefix_error_formula
    (p M q r K b : ℝ) (H : ℕ)
    (hM : 0 ≤ M) (hq : 0 < q) (hr : 0 < r) (hK : 0 < K)
    (hrate : (q / r) ^ p = Real.exp (-b)) :
    aux_prefix_error p M q r K H =
      2 * (2 * M / (q * K)) ^ p * Real.exp (-(b * (H : ℝ))) := by
  have hx : 0 ≤ 2 * M / (q * K) := by positivity
  have hqr : 0 ≤ q / r := (div_pos hq hr).le
  have hid : 2 * (M / q * q ^ H) / (K * r ^ H) =
      (2 * M / (q * K)) * (q / r) ^ H := by
    rw [div_pow]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  unfold aux_prefix_error
  rw [hid, Real.mul_rpow hx (pow_nonneg hqr H),
    ← Real.rpow_pow_comm hqr p H, hrate, aux_prefix_exp_nat_pow]
  have heq : -b * (H : ℝ) = -(b * (H : ℝ)) := by ring
  rw [heq]
  ring

theorem aux_prefix_small_coefficient
    (p Cp q K B : ℝ)
    (hp : 0 < p) (hCp : 0 < Cp) (hq : 0 < q) (hK : 0 < K)
    (hB : 0 < B) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
        (2 * (Cp * eta) / (q * K)) ^ p ≤ B := by
  let c : ℝ := B ^ p⁻¹
  let eta0 : ℝ := c * (q * K) / (2 * Cp)
  have hc : 0 < c := Real.rpow_pos_of_pos hB _
  have hcp : c ^ p = B := Real.rpow_inv_rpow hB.le (ne_of_gt hp)
  refine ⟨eta0, by dsimp [eta0]; positivity, ?_⟩
  intro eta heta hetale
  have hx : 0 ≤ 2 * (Cp * eta) / (q * K) := by positivity
  have hxc : 2 * (Cp * eta) / (q * K) ≤ c := by
    apply (div_le_iff₀ (mul_pos hq hK)).2
    calc
      2 * (Cp * eta) ≤ 2 * (Cp * eta0) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hetale hCp.le) (by norm_num)
      _ = c * (q * K) := by
        dsimp [eta0]
        field_simp [ne_of_gt hCp]

  exact (Real.rpow_le_rpow hx hxc hp.le).trans_eq hcp

theorem aux_prefix_weighted_budget
    (p Cp q r K b beta v C c Cgeom delta : ℝ)
    (hp : 0 < p) (hCp : 0 < Cp) (hq : 0 < q) (hr : 0 < r)
    (hK : 0 < K) (hCgeom : 0 < Cgeom) (hdelta : 0 < delta)
    (hb : b = beta * C + v + 1)
    (hrate : (q / r) ^ p = Real.exp (-b)) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 → ∀ H : ℕ,
        ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
            aux_prefix_error p (Cp * eta) q r K H ≤
          delta * Real.exp (-(beta * (C * (H : ℝ) + c))) := by
  let B : ℝ := delta * Real.exp (-(beta * c)) / (2 * Cgeom)
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨eta0, heta0, hsmall⟩ :=
    aux_prefix_small_coefficient p Cp q K B hp hCp hq hK hB
  refine ⟨eta0, heta0, ?_⟩
  intro eta heta hetale H
  have he : aux_prefix_error p (Cp * eta) q r K H ≤
      2 * B * Real.exp (-(b * (H : ℝ))) := by
    rw [aux_prefix_error_formula p (Cp * eta) q r K b H
      (mul_pos hCp heta).le hq hr hK hrate]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hsmall eta heta hetale) (by norm_num))
      (Real.exp_pos _).le
  have hcoef : 2 * Cgeom * B = delta * Real.exp (-(beta * c)) := by
    dsimp [B]
    field_simp [ne_of_gt hCgeom]

  have hexp : Real.exp (H : ℝ) * Real.exp (v * (H : ℝ)) *
      Real.exp (-(b * (H : ℝ))) = Real.exp (-(beta * C * (H : ℝ))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hb]
    ring
  calc
    ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
        aux_prefix_error p (Cp * eta) q r K H ≤
        ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
          (2 * B * Real.exp (-(b * (H : ℝ)))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((H : ℝ) + 1) *
        (Cgeom * Real.exp (v * (H : ℝ)) *
          (2 * B * Real.exp (-(b * (H : ℝ))))) := by ring
    _ ≤ Real.exp (H : ℝ) *
        (Cgeom * Real.exp (v * (H : ℝ)) *
          (2 * B * Real.exp (-(b * (H : ℝ))))) :=
      mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (by positivity)
    _ = (2 * Cgeom * B) *
        (Real.exp (H : ℝ) * Real.exp (v * (H : ℝ)) *
          Real.exp (-(b * (H : ℝ)))) := by ring
    _ = delta * Real.exp (-(beta * c)) *
        Real.exp (-(beta * C * (H : ℝ))) := by rw [hcoef, hexp]
    _ = delta * Real.exp (-(beta * (C * (H : ℝ) + c))) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem aux_prefix_base_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T U : Ω → ℝ)
    (D : ℕ) (p M q r lam K tail : ℝ)
    (hD : 0 < (D : ℝ)) (hp : 0 < p) (hM : 0 ≤ M)
    (hq : 0 < q) (hq1 : q ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hK : 0 < K) (hKle : K ≤ lam / 4) (htail : 0 ≤ tail)
    (hT : AEStronglyMeasurable T P) (hU : AEStronglyMeasurable U P)
    (hn : eLpNorm (fun om => T om - U om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal ((D : ℝ) * M * q ^ D))
    (hprob : P {om | lam * (D : ℝ) / 4 < T om} ≤ ENNReal.ofReal tail) :
    P {om | lam * (D : ℝ) / 2 ≤ U om} ≤
      ENNReal.ofReal (tail + aux_prefix_error p M q r K D) := by
  have hrpow : ∀ k : ℕ, r ^ k ≤ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        exact (mul_le_mul_of_nonneg_right ih hr.le).trans
          (by simpa using hr1)
  have ht : 0 < (D : ℝ) * K * r ^ D := by positivity
  have htupper : (D : ℝ) * K * r ^ D ≤ lam * (D : ℝ) / 4 := by
    calc
      (D : ℝ) * K * r ^ D ≤ (D : ℝ) * K * 1 :=
        mul_le_mul_of_nonneg_left (hrpow D) (by positivity)
      _ ≤ (D : ℝ) * (lam / 4) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hKle hD.le
      _ = lam * (D : ℝ) / 4 := by ring
  have hm : (D : ℝ) * M ≤ (D : ℝ) * M / q := by
    apply (le_div_iff₀ hq).2
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hq1 (mul_nonneg hD.le hM)
  have hn' : eLpNorm (fun om => T om - U om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal ((D : ℝ) * M / q * q ^ D) :=
    hn.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hm (pow_nonneg hq.le D)))
  have hz : eLpNorm (fun _ : Ω => (0 : ℝ)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal ((D : ℝ) * M / q * q ^ D) := by
    simp only [eLpNorm_fun_zero]
    exact zero_le
  have herr := aux_prefix_lp_sub_tail P
    (fun om => T om - U om) (fun _ => 0)
    p ((D : ℝ) * K * r ^ D) ((D : ℝ) * M / q * q ^ D)
    hp ht (by positivity) (hT.sub hU) aestronglyMeasurable_const hn' hz
  have hratio : 2 * ((D : ℝ) * M / q * q ^ D) /
      ((D : ℝ) * K * r ^ D) =
      2 * (M / q * q ^ D) / (K * r ^ D) := by
    field_simp
      [ne_of_gt hD, ne_of_gt hq, ne_of_gt hK, ne_of_gt (pow_pos hr D)]

  have herr' : P {om | (D : ℝ) * K * r ^ D ≤ |T om - U om|} ≤
      ENNReal.ofReal (aux_prefix_error p M q r K D) := by
    simpa only [sub_zero, hratio, aux_prefix_error] using herr
  have hsub : {om | lam * (D : ℝ) / 2 ≤ U om} ⊆
      {om | lam * (D : ℝ) / 4 < T om} ∪
        {om | (D : ℝ) * K * r ^ D ≤ |T om - U om|} := by
    intro om hom
    by_cases hlarge : lam * (D : ℝ) / 4 < T om
    · exact Or.inl hlarge
    · apply Or.inr
      have hsmall := le_of_not_gt hlarge
      have habs := neg_le_abs (T om - U om)
      have hom' : lam * (D : ℝ) / 2 ≤ U om := hom
      change (D : ℝ) * K * r ^ D ≤ |T om - U om|
      linarith
  calc
    P {om | lam * (D : ℝ) / 2 ≤ U om} ≤
        P ({om | lam * (D : ℝ) / 4 < T om} ∪
          {om | (D : ℝ) * K * r ^ D ≤ |T om - U om|}) :=
      measure_mono hsub
    _ ≤ P {om | lam * (D : ℝ) / 4 < T om} +
        P {om | (D : ℝ) * K * r ^ D ≤ |T om - U om|} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal tail +
        ENNReal.ofReal (aux_prefix_error p M q r K D) :=
      add_le_add hprob herr'
    _ = ENNReal.ofReal (tail + aux_prefix_error p M q r K D) :=
      (ENNReal.ofReal_add htail
        (aux_prefix_error_nonneg p M q r K D hM hq hr hK)).symm

theorem aux_prefix_step_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T U V : Ω → ℝ)
    (D H : ℕ) (p M q r K : ℝ)
    (hD : 0 < (D : ℝ)) (hH : 1 ≤ H) (hp : 0 < p) (hM : 0 ≤ M)
    (hq : 0 < q) (hq1 : q ≤ 1) (hr : 0 < r) (hK : 0 < K)
    (hT : AEStronglyMeasurable T P)
    (hU : AEStronglyMeasurable U P) (hV : AEStronglyMeasurable V P)
    (hnU : eLpNorm (fun om => T om - U om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal ((D : ℝ) * M * q ^ (H - 1)))
    (hnV : eLpNorm (fun om => T om - V om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal ((D : ℝ) * M * q ^ H)) :
    P {om | (D : ℝ) * K * r ^ H ≤ |V om - U om|} ≤
      ENNReal.ofReal (aux_prefix_error p M q r K H) := by
  have ht : 0 < (D : ℝ) * K * r ^ H := by positivity
  have hs : (D : ℝ) * M / q * q ^ H =
      (D : ℝ) * M * q ^ (H - 1) := by
    calc
      (D : ℝ) * M / q * q ^ H =
          (D : ℝ) * M / q * q ^ ((H - 1) + 1) := by
        rw [Nat.sub_add_cancel hH]
      _ = (D : ℝ) * M * q ^ (H - 1) := by
        rw [pow_succ]
        field_simp [ne_of_gt hq]

  have hm : (D : ℝ) * M ≤ (D : ℝ) * M / q := by
    apply (le_div_iff₀ hq).2
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hq1 (mul_nonneg hD.le hM)
  have hnU' : eLpNorm (fun om => T om - U om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal ((D : ℝ) * M / q * q ^ H) := by
    rw [hs]
    exact hnU
  have hnV' : eLpNorm (fun om => T om - V om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal ((D : ℝ) * M / q * q ^ H) :=
    hnV.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hm (pow_nonneg hq.le H)))
  have htail := aux_prefix_lp_sub_tail P
    (fun om => T om - U om) (fun om => T om - V om)
    p ((D : ℝ) * K * r ^ H) ((D : ℝ) * M / q * q ^ H)
    hp ht (by positivity) (hT.sub hU) (hT.sub hV) hnU' hnV'
  have hid : ∀ om,
      (T om - U om) - (T om - V om) = V om - U om := by
    intro om
    ring
  have hratio : 2 * ((D : ℝ) * M / q * q ^ H) /
      ((D : ℝ) * K * r ^ H) =
      2 * (M / q * q ^ H) / (K * r ^ H) := by
    field_simp
      [ne_of_gt hD, ne_of_gt hq, ne_of_gt hK, ne_of_gt (pow_pos hr H)]

  simpa only [hid, hratio, aux_prefix_error] using htail

theorem aux_prefix_cover_from_budget
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℕ+ → MeasurableSpace Ω)
    (bound : ℕ+ → ℝ) (w : ℕ → ℕ+) (hw : Function.Injective w)
    (k0 : ℕ) (hk0 : 1 ≤ k0)
    (I : ℕ → Type) [∀ D, Fintype (I D)]
    (lam p M q r K Cgeom v A Ctail : ℝ)
    (hlam : 0 < lam) (hp : 0 < p) (hM : 0 ≤ M)
    (hq : 0 < q) (hq1 : q ≤ 1) (hr : 0 < r) (hr1 : r < 1)
    (hKdef : K = lam * (1 - r) / 4)
    (hCgeom : 0 ≤ Cgeom) (hv : 0 ≤ v) (hCtail : 0 ≤ Ctail)
    (hcard : ∀ D, (Fintype.card (I D) : ℝ) ≤
      Cgeom * Real.exp (v * (D : ℝ)))
    (T : (D : ℕ) → I D → Ω → ℝ)
    (U : (D : ℕ) → I D → ℕ → Ω → ℝ)
    (hT : ∀ D i, AEStronglyMeasurable (T D i) P)
    (hU : ∀ D i H, AEStronglyMeasurable (U D i H) P)
    (herror : ∀ D H, k0 ≤ D → D ≤ H → ∀ i : I D,
      eLpNorm (fun om => T D i om - U D i H om)
          (ENNReal.ofReal p) P ≤
        ENNReal.ofReal ((D : ℝ) * M * q ^ H))
    (htail : ∀ D, k0 ≤ D → ∀ i : I D,
      P {om | lam * (D : ℝ) / 4 < T D i om} ≤
        ENNReal.ofReal (Ctail * Real.exp (-(A * (D : ℝ)))))
    (hwindow : ∀ D H j, k0 ≤ D → D ≤ j → j ≤ H → ∀ i : I D,
      StronglyMeasurable[B (w H)] (U D i j))
    (hbudget : ∀ H, k0 ≤ H →
      Cgeom * Ctail * Real.exp (-((A - v) * (H : ℝ))) +
          ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
            aux_prefix_error p M q r K H ≤ bound (w H))
    (Sigma : Set Ω)
    (hlimit : ∀ om, om ∈ Sigma → ∀ D i,
      Tendsto (fun H => U D i H om) atTop (𝓝 (T D i om))) :
    ∃ W : ℕ+ → Set Ω,
      (∀ h, MeasurableSet[B h] (W h)) ∧
      (∀ h, P (W h) ≤ ENNReal.ofReal (bound h)) ∧
      Sigma ∩ {om | ∃ D, k0 ≤ D ∧ ∃ i : I D,
        lam * (D : ℝ) ≤ T D i om} ⊆
        ⋃ h : ℕ+, W h := by
  classical
  have hK : 0 < K := by
    rw [hKdef]
    exact div_pos (mul_pos hlam (sub_pos.mpr hr1)) (by norm_num)
  have hKle : K ≤ lam / 4 := by
    rw [hKdef]
    have hh : 0 ≤ lam * r := mul_nonneg hlam.le hr.le
    nlinarith
  have hDpos : ∀ D : ℕ, k0 ≤ D → 0 < (D : ℝ) := by
    intro D hD
    have hn : 0 < D :=
      lt_of_lt_of_le Nat.zero_lt_one (hk0.trans hD)
    exact_mod_cast hn
  have herrpos : ∀ H, 0 ≤ aux_prefix_error p M q r K H :=
    fun H => aux_prefix_error_nonneg p M q r K H hM hq hr hK
  have hcardH : ∀ D H : ℕ, D ≤ H →
      (Fintype.card (I D) : ℝ) ≤
        Cgeom * Real.exp (v * (H : ℝ)) := by
    intro D H hDH
    have hcast : (D : ℝ) ≤ (H : ℝ) := by exact_mod_cast hDH
    calc
      (Fintype.card (I D) : ℝ) ≤
          Cgeom * Real.exp (v * (D : ℝ)) := hcard D
      _ ≤ Cgeom * Real.exp (v * (H : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left hcast hv)) hCgeom
  let Ebase : ℕ → Set Ω := fun H =>
    ⋃ i : I H, {om | lam * (H : ℝ) / 2 ≤ U H i H om}
  let Estep : (H : ℕ) → Fin H → Set Ω := fun H D =>
    if k0 ≤ (D : ℕ) then
      ⋃ i : I (D : ℕ),
        {om | (D : ℝ) * K * r ^ H ≤
          |U D i H om - U D i (H - 1) om|}
    else ∅
  let E : ℕ → Set Ω := fun H =>
    if k0 ≤ H then Ebase H ∪ ⋃ D : Fin H, Estep H D else ∅
  have hEmeas : ∀ H, MeasurableSet[B (w H)] (E H) := by
    intro H
    by_cases hH : k0 ≤ H
    · simp only [E, ite_eq_left hH]
      apply MeasurableSet.union
      · apply MeasurableSet.iUnion
        intro i
        let : MeasurableSpace Ω := B (w H)
        exact measurableSet_le measurable_const
          (hwindow H H H hH le_rfl le_rfl i).measurable
      · apply MeasurableSet.iUnion
        intro D
        by_cases hD : k0 ≤ (D : ℕ)
        · simp only [Estep, ite_eq_left hD]
          apply MeasurableSet.iUnion
          intro i
          have hDH : (D : ℕ) ≤ H := Nat.le_of_lt D.isLt
          have hDprev : (D : ℕ) ≤ H - 1 := by
            have hlt := D.isLt
            omega
          let : MeasurableSpace Ω := B (w H)
          exact measurableSet_le measurable_const
            (((hwindow D H H hD hDH le_rfl i).sub
              (hwindow D H (H - 1) hD hDprev
                (Nat.sub_le H 1) i)).measurable.abs)
        · simp only [Estep, ite_eq_right hD]
          let : MeasurableSpace Ω := B (w H)
          exact MeasurableSet.empty
    · simp only [E, ite_eq_right hH]
      let : MeasurableSpace Ω := B (w H)
      exact MeasurableSet.empty
  have hbaseprob : ∀ H, k0 ≤ H →
      P (Ebase H) ≤ ENNReal.ofReal
        (Cgeom * Real.exp (v * (H : ℝ)) *
          (Ctail * Real.exp (-(A * (H : ℝ))) +
            aux_prefix_error p M q r K H)) := by
    intro H hH
    have hb : 0 ≤ Ctail * Real.exp (-(A * (H : ℝ))) +
        aux_prefix_error p M q r K H :=
      add_nonneg
        (mul_nonneg hCtail (Real.exp_pos _).le) (herrpos H)
    have hi : ∀ i : I H,
        P {om | lam * (H : ℝ) / 2 ≤ U H i H om} ≤
          ENNReal.ofReal (Ctail * Real.exp (-(A * (H : ℝ))) +
            aux_prefix_error p M q r K H) := by
      intro i
      exact aux_prefix_base_tail P (T H i) (U H i H) H
        p M q r lam K (Ctail * Real.exp (-(A * (H : ℝ))))
        (hDpos H hH) hp hM hq hq1 hr hr1.le hK hKle
        (mul_nonneg hCtail (Real.exp_pos _).le)
        (hT H i) (hU H i H)
        (herror H H hH le_rfl i) (htail H hH i)
    exact (aux_prefix_finite_union P
      (fun i : I H => {om | lam * (H : ℝ) / 2 ≤ U H i H om})
      (Ctail * Real.exp (-(A * (H : ℝ))) +
        aux_prefix_error p M q r K H) hb hi).trans
        (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (hcard H) hb))
  have hstepprob : ∀ H (D : Fin H),
      P (Estep H D) ≤ ENNReal.ofReal
        (Cgeom * Real.exp (v * (H : ℝ)) *
          aux_prefix_error p M q r K H) := by
    intro H D
    by_cases hD : k0 ≤ (D : ℕ)
    · simp only [Estep, ite_eq_left hD]
      have hprev : (D : ℕ) ≤ H - 1 := by
        have hlt := D.isLt
        omega
      have hDH : (D : ℕ) ≤ H := Nat.le_of_lt D.isLt
      have hH : 1 ≤ H := by
        have hlt := D.isLt
        omega
      have hi : ∀ i : I (D : ℕ),
          P {om | (D : ℝ) * K * r ^ H ≤
            |U D i H om - U D i (H - 1) om|} ≤
            ENNReal.ofReal (aux_prefix_error p M q r K H) := by
        intro i
        exact aux_prefix_step_tail P
          (T D i) (U D i (H - 1)) (U D i H)
          D H p M q r K (hDpos D hD) hH hp hM hq hq1 hr hK
          (hT D i) (hU D i (H - 1)) (hU D i H)
          (herror D (H - 1) hD hprev i)
          (herror D H hD hDH i)
      exact (aux_prefix_finite_union P
        (fun i : I (D : ℕ) =>
          {om | (D : ℝ) * K * r ^ H ≤
            |U D i H om - U D i (H - 1) om|})
        (aux_prefix_error p M q r K H) (herrpos H) hi).trans
          (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right
              (hcardH D H hDH) (herrpos H)))
    · simp only [Estep, ite_eq_right hD, measure_empty]
      exact zero_le
  have hEprob : ∀ H, P (E H) ≤ ENNReal.ofReal (bound (w H)) := by
    intro H
    by_cases hH : k0 ≤ H
    · have hsteps : P (⋃ D : Fin H, Estep H D) ≤
          ENNReal.ofReal ((H : ℝ) *
            (Cgeom * Real.exp (v * (H : ℝ)) *
              aux_prefix_error p M q r K H)) := by
        simpa only [Fintype.card_fin] using
          aux_prefix_finite_union P (Estep H)
            (Cgeom * Real.exp (v * (H : ℝ)) *
              aux_prefix_error p M q r K H)
            (mul_nonneg
              (mul_nonneg hCgeom (Real.exp_pos _).le) (herrpos H))
            (hstepprob H)
      have hbase_nonneg : 0 ≤ Cgeom * Real.exp (v * (H : ℝ)) *
          (Ctail * Real.exp (-(A * (H : ℝ))) +
            aux_prefix_error p M q r K H) :=
        mul_nonneg (mul_nonneg hCgeom (Real.exp_pos _).le)
          (add_nonneg
            (mul_nonneg hCtail (Real.exp_pos _).le) (herrpos H))
      have hsteps_nonneg : 0 ≤ (H : ℝ) *
          (Cgeom * Real.exp (v * (H : ℝ)) *
            aux_prefix_error p M q r K H) :=
        mul_nonneg (Nat.cast_nonneg H)
          (mul_nonneg
            (mul_nonneg hCgeom (Real.exp_pos _).le) (herrpos H))
      have hexp :
          Real.exp (v * (H : ℝ)) * Real.exp (-(A * (H : ℝ))) =
          Real.exp (-((A - v) * (H : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hid : Cgeom * Real.exp (v * (H : ℝ)) *
            (Ctail * Real.exp (-(A * (H : ℝ))) +
              aux_prefix_error p M q r K H) +
          (H : ℝ) * (Cgeom * Real.exp (v * (H : ℝ)) *
            aux_prefix_error p M q r K H) =
          Cgeom * Ctail * Real.exp (-((A - v) * (H : ℝ))) +
            ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
              aux_prefix_error p M q r K H := by
        calc
          _ = Cgeom * Ctail *
                (Real.exp (v * (H : ℝ)) *
                  Real.exp (-(A * (H : ℝ)))) +
              ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
                aux_prefix_error p M q r K H := by ring
          _ = _ := by rw [hexp]
      simp only [E, ite_eq_left hH]
      calc
        P (Ebase H ∪ ⋃ D : Fin H, Estep H D) ≤
            P (Ebase H) + P (⋃ D : Fin H, Estep H D) :=
          measure_union_le _ _
        _ ≤ ENNReal.ofReal (Cgeom * Real.exp (v * (H : ℝ)) *
              (Ctail * Real.exp (-(A * (H : ℝ))) +
                aux_prefix_error p M q r K H)) +
            ENNReal.ofReal ((H : ℝ) *
              (Cgeom * Real.exp (v * (H : ℝ)) *
                aux_prefix_error p M q r K H)) :=
          add_le_add (hbaseprob H hH) hsteps
        _ = ENNReal.ofReal
            (Cgeom * Ctail * Real.exp (-((A - v) * (H : ℝ))) +
              ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
                aux_prefix_error p M q r K H) := by
          rw [← ENNReal.ofReal_add hbase_nonneg hsteps_nonneg, hid]
        _ ≤ ENNReal.ofReal (bound (w H)) :=
          ENNReal.ofReal_le_ofReal (hbudget H hH)
    · simp only [E, ite_eq_right hH, measure_empty]
      exact zero_le
  have hcover :
      Sigma ∩ {om | ∃ D, k0 ≤ D ∧ ∃ i : I D,
        lam * (D : ℝ) ≤ T D i om} ⊆
        ⋃ H : ℕ, E H := by
    intro om hom
    obtain ⟨D, hD, i, hbad⟩ := hom.2
    have hthreshold : 0 < lam * (D : ℝ) :=
      mul_pos hlam (hDpos D hD)
    obtain hbase | ⟨H, hDH, hstep⟩ :=
      aux_prefix_increment_witness
        (fun H => U D i H om) (T D i om)
        (lam * (D : ℝ)) r D hthreshold hr hr1
        (hlimit om hom.1 D i) hbad
    · apply Set.mem_iUnion.mpr
      refine ⟨D, ?_⟩
      simp only [E, ite_eq_left hD]
      apply Or.inl
      exact Set.mem_iUnion.mpr ⟨i, hbase⟩
    · have hH : k0 ≤ H := hD.trans (Nat.le_of_lt hDH)
      apply Set.mem_iUnion.mpr
      refine ⟨H, ?_⟩
      simp only [E, ite_eq_left hH]
      apply Or.inr
      apply Set.mem_iUnion.mpr
      refine ⟨⟨D, hDH⟩, ?_⟩
      change om ∈ (if k0 ≤ D then
        ⋃ i : I D, {om | (D : ℝ) * K * r ^ H ≤
          |U D i H om - U D i (H - 1) om|} else ∅)
      rw [ite_eq_left hD]
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      have hcoef :
          (D : ℝ) * K = (lam * (D : ℝ)) * (1 - r) / 4 := by
        rw [hKdef]
        ring
      change (D : ℝ) * K * r ^ H ≤ |U D i H om - U D i (H - 1) om|
      rw [hcoef]
      exact hstep
  exact aux_prefix_reindex_cover P B (fun h => ENNReal.ofReal (bound h))
    (Sigma ∩ {om | ∃ D, k0 ≤ D ∧ ∃ i : I D,
      lam * (D : ℝ) ≤ T D i om})
    w hw E hEmeas hEprob hcover




theorem lem_witness_prefix_dyadic_cover
    (d : ℕ) (_hd : 1 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
    (Bsig : ℤ → ℤ → MeasurableSpace (BilateralField d))
    (Cband c0 k0 : ℕ) (hCband : 0 < Cband)
    (hk0 : 1 ≤ k0) (_hc0 : c0 ≤ k0)
    (beta a lam v Cgeom : ℝ)
    (hbeta : 0 < beta) (ha : 0 < a) (hlam : 0 < lam)
    (hv : 0 ≤ v) (hCgeom : 1 ≤ Cgeom)
    (p A Ctail Cp : ℝ)
    (hp : 2 ≤ p) (hCtail : 0 < Ctail) (hCp : 0 < Cp)
    (hA : 64 * ((Cband : ℝ) + 1) * (beta + v + 1) ≤ A)
    (hpRate : 64 * ((Cband : ℝ) + 1) * (beta + v + 1) ≤
      p * a * Real.log 3)
    (hBsig_interval_mono : ∀ l₁ r₁ l₂ r₂ : ℤ,
      l₂ ≤ l₁ → r₁ ≤ r₂ → Bsig l₁ r₁ ≤ Bsig l₂ r₂)
    (hprefix_tail_budget :
      Cgeom * Ctail * Real.exp
        (beta * ((Cband : ℝ) + (c0 : ℝ)) -
          (A - v - beta * ((Cband : ℝ) + 1)) * (k0 : ℝ)) < 1) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
        ∀ (I : ℕ → Type) [∀ D, Fintype (I D)],
        ∀ (start : (n : ℤ) → (D : ℕ) → I D → ℤ),
        ∀ (centre : (D : ℕ) → I D → SpatialCoordinates d),
        ∀ (tag : (D : ℕ) → I D → Fin2 2),
        (∀ D, (Fintype.card (I D) : ℝ) ≤
          Cgeom * Real.exp (v * (D : ℝ))) →
        (∀ n D i,
          n - (c0 : ℤ) ≤ start n D i ∧
            start n D i ≤ n + (c0 : ℤ)) →
        ∀ (X : Fin2 2 → ℤ → SpatialCoordinates d →
          BilateralField d → ℝ),
        ∀ (Xb : Fin2 2 → ℤ → ℕ → SpatialCoordinates d →
          BilateralField d → ℝ),
        (∀ q n z, MemLp (X q n z) (ENNReal.ofReal p) P) →
        (∀ q n H z, AEStronglyMeasurable (Xb q n H z) P) →
        (∀ q n H z,
          eLpNorm (fun om => X q n z om - Xb q n H z om)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal
              (Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
        (Sigma : Set (BilateralField d)) →
        MeasurableSet Sigma → P Sigma = 1 →
        (∀ om, om ∈ Sigma →
          ∀ q n D i j,
            Tendsto
              (fun H => Xb q (start n D i + (j : ℤ)) H
                (centre D i) om)
              atTop (𝓝 (X q (start n D i + (j : ℤ))
                (centre D i) om))) →
        (∀ n D, k0 ≤ D → ∀ i : I D,
          P {om |
              lam * (D : ℝ) / 4 <
                ∑ j ∈ Finset.range D,
                  X (tag D i) (start n D i + (j : ℤ))
                    (centre D i) om} ≤
            ENNReal.ofReal (Ctail * Real.exp (-(A * (D : ℝ))))) →
        (∀ n D H, k0 ≤ D → D ≤ H → ∀ i : I D,
          let R : ℕ := Cband * (H + 1) + c0 + D
          StronglyMeasurable[
            Bsig (n - (R : ℤ)) (n + 2 * (R : ℤ))]
            (fun om =>
              ∑ j ∈ Finset.range D,
                Xb (tag D i)
                  (start n D i + (j : ℤ)) H (centre D i) om)) →
        ∀ n : ℤ, ∃ W : ℕ+ → Set (BilateralField d),
          (∀ h : ℕ+,
            MeasurableSet[
              Bsig (n - (h : ℤ)) (n + 2 * (h : ℤ))] (W h)) ∧
          (∀ h : ℕ+,
            P (W h) ≤
              ENNReal.ofReal (Real.exp (-(beta * (h : ℝ))))) ∧
          Sigma ∩ {om |
            ∃ D : ℕ, k0 ≤ D ∧ ∃ i : I D,
              lam * (D : ℝ) ≤
                ∑ j ∈ Finset.range D,
                  X (tag D i) (start n D i + (j : ℤ))
                    (centre D i) om} ⊆
            ⋃ h : ℕ+, W h := by
  classical
  let C : ℝ := (Cband : ℝ) + 1
  let c : ℝ := (Cband : ℝ) + (c0 : ℝ)
  let b : ℝ := beta * C + v + 1
  let theta : ℝ := Cgeom * Ctail *
    Real.exp (beta * c - (A - v - beta * C) * (k0 : ℝ))
  have hp0 : 0 < p := by linarith
  have hCg : 0 < Cgeom := lt_of_lt_of_le zero_lt_one hCgeom
  have hC : 1 ≤ C := by
    dsimp [C]
    have hn : 0 ≤ (Cband : ℝ) := Nat.cast_nonneg Cband
    linarith
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hproduct : 0 < C * (beta + v + 1) :=
    mul_pos hCpos (by linarith)
  have hble : b ≤ C * (beta + v + 1) := by
    dsimp [b]
    nlinarith only [hC, mul_nonneg (sub_nonneg.mpr hC) hv]
  have hb64 : b < 64 * C * (beta + v + 1) := by
    nlinarith only [hproduct, hble]
  have hA' : 64 * C * (beta + v + 1) ≤ A := by
    simpa only [C] using hA
  have hgapA : 0 ≤ A - v - beta * C := by
    have hbA := hb64.trans_le hA'
    dsimp [b] at hbA
    linarith
  have hgap : b < a * p * Real.log 3 := by
    calc
      b < 64 * C * (beta + v + 1) := hb64
      _ ≤ p * a * Real.log 3 := by simpa only [C] using hpRate
      _ = a * p * Real.log 3 := by ring
  obtain ⟨q, r, hqeq, hq, hq1, hr, hr1, hrate⟩ :=
    aux_prefix_geometric_rate a b p ha hp0 hgap
  let K : ℝ := lam * (1 - r) / 4
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos (mul_pos hlam (sub_pos.mpr hr1)) (by norm_num)
  have htheta : theta < 1 := by
    simpa only [theta, C, c] using hprefix_tail_budget
  have htheta0 : 0 ≤ theta := by dsimp [theta]; positivity
  obtain ⟨eta0, heta0, herrorbudget⟩ :=
    aux_prefix_weighted_budget p Cp q r K b beta v C c Cgeom (1 - theta)
      hp0 hCp hq hr hK hCg (sub_pos.mpr htheta) rfl hrate
  refine ⟨eta0, heta0, ?_⟩
  intro eta heta hetale I instI start centre tag hcard hstart X Xb hXmem hXbae
    happrox Sigma hSigma hSigmaP hlimit htail hband n
  let w : ℕ → ℕ+ := fun H =>
    ⟨Cband * (H + 1) + c0 + H, by
      have hpos : 0 < Cband * (H + 1) :=
        Nat.mul_pos hCband (Nat.succ_pos H)
      omega⟩
  have hw : Function.Injective w := by
    have hstrict : StrictMono w := by
      intro j k hjk
      change Cband * (j + 1) + c0 + j <
        Cband * (k + 1) + c0 + k
      have hmul := Nat.mul_le_mul_left Cband
        (Nat.add_le_add_right (Nat.le_of_lt hjk) 1)
      omega
    exact hstrict.injective
  have hwr : ∀ H, (w H : ℝ) = C * (H : ℝ) + c := by
    intro H
    change ((Cband * (H + 1) + c0 + H : ℕ) : ℝ) =
      C * (H : ℝ) + c
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    dsimp [C, c]
    ring
  have hgeom : ∀ H : ℕ,
      (3 : ℝ) ^ (-(a * (H : ℝ))) = q ^ H := by
    intro H
    calc
      (3 : ℝ) ^ (-(a * (H : ℝ))) =
          (3 : ℝ) ^ ((-a) * (H : ℝ)) := by
        congr 1
        ring
      _ = ((3 : ℝ) ^ (-a)) ^ H :=
        Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3) (-a) H
      _ = q ^ H := by rw [hqeq]
  let T : (D : ℕ) → I D → BilateralField d → ℝ := fun D i om =>
    ∑ j ∈ Finset.range D,
      X (tag D i) (start n D i + (j : ℤ)) (centre D i) om
  let U : (D : ℕ) → I D → ℕ → BilateralField d → ℝ :=
    fun D i H om =>
      ∑ j ∈ Finset.range D,
        Xb (tag D i) (start n D i + (j : ℤ)) H (centre D i) om
  have hTae : ∀ D i, AEStronglyMeasurable (T D i) P := by
    intro D i
    exact aux_prefix_ae_sum P
      (fun j => X (tag D i) (start n D i + (j : ℤ)) (centre D i))
      (fun j =>
        (hXmem (tag D i) (start n D i + (j : ℤ)) (centre D i)).aestronglyMeasurable) D
  have hUae : ∀ D i H, AEStronglyMeasurable (U D i H) P := by
    intro D i H
    exact aux_prefix_ae_sum P
      (fun j =>
        Xb (tag D i) (start n D i + (j : ℤ)) H (centre D i))
      (fun j =>
        hXbae (tag D i) (start n D i + (j : ℤ)) H (centre D i)) D
  have herror : ∀ D H, k0 ≤ D → D ≤ H → ∀ i : I D,
      eLpNorm (fun om => T D i om - U D i H om)
          (ENNReal.ofReal p) P ≤
        ENNReal.ofReal ((D : ℝ) * (Cp * eta) * q ^ H) := by
    intro D H hD hDH i
    have hbound := aux_prefix_norm_sum P
      (fun j => X (tag D i) (start n D i + (j : ℤ)) (centre D i))
      (fun j =>
        Xb (tag D i) (start n D i + (j : ℤ)) H (centre D i))
      D p (Cp * eta * q ^ H) (by linarith) (by positivity)
      (fun j =>
        (hXmem (tag D i) (start n D i + (j : ℤ)) (centre D i)).aestronglyMeasurable)
      (fun j =>
        hXbae (tag D i) (start n D i + (j : ℤ)) H (centre D i))
      (fun j => by
        simpa only [hgeom H] using
          happrox (tag D i) (start n D i + (j : ℤ)) H (centre D i))
    simpa only [T, U, mul_assoc] using hbound
  have hTtail : ∀ D, k0 ≤ D → ∀ i : I D,
      P {om | lam * (D : ℝ) / 4 < T D i om} ≤
        ENNReal.ofReal (Ctail * Real.exp (-(A * (D : ℝ)))) := by
    intro D hD i
    exact htail n D hD i
  have hwindow : ∀ D H j, k0 ≤ D → D ≤ j → j ≤ H → ∀ i : I D,
      StronglyMeasurable[
        Bsig (n - (w H : ℤ)) (n + 2 * (w H : ℤ))] (U D i j) := by
    intro D H j hD hDj hjH i
    let R : ℕ := Cband * (j + 1) + c0 + D
    have hR : R ≤ (w H : ℕ) := by
      change Cband * (j + 1) + c0 + D ≤
        Cband * (H + 1) + c0 + H
      have hmul :=
        Nat.mul_le_mul_left Cband (Nat.add_le_add_right hjH 1)
      omega
    have hRint : (R : ℤ) ≤ (w H : ℤ) := by exact_mod_cast hR
    have hsm : StronglyMeasurable[
        Bsig (n - (R : ℤ)) (n + 2 * (R : ℤ))] (U D i j) :=
      hband n D j hD hDj i
    apply hsm.mono
    apply hBsig_interval_mono
    · omega
    · omega
  have hbudget : ∀ H, k0 ≤ H →
      Cgeom * Ctail * Real.exp (-((A - v) * (H : ℝ))) +
          ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
            aux_prefix_error p (Cp * eta) q r K H ≤
        Real.exp (-(beta * (w H : ℝ))) := by
    intro H hH
    have hcast : (k0 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    have hmono : Cgeom * Ctail *
        Real.exp (beta * c - (A - v - beta * C) * (H : ℝ)) ≤
        theta := by
      dsimp only [theta]
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg hCg.le hCtail.le)
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hcast hgapA
      linarith
    have hexp :
        Real.exp (beta * c - (A - v - beta * C) * (H : ℝ)) *
          Real.exp (-(beta * (C * (H : ℝ) + c))) =
        Real.exp (-((A - v) * (H : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have htailbudget :
        Cgeom * Ctail * Real.exp (-((A - v) * (H : ℝ))) ≤
        theta * Real.exp (-(beta * (C * (H : ℝ) + c))) := by
      calc
        Cgeom * Ctail * Real.exp (-((A - v) * (H : ℝ))) =
            (Cgeom * Ctail *
              Real.exp (beta * c -
                (A - v - beta * C) * (H : ℝ))) *
              Real.exp (-(beta * (C * (H : ℝ) + c))) := by
          rw [mul_assoc (Cgeom * Ctail)
            (Real.exp (beta * c -
              (A - v - beta * C) * (H : ℝ)))
            (Real.exp (-(beta * (C * (H : ℝ) + c)))), hexp]
        _ ≤ theta * Real.exp (-(beta * (C * (H : ℝ) + c))) :=
          mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le
    calc
      Cgeom * Ctail * Real.exp (-((A - v) * (H : ℝ))) +
          ((H : ℝ) + 1) * Cgeom * Real.exp (v * (H : ℝ)) *
            aux_prefix_error p (Cp * eta) q r K H ≤
          theta * Real.exp (-(beta * (C * (H : ℝ) + c))) +
            (1 - theta) *
              Real.exp (-(beta * (C * (H : ℝ) + c))) :=
        add_le_add htailbudget (herrorbudget eta heta hetale H)
      _ = Real.exp (-(beta * (w H : ℝ))) := by
        rw [hwr]
        ring
  have hlimitSum : ∀ om, om ∈ Sigma → ∀ D i,
      Tendsto (fun H => U D i H om) atTop (𝓝 (T D i om)) := by
    intro om hom D i
    exact aux_prefix_limit_sum
      (fun j H =>
        Xb (tag D i) (start n D i + (j : ℤ)) H (centre D i) om)
      (fun j =>
        X (tag D i) (start n D i + (j : ℤ)) (centre D i) om)
      (fun j => hlimit om hom (tag D i) n D i (j : ℤ)) D
  exact aux_prefix_cover_from_budget P
    (fun h => Bsig (n - (h : ℤ)) (n + 2 * (h : ℤ)))
    (fun h => Real.exp (-(beta * (h : ℝ)))) w hw k0 hk0 I
    lam p (Cp * eta) q r K Cgeom v A Ctail
    hlam hp0 (mul_pos hCp heta).le hq hq1.le hr hr1 rfl
    hCg.le hv hCtail.le
    hcard T U hTae hUae herror hTtail hwindow hbudget Sigma hlimitSum

theorem aux_prefix_tail_budget_of_log
    (Cgeom Ctail beta v A : ℝ) (Cband c0 k0 : ℕ)
    (hCgeom : 0 < Cgeom) (hCtail : 0 < Ctail)
    (hcutoff :
      Real.log (Cgeom * Ctail) + beta * ((Cband : ℝ) + (c0 : ℝ)) <
        (A - v - beta * ((Cband : ℝ) + 1)) * (k0 : ℝ)) :
    Cgeom * Ctail * Real.exp
      (beta * ((Cband : ℝ) + (c0 : ℝ)) -
        (A - v - beta * ((Cband : ℝ) + 1)) * (k0 : ℝ)) < 1 := by
  have hprod : 0 < Cgeom * Ctail := mul_pos hCgeom hCtail
  calc
    Cgeom * Ctail * Real.exp
        (beta * ((Cband : ℝ) + (c0 : ℝ)) -
          (A - v - beta * ((Cband : ℝ) + 1)) * (k0 : ℝ)) =
        Real.exp (Real.log (Cgeom * Ctail) +
          (beta * ((Cband : ℝ) + (c0 : ℝ)) -
            (A - v - beta * ((Cband : ℝ) + 1)) * (k0 : ℝ))) := by
      rw [Real.exp_add, Real.exp_log hprod]
    _ < 1 := Real.exp_lt_one_iff.mpr (by linarith only [hcutoff])

theorem aux_prefix_tail_budget_at_large_cutoff
    (Cgeom Ctail beta v A : ℝ) (Cband c0 D0 : ℕ)
    (hCgeom : 0 < Cgeom) (hCtail : 0 < Ctail)
    (hgap : 0 < A - v - beta * ((Cband : ℝ) + 1)) :
    ∃ k0 : ℕ, D0 ≤ k0 ∧
      Cgeom * Ctail * Real.exp
        (beta * ((Cband : ℝ) + (c0 : ℝ)) -
          (A - v - beta * ((Cband : ℝ) + 1)) * (k0 : ℝ)) < 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt
    ((Real.log (Cgeom * Ctail) +
        beta * ((Cband : ℝ) + (c0 : ℝ))) /
      (A - v - beta * ((Cband : ℝ) + 1)))
  refine ⟨max D0 N, le_max_left D0 N, ?_⟩
  apply aux_prefix_tail_budget_of_log
    Cgeom Ctail beta v A Cband c0 (max D0 N) hCgeom hCtail
  have hcast : (N : ℝ) ≤ ((max D0 N : ℕ) : ℝ) := by
    exact_mod_cast le_max_right D0 N
  have hlt := hN.trans_le hcast
  have hmul := (div_lt_iff₀ hgap).mp hlt
  simpa only [mul_comm] using hmul

end SubdiffusiveProcess.Paper
