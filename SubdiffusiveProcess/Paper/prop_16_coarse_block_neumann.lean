module

public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Sobolev.PotentialResponses
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.cor_14
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.rem_bank
public import SubdiffusiveProcess.Main.NativeBilateralPotentialSample
public import SubdiffusiveProcess.Main.PositiveScaledNativeLayer
public import SubdiffusiveProcess.Main.CompactPotentialC1Norm
public import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
public import SubdiffusiveProcess.Main.LayerScaling
public import SubdiffusiveProcess.Main.ChaosRootFieldLaw
public import SubdiffusiveProcess.Main.ScaledLayerLaw
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Probability.GeometricSeriesLp
public import SubdiffusiveProcess.Sobolev.CompactPotential
public import SubdiffusiveProcess.Main.ContinuousPositiveLog
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient
public import SubdiffusiveProcess.Assumptions.AnchoredPartialSum

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- One-sided response comparison bound from an exponential-multiplicative sandwich. -/
theorem aux_prop_16_coarse_block_neumann_one_sided
    (s x y : ℝ) (hs : 0 ≤ s) (hxy : Real.exp (-s) * x ≤ y) :
    x - y ≤ s * |x| := by
  have hexp : Real.exp (-s) ≤ 1 := by
    calc
      Real.exp (-s) ≤ Real.exp 0 := Real.exp_le_exp.mpr (neg_nonpos.mpr hs)
      _ = 1 := Real.exp_zero
  have hlinear : 1 - Real.exp (-s) ≤ s := by
    have htangent : -s + 1 ≤ Real.exp (-s) := Real.add_one_le_exp (-s)
    linarith
  calc
    x - y ≤ x - Real.exp (-s) * x := sub_le_sub_left hxy x
    _ = (1 - Real.exp (-s)) * x := by ring
    _ ≤ (1 - Real.exp (-s)) * |x| :=
      mul_le_mul_of_nonneg_left (le_abs_self x) (sub_nonneg.mpr hexp)
    _ ≤ s * |x| := mul_le_mul_of_nonneg_right hlinear (abs_nonneg x)

/-- Two-sided response comparison bound. -/
theorem aux_prop_16_coarse_block_neumann_abs_sub
    (s x y : ℝ) (hs : 0 ≤ s)
    (hxy : Real.exp (-s) * x ≤ y) (hyx : Real.exp (-s) * y ≤ x) :
    |x - y| ≤ s * (|x| + |y|) := by
  have h1 := aux_prop_16_coarse_block_neumann_one_sided s x y hs hxy
  have h2 := aux_prop_16_coarse_block_neumann_one_sided s y x hs hyx
  have hx : 0 ≤ s * |x| := mul_nonneg hs (abs_nonneg x)
  have hy : 0 ≤ s * |y| := mul_nonneg hs (abs_nonneg y)
  rw [mul_add]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Response-difference bound from `cor_14`'s multiplicative comparison clause, isolated so
that later instantiation at large concrete arguments needs only a single unification pass. -/
theorem aux_prop_16_coarse_block_neumann_response_diff
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (S : ResponseSpace Q) (L : S.space →L[ℝ] ℝ)
    (hInvResp : ∀ p q : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))),
      Real.exp (-‖p - q‖) * inverseResponse S (expPotentialCoefficient q) L ≤
          inverseResponse S (expPotentialCoefficient p) L ∧
        inverseResponse S (expPotentialCoefficient p) L ≤
          Real.exp ‖p - q‖ * inverseResponse S (expPotentialCoefficient q) L)
    (u1 u2 : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d)))) :
    |inverseResponse S (expPotentialCoefficient u1) L -
        inverseResponse S (expPotentialCoefficient u2) L| ≤
      ‖u1 - u2‖ * (|inverseResponse S (expPotentialCoefficient u1) L| +
        |inverseResponse S (expPotentialCoefficient u2) L|) := by
  have e1 := hInvResp u1 u2
  have e2 := hInvResp u2 u1
  rw [norm_sub_rev u2 u1] at e2
  exact aux_prop_16_coarse_block_neumann_abs_sub ‖u1 - u2‖ _ _ (norm_nonneg _) e2.1 e1.1

/-- The generic bilateral-coordinate copy map: keep coordinates `≤ h` from the first copy
and coordinates `> h` from the second copy. -/
def aux_prop_16_coarse_block_neumann_copy {E : Type*} (h : ℕ)
    (pair : (ℤ → E) × (ℤ → E)) : ℤ → E :=
  fun j => if (h : ℤ) < j then pair.2 j else pair.1 j

theorem aux_prop_16_coarse_block_neumann_copy_measurable
    {E : Type*} [MeasurableSpace E] (h : ℕ) :
    Measurable (aux_prop_16_coarse_block_neumann_copy (E := E) h) := by
  unfold aux_prop_16_coarse_block_neumann_copy
  refine Measurable.of_eval fun j : ℤ => ?_
  by_cases hj : (h : ℤ) < j
  · have hm : Measurable (fun pair : (ℤ → E) × (ℤ → E) => pair.2 j) :=
      (measurable_pi_apply j).comp measurable_snd
    simpa only [ite_eq_left hj] using hm
  · have hm : Measurable (fun pair : (ℤ → E) × (ℤ → E) => pair.1 j) :=
      (measurable_pi_apply j).comp measurable_fst
    simpa only [ite_eq_right hj] using hm

theorem aux_prop_16_coarse_block_neumann_copy_infinitePi
    {E : Type*} [MeasurableSpace E]
    (mu : ℤ → Measure E) [∀ j : ℤ, IsProbabilityMeasure (mu j)] (h : ℕ) :
    MeasurePreserving (aux_prop_16_coarse_block_neumann_copy (E := E) h)
      ((Measure.infinitePi mu).prod (Measure.infinitePi mu))
      (Measure.infinitePi mu) := by
  classical
  refine ⟨aux_prop_16_coarse_block_neumann_copy_measurable h, ?_⟩
  apply Measure.eq_infinitePi mu
  intro s t ht
  let s1 : Finset ℤ := s.filter (fun j : ℤ => ¬ (h : ℤ) < j)
  let s2 : Finset ℤ := s.filter (fun j : ℤ => (h : ℤ) < j)
  have hpre :
      (aux_prop_16_coarse_block_neumann_copy (E := E) h) ⁻¹'
          Set.pi (s : Set ℤ) t =
        Set.pi (s1 : Set ℤ) t ×ˢ Set.pi (s2 : Set ℤ) t := by
    ext pair
    change
      (∀ j : ℤ, j ∈ s →
        (if (h : ℤ) < j then pair.2 j else pair.1 j) ∈ t j) ↔
      ((∀ j : ℤ, j ∈ s1 → pair.1 j ∈ t j) ∧
        (∀ j : ℤ, j ∈ s2 → pair.2 j ∈ t j))
    constructor
    · intro hmem
      constructor
      · intro j hj
        have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
        have hjh : ¬ (h : ℤ) < j := (Finset.mem_filter.mp hj).2
        simpa only [ite_eq_right hjh] using hmem j hjs
      · intro j hj
        have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
        have hjh : (h : ℤ) < j := (Finset.mem_filter.mp hj).2
        simpa only [ite_eq_left hjh] using hmem j hjs
    · rintro ⟨h1, h2⟩ j hjs
      by_cases hjh : (h : ℤ) < j
      · have hj2 : j ∈ s2 := Finset.mem_filter.mpr ⟨hjs, hjh⟩
        simpa only [ite_eq_left hjh] using h2 j hj2
      · have hj1 : j ∈ s1 := Finset.mem_filter.mpr ⟨hjs, hjh⟩
        simpa only [ite_eq_right hjh] using h1 j hj1
  have hdisj : Disjoint s1 s2 := by
    apply Finset.disjoint_left.mpr
    intro j hj1 hj2
    exact (Finset.mem_filter.mp hj1).2 (Finset.mem_filter.mp hj2).2
  have hunion : s1 ∪ s2 = s := by
    ext j
    simp only [Finset.mem_union, s1, s2, Finset.mem_filter]
    constructor
    · rintro (⟨hjs, _⟩ | ⟨hjs, _⟩) <;> exact hjs
    · intro hjs
      by_cases hjh : (h : ℤ) < j
      · exact Or.inr ⟨hjs, hjh⟩
      · exact Or.inl ⟨hjs, hjh⟩
  have hbox : MeasurableSet (Set.pi (s : Set ℤ) t) :=
    MeasurableSet.pi s.countable_toSet (fun j _hj => ht j)
  rw [Measure.map_apply
      (aux_prop_16_coarse_block_neumann_copy_measurable h) hbox,
    hpre, Measure.prod_prod,
    Measure.infinitePi_pi mu (s := s1) (fun j _hj => ht j),
    Measure.infinitePi_pi mu (s := s2) (fun j _hj => ht j)]
  rw [← Finset.prod_union hdisj, hunion]

theorem aux_prop_16_coarse_block_neumann_copy_nonpos
    {E : Type*} (h : ℕ) (pair : (ℤ → E) × (ℤ → E)) (j : ℤ) (hj : j ≤ 0) :
    aux_prop_16_coarse_block_neumann_copy h pair j = pair.1 j := by
  have hjh : ¬ (h : ℤ) < j :=
    not_lt_of_ge (le_trans hj (Int.natCast_nonneg h))
  exact ite_eq_right hjh

theorem aux_prop_16_coarse_block_neumann_copy_le
    {E : Type*} (h : ℕ) (pair : (ℤ → E) × (ℤ → E)) (j : ℤ) (hj : j ≤ (h : ℤ)) :
    aux_prop_16_coarse_block_neumann_copy h pair j = pair.1 j := by
  have hjh : ¬ (h : ℤ) < j := not_lt.mpr hj
  exact ite_eq_right hjh

theorem aux_prop_16_coarse_block_neumann_copy_tail
    {E : Type*} (h : ℕ) (pair : (ℤ → E) × (ℤ → E)) (n : ℕ) (hn : h ≤ n) :
    aux_prop_16_coarse_block_neumann_copy h pair (Int.ofNat (n + 1)) =
      pair.2 (Int.ofNat (n + 1)) := by
  have hjh : (h : ℤ) < (Int.ofNat (n + 1)) := by
    simp only [Int.ofNat_eq_natCast]
    exact_mod_cast Nat.lt_succ_of_le hn
  exact ite_eq_left hjh



theorem aux_prop_16_coarse_block_neumann_layer_tail
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (K : Compacts (SpatialCoordinates d)) :
    ∃ CK : ℝ, 0 ≤ CK ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d), 0 ≤ M.delta →
      (∀ᵐ beta : BilateralField d ∂(chaosSampleLaw M).toMeasure,
        Summable (fun n : ℕ => ‖(beta (Int.ofNat (n + 1))).restrict
            (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((beta (Int.ofNat (n + 1))) 0)‖)) ∧
      ∀ p : ℝ≥0∞, 2 ≤ p → p ≠ (⊤ : ℝ≥0∞) → ∀ h : ℕ,
        MemLp (fun beta : BilateralField d =>
            ∑' n : ℕ, ‖(beta (Int.ofNat (n + h + 1))).restrict
                (K : Set (SpatialCoordinates d)) -
              ContinuousMap.const K ((beta (Int.ofNat (n + h + 1))) 0)‖)
          p (chaosSampleLaw M).toMeasure ∧
        eLpNorm (fun beta : BilateralField d =>
            ∑' n : ℕ, ‖(beta (Int.ofNat (n + h + 1))).restrict
                (K : Set (SpatialCoordinates d)) -
              ContinuousMap.const K ((beta (Int.ofNat (n + h + 1))) 0)‖)
          p (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (CK * M.delta * Real.sqrt p.toReal * (3 : ℝ) ^ (-(h : ℝ))) := by
  classical
  obtain ⟨C, _hCnonneg, hCM⟩ := _root_.SubdiffusiveProcess.Paper.lem_infrared hd
  have hCK : 0 ≤ C K := _hCnonneg K
  refine ⟨C K / 2, by linarith, ?_⟩
  intro M hdelta
  let μ0 : Measure (NativeBilateralPotentialSample d) :=
    Measure.infinitePi (fun _ : ℤ =>
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
  obtain ⟨Hn, _hHnmeas, _hHnCont, _hHnLimAE, hLpLayer, _hLpAll⟩ := hCM M μ0 rfl
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let π : NativeBilateralPotentialSample d → BilateralField d :=
    fun omega j => layerScaling d j (forget (omega j))
  have hπmeasure : Measure.map π μ0 = (chaosSampleLaw M).toMeasure := by
    simpa only [chaosSampleLaw, chaosRootFieldLaw, μ0, π, Function.comp_apply] using
      (measurePreserving_nativeCopies_commonScaleLaw M).map_eq
  have hπmeas : Measurable π := by
    apply Measurable.of_eval
    intro j
    exact (layerScaling d j).continuous.measurable.comp
      (forget.continuous.measurable.comp (measurable_pi_apply j))
  have hMP : MeasurePreserving π μ0 (chaosSampleLaw M).toMeasure := ⟨hπmeas, hπmeasure⟩
  let G : ℕ → BilateralField d → ℝ := fun n beta =>
    ‖(beta (Int.ofNat (n + 1))).restrict (K : Set (SpatialCoordinates d)) -
      ContinuousMap.const K ((beta (Int.ofNat (n + 1))) 0)‖
  have hπ : ∀ omega n,
      forget (positiveScaledNativeLayer omega n) = π omega (Int.ofNat (n + 1)) := by
    intro omega n
    ext x
    change omega (n + 1) ((3 : ℝ) ^ (-(n + 1 : ℤ)) • x) =
      omega (Int.ofNat (n + 1)) ((3 : ℝ) ^ (-Int.ofNat (n + 1)) • x)
    congr 1
  have hGcont : ∀ n : ℕ, Continuous (G n) := by
    intro n
    have h1 : Continuous (fun beta : BilateralField d =>
        (beta (Int.ofNat (n + 1))).restrict (K : Set (SpatialCoordinates d))) :=
      (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).comp
        (continuous_apply (Int.ofNat (n + 1)))
    have h2 : Continuous (fun beta : BilateralField d =>
        ContinuousMap.const K ((beta (Int.ofNat (n + 1))) 0)) := by
      have : Continuous (fun beta : BilateralField d => (beta (Int.ofNat (n + 1))) 0) :=
        (continuous_eval_const (0 : SpatialCoordinates d)).comp
          (continuous_apply (Int.ofNat (n + 1)))
      simpa only [Function.comp_def] using
        (ContinuousMap.continuous_const' (X := K) (Y := ℝ)).comp this
    exact continuous_norm.comp (h1.sub h2)
  have hGmeas : ∀ n : ℕ, Measurable (G n) := fun n => (hGcont n).measurable
  have hGpi : ∀ n omega, G n (π omega) ≤
      compactPotentialC1Norm K
        (_root_.SubdiffusiveProcess.Model.PotentialField.anchor (positiveScaledNativeLayer omega n)) := by
    intro n omega
    have hAeq : (π omega (Int.ofNat (n + 1))).restrict (K : Set (SpatialCoordinates d)) -
        ContinuousMap.const K ((π omega (Int.ofNat (n + 1))) 0) =
        (⟨fun z : K => (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
              (positiveScaledNativeLayer omega n)) z.1,
            (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
              (positiveScaledNativeLayer omega n)).1.1.continuous.comp
              continuous_subtype_val⟩ :
          C(K, ℝ)) := by
      apply ContinuousMap.ext
      intro x
      show (π omega (Int.ofNat (n + 1))) (x : SpatialCoordinates d) -
          (π omega (Int.ofNat (n + 1))) 0 = _
      rw [← hπ omega n]
      show (forget (positiveScaledNativeLayer omega n)) (x : SpatialCoordinates d) -
          (forget (positiveScaledNativeLayer omega n)) 0 = _
      show (positiveScaledNativeLayer omega n) (x : SpatialCoordinates d) -
          (positiveScaledNativeLayer omega n) 0 =
          (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
            (positiveScaledNativeLayer omega n)) (x : SpatialCoordinates d)
      rw [_root_.SubdiffusiveProcess.Model.PotentialField.anchor_apply]
    show ‖(π omega (Int.ofNat (n + 1))).restrict (K : Set (SpatialCoordinates d)) -
        ContinuousMap.const K ((π omega (Int.ofNat (n + 1))) 0)‖ ≤ _
    rw [hAeq]
    unfold compactPotentialC1Norm
    exact le_add_of_nonneg_right (by positivity)
  have hGbound : ∀ p : ℝ≥0∞, 2 ≤ p → p ≠ (⊤ : ℝ≥0∞) → ∀ n : ℕ,
      eLpNorm (G n) p (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (C K * M.delta * Real.sqrt p.toReal * (3 : ℝ) ^ (-((n : ℤ) + 1))) := by
    intro p hp2 hpt n
    have hcomp : eLpNorm (G n ∘ π) p μ0 = eLpNorm (G n) p (chaosSampleLaw M).toMeasure :=
      eLpNorm_comp_measurePreserving (hGmeas n).aestronglyMeasurable hMP
    rw [← hcomp]
    calc eLpNorm (G n ∘ π) p μ0
        ≤ eLpNorm (fun omega => compactPotentialC1Norm K
            (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
              (positiveScaledNativeLayer omega n))) p μ0 := by
          apply eLpNorm_mono_ae ((hGmeas n).comp hMP.measurable).aestronglyMeasurable
          filter_upwards with omega
          have h1 : 0 ≤ (G n ∘ π) omega := norm_nonneg _
          have h2 : 0 ≤ compactPotentialC1Norm K (_root_.SubdiffusiveProcess.Model.PotentialField.anchor
              (positiveScaledNativeLayer omega n)) := by
            unfold compactPotentialC1Norm; positivity
          rw [Real.norm_eq_abs, abs_of_nonneg h1, Real.norm_eq_abs, abs_of_nonneg h2]
          exact hGpi n omega
      _ ≤ _ := hLpLayer K p hp2 hpt n
  have hGmem : ∀ p : ℝ≥0∞, 2 ≤ p → p ≠ (⊤ : ℝ≥0∞) → ∀ n : ℕ,
      MemLp (G n) p (chaosSampleLaw M).toMeasure := by
    intro p hp2 hpt n
    exact lt_of_le_of_lt (hGbound p hp2 hpt n) ENNReal.ofReal_lt_top
  have hexp : ∀ n : ℕ,
      (3 : ℝ) ^ (-((n : ℤ) + 1)) = (1 / 3 : ℝ) ^ (n + 1) := by
    intro n
    have hcast : (-((n : ℤ) + 1)) = -(((n + 1 : ℕ) : ℤ)) := by push_cast; ring
    rw [hcast, zpow_neg, zpow_natCast, ← inv_pow, one_div]
  have hbound : ∀ p : ℝ≥0∞, 2 ≤ p → p ≠ (⊤ : ℝ≥0∞) → ∀ n : ℕ,
      eLpNorm (G n) p (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((C K * M.delta * Real.sqrt p.toReal / 3) * (1 / 3 : ℝ) ^ n) := by
    intro p hp2 hpt n
    have := hGbound p hp2 hpt n
    rw [hexp n, pow_succ'] at this
    convert this using 2
    ring
  refine ⟨?_, ?_⟩
  · obtain ⟨hSummable, _hTail⟩ := memLp_geometric_tsum_tails
      (μ := (chaosSampleLaw M).toMeasure) (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) G (hGmem 2 (by norm_num) (by norm_num))
      (B := C K * M.delta * Real.sqrt (2 : ℝ≥0∞).toReal / 3) (r := 1 / 3)
      (by positivity) (by norm_num) (by norm_num) (hbound 2 (by norm_num) (by norm_num))
    have hGnn : ∀ (n : ℕ) (x : BilateralField d), ‖G n x‖ = G n x :=
      fun n x => Real.norm_of_nonneg (norm_nonneg _)
    simpa only [hGnn] using hSummable
  · intro p hp2 hpt h
    obtain ⟨_hSummable, hTail⟩ := memLp_geometric_tsum_tails
      (μ := (chaosSampleLaw M).toMeasure) (p := p)
      (le_trans (by norm_num) hp2) hpt G (hGmem p hp2 hpt)
      (B := C K * M.delta * Real.sqrt p.toReal / 3) (r := 1 / 3)
      (by positivity) (by norm_num) (by norm_num) (hbound p hp2 hpt)
    refine ⟨(hTail h).1, ?_⟩
    have hrw : (fun beta : BilateralField d =>
        ∑' n : ℕ, ‖(beta (Int.ofNat (n + h + 1))).restrict
            (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((beta (Int.ofNat (n + h + 1))) 0)‖) =
        (fun beta : BilateralField d => ∑' n : ℕ, G (n + h) beta) := by
      funext beta
      congr 1
    rw [hrw]
    refine (hTail h).2.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    have hrpow : (3 : ℝ) ^ (-(h : ℝ)) = (1 / 3 : ℝ) ^ h := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3), Real.rpow_natCast, one_div, inv_pow]
    rw [hrpow]
    ring



/-- Pointwise (a.e.) bound of the infrared field's coarse-block difference by the two-sided
tail of layer norms, isolated as its own declaration so that its substantial elaboration cost
does not accumulate against the main theorem's heartbeat budget. -/
theorem aux_prop_16_coarse_block_neumann_Hdiff_le
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (hMdelta0 : 0 ≤ M.delta)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hInfrared : InfraredCharacterization M H)
    (K : Compacts (SpatialCoordinates d)) (h : ℕ) :
    ∀ᵐ pair : BilateralField d × BilateralField d ∂
        (((chaosSampleLaw M).toMeasure).prod ((chaosSampleLaw M).toMeasure)), ∀ x : K,
      |H pair.1 (x : SpatialCoordinates d) -
          H (aux_prop_16_coarse_block_neumann_copy h pair) (x : SpatialCoordinates d)| ≤
        (∑' n : ℕ, ‖(pair.1 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((pair.1 (Int.ofNat (n + h + 1))) 0)‖) +
        (∑' n : ℕ, ‖(pair.2 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((pair.2 (Int.ofNat (n + h + 1))) 0)‖) := by
  classical
  set P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure with hPdef
  obtain ⟨_, _, hCKbound⟩ := aux_prop_16_coarse_block_neumann_layer_tail hd K
  obtain ⟨hSummableM, _⟩ := hCKbound M hMdelta0
  have hPinf : P = Measure.infinitePi
      (fun j : ℤ => (scaledLayerLaw d (chaosRootFieldLaw M) j :
        Measure C(SpatialCoordinates d, ℝ))) := rfl
  have hcopyMP : MeasurePreserving (aux_prop_16_coarse_block_neumann_copy h) (P.prod P) P := by
    rw [hPinf]
    exact aux_prop_16_coarse_block_neumann_copy_infinitePi _ h
  have hInfraredAE : ∀ᵐ beta ∂P, Tendsto (infraredPartialSum beta) atTop (nhds (H beta)) :=
    hInfrared.2
  have hTendsto1 : ∀ᵐ pair : BilateralField d × BilateralField d ∂(P.prod P),
      Tendsto (infraredPartialSum pair.1) atTop (nhds (H pair.1)) :=
    (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae hInfraredAE
  have hTendsto2 : ∀ᵐ pair : BilateralField d × BilateralField d ∂(P.prod P),
      Tendsto (infraredPartialSum (aux_prop_16_coarse_block_neumann_copy h pair)) atTop
        (nhds (H (aux_prop_16_coarse_block_neumann_copy h pair))) :=
    hcopyMP.quasiMeasurePreserving.ae hInfraredAE
  have hSum1 : ∀ᵐ pair : BilateralField d × BilateralField d ∂(P.prod P),
      Summable (fun n : ℕ => ‖(pair.1 (Int.ofNat (n + 1))).restrict
          (K : Set (SpatialCoordinates d)) -
        ContinuousMap.const K ((pair.1 (Int.ofNat (n + 1))) 0)‖) :=
    (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae hSummableM
  have hSum2 : ∀ᵐ pair : BilateralField d × BilateralField d ∂(P.prod P),
      Summable (fun n : ℕ => ‖(pair.2 (Int.ofNat (n + 1))).restrict
          (K : Set (SpatialCoordinates d)) -
        ContinuousMap.const K ((pair.2 (Int.ofNat (n + 1))) 0)‖) :=
    (measurePreserving_snd (μ := P) (ν := P)).quasiMeasurePreserving.ae hSummableM
  have hIPS_succ : ∀ (omega : BilateralField d) (L : ℕ),
      infraredPartialSum omega (L + 1) = infraredPartialSum omega L +
        (omega (Int.ofNat (L + 1)) - ContinuousMap.const _ (omega (Int.ofNat (L + 1)) 0)) := by
    intro omega L
    unfold infraredPartialSum
    exact Finset.sum_range_succ _ _
  have hIPS_apply : ∀ (omega : BilateralField d) (L : ℕ) (x : SpatialCoordinates d),
      infraredPartialSum omega L x =
        ∑ n ∈ Finset.range L, (omega (Int.ofNat (n + 1)) x - omega (Int.ofNat (n + 1)) 0) := by
    intro omega L x
    induction L with
    | zero => simp [infraredPartialSum]
    | succ L ih =>
        simp only [hIPS_succ, ContinuousMap.add_apply, ContinuousMap.sub_apply,
          ContinuousMap.const_apply, ih, Finset.sum_range_succ]
  have hHdiff_le : ∀ᵐ pair : BilateralField d × BilateralField d ∂(P.prod P), ∀ x : K,
      |H pair.1 (x : SpatialCoordinates d) -
          H (aux_prop_16_coarse_block_neumann_copy h pair) (x : SpatialCoordinates d)| ≤
        (∑' n : ℕ, ‖(pair.1 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((pair.1 (Int.ofNat (n + h + 1))) 0)‖) +
        (∑' n : ℕ, ‖(pair.2 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((pair.2 (Int.ofNat (n + h + 1))) 0)‖) := by
    filter_upwards [hTendsto1, hTendsto2, hSum1, hSum2] with pair ht1 ht2 hs1 hs2 x
    set f1 : ℕ → ℝ := fun n => ‖(pair.1 (Int.ofNat (n + 1))).restrict
        (K : Set (SpatialCoordinates d)) -
      ContinuousMap.const K ((pair.1 (Int.ofNat (n + 1))) 0)‖ with hf1def
    set f2 : ℕ → ℝ := fun n => ‖(pair.2 (Int.ofNat (n + 1))).restrict
        (K : Set (SpatialCoordinates d)) -
      ContinuousMap.const K ((pair.2 (Int.ofNat (n + 1))) 0)‖ with hf2def
    have hs1' : Summable (fun n : ℕ => f1 (n + h)) := (summable_nat_add_iff h).mpr hs1
    have hs2' : Summable (fun n : ℕ => f2 (n + h)) := (summable_nat_add_iff h).mpr hs2
    have hbdd : ∀ L : ℕ, h ≤ L →
        |infraredPartialSum pair.1 L (x : SpatialCoordinates d) -
          infraredPartialSum (aux_prop_16_coarse_block_neumann_copy h pair) L
            (x : SpatialCoordinates d)| ≤
        (∑' n : ℕ, f1 (n + h)) + (∑' n : ℕ, f2 (n + h)) := by
      intro L hL
      obtain ⟨m, hm⟩ : ∃ m, L = h + m := ⟨L - h, by omega⟩
      have hrepr1 : infraredPartialSum pair.1 L (x : SpatialCoordinates d) =
          (∑ n ∈ Finset.range h,
            (pair.1 (Int.ofNat (n + 1)) (x : SpatialCoordinates d) - pair.1 (Int.ofNat (n + 1)) 0)) +
          ∑ n ∈ Finset.range m,
            (pair.1 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
              pair.1 (Int.ofNat (h + n + 1)) 0) := by
        rw [hIPS_apply, hm, Finset.sum_range_add]
      have hrepr2 : infraredPartialSum (aux_prop_16_coarse_block_neumann_copy h pair) L
          (x : SpatialCoordinates d) =
          (∑ n ∈ Finset.range h,
            (pair.1 (Int.ofNat (n + 1)) (x : SpatialCoordinates d) - pair.1 (Int.ofNat (n + 1)) 0)) +
          ∑ n ∈ Finset.range m,
            (pair.2 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
              pair.2 (Int.ofNat (h + n + 1)) 0) := by
        rw [hIPS_apply, hm, Finset.sum_range_add]
        congr 1
        · apply Finset.sum_congr rfl
          intro n hn
          have hnh : n + 1 ≤ h := by
            have := Finset.mem_range.mp hn; omega
          rw [aux_prop_16_coarse_block_neumann_copy_le h pair (Int.ofNat (n + 1))
            (by show (n : ℤ) + 1 ≤ (h : ℤ); exact_mod_cast hnh)]
        · apply Finset.sum_congr rfl
          intro n _hn
          rw [aux_prop_16_coarse_block_neumann_copy_tail h pair (h + n) (by omega)]
      have hval : infraredPartialSum pair.1 L (x : SpatialCoordinates d) -
          infraredPartialSum (aux_prop_16_coarse_block_neumann_copy h pair) L
            (x : SpatialCoordinates d) =
          ∑ n ∈ Finset.range m,
            ((pair.1 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
                pair.1 (Int.ofNat (h + n + 1)) 0) -
              (pair.2 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
                pair.2 (Int.ofNat (h + n + 1)) 0)) := by
        have hexpand : ∑ n ∈ Finset.range m,
            ((pair.1 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
                pair.1 (Int.ofNat (h + n + 1)) 0) -
              (pair.2 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
                pair.2 (Int.ofNat (h + n + 1)) 0)) =
            (∑ n ∈ Finset.range m,
              (pair.1 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
                pair.1 (Int.ofNat (h + n + 1)) 0)) -
            (∑ n ∈ Finset.range m,
              (pair.2 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
                pair.2 (Int.ofNat (h + n + 1)) 0)) :=
          Finset.sum_sub_distrib
            (fun n => pair.1 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
              pair.1 (Int.ofNat (h + n + 1)) 0)
            (fun n => pair.2 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
              pair.2 (Int.ofNat (h + n + 1)) 0)
        rw [hrepr1, hrepr2, hexpand]
        abel
      rw [hval]
      have hterm : ∀ n ∈ Finset.range m,
          ‖(pair.1 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
              pair.1 (Int.ofNat (h + n + 1)) 0) -
            (pair.2 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
              pair.2 (Int.ofNat (h + n + 1)) 0)‖ ≤ f1 (n + h) + f2 (n + h) := by
        intro n _hn
        have e1 : (pair.1 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
            pair.1 (Int.ofNat (h + n + 1)) 0) =
            ((pair.1 (Int.ofNat (h + n + 1))).restrict (K : Set (SpatialCoordinates d)) -
              ContinuousMap.const K (pair.1 (Int.ofNat (h + n + 1)) 0)) x := rfl
        have e2 : (pair.2 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
            pair.2 (Int.ofNat (h + n + 1)) 0) =
            ((pair.2 (Int.ofNat (h + n + 1))).restrict (K : Set (SpatialCoordinates d)) -
              ContinuousMap.const K (pair.2 (Int.ofNat (h + n + 1)) 0)) x := rfl
        have hb1 : ‖(pair.1 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
            pair.1 (Int.ofNat (h + n + 1)) 0)‖ ≤ f1 (n + h) := by
          rw [e1, hf1def]
          have hle := ContinuousMap.norm_coe_le_norm
            ((pair.1 (Int.ofNat (h + n + 1))).restrict (K : Set (SpatialCoordinates d)) -
              ContinuousMap.const K (pair.1 (Int.ofNat (h + n + 1)) 0)) x
          rwa [show h + n + 1 = n + h + 1 by ring, show n + h = h + n from by ring]
        have hb2 : ‖(pair.2 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
            pair.2 (Int.ofNat (h + n + 1)) 0)‖ ≤ f2 (n + h) := by
          rw [e2, hf2def]
          have hle := ContinuousMap.norm_coe_le_norm
            ((pair.2 (Int.ofNat (h + n + 1))).restrict (K : Set (SpatialCoordinates d)) -
              ContinuousMap.const K (pair.2 (Int.ofNat (h + n + 1)) 0)) x
          rwa [show h + n + 1 = n + h + 1 by ring, show n + h = h + n from by ring]
        calc ‖(pair.1 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
              pair.1 (Int.ofNat (h + n + 1)) 0) -
            (pair.2 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
              pair.2 (Int.ofNat (h + n + 1)) 0)‖
            ≤ ‖(pair.1 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
                pair.1 (Int.ofNat (h + n + 1)) 0)‖ +
              ‖(pair.2 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
                pair.2 (Int.ofNat (h + n + 1)) 0)‖ := norm_sub_le _ _
          _ ≤ f1 (n + h) + f2 (n + h) := add_le_add hb1 hb2
      calc |∑ n ∈ Finset.range m,
            ((pair.1 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
                pair.1 (Int.ofNat (h + n + 1)) 0) -
              (pair.2 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
                pair.2 (Int.ofNat (h + n + 1)) 0))|
          ≤ ∑ n ∈ Finset.range m,
              ‖(pair.1 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
                  pair.1 (Int.ofNat (h + n + 1)) 0) -
                (pair.2 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
                  pair.2 (Int.ofNat (h + n + 1)) 0)‖ :=
            Finset.abs_sum_le_sum_abs (fun n =>
              (pair.1 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
                  pair.1 (Int.ofNat (h + n + 1)) 0) -
                (pair.2 (Int.ofNat (h + n + 1)) (x : SpatialCoordinates d) -
                  pair.2 (Int.ofNat (h + n + 1)) 0)) (Finset.range m)
        _ ≤ ∑ n ∈ Finset.range m, (f1 (n + h) + f2 (n + h)) := Finset.sum_le_sum hterm
        _ ≤ (∑' n : ℕ, f1 (n + h)) + (∑' n : ℕ, f2 (n + h)) := by
            rw [Finset.sum_add_distrib]
            exact add_le_add
              (hs1'.sum_le_tsum (Finset.range m) (fun n _ => norm_nonneg _))
              (hs2'.sum_le_tsum (Finset.range m) (fun n _ => norm_nonneg _))
    have htendsto : Tendsto
        (fun L : ℕ => infraredPartialSum pair.1 L (x : SpatialCoordinates d) -
          infraredPartialSum (aux_prop_16_coarse_block_neumann_copy h pair) L
            (x : SpatialCoordinates d))
        atTop (nhds (H pair.1 (x : SpatialCoordinates d) -
          H (aux_prop_16_coarse_block_neumann_copy h pair) (x : SpatialCoordinates d))) := by
      have h1 : Tendsto (fun L => infraredPartialSum pair.1 L (x : SpatialCoordinates d))
          atTop (nhds (H pair.1 (x : SpatialCoordinates d))) :=
        ((continuous_eval_const (x : SpatialCoordinates d)).continuousAt.tendsto).comp
          ht1
      have h2 : Tendsto (fun L =>
          infraredPartialSum (aux_prop_16_coarse_block_neumann_copy h pair) L
            (x : SpatialCoordinates d)) atTop
          (nhds (H (aux_prop_16_coarse_block_neumann_copy h pair) (x : SpatialCoordinates d))) :=
        ((continuous_eval_const (x : SpatialCoordinates d)).continuousAt.tendsto).comp
          ht2
      exact h1.sub h2
    have hcont : Continuous (fun r : ℝ => |r|) := continuous_abs
    have htendsto2 : Tendsto
        (fun L : ℕ => |infraredPartialSum pair.1 L (x : SpatialCoordinates d) -
          infraredPartialSum (aux_prop_16_coarse_block_neumann_copy h pair) L
            (x : SpatialCoordinates d)|)
        atTop (nhds |H pair.1 (x : SpatialCoordinates d) -
          H (aux_prop_16_coarse_block_neumann_copy h pair) (x : SpatialCoordinates d)|) :=
      (hcont.continuousAt).tendsto.comp htendsto
    refine le_of_tendsto' htendsto2 (fun L => ?_)
    rcases le_or_gt h L with hL | hL
    · exact hbdd L hL
    · have heq0 : infraredPartialSum pair.1 L (x : SpatialCoordinates d) -
          infraredPartialSum (aux_prop_16_coarse_block_neumann_copy h pair) L
            (x : SpatialCoordinates d) = 0 := by
        have heq : infraredPartialSum (aux_prop_16_coarse_block_neumann_copy h pair) L
            (x : SpatialCoordinates d) = infraredPartialSum pair.1 L (x : SpatialCoordinates d) := by
          rw [hIPS_apply, hIPS_apply]
          apply Finset.sum_congr rfl
          intro n hn
          have hnh : n + 1 ≤ h := by
            have := Finset.mem_range.mp hn; omega
          rw [aux_prop_16_coarse_block_neumann_copy_le h pair (Int.ofNat (n + 1))
            (by show (n : ℤ) + 1 ≤ (h : ℤ); exact_mod_cast hnh)]
        rw [heq]; ring
      rw [heq0, abs_zero]
      positivity
  exact hHdiff_le


/-- The two-sided coarse tail has `eLpNorm` at any admissible even order controlled by
`CK`, isolated to keep the main theorem's elaboration within budget. -/
theorem aux_prop_16_coarse_block_neumann_Tbound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (hMdelta0 : 0 ≤ M.delta)
    (K : Compacts (SpatialCoordinates d)) (CK : ℝ) (hCKnonneg : 0 ≤ CK)
    (hCKbound : ∀ (M' : _root_.SubdiffusiveProcess.Model.GMCModel d), 0 ≤ M'.delta →
      (∀ᵐ beta : BilateralField d ∂(chaosSampleLaw M').toMeasure,
        Summable (fun n : ℕ => ‖(beta (Int.ofNat (n + 1))).restrict
            (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((beta (Int.ofNat (n + 1))) 0)‖)) ∧
      ∀ p : ℝ≥0∞, 2 ≤ p → p ≠ (⊤ : ℝ≥0∞) → ∀ h : ℕ,
        MemLp (fun beta : BilateralField d =>
            ∑' n : ℕ, ‖(beta (Int.ofNat (n + h + 1))).restrict
                (K : Set (SpatialCoordinates d)) -
              ContinuousMap.const K ((beta (Int.ofNat (n + h + 1))) 0)‖)
          p (chaosSampleLaw M').toMeasure ∧
        eLpNorm (fun beta : BilateralField d =>
            ∑' n : ℕ, ‖(beta (Int.ofNat (n + h + 1))).restrict
                (K : Set (SpatialCoordinates d)) -
              ContinuousMap.const K ((beta (Int.ofNat (n + h + 1))) 0)‖)
          p (chaosSampleLaw M').toMeasure ≤
        ENNReal.ofReal (CK * M'.delta * Real.sqrt p.toReal * (3 : ℝ) ^ (-(h : ℝ))))
    (h : ℕ) (p : ℝ) (hp : 2 ≤ p) :
    let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
    AEStronglyMeasurable (fun pair : BilateralField d × BilateralField d =>
        (∑' n : ℕ, ‖(pair.1 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((pair.1 (Int.ofNat (n + h + 1))) 0)‖) +
        (∑' n : ℕ, ‖(pair.2 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((pair.2 (Int.ofNat (n + h + 1))) 0)‖)) (P.prod P) ∧
    eLpNorm (fun pair : BilateralField d × BilateralField d =>
        (∑' n : ℕ, ‖(pair.1 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((pair.1 (Int.ofNat (n + h + 1))) 0)‖) +
        (∑' n : ℕ, ‖(pair.2 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((pair.2 (Int.ofNat (n + h + 1))) 0)‖))
      (ENNReal.ofReal (4 * p)) (P.prod P) ≤
    ENNReal.ofReal (2 * CK * M.delta * Real.sqrt (4 * p) * (3 : ℝ) ^ (-(h : ℝ))) := by
  intro P
  have h4p2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (4 * p) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have h4pt : ENNReal.ofReal (4 * p) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have h4ptoReal : (ENNReal.ofReal (4 * p)).toReal = 4 * p := ENNReal.toReal_ofReal (by linarith)
  have hb := (hCKbound M hMdelta0).2 (ENNReal.ofReal (4 * p)) h4p2 h4pt h
  rw [h4ptoReal] at hb
  have hle1 : eLpNorm (fun pair : BilateralField d × BilateralField d =>
      ∑' n : ℕ, ‖(pair.1 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
        ContinuousMap.const K ((pair.1 (Int.ofNat (n + h + 1))) 0)‖)
      (ENNReal.ofReal (4 * p)) (P.prod P) ≤
      ENNReal.ofReal (CK * M.delta * Real.sqrt (4 * p) * (3 : ℝ) ^ (-(h : ℝ))) := by
    rw [show (fun pair : BilateralField d × BilateralField d =>
        ∑' n : ℕ, ‖(pair.1 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((pair.1 (Int.ofNat (n + h + 1))) 0)‖) =
        (fun beta : BilateralField d => ∑' n : ℕ, ‖(beta (Int.ofNat (n + h + 1))).restrict
            (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((beta (Int.ofNat (n + h + 1))) 0)‖) ∘ Prod.fst from rfl,
      eLpNorm_comp_measurePreserving hb.1.aestronglyMeasurable
        (measurePreserving_fst (μ := P) (ν := P))]
    exact hb.2
  have hle2 : eLpNorm (fun pair : BilateralField d × BilateralField d =>
      ∑' n : ℕ, ‖(pair.2 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
        ContinuousMap.const K ((pair.2 (Int.ofNat (n + h + 1))) 0)‖)
      (ENNReal.ofReal (4 * p)) (P.prod P) ≤
      ENNReal.ofReal (CK * M.delta * Real.sqrt (4 * p) * (3 : ℝ) ^ (-(h : ℝ))) := by
    rw [show (fun pair : BilateralField d × BilateralField d =>
        ∑' n : ℕ, ‖(pair.2 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((pair.2 (Int.ofNat (n + h + 1))) 0)‖) =
        (fun beta : BilateralField d => ∑' n : ℕ, ‖(beta (Int.ofNat (n + h + 1))).restrict
            (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((beta (Int.ofNat (n + h + 1))) 0)‖) ∘ Prod.snd from rfl,
      eLpNorm_comp_measurePreserving hb.1.aestronglyMeasurable
        (measurePreserving_snd (μ := P) (ν := P))]
    exact hb.2
  have hm1 : AEStronglyMeasurable (fun pair : BilateralField d × BilateralField d =>
      ∑' n : ℕ, ‖(pair.1 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
        ContinuousMap.const K ((pair.1 (Int.ofNat (n + h + 1))) 0)‖) (P.prod P) :=
    hb.1.aestronglyMeasurable.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))
  have hm2 : AEStronglyMeasurable (fun pair : BilateralField d × BilateralField d =>
      ∑' n : ℕ, ‖(pair.2 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
        ContinuousMap.const K ((pair.2 (Int.ofNat (n + h + 1))) 0)‖) (P.prod P) :=
    hb.1.aestronglyMeasurable.comp_measurePreserving (measurePreserving_snd (μ := P) (ν := P))
  have h1le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (4 * p) := h4p2.trans' (by norm_num)
  refine ⟨hm1.add hm2, (eLpNorm_add_le h1le).trans ((add_le_add hle1 hle2).trans (le_of_eq ?_))⟩
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- The two-sided response-norm sum has `eLpNorm` controlled by `2B`, isolated to keep the
main theorem's elaboration within budget. -/
theorem aux_prop_16_coarse_block_neumann_Wbound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {P : Measure (BilateralField d)} [IsProbabilityMeasure P]
    (copyMap : BilateralField d × BilateralField d → BilateralField d)
    (hcopyMP : MeasurePreserving copyMap (P.prod P) P)
    (y : BilateralField d → ℝ) (p B : ℝ) (hp : 2 ≤ p) (hB : 0 ≤ B)
    (hy : MemLp y (ENNReal.ofReal (4 * p)) P ∧ eLpNorm y (ENNReal.ofReal (4 * p)) P ≤
      ENNReal.ofReal B) :
    AEStronglyMeasurable (fun pair : BilateralField d × BilateralField d =>
        |y pair.1| + |y (copyMap pair)|) (P.prod P) ∧
    eLpNorm (fun pair : BilateralField d × BilateralField d =>
        |y pair.1| + |y (copyMap pair)|) (ENNReal.ofReal (4 * p)) (P.prod P) ≤
      ENNReal.ofReal (2 * B) := by
  have h4p2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (4 * p) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have h1m : AEStronglyMeasurable (fun pair : BilateralField d × BilateralField d =>
      |y pair.1|) (P.prod P) :=
    (continuous_abs.comp_aestronglyMeasurable hy.1.aestronglyMeasurable).comp_measurePreserving
      (measurePreserving_fst (μ := P) (ν := P))
  have h2m : AEStronglyMeasurable (fun pair : BilateralField d × BilateralField d =>
      |y (copyMap pair)|) (P.prod P) :=
    (continuous_abs.comp_aestronglyMeasurable hy.1.aestronglyMeasurable).comp_measurePreserving
      hcopyMP
  have hle1 : eLpNorm (fun pair : BilateralField d × BilateralField d => |y pair.1|)
      (ENNReal.ofReal (4 * p)) (P.prod P) ≤ ENNReal.ofReal B := by
    have heq : (fun pair : BilateralField d × BilateralField d => |y pair.1|) =
        (fun x => ‖y x‖) ∘ Prod.fst := by
      funext pair; simp [Real.norm_eq_abs]
    rw [heq, eLpNorm_comp_measurePreserving hy.1.aestronglyMeasurable.norm
      (measurePreserving_fst (μ := P) (ν := P)), eLpNorm_norm y hy.1.aestronglyMeasurable]
    exact hy.2
  have hle2 : eLpNorm (fun pair : BilateralField d × BilateralField d => |y (copyMap pair)|)
      (ENNReal.ofReal (4 * p)) (P.prod P) ≤ ENNReal.ofReal B := by
    have heq : (fun pair : BilateralField d × BilateralField d => |y (copyMap pair)|) =
        (fun x => ‖y x‖) ∘ copyMap := by
      funext pair; simp [Real.norm_eq_abs]
    rw [heq, eLpNorm_comp_measurePreserving hy.1.aestronglyMeasurable.norm hcopyMP, eLpNorm_norm y hy.1.aestronglyMeasurable]
    exact hy.2
  have h1le : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (4 * p) := h4p2.trans' (by norm_num)
  refine ⟨h1m.add h2m,
    (eLpNorm_add_le h1le).trans ((add_le_add hle1 hle2).trans (le_of_eq ?_))⟩
  rw [← ENNReal.ofReal_add hB hB]
  congr 1
  ring

/-- The pointwise coarse-block response-difference bound, combining the coefficient-potential
distance estimate with `cor_14`'s response comparison. Isolated to keep the main theorem's
elaboration within budget. -/
theorem aux_prop_16_coarse_block_neumann_point
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (K : Compacts (SpatialCoordinates d))
    [Fact ((unitNeumannCube d : Set (SpatialCoordinates d)) ⊆ K)] (h : ℕ)
    (S : ResponseSpace (unitNeumannCube d)) (L0 : S.space →L[ℝ] ℝ)
    (Fomega : BilateralField d → C(K, ℝ))
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hFdiff : ∀ pair : BilateralField d × BilateralField d, ∀ x : K,
      Fomega pair.1 x - Fomega (aux_prop_16_coarse_block_neumann_copy h pair) x =
      H pair.1 (x : SpatialCoordinates d) -
        H (aux_prop_16_coarse_block_neumann_copy h pair) (x : SpatialCoordinates d))
    (y : BilateralField d → ℝ)
    (hy_eq : ∀ om : BilateralField d, y om = inverseResponse S
        (expPotentialCoefficient (compactPotentialToLp (Ω := unitNeumannCube d) K (Fomega om))) L0)
    (hInvResp : ∀ p q : Lp ℝ ∞ (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
      Real.exp (-‖p - q‖) * inverseResponse S (expPotentialCoefficient q) L0 ≤
          inverseResponse S (expPotentialCoefficient p) L0 ∧
        inverseResponse S (expPotentialCoefficient p) L0 ≤
          Real.exp ‖p - q‖ * inverseResponse S (expPotentialCoefficient q) L0)
    (hHdiff_le : ∀ᵐ pair : BilateralField d × BilateralField d ∂
        (((chaosSampleLaw M).toMeasure).prod ((chaosSampleLaw M).toMeasure)), ∀ x : K,
      |H pair.1 (x : SpatialCoordinates d) -
          H (aux_prop_16_coarse_block_neumann_copy h pair) (x : SpatialCoordinates d)| ≤
        (∑' n : ℕ, ‖(pair.1 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((pair.1 (Int.ofNat (n + h + 1))) 0)‖) +
        (∑' n : ℕ, ‖(pair.2 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((pair.2 (Int.ofNat (n + h + 1))) 0)‖)) :
    ∀ᵐ pair : BilateralField d × BilateralField d ∂
        (((chaosSampleLaw M).toMeasure).prod ((chaosSampleLaw M).toMeasure)),
      |y pair.1 - y (aux_prop_16_coarse_block_neumann_copy h pair)| ≤
        ((∑' n : ℕ, ‖(pair.1 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
            ContinuousMap.const K ((pair.1 (Int.ofNat (n + h + 1))) 0)‖) +
          (∑' n : ℕ, ‖(pair.2 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
            ContinuousMap.const K ((pair.2 (Int.ofNat (n + h + 1))) 0)‖)) *
        (|y pair.1| + |y (aux_prop_16_coarse_block_neumann_copy h pair)|) := by
  filter_upwards [hHdiff_le] with pair hpair
  have hRHSnonneg : (0 : ℝ) ≤
      (∑' n : ℕ, ‖(pair.1 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
        ContinuousMap.const K ((pair.1 (Int.ofNat (n + h + 1))) 0)‖) +
      (∑' n : ℕ, ‖(pair.2 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
        ContinuousMap.const K ((pair.2 (Int.ofNat (n + h + 1))) 0)‖) := by
    positivity
  have hsb : ‖compactPotentialToLp (Ω := unitNeumannCube d) K (Fomega pair.1) -
      compactPotentialToLp (Ω := unitNeumannCube d) K
        (Fomega (aux_prop_16_coarse_block_neumann_copy h pair))‖ ≤
      (∑' n : ℕ, ‖(pair.1 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
        ContinuousMap.const K ((pair.1 (Int.ofNat (n + h + 1))) 0)‖) +
      (∑' n : ℕ, ‖(pair.2 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
        ContinuousMap.const K ((pair.2 (Int.ofNat (n + h + 1))) 0)‖) := by
    refine (compactPotentialToLp_sub_norm_le (Ω := unitNeumannCube d) K
      (Fomega pair.1) (Fomega (aux_prop_16_coarse_block_neumann_copy h pair))).trans ?_
    rw [ContinuousMap.norm_le _ hRHSnonneg]
    intro x
    have hFx : (Fomega pair.1 - Fomega (aux_prop_16_coarse_block_neumann_copy h pair)) x =
        Fomega pair.1 x - Fomega (aux_prop_16_coarse_block_neumann_copy h pair) x := rfl
    rw [hFx, hFdiff pair x]
    exact hpair x
  rw [hy_eq, hy_eq]
  exact (aux_prop_16_coarse_block_neumann_response_diff S L0 hInvResp
    (compactPotentialToLp (Ω := unitNeumannCube d) K (Fomega pair.1))
    (compactPotentialToLp (Ω := unitNeumannCube d) K
      (Fomega (aux_prop_16_coarse_block_neumann_copy h pair)))).trans
    (mul_le_mul_of_nonneg_right hsb (add_nonneg (abs_nonneg _) (abs_nonneg _)))

/-- The `N`-th cutoff coefficient's compact-root log-potential and its exact difference against
the infrared field `H` on copied coordinates, isolated to keep the main theorem's elaboration
within budget. -/
theorem aux_prop_16_coarse_block_neumann_Fomega
    {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N h : ℕ)
    [Fact ((unitNeumannCube d : Set (SpatialCoordinates d)) ⊆
      (closedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos : Compacts (SpatialCoordinates d)))] :
    ∃ Fomega : BilateralField d → C(closedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos, ℝ),
      (∀ om : BilateralField d,
        cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos =
        expPotentialCoefficient
          (compactPotentialToLp (Ω := unitNeumannCube d)
            (closedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos) (Fomega om))) ∧
      (∀ pair : BilateralField d × BilateralField d,
        ∀ x : closedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos,
        Fomega pair.1 x - Fomega (aux_prop_16_coarse_block_neumann_copy h pair) x =
        H pair.1 (x : SpatialCoordinates d) -
          H (aux_prop_16_coarse_block_neumann_copy h pair) (x : SpatialCoordinates d)) := by
  set K : Compacts (SpatialCoordinates d) := closedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos with hKdef
  refine ⟨fun om => continuousPositiveLog
      (cutoffCoefficientCM M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
      (cutoffCoefficientCM_pos M H om N (fun _ => (1 / 2 : ℝ)) one_pos) -
      ContinuousMap.const K (Real.log 1),
    fun om => rfl, ?_⟩
  have hlogdiff : ∀ (om om' : BilateralField d) (x : SpatialCoordinates d),
      Real.log (cutoffCoefficient M H om N x) - Real.log (cutoffCoefficient M H om' N x) =
      cutoffPotential H om N x - cutoffPotential H om' N x := by
    intro om om' x
    unfold cutoffCoefficient
    rw [Real.log_mul (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne')
        (Real.exp_pos _).ne',
      Real.log_mul (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne')
        (Real.exp_pos _).ne',
      Real.log_exp, Real.log_exp]
    ring
  have hFomega_apply : ∀ (om : BilateralField d) (x : K),
      (continuousPositiveLog (cutoffCoefficientCM M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
          (cutoffCoefficientCM_pos M H om N (fun _ => (1 / 2 : ℝ)) one_pos) -
        ContinuousMap.const K (Real.log 1)) x =
      Real.log (cutoffCoefficient M H om N (x : SpatialCoordinates d)) - Real.log 1 := by
    intro om x
    show continuousPositiveLog (cutoffCoefficientCM M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
        (cutoffCoefficientCM_pos M H om N (fun _ => (1 / 2 : ℝ)) one_pos) x -
      ContinuousMap.const K (Real.log 1) x = _
    rfl
  intro pair x
  rw [hFomega_apply, hFomega_apply]
  have hld := hlogdiff pair.1 (aux_prop_16_coarse_block_neumann_copy h pair)
    (x : SpatialCoordinates d)
  have hUV : ∑ j ∈ Finset.range (N + 1), pair.1 (-(Int.ofNat j)) (x : SpatialCoordinates d) =
      ∑ j ∈ Finset.range (N + 1),
        (aux_prop_16_coarse_block_neumann_copy h pair) (-(Int.ofNat j))
          (x : SpatialCoordinates d) := by
    apply Finset.sum_congr rfl
    intro j _hj
    rw [aux_prop_16_coarse_block_neumann_copy_nonpos h pair (-(Int.ofNat j))
      (by show -(j : ℤ) ≤ 0; omega)]
  unfold cutoffPotential at hld
  rw [hUV] at hld
  linarith

/-- Hölder assembly: combine the pointwise coarse-block bound with the two tail estimates to
close the `eLpNorm` inequality. Isolated to keep `aux_prop_16_coarse_block_neumann_main`'s
elaboration within budget. -/
theorem aux_prop_16_coarse_block_neumann_assemble
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (K : Compacts (SpatialCoordinates d))
    (CK : ℝ) (hCKnonneg : 0 ≤ CK)
    (hCKbound : ∀ (M' : _root_.SubdiffusiveProcess.Model.GMCModel d), 0 ≤ M'.delta →
      (∀ᵐ beta : BilateralField d ∂(chaosSampleLaw M').toMeasure,
        Summable (fun n : ℕ => ‖(beta (Int.ofNat (n + 1))).restrict
            (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((beta (Int.ofNat (n + 1))) 0)‖)) ∧
      ∀ p : ℝ≥0∞, 2 ≤ p → p ≠ (⊤ : ℝ≥0∞) → ∀ h : ℕ,
        MemLp (fun beta : BilateralField d =>
            ∑' n : ℕ, ‖(beta (Int.ofNat (n + h + 1))).restrict
                (K : Set (SpatialCoordinates d)) -
              ContinuousMap.const K ((beta (Int.ofNat (n + h + 1))) 0)‖)
          p (chaosSampleLaw M').toMeasure ∧
        eLpNorm (fun beta : BilateralField d =>
            ∑' n : ℕ, ‖(beta (Int.ofNat (n + h + 1))).restrict
                (K : Set (SpatialCoordinates d)) -
              ContinuousMap.const K ((beta (Int.ofNat (n + h + 1))) 0)‖)
          p (chaosSampleLaw M').toMeasure ≤
        ENNReal.ofReal (CK * M'.delta * Real.sqrt p.toReal * (3 : ℝ) ^ (-(h : ℝ))))
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (hMdelta0 : 0 < M.delta)
    (h _N : ℕ) (p B : ℝ) (hp : 2 ≤ p) (hB : 0 ≤ B)
    (y : BilateralField d → ℝ)
    (hy : MemLp y (ENNReal.ofReal (4 * p)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm y (ENNReal.ofReal (4 * p)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B)
    (hcopyMP : MeasurePreserving (aux_prop_16_coarse_block_neumann_copy h)
      (((chaosSampleLaw M).toMeasure).prod ((chaosSampleLaw M).toMeasure))
      ((chaosSampleLaw M).toMeasure))
    (hpoint : ∀ᵐ pair : BilateralField d × BilateralField d ∂
        (((chaosSampleLaw M).toMeasure).prod ((chaosSampleLaw M).toMeasure)),
      |y pair.1 - y (aux_prop_16_coarse_block_neumann_copy h pair)| ≤
        ((∑' n : ℕ, ‖(pair.1 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
            ContinuousMap.const K ((pair.1 (Int.ofNat (n + h + 1))) 0)‖) +
          (∑' n : ℕ, ‖(pair.2 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
            ContinuousMap.const K ((pair.2 (Int.ofNat (n + h + 1))) 0)‖)) *
        (|y pair.1| + |y (aux_prop_16_coarse_block_neumann_copy h pair)|)) :
    eLpNorm (fun pair : BilateralField d × BilateralField d =>
        y pair.1 - y (aux_prop_16_coarse_block_neumann_copy h pair))
      (ENNReal.ofReal (2 * p))
      (((chaosSampleLaw M).toMeasure).prod ((chaosSampleLaw M).toMeasure)) ≤
    ENNReal.ofReal ((4 * (B + 1) * (CK + 1) * Real.sqrt (4 * p)) * M.delta *
      (3 : ℝ) ^ (-(h : ℝ))) := by
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let Gtail1 : BilateralField d × BilateralField d → ℝ := fun pair =>
    ∑' n : ℕ, ‖(pair.1 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
      ContinuousMap.const K ((pair.1 (Int.ofNat (n + h + 1))) 0)‖
  let Gtail2 : BilateralField d × BilateralField d → ℝ := fun pair =>
    ∑' n : ℕ, ‖(pair.2 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
      ContinuousMap.const K ((pair.2 (Int.ofNat (n + h + 1))) 0)‖
  have h4p2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (4 * p) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have h4pt : ENNReal.ofReal (4 * p) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hpoint' : ∀ᵐ pair : BilateralField d × BilateralField d ∂(P.prod P),
      ‖y pair.1 - y (aux_prop_16_coarse_block_neumann_copy h pair)‖ ≤
        ‖(Gtail1 pair + Gtail2 pair) *
          (|y pair.1| + |y (aux_prop_16_coarse_block_neumann_copy h pair)|)‖ := by
    filter_upwards [hpoint] with pair hp
    have hGnn : (0 : ℝ) ≤ Gtail1 pair + Gtail2 pair := by
      show (0 : ℝ) ≤ (∑' n : ℕ, ‖(pair.1 (Int.ofNat (n + h + 1))).restrict
          (K : Set (SpatialCoordinates d)) -
        ContinuousMap.const K ((pair.1 (Int.ofNat (n + h + 1))) 0)‖) +
        (∑' n : ℕ, ‖(pair.2 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((pair.2 (Int.ofNat (n + h + 1))) 0)‖)
      positivity
    have hWnn : (0 : ℝ) ≤ |y pair.1| + |y (aux_prop_16_coarse_block_neumann_copy h pair)| :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hGnn hWnn)]
    exact hp
  have hstep1 : eLpNorm (fun pair : BilateralField d × BilateralField d =>
        y pair.1 - y (aux_prop_16_coarse_block_neumann_copy h pair))
      (ENNReal.ofReal (2 * p)) (P.prod P) ≤
      eLpNorm (fun pair : BilateralField d × BilateralField d =>
        (Gtail1 pair + Gtail2 pair) *
          (|y pair.1| + |y (aux_prop_16_coarse_block_neumann_copy h pair)|))
      (ENNReal.ofReal (2 * p)) (P.prod P) :=
    eLpNorm_mono_ae
      ((hy.1.aestronglyMeasurable.comp_measurePreserving
        (measurePreserving_fst (μ := P) (ν := P))).sub
        (hy.1.aestronglyMeasurable.comp_measurePreserving hcopyMP)) hpoint'
  let hHT : ENNReal.HolderTriple (ENNReal.ofReal (4 * p)) (ENNReal.ofReal (4 * p))
      (ENNReal.ofReal (2 * p)) := by
    constructor
    have h4 : ENNReal.ofReal (4 * p) = 2 * ENNReal.ofReal (2 * p) := by
      rw [show (4 * p : ℝ) = 2 * (2 * p) by ring,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    rw [h4, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← add_mul,
      ENNReal.inv_two_add_inv_two, one_mul]
  have hTbound := aux_prop_16_coarse_block_neumann_Tbound M hMdelta0.le K CK hCKnonneg
    hCKbound h p hp
  have hWbound := aux_prop_16_coarse_block_neumann_Wbound (P := P)
    (aux_prop_16_coarse_block_neumann_copy h) hcopyMP y p B hp hB hy
  have hstep2raw := eLpNorm_smul_le_mul_eLpNorm (𝕜 := ℝ)
    (p := ENNReal.ofReal (4 * p)) (q := ENNReal.ofReal (4 * p)) (r := ENNReal.ofReal (2 * p))
    (f := fun pair : BilateralField d × BilateralField d =>
      |y pair.1| + |y (aux_prop_16_coarse_block_neumann_copy h pair)|)
    (φ := fun pair : BilateralField d × BilateralField d => Gtail1 pair + Gtail2 pair)
    hTbound.1 hWbound.1
  have hstep2 : eLpNorm (fun pair : BilateralField d × BilateralField d =>
        (Gtail1 pair + Gtail2 pair) *
          (|y pair.1| + |y (aux_prop_16_coarse_block_neumann_copy h pair)|))
      (ENNReal.ofReal (2 * p)) (P.prod P) ≤
      eLpNorm (fun pair : BilateralField d × BilateralField d => Gtail1 pair + Gtail2 pair)
        (ENNReal.ofReal (4 * p)) (P.prod P) *
      eLpNorm (fun pair : BilateralField d × BilateralField d =>
        |y pair.1| + |y (aux_prop_16_coarse_block_neumann_copy h pair)|)
        (ENNReal.ofReal (4 * p)) (P.prod P) := by
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply] using! hstep2raw
  refine hstep1.trans (hstep2.trans ?_)
  refine (mul_le_mul' hTbound.2 hWbound.2).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hscale : (0:ℝ) ≤ M.delta * (3:ℝ) ^ (-(h:ℝ)) := by positivity
  have hkey : 2 * CK * Real.sqrt (4 * p) * (2 * B) ≤
      4 * (B + 1) * (CK + 1) * Real.sqrt (4 * p) := by
    have hCKB : CK * B ≤ (CK + 1) * (B + 1) := by nlinarith [hCKnonneg, hB]
    have hsq : (0:ℝ) ≤ Real.sqrt (4 * p) := Real.sqrt_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hCKB hsq]
  calc 2 * CK * M.delta * Real.sqrt (4 * p) * (3 : ℝ) ^ (-(h : ℝ)) * (2 * B)
      = (2 * CK * Real.sqrt (4 * p) * (2 * B)) * (M.delta * (3:ℝ) ^ (-(h:ℝ))) := by ring
    _ ≤ (4 * (B + 1) * (CK + 1) * Real.sqrt (4 * p)) * (M.delta * (3:ℝ) ^ (-(h:ℝ))) :=
        mul_le_mul_of_nonneg_right hkey hscale
    _ = 4 * (B + 1) * (CK + 1) * Real.sqrt (4 * p) * M.delta * (3 : ℝ) ^ (-(h : ℝ)) := by ring

/-- The full per-model coarse-block estimate, isolated as its own declaration so the main
theorem only needs to fix the constant and invoke this. -/
theorem aux_prop_16_coarse_block_neumann_main
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (pvec : Fin d → ℝ)
    (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖)
    (p B : ℝ) (hp : 2 ≤ p) (hB : 0 ≤ B) :
    let K : Compacts (SpatialCoordinates d) := closedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos
    ∀ (CK : ℝ) (_hCKnonneg : 0 ≤ CK)
    (_hCKbound : ∀ (M' : _root_.SubdiffusiveProcess.Model.GMCModel d), 0 ≤ M'.delta →
      (∀ᵐ beta : BilateralField d ∂(chaosSampleLaw M').toMeasure,
        Summable (fun n : ℕ => ‖(beta (Int.ofNat (n + 1))).restrict
            (K : Set (SpatialCoordinates d)) -
          ContinuousMap.const K ((beta (Int.ofNat (n + 1))) 0)‖)) ∧
      ∀ p : ℝ≥0∞, 2 ≤ p → p ≠ (⊤ : ℝ≥0∞) → ∀ h : ℕ,
        MemLp (fun beta : BilateralField d =>
            ∑' n : ℕ, ‖(beta (Int.ofNat (n + h + 1))).restrict
                (K : Set (SpatialCoordinates d)) -
              ContinuousMap.const K ((beta (Int.ofNat (n + h + 1))) 0)‖)
          p (chaosSampleLaw M').toMeasure ∧
        eLpNorm (fun beta : BilateralField d =>
            ∑' n : ℕ, ‖(beta (Int.ofNat (n + h + 1))).restrict
                (K : Set (SpatialCoordinates d)) -
              ContinuousMap.const K ((beta (Int.ofNat (n + h + 1))) 0)‖)
          p (chaosSampleLaw M').toMeasure ≤
        ENNReal.ofReal (CK * M'.delta * Real.sqrt p.toReal * (3 : ℝ) ^ (-(h : ℝ))))
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_hMdelta0 : 0 < M.delta) (_hMdelta1 : M.delta ≤ 1)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hInfrared : InfraredCharacterization M H)
    (aN : ℕ → BilateralField d → PositiveCoefficient (unitNeumannCube d))
    (_haN_def : ∀ N om, aN N om = cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
    (yN : ℕ → BilateralField d → ℝ)
    (_hyN_def : ∀ N om, yN N om = inverseResponse (meanZeroResponseSpace hP) (aN N om)
      ((affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))))
    (_hyN : ∀ N, MemLp (yN N) (ENNReal.ofReal (4 * p)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (yN N) (ENNReal.ofReal (4 * p)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B)
    (h N : ℕ),
    eLpNorm (fun pair : BilateralField d × BilateralField d =>
        yN N pair.1 - yN N (fun j => if (h : ℤ) < j then pair.2 j else pair.1 j))
      (ENNReal.ofReal (2 * p)) (((chaosSampleLaw M).toMeasure).prod
        ((chaosSampleLaw M).toMeasure)) ≤
    ENNReal.ofReal ((4 * (B + 1) * (CK + 1) * Real.sqrt (4 * p)) * M.delta * (3 : ℝ) ^ (-(h : ℝ))) := by
  intro K CK hCKnonneg hCKbound M hMdelta0 hMdelta1 H hInfrared aN haN_def yN hyN_def hyN h N
  classical
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let zn : SpatialCoordinates d := fun _ => (1 / 2 : ℝ)
  let S := meanZeroResponseSpace hP
  let L0 : S.space →L[ℝ] ℝ :=
    (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))
  have hSubset : Fact ((unitNeumannCube d : Set (SpatialCoordinates d)) ⊆ K) :=
    ⟨centeredCube_subset_closedCube zn one_pos⟩
  obtain ⟨Fomega, hFomega_eq, hFdiff⟩ :=
    aux_prop_16_coarse_block_neumann_Fomega M H N h
  have haNeq : ∀ om : BilateralField d,
      aN N om = expPotentialCoefficient
        (compactPotentialToLp (Ω := unitNeumannCube d) K (Fomega om)) := by
    intro om
    rw [haN_def]
    exact hFomega_eq om
  have hHdiff_le := aux_prop_16_coarse_block_neumann_Hdiff_le hd M hMdelta0.le H hInfrared K h
  have hcopyMP : MeasurePreserving (aux_prop_16_coarse_block_neumann_copy h) (P.prod P) P := by
    have hPinf : P = Measure.infinitePi
        (fun j : ℤ => (scaledLayerLaw d (chaosRootFieldLaw M) j :
          Measure C(SpatialCoordinates d, ℝ))) := rfl
    rw [hPinf]
    exact aux_prop_16_coarse_block_neumann_copy_infinitePi _ h
  let Gtail1 : BilateralField d × BilateralField d → ℝ := fun pair =>
    ∑' n : ℕ, ‖(pair.1 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
      ContinuousMap.const K ((pair.1 (Int.ofNat (n + h + 1))) 0)‖
  let Gtail2 : BilateralField d × BilateralField d → ℝ := fun pair =>
    ∑' n : ℕ, ‖(pair.2 (Int.ofNat (n + h + 1))).restrict (K : Set (SpatialCoordinates d)) -
      ContinuousMap.const K ((pair.2 (Int.ofNat (n + h + 1))) 0)‖
  have hsupp0 : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      x ∉ (Set.univ : Set (SpatialCoordinates d)) →
        (0 : Lp ℝ ∞ (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)))) x = 0 :=
    Eventually.of_forall fun x hx => (hx (Set.mem_univ x)).elim
  have hInvResp : ∀ p q : Lp ℝ ∞ (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
      Real.exp (-‖p - q‖) * inverseResponse S (expPotentialCoefficient q) L0 ≤
          inverseResponse S (expPotentialCoefficient p) L0 ∧
        inverseResponse S (expPotentialCoefficient p) L0 ≤
          Real.exp ‖p - q‖ * inverseResponse S (expPotentialCoefficient q) L0 := by
    obtain ⟨_, _, hIR, _⟩ := cor_14.1 d (unitNeumannCube d) (S)
      (0 : Lp ℝ ∞ (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
      (0 : Lp ℝ ∞ (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
      Set.univ MeasurableSet.univ hsupp0
      (L0)
      (0 : weakSobolevGraph (unitNeumannCube d))
    exact hIR
  have hy_eq : ∀ om : BilateralField d, yN N om = inverseResponse S
      (expPotentialCoefficient
        (compactPotentialToLp (Ω := unitNeumannCube d) K (Fomega om))) L0 := by
    intro om
    rw [hyN_def]
    congr 1
    exact haNeq om
  have hpoint := aux_prop_16_coarse_block_neumann_point M K h S L0 Fomega H hFdiff (yN N)
    hy_eq hInvResp hHdiff_le
  exact aux_prop_16_coarse_block_neumann_assemble K CK hCKnonneg hCKbound M hMdelta0
    h N p B hp hB (yN N) (hyN N) hcopyMP hpoint

/--
Coarse-block response estimate for the primitive Neumann branch of
`prop_16`, `mfd:lem-neumann-error`.
-/
theorem prop_16_coarse_block_neumann :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cresp : ℝ) (_hCresp : 0 < Cresp)
    (pvec : Fin d → ℝ)
    (_hpvec : (∑ i : Fin d, (pvec i) ^ 2) = 1)
    (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖)
    (p B : ℝ) (_hp : 2 ≤ p) (_hB : 0 ≤ B),
    let Q := unitNeumannCube d
    let S := meanZeroResponseSpace hP
    let L0 : S.space →L[ℝ] ℝ :=
      (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph Q))
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d),
        (0 < M.delta ∧ M.delta ≤ 1) →
        ∀ (Rinput : _root_.SubdiffusiveProcess.Paper.in_responses d M),
          Rinput.C ≤ Cresp →
          4 * p ≤ Cresp⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            InfraredCharacterization M H →
            let P : Measure (BilateralField d) :=
              (chaosSampleLaw M).toMeasure
            let aN : ℕ → BilateralField d → PositiveCoefficient Q := fun N om =>
              cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos
            let yN : ℕ → BilateralField d → ℝ := fun N om =>
              inverseResponse S (aN N om) L0
            ∀ (_hyN : ∀ N,
              MemLp (yN N) (ENNReal.ofReal (4 * p)) P ∧
              eLpNorm (yN N) (ENNReal.ofReal (4 * p)) P ≤ ENNReal.ofReal B),
              ∀ (h N : ℕ),
                eLpNorm
                  (fun pair : BilateralField d × BilateralField d =>
                    yN N pair.1 -
                      yN N (fun j =>
                        if (h : ℤ) < j then pair.2 j else pair.1 j))
                  (ENNReal.ofReal (2 * p)) (P.prod P) ≤
                ENNReal.ofReal (C * M.delta * (3 : ℝ) ^ (-(h : ℝ)))
    := by
  intro d hd _ _ Cresp hCresp pvec hpvec hP p B hp hB
  obtain ⟨CK, hCKnonneg, hCKbound⟩ :=
    aux_prop_16_coarse_block_neumann_layer_tail hd
      (closedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos : Compacts (SpatialCoordinates d))
  refine ⟨4 * (B + 1) * (CK + 1) * Real.sqrt (4 * p), by positivity, ?_⟩
  intro M hMdelta Rinput hRC hRmoment H hInfrared P aN yN hyN h N
  obtain ⟨hMdelta0, hMdelta1⟩ := hMdelta
  exact aux_prop_16_coarse_block_neumann_main hd pvec hP p B hp hB CK hCKnonneg hCKbound
    M hMdelta0 hMdelta1 H hInfrared aN (fun N om => rfl) yN (fun N om => rfl) hyN h N

end SubdiffusiveProcess.Paper
