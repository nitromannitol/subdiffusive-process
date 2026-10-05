module

public import SubdiffusiveProcess.CoarseGrainingVocab.OGammaTail

@[expose] public section




set_option autoImplicit false

open MeasureTheory Filter Set
open SubdiffusiveProcess.CoarseGrainingVocab.OGamma

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.OGamma

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

omit [MeasurableSpace Omega] in
/-- The `σ = 1` companion of `level_subset`. -/
theorem level_subset_one {B : ℝ} (hB : 0 < B) {X : Omega → ℝ} {s : ℝ} (hs : 0 < s) :
    {omega : Omega | s < integrand 1 B X omega - 1}
      ⊆ {omega : Omega | B * Real.log (1+s) ≤ X omega} := by
  have hL : (0:ℝ) < Real.log (1+s) := Real.log_pos (by linarith)
  intro omega homega
  simp only [mem_ofPred_eq, integrand] at homega ⊢
  set u : ℝ := B⁻¹ * max (X omega) 0 with hu
  have hunn : 0 ≤ u := by positivity
  have h1 : Real.log (1+s) < u := by
    have h2 : 1 + s < Real.exp (u ^ (1:ℝ)) := by linarith
    rw [Real.rpow_one] at h2
    have h3 := Real.log_lt_log (by linarith) h2
    rwa [Real.log_exp] at h3
  have h5 : B * Real.log (1+s) < max (X omega) 0 := by
    have h6 := mul_lt_mul_of_pos_left h1 hB
    rwa [hu, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hB), one_mul] at h6
  have h7 : (0:ℝ) < max (X omega) 0 := lt_of_le_of_lt (by positivity) h5
  rcases le_or_gt (X omega) 0 with hx | hx
  · rw [max_eq_right hx] at h7; exact absurd h7 (lt_irrefl 0)
  · rw [max_eq_left hx.le] at h5
    linarith

/-- The `σ = 1` layer cake. -/
theorem ogammaLE_one_of_layercake [IsProbabilityMeasure mu] {B : ℝ} (hB : 0 < B)
    {X : Omega → ℝ} (hXm : AEMeasurable X mu) {g : ℝ → ℝ}
    (hgnn : ∀ᵐ s ∂(volume.restrict (Ioi (0:ℝ))), 0 ≤ g s)
    (hgint : IntegrableOn g (Ioi 0)) (hgle : ∫ s in Ioi (0:ℝ), g s ≤ 1)
    (htail : ∀ s ∈ Ioi (0:ℝ),
      mu {omega | B * Real.log (1+s) ≤ X omega} ≤ ENNReal.ofReal (g s)) :
    SubdiffusiveProcess.OGammaLE mu 1 B X := by
  set Z : Omega → ℝ := fun omega => integrand 1 B X omega - 1 with hZdef
  have hZnn : ∀ omega, 0 ≤ Z omega := by
    intro omega
    have h1 : (1:ℝ) ≤ integrand 1 B X omega :=
      Real.one_le_exp (Real.rpow_nonneg (by positivity) 1)
    simp only [hZdef]; linarith
  have hZm : AEMeasurable Z mu := (aemeasurable_integrand 1 B hXm).sub aemeasurable_const
  have hgL : ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (g s)
      = ENNReal.ofReal (∫ s in Ioi (0:ℝ), g s) :=
    (ofReal_integral_eq_lintegral_ofReal hgint hgnn).symm
  have hbound : ∫⁻ omega, ENNReal.ofReal (Z omega) ∂mu
      ≤ ENNReal.ofReal (∫ s in Ioi (0:ℝ), g s) := by
    rw [lintegral_eq_lintegral_meas_lt mu (Filter.Eventually.of_forall hZnn) hZm, ← hgL]
    refine lintegral_mono_ae ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact le_trans (measure_mono (level_subset_one hB hs)) (htail s hs)
  have hgnn' : 0 ≤ ∫ s in Ioi (0:ℝ), g s := integral_nonneg_of_ae hgnn
  have hZint : Integrable Z mu := by
    refine ⟨hZm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hZnn)]
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hZle : ∫ omega, Z omega ∂mu ≤ ∫ s in Ioi (0:ℝ), g s := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hZnn)
      hZm.aestronglyMeasurable]
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    rwa [ENNReal.toReal_ofReal hgnn'] at h
  rw [ogammaLE_iff]
  have hsplit : integrand 1 B X = fun omega => Z omega + 1 := by
    funext omega; simp [hZdef]
  rw [hsplit]
  refine ⟨hZint.add (integrable_const 1), ?_⟩
  rw [integral_add hZint (integrable_const 1), integral_const, probReal_univ, smul_eq_mul,
    one_mul]
  linarith

/-- An exponential tail gives `O_{Γ₁}` at four times the scale. -/
theorem ogammaLE_one_of_tail [IsProbabilityMeasure mu] {A : ℝ} (hA : 0 < A) {X : Omega → ℝ}
    (hXm : AEMeasurable X mu)
    (htail : ∀ lam : ℝ, 0 < lam →
      mu.real {omega | lam ≤ X omega} ≤ 2 * Real.exp (-(lam / A))) :
    SubdiffusiveProcess.OGammaLE mu 1 (4 * A) X := by
  have hB : (0:ℝ) < 4 * A := by linarith
  refine ogammaLE_one_of_layercake hB hXm ?_ integrableOn_tail
    (by rw [integral_tail]; norm_num) ?_
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have : (0:ℝ) < 1 + s := by simp at hs; linarith
    positivity
  · intro s hs
    have hs0 : (0:ℝ) < s := hs
    have hL : (0:ℝ) < Real.log (1+s) := Real.log_pos (by linarith)
    have hlam : (0:ℝ) < (4*A) * Real.log (1+s) := by positivity
    have hfin : mu {omega | (4*A) * Real.log (1+s) ≤ X omega} ≠ ⊤ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hfin]
    refine ENNReal.ofReal_le_ofReal (le_trans (htail _ hlam) ?_)
    have hratio : (4*A) * Real.log (1+s) / A = 4 * Real.log (1+s) := by field_simp
    rw [hratio]
    have hlog : Real.log ((1+s)^(4:ℕ)) = 4 * Real.log (1+s) := by
      rw [Real.log_pow]; norm_num
    rw [← hlog, Real.exp_neg, Real.exp_log (by positivity)]
    exact le_of_eq (by ring)

/-! ### Absorbing a constant `4` into the scale

A probability is at most `1`, so a tail bound with the constant `4` can be traded for one with
the constant `2` at twice the scale: where the `4` would be binding the bound is already past
the point where doubling the scale pays for it, and where it is not, the trivial bound `1` is.
-/

/-- The numeric fact behind absorbing a constant into the scale: for `u ≥ 2`,
`log (u/2) ≤ (u−1) log 2`. -/
theorem log_half_le {u : ℝ} (hu : 2 ≤ u) : Real.log (u / 2) ≤ (u - 1) * Real.log 2 := by
  have h1 : Real.log (u / 2) ≤ u / 2 - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have h2 := Real.log_two_gt_d9
  nlinarith [h2, hu]

/-- **Absorbing an arbitrary constant `c₀ ≥ 2` into the scale.**  The core, in the exponent
itself: a probability bounded by `c₀ e^{-t}` is bounded by `2 e^{-t/c₀}`. -/
theorem const_to_two_core {t p c0 : ℝ} (htpos : 0 < t) (hc0 : 2 ≤ c0)
    (hp1 : p ≤ 1) (hpc : p ≤ c0 * Real.exp (-t)) :
    p ≤ 2 * Real.exp (-(t / c0)) := by
  have hc0pos : (0:ℝ) < c0 := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt t (c0 * Real.log 2) with hc | hc
  · have h1 : Real.exp (-(Real.log 2)) ≤ Real.exp (-(t / c0)) := by
      refine Real.exp_le_exp.mpr ?_
      have : t / c0 ≤ Real.log 2 := by
        rw [div_le_iff₀ hc0pos]; linarith [hc]
      linarith
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)] at h1
    linarith
  · have hkey : Real.log (c0 / 2) ≤ t * (1 - 1 / c0) := by
      have h3 : (c0 - 1) * Real.log 2 ≤ t * (1 - 1 / c0) := by
        have hfac : t * (1 - 1 / c0) = t * (c0 - 1) / c0 := by field_simp
        rw [hfac, le_div_iff₀ hc0pos]
        nlinarith [hc, hlog2, hc0]
      exact le_trans (log_half_le hc0) h3
    have h4 : c0 / 2 ≤ Real.exp (t * (1 - 1 / c0)) := by
      have := Real.exp_le_exp.mpr hkey
      rwa [Real.exp_log (by linarith : (0:ℝ) < c0 / 2)] at this
    have hE : Real.exp (-t) = Real.exp (-(t / c0)) * Real.exp (-(t * (1 - 1 / c0))) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    have hE1 : (0:ℝ) < Real.exp (-(t / c0)) := Real.exp_pos _
    have hy : (0:ℝ) < Real.exp (t * (1 - 1 / c0)) := Real.exp_pos _
    have hinv : Real.exp (-(t * (1 - 1 / c0))) ≤ 2 / c0 := by
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ hy hc0pos]
      linarith [h4]
    have hle : c0 * Real.exp (-t) ≤ 2 * Real.exp (-(t / c0)) := by
      rw [hE]
      have hmul := mul_le_mul_of_nonneg_left hinv (le_of_lt (mul_pos hc0pos hE1))
      have hsimp : c0 * Real.exp (-(t / c0)) * (2 / c0) = 2 * Real.exp (-(t / c0)) := by
        field_simp
      calc c0 * (Real.exp (-(t / c0)) * Real.exp (-(t * (1 - 1 / c0))))
          = c0 * Real.exp (-(t / c0)) * Real.exp (-(t * (1 - 1 / c0))) := by ring
        _ ≤ c0 * Real.exp (-(t / c0)) * (2 / c0) := hmul
        _ = 2 * Real.exp (-(t / c0)) := hsimp
    linarith

/-- The exponential instance. -/
theorem const_to_two_exp {B lam p c0 : ℝ} (hB : 0 < B) (hlam : 0 < lam) (hc0 : 2 ≤ c0)
    (hp1 : p ≤ 1) (hpc : p ≤ c0 * Real.exp (-(lam / B))) :
    p ≤ 2 * Real.exp (-(lam / (c0 * B))) := by
  have hrw : lam / (c0 * B) = (lam / B) / c0 := by field_simp
  rw [hrw]
  exact const_to_two_core (div_pos hlam hB) hc0 hp1 hpc

/-- The Gaussian instance: the scale grows by `√c₀`. -/
theorem const_to_two_gauss {A lam p c0 : ℝ} (hA : 0 < A) (hlam : 0 < lam) (hc0 : 2 ≤ c0)
    (hp1 : p ≤ 1) (hpc : p ≤ c0 * Real.exp (-((lam / A) ^ (2:ℕ)))) :
    p ≤ 2 * Real.exp (-((lam / (Real.sqrt c0 * A)) ^ (2:ℕ))) := by
  have hc0pos : (0:ℝ) < c0 := by linarith
  have hsq : Real.sqrt c0 ^ (2:ℕ) = c0 := Real.sq_sqrt hc0pos.le
  have hspos : (0:ℝ) < Real.sqrt c0 := Real.sqrt_pos.mpr hc0pos
  have hrw : (lam / (Real.sqrt c0 * A)) ^ (2:ℕ) = ((lam / A) ^ (2:ℕ)) / c0 := by
    rw [div_pow, div_pow, mul_pow, hsq]
    field_simp
  rw [hrw]
  exact const_to_two_core (by positivity) hc0 hp1 hpc

theorem four_to_two_exp {B lam p : ℝ} (hB : 0 < B) (hlam : 0 < lam)
    (hp1 : p ≤ 1) (hp4 : p ≤ 4 * Real.exp (-(lam / B))) :
    p ≤ 2 * Real.exp (-(lam / (2 * B))) := by
  have htpos : 0 < lam / B := div_pos hlam hB
  have hrw : lam / (2 * B) = (lam / B) / 2 := by field_simp
  rw [hrw]
  set t : ℝ := lam / B with ht
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt t (2 * Real.log 2) with hc | hc
  · have h1 : Real.exp (-(Real.log 2)) ≤ Real.exp (-(t/2)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)] at h1
    linarith
  · have h2 : (2:ℝ) ≤ Real.exp (t/2) := by
      have := Real.exp_le_exp.mpr (by linarith : Real.log 2 ≤ t/2)
      rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at this
    have hE : Real.exp (-t) = Real.exp (-(t/2)) * Real.exp (-(t/2)) := by
      rw [← Real.exp_add]; ring_nf
    have hEpos : (0:ℝ) < Real.exp (-(t/2)) := Real.exp_pos _
    have hinv : Real.exp (-(t/2)) ≤ 1/2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      simpa using h2
    have hle : 4 * Real.exp (-t) ≤ 2 * Real.exp (-(t/2)) := by
      rw [hE]; nlinarith [hEpos, hinv]
    linarith

theorem four_to_two_gauss {A lam p : ℝ} (hA : 0 < A) (hlam : 0 < lam)
    (hp1 : p ≤ 1) (hp4 : p ≤ 4 * Real.exp (-((lam / A) ^ (2:ℕ)))) :
    p ≤ 2 * Real.exp (-((lam / (2 * A)) ^ (2:ℕ))) := by
  have htpos : 0 < lam / A := div_pos hlam hA
  have hrw : (lam / (2 * A)) ^ (2:ℕ) = (lam / A) ^ (2:ℕ) / 4 := by field_simp; ring
  rw [hrw]
  set t : ℝ := (lam / A) ^ (2:ℕ) with ht
  have htnn : 0 ≤ t := by rw [ht]; positivity
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt t (4 * Real.log 2) with hc | hc
  · have h1 : Real.exp (-(Real.log 2)) ≤ Real.exp (-(t/4)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)] at h1
    linarith
  · have h2 : (2:ℝ) ≤ Real.exp (3 * t / 4) := by
      have := Real.exp_le_exp.mpr (by linarith : Real.log 2 ≤ 3 * t / 4)
      rwa [Real.exp_log (by norm_num : (0:ℝ) < 2)] at this
    have hE : Real.exp (-t) = Real.exp (-(t/4)) * Real.exp (-(3 * t / 4)) := by
      rw [← Real.exp_add]; ring_nf
    have hE1 : (0:ℝ) < Real.exp (-(t/4)) := Real.exp_pos _
    have hinv : Real.exp (-(3 * t / 4)) ≤ 1/2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      simpa using h2
    have hE2 : (0:ℝ) < Real.exp (-(3 * t / 4)) := Real.exp_pos _
    have hle : 4 * Real.exp (-t) ≤ 2 * Real.exp (-(t/4)) := by
      rw [hE]; nlinarith [hE1, hE2, hinv]
    linarith

/-! ### The split -/

/-- **A two-term tail splits into `O_{Γ₂} + O_{Γ₁}`.**  Cut `X` at the crossing radius `A²/B`,
where the Gaussian and exponential exponents agree.  Below the cut the Gaussian term dominates,
above it the exponential one, and the two halves are `min X (A²/B)` and `(X − A²/B)⁺`, whose
sum is `X` and whose measurability is free. -/
theorem ogammaLE_split_of_two_term [IsProbabilityMeasure mu] {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) {X : Omega → ℝ} (hXm : AEMeasurable X mu)
    (htail : ∀ lam : ℝ, 0 < lam →
      mu.real {omega | lam ≤ X omega}
        ≤ 2 * Real.exp (-((lam / A) ^ (2:ℕ))) + 2 * Real.exp (-(lam / B))) :
    ∃ X2 X1 : Omega → ℝ,
      (∀ omega, X omega = X2 omega + X1 omega) ∧
      (∀ omega, 0 ≤ X1 omega) ∧
      SubdiffusiveProcess.OGammaLE mu 2 (4 * A) X2 ∧ SubdiffusiveProcess.OGammaLE mu 1 (8 * B) X1 := by
  set u0 : ℝ := A ^ (2:ℕ) / B with hu0
  have hu0pos : 0 < u0 := by rw [hu0]; positivity
  refine ⟨fun omega => min (X omega) u0, fun omega => max (X omega - u0) 0, ?_, ?_, ?_, ?_⟩
  · intro omega
    show X omega = min (X omega) u0 + max (X omega - u0) 0
    rcases le_or_gt (X omega) u0 with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h.le, max_eq_left (by linarith)]; ring
  · intro omega; exact le_max_right _ _
  · -- the Gaussian half
    have hm : AEMeasurable (fun omega => min (X omega) u0) mu := hXm.min aemeasurable_const
    have hkey : ∀ lam : ℝ, 0 < lam →
        mu.real {omega | lam ≤ min (X omega) u0}
          ≤ 2 * Real.exp (-((lam / (2 * A)) ^ (2:ℕ))) := by
      intro lam hlam
      have hone : mu.real {omega | lam ≤ min (X omega) u0} ≤ 1 := by
        have _h := ENNReal.toReal_mono (by norm_num : (1:ENNReal) ≠ ⊤)
          (prob_le_one : mu {omega | lam ≤ min (X omega) u0} ≤ 1)
        simp
      refine four_to_two_gauss hA hlam hone ?_
      rcases le_or_gt lam u0 with hc | hc
      · have hsub : {omega | lam ≤ min (X omega) u0} ⊆ {omega | lam ≤ X omega} := by
          intro omega homega
          simp only [mem_ofPred_eq] at homega ⊢
          exact le_trans homega (min_le_left _ _)
        have hcmp : Real.exp (-(lam / B)) ≤ Real.exp (-((lam / A) ^ (2:ℕ))) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : (lam / A) ^ (2:ℕ) ≤ lam / B := by
            have hlb : lam * B ≤ A ^ (2:ℕ) := by
              rw [hu0, le_div_iff₀ hB] at hc; exact hc
            rw [div_pow, div_le_div_iff₀ (by positivity) hB]
            nlinarith [hlb, hlam.le]
          linarith
        have := le_trans (measureReal_mono hsub) (htail lam hlam)
        linarith
      · have hempty : {omega | lam ≤ min (X omega) u0} = ∅ := by
          ext omega
          simp only [mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
          exact lt_of_le_of_lt (min_le_right _ _) hc
        rw [hempty]
        simp only [measureReal_empty]
        positivity
    have := ogammaLE_of_measureReal_tail (by positivity : (0:ℝ) < 2 * A) hm hkey
    have heq : 2 * (2 * A) = 4 * A := by ring
    rwa [heq] at this
  · -- the exponential half
    have hm : AEMeasurable (fun omega => max (X omega - u0) 0) mu :=
      (hXm.sub aemeasurable_const).max aemeasurable_const
    have hkey : ∀ lam : ℝ, 0 < lam →
        mu.real {omega | lam ≤ max (X omega - u0) 0}
          ≤ 2 * Real.exp (-(lam / (2 * B))) := by
      intro lam hlam
      have hone : mu.real {omega | lam ≤ max (X omega - u0) 0} ≤ 1 := by
        have _h := ENNReal.toReal_mono (by norm_num : (1:ENNReal) ≠ ⊤)
          (prob_le_one : mu {omega | lam ≤ max (X omega - u0) 0} ≤ 1)
        simp
      refine four_to_two_exp hB hlam hone ?_
      have hsub : {omega | lam ≤ max (X omega - u0) 0} ⊆ {omega | lam + u0 ≤ X omega} := by
        intro omega homega
        simp only [mem_ofPred_eq, le_max_iff] at homega
        rcases homega with h | h
        · simp only [mem_ofPred_eq]; linarith
        · exact absurd h (not_le.mpr hlam)
      have hlu : 0 < lam + u0 := by linarith
      have hcmp : Real.exp (-(((lam + u0) / A) ^ (2:ℕ))) ≤ Real.exp (-((lam + u0) / B)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : (lam + u0) / B ≤ ((lam + u0) / A) ^ (2:ℕ) := by
          have hub : A ^ (2:ℕ) ≤ (lam + u0) * B := by
            have hu0B : u0 * B = A ^ (2:ℕ) := by rw [hu0]; field_simp
            nlinarith [hlam.le, hB]
          rw [div_pow, div_le_div_iff₀ hB (by positivity)]
          nlinarith [hub, hlu.le]
        linarith
      have hmono : Real.exp (-((lam + u0) / B)) ≤ Real.exp (-(lam / B)) := by
        refine Real.exp_le_exp.mpr ?_
        have hle2 : lam / B ≤ (lam + u0) / B := by
          rw [div_le_div_iff₀ hB hB]; nlinarith [hu0pos, hB]
        linarith
      have := le_trans (measureReal_mono hsub) (htail _ hlu)
      linarith
    have := ogammaLE_one_of_tail (by positivity : (0:ℝ) < 2 * B) hm hkey
    have heq : 4 * (2 * B) = 8 * B := by ring
    rwa [heq] at this

/-! ### A finite maximum keeps the tail, at the cost of the cardinality

The paper's random factor at a point is a maximum of the lattice field over the finitely many
sites within a fixed distance, so the passage from a pointwise tail to the tail of the
supremum over a unit ball is a union bound over a *bounded* number of terms.  The cardinality
is then absorbed into the scale by `const_to_two_core`, not into the deterministic term. -/

theorem measureReal_finset_sup'_tail {iota : Type*} [IsFiniteMeasure mu]
    {s : Finset iota} (hs : s.Nonempty) {Z : iota → Omega → ℝ} {c f : ℝ}
    (hf : ∀ i ∈ s, mu.real {omega | c ≤ Z i omega} ≤ f) :
    mu.real {omega | c ≤ s.sup' hs (fun i => Z i omega)} ≤ (s.card : ℝ) * f := by
  classical
  have hset : {omega | c ≤ s.sup' hs (fun i => Z i omega)}
      = ⋃ i ∈ s, {omega | c ≤ Z i omega} := by
    ext omega
    simp only [mem_ofPred_eq, Set.mem_iUnion, exists_prop]
    exact Finset.le_sup'_iff hs
  have hle : mu {omega | c ≤ s.sup' hs (fun i => Z i omega)}
      ≤ ∑ i ∈ s, mu {omega | c ≤ Z i omega} := by
    rw [hset]; exact measure_biUnion_finset_le s _
  have hfin : ∀ i, mu {omega | c ≤ Z i omega} ≠ ⊤ := fun i => measure_ne_top _ _
  have hsumfin : (∑ i ∈ s, mu {omega | c ≤ Z i omega}) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr (fun i _ => measure_lt_top _ _)).ne
  have htoReal := ENNReal.toReal_mono hsumfin hle
  rw [ENNReal.toReal_sum (fun i _ => hfin i)] at htoReal
  refine le_trans htoReal ?_
  calc ∑ i ∈ s, (mu {omega | c ≤ Z i omega}).toReal ≤ ∑ _i ∈ s, f :=
        Finset.sum_le_sum fun i hi => hf i hi
    _ = (s.card : ℝ) * f := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### The split with an arbitrary constant -/

/-- `ogammaLE_split_of_two_term` with the constant `2` replaced by any `c₀ ≥ 1`.  The two
halves land at `2√(2c₀) A` and `8 c₀ B`. -/
theorem ogammaLE_split_of_two_term_const [IsProbabilityMeasure mu] {A B c0 : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hc0 : 1 ≤ c0) {X : Omega → ℝ} (hXm : AEMeasurable X mu)
    (htail : ∀ lam : ℝ, 0 < lam →
      mu.real {omega | lam ≤ X omega}
        ≤ c0 * Real.exp (-((lam / A) ^ (2:ℕ))) + c0 * Real.exp (-(lam / B))) :
    ∃ X2 X1 : Omega → ℝ,
      (∀ omega, X omega = X2 omega + X1 omega) ∧
      (∀ omega, 0 ≤ X1 omega) ∧
      SubdiffusiveProcess.OGammaLE mu 2 (2 * Real.sqrt (2 * c0) * A) X2 ∧
      SubdiffusiveProcess.OGammaLE mu 1 (8 * c0 * B) X1 := by
  have hc2 : (2:ℝ) ≤ 2 * c0 := by linarith
  have hc0pos : (0:ℝ) < c0 := by linarith
  set u0 : ℝ := A ^ (2:ℕ) / B with hu0
  have hu0pos : 0 < u0 := by rw [hu0]; positivity
  refine ⟨fun omega => min (X omega) u0, fun omega => max (X omega - u0) 0, ?_, ?_, ?_, ?_⟩
  · intro omega
    show X omega = min (X omega) u0 + max (X omega - u0) 0
    rcases le_or_gt (X omega) u0 with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h.le, max_eq_left (by linarith)]; ring
  · intro omega; exact le_max_right _ _
  · have hm : AEMeasurable (fun omega => min (X omega) u0) mu := hXm.min aemeasurable_const
    have hkey : ∀ lam : ℝ, 0 < lam →
        mu.real {omega | lam ≤ min (X omega) u0}
          ≤ 2 * Real.exp (-((lam / (Real.sqrt (2 * c0) * A)) ^ (2:ℕ))) := by
      intro lam hlam
      have hone : mu.real {omega | lam ≤ min (X omega) u0} ≤ 1 := by
        have _h := ENNReal.toReal_mono (by norm_num : (1:ENNReal) ≠ ⊤)
          (prob_le_one : mu {omega | lam ≤ min (X omega) u0} ≤ 1)
        simp
      refine const_to_two_gauss hA hlam hc2 hone ?_
      rcases le_or_gt lam u0 with hc | hc
      · have hsub : {omega | lam ≤ min (X omega) u0} ⊆ {omega | lam ≤ X omega} := by
          intro omega homega
          simp only [mem_ofPred_eq] at homega ⊢
          exact le_trans homega (min_le_left _ _)
        have hcmp : Real.exp (-(lam / B)) ≤ Real.exp (-((lam / A) ^ (2:ℕ))) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : (lam / A) ^ (2:ℕ) ≤ lam / B := by
            have hlb : lam * B ≤ A ^ (2:ℕ) := by
              rw [hu0, le_div_iff₀ hB] at hc; exact hc
            rw [div_pow, div_le_div_iff₀ (by positivity) hB]
            nlinarith [hlb, hlam.le]
          linarith
        have hmain := le_trans (measureReal_mono hsub) (htail lam hlam)
        nlinarith [hmain, hcmp, hc0pos]
      · have hempty : {omega | lam ≤ min (X omega) u0} = ∅ := by
          ext omega
          simp only [mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
          exact lt_of_le_of_lt (min_le_right _ _) hc
        rw [hempty]
        simp only [measureReal_empty]
        positivity
    have hres := ogammaLE_of_measureReal_tail
      (by positivity : (0:ℝ) < Real.sqrt (2 * c0) * A) hm hkey
    have heq : 2 * (Real.sqrt (2 * c0) * A) = 2 * Real.sqrt (2 * c0) * A := by ring
    rwa [heq] at hres
  · have hm : AEMeasurable (fun omega => max (X omega - u0) 0) mu :=
      (hXm.sub aemeasurable_const).max aemeasurable_const
    have hkey : ∀ lam : ℝ, 0 < lam →
        mu.real {omega | lam ≤ max (X omega - u0) 0}
          ≤ 2 * Real.exp (-(lam / (2 * c0 * B))) := by
      intro lam hlam
      have hone : mu.real {omega | lam ≤ max (X omega - u0) 0} ≤ 1 := by
        have _h := ENNReal.toReal_mono (by norm_num : (1:ENNReal) ≠ ⊤)
          (prob_le_one : mu {omega | lam ≤ max (X omega - u0) 0} ≤ 1)
        simp
      refine const_to_two_exp hB hlam hc2 hone ?_
      have hsub : {omega | lam ≤ max (X omega - u0) 0} ⊆ {omega | lam + u0 ≤ X omega} := by
        intro omega homega
        simp only [mem_ofPred_eq, le_max_iff] at homega
        rcases homega with h | h
        · simp only [mem_ofPred_eq]; linarith
        · exact absurd h (not_le.mpr hlam)
      have hlu : 0 < lam + u0 := by linarith
      have hcmp : Real.exp (-(((lam + u0) / A) ^ (2:ℕ))) ≤ Real.exp (-((lam + u0) / B)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : (lam + u0) / B ≤ ((lam + u0) / A) ^ (2:ℕ) := by
          have hub : A ^ (2:ℕ) ≤ (lam + u0) * B := by
            have hu0B : u0 * B = A ^ (2:ℕ) := by rw [hu0]; field_simp
            nlinarith [hlam.le, hB]
          rw [div_pow, div_le_div_iff₀ hB (by positivity)]
          nlinarith [hub, hlu.le]
        linarith
      have hmono : Real.exp (-((lam + u0) / B)) ≤ Real.exp (-(lam / B)) := by
        refine Real.exp_le_exp.mpr ?_
        have hle2 : lam / B ≤ (lam + u0) / B := by
          rw [div_le_div_iff₀ hB hB]; nlinarith [hu0pos, hB]
        linarith
      have hmain := le_trans (measureReal_mono hsub) (htail _ hlu)
      nlinarith [hmain, hcmp, hmono, hc0pos]
    have hres := ogammaLE_one_of_tail (by positivity : (0:ℝ) < 2 * c0 * B) hm hkey
    have heq : 4 * (2 * c0 * B) = 8 * c0 * B := by ring
    rwa [heq] at hres

/-! ### Union bounds with the entropy in the exponent

A supremum over a net is handled by a union bound, and the net's cardinality is exponential in
the parameters — `exp(C(M + h + log(j+2)))` in the macroscopic clock divergence lemma, and similarly
in Step 3 of the weighted stopping estimate.  Absorbing such a cardinality into the *scale*
would destroy it; it has to be absorbed into the **exponent**, against the Gaussian term.  These
three lemmas are that absorption. -/

/-- A supremum over a finite family with a common `Γ₂` scale, by union bound. -/
theorem measureReal_sup'_le_of_ogammaLE {iota : Type*} [IsProbabilityMeasure mu]
    {s : Finset iota} (hs : s.Nonempty) {Z : iota → Omega → ℝ} {A : ℝ} (hA : 0 < A)
    (hZ : ∀ i ∈ s, SubdiffusiveProcess.OGammaLE mu 2 A (Z i)) {lam : ℝ} (hlam : 0 ≤ lam) :
    mu.real {omega | lam ≤ s.sup' hs (fun i => Z i omega)}
      ≤ (s.card : ℝ) * (2 * Real.exp (-((lam / A) ^ (2:ℕ)))) := by
  refine measureReal_finset_sup'_tail hs fun i hi => ?_
  have h := measureReal_ge_le_of_ogammaLE (hZ i hi) hA (by norm_num) hlam
  have hrw : (A⁻¹ * lam) ^ (2:ℝ) = (lam / A) ^ (2:ℕ) := by
    rw [rpow_two, inv_mul_eq_div]
  rwa [hrw] at h

/-- **The entropy absorption.**  A cardinality `N` in front of an exponential tail is paid for
by the exponent, provided the exponent has `log N` to spare. -/
theorem const_absorb {N E F : ℝ} (hN : 0 < N) (hE : Real.log N + F ≤ E) :
    N * (2 * Real.exp (-E)) ≤ 2 * Real.exp (-F) := by
  have hrw : N = Real.exp (Real.log N) := (Real.exp_log hN).symm
  rw [hrw]
  have hle : Real.exp (Real.log N) * Real.exp (-E) ≤ Real.exp (-F) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  nlinarith [hle, Real.exp_pos (-F)]

/-- The Gaussian instance, which is the one the net union bound needs. -/
theorem card_absorb {N lam A E : ℝ} (hN : 0 < N)
    (hE : Real.log N + E ≤ (lam / A) ^ (2:ℕ)) :
    N * (2 * Real.exp (-((lam / A) ^ (2:ℕ)))) ≤ 2 * Real.exp (-E) :=
  const_absorb hN hE

/-- **The AM-GM that turns the Gaussian exponent into a linear one.**  The source uses it to
show that `M + h²/(δ²(M+1))` dominates `h/δ`, which is what converts the Gaussian term into the
`Γ₁` term of the level-failure bound. -/
theorem two_mul_div_le_add_sq_div {M h delta : ℝ} (hM : 0 ≤ M) (_hh : 0 ≤ h) (hd : 0 < delta) :
    2 * h / delta ≤ (M + 1) + h ^ (2:ℕ) / (delta ^ (2:ℕ) * (M + 1)) := by
  have hM1 : (0:ℝ) < M + 1 := by linarith
  rw [← sub_nonneg]
  have hfield : (M + 1) + h ^ (2:ℕ) / (delta ^ (2:ℕ) * (M + 1)) - 2 * h / delta
      = ((M + 1) - h / delta) ^ (2:ℕ) / (M + 1) := by
    field_simp
    ring
  rw [hfield]
  positivity

/-! ### Transport along a measure-preserving map

`OGammaLE` is defined through an integral, so it is carried by any measure-preserving map.
The development uses this for spatial translations of the potential sequence, whose law is
stationary: a bound proved at the origin holds at every centre, with the same scale. -/

theorem ogammaLE_comp_measurePreserving {T : Omega → Omega}
    (hT : MeasurePreserving T mu mu) {sigma A : ℝ} {X : Omega → ℝ}
    (hX : AEMeasurable X mu) (h : SubdiffusiveProcess.OGammaLE mu sigma A X) :
    SubdiffusiveProcess.OGammaLE mu sigma A (fun omega => X (T omega)) := by
  rw [ogammaLE_iff] at h ⊢
  have hfun : integrand sigma A (fun omega => X (T omega))
      = fun omega => integrand sigma A X (T omega) := rfl
  have hmeas : AEStronglyMeasurable (integrand sigma A X) mu :=
    (aemeasurable_integrand sigma A hX).aestronglyMeasurable
  have hmap : Measure.map T mu = mu := hT.map_eq
  have hmeas' : AEStronglyMeasurable (integrand sigma A X) (Measure.map T mu) := by
    rw [hmap]; exact hmeas
  have hcomp : (fun omega => integrand sigma A X (T omega))
      = (integrand sigma A X) ∘ T := rfl
  rw [hfun]
  constructor
  · rw [hcomp, ← integrable_map_measure hmeas' hT.aemeasurable, hmap]
    exact h.1
  · rw [← integral_map hT.aemeasurable hmeas', hmap]
    exact h.2

/-! ### Finite unions

The level event of the macroscopic clock is a union over the pairs `0 ≤ n ≤ j ≤ m+h`, a
*polynomial* number of terms, so its log-cardinality is `2 log(m+h+1)` and `card_absorb` pays
for it the same way it pays for the net.  The source spends the same reserve on both. -/

theorem measureReal_biUnion_finset_le {iota : Type*} [IsFiniteMeasure mu]
    (s : Finset iota) {A : iota → Set Omega} {b : ℝ}
    (hb : ∀ i ∈ s, mu.real (A i) ≤ b) :
    mu.real (⋃ i ∈ s, A i) ≤ (s.card : ℝ) * b := by
  classical
  have hle : mu (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, mu (A i) := measure_biUnion_finset_le s _
  have hsumfin : (∑ i ∈ s, mu (A i)) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr (fun i _ => measure_lt_top _ _)).ne
  have htoReal := ENNReal.toReal_mono hsumfin hle
  rw [ENNReal.toReal_sum (fun i _ => (measure_lt_top mu (A i)).ne)] at htoReal
  refine le_trans htoReal ?_
  calc ∑ i ∈ s, (mu (A i)).toReal ≤ ∑ _i ∈ s, b := Finset.sum_le_sum fun i hi => hb i hi
    _ = (s.card : ℝ) * b := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The pairs `n < j ≤ L` number at most `(L+1)²`. -/
theorem card_pairs_le (L : ℕ) :
    ((Finset.range (L + 1) ×ˢ Finset.range (L + 1)).card : ℝ) = ((L : ℝ) + 1) ^ (2:ℕ) := by
  rw [Finset.card_product, Finset.card_range]
  push_cast
  ring

/-! ### The last failing level

The paper's random factors are built from a family of level events `F h`, decreasing in `h`,
and the factor is an exponential of *the last level that fails*.  Written as a supremum that
has to be read as `−1` on the empty set and `∞` when every level fails, it carries two junk
conventions.  Written instead as

    firstGood F ω = inf { h : ω ∉ F h },

it carries one, and that one is harmless: `sInf ∅ = 0` in `ℕ`, so a sample at which *every*
level fails is assigned `0`, which is the smallest possible value and therefore cannot make any
upper bound false.  The tail is exact — `h < firstGood F ω` forces `ω ∈ F h`, with no side
condition — which is what makes the construction usable without an a.e. caveat. -/

/-- The first level that does not fail. -/
noncomputable def firstGood (F : ℕ → Set Omega) (omega : Omega) : ℕ :=
  sInf {h : ℕ | omega ∉ F h}

omit [MeasurableSpace Omega] in
/-- **The tail of the last failing level.**  Exceeding `h` means level `h` failed. -/
theorem firstGood_gt_subset (F : ℕ → Set Omega) (h : ℕ) :
    {omega | h < firstGood F omega} ⊆ F h := by
  intro omega homega
  by_contra hc
  have hmem : h ∈ {h' : ℕ | omega ∉ F h'} := hc
  exact absurd (Nat.sInf_le hmem) (not_le.mpr homega)

theorem measureReal_firstGood_gt_le [IsFiniteMeasure mu] (F : ℕ → Set Omega) (h : ℕ)
    {b : ℝ} (hF : mu.real (F h) ≤ b) :
    mu.real {omega | h < firstGood F omega} ≤ b :=
  le_trans (measureReal_mono (firstGood_gt_subset F h) (measure_ne_top _ _)) hF

omit [MeasurableSpace Omega] in
/-- The level index is monotone in the family — **but only where the larger family has a good
level**.  The junk convention `sInf ∅ = 0` breaks monotonicity on the set where every level of
`G` fails: there `firstGood G = 0` while `firstGood F` may be positive.  That set is null in
every application, but a statement asserting monotonicity *everywhere* cannot be proved from
this definition, and a field required to be monotone pointwise must be built as a running
maximum (`firstGoodRunning`) rather than as `firstGood` itself. -/
theorem firstGood_mono {F G : ℕ → Set Omega} (hFG : ∀ h, F h ⊆ G h) {omega : Omega}
    (hne : ∃ h, omega ∉ G h) :
    firstGood F omega ≤ firstGood G omega := by
  have hne' : {h : ℕ | omega ∉ G h}.Nonempty := hne
  have hmem := Nat.sInf_mem hne'
  exact Nat.sInf_le (fun hFmem => hmem (hFG _ hFmem))

/-- The running maximum of a family of level indices: monotone in the index **everywhere**, by
construction, and equal to the intended value wherever the family is itself monotone. -/
noncomputable def firstGoodRunning (F : ℕ → ℕ → Set Omega) (m : ℕ) (omega : Omega) : ℕ :=
  (Finset.range (m + 1)).sup fun i => firstGood (F i) omega

omit [MeasurableSpace Omega] in
theorem firstGoodRunning_mono (F : ℕ → ℕ → Set Omega) {m m' : ℕ} (hm : m ≤ m')
    (omega : Omega) :
    firstGoodRunning F m omega ≤ firstGoodRunning F m' omega :=
  Finset.sup_mono (fun x hx => Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hx) (by omega)))

omit [MeasurableSpace Omega] in
theorem firstGood_le_firstGoodRunning (F : ℕ → ℕ → Set Omega) (m : ℕ) (omega : Omega) :
    firstGood (F m) omega ≤ firstGoodRunning F m omega :=
  Finset.le_sup (f := fun i => firstGood (F i) omega) (Finset.self_mem_range_succ m)

omit [MeasurableSpace Omega] in
/-- The running maximum's tail is the union of the individual tails. -/
theorem firstGoodRunning_gt_subset (F : ℕ → ℕ → Set Omega) (m h : ℕ) :
    {omega | h < firstGoodRunning F m omega} ⊆ ⋃ i ∈ Finset.range (m + 1), F i h := by
  intro omega homega
  simp only [mem_ofPred_eq, firstGoodRunning, Finset.lt_sup_iff] at homega
  obtain ⟨i, hi, hlt⟩ := homega
  exact Set.mem_biUnion hi (firstGood_gt_subset (F i) h hlt)



/-! ### Threshold arithmetic

The level thresholds have the shape `t = B h + η₀ M` and the scales the shape
`A = C δ √(M+1)`, so the Gaussian exponent `(t/A)²` splits into a part linear in `M` and a part
carrying `h²/(δ²(M+1))`.  Those are exactly the two terms of the source's level-failure bound,
and these two lemmas are the only inequalities needed to produce them. -/

omit [MeasurableSpace Omega] in
/-- `(a+b)² ≥ a² + b²` for nonnegative `a, b`, in the form the thresholds need. -/
theorem sq_sum_ge_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ (2:ℕ) + b ^ (2:ℕ) ≤ (a + b) ^ (2:ℕ) := by nlinarith [mul_nonneg ha hb]

omit [MeasurableSpace Omega] in
/-- **The threshold split.**  At `t = B h + η₀ M` and `A = C δ √(M+1)` with `η₀ = C₀ δ`, the
exponent dominates the sum of its two natural parts. -/
theorem threshold_lower {B C0 C delta h M : ℝ} (hB : 0 ≤ B) (hC0 : 0 ≤ C0) (hC : 0 < C)
    (hdelta : 0 < delta) (hh : 0 ≤ h) (hM : 0 ≤ M) :
    (C0 / C) ^ (2:ℕ) * (M ^ (2:ℕ) / (M + 1))
        + (B / (C * delta)) ^ (2:ℕ) * (h ^ (2:ℕ) / (M + 1))
      ≤ ((B * h + C0 * delta * M) / (C * delta * Real.sqrt (M + 1))) ^ (2:ℕ) := by
  have hM1 : (0:ℝ) < M + 1 := by linarith
  have hsqrt : Real.sqrt (M + 1) ^ (2:ℕ) = M + 1 := Real.sq_sqrt hM1.le
  have hspos : (0:ℝ) < Real.sqrt (M + 1) := Real.sqrt_pos.mpr hM1
  have hden : (0:ℝ) < C * delta * Real.sqrt (M + 1) := by positivity
  have hrhs : ((B * h + C0 * delta * M) / (C * delta * Real.sqrt (M + 1))) ^ (2:ℕ)
      = (B * h + C0 * delta * M) ^ (2:ℕ) / (C ^ (2:ℕ) * delta ^ (2:ℕ) * (M + 1)) := by
    rw [div_pow, mul_pow, mul_pow, hsqrt]
  rw [hrhs, le_div_iff₀ (by positivity)]
  have hsplit : (B * h) ^ (2:ℕ) + (C0 * delta * M) ^ (2:ℕ)
      ≤ (B * h + C0 * delta * M) ^ (2:ℕ) :=
    sq_sum_ge_of_nonneg (by positivity) (by positivity)
  have hexp : ((C0 / C) ^ (2:ℕ) * (M ^ (2:ℕ) / (M + 1))
      + (B / (C * delta)) ^ (2:ℕ) * (h ^ (2:ℕ) / (M + 1))) * (C ^ (2:ℕ) * delta ^ (2:ℕ) * (M + 1))
      = (C0 * delta * M) ^ (2:ℕ) + (B * h) ^ (2:ℕ) := by
    field_simp
  rw [hexp]
  linarith [hsplit]

omit [MeasurableSpace Omega] in
/-- `M²/(M+1) ≥ M − 1`: the linear part of the exponent really is linear. -/
theorem sq_div_succ_ge {M : ℝ} (hM : 0 ≤ M) : M - 1 ≤ M ^ (2:ℕ) / (M + 1) := by
  have hM1 : (0:ℝ) < M + 1 := by linarith
  rw [le_div_iff₀ hM1]
  nlinarith

omit [MeasurableSpace Omega] in
/-- **The exponent dominates both reserves at once.**  The two parts of `threshold_lower` are
each bounded below by `M − 1` and by `2h/δ − 1`, so their sum dominates the average — which is
what lets the entropy's `M`-linear part be paid by the first and its `h`-linear part by the
second, from one inequality.  This is the source's

> `M + h²/(δ²(M+1)) ≥ c h/δ ≥ C log(m+h+2)`

with the first inequality made explicit. -/
theorem exponent_parts_ge {M h delta : ℝ} (hM : 0 ≤ M) (hh : 0 ≤ h) (hdelta : 0 < delta) :
    (M + 2 * h / delta) / 2 - 2
      ≤ M ^ (2:ℕ) / (M + 1) + h ^ (2:ℕ) / (delta ^ (2:ℕ) * (M + 1)) := by
  have hM1 : (0:ℝ) < M + 1 := by linarith
  have hlin : M - 1 ≤ M ^ (2:ℕ) / (M + 1) := sq_div_succ_ge hM
  have hterm : (0:ℝ) ≤ h ^ (2:ℕ) / (delta ^ (2:ℕ) * (M + 1)) := by positivity
  have hsq : (0:ℝ) ≤ M ^ (2:ℕ) / (M + 1) := by positivity
  have hamgm : 2 * h / delta ≤ (M + 1) + h ^ (2:ℕ) / (delta ^ (2:ℕ) * (M + 1)) :=
    two_mul_div_le_add_sq_div hM hh hdelta
  -- the first part pays for `M`, the second for `2h/δ`, and the average is below their sum
  have hA : M - 1 ≤ M ^ (2:ℕ) / (M + 1) + h ^ (2:ℕ) / (delta ^ (2:ℕ) * (M + 1)) := by
    linarith
  have hB : 2 * h / delta - 2 ≤ M ^ (2:ℕ) / (M + 1) + h ^ (2:ℕ) / (delta ^ (2:ℕ) * (M + 1)) := by
    have hstep : 2 * h / delta - 1 ≤ M + h ^ (2:ℕ) / (delta ^ (2:ℕ) * (M + 1)) := by linarith
    linarith [hlin]
  linarith

omit [MeasurableSpace Omega] in
/-- **The entropy discharge.**  With `κ` the smaller of the two coefficients of
`threshold_lower`, the entropy `d(log 2 + lg + h + log 3 · M + 4 log 3)` — which is
`levelRadius_le` times `d log 3` — plus the reserve `κ(M/8 + h/(4δ))` stays below
`κ((M + 2h/δ)/2 − 2)`, which `exponent_parts_ge` puts below the exponent.

The three conditions are the source's: `κ` above a dimensional multiple of `log 3`, `δ` below
one, and `h/δ` above a dimensional multiple of `1 + lg`, where `lg` is the `log(j+2)` of the
radius.  The last is `h ≥ Cδ√(D_m(x))` in the source's form. -/
theorem entropy_discharge (dim : ℝ) {kappa M h delta lg : ℝ}
    (hdim : 0 ≤ dim) (hkappa : 8 * dim * Real.log 3 ≤ kappa) (hM : 0 ≤ M) (hh : 0 ≤ h)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hres : dim * Real.log 2 + dim * lg + 4 * dim * Real.log 3 + 2 * kappa
      ≤ kappa * h / (2 * delta)) :
    dim * (Real.log 2 + lg + h + Real.log 3 * M + 4 * Real.log 3)
        + kappa * (M / 8 + h / (4 * delta))
      ≤ kappa * ((M + 2 * h / delta) / 2 - 2) := by
  have hq4 : kappa * h / (4 * delta) = (kappa * h / delta) / 4 := by
    field_simp
  have hq2 : kappa * h / (2 * delta) = (kappa * h / delta) / 2 := by
    field_simp
  have hlog3 : (1:ℝ) < Real.log 3 := by
    have hexp := Real.exp_one_lt_d9
    have he3 : Real.exp 1 < 3 := by linarith
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he3
  have hkpos : 0 ≤ kappa := le_trans (by positivity) hkappa
  -- the `M`-linear part of the entropy is paid by an eighth of the first reserve
  have hMpay : dim * (Real.log 3 * M) ≤ kappa * (M / 8) := by
    nlinarith [hkappa, hM, hlog3, hdim]
  -- the `h`-linear part by a quarter of the second
  have hhpay : dim * h ≤ (kappa * h / delta) / 4 := by
    have h4 : 4 * dim * delta ≤ kappa := by nlinarith [hkappa, hlog3, hdim, hdelta1, hdelta]
    have hkey : 4 * (dim * h) ≤ kappa * h / delta := by
      rw [le_div_iff₀ hdelta]
      nlinarith [h4, hh, hdelta]
    linarith
  -- what remains is the reserve condition
  have hrest : dim * Real.log 2 + dim * lg + 4 * dim * Real.log 3 + 2 * kappa
      + (kappa * h / delta) / 4 ≤ (kappa * h / delta) - (kappa * h / delta) / 4 := by
    rw [hq2] at hres
    linarith [hres]
  have hMhalf : kappa * (M / 8) + kappa * (M / 8) ≤ kappa * (M / 2) := by
    nlinarith [hkpos, hM]
  have hexpand : kappa * ((M + 2 * h / delta) / 2 - 2)
      = kappa * (M / 2) + kappa * h / delta - 2 * kappa := by
    field_simp

  have hres2 : kappa * (M / 8 + h / (4 * delta))
      = kappa * (M / 8) + (kappa * h / delta) / 4 := by
    field_simp
  rw [hexpand, hres2]
  have hlhs : dim * (Real.log 2 + lg + h + Real.log 3 * M + 4 * Real.log 3)
      = dim * Real.log 2 + dim * lg + dim * h + dim * (Real.log 3 * M)
        + 4 * dim * Real.log 3 := by ring
  rw [hlhs]
  linarith [hMpay, hhpay, hrest, hMhalf]

/-! ### From a level tail to the `Γ₁` bound on the excess

The paper's factor is an exponential of a natural-valued level, and what the construction
delivers is a geometric tail on that level above a threshold `h₀`.  The excess `(X − h₀)⁺`,
taken in `ℕ`, is then `O_{Γ₁}` at the geometric scale — and the threshold itself is
deterministic, hence `O_{Γ₂}` at any scale above it.  Together they are the printed display.

The tail must be indexed by `h + 1 − h₀` rather than `h − h₀`: the event is `h < X`, i.e.
`h + 1 ≤ X`, so `h + 1` is the natural parameter, and indexing by `h − h₀` instead loses a
factor `e^{1/A}` — unbounded as the scale shrinks. -/

theorem ogammaLE_one_of_nat_tail [IsProbabilityMeasure mu] {X : Omega → ℕ} {h0 : ℕ} {A : ℝ}
    (hA : 0 < A) (hmeas : Measurable X)
    (htail : ∀ h : ℕ, h0 ≤ h →
      mu.real {omega | h < X omega} ≤ 2 * Real.exp (-(((h : ℝ) + 1 - (h0 : ℝ)) / A))) :
    SubdiffusiveProcess.OGammaLE mu 1 (4 * A) (fun omega => ((X omega - h0 : ℕ) : ℝ)) := by
  refine ogammaLE_one_of_tail hA (by fun_prop) ?_
  intro lam hlam
  set c : ℕ := ⌈lam⌉.toNat with hc
  have hceil1 : (1:ℤ) ≤ ⌈lam⌉ := Int.one_le_ceil_iff.mpr hlam
  have hcpos : 1 ≤ c := by rw [hc]; omega
  have hcz : ((c : ℕ) : ℤ) = ⌈lam⌉ := by rw [hc]; exact Int.toNat_of_nonneg (by omega)
  have hcge : lam ≤ (c : ℝ) := by
    have h3 := Int.le_ceil lam
    have h4 : ((c : ℕ) : ℝ) = ((⌈lam⌉ : ℤ) : ℝ) := by exact_mod_cast hcz
    rw [h4]
    exact h3
  set h : ℕ := h0 + c - 1 with hh
  have hh0 : h0 ≤ h := by omega
  have hsub : {omega : Omega | lam ≤ ((X omega - h0 : ℕ) : ℝ)}
      ⊆ {omega : Omega | h < X omega} := by
    intro omega homega
    simp only [mem_ofPred_eq] at homega ⊢
    have hge : (⌈lam⌉ : ℤ) ≤ ((X omega - h0 : ℕ) : ℤ) := by
      rw [Int.ceil_le]
      exact_mod_cast homega
    have hnat : c ≤ X omega - h0 := by rw [hc]; omega
    omega
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (htail h hh0) ?_
  have hstep : ((h : ℝ) + 1 - (h0 : ℝ)) = (c : ℝ) := by
    have : h + 1 = h0 + c := by omega
    have hcast : ((h + 1 : ℕ) : ℝ) = ((h0 + c : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hcast ⊢
    linarith
  rw [hstep]
  have hmono : Real.exp (-((c : ℝ) / A)) ≤ Real.exp (-(lam / A)) := by
    refine Real.exp_le_exp.mpr ?_
    have hdiv : lam / A ≤ (c : ℝ) / A := by gcongr
    linarith
  linarith

/-- The level index is measurable when the level events are. -/
theorem measurableSet_firstGood_le {F : ℕ → Set Omega} (hF : ∀ h, MeasurableSet (F h))
    (n : ℕ) : MeasurableSet {omega | firstGood F omega ≤ n} := by
  classical
  have hset : {omega | firstGood F omega ≤ n}
      = (⋃ h ∈ Finset.range (n + 1), (F h)ᶜ) ∪ (⋂ h, F h) := by
    ext omega
    simp only [mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, Set.mem_compl_iff,
      Set.mem_iInter, Finset.mem_range, exists_prop]
    constructor
    · intro hle
      by_cases hall : ∀ h, omega ∈ F h
      · exact Or.inr hall
      · push Not at hall
        obtain ⟨h, hh⟩ := hall
        have hne : {h : ℕ | omega ∉ F h}.Nonempty := ⟨h, hh⟩
        have hmem := Nat.sInf_mem hne
        exact Or.inl ⟨sInf {h : ℕ | omega ∉ F h}, Nat.lt_succ_of_le hle, hmem⟩
    · rintro (⟨h, hhn, hh⟩ | hall)
      · exact le_trans (Nat.sInf_le hh) (by omega)
      · have hempty : {h : ℕ | omega ∉ F h} = ∅ := by
          ext h; simp only [mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
          exact hall h
        rw [firstGood, hempty]
        simp
  rw [hset]
  exact ((MeasurableSet.biUnion (Set.to_countable _) fun h _ => (hF h).compl)).union
    (MeasurableSet.iInter hF)

theorem measurable_firstGood {F : ℕ → Set Omega} (hF : ∀ h, MeasurableSet (F h)) :
    Measurable (firstGood F) := by
  classical
  refine measurable_to_countable' fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : (firstGood F) ⁻¹' {0} = {omega | firstGood F omega ≤ 0} := by
      ext omega; simp
    rw [this]
    exact measurableSet_firstGood_le hF 0
  · have : (firstGood F) ⁻¹' {n}
        = {omega | firstGood F omega ≤ n} \ {omega | firstGood F omega ≤ n - 1} := by
      ext omega
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, mem_ofPred_eq]
      omega
    rw [this]
    exact (measurableSet_firstGood_le hF n).diff (measurableSet_firstGood_le hF (n - 1))

theorem measurableSet_firstGoodRunning_le {F : ℕ → ℕ → Set Omega}
    (hF : ∀ i h, MeasurableSet (F i h)) (m n : ℕ) :
    MeasurableSet {omega | firstGoodRunning F m omega ≤ n} := by
  classical
  have hset : {omega | firstGoodRunning F m omega ≤ n}
      = ⋂ i ∈ Finset.range (m + 1), {omega | firstGood (F i) omega ≤ n} := by
    ext omega
    simp only [mem_ofPred_eq, Set.mem_iInter, Finset.mem_range, firstGoodRunning,
      Finset.sup_le_iff]
  rw [hset]
  exact MeasurableSet.biInter (Set.to_countable _)
    fun i _ => measurableSet_firstGood_le (hF i) n

theorem measurable_firstGoodRunning {F : ℕ → ℕ → Set Omega}
    (hF : ∀ i h, MeasurableSet (F i h)) (m : ℕ) :
    Measurable (firstGoodRunning F m) := by
  classical
  refine measurable_to_countable' fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz : (firstGoodRunning F m) ⁻¹' {0} = {omega | firstGoodRunning F m omega ≤ 0} := by
      ext omega; simp
    rw [hz]
    exact measurableSet_firstGoodRunning_le hF m 0
  · have hz : (firstGoodRunning F m) ⁻¹' {n}
        = {omega | firstGoodRunning F m omega ≤ n}
          \ {omega | firstGoodRunning F m omega ≤ n - 1} := by
      ext omega
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, mem_ofPred_eq]
      omega
    rw [hz]
    exact (measurableSet_firstGoodRunning_le hF m n).diff
      (measurableSet_firstGoodRunning_le hF m (n - 1))

/-! ### The reserve condition, from a threshold

Every absorption in the construction asks the same thing of `h`: that `h/δ` exceed a dimensional
multiple of `1 + log(m + h + 2)`.  Because the right side grows with `h` too, that is not a
plain threshold — but it becomes one, because `log(h+2) ≤ h` for `h ≥ 2`, so the `h`-dependent
half is paid by `h` itself once `δ` is small, and only the `m`-dependent half needs a
threshold. -/

omit [MeasurableSpace Omega] in
/-- `log (h + 2) ≤ h` for `h ≥ 2`: the step that turns the reserve into a threshold. -/
theorem log_add_two_le {h : ℝ} (hh : 2 ≤ h) : Real.log (h + 2) ≤ h := by
  have hexp : h + 2 ≤ Real.exp h := by
    have hhalf : (h / 2) + 1 ≤ Real.exp (h / 2) := Real.add_one_le_exp _
    have hpos : (0:ℝ) < (h / 2) + 1 := by linarith
    have hsplit : Real.exp h = Real.exp (h / 2) * Real.exp (h / 2) := by
      rw [← Real.exp_add]; ring_nf
    have hsq : ((h / 2) + 1) * ((h / 2) + 1) ≤ Real.exp (h / 2) * Real.exp (h / 2) :=
      mul_le_mul hhalf hhalf hpos.le (le_trans hpos.le hhalf)
    rw [hsplit]
    nlinarith [hsq, hh]
  have h2 : (0:ℝ) < h + 2 := by linarith
  calc Real.log (h + 2) ≤ Real.log (Real.exp h) := Real.log_le_log h2 hexp
    _ = h := Real.log_exp h

omit [MeasurableSpace Omega] in
/-- **The reserve condition holds above a threshold.**  The `m`-dependent half needs `h₀`; the
`h`-dependent half is paid by `h` itself once `δ` is small. -/
theorem reserve_of_threshold {kappa delta Cres : ℝ} (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (hCres : 0 ≤ Cres) (hsmall : 2 * delta * Cres ≤ kappa) (m h h0 : ℕ)
    (hh0 : Cres * (1 + Real.log ((m : ℝ) + 2)) ≤ kappa * (h0 : ℝ) / (2 * delta))
    (hh : max 2 h0 ≤ h) :
    Cres * (1 + Real.log ((m : ℝ) + (h : ℝ) + 2)) ≤ kappa * (h : ℝ) / delta := by
  have h2h : (2:ℝ) ≤ (h : ℝ) := by exact_mod_cast le_trans (le_max_left 2 h0) hh
  have hh0h : (h0 : ℝ) ≤ (h : ℝ) := by exact_mod_cast le_trans (le_max_right 2 h0) hh
  have hmnn : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  -- `log(m+h+2) ≤ log(m+2) + log(h+2)`
  have hprod : (m : ℝ) + (h : ℝ) + 2 ≤ ((m : ℝ) + 2) * ((h : ℝ) + 2) := by
    nlinarith [hmnn, h2h, mul_nonneg hmnn (by linarith : (0:ℝ) ≤ (h : ℝ))]
  have hlogsum : Real.log ((m : ℝ) + (h : ℝ) + 2)
      ≤ Real.log ((m : ℝ) + 2) + Real.log ((h : ℝ) + 2) := by
    have hle := Real.log_le_log (by linarith) hprod
    rwa [Real.log_mul (by linarith) (by linarith)] at hle
  have hlogh := log_add_two_le h2h
  -- the `m`-half
  have hmhalf : Cres * (1 + Real.log ((m : ℝ) + 2)) ≤ kappa * (h : ℝ) / (2 * delta) := by
    refine le_trans hh0 ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hh0h) hkappa.le)
      (by positivity : (0:ℝ) ≤ 2 * delta)]
  -- the `h`-half
  have hhhalf : Cres * Real.log ((h : ℝ) + 2) ≤ kappa * (h : ℝ) / (2 * delta) := by
    have hstep : Cres * Real.log ((h : ℝ) + 2) ≤ Cres * (h : ℝ) :=
      mul_le_mul_of_nonneg_left hlogh hCres
    refine le_trans hstep ?_
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hsmall, h2h, hdelta]
  have hsplit : kappa * (h : ℝ) / (2 * delta) + kappa * (h : ℝ) / (2 * delta)
      = kappa * (h : ℝ) / delta := by field_simp; ring
  nlinarith [hmhalf, hhhalf, hlogsum, hCres, hsplit]

/-! ### The first stable level

`firstGood` is the first level that does not fail.  It gives the tail — `h < firstGood` forces
`ω ∈ F h` — but it does **not** give the converse the consumers need: `firstGood ≤ h` says only
that *some* level below `h` is good, and concluding that `h` itself is good requires `F`
antitone.

The level events of the macroscopic clock divergence lemma are **not** antitone in `h`: raising `h`
raises the threshold `Bh` (harder to fail) and simultaneously enlarges the ball
`B_{(j+2)e^h 3^j}` and the range of `j` (easier to fail).  Neither containment holds.

The object that gives both directions without monotonicity is the first level **after which
nothing fails**:

    firstStable F ω = inf { h : ∀ h' ≥ h, ω ∉ F h' }.

Above it every level is good — which is what the pointwise consequences need — and exceeding
`h` still forces membership in *some* `F h'` with `h' ≥ h`, so the tail costs a sum over
`h' ≥ h` instead of a single term.  For geometric level bounds that is a constant factor. -/

/-- The first level after which no level fails. -/
noncomputable def firstStable (F : ℕ → Set Omega) (omega : Omega) : ℕ :=
  sInf {h : ℕ | ∀ h', h ≤ h' → omega ∉ F h'}

omit [MeasurableSpace Omega] in
/-- **Above the first stable level, every level is good.**  This is the direction `firstGood`
cannot give. -/
theorem not_mem_of_firstStable_le {F : ℕ → Set Omega} {omega : Omega} {h : ℕ}
    (hne : ∃ h0 : ℕ, ∀ h', h0 ≤ h' → omega ∉ F h')
    (hle : firstStable F omega ≤ h) : omega ∉ F h := by
  have hne' : {h : ℕ | ∀ h', h ≤ h' → omega ∉ F h'}.Nonempty := hne
  have hmem := Nat.sInf_mem hne'
  exact hmem h hle

omit [MeasurableSpace Omega] in
/-- **The tail.**  Exceeding `h` forces some level `h' ≥ h` to fail. -/
theorem firstStable_gt_subset (F : ℕ → Set Omega) (h : ℕ) :
    {omega | h < firstStable F omega} ⊆ ⋃ i : ℕ, F (h + i) := by
  intro omega homega
  by_contra hc
  simp only [Set.mem_iUnion, not_exists] at hc
  have hmem : h ∈ {h' : ℕ | ∀ h'', h' ≤ h'' → omega ∉ F h''} := by
    intro h'' hh''
    have : h'' = h + (h'' - h) := by omega
    rw [this]
    exact hc (h'' - h)
  exact absurd (Nat.sInf_le hmem) (not_le.mpr homega)

/-- A countable union, bounded term by term. -/
theorem measureReal_iUnion_le' [IsFiniteMeasure mu] (A : ℕ → Set Omega)
    {b : ℕ → ℝ} (hb : ∀ i, mu.real (A i) ≤ b i) (hbnn : ∀ i, 0 ≤ b i)
    (hsum : Summable b) :
    mu.real (⋃ i : ℕ, A i) ≤ ∑' i, b i := by
  have hle : mu (⋃ i : ℕ, A i) ≤ ∑' i, mu (A i) := measure_iUnion_le _
  have hfin : ∀ i, mu (A i) ≠ ⊤ := fun i => measure_ne_top _ _
  have hsum' : (∑' i, mu (A i)) ≤ ∑' i, ENNReal.ofReal (b i) := by
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [← ENNReal.ofReal_toReal (hfin i)]
    exact ENNReal.ofReal_le_ofReal (hb i)
  have hchain := le_trans hle hsum'
  have hofReal : (∑' i, ENNReal.ofReal (b i)) = ENNReal.ofReal (∑' i, b i) :=
    (ENNReal.ofReal_tsum_of_nonneg hbnn hsum).symm
  rw [hofReal] at hchain
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain
  rwa [ENNReal.toReal_ofReal (tsum_nonneg hbnn)] at this

/-- A countable union of shifted events, bounded term by term. -/
theorem measureReal_iUnion_shift_le [IsFiniteMeasure mu] (F : ℕ → Set Omega) (h : ℕ)
    {b : ℕ → ℝ} (hb : ∀ i, mu.real (F (h + i)) ≤ b i) (hbnn : ∀ i, 0 ≤ b i)
    (hsum : Summable b) :
    mu.real (⋃ i : ℕ, F (h + i)) ≤ ∑' i, b i :=
  measureReal_iUnion_le' (fun i => F (h + i)) hb hbnn hsum

/-- The tail of the first stable level, summed over the levels above `h`. -/
theorem measureReal_firstStable_gt_le [IsFiniteMeasure mu] (F : ℕ → Set Omega) (h : ℕ)
    {b : ℕ → ℝ} (hb : ∀ i, mu.real (F (h + i)) ≤ b i) (hbnn : ∀ i, 0 ≤ b i)
    (hsum : Summable b) :
    mu.real {omega | h < firstStable F omega} ≤ ∑' i, b i :=
  le_trans (measureReal_mono (firstStable_gt_subset F h) (measure_ne_top _ _))
    (measureReal_iUnion_shift_le F h hb hbnn hsum)

/-- The running maximum of first-stable levels: monotone in the index everywhere. -/
noncomputable def firstStableRunning (F : ℕ → ℕ → Set Omega) (m : ℕ) (omega : Omega) : ℕ :=
  (Finset.range (m + 1)).sup fun i => firstStable (F i) omega

omit [MeasurableSpace Omega] in
theorem firstStableRunning_mono (F : ℕ → ℕ → Set Omega) {m m' : ℕ} (hm : m ≤ m')
    (omega : Omega) :
    firstStableRunning F m omega ≤ firstStableRunning F m' omega :=
  Finset.sup_mono (fun x hx => Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hx) (by omega)))

omit [MeasurableSpace Omega] in
/-- Above the running maximum, every level of every index is good. -/
theorem not_mem_of_firstStableRunning_le {F : ℕ → ℕ → Set Omega} {omega : Omega} {m h i : ℕ}
    (hi : i ≤ m) (hne : ∃ h0 : ℕ, ∀ h', h0 ≤ h' → omega ∉ F i h')
    (hle : firstStableRunning F m omega ≤ h) : omega ∉ F i h := by
  refine not_mem_of_firstStable_le hne (le_trans ?_ hle)
  exact Finset.le_sup (f := fun k => firstStable (F k) omega)
    (Finset.mem_range.mpr (by omega))

omit [MeasurableSpace Omega] in
theorem firstStableRunning_gt_subset (F : ℕ → ℕ → Set Omega) (m h : ℕ) :
    {omega | h < firstStableRunning F m omega}
      ⊆ ⋃ i ∈ Finset.range (m + 1), ⋃ k : ℕ, F i (h + k) := by
  intro omega homega
  simp only [mem_ofPred_eq, firstStableRunning, Finset.lt_sup_iff] at homega
  obtain ⟨i, hi, hlt⟩ := homega
  exact Set.mem_biUnion hi (firstStable_gt_subset (F i) h hlt)

theorem measurableSet_firstStable_le {F : ℕ → Set Omega} (hF : ∀ h, MeasurableSet (F h))
    (n : ℕ) : MeasurableSet {omega | firstStable F omega ≤ n} := by
  classical
  have hset : {omega | firstStable F omega ≤ n}
      = (⋃ h ∈ Finset.range (n + 1), ⋂ k : ℕ, (F (h + k))ᶜ)
        ∪ (⋂ h : ℕ, ⋃ k : ℕ, F (h + k)) := by
    ext omega
    simp only [mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_compl_iff, Finset.mem_range, exists_prop]
    constructor
    · intro hle
      by_cases hall : ∀ h : ℕ, ∃ k : ℕ, omega ∈ F (h + k)
      · exact Or.inr hall
      · push Not at hall
        obtain ⟨h, hh⟩ := hall
        have hmem : h ∈ {h' : ℕ | ∀ h'', h' ≤ h'' → omega ∉ F h''} := by
          intro h'' hh''
          have : h'' = h + (h'' - h) := by omega
          rw [this]
          exact hh (h'' - h)
        have hne : {h' : ℕ | ∀ h'', h' ≤ h'' → omega ∉ F h''}.Nonempty := ⟨h, hmem⟩
        refine Or.inl ⟨sInf {h' : ℕ | ∀ h'', h' ≤ h'' → omega ∉ F h''},
          Nat.lt_succ_of_le hle, ?_⟩
        intro k
        exact Nat.sInf_mem hne _ (by omega)
    · rintro (⟨h, hhn, hh⟩ | hall)
      · have hmem : h ∈ {h' : ℕ | ∀ h'', h' ≤ h'' → omega ∉ F h''} := by
          intro h'' hh''
          have : h'' = h + (h'' - h) := by omega
          rw [this]
          exact hh (h'' - h)
        exact le_trans (Nat.sInf_le hmem) (by omega)
      · have hempty : {h' : ℕ | ∀ h'', h' ≤ h'' → omega ∉ F h''} = ∅ := by
          ext h'
          constructor
          · intro hmem
            obtain ⟨k, hk⟩ := hall h'
            exact absurd hk (hmem (h' + k) (by omega))
          · intro hx
            exact absurd hx (Set.notMem_empty _)
        rw [firstStable, hempty]
        simp
  rw [hset]
  refine MeasurableSet.union ?_ ?_
  · exact MeasurableSet.biUnion (Set.to_countable _)
      fun h _ => MeasurableSet.iInter fun k => (hF _).compl
  · exact MeasurableSet.iInter fun h => MeasurableSet.iUnion fun k => hF _

theorem measurableSet_firstStableRunning_le {F : ℕ → ℕ → Set Omega}
    (hF : ∀ i h, MeasurableSet (F i h)) (m n : ℕ) :
    MeasurableSet {omega | firstStableRunning F m omega ≤ n} := by
  classical
  have hset : {omega | firstStableRunning F m omega ≤ n}
      = ⋂ i ∈ Finset.range (m + 1), {omega | firstStable (F i) omega ≤ n} := by
    ext omega
    simp only [mem_ofPred_eq, Set.mem_iInter, Finset.mem_range, firstStableRunning,
      Finset.sup_le_iff]
  rw [hset]
  exact MeasurableSet.biInter (Set.to_countable _)
    fun i _ => measurableSet_firstStable_le (hF i) n

theorem measurable_firstStableRunning {F : ℕ → ℕ → Set Omega}
    (hF : ∀ i h, MeasurableSet (F i h)) (m : ℕ) :
    Measurable (firstStableRunning F m) := by
  classical
  refine measurable_to_countable' fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz : (firstStableRunning F m) ⁻¹' {0}
        = {omega | firstStableRunning F m omega ≤ 0} := by ext omega; simp
    rw [hz]
    exact measurableSet_firstStableRunning_le hF m 0
  · have hz : (firstStableRunning F m) ⁻¹' {n}
        = {omega | firstStableRunning F m omega ≤ n}
          \ {omega | firstStableRunning F m omega ≤ n - 1} := by
      ext omega
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, mem_ofPred_eq]
      omega
    rw [hz]
    exact (measurableSet_firstStableRunning_le hF m n).diff
      (measurableSet_firstStableRunning_le hF m (n - 1))

/-- **The tail of the running first-stable level.**  Every index below `m` contributes the
whole tail of its own levels above `h`. -/
theorem measureReal_firstStableRunning_gt_le [IsFiniteMeasure mu] (F : ℕ → ℕ → Set Omega)
    (m h : ℕ) {b : ℕ → ℝ}
    (hb : ∀ i ∈ Finset.range (m + 1), ∀ k : ℕ, mu.real (F i (h + k)) ≤ b k)
    (hbnn : ∀ k, 0 ≤ b k) (hsum : Summable b) :
    mu.real {omega | h < firstStableRunning F m omega} ≤ ((m : ℝ) + 1) * ∑' k, b k := by
  refine le_trans (measureReal_mono (firstStableRunning_gt_subset F m h)
    (measure_ne_top _ _)) ?_
  have hstep := measureReal_biUnion_finset_le (mu := mu) (Finset.range (m + 1))
    (A := fun i => ⋃ k : ℕ, F i (h + k)) (b := ∑' k, b k)
    (fun i hi => measureReal_iUnion_shift_le (F i) h (hb i hi) hbnn hsum)
  rw [Finset.card_range] at hstep
  refine le_trans hstep ?_
  push_cast
  exact le_of_eq rfl

/-! ### The geometric factor

Summing a per-level exponential bound over the levels above `h` costs the factor
`(1 - e^{-c})⁻¹`, which `1 + c⁻¹` dominates. -/

theorem summable_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    Summable fun k : ℕ => Real.exp (-(c * (k : ℝ))) := by
  have hpow : (fun k : ℕ => Real.exp (-(c * (k : ℝ))))
      = fun k : ℕ => (Real.exp (-c)) ^ k := by
    funext k
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [hpow]
  exact summable_geometric_of_lt_one (Real.exp_pos _).le
    (by rw [Real.exp_lt_one_iff]; linarith)

theorem tsum_exp_neg_mul_le {c : ℝ} (hc : 0 < c) :
    (∑' k : ℕ, Real.exp (-(c * (k : ℝ)))) ≤ 1 + 1 / c := by
  have hpow : (fun k : ℕ => Real.exp (-(c * (k : ℝ))))
      = fun k : ℕ => (Real.exp (-c)) ^ k := by
    funext k
    rw [← Real.exp_nat_mul]
    ring_nf
  have hlt : Real.exp (-c) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hts : (∑' k : ℕ, Real.exp (-(c * (k : ℝ)))) = (1 - Real.exp (-c))⁻¹ := by
    rw [hpow]
    exact tsum_geometric_of_lt_one (Real.exp_pos _).le hlt
  have hcpos : (0:ℝ) < 1 + c := by linarith
  have hexp : Real.exp (-c) ≤ 1 / (1 + c) := by
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    refine one_div_le_one_div_of_le hcpos ?_
    linarith [Real.add_one_le_exp c]
  have hden : c / (1 + c) ≤ 1 - Real.exp (-c) := by
    have : (1:ℝ) - 1 / (1 + c) = c / (1 + c) := by field_simp; ring
    linarith
  have hdenpos : (0:ℝ) < c / (1 + c) := by positivity
  rw [hts, inv_eq_one_div]
  refine le_trans (one_div_le_one_div_of_le hdenpos hden) ?_
  rw [one_div_div]
  rw [add_div, div_self hc.ne']
  linarith

/-- **Scaling.**  A positive multiple of an `O_Γ` variable is `O_Γ` at the multiplied scale --
an equality of integrands, not an estimate. -/
theorem ogammaLE_const_mul {sigma A c : ℝ} (hA : 0 < A) (hc : 0 < c) {X : Omega → ℝ}
    (h : SubdiffusiveProcess.OGammaLE mu sigma A X) :
    SubdiffusiveProcess.OGammaLE mu sigma (c * A) (fun omega => c * X omega) := by
  rw [ogammaLE_iff] at h ⊢
  have hfun : integrand sigma (c * A) (fun omega => c * X omega) = integrand sigma A X := by
    funext omega
    simp only [integrand]
    congr 2
    have hmax : max (c * X omega) 0 = c * max (X omega) 0 := by
      rw [show (0:ℝ) = c * 0 by ring, ← mul_max_of_nonneg _ _ hc.le]
      ring_nf
    rw [hmax]
    field_simp
  rw [hfun]
  exact h

omit [MeasurableSpace Omega] in
/-- `log (h + 2) ≤ 2√2 · √h` for `h ≥ 2`. -/
theorem log_add_two_le_sqrt {h : ℝ} (hh : 2 ≤ h) :
    Real.log (h + 2) ≤ 2 * Real.sqrt 2 * Real.sqrt h := by
  have hpos : (0:ℝ) < h := by linarith
  have h1 : Real.log (h + 2) ≤ 2 * Real.sqrt (h + 2) := by
    have hs : (0:ℝ) < Real.sqrt (h + 2) := Real.sqrt_pos.mpr (by linarith)
    have hhalf : Real.log (h + 2) = 2 * Real.log (Real.sqrt (h + 2)) := by
      rw [Real.log_sqrt (by linarith)]
      ring
    have hlog := Real.log_le_sub_one_of_pos hs
    rw [hhalf]
    linarith
  have h2 : Real.sqrt (h + 2) ≤ Real.sqrt 2 * Real.sqrt h := by
    rw [← Real.sqrt_mul (by norm_num)]
    refine Real.sqrt_le_sqrt ?_
    linarith
  nlinarith [h1, h2, Real.sqrt_nonneg h, Real.sqrt_nonneg 2]

omit [MeasurableSpace Omega] in
/-- **The reserve, with no smallness hypothesis.**  The crude `log(h+2) ≤ h` forces a
constraint on `δ`; the sharp `log(h+2) ≤ 2√2·√h` turns it into a threshold on `h` instead,
which is what lets the reserve hold for **every** model rather than only for small `δ`. -/
theorem reserve_of_threshold_sqrt {kappa delta Cres : ℝ} (hkappa : 0 < kappa)
    (hdelta : 0 < delta) (hCres : 0 ≤ Cres) (m h h0 : ℕ)
    (hh0 : Cres * (1 + Real.log ((m : ℝ) + 2)) ≤ kappa * (h0 : ℝ) / (2 * delta))
    (hthr : 32 * Cres ^ 2 * delta ^ 2 ≤ kappa ^ 2 * (h : ℝ))
    (hh : max 2 h0 ≤ h) :
    Cres * (1 + Real.log ((m : ℝ) + (h : ℝ) + 2)) ≤ kappa * (h : ℝ) / delta := by
  have h2h : (2:ℝ) ≤ (h : ℝ) := by exact_mod_cast le_trans (le_max_left 2 h0) hh
  have hh0h : (h0 : ℝ) ≤ (h : ℝ) := by exact_mod_cast le_trans (le_max_right 2 h0) hh
  have hmnn : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hprod : (m : ℝ) + (h : ℝ) + 2 ≤ ((m : ℝ) + 2) * ((h : ℝ) + 2) := by
    nlinarith [hmnn, h2h, mul_nonneg hmnn (by linarith : (0:ℝ) ≤ (h : ℝ))]
  have hlogsum : Real.log ((m : ℝ) + (h : ℝ) + 2)
      ≤ Real.log ((m : ℝ) + 2) + Real.log ((h : ℝ) + 2) := by
    have hle := Real.log_le_log (by linarith) hprod
    rwa [Real.log_mul (by linarith) (by linarith)] at hle
  have hmhalf : Cres * (1 + Real.log ((m : ℝ) + 2)) ≤ kappa * (h : ℝ) / (2 * delta) := by
    refine le_trans hh0 ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hh0h) hkappa.le)
      (by positivity : (0:ℝ) ≤ 2 * delta)]
  have hhhalf : Cres * Real.log ((h : ℝ) + 2) ≤ kappa * (h : ℝ) / (2 * delta) := by
    have hsq : Cres * Real.log ((h : ℝ) + 2)
        ≤ Cres * (2 * Real.sqrt 2 * Real.sqrt (h : ℝ)) :=
      mul_le_mul_of_nonneg_left (log_add_two_le_sqrt h2h) hCres
    refine le_trans hsq ?_
    rw [le_div_iff₀ (by positivity)]
    have hsh : Real.sqrt (h : ℝ) * Real.sqrt (h : ℝ) = (h : ℝ) :=
      Real.mul_self_sqrt (by linarith)
    have hshpos : (0:ℝ) < Real.sqrt (h : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hLnn : (0:ℝ) ≤ Cres * (2 * Real.sqrt 2 * Real.sqrt (h : ℝ)) * (2 * delta) := by
      positivity
    have hRnn : (0:ℝ) ≤ kappa * (h : ℝ) := by positivity
    have hsq : (Cres * (2 * Real.sqrt 2 * Real.sqrt (h : ℝ)) * (2 * delta)) ^ 2
        ≤ (kappa * (h : ℝ)) ^ 2 := by
      have hexp : (Cres * (2 * Real.sqrt 2 * Real.sqrt (h : ℝ)) * (2 * delta)) ^ 2
          = 32 * Cres ^ 2 * delta ^ 2 * (h : ℝ) := by
        have : Real.sqrt 2 ^ 2 = 2 := by
          rw [sq]; exact hs2
        have h2 : Real.sqrt (h : ℝ) ^ 2 = (h : ℝ) := by
          rw [sq]; exact hsh
        ring_nf
        rw [this, h2]
        ring
      rw [hexp]
      nlinarith [hthr, h2h]
    nlinarith [hsq, hLnn, hRnn]
  have hsplit : kappa * (h : ℝ) / (2 * delta) + kappa * (h : ℝ) / (2 * delta)
      = kappa * (h : ℝ) / delta := by field_simp; ring
  have hmul : Cres * Real.log ((m : ℝ) + (h : ℝ) + 2)
      ≤ Cres * (Real.log ((m : ℝ) + 2) + Real.log ((h : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_left hlogsum hCres
  linarith [hmhalf, hhhalf, hmul, hsplit.le, hsplit.ge]

/-! ### The level is almost surely stable

`firstStable` is the honest first-stable level only where the failing levels are bounded.
Borel-Cantelli gives that from the summability of the level probabilities, and a bound valid
only above a threshold suffices -- the levels below it are finitely many. -/

theorem ae_exists_stable_level [IsFiniteMeasure mu] (F : ℕ → Set Omega)
    {b : ℕ → ℝ} (hb : ∀ h, mu.real (F h) ≤ b h) (hbnn : ∀ h, 0 ≤ b h) (hsum : Summable b) :
    ∀ᵐ omega ∂mu, ∃ h0 : ℕ, ∀ h', h0 ≤ h' → omega ∉ F h' := by
  have hfin : (∑' h, mu (F h)) ≠ ⊤ := by
    have hle : (∑' h, mu (F h)) ≤ ∑' h, ENNReal.ofReal (b h) := by
      refine ENNReal.tsum_le_tsum fun h => ?_
      rw [← ENNReal.ofReal_toReal (measure_ne_top mu (F h))]
      exact ENNReal.ofReal_le_ofReal (hb h)
    have hofReal : (∑' h, ENNReal.ofReal (b h)) = ENNReal.ofReal (∑' h, b h) :=
      (ENNReal.ofReal_tsum_of_nonneg hbnn hsum).symm
    rw [hofReal] at hle
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  filter_upwards [ae_finite_setOfPred_mem hfin] with omega hfinite
  obtain ⟨c, hc⟩ := hfinite.bddAbove
  refine ⟨c + 1, fun h' hh' hmem => ?_⟩
  have hle := hc (show h' ∈ {i | omega ∈ F i} from hmem)
  omega

/-- The same, from a bound that holds only above a threshold. -/
theorem ae_exists_stable_level_of_tail [IsFiniteMeasure mu] (F : ℕ → Set Omega) (T : ℕ)
    {b : ℕ → ℝ} (hb : ∀ h, T ≤ h → mu.real (F h) ≤ b h) (hbnn : ∀ h, 0 ≤ b h)
    (hsum : Summable b) :
    ∀ᵐ omega ∂mu, ∃ h0 : ℕ, ∀ h', h0 ≤ h' → omega ∉ F h' := by
  have hshift := ae_exists_stable_level (mu := mu) (fun i => F (T + i))
    (b := fun i => b (T + i)) (fun i => hb (T + i) (by omega)) (fun i => hbnn _)
    (by
      have := (summable_nat_add_iff (f := b) T).mpr hsum
      simpa [Nat.add_comm] using this)
  filter_upwards [hshift] with omega homega
  obtain ⟨i0, hi0⟩ := homega
  refine ⟨T + i0, fun h' hh' => ?_⟩
  have hrw : h' = T + (h' - T) := by omega
  rw [hrw]
  exact hi0 (h' - T) (by omega)

/-! ### The discounted level

The index-growth clause of the macroscopic clock divergence lemma is *pointwise in the sample*:
`X_{m+j} ≤ e^{a δ j} X_m` for every `omega`, so a running maximum of levels is the wrong
object -- it can jump arbitrarily at one index step.  The right object discounts every index
by `a` per step and maximizes over **all** indices, future ones included:

`Λ_m = sup_i (L_i - a (i - m)⁺)`.

It dominates `L_m`, is nondecreasing in `m`, and increases by at most `a` per step, all three
for every sample.  Where the set is unbounded the `ℕ`-valued `sSup` returns its junk `0`, and
boundedness does not depend on `m`, so the three pointwise clauses survive on that set too.

This is the source's own device: the closing paragraph of the proof replaces the constructed
factors by `sup_{j≥0} e^{-a δ j} X^{time,0}_{m+j}`, which "dominate the original ones, are
nondecreasing in `m`, and satisfy the index-growth clause **by shifting the supremum**". -/

/-- The levels available at index `m` once the index gap is discounted at rate `a`. -/
def discountSet (L : ℕ → Omega → ℕ) (a m : ℕ) (omega : Omega) : Set ℕ :=
  {v : ℕ | ∃ i : ℕ, v + a * (i - m) ≤ L i omega}

/-- `Λ_m`: the discounted supremum of a family of levels. -/
noncomputable def levelDiscounted (L : ℕ → Omega → ℕ) (a m : ℕ) (omega : Omega) : ℕ :=
  sSup (discountSet L a m omega)

variable {L : ℕ → Omega → ℕ} {a m m' : ℕ} {omega : Omega}

omit [MeasurableSpace Omega] in
theorem zero_mem_discountSet : (0 : ℕ) ∈ discountSet L a m omega :=
  ⟨m, by simp⟩

omit [MeasurableSpace Omega] in
theorem nonempty_discountSet : (discountSet L a m omega).Nonempty :=
  ⟨0, zero_mem_discountSet⟩

omit [MeasurableSpace Omega] in
theorem discountSet_subset (hm : m ≤ m') :
    discountSet L a m omega ⊆ discountSet L a m' omega := by
  rintro v ⟨i, hi⟩
  refine ⟨i, le_trans ?_ hi⟩
  have : a * (i - m') ≤ a * (i - m) := Nat.mul_le_mul_left a (by omega)
  omega

omit [MeasurableSpace Omega] in
/-- The reverse inclusion, after paying `a` per index step. -/
theorem discountSet_shift (hm : m ≤ m') {v : ℕ} (hv : v ∈ discountSet L a m' omega) :
    v - a * (m' - m) ∈ discountSet L a m omega := by
  rcases le_or_gt v (a * (m' - m)) with hsmall | hbig
  · have : v - a * (m' - m) = 0 := by omega
    rw [this]
    exact zero_mem_discountSet
  · obtain ⟨i, hi⟩ := hv
    refine ⟨i, le_trans ?_ hi⟩
    have hsplit : a * (i - m) ≤ a * (i - m') + a * (m' - m) := by
      have := Nat.mul_le_mul_left a (show i - m ≤ (i - m') + (m' - m) by omega)
      rw [Nat.mul_add] at this
      omega
    omega

omit [MeasurableSpace Omega] in
theorem bddAbove_discountSet_of_le (hm : m ≤ m')
    (hb : BddAbove (discountSet L a m omega)) :
    BddAbove (discountSet L a m' omega) := by
  obtain ⟨c, hc⟩ := hb
  refine ⟨c + a * (m' - m), fun v hv => ?_⟩
  have := hc (discountSet_shift hm hv)
  omega

omit [MeasurableSpace Omega] in
theorem bddAbove_discountSet_iff (hm : m ≤ m') :
    BddAbove (discountSet L a m omega) ↔ BddAbove (discountSet L a m' omega) :=
  ⟨bddAbove_discountSet_of_le hm, fun h => h.mono (discountSet_subset hm)⟩

omit [MeasurableSpace Omega] in
theorem levelDiscounted_eq_zero_of_not_bddAbove
    (hb : ¬ BddAbove (discountSet L a m omega)) :
    levelDiscounted L a m omega = 0 := by
  refine Set.Infinite.Nat.sSup_eq_zero ?_
  intro hfin
  exact hb hfin.bddAbove

omit [MeasurableSpace Omega] in
/-- **Clause (ii): nondecreasing in the index.** -/
theorem levelDiscounted_mono (hm : m ≤ m') :
    levelDiscounted L a m omega ≤ levelDiscounted L a m' omega := by
  by_cases hb : BddAbove (discountSet L a m' omega)
  · exact csSup_le_csSup hb nonempty_discountSet (discountSet_subset hm)
  · have hb' : ¬ BddAbove (discountSet L a m omega) := fun h =>
      hb (bddAbove_discountSet_of_le hm h)
    rw [levelDiscounted_eq_zero_of_not_bddAbove hb',
      levelDiscounted_eq_zero_of_not_bddAbove hb]

omit [MeasurableSpace Omega] in
/-- **Clause (iii): at most `a` per index step, for every sample.** -/
theorem levelDiscounted_add_le (j : ℕ) :
    levelDiscounted L a (m + j) omega ≤ levelDiscounted L a m omega + a * j := by
  by_cases hb : BddAbove (discountSet L a m omega)
  · have hbj : BddAbove (discountSet L a (m + j) omega) :=
      bddAbove_discountSet_of_le (by omega) hb
    refine csSup_le nonempty_discountSet fun v hv => ?_
    have hshift := discountSet_shift (show m ≤ m + j by omega) hv
    have hle : v - a * (m + j - m) ≤ levelDiscounted L a m omega := le_csSup hb hshift
    have hsimp : m + j - m = j := by omega
    rw [hsimp] at hle
    omega
  · have hbj : ¬ BddAbove (discountSet L a (m + j) omega) := fun h =>
      hb (h.mono (discountSet_subset (by omega)))
    rw [levelDiscounted_eq_zero_of_not_bddAbove hbj]
    exact Nat.zero_le _

omit [MeasurableSpace Omega] in
/-- **Clause (i'): it dominates its own index's level**, wherever it is not junk. -/
theorem le_levelDiscounted (hb : BddAbove (discountSet L a m omega)) :
    L m omega ≤ levelDiscounted L a m omega :=
  le_csSup hb ⟨m, by simp⟩

omit [MeasurableSpace Omega] in
/-- **The tail.**  Exceeding `h` forces some index to exceed `h` plus its own discount. -/
theorem levelDiscounted_gt_subset (L : ℕ → Omega → ℕ) (a m h : ℕ) :
    {omega | h < levelDiscounted L a m omega}
      ⊆ ⋃ i : ℕ, {omega | h + a * (i - m) < L i omega} := by
  intro omega homega
  simp only [mem_ofPred_eq] at homega
  have hs : levelDiscounted L a m omega = sSup (discountSet L a m omega) := rfl
  rw [hs] at homega
  by_cases hb : BddAbove (discountSet L a m omega)
  · obtain ⟨i, hi⟩ := Nat.sSup_mem (nonempty_discountSet (L := L) (a := a) (m := m)) hb
    exact Set.mem_iUnion.mpr ⟨i, by simp only [mem_ofPred_eq]; omega⟩
  · rw [← hs, levelDiscounted_eq_zero_of_not_bddAbove hb] at homega
    exact absurd homega (by omega)

theorem measureReal_levelDiscounted_gt_le [IsFiniteMeasure mu] (L : ℕ → Omega → ℕ)
    (a m h : ℕ) {b : ℕ → ℝ}
    (hb : ∀ i, mu.real {omega | h + a * (i - m) < L i omega} ≤ b i)
    (hbnn : ∀ i, 0 ≤ b i) (hsum : Summable b) :
    mu.real {omega | h < levelDiscounted L a m omega} ≤ ∑' i, b i :=
  le_trans (measureReal_mono (levelDiscounted_gt_subset L a m h) (measure_ne_top _ _))
    (measureReal_iUnion_le' _ hb hbnn hsum)

/-! ### The Gaussian level exponent is geometric in the level

The printed level failure is Gaussian in `h` with variance `δ²(D_m + h)`, so the sum over the
levels above `h` is **not** a geometric series in `h` -- but it is dominated by one.  The
function `h ↦ h²/(m+h)` is convex, and its tangent at `h` has slope at least `h/(m+h)`:

    (h+k)²/(m+h+k) ≥ h²/(m+h) + (h/(m+h)) · k,

which after clearing denominators is `0 ≤ km`.  So the existing geometric machinery applies
verbatim, with the rate `h/(m+h)` in place of a constant. -/

theorem sq_div_add_tangent {m h k : ℝ} (hm : 0 ≤ m) (hh : 0 < h) (hk : 0 ≤ k) :
    h ^ 2 / (m + h) + (h / (m + h)) * k ≤ (h + k) ^ 2 / (m + h + k) := by
  have hmh : (0:ℝ) < m + h := by linarith
  have hmhk : (0:ℝ) < m + h + k := by linarith
  have hlhs : h ^ 2 / (m + h) + (h / (m + h)) * k = (h ^ 2 + h * k) / (m + h) := by
    field_simp
  rw [hlhs, div_le_div_iff₀ hmh hmhk]
  nlinarith [mul_nonneg hk hm, hh.le, hk, hm]

/-! ### The geometric bookkeeping of the index sum

The indices below `m` carry no discount, so they contribute `m+1` copies; the indices above
carry a geometric series.  Both the level tail and the a.s. boundedness use the same two
facts about the majorant. -/

theorem summable_discount_bound {c F : ℝ} (hc : 0 < c) (m : ℕ) :
    Summable fun i : ℕ => 2 * Real.exp (-(F + c * ((i - m : ℕ) : ℝ))) := by
  have hbnn : ∀ i : ℕ, 0 ≤ 2 * Real.exp (-(F + c * ((i - m : ℕ) : ℝ))) := by
    intro i; positivity
  have hmaj : ∀ i : ℕ, 2 * Real.exp (-(F + c * ((i - m : ℕ) : ℝ)))
      ≤ (2 * Real.exp (-F) * Real.exp (c * (m : ℝ))) * Real.exp (-(c * (i : ℝ))) := by
    intro i
    have hstep : (i : ℝ) - (m : ℝ) ≤ ((i - m : ℕ) : ℝ) := by
      rcases le_or_gt i m with hle | hgt
      · have h1 : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast hle
        have h2 : (0:ℝ) ≤ ((i - m : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      · have heq : ((i - m : ℕ) : ℝ) = (i : ℝ) - (m : ℝ) := by
          have hmi : m ≤ i := le_of_lt hgt
          push_cast [Nat.cast_sub hmi]
          ring
        linarith [heq.ge, heq.le]
    have hrw : (2 * Real.exp (-F) * Real.exp (c * (m : ℝ))) * Real.exp (-(c * (i : ℝ)))
        = 2 * Real.exp (-F + c * (m : ℝ) + -(c * (i : ℝ))) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    rw [hrw]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    nlinarith [hstep, hc.le]
  exact Summable.of_nonneg_of_le hbnn hmaj ((summable_exp_neg_mul hc).mul_left _)

theorem tsum_discount_bound_le {c F : ℝ} (hc : 0 < c) (m : ℕ) :
    (∑' i : ℕ, 2 * Real.exp (-(F + c * ((i - m : ℕ) : ℝ))))
      ≤ 2 * ((m : ℝ) + 2 + 1 / c) * Real.exp (-F) := by
  set b : ℕ → ℝ := fun i => 2 * Real.exp (-(F + c * ((i - m : ℕ) : ℝ))) with hbdef
  have hsum : Summable b := summable_discount_bound hc m
  rw [← hsum.sum_add_tsum_nat_add (m + 1)]
  have hhead : (∑ i ∈ Finset.range (m + 1), b i) ≤ ((m : ℝ) + 1) * (2 * Real.exp (-F)) := by
    have hterm : ∀ i ∈ Finset.range (m + 1), b i = 2 * Real.exp (-F) := by
      intro i hi
      have hz : i - m = 0 := by
        have := Finset.mem_range.mp hi
        omega
      rw [hbdef]
      simp only [hz]
      norm_num
    have h1 : (∑ i ∈ Finset.range (m + 1), b i)
        = ∑ _i ∈ Finset.range (m + 1), 2 * Real.exp (-F) :=
      Finset.sum_congr rfl hterm
    rw [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    linarith
  have htail : (∑' k : ℕ, b (k + (m + 1)))
      ≤ (2 * Real.exp (-F)) * (1 + 1 / c) := by
    have hterm : ∀ k : ℕ, b (k + (m + 1))
        = (2 * Real.exp (-F)) * Real.exp (-(c * ((k : ℝ) + 1))) := by
      intro k
      have hk : k + (m + 1) - m = k + 1 := by omega
      rw [hbdef]
      simp only [hk]
      rw [mul_assoc, ← Real.exp_add]
      push_cast
      ring_nf
    have hle : ∀ k : ℕ, b (k + (m + 1))
        ≤ (2 * Real.exp (-F)) * Real.exp (-(c * (k : ℝ))) := by
      intro k
      rw [hterm k]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      nlinarith [hc.le, Nat.cast_nonneg (α := ℝ) k]
    have hsum2 : Summable fun k : ℕ => b (k + (m + 1)) :=
      (summable_nat_add_iff (m + 1)).mpr hsum
    refine le_trans (Summable.tsum_le_tsum hle hsum2
      ((summable_exp_neg_mul hc).mul_left _)) ?_
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (tsum_exp_neg_mul_le hc) (by positivity)
  have hcinv : (0:ℝ) < 1 / c := by positivity
  nlinarith [hhead, htail, Real.exp_pos (-F)]

/-- **The discounted level's tail, summed.** -/
theorem measureReal_levelDiscounted_gt_geom [IsFiniteMeasure mu] (L : ℕ → Omega → ℕ)
    (a m h : ℕ) {c F : ℝ} (hc : 0 < c)
    (hb : ∀ i, mu.real {omega | h + a * (i - m) < L i omega}
      ≤ 2 * Real.exp (-(F + c * ((i - m : ℕ) : ℝ)))) :
    mu.real {omega | h < levelDiscounted L a m omega}
      ≤ 2 * ((m : ℝ) + 2 + 1 / c) * Real.exp (-F) :=
  le_trans (measureReal_levelDiscounted_gt_le (mu := mu) L a m h hb
      (fun i => by positivity) (summable_discount_bound hc m))
    (tsum_discount_bound_le hc m)

omit [MeasurableSpace Omega] in
/-- Unboundedness of the discount set is witnessed at every level. -/
theorem not_bddAbove_discountSet_subset (L : ℕ → Omega → ℕ) (a m h : ℕ) :
    {omega | ¬ BddAbove (discountSet L a m omega)}
      ⊆ ⋃ i : ℕ, {omega | h + a * (i - m) < L i omega} := by
  intro omega homega
  simp only [mem_ofPred_eq] at homega
  have hex : ∃ v ∈ discountSet L a m omega, h < v := by
    by_contra hcon
    push Not at hcon
    exact homega ⟨h, fun v hv => hcon v hv⟩
  obtain ⟨v, ⟨i, hi⟩, hv⟩ := hex
  exact Set.mem_iUnion.mpr ⟨i, by simp only [mem_ofPred_eq]; omega⟩

theorem measureReal_not_bddAbove_le [IsFiniteMeasure mu] (L : ℕ → Omega → ℕ) (a m h : ℕ)
    {b : ℕ → ℝ} (hb : ∀ i, mu.real {omega | h + a * (i - m) < L i omega} ≤ b i)
    (hbnn : ∀ i, 0 ≤ b i) (hsum : Summable b) :
    mu.real {omega | ¬ BddAbove (discountSet L a m omega)} ≤ ∑' i, b i :=
  le_trans (measureReal_mono (not_bddAbove_discountSet_subset L a m h) (measure_ne_top _ _))
    (measureReal_iUnion_le' _ hb hbnn hsum)

/-- **The same sum bounds the unbounded set**, at every level -- which is what drives its
measure to zero. -/
theorem measureReal_not_bddAbove_geom [IsFiniteMeasure mu] (L : ℕ → Omega → ℕ)
    (a m h : ℕ) {c F : ℝ} (hc : 0 < c)
    (hb : ∀ i, mu.real {omega | h + a * (i - m) < L i omega}
      ≤ 2 * Real.exp (-(F + c * ((i - m : ℕ) : ℝ)))) :
    mu.real {omega | ¬ BddAbove (discountSet L a m omega)}
      ≤ 2 * ((m : ℝ) + 2 + 1 / c) * Real.exp (-F) :=
  le_trans (measureReal_not_bddAbove_le (mu := mu) L a m h hb
      (fun i => by positivity) (summable_discount_bound hc m))
    (tsum_discount_bound_le hc m)

/-- **The discount set is almost surely bounded**, hence the level is almost surely its
honest supremum rather than the `ℕ`-valued junk `0`.  This is the source's "countable
intersection of the probability-one events on which all `H_m(z)` are finite". -/
theorem ae_bddAbove_discountSet [IsFiniteMeasure mu] (L : ℕ → Omega → ℕ) (a m : ℕ)
    (hsmall : ∀ eps : ℝ, 0 < eps →
      mu.real {omega | ¬ BddAbove (discountSet L a m omega)} ≤ eps) :
    ∀ᵐ omega ∂mu, BddAbove (discountSet L a m omega) := by
  have hzero : mu.real {omega | ¬ BddAbove (discountSet L a m omega)} = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun eps heps => ?_) measureReal_nonneg
    simpa using hsmall eps heps
  have hfin : mu {omega | ¬ BddAbove (discountSet L a m omega)} ≠ ⊤ := measure_ne_top _ _
  rw [ae_iff]
  rw [Measure.real, ENNReal.toReal_eq_zero_iff] at hzero
  tauto

omit [MeasurableSpace Omega] in
/-- **Monotone in the family**, where both discount sets are bounded. -/
theorem levelDiscounted_mono_family {L L' : ℕ → Omega → ℕ} (hL : ∀ i, L i omega ≤ L' i omega)
    (hb : BddAbove (discountSet L' a m omega)) :
    levelDiscounted L a m omega ≤ levelDiscounted L' a m omega := by
  refine csSup_le_csSup hb nonempty_discountSet ?_
  rintro v ⟨i, hi⟩
  exact ⟨i, le_trans hi (hL i)⟩

/-- The exact description of the sublevel sets: either the next level is unavailable, or the
set is unbounded and the `ℕ`-valued supremum is its junk `0`. -/
theorem measurableSet_levelDiscounted_le {L : ℕ → Omega → ℕ}
    (hL : ∀ i, Measurable (L i)) (a m n : ℕ) :
    MeasurableSet {omega | levelDiscounted L a m omega ≤ n} := by
  classical
  have hset : {omega | levelDiscounted L a m omega ≤ n}
      = (⋂ i : ℕ, {omega | L i omega < n + 1 + a * (i - m)})
        ∪ (⋂ h : ℕ, ⋃ i : ℕ, {omega | h + a * (i - m) < L i omega}) := by
    ext omega
    simp only [mem_ofPred_eq, Set.mem_union, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro hle
      by_cases hb : BddAbove (discountSet L a m omega)
      · refine Or.inl fun i => ?_
        by_contra hcon
        push Not at hcon
        have hmem : n + 1 ∈ discountSet L a m omega := ⟨i, by omega⟩
        have := le_csSup hb hmem
        have hs : levelDiscounted L a m omega = sSup (discountSet L a m omega) := rfl
        omega
      · refine Or.inr fun h => ?_
        have := not_bddAbove_discountSet_subset L a m h (by simpa using hb)
        simpa using this
    · rintro (hno | hall)
      · by_cases hb : BddAbove (discountSet L a m omega)
        · refine csSup_le nonempty_discountSet fun v hv => ?_
          obtain ⟨i, hi⟩ := hv
          have := hno i
          omega
        · rw [levelDiscounted_eq_zero_of_not_bddAbove hb]
          exact Nat.zero_le _
      · by_cases hb : BddAbove (discountSet L a m omega)
        · obtain ⟨c, hc⟩ := hb
          obtain ⟨i, hi⟩ := hall c
          have hmem : c + 1 ∈ discountSet L a m omega := ⟨i, by omega⟩
          have := hc hmem
          omega
        · rw [levelDiscounted_eq_zero_of_not_bddAbove hb]
          exact Nat.zero_le _
  have hpre : ∀ (i : ℕ) (s : Set ℕ), MeasurableSet {omega | L i omega ∈ s} :=
    fun i s => (hL i) MeasurableSet.of_discrete
  rw [hset]
  refine MeasurableSet.union ?_ ?_
  · exact MeasurableSet.iInter fun i =>
      hpre i {v | v < n + 1 + a * (i - m)}
  · exact MeasurableSet.iInter fun h =>
      MeasurableSet.iUnion fun i => hpre i {v | h + a * (i - m) < v}

theorem measurable_levelDiscounted {L : ℕ → Omega → ℕ} (hL : ∀ i, Measurable (L i)) (a m : ℕ) :
    Measurable (levelDiscounted L a m) := by
  classical
  refine measurable_to_countable' fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz : (levelDiscounted L a m) ⁻¹' {0}
        = {omega | levelDiscounted L a m omega ≤ 0} := by ext omega; simp
    rw [hz]
    exact measurableSet_levelDiscounted_le hL a m 0
  · have hz : (levelDiscounted L a m) ⁻¹' {n}
        = {omega | levelDiscounted L a m omega ≤ n}
          \ {omega | levelDiscounted L a m omega ≤ n - 1} := by
      ext omega
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, mem_ofPred_eq]
      omega
    rw [hz]
    exact (measurableSet_levelDiscounted_le hL a m n).diff
      (measurableSet_levelDiscounted_le hL a m (n - 1))

/-- **The two-term level tail, summed.**  Each term sums by the one-term bound; the linear
family's rate and the Gaussian family's rate are different, so they are carried separately all
the way to the `Γ₂ + Γ₁` split at the end. -/
theorem measureReal_levelDiscounted_gt_geom_two [IsFiniteMeasure mu] (L : ℕ → Omega → ℕ)
    (a m h : ℕ) {c1 c2 F1 F2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hb : ∀ i, mu.real {omega | h + a * (i - m) < L i omega}
      ≤ 4 * (2 * Real.exp (-(F1 + c1 * ((i - m : ℕ) : ℝ))))
        + 2 * Real.exp (-(F2 + c2 * ((i - m : ℕ) : ℝ)))) :
    mu.real {omega | h < levelDiscounted L a m omega}
      ≤ 8 * ((m : ℝ) + 2 + 1 / c1) * Real.exp (-F1)
        + 2 * ((m : ℝ) + 2 + 1 / c2) * Real.exp (-F2) := by
  set b1 : ℕ → ℝ := fun i => 2 * Real.exp (-(F1 + c1 * ((i - m : ℕ) : ℝ))) with hb1
  set b2 : ℕ → ℝ := fun i => 2 * Real.exp (-(F2 + c2 * ((i - m : ℕ) : ℝ))) with hb2
  have hs1 : Summable b1 := summable_discount_bound hc1 m
  have hs2 : Summable b2 := summable_discount_bound hc2 m
  have hsum : Summable fun i => 4 * b1 i + b2 i := (hs1.mul_left 4).add hs2
  have hnn : ∀ i, 0 ≤ 4 * b1 i + b2 i := by
    intro i
    rw [hb1, hb2]
    positivity
  have hmain := measureReal_levelDiscounted_gt_le (mu := mu) L a m h hb hnn hsum
  refine le_trans hmain ?_
  rw [Summable.tsum_add (hs1.mul_left 4) hs2, tsum_mul_left]
  have h1 := tsum_discount_bound_le (c := c1) (F := F1) hc1 m
  have h2 := tsum_discount_bound_le (c := c2) (F := F2) hc2 m
  rw [← hb1] at h1
  rw [← hb2] at h2
  have hnn1 : (0:ℝ) ≤ 4 := by norm_num
  nlinarith [h1, h2, Real.exp_pos (-F1), Real.exp_pos (-F2)]

/-- The instance the level construction uses: the levels are first-stable levels. -/
noncomputable def stableDiscounted (F : ℕ → ℕ → Set Omega) (a m : ℕ) (omega : Omega) : ℕ :=
  levelDiscounted (fun i => firstStable (F i)) a m omega

omit [MeasurableSpace Omega] in
/-- **Nested families give a monotone level.**  This is the source's own route to the
monotonicity of `X_m` in `m`: the testing families at index `m'` are contained in those at
`m`, so the last failing level only shrinks. -/
theorem firstStable_mono_of_subset {G : ℕ → Set Omega} {F : ℕ → Set Omega}
    (hsub : ∀ h, G h ⊆ F h) {omega : Omega}
    (hne : ∃ h0 : ℕ, ∀ h', h0 ≤ h' → omega ∉ F h') :
    firstStable G omega ≤ firstStable F omega := by
  obtain ⟨h0, hh0⟩ := hne
  have hmem : firstStable F omega ∈ {h : ℕ | ∀ h', h ≤ h' → omega ∉ F h'} :=
    Nat.sInf_mem ⟨h0, hh0⟩
  exact Nat.sInf_le fun h' hh' => fun hmemG => hmem h' hh' (hsub h' hmemG)

/-! ### Dyadic gating

The source tests dyadic levels `h ∈ 2^ℤ`.  With unit-spaced levels the union over `h' ≥ h` of a
Gaussian tail `exp(−h'²/σ²)` costs a `σ²/h ≍ √m` prefactor, which would force a `√(m log m)`
threshold the printed display cannot pay; over dyadic levels the same union is geometric with
no prefactor.  `dyadicGate F` is the family that fails only at powers of two, so its first
stable level is one more than the last failing dyadic level. -/

/-- `h` is a power of two, decidably. -/
def IsPow2 (h : ℕ) : Prop := 2 ^ Nat.log 2 h = h

instance instDecidableIsPow2 (h : ℕ) : Decidable (IsPow2 h) := by
  unfold IsPow2; infer_instance

theorem isPow2_pow (k : ℕ) : IsPow2 (2 ^ k) := by
  unfold IsPow2
  rw [Nat.log_pow (by norm_num : 1 < 2)]

/-- The family gated to dyadic levels. -/
def dyadicGate (F : ℕ → Set Omega) (h : ℕ) : Set Omega :=
  if IsPow2 h then F h else ∅

omit [MeasurableSpace Omega] in
theorem dyadicGate_subset (F : ℕ → Set Omega) (h : ℕ) : dyadicGate F h ⊆ F h := by
  unfold dyadicGate
  split_ifs
  · exact le_rfl
  · exact Set.empty_subset _

omit [MeasurableSpace Omega] in
theorem dyadicGate_pow (F : ℕ → Set Omega) (k : ℕ) : dyadicGate F (2 ^ k) = F (2 ^ k) := by
  unfold dyadicGate
  rw [ite_eq_left (isPow2_pow k)]

omit [MeasurableSpace Omega] in
/-- Off the gated family at a dyadic level is off the family there. -/
theorem not_mem_of_not_mem_dyadicGate {F : ℕ → Set Omega} {omega : Omega} {k : ℕ}
    (h : omega ∉ dyadicGate F (2 ^ k)) : omega ∉ F (2 ^ k) := by
  rwa [dyadicGate_pow] at h

theorem measurableSet_dyadicGate {F : ℕ → Set Omega} (hF : ∀ h, MeasurableSet (F h)) (h : ℕ) :
    MeasurableSet (dyadicGate F h) := by
  unfold dyadicGate
  split_ifs
  · exact hF h
  · exact MeasurableSet.empty

omit [MeasurableSpace Omega] in
/-- **Exceeding `h` means some dyadic level `2^(clog 2 h + j)` fails.** -/
theorem firstStable_dyadicGate_gt_subset (F : ℕ → Set Omega) (h : ℕ) :
    {omega | h < firstStable (dyadicGate F) omega}
      ⊆ ⋃ j : ℕ, F (2 ^ (Nat.clog 2 h + j)) := by
  intro omega homega
  have hmem := firstStable_gt_subset (dyadicGate F) h homega
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  unfold dyadicGate at hi
  split_ifs at hi with hp
  · have hk : h + i = 2 ^ Nat.log 2 (h + i) := hp.symm
    have hle : Nat.clog 2 h ≤ Nat.log 2 (h + i) := by
      rw [Nat.clog_le_iff_le_pow (by norm_num : 1 < 2), ← hk]
      exact Nat.le_add_right h i
    refine Set.mem_iUnion.mpr ⟨Nat.log 2 (h + i) - Nat.clog 2 h, ?_⟩
    have hidx : Nat.clog 2 h + (Nat.log 2 (h + i) - Nat.clog 2 h) = Nat.log 2 (h + i) := by
      omega
    rw [hidx, ← hk]
    exact hi
  · exact absurd hi (Set.notMem_empty _)

/-- **The dyadic tail**, bounded term by term along `k ↦ clog 2 h + k`. -/
theorem measureReal_firstStable_dyadicGate_gt_le [IsFiniteMeasure mu] (F : ℕ → Set Omega)
    (h : ℕ) {b : ℕ → ℝ} (hb : ∀ j, mu.real (F (2 ^ (Nat.clog 2 h + j))) ≤ b j)
    (hbnn : ∀ j, 0 ≤ b j) (hsum : Summable b) :
    mu.real {omega | h < firstStable (dyadicGate F) omega} ≤ ∑' j, b j :=
  le_trans (measureReal_mono (firstStable_dyadicGate_gt_subset F h) (measure_ne_top _ _))
    (measureReal_iUnion_le' _ hb hbnn hsum)

omit [MeasurableSpace Omega] in
/-- **A dyadic exponential sum is geometric.**  If the exponent gains at least `c` per doubling
from `2^k₀` on and is at least `Eh` there, the dyadic sum is at most `(1 + 1/c) exp(−Eh)`. -/
theorem tsum_dyadic_exp_le {E : ℕ → ℝ} {c Eh : ℝ} (hc : 0 < c) (k0 : ℕ)
    (hbase : Eh ≤ E (2 ^ k0))
    (hstep : ∀ j : ℕ, E (2 ^ (k0 + j)) + c ≤ E (2 ^ (k0 + j + 1))) :
    (∑' j : ℕ, Real.exp (-(E (2 ^ (k0 + j))))) ≤ (1 + 1 / c) * Real.exp (-Eh) := by
  have hlin : ∀ j : ℕ, Eh + c * (j : ℝ) ≤ E (2 ^ (k0 + j)) := by
    intro j
    induction j with
    | zero => simpa using hbase
    | succ n ih =>
      have hs := hstep n
      have h1 : k0 + (n + 1) = k0 + n + 1 := by ring
      rw [h1]
      push_cast
      linarith
  have hterm : ∀ j : ℕ, Real.exp (-(E (2 ^ (k0 + j))))
      ≤ Real.exp (-Eh) * Real.exp (-(c * (j : ℝ))) := by
    intro j
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hlin j])
  have hsum : Summable fun j : ℕ => Real.exp (-Eh) * Real.exp (-(c * (j : ℝ))) :=
    (summable_exp_neg_mul hc).mul_left _
  have hsumL : Summable fun j : ℕ => Real.exp (-(E (2 ^ (k0 + j)))) :=
    Summable.of_nonneg_of_le (fun j => (Real.exp_pos _).le) hterm hsum
  calc (∑' j : ℕ, Real.exp (-(E (2 ^ (k0 + j)))))
      ≤ ∑' j : ℕ, Real.exp (-Eh) * Real.exp (-(c * (j : ℝ))) :=
        Summable.tsum_le_tsum hterm hsumL hsum
    _ = Real.exp (-Eh) * ∑' j : ℕ, Real.exp (-(c * (j : ℝ))) := by rw [tsum_mul_left]
    _ ≤ Real.exp (-Eh) * (1 + 1 / c) :=
        mul_le_mul_of_nonneg_left (tsum_exp_neg_mul_le hc) (Real.exp_pos _).le
    _ = (1 + 1 / c) * Real.exp (-Eh) := by ring

omit [MeasurableSpace Omega] in
/-- The same, for a two-family term `p exp(−E₁) + q exp(−E₂)`. -/
theorem tsum_dyadic_two_exp_le {E1 E2 : ℕ → ℝ} {c1 c2 Eh1 Eh2 p q : ℝ} (hc1 : 0 < c1)
    (hc2 : 0 < c2) (hp : 0 ≤ p) (hq : 0 ≤ q) (k0 : ℕ)
    (hbase1 : Eh1 ≤ E1 (2 ^ k0)) (hbase2 : Eh2 ≤ E2 (2 ^ k0))
    (hstep1 : ∀ j : ℕ, E1 (2 ^ (k0 + j)) + c1 ≤ E1 (2 ^ (k0 + j + 1)))
    (hstep2 : ∀ j : ℕ, E2 (2 ^ (k0 + j)) + c2 ≤ E2 (2 ^ (k0 + j + 1))) :
    (∑' j : ℕ, (p * Real.exp (-(E1 (2 ^ (k0 + j)))) + q * Real.exp (-(E2 (2 ^ (k0 + j))))))
      ≤ p * ((1 + 1 / c1) * Real.exp (-Eh1)) + q * ((1 + 1 / c2) * Real.exp (-Eh2)) := by
  have hlin1 : ∀ j : ℕ, Eh1 + c1 * (j : ℝ) ≤ E1 (2 ^ (k0 + j)) := by
    intro j
    induction j with
    | zero => simpa using hbase1
    | succ n ih =>
      have hs := hstep1 n
      have h1 : k0 + (n + 1) = k0 + n + 1 := by ring
      rw [h1]
      push_cast
      linarith
  have hlin2 : ∀ j : ℕ, Eh2 + c2 * (j : ℝ) ≤ E2 (2 ^ (k0 + j)) := by
    intro j
    induction j with
    | zero => simpa using hbase2
    | succ n ih =>
      have hs := hstep2 n
      have h1 : k0 + (n + 1) = k0 + n + 1 := by ring
      rw [h1]
      push_cast
      linarith
  have hterm1 : ∀ j : ℕ, Real.exp (-(E1 (2 ^ (k0 + j))))
      ≤ Real.exp (-Eh1) * Real.exp (-(c1 * (j : ℝ))) := by
    intro j
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hlin1 j])
  have hterm2 : ∀ j : ℕ, Real.exp (-(E2 (2 ^ (k0 + j))))
      ≤ Real.exp (-Eh2) * Real.exp (-(c2 * (j : ℝ))) := by
    intro j
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hlin2 j])
  have hs1 : Summable fun j : ℕ => Real.exp (-Eh1) * Real.exp (-(c1 * (j : ℝ))) :=
    (summable_exp_neg_mul hc1).mul_left _
  have hs2 : Summable fun j : ℕ => Real.exp (-Eh2) * Real.exp (-(c2 * (j : ℝ))) :=
    (summable_exp_neg_mul hc2).mul_left _
  have hsL1 : Summable fun j : ℕ => Real.exp (-(E1 (2 ^ (k0 + j)))) :=
    Summable.of_nonneg_of_le (fun j => (Real.exp_pos _).le) hterm1 hs1
  have hsL2 : Summable fun j : ℕ => Real.exp (-(E2 (2 ^ (k0 + j)))) :=
    Summable.of_nonneg_of_le (fun j => (Real.exp_pos _).le) hterm2 hs2
  have hA := tsum_dyadic_exp_le hc1 k0 hbase1 hstep1
  have hB := tsum_dyadic_exp_le hc2 k0 hbase2 hstep2
  rw [Summable.tsum_add (hsL1.mul_left p) (hsL2.mul_left q), tsum_mul_left, tsum_mul_left]
  exact add_le_add (mul_le_mul_of_nonneg_left hA hp) (mul_le_mul_of_nonneg_left hB hq)

omit [MeasurableSpace Omega] in
/-- Summability companion of `tsum_dyadic_exp_le`. -/
theorem summable_dyadic_exp {E : ℕ → ℝ} {c Eh : ℝ} (hc : 0 < c) (k0 : ℕ)
    (hbase : Eh ≤ E (2 ^ k0))
    (hstep : ∀ j : ℕ, E (2 ^ (k0 + j)) + c ≤ E (2 ^ (k0 + j + 1))) :
    Summable fun j : ℕ => Real.exp (-(E (2 ^ (k0 + j)))) := by
  have hlin : ∀ j : ℕ, Eh + c * (j : ℝ) ≤ E (2 ^ (k0 + j)) := by
    intro j
    induction j with
    | zero => simpa using hbase
    | succ n ih =>
      have hs := hstep n
      have h1 : k0 + (n + 1) = k0 + n + 1 := by ring
      rw [h1]
      push_cast
      linarith
  have hterm : ∀ j : ℕ, Real.exp (-(E (2 ^ (k0 + j))))
      ≤ Real.exp (-Eh) * Real.exp (-(c * (j : ℝ))) := by
    intro j
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hlin j])
  exact Summable.of_nonneg_of_le (fun j => (Real.exp_pos _).le) hterm
    ((summable_exp_neg_mul hc).mul_left _)

/-! ### Dyadic blocking of the discounted supremum

For a family nondecreasing in the index, the indices `i ≤ m + N` are dominated by `m + N`, and
the indices in `(m + 2^k N, m + 2^{k+1} N]` by the top of their block, at discount at least
`a 2^k N`.  This is the source's device for `X^time_m = sup_j e^{−aδj} X^{time,0}_{m+j}`: the
block's Gaussian variance `≍ 2^k N` is beaten by the square of its discount. -/

omit [MeasurableSpace Omega] in
theorem discount_union_subset_dyadic (L : ℕ → Omega → ℕ)
    (hmono : ∀ (i i' : ℕ) (omega : Omega), i ≤ i' → L i omega ≤ L i' omega)
    (a m h N : ℕ) (hN : 1 ≤ N) :
    (⋃ i : ℕ, {omega | h + a * (i - m) < L i omega})
      ⊆ {omega | h < L (m + N) omega}
        ∪ ⋃ k : ℕ, {omega | h + a * (2 ^ k * N) < L (m + 2 ^ (k + 1) * N) omega} := by
  intro omega homega
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp homega
  simp only [mem_ofPred_eq] at hi
  by_cases hle : i ≤ m + N
  · left
    simp only [mem_ofPred_eq]
    have := hmono i (m + N) omega hle
    omega
  · right
    push Not at hle
    have hNpos : 0 < N := hN
    have htN : N < i - m := by omega
    set t : ℕ := i - m with ht
    set k : ℕ := Nat.log 2 (t / N) with hk
    have hq1 : 1 ≤ t / N := (Nat.one_le_div_iff hNpos).mpr htN.le
    have hlow : 2 ^ k ≤ t / N := Nat.pow_log_le_self 2 (by omega)
    have hup : t / N < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (t / N)
    have h1 : 2 ^ k * N ≤ t :=
      le_trans (Nat.mul_le_mul_right N hlow) (Nat.div_mul_le_self t N)
    have h2 : t < 2 ^ (k + 1) * N := by
      have h3 : t < t / N * N + N := Nat.lt_div_mul_add hNpos
      have h4 : t / N * N + N ≤ 2 ^ (k + 1) * N := by
        calc t / N * N + N = (t / N + 1) * N := by ring
          _ ≤ 2 ^ (k + 1) * N := Nat.mul_le_mul_right N hup
      omega
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    simp only [mem_ofPred_eq]
    have hi' : i ≤ m + 2 ^ (k + 1) * N := by omega
    have hL := hmono i (m + 2 ^ (k + 1) * N) omega hi'
    have hdisc : a * (2 ^ k * N) ≤ a * (i - m) := Nat.mul_le_mul_left a (by omega)
    exact lt_of_le_of_lt (Nat.add_le_add_left hdisc h) (lt_of_lt_of_le hi hL)

omit [MeasurableSpace Omega] in
theorem levelDiscounted_gt_subset_dyadic (L : ℕ → Omega → ℕ)
    (hmono : ∀ (i i' : ℕ) (omega : Omega), i ≤ i' → L i omega ≤ L i' omega)
    (a m h N : ℕ) (hN : 1 ≤ N) :
    {omega | h < levelDiscounted L a m omega}
      ⊆ {omega | h < L (m + N) omega}
        ∪ ⋃ k : ℕ, {omega | h + a * (2 ^ k * N) < L (m + 2 ^ (k + 1) * N) omega} :=
  le_trans (levelDiscounted_gt_subset L a m h) (discount_union_subset_dyadic L hmono a m h N hN)

omit [MeasurableSpace Omega] in
theorem not_bddAbove_subset_dyadic (L : ℕ → Omega → ℕ)
    (hmono : ∀ (i i' : ℕ) (omega : Omega), i ≤ i' → L i omega ≤ L i' omega)
    (a m h N : ℕ) (hN : 1 ≤ N) :
    {omega | ¬ BddAbove (discountSet L a m omega)}
      ⊆ {omega | h < L (m + N) omega}
        ∪ ⋃ k : ℕ, {omega | h + a * (2 ^ k * N) < L (m + 2 ^ (k + 1) * N) omega} :=
  le_trans (not_bddAbove_discountSet_subset L a m h)
    (discount_union_subset_dyadic L hmono a m h N hN)

/-- **The dyadic tail of the discounted supremum.** -/
theorem measureReal_levelDiscounted_gt_dyadic_le [IsFiniteMeasure mu] (L : ℕ → Omega → ℕ)
    (hmono : ∀ (i i' : ℕ) (omega : Omega), i ≤ i' → L i omega ≤ L i' omega)
    (a m h N : ℕ) (hN : 1 ≤ N) {b : ℕ → ℝ}
    (hb : ∀ k, mu.real {omega | h + a * (2 ^ k * N) < L (m + 2 ^ (k + 1) * N) omega} ≤ b k)
    (hbnn : ∀ k, 0 ≤ b k) (hsum : Summable b) :
    mu.real {omega | h < levelDiscounted L a m omega}
      ≤ mu.real {omega | h < L (m + N) omega} + ∑' k, b k :=
  le_trans (measureReal_mono (levelDiscounted_gt_subset_dyadic L hmono a m h N hN)
      (measure_ne_top _ _))
    (le_trans (measureReal_union_le _ _)
      (add_le_add le_rfl (measureReal_iUnion_le' _ hb hbnn hsum)))

/-- The same bound for the unbounded set, at any `h`. -/
theorem measureReal_not_bddAbove_dyadic_le [IsFiniteMeasure mu] (L : ℕ → Omega → ℕ)
    (hmono : ∀ (i i' : ℕ) (omega : Omega), i ≤ i' → L i omega ≤ L i' omega)
    (a m h N : ℕ) (hN : 1 ≤ N) {b : ℕ → ℝ}
    (hb : ∀ k, mu.real {omega | h + a * (2 ^ k * N) < L (m + 2 ^ (k + 1) * N) omega} ≤ b k)
    (hbnn : ∀ k, 0 ≤ b k) (hsum : Summable b) :
    mu.real {omega | ¬ BddAbove (discountSet L a m omega)}
      ≤ mu.real {omega | h < L (m + N) omega} + ∑' k, b k :=
  le_trans (measureReal_mono (not_bddAbove_subset_dyadic L hmono a m h N hN)
      (measure_ne_top _ _))
    (le_trans (measureReal_union_le _ _)
      (add_le_add le_rfl (measureReal_iUnion_le' _ hb hbnn hsum)))

/-- The constant split with its two pieces explicit: `min X (A²/B)` and `(X − A²/B)⁺`. -/
theorem ogammaLE_split_of_two_term_const_explicit [IsProbabilityMeasure mu] {A B c0 : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hc0 : 1 ≤ c0) {X : Omega → ℝ} (hXm : AEMeasurable X mu)
    (htail : ∀ lam : ℝ, 0 < lam →
      mu.real {omega | lam ≤ X omega}
        ≤ c0 * Real.exp (-((lam / A) ^ (2:ℕ))) + c0 * Real.exp (-(lam / B))) :
    (∀ omega, X omega = min (X omega) (A ^ (2:ℕ) / B) + max (X omega - A ^ (2:ℕ) / B) 0) ∧
      (∀ omega, 0 ≤ max (X omega - A ^ (2:ℕ) / B) 0) ∧
      SubdiffusiveProcess.OGammaLE mu 2 (2 * Real.sqrt (2 * c0) * A) (fun omega => min (X omega) (A ^ (2:ℕ) / B)) ∧
      SubdiffusiveProcess.OGammaLE mu 1 (8 * c0 * B) (fun omega => max (X omega - A ^ (2:ℕ) / B) 0) := by
  have hc2 : (2:ℝ) ≤ 2 * c0 := by linarith
  have hc0pos : (0:ℝ) < c0 := by linarith
  set u0 : ℝ := A ^ (2:ℕ) / B with hu0
  have hu0pos : 0 < u0 := by rw [hu0]; positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro omega
    show X omega = min (X omega) u0 + max (X omega - u0) 0
    rcases le_or_gt (X omega) u0 with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h.le, max_eq_left (by linarith)]; ring
  · intro omega; exact le_max_right _ _
  · have hm : AEMeasurable (fun omega => min (X omega) u0) mu := hXm.min aemeasurable_const
    have hkey : ∀ lam : ℝ, 0 < lam →
        mu.real {omega | lam ≤ min (X omega) u0}
          ≤ 2 * Real.exp (-((lam / (Real.sqrt (2 * c0) * A)) ^ (2:ℕ))) := by
      intro lam hlam
      have hone : mu.real {omega | lam ≤ min (X omega) u0} ≤ 1 := by
        have _h := ENNReal.toReal_mono (by norm_num : (1:ENNReal) ≠ ⊤)
          (prob_le_one : mu {omega | lam ≤ min (X omega) u0} ≤ 1)
        simp
      refine const_to_two_gauss hA hlam hc2 hone ?_
      rcases le_or_gt lam u0 with hc | hc
      · have hsub : {omega | lam ≤ min (X omega) u0} ⊆ {omega | lam ≤ X omega} := by
          intro omega homega
          simp only [mem_ofPred_eq] at homega ⊢
          exact le_trans homega (min_le_left _ _)
        have hcmp : Real.exp (-(lam / B)) ≤ Real.exp (-((lam / A) ^ (2:ℕ))) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : (lam / A) ^ (2:ℕ) ≤ lam / B := by
            have hlb : lam * B ≤ A ^ (2:ℕ) := by
              rw [hu0, le_div_iff₀ hB] at hc; exact hc
            rw [div_pow, div_le_div_iff₀ (by positivity) hB]
            nlinarith [hlb, hlam.le]
          linarith
        have hmain := le_trans (measureReal_mono hsub) (htail lam hlam)
        nlinarith [hmain, hcmp, hc0pos]
      · have hempty : {omega | lam ≤ min (X omega) u0} = ∅ := by
          ext omega
          simp only [mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
          exact lt_of_le_of_lt (min_le_right _ _) hc
        rw [hempty]
        simp only [measureReal_empty]
        positivity
    have hres := ogammaLE_of_measureReal_tail
      (by positivity : (0:ℝ) < Real.sqrt (2 * c0) * A) hm hkey
    have heq : 2 * (Real.sqrt (2 * c0) * A) = 2 * Real.sqrt (2 * c0) * A := by ring
    rwa [heq] at hres
  · have hm : AEMeasurable (fun omega => max (X omega - u0) 0) mu :=
      (hXm.sub aemeasurable_const).max aemeasurable_const
    have hkey : ∀ lam : ℝ, 0 < lam →
        mu.real {omega | lam ≤ max (X omega - u0) 0}
          ≤ 2 * Real.exp (-(lam / (2 * c0 * B))) := by
      intro lam hlam
      have hone : mu.real {omega | lam ≤ max (X omega - u0) 0} ≤ 1 := by
        have _h := ENNReal.toReal_mono (by norm_num : (1:ENNReal) ≠ ⊤)
          (prob_le_one : mu {omega | lam ≤ max (X omega - u0) 0} ≤ 1)
        simp
      refine const_to_two_exp hB hlam hc2 hone ?_
      have hsub : {omega | lam ≤ max (X omega - u0) 0} ⊆ {omega | lam + u0 ≤ X omega} := by
        intro omega homega
        simp only [mem_ofPred_eq, le_max_iff] at homega
        rcases homega with h | h
        · simp only [mem_ofPred_eq]; linarith
        · exact absurd h (not_le.mpr hlam)
      have hlu : 0 < lam + u0 := by linarith
      have hcmp : Real.exp (-(((lam + u0) / A) ^ (2:ℕ))) ≤ Real.exp (-((lam + u0) / B)) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : (lam + u0) / B ≤ ((lam + u0) / A) ^ (2:ℕ) := by
          have hub : A ^ (2:ℕ) ≤ (lam + u0) * B := by
            have hu0B : u0 * B = A ^ (2:ℕ) := by rw [hu0]; field_simp
            nlinarith [hlam.le, hB]
          rw [div_pow, div_le_div_iff₀ hB (by positivity)]
          nlinarith [hub, hlu.le]
        linarith
      have hmono : Real.exp (-((lam + u0) / B)) ≤ Real.exp (-(lam / B)) := by
        refine Real.exp_le_exp.mpr ?_
        have hle2 : lam / B ≤ (lam + u0) / B := by
          rw [div_le_div_iff₀ hB hB]; nlinarith [hu0pos, hB]
        linarith
      have hmain := le_trans (measureReal_mono hsub) (htail _ hlu)
      nlinarith [hmain, hcmp, hmono, hc0pos]
    have hres := ogammaLE_one_of_tail (by positivity : (0:ℝ) < 2 * c0 * B) hm hkey
    have heq : 4 * (2 * c0 * B) = 8 * c0 * B := by ring
    rwa [heq] at hres

/-! ### A two-term ℕ-valued tail splits -/

/-- **From an integer two-term tail to the `O_Γ` split.**  A linear-plus-Gaussian tail of an
ℕ-valued level above `h₀`, with prefactors `p, q ≥ 1`, splits the excess over `h₀` into an
`O_{Γ₂}` part at scale `2√(2 max p q)·√S` and an `O_{Γ₁}` part at scale `8 max p q / ρ`. -/
theorem ogammaLE_split_of_nat_two_term [IsProbabilityMeasure mu] {X : Omega → ℕ} {h0 : ℕ}
    {p q rho S : ℝ} (hp : 1 ≤ p) (hrho : 0 < rho) (hS : 0 < S)
    (hmeas : Measurable X)
    (htail : ∀ h : ℕ, h0 ≤ h →
      mu.real {omega | h < X omega}
        ≤ p * Real.exp (-(rho * ((h : ℝ) + 1 - (h0 : ℝ))))
          + q * Real.exp (-(((h : ℝ) + 1 - (h0 : ℝ)) ^ (2:ℕ) / S))) :
    ∃ X2 X1 : Omega → ℝ,
      (∀ omega, ((X omega - h0 : ℕ) : ℝ) = X2 omega + X1 omega) ∧
      (∀ omega, 0 ≤ X1 omega) ∧
      Measurable X2 ∧ Measurable X1 ∧
      SubdiffusiveProcess.OGammaLE mu 2 (2 * Real.sqrt (2 * max p q) * Real.sqrt S) X2 ∧
      SubdiffusiveProcess.OGammaLE mu 1 (8 * max p q * rho⁻¹) X1 := by
  have hc0 : 1 ≤ max p q := le_trans hp (le_max_left _ _)
  have hA : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hB : 0 < rho⁻¹ := by positivity
  have hXr : Measurable fun omega => ((X omega - h0 : ℕ) : ℝ) :=
    (measurable_of_countable fun n : ℕ => ((n - h0 : ℕ) : ℝ)).comp hmeas
  have hsplit := ogammaLE_split_of_two_term_const_explicit (mu := mu) hA hB hc0
    (X := fun omega => ((X omega - h0 : ℕ) : ℝ)) (hXr.aemeasurable (μ := mu)) ?_
  · refine ⟨_, _, hsplit.1, hsplit.2.1, hXr.min measurable_const,
      (hXr.sub_const _).max measurable_const, hsplit.2.2.1, hsplit.2.2.2⟩
  intro lam hlam
  set c : ℕ := ⌈lam⌉.toNat with hc
  have hceil1 : (1:ℤ) ≤ ⌈lam⌉ := Int.one_le_ceil_iff.mpr hlam
  have hcpos : 1 ≤ c := by rw [hc]; omega
  have hcz : ((c : ℕ) : ℤ) = ⌈lam⌉ := by rw [hc]; exact Int.toNat_of_nonneg (by omega)
  have hcge : lam ≤ (c : ℝ) := by
    have h3 := Int.le_ceil lam
    have h4 : ((c : ℕ) : ℝ) = ((⌈lam⌉ : ℤ) : ℝ) := by exact_mod_cast hcz
    rw [h4]
    exact h3
  set h : ℕ := h0 + c - 1 with hh
  have hh0 : h0 ≤ h := by omega
  have hsub : {omega : Omega | lam ≤ ((X omega - h0 : ℕ) : ℝ)}
      ⊆ {omega : Omega | h < X omega} := by
    intro omega homega
    simp only [mem_ofPred_eq] at homega ⊢
    have hge : (⌈lam⌉ : ℤ) ≤ ((X omega - h0 : ℕ) : ℤ) := by
      rw [Int.ceil_le]
      exact_mod_cast homega
    have hnat : c ≤ X omega - h0 := by rw [hc]; omega
    omega
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans (htail h hh0) ?_
  have hstep : ((h : ℝ) + 1 - (h0 : ℝ)) = (c : ℝ) := by
    have : h + 1 = h0 + c := by omega
    have hcast : ((h + 1 : ℕ) : ℝ) = ((h0 + c : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hcast ⊢
    linarith
  rw [hstep]
  have hmono1 : Real.exp (-(rho * (c : ℝ))) ≤ Real.exp (-(lam / rho⁻¹)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [div_inv_eq_mul]
    nlinarith [hcge, hrho]
  have hmono2 : Real.exp (-((c : ℝ) ^ (2:ℕ) / S)) ≤ Real.exp (-((lam / Real.sqrt S) ^ (2:ℕ))) := by
    refine Real.exp_le_exp.mpr ?_
    rw [div_pow, Real.sq_sqrt hS.le]
    have h1 : lam ^ (2:ℕ) ≤ (c : ℝ) ^ (2:ℕ) := pow_le_pow_left₀ hlam.le hcge 2
    have h2 := div_le_div_of_nonneg_right h1 hS.le
    linarith
  have e1 : p * Real.exp (-(rho * (c : ℝ))) ≤ max p q * Real.exp (-(lam / rho⁻¹)) :=
    mul_le_mul (le_max_left _ _) hmono1 (Real.exp_pos _).le (by linarith)
  have e2 : q * Real.exp (-((c : ℝ) ^ (2:ℕ) / S))
      ≤ max p q * Real.exp (-((lam / Real.sqrt S) ^ (2:ℕ))) :=
    mul_le_mul (le_max_right _ _) hmono2 (Real.exp_pos _).le (by linarith)
  linarith

end SubdiffusiveProcess.CoarseGrainingVocab.OGamma
