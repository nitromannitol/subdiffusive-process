import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.FluxRowFractionalCutoffKernel




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The pointwise cutoff bound: the Gagliardo kernel of `chi * v` is bounded
by twice the kernel of `v` restricted to `U × U` plus the commutator majorant
weighted by the mass of `v` on `U` at either endpoint. -/
theorem fluxRowFractionalKernelOf_cutoff_le {sigma Lam : ℝ} (hsigma : 0 ≤ sigma)
    {U : Set (Vec d)} {chi : Vec d → ℝ}
    (hchi0 : ∀ x, 0 ≤ chi x) (hchi1 : ∀ x, chi x ≤ 1)
    (hchisupp : ∀ x, x ∉ U → chi x = 0)
    (hchiLip : ∀ x y, |chi x - chi y| ≤ Lam * ‖x - y‖)
    (v : Vec d → ℂ) (z : Vec d × Vec d) :
    fluxRowFractionalKernelOf sigma (fun x ↦ (chi x : ℂ) * v x) z ≤
      2 * (U ×ˢ U).indicator (fluxRowFractionalKernelOf sigma v) z +
        2 * ENNReal.ofReal sigma *
          ((U.indicator (fun x ↦ ENNReal.ofReal (‖v x‖ ^ 2)) z.1 +
            U.indicator (fun x ↦ ENNReal.ofReal (‖v x‖ ^ 2)) z.2) *
              fluxRowFractionalCutoffIntegrand d sigma Lam (z.1 - z.2)) := by
  obtain ⟨x, y⟩ := z
  set D : ℝ := Real.rpow ‖x - y‖ ((d : ℝ) + 2 * sigma) with hDdef
  have hD : 0 ≤ D := Real.rpow_nonneg (norm_nonneg _) _
  set m : ℝ := min 1 (Lam ^ 2 * ‖x - y‖ ^ 2) with hmdef
  have hm0 : 0 ≤ m := le_min zero_le_one (by positivity)
  have hchisq : (chi x - chi y) ^ 2 ≤ m := by
    apply le_min
    · nlinarith [hchi0 x, hchi1 x, hchi0 y, hchi1 y]
    · have h := hchiLip x y
      have h0 : 0 ≤ |chi x - chi y| := abs_nonneg _
      nlinarith [sq_abs (chi x - chi y)]
  -- the cutoff majorant in `ofReal` form
  have hcut : fluxRowFractionalCutoffIntegrand d sigma Lam (x - y) =
      ENNReal.ofReal (m / D) := rfl
  have hker : ∀ w : Vec d → ℂ,
      fluxRowFractionalKernelOf sigma w (x, y) =
        ENNReal.ofReal (sigma * ‖w x - w y‖ ^ 2 / D) := fun _ ↦ rfl
  -- the two commutator contributions, in `ofReal` form
  have hcomm : ∀ p : ℝ, 0 ≤ p →
      2 * ENNReal.ofReal sigma *
          (ENNReal.ofReal p * fluxRowFractionalCutoffIntegrand d sigma Lam (x - y)) =
        ENNReal.ofReal (2 * sigma * p * (m / D)) := by
    intro p hp
    rw [hcut, ← ENNReal.ofReal_mul hp,
      show ((2 : ℝ≥0∞)) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * sigma)]
    congr 1
    ring
  have hdouble : (2 : ℝ≥0∞) * fluxRowFractionalKernelOf sigma v (x, y) =
      ENNReal.ofReal (2 * sigma * ‖v x - v y‖ ^ 2 / D) := by
    rw [hker v, show ((2 : ℝ≥0∞)) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  -- the elementary product bound
  have hsplit : ∀ a b : Vec d,
      ‖(chi a : ℂ) * v a - (chi b : ℂ) * v b‖ ^ 2 ≤
        2 * (chi a) ^ 2 * ‖v a - v b‖ ^ 2 +
          2 * (chi a - chi b) ^ 2 * ‖v b‖ ^ 2 := by
    intro a b
    have hid : (chi a : ℂ) * v a - (chi b : ℂ) * v b =
        (chi a : ℂ) * (v a - v b) + ((chi a - chi b : ℝ) : ℂ) * v b := by
      push_cast
      ring
    have h1 : ‖(chi a : ℂ) * v a - (chi b : ℂ) * v b‖ ≤
        |chi a| * ‖v a - v b‖ + |chi a - chi b| * ‖v b‖ := by
      rw [hid]
      refine (norm_add_le _ _).trans_eq ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
    have h2 : ‖(chi a : ℂ) * v a - (chi b : ℂ) * v b‖ ^ 2 ≤
        (|chi a| * ‖v a - v b‖ + |chi a - chi b| * ‖v b‖) ^ 2 := by
      have hmm := mul_self_le_mul_self (norm_nonneg
        ((chi a : ℂ) * v a - (chi b : ℂ) * v b)) h1
      simpa [pow_two] using hmm
    nlinarith [sq_nonneg (|chi a| * ‖v a - v b‖ - |chi a - chi b| * ‖v b‖),
      sq_abs (chi a), sq_abs (chi a - chi b), sq_nonneg ‖v a - v b‖,
      sq_nonneg ‖v b‖]
  by_cases hx : x ∈ U <;> by_cases hy : y ∈ U
  · -- both endpoints inside the cell
    rw [Set.indicator_of_mem (Set.mk_mem_prod hx hy),
      Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    have hnum : sigma * ‖(chi x : ℂ) * v x - (chi y : ℂ) * v y‖ ^ 2 ≤
        2 * sigma * ‖v x - v y‖ ^ 2 + 2 * sigma * ‖v y‖ ^ 2 * m := by
      have h := hsplit x y
      have hx1 : chi x ^ 2 ≤ 1 := by nlinarith [hchi0 x, hchi1 x]
      have t1 : 2 * chi x ^ 2 * ‖v x - v y‖ ^ 2 ≤ 2 * ‖v x - v y‖ ^ 2 := by
        nlinarith [sq_nonneg ‖v x - v y‖]
      have t2 : 2 * (chi x - chi y) ^ 2 * ‖v y‖ ^ 2 ≤ 2 * ‖v y‖ ^ 2 * m := by
        nlinarith [sq_nonneg ‖v y‖]
      have hstep : ‖(chi x : ℂ) * v x - (chi y : ℂ) * v y‖ ^ 2 ≤
          2 * ‖v x - v y‖ ^ 2 + 2 * ‖v y‖ ^ 2 * m := by linarith
      calc sigma * ‖(chi x : ℂ) * v x - (chi y : ℂ) * v y‖ ^ 2
          ≤ sigma * (2 * ‖v x - v y‖ ^ 2 + 2 * ‖v y‖ ^ 2 * m) :=
            mul_le_mul_of_nonneg_left hstep hsigma
        _ = 2 * sigma * ‖v x - v y‖ ^ 2 + 2 * sigma * ‖v y‖ ^ 2 * m := by ring
    calc fluxRowFractionalKernelOf sigma (fun x ↦ (chi x : ℂ) * v x) (x, y)
        = ENNReal.ofReal (sigma * ‖(chi x : ℂ) * v x - (chi y : ℂ) * v y‖ ^ 2 / D) :=
          hker _
      _ ≤ ENNReal.ofReal (2 * sigma * ‖v x - v y‖ ^ 2 / D +
            2 * sigma * ‖v y‖ ^ 2 * (m / D)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [mul_div_assoc', ← add_div]
          exact div_le_div_of_nonneg_right hnum hD
      _ = ENNReal.ofReal (2 * sigma * ‖v x - v y‖ ^ 2 / D) +
            ENNReal.ofReal (2 * sigma * ‖v y‖ ^ 2 * (m / D)) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      _ ≤ 2 * fluxRowFractionalKernelOf sigma v (x, y) +
            2 * ENNReal.ofReal sigma *
              ((ENNReal.ofReal (‖v x‖ ^ 2) + ENNReal.ofReal (‖v y‖ ^ 2)) *
                fluxRowFractionalCutoffIntegrand d sigma Lam (x - y)) := by
          rw [hdouble, add_mul, mul_add,
            hcomm (‖v x‖ ^ 2) (by positivity), hcomm (‖v y‖ ^ 2) (by positivity)]
          have hstep2 : ENNReal.ofReal (2 * sigma * ‖v y‖ ^ 2 * (m / D)) ≤
              ENNReal.ofReal (2 * sigma * ‖v x‖ ^ 2 * (m / D)) +
                ENNReal.ofReal (2 * sigma * ‖v y‖ ^ 2 * (m / D)) := by
            rw [add_comm]
            exact le_self_add
          exact add_le_add le_rfl hstep2
  · -- inside on the left, outside on the right
    rw [Set.indicator_of_notMem (by simp [hy]), Set.indicator_of_mem hx,
      Set.indicator_of_notMem hy]
    have hzero : chi y = 0 := hchisupp y hy
    have hcx : chi x ^ 2 ≤ m := by rw [hzero] at hchisq; simpa using hchisq
    have hnum : sigma * ‖(chi x : ℂ) * v x - (chi y : ℂ) * v y‖ ^ 2 ≤
        2 * sigma * ‖v x‖ ^ 2 * m := by
      have hval : ‖(chi x : ℂ) * v x - (chi y : ℂ) * v y‖ ^ 2 =
          (chi x) ^ 2 * ‖v x‖ ^ 2 := by
        rw [hzero]
        simp [Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [hval]
      have hstep : chi x ^ 2 * ‖v x‖ ^ 2 ≤ m * ‖v x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcx (sq_nonneg _)
      have hpos : 0 ≤ sigma * (m * ‖v x‖ ^ 2) :=
        mul_nonneg hsigma (mul_nonneg hm0 (sq_nonneg _))
      nlinarith [mul_le_mul_of_nonneg_left hstep hsigma]
    calc fluxRowFractionalKernelOf sigma (fun x ↦ (chi x : ℂ) * v x) (x, y)
        = ENNReal.ofReal (sigma * ‖(chi x : ℂ) * v x - (chi y : ℂ) * v y‖ ^ 2 / D) :=
          hker _
      _ ≤ ENNReal.ofReal (2 * sigma * ‖v x‖ ^ 2 * (m / D)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [mul_div_assoc']
          exact div_le_div_of_nonneg_right hnum hD
      _ ≤ 2 * (0 : ℝ≥0∞) + 2 * ENNReal.ofReal sigma *
            ((ENNReal.ofReal (‖v x‖ ^ 2) + 0) *
              fluxRowFractionalCutoffIntegrand d sigma Lam (x - y)) := by
          simp only [add_zero, mul_zero, zero_add]
          rw [hcomm (‖v x‖ ^ 2) (by positivity)]
  · -- outside on the left, inside on the right
    rw [Set.indicator_of_notMem (by simp [hx]), Set.indicator_of_notMem hx,
      Set.indicator_of_mem hy]
    have hzero : chi x = 0 := hchisupp x hx
    have hcy : chi y ^ 2 ≤ m := by rw [hzero] at hchisq; simpa using hchisq
    have hnum : sigma * ‖(chi x : ℂ) * v x - (chi y : ℂ) * v y‖ ^ 2 ≤
        2 * sigma * ‖v y‖ ^ 2 * m := by
      have hval : ‖(chi x : ℂ) * v x - (chi y : ℂ) * v y‖ ^ 2 =
          (chi y) ^ 2 * ‖v y‖ ^ 2 := by
        rw [hzero]
        simp [Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [hval]
      have hstep : chi y ^ 2 * ‖v y‖ ^ 2 ≤ m * ‖v y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcy (sq_nonneg _)
      have hpos : 0 ≤ sigma * (m * ‖v y‖ ^ 2) :=
        mul_nonneg hsigma (mul_nonneg hm0 (sq_nonneg _))
      nlinarith [mul_le_mul_of_nonneg_left hstep hsigma]
    calc fluxRowFractionalKernelOf sigma (fun x ↦ (chi x : ℂ) * v x) (x, y)
        = ENNReal.ofReal (sigma * ‖(chi x : ℂ) * v x - (chi y : ℂ) * v y‖ ^ 2 / D) :=
          hker _
      _ ≤ ENNReal.ofReal (2 * sigma * ‖v y‖ ^ 2 * (m / D)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [mul_div_assoc']
          exact div_le_div_of_nonneg_right hnum hD
      _ ≤ 2 * (0 : ℝ≥0∞) + 2 * ENNReal.ofReal sigma *
            ((0 + ENNReal.ofReal (‖v y‖ ^ 2)) *
              fluxRowFractionalCutoffIntegrand d sigma Lam (x - y)) := by
          simp only [zero_add, mul_zero]
          rw [hcomm (‖v y‖ ^ 2) (by positivity)]
  · -- both endpoints outside the cell
    have hzx : chi x = 0 := hchisupp x hx
    have hzy : chi y = 0 := hchisupp y hy
    have : fluxRowFractionalKernelOf sigma (fun x ↦ (chi x : ℂ) * v x) (x, y) = 0 := by
      rw [hker _]
      simp [hzx, hzy]
    rw [this]
    exact zero_le _

/-- **The fractional multiplier estimate.**  The whole-space Gagliardo energy
of `chi * v`, for a `[0,1]`-valued `Lam`-Lipschitz cutoff supported in `U`, is
bounded by twice the Gagliardo energy of `v` inside `U` plus
`Lam ^ (2 sigma)` times the mass of `v` on `U`.  The constant depends only on
`d` and `sigma`. -/
theorem fluxRowFractional_cutoff_gagliardo_le {sigma Lam : ℝ} (hsigma : 0 ≤ sigma)
    (hLam : 0 < Lam) {U : Set (Vec d)} (hU : MeasurableSet U) {chi : Vec d → ℝ}
    (hchi0 : ∀ x, 0 ≤ chi x) (hchi1 : ∀ x, chi x ≤ 1)
    (hchisupp : ∀ x, x ∉ U → chi x = 0)
    (hchiLip : ∀ x y, |chi x - chi y| ≤ Lam * ‖x - y‖)
    {v : Vec d → ℂ} (hv : Measurable v) :
    ∫⁻ z, fluxRowFractionalKernelOf sigma (fun x ↦ (chi x : ℂ) * v x) z
        ∂((volume : Measure (Vec d)).prod volume) ≤
      2 * ∫⁻ z in U ×ˢ U, fluxRowFractionalKernelOf sigma v z
          ∂((volume : Measure (Vec d)).prod volume) +
        4 * ENNReal.ofReal sigma * ENNReal.ofReal (Real.rpow Lam (2 * sigma)) *
          fluxRowFractionalCutoffConst d sigma *
          ∫⁻ x in U, ENNReal.ofReal (‖v x‖ ^ 2) ∂volume := by
  classical
  set S : Vec d → ℝ≥0∞ := U.indicator (fun x ↦ ENNReal.ofReal (‖v x‖ ^ 2))
    with hSdef
  set C : Vec d → ℝ≥0∞ := fluxRowFractionalCutoffIntegrand d sigma Lam
    with hCdef
  set M : ℝ≥0∞ := ENNReal.ofReal (Real.rpow Lam (2 * sigma)) *
    fluxRowFractionalCutoffConst d sigma with hMdef
  have hKv : Measurable (fluxRowFractionalKernelOf sigma v) :=
    measurable_fluxRowFractionalKernelOf hv
  have hS : Measurable S := ((hv.norm.pow_const 2).ennreal_ofReal).indicator hU
  have hC : Measurable C := measurable_fluxRowFractionalCutoffIntegrand d sigma Lam
  have hK1 : Measurable fun z : Vec d × Vec d ↦
      2 * (U ×ˢ U).indicator (fluxRowFractionalKernelOf sigma v) z :=
    (hKv.indicator (hU.prod hU)).const_mul 2
  have hK2a : Measurable fun z : Vec d × Vec d ↦ S z.1 * C (z.1 - z.2) :=
    (hS.comp measurable_fst).mul (hC.comp (measurable_fst.sub measurable_snd))
  have hK2b : Measurable fun z : Vec d × Vec d ↦ S z.2 * C (z.1 - z.2) :=
    (hS.comp measurable_snd).mul (hC.comp (measurable_fst.sub measurable_snd))
  have hmass : ∫⁻ h : Vec d, C h ∂volume = M :=
    lintegral_fluxRowFractionalCutoffIntegrand d sigma hLam
  have hSint : ∫⁻ x : Vec d, S x ∂volume =
      ∫⁻ x in U, ENNReal.ofReal (‖v x‖ ^ 2) ∂volume :=
    lintegral_indicator hU _
  -- the two commutator integrals
  have hI1 : ∫⁻ z : Vec d × Vec d, S z.1 * C (z.1 - z.2)
        ∂((volume : Measure (Vec d)).prod volume) =
      M * ∫⁻ x : Vec d, S x ∂volume := by
    rw [lintegral_prod _ hK2a.aemeasurable]
    have hinner : ∀ x : Vec d,
        ∫⁻ y : Vec d, S x * C (x - y) ∂volume = S x * M := by
      intro x
      have hCy : Measurable fun y : Vec d ↦ C (x - y) :=
        hC.comp (measurable_const.sub measurable_id)
      rw [lintegral_const_mul _ hCy,
        (Measure.measurePreserving_sub_left (volume : Measure (Vec d)) x).lintegral_comp hC,
        hmass]
    rw [lintegral_congr hinner, lintegral_mul_const _ hS, mul_comm]
  have hI2 : ∫⁻ z : Vec d × Vec d, S z.2 * C (z.1 - z.2)
        ∂((volume : Measure (Vec d)).prod volume) =
      M * ∫⁻ x : Vec d, S x ∂volume := by
    rw [lintegral_prod_symm _ hK2b.aemeasurable]
    have hinner : ∀ y : Vec d,
        ∫⁻ x : Vec d, S y * C (x - y) ∂volume = S y * M := by
      intro y
      have hCx : Measurable fun x : Vec d ↦ C (x - y) :=
        hC.comp (measurable_id.sub measurable_const)
      rw [lintegral_const_mul _ hCx,
        (measurePreserving_sub_right (volume : Measure (Vec d)) y).lintegral_comp hC,
        hmass]
    rw [lintegral_congr hinner, lintegral_mul_const _ hS, mul_comm]
  -- integrate the pointwise bound
  calc ∫⁻ z, fluxRowFractionalKernelOf sigma (fun x ↦ (chi x : ℂ) * v x) z
        ∂((volume : Measure (Vec d)).prod volume)
      ≤ ∫⁻ z : Vec d × Vec d,
          (2 * (U ×ˢ U).indicator (fluxRowFractionalKernelOf sigma v) z +
            2 * ENNReal.ofReal sigma * ((S z.1 + S z.2) * C (z.1 - z.2)))
          ∂((volume : Measure (Vec d)).prod volume) :=
        lintegral_mono fun z ↦ fluxRowFractionalKernelOf_cutoff_le hsigma
          hchi0 hchi1 hchisupp hchiLip v z
    _ = (∫⁻ z : Vec d × Vec d,
          2 * (U ×ˢ U).indicator (fluxRowFractionalKernelOf sigma v) z
            ∂((volume : Measure (Vec d)).prod volume)) +
        ∫⁻ z : Vec d × Vec d,
          2 * ENNReal.ofReal sigma * ((S z.1 + S z.2) * C (z.1 - z.2))
            ∂((volume : Measure (Vec d)).prod volume) :=
        lintegral_add_left hK1 _
    _ = 2 * ∫⁻ z in U ×ˢ U, fluxRowFractionalKernelOf sigma v z
            ∂((volume : Measure (Vec d)).prod volume) +
          2 * ENNReal.ofReal sigma * (M * ∫⁻ x : Vec d, S x ∂volume +
            M * ∫⁻ x : Vec d, S x ∂volume) := by
        congr 1
        · rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
            lintegral_indicator (hU.prod hU)]
        · rw [lintegral_const_mul' _ _
            (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)]
          congr 1
          calc ∫⁻ z : Vec d × Vec d, (S z.1 + S z.2) * C (z.1 - z.2)
                ∂((volume : Measure (Vec d)).prod volume)
              = ∫⁻ z : Vec d × Vec d,
                  (S z.1 * C (z.1 - z.2) + S z.2 * C (z.1 - z.2))
                  ∂((volume : Measure (Vec d)).prod volume) :=
                lintegral_congr fun z ↦ by rw [add_mul]
            _ = (∫⁻ z : Vec d × Vec d, S z.1 * C (z.1 - z.2)
                  ∂((volume : Measure (Vec d)).prod volume)) +
                ∫⁻ z : Vec d × Vec d, S z.2 * C (z.1 - z.2)
                  ∂((volume : Measure (Vec d)).prod volume) :=
                lintegral_add_left hK2a _
            _ = M * (∫⁻ x : Vec d, S x ∂volume) +
                M * ∫⁻ x : Vec d, S x ∂volume := by rw [hI1, hI2]
    _ = 2 * ∫⁻ z in U ×ˢ U, fluxRowFractionalKernelOf sigma v z
            ∂((volume : Measure (Vec d)).prod volume) +
          4 * ENNReal.ofReal sigma * ENNReal.ofReal (Real.rpow Lam (2 * sigma)) *
            fluxRowFractionalCutoffConst d sigma *
            ∫⁻ x in U, ENNReal.ofReal (‖v x‖ ^ 2) ∂volume := by
        rw [hSint, hMdef]
        ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
