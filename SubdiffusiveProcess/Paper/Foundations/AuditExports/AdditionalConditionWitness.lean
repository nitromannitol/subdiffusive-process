module

public import SubdiffusiveProcess.Paper.lem_witness_test_dyadic_cover
public import SubdiffusiveProcess.Paper.gcat_band_condexp

@[expose] public section

open SubdiffusiveProcess SubdiffusiveProcess.Paper MeasureTheory Filter Set Topology
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- The finite-test cover with its constant-only threshold chosen before the field law. -/
private theorem uniform_test_cover
    (d : ℕ) (_hd : 1 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Bsig : ℤ → ℤ → MeasurableSpace (BilateralField d))
    (Cband k0 : ℕ) (hCband : 0 < Cband) (_hk0 : 1 ≤ k0) (J : ℕ)
    (beta a lam Cp : ℝ)
    (_hbeta : 0 < beta) (ha : 0 < a) (hlam : 0 < lam) (hCp : 0 < Cp)
    (p : ℝ) (hp : 2 ≤ p)
    (hBsig_interval_mono : ∀ l₁ r₁ l₂ r₂ : ℤ,
      l₂ ≤ l₁ → r₁ ≤ r₂ → Bsig l₁ r₁ ≤ Bsig l₂ r₂)
    (hdecay_strict : beta * (Cband : ℝ) < a * p * Real.log 3) :
    ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ (P : Measure (BilateralField d)) [IsProbabilityMeasure P],
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
  intro P _ eta heta hetale T Tb hTmem hTnorm hTbband hTbae happrox
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
    let : MeasurableSpace (BilateralField d) := Bsig (n - (w k : ℤ)) (n + 2 * (w k : ℤ))
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


/-- The additional-condition clause of paper `mfd:lem-witness`. The moment order is chosen
before the condition and the disorder threshold, as in the paper's proof. `E` may be the
scalar space or a matrix space; `T` is the centered deviation and `lam` its fixed failure
threshold. Only positive band radii are required. -/
theorem additional_condition_witness
    (d : ℕ) (hd : 1 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cband : ℕ) (hCband : 0 < Cband)
    (a lam A : ℝ) (ha : 0 < a) (hlam : 0 < lam) :
    ∃ p : ℝ, 2 ≤ p ∧
      ∀ Cp : ℝ, 0 < Cp →
      ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (P : Measure (BilateralField d)) [IsProbabilityMeasure P],
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
      ∀ (E : Type) [NormedAddCommGroup E]
        (n : ℤ) (T : BilateralField d → E) (Tb : ℕ → BilateralField d → E),
        MemLp T (ENNReal.ofReal p) P →
        eLpNorm T (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cp * delta) →
        (∀ H : ℕ, 1 ≤ H →
          StronglyMeasurable[aux_gcat_band_condexp_Bsig d
            (n - ((Cband * (H + 1) : ℕ) : ℤ))
            (n + ((Cband * (H + 1) : ℕ) : ℤ))] (Tb H)) →
        (∀ H : ℕ, 1 ≤ H →
          eLpNorm (fun omega => T omega - Tb H omega) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (Cp * delta * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
        ∃ W : ℕ+ → Set (BilateralField d),
          (∀ h : ℕ+, MeasurableSet[aux_gcat_band_condexp_Bsig d
            (n - (h : ℤ)) (n + 2 * (h : ℤ))] (W h)) ∧
          (∀ h : ℕ+, P (W h) ≤ ENNReal.ofReal (Real.exp (-(A * (h : ℝ))))) ∧
          (∀ᵐ omega ∂P, lam ≤ ‖T omega‖ → omega ∈ ⋃ h : ℕ+, W h) := by
  classical
  let beta : ℝ := max A 1
  have hbeta : 0 < beta := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have halog : 0 < a * Real.log 3 := mul_pos ha (Real.log_pos (by norm_num))
  obtain ⟨q, hq⟩ := exists_nat_gt (beta * (2 * Cband : ℕ) / (a * Real.log 3))
  let p : ℝ := (q : ℝ) + 2
  have hp : 2 ≤ p := by dsimp [p]; have := Nat.cast_nonneg (α := ℝ) q; linarith
  have hdecay : beta * (2 * Cband : ℕ) < a * p * Real.log 3 := by
    have hq' := (div_lt_iff₀ halog).mp hq
    dsimp [p]
    nlinarith
  let Bsig : ℤ → ℤ → MeasurableSpace (BilateralField d) :=
    aux_gcat_band_condexp_Bsig d
  have hmono : ∀ l₁ r₁ l₂ r₂ : ℤ,
      l₂ ≤ l₁ → r₁ ≤ r₂ → Bsig l₁ r₁ ≤ Bsig l₂ r₂ := by
    intro l₁ r₁ l₂ r₂ hl hr
    apply aux_neg_restrict_mono
    intro j hj
    exact ⟨hl.trans hj.1, hj.2.trans hr⟩
  have hambient : ∀ lo hi : ℤ,
      Bsig lo hi ≤ (inferInstance : MeasurableSpace (BilateralField d)) :=
    fun lo hi => aux_neg_restrict_le_ambient (Set.Icc lo hi)
  refine ⟨p, hp, ?_⟩
  intro Cp hCp
  obtain ⟨delta0, hdelta0, hcover⟩ := uniform_test_cover d hd
    Bsig (2 * Cband) 1 (by omega) (by omega) 1 beta a lam Cp
    hbeta ha hlam hCp p hp hmono hdecay
  refine ⟨delta0, hdelta0, ?_⟩
  intro P _ delta hdelta hsmall E _ n T Tb hT hnorm hTb herr
  let U : BilateralField d → ℝ := fun omega => ‖T omega‖
  let Ub : ℕ → BilateralField d → ℝ := fun H omega => ‖Tb (H + 1) omega‖
  have hUm : MemLp U (ENNReal.ofReal p) P := hT.norm
  have hUnorm : eLpNorm U (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cp * delta) := by
    rw [show U = (fun omega => ‖T omega‖) from rfl,
      eLpNorm_norm T hT.aestronglyMeasurable]
    exact hnorm
  have hUbm : ∀ H, StronglyMeasurable[Bsig
      (n - (((2 * Cband) * (H + 1) : ℕ) : ℤ))
      (n + (((2 * Cband) * (H + 1) : ℕ) : ℤ))] (Ub H) := by
    intro H
    have hrad : Cband * (H + 1 + 1) ≤ (2 * Cband) * (H + 1) := by
      nlinarith
    have hradZ : (Cband * (H + 1 + 1) : ℕ) ≤ (((2 * Cband) * (H + 1) : ℕ) : ℤ) :=
      by exact_mod_cast hrad
    exact (hTb (H + 1) (by omega)).norm.mono (hmono _ _ _ _ (by omega) (by omega))
  have hUba : ∀ H, AEStronglyMeasurable (Ub H) P :=
    fun H => ((hUbm H).mono (hambient _ _)).aestronglyMeasurable
  have hUerr : ∀ H,
      eLpNorm (fun omega => U omega - Ub H omega) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Cp * delta * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
    intro H
    calc eLpNorm (fun omega => U omega - Ub H omega) (ENNReal.ofReal p) P
        ≤ eLpNorm (fun omega => T omega - Tb (H + 1) omega) (ENNReal.ofReal p) P := by
          apply eLpNorm_mono (hUm.aestronglyMeasurable.sub (hUba H))
          intro omega
          simpa only [U, Ub, Pi.sub_apply, Real.norm_eq_abs] using abs_norm_sub_norm_le (T omega) (Tb (H + 1) omega)
      _ ≤ ENNReal.ofReal (Cp * delta * (3 : ℝ) ^ (-(a * ((H + 1 : ℕ) : ℝ)))) :=
        herr (H + 1) (by omega)
      _ ≤ ENNReal.ofReal (Cp * delta * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ (mul_pos hCp hdelta).le
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          simp only [Nat.cast_add, Nat.cast_one]
          linarith
  obtain ⟨Sigma, hSigma, hPSigma, hSigmaProp⟩ := lem_witness_common_ae_limit
    (BilateralField d) P Unit p a Cp delta hp ha hCp hdelta
    (fun _ => U) (fun _ => Ub) (fun _ => hUm) (fun _ => hUba) (fun _ => hUerr)
  let Y : ℤ → Fin 1 → BilateralField d → ℝ :=
    fun k _ omega => if k = n then U omega else 0
  let Yb : ℤ → Fin 1 → ℕ → BilateralField d → ℝ :=
    fun k _ H omega => if k = n then Ub H omega else 0
  have hYm : ∀ k i, MemLp (Y k i) (ENNReal.ofReal p) P := by
    intro k i
    by_cases hk : k = n
    · simpa only [Y, ite_eq_left hk] using hUm
    · simpa only [Y, ite_eq_right hk] using (MemLp.zero' (μ := P) (p := ENNReal.ofReal p) (ε := ℝ))
  have hYn : ∀ k i, eLpNorm (Y k i) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cp * delta) := by
    intro k i
    by_cases hk : k = n
    · simpa only [Y, ite_eq_left hk] using hUnorm
    · simp only [Y, ite_eq_right hk, eLpNorm_fun_zero, zero_le]
  have hYbm : ∀ k i H, StronglyMeasurable[Bsig
      (k - (((2 * Cband) * (H + 1) : ℕ) : ℤ))
      (k + (((2 * Cband) * (H + 1) : ℕ) : ℤ))] (Yb k i H) := by
    intro k i H
    by_cases hk : k = n
    · subst k
      simpa only [Yb, ↓reduceIte] using hUbm H
    · simpa only [Yb, ite_eq_right hk] using
        (stronglyMeasurable_const : StronglyMeasurable[Bsig
          (k - (((2 * Cband) * (H + 1) : ℕ) : ℤ))
          (k + (((2 * Cband) * (H + 1) : ℕ) : ℤ))] (fun _ : BilateralField d => (0 : ℝ)))
  have hYba : ∀ k i H, AEStronglyMeasurable (Yb k i H) P :=
    fun k i H => ((hYbm k i H).mono (hambient _ _)).aestronglyMeasurable
  have hYerr : ∀ k i H,
      eLpNorm (fun omega => Y k i omega - Yb k i H omega) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Cp * delta * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
    intro k i H
    by_cases hk : k = n
    · simpa only [Y, Yb, ite_eq_left hk] using hUerr H
    · simp only [Y, Yb, ite_eq_right hk, sub_self, eLpNorm_fun_zero, zero_le]
  have hYlim : ∀ omega, omega ∈ Sigma → ∀ k i,
      Tendsto (fun H => Yb k i H omega) atTop (𝓝 (Y k i omega)) := by
    intro omega homega k i
    by_cases hk : k = n
    · simpa only [Y, Yb, ite_eq_left hk] using hSigmaProp () omega homega
    · simpa only [Y, Yb, ite_eq_right hk] using (tendsto_const_nhds (x := (0 : ℝ)))
  obtain ⟨W, hWm, hWp, hWcover⟩ := hcover P delta hdelta hsmall
    Y Yb hYm hYn hYbm hYba hYerr Sigma hSigma hPSigma hYlim n
  refine ⟨W, hWm, fun h => (hWp h).trans ?_, ?_⟩
  · apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (le_max_left A 1) (show 0 ≤ (h : ℝ) by positivity)
    dsimp [beta]
    linarith
  · have hSigmaAe : ∀ᵐ omega ∂P, omega ∈ Sigma := by
      apply (ae_iff).mpr
      change P Sigmaᶜ = 0
      rw [measure_compl hSigma (by simp), hPSigma]
      simp only [measure_univ, tsub_self]
    filter_upwards [hSigmaAe] with omega homega hbad
    apply hWcover
    refine ⟨homega, 0, ?_⟩
    simpa only [Y, ↓reduceIte] using hbad

end SubdiffusiveProcess.AuditExports
