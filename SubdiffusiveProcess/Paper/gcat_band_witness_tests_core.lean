import SubdiffusiveProcess.Paper.gcat_band_condexp
import SubdiffusiveProcess.Paper.lem_witness

open MeasureTheory Filter Set SubdiffusiveProcess
open scoped ENNReal BigOperators Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Almost-sure band limits for the finite tests. -/
theorem aux_gcat_band_witness_tests_core_sigma
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
    (n : ℤ) (Cband J : ℕ) (a Cp eta p : ℝ) (hp : 2 ≤ p) (ha : 0 < a) (hCp : 0 < Cp) (heta : 0 < eta)
    (Tt : Fin J → BilateralField d → ℝ) (Ttb : Fin J → ℕ → BilateralField d → ℝ)
    (hTtmem : ∀ i, MemLp (Tt i) (ENNReal.ofReal p) P)
    (hTtbmeas : ∀ i H, 1 ≤ H →
      StronglyMeasurable[aux_gcat_band_condexp_Bsig d (n - ((Cband * (H + 1) : ℕ) : ℤ))
        (n + ((Cband * (H + 1) : ℕ) : ℤ))] (Ttb i H))
    (hTterr : ∀ i H, 1 ≤ H → eLpNorm (fun om => Tt i om - Ttb i H om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ))))) :
    ∃ Sigma : Set (BilateralField d), MeasurableSet Sigma ∧ P Sigma = 1 ∧
      (∀ om ∈ Sigma, ∀ i, Tendsto (fun H => Ttb i (H + 1) om) atTop (𝓝 (Tt i om))) := by
  classical
  have hle := aux_gcat_band_condexp_Bsig_le d
  have hrate3 : ∀ H : ℕ, (3 : ℝ) ^ (-(a * (((H + 1 : ℕ) : ℝ)))) ≤ (3 : ℝ) ^ (-(a * (H : ℝ))) := by
    intro H
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    nlinarith
  have hCpeta : 0 ≤ Cp * eta := (mul_pos hCp heta).le
  obtain ⟨Sigma, hSigmeas, hSigP, hSiglim⟩ :=
    lem_witness_common_ae_limit (BilateralField d) P (Fin J) p a Cp eta hp ha hCp heta Tt
      (fun i H => Ttb i (H + 1)) hTtmem
      (fun i H => ((hTtbmeas i (H + 1) (by omega)).mono (hle _ _)).aestronglyMeasurable)
      (fun i H => ((hTterr i (H + 1) (by omega)).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (hrate3 H) hCpeta))))
  exact ⟨Sigma, hSigmeas, hSigP, fun om hom i => hSiglim i om hom⟩

/-- Finite-test part of the abstract cover (the base-band Markov estimate and dyadic telescoping of
`lem_witness_test_dyadic_cover`, at one level `n`), with the disorder threshold produced before the law. -/
theorem gcat_band_witness_tests_core
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cband J : ℕ) (hCband : 0 < Cband)
    (beta a lam Cp p : ℝ) (ha : 0 < a) (hlam : 0 < lam) (hCp : 0 < Cp)
    (hp : 2 ≤ p) (hdecay : beta * (Cband : ℝ) < a * p * Real.log 3) :
    ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ eta : ℝ, 0 < eta → eta ≤ eta0 →
      ∀ (P : Measure (BilateralField d)) [IsProbabilityMeasure P] (n : ℤ)
        (Tt : Fin J → BilateralField d → ℝ) (Ttb : Fin J → ℕ → BilateralField d → ℝ),
      (∀ i, MemLp (Tt i) (ENNReal.ofReal p) P) →
      (∀ i, eLpNorm (Tt i) (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cp * eta)) →
      (∀ i H, 1 ≤ H →
        StronglyMeasurable[aux_gcat_band_condexp_Bsig d (n - ((Cband * (H + 1) : ℕ) : ℤ))
          (n + ((Cband * (H + 1) : ℕ) : ℤ))] (Ttb i H)) →
      (∀ i H, 1 ≤ H → eLpNorm (fun om => Tt i om - Ttb i H om) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (Cp * eta * (3 : ℝ) ^ (-(a * (H : ℝ))))) →
      ∃ Sigma : Set (BilateralField d), MeasurableSet Sigma ∧ P Sigma = 1 ∧
        ∃ Wt : ℕ+ → Set (BilateralField d),
          (∀ h : ℕ+, MeasurableSet[aux_gcat_band_condexp_Bsig d (n - (h : ℤ)) (n + 2 * (h : ℤ))]
            (Wt h)) ∧
          (∀ h : ℕ+, P (Wt h) ≤ ENNReal.ofReal (Real.exp (-(beta * ((h : ℕ) : ℝ))))) ∧
          Sigma ∩ {om | ∃ i : Fin J, lam ≤ Tt i om} ⊆ ⋃ h : ℕ+, Wt h := by
  classical
  have hp0 : 0 < p := by linarith only [hp]
  obtain ⟨q, r, hqeq, hq, hq1, hr, hr1, hrate⟩ :=
    aux_geometric_rate a (beta * (Cband : ℝ)) p ha hp0 hdecay
  let K : ℝ := lam * (1 - r) / 2
  have hK : 0 < K := by
    dsimp [K]
    exact div_pos (mul_pos hlam (sub_pos.mpr hr1)) (by norm_num)
  obtain ⟨eta0, heta0, hbudget⟩ :=
    aux_geometric_budget J p (beta * (Cband : ℝ)) Cp q r K hp0 hCp hq hr hK hrate
  refine ⟨eta0, heta0, ?_⟩
  intro eta heta hetale P _ n Tt Ttb hTtmem hTtnorm hTtbmeas hTterr
  have hle := aux_gcat_band_condexp_Bsig_le d
  have hCpeta : 0 ≤ Cp * eta := (mul_pos hCp heta).le
  obtain ⟨Sigma, hSigmeas, hSigP, hSigT⟩ :=
    aux_gcat_band_witness_tests_core_sigma d P n Cband J a Cp eta p hp ha hCp heta Tt Ttb hTtmem
      hTtbmeas hTterr
  -- internal approximants: zero at level 0
  let Tb : Fin J → ℕ → BilateralField d → ℝ := fun i H => if H = 0 then fun _ => 0 else Ttb i H
  have hTbband : ∀ i H, StronglyMeasurable[aux_gcat_band_condexp_Bsig d
      (n - ((Cband * (H + 1) : ℕ) : ℤ)) (n + ((Cband * (H + 1) : ℕ) : ℤ))] (Tb i H) := by
    intro i H
    by_cases hH : H = 0
    · simp only [Tb, hH, if_true]; exact stronglyMeasurable_const
    · simp only [Tb, hH, if_false]; exact hTtbmeas i H (by omega)
  have hTbae : ∀ i H, AEStronglyMeasurable (Tb i H) P := fun i H =>
    ((hTbband i H).mono (hle _ _)).aestronglyMeasurable
  have hgeom : ∀ H : ℕ, (3 : ℝ) ^ (-(a * (H : ℝ))) = q ^ H := by
    intro H
    calc (3 : ℝ) ^ (-(a * (H : ℝ))) = (3 : ℝ) ^ ((-a) * (H : ℝ)) := by congr 1; ring
      _ = ((3 : ℝ) ^ (-a)) ^ H := Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3) (-a) H
      _ = q ^ H := by rw [hqeq]
  have herror : ∀ i H, eLpNorm (fun om => Tt i om - Tb i H om) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Cp * eta * q ^ H) := by
    intro i H
    by_cases hH : H = 0
    · simp only [Tb, hH, if_true, sub_zero, pow_zero, mul_one]
      exact hTtnorm i
    · simp only [Tb, hH, if_false]
      simpa only [hgeom H] using hTterr i H (by omega)
  let w : ℕ → ℕ+ := fun k => ⟨Cband * (k + 1), Nat.mul_pos hCband (Nat.succ_pos k)⟩
  have hw : Function.Injective w := by
    intro j k hjk
    have heq : Cband * (j + 1) = Cband * (k + 1) := congrArg (fun h : ℕ+ => (h : ℕ)) hjk
    have hsucc : j + 1 = k + 1 := mul_left_cancel₀ (ne_of_gt hCband) heq
    omega
  have hwr : ∀ k : ℕ, (w k : ℝ) = (Cband : ℝ) * ((k : ℝ) + 1) := by
    intro k
    change ((Cband * (k + 1) : ℕ) : ℝ) = (Cband : ℝ) * ((k : ℝ) + 1)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hTbwindow : ∀ (i : Fin J) (k j : ℕ), j ≤ k →
      StronglyMeasurable[aux_gcat_band_condexp_Bsig d (n - (w k : ℤ)) (n + 2 * (w k : ℤ))]
        (Tb i j) := by
    intro i k j hj
    have hrad : ((Cband * (j + 1) : ℕ) : ℤ) ≤ ((Cband * (k + 1) : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_le_mul_left Cband (Nat.add_le_add_right hj 1)
    have hrad0 : (0 : ℤ) ≤ ((Cband * (k + 1) : ℕ) : ℤ) := by positivity
    apply (hTbband i j).mono
    have hsub : Set.Icc (n - ((Cband * (j + 1) : ℕ) : ℤ)) (n + ((Cband * (j + 1) : ℕ) : ℤ)) ⊆
        Set.Icc (n - (w k : ℤ)) (n + 2 * (w k : ℤ)) := by
      intro x hx
      simp only [Set.mem_Icc] at hx ⊢
      change n - ((Cband * (k + 1) : ℕ) : ℤ) ≤ x ∧ x ≤ n + 2 * ((Cband * (k + 1) : ℕ) : ℤ)
      constructor <;> omega
    exact aux_neg_restrict_mono (E := C(SpatialCoordinates d, ℝ)) hsub
  have hYmeas : ∀ (i : Fin J) (k : ℕ),
      StronglyMeasurable[aux_gcat_band_condexp_Bsig d (n - (w k : ℤ)) (n + 2 * (w k : ℤ))]
        (fun om => aux_increment (fun H => Tb i H om) k) := by
    intro i k
    cases k with
    | zero => exact hTbwindow i 0 0 le_rfl
    | succ k =>
        exact (hTbwindow i (k + 1) (k + 1) le_rfl).sub (hTbwindow i (k + 1) k (Nat.le_succ k))
  let E : ℕ → Set (BilateralField d) := fun k =>
    ⋃ i : Fin J, {om | K * r ^ k ≤ |aux_increment (fun H => Tb i H om) k|}
  have hEmeas : ∀ k : ℕ,
      MeasurableSet[aux_gcat_band_condexp_Bsig d (n - (w k : ℤ)) (n + 2 * (w k : ℤ))] (E k) := by
    intro k
    apply MeasurableSet.iUnion
    intro i
    letI : MeasurableSpace (BilateralField d) :=
      aux_gcat_band_condexp_Bsig d (n - (w k : ℤ)) (n + 2 * (w k : ℤ))
    exact measurableSet_le measurable_const ((hYmeas i k).measurable.abs)
  have hEprob : ∀ k : ℕ, P (E k) ≤ ENNReal.ofReal (Real.exp (-(beta * (w k : ℝ)))) := by
    intro k
    have hthreshold : 0 < K * r ^ k := mul_pos hK (pow_pos hr _)
    have htail : ∀ i : Fin J,
        P {om | K * r ^ k ≤ |aux_increment (fun H => Tb i H om) k|} ≤
          ENNReal.ofReal (2 * ((2 * (Cp * eta / q * q ^ k) / (K * r ^ k)) ^ p)) := by
      intro i
      exact aux_increment_tail P p (Cp * eta) q hp0 hCpeta hq hq1.le
        (Tt i) (Tb i) (hTtmem i).1 (hTbae i) (hTtnorm i) (herror i) k (K * r ^ k) hthreshold
    calc
      P (E k) ≤ ENNReal.ofReal
          ((J : ℝ) * (2 * ((2 * (Cp * eta / q * q ^ k) / (K * r ^ k)) ^ p))) :=
        aux_fin_union_bound P J
          (fun i => {om | K * r ^ k ≤ |aux_increment (fun H => Tb i H om) k|})
          (2 * ((2 * (Cp * eta / q * q ^ k) / (K * r ^ k)) ^ p))
          (by positivity) htail
      _ ≤ ENNReal.ofReal (Real.exp (-((beta * (Cband : ℝ)) * ((k : ℝ) + 1)))) :=
        ENNReal.ofReal_le_ofReal (hbudget eta heta hetale k)
      _ = ENNReal.ofReal (Real.exp (-(beta * (w k : ℝ)))) := by
        rw [hwr]
        congr 2
        ring
  have hlimit : ∀ om ∈ Sigma, ∀ i, Tendsto (fun H => Tb i H om) atTop (𝓝 (Tt i om)) := by
    intro om hom i
    have h2 : Tendsto (fun H => Ttb i H om) atTop (𝓝 (Tt i om)) :=
      (tendsto_add_atTop_iff_nat 1).mp (hSigT om hom i)
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with H hH
    have hne : H ≠ 0 := by omega
    simp [Tb, hne]
  have hcover : Sigma ∩ {om | ∃ i : Fin J, lam ≤ Tt i om} ⊆ ⋃ k : ℕ, E k := by
    intro om hom
    obtain ⟨i, hi⟩ := hom.2
    obtain ⟨k, hk⟩ := aux_increment_witness
      (fun H => Tb i H om) (Tt i om) lam r hlam hr.le (hlimit om hom.1 i) hi
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    exact hk
  obtain ⟨Wt, hWtmeas, hWtprob, hWtcover⟩ := aux_reindex_cover P
    (fun h => aux_gcat_band_condexp_Bsig d (n - (h : ℤ)) (n + 2 * (h : ℤ)))
    (fun h => ENNReal.ofReal (Real.exp (-(beta * (h : ℝ)))))
    (Sigma ∩ {om | ∃ i : Fin J, lam ≤ Tt i om}) w hw E hEmeas hEprob hcover
  exact ⟨Sigma, hSigmeas, hSigP, Wt, hWtmeas, hWtprob, hWtcover⟩

end Paper
