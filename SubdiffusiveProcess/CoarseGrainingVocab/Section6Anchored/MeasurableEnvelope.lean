import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GeometricSqrt
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GrowingBallDerivative
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ValueMaximum




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open MeasureTheory
open Homogenization Homogenization.IndependentSums
open SubdiffusiveProcess.Frozen.Assumptions
open scoped BigOperators ENNReal

noncomputable section

/-! ## The countable-supremum device -/

section Device

variable {Omega Index : Type*} [MeasurableSpace Omega]

/-- The `ℝ≥0∞`-valued countable supremum of a family of real observables. -/
def supEnvelopeENN (f : Index → Omega → ℝ) (omega : Omega) : ℝ≥0∞ :=
  ⨆ i : Index, ENNReal.ofReal (f i omega)

/-- The real-valued countable supremum envelope.  Its value is junk (`0`) where
the family is unbounded; every use below is guarded by boundedness. -/
def supEnvelope (f : Index → Omega → ℝ) (omega : Omega) : ℝ :=
  (supEnvelopeENN f omega).toReal

omit [MeasurableSpace Omega] in
theorem supEnvelope_nonneg (f : Index → Omega → ℝ) (omega : Omega) :
    0 ≤ supEnvelope f omega :=
  ENNReal.toReal_nonneg

theorem measurable_supEnvelope [Countable Index] {f : Index → Omega → ℝ}
    (hf : ∀ i, Measurable (f i)) : Measurable (supEnvelope f) := by
  have h : Measurable fun omega : Omega => supEnvelopeENN f omega :=
    Measurable.iSup fun i => (hf i).ennreal_ofReal
  exact h.ennreal_toReal

omit [MeasurableSpace Omega] in
theorem supEnvelopeENN_ne_top {f : Index → Omega → ℝ} {omega : Omega} {C : ℝ}
    (hC : ∀ i, f i omega ≤ C) : supEnvelopeENN f omega ≠ ⊤ := by
  have hle : supEnvelopeENN f omega ≤ ENNReal.ofReal C :=
    iSup_le fun i => ENNReal.ofReal_le_ofReal (hC i)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

omit [MeasurableSpace Omega] in
/-- On the bounded set the envelope dominates every member of the family. -/
theorem le_supEnvelope {f : Index → Omega → ℝ} {omega : Omega}
    (hbdd : ∃ C : ℝ, ∀ i, f i omega ≤ C) (i : Index) :
    f i omega ≤ supEnvelope f omega := by
  obtain ⟨C, hC⟩ := hbdd
  have hne := supEnvelopeENN_ne_top hC
  have hle : ENNReal.ofReal (f i omega) ≤ supEnvelopeENN f omega :=
    le_iSup (fun j => ENNReal.ofReal (f j omega)) i
  have hmono := ENNReal.toReal_mono hne hle
  have hself : f i omega ≤ (ENNReal.ofReal (f i omega)).toReal := by
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  exact hself.trans hmono

/-- The almost sure form: an almost sure bound turns into almost sure
domination by the *fixed measurable* envelope. -/
theorem ae_forall_le_supEnvelope {mu : Measure Omega} {f : Index → Omega → ℝ}
    (h : ∀ᵐ omega ∂mu, ∃ C : ℝ, ∀ i, f i omega ≤ C) :
    ∀ᵐ omega ∂mu, ∀ i, f i omega ≤ supEnvelope f omega := by
  filter_upwards [h] with omega homega i using le_supEnvelope homega i

end Device

/-! ## Measurability of the two observable families -/

variable {d : ℕ}

theorem measurable_anchoredPartialSum (L : ℕ) (x : Vec d) :
    Measurable fun omega : PotentialSample d => anchoredPartialSum omega L x := by
  refine Finset.measurable_sum _ fun k _ => ?_
  exact ((PotentialField.measurable_eval x).comp (measurable_pi_apply k)).sub
    ((PotentialField.measurable_eval (0 : Vec d)).comp (measurable_pi_apply k))

/-! ## The value envelope -/

/-- The value family: the deficit of the value-maximal bound at an admissible
lattice point and cutoff level, and `0` at inadmissible indices. -/
def valueDeficit (M : GMCModel d) (i : ℕ × (Fin d → ℤ) × ℕ)
    (omega : PotentialSample d) : ℝ :=
  if i.2.1 ∈ latticeBox d i.1 ∧ i.2.2 ≤ maxCutoffLevel i.1 then
    |anchoredPartialSum omega i.2.2 (latticePoint i.2.1)| -
      valueMaximalSlope d * M.delta * ((i.1 : ℝ) + 1)
  else 0

/-- The measurable additive constant of the value-maximal bound. -/
def valueEnvelope (M : GMCModel d) (omega : PotentialSample d) : ℝ :=
  supEnvelope (valueDeficit M) omega

theorem valueEnvelope_nonneg (M : GMCModel d) (omega : PotentialSample d) :
    0 ≤ valueEnvelope M omega :=
  supEnvelope_nonneg _ _

theorem valueDeficit_of_mem (M : GMCModel d) {i : ℕ × (Fin d → ℤ) × ℕ}
    (h : i.2.1 ∈ latticeBox d i.1 ∧ i.2.2 ≤ maxCutoffLevel i.1) :
    valueDeficit M i = fun omega : PotentialSample d =>
      |anchoredPartialSum omega i.2.2 (latticePoint i.2.1)| -
        valueMaximalSlope d * M.delta * ((i.1 : ℝ) + 1) := by
  funext omega
  simp only [valueDeficit]
  rw [if_pos h]

theorem valueDeficit_of_not_mem (M : GMCModel d) {i : ℕ × (Fin d → ℤ) × ℕ}
    (h : ¬ (i.2.1 ∈ latticeBox d i.1 ∧ i.2.2 ≤ maxCutoffLevel i.1)) :
    valueDeficit M i = fun _ : PotentialSample d => (0 : ℝ) := by
  funext omega
  simp only [valueDeficit]
  rw [if_neg h]

theorem measurable_valueEnvelope (M : GMCModel d) :
    Measurable (valueEnvelope M) := by
  refine measurable_supEnvelope fun i => ?_
  by_cases h : i.2.1 ∈ latticeBox d i.1 ∧ i.2.2 ≤ maxCutoffLevel i.1
  · rw [valueDeficit_of_mem M h]
    exact Measurable.sub
      (continuous_abs.measurable.comp
        (measurable_anchoredPartialSum i.2.2 (latticePoint i.2.1)))
      measurable_const
  · rw [valueDeficit_of_not_mem M h]
    exact measurable_const

/-- **The value-maximal bound with a measurable constant.** -/
theorem ae_forall_abs_anchoredPartialSum_le_valueEnvelope (M : GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ∀ n : ℕ, ∀ z : Fin d → ℤ, z ∈ latticeBox d n →
        ∀ L : ℕ, L ≤ maxCutoffLevel n →
          |anchoredPartialSum omega L (latticePoint z)| ≤
            valueMaximalSlope d * M.delta * ((n : ℝ) + 1) + valueEnvelope M omega := by
  have hbdd : ∀ᵐ omega ∂M.P.toMeasure,
      ∃ C : ℝ, ∀ i : ℕ × (Fin d → ℤ) × ℕ, valueDeficit M i omega ≤ C := by
    refine (ae_exists_forall_abs_anchoredPartialSum_le M).mono ?_
    rintro omega ⟨C, hC0, hC⟩
    refine ⟨C, fun i => ?_⟩
    by_cases h : i.2.1 ∈ latticeBox d i.1 ∧ i.2.2 ≤ maxCutoffLevel i.1
    · rw [valueDeficit_of_mem M h]
      have := hC i.1 i.2.1 h.1 i.2.2 h.2
      linarith
    · rw [valueDeficit_of_not_mem M h]
      exact hC0
  filter_upwards [ae_forall_le_supEnvelope hbdd] with omega homega n z hz L hL
  have h := homega (n, z, L)
  rw [valueDeficit_of_mem M (i := (n, z, L)) ⟨hz, hL⟩] at h
  have hval : supEnvelope (valueDeficit M) omega = valueEnvelope M omega := rfl
  rw [hval] at h
  linarith

/-! ## The derivative envelope -/

/-- The derivative family: the cube gauge of the cover divided by the graded
price `√(n+k+1)`, and `0` at inadmissible indices. -/
def coverGaugeRatio (i : (ℕ × ℕ) × (Fin d → ℤ)) (omega : PotentialSample d) : ℝ :=
  if i.2 ∈ shellCoverShifts d (coverExp i.1.1 i.1.2) then
    translatedShellG2 i.1.2 (shellCoverCenter i.2) omega /
      Real.sqrt ((i.1.1 : ℝ) + (i.1.2 : ℝ) + 1)
  else 0

/-- The measurable multiplicative constant of the growing-ball derivative
Borel–Cantelli. -/
def derivEnvelope (omega : PotentialSample d) : ℝ :=
  supEnvelope (coverGaugeRatio (d := d)) omega

theorem derivEnvelope_nonneg (omega : PotentialSample d) :
    0 ≤ derivEnvelope omega :=
  supEnvelope_nonneg _ _

theorem coverGaugeRatio_of_mem {i : (ℕ × ℕ) × (Fin d → ℤ)}
    (h : i.2 ∈ shellCoverShifts d (coverExp i.1.1 i.1.2)) :
    coverGaugeRatio i = fun omega : PotentialSample d =>
      translatedShellG2 i.1.2 (shellCoverCenter i.2) omega /
        Real.sqrt ((i.1.1 : ℝ) + (i.1.2 : ℝ) + 1) := by
  funext omega
  simp only [coverGaugeRatio]
  rw [if_pos h]

theorem coverGaugeRatio_of_not_mem {i : (ℕ × ℕ) × (Fin d → ℤ)}
    (h : ¬ i.2 ∈ shellCoverShifts d (coverExp i.1.1 i.1.2)) :
    coverGaugeRatio i = fun _ : PotentialSample d => (0 : ℝ) := by
  funext omega
  simp only [coverGaugeRatio]
  rw [if_neg h]

theorem measurable_derivEnvelope : Measurable (derivEnvelope (d := d)) := by
  refine measurable_supEnvelope fun i => ?_
  by_cases h : i.2 ∈ shellCoverShifts d (coverExp i.1.1 i.1.2)
  · rw [coverGaugeRatio_of_mem h]
    exact Measurable.div_const
      (measurable_translatedShellG2 i.1.2 (shellCoverCenter i.2)) _
  · rw [coverGaugeRatio_of_not_mem h]
    exact measurable_const

/-- **The gauge envelope with a measurable constant.** -/
theorem ae_forall_translatedShellG2_le_derivEnvelope (M : GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure,
      ∀ n k : ℕ, ∀ p ∈ shellCoverShifts d (coverExp n k),
        translatedShellG2 k (shellCoverCenter p) omega ≤
          derivEnvelope omega * Real.sqrt ((n : ℝ) + (k : ℝ) + 1) := by
  have hbdd : ∀ᵐ omega ∂M.P.toMeasure,
      ∃ C : ℝ, ∀ i : (ℕ × ℕ) × (Fin d → ℤ), coverGaugeRatio i omega ≤ C := by
    refine (ae_exists_forall_translatedShellG2_le M).mono ?_
    rintro omega ⟨C, hC0, hC⟩
    refine ⟨C, fun i => ?_⟩
    by_cases h : i.2 ∈ shellCoverShifts d (coverExp i.1.1 i.1.2)
    · rw [coverGaugeRatio_of_mem h]
      have hs : (0 : ℝ) < Real.sqrt ((i.1.1 : ℝ) + (i.1.2 : ℝ) + 1) :=
        lt_of_lt_of_le zero_lt_one (by
          have := one_le_sqrt_natSucc (i.1.1 + i.1.2)
          have hcast : (((i.1.1 + i.1.2 : ℕ) : ℝ) + 1) =
              (i.1.1 : ℝ) + (i.1.2 : ℝ) + 1 := by push_cast; ring
          rwa [hcast] at this)
      rw [div_le_iff₀ hs]
      exact hC i.1.1 i.1.2 i.2 h
    · rw [coverGaugeRatio_of_not_mem h]
      exact hC0
  filter_upwards [ae_forall_le_supEnvelope hbdd] with omega homega n k p hp
  have h := homega ((n, k), p)
  rw [coverGaugeRatio_of_mem (i := ((n, k), p)) hp] at h
  have hs : (0 : ℝ) < Real.sqrt ((n : ℝ) + (k : ℝ) + 1) :=
    lt_of_lt_of_le zero_lt_one (by
      have := one_le_sqrt_natSucc (n + k)
      have hcast : (((n + k : ℕ) : ℝ) + 1) = (n : ℝ) + (k : ℝ) + 1 := by push_cast; ring
      rwa [hcast] at this)
  rw [div_le_iff₀ hs] at h
  have hval : supEnvelope (coverGaugeRatio (d := d)) omega = derivEnvelope omega := rfl
  rw [hval] at h
  exact h

/-! ## The growing-ball readouts, deterministically

This is the body of `ae_exists_forall_growingBall_shell_bounds` (P-85) stated
with the constant as a hypothesis rather than an existential witness, so that it
can be applied with `C = derivEnvelope omega`.  That theorem is exactly the
`Filter.Eventually.mono` of this one along
`ae_exists_forall_translatedShellG2_le`. -/

/-- The three growing-ball shell readouts for any constant dominating the cube
gauges of every cover. -/
theorem growingBall_shell_bounds_of_forall_le (omega : PotentialSample d) {C : ℝ}
    (hC0 : 0 ≤ C)
    (hC : ∀ n k : ℕ, ∀ p ∈ shellCoverShifts d (coverExp n k),
      translatedShellG2 k (shellCoverCenter p) omega ≤
        C * Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) :
    ∀ n k : ℕ,
      (∀ x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
          ‖PotentialField.deriv (omega k) x‖ ≤
            C * ((((3 : ℝ) ^ k)⁻¹) * Real.sqrt ((n : ℝ) + (k : ℝ) + 1))) ∧
        (∀ x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
            ∀ y ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
              ‖PotentialField.deriv (omega k) x -
                  PotentialField.deriv (omega k) y‖ ≤
                C * ((((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹) *
                  Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * ‖x - y‖) ∧
        (∀ x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
            |omega k x - omega k 0| ≤
              growingBallRadius n *
                (C * ((((3 : ℝ) ^ k)⁻¹) *
                  Real.sqrt ((n : ℝ) + (k : ℝ) + 1)))) := by
  intro n k
  have h3 : (0 : ℝ) < (((3 : ℝ) ^ k)⁻¹) := by positivity
  set G : ℝ := C * Real.sqrt ((n : ℝ) + (k : ℝ) + 1) with hG_def
  have hGmem : ∀ p ∈ shellCoverShifts d (coverExp n k),
      translatedShellG2 k (shellCoverCenter p) omega ≤ G := hC n k
  have hgrad : ∀ x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
      ‖PotentialField.deriv (omega k) x‖ ≤ (((3 : ℝ) ^ k)⁻¹) * G := by
    intro x hx
    have hball := smul_mem_scaledBall (d := d) n k hx
    have hcube := mem_originCube_of_mem_scaledBall (d := d) n k hball
    obtain ⟨p, hp, hmem⟩ := exists_shellCoverShift_mem hcube
    have hbox := norm_deriv_unscalePotential_le_translatedShellG2 k omega p hmem
    rw [deriv_eq_smul_deriv_unscalePotential k (omega k) x, norm_smul,
      Real.norm_eq_abs, abs_of_pos h3]
    exact mul_le_mul_of_nonneg_left (hbox.trans (hGmem p hp)) h3.le
  refine ⟨fun x hx => (hgrad x hx).trans_eq (by rw [hG_def]; ring), ?_, ?_⟩
  · intro x hx y hy
    have hballx := smul_mem_scaledBall (d := d) n k hx
    have hbally := smul_mem_scaledBall (d := d) n k hy
    have hchain := norm_deriv_unscalePotential_sub_le_of_forall_le k omega hGmem
      (S := Metric.closedBall (0 : Vec d) ((((3 : ℝ) ^ k)⁻¹) * growingBallRadius n))
      (convex_closedBall _ _)
      (fun w hw => mem_originCube_of_mem_scaledBall n k hw) hballx hbally
    have hkey : PotentialField.deriv (omega k) x - PotentialField.deriv (omega k) y =
        (((3 : ℝ) ^ k)⁻¹) •
          (PotentialField.deriv (unscalePotential k (omega k))
              ((((3 : ℝ) ^ k)⁻¹) • x) -
            PotentialField.deriv (unscalePotential k (omega k))
              ((((3 : ℝ) ^ k)⁻¹) • y)) := by
      rw [smul_sub, ← deriv_eq_smul_deriv_unscalePotential k (omega k) x,
        ← deriv_eq_smul_deriv_unscalePotential k (omega k) y]
    have hscaled : ‖(((3 : ℝ) ^ k)⁻¹) • x - (((3 : ℝ) ^ k)⁻¹) • y‖ =
        (((3 : ℝ) ^ k)⁻¹) * ‖x - y‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos h3]
    rw [hscaled] at hchain
    rw [hkey, norm_smul, Real.norm_eq_abs, abs_of_pos h3]
    calc (((3 : ℝ) ^ k)⁻¹) *
          ‖PotentialField.deriv (unscalePotential k (omega k))
              ((((3 : ℝ) ^ k)⁻¹) • x) -
            PotentialField.deriv (unscalePotential k (omega k))
              ((((3 : ℝ) ^ k)⁻¹) • y)‖
        ≤ (((3 : ℝ) ^ k)⁻¹) * (G * ((((3 : ℝ) ^ k)⁻¹) * ‖x - y‖)) :=
          mul_le_mul_of_nonneg_left hchain h3.le
      _ = C * ((((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹) *
            Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * ‖x - y‖ := by
          rw [hG_def]; ring
  · intro x hx
    have hconv : Convex ℝ (Metric.closedBall (0 : Vec d) (growingBallRadius n)) :=
      convex_closedBall _ _
    have hzero : (0 : Vec d) ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n) := by
      simpa using (growingBallRadius_pos n).le
    have hmean := hconv.norm_image_sub_le_of_norm_fderiv_le
      (f := fun z : Vec d => omega k z)
      (fun z _ => ((omega k).hasFDerivAt z).differentiableAt)
      (fun z hz => by
        rw [((omega k).hasFDerivAt z).fderiv]
        exact hgrad z hz)
      hzero hx
    rw [Real.norm_eq_abs] at hmean
    have hxnorm : ‖x - (0 : Vec d)‖ ≤ growingBallRadius n := by simpa using hx
    have hGnn : 0 ≤ G := by
      rw [hG_def]
      exact mul_nonneg hC0 (Real.sqrt_nonneg _)
    have hCnn : 0 ≤ (((3 : ℝ) ^ k)⁻¹) * G := mul_nonneg h3.le hGnn
    refine hmean.trans ?_
    calc (((3 : ℝ) ^ k)⁻¹) * G * ‖x - (0 : Vec d)‖
        ≤ (((3 : ℝ) ^ k)⁻¹) * G * growingBallRadius n :=
          mul_le_mul_of_nonneg_left hxnorm hCnn
      _ = growingBallRadius n *
            (C * ((((3 : ℝ) ^ k)⁻¹) * Real.sqrt ((n : ℝ) + (k : ℝ) + 1))) := by
          rw [hG_def]; ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
