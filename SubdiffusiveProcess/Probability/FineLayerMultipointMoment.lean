import SubdiffusiveProcess.Probability.FineLayerMoment

open MeasureTheory ProbabilityTheory Homogenization
open scoped BigOperators
noncomputable section
namespace SubdiffusiveProcess

theorem fineLayer_multiPoint_exp_moment_le
    {d : ℕ} (p : ℕ) (hp : 1 ≤ p)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (x : Fin p → Vec d)
    (hpdelta : (p : ℝ) * M.delta ≤ 1) :
    Integrable
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
        Real.exp (∑ i : Fin p, g (x i)))
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure ∧
    (∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      Real.exp (∑ i : Fin p, g (x i))
        ∂(SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure) ≤
      Real.exp ((Real.log 2 / 2) * (p : ℝ) ^ 2 * M.delta ^ 2) := by
  classical
  let μ := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpInv : 0 ≤ (p : ℝ)⁻¹ := (inv_pos.mpr hpR).le
  have hpOne : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpInv_le_one : (p : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hpR).2 hpOne
  have hweight : ∑ i : Fin p, (p : ℝ)⁻¹ = 1 := by
    simp [hpR.ne']
  have hscalar : ∀ i : Fin p,
      Integrable
          (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
            Real.exp ((p : ℝ) * g (x i))) μ ∧
        (∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
          Real.exp ((p : ℝ) * g (x i)) ∂μ) ≤
          Real.exp ((Real.log 2 / 2) * (p : ℝ) ^ 2 * M.delta ^ 2) := by
    intro i
    have hpnonneg : (0 : ℝ) ≤ (p : ℝ) := by positivity
    simpa [μ, abs_of_nonneg hpnonneg] using
      (fineLayer_exp_moment_le (p : ℝ) M (x i) (by simpa using hpdelta))
  have hfi : ∀ i : Fin p,
      Integrable
        (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
          Real.exp ((p : ℝ) * g (x i))) μ := fun i => (hscalar i).1
  have hsum : Integrable
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
        ∑ i : Fin p, Real.exp ((p : ℝ) * g (x i))) μ := by
    simpa using
      (integrable_finset_sum (μ := μ) (Finset.univ : Finset (Fin p))
        (fun i _ => hfi i))
  have hpoint : ∀ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
      Real.exp (∑ i : Fin p, g (x i)) ≤
        (p : ℝ)⁻¹ * ∑ i : Fin p, Real.exp ((p : ℝ) * g (x i)) := by
    intro g
    have hj := convexOn_exp.map_sum_le
      (t := (Finset.univ : Finset (Fin p)))
      (w := fun _ : Fin p => (p : ℝ)⁻¹)
      (p := fun i : Fin p => (p : ℝ) * g (x i))
      (fun _ _ => hpInv) hweight (fun _ _ => Set.mem_univ _)
    simpa [smul_eq_mul, ← Finset.mul_sum, hpR.ne'] using hj
  have hleft : Integrable
      (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
        Real.exp (∑ i : Fin p, g (x i))) μ := by
    have hmeas : Measurable
        (fun g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d =>
          Real.exp (∑ i : Fin p, g (x i))) := by
      apply Measurable.exp
      apply Finset.measurable_sum
      intro i hi
      exact SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_eval (x i)
    refine hsum.mono' ?_ ?_
    · exact hmeas.aestronglyMeasurable
    · filter_upwards with g
      calc
        ‖Real.exp (∑ i : Fin p, g (x i))‖ =
            Real.exp (∑ i : Fin p, g (x i)) :=
          Real.norm_of_nonneg (Real.exp_pos _).le
        _ ≤ (p : ℝ)⁻¹ * ∑ i : Fin p,
            Real.exp ((p : ℝ) * g (x i)) := hpoint g
        _ ≤ ‖∑ i : Fin p, Real.exp ((p : ℝ) * g (x i))‖ := by
          rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ =>
            (Real.exp_pos _).le)]
          exact mul_le_of_le_one_left
            (Finset.sum_nonneg fun i _ => (Real.exp_pos _).le) hpInv_le_one
        _ = ∑ i : Fin p, Real.exp ((p : ℝ) * g (x i)) :=
          Real.norm_of_nonneg (Finset.sum_nonneg fun i _ =>
            (Real.exp_pos _).le)
  refine ⟨?_, ?_⟩
  · simpa [μ] using hleft
  · have hbound :
        ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            Real.exp (∑ i : Fin p, g (x i)) ∂μ ≤
          ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            (p : ℝ)⁻¹ * ∑ i : Fin p, Real.exp ((p : ℝ) * g (x i)) ∂μ := by
      exact integral_mono hleft
        (hsum.const_mul (p : ℝ)⁻¹) hpoint
    calc
      ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
          Real.exp (∑ i : Fin p, g (x i)) ∂μ ≤
        ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
          (p : ℝ)⁻¹ * ∑ i : Fin p, Real.exp ((p : ℝ) * g (x i)) ∂μ := hbound
      _ = (p : ℝ)⁻¹ * ∑ i : Fin p,
          ∫ g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            Real.exp ((p : ℝ) * g (x i)) ∂μ := by
        rw [integral_const_mul]
        rw [integral_finset_sum (μ := μ) Finset.univ (fun i _ => hfi i)]
      _ ≤ (p : ℝ)⁻¹ * ∑ _i : Fin p,
          Real.exp ((Real.log 2 / 2) * (p : ℝ) ^ 2 * M.delta ^ 2) := by
        gcongr with i
        exact (hscalar i).2
      _ = Real.exp ((Real.log 2 / 2) * (p : ℝ) ^ 2 * M.delta ^ 2) := by
        simp [Finset.sum_const, hpR.ne']

end SubdiffusiveProcess
