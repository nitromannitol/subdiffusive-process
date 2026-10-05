module

public import SubdiffusiveProcess.Sobolev.GMCRootCover
public import SubdiffusiveProcess.Probability.OrliczFiniteSum

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess

/-- The native finite-cover Lipschitz envelope inherits the actual GMC exponential-square
regularity bound, with its cover fixed before the model. -/
theorem exists_gmc_root_lipschitz_cover_exp_square
    {d : ℕ} (R : ℝ) :
  ∃ S : Finset (Homogenization.Vec d), S.Nonempty ∧
    (∀ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
      LipschitzOnWith
        (∑ z ∈ S, (⟨_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
           (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g),
          _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _⟩ : ℝ≥0))
        (fun x => g x) (Metric.closedBall (0 : Homogenization.Vec d) R)) ∧
    ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
    (∫⁻ g, ENNReal.ofReal (Real.exp
      (((∑ z ∈ S, _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)) /
        (∑ _z ∈ S, M.delta)) ^ 2))
      ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) ≤ 2 := by
  classical
  obtain ⟨S, hSne, hLip⟩ := exists_gmc_root_lipschitz_cover (d := d) R
  refine ⟨S, hSne, hLip, ?_⟩
  intro M
  let μ : Measure (_root_.SubdiffusiveProcess.Model.PotentialField d) :=
    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
  let X : Homogenization.Vec d →
      _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ := fun z g =>
    _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)
  let f₀ : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ≥0∞ := fun g =>
    ENNReal.ofReal (Real.exp
      ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2))
  have hδ : 0 < M.delta := M.shellPrefix.delta_pos
  have hG2 :
      Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
        Real.exp
          ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2)) μ ∧
        (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
          Real.exp
            ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2)
          ∂μ) ≤ 2 := by
    apply (SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping.ogammaLE_two_iff_of_nonneg
      hδ (fun g =>
        _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg g)).mp
    simpa [μ] using M.G2.regularity_expectation
  have hbaseAE : AEMeasurable f₀ μ := by
    change AEMeasurable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
      ENNReal.ofReal (Real.exp
        ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2))) μ
    have hgm : AEMeasurable
        (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          : _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ) μ :=
      (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable).aemeasurable
    exact (((hgm.div_const M.delta).pow_const 2).exp).ennreal_ofReal
  have hbaseLin : (∫⁻ g, f₀ g ∂μ) ≤ 2 := by
    change (∫⁻ g, ENNReal.ofReal (Real.exp
      ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2)) ∂μ) ≤ 2
    have hpos : ∀ᵐ g ∂μ, 0 ≤ Real.exp
        ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2) :=
      Filter.Eventually.of_forall fun g => (Real.exp_pos _).le
    have heq := ofReal_integral_eq_lintegral_ofReal hG2.1 hpos
    calc
      (∫⁻ g, ENNReal.ofReal (Real.exp
          ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2)) ∂μ) =
          ENNReal.ofReal (∫ g, Real.exp
            ((_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g / M.delta) ^ 2) ∂μ) :=
        heq.symm
      _ ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal hG2.2
      _ = 2 := by norm_num
  have hXmeas : ∀ z ∈ S,
      AEStronglyMeasurable (X z) μ := by
    intro z hz
    exact (_root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable.comp
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z)).aestronglyMeasurable
  have hX0 : ∀ z ∈ S, ∀ᵐ g ∂μ, 0 ≤ X z g := by
    intro z hz
    exact Filter.Eventually.of_forall fun g =>
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _
  have hXExp : ∀ z ∈ S, (∫⁻ g, ENNReal.ofReal
      (Real.exp ((X z g / M.delta) ^ 2)) ∂μ) ≤ 2 := by
    intro z hz
    have hbaseMap : AEMeasurable f₀
        (Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.translate z) μ) := by
      rw [show Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.translate z) μ = μ by
        simpa [μ] using M.G1.stationary z]
      exact hbaseAE
    have hmap := lintegral_map' hbaseMap
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z).aemeasurable
    calc
      (∫⁻ g, ENNReal.ofReal (Real.exp ((X z g / M.delta) ^ 2)) ∂μ) =
          ∫⁻ g, f₀ (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) ∂μ := by
            rfl
      _ = ∫⁻ g, f₀ g ∂Measure.map
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate z) μ := hmap.symm
      _ = ∫⁻ g, f₀ g ∂μ := by
        rw [show Measure.map (_root_.SubdiffusiveProcess.Model.PotentialField.translate z) μ = μ by
          simpa [μ] using M.G1.stationary z]
      _ ≤ 2 := hbaseLin
  have hsum := lintegral_exp_sq_finset_sum_le μ S X (fun _ => M.delta) hSne
    hXmeas hX0 (fun z hz => hδ) hXExp
  change (∫⁻ g, ENNReal.ofReal (Real.exp
      (((∑ z ∈ S, _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)) /
        (∑ z ∈ S, M.delta)) ^ 2)) ∂μ) ≤ 2
  simpa only [X] using hsum

end SubdiffusiveProcess
