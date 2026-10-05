module

public import SubdiffusiveProcess.Paper.prop_conc_cutoff_affine_coercivity
public import SubdiffusiveProcess.Paper.prop_conc_normalized_growth
public import SubdiffusiveProcess.Paper.lem_band

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators

namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Uniform first moments of the inverse finite responses prevent a zero limit.
The inverse is taken in ENNReal during Fatou, so a zero limit has infinite cost. -/
theorem aux_prop_conc_limit_positive_of_inverse_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (R : ℕ → Ω → ℝ) (f : Ω → ℝ) (C : ℝ)
    (hRmeas : ∀ n, AEStronglyMeasurable (R n) P)
    (hRpos : ∀ n, ∀ᵐ ω ∂P, 0 < R n ω)
    (hRinv : ∀ n, eLpNorm (fun ω => (R n ω)⁻¹) 1 P ≤ ENNReal.ofReal C)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop (𝓝 (f ω))) :
    ∀ᵐ ω ∂P, 0 < f ω := by
  let g : ℕ → Ω → ℝ≥0∞ := fun n ω => (ENNReal.ofReal (R n ω))⁻¹
  have hgmeas (n : ℕ) : AEMeasurable (g n) P :=
    (hRmeas n).aemeasurable.ennreal_ofReal.inv
  have hgint (n : ℕ) : ∫⁻ ω, g n ω ∂P ≤ ENNReal.ofReal C := by
    have heq : (∫⁻ ω, g n ω ∂P) = eLpNorm (fun ω => (R n ω)⁻¹) 1 P := by
      have hInvMeas : AEStronglyMeasurable (fun ω => (R n ω)⁻¹) P :=
        (hRmeas n).aemeasurable.inv.aestronglyMeasurable
      rw [eLpNorm_one_eq_lintegral_enorm hInvMeas]
      apply lintegral_congr_ae
      filter_upwards [hRpos n] with ω hω
      exact (ENNReal.ofReal_inv_of_pos hω).symm.trans
        (Real.enorm_eq_ofReal (inv_nonneg.mpr hω.le)).symm
    rw [heq]
    exact hRinv n
  have hgconv : ∀ᵐ ω ∂P, liminf (fun n => g n ω) atTop =
      (ENNReal.ofReal (f ω))⁻¹ := by
    filter_upwards [hlim] with ω hω
    exact ((ENNReal.continuous_ofReal.tendsto (f ω)).comp hω).inv.liminf_eq
  have hbound : ∫⁻ ω, (ENNReal.ofReal (f ω))⁻¹ ∂P ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ ω, liminf (fun n => g n ω) atTop ∂P :=
        lintegral_congr_ae (hgconv.mono fun _ h => h.symm)
      _ ≤ liminf (fun n => ∫⁻ ω, g n ω ∂P) atTop := lintegral_liminf_le' hgmeas
      _ ≤ ENNReal.ofReal C := liminf_le_of_frequently_le'
        (Filter.Eventually.of_forall hgint).frequently
  have hfmeas := aestronglyMeasurable_of_tendsto_ae atTop hRmeas hlim
  have hfinite := ae_lt_top' hfmeas.aemeasurable.ennreal_ofReal.inv
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound)
  filter_upwards [hfinite] with ω hω
  exact ENNReal.ofReal_ne_zero_iff.mp (ENNReal.inv_ne_top.mp hω.ne)



/-- Actual unit-cell affine limits have reciprocal-trace moments at each
prescribed order. The disorder threshold and moment constant are selected
before the model, representation and subsequence. The factor d⁻¹ is retained. -/
theorem prop_conc_unit_inverse_trace_moment (d : ℕ) (hd : 2 ≤ d)
    (I : in_J d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta0 Cq : ℝ, 0 < delta0 ∧ 0 < Cq ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (M : _root_.SubdiffusiveProcess.Model.GMCModel d), M.delta ≤ delta0 →
      ∀ (_Rm : in_responses d M) (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (field : Ω → BilateralField d),
        MeasurePreserving field P (chaosSampleLaw M).toMeasure →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
          (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
          ‖(u : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph
              (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) u‖)
        (N : ℕ → ℕ) (A : Ω → Matrix (Fin d) (Fin d) ℝ),
        (∀ᵐ om ∂P, ∀ i : Fin d,
          Tendsto (fun n =>
            affineDirichletResponse
              (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) hP
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (field om) (N n)
                (0 : SpatialCoordinates d) one_pos) (Pi.single i 1))
            atTop (𝓝 (A om i i))) →
        (∀ᵐ om ∂P, 0 < Matrix.trace (A om)) ∧
        AEStronglyMeasurable (fun om => (Matrix.trace (A om))⁻¹) P ∧
        eLpNorm (fun om => (Matrix.trace (A om))⁻¹) (ENNReal.ofReal q) P ≤
          ENNReal.ofReal (Cq / d) := by
  let : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  let : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  obtain ⟨delta0, Cd, hdelta0, _hCd, _hrate1, _hrate2, Cq, hCq, hmom⟩ :=
    aux_lem_band_rb_uniform_cell_moment d hd I q hq (1 / 8) (by norm_num)
      (0 : SpatialCoordinates d) 1 one_pos le_rfl
  refine ⟨delta0, Cq, hdelta0, hCq, ?_⟩
  intro mC bC
  have hmC : mC = borel C(SpatialCoordinates d, ℝ) := bC.measurable_eq
  subst mC
  intro M hdelta Rm H hIR Ω _ P _ field hfield hP N A hlim
  let : NeZero d := ⟨by omega⟩
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  let Q := centeredCube (0 : SpatialCoordinates d) 1 one_pos
  let V : ℕ → Ω → Fin d → ℝ := fun n om i =>
    affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) hP
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (field om) (N n)
        (0 : SpatialCoordinates d) one_pos) (Pi.single i 1)
  let R : ℕ → Ω → ℝ := fun n om => ∑ i : Fin d, V n om i
  let K : ℕ → BilateralField d → ℝ := fun n om =>
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale (originCube d 0) 0
      (I.chart (0 : SpatialCoordinates d) 1 one_pos
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H om (N n) (0 : SpatialCoordinates d) one_pos)
        (0 : SpatialCoordinates d) 1)
  have hKmeas (n : ℕ) : AEStronglyMeasurable (K n) (chaosSampleLaw M).toMeasure := by
    simpa [K] using (hmom M Rm H hIR hdelta (N n) 0).1
  have hKnorm (n : ℕ) :
      eLpNorm (K n) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cq := by
    simpa [K] using (hmom M Rm H hIR hdelta (N n) 0).2
  have hVmeas (n : ℕ) (i : Fin d) : Measurable (fun om => V n om i) :=
    (aux_prop_conc_resp_measurable M H hIR.1 (N n) (0 : SpatialCoordinates d)
      one_pos hP (Pi.single i 1)).comp hfield.measurable
  have hRmeas (n : ℕ) : AEStronglyMeasurable (R n) P :=
    (Finset.measurable_sum _ fun i _ => hVmeas n i).aestronglyMeasurable
  have hfinite (n : ℕ) (om : Ω) :
      0 < R n om ∧ (R n om)⁻¹ ≤ K n (field om) / d := by
    have hdiag (i : Fin d) : 0 ≤ V n om i :=
      dirichletResponse_nonneg _ _ _
    have hcoercive (i : Fin d) : 1 ≤ K n (field om) * V n om i := by
      simpa only [V, K, centeredCube_volume_real, one_pow,
        div_one, dotProduct, Pi.single_apply, mul_ite, ite_mul, zero_mul,
        mul_zero, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
        prop_conc_cutoff_affine_coercivity I M H (field om) (N n)
          (0 : SpatialCoordinates d) 1 one_pos hP (Pi.single i 1)
    simpa only [Matrix.trace_diagonal] using
      aux_prop_conc_reciprocal_trace_le hd0 (Matrix.diagonal (V n om)) (K n (field om))
        (fun i => by simpa only [Matrix.diagonal_apply_eq] using hdiag i)
        (fun i => by simpa only [Matrix.diagonal_apply_eq] using hcoercive i)
  have hfiniteNorm (n : ℕ) :
      eLpNorm (fun om => (R n om)⁻¹) (ENNReal.ofReal q) P ≤ ENNReal.ofReal (Cq / d) := by
    have hpoint : ∀ᵐ om ∂P, ‖(R n om)⁻¹‖ ≤ (d : ℝ)⁻¹ * K n (field om) :=
      Filter.Eventually.of_forall fun om => by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hfinite n om).1)]
        simpa only [div_eq_mul_inv, mul_comm] using (hfinite n om).2
    apply (eLpNorm_mono_ae_real (p := ENNReal.ofReal q)
      ((hRmeas n).aemeasurable.inv.aestronglyMeasurable) hpoint).trans
    change eLpNorm ((d : ℝ)⁻¹ • (K n ∘ field)) (ENNReal.ofReal q) P ≤ _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (inv_nonneg.mpr hdR.le),
      eLpNorm_comp_measurePreserving (hKmeas n) hfield]
    calc
      _ ≤ ENNReal.ofReal (d : ℝ)⁻¹ * ENNReal.ofReal Cq :=
        mul_le_mul_right (hKnorm n) _
      _ = ENNReal.ofReal (Cq / d) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hdR.le)]
        congr 1
        rw [div_eq_mul_inv, mul_comm]
  have hRlim : ∀ᵐ om ∂P, Tendsto (fun n => R n om) atTop (𝓝 (Matrix.trace (A om))) := by
    filter_upwards [hlim] with om hom
    exact tendsto_finsetSum _ (fun i _ => hom i)
  have hpositive : ∀ᵐ om ∂P, 0 < Matrix.trace (A om) := by
    apply aux_prop_conc_limit_positive_of_inverse_moment P R
      (fun om => Matrix.trace (A om)) (Cq / d) hRmeas
      (fun n => Filter.Eventually.of_forall fun om => (hfinite n om).1) ?_ hRlim
    intro n
    exact (eLpNorm_le_eLpNorm_of_exponent_le
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq)).trans (hfiniteNorm n)
  refine ⟨hpositive,
    (aestronglyMeasurable_of_tendsto_ae atTop hRmeas hRlim).aemeasurable.inv.aestronglyMeasurable,
    ?_⟩
  exact aux_prop_conc_limit_reciprocal_moment P R (fun om => Matrix.trace (A om))
    (ENNReal.ofReal q) (ENNReal.ofReal (Cq / d)) hRmeas hpositive hRlim hfiniteNorm

end
end SubdiffusiveProcess.Paper
