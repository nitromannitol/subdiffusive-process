module

public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_zero_ir_factor_moment_rate
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_uniform_factor_envelope
public import SubdiffusiveProcess.Paper.reference_oscillation_moments
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set Metric SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **Uniform-in-cutoff H=0 shallow factor.** For `d,hd,q≥1,eta>0`, choose `B0>0`
and `delta0∈(0,1]` before `M,Rm,H`; assuming `InfraredCharacterization M H` and
`M.delta≤delta0`, the N-independent infrared-free factor

`G0 k ω x = Σ_{j<k} (ω (-j)) x`,
`osc0 k ω y = sup_{x,x'∈closedBall y (3*(3^-k/2))} |G0 k ω x-G0 k ω x'|`,
`D0 k ω y = exp(osc0 k ω y) * exp(2*tauSq M.P*k) *
             (exp(G0 k ω y-tauSq M.P*k)+exp(-(G0 k ω y-tauSq M.P*k)))`

at every actual descendant center `y=cubeCenter Q` has
`AEStronglyMeasurable (fun ω => D0 k ω y) P` and
`eLpNorm ... (ofReal q) P ≤ ofReal (B0*3^(eta*k))`. -/
theorem lem_as_coarse_shallow_grid_zero_ir_uniform_factor_moment_rate
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q eta : ℝ) (hq : 1 ≤ q) (heta : 0 < eta) :
    ∃ B0 delta0 : ℝ, 0 < B0 ∧ 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d),
        _root_.SubdiffusiveProcess.Paper.in_responses d M →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let G0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω x => ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let oscSet0 : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k ω y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k),
              v = |G0 k ω x - G0 k ω x'|}
        let osc0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω y => sSup (oscSet0 k ω y)
        let D0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k ω y => Real.exp (osc0 k ω y) * Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)) *
            (Real.exp (G0 k ω y - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) +
              Real.exp (-(G0 k ω y - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)))
        ∀ (k : ℕ) (Q : TriadicCube d),
          Q ∈ descendantsAtScale (originCube d 0) (-(k : ℤ)) →
          AEStronglyMeasurable (fun ω => D0 k ω (cubeCenter Q))
            (chaosSampleLaw M).toMeasure ∧
          eLpNorm (fun ω => D0 k ω (cubeCenter Q))
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (B0 * (3 : ℝ) ^ (eta * (k : ℝ))) := by
  -- Obtain B0, delta0 from the H=0 moment rate lemma with half rate
  obtain ⟨B0, delta0, hB0, hd0, hd01, hFull⟩ :=
    lem_as_coarse_shallow_grid_zero_ir_factor_moment_rate d hd q (eta / 2) hq
      (by positivity)
  -- Take min with eta/4 for the absorb lemma
  have hd0_eta4 : 0 < min delta0 (eta / 4) := lt_min hd0 (by positivity)
  have hd01_min : min delta0 (eta / 4) ≤ 1 := (min_le_left _ _).trans hd01
  refine ⟨B0, min delta0 (eta / 4), hB0, hd0_eta4, hd01_min, ?_⟩
  intro M Rm H hH hMd G0 R oscSet0 osc0 D0 k Q hQ
  have hMd0 : M.delta ≤ delta0 := hMd.trans (min_le_left _ _)
  have hMd_eta4 : M.delta ≤ eta / 4 := hMd.trans (min_le_right _ _)
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hXk := hFull M Rm H hH hMd0 k k le_rfl Q hQ
  have hdom := aux_lem_as_coarse_shallow_grid_uniform_factor_dominates d M Rm (fun _ => 0)
  have hmeas_osc : Measurable (fun ω => osc0 k ω (cubeCenter Q)) := by
    -- Replicate the measurability proof from lem_as_coarse_shallow_grid_zero_ir_factor_measurable
    let r : ℝ := 3 * R k
    have hr : 0 < r := by
      dsimp [r, R]
      positivity
    have hUopen : IsOpen (Metric.ball (cubeCenter Q) r ×ˢ Metric.ball (cubeCenter Q) r) :=
      isOpen_ball.prod isOpen_ball
    let U : Set (SpatialCoordinates d × SpatialCoordinates d) :=
      Metric.ball (cubeCenter Q) r ×ˢ Metric.ball (cubeCenter Q) r
    let Kpair : Set (SpatialCoordinates d × SpatialCoordinates d) :=
      Metric.closedBall (cubeCenter Q) r ×ˢ Metric.closedBall (cubeCenter Q) r
    have hUsub : U ⊆ Kpair := by
      intro z hz
      exact ⟨mem_ball.mp hz.1 |>.le, mem_ball.mp hz.2 |>.le⟩
    have hKsub : Kpair ⊆ closure U := by
      intro z hz
      change z ∈ closure (Metric.ball (cubeCenter Q) r ×ˢ Metric.ball (cubeCenter Q) r)
      rw [closure_prod_eq, closure_ball (cubeCenter Q) hr.ne']
      exact ⟨hz.1, hz.2⟩
    have hKne : Kpair.Nonempty := by
      exact ⟨(cubeCenter Q, cubeCenter Q), ⟨Metric.mem_closedBall_self hr.le,
        Metric.mem_closedBall_self hr.le⟩⟩
    let F : BilateralField d → SpatialCoordinates d × SpatialCoordinates d → ℝ :=
      fun ω z => |G0 k ω z.1 - G0 k ω z.2|
    have hFcont : ∀ ω, Continuous (F ω) := by
      intro ω
      have hsum : Continuous (fun x : SpatialCoordinates d =>
          ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) x) :=
        continuous_finsetSum (Finset.range k) (fun j _ => (ω (-(j : ℤ))).continuous)
      exact continuous_abs.comp ((hsum.comp continuous_fst).sub (hsum.comp continuous_snd))
    have hFmeas : ∀ z : SpatialCoordinates d × SpatialCoordinates d,
        Measurable (fun ω => F ω z) := by
      intro z
      have hsum1 : Measurable (fun ω : BilateralField d =>
          ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) z.1) := by
        refine Finset.measurable_sum (Finset.range k) (fun j hj => ?_)
        have heval : Measurable (fun ω : BilateralField d => ω (-(j : ℤ))) := measurable_pi_apply _
        simpa only [Function.comp_apply] using!
          ((continuous_eval_const z.1).measurable.comp heval)
      have hsum2 : Measurable (fun ω : BilateralField d =>
          ∑ j ∈ Finset.range k, (ω (-(j : ℤ))) z.2) := by
        refine Finset.measurable_sum (Finset.range k) (fun j hj => ?_)
        have heval : Measurable (fun ω : BilateralField d => ω (-(j : ℤ))) := measurable_pi_apply _
        simpa only [Function.comp_apply] using!
          ((continuous_eval_const z.2).measurable.comp heval)
      have hsub : Measurable (fun ω => G0 k ω z.1 - G0 k ω z.2) := by
        dsimp [G0]
        exact (hsum1).sub (hsum2)
      exact measurable_abs.comp hsub
    have hAbdd : ∀ ω, BddAbove {v : ℝ | ∃ z ∈ Kpair, v = F ω z} := by
      intro ω
      have hcompact : IsCompact Kpair := by
        dsimp [Kpair]
        exact (isCompact_closedBall (cubeCenter Q) r).prod
          (isCompact_closedBall (cubeCenter Q) r)
      have himage := hcompact.bddAbove_image (hFcont ω).continuousOn
      apply himage.mono
      rintro v ⟨z, hz, rfl⟩
      exact ⟨z, hz, rfl⟩
    have hSupOpen : Measurable (fun ω =>
        sSup {v : ℝ | ∃ z ∈ U, v = F ω z}) :=
      aux_reference_oscillation_moments_measurable_sup_open
        hUopen hFcont hFmeas (by
          intro ω
          have himage := hAbdd ω
          exact himage.mono (by
            rintro v ⟨z, hz, rfl⟩
            exact ⟨z, hUsub hz, rfl⟩))
    have hSupMeas : Measurable (fun ω =>
        sSup {v : ℝ | ∃ x ∈ Metric.closedBall (cubeCenter Q) r,
          ∃ x' ∈ Metric.closedBall (cubeCenter Q) r, v = F ω (x, x')}) := by
      have heq : (fun ω => sSup {v : ℝ | ∃ x ∈ Metric.closedBall (cubeCenter Q) r,
          ∃ x' ∈ Metric.closedBall (cubeCenter Q) r, v = F ω (x, x')}) =
          (fun ω => sSup {v : ℝ | ∃ z ∈ U, v = F ω z}) := by
        funext ω
        calc
          sSup {v : ℝ | ∃ x ∈ Metric.closedBall (cubeCenter Q) r,
              ∃ x' ∈ Metric.closedBall (cubeCenter Q) r, v = F ω (x, x')} =
              sSup {v : ℝ | ∃ z ∈ Kpair, v = F ω z} := by
            apply congrArg sSup
            ext v
            constructor
            · rintro ⟨x, hx, x', hx', hv⟩
              exact ⟨(x, x'), ⟨hx, hx'⟩, hv⟩
            · rintro ⟨z, hz, hv⟩
              exact ⟨z.1, hz.1, z.2, hz.2, hv⟩
          _ = sSup {v : ℝ | ∃ z ∈ U, v = F ω z} :=
            aux_reference_oscillation_moments_sup_closed_eq_sup_open
              hUsub hKsub hKne (hFcont ω) (hAbdd ω)
      rw [heq]
      exact hSupOpen
    have hOscMeas : Measurable (fun ω => osc0 k ω (cubeCenter Q)) := by
      have : (fun ω => sSup {v : ℝ | ∃ x ∈ Metric.closedBall (cubeCenter Q) r,
          ∃ x' ∈ Metric.closedBall (cubeCenter Q) r, v = |G0 k ω x - G0 k ω x'|}) =
          (fun ω => sSup {v : ℝ | ∃ x ∈ Metric.closedBall (cubeCenter Q) r,
            ∃ x' ∈ Metric.closedBall (cubeCenter Q) r, v = F ω (x, x')}) := by
        funext ω
        simp [F]
      have hmeas : Measurable (fun ω => sSup {v : ℝ | ∃ x ∈ Metric.closedBall (cubeCenter Q) r,
          ∃ x' ∈ Metric.closedBall (cubeCenter Q) r, v = |G0 k ω x - G0 k ω x'|}) := by
        rw [this]
        exact hSupMeas
      simpa [osc0, oscSet0, r] using hmeas
    exact hOscMeas
  have hmeas_G0 : Measurable (fun ω => G0 k ω (cubeCenter Q)) := by
    dsimp [G0]
    refine Finset.measurable_sum (Finset.range k) (fun j _ => ?_)
    have heval : Measurable (fun (ω : BilateralField d) => ω (-(j : ℤ))) := measurable_pi_apply _
    exact ((continuous_eval_const (cubeCenter Q)).measurable.comp heval)
  have hmeas_D0 : AEStronglyMeasurable (fun ω => D0 k ω (cubeCenter Q))
      (chaosSampleLaw M).toMeasure := by
    dsimp [D0]
    have hshift : Measurable (fun ω => G0 k ω (cubeCenter Q) -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) :=
      hmeas_G0.sub measurable_const
    exact ((hmeas_osc.exp.mul measurable_const).mul
      (hshift.exp.add hshift.neg.exp)).aestronglyMeasurable
  refine ⟨hmeas_D0, ?_⟩
  have hc0 : 0 ≤ Real.exp (4 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)) :=
    (Real.exp_pos _).le
  have hbound := aux_lem_as_coarse_shallow_grid_uniform_factor_eLpNorm_le
    (chaosSampleLaw M).toMeasure (ENNReal.ofReal q)
    (fun ω => D0 k ω (cubeCenter Q)) _ _ _ hc0
    (fun ω => by
      have h := hdom k k le_rfl ω (cubeCenter Q)
      simpa only [ContinuousMap.zero_apply, zero_add, D0, G0, R, oscSet0, osc0,
        mul_assoc] using h.1.trans h.2.1)
    (fun ω => by
      have h := hdom k k le_rfl ω (cubeCenter Q)
      simpa only [ContinuousMap.zero_apply, zero_add, D0, G0, R, oscSet0, osc0,
        mul_assoc] using h.2.2) hXk
  rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hmeas_D0] at hbound
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  have habsorb := aux_lem_as_coarse_shallow_grid_uniform_factor_absorb
    (_root_.SubdiffusiveProcess.Model.tauSq M.P) M.delta eta k
    (SubdiffusiveProcess.CoarseGrainingVocab.tauSq_le_delta_sq M) hdelta (hMd0.trans hd01) hMd_eta4
  have hY0 : 0 ≤ (3 : ℝ) ^ (eta / 2 * (k : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hsplit : (3 : ℝ) ^ (eta * (k : ℝ)) =
      (3 : ℝ) ^ (eta / 2 * (k : ℝ)) * (3 : ℝ) ^ (eta / 2 * (k : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [hsplit]
  calc
    Real.exp (4 * _root_.SubdiffusiveProcess.Model.tauSq M.P * (k : ℝ)) *
        (B0 * (3 : ℝ) ^ (eta / 2 * (k : ℝ))) ≤
      (3 : ℝ) ^ (eta / 2 * (k : ℝ)) * (B0 * (3 : ℝ) ^ (eta / 2 * (k : ℝ))) :=
        mul_le_mul_of_nonneg_right habsorb (mul_nonneg hB0.le hY0)
    _ = B0 * ((3 : ℝ) ^ (eta / 2 * (k : ℝ)) * (3 : ℝ) ^ (eta / 2 * (k : ℝ))) := by ring
end SubdiffusiveProcess.Paper

