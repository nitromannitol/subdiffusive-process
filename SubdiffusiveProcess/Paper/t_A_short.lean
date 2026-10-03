module

public import SubdiffusiveProcess.Paper.t_A
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Order.LiminfLimsup

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics SubdiffusiveProcess MarkovProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- An unbounded nonnegative quotient has infinite extended limsup. -/
theorem aux_t_A_short_limsup (f : ℝ≥0 → ℝ) (hf : ∀ t, 0 ≤ f t) (gamma : ℝ)
    (h : ¬ (f =O[𝓝[>] 0] (fun t : ℝ≥0 ↦ (t : ℝ) ^ gamma))) :
    Filter.limsup (fun t : ℝ≥0 ↦ ENNReal.ofReal ((t : ℝ) ^ (-gamma) * f t))
      (𝓝[>] 0) = ∞ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro c
  apply le_limsup_of_frequently_le'
  have hfreq : ∃ᶠ t : ℝ≥0 in 𝓝[>] 0, (c : ℝ) < (t : ℝ) ^ (-gamma) * f t := by
    by_contra hn
    apply h
    apply Asymptotics.IsBigO.of_bound (c : ℝ)
    filter_upwards [not_frequently.mp hn, self_mem_nhdsWithin] with t ht htpos
    have htp : 0 < (t : ℝ) := htpos
    have hp : 0 ≤ (t : ℝ) ^ gamma := Real.rpow_nonneg t.coe_nonneg _
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt ht) hp
    have heq : (t : ℝ) ^ gamma * ((t : ℝ) ^ (-gamma) * f t) = f t := by
      rw [← mul_assoc, ← Real.rpow_add htp, add_neg_cancel, Real.rpow_zero, one_mul]
    rw [heq] at hm
    simpa only [Real.norm_of_nonneg (hf t), Real.norm_of_nonneg hp, mul_comm] using hm
  exact hfreq.mono fun t ht => by
    exact (show (c : ℝ≥0∞) = ENNReal.ofReal (c : ℝ) by simp only [ENNReal.ofReal_coe_nnreal]) ▸
      ENNReal.ofReal_le_ofReal ht.le

/-- Comparing an arbitrary side length with two successive triadic lengths. -/
theorem aux_t_A_short_scale (r alpha : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (ha : 0 ≤ alpha) :
    ∃ k : ℕ, r ≤ (3 : ℝ) ^ (-(k : ℤ)) ∧
      (3 : ℝ) ^ (-(alpha * (k : ℝ))) ≤ (3 : ℝ) ^ alpha * r ^ alpha := by
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hr hr1
    (by norm_num : 0 < (3 : ℝ)⁻¹) (by norm_num : (3 : ℝ)⁻¹ < 1)
  have heq : ∀ j : ℕ, (3 : ℝ)⁻¹ ^ j = (3 : ℝ) ^ (-(j : ℤ)) := by
    intro j
    rw [inv_pow, zpow_neg, zpow_natCast]
  refine ⟨k, by simpa only [heq] using hk2, ?_⟩
  have hkr : (3 : ℝ) ^ (-(k : ℤ)) ≤ 3 * r := by
    rw [← heq]
    have hm := mul_le_mul_of_nonneg_left hk1.le (by norm_num : (0 : ℝ) ≤ 3)
    rw [pow_succ] at hm
    norm_num at hm
    linarith
  have hm := Real.rpow_le_rpow (by positivity : 0 ≤ (3 : ℝ) ^ (-(k : ℤ))) hkr ha
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hr.le] at hm
  have he : ((3 : ℝ) ^ (-(k : ℤ))) ^ alpha = (3 : ℝ) ^ (-(alpha * (k : ℝ))) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    simp only [Int.cast_neg, Int.cast_natCast]
    ring
  rwa [he] at hm

/-- The short scaling-limit theorem, `t.A` in the introduction (lines 167–185).
The cutoff resolvent and finite-dimensional identities identify the analytic laws
used in the annealed convergence. Cubes are balls for the sup norm on `Fin d → ℝ`.
The nonnegative extended-real limsup expresses divergence to infinity. -/
theorem t_A_short
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        0 < M.delta → M.delta ≤ delta0 →
        let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ)) :=
          ⟨fun g ↦ g.1.1, continuous_subtype_val.fst⟩
        let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).map forget
        let law := (commonScaleLaw d nu).toMeasure
        ∃ C eta : ℝ, 0 < eta ∧
        (d = 2 → eta = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P / Real.log 3) ∧
        ∃ H : BilateralField d → C(SpatialCoordinates d, ℝ), Measurable H ∧
        ∃ PN : ℕ → BilateralField d →
            SubMarkovKernelSemigroup (SpatialCoordinates d),
        ∃ _hPN : ∀ N omega, (PN N omega).IsConservative,
        ∃ P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d),
        ∃ _hP : ∀ omega, (P omega).IsConservative,
        ∃ KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d),
        ∃ _hKN : ∀ N, IsMarkovKernel (KN N),
        ∃ K : Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d),
        ∃ hK : IsMarkovKernel K,
          (∀ omega : BilateralField d,
            Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x)) ∧
          (∀ᵐ omega ∂law,
            Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∧
            (∀ N, ∃ D :
                SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum
                  (SpatialCoordinates d),
              (∀ mu, DenseRange (D.operator mu)) ∧
              SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent
                (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) D ∧
              ∀ (mu : Semigroup.PositiveShift)
                (f : ZeroAtInftyContinuousMap (SpatialCoordinates d) ℝ)
                (x : SpatialCoordinates d),
                D.solution mu f x =
                  ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
                    kernelIntegral (PN N omega (Real.toNNReal t)) f x) ∧
            (∀ N I x,
              (KN N).map (ContinuousPath.finsetEvaluation I) (omega, x) =
                SubMarkovKernelSemigroup.finiteSetKernel (PN N omega) I x) ∧
            (∀ I x, K.map (ContinuousPath.finsetEvaluation I) (omega, x) =
              SubMarkovKernelSemigroup.finiteSetKernel (P omega) I x) ∧
            HasStrongMarkovRestart K omega) ∧
          -- (i) Annealed convergence of the physical rescaled process.
          (∀ (x : SpatialCoordinates d) (F : BoundedContinuousFunction (DiffusionPath d) ℝ),
            Tendsto
              (fun N ↦ ∫ omega,
                (∫ path, F (physicalRescaledPath M N path)
                  ∂(KN 0 (omega, (3 : ℝ) ^ N • x))) ∂law)
              atTop
              (nhds (∫ omega, (∫ path, F path ∂(K (omega, x))) ∂law))) ∧
          -- (ii), (iv) The same reversible singular measure governs the marginals.
          (∃ Mlim : BilateralField d → Measure (SpatialCoordinates d), Measurable Mlim ∧
            ∀ᵐ omega ∂law,
              let mu := (Mlim omega).withDensity
                (fun y ↦ ENNReal.ofReal (Real.exp (H omega y)))
              MeasuresConvergeLocally (fun N ↦ chaosCutoff M N omega) (Mlim omega) ∧
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu ∧
              IsLocallyFiniteMeasure (Mlim omega) ∧ IsLocallyFiniteMeasure mu ∧
              SemigroupSymmetric (P omega) mu ∧ mu ⟂ₘ volume ∧
              ∀ (x : SpatialCoordinates d) (t : ℝ≥0), 0 < t →
                (K (omega, x)).map (fun w : DiffusionPath d ↦ w t) ≪ mu ∧
                ¬ IsGaussian ((K (omega, x)).map (fun w : DiffusionPath d ↦ w t))) ∧
          -- (iii) Exit times for every side length in (0,1].
          (∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
            ∫⁻ omega, (∫⁻ w, ContinuousPath.exitTime
                (Metric.ball (w 0) (r / 2)) w ∂(K (omega, x))) ∂law ≤
              ENNReal.ofReal (C * r ^ (2 + eta))) ∧
          ∀ x : SpatialCoordinates d, ∀ᵐ omega ∂law,
            ∀ᵐ w ∂(K (omega, x)), ∀ gamma : ℝ, 1 / (2 + eta) < gamma →
              Filter.limsup
                (fun t : ℝ≥0 ↦ ENNReal.ofReal
                  ((t : ℝ) ^ (-gamma) * ‖w t - w 0‖)) (𝓝[>] 0) = ∞ := by
  classical
  obtain ⟨delta0, hdelta0, hmain⟩ := t_A d hd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hMpos hMle forget nu law
  obtain ⟨C, eta, hC, heta, hd2, _, H, hHm, PN, hPN, P, hP, KN, hKN, K, hK,
    hcont, hA, hB, hMeasures, hExit, hHolder⟩ :=
    hmain M hMpos hMle
  obtain ⟨Mlim, hMlim, hMeas, _, _, _⟩ := hMeasures
  refine ⟨(3 : ℝ) ^ (2 + eta) * C, eta, heta, hd2, H, hHm,
    PN, hPN, P, hP, KN, hKN, K, hK, hcont, ?_, hB, ?_, ?_, ?_⟩
  · filter_upwards [hA] with omega h
    obtain ⟨hH, hres, hKNlaw, hKlaw, _, _, _, _, hmarkov, _⟩ := h
    exact ⟨hH, hres, hKNlaw, hKlaw, hmarkov⟩
  · refine ⟨Mlim, hMlim, ?_⟩
    filter_upwards [hA, hMeas] with omega hAω hMω
    obtain ⟨hmu0, hmu, hloc0, _, _, _, hloc, _, _, hsing, _, hmarg⟩ := hMω
    obtain ⟨_, _, _, _, _, _, _, hReversible, _, _⟩ := hAω
    obtain ⟨mu', hmu', hloc', _, _, hsymm⟩ := hReversible
    letI := hloc
    letI := hloc'
    have heq : mu' = (Mlim omega).withDensity
        (fun y ↦ ENNReal.ofReal (Real.exp (H omega y))) := by
      apply Measure.ext_of_integral_eq_on_compactlySupported
      intro f
      exact tendsto_nhds_unique (hmu' f) (hmu f)
    exact ⟨hmu0, hmu, hloc0, hloc, heq ▸ hsymm, hsing, hmarg⟩
  · intro x r hr hr1
    have halpha : 0 ≤ 2 + eta := by linarith
    obtain ⟨k, hrk, hscale⟩ := aux_t_A_short_scale r (2 + eta) hr hr1 halpha
    calc
      (∫⁻ omega, (∫⁻ w, ContinuousPath.exitTime
          (Metric.ball (w 0) (r / 2)) w ∂(K (omega, x))) ∂law) ≤
          ∫⁻ omega, (∫⁻ w, ContinuousPath.exitTime
            (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w ∂(K (omega, x))) ∂law := by
              apply lintegral_mono
              intro omega
              apply lintegral_mono
              intro w
              exact ContinuousPath.exitTime_mono
                (Metric.ball_subset_ball (div_le_div_of_nonneg_right hrk (by norm_num))) w
      _ ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-((2 + eta) * (k : ℝ)))) := hExit x k
      _ ≤ ENNReal.ofReal (((3 : ℝ) ^ (2 + eta) * C) * r ^ (2 + eta)) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          C * (3 : ℝ) ^ (-((2 + eta) * (k : ℝ))) ≤
              C * ((3 : ℝ) ^ (2 + eta) * r ^ (2 + eta)) :=
            mul_le_mul_of_nonneg_left hscale (le_trans (by norm_num) hC)
          _ = _ := by ring
  · intro x
    filter_upwards [hHolder x] with omega h
    filter_upwards [h.2.2] with w hw
    intro gamma hgamma
    apply aux_t_A_short_limsup (fun t ↦ ‖w t - w 0‖) (fun t ↦ norm_nonneg _) gamma
    intro hO
    have hbound : 0 < 1 / (2 + eta) := by positivity
    exact (not_le_of_gt hgamma) (hw gamma (hbound.le.trans hgamma.le) hO)

end Paper
