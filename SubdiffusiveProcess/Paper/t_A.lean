module

public import SubdiffusiveProcess.Paper.thm_A
public import SubdiffusiveProcess.Paper.inputs_simultaneous
public import SubdiffusiveProcess.Paper.thm_A_in_probability_paths

@[expose] public section

/-!
# Theorem A: diffusion and its scaling limit

The environment is a bilateral field with the product law `commonScaleLaw`, obtained
from the layer law of a given `GMCModel d`, with `d ≥ 2` and sufficiently small positive
disorder. Paths belong to `DiffusionPath d`, the continuous maps from nonnegative time
to `SpatialCoordinates d`, with the compact-open topology. Their probability laws are
represented by Markov kernels indexed by the environment and starting point.

The theorem gives conservative cutoff and limiting semigroups, convergence of path
laws uniformly over compact sets of starting points on a full-measure environment
set, and annealed convergence after the physical space and time rescaling. It also
gives limiting speed measures, reversibility, anomalous exit-time bounds, singularity
with Brownian path laws, and positive-time non-Gaussian transition laws.

Continuity in the starting point is extended to every environment by assigning
constant paths on a measurable null set. The analytic identifications hold almost
surely. The last Brownian-singularity and path-regularity assertions have the order
`∀ x, ∀ᵐ omega`: their null sets may depend on the starting point. The earlier
`∀ᵐ omega, ∀ x` clauses share one environment event. Neither order is interchanged.

The physical path is `3^(-N) X(T_N t)`, where
`T_N = ahom M 0 * 3^(2N) / ahom M N`. Spatial coordinates use the sup norm for
cube geometry; energy and dual norms are specified by their defining functions.
Existence of a model satisfying `GMCModel` is a standing assumption. Brownian-driver
SDE identification belongs to the paper and is not a conclusion of this theorem.
-/

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open MarkovProcess
open scoped CompactlySupported ENNReal NNReal LevyProkhorov
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The clock-scaling conclusion of `thm_A`, `T_m/T_ℓ ≥ C⁻¹ 3^{(2+η)(m-ℓ)}` with
`T_n = 3^{2n}/a_n`, in the form `a_m/a_ℓ ≤ C 3^{-η(m-ℓ)}` of the paper. -/
theorem aux_t_A_ahom_decay (a : ℕ → ℝ) (hpos : ∀ n, 0 < a n) (C eta : ℝ) (hC : 0 < C)
    (h : ∀ l m : ℕ, l ≤ m →
      C⁻¹ * (3 : ℝ) ^ ((2 + eta) * ((m : ℝ) - (l : ℝ))) ≤
        ((3 : ℝ) ^ (2 * m) / a m) / ((3 : ℝ) ^ (2 * l) / a l)) :
    ∀ l m : ℕ, l ≤ m → a m / a l ≤ C * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (l : ℝ)))) := by
  intro l m hlm
  have h1 := h l m hlm
  set s : ℝ := (m : ℝ) - (l : ℝ) with hs
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hal := hpos l
  have ham := hpos m
  have hpow : ((3 : ℝ) ^ (2 * m) / a m) / ((3 : ℝ) ^ (2 * l) / a l) =
      (3 : ℝ) ^ ((2 : ℝ) * s) * (a l / a m) := by
    have e1 : (3 : ℝ) ^ (2 * m) = (3 : ℝ) ^ ((2 : ℝ) * (m : ℝ)) := by
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    have e2 : (3 : ℝ) ^ (2 * l) = (3 : ℝ) ^ ((2 : ℝ) * (l : ℝ)) := by
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    have e3 : (3 : ℝ) ^ ((2 : ℝ) * s) = (3 : ℝ) ^ ((2 : ℝ) * (m : ℝ)) / (3 : ℝ) ^ ((2 : ℝ) * (l : ℝ)) := by
      rw [← Real.rpow_sub h3, hs]; ring_nf
    rw [e1, e2, e3]
    field_simp
  rw [hpow] at h1
  have hsplit : (3 : ℝ) ^ ((2 + eta) * s) = (3 : ℝ) ^ ((2 : ℝ) * s) * (3 : ℝ) ^ (eta * s) := by
    rw [show (2 + eta) * s = (2 : ℝ) * s + eta * s by ring, Real.rpow_add h3]
  have hp2 : (0 : ℝ) < (3 : ℝ) ^ ((2 : ℝ) * s) := Real.rpow_pos_of_pos h3 _
  have hpe : (0 : ℝ) < (3 : ℝ) ^ (eta * s) := Real.rpow_pos_of_pos h3 _
  have h2 : C⁻¹ * (3 : ℝ) ^ (eta * s) ≤ a l / a m := by
    rw [hsplit] at h1
    have : (3 : ℝ) ^ ((2 : ℝ) * s) * (C⁻¹ * (3 : ℝ) ^ (eta * s)) ≤
        (3 : ℝ) ^ ((2 : ℝ) * s) * (a l / a m) := by
      calc (3 : ℝ) ^ ((2 : ℝ) * s) * (C⁻¹ * (3 : ℝ) ^ (eta * s))
          = C⁻¹ * ((3 : ℝ) ^ ((2 : ℝ) * s) * (3 : ℝ) ^ (eta * s)) := by ring
        _ ≤ _ := h1
    exact le_of_mul_le_mul_left this hp2
  have hq : 0 < C⁻¹ * (3 : ℝ) ^ (eta * s) := mul_pos (inv_pos.mpr hC) hpe
  have h4 : (a l / a m)⁻¹ ≤ (C⁻¹ * (3 : ℝ) ^ (eta * s))⁻¹ := inv_anti₀ hq h2
  rw [inv_div] at h4
  calc a m / a l ≤ (C⁻¹ * (3 : ℝ) ^ (eta * s))⁻¹ := h4
    _ = C * (3 : ℝ) ^ (-(eta * s)) := by
      rw [mul_inv, inv_inv, Real.rpow_neg h3.le]

/-- Theorem A, conditional on a `GMCModel d` with sufficiently small disorder.
The cutoff and limit kernels give continuous path laws, local convergence of speed
measures, reversibility and anomalous scaling. The physical clock is
`ahom M 0 * 3^(2N) / ahom M N`. Continuity for every environment uses a constant-path
version on a measurable null set; resolvent and process identifications remain
almost sure. Its repetition inside the full-measure block keeps that block usable
as one conjunction. The final `∀ x, ∀ᵐ omega` assertions permit a starting-point
dependent exceptional set. -/
theorem t_A
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d),
        0 < M.delta → M.delta ≤ delta0 →
        let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
            C(SpatialCoordinates d, ℝ)) :=
          ⟨fun g ↦ g.1.1, continuous_subtype_val.fst⟩
        let nu := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).map
          forget
        let law := (commonScaleLaw d nu).toMeasure
        ∃ C eta : ℝ, 1 ≤ C ∧ 0 < eta ∧
        (d = 2 → eta = _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3) ∧
        (∀ l m : ℕ, l ≤ m →
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M m / SubdiffusiveProcess.CoarseGrainingVocab.ahom M l ≤
            C * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (l : ℝ))))) ∧
        ∃ H : BilateralField d → C(SpatialCoordinates d, ℝ), Measurable H ∧
        ∃ PN : ℕ → BilateralField d →
            SubMarkovKernelSemigroup (SpatialCoordinates d),
        ∃ _hPN : ∀ N omega, (PN N omega).IsConservative,
        ∃ P : BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d),
        ∃ _hP : ∀ omega, (P omega).IsConservative,
        ∃ KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d),
        ∃ hKN : ∀ N, IsMarkovKernel (KN N),
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
            Continuous (fun x ↦ jointPathProbabilityMeasure K hK omega x) ∧
            (∀ B : Set (SpatialCoordinates d), IsCompact B →
              ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, ∀ N, N0 ≤ N →
                ∀ x ∈ B,
                  pathLevyProkhorovDist
                    (jointPathProbabilityMeasure (KN N) (hKN N) omega x)
                    (jointPathProbabilityMeasure K hK omega x) < epsilon) ∧
            (∀ (t : ℝ≥0) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ),
              Continuous (kernelIntegral (P omega t) f)) ∧
            (∃ mu : Measure (SpatialCoordinates d),
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu ∧
              IsLocallyFiniteMeasure mu ∧ NullSingletonClass mu ∧ mu.IsOpenPosMeasure ∧
              SemigroupSymmetric (P omega) mu) ∧
            HasStrongMarkovRestart K omega ∧ HasFiniteMeanExits K omega) ∧
          (∀ (x : SpatialCoordinates d) (F : BoundedContinuousFunction (DiffusionPath d) ℝ),
            Tendsto
              (fun N ↦ ∫ omega,
                (∫ path, F (physicalRescaledPath M N path)
                  ∂(KN 0 (omega, (3 : ℝ) ^ N • x))) ∂law)
              atTop
              (nhds (∫ omega, (∫ path, F path ∂(K (omega, x))) ∂law))) ∧
          -- (ii) the limiting measures `M = lim M_N` and `μ = e^H M`, reversibility's invariance
          (∃ Mlim : BilateralField d → Measure (SpatialCoordinates d), Measurable Mlim ∧
            (∀ᵐ omega ∂law,
              let mu := (Mlim omega).withDensity
                (fun y ↦ ENNReal.ofReal (Real.exp (H omega y)))
              MeasuresConvergeLocally (fun N ↦ chaosCutoff M N omega) (Mlim omega) ∧
              MeasuresConvergeLocally (fun N ↦ cutoffSpeedMeasure M H omega N) mu ∧
              IsLocallyFiniteMeasure (Mlim omega) ∧ NullSingletonClass (Mlim omega) ∧
              (Mlim omega).IsOpenPosMeasure ∧ Mlim omega ⟂ₘ volume ∧
              IsLocallyFiniteMeasure mu ∧ NullSingletonClass mu ∧ mu.IsOpenPosMeasure ∧ mu ⟂ₘ volume ∧
              (∀ (t : ℝ≥0) (f : SpatialCoordinates d → ℝ≥0∞), Measurable f →
                ∫⁻ x, (∫⁻ w, f (w t) ∂(K (omega, x))) ∂mu = ∫⁻ x, f x ∂mu) ∧
              -- (iv) positive-time transition laws: absolutely continuous, non-Gaussian
              ∀ (x : SpatialCoordinates d) (t : ℝ≥0), 0 < t →
                (K (omega, x)).map (fun w : DiffusionPath d ↦ w t) ≪ mu ∧
                ¬ IsGaussian ((K (omega, x)).map (fun w : DiffusionPath d ↦ w t))) ∧
            (¬ ∃ m : Measure (SpatialCoordinates d), ∀ᵐ omega ∂law, Mlim omega = m) ∧
            (∀ A : Set (SpatialCoordinates d), MeasurableSet A →
              ∫⁻ omega, Mlim omega A ∂law = volume A) ∧
            ∀ y : SpatialCoordinates d,
              law.map (fun omega ↦ (Mlim omega).map (fun z ↦ z + y)) = law.map Mlim) ∧
          -- (iii) annealed small-cube exits, Brownian singularity, pointwise Hölder bound
          (∀ (x : SpatialCoordinates d) (k : ℕ),
            ∫⁻ omega, (∫⁻ w, ContinuousPath.exitTime
                (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w ∂(K (omega, x))) ∂law ≤
              ENNReal.ofReal (C * (3 : ℝ) ^ (-((2 + eta) * (k : ℝ))))) ∧
          ∀ x : SpatialCoordinates d, ∀ᵐ omega ∂law,
            (∀ Q : Measure (DiffusionPath d), lim_brownian_law Q → K (omega, x) ⟂ₘ Q) ∧
            (∀ (Θ : Type) [MeasurableSpace Θ] (nu' : Measure Θ) [IsProbabilityMeasure nu']
                (kappa : Kernel Θ (DiffusionPath d)), (∀ θ, lim_brownian_law (kappa θ)) →
              K (omega, x) ⟂ₘ nu'.bind kappa) ∧
            ∀ᵐ w ∂(K (omega, x)), ∀ gamma : ℝ, 0 ≤ gamma →
              (fun t : ℝ≥0 ↦ ‖w t - w 0‖) =O[𝓝[>] 0] (fun t : ℝ≥0 ↦ (t : ℝ) ^ gamma) →
              gamma ≤ 1 / (2 + eta) := by
  classical
  obtain ⟨Jc, Pc, Xc, Sf, W, Cp, D, hES, Step, Dbase, Interp, BD, BDQ, hcontract, hlife, EM,
    deltaI, Cresp, hdeltaI, hCresp, hmodels⟩ := inputs_simultaneous d hd
  obtain ⟨delta0, hdelta0, hmain⟩ :=
    thm_A d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp BD BDQ hcontract hlife
  refine ⟨min delta0 deltaI, lt_min hdelta0 hdeltaI, ?_⟩
  intro M hMpos hMle forget nu law
  obtain ⟨Rm, Sreg, hRm, ⟨It⟩⟩ := hmodels M hMpos (hMle.trans (min_le_right _ _))
  obtain ⟨C, eta, hC, heta, hd2, hclock, H, hHm, PN, hPN, P, hP, KN, hKN, K, hK, hA, hB, hMeas,
    hExit, hSing⟩ := hmain M Rm Sreg It hMpos (hMle.trans (min_le_left _ _))
  have hKeq0 : ∀ᵐ omega ∂law, ∀ x : SpatialCoordinates d,
      (jointPathProbabilityMeasure K hK omega x : Measure (DiffusionPath d)) = K (omega, x) :=
    Filter.Eventually.of_forall fun _ _ => rfl
  obtain ⟨K', hK', hcont, hKK'⟩ := aux_thm_A_in_probability_paths_everywhere law K hK
    (hA.mono fun omega h => h.2.2.2.2.1)
  have hKeq : ∀ᵐ omega ∂law, ∀ x : SpatialCoordinates d, K' (omega, x) = K (omega, x) := by
    filter_upwards [hKK'] with omega h x
    exact congrArg (fun P : ProbabilityMeasure (DiffusionPath d) => (P : Measure (DiffusionPath d)))
      (h x)
  refine ⟨C, eta, hC, heta, hd2, ?_, H, hHm, PN, hPN, P, hP, KN, hKN, K', hK', hcont,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact aux_t_A_ahom_decay (SubdiffusiveProcess.CoarseGrainingVocab.ahom M)
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M) C eta (lt_of_lt_of_le one_pos hC) hclock
  · filter_upwards [hA, hKK', hKeq] with omega hAω hKKω hE
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hAω
    refine ⟨c1, c2, c3, ?_, hcont omega, ?_, c7, c8, ?_, ?_⟩
    · intro I x
      rw [Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I), hE x,
        ← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I)]
      exact c4 I x
    · intro B hB eps heps
      obtain ⟨N0, hN0⟩ := c6 B hB eps heps
      refine ⟨N0, fun N hN x hx => ?_⟩
      rw [hKKω x]
      exact hN0 N hN x hx
    · simpa only [HasStrongMarkovRestart, hE] using c9
    · simpa only [HasFiniteMeanExits, hE] using c10
  · intro x F
    have h := hB x F
    have hint : (∫ omega, (∫ path, F path ∂(K' (omega, x))) ∂law) =
        ∫ omega, (∫ path, F path ∂(K (omega, x))) ∂law := by
      refine integral_congr_ae ?_
      filter_upwards [hKeq] with omega hE
      rw [hE x]
    rw [hint]
    exact h
  · obtain ⟨Mlim, hMlim, hC1, hnondet, hmean, hstat⟩ := hMeas
    refine ⟨Mlim, hMlim, ?_, hnondet, hmean, hstat⟩
    filter_upwards [hC1, hKeq] with omega h hE
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ := h
    refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, ?_, ?_⟩
    · intro t f hf
      have := c11 t f hf
      simpa only [hE] using this
    · intro x t ht
      have := c12 x t ht
      simpa only [hE] using this
  · intro x k
    have h := hExit x k
    have hint : (∫⁻ omega, (∫⁻ w, ContinuousPath.exitTime
        (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w ∂(K' (omega, x))) ∂law) =
        ∫⁻ omega, (∫⁻ w, ContinuousPath.exitTime
        (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w ∂(K (omega, x))) ∂law := by
      refine lintegral_congr_ae ?_
      filter_upwards [hKeq] with omega hE
      rw [hE x]
    rw [hint]
    exact h
  · intro x
    filter_upwards [hSing x, hKeq] with omega h hE
    simpa only [hE x] using h

end SubdiffusiveProcess.Paper
