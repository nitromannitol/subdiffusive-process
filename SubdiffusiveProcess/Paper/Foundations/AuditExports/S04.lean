module

public import SubdiffusiveProcess.Paper.thm_A
public import SubdiffusiveProcess.Paper.inputs_simultaneous
public import SubdiffusiveProcess.Paper.lim_thm_nongaussian

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open MarkovProcess SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity _root_.SubdiffusiveProcess.Paper
open scoped CompactlySupported ENNReal NNReal LevyProkhorov

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- Theorem A with every non-Gaussian clause on its same common kernel.
All construction packages are supplied internally. The extra clauses quantify over
any local limit of the actual speed measures, so they apply to exactly A's weighted
measure and do not introduce a second unrelated limit object. -/
theorem theoremA_nongaussian
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
 :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
        0 < M.delta → M.delta ≤ delta0 →
        let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
            C(SpatialCoordinates d, ℝ)) :=
          ⟨fun g ↦ g.1.1, continuous_subtype_val.fst⟩
        let nu := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).map forget
        let law := (commonScaleLaw d nu).toMeasure
        ∃ C eta : ℝ, 1 ≤ C ∧ 0 < eta ∧
        (d = 2 → eta = _root_.SubdiffusiveProcess.Model.tauSq M.P / Real.log 3) ∧
        (∀ l m : ℕ, l ≤ m →
          C⁻¹ * (3 : ℝ) ^ ((2 + eta) * ((m : ℝ) - (l : ℝ))) ≤
            ((3 : ℝ) ^ (2 * m) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M m) /
              ((3 : ℝ) ^ (2 * l) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M l)) ∧
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
          (∀ᵐ omega ∂law, ∀ mu : Measure (SpatialCoordinates d),
            MeasuresConvergeLocally (fun N => cutoffSpeedMeasure M H omega N) mu →
          (∀ x : SpatialCoordinates d, ∀ t : ℝ≥0, 0 < t →
            (K (omega, x)).map (fun w : DiffusionPath d => w t) ≪ mu ∧
            (K (omega, x)).map (fun w : DiffusionPath d => w t) ⟂ₘ
              (volume : Measure (SpatialCoordinates d)) ∧
            ∀ gamma : Measure (SpatialCoordinates d), IsGaussian gamma →
              (K (omega, x)).map (fun w : DiffusionPath d => w t) ⟂ₘ gamma) ∧
          (∀ U : Set (SpatialCoordinates d), IsOpen U → Bornology.IsBounded U →
            ∃ CU : ℝ, 0 < CU ∧ ∀ x ∈ U, ∀ t : ℝ≥0, 0 < t →
              ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
                K (omega, x) {w | w t ∈ A ∧ (t : ℝ≥0∞) < ContinuousPath.exitTime U w} ≤
                  ENNReal.ofReal (CU * (t : ℝ) ^ (-(d : ℝ))) * mu.restrict U A) ∧
          (∀ (x : SpatialCoordinates d) (n : ℕ), 0 < n →
            ∀ times : Fin n → ℝ≥0, (∀ i, 0 < times i) →
            ∀ gamma : Measure (Fin n → SpatialCoordinates d), IsGaussian gamma →
              (K (omega, x)).map (fun w : DiffusionPath d => fun i => w (times i)) ⟂ₘ gamma) ∧
          ∀ (x : SpatialCoordinates d) (s t : ℝ≥0), s < t →
            letI : MeasurableSpace C(Set.Icc s t, SpatialCoordinates d) :=
              borel C(Set.Icc s t, SpatialCoordinates d)
            ∀ Q : Measure C(Set.Icc s t, SpatialCoordinates d),
              (IsProbabilityMeasure Q ∧ ∀ (n : ℕ) (times : Fin n → Set.Icc s t),
                IsGaussian (Q.map (fun w => fun i => w (times i)))) →
              (K (omega, x)).map (fun w : DiffusionPath d => w.restrict (Set.Icc s t)) ⟂ₘ Q) ∧

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
  obtain ⟨Jc, Pc, Xc, Sf, W, Cp, D, hES, Step, Dbase, Interp, BD, BDQ,
    hcontract, hlife, _, _, _, _, _⟩ := inputs_simultaneous d hd
  obtain ⟨δA, hδA, hA⟩ := thm_A d hd Jc Pc Xc Sf W Cp D hES Step Dbase Interp BD BDQ
    hcontract hlife
  obtain ⟨δNG, hδNG, hNG⟩ := lim_thm_nongaussian hd
  obtain ⟨Cresp, δR, _, hδR, hR⟩ := inputs_responses_witness d hd 1 le_rfl
  refine ⟨min δA (min δNG δR), lt_min hδA (lt_min hδNG hδR), ?_⟩
  intro M hMpos hM forget nu law
  obtain ⟨Rm, _, _⟩ := hR M (hM.trans ((min_le_right _ _).trans (min_le_right _ _)))
  let Sreg := inputs_regularity_witness d M
  let It := inputs_iteration_witness d hd M Jc
  obtain ⟨C, eta, hC, heta, hd2, hdec, H, hHmeas, PN, hPN, P, hP, KN, hKN, K, hK, hAout⟩ :=
    hA M Rm Sreg It hMpos (hM.trans (min_le_left _ _))
  have hIR : InfraredCharacterization M H := ⟨hHmeas, hAout.1.mono (fun _ hw => hw.1)⟩
  have hin : in_crossing M H PN KN :=
    ⟨hAout.1.mono (fun _ hw => hw.2.1), hPN,
      hAout.1.mono (fun _ hw => hw.2.2.1)⟩
  have hconv : aux_lim_thm_nongaussian_QuenchedConv M KN hKN K hK :=
    hAout.1.mono (fun _ hw => hw.2.2.2.2.2.1)
  obtain ⟨muNG, _, hng⟩ := hNG M
    (hM.trans ((min_le_right _ _).trans (min_le_left _ _))) H hIR PN KN hKN hin K hK hconv
  obtain ⟨Mlim, _, hmeasure, _⟩ := hAout.2.2.1
  refine ⟨C, eta, hC, heta, hd2, hdec, H, hHmeas, PN, hPN, P, hP, KN, hKN, K, hK,
    ?_, hAout⟩
  filter_upwards [hng, hmeasure] with omega hng hm
  let muA := (Mlim omega).withDensity (fun y => ENNReal.ofReal (Real.exp (H omega y)))
  let : IsLocallyFiniteMeasure muA := hm.2.2.2.2.2.2.1
  let : muA.IsOpenPosMeasure := hm.2.2.2.2.2.2.2.2.1
  have heq : muNG omega = muA := aux_lim_transition_domination_vague_identification
    (fun N => cutoffSpeedMeasure M H omega N) muA (muNG omega) hm.2.1 hng.1
  intro mu hmu
  have heq' : mu = muA := aux_lim_transition_domination_vague_identification
    (fun N => cutoffSpeedMeasure M H omega N) muA mu hm.2.1 hmu
  rw [← heq] at heq'
  subst mu
  exact hng.2

end SubdiffusiveProcess.AuditExports
