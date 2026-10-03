module

public import SubdiffusiveProcess.Paper.represented_estimates_actual_model
public import SubdiffusiveProcess.Paper.Support.JointComparison
public import SubdiffusiveProcess.Paper.Support.OriginalComparison
public import SubdiffusiveProcess.Paper.conv_represented_root_family

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.Comparison
open scoped Topology ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- Paper-literal represented-pair export (review Q1). Constants precede the model and cutoff pair. -/
theorem aux_mfd_prop_density_represented
    (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_Step : Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ddet : Paper.lane4_deterministic_good_scale_input d)
    (Cp : Lane4.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (eta0 : ℝ) (heta0 : 0 < eta0) (heta03 : eta0 < 1 / 3)
    (D theta alpha eta : ℝ)
    (hD : 8 * (d : ℝ) / eta0 ≤ D)
    (htheta : 0 < theta) (htheta8 : theta ≤ eta0 / 8)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (heta : 0 < eta) (heta2 : eta < 2)
    (hexp : 2 * (1 - alpha) + eta < eta0 / 8)
    (H1 : ℕ) (hH1 : 0 < H1) (Cd : ℝ) (hCd : 6 * (d : ℝ) ≤ Cd)
    (t beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hbeta : 1 / 2 < beta) (hbetaAlpha : beta < alpha) :
    let L : ℝ := (3 : ℝ) ^ H1
    ∀ (hLlarge : 2 * Cd ^ (eta0 / 3) ≤ L ^ (eta0 / 3 - eta0 / 8))
      (hCdPad : ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
        (Nat.card {i : OddGridIndex d (subdivisionHalfWidth H1) //
          ¬ Metric.closedBall (oddGridCenter zP R (subdivisionHalfWidth H1) i)
              (3 * (R / L) / 2) ⊆
            (centeredCube zP R hR : Set (SpatialCoordinates d))} : ℝ) ≤
          Cd * L ^ ((d : ℝ) - 1)),
    ∃ delta0 Cstar : ℝ, 0 < delta0 ∧ 0 < Cstar ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization model H)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
        (hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, z i c = (q : ℝ)) ∧ ∃ m : ℤ, r i = (3 : ℝ) ^ m)
        (hfam : conv_represented_root_family d z r hr)
        (NE NF : ℕ → ℕ) (hNE : StrictMono NE) (hNF : StrictMono NF),
      ∃ seq : ℕ → ℕ, StrictMono seq ∧
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
          (field : Ω → BilateralField d) (env : ℕ → Ω → BilateralField d)
          (GNE GNF : (i : ℕ) → ℕ → Ω →
            DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
              DomainL2 (centeredCube (z i) (r i) (hr i)))
          (GE GF : (i : ℕ) → Ω →
            DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
              DomainL2 (centeredCube (z i) (r i) (hr i))),
          conv_represented_joint_grids d hd model H Ω P field env env z r hr Sspace
            GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) alpha eta I beta t ∧
          aux_conv_represented_env_interface_bounds d hd model H Ω P env env z r hr Sspace
            GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) ∧
      ∀ (eE eF : ℕ → ℝ), (∀ k, 0 < eE k ∧ 0 < eF k) →
      let kappa : ℕ → ℝ := fun N =>
        Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N
      (∀ k, Tendsto (fun j => kappa (NE j - k) / kappa (NE j)) atTop (nhds (eE k))) →
      (∀ k, Tendsto (fun j => kappa (NF j - k) / kappa (NF j)) atTop (nhds (eF k))) →
      ∀ (Sset : ℕ → Prop) (a : ℝ), 0 < a → eta0 ≤ upperDensity Sset →
        (∀ n, Sset n → eF (H1 * n) / eE (H1 * n) ≤ a) →
        ∀ᵐ omega ∂P, ∀ i : ℕ,
          limitFormDomain (GE i omega) ⊆ limitFormDomain (GF i omega) ∧
          ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
            u ∈ limitFormDomain (GE i omega) →
            (limitFormEnergy (GF i omega) u).toReal ≤
              Cstar * a * (limitFormEnergy (GE i omega) u).toReal := by
  classical
  intro L hLlarge hCdPad
  letI canonicalMeas : MeasurableSpace C(SpatialCoordinates d, ℝ) := borel _
  letI canonicalBorel : BorelSpace C(SpatialCoordinates d, ℝ) := ⟨rfl⟩
  have hAeta : 1 + eta < 2 * alpha := by linarith
  obtain ⟨_, _, hcharts⟩ := represented_estimates_actual_model d hd alpha eta beta t
    ht htd (by linarith) halpha1 heta hAeta hbeta hbetaAlpha
  obtain ⟨deltaB1, hdeltaB1, hB1⟩ := hcharts I
  obtain ⟨deltaCmp, Cstar, hdeltaCmp, hCstar, hCmp⟩ :=
    aux_mfd_prop_density_joint d hd I _X _Sob _Step _MeyersMorrey Pin Ddet Cp
    eta0 heta0 heta03 D theta alpha eta hD htheta htheta8 halpha halpha1
    heta heta2 hexp H1 hH1 Cd hCd t beta ht htd hbeta hbetaAlpha hLlarge hCdPad
  refine ⟨min deltaCmp deltaB1, Cstar, lt_min hdeltaCmp hdeltaB1, hCstar, ?_⟩
  intro measC borelC
  have heq : measC = canonicalMeas := borelC.measurable_eq
  subst measC
  intro model hmodel Rm Sreg It H hH z r hr Sspace hS hrat hfam NE NF hNE hNF
  obtain ⟨seq, hseq, Ω, measΩ, P, probP, field, env, GNE, GNF, GE, GF, hdata, hBounds⟩ :=
    (hB1 model (hmodel.trans (min_le_right _ _))).2 H hH z r hr Sspace hS hrat hfam
      NE NF hNE hNF
  letI : MeasurableSpace Ω := measΩ
  letI : IsProbabilityMeasure P := probP
  refine ⟨seq, hseq, Ω, measΩ, P, probP, field, env, GNE, GNF, GE, GF, hdata, hBounds, ?_⟩
  intro eE eF hpos kappa hE hF Sset a ha hdens hratio
  exact hCmp model (hmodel.trans (min_le_left _ _)) Rm Sreg It H Ω P field env env
    z r hr Sspace GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) hdata hBounds
    eE eF hpos (fun k => (hE k).comp hseq.tendsto_atTop)
    (fun k => (hF k).comp hseq.tendsto_atTop) Sset a ha hdens hratio

/-- Record-free original-space successor. The complete unbounded determining family follows from countably many rooted applications and intersection of their events. -/
theorem mfd_prop_density
    (d : ℕ) (hd : 2 ≤ d)
    [NeZero d]
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : Lane4.SobolevFoundationalInput d hd)
    (_Step : Paper.cutoff_good_scale_input d)
    (_MeyersMorrey : Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ddet : Paper.lane4_deterministic_good_scale_input d)
    (Cp : Lane4.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (eta0 : ℝ) (heta0 : 0 < eta0) (heta03 : eta0 < 1 / 3)
    (D theta alpha eta : ℝ)
    (hD : 8 * (d : ℝ) / eta0 ≤ D)
    (htheta : 0 < theta) (htheta8 : theta ≤ eta0 / 8)
    (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (heta : 0 < eta) (heta2 : eta < 2)
    (hexp : 2 * (1 - alpha) + eta < eta0 / 8)
    (H1 : ℕ) (hH1 : 0 < H1) (Cd : ℝ) (hCd : 6 * (d : ℝ) ≤ Cd)
    (t beta : ℝ) (ht : (d : ℝ) - 1 < t) (htd : t < (d : ℝ))
    (hbeta : 1 / 2 < beta) (hbetaAlpha : beta < alpha) :
    let L : ℝ := (3 : ℝ) ^ H1
    ∀ (hLlarge : 2 * Cd ^ (eta0 / 3) ≤ L ^ (eta0 / 3 - eta0 / 8))
      (hCdPad : ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
        (Nat.card {i : OddGridIndex d (subdivisionHalfWidth H1) //
          ¬ Metric.closedBall (oddGridCenter zP R (subdivisionHalfWidth H1) i)
              (3 * (R / L) / 2) ⊆
            (centeredCube zP R hR : Set (SpatialCoordinates d))} : ℝ) ≤
          Cd * L ^ ((d : ℝ) - 1)),
    ∃ delta0 Cstar : ℝ, 0 < delta0 ∧ 0 < Cstar ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (hH : InfraredCharacterization model H)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
        (hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, z i c = (q : ℝ)) ∧ ∃ m : ℤ, r i = (3 : ℝ) ^ m)
        (hfam : conv_represented_root_family d z r hr)
        (NE NF : ℕ → ℕ) (hNE : StrictMono NE) (hNF : StrictMono NF)
        (GE GF : (i : ℕ) → BilateralField d →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (hlimE : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ i,
          Tendsto (fun n => volumeResponseOperator (Sspace i)
            (Lane4.cutoffPositiveCoefficient model H omega (NE n) (z i) (hr i))) atTop (𝓝 (GE i omega)))
        (hlimF : ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ i,
          Tendsto (fun n => volumeResponseOperator (Sspace i)
            (Lane4.cutoffPositiveCoefficient model H omega (NF n) (z i) (hr i))) atTop (𝓝 (GF i omega))),
      ∀ (eE eF : ℕ → ℝ), (∀ k, 0 < eE k ∧ 0 < eF k) →
      let kappa : ℕ → ℝ := fun N =>
        Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom model N
      (∀ k, Tendsto (fun j => kappa (NE j - k) / kappa (NE j)) atTop (nhds (eE k))) →
      (∀ k, Tendsto (fun j => kappa (NF j - k) / kappa (NF j)) atTop (nhds (eF k))) →
      ∀ (Sset : ℕ → Prop) (a : ℝ), 0 < a → eta0 ≤ upperDensity Sset →
        (∀ n, Sset n → eF (H1 * n) / eE (H1 * n) ≤ a) →
        ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ i : ℕ,
          limitFormDomain (GE i omega) ⊆ limitFormDomain (GF i omega) ∧
          ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
            u ∈ limitFormDomain (GE i omega) →
            (limitFormEnergy (GF i omega) u).toReal ≤
              Cstar * a * (limitFormEnergy (GE i omega) u).toReal := by
  classical
  intro L hLlarge hCdPad
  obtain ⟨delta0, Cstar, hdelta0, hCstar, hrepresented⟩ :=
    aux_mfd_prop_density_represented d hd I _X _Sob _Step _MeyersMorrey Pin Ddet Cp Interp
    eta0 heta0 heta03 D theta alpha eta hD htheta htheta8 halpha halpha1
    heta heta2 hexp H1 hH1 Cd hCd t beta ht htd hbeta hbetaAlpha hLlarge hCdPad
  refine ⟨delta0, Cstar, hdelta0, hCstar, ?_⟩
  intro _ _ model hmodel Rm Sreg It H hH z r hr Sspace hS hrat hfam NE NF hNE hNF
    GE0 GF0 hlimE hlimF
    eE eF hpos kappa hE hF Sset a ha hdens hratio
  obtain ⟨seq, hseq, Ω, measΩ, P, probP, field, env, GNE, GNF, GE, GF,
      hdata, hBounds, hcomparison⟩ :=
    hrepresented model hmodel Rm Sreg It H hH z r hr Sspace hS hrat hfam NE NF hNE hNF
  letI : MeasurableSpace Ω := measΩ
  letI : IsProbabilityMeasure P := probP
  exact original_comparison_of_represented d model H hH z r hr Sspace NE NF seq hseq
    GE0 GF0 hlimE hlimF Ω P field env GNE GNF GE GF hdata.1
    (Cstar * a) (mul_pos hCstar ha)
    (hcomparison eE eF hpos hE hF Sset a ha hdens hratio)

end Paper


