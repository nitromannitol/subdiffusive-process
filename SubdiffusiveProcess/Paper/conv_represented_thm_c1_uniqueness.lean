module

public import SubdiffusiveProcess.Paper.conv_represented_env_interface
public import SubdiffusiveProcess.Paper.conv_represented_thm_c1_hyp
public import SubdiffusiveProcess.Paper.conv_represented_limit_transfer
public import SubdiffusiveProcess.Lnorm.CutoffVolumeResponseMeasurability

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped Topology ENNReal NNReal InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



theorem conv_represented_thm_c1_uniqueness
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization model H)
    (alpha eta : ℝ)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (S : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (hS : ∀ i, (S i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (Dop : (i : ℕ) → Set (DomainL2 (centeredCube (z i) (r i) (hr i))))
    [hDcount : ∀ i, Countable (Dop i)]
    (hDdense : ∀ i, Dense (Dop i))
    (hDadd : ∀ i, ∀ x ∈ Dop i, ∀ y ∈ Dop i, x + y ∈ Dop i)
    (NE NF : ℕ → ℕ) (hNE : StrictMono NE) (hNF : StrictMono NF)
    (Kc : ℕ → ℕ → BilateralField d → ℝ)
    (hKcmeas : ∀ i N, Measurable (Kc i N))
    (hKcnonneg : ∀ i N β, 0 ≤ Kc i N β)
    (hcoer : ∀ i N, ∀ᵐ β ∂(chaosSampleLaw model).toMeasure,
      ∀ v : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
        cubeFractionalL2Seminorm hd (z i) (r i) (hr i) threeQuarterOrder
            (fun _ : Fin 1 => (v : SobolevData (centeredCube (z i) (r i) (hr i))).1) < ⊤ ∧
        cubeFractionalSqNorm hd (z i) (r i) (hr i) threeQuarterOrder
            (v : SobolevData (centeredCube (z i) (r i) (hr i))).1 ≤
          Kc i N β *
            sobolevCoefficientForm
              (Lane4.cutoffPositiveCoefficient model H β N (z i) (hr i))
              (v : SobolevData (centeredCube (z i) (r i) (hr i)))
              (v : SobolevData (centeredCube (z i) (r i) (hr i))))
    (htightK : ∀ i, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      (chaosSampleLaw model).toMeasure {β | Mb < Kc i (NE n) β} ≤ ENNReal.ofReal rho ∧
      (chaosSampleLaw model).toMeasure {β | Mb < Kc i (NF n) β} ≤ ENNReal.ofReal rho)
    (hdata : ∀ k : ℕ, ∃ e : ℕ → ℕ, (∀ i ≤ k, ∃ j, e j = i) ∧
      aux_conv_represented_env_interface_orig d hd model H (z ∘ e) (r ∘ e)
        (fun j => hr (e j)) (fun j => S (e j)) NE NF alpha eta)
    (GE0 GF0 : (i : ℕ) → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)))
    (hlimE : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => volumeResponseOperator (S i)
        (Lane4.cutoffPositiveCoefficient model H β (NE n) (z i) (hr i))) atTop (𝓝 (GE0 i β)))
    (hlimF : ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i,
      Tendsto (fun n => volumeResponseOperator (S i)
        (Lane4.cutoffPositiveCoefficient model H β (NF n) (z i) (hr i))) atTop (𝓝 (GF0 i β)))
    (hUniq : ∀ (Ωh : Type) [MeasurableSpace Ωh] (Ph : Measure Ωh) [IsProbabilityMeasure Ph]
        (field : Ωh → BilateralField d) (env : ℕ → Ωh → BilateralField d)
        (GNE GNF : (i : ℕ) → ℕ → Ωh →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ωh →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE' NF' : ℕ → ℕ),
      conv_represented_env_interface d hd model H Ωh Ph field env env z r hr S
        GNE GNF GE GF NE' NF' alpha eta →
      ∀ᵐ w ∂Ph, ∀ i, GE i w = GF i w) :
    ∀ᵐ β ∂(chaosSampleLaw model).toMeasure, ∀ i, GE0 i β = GF0 i β := by
  classical
  haveI : PolishSpace (BilateralField d) := aux_conv_represented_model_operators_polish d
  let P0 : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
  obtain ⟨seq, hseq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF, hI⟩ :=
    conv_represented_thm_c1_hyp d hd hInterp model H hH alpha eta z r hr S hS Dop hDdense hDadd
      NE NF hNE hNF Kc hKcmeas hKcnonneg hcoer htightK hdata
  haveI : IsProbabilityMeasure Ph := hPh
  have hEF := hUniq Ωh Ph field env GNE GNF GE GF _ _ hI
  obtain ⟨-, hfm, hfmap, -, -, -, hMP, henvc, -, hGNd, hGNc⟩ := hI.1
  have hmpLim : MeasurePreserving field Ph P0 := ⟨hfm, hfmap⟩
  have hΦmeas : ∀ i N, StronglyMeasurable (fun β => volumeResponseOperator (S i)
      (Lane4.cutoffPositiveCoefficient model H β N (z i) (hr i))) := fun i N =>
    stronglyMeasurable_cutoffVolumeResponseOperator model H hH.1 N (z i) (r i) (hr i) (S i)
  have hper : ∀ i, ∀ᵐ β ∂P0, GE0 i β = GF0 i β := by
    intro i
    let Nb : Bool → ℕ → ℕ := fun b n => cond b (NE (seq n)) (NF (seq n))
    let T : Bool → ℕ → BilateralField d →
        DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)) :=
      fun b n β => volumeResponseOperator (S i)
        (Lane4.cutoffPositiveCoefficient model H β (Nb b n) (z i) (hr i))
    let L0 : Bool → BilateralField d → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)) := fun b β => cond b (GE0 i β) (GF0 i β)
    let Lh : Bool → Ωh → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)) := fun b w => cond b (GE i w) (GF i w)
    have hsym : ∀ b n β x y, ⟪T b n β x, y⟫_ℝ = ⟪x, T b n β y⟫_ℝ := by
      intro b n β x y
      rw [real_inner_comm]
      exact volumeResponseOperator_symm (S i) _ y x
    have hmeas : ∀ b n, ∀ x ∈ Dop i, Measurable (fun β => ⟪x, T b n β x⟫_ℝ) := by
      intro b n x hx
      have hc : Continuous (fun A : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
          DomainL2 (centeredCube (z i) (r i) (hr i)) => ⟪x, A x⟫_ℝ) :=
        continuous_const.inner ((ContinuousLinearMap.apply ℝ _ x).continuous)
      exact (hc.comp_stronglyMeasurable (hΦmeas i (Nb b n))).measurable
    have hmp : ∀ n, MeasurePreserving (env n) Ph P0 := fun n => (hMP n).1
    have horig : ∀ b, ∀ᵐ β ∂P0, Tendsto (fun n => T b n β) atTop (𝓝 (L0 b β)) := by
      intro b
      cases b
      · filter_upwards [hlimF] with β hβ
        exact (hβ i).comp hseq.tendsto_atTop
      · filter_upwards [hlimE] with β hβ
        exact (hβ i).comp hseq.tendsto_atTop
    have hrep : ∀ b, ∀ᵐ w ∂Ph, Tendsto (fun n => env n w) atTop (𝓝 (field w)) ∧
        Tendsto (fun n => T b (id n) (env n w)) atTop (𝓝 (Lh b w)) := by
      intro b
      cases b
      · filter_upwards [henvc, hGNd, hGNc] with w h1 h2 h3
        refine ⟨h1.2, ?_⟩
        have hfun : (fun n => T false (id n) (env n w)) = fun n => GNF i n w := by
          funext n
          refine ContinuousLinearMap.ext fun f => ?_
          simp only [T, Nb, id, cond]
          rw [volumeResponseOperator_apply]
          exact ((h2 i n f).2).symm
        rw [hfun]
        exact (h3 i).2
      · filter_upwards [henvc, hGNd, hGNc] with w h1 h2 h3
        refine ⟨h1.1, ?_⟩
        have hfun : (fun n => T true (id n) (env n w)) = fun n => GNE i n w := by
          funext n
          refine ContinuousLinearMap.ext fun f => ?_
          simp only [T, Nb, id, cond]
          rw [volumeResponseOperator_apply]
          exact ((h2 i n f).1).symm
        rw [hfun]
        exact (h3 i).1
    have hEF' : ∀ᵐ w ∂Ph, Lh true w = Lh false w := by
      filter_upwards [hEF] with w hw
      exact hw i
    have key := conv_represented_limit_transfer P0 Ph T L0 Lh id strictMono_id env field hsym
      (Dop i) (Set.countable_coe_iff.1 (hDcount i)) (hDdense i) (hDadd i) hmeas hmp hmpLim
      horig hrep hEF'
    filter_upwards [key] with β hβ
    exact hβ
  exact ae_all_iff.2 hper

end Paper
