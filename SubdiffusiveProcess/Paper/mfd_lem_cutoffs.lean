import SubdiffusiveProcess.Paper.lem_cutoffs
import SubdiffusiveProcess.Paper.represented_estimates_actual_model
import SubdiffusiveProcess.Paper.cutoffs_actual_model_estimates
import SubdiffusiveProcess.Paper.in_cutoffs_actual_model_output
import SubdiffusiveProcess.Paper.conv_represented_estimates_subcatalogue
import SubdiffusiveProcess.Paper.conv_represented_joint_grids

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal BigOperators Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper



theorem mfd_lem_cutoffs
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : Paper.in_J d)
    (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
    (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
    (hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (Z i) (R i) (hR i)))
    (hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m)
    (hfamily : conv_represented_root_family d Z R hR) (jTarget : ℕ)
    (beta alpha eta t : ℝ)
    (hbeta : 1 / 2 < beta) (hbetaalpha : beta < alpha)
    (halpha : alpha < 1) (heta : 0 < eta)
    (htlow : (d : ℝ) - 1 < t) (htupper : t < (d : ℝ))
    (hetaalpha : 1 + eta < 2 * alpha)
    (orders : Finset ℝ) (horders : ∀ p ∈ orders, 0 < p)
    (Cgrad : ℝ) (hCgrad : 0 < Cgrad) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d, M.delta ≤ delta0 →
        (∃ H : BilateralField d → C(SpatialCoordinates d, ℝ), InfraredCharacterization M H) ∧
        ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ), InfraredCharacterization M H →
        ∀ NE NF : ℕ → ℕ, StrictMono NE → StrictMono NF →
        ∃ seq : ℕ → ℕ, StrictMono seq ∧
          ∃ (Ωh : Type) (_ : MeasurableSpace Ωh) (Ph : Measure Ωh) (_ : IsProbabilityMeasure Ph)
            (field : Ωh → BilateralField d) (env : ℕ → Ωh → BilateralField d)
            (GNE GNF : (i : ℕ) → ℕ → Ωh →
              DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
                DomainL2 (centeredCube (Z i) (R i) (hR i)))
            (GE GF : (i : ℕ) → Ωh →
              DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ]
                DomainL2 (centeredCube (Z i) (R i) (hR i))),
            conv_represented_joint_grids d hd M H Ωh Ph field env env Z R hR Sspace
              GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) alpha eta E beta t ∧
            aux_conv_represented_env_interface_bounds d hd M H Ωh Ph env env Z R hR Sspace GE GF
              (fun n => NE (seq n)) (fun n => NF (seq n)) ∧
            ∀ k : ℕ, ∃ e : ℕ → ℕ, (∀ i ≤ k, ∃ j, e j = i) ∧
              aux_lem_cutoffs_actual_model_catalogue d hd M H Ωh Ph env env
                (Z ∘ e) (R ∘ e) (fun j => hR (e j)) (fun j => Sspace (e j))
                (fun n => NE (seq n)) (fun n => NF (seq n)) alpha eta E beta t
                (Z jTarget) (R jTarget) orders Cgrad :=
by
  classical
  have ha0 : 0 < alpha := by linarith
  obtain ⟨_, _, hEveryChart⟩ := represented_estimates_actual_model d hd alpha eta beta t
    htlow htupper ha0 halpha heta hetaalpha hbeta hbetaalpha
  obtain ⟨δB, hδB, hB⟩ := hEveryChart E
  obtain ⟨δC, hδC, hC⟩ := cutoffs_actual_model_estimates d hd
    (Z jTarget) (R jTarget) (hR jTarget) beta alpha eta t hbeta hbetaalpha halpha heta
    htlow htupper hetaalpha orders horders E Cgrad hCgrad
  refine ⟨min δB δC, lt_min hδB hδC, ?_⟩
  intro M hM
  have hMB := hM.trans (min_le_left _ _)
  have hMC := hM.trans (min_le_right _ _)
  refine ⟨(hB M hMB).1, ?_⟩
  intro H hH NE NF hNE hNF
  obtain ⟨seq, hseq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF, hjoint, hbounds⟩ :=
    (hB M hMB).2 H hH Z R hR Sspace hS hrat hfamily NE NF hNE hNF
  letI : MeasurableSpace Ωh := mΩh
  letI : IsProbabilityMeasure Ph := hPh
  refine ⟨seq, hseq, Ωh, mΩh, Ph, hPh, field, env, GNE, GNF, GE, GF, hjoint, hbounds, ?_⟩
  intro k
  obtain ⟨e, he, hcat⟩ := hjoint.2 k
  refine ⟨e, he, ?_⟩
  rcases hcat with ⟨catalogResponse, catalogConstant, responseE, responseF, eventE, eventF,
    root, hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF,
    ucellE, ucellF, Cext, beta', t', I, coercivityKey, extensionKey, lambdaKey,
    sourceResponseKey, sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey,
    cellHolderKey, origin, gridRoot, gridKey, hI, hGridCoverage, hCollarTraces, hrepE, hrepF⟩
  rcases hI with ⟨hI, hbeta', ht'⟩
  subst I
  subst beta'
  subst t'
  letI : ∀ i, Countable (Dcat i) := hDcat
  refine ⟨catalogResponse, catalogConstant, responseE, responseF, eventE, eventF, root,
    hunitRoot, Dcat, hDcat, fcat, trace, traceH1, usrcE, usrcF, srcRepE, srcRepF, ucellE,
    ucellF, Cext, beta, t, E, coercivityKey, extensionKey, lambdaKey, sourceResponseKey,
    sourceGrowthKey, sourceHolderKey, cellResponseKey, cellGrowthKey, cellHolderKey, origin,
    gridRoot, gridKey, ⟨rfl, rfl, rfl⟩, hGridCoverage, hCollarTraces, ⟨hrepE, hrepF⟩, ?_⟩
  intro j hzj hrj Q Small
  letI : ∀ i : Small, Countable (Dcat i.val) := fun i => hDcat i.val
  have hsubE := conv_represented_estimates_subcatalogue d hd M H Cext beta alpha eta t {1}
    Ωh Ph (fun n => NE (seq n)) env ℕ root (Z ∘ e) (R ∘ e) (fun i => hR (e i))
    (fun i => Sspace (e i)) Dcat fcat (fun _ => ℕ) trace traceH1 usrcE srcRepE ucellE E
    ℕ (fun i n om => catalogResponse i (NE (seq n)) (env n om)) responseE
    (fun i n om => catalogConstant i (NE (seq n)) (env n om)) eventE coercivityKey extensionKey
    lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey ℕ origin gridRoot gridKey hrepE j
  have hsubF := conv_represented_estimates_subcatalogue d hd M H Cext beta alpha eta t {1}
    Ωh Ph (fun n => NF (seq n)) env ℕ root (Z ∘ e) (R ∘ e) (fun i => hR (e i))
    (fun i => Sspace (e i)) Dcat fcat (fun _ => ℕ) trace traceH1 usrcF srcRepF ucellF E
    ℕ (fun i n om => catalogResponse i (NF (seq n)) (env n om)) responseF
    (fun i n om => catalogConstant i (NF (seq n)) (env n om)) eventF coercivityKey extensionKey
    lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey
    cellHolderKey ℕ origin gridRoot gridKey hrepF j
  constructor
  · exact @hC M H hMC Cext Ωh mΩh Ph hPh (fun n => NE (seq n)) env Small inferInstance inferInstance ⟨j, subset_rfl⟩
      (fun i => Z (e i.val)) (fun i => R (e i.val)) (fun i => hR (e i.val))
      (fun i => Sspace (e i.val)) (fun i => Dcat i.val) (fun i => hDcat i.val) (fun i => fcat i.val)
      (fun _ => ℕ) (fun _ => inferInstance) (fun i => trace i.val) (fun i => traceH1 i.val)
      (fun i => usrcE i.val) (fun i => srcRepE i.val) (fun i => ucellE i.val)
      ℕ inferInstance (fun i n om => catalogResponse i (NE (seq n)) (env n om)) responseE
      (fun i n om => catalogConstant i (NE (seq n)) (env n om)) eventE
      (fun i => coercivityKey i.val) (fun i => extensionKey i.val) (fun i => lambdaKey i.val)
      (fun i => sourceResponseKey i.val) (fun i => sourceGrowthKey i.val)
      (fun i => sourceHolderKey i.val) (fun i => cellResponseKey i.val)
      (fun i => cellGrowthKey i.val) (fun i => cellHolderKey i.val)
      {g : ℕ // Q (gridRoot g) ⊆ Q j} inferInstance (fun g => origin g.val)
      (fun g => ⟨gridRoot g.val, g.property⟩) (fun g => gridKey g.val) hzj hrj hsubE
  · exact @hC M H hMC Cext Ωh mΩh Ph hPh (fun n => NF (seq n)) env Small inferInstance inferInstance ⟨j, subset_rfl⟩
      (fun i => Z (e i.val)) (fun i => R (e i.val)) (fun i => hR (e i.val))
      (fun i => Sspace (e i.val)) (fun i => Dcat i.val) (fun i => hDcat i.val) (fun i => fcat i.val)
      (fun _ => ℕ) (fun _ => inferInstance) (fun i => trace i.val) (fun i => traceH1 i.val)
      (fun i => usrcF i.val) (fun i => srcRepF i.val) (fun i => ucellF i.val)
      ℕ inferInstance (fun i n om => catalogResponse i (NF (seq n)) (env n om)) responseF
      (fun i n om => catalogConstant i (NF (seq n)) (env n om)) eventF
      (fun i => coercivityKey i.val) (fun i => extensionKey i.val) (fun i => lambdaKey i.val)
      (fun i => sourceResponseKey i.val) (fun i => sourceGrowthKey i.val)
      (fun i => sourceHolderKey i.val) (fun i => cellResponseKey i.val)
      (fun i => cellGrowthKey i.val) (fun i => cellHolderKey i.val)
      {g : ℕ // Q (gridRoot g) ⊆ Q j} inferInstance (fun g => origin g.val)
      (fun g => ⟨gridRoot g.val, g.property⟩) (fun g => gridKey g.val) hzj hrj hsubF

end Paper
