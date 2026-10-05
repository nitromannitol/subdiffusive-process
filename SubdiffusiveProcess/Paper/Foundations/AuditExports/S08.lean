module

public import SubdiffusiveProcess.Paper.mfd_lem_cutoffs
public import SubdiffusiveProcess.Paper.inputs_J_witness
public import SubdiffusiveProcess.Paper.Foundations.AuditExports.S07

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization _root_.SubdiffusiveProcess.Paper
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal BigOperators Topology ContDiff

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- The literal killed spaces on the chosen cubes, with Poincaré supplied by their geometry. -/
def cutoffResponseSpaces (d : ℕ) (hd : 2 ≤ d)
    (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i) :
    ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)) :=
  fun i => killedResponseSpace
    (cubeKilledPoincare (lt_of_lt_of_le Nat.zero_lt_two hd) (Z i) (hR i))

/-- `mfd:lem-cutoffs`, with the chart and killed response spaces supplied internally
and clauses (i)–(iii) exposed.
The same full-measure event carries the spatial cutoff, energy/Morrey/Hölder
bounds, uniform subsequence limit, and triadic collars. The combined random
majorant has every requested finite moment; the deterministic collar factor is one. -/
theorem cutoffClauses
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
    (hrat : ∀ i, (∀ c : Fin d, ∃ q : ℚ, Z i c = (q : ℝ)) ∧ ∃ m : ℤ, R i = (3 : ℝ) ^ m)
    (hfamily : conv_represented_root_family d Z R hR) (jTarget : ℕ)
    (beta alpha eta t : ℝ)
    (hbeta : 1 / 2 < beta) (hbetaalpha : beta < alpha)
    (halpha : alpha < 1) (heta : 0 < eta)
    (htlow : (d : ℝ) - 1 < t) (htupper : t < (d : ℝ))
    (hetaalpha : 1 + eta < 2 * alpha)
    (orders : Finset ℝ) (horders : ∀ p ∈ orders, 0 < p)
    (Cgrad : ℝ) (hCgrad : 0 < Cgrad) :
    let E := Classical.choice (inputs_J_witness d hd)
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d, M.delta ≤ delta0 →
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
            conv_represented_joint_grids d hd M H Ωh Ph field env env Z R hR (cutoffResponseSpaces d hd Z R hR)
              GNE GNF GE GF (fun n => NE (seq n)) (fun n => NF (seq n)) alpha eta E beta t ∧
            aux_conv_represented_env_interface_bounds d hd M H Ωh Ph env env Z R hR (cutoffResponseSpaces d hd Z R hR) GE GF
              (fun n => NE (seq n)) (fun n => NF (seq n)) ∧
            ∀ k : ℕ, ∃ e : ℕ → ℕ, (∀ i ≤ k, ∃ j, e j = i) ∧
  ∃ (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (responseE responseF : ℕ → Ωh → ℝ)
    (eventE eventF : Set Ωh)
    (root : ℕ)
    (_hunitRoot : (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) ⊆
      (centeredCube ((Z ∘ e) root) ((R ∘ e) root) ((fun j => hR (e j)) root) : Set (SpatialCoordinates d)))
    (Dcat : ∀ i, Submodule ℚ
      (DomainL2 (centeredCube ((Z ∘ e) i) ((R ∘ e) i) ((fun j => hR (e j)) i))))
    (hDcat : ∀ i, Countable (Dcat i))
    (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
    (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (traceH1 : ∀ i, ℕ → Homogenization.H1Function
      (centeredCube ((Z ∘ e) i) ((R ∘ e) i) ((fun j => hR (e j)) i) : Set (SpatialCoordinates d)))
    (usrcE usrcF : ∀ i, Dcat i → ℕ → Ωh → ((fun j => (cutoffResponseSpaces d hd Z R hR) (e j)) i).space)
    (srcRepE srcRepF : ∀ i, Dcat i → ℕ → Ωh → SpatialCoordinates d → ℝ)
    (ucellE ucellF : ∀ i, ℕ → ℕ → Ωh → Homogenization.H1Function
      (centeredCube ((Z ∘ e) i) ((R ∘ e) i) ((fun j => hR (e j)) i) : Set (SpatialCoordinates d)))
    (Cext betaCat tCat : ℝ) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
    (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
    (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ),
    (I = E ∧ betaCat = beta ∧ tCat = t) ∧
    (∀ (j : ℕ) (o : SpatialCoordinates d), (∀ i : Fin d, ∃ q : ℚ, o i = (q : ℝ)) →
      ∃ g : ℕ, gridRoot g = j ∧ origin g = o) ∧
    (∀ (j' : ℕ) (k : ℕ) (j : ℕ), ∃ h : ℕ,
      trace j h = bufferedCollarProfile d ((Z ∘ e) j') ((R ∘ e) j') ((R ∘ e) j' / (10 * (3 : ℝ) ^ k))) ∧
    letI : ∀ i, Countable (Dcat i) := hDcat
    (conv_represented_estimates d hd M H Ωh Ph (fun n => NE (seq n)) env
      ℕ root (Z ∘ e) (R ∘ e) (fun j => hR (e j)) (fun j => (cutoffResponseSpaces d hd Z R hR) (e j)) Dcat fcat (fun _ => ℕ) trace traceH1
      usrcE srcRepE ucellE Cext betaCat alpha eta tCat {1} I
      ℕ (fun i n omega => catalogResponse i ((fun n => NE (seq n)) n) (env n omega)) responseE
      (fun i n omega => catalogConstant i ((fun n => NE (seq n)) n) (env n omega)) eventE
      coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
    conv_represented_estimates d hd M H Ωh Ph (fun n => NF (seq n)) env
      ℕ root (Z ∘ e) (R ∘ e) (fun j => hR (e j)) (fun j => (cutoffResponseSpaces d hd Z R hR) (e j)) Dcat fcat (fun _ => ℕ) trace traceH1
      usrcF srcRepF ucellF Cext betaCat alpha eta tCat {1} I
      ℕ (fun i n omega => catalogResponse i ((fun n => NF (seq n)) n) (env n omega)) responseF
      (fun i n omega => catalogConstant i ((fun n => NF (seq n)) n) (env n omega)) eventF
      coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey) ∧
    ∀ jCut : ℕ, (Z ∘ e) jCut = (Z jTarget) → (R ∘ e) jCut = (R jTarget) →
      let Q := fun j => (centeredCube ((Z ∘ e) j) ((R ∘ e) j) ((fun j => hR (e j)) j) : Set (SpatialCoordinates d))
      let Small := {j : ℕ // Q j ⊆ Q jCut}
      (  let Q := centeredCube ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
  let S0 := (fun j : Small => (fun j => (cutoffResponseSpaces d hd Z R hR) (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small)
  let aN := fun (omega : Ωh) (n : ℕ) =>
    _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) ((fun n => NE (seq n)) n)
      ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
  let rawAN := fun (omega : Ωh) (n : ℕ) =>
    cutoffCoefficient M H (env n omega) ((fun n => NE (seq n)) n)
  ∃ KN : ℕ → Ωh → ℝ, ∃ Ggood : Set Ωh,
    MeasurableSet Ggood ∧ Ggood ⊆ eventE ∧ Ph (Ggoodᶜ) = 0 ∧
    (∀ n : ℕ, Measurable (KN n)) ∧
    (∀ n : ℕ, ∀ omega : Ωh, 1 ≤ KN n omega) ∧
    (∀ p ∈ orders, ∃ Cp : ℝ, 0 ≤ Cp ∧
      ∀ n : ℕ,
        MemLp (KN n) (ENNReal.ofReal p) Ph ∧
          eLpNorm (KN n) (ENNReal.ofReal p) Ph ≤ ENNReal.ofReal Cp) ∧
    (∀ omega ∈ Ggood,
      BddAbove (Set.range (fun n : ℕ => KN n omega))) ∧
    ∀ omega ∈ Ggood,
      (∀ b : (fun _ : Small => ℕ) (⟨jCut, subset_rfl⟩ : Small), ∀ K O W : Set (SpatialCoordinates d), ∀ Jmesh : ℕ,
        IsCompact K → IsOpen O →
        closure O ⊆ (Q : Set (SpatialCoordinates d)) →
        IsOpen W → K ⊆ W → W ⊆ O →
        (∀ x : SpatialCoordinates d,
          0 ≤ (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x ∧ (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x ≤ 1) →
        (∀ x ∈ W, (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x = 1) →
        tsupport ((fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b) ⊆ O →
        (∀ k : OddGridIndex d (triadicHalf Jmesh),
          (closure
              (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ∩
              {x : SpatialCoordinates d |
                0 < (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x ∧ (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x < 1}).Nonempty →
            closure
                (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ⊆
              O \ K) →
        ∃ chiH : ℕ → Homogenization.H1Function
            (Q : Set (SpatialCoordinates d)),
          ∃ chiS : ℕ → S0.space,
            ∃ chic : ℕ → SpatialCoordinates d → ℝ,
              ∃ V : Set (SpatialCoordinates d),
                ∃ Benergy Ball Bholder : ℝ,
                  IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧
                  0 ≤ Benergy ∧ 0 ≤ Ball ∧ 0 ≤ Bholder ∧
                  (∀ n : ℕ,
                    (chiS n).val = sobolevDataOfH1 (chiH n) ∧
                    ContinuousOn (chic n)
                      (closure (Q : Set (SpatialCoordinates d))) ∧
                    (chiS n).val.1 =ᵐ[
                      volume.restrict (Q : Set (SpatialCoordinates d))]
                      chic n ∧
                    (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                      0 ≤ chic n x ∧ chic n x ≤ 1) ∧
                    (∀ x ∈ V, chic n x = 1) ∧
                    (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                      x ∉ O → chic n x = 0) ∧
                    (∀ k : OddGridIndex d (triadicHalf Jmesh),
                      IsWeaklyHarmonicOn (rawAN omega n)
                        (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                          (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                        ((chiH n).restrict
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k).isOpen
                          (oddGridCell_subset ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k)) ∧
                      HasZeroTraceDifferenceOn
                        (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                          (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                        ((chiH n).restrict
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k).isOpen
                          (oddGridCell_subset ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k))
                        (((fun j : Small => traceH1 j.val) (⟨jCut, subset_rfl⟩ : Small) b).restrict
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k).isOpen
                          (oddGridCell_subset ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k))) ∧
                    (∀ k : OddGridIndex d (triadicHalf Jmesh),
                      (∃ c : ℝ, ∀ x ∈ closure
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                        (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x = c) →
                        ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                          (chiS n).val.2 i x = 0) ∧
                    responseForm S0 (aN omega n) (chiS n) (chiS n) ≤ Benergy ∧
                    (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ s : ℝ,
                      0 < s → s ≤ 1 →
                      ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
                        (fun y => ENNReal.ofReal
                          ((aN omega n).val y *
                            ∑ i : Fin d, ((chiS n).val.2 i y) ^ 2)))
                        (Metric.ball x s) ≤ ENNReal.ofReal (Ball * s ^ tCat)) ∧
                    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
                      (closure (Q : Set (SpatialCoordinates d))) (chic n) ∧
                    _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
                      (closure (Q : Set (SpatialCoordinates d))) (chic n) ≤
                      Bholder) ∧
                  (∃ sigma : ℕ → ℕ, ∃ chiLim : SpatialCoordinates d → ℝ,
                    StrictMono sigma ∧
                    ContinuousOn chiLim
                      (closure (Q : Set (SpatialCoordinates d))) ∧
                    TendstoUniformlyOn (fun n => chic (sigma n)) chiLim atTop
                      (closure (Q : Set (SpatialCoordinates d))) ∧
                    (∀ k : OddGridIndex d (triadicHalf Jmesh),
                      (∃ c : ℝ, ∀ x ∈ closure
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                        (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x = c) →
                        ∀ x ∈ closure
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                          chiLim x = (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x))) ∧
      (∀ Jr : ℕ,
        let rho := (fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small) / (3 : ℝ) ^ Jr
          ∀ thetaR : SpatialCoordinates d → ℝ,
            ContDiff ℝ ∞ thetaR →
            (∀ x : SpatialCoordinates d,
              0 ≤ thetaR x ∧ thetaR x ≤ 1) →
            (∀ x ∈ (Q : Set (SpatialCoordinates d)),
              Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                thetaR x = 0) →
            (∀ x ∈ (Q : Set (SpatialCoordinates d)),
              3 * rho ≤ Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) →
                thetaR x = 1) →
            (∀ x : SpatialCoordinates d,
              norm (fderiv ℝ thetaR x) ≤ Cgrad / rho) →
            ∀ thetaRH1 : Homogenization.H1Function
              (Q : Set (SpatialCoordinates d)),
              thetaRH1.toFun = thetaR →
              ∃ collarH : ℕ → Homogenization.H1Function
                  (Q : Set (SpatialCoordinates d)),
                ∃ collarS : ℕ → S0.space,
                  ∃ collarC : ℕ → SpatialCoordinates d → ℝ,
                    ∀ n : ℕ,
                      (collarS n).val = sobolevDataOfH1 (collarH n) ∧
                      ContinuousOn (collarC n)
                        (closure (Q : Set (SpatialCoordinates d))) ∧
                      (collarS n).val.1 =ᵐ[
                        volume.restrict (Q : Set (SpatialCoordinates d))]
                        collarC n ∧
                      (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                        0 ≤ collarC n x ∧ collarC n x ≤ 1) ∧
                      (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                        Metric.infDist x
                            (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                          collarC n x = 0) ∧
                      (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                        3 * rho ≤ Metric.infDist x
                            (frontier (Q : Set (SpatialCoordinates d))) →
                          collarC n x = 1) ∧
                      (∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                        (Q : Set (SpatialCoordinates d)),
                        3 * rho < Metric.infDist x
                            (frontier (Q : Set (SpatialCoordinates d))) →
                          (collarS n).val.2 i x = 0) ∧
                      (∀ k : OddGridIndex d (triadicHalf Jr),
                        IsWeaklyHarmonicOn (rawAN omega n)
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jr) k : Set (SpatialCoordinates d))
                          ((collarH n).restrict
                            (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                              (triadicHalf Jr) k).isOpen
                            (oddGridCell_subset ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                              (triadicHalf Jr) k)) ∧
                        HasZeroTraceDifferenceOn
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jr) k : Set (SpatialCoordinates d))
                          ((collarH n).restrict
                            (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                              (triadicHalf Jr) k).isOpen
                            (oddGridCell_subset ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                              (triadicHalf Jr) k))
                          (thetaRH1.restrict
                            (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                              (triadicHalf Jr) k).isOpen
                            (oddGridCell_subset ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                              (triadicHalf Jr) k))) ∧
                      responseForm S0 (aN omega n) (collarS n) (collarS n) ≤
                        (1 : ℝ) * KN n omega * rho ^ (-1 - eta))) ∧
      (  let Q := centeredCube ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
  let S0 := (fun j : Small => (fun j => (cutoffResponseSpaces d hd Z R hR) (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small)
  let aN := fun (omega : Ωh) (n : ℕ) =>
    _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) ((fun n => NF (seq n)) n)
      ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
  let rawAN := fun (omega : Ωh) (n : ℕ) =>
    cutoffCoefficient M H (env n omega) ((fun n => NF (seq n)) n)
  ∃ KN : ℕ → Ωh → ℝ, ∃ Ggood : Set Ωh,
    MeasurableSet Ggood ∧ Ggood ⊆ eventF ∧ Ph (Ggoodᶜ) = 0 ∧
    (∀ n : ℕ, Measurable (KN n)) ∧
    (∀ n : ℕ, ∀ omega : Ωh, 1 ≤ KN n omega) ∧
    (∀ p ∈ orders, ∃ Cp : ℝ, 0 ≤ Cp ∧
      ∀ n : ℕ,
        MemLp (KN n) (ENNReal.ofReal p) Ph ∧
          eLpNorm (KN n) (ENNReal.ofReal p) Ph ≤ ENNReal.ofReal Cp) ∧
    (∀ omega ∈ Ggood,
      BddAbove (Set.range (fun n : ℕ => KN n omega))) ∧
    ∀ omega ∈ Ggood,
      (∀ b : (fun _ : Small => ℕ) (⟨jCut, subset_rfl⟩ : Small), ∀ K O W : Set (SpatialCoordinates d), ∀ Jmesh : ℕ,
        IsCompact K → IsOpen O →
        closure O ⊆ (Q : Set (SpatialCoordinates d)) →
        IsOpen W → K ⊆ W → W ⊆ O →
        (∀ x : SpatialCoordinates d,
          0 ≤ (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x ∧ (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x ≤ 1) →
        (∀ x ∈ W, (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x = 1) →
        tsupport ((fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b) ⊆ O →
        (∀ k : OddGridIndex d (triadicHalf Jmesh),
          (closure
              (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ∩
              {x : SpatialCoordinates d |
                0 < (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x ∧ (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x < 1}).Nonempty →
            closure
                (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                  (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ⊆
              O \ K) →
        ∃ chiH : ℕ → Homogenization.H1Function
            (Q : Set (SpatialCoordinates d)),
          ∃ chiS : ℕ → S0.space,
            ∃ chic : ℕ → SpatialCoordinates d → ℝ,
              ∃ V : Set (SpatialCoordinates d),
                ∃ Benergy Ball Bholder : ℝ,
                  IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧
                  0 ≤ Benergy ∧ 0 ≤ Ball ∧ 0 ≤ Bholder ∧
                  (∀ n : ℕ,
                    (chiS n).val = sobolevDataOfH1 (chiH n) ∧
                    ContinuousOn (chic n)
                      (closure (Q : Set (SpatialCoordinates d))) ∧
                    (chiS n).val.1 =ᵐ[
                      volume.restrict (Q : Set (SpatialCoordinates d))]
                      chic n ∧
                    (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                      0 ≤ chic n x ∧ chic n x ≤ 1) ∧
                    (∀ x ∈ V, chic n x = 1) ∧
                    (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                      x ∉ O → chic n x = 0) ∧
                    (∀ k : OddGridIndex d (triadicHalf Jmesh),
                      IsWeaklyHarmonicOn (rawAN omega n)
                        (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                          (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                        ((chiH n).restrict
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k).isOpen
                          (oddGridCell_subset ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k)) ∧
                      HasZeroTraceDifferenceOn
                        (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                          (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                        ((chiH n).restrict
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k).isOpen
                          (oddGridCell_subset ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k))
                        (((fun j : Small => traceH1 j.val) (⟨jCut, subset_rfl⟩ : Small) b).restrict
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k).isOpen
                          (oddGridCell_subset ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k))) ∧
                    (∀ k : OddGridIndex d (triadicHalf Jmesh),
                      (∃ c : ℝ, ∀ x ∈ closure
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                        (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x = c) →
                        ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                          (chiS n).val.2 i x = 0) ∧
                    responseForm S0 (aN omega n) (chiS n) (chiS n) ≤ Benergy ∧
                    (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ s : ℝ,
                      0 < s → s ≤ 1 →
                      ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
                        (fun y => ENNReal.ofReal
                          ((aN omega n).val y *
                            ∑ i : Fin d, ((chiS n).val.2 i y) ^ 2)))
                        (Metric.ball x s) ≤ ENNReal.ofReal (Ball * s ^ tCat)) ∧
                    _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
                      (closure (Q : Set (SpatialCoordinates d))) (chic n) ∧
                    _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm alpha
                      (closure (Q : Set (SpatialCoordinates d))) (chic n) ≤
                      Bholder) ∧
                  (∃ sigma : ℕ → ℕ, ∃ chiLim : SpatialCoordinates d → ℝ,
                    StrictMono sigma ∧
                    ContinuousOn chiLim
                      (closure (Q : Set (SpatialCoordinates d))) ∧
                    TendstoUniformlyOn (fun n => chic (sigma n)) chiLim atTop
                      (closure (Q : Set (SpatialCoordinates d))) ∧
                    (∀ k : OddGridIndex d (triadicHalf Jmesh),
                      (∃ c : ℝ, ∀ x ∈ closure
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                        (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x = c) →
                        ∀ x ∈ closure
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                          chiLim x = (fun j : Small => trace j.val) (⟨jCut, subset_rfl⟩ : Small) b x))) ∧
      (∀ Jr : ℕ,
        let rho := (fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small) / (3 : ℝ) ^ Jr
          ∀ thetaR : SpatialCoordinates d → ℝ,
            ContDiff ℝ ∞ thetaR →
            (∀ x : SpatialCoordinates d,
              0 ≤ thetaR x ∧ thetaR x ≤ 1) →
            (∀ x ∈ (Q : Set (SpatialCoordinates d)),
              Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                thetaR x = 0) →
            (∀ x ∈ (Q : Set (SpatialCoordinates d)),
              3 * rho ≤ Metric.infDist x (frontier (Q : Set (SpatialCoordinates d))) →
                thetaR x = 1) →
            (∀ x : SpatialCoordinates d,
              norm (fderiv ℝ thetaR x) ≤ Cgrad / rho) →
            ∀ thetaRH1 : Homogenization.H1Function
              (Q : Set (SpatialCoordinates d)),
              thetaRH1.toFun = thetaR →
              ∃ collarH : ℕ → Homogenization.H1Function
                  (Q : Set (SpatialCoordinates d)),
                ∃ collarS : ℕ → S0.space,
                  ∃ collarC : ℕ → SpatialCoordinates d → ℝ,
                    ∀ n : ℕ,
                      (collarS n).val = sobolevDataOfH1 (collarH n) ∧
                      ContinuousOn (collarC n)
                        (closure (Q : Set (SpatialCoordinates d))) ∧
                      (collarS n).val.1 =ᵐ[
                        volume.restrict (Q : Set (SpatialCoordinates d))]
                        collarC n ∧
                      (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
                        0 ≤ collarC n x ∧ collarC n x ≤ 1) ∧
                      (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                        Metric.infDist x
                            (frontier (Q : Set (SpatialCoordinates d))) ≤ rho →
                          collarC n x = 0) ∧
                      (∀ x ∈ (Q : Set (SpatialCoordinates d)),
                        3 * rho ≤ Metric.infDist x
                            (frontier (Q : Set (SpatialCoordinates d))) →
                          collarC n x = 1) ∧
                      (∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                        (Q : Set (SpatialCoordinates d)),
                        3 * rho < Metric.infDist x
                            (frontier (Q : Set (SpatialCoordinates d))) →
                          (collarS n).val.2 i x = 0) ∧
                      (∀ k : OddGridIndex d (triadicHalf Jr),
                        IsWeaklyHarmonicOn (rawAN omega n)
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jr) k : Set (SpatialCoordinates d))
                          ((collarH n).restrict
                            (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                              (triadicHalf Jr) k).isOpen
                            (oddGridCell_subset ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                              (triadicHalf Jr) k)) ∧
                        HasZeroTraceDifferenceOn
                          (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                            (triadicHalf Jr) k : Set (SpatialCoordinates d))
                          ((collarH n).restrict
                            (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                              (triadicHalf Jr) k).isOpen
                            (oddGridCell_subset ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                              (triadicHalf Jr) k))
                          (thetaRH1.restrict
                            (oddGridCell ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (R ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                              (triadicHalf Jr) k).isOpen
                            (oddGridCell_subset ((fun j : Small => (Z ∘ e) j.val) (⟨jCut, subset_rfl⟩ : Small)) ((fun j : Small => (fun j => hR (e j)) j.val) (⟨jCut, subset_rfl⟩ : Small))
                              (triadicHalf Jr) k))) ∧
                      responseForm S0 (aN omega n) (collarS n) (collarS n) ≤
                        (1 : ℝ) * KN n omega * rho ^ (-1 - eta))) := by
  classical
  exact
    mfd_lem_cutoffs d hd (Classical.choice (inputs_J_witness d hd)) Z R hR
      (cutoffResponseSpaces d hd Z R hR)
      (fun _ => rfl) hrat hfamily jTarget beta alpha eta t
      hbeta hbetaalpha halpha heta htlow htupper hetaalpha orders horders Cgrad hCgrad

end SubdiffusiveProcess.AuditExports
