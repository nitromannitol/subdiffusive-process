module

public import SubdiffusiveProcess.Paper.lem_cutoffs
public import SubdiffusiveProcess.Paper.conv_represented_estimates_subcatalogue
public import SubdiffusiveProcess.Paper.conv_represented_joint_grids

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal BigOperators Topology ContDiff
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The complete cutoff conclusion, copied verbatim from the existing principal.
The represented record is not a premise of this predicate. -/
def in_cutoffs_actual_model_output
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (J : Type) (j0 : J)
    (z : J → SpatialCoordinates d) (rad : J → ℝ) (hrad : ∀ j, 0 < rad j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (rad j) (hrad j)))
    (T : J → Type) (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j → Homogenization.H1Function
      (centeredCube (z j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (alpha eta t Cgrad Ccollar : ℝ) (orders : Finset ℝ) (G : Set Ω) : Prop :=
  let Q := centeredCube (z j0) (rad j0) (hrad j0)
  let S0 := S j0
  let aN := fun (omega : Ω) (n : ℕ) =>
    _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n omega) (cutoff n)
      (z j0) (hrad j0)
  let rawAN := fun (omega : Ω) (n : ℕ) =>
    cutoffCoefficient M H (env n omega) (cutoff n)
  ∃ KN : ℕ → Ω → ℝ, ∃ Ggood : Set Ω,
    MeasurableSet Ggood ∧ Ggood ⊆ G ∧ P (Ggoodᶜ) = 0 ∧
    (∀ n : ℕ, Measurable (KN n)) ∧
    (∀ n : ℕ, ∀ omega : Ω, 1 ≤ KN n omega) ∧
    (∀ p ∈ orders, ∃ Cp : ℝ, 0 ≤ Cp ∧
      ∀ n : ℕ,
        MemLp (KN n) (ENNReal.ofReal p) P ∧
          eLpNorm (KN n) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cp) ∧
    (∀ omega ∈ Ggood,
      BddAbove (Set.range (fun n : ℕ => KN n omega))) ∧
    ∀ omega ∈ Ggood,
      (∀ b : T j0, ∀ K O W : Set (SpatialCoordinates d), ∀ Jmesh : ℕ,
        IsCompact K → IsOpen O →
        closure O ⊆ (Q : Set (SpatialCoordinates d)) →
        IsOpen W → K ⊆ W → W ⊆ O →
        (∀ x : SpatialCoordinates d,
          0 ≤ theta j0 b x ∧ theta j0 b x ≤ 1) →
        (∀ x ∈ W, theta j0 b x = 1) →
        tsupport (theta j0 b) ⊆ O →
        (∀ k : OddGridIndex d (triadicHalf Jmesh),
          (closure
              (oddGridCell (z j0) (rad j0) (hrad j0)
                (triadicHalf Jmesh) k : Set (SpatialCoordinates d)) ∩
              {x : SpatialCoordinates d |
                0 < theta j0 b x ∧ theta j0 b x < 1}).Nonempty →
            closure
                (oddGridCell (z j0) (rad j0) (hrad j0)
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
                        (oddGridCell (z j0) (rad j0) (hrad j0)
                          (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                        ((chiH n).restrict
                          (oddGridCell (z j0) (rad j0) (hrad j0)
                            (triadicHalf Jmesh) k).isOpen
                          (oddGridCell_subset (z j0) (hrad j0)
                            (triadicHalf Jmesh) k)) ∧
                      HasZeroTraceDifferenceOn
                        (oddGridCell (z j0) (rad j0) (hrad j0)
                          (triadicHalf Jmesh) k : Set (SpatialCoordinates d))
                        ((chiH n).restrict
                          (oddGridCell (z j0) (rad j0) (hrad j0)
                            (triadicHalf Jmesh) k).isOpen
                          (oddGridCell_subset (z j0) (hrad j0)
                            (triadicHalf Jmesh) k))
                        ((thetaH1 j0 b).restrict
                          (oddGridCell (z j0) (rad j0) (hrad j0)
                            (triadicHalf Jmesh) k).isOpen
                          (oddGridCell_subset (z j0) (hrad j0)
                            (triadicHalf Jmesh) k))) ∧
                    (∀ k : OddGridIndex d (triadicHalf Jmesh),
                      (∃ c : ℝ, ∀ x ∈ closure
                          (oddGridCell (z j0) (rad j0) (hrad j0)
                            (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                        theta j0 b x = c) →
                        ∀ i : Fin d, ∀ᵐ x ∂volume.restrict
                          (oddGridCell (z j0) (rad j0) (hrad j0)
                            (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                          (chiS n).val.2 i x = 0) ∧
                    responseForm S0 (aN omega n) (chiS n) (chiS n) ≤ Benergy ∧
                    (∀ x ∈ closure (Q : Set (SpatialCoordinates d)), ∀ s : ℝ,
                      0 < s → s ≤ 1 →
                      ((volume.restrict (Q : Set (SpatialCoordinates d))).withDensity
                        (fun y => ENNReal.ofReal
                          ((aN omega n).val y *
                            ∑ i : Fin d, ((chiS n).val.2 i y) ^ 2)))
                        (Metric.ball x s) ≤ ENNReal.ofReal (Ball * s ^ t)) ∧
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
                          (oddGridCell (z j0) (rad j0) (hrad j0)
                            (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                        theta j0 b x = c) →
                        ∀ x ∈ closure
                          (oddGridCell (z j0) (rad j0) (hrad j0)
                            (triadicHalf Jmesh) k : Set (SpatialCoordinates d)),
                          chiLim x = theta j0 b x))) ∧
      (∀ Jr : ℕ,
        let rho := rad j0 / (3 : ℝ) ^ Jr
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
                          (oddGridCell (z j0) (rad j0) (hrad j0)
                            (triadicHalf Jr) k : Set (SpatialCoordinates d))
                          ((collarH n).restrict
                            (oddGridCell (z j0) (rad j0) (hrad j0)
                              (triadicHalf Jr) k).isOpen
                            (oddGridCell_subset (z j0) (hrad j0)
                              (triadicHalf Jr) k)) ∧
                        HasZeroTraceDifferenceOn
                          (oddGridCell (z j0) (rad j0) (hrad j0)
                            (triadicHalf Jr) k : Set (SpatialCoordinates d))
                          ((collarH n).restrict
                            (oddGridCell (z j0) (rad j0) (hrad j0)
                              (triadicHalf Jr) k).isOpen
                            (oddGridCell_subset (z j0) (hrad j0)
                              (triadicHalf Jr) k))
                          (thetaRH1.restrict
                            (oddGridCell (z j0) (rad j0) (hrad j0)
                              (triadicHalf Jr) k).isOpen
                            (oddGridCell_subset (z j0) (hrad j0)
                              (triadicHalf Jr) k))) ∧
                      responseForm S0 (aN omega n) (collarS n) (collarS n) ≤
                        Ccollar * KN n omega * rho ^ (-1 - eta))

/-- The represented catalogue retaining full rational grid coverage and buffered collar profiles. -/
def aux_lem_cutoffs_actual_model_catalogue (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (envE envF : ℕ → Ω → BilateralField d)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (NE NF : ℕ → ℕ) (alpha eta : ℝ)
    (E : _root_.SubdiffusiveProcess.Paper.in_J d) (beta0 t0 : ℝ)
    (z0 : SpatialCoordinates d) (R0 : ℝ) (orders : Finset ℝ) (Cgrad : ℝ) : Prop :=
  ∃ (catalogResponse catalogConstant : ℕ → ℕ → BilateralField d → ℝ)
    (responseE responseF : ℕ → Ω → ℝ)
    (eventE eventF : Set Ω)
    (root : ℕ)
    (_hunitRoot : (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d)) ⊆
      (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
    (Dcat : ∀ i, Submodule ℚ
      (DomainL2 (centeredCube (z i) (r i) (hr i))))
    (hDcat : ∀ i, Countable (Dcat i))
    (fcat : ∀ i, Dcat i → SpatialCoordinates d → ℝ)
    (trace : ℕ → ℕ → SpatialCoordinates d → ℝ)
    (traceH1 : ∀ i, ℕ → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (usrcE usrcF : ∀ i, Dcat i → ℕ → Ω → (Sspace i).space)
    (srcRepE srcRepF : ∀ i, Dcat i → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucellE ucellF : ∀ i, ℕ → ℕ → Ω → Homogenization.H1Function
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)))
    (Cext beta t : ℝ) (I : _root_.SubdiffusiveProcess.Paper.in_J d)
    (coercivityKey extensionKey lambdaKey : ℕ → ℕ)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ i, Dcat i → ℕ)
    (cellResponseKey cellGrowthKey cellHolderKey : ℕ → ℕ → ℕ)
    (origin : ℕ → SpatialCoordinates d) (gridRoot gridKey : ℕ → ℕ),
    (I = E ∧ beta = beta0 ∧ t = t0) ∧
    (∀ (j : ℕ) (o : SpatialCoordinates d), (∀ i : Fin d, ∃ q : ℚ, o i = (q : ℝ)) →
      ∃ g : ℕ, gridRoot g = j ∧ origin g = o) ∧
    (∀ (j' : ℕ) (k : ℕ) (j : ℕ), ∃ h : ℕ,
      trace j h = bufferedCollarProfile d (z j') (r j') (r j' / (10 * (3 : ℝ) ^ k))) ∧
    letI : ∀ i, Countable (Dcat i) := hDcat
    (conv_represented_estimates d hd model H Ω P NE envE
      ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcE srcRepE ucellE Cext beta alpha eta t {1} I
      ℕ (fun i n omega => catalogResponse i (NE n) (envE n omega)) responseE
      (fun i n omega => catalogConstant i (NE n) (envE n omega)) eventE
      coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey ∧
    conv_represented_estimates d hd model H Ω P NF envF
      ℕ root z r hr Sspace Dcat fcat (fun _ => ℕ) trace traceH1
      usrcF srcRepF ucellF Cext beta alpha eta t {1} I
      ℕ (fun i n omega => catalogResponse i (NF n) (envF n omega)) responseF
      (fun i n omega => catalogConstant i (NF n) (envF n omega)) eventF
      coercivityKey extensionKey lambdaKey
      sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey ℕ origin gridRoot gridKey) ∧
    ∀ jTarget : ℕ, z jTarget = z0 → r jTarget = R0 →
      let Q := fun j => (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))
      let Small := {j : ℕ // Q j ⊆ Q jTarget}
      in_cutoffs_actual_model_output d model H Ω P NE envE Small ⟨jTarget, subset_rfl⟩
        (fun j => z j.val) (fun j => r j.val) (fun j => hr j.val)
        (fun j => Sspace j.val) (fun _ => ℕ) (fun j => trace j.val)
        (fun j => traceH1 j.val) alpha eta t Cgrad 1 orders eventE ∧
      in_cutoffs_actual_model_output d model H Ω P NF envF Small ⟨jTarget, subset_rfl⟩
        (fun j => z j.val) (fun j => r j.val) (fun j => hr j.val)
        (fun j => Sspace j.val) (fun _ => ℕ) (fun j => trace j.val)
        (fun j => traceH1 j.val) alpha eta t Cgrad 1 orders eventF

end SubdiffusiveProcess.Paper
