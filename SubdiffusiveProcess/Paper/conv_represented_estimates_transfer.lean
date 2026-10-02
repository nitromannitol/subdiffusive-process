import SubdiffusiveProcess.Paper.conv_represented_estimates
import SubdiffusiveProcess.Paper.conv_represented_sequence
import SubdiffusiveProcess.Paper.conv_represented_sequence_of_ae_tendsto
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane2.NativeBridge
import SubdiffusiveProcess.Lane2.BoundaryResponse
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Main.CubeFractionalL2Norm

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- **Finite-cutoff catalogue on the original space.**  Verbatim the clauses of
`conv_represented_estimates` for the environment `β` of the original (chaos-law) space and the
finite cutoff `cutoff n`, with the single conjunct that cannot hold along a fixed cutoff sequence
on the original space removed: the pathwise boundedness of the constants (`conv_represented_sequence`).
Every displayed estimate holds on one measurable event `G0` of full chaos measure, for every `n`;
constants are measurable, nonnegative and have the moment bank. Nothing here bounds the constants
along the cutoff sequence. -/
def aux_conv_represented_estimates_transfer_core
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (cutoff : ℕ → ℕ)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (r j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (r j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → BilateralField d → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → BilateralField d → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → BilateralField d →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp constants : Index → ℕ → BilateralField d → ℝ) (G0 : Set (BilateralField d))
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index) :
    Prop :=
  -- A. exponents
  ((d : ℝ) - 1 < t ∧ t < (d : ℝ)) ∧
  (alpha < 1 ∧ 0 < eta ∧ 1 + eta < 2 * alpha) ∧
  (1 / 2 < beta ∧ beta < alpha) ∧
  (0 < Cext) ∧
  (∀ p ∈ orders, 0 < p) ∧
  -- B. representation
  StrictMono cutoff ∧
  InfraredCharacterization M H ∧
  MeasurableSet G0 ∧
  (chaosSampleLaw M).toMeasure G0ᶜ = 0 ∧
  -- C. actual catalog geometry
  (∀ j : J, (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ⊆
      (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d))) ∧
  (∀ (j : J) (i : Fin d), ∃ q : ℚ, z j i = (q : ℝ)) ∧
  (∀ j : J, ∃ k : ℤ, r j = (3 : ℝ) ^ k) ∧
  (∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (∀ i : Fin d, ∃ q : ℚ, z' i = (q : ℝ)) →
      (∃ k : ℤ, r' = (3 : ℝ) ^ k) →
      (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d)) →
      ∃ j : J, z j = z' ∧ r j = r') ∧
  (∀ (g : Grid) (i : Fin d), ∃ q : ℚ, origin g i = (q : ℝ)) ∧
  (∀ j : J, ∃ g : Grid, gridRoot g = j ∧ origin g = z j) ∧
  -- D. pinned killed spaces, source catalogue, trace catalogue, density, plateaus
  (∀ j : J, (S j).space = killedSobolevGraph (centeredCube (z j) (r j) (hr j))) ∧
  (∀ j : J, Dense (D j : Set (DomainL2 (centeredCube (z j) (r j) (hr j))))) ∧
  (∀ j : J, ∀ g : D j,
      ContDiff ℝ ∞ (f j g) ∧
      HasCompactSupport (f j g) ∧
      tsupport (f j g) ⊆ (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ∧
      (g.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))]
            f j g) ∧
  (∀ j : J, ∀ phi : SpatialCoordinates d → ℝ,
      ContDiff ℝ ∞ phi →
      HasCompactSupport phi →
      tsupport phi ⊆
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) →
      ∃ K : Set (SpatialCoordinates d), ∃ g : ℕ → D j,
        IsCompact K ∧
        K ⊆ (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ∧
        tsupport phi ⊆ K ∧
        (∀ n : ℕ, tsupport (f j (g n)) ⊆ K) ∧
        (∀ k : ℕ,
          TendstoUniformly
            (fun n x =>
              iteratedFDeriv ℝ k (fun y => f j (g n) y - phi y) x)
            (fun _ => 0) atTop)) ∧
  (∀ j : J, ∀ h : T j,
      ContDiff ℝ ∞ (theta j h) ∧
      (thetaH1 j h).toFun = theta j h) ∧
  (∀ j : J, ∀ g : D j, ∃ h : T j, theta j h = f j g) ∧
  (∀ j k : J,
      (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) →
      ∀ h : T j, ∃ h' : T k, theta k h' = theta j h) ∧
  (∀ j : J, ∀ b : SpatialCoordinates d → ℝ,
      Lane4.IsHolderOn alpha
          (frontier (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) b →
      IsCellBoundaryClass beta (z j) (r j) b →
      ∃ h : ℕ → T j,
        (∀ k : ℕ, IsCellBoundaryClass beta (z j) (r j) (theta j (h k) - b)) ∧
        Tendsto (fun k : ℕ =>
            cellBoundaryQuotientNorm beta (z j) (r j) (theta j (h k) - b)) atTop (𝓝 0) ∧
        TendstoUniformlyOn (fun k : ℕ => theta j (h k)) b atTop
          (frontier (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))) ∧
  (∀ j : J, ∀ s o : Finset J,
      (⋃ k ∈ s, closure (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ⊆
        (⋃ k ∈ o, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) →
      closure (⋃ k ∈ o, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ⊆
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) →
      ∀ m : ℕ, ∃ h : T j, ∃ V : Set (SpatialCoordinates d),
        IsOpen V ∧
        (⋃ k ∈ s, closure (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ⊆ V ∧
        V ⊆ (⋃ k ∈ o, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d))) ∧
        (∀ x : SpatialCoordinates d, 0 ≤ theta j h x ∧ theta j h x ≤ 1) ∧
        (∀ x ∈ V, theta j h x = 1) ∧
        tsupport (theta j h) ⊆
          (⋃ k ∈ o, (centeredCube (z k) (r k) (hr k) : Set (SpatialCoordinates d)))) ∧
  -- E. moment bank and boundedness
  (∀ (i : Index) (n : ℕ), Measurable (constants i n)) ∧
  (∀ i : Index, ∀ p ∈ orders, ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      MemLp (constants i n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (constants i n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal B) ∧
  (∀ i : Index, ∀ β ∈ G0, ∀ n : ℕ, 0 ≤ constants i n β) ∧
  -- F. actual solutions and responses
  (∀ j : J, ∀ n : ℕ, ∀ β ∈ G0,
      (∀ g : D j,
          usrc j g n β =
              responseSolution (S j)
                (Lane4.cutoffPositiveCoefficient M H β (cutoff n) (z j) (hr j))
                ((sobolevVolumeLoad g.val).comp (S j).space.subtypeL) ∧
          ((usrc j g n β).val.1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))]
            srcRep j g n β ∧
          resp (sourceResponseKey j g) n β =
            inverseResponse (S j)
              (Lane4.cutoffPositiveCoefficient M H β (cutoff n) (z j) (hr j))
              ((sobolevVolumeLoad g.val).comp (S j).space.subtypeL)) ∧
      (∀ h : T j,
          SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn
              (cutoffCoefficient M H β (cutoff n))
              (centeredCube (z j) (r j) (hr j))
              (ucell j h n β) ∧
          SubdiffusiveProcess.CoarseGrainingVocab.HasZeroTraceDifferenceOn (d := d)
              (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))
              (ucell j h n β) (thetaH1 j h) ∧
          ContinuousOn (ucell j h n β).toFun
              (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ frontier (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
              (ucell j h n β).toFun x = theta j h x) ∧
          resp (cellResponseKey j h) n β =
            cellDirichletInfimum
              (cutoffCoefficient M H β (cutoff n))
              (centeredCube (z j) (r j) (hr j)) (thetaH1 j h))) ∧
  -- G. coarse coefficients pinned
  (∀ j : J, ∀ n : ℕ, ∀ β ∈ G0,
      constants (extensionKey j) n β =
        E.Lam (z j) (r j) (hr j)
          (Lane4.cutoffPositiveCoefficient M H β (cutoff n) (z j) (hr j))
          (z j) (r j) ((beta - 1 / 2) / 4) 2 ∧
      constants (lambdaKey j) n β =
        (E.lam (z j) (r j) (hr j)
          (Lane4.cutoffPositiveCoefficient M H β (cutoff n) (z j) (hr j))
          (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ))) ∧
  -- H. eq:mfd-1, killed functions
  (∀ j : J, ∀ n : ℕ, ∀ β ∈ G0, ∀ v : (S j).space,
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) Lane4.threeQuarterOrder
          (fun _ : Fin 1 => v.val.1) < ⊤ ∧
      ‖v.val.1‖ ^ 2 +
          volume.real (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) *
            ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) Lane4.threeQuarterOrder
                (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤
        constants (coercivityKey j) n β *
          responseForm (S j)
            (Lane4.cutoffPositiveCoefficient M H β (cutoff n) (z j) (hr j)) v v) ∧
  -- I. eq:mfd-2, absolute trace estimate
  (∀ j : J, ∀ n : ℕ, ∀ β ∈ G0,
      ∀ e : Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
        ContinuousOn e.toFun
            (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) →
        IsCellBoundaryClass beta (z j) (r j) e.toFun →
        cellDirichletInfimum
            (cutoffCoefficient M H β (cutoff n))
            (centeredCube (z j) (r j) (hr j)) e ≤
          Cext * constants (extensionKey j) n β * (r j) ^ ((d : ℝ) - 2) *
            (cellBoundaryQuotientNorm beta (z j) (r j) e.toFun) ^ 2) ∧
  -- J. eq:mfd-3, rational meshes with the ultraviolet cutoff retained
  (∀ g : Grid, ∀ n : ℕ, ∀ k : ℕ, ∀ j : J, ∀ β ∈ G0,
      k ≤ cutoff n →
      r j = (3 : ℝ) ^ (-(k : ℤ)) →
      (∃ idx : Fin d → ℤ,
          z j = (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * (idx i : ℝ))) →
      (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z (gridRoot g)) (r (gridRoot g)) (hr (gridRoot g)) :
          Set (SpatialCoordinates d)) →
      constants (extensionKey j) n β + constants (lambdaKey j) n β ≤
        constants (gridKey g) n β * (r j) ^ (-eta)) ∧
  -- K. eq:mfd-4 / eq:mfd-5 for the killed source solutions
  (∀ j : J, ∀ g : D j, ∀ n : ℕ, ∀ β ∈ G0,
      (∀ x ∈ closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
        ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict
            (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal
              ((Lane4.cutoffPositiveCoefficient M H β (cutoff n) (z j) (hr j)).val y *
                ∑ i : Fin d, ((usrc j g n β).val.2 i y) ^ 2)))
          (Metric.ball x rr) ≤
        ENNReal.ofReal
          (constants (sourceGrowthKey j g) n β *
            (sSup {v : ℝ |
              ∃ x ∈ closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
                v = |f j g x|}) ^ 2 * rr ^ t)) ∧
      ContinuousOn (srcRep j g n β)
        (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
        srcRep j g n β x = 0) ∧
      Lane4.IsHolderOn alpha
        (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
        (srcRep j g n β) ∧
      Lane4.cAlphaNorm alpha
        (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
        (srcRep j g n β) ≤
        constants (sourceHolderKey j g) n β *
          (sSup {v : ℝ |
            ∃ x ∈ closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
              v = |f j g x|})) ∧
  -- L. eq:mfd-4 and its Holder analogue for the cell solutions
  (∀ j : J, ∀ h : T j, ∀ n : ℕ, ∀ β ∈ G0,
      (∀ x ∈ closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
        ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict
            (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal
              ((Lane4.cutoffPositiveCoefficient M H β (cutoff n) (z j) (hr j)).val y *
                ∑ i : Fin d, (((sobolevDataOfH1 (ucell j h n β)).2 i) y) ^ 2)))
          (Metric.ball x rr) ≤
        ENNReal.ofReal
          (constants (cellGrowthKey j h) n β *
            (Lane4.c2Norm
              (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
              (theta j h)) ^ 2 * rr ^ t)) ∧
      Lane4.IsHolderOn alpha
        (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
        (ucell j h n β).toFun ∧
      Lane4.cAlphaNorm alpha
        (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
        (ucell j h n β).toFun ≤
        constants (cellHolderKey j h) n β *
          Lane4.c2Norm
            (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
            (theta j h))



/-- **Transfer of the finite-cutoff catalogue to a represented sequence.**  Let `env n` be
environments on a probability space, each preserving the chaos law, and `seq` strictly increasing.
If the finite-cutoff catalogue holds on the original space and, almost surely on the represented
space, every response and every constant evaluated along `(seq n, env n ·)` converges, then
`conv_represented_estimates` holds on the represented space for the cutoffs `cutoff (seq n)`, the
environments `env n`, and the composed objects. The pathwise bounds along the represented sequence
come from the convergence of the constants, never from the moment bank. -/
theorem conv_represented_estimates_transfer
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (cutoff : ℕ → ℕ)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (r j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (r j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → BilateralField d → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → BilateralField d → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → BilateralField d →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp constants : Index → ℕ → BilateralField d → ℝ) (G0 : Set (BilateralField d))
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (hcore : aux_conv_represented_estimates_transfer_core d hd M H cutoff J j0 z r hr S D f T
      theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp constants G0
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    {Ωh : Type} [MeasurableSpace Ωh] (Ph : Measure Ωh) [IsProbabilityMeasure Ph]
    (seq : ℕ → ℕ) (hseq : StrictMono seq) (env : ℕ → Ωh → BilateralField d)
    (hmp : ∀ n, MeasurePreserving (env n) Ph (chaosSampleLaw M).toMeasure)
    (hresp : ∀ᵐ w ∂Ph, ∀ i, ∃ l : ℝ,
      Tendsto (fun n => resp i (seq n) (env n w)) atTop (𝓝 l))
    (hconst : ∀ᵐ w ∂Ph, ∀ i, ∃ l : ℝ,
      Tendsto (fun n => constants i (seq n) (env n w)) atTop (𝓝 l)) :
    ∃ (respLim : Index → Ωh → ℝ) (G : Set Ωh),
      conv_represented_estimates d hd M H Ωh Ph (fun n => cutoff (seq n)) env J j0 z r hr S D f T
        theta thetaH1 (fun j g n w => usrc j g (seq n) (env n w))
        (fun j g n w => srcRep j g (seq n) (env n w))
        (fun j h n w => ucell j h (seq n) (env n w)) Cext beta alpha eta t orders E Index
        (fun i n w => resp i (seq n) (env n w)) respLim
        (fun i n w => constants i (seq n) (env n w)) G
        coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
        cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey := by
  classical
  unfold aux_conv_represented_estimates_transfer_core at hcore
  obtain ⟨A1, A2, A3, A4, A5, B1, B2, hG0m, hG0n,
    C1, C2, C3, C4, C5, C6,
    D1, D2, D3, D4, D5, D6, D7, D8, D9,
    E1, E2, E3, hF, hG, hH, hI, hJc, hK, hL⟩ := hcore
  let respLim : Index → Ωh → ℝ := fun i w =>
    if h : ∃ l : ℝ, Tendsto (fun n => resp i (seq n) (env n w)) atTop (𝓝 l) then h.choose else 0
  let constLim : Index → Ωh → ℝ := fun i w =>
    if h : ∃ l : ℝ, Tendsto (fun n => constants i (seq n) (env n w)) atTop (𝓝 l)
    then h.choose else 0
  have hrl : ∀ i, ∀ᵐ w ∂Ph,
      Tendsto (fun n => resp i (seq n) (env n w)) atTop (𝓝 (respLim i w)) := by
    intro i
    filter_upwards [hresp] with w h
    have := h i
    simp only [respLim, dif_pos this]
    exact this.choose_spec
  have hcl : ∀ i, ∀ᵐ w ∂Ph,
      Tendsto (fun n => constants i (seq n) (env n w)) atTop (𝓝 (constLim i w)) := by
    intro i
    filter_upwards [hconst] with w h
    have := h i
    simp only [constLim, dif_pos this]
    exact this.choose_spec
  obtain ⟨G1, hG1⟩ := conv_represented_sequence_of_ae_tendsto Ph
    (fun i n w => resp i (seq n) (env n w)) (fun i n w => constants i (seq n) (env n w))
    respLim constLim hrl hcl
  let G : Set Ωh := G1 ∩ ⋂ n, env n ⁻¹' G0
  have hGmeas : MeasurableSet G :=
    hG1.2.1.inter (MeasurableSet.iInter fun n => (hmp n).measurable hG0m)
  have hGnull : Ph Gᶜ = 0 := by
    have hsub : Gᶜ ⊆ G1ᶜ ∪ ⋃ n, (env n ⁻¹' G0)ᶜ := by
      intro w hw
      simp only [G, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
        not_and, not_forall, Set.mem_union, Set.mem_iUnion] at hw ⊢
      by_cases h1 : w ∈ G1
      · exact Or.inr (hw h1)
      · exact Or.inl h1
    refine measure_mono_null hsub (measure_union_null hG1.2.2.1
      (measure_iUnion_null fun n => ?_))
    rw [← Set.preimage_compl, (hmp n).measure_preimage hG0m.compl.nullMeasurableSet]
    exact hG0n
  have hGmem : ∀ n w, w ∈ G → env n w ∈ G0 := fun n w hw => (Set.mem_iInter.1 hw.2) n
  refine ⟨respLim, G, ?_⟩
  unfold conv_represented_estimates
  refine ⟨A1, A2, A3, A4, A5, B1.comp hseq, B2, fun n => (hmp n).measurable,
    fun n => (hmp n).map_eq,
    ⟨hG1.1, hGmeas, hGnull, fun i w hw => hG1.2.2.2.1 i w hw.1,
      fun i w hw => hG1.2.2.2.2 i w hw.1⟩,
    C1, C2, C3, C4, C5, C6,
    D1, D2, D3, D4, D5, D6, D7, D8, D9,
    fun i n => (E1 i (seq n)).comp (hmp n).measurable,
    fun i p hp => ?_,
    fun i w hw n => E3 i (env n w) (hGmem n w hw) (seq n),
    fun j n w hw => hF j (seq n) (env n w) (hGmem n w hw),
    fun j n w hw => hG j (seq n) (env n w) (hGmem n w hw),
    fun j n w hw v => hH j (seq n) (env n w) (hGmem n w hw) v,
    fun j n w hw e hce hicb => hI j (seq n) (env n w) (hGmem n w hw) e hce hicb,
    fun g n k j w hw hk1 hk2 hk3 => hJc g (seq n) k j (env n w) (hGmem n w hw) hk1 hk2 hk3,
    fun j g n w hw => hK j g (seq n) (env n w) (hGmem n w hw),
    fun j h n w hw => hL j h (seq n) (env n w) (hGmem n w hw)⟩
  obtain ⟨B, hB0, hBall⟩ := E2 i p hp
  refine ⟨B, hB0, fun n => ⟨(hBall (seq n)).1.comp_measurePreserving (hmp n), ?_⟩⟩
  have := eLpNorm_comp_measurePreserving (hBall (seq n)).1.aestronglyMeasurable (hmp n)
    (p := ENNReal.ofReal p)
  simp only [Function.comp_def] at this
  rw [this]
  exact (hBall (seq n)).2

/-- The measurability and moment-bank clauses of the finite-cutoff catalogue. -/
theorem aux_conv_represented_estimates_transfer_core_bank
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (cutoff : ℕ → ℕ)
    (J : Type) [Countable J] [DecidableEq J] (j0 : J)
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j)
    (S : ∀ j, ResponseSpace (centeredCube (z j) (r j) (hr j)))
    (D : ∀ j, Submodule ℚ (DomainL2 (centeredCube (z j) (r j) (hr j))))
    [hDc : ∀ j, Countable (D j)]
    (f : ∀ j, (D j) → SpatialCoordinates d → ℝ)
    (T : J → Type) [hTc : ∀ j, Countable (T j)]
    (theta : ∀ j, T j → SpatialCoordinates d → ℝ)
    (thetaH1 : ∀ j, T j →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (usrc : ∀ j, (D j) → ℕ → BilateralField d → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → BilateralField d → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → BilateralField d →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp constants : Index → ℕ → BilateralField d → ℝ) (G0 : Set (BilateralField d))
    (coercivityKey extensionKey lambdaKey : J → Index)
    (sourceResponseKey sourceGrowthKey sourceHolderKey : ∀ j, (D j) → Index)
    (cellResponseKey cellGrowthKey cellHolderKey : ∀ j, T j → Index)
    (Grid : Type) [Countable Grid]
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (h : aux_conv_represented_estimates_transfer_core d hd M H cutoff J j0 z r hr S D f T
      theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp constants G0
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey) :
    (∀ (i : Index) (n : ℕ), Measurable (constants i n)) ∧
    (∀ i : Index, ∀ p ∈ orders, ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      MemLp (constants i n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (constants i n) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal B) := by
  unfold aux_conv_represented_estimates_transfer_core at h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, E1, E2, -⟩ := h
  exact ⟨E1, E2⟩

end Paper
