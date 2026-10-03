module

public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Lane2.NativeBridge
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Metric
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



def conv_represented_estimates
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
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
    (usrc : ∀ j, (D j) → ℕ → Ω → (S j).space)
    (srcRep : ∀ j, (D j) → ℕ → Ω → SpatialCoordinates d → ℝ)
    (ucell : ∀ j, T j → ℕ → Ω →
      Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
    (Cext : ℝ) (beta alpha eta t : ℝ) (orders : Finset ℝ)
    (E : Paper.in_J d)
    (Index : Type) [Countable Index]
    (resp : Index → ℕ → Ω → ℝ) (respLim : Index → Ω → ℝ)
    (constants : Index → ℕ → Ω → ℝ) (G : Set Ω)
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
  (∀ n : ℕ, Measurable (env n)) ∧
  (∀ n : ℕ, Measure.map (env n) P = (chaosSampleLaw M).toMeasure) ∧
  Paper.conv_represented_sequence P resp respLim constants G ∧
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
      MemLp (constants i n) (ENNReal.ofReal p) P ∧
      eLpNorm (constants i n) (ENNReal.ofReal p) P ≤ ENNReal.ofReal B) ∧
  (∀ i : Index, ∀ om ∈ G, ∀ n : ℕ, 0 ≤ constants i n om) ∧
  -- F. actual solutions and responses
  (∀ j : J, ∀ n : ℕ, ∀ om ∈ G,
      (∀ g : D j,
          usrc j g n om =
              responseSolution (S j)
                (Lane4.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j))
                ((sobolevVolumeLoad g.val).comp (S j).space.subtypeL) ∧
          ((usrc j g n om).val.1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))]
            srcRep j g n om ∧
          resp (sourceResponseKey j g) n om =
            inverseResponse (S j)
              (Lane4.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j))
              ((sobolevVolumeLoad g.val).comp (S j).space.subtypeL)) ∧
      (∀ h : T j,
          SubdiffusiveProcess.CoarseGrainingVocab.IsWeaklyHarmonicOn
              (cutoffCoefficient M H (env n om) (cutoff n))
              (centeredCube (z j) (r j) (hr j))
              (ucell j h n om) ∧
          SubdiffusiveProcess.CoarseGrainingVocab.HasZeroTraceDifferenceOn (d := d)
              (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))
              (ucell j h n om) (thetaH1 j h) ∧
          ContinuousOn (ucell j h n om).toFun
              (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ frontier (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
              (ucell j h n om).toFun x = theta j h x) ∧
          resp (cellResponseKey j h) n om =
            cellDirichletInfimum
              (cutoffCoefficient M H (env n om) (cutoff n))
              (centeredCube (z j) (r j) (hr j)) (thetaH1 j h))) ∧
  -- G. coarse coefficients pinned
  (∀ j : J, ∀ n : ℕ, ∀ om ∈ G,
      constants (extensionKey j) n om =
        E.Lam (z j) (r j) (hr j)
          (Lane4.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j))
          (z j) (r j) ((beta - 1 / 2) / 4) 2 ∧
      constants (lambdaKey j) n om =
        (E.lam (z j) (r j) (hr j)
          (Lane4.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j))
          (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ))) ∧
  -- H. eq:mfd-1, killed functions
  (∀ j : J, ∀ n : ℕ, ∀ om ∈ G, ∀ v : (S j).space,
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j) Lane4.threeQuarterOrder
          (fun _ : Fin 1 => v.val.1) < ⊤ ∧
      ‖v.val.1‖ ^ 2 +
          volume.real (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) *
            ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j) Lane4.threeQuarterOrder
                (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤
        constants (coercivityKey j) n om *
          responseForm (S j)
            (Lane4.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j)) v v) ∧
  -- I. eq:mfd-2, absolute trace estimate
  (∀ j : J, ∀ n : ℕ, ∀ om ∈ G,
      ∀ e : Homogenization.H1Function
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
        ContinuousOn e.toFun
            (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) →
        IsCellBoundaryClass beta (z j) (r j) e.toFun →
        cellDirichletInfimum
            (cutoffCoefficient M H (env n om) (cutoff n))
            (centeredCube (z j) (r j) (hr j)) e ≤
          Cext * constants (extensionKey j) n om * (r j) ^ ((d : ℝ) - 2) *
            (cellBoundaryQuotientNorm beta (z j) (r j) e.toFun) ^ 2) ∧
  -- J. eq:mfd-3, rational meshes with the ultraviolet cutoff retained
  (∀ g : Grid, ∀ n : ℕ, ∀ k : ℕ, ∀ j : J, ∀ om ∈ G,
      k ≤ cutoff n →
      r j = (3 : ℝ) ^ (-(k : ℤ)) →
      (∃ idx : Fin d → ℤ,
          z j = (fun i => origin g i + (3 : ℝ) ^ (-(k : ℤ)) * (idx i : ℝ))) →
      (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z (gridRoot g)) (r (gridRoot g)) (hr (gridRoot g)) :
          Set (SpatialCoordinates d)) →
      constants (extensionKey j) n om + constants (lambdaKey j) n om ≤
        constants (gridKey g) n om * (r j) ^ (-eta)) ∧
  -- K. eq:mfd-4 / eq:mfd-5 for the killed source solutions
  (∀ j : J, ∀ g : D j, ∀ n : ℕ, ∀ om ∈ G,
      (∀ x ∈ closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
        ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict
            (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal
              ((Lane4.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j)).val y *
                ∑ i : Fin d, ((usrc j g n om).val.2 i y) ^ 2)))
          (Metric.ball x rr) ≤
        ENNReal.ofReal
          (constants (sourceGrowthKey j g) n om *
            (sSup {v : ℝ |
              ∃ x ∈ closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
                v = |f j g x|}) ^ 2 * rr ^ t)) ∧
      ContinuousOn (srcRep j g n om)
        (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))) ∧
      (∀ x ∈ frontier (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
        srcRep j g n om x = 0) ∧
      Lane4.IsHolderOn alpha
        (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
        (srcRep j g n om) ∧
      Lane4.cAlphaNorm alpha
        (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
        (srcRep j g n om) ≤
        constants (sourceHolderKey j g) n om *
          (sSup {v : ℝ |
            ∃ x ∈ closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
              v = |f j g x|})) ∧
  -- L. eq:mfd-4 and its Holder analogue for the cell solutions
  (∀ j : J, ∀ h : T j, ∀ n : ℕ, ∀ om ∈ G,
      (∀ x ∈ closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)),
        ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
        ((volume.restrict
            (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d))).withDensity
            (fun y => ENNReal.ofReal
              ((Lane4.cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j)).val y *
                ∑ i : Fin d, (((sobolevDataOfH1 (ucell j h n om)).2 i) y) ^ 2)))
          (Metric.ball x rr) ≤
        ENNReal.ofReal
          (constants (cellGrowthKey j h) n om *
            (Lane4.c2Norm
              (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
              (theta j h)) ^ 2 * rr ^ t)) ∧
      Lane4.IsHolderOn alpha
        (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
        (ucell j h n om).toFun ∧
      Lane4.cAlphaNorm alpha
        (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
        (ucell j h n om).toFun ≤
        constants (cellHolderKey j h) n om *
          Lane4.c2Norm
            (closure (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)))
            (theta j h))

end Paper
