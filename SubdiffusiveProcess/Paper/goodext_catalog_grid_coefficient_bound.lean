module

public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.goodext_cutoff_ellipticity_locality

@[expose] public section




open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper

/-- A finite family of represented grid constants bounds every guarded cell in those grids. -/
theorem goodext_catalog_grid_coefficient_bound
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
    (origin : Grid → SpatialCoordinates d) (gridRoot : Grid → J) (gridKey : Grid → Index)
    (hRep : conv_represented_estimates d hd M H Ω P cutoff env J j0 z r hr S D f T theta
      thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim constants G
      coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
      cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey)
    (m : ℕ) (gridChoice : Fin m → Grid) (hGridChoice : ∀ i, gridRoot (gridChoice i) = j0) :
    ∀ om ∈ G, ∃ K : ℝ, 0 ≤ K ∧ ∀ (n k : ℕ) (i : Fin m) (idx : Fin d → ℤ),
      k ≤ cutoff n →
      let wc : SpatialCoordinates d := fun a => origin (gridChoice i) a + (3 : ℝ) ^ (-(k : ℤ)) * idx a
      let rc : ℝ := (3 : ℝ) ^ (-(k : ℤ))
      ∀ hc : 0 < rc,
      (centeredCube wc rc hc : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z j0) (r j0) (hr j0) : Set (SpatialCoordinates d)) →
      E.Lam wc rc hc (cutoffPositiveCoefficient M H (env n om) (cutoff n) wc hc)
        wc rc ((beta - 1 / 2) / 4) 2 +
        (E.lam wc rc hc (cutoffPositiveCoefficient M H (env n om) (cutoff n) wc hc)
          wc rc ((beta - 1 / 2) / 4) 2)⁻¹ ≤ K * rc ^ (-eta) := by
  intro om hom
  unfold conv_represented_estimates at hRep
  rcases hRep with
    ⟨_, hAlpha, hBeta, _, _, _, _, _, _, hSeq,
      _, _, _, hCover, hGridRat,
      _, _, _, _, _, _, _, _, _, _, _, _,
      hConstNonneg, _, hPinned, _, _, hGridClause, _, _⟩
  rcases hSeq with ⟨_, _, _, _, hConstBound⟩
  let rawBound : Fin m → ℝ := fun i =>
    Classical.choose (hConstBound (gridKey (gridChoice i)) om hom)
  let B : Fin m → ℝ := fun i => max 0 (rawBound i)
  have hRawBound : ∀ i n, |constants (gridKey (gridChoice i)) n om| ≤ rawBound i := by
    intro i n
    dsimp only [rawBound]
    exact Classical.choose_spec (hConstBound (gridKey (gridChoice i)) om hom) n
  have hBnonneg : ∀ i, 0 ≤ B i := by
    intro i
    dsimp only [B]
    exact le_max_left 0 (rawBound i)
  have hBcontrol : ∀ i n, constants (gridKey (gridChoice i)) n om ≤ B i := by
    intro i n
    dsimp only [B]
    calc
      constants (gridKey (gridChoice i)) n om ≤
          |constants (gridKey (gridChoice i)) n om| := le_abs_self _
      _ ≤ rawBound i := hRawBound i n
      _ ≤ max 0 (rawBound i) := le_max_right _ _
  let K : ℝ := ∑ i : Fin m, B i
  have hKnonneg : 0 ≤ K := by
    dsimp only [K]
    exact Finset.sum_nonneg (fun i hi => hBnonneg i)
  have hBleK : ∀ i : Fin m, B i ≤ K := by
    intro i
    dsimp only [K]
    exact Finset.single_le_sum (fun j hj => hBnonneg j) (Finset.mem_univ i)
  have hGridBound : ∀ i n, constants (gridKey (gridChoice i)) n om ≤ K := by
    intro i n
    exact le_trans (hBcontrol i n) (hBleK i)
  refine ⟨K, hKnonneg, ?_⟩
  intro n k i idx hk
  dsimp only
  intro hc hsub
  let wc : SpatialCoordinates d := fun a =>
    origin (gridChoice i) a + (3 : ℝ) ^ (-(k : ℤ)) * idx a
  let rc : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  have hCenterRat : ∀ a : Fin d, ∃ q : ℚ, wc a = (q : ℝ) := by
    intro a
    rcases hGridRat (gridChoice i) a with ⟨q, hq⟩
    refine ⟨q + (3 : ℚ) ^ (-(k : ℤ)) * (idx a : ℚ), ?_⟩
    dsimp only [wc]
    rw [hq]
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_zpow, Rat.cast_intCast,
      Rat.cast_ofNat]
  obtain ⟨j, hjz, hjr⟩ :=
    hCover wc rc hc hCenterRat ⟨-(k : ℤ), rfl⟩ hsub
  have hRootSub :
      (centeredCube wc rc hc : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z (gridRoot (gridChoice i)))
          (r (gridRoot (gridChoice i))) (hr (gridRoot (gridChoice i))) :
            Set (SpatialCoordinates d)) := by
    simpa only [hGridChoice i] using hsub
  have hjrTri : r j = (3 : ℝ) ^ (-(k : ℤ)) := by
    simpa only [rc] using hjr
  have hjIndex : ∃ idx' : Fin d → ℤ,
      z j = fun a => origin (gridChoice i) a +
        (3 : ℝ) ^ (-(k : ℤ)) * (idx' a : ℝ) := by
    refine ⟨idx, ?_⟩
    simpa only [wc] using hjz
  have hJSub :
      (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z (gridRoot (gridChoice i)))
          (r (gridRoot (gridChoice i))) (hr (gridRoot (gridChoice i))) :
            Set (SpatialCoordinates d)) := by
    simpa only [hjz, hjr] using hRootSub
  have hJ := hGridClause (gridChoice i) n k j om hom hk hjrTri hjIndex hJSub
  have hJ' : constants (extensionKey j) n om + constants (lambdaKey j) n om ≤
      constants (gridKey (gridChoice i)) n om * rc ^ (-eta) := by
    simpa only [hjr] using hJ
  rcases hPinned j n om hom with ⟨hExt, hInv⟩
  have hSigma : ((beta - 1 / 2) / 4) ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · linarith only [hBeta.1]
    · have hBetaLtOne : beta < 1 := lt_trans hBeta.2 hAlpha.1
      linarith only [hBetaLtOne]
  have hLocalSub :
      (centeredCube wc rc hc : Set (SpatialCoordinates d)) ⊆
        (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) := by
    simpa only [hjz, hjr] using
      (Set.Subset.rfl :
        (centeredCube wc rc hc : Set (SpatialCoordinates d)) ⊆
          (centeredCube wc rc hc : Set (SpatialCoordinates d)))
  letI instNeZeroD : NeZero d :=
    NeZero.of_gt (lt_of_lt_of_le (Nat.zero_lt_succ 1) hd)
  have hLocal := goodext_cutoff_ellipticity_locality E M H (env n om) (cutoff n)
    (z j) (r j) (hr j) wc rc hc hLocalSub ((beta - 1 / 2) / 4) hSigma
  have hExtCell : constants (extensionKey j) n om =
      E.Lam (z j) (r j) (hr j)
        (cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j))
        wc rc ((beta - 1 / 2) / 4) 2 := by
    simpa only [hjz, hjr] using hExt
  have hExt' : constants (extensionKey j) n om =
      E.Lam wc rc hc
        (cutoffPositiveCoefficient M H (env n om) (cutoff n) wc hc)
        wc rc ((beta - 1 / 2) / 4) 2 := by
    calc
      constants (extensionKey j) n om =
          E.Lam (z j) (r j) (hr j)
            (cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j))
            wc rc ((beta - 1 / 2) / 4) 2 := hExtCell
      _ = E.Lam wc rc hc
          (cutoffPositiveCoefficient M H (env n om) (cutoff n) wc hc)
          wc rc ((beta - 1 / 2) / 4) 2 := hLocal.1
  have hInvCell : constants (lambdaKey j) n om =
      (E.lam (z j) (r j) (hr j)
        (cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j))
        wc rc ((beta - 1 / 2) / 4) 2)⁻¹ := by
    simpa only [hjz, hjr, Real.rpow_neg_one] using hInv
  have hInv' : constants (lambdaKey j) n om =
      (E.lam wc rc hc
        (cutoffPositiveCoefficient M H (env n om) (cutoff n) wc hc)
        wc rc ((beta - 1 / 2) / 4) 2)⁻¹ := by
    calc
      constants (lambdaKey j) n om =
          (E.lam (z j) (r j) (hr j)
            (cutoffPositiveCoefficient M H (env n om) (cutoff n) (z j) (hr j))
            wc rc ((beta - 1 / 2) / 4) 2)⁻¹ := hInvCell
      _ = _ := hLocal.2
  calc
    E.Lam wc rc hc
        (cutoffPositiveCoefficient M H (env n om) (cutoff n) wc hc)
        wc rc ((beta - 1 / 2) / 4) 2 +
        (E.lam wc rc hc
          (cutoffPositiveCoefficient M H (env n om) (cutoff n) wc hc)
          wc rc ((beta - 1 / 2) / 4) 2)⁻¹ =
        constants (extensionKey j) n om + constants (lambdaKey j) n om := by
          rw [← hExt', ← hInv']
    _ ≤ constants (gridKey (gridChoice i)) n om * rc ^ (-eta) := hJ'
    _ ≤ K * rc ^ (-eta) :=
      mul_le_mul_of_nonneg_right (hGridBound i n) (Real.rpow_nonneg hc.le _)

end Paper
