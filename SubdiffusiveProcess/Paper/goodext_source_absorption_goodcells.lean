module

public import SubdiffusiveProcess.Paper.goodext_source_absorption_arrays
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- The actual good-cell arrays supply the uniform source bound on their own
literal good event. The self-root coordinate provides the required upper cap. -/
theorem goodext_source_absorption_goodcells
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hMH : InfraredCharacterization M H)
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
    (z0 : SpatialCoordinates d) (R0 : ℝ) (hR0 : 0 < R0)
    (hRoot : z j0 = z0 ∧ r j0 = R0)
    (Cells : Type) [Countable Cells] (level : Cells → ℕ)
    (centre : Cells → SpatialCoordinates d) (idx : Cells → Fin d → ℤ)
    (hcentre : ∀ b, centre b = fun i => z0 i + (3 : ℝ) ^ (-(level b : ℤ)) * idx b i)
    (hsub : ∀ b, (centeredCube (centre b) ((3 : ℝ) ^ (-(level b : ℤ)))
      (zpow_pos (by norm_num) _) : Set (SpatialCoordinates d)) ⊆
        (centeredCube z0 R0 hR0 : Set (SpatialCoordinates d)))
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure)
    (hEnv : ∀ n, MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure)
    (hEnvConv : ∀ᵐ omega ∂P, Tendsto (fun n => env n omega) atTop (𝓝 (field omega)))
    (eRef : ℕ → ℝ) (heRef : ∀ k, 0 < eRef k)
    (hRefLim : ∀ k : ℕ,
      let kappa : ℕ → ℝ := fun N => Real.exp (((N : ℝ) + 1) *
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
      Tendsto (fun n => kappa (cutoff n - k) / kappa (cutoff n)) atTop (𝓝 (eRef k)))
    (s sigma : ℝ) (hsigma : sigma = (beta - 1 / 2) / 4) (gH cbuf k0 : ℕ)
    (lambdaLim cell epshom cdet : ℝ) (hcell : 0 < cell)
    (Z : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
    (Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal)
    (ZL DL : Cells → ∀ (_U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
      ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
    (loL hiL : Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
    (AEL : Cells → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
    (errL ratL : Cells → Unit → BilateralField d → ℝ)
    (hMeas : ∀ b U, Measurable (hiL b U))
    (hArr : ∀ b, aux_affine_source_cells_env_cellArrays E M H s sigma gH cbuf Z Draw cutoff
      (level b) (centre b) (ZL b) (DL b) (loL b) (hiL b) (AEL b) (errL b) (ratL b)) :
    let side := fun b => (3 : ℝ) ^ (-(level b : ℤ))
    let ref := fun b omega => eRef (level b) * Real.exp
      (H (field omega) (centre b) + ∑ j ∈ Finset.range (level b), (field omega) (-(j : ℤ)) (centre b))
    let Good := fun b => field ⁻¹' gcat_good k0 lambdaLim cell epshom cdet
      (ZL b) (DL b) (loL b) (hiL b) (errL b) (ratL b)
    ∃ K : Ω → ℝ, (∀ omega, 0 ≤ K omega) ∧ ∀ᵐ omega ∂P,
      (∀ b, omega ∈ Good b → (ref b omega)⁻¹ ≤ K omega * side b ^ (-eta)) ∧
      ∀ fsup c : ℝ, 0 < c → ∃ r0 : ℝ, 0 < r0 ∧ ∀ b,
        side b ≤ r0 → omega ∈ Good b →
        (ref b omega)⁻¹ * side b ^ ((d : ℝ) + 2) * fsup ^ 2 ≤ c * side b ^ d := by
  intro side ref Good
  let U0 : Fin 3 × (Fin d → Fin 3) := (0, fun _ => 1)
  have hRootLevel : ∀ k, gcat_rootLevel gH k U0 = (k : ℤ) := by
    intro k
    simp only [U0, gcat_rootLevel, gcat_factor, Matrix.cons_val_zero, Nat.cast_zero, sub_zero]
  have hRootCentre : ∀ k z, gcat_rootCentre gH k z U0 = z := by
    intro k z
    have hshift : gcat_shift U0.2 = 0 := by
      funext i
      simp only [gcat_shift, U0, Fin.val_one, Nat.cast_one, sub_self, zero_div, Pi.zero_apply]
    simp only [gcat_rootCentre, hshift, smul_zero, add_zero]
  have hHi : ∀ b, TendstoInMeasure (chaosSampleLaw M).toMeasure (fun n omega =>
      E.Lam (centre b) (side b) (zpow_pos (by norm_num) _)
        (cutoffPositiveCoefficient M H omega (cutoff n) (centre b) (zpow_pos (by norm_num) _))
        (centre b) (side b) ((beta - 1 / 2) / 4) 2 /
        gcat_sN M H (cutoff n) (level b : ℤ) (centre b) omega) atTop (hiL b U0) := by
    intro b
    let norm : ℤ → SpatialCoordinates d → ℕ → BilateralField d → ℝ := fun ell w n omega =>
      E.Lam w ((3 : ℝ) ^ (-ell)) (zpow_pos (by norm_num) _)
        (cutoffPositiveCoefficient M H omega (cutoff n) w (zpow_pos (by norm_num) _))
        w ((3 : ℝ) ^ (-ell)) sigma 2 / gcat_sN M H (cutoff n) ell w omega
    have h : TendstoInMeasure (chaosSampleLaw M).toMeasure
        (norm (gcat_rootLevel gH (level b) U0) (gcat_rootCentre gH (level b) (centre b) U0))
        atTop (hiL b U0) := (hArr b).2.2.2.1 U0
    rw [hRootLevel, hRootCentre] at h
    simpa only [norm, side, hsigma] using h
  obtain ⟨K, hK, hAll⟩ := goodext_source_absorption_arrays d hd M H hMH Ω P cutoff env
    J j0 z r hr S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E
    Index resp respLim constants G coercivityKey extensionKey lambdaKey sourceResponseKey
    sourceGrowthKey sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin
    gridRoot gridKey hRep z0 R0 hR0 hRoot Cells level centre idx hcentre hsub field hfield
    hEnv hEnvConv eRef heRef hRefLim (fun b => hiL b U0) (fun b => hMeas b U0) hHi
    cell⁻¹ (inv_nonneg.mpr hcell.le)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hAll] with omega h
  have hgood : ∀ b, omega ∈ Good b → hiL b U0 (field omega) ≤ cell⁻¹ :=
    fun b hb => (hb.2.1 U0).2
  refine ⟨fun b hb => h.1 b (hgood b hb), ?_⟩
  intro fsup c hc
  obtain ⟨r0, hr0, hsmall⟩ := h.2 fsup c hc
  exact ⟨r0, hr0, fun b hb hg => hsmall b hb (hgood b hg)⟩

end Paper
