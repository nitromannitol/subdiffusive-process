import SubdiffusiveProcess.Paper.goodext_grid_reference_cap
import SubdiffusiveProcess.Paper.density_source_absorption
import SubdiffusiveProcess.Paper.affine_source_cells_env
import SubdiffusiveProcess.Paper.represented_infrared_subsequence
import SubdiffusiveProcess.Paper.conv_represented_estimates_subseq

/-! Actual array limits and the represented grid bound give a uniform source-absorption mesh. -/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper
/-- The actual scalar reference and upper-normalization limits are transported
on a common infrared refinement, before using any represented coefficient cap. -/
theorem aux_goodext_source_absorption_arrays_limits
    (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hMH : InfraredCharacterization M H)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (cutoff : ℕ → ℕ) (hCutoff : StrictMono cutoff) (env : ℕ → Ω → BilateralField d)
    (beta : ℝ) (Cells : Type) [Countable Cells] (level : Cells → ℕ)
    (centre : Cells → SpatialCoordinates d)
    (field : Ω → BilateralField d)
    (hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure)
    (hEnv : ∀ n, MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure)
    (hEnvConv : ∀ᵐ omega ∂P, Tendsto (fun n => env n omega) atTop (𝓝 (field omega)))
    (eRef : ℕ → ℝ) (heRef : ∀ k, 0 < eRef k)
    (hRefLim : ∀ k : ℕ,
      let kappa : ℕ → ℝ := fun N => Real.exp (((N : ℝ) + 1) *
        SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
      Tendsto (fun n => kappa (cutoff n - k) / kappa (cutoff n)) atTop (𝓝 (eRef k)))
    (hi : Cells → BilateralField d → ℝ) (hMeas : ∀ b, Measurable (hi b))
    (hHi : ∀ b, TendstoInMeasure (chaosSampleLaw M).toMeasure (fun n omega =>
      E.Lam (centre b) ((3 : ℝ) ^ (-(level b : ℤ))) (zpow_pos (by norm_num) _)
        (cutoffPositiveCoefficient M H omega (cutoff n) (centre b) (zpow_pos (by norm_num) _))
        (centre b) ((3 : ℝ) ^ (-(level b : ℤ))) ((beta - 1 / 2) / 4) 2 /
        gcat_sN M H (cutoff n) (level b : ℤ) (centre b) omega) atTop (hi b))
    :
    let side := fun b => (3 : ℝ) ^ (-(level b : ℤ))
    let ref := fun b omega => eRef (level b) * Real.exp
      (H (field omega) (centre b) + ∑ j ∈ Finset.range (level b), (field omega) (-(j : ℤ)) (centre b))
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ ( ∀ b, ∀ᵐ omega ∂P, 0 < ref b omega ∧
      Tendsto (fun n => gcat_sN M H (cutoff (psi n)) (level b : ℤ) (centre b)
        (env (psi n) omega)) atTop (𝓝 (ref b omega))) ∧ ( ∀ b, TendstoInMeasure P (fun n omega =>
      E.Lam (centre b) (side b) (zpow_pos (by norm_num) _)
        (cutoffPositiveCoefficient M H (env (psi n) omega) (cutoff (psi n))
          (centre b) (zpow_pos (by norm_num) _))
        (centre b) (side b) ((beta - 1 / 2) / 4) 2 /
        gcat_sN M H (cutoff (psi n)) (level b : ℤ) (centre b) (env (psi n) omega))
      atTop (fun omega => hi b (field omega))) := by
  intro side ref
  obtain ⟨psi, hpsi, hIR⟩ := represented_infrared_subsequence M H hMH P field hfield
    PUnit Cells (fun _ => env) (fun _ => hEnv) (hEnvConv.mono fun omega h _ => h) centre
  have hScale : ∀ b, ∀ᵐ omega ∂P, 0 < ref b omega ∧
      Tendsto (fun n => gcat_sN M H (cutoff (psi n)) (level b : ℤ) (centre b)
        (env (psi n) omega)) atTop (𝓝 (ref b omega)) := by
    intro b
    filter_upwards [hEnvConv, hIR] with omega henv hir
    refine ⟨mul_pos (heRef _) (Real.exp_pos _), ?_⟩
    exact aux_affine_source_cells_env_sN_tendsto M H (fun n => cutoff (psi n))
      (hCutoff.comp hpsi) eRef
      (fun k => by simpa only [Int.toNat_sub, Int.toNat_natCast] using
        (hRefLim k).comp hpsi.tendsto_atTop)
      (level b) (centre b) (fun n => env (psi n) omega) (field omega)
      (henv.comp hpsi.tendsto_atTop) (hir PUnit.unit b)
  have hNorm : ∀ b, TendstoInMeasure P (fun n omega =>
      E.Lam (centre b) (side b) (zpow_pos (by norm_num) _)
        (cutoffPositiveCoefficient M H (env (psi n) omega) (cutoff (psi n))
          (centre b) (zpow_pos (by norm_num) _))
        (centre b) (side b) ((beta - 1 / 2) / 4) 2 /
        gcat_sN M H (cutoff (psi n)) (level b : ℤ) (centre b) (env (psi n) omega))
      atTop (fun omega => hi b (field omega)) := fun b =>
    represented_same_law_in_measure
      (X := fun n omega =>
        E.Lam (centre b) (side b) (zpow_pos (by norm_num) _)
          (cutoffPositiveCoefficient M H omega (cutoff (psi n))
            (centre b) (zpow_pos (by norm_num) _))
          (centre b) (side b) ((beta - 1 / 2) / 4) 2 /
          gcat_sN M H (cutoff (psi n)) (level b : ℤ) (centre b) omega)
      (V := hi b) (Y := fun n => env (psi n)) (Y0 := field)
      (fun n => hEnv (psi n)) hfield
      (hEnvConv.mono fun omega h => h.comp hpsi.tendsto_atTop)
      (hMeas b).aestronglyMeasurable ((hHi b).comp hpsi.tendsto_atTop)
  exact ⟨psi, hpsi, hScale, hNorm⟩

/-- The literal original-space upper-normalization limits and actual represented
root-grid bounds supply a uniform source-absorption mesh. Infrared convergence and
transport through changing environments are constructed internally. -/
theorem goodext_source_absorption_arrays
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
    (hi : Cells → BilateralField d → ℝ) (hMeas : ∀ b, Measurable (hi b))
    (hHi : ∀ b, TendstoInMeasure (chaosSampleLaw M).toMeasure (fun n omega =>
      E.Lam (centre b) ((3 : ℝ) ^ (-(level b : ℤ))) (zpow_pos (by norm_num) _)
        (cutoffPositiveCoefficient M H omega (cutoff n) (centre b) (zpow_pos (by norm_num) _))
        (centre b) ((3 : ℝ) ^ (-(level b : ℤ))) ((beta - 1 / 2) / 4) 2 /
        gcat_sN M H (cutoff n) (level b : ℤ) (centre b) omega) atTop (hi b))
    (cap : ℝ) (hcap : 0 ≤ cap) :
    let side := fun b => (3 : ℝ) ^ (-(level b : ℤ))
    let ref := fun b omega => eRef (level b) * Real.exp
      (H (field omega) (centre b) + ∑ j ∈ Finset.range (level b), (field omega) (-(j : ℤ)) (centre b))
    ∃ K : Ω → ℝ, (∀ omega, 0 ≤ K omega) ∧ ∀ᵐ omega ∂P,
      (∀ b, hi b (field omega) ≤ cap → (ref b omega)⁻¹ ≤ K omega * side b ^ (-eta)) ∧
      ∀ fsup c : ℝ, 0 < c → ∃ r0 : ℝ, 0 < r0 ∧ ∀ b,
        side b ≤ r0 → hi b (field omega) ≤ cap →
        (ref b omega)⁻¹ * side b ^ ((d : ℝ) + 2) * fsup ^ 2 ≤ c * side b ^ d := by
  intro side ref
  have hCutoff : StrictMono cutoff := hRep.2.2.2.2.2.1
  have heta2 : eta < 2 := by
    have h := hRep.2.1
    linarith only [h.1, h.2.2]
  obtain ⟨psi, hpsi, hScale, hNorm⟩ := aux_goodext_source_absorption_arrays_limits d E M H hMH
    Ω P cutoff hCutoff env beta Cells level centre field hfield hEnv hEnvConv eRef heRef hRefLim hi hMeas hHi
  have hRepSub := conv_represented_estimates_subseq d hd M H Ω P cutoff env J j0 z r hr
    S D f T theta thetaH1 usrc srcRep ucell Cext beta alpha eta t orders E Index resp respLim
    constants G coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey
    sourceHolderKey cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey
    hRep psi hpsi
  obtain ⟨K, hK, hAll⟩ := goodext_grid_reference_cap d hd M H Ω P
    (fun n => cutoff (psi n)) (fun n => env (psi n)) J j0 z r hr S D f T theta thetaH1
    (fun j f n => usrc j f (psi n)) (fun j f n => srcRep j f (psi n))
    (fun j t n => ucell j t (psi n)) Cext beta alpha eta t orders E Index
    (fun i n => resp i (psi n)) respLim (fun i n => constants i (psi n)) G
    coercivityKey extensionKey lambdaKey sourceResponseKey sourceGrowthKey sourceHolderKey
    cellResponseKey cellGrowthKey cellHolderKey Grid origin gridRoot gridKey hRepSub
    z0 R0 hR0 hRoot Cells level centre idx hcentre hsub
    (fun b n omega => gcat_sN M H (cutoff (psi n)) (level b : ℤ) (centre b) (env (psi n) omega))
    ref (fun b omega => hi b (field omega)) cap hScale hNorm
  refine ⟨(fun omega => K omega * cap), (fun omega => mul_nonneg (hK omega) hcap), ?_⟩
  filter_upwards [hAll] with omega h
  have hBound : ∀ b, hi b (field omega) ≤ cap →
      (ref b omega)⁻¹ ≤ (K omega * cap) * side b ^ (-eta) := by
    intro b hb
    exact (h b hb).trans_eq (by ring)
  refine ⟨hBound, fun fsup c hc => ?_⟩
  exact density_source_absorption d eta (K omega * cap) fsup c heta2
    (mul_nonneg (hK omega) hcap) hc side (fun b => ref b omega)
    (fun _ => zpow_pos (by norm_num) _) (fun b => hi b (field omega) ≤ cap) hBound

end Paper
