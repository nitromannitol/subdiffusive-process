module

public import SubdiffusiveProcess.Paper.goodext_source_upper_arrays
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- Actual finite-cutoff upper coefficients are eventually bounded by twice the
good-event cap times the limiting scalar reference, simultaneously for all cells. -/
theorem goodext_source_upper_goodcells
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
    let upper := fun b n omega => E.Lam (centre b) (side b) (zpow_pos (by norm_num) _)
      (cutoffPositiveCoefficient M H (env n omega) (cutoff n)
        (centre b) (zpow_pos (by norm_num) _))
      (centre b) (side b) ((beta - 1 / 2) / 4) 2
    let Good := fun b => field ⁻¹' gcat_good k0 lambdaLim cell epshom cdet
      (ZL b) (DL b) (loL b) (hiL b) (errL b) (ratL b)
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∀ᵐ omega ∂P, ∀ b,
      0 < ref b omega ∧
      Tendsto (fun n => gcat_sN M H (cutoff (psi n)) (level b : ℤ) (centre b)
        (env (psi n) omega)) atTop (𝓝 (ref b omega)) ∧
      Tendsto (fun n => upper b (psi n) omega) atTop (𝓝 (hiL b (0, fun _ => 1) (field omega) * ref b omega)) ∧
      (omega ∈ Good b →
        ∀ᶠ n in atTop, upper b (psi n) omega ≤ (2 * cell⁻¹) * ref b omega) := by
  intro side ref upper Good
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
  obtain ⟨psi, hpsi, hAll⟩ := goodext_source_upper_arrays d E M H hMH Ω P cutoff
    hCutoff env beta Cells level centre field hfield hEnv hEnvConv eRef heRef hRefLim
    (fun b => hiL b U0) (fun b => hMeas b U0) hHi
  refine ⟨psi, hpsi, ?_⟩
  filter_upwards [hAll] with omega h
  intro b
  refine ⟨(h b).1, (h b).2.1, (h b).2.2.1, ?_⟩
  intro hb
  exact (h b).2.2.2 cell⁻¹ (inv_pos.mpr hcell) (hb.2.1 U0).2
end Paper
