module

public import SubdiffusiveProcess.Sobolev.ResponseLimits
public import SubdiffusiveProcess.Variational.PositiveShift
public import SubdiffusiveProcess.Variational.DualEnergyApproximation
public import SubdiffusiveProcess.Compactness.RecoverySequence
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology
namespace SubdiffusiveProcess

/-- Every finite dual-energy vector has an actual Sobolev recovery sequence, retaining every cutoff. -/
theorem exists_responseForm_recoverySequence
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a : ℕ → PositiveCoefficient Ω)
    (G : DomainL2 Ω →L[ℝ] DomainL2 Ω)
    (hsym : ∀ x y : DomainL2 Ω, inner ℝ (G x) y = inner ℝ x (G y))
    (hpos : ∀ x : DomainL2 Ω, 0 ≤ inner ℝ x (G x))
    (hstrong : ∀ f : DomainL2 Ω,
      Tendsto (fun n => (responseSolution S (a n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) atTop (𝓝 (G f)))
    (u : DomainL2 Ω)
    (hu : (⨆ f : DomainL2 Ω, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)) < ⊤) :
    ∃ w : ℕ → S.space,
      Tendsto (fun n => ((w n).val.1,
        ((responseForm S (a n) (w n) (w n) : ℝ) : EReal)))
        atTop (𝓝 (u, ⨆ f : DomainL2 Ω,
          ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal))) := by
  let E : EReal :=
    ⨆ f : DomainL2 Ω, ((2 * inner ℝ f u - inner ℝ f (G f) : ℝ) : EReal)
  have hE_nonneg : (0 : EReal) ≤ E := by
    exact le_iSup_of_le (0 : DomainL2 Ω) (by simp)
  have hE_ne_top : E ≠ ⊤ := ne_of_lt hu
  have hE_ne_bot : E ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hE_nonneg)
  lift E to ℝ using ⟨hE_ne_top, hE_ne_bot⟩ with e he
  have hInv (n : ℕ) : ∃ R : DomainL2 Ω →L[ℝ] DomainL2 Ω,
      (G + (1 / (n + 1 : ℝ)) • ContinuousLinearMap.id ℝ (DomainL2 Ω)).comp R =
        ContinuousLinearMap.id ℝ (DomainL2 Ω) := by
    obtain ⟨R, hR, _⟩ := existsUnique_positive_shift_inverse G hsym hpos
      (1 / (n + 1 : ℝ)) (by positivity)
    exact ⟨R, hR.1⟩
  choose R hR using hInv
  have happ := tendsto_positive_shift_energy_approximation G R hsym hpos hR u e (by
    simpa [E] using he.symm)
  have huR : Tendsto (fun n => G (R n u)) atTop (𝓝 u) := by
    exact happ.fst_nhds
  have heR : Tendsto (fun n => inner ℝ (R n u) (G (R n u))) atTop (𝓝 e) := by
    exact happ.snd_nhds.fst_nhds
  let v : ℕ → ℕ → S.space := fun j n =>
    responseSolution S (a n) ((sobolevVolumeLoad (R j u)).comp S.space.subtypeL)
  have hv (j : ℕ) : Tendsto
      (fun n => ((v j n).val.1, responseForm S (a n) (v j n) (v j n))) atTop
      (𝓝 (G (R j u), inner ℝ (R j u) (G (R j u)))) := by
    have hL2 := hstrong (R j u)
    have henergy : Tendsto (fun n => responseForm S (a n) (v j n) (v j n)) atTop
        (𝓝 (inner ℝ (R j u) (G (R j u)))) := by
      simp only [v, responseSolution_spec]
      exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => R j u) atTop
        (𝓝 (R j u))).inner (𝕜 := ℝ) hL2
    exact hL2.prodMk_nhds henergy
  obtain ⟨w, hw⟩ := exists_recoverySequence_of_approximations
    (fun z : S.space => z.val.1) (fun n z => responseForm S (a n) z z)
    (fun j => G (R j u)) (fun j => inner ℝ (R j u) (G (R j u))) v u e huR heR hv
  refine ⟨w, ?_⟩
  have hw' := hw.fst_nhds.prodMk_nhds (EReal.tendsto_coe.mpr hw.snd_nhds)
  simpa only [E, he] using hw'

end SubdiffusiveProcess
