import SubdiffusiveProcess.Paper.reference_coefficients
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped Topology BigOperators ENNReal NNReal
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Paper
/-- Both deterministic reference sequences converge along one common refinement.
In particular the shared represented environment is reindexed in the same way
for the two candidates. No ratio limit is assumed. -/
theorem reference_coefficients_common
    (d : ℕ) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (NE NF : ℕ → ℕ) (hNE : StrictMono NE) (hNF : StrictMono NF) :
    let kappa : ℕ → ℝ := fun N =>
      Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
    ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∃ eE eF : ℕ → ℝ,
      (∀ k, 0 < eE k ∧ 0 < eF k) ∧
      (∀ k : ℕ, Tendsto (fun n => kappa (((NE (psi n) : ℤ) - (k : ℤ)).toNat) /
          kappa (NE (psi n))) atTop (𝓝 (eE k))) ∧
      (∀ k : ℕ, Tendsto (fun n => kappa (((NF (psi n) : ℤ) - (k : ℤ)).toNat) /
          kappa (NF (psi n))) atTop (𝓝 (eF k))) := by
  dsimp only
  let kappa : ℕ → ℝ := fun N =>
    Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
  let lo : ℕ → ℝ := fun k => Real.exp (-((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
  let hi : ℕ → ℝ := fun k => Real.exp ((k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  have hlo : ∀ k, 0 < lo k := fun k => Real.exp_pos _
  have hlohi : ∀ k, lo k ≤ hi k := fun k => Real.exp_le_exp.mpr
    (neg_le_self (mul_nonneg (Nat.cast_nonneg k) M.G4.tauSq_pos.le))
  have hb : ∀ N k, k ≤ N → lo k ≤ kappa (N-k) / kappa N ∧
      kappa (N-k) / kappa N ≤ hi k := fun N k hk =>
    aux_reference_coefficients_kappa_ratio_bounds d M kappa (fun _ => rfl) N k hk
  obtain ⟨sE, hsE, eE, heE, hE⟩ := aux_reference_coefficients_extract_bounded NE hNE
    (fun N k => kappa (N-k) / kappa N) lo hi hlo hlohi hb
  obtain ⟨sF, hsF, eF, heF, hF⟩ := aux_reference_coefficients_extract_bounded
    (fun n => NF (sE n)) (hNF.comp hsE)
    (fun N k => kappa (N-k) / kappa N) lo hi hlo hlohi hb
  refine ⟨fun n => sE (sF n), hsE.comp hsF, eE, eF, fun k => ⟨heE k, heF k⟩, ?_, ?_⟩
  · intro k
    simpa only [Int.toNat_sub, Int.toNat_natCast] using (hE k).comp hsF.tendsto_atTop
  · intro k
    simpa only [Int.toNat_sub, Int.toNat_natCast] using hF k
end Paper
