module

public import SubdiffusiveProcess.CoarseGrainingVocab.AhomStarCharacterization
public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedMatrixReverse
public import SubdiffusiveProcess.Providers.Section5.ReciprocalLower

@[expose] public section

/-!
# Annealed matrix bounds

This provider assembles the four finite-volume variational inequalities and
passes the primal and inverse-star comparisons to the common scalar limit.

The starred limit passage follows the lower-right-entry route in
`Algsuperdiff/Section3/Provider/Homogenization/SigmaBarAnchor.lean`.
-/

namespace SubdiffusiveProcess.Providers.Section3

open Filter Homogenization Homogenization.Book SubdiffusiveProcess.CoarseGrainingVocab
open scoped MatrixOrder

noncomputable section

private theorem ahom_reverse_cutoff {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m n : ℕ) (hnm : n < m) :
    ahom M n ≤
      Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ)) *
        ahom M m := by
  let i : Fin d :=
    ⟨0, lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension⟩
  let e : Homogenization.Vec d := Pi.single i 1
  let x : ℝ :=
    2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ)
  have hle : ∀ k : ℕ,
      Real.exp (-x) *
          abarStarInv M m (Ch02.cubeDomain (originCube d (k : ℤ))) i i ≤
        abarStarInv M n (Ch02.cubeDomain (originCube d (k : ℤ))) i i := by
    intro k
    have hmat := matLoewnerLE_exp_smul_abarStarInv_cutoff M
      (Ch02.cubeDomain (originCube d (k : ℤ))) hnm e
    simp only [e, vecDot_single_left, matVecMul_single, Matrix.smul_apply,
      smul_eq_mul] at hmat
    have hexp : Real.exp (-x) = Real.exp
        (-2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ)) := by
      congr 1
      dsimp only [x]
      ring
    rw [hexp]
    nlinarith
  have hm0 := tendsto_pi_nhds.mp (tendsto_abarStarInv_originCube M m) i
  have hm := tendsto_pi_nhds.mp hm0 i
  have hn0 := tendsto_pi_nhds.mp (tendsto_abarStarInv_originCube M n) i
  have hn := tendsto_pi_nhds.mp hn0 i
  have hm' : Tendsto
      (fun k : ℕ => abarStarInv M m
        (Ch02.cubeDomain (originCube d (k : ℤ))) i i)
      atTop (nhds (ahom M m)⁻¹) := by
    simpa [Matrix.one_apply] using hm
  have hn' : Tendsto
      (fun k : ℕ => abarStarInv M n
        (Ch02.cubeDomain (originCube d (k : ℤ))) i i)
      atTop (nhds (ahom M n)⁻¹) := by
    simpa [Matrix.one_apply] using hn
  have hlim : Real.exp (-x) * (ahom M m)⁻¹ ≤ (ahom M n)⁻¹ :=
    le_of_tendsto_of_tendsto (hm'.const_mul (Real.exp (-x))) hn'
      (Filter.Eventually.of_forall hle)
  have hmpos : 0 < ahom M m :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Providers.Section5.homogenized_coefficient_reciprocal_lower M m)
  have hnpos : 0 < ahom M n :=
    (Real.exp_pos _).trans_le
      (SubdiffusiveProcess.Providers.Section5.homogenized_coefficient_reciprocal_lower M n)
  have hratio : Real.exp (-x) * ahom M n ≤ ahom M m := by
    have hlim' : Real.exp (-x) / ahom M m ≤ 1 / ahom M n := by
      simpa only [div_eq_mul_inv, one_mul] using hlim
    simpa only [one_mul] using (div_le_div_iff₀ hmpos hnpos).1 hlim'
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    ahom M n = Real.exp x * (Real.exp (-x) * ahom M n) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ Real.exp x * ahom M m :=
      mul_le_mul_of_nonneg_left hratio (Real.exp_pos x).le

/-- Provider for the frozen annealed matrix bounds anchor. -/
theorem annealed_matrix_bounds {d : ℕ} :
    (∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (U : Ch02.Domain d)
        (m n : ℕ), n < m →
      Homogenization.MatLoewnerLE (abar M m U) (abar M n U) ∧
      Homogenization.MatLoewnerLE (abar M n U)
        ((∫ ω, cutoffRatioSup M n m U ω ∂M.P.toMeasure) • abar M m U) ∧
      Homogenization.MatLoewnerLE
        (Real.exp (-2 * _root_.SubdiffusiveProcess.Model.tauSq M.P *
          ((m - n : ℕ) : ℝ)) • abarStarInv M m U)
        (abarStarInv M n U) ∧
      Homogenization.MatLoewnerLE (abarStarInv M n U)
        ((∫ ω, cutoffRatioSup M m n U ω ∂M.P.toMeasure) • abarStarInv M m U)) ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m n : ℕ), n < m →
      ahom M m ≤ ahom M n ∧
      ahom M n ≤
        Real.exp (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P *
          ((m - n : ℕ) : ℝ)) * ahom M m := by
  constructor
  · intro M U m n hnm
    exact ⟨matLoewnerLE_abar_cutoff M U hnm,
      matLoewnerLE_abar_cutoff_reverse M U hnm,
      matLoewnerLE_exp_smul_abarStarInv_cutoff M U hnm,
      matLoewnerLE_abarStarInv_cutoff_reverse M U hnm⟩
  · intro M m n hnm
    exact ⟨ahom_antitone_cutoff M hnm, ahom_reverse_cutoff M m n hnm⟩

end

end SubdiffusiveProcess.Providers.Section3
