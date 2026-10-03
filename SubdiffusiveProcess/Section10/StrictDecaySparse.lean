module

public import SubdiffusiveProcess.Section10.RetainedPrefixReadoutConsumer
public import SubdiffusiveProcess.Section10.InitialSimplexPackingGeometryConsumer
public import SubdiffusiveProcess.Providers.Section3.SpecialTwoDExactFormula
public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum

@[expose] public section

/-!
# Strict decay from the actual retained-prefix induction

The ready all-cell initial estimate and the actual Section 5 gap discharge
all analytic premises. The initial constant is paid once. The planar branch
applies the proved exact formula on the genuine model.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (ahom ahom_pos aCutoffCoeffOnData randomAMatrix)
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

noncomputable section

/-- The single fixed prefactor lost when replacing a natural floor by a real
exponent. Includes n=0 and arbitrary positive integer spacings. -/
theorem strictDecay_floor_power_le {qq : ℝ} (hqq : 0 < qq) (hqq1 : qq < 1)
    {R : ℕ} (hR : 0 < R) (n : ℕ) :
    qq ^ (n / R) ≤ qq⁻¹ * Real.rpow 3
      (-(-Real.log qq / ((R : ℝ) * Real.log 3)) * (n : ℝ)) := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hcount : (n : ℝ) / (R : ℝ) - 1 ≤ ((n / R : ℕ) : ℝ) := by
    have hn : n ≤ R * (n / R + 1) := (Nat.lt_mul_div_succ n hR).le
    have hnreal : (n : ℝ) ≤ (R : ℝ) * (((n / R : ℕ) : ℝ) + 1) := by
      exact_mod_cast hn
    have hdiv := (div_le_iff₀ hRreal).mpr (by nlinarith :
      (n : ℝ) ≤ (((n / R : ℕ) : ℝ) + 1) * (R : ℝ))
    linarith
  have hlog3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  change qq ^ (n / R) ≤ qq⁻¹ * (3 : ℝ) ^
    (-(-Real.log qq / ((R : ℝ) * Real.log 3)) * (n : ℝ))
  rw [← Real.rpow_natCast qq (n / R), Real.rpow_def_of_pos hqq,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  rw [show qq⁻¹ = Real.exp (-Real.log qq) by
    rw [Real.exp_neg, Real.exp_log hqq], ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonpos_left hcount (Real.log_neg hqq hqq1).le
  have heq : -Real.log qq + Real.log 3 *
      (-(-Real.log qq / ((R : ℝ) * Real.log 3)) * (n : ℝ)) =
      Real.log qq * ((n : ℝ) / (R : ℝ) - 1) := by
    field_simp [hRreal.ne', hlog3]
    ring
  rw [heq]
  exact hmul

/-- The genuine all-cell initial estimate, actual gap and D3 readout yield
the arbitrary-scale strict-decay ratio, with no analytic input premise. -/
theorem exists_strictDecay_ratio_of_geometry (d : ℕ) (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ M : GMCModel d, M.delta ≤ delta0 →
      ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧
        ∀ ell m : ℕ, ell ≤ m → ahom M m / ahom M ell ≤
          C * Real.rpow 3 (-(eta * ((m : ℝ) - (ell : ℝ)))) := by
  obtain ⟨delta0, C0, hdelta0, hC0, henergy⟩ :=
    exists_initialSimplexEnergy_all_cells_of_geometry d hd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M hM
  obtain ⟨R, hR, qq, hqq, hqq1, hqR⟩ := exists_pos_forall_qRCell_lt_one M
  let eta := -Real.log qq / ((R : ℝ) * Real.log 3)
  have heta : 0 < eta := div_pos (neg_pos.mpr (Real.log_neg hqq hqq1))
    (mul_pos (by exact_mod_cast hR) (Real.log_pos (by norm_num)))
  refine ⟨C0 / qq, eta, div_pos hC0 hqq, heta, ?_⟩
  intro ell m hell
  have hbase : ∀ (c : Fin d → ℤ) (pi : Equiv.Perm (Fin d)) (p : Vec d),
      ∫ omega, (volume (dilatedCell ell c pi).openCarrier).toReal⁻¹ *
        dirichletInfOn (aCutoff M ell omega) (dilatedCell ell c pi).openCarrier p
        ∂M.P.toMeasure ≤ (C0 * ahom M ell) * vecNormSq p := by
    intro c pi p
    have heq (omega : PotentialSample d) :
        (volume (dilatedCell ell c pi).openCarrier).toReal⁻¹ *
          dirichletInfOn (aCutoff M ell omega) (dilatedCell ell c pi).openCarrier p =
        vecDot p (matVecMul
          (randomAMatrix M ell (kuhnCellDomain (dilatedCell ell c pi)) omega) p) :=
      (vecDot_aMatrix_eq_dirichletInfOn
        (aCutoffCoeffOnData M ell omega (kuhnCellDomain (dilatedCell ell c pi)))
        (fun _ => (Real.exp_pos _).le) p).symm
    simp_rw [heq]
    exact henergy M hM ell (dilatedCell ell c pi) rfl p
  have hdec := ahom_le_retainedPrefix_pow_of_initial M ell hR
    (mul_nonneg hC0.le (ahom_pos M ell).le) hqq.le hbase hqR (floor_scale_le hell)
  have hratio : ahom M m / ahom M ell ≤ C0 * qq ^ ((m - ell) / R) := by
    apply (div_le_iff₀ (ahom_pos M ell)).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hdec
  refine hratio.trans ?_
  have hfloor := mul_le_mul_of_nonneg_left
    (strictDecay_floor_power_le hqq hqq1 hR (m - ell)) hC0.le
  rw [Nat.cast_sub hell] at hfloor
  dsimp only [eta]
  simpa only [div_eq_mul_inv, mul_assoc, neg_mul] using hfloor

/-- Exact planar ratio, by applying the proved model identity at both scales. -/
theorem strictDecay_planar_ratio (M : GMCModel 2) (ell m : ℕ) :
    ahom M m / ahom M ell = Real.rpow 3
      (-((tauSq M.P / Real.log 3) * ((m : ℝ) - (ell : ℝ)))) := by
  change ahom M m / ahom M ell = (3 : ℝ) ^
    (-((tauSq M.P / Real.log 3) * ((m : ℝ) - (ell : ℝ))))
  rw [SubdiffusiveProcess.Providers.Section3.special_two_d_exact_formula M m,
    SubdiffusiveProcess.Providers.Section3.special_two_d_exact_formula M ell,
    ← Real.exp_sub, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  congr 1
  have hlog3 : Real.log 3 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp [hlog3]
  ring

end

end SubdiffusiveProcess.Section10
