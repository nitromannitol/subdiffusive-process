module

public import SubdiffusiveProcess.Static.HarmonicPairMesh
public import SubdiffusiveProcess.Static.HarmonicPairComparison
public import SubdiffusiveProcess.Static.CutoffHarmonicCellCarrier

@[expose] public section

/-! # A moment-controlled bank of normalized harmonic cells -/
open MeasureTheory Homogenization Metric
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open _root_.SubdiffusiveProcess.Model
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- The own-scale cell supplier and the two comparison prices yield a common
finite bank, whose only geometric cost is one power of the mesh inverse. -/
theorem exists_pair_cell_bank {d : ℕ} (M : GMCModel d) {R Ccell Cblock rho : ℝ}
    (hR : 1 ≤ R) (hdR : 2 * (d : ℝ) ≤ R) (hCcell : 0 ≤ Ccell) (hCblock : 0 ≤ Cblock)
    (hrho : 0 ≤ rho)
    (hcell : ∀ (l : ℕ) (k : ℤ), l ≤ k.toNat → ∀ Y : Vec d,
      ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
        eLpNorm K (ENNReal.ofReal (2 * R)) M.P.toMeasure ≤ ENNReal.ofReal Ccell ∧
        ∀ᵐ omega ∂M.P.toMeasure, CutoffHarmonicCellGrowth M l k Y omega (K omega))
    (hblock : ∀ j l : ℕ, l ≤ j → ∀ Y : Vec d,
      eLpNorm (cutoffBlockFactor M j l Y) (ENNReal.ofReal (2 * R)) M.P.toMeasure ≤
        ENNReal.ofReal (Cblock * (3 : ℝ) ^ ((1 / 4 : ℝ) * ((j - l : ℕ) : ℝ))))
    (hratio : ∀ j l : ℕ, l ≤ j →
      ahom M l / ahom M j ≤ (3 : ℝ) ^ ((1 / 4 : ℝ) * ((j - l : ℕ) : ℝ)))
    (j m n : ℕ) (hjm : j ≤ m) (z c : Vec d) (R1 R2 : ℝ) (hR2 : R2 ≤ rho) :
    let h := ((3 : ℝ) ^ n)⁻¹
    let T := (aux_hcut_trans_finite (d := d) (R1 := R1) (R2 := R2)
      (by positivity : 0 < h)).toFinset
    ∃ W : PotentialSample d → ℝ, Measurable W ∧ (∀ omega, 0 ≤ W omega) ∧
      eLpNorm W (ENNReal.ofReal R) M.P.toMeasure ≤
        ENNReal.ofReal ((2 * (rho + 1)) ^ d * Cblock * Ccell * (3 : ℝ) ^ n) ∧
      ∀ᵐ omega ∂M.P.toMeasure, ∀ a ∈ T,
        ∃ K : ℝ, 1 ≤ K ∧
          CutoffHarmonicCellGrowth M (min j ((m : ℤ) - n).toNat) ((m : ℤ) - n)
            (z + (3 : ℝ) ^ m • (c + aux_hcut_cc h a)) omega K ∧
          (ahom M (min j ((m : ℤ) - n).toNat) / ahom M j *
            cutoffBlockFactor M j (min j ((m : ℤ) - n).toNat)
              (z + (3 : ℝ) ^ m • (c + aux_hcut_cc h a)) omega) * K ≤ W omega := by
  classical
  dsimp only
  let h := ((3 : ℝ) ^ n)⁻¹
  have hh : 0 < h := by positivity
  let T := (aux_hcut_trans_finite (d := d) (R1 := R1) (R2 := R2) hh).toFinset
  let k : ℤ := (m : ℤ) - n
  let l := min j k.toNat
  let Y := fun a : Fin d → ℤ => z + (3 : ℝ) ^ m • (c + aux_hcut_cc h a)
  have hlj : l ≤ j := min_le_left _ _
  have hlk : l ≤ k.toNat := min_le_right _ _
  choose K hKmeas hKone hKnorm hKgrowth using (fun a : Fin d → ℤ => hcell l k hlk (Y a))
  let D := ahom M l / ahom M j
  have hD : 0 ≤ D := (div_pos (ahom_pos M l) (ahom_pos M j)).le
  let P := fun a omega => D * (cutoffBlockFactor M j l (Y a) omega * K a omega)
  have hPmeas : ∀ a, Measurable (P a) := fun a =>
    ((measurable_cutoffBlockFactor M j l (Y a)).mul (hKmeas a)).const_mul D
  have hPnorm : ∀ a, eLpNorm (P a) (ENNReal.ofReal R) M.P.toMeasure ≤
      ENNReal.ofReal (Cblock * Ccell * (3 : ℝ) ^ ((n : ℝ) / 2)) := by
    intro a
    have hprod := pair_eLpNorm_mul_le M.P.toMeasure
      (cutoffBlockFactor M j l (Y a)) (K a) (zero_lt_one.trans_le hR)
      (measurable_cutoffBlockFactor M j l (Y a)).aestronglyMeasurable
      (hKmeas a).aestronglyMeasurable
    have hprod' := hprod.trans (mul_le_mul' (hblock j l hlj (Y a)) (hKnorm a))
    rw [show P a = D • (fun omega => cutoffBlockFactor M j l (Y a) omega * K a omega)
      from rfl, eLpNorm_const_smul, Real.enorm_eq_ofReal hD]
    refine (mul_le_mul_right hprod' _).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul hD,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hg : ((j - l : ℕ) : ℝ) ≤ n := by
      have hgapNat : j - l ≤ n := pair_cell_cutoff_gap (n := n) hjm
      exact_mod_cast hgapNat
    have hpowers : (3 : ℝ) ^ ((1 / 4 : ℝ) * ((j - l : ℕ) : ℝ)) *
        (3 : ℝ) ^ ((1 / 4 : ℝ) * ((j - l : ℕ) : ℝ)) ≤
          (3 : ℝ) ^ ((n : ℝ) / 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    calc
      _ ≤ (3 : ℝ) ^ ((1 / 4 : ℝ) * ((j - l : ℕ) : ℝ)) *
          (Cblock * (3 : ℝ) ^ ((1 / 4 : ℝ) * ((j - l : ℕ) : ℝ)) * Ccell) := by
        nlinarith only [mul_le_mul_of_nonneg_right (hratio j l hlj)
          (by positivity : 0 ≤ Cblock * (3 : ℝ) ^ ((1 / 4 : ℝ) * ((j - l : ℕ) : ℝ)) * Ccell)]
      _ = Cblock * Ccell * ((3 : ℝ) ^ ((1 / 4 : ℝ) * ((j - l : ℕ) : ℝ)) *
          (3 : ℝ) ^ ((1 / 4 : ℝ) * ((j - l : ℕ) : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpowers (mul_nonneg hCblock hCcell)
  let I := {a : Fin d → ℤ // a ∈ T}
  let W := fun omega => ‖fun a : I => P a.val omega‖
  have hWmeas : Measurable W := (Measurable.of_eval fun a : I => hPmeas a.val).norm
  have hWnorm := pair_eLpNorm_finite_bank_le M.P.toMeasure hR
    (fun a : I => P a.val) (fun a => (hPmeas a.val).aestronglyMeasurable)
    (by positivity : 0 ≤ Cblock * Ccell * (3 : ℝ) ^ ((n : ℝ) / 2)) (fun a => hPnorm a.val)
  have hScard : 1 ≤ (2 * (rho + 1)) ^ d := one_le_pow₀ (by linarith)
  have hcard := pair_cardinality_root_bound d n hScard hR hdR
    (pair_transition_card_bound (R1 := R1) hrho hR2)
  have hcardI : Fintype.card I = T.card := by simp [I]
  refine ⟨W, hWmeas, fun omega => norm_nonneg _, ?_, ?_⟩
  · refine hWnorm.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hcardI]
    calc
      (T.card : ℝ) ^ (1 / R) * (Cblock * Ccell * (3 : ℝ) ^ ((n : ℝ) / 2)) ≤
          ((2 * (rho + 1)) ^ d * (3 : ℝ) ^ ((n : ℝ) / 2)) *
            (Cblock * Ccell * (3 : ℝ) ^ ((n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (2 * (rho + 1)) ^ d * Cblock * Ccell *
          ((3 : ℝ) ^ ((n : ℝ) / 2) * (3 : ℝ) ^ ((n : ℝ) / 2)) := by ring
      _ = _ := by
        rw [← Real.rpow_add (by norm_num),
          show (n : ℝ) / 2 + (n : ℝ) / 2 = n by ring, Real.rpow_natCast]
  · have hKgrowthAll := ae_all_iff.mpr hKgrowth
    filter_upwards [hKgrowthAll] with omega homega
    intro a ha
    refine ⟨K a omega, hKone a omega, homega a, ?_⟩
    have hcap := norm_le_pi_norm (fun b : I => P b.val omega) ⟨a, ha⟩
    have hcap' : P a omega ≤ W omega := (le_abs_self _).trans hcap
    change (D * cutoffBlockFactor M j l (Y a) omega) * K a omega ≤ _
    simpa only [P, mul_assoc] using hcap'

end SubdiffusiveProcess.Static
