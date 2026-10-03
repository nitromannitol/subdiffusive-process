module

public import SubdiffusiveProcess.Static.HarmonicPairCell
public import SubdiffusiveProcess.Static.HarmonicPairBank
public import SubdiffusiveProcess.Static.HarmonicPairPrice
public import SubdiffusiveProcess.Static.HarmonicPairTranslation

@[expose] public section

/-! # Pair cutoffs from the native own-scale harmonic cell bank -/
open MeasureTheory Homogenization Metric
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- The finite cell bank constructs a pair cutoff with gap exponent three. -/
theorem exists_pair_cutoff_of_cell_bank {d : ℕ} (M : GMCModel d)
    (j m n : ℕ) (z c : Vec d) (omega : PotentialSample d)
    (R1 R2 C0 D W : ℝ) (hR1 : 0 < R1) (hR12 : R1 < R2) (hC0 : 0 < C0)
    (hn : 1 ≤ n) (hW : 0 ≤ W)
    (h5 : 5 * ((3 : ℝ) ^ n)⁻¹ ≤ R2 - R1)
    (hscale : (3 : ℝ) ^ n ≤ D / (R2 - R1))
    (hsmooth : ∀ a1 a2 : ℝ, 0 < a1 → a1 < a2 →
      ∃ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ x, ‖x‖ ≤ a1 → f x = 1) ∧
        (∀ x, a2 ≤ ‖x‖ → f x = 0) ∧
        (∀ x, ‖fderiv ℝ f x‖ ≤ C0 / (a2 - a1)) ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C0 / (a2 - a1) ^ 2))
    (hbank : ∀ a ∈ (aux_hcut_trans_finite (d := d) (R1 := R1) (R2 := R2)
        (by positivity : 0 < ((3 : ℝ) ^ n)⁻¹)).toFinset,
      ∃ K : ℝ, 1 ≤ K ∧
        CutoffHarmonicCellGrowth M (min j ((m : ℤ) - n).toNat) ((m : ℤ) - n)
          (z + (3 : ℝ) ^ m • (c + aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ a)) omega K ∧
        (ahom M (min j ((m : ℤ) - n).toNat) / ahom M j *
          cutoffBlockFactor M j (min j ((m : ℤ) - n).toNat)
            (z + (3 : ℝ) ^ m • (c + aux_hcut_cc ((3 : ℝ) ^ n)⁻¹ a)) omega) * K ≤ W) :
    ∃ chi : H10Function (ball c R2),
      (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
      (∀ x ∈ ball c R1, chi.toFun x = 1) ∧ tsupport chi.toFun ⊆ ball c R2 ∧
      ∀ (x : Vec d) (r : ℝ), 0 < r → r ≤ 1 →
        ∫⁻ w in ball x r ∩ ball c R2,
          ENNReal.ofReal ((ahom M j)⁻¹ * aCutoff M j omega (z + (3 : ℝ) ^ m • w) *
            vecDot (chi.grad w) (chi.grad w)) ≤
          ENNReal.ofReal ((8 ^ d * (1 + C0) ^ 2 * D ^ 3 * (((3 : ℝ) ^ n)⁻¹ * W)) *
            (R2 - R1) ^ (-3 : ℝ) * r ^ ((d : ℝ) - 1 / 2)) := by
  let h := ((3 : ℝ) ^ n)⁻¹
  have hh : 0 < h := by positivity
  have hh1 : h ≤ 1 / 2 := by
    have h3 : (3 : ℝ) ≤ (3 : ℝ) ^ n := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hn
    dsimp only [h]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  let g := R2 - R1
  have hg : 0 < g := sub_pos.mpr hR12
  obtain ⟨f, hf, hf01, hf1, hf0, hD1, hD2⟩ :=
    hsmooth (R1 + h) (R2 - 2 * h) (by linarith) (by linarith)
  have hgap : R2 - 2 * h - (R1 + h) = g - 3 * h := by dsimp [g]; ring
  rw [hgap] at hD1 hD2
  have hc := aux_hcut_f_compact hf0
  let A := fun w : Vec d => (ahom M j)⁻¹ * aCutoff M j omega (z + (3 : ℝ) ^ m • w)
  let Ashift := fun w => A (c + w)
  let B := 1 + C0
  let G := W * B ^ 2 * h ^ (-(3 / 2 : ℝ))
  have hG : 0 ≤ G := by positivity
  have hd : 1 ≤ d := by have hdim := M.shellPrefix.dimension; omega
  obtain ⟨chi, h01, hone, hsupp, he⟩ := aux_hcut_hcut_core hd Ashift
    (fun w => mul_pos (inv_pos.mpr (ahom_pos M j)) (aCutoff_pos M j omega _))
    R1 R2 h G hh hh1 hG f hf hf01 hf1 hf0 (fun a ha => by
      obtain ⟨K, hK, hKgrowth, hcap⟩ := hbank a ((aux_hcut_mem_T hh).mpr ha)
      let k : ℤ := (m : ℤ) - n
      let l := min j k.toNat
      let y := aux_hcut_cc h a
      let Y := z + (3 : ℝ) ^ m • (c + y)
      let b := fun w : Vec d => (ahom M l)⁻¹ * aCutoff M l omega (Y + (3 : ℝ) ^ k • w)
      let F := ahom M l / ahom M j * cutoffBlockFactor M j l Y omega
      have hF : 0 ≤ F := mul_nonneg (div_pos (ahom_pos M l) (ahom_pos M j)).le
        (zero_le_one.trans (one_le_cutoffBlockFactor M j l Y omega))
      have hmap : Continuous (fun w : Vec d => Y + (3 : ℝ) ^ k • w) := by fun_prop
      have hb : Continuous b := continuous_const.mul
        ((continuous_aCutoff M l omega).comp hmap)
      have hbpos : ∀ w, 0 < b w := fun w =>
        mul_pos (inv_pos.mpr (ahom_pos M l)) (aCutoff_pos M l omega _)
      have hcomp : ∀ w ∈ openCubeSet (originCube d 0), Ashift (y + h • w) ≤ F * b w := by
        intro w hw
        simpa only [Ashift, A, F, b, Y, y, h, l, k, add_assoc] using
          pair_normalized_coefficient_comparison M j m n z (c + y) omega hw
      have hdatum := pair_affine_datum_size y hh hg h5 hC0.le f hf hf01 hD1 hD2
      obtain ⟨e, he01, heenergy⟩ := exists_pair_cell_correction hd y hh hF
        (zero_le_one.trans hK) (by positivity : 0 ≤ B) Ashift b hb hbpos f hf hc hf01 hcomp
        (fun u hu htr x hx r hr hr1 =>
          hKgrowth _ (pair_affine_smooth_compact y hh f hf hc).1
            (pair_affine_smooth_compact y hh f hf hc).2 B (by positivity) hdatum
            u hu htr x hx r hr hr1)
      refine ⟨e, he01, fun x hx r hr hr1 => (heenergy x hx r hr hr1).trans ?_⟩
      apply ENNReal.ofReal_le_ofReal
      have hp := mul_le_mul_of_nonneg_right hcap
        (by positivity : 0 ≤ B ^ 2 * h ^ (-(3 / 2 : ℝ)) * r ^ ((d : ℝ) - 1 / 2))
      simpa only [G, F, Y, l, k, y, h, mul_assoc] using hp)
  apply exists_pair_translated_cutoff c A R1 R2
    (8 ^ d * B ^ 2 * D ^ 3 * (h * W) * g ^ (-3 : ℝ)) chi h01 hone hsupp
  intro x r hr hr1
  refine (he x r hr hr1).trans (ENNReal.ofReal_le_ofReal ?_)
  have hprice := pair_gap_three_bound hh hg
    (by positivity : 0 ≤ (8 : ℝ) ^ d * W * B ^ 2)
    (by simpa only [h, inv_inv] using hscale)
  have hp := mul_le_mul_of_nonneg_right hprice (Real.rpow_nonneg hr.le ((d : ℝ) - 1 / 2))
  simpa only [G, B, g, mul_assoc, mul_left_comm, mul_comm] using hp

end SubdiffusiveProcess.Static
