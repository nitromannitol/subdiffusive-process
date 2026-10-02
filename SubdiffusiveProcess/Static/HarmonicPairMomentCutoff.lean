import SubdiffusiveProcess.Static.HarmonicPairCutoff

/-! # Uniform same-order moments for every nested cutoff pair -/
open MeasureTheory Homogenization Metric
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec TriadicCube
open SubdiffusiveProcess.Frozen.Assumptions
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- A high-order cell bank yields a cutoff for each pair with a uniform
same-order moment and the exact gap exponent three. -/
theorem exists_pair_moment_cutoff {d : ℕ} (M : GMCModel d)
    {q R Ccell Cblock rho C0 : ℝ} (hq : 1 ≤ q) (hqR : q ≤ R)
    (hdR : 2 * (d : ℝ) ≤ R) (hCcell : 0 ≤ Ccell) (hCblock : 0 ≤ Cblock)
    (hrho : 0 ≤ rho) (hC0 : 0 < C0)
    (hcell : ∀ (l : ℕ) (k : ℤ), l ≤ k.toNat → ∀ Y : Vec d,
      ∃ K : PotentialSample d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
        eLpNorm K (ENNReal.ofReal (2 * R)) M.P.toMeasure ≤ ENNReal.ofReal Ccell ∧
        ∀ᵐ omega ∂M.P.toMeasure, CutoffHarmonicCellGrowth M l k Y omega (K omega))
    (hblock : ∀ j l : ℕ, l ≤ j → ∀ Y : Vec d,
      eLpNorm (cutoffBlockFactor M j l Y) (ENNReal.ofReal (2 * R)) M.P.toMeasure ≤
        ENNReal.ofReal (Cblock * (3 : ℝ) ^ ((1 / 4 : ℝ) * ((j - l : ℕ) : ℝ))))
    (hratio : ∀ j l : ℕ, l ≤ j →
      ahom M l / ahom M j ≤ (3 : ℝ) ^ ((1 / 4 : ℝ) * ((j - l : ℕ) : ℝ)))
    (hsmooth : ∀ a1 a2 : ℝ, 0 < a1 → a1 < a2 →
      ∃ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ x, ‖x‖ ≤ a1 → f x = 1) ∧
        (∀ x, a2 ≤ ‖x‖ → f x = 0) ∧
        (∀ x, ‖fderiv ℝ f x‖ ≤ C0 / (a2 - a1)) ∧
        (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ C0 / (a2 - a1) ^ 2))
    (j m : ℕ) (hjm : j ≤ m) (z c : Vec d) (R1 R2 : ℝ)
    (hR1 : 0 < R1) (hR12 : R1 < R2) (hR2 : R2 ≤ rho) :
    ∃ Z : PotentialSample d → ℝ, Measurable Z ∧
      eLpNorm Z (ENNReal.ofReal q) M.P.toMeasure ≤
        ENNReal.ofReal ((8 : ℝ) ^ d * (1 + C0) ^ 2 * (3 * rho + 15) ^ 3 *
          (2 * (rho + 1)) ^ d * Cblock * Ccell) ∧
      ∀ᵐ omega ∂M.P.toMeasure,
        ∃ chi : H10Function (ball c R2),
          (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
          (∀ x ∈ ball c R1, chi.toFun x = 1) ∧ tsupport chi.toFun ⊆ ball c R2 ∧
          ∀ (x : Vec d) (r : ℝ), 0 < r → r ≤ 1 →
            ∫⁻ w in ball x r ∩ ball c R2,
              ENNReal.ofReal ((ahom M j)⁻¹ * aCutoff M j omega (z + (3 : ℝ) ^ m • w) *
                vecDot (chi.grad w) (chi.grad w)) ≤
              ENNReal.ofReal (Z omega * (R2 - R1) ^ (-3 : ℝ) *
                r ^ ((d : ℝ) - 1 / 2)) := by
  have hR : 1 ≤ R := hq.trans hqR
  obtain ⟨n, hn, h5, hscale, _⟩ := exists_harmonic_cutoff_mesh
    (sub_pos.mpr hR12) (rho0 := 2 * rho) (by linarith)
  have hscale' : (3 : ℝ) ^ n ≤ (3 * rho + 15) / (R2 - R1) := by
    convert hscale using 1 <;> ring
  obtain ⟨W, hWmeas, hW0, hWnorm, hWbank⟩ := exists_pair_cell_bank M hR hdR
    hCcell hCblock hrho hcell hblock hratio j m n hjm z c R1 R2 hR2
  let h := ((3 : ℝ) ^ n)⁻¹
  let F := (8 : ℝ) ^ d * (1 + C0) ^ 2 * (3 * rho + 15) ^ 3
  let Z := fun omega => (F * h) * W omega
  have hF : 0 ≤ F := by positivity
  have hh : 0 < h := by positivity
  refine ⟨Z, hWmeas.const_mul (F * h), ?_, ?_⟩
  · have hWq := (eLpNorm_le_eLpNorm_of_exponent_le
      (ENNReal.ofReal_le_ofReal hqR) hWmeas.aestronglyMeasurable).trans hWnorm
    rw [show Z = (F * h) • W from rfl, eLpNorm_const_smul,
      Real.enorm_eq_ofReal (mul_nonneg hF hh.le)]
    refine (mul_le_mul_right hWq _).trans_eq ?_
    rw [← ENNReal.ofReal_mul (mul_nonneg hF hh.le)]
    congr 1
    dsimp only [F, h]
    field_simp
  · filter_upwards [hWbank] with omega homega
    simpa only [Z, F, h, mul_assoc] using exists_pair_cutoff_of_cell_bank
      M j m n z c omega R1 R2 C0 (3 * rho + 15) (W omega)
      hR1 hR12 hC0 hn (hW0 omega) h5 hscale' hsmooth homega

end SubdiffusiveProcess.Static
