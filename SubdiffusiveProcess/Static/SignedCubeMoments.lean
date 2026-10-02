import SubdiffusiveProcess.Static.MicroscopicCubeMoments
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Action

/-! # Uniform mass moments at every signed physical subscale -/
open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions
open Homogenization hiding Vec TriadicCube
open SubdiffusiveProcess.Static
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.Static

/-- Cube masses translated by an arbitrary real vector. -/
def translatedCutoffAverage {d : ℕ} (M : GMCModel d) (L : ℕ) (k : ℤ)
    (z : Vec d) (ω : PotentialSample d) : ℝ :=
  SubdiffusiveProcess.Section9.cutoffCubeAverage M L (originCube d k) (translatePotentialSample z ω)

theorem measurable_translatedCutoffAverage {d : ℕ} (M : GMCModel d) (L : ℕ) (k : ℤ)
    (z : Vec d) : Measurable (translatedCutoffAverage M L k z) :=
  (SubdiffusiveProcess.Section9.measurable_cutoffCubeAverage M L _).comp
    (Section6Covariance.measurable_translatePotentialSample z)

theorem translatedCutoffAverage_pos {d : ℕ} (M : GMCModel d) (L : ℕ) (k : ℤ)
    (z : Vec d) (ω : PotentialSample d) : 0 < translatedCutoffAverage M L k z ω :=
  cutoffCubeAverage_pos M L _ _

/-- Both signs of every translated physical cube have at most an arbitrary
small geometric cost in their depth below a parent. This includes cubes below
one, cubes above the finite cutoff and parents above that cutoff. -/
theorem exists_uniform_signed_cube_mass_moments (d : ℕ) (q η : ℝ)
    (hq : 1 ≤ q) (hη : 0 < η) :
    ∃ δ0 C : ℝ, 0 < δ0 ∧ 0 < C ∧
      ∀ M : GMCModel d, M.delta ≤ δ0 →
        ∀ L m n : ℕ, L ≤ m → ∀ k : ℤ, (m : ℤ) - n ≤ k → ∀ z : Vec d,
          (∫⁻ ω, ENNReal.ofReal (translatedCutoffAverage M L k z ω ^ q)
            ∂M.P.toMeasure) ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (q * η * n)) ∧
          (∫⁻ ω, ENNReal.ofReal ((translatedCutoffAverage M L k z ω)⁻¹ ^ q)
            ∂M.P.toMeasure) ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (q * η * n)) := by
  obtain ⟨δa, A, hδa, hA, ha⟩ := exists_uniform_cutoffCube_mass_moments d q hq
  obtain ⟨δb, B, hδb, hB, hb⟩ := exists_uniform_subscale_cube_mass_moments d q η hq hη
  obtain ⟨δc, D, hδc, hD, hc⟩ := exists_uniform_microscopic_cube_mass_moments d q η hq hη
  let C := A + B + D
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨min (min δa δb) δc, C, lt_min (lt_min hδa hδb) hδc, hC, ?_⟩
  intro M hM L m n hLm k hkn z
  have hMa : M.delta ≤ δa := hM.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hMb : M.delta ≤ δb := hM.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hMc : M.delta ≤ δc := hM.trans (min_le_right _ _)
  have hqη : 0 ≤ q * η := mul_nonneg (zero_le_one.trans hq) hη.le
  have hpower : 1 ≤ (3 : ℝ) ^ (q * η * n) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hqη (Nat.cast_nonneg _))
  have hconst : ∀ E : ℝ, 0 ≤ E → E ≤ C →
      E ≤ C * (3 : ℝ) ^ (q * η * n) := by
    intro E hE hEC
    exact hEC.trans (le_mul_of_one_le_right hC.le hpower)
  have hscaled : ∀ (E : ℝ) (j : ℕ), 0 ≤ E → E ≤ C → j ≤ n →
      E * (3 : ℝ) ^ (q * η * j) ≤ C * (3 : ℝ) ^ (q * η * n) := by
    intro E j hE hEC hj
    apply mul_le_mul hEC _ (by positivity) hC.le
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hqη
  have hbase :
      (∫⁻ ω, ENNReal.ofReal (SubdiffusiveProcess.Section9.cutoffCubeAverage M L (originCube d k) ω ^ q)
        ∂M.P.toMeasure) ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (q * η * n)) ∧
      (∫⁻ ω, ENNReal.ofReal ((SubdiffusiveProcess.Section9.cutoffCubeAverage M L (originCube d k) ω)⁻¹ ^ q)
        ∂M.P.toMeasure) ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (q * η * n)) := by
    by_cases hk : 0 ≤ k
    · have heq : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
      by_cases hLk : L ≤ k.toNat
      · obtain ⟨hp, hi⟩ := ha M hMa L k.toNat hLk (originCube d k) (by change k = (k.toNat : ℤ); exact heq.symm)
        have hh := ENNReal.ofReal_le_ofReal (hconst A hA.le (by dsimp only [C]; linarith))
        exact ⟨hp.trans hh, hi.trans hh⟩
      · have hkL : k.toNat ≤ L := Nat.le_of_lt (lt_of_not_ge hLk)
        obtain ⟨hp, hi⟩ := hb M hMb L k.toNat hkL (originCube d k) (by change k = (k.toNat : ℤ); exact heq.symm)
        have hgap : L - k.toNat ≤ n := by omega
        have hh := ENNReal.ofReal_le_ofReal
          (hscaled B (L - k.toNat) hB.le (by dsimp only [C]; linarith) hgap)
        exact ⟨hp.trans hh, hi.trans hh⟩
    · obtain ⟨hp, hi⟩ := hc M hMc L k (le_of_not_ge hk)
      have hgap : L ≤ n := by omega
      have hh := ENNReal.ofReal_le_ofReal
        (hscaled D L hD.le (by dsimp only [C]; linarith) hgap)
      exact ⟨hp.trans hh, hi.trans hh⟩
  have htranslate (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
      (∫⁻ ω, F (translatedCutoffAverage M L k z ω) ∂M.P.toMeasure) =
        ∫⁻ ω, F (SubdiffusiveProcess.Section9.cutoffCubeAverage M L (originCube d k) ω) ∂M.P.toMeasure :=
    (Section6Covariance.measurePreserving_translatePotentialSample M z).lintegral_comp
      (hF.comp (SubdiffusiveProcess.Section9.measurable_cutoffCubeAverage M L _))
  constructor
  · rw [htranslate (fun a : ℝ => ENNReal.ofReal (a ^ q))
      ((measurable_id.pow_const q).ennreal_ofReal)]
    exact hbase.1
  · rw [htranslate (fun a : ℝ => ENNReal.ofReal (a⁻¹ ^ q))
      ((measurable_inv.pow_const q).ennreal_ofReal)]
    exact hbase.2

end SubdiffusiveProcess.Static
