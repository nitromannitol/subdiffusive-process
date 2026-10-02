import SubdiffusiveProcess.FractionalEmbedding.PairEnergy

open MeasureTheory Set
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.FractionalEmbedding

def criticalPower (d : ℕ) (s : ℝ) : ℝ := 2 * (d : ℝ) / ((d : ℝ) - 2 * s)
def criticalRoot (d : ℕ) (s : ℝ) : ℝ := ((d : ℝ) - 2 * s) / (d : ℝ)
def smallSetThreshold (d : ℕ) (r : ℝ) : ℝ := (r / 2) ^ d / 2

def rawEmbeddingConstant (d : ℕ) (s r : ℝ) : ℝ :=
  1 + max 0 (max (9 * (r ^ d : ℝ) ^ (criticalRoot d s) / smallSetThreshold d r)
    (128 * dyadicStepConstant (criticalRoot d s) / (3 * cubeKernelLowerConstant d s)))

theorem critical_exponents {d : ℕ} (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1) :
    0 < criticalRoot d s ∧ criticalRoot d s < 1 ∧ 0 < criticalPower d s ∧
      criticalPower d s * criticalRoot d s = 2 ∧
      criticalRoot d s - 1 = -2 * (s : ℝ) / (d : ℝ) := by
  have hdReal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdPos : 0 < (d : ℝ) := by linarith
  have hden : 0 < (d : ℝ) - 2 * (s : ℝ) := by linarith [s.2.2]
  have hsPos : 0 < (s : ℝ) := s.2.1
  refine ⟨div_pos hden hdPos, ?_, div_pos (by positivity) hden, ?_, ?_⟩
  · unfold criticalRoot
    exact (div_lt_one hdPos).mpr (by linarith)
  · unfold criticalPower criticalRoot
    field_simp
  · unfold criticalRoot
    field_simp
    ring

theorem rawEmbeddingConstant_pos (d : ℕ) (s r : ℝ) : 0 < rawEmbeddingConstant d s r := by
  unfold rawEmbeddingConstant
  have h := le_max_left 0 (max (9 * (r ^ d : ℝ) ^ (criticalRoot d s) / smallSetThreshold d r)
    (128 * dyadicStepConstant (criticalRoot d s) / (3 * cubeKernelLowerConstant d s)))
  linarith

theorem rawEmbeddingConstant_bounds (d : ℕ) (s r : ℝ) :
    9 * (r ^ d : ℝ) ^ (criticalRoot d s) / smallSetThreshold d r ≤ rawEmbeddingConstant d s r ∧
      128 * dyadicStepConstant (criticalRoot d s) / (3 * cubeKernelLowerConstant d s) ≤
        rawEmbeddingConstant d s r := by
  unfold rawEmbeddingConstant
  have h₁ := le_max_left (9 * (r ^ d : ℝ) ^ (criticalRoot d s) / smallSetThreshold d r)
    (128 * dyadicStepConstant (criticalRoot d s) / (3 * cubeKernelLowerConstant d s))
  have h₂ := le_max_right (9 * (r ^ d : ℝ) ^ (criticalRoot d s) / smallSetThreshold d r)
    (128 * dyadicStepConstant (criticalRoot d s) / (3 * cubeKernelLowerConstant d s))
  have h₃ := le_max_right 0 (max (9 * (r ^ d : ℝ) ^ (criticalRoot d s) / smallSetThreshold d r)
    (128 * dyadicStepConstant (criticalRoot d s) / (3 * cubeKernelLowerConstant d s)))
  constructor <;> linarith

/-- The direct-cube fractional endpoint bound, obtained from finite dyadic level sums. -/
theorem cube_fractional_moment_bound {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hL2 : (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((f x) ^ 2)) < ⊤)
    (hM : 0 < (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((f x) ^ 2)).toReal)
    (hE : scalarGagliardoEnergy z r hr s f < ⊤) :
    (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((f x) ^ criticalPower d s)) < ⊤ ∧
      (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal ((f x) ^ criticalPower d s)).toReal ^ (criticalRoot d s) ≤
        rawEmbeddingConstant d s r *
          ((∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ENNReal.ofReal ((f x) ^ 2)).toReal + (scalarGagliardoEnergy z r hr s f).toReal) := by
  classical
  let μ := volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  let M := (∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ).toReal
  let E := (scalarGagliardoEnergy z r hr s f).toReal
  let β := criticalRoot d s
  let ε := smallSetThreshold d r
  let t := Real.sqrt (M / ε)
  let a : ℕ → ℝ := levelMass μ f t
  obtain ⟨hβ, hβ1, hq, hqβ, hβminus⟩ := critical_exponents hd s
  have hε : 0 < ε := by dsimp [ε, smallSetThreshold]; positivity
  have hMpos : 0 < M := hM
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hMpos hε)
  have htSq : t ^ 2 = M / ε := Real.sq_sqrt (div_nonneg hMpos.le hε.le)
  have htail := squared_tail_bound μ f hf ht hL2
  have ha0 : a 0 ≤ ε := by
    have htail' : t ^ 2 * a 0 ≤ M := by
      simpa only [a, levelMass, levelScale, pow_zero, mul_one] using htail
    have heq : M = t ^ 2 * ε := by rw [htSq, div_mul_cancel₀ _ hε.ne']
    nlinarith only [htail', heq, pow_pos ht 2]
  have hV : (μ Set.univ).toReal = r ^ d := by
    dsimp only [μ]
    rw [Measure.restrict_apply_univ]
    exact centeredCube_volume_real z hr
  have ha (k : ℕ) : 0 ≤ a k := levelMass_nonneg μ f t k
  have hmono (k : ℕ) : a (k + 1) ≤ a k := levelMass_step μ f ht k
  have hav : (a 0) ^ β ≤ (r ^ d : ℝ) ^ β :=
    Real.rpow_le_rpow (ha 0) (by rw [← hV]; exact levelMass_le_univ μ f t 0) hβ.le
  have hD : 0 ≤ dyadicStepConstant β := (dyadicStepConstant_pos β).le
  have hκ := cubeKernelLowerConstant_pos (by omega : 0 < d) (s : ℝ)
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
  have hC := rawEmbeddingConstant_pos d (s : ℝ) r
  have hCbound := rawEmbeddingConstant_bounds d (s : ℝ) r
  apply fullMoment_from_truncations μ f hf hf0 ht hq hβ
    (mul_nonneg hC.le (add_nonneg hMpos.le hE0))
  intro N
  have hmom := dyadic_moment_power ht
    (ENNReal.toReal_nonneg (a := truncatedMoment μ f t (criticalPower d s) N))
    (by positivity : (0 : ℝ) ≤ r ^ d) hβ hβ1 hqβ a ha N
    (by rw [← hV]; exact truncatedMoment_le_levels μ f hf ht hq hf0 N)
  have hmass := dyadic_mass_sum hβ hβ1 a ha hmono N
  have henergy := dyadic_energy_bound (by omega : 0 < d) z r hr s f hf hE ht ha0 N
  change t ^ 2 * (∑ k ∈ Finset.range N, (4 : ℝ) ^ k * a (k + 1) *
      (a k) ^ (-2 * (s : ℝ) / (d : ℝ))) ≤ _ at henergy
  have hlarge :
      (truncatedMoment μ f t (criticalPower d s) N).toReal ^ β ≤
        9 * t ^ 2 * (r ^ d : ℝ) ^ β +
          32 * dyadicStepConstant β *
            (t ^ 2 * ∑ k ∈ Finset.range N, (4 : ℝ) ^ k * a (k + 1) *
              (a k) ^ (-2 * (s : ℝ) / (d : ℝ))) := by
    calc
      _ ≤ t ^ 2 * (r ^ d : ℝ) ^ β + 4 * t ^ 2 *
          (2 * (a 0) ^ β + 8 * dyadicStepConstant β *
            ∑ k ∈ Finset.range N, (4 : ℝ) ^ k * a (k + 1) * (a k) ^ (β - 1)) := by
        have hscaled := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 4 * t ^ 2 by positivity)
        linarith only [hmom, hscaled]
      _ ≤ t ^ 2 * (r ^ d : ℝ) ^ β + 4 * t ^ 2 *
          (2 * (r ^ d : ℝ) ^ β + 8 * dyadicStepConstant β *
            ∑ k ∈ Finset.range N, (4 : ℝ) ^ k * a (k + 1) * (a k) ^ (β - 1)) := by
        have hscaled := mul_le_mul_of_nonneg_left hav (show 0 ≤ 8 * t ^ 2 by positivity)
        nlinarith only [hscaled]
      _ = _ := by rw [show β - 1 = -2 * (s : ℝ) / (d : ℝ) from hβminus]; ring
  calc
    _ ≤ 9 * t ^ 2 * (r ^ d : ℝ) ^ β +
        32 * dyadicStepConstant β * ((4 / (3 * cubeKernelLowerConstant d s)) * E) :=
      by
        have hscaled := mul_le_mul_of_nonneg_left henergy
          (show 0 ≤ 32 * dyadicStepConstant β by positivity)
        linarith only [hlarge, hscaled]
    _ = (9 * (r ^ d : ℝ) ^ β / ε) * M +
        (128 * dyadicStepConstant β / (3 * cubeKernelLowerConstant d s)) * E := by
      rw [htSq]
      ring
    _ ≤ rawEmbeddingConstant d s r * (M + E) := by
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right hCbound.1 hMpos.le)
        (mul_le_mul_of_nonneg_right hCbound.2 hE0)

end SubdiffusiveProcess.FractionalEmbedding
