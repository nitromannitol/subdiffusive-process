import SubdiffusiveProcess.FractionalEmbedding.Normalization
import SubdiffusiveProcess.Sobolev.CampanatoRepresentative
import SubdiffusiveProcess.Geometry.CubeEuclideanDiameter

open MeasureTheory Set
open SubdiffusiveProcess
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.FractionalEmbedding

/-- The Euclidean fractional kernel, interpreted as an extended nonnegative weight. -/
def fractionalKernel (d : ℕ) (s : ℝ) (x y : SpatialCoordinates d) : ℝ≥0∞ :=
  1 / (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ ((d : ℝ) + 2 * s)

/-- A dimension/order constant in the cube complement-kernel estimate. -/
def cubeKernelLowerConstant (d : ℕ) (s : ℝ) : ℝ :=
  (2 * Real.sqrt d) ^ (-((d : ℝ) + 2 * s)) *
    (2 : ℝ) ^ (-((d : ℝ) + 2 * s) / (d : ℝ))

theorem cubeKernelLowerConstant_pos {d : ℕ} (hd : 0 < d) (s : ℝ) :
    0 < cubeKernelLowerConstant d s := by
  have hdReal : 0 < (d : ℝ) := by exact_mod_cast hd
  exact mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hdReal)) _)
    (Real.rpow_pos_of_pos (by norm_num) _)

/-- Pure power bookkeeping for the local cube radius used in the kernel bound. -/
theorem kernel_radius_identity (n D a s : ℝ) (hn : 0 < n) (hD : 0 < D) (ha : 0 < a) :
    a * (D * (2 * a) ^ (1 / n)) ^ (-(n + 2 * s)) =
      (D ^ (-(n + 2 * s)) * (2 : ℝ) ^ (-(n + 2 * s) / n)) * a ^ (-2 * s / n) := by
  rw [Real.mul_rpow hD.le (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * a) _),
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * a)]
  have hexp : (1 / n) * (-(n + 2 * s)) = -(n + 2 * s) / n := by ring
  rw [hexp, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha.le]
  have haExp : 1 + (-(n + 2 * s) / n) = -2 * s / n := by
    field_simp
    ring
  calc
    a * (D ^ (-(n + 2 * s)) *
        ((2 : ℝ) ^ (-(n + 2 * s) / n) * a ^ (-(n + 2 * s) / n))) =
      (D ^ (-(n + 2 * s)) * (2 : ℝ) ^ (-(n + 2 * s) / n)) *
        (a ^ (1 : ℝ) * a ^ (-(n + 2 * s) / n)) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add ha, haExp]

/-- Choosing a cube radius from a small set's measure leaves twice that measure locally. -/
theorem cube_small_set_radius {d : ℕ} (hd : 0 < d)
    (z x : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (a : ℝ) (ha : 0 < a) (hsmall : a ≤ (r / 2) ^ d / 2) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ρ ≤ r ∧
      ρ = 2 * (2 * a) ^ (1 / (d : ℝ)) ∧
      2 * a ≤ volume.real ((centeredCube x ρ hρ : Set (SpatialCoordinates d)) ∩
        (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  have hdReal : 0 < (d : ℝ) := by exact_mod_cast hd
  let ρ : ℝ := 2 * (2 * a) ^ (1 / (d : ℝ))
  have hρ : 0 < ρ := mul_pos (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
  have hroot : ((2 * a) ^ (1 / (d : ℝ))) ^ d = 2 * a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * a)]
    rw [div_mul_cancel₀ _ hdReal.ne', Real.rpow_one]
  have hrootR : (((r / 2) ^ d : ℝ) ^ (1 / (d : ℝ))) = r / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ r / 2)]
    rw [mul_one_div_cancel hdReal.ne', Real.rpow_one]
  have hle : (2 * a) ^ (1 / (d : ℝ)) ≤ r / 2 := by
    rw [← hrootR]
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have hρr : ρ ≤ r := by dsimp only [ρ]; linarith
  refine ⟨ρ, hρ, hρr, rfl, ?_⟩
  have hlocal := aux_campanato_cube_inter_volume_ge z x hr hρ hρr hx
  have hside : (ρ / 2) ^ d = 2 * a := by
    dsimp only [ρ]
    rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    exact hroot
  rwa [hside] at hlocal

/-- Cube version of DNPV Lemma 6.1, for upper level sets made small by an L2 cutoff. -/
theorem cube_complement_kernel_lower {d : ℕ} (hd : 0 < d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : ℝ)
    (hs : 0 < (d : ℝ) + 2 * s)
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A)
    (ha : 0 < (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) A).toReal)
    (hsmall : (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) A).toReal ≤
      (r / 2) ^ d / 2)
    (x : SpatialCoordinates d) (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))) :
    ENNReal.ofReal (cubeKernelLowerConstant d s *
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) A).toReal ^
        (-2 * s / (d : ℝ))) ≤
      ∫⁻ y in Aᶜ, fractionalKernel d s x y
        ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  let Q : Set (SpatialCoordinates d) := centeredCube z r hr
  let μ : Measure (SpatialCoordinates d) := volume.restrict Q
  let a : ℝ := (μ A).toReal
  have hdReal : 0 < (d : ℝ) := by exact_mod_cast hd
  have haPos : 0 < a := ha
  obtain ⟨ρ, hρ, hρr, hρdef, hlocal⟩ :=
    cube_small_set_radius hd z x r hr hx a haPos hsmall
  let B : Set (SpatialCoordinates d) :=
    (centeredCube x ρ hρ : Set (SpatialCoordinates d)) ∩ Q
  have hBmeas : MeasurableSet B :=
    (centeredCube x ρ hρ).isOpen.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet
  have hBsub : B ⊆ Q := Set.inter_subset_right
  have hμB : μ B = volume B := by
    dsimp only [μ]
    rw [Measure.restrict_apply hBmeas, Set.inter_eq_left.mpr hBsub]
  have hAlower : ENNReal.ofReal a = μ A := ENNReal.ofReal_toReal (measure_ne_top μ A)
  have hBlower : ENNReal.ofReal (2 * a) ≤ μ B := by
    apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ B)).mpr
    rw [hμB]
    exact hlocal
  have hdecomp : μ B ≤ μ A + μ (B \ A) := by
    calc
      μ B = μ ((B ∩ A) ∪ (B \ A)) := by rw [Set.inter_union_diff]
      _ ≤ μ (B ∩ A) + μ (B \ A) := measure_union_le _ _
      _ ≤ μ A + μ (B \ A) := add_le_add (measure_mono Set.inter_subset_right) le_rfl
  have hdiff : ENNReal.ofReal a ≤ μ (B \ A) := by
    apply ENNReal.le_of_add_le_add_left ENNReal.ofReal_ne_top
    calc
      ENNReal.ofReal a + ENNReal.ofReal a = ENNReal.ofReal (2 * a) := by
        rw [← ENNReal.ofReal_add haPos.le haPos.le]
        congr 1
        ring
      _ ≤ μ B := hBlower
      _ ≤ ENNReal.ofReal a + μ (B \ A) := by rw [hAlower]; exact hdecomp
  have hR : 0 < Real.sqrt d * ρ := mul_pos (Real.sqrt_pos.mpr hdReal) hρ
  let c : ℝ := (Real.sqrt d * ρ) ^ (-((d : ℝ) + 2 * s))
  have hc : 0 < c := Real.rpow_pos_of_pos hR _
  have hcinv : ENNReal.ofReal c =
      (ENNReal.ofReal (Real.sqrt d * ρ) ^ ((d : ℝ) + 2 * s))⁻¹ := by
    dsimp only [c]
    rw [Real.rpow_neg hR.le,
      ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hR _),
      ENNReal.ofReal_rpow_of_pos hR]
  have hpoint : ∀ y ∈ B \ A, ENNReal.ofReal c ≤ fractionalKernel d s x y := by
    intro y hy
    have hxlocal : x ∈ (centeredCube x ρ hρ : Set (SpatialCoordinates d)) := by
      change dist x x < ρ / 2
      simpa only [dist_self] using half_pos hρ
    have hdist := euclideanDist_le_sqrt_dim_mul_side_of_mem_centeredCube x hρ hxlocal hy.1.1
    rw [hcinv, fractionalKernel, one_div]
    exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal hdist) hs.le)
  have hidentity : a * c = cubeKernelLowerConstant d s * a ^ (-2 * s / (d : ℝ)) := by
    dsimp only [c, cubeKernelLowerConstant]
    rw [hρdef]
    have hmul : Real.sqrt d * (2 * (2 * a) ^ (1 / (d : ℝ))) =
        (2 * Real.sqrt d) * (2 * a) ^ (1 / (d : ℝ)) := by ring
    rw [hmul]
    exact kernel_radius_identity (d : ℝ) (2 * Real.sqrt d) a s hdReal (by positivity) haPos
  calc
    ENNReal.ofReal (cubeKernelLowerConstant d s * a ^ (-2 * s / (d : ℝ))) =
        ENNReal.ofReal c * ENNReal.ofReal a := by
      rw [← hidentity, ENNReal.ofReal_mul haPos.le, mul_comm]
    _ ≤ ENNReal.ofReal c * μ (B \ A) := mul_le_mul_right hdiff _
    _ = ∫⁻ y in B \ A, ENNReal.ofReal c ∂μ := by
      rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ∫⁻ y in B \ A, fractionalKernel d s x y ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (hBmeas.diff hA)] with y hy
      exact hpoint y hy
    _ ≤ ∫⁻ y in Aᶜ, fractionalKernel d s x y ∂μ :=
      lintegral_mono' (Measure.restrict_mono (fun _ hy => hy.2) le_rfl) le_rfl

end SubdiffusiveProcess.FractionalEmbedding
