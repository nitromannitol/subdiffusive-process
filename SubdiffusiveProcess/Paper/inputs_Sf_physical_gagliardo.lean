module

public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Lane2.ExternalInputs
public import SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable
public import Homogenization.Sobolev.Fractional.ExactOverlapScalarComparison
public import Homogenization.Sobolev.Fractional.GagliardoLeBesov
public import SubdiffusiveProcess.Lane4.CubeDilation
public import Homogenization.Besov.Negative.ExactFiniteBridge

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

private theorem aux_inputs_Sf_physical_gagliardo_double_integral_dilation
    (d k : ℕ) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1) (s : ℝ) (hs : 0 < s)
    (F G : Fin k → SpatialCoordinates d → ℝ)
    (hG : ∀ i x, G i x = F i (SubdiffusiveProcess.Lane4.cubeDilation z z' r x)) :
    (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin k, (F i x - F i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * s)) =
      ENNReal.ofReal (r ^ ((d : ℝ) - 2 * s)) *
        (∫⁻ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
            ENNReal.ofReal (∑ i : Fin k, (G i x - G i y) ^ 2) /
              (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                ((d : ℝ) + 2 * s)) := by
  have hepos : (0 : ℝ) < (d : ℝ) + 2 * s := by positivity
  set c : ℝ≥0∞ := (ENNReal.ofReal r) ^ ((d : ℝ) + 2 * s) with hcdef
  have hor : ENNReal.ofReal r ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hr
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    exact fun h => hor (by
      rcases ENNReal.rpow_eq_zero_iff.1 h with ⟨h', _⟩ | ⟨h', _⟩
      · exact h'
      · exact absurd h' ENNReal.ofReal_ne_top)
  have hctop : c ≠ ⊤ := by
    rw [hcdef]
    exact fun h => by
      rcases ENNReal.rpow_eq_top_iff.1 h with ⟨h', _⟩ | ⟨h', _⟩
      · exact hor h'
      · exact ENNReal.ofReal_ne_top h'
  have hkernel : ∀ x0 y0 : SpatialCoordinates d,
      ENNReal.ofReal (∑ i : Fin k,
          (F i (SubdiffusiveProcess.Lane4.cubeDilation z z' r x0) -
            F i (SubdiffusiveProcess.Lane4.cubeDilation z z' r y0)) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
          (SubdiffusiveProcess.Lane4.cubeDilation z z' r x0 j -
            SubdiffusiveProcess.Lane4.cubeDilation z z' r y0 j) ^ 2))) ^
            ((d : ℝ) + 2 * s) =
      c⁻¹ * (ENNReal.ofReal (∑ i : Fin k, (G i x0 - G i y0) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x0 j - y0 j) ^ 2))) ^
          ((d : ℝ) + 2 * s)) := by
    intro x0 y0
    have hnum : (∑ i : Fin k,
        (F i (SubdiffusiveProcess.Lane4.cubeDilation z z' r x0) -
          F i (SubdiffusiveProcess.Lane4.cubeDilation z z' r y0)) ^ 2) =
        ∑ i : Fin k, (G i x0 - G i y0) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [hG i x0, hG i y0]
    rw [hnum, SubdiffusiveProcess.Lane4.sqrt_sum_sq_cubeDilation z z' hr x0 y0,
      ENNReal.ofReal_mul hr.le, ENNReal.mul_rpow_of_nonneg _ _ hepos.le,
      ← hcdef, div_eq_mul_inv, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop)]
    ring
  rw [SubdiffusiveProcess.Lane4.lintegral_centeredCube_cubeDilation z z' hr h1
    (fun x => ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal (∑ i : Fin k, (F i x - F i y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * s))]
  have hstep : ∀ x0 : SpatialCoordinates d,
      (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin k,
          (F i (SubdiffusiveProcess.Lane4.cubeDilation z z' r x0) - F i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
            (SubdiffusiveProcess.Lane4.cubeDilation z z' r x0 j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * s)) =
      ENNReal.ofReal (r ^ d) * (c⁻¹ *
        ∫⁻ y0 in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
          ENNReal.ofReal (∑ i : Fin k, (G i x0 - G i y0) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x0 j - y0 j) ^ 2))) ^
              ((d : ℝ) + 2 * s)) := by
    intro x0
    rw [SubdiffusiveProcess.Lane4.lintegral_centeredCube_cubeDilation z z' hr h1
      (fun y => ENNReal.ofReal (∑ i : Fin k,
        (F i (SubdiffusiveProcess.Lane4.cubeDilation z z' r x0) - F i y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d,
          (SubdiffusiveProcess.Lane4.cubeDilation z z' r x0 j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * s))]
    congr 1
    rw [← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0)]
    exact lintegral_congr fun y0 => hkernel x0 y0
  rw [lintegral_congr hstep, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), ← mul_assoc, ← mul_assoc]
  congr 1
  have hconst : ENNReal.ofReal (r ^ d) * ENNReal.ofReal (r ^ d) * c⁻¹ =
      ENNReal.ofReal (r ^ ((d : ℝ) - 2 * s)) := by
    have hrd : ENNReal.ofReal (r ^ d) = ENNReal.ofReal (r ^ ((d : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    have hcr : c = ENNReal.ofReal (r ^ ((d : ℝ) + 2 * s)) := by
      rw [hcdef, ← ENNReal.ofReal_rpow_of_pos hr]
    rw [hrd, hcr, ← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.rpow_neg hr.le, ← Real.rpow_add hr, ← Real.rpow_add hr]
    congr 1
    ring
  exact hconst

private theorem aux_inputs_Sf_physical_gagliardo_unit_euclidean_le_gagliardo
    (d : ℕ) [NeZero d] (u : SpatialCoordinates d → ℝ) (hu : Measurable u) :
    (∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
        Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
        Set (SpatialCoordinates d)),
        ENNReal.ofReal ((u x - u y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (3 / 4 : ℝ))) ≤
      Homogenization.Gagliardo.cubeGagliardoESeminorm
        (Homogenization.originCube d 0) (3 / 4) (2 : ℝ≥0∞) u ^ 2 := by
  let Q := Homogenization.originCube d 0
  let U : Set (SpatialCoordinates d) :=
    centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)
  let μ : Measure (SpatialCoordinates d) := volume.restrict U
  have hscale : Homogenization.cubeScaleFactor Q = 1 := by simp [Q]
  have hpos : 0 < Homogenization.cubeScaleFactor Q := by rw [hscale]; norm_num
  have hvol : Homogenization.cubeVolume Q = 1 := by
    simp [Homogenization.cubeVolume, hscale]
  have hcube : Homogenization.cubeMeasure Q = μ := by
    have h := SubdiffusiveProcess.centeredCube_restrict_volume_eq_cubeMeasure Q hpos
    have hcenter : Homogenization.cubeCenter Q = (0 : SpatialCoordinates d) := by
      funext i
      simp [Q, Homogenization.cubeCenter, Homogenization.originCube,
        Homogenization.cubeScaleFactor]
    simpa only [hcenter, hscale, U, μ] using h.symm
  have hnorm : Homogenization.normalizedCubeMeasure Q = μ := by
    rw [Homogenization.normalizedCubeMeasure, hvol, hcube]
    simp
  have hmeasure :
      Homogenization.Gagliardo.gagliardoCubeMeasure Q = μ.prod μ := by
    rw [Homogenization.Gagliardo.gagliardoCubeMeasure, hnorm, hcube]
  have hkernel_meas : Measurable
      (Homogenization.Gagliardo.gagliardoKernel (3 / 4) (2 : ℝ≥0∞) u) := by
    unfold Homogenization.Gagliardo.gagliardoKernel
    have hw : Measurable (fun z : SpatialCoordinates d × SpatialCoordinates d =>
        dist z.1 z.2 ^ (-Homogenization.Gagliardo.kernelExponent d (3 / 4) 2)) :=
      measurable_dist.pow measurable_const
    simpa only [smul_eq_mul] using!
      hw.mul ((hu.comp measurable_fst).sub (hu.comp measurable_snd))
  have hkernel_sq_meas : Measurable (fun z : SpatialCoordinates d × SpatialCoordinates d =>
      ‖Homogenization.Gagliardo.gagliardoKernel (3 / 4) (2 : ℝ≥0∞) u z‖ₑ ^ 2) :=
    hkernel_meas.enorm.pow measurable_const
  have hprod :
      (∫⁻ z : SpatialCoordinates d × SpatialCoordinates d,
        ‖Homogenization.Gagliardo.gagliardoKernel (3 / 4)
          (2 : ℝ≥0∞) u z‖ₑ ^ 2 ∂(μ.prod μ)) =
      ∫⁻ x in U, ∫⁻ y in U,
        ‖Homogenization.Gagliardo.gagliardoKernel (3 / 4)
          (2 : ℝ≥0∞) u (x, y)‖ₑ ^ 2 := by
    have h := MeasureTheory.lintegral_prod (μ := μ) (ν := μ)
      (fun z : SpatialCoordinates d × SpatialCoordinates d =>
        ‖Homogenization.Gagliardo.gagliardoKernel (3 / 4)
          (2 : ℝ≥0∞) u z‖ₑ ^ 2) hkernel_sq_meas.aemeasurable
    simpa only [μ, U] using h
  have hgsqReal :
      Homogenization.Gagliardo.cubeGagliardoESeminorm Q (3 / 4)
          (2 : ℝ≥0∞) u ^ (2 : ℝ) =
        ∫⁻ x in U, ∫⁻ y in U,
          ‖Homogenization.Gagliardo.gagliardoKernel (3 / 4)
            (2 : ℝ≥0∞) u (x, y)‖ₑ ^ 2 := by
    rw [Homogenization.Gagliardo.Internal.cubeGagliardoESeminorm_eq_lintegral
      (by norm_num) (by norm_num) hkernel_meas.aestronglyMeasurable]
    rw [← ENNReal.rpow_mul]
    norm_num
    rw [hmeasure, hprod]
  have hgsq :
      Homogenization.Gagliardo.cubeGagliardoESeminorm Q (3 / 4)
          (2 : ℝ≥0∞) u ^ 2 =
        ∫⁻ x in U, ∫⁻ y in U,
          ‖Homogenization.Gagliardo.gagliardoKernel (3 / 4)
            (2 : ℝ≥0∞) u (x, y)‖ₑ ^ 2 := by
    calc
      _ = Homogenization.Gagliardo.cubeGagliardoESeminorm Q (3 / 4)
            (2 : ℝ≥0∞) u ^ (2 : ℝ) := by
              simpa using (ENNReal.rpow_natCast
                (Homogenization.Gagliardo.cubeGagliardoESeminorm Q (3 / 4)
                  (2 : ℝ≥0∞) u) 2).symm
      _ = _ := hgsqReal
  have hpoint : ∀ x y : SpatialCoordinates d,
      ENNReal.ofReal ((u x - u y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (3 / 4 : ℝ)) ≤
        ‖Homogenization.Gagliardo.gagliardoKernel (3 / 4)
          (2 : ℝ≥0∞) u (x, y)‖ₑ ^ 2 := by
    intro x y
    let a : ℝ := (d : ℝ) + 2 * (3 / 4 : ℝ)
    let A : ℝ := (u x - u y) ^ 2
    have ha : 0 < a := by dsimp [a]; positivity
    have hkernel := Homogenization.Gagliardo.enorm_gagliardoKernel_rpow
      (3 / 4 : ℝ) (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) u (x, y)
    have hdiff : ‖u x - u y‖ₑ ^ (2 : ℕ) = ENNReal.ofReal A := by
      rw [Real.enorm_eq_ofReal_abs,
        ← ENNReal.ofReal_pow (abs_nonneg (u x - u y)), sq_abs]
    have hcomp :
        ENNReal.ofReal (A / Real.rpow (euclideanDist x y) a) ≤
          ENNReal.ofReal (dist x y ^ (-a)) * ENNReal.ofReal A := by
      change ENNReal.ofReal (A / Real.rpow (euclideanDist x y) a) ≤
        ENNReal.ofReal (dist x y ^ (-a)) * ENNReal.ofReal A
      by_cases hxy : x = y
      · subst y
        simp [A]
      · have hdist : 0 < dist x y := dist_pos.mpr hxy
        have heuclidean : 0 < euclideanDist x y := by
          apply lt_of_le_of_ne (euclideanDist_nonneg x y)
          intro hzero
          exact hxy (euclideanDist_eq_zero_iff.mp hzero.symm)
        have hpow : Real.rpow (euclideanDist x y) (-a) ≤
            Real.rpow (dist x y) (-a) :=
          Real.rpow_le_rpow_of_nonpos hdist (dist_le_euclideanDist x y)
            (neg_nonpos.mpr ha.le)
        have hneg : Real.rpow (euclideanDist x y) (-a) =
            (Real.rpow (euclideanDist x y) a)⁻¹ := Real.rpow_neg heuclidean.le a
        have hA : 0 ≤ A := sq_nonneg _
        have hreal : A / Real.rpow (euclideanDist x y) a ≤
            Real.rpow (dist x y) (-a) * A := by
          calc
            A / Real.rpow (euclideanDist x y) a =
                Real.rpow (euclideanDist x y) (-a) * A := by
                  rw [div_eq_mul_inv, hneg]
                  ring
            _ ≤ Real.rpow (dist x y) (-a) * A := mul_le_mul_of_nonneg_right hpow hA
        calc
          ENNReal.ofReal (A / Real.rpow (euclideanDist x y) a) ≤
              ENNReal.ofReal (Real.rpow (dist x y) (-a) * A) :=
            ENNReal.ofReal_le_ofReal hreal
          _ = ENNReal.ofReal (dist x y ^ (-a)) * ENNReal.ofReal A := by
            rw [← ENNReal.ofReal_mul (Real.rpow_nonneg dist_nonneg (-a))]
            rfl
    have hkernel' :
        ‖Homogenization.Gagliardo.gagliardoKernel (3 / 4)
          (2 : ℝ≥0∞) u (x, y)‖ₑ ^ 2 =
        ENNReal.ofReal (dist x y ^ (-a)) * ENNReal.ofReal A := by
      have h := hkernel
      norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, ENNReal.rpow_two] at h
      rw [hdiff] at h
      convert h using 2 <;> congr 1 <;> ring_nf
      all_goals
        congr 1
        dsimp [a]
        ring
    calc
      _ ≤ ENNReal.ofReal (dist x y ^ (-a)) * ENNReal.ofReal A := by
        by_cases hxy : x = y
        · subst y
          simp [A]
        · have heuclidean : 0 < euclideanDist x y := by
            apply lt_of_le_of_ne (euclideanDist_nonneg x y)
            intro hzero
            exact hxy (euclideanDist_eq_zero_iff.mp hzero.symm)
          have hfrac :
              ENNReal.ofReal (A / Real.rpow (euclideanDist x y) a) =
                ENNReal.ofReal A /
                  (ENNReal.ofReal (euclideanDist x y)) ^ a := by
            change ENNReal.ofReal (A / ((euclideanDist x y) ^ a)) = _
            rw [ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos heuclidean a),
              ← ENNReal.ofReal_rpow_of_nonneg (euclideanDist_nonneg x y) ha.le]
          calc
            _ = ENNReal.ofReal (A / Real.rpow (euclideanDist x y) a) := by
              have heuc : euclideanDist x y =
                  Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
                simp [Homogenization.euclideanDist, Homogenization.euclideanNorm,
                  Homogenization.vecNormSq, Homogenization.vecDot, Pi.sub_apply, pow_two]
              simpa [A, a, heuc] using hfrac.symm
            _ ≤ ENNReal.ofReal (dist x y ^ (-a)) * ENNReal.ofReal A := by
              simpa [A] using hcomp
      _ = ‖Homogenization.Gagliardo.gagliardoKernel (3 / 4)
            (2 : ℝ≥0∞) u (x, y)‖ₑ ^ 2 := by
        exact hkernel'.symm
  calc
    (∫⁻ x in U, ∫⁻ y in U,
        ENNReal.ofReal ((u x - u y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (3 / 4 : ℝ))) ≤
      ∫⁻ x in U, ∫⁻ y in U,
        ‖Homogenization.Gagliardo.gagliardoKernel (3 / 4)
          (2 : ℝ≥0∞) u (x, y)‖ₑ ^ 2 := by
            apply lintegral_mono
            intro x
            apply lintegral_mono
            intro y
            exact hpoint x y
    _ = Homogenization.Gagliardo.cubeGagliardoESeminorm Q (3 / 4)
          (2 : ℝ≥0∞) u ^ 2 := hgsq.symm

theorem inputs_Sf_physical_gagliardo (d : ℕ) (hd : 2 ≤ d) :
    (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (v : DomainL2 (centeredCube z r hr)),
      (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder (fun _ : Fin 1 => v)) ^ 2 ≤
        ENNReal.ofReal ((3 / 4 : ℝ) * r ^ (-(3 / 2) : ℝ)) *
          (Homogenization.Gagliardo.cubeGagliardoESeminorm (Homogenization.originCube d 0)
            (3 / 4) (2 : ℝ≥0∞) (fun x => v (fun i : Fin d => z i + r * x i))) ^ 2) := by
  letI : NeZero d := ⟨by omega⟩
  intro z r hr v
  let F : Fin 1 → SpatialCoordinates d → ℝ := fun _ => v
  let G : Fin 1 → SpatialCoordinates d → ℝ := fun _ x => v (fun i => z i + r * x i)
  have hDilation := aux_inputs_Sf_physical_gagliardo_double_integral_dilation
    d 1 z 0 r hr (by norm_num) (3 / 4) (by norm_num) F G (by
      intro i x
      dsimp [F, G, SubdiffusiveProcess.Lane4.cubeDilation]
      congr 1
      funext j
      simp)
  have hmeas : Measurable (fun x : SpatialCoordinates d => v (fun i => z i + r * x i)) :=
    (Lp.stronglyMeasurable v).measurable.comp (by fun_prop)
  have hunit := aux_inputs_Sf_physical_gagliardo_unit_euclidean_le_gagliardo d
    (fun x => v (fun i => z i + r * x i)) hmeas
  simp only [F, G, Fin.sum_univ_one] at hDilation
  have hhalf (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
    simpa using ENNReal.rpow_inv_natCast_pow (n := 2) (by decide) x
  unfold cubeFractionalL2Seminorm
  rw [hhalf]
  simp only [threeQuarterOrder, Fin.sum_univ_one]
  rw [hDilation, centeredCube_volume]
  rw [← mul_assoc]
  have hcoeff : ENNReal.ofReal (3 / 4 : ℝ) / ENNReal.ofReal (r ^ d) *
      ENNReal.ofReal (r ^ ((d : ℝ) - 2 * (3 / 4 : ℝ))) =
      ENNReal.ofReal ((3 / 4 : ℝ) * r ^ (-(3 / 2) : ℝ)) := by
    rw [← ENNReal.ofReal_div_of_pos (pow_pos hr _),
      ← ENNReal.ofReal_mul (div_nonneg (by norm_num) (pow_nonneg hr.le _))]
    congr 1
    rw [Real.rpow_sub hr, Real.rpow_natCast]
    have hp : r ^ d ≠ 0 := (pow_pos hr _).ne'
    have hq : r ^ (2 * (3 / 4 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
    rw [Real.rpow_neg hr.le]
    have he : (2 * (3 / 4 : ℝ)) = 3 / 2 := by norm_num
    rw [he] at *
    field_simp
  rw [hcoeff]
  exact mul_le_mul_right hunit _

end Paper

