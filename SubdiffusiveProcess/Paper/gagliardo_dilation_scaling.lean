module

public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.Paper.dilation_quasi_measure_preserving
public import SubdiffusiveProcess.Paper.cube_volume_scaling
public import SubdiffusiveProcess.Paper.gagliardo_dilation_double_integral
public import SubdiffusiveProcess.Paper.dilation_coefficient_transport

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_gagliardo_dilation_scaling_volume_real (d : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) = r ^ d := by
  exact centeredCube_volume_real z hr

theorem aux_gagliardo_dilation_scaling_norm
    (d : ℕ) (z z' : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (h1 : (0 : ℝ) < 1)
    (f : DomainL2 (centeredCube z r hr))
    (g : DomainL2 (centeredCube z' 1 h1))
    (hfg : ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      g x = f (cubeDilation z z' r x)) :
    ‖f‖ ^ 2 = r ^ d * ‖g‖ ^ 2 := by
  have hmeas : Measurable (cubeDilation z z' r) :=
    (continuous_cubeDilation z z' r).measurable
  have hmap := map_cubeDilation_restrict z z' hr h1
  have habs : |((r : ℝ) ^ d)⁻¹| = ((r : ℝ) ^ d)⁻¹ :=
    abs_of_pos (by positivity)
  have h1' : eLpNorm (fun x => (f : SpatialCoordinates d → ℝ) x) 2
        (Measure.map (cubeDilation z z' r)
          (volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d))))
      = eLpNorm (fun x => (f : SpatialCoordinates d → ℝ) (cubeDilation z z' r x)) 2
          (volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) := by
    refine eLpNorm_map_measure ?_ hmeas.aemeasurable
    rw [hmap]
    exact (Lp.aestronglyMeasurable f).smul_measure _
  have h2' : eLpNorm (fun x => (f : SpatialCoordinates d → ℝ) x) 2
        (ENNReal.ofReal |((r : ℝ) ^ d)⁻¹| •
          volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
      = (ENNReal.ofReal |((r : ℝ) ^ d)⁻¹|) ^ (1 / (2 : ℝ)) *
          eLpNorm (fun x => (f : SpatialCoordinates d → ℝ) x) 2
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    simpa using! eLpNorm_smul_measure_of_ne_top (p := (2 : ℝ≥0∞))
      (f := fun x => (f : SpatialCoordinates d → ℝ) x)
      (μ := volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
      (by norm_num) (ENNReal.ofReal |((r : ℝ) ^ d)⁻¹|) (Lp.aestronglyMeasurable f)
  have hgf : eLpNorm (fun x => (f : SpatialCoordinates d → ℝ) (cubeDilation z z' r x)) 2
        (volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)))
      = eLpNorm (fun x => (g : SpatialCoordinates d → ℝ) x) 2
          (volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d))) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [hfg] with x hx
    exact hx.symm
  rw [hmap, h2'] at h1'
  rw [hgf] at h1'
  have hpow : (ENNReal.ofReal (((r : ℝ) ^ d)⁻¹) ^ (1 / (2 : ℝ))).toReal
      = (((r : ℝ) ^ d)⁻¹) ^ (1 / (2 : ℝ)) := by
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (by positivity)]
  have hgn : ‖g‖ = (((r : ℝ) ^ d)⁻¹) ^ (1 / (2 : ℝ)) * ‖f‖ := by
    rw [Lp.norm_def, Lp.norm_def, ← h1', ENNReal.toReal_mul, habs, hpow]
  have hf2 : ‖g‖ ^ 2 = ((r : ℝ) ^ d)⁻¹ * ‖f‖ ^ 2 := by
    rw [hgn, mul_pow, ← Real.rpow_natCast ((((r : ℝ) ^ d)⁻¹) ^ (1 / (2 : ℝ))) 2,
      ← Real.rpow_mul (by positivity)]
    norm_num
  field_simp at hf2 ⊢
  linarith [hf2]

theorem aux_gagliardo_dilation_scaling_double_ae
    (d k : ℕ) (z' : SpatialCoordinates d) (h1 : (0 : ℝ) < 1) (s : ℝ)
    (G g : Fin k → SpatialCoordinates d → ℝ)
    (hg : ∀ i, ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      g i x = G i x) :
    (∫⁻ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin k, (G i x - G i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * s)) =
    (∫⁻ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin k, (g i x - g i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * s)) := by
  have hae : ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      ∀ i, g i x = G i x := by
    rw [ae_all_iff]
    exact hg
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with y hy
  have hsum : (∑ i : Fin k, (G i x - G i y) ^ 2) =
      ∑ i : Fin k, (g i x - g i y) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [hx i, hy i]
  rw [hsum]

/-- How the two summands of the normalized `H^s` norm scale under
`cubeDilation`.

Both are exact identities, not estimates, and they scale *differently* — which is the whole
point of doing them separately:

* the extended-valued normalized Gagliardo seminorm squared picks up `r ^ (-2s)`.  In the double integral
  `dx dy` contributes `r^(2d)`, `|x-y|^(d+2s)` contributes `r^(-(d+2s))`, and the
  normalizing factor `1/|Q_r|` contributes `r^(-d)`; the three combine to `r^(-2s)`.  At
  the order `s = 3/4` of `eq:mfd-1` this is the paper's `r^(-3/2)`;
* the normalized `L²` summand is **invariant**: `‖f‖²` over `Q_r` is `r^d` times `‖g‖²`
  over `Q_1`, and `|Q_r|` is `r^d` times `|Q_1|`, so the quotient is unchanged.  This is
  exactly what the normalization of `cubeFractionalVecSqNorm` was repaired to make true;
  with the earlier un-normalized `L²` summand it was false.  The principal conclusion uses
  `cubeFractionalL2Seminorm ^ 2` directly, rather than `cubeFractionalVecSeminormSq`,
  so that an infinite Gagliardo seminorm is not collapsed by `ENNReal.toReal`.

The hypothesis is the a.e. tie `g i = f i ∘ T` on the unit cube, whose supplier for
coefficients is `\noderef{dilation_coefficient_transport}` and whose
measure-theoretic engine is `\noderef{dilation_quasi_measure_preserving}`.

The companion scaling `E^{Q_r}(u) = r^(d-2) E^{Q_1}(u ∘ T)` for `sobolevCoefficientForm`
is **not** stated here: it needs the chain rule for the weak gradient under an affine map,
which is a different piece of machinery. -/
theorem gagliardo_dilation_scaling :
  ∀ (d k : ℕ) (hd : 2 ≤ d) (z z' : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (h1 : (0 : ℝ) < 1) (s : Set.Ioo (0 : ℝ) 1)
    (f : Fin k → DomainL2 (centeredCube z r hr))
    (g : Fin k → DomainL2 (centeredCube z' 1 h1)),
    (∀ i, ∀ᵐ x ∂volume.restrict (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
      g i x = f i (cubeDilation z z' r x)) →
    (cubeFractionalL2Seminorm hd z r hr s f) ^ (2 : ℕ) =
        ENNReal.ofReal (r ^ (-(2 * (s : ℝ)))) *
          (cubeFractionalL2Seminorm hd z' 1 h1 s g) ^ (2 : ℕ) ∧
      (∑ i : Fin k, ‖f i‖ ^ 2) /
          volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) =
        (∑ i : Fin k, ‖g i‖ ^ 2) /
          volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) := by
  intro d k hd z z' r hr h1 s f g hfg
  have hsq_half (x : ℝ≥0∞) : (x ^ (1/2 : ℝ)) ^ (2 : ℕ) = x := by
    by_cases hx0 : x = 0
    · subst x; simp
    · by_cases hx_top : x = ∞
      · subst x; simp
      · calc
          (x ^ (1/2 : ℝ)) ^ (2 : ℕ) = (x ^ (1/2 : ℝ)) ^ (2 : ℝ) := by
            simp
          _ = x ^ ((1/2 : ℝ) * (2 : ℝ)) := by
            rw [ENNReal.rpow_mul x (1/2 : ℝ) (2 : ℝ)]
          _ = x ^ (1 : ℝ) := by ring
          _ = x := by simp
  have hvolr : volume (centeredCube z r hr : Set (SpatialCoordinates d)) =
      ENNReal.ofReal (r ^ d) := centeredCube_volume z hr
  have hvol1 : volume (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) = 1 := by
    rw [centeredCube_volume]
    simp
  have hfactor :
      ENNReal.ofReal (r ^ ((d : ℝ) - 2 * (s : ℝ))) *
          (ENNReal.ofReal (r ^ ((d : ℝ))))⁻¹ =
        ENNReal.ofReal (r ^ (-(2 * (s : ℝ)))) := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity : 0 < r ^ ((d : ℝ)))]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.rpow_neg hr.le]
    field_simp
    rw [← Real.rpow_add hr]
    ring
  have hdouble := gagliardo_dilation_double_integral d k z z' r hr h1
    (s : ℝ) s.2.1
    (fun i x => (f i : SpatialCoordinates d → ℝ) x)
    (fun i x => (f i : SpatialCoordinates d → ℝ) (cubeDilation z z' r x))
    (by intro i x; rfl)
  have hDI :
      (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal (∑ i : Fin k,
            ((f i : SpatialCoordinates d → ℝ) x - (f i : SpatialCoordinates d → ℝ) y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (s : ℝ))) =
      ENNReal.ofReal (r ^ ((d : ℝ) - 2 * (s : ℝ))) *
        (∫⁻ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
            ENNReal.ofReal (∑ i : Fin k, ((g i : SpatialCoordinates d → ℝ) x -
              (g i : SpatialCoordinates d → ℝ) y) ^ 2) /
              (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                ((d : ℝ) + 2 * (s : ℝ))) := by
    calc
      _ = ENNReal.ofReal (r ^ ((d : ℝ) - 2 * (s : ℝ))) *
          (∫⁻ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
            ∫⁻ y in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
              ENNReal.ofReal (∑ i : Fin k,
                (((f i : SpatialCoordinates d → ℝ) (cubeDilation z z' r x)) -
                  ((f i : SpatialCoordinates d → ℝ) (cubeDilation z z' r y))) ^ 2) /
                (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                  ((d : ℝ) + 2 * (s : ℝ))) := by
                simpa only using hdouble
      _ = _ := by
        rw [aux_gagliardo_dilation_scaling_double_ae d k z' h1 (s : ℝ)
          (fun i x => (f i : SpatialCoordinates d → ℝ) (cubeDilation z z' r x))
          (fun i x => (g i : SpatialCoordinates d → ℝ) x) hfg]
  have hfirst : (cubeFractionalL2Seminorm hd z r hr s f) ^ (2 : ℕ) =
      ENNReal.ofReal (r ^ (-(2 * (s : ℝ)))) *
        (cubeFractionalL2Seminorm hd z' 1 h1 s g) ^ (2 : ℕ) := by
    unfold cubeFractionalL2Seminorm
    rw [hsq_half, hsq_half]
    rw [hDI]
    rw [hvolr, hvol1]
    have hrd : ENNReal.ofReal (r ^ d) =
        ENNReal.ofReal (r ^ ((d : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    rw [hrd]
    simp only [div_one]
    rw [div_eq_mul_inv]
    calc
      (ENNReal.ofReal (s : ℝ) * ((ENNReal.ofReal (r ^ ((d : ℝ))))⁻¹)) *
            (ENNReal.ofReal (r ^ ((d : ℝ) - 2 * (s : ℝ))) *
              (∫⁻ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
                ∫⁻ y in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
                  ENNReal.ofReal (∑ i : Fin k, ((g i : SpatialCoordinates d → ℝ) x -
                    (g i : SpatialCoordinates d → ℝ) y) ^ 2) /
                    (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                      ((d : ℝ) + 2 * (s : ℝ)))) =
          (ENNReal.ofReal (r ^ ((d : ℝ) - 2 * (s : ℝ))) *
            ((ENNReal.ofReal (r ^ ((d : ℝ))))⁻¹)) *
              (ENNReal.ofReal (s : ℝ) *
                (∫⁻ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
                  ∫⁻ y in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
                    ENNReal.ofReal (∑ i : Fin k, ((g i : SpatialCoordinates d → ℝ) x -
                      (g i : SpatialCoordinates d → ℝ) y) ^ 2) /
                      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                        ((d : ℝ) + 2 * (s : ℝ)))) := by ring
      _ = ENNReal.ofReal (r ^ (-(2 * (s : ℝ)))) *
            (ENNReal.ofReal (s : ℝ) *
              (∫⁻ x in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
                ∫⁻ y in (centeredCube z' 1 h1 : Set (SpatialCoordinates d)),
                  ENNReal.ofReal (∑ i : Fin k, ((g i : SpatialCoordinates d → ℝ) x -
                    (g i : SpatialCoordinates d → ℝ) y) ^ 2) /
                    (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                      ((d : ℝ) + 2 * (s : ℝ)))) := by rw [hfactor]
  have hsecond : (∑ i : Fin k, ‖f i‖ ^ 2) /
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (∑ i : Fin k, ‖g i‖ ^ 2) /
        volume.real (centeredCube z' 1 h1 : Set (SpatialCoordinates d)) := by
    have hnorm : ∀ i : Fin k, ‖f i‖ ^ 2 = r ^ d * ‖g i‖ ^ 2 := by
      intro i
      exact aux_gagliardo_dilation_scaling_norm d z z' hr h1 (f i) (g i) (hfg i)
    have hvolr' := aux_gagliardo_dilation_scaling_volume_real d z hr
    have hvol1' := aux_gagliardo_dilation_scaling_volume_real d z' h1
    rw [hvolr', hvol1']
    rw [Finset.sum_congr rfl (fun i _ => hnorm i)]
    field_simp
    rw [← Finset.mul_sum]
    simp
  exact And.intro hfirst hsecond

end SubdiffusiveProcess.Paper
