import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedLocalSobolevMassCore
import SubdiffusiveProcess.Section9.BesovRestriction
import Homogenization.Besov.Duality.Full
import Mathlib.Analysis.SpecificLimits.Basic
/-!
# From the paper negative Besov test to half-order forcing duality

The full norm is controlled through its finite partial sums; no conversion
of an infinite ENNReal value to a real number is used.
-/

set_option autoImplicit false
open Homogenization MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Section9
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support
open scoped ENNReal BigOperators
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- The paper test controls the full half-order negative norm, including depth zero. -/
theorem goodCube_negative_half_norm_le_paper_test
    {d : ℕ} (hd : 2 ≤ d) (Q : TriadicCube d) (g : Vec d → ℝ)
    (hg : MemLp g (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hf : ExactCircIntegrable Q g) {zeta : ℝ} (hzeta : 0 ≤ zeta)
    (hBesov : ENNReal.ofReal ((3 : ℝ) ^ (-((Q.scale : ℝ) / 8))) *
      paperNegativeBesovCircDiagonal Q (1 / 8) (4 * (d : ℝ)) g hf ≤
        ENNReal.ofReal zeta) :
    cubeBesovCircNorm Q (1 / 2) (2 : ℝ≥0∞) (1 : ℝ≥0∞) g ≤
      8 * (1 - (3 : ℝ) ^ (-(3 / 8 : ℝ)))⁻¹ * zeta *
        cubeBesovScaleWeight (-1 / 2) Q := by
  have hdR : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hPpos : (0:ℝ) < (4*(d:ℝ):ℝ) := by linarith
  have h1leP : (1:ℝ) ≤ (4*(d:ℝ):ℝ) := by linarith
  have h2ltP : (2:ℝ) < (4*(d:ℝ):ℝ) := by linarith
  have hp2 : (1:ℝ) ≤ 2 := by norm_num
  have hp2pos : (0:ℝ) < 2 := by norm_num
  have h3pos : (0:ℝ) < (3:ℝ) := by norm_num
  have htwo : (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) := by
    norm_num
  have hmem : MeasureTheory.MemLp g (ENNReal.ofReal (2:ℝ)) (normalizedCubeMeasure Q) := by
    simpa using hg
  have h3of : (3:ℝ≥0∞) = ENNReal.ofReal (3:ℝ) := by
    norm_num
  have hhalf : ((3:ℝ≥0∞) ^ (-((Q.scale:ℝ) * (1/2:ℝ)))) =
      ENNReal.ofReal (((3:ℝ) ^ (-((Q.scale:ℝ) * (1/2:ℝ))))) := by
    rw [show (3:ℝ≥0∞) = ENNReal.ofReal (3:ℝ) from h3of, ENNReal.ofReal_rpow_of_pos h3pos]
  have hc8 : ((3:ℝ≥0∞) ^ (-((Q.scale:ℝ) * (1/8:ℝ)))) =
      ENNReal.ofReal (((3:ℝ) ^ (-((Q.scale:ℝ) / 8)))) := by
    have he8 : ((Q.scale:ℝ) * ((1:ℝ)/8)) = ((Q.scale:ℝ) / 8) := by ring
    rw [show (3:ℝ≥0∞) = ENNReal.ofReal (3:ℝ) from h3of, ENNReal.ofReal_rpow_of_pos h3pos, he8]
  have hrho_eq : ((3:ℝ≥0∞) ^ (-((1:ℝ)/2 - 1/8))) =
      ENNReal.ofReal (((3:ℝ) ^ (-((1:ℝ)/2 - 1/8)))) := by
    rw [show (3:ℝ≥0∞) = ENNReal.ofReal (3:ℝ) from h3of, ENNReal.ofReal_rpow_of_pos h3pos]
  have hhalfpos : (0:ℝ) < (3:ℝ) ^ (-((Q.scale:ℝ) * (1/2:ℝ))) :=
    Real.rpow_pos_of_pos h3pos _
  -- Control every source depth by the full paper norm.
  have hstep1 : ∀ j : ℕ, ENNReal.ofReal ((3:ℝ) ^ (-((Q.scale:ℝ) / 8))) *
      exactCircDepthTerm Q ((1:ℝ)/8) ((4*(d:ℝ):ℝ)) g hf j ≤ ENNReal.ofReal (8*zeta) := by
    intro j
    have hWj := weightedSobolev_depth_single Q ((1:ℝ)/8) ((4*(d:ℝ):ℝ)) hPpos g hf j
    have hone8 : (1:ℝ≥0∞) ≤ ENNReal.ofReal (8:ℝ) := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0:ℝ) ≤ (8:ℝ))).mpr
        (by norm_num : (1:ℝ) ≤ (8:ℝ))
    have key : ENNReal.ofReal (8:ℝ) ≤ (ENNReal.ofReal (8:ℝ)) ^ ((4*(d:ℝ):ℝ)) := by
      have h2 := ENNReal.rpow_le_rpow_of_exponent_le hone8 h1leP
      rwa [ENNReal.rpow_one] at h2
    have h8 : ENNReal.ofReal (8:ℝ) * ENNReal.ofReal ((1:ℝ)/8) = 1 := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ (8:ℝ)),
        show (8:ℝ) * ((1:ℝ)/8) = 1 from by norm_num, ENNReal.ofReal_one]
    have hge : (1:ℝ≥0∞) ≤ (ENNReal.ofReal (8:ℝ)) ^ ((4*(d:ℝ):ℝ)) * ENNReal.ofReal ((1:ℝ)/8) := by
      have h4 := mul_le_mul_left key (ENNReal.ofReal ((1:ℝ)/8))
      rwa [h8] at h4
    have hB : exactCircDepthTerm Q ((1:ℝ)/8) ((4*(d:ℝ):ℝ)) g hf j ≤
        ENNReal.ofReal (8:ℝ) * paperNegativeBesovCircDiagonal Q ((1:ℝ)/8) ((4*(d:ℝ):ℝ)) g hf := by
      have h3 : exactCircDepthTerm Q ((1:ℝ)/8) ((4*(d:ℝ):ℝ)) g hf j ^ ((4*(d:ℝ):ℝ)) ≤
          (ENNReal.ofReal (8:ℝ)) ^ ((4*(d:ℝ):ℝ)) *
            paperNegativeBesovCircDiagonal Q ((1:ℝ)/8) ((4*(d:ℝ):ℝ)) g hf ^ ((4*(d:ℝ):ℝ)) := by
        have h3a := mul_le_mul_right hWj ((ENNReal.ofReal (8:ℝ)) ^ ((4*(d:ℝ):ℝ)))
        have h3b : exactCircDepthTerm Q ((1:ℝ)/8) ((4*(d:ℝ):ℝ)) g hf j ^ ((4*(d:ℝ):ℝ)) ≤
            (ENNReal.ofReal (8:ℝ)) ^ ((4*(d:ℝ):ℝ)) *
              (ENNReal.ofReal ((1:ℝ)/8) *
                exactCircDepthTerm Q ((1:ℝ)/8) ((4*(d:ℝ):ℝ)) g hf j ^ ((4*(d:ℝ):ℝ))) := by
          have h5 := mul_le_mul_left hge
            (exactCircDepthTerm Q ((1:ℝ)/8) ((4*(d:ℝ):ℝ)) g hf j ^ ((4*(d:ℝ):ℝ)))
          rw [one_mul, mul_assoc] at h5
          exact h5
        exact le_trans h3b h3a
      exact (ENNReal.rpow_le_rpow_iff hPpos).mp
        (le_trans h3 (le_of_eq (ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal (8:ℝ))
          (paperNegativeBesovCircDiagonal Q ((1:ℝ)/8) ((4*(d:ℝ):ℝ)) g hf)
          (le_of_lt hPpos)).symm))
    calc ENNReal.ofReal ((3:ℝ) ^ (-((Q.scale:ℝ) / 8))) *
          exactCircDepthTerm Q ((1:ℝ)/8) ((4*(d:ℝ):ℝ)) g hf j
        ≤ ENNReal.ofReal ((3:ℝ) ^ (-((Q.scale:ℝ) / 8))) *
            (ENNReal.ofReal (8:ℝ) *
              paperNegativeBesovCircDiagonal Q ((1:ℝ)/8) ((4*(d:ℝ):ℝ)) g hf) :=
          mul_le_mul_right hB _
      _ = ENNReal.ofReal (8:ℝ) * (ENNReal.ofReal ((3:ℝ) ^ (-((Q.scale:ℝ) / 8))) *
            paperNegativeBesovCircDiagonal Q ((1:ℝ)/8) ((4*(d:ℝ):ℝ)) g hf) := by ring
      _ ≤ ENNReal.ofReal (8:ℝ) * ENNReal.ofReal (zeta) := mul_le_mul_right hBesov _
      _ = ENNReal.ofReal (8*zeta) := (ENNReal.ofReal_mul (by linarith)).symm
  -- Restrict the exponent and sum the extra geometric decay.
  have hcomb : ∀ j : ℕ, ENNReal.ofReal ((3:ℝ) ^ (-((Q.scale:ℝ) * (1/2:ℝ)))) *
      ENNReal.ofReal (cubeBesovCircDepthSeminorm Q ((1:ℝ)/2) (2:ℝ≥0∞) g j) ≤
      ((3:ℝ≥0∞) ^ (-((1:ℝ)/2 - 1/8))) ^ j * ENNReal.ofReal (8*zeta) := by
    intro j
    have hQ0 : Q ∈ descendantsAtDepth Q 0 := by simp
    have heq := exactCircDepthTerm_eq_ofReal_cubeBesovCircDepthSeminorm Q ((1:ℝ)/2) (2:ℝ) hp2 g hmem j
    rw [← htwo] at heq
    have h := exactCircDepthTerm_normalized_descendant_le (H := Q) (Q := Q) (a := 0) (j := j)
      (f := g) hf hQ0 (s := (1/2:ℝ)) (σ := (1/8:ℝ)) (p := (2:ℝ)) (P := (4*(d:ℝ):ℝ)) hp2pos h2ltP
    rw [show exactCircDepthTerm Q ((1:ℝ)/2) (2:ℝ) g (ExactCircIntegrable.descendant hf hQ0) j =
          ENNReal.ofReal (cubeBesovCircDepthSeminorm Q ((1:ℝ)/2) (2:ℝ≥0∞) g j) from heq,
        Nat.cast_zero, mul_zero, zero_div, ENNReal.rpow_zero, one_mul, hhalf] at h
    refine le_trans h ?_
    rw [hc8]
    simpa only [zero_add] using mul_le_mul_right (hstep1 j) _
  have hainv : ((3 : ℝ) ^ (-((Q.scale : ℝ) * (1 / 2))))⁻¹ =
      (3 : ℝ) ^ ((Q.scale : ℝ) * (1 / 2)) := by
    rw [Real.rpow_neg h3pos.le, inv_inv]
  have hexp : (1 / 2 : ℝ) - 1 / 8 = 3 / 8 := by norm_num
  have hW1 : cubeBesovScaleWeight (-1 / 2) Q =
      (3 : ℝ) ^ ((Q.scale : ℝ) * (1 / 2)) := by
    unfold cubeBesovScaleWeight cubeScaleFactor
    rw [← Real.rpow_intCast, ← Real.rpow_mul h3pos.le]
    congr 1
    ring
  have hreal : ∀ j : ℕ, cubeBesovCircDepthSeminorm Q (1 / 2) 2 g j ≤
      (8 * zeta * cubeBesovScaleWeight (-1 / 2) Q) *
        ((3 : ℝ) ^ (-(3 / 8 : ℝ))) ^ j := by
    intro j
    have hrho0 : 0 ≤ (3 : ℝ) ^ (-(1 / 2 - 1 / 8 : ℝ)) :=
      (Real.rpow_pos_of_pos h3pos _).le
    have h := hcomb j
    rw [hrho_eq, ← ENNReal.ofReal_pow hrho0,
      ← ENNReal.ofReal_mul hhalfpos.le,
      ← ENNReal.ofReal_mul (pow_nonneg hrho0 j)] at h
    have hbnd := (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (pow_nonneg hrho0 j) (mul_nonneg (by norm_num) hzeta))).mp h
    have hdiv := (le_div_iff₀' hhalfpos).mpr hbnd
    calc cubeBesovCircDepthSeminorm Q (1 / 2) 2 g j
        ≤ ((3 : ℝ) ^ (-(1 / 2 - 1 / 8 : ℝ))) ^ j * (8 * zeta) /
            ((3 : ℝ) ^ (-((Q.scale : ℝ) * (1 / 2)))) := hdiv
      _ = _ := by rw [div_eq_mul_inv, hainv, hexp, hW1]; ring
  have hrho0 : 0 ≤ (3 : ℝ) ^ (-(3 / 8 : ℝ)) :=
    (Real.rpow_pos_of_pos h3pos _).le
  have hrho1 : (3 : ℝ) ^ (-(3 / 8 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hgeo : Summable (fun j : ℕ => ((3 : ℝ) ^ (-(3 / 8 : ℝ))) ^ j) :=
    summable_geometric_of_lt_one hrho0 hrho1
  have hK0 : 0 ≤ 8 * zeta * cubeBesovScaleWeight (-1 / 2) Q :=
    mul_nonneg (mul_nonneg (by norm_num) hzeta)
      (cubeBesovScaleWeight_nonneg _ Q)
  have hsumbound : ∀ N : ℕ,
      ∑ j ∈ Finset.range (N + 1), ((3 : ℝ) ^ (-(3 / 8 : ℝ))) ^ j ≤
        (1 - (3 : ℝ) ^ (-(3 / 8 : ℝ)))⁻¹ := by
    intro N
    rw [← tsum_geometric_of_lt_one hrho0 hrho1]
    exact hgeo.sum_le_tsum (Finset.range (N + 1)) (fun j _ => pow_nonneg hrho0 j)
  refine cubeBesovCircNorm_le_of_forall_partialNorm_le Q (1 / 2) 2 1 g (by simp) ?_
  intro N
  have hpart : cubeBesovCircPartialNorm Q (1 / 2) 2 1 N g =
      ∑ j ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm Q (1 / 2) 2 g j := by
    simp [cubeBesovCircPartialNorm, cubeBesovCircPartialSeminorm]
  rw [hpart]
  calc (∑ j ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm Q (1 / 2) 2 g j)
      ≤ ∑ j ∈ Finset.range (N + 1),
          (8 * zeta * cubeBesovScaleWeight (-1 / 2) Q) *
            ((3 : ℝ) ^ (-(3 / 8 : ℝ))) ^ j := Finset.sum_le_sum (fun j _ => hreal j)
    _ = (8 * zeta * cubeBesovScaleWeight (-1 / 2) Q) *
          ∑ j ∈ Finset.range (N + 1), ((3 : ℝ) ^ (-(3 / 8 : ℝ))) ^ j :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (8 * zeta * cubeBesovScaleWeight (-1 / 2) Q) *
          (1 - (3 : ℝ) ^ (-(3 / 8 : ℝ)))⁻¹ :=
      mul_le_mul_of_nonneg_left (hsumbound N) hK0
    _ = _ := by ring

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
