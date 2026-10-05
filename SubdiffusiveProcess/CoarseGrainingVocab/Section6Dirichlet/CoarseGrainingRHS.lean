module

public import SubdiffusiveProcess.Section2.GeneralCoarseGraining
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.EnergyConsequence

@[expose] public section

/-!
# The finite-two coarse-graining right-hand side

This file specializes the proved general coarse-graining theorem at `p = 2`
and exposes the four source-facing upper-bound slots: the two truncated
response errors, the weighted local energy, and the positive fractional datum.
It is the deterministic composition used by `e.Dirichlet.prebalance` after
the dilation and partition adapters supply those four bounds.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet

open Homogenization Homogenization.Book Homogenization.Book.Ch03
open Homogenization.Book.Ch03.ABK26
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The real manuscript spelling of the `p = 2` coarse-graining right-hand
side after its four analytic carriers have been bounded. -/
def dirichletCoarseGrainingRHS
    (C alpha s s2 E1 E2 S D : ℝ) (n : ℤ) : ℝ :=
  C * Real.rpow s (-(3 / 2 : ℝ)) * Real.sqrt alpha * E1 * S +
    C * Real.rpow s (-11 / 2) * (s2 - s)⁻¹ *
      Real.rpow 3 (s2 * (n : ℝ)) * (1 + E2 ^ (2 : ℕ)) * D

theorem dirichletCoarseGrainingRHS_nonneg
    {C alpha s s2 E1 E2 S D : ℝ} {n : ℤ}
    (hC : 0 ≤ C) (_halpha : 0 ≤ alpha) (hs : 0 < s) (hss2 : s < s2)
    (hE1 : 0 ≤ E1) (_hE2 : 0 ≤ E2) (hS : 0 ≤ S) (hD : 0 ≤ D) :
    0 ≤ dirichletCoarseGrainingRHS C alpha s s2 E1 E2 S D n := by
  unfold dirichletCoarseGrainingRHS
  have hgap : 0 ≤ (s2 - s)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hss2.le)
  have hspow1 : 0 ≤ Real.rpow s (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg hs.le _
  have hspow2 : 0 ≤ Real.rpow s (-11 / 2) := Real.rpow_nonneg hs.le _
  have h3pow : 0 ≤ Real.rpow 3 (s2 * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hfirst : 0 ≤ C * Real.rpow s (-(3 / 2 : ℝ)) *
      Real.sqrt alpha * E1 * S :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hC hspow1) (Real.sqrt_nonneg _)) hE1) hS
  have hsecond : 0 ≤ C * Real.rpow s (-11 / 2) * (s2 - s)⁻¹ *
      Real.rpow 3 (s2 * (n : ℝ)) * (1 + E2 ^ (2 : ℕ)) * D :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg hC hspow2) hgap) h3pow)
          (add_nonneg (by norm_num) (sq_nonneg E2))) hD
  exact add_nonneg hfirst hsecond

/-- The proved general coarse-graining estimate at `p = 2`, with each of its
four right-hand-side carriers replaced by an explicit finite real upper
bound. -/
theorem exists_generalCoarseGraining_two_le_dirichletRHS
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (m n : ℤ), ∀ hnm : n < m,
        ∀ (a : Ch02.TriadicCoeffFamily d),
          (∀ Q, Ch02.CoeffOn.IsSymmetric (a.coeffOn Q)) →
        ∀ (alpha s s1 s2 : ℝ), 0 < alpha →
          ∀ hs1pos : 0 < s1, ∀ hs1s : s1 < s,
          ∀ hss2 : s < s2, ∀ hs2one : s2 < 1,
          ∀ (hs : FractionalOrder), hs.1 = s →
          ∀ (hs2 : FractionalOrder), hs2.1 = s2 →
          ∀ g : CubeEuclideanWspField (originCube d m) hs2 FiniteLpExponent.two,
          ∀ u v : H1Function (openCubeSet (originCube d m)),
            IsForcedEquation (originCube d m)
                (a.coeffOn (originCube d m)) u g.toField →
            IsScalarForcedEquation (originCube d m) alpha v g.toField →
            HasH10Difference (originCube d m) u v →
          ∀ E1 E2 S D : ℝ, 0 ≤ E1 → 0 ≤ E2 → 0 ≤ S → 0 ≤ D →
            paperHomogenizationError (originCube d m) n s1
                .infinity (.finite 1) a alpha ≤ ENNReal.ofReal E1 →
            paperHomogenizationError (originCube d m) n (s1 / 2)
                .infinity (.finite 2) a alpha ≤ ENNReal.ofReal E2 →
            weightedLocalSymmetricEnergyLp (originCube d m) n
                (by simpa [originCube] using hnm.le)
                (a.coeffOn (originCube d m)) u
                ⟨s1, hs1pos, by linarith⟩ hs FiniteLpExponent.two ≤
              ENNReal.ofReal S →
            paperFractionalSeminorm (originCube d m) hs2
                FiniteLpExponent.two g.toField ≤ ENNReal.ofReal D →
            ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ)) * alpha) *
                  paperNegativeFractionalDual (originCube d m) hs
                    FiniteLpExponent.two
                    (centeredCubeGradientDifferenceL2Field m u v) +
                ENNReal.ofReal (Real.rpow 3 (-s * (m : ℝ))) *
                  paperNegativeFractionalDual (originCube d m) hs
                    FiniteLpExponent.two
                    (centeredCubeFluxDifferenceL2Field m
                      (a.coeffOn (originCube d m)) alpha u v) ≤
              ENNReal.ofReal
                (dirichletCoarseGrainingRHS C alpha s s2 E1 E2 S D n) := by
  obtain ⟨C, hC, hmain⟩ :=
    _root_.SubdiffusiveProcess.Section2.general_coarse_graining FiniteLpExponent.two
      (by norm_num) hd
  refine ⟨C, hC, ?_⟩
  intro m n hnm a ha alpha s s1 s2 halpha hs1pos hs1s hss2 hs2one
    hs hhs hs2 hhs2 g u v hu hv huv E1 E2 S D hE10 hE20 hS0 hD0
    hE1 hE2 hS hD
  have hbase := hmain m n hnm a ha alpha s s1 s2 halpha hs1pos hs1s
    hss2 hs2one hs hhs hs2 hhs2 g u v hu hv huv
  have hspos : 0 < s := lt_trans hs1pos hs1s
  have hspow1 : 0 ≤ Real.rpow s (-(3 / 2 : ℝ)) :=
    Real.rpow_nonneg hspos.le _
  have hspow2 : 0 ≤ Real.rpow s (-11 / 2) := Real.rpow_nonneg hspos.le _
  have h3pow : 0 ≤ Real.rpow 3 (s2 * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hfirst0 : 0 ≤ C * Real.rpow s (-(3 / 2 : ℝ)) *
      Real.sqrt alpha * E1 * S :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hC.le hspow1) (Real.sqrt_nonneg _)) hE10) hS0
  have hsecond0 : 0 ≤ C * Real.rpow s (-11 / 2) * (s2 - s)⁻¹ *
      Real.rpow 3 (s2 * (n : ℝ)) * (1 + E2 ^ (2 : ℕ)) * D := by
    have hgap : 0 ≤ (s2 - s)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hss2.le)
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg hC.le hspow2) hgap) h3pow)
          (add_nonneg (by norm_num) (sq_nonneg E2))) hD0
  refine hbase.trans ?_
  rw [dirichletCoarseGrainingRHS,
    ENNReal.ofReal_add hfirst0 hsecond0]
  apply add_le_add
  · have hcoefficient :
        C * Real.rpow s
            (-1 - (FiniteLpExponent.two.conjugate.exponent.toReal)⁻¹) *
            Real.sqrt alpha =
          C * Real.rpow s (-(3 / 2 : ℝ)) * Real.sqrt alpha := by
      norm_num
    let front := C * Real.rpow s (-(3 / 2 : ℝ)) * Real.sqrt alpha
    have hfront0 : 0 ≤ front := by
      dsimp only [front]
      exact mul_nonneg (mul_nonneg hC.le hspow1) (Real.sqrt_nonneg _)
    have hfirstOfReal :
        ENNReal.ofReal (front * E1 * S) =
          ENNReal.ofReal front * ENNReal.ofReal E1 * ENNReal.ofReal S := by
      rw [ENNReal.ofReal_mul (mul_nonneg hfront0 hE10),
        ENNReal.ofReal_mul hfront0]
    rw [hcoefficient, show C * Real.rpow s (-(3 / 2 : ℝ)) *
      Real.sqrt alpha = front by rfl, hfirstOfReal]
    exact mul_le_mul' (mul_le_mul' le_rfl hE1) hS
  · have hfront0 : 0 ≤ C * Real.rpow s (-11 / 2) *
        (s2 - s)⁻¹ * Real.rpow 3 (s2 * (n : ℝ)) := by
      have hgap : 0 ≤ (s2 - s)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hss2.le)
      exact mul_nonneg (mul_nonneg (mul_nonneg hC.le hspow2) hgap) h3pow
    have hsq :
        (1 + paperHomogenizationError (originCube d m) n (s1 / 2)
            .infinity (.finite 2) a alpha ^ 2) ≤
          ENNReal.ofReal (1 + E2 ^ (2 : ℕ)) := by
      calc
        1 + paperHomogenizationError (originCube d m) n (s1 / 2)
              .infinity (.finite 2) a alpha ^ 2 ≤
            1 + (ENNReal.ofReal E2) ^ 2 := add_le_add le_rfl (pow_le_pow_left' hE2 2)
        _ = ENNReal.ofReal (1 + E2 ^ (2 : ℕ)) := by
          rw [ENNReal.ofReal_add (by norm_num) (sq_nonneg E2),
            ENNReal.ofReal_one, ENNReal.ofReal_pow hE20]
    let front := C * Real.rpow s (-11 / 2) *
      (s2 - s)⁻¹ * Real.rpow 3 (s2 * (n : ℝ))
    have hsecondOfReal :
        ENNReal.ofReal (front * (1 + E2 ^ (2 : ℕ)) * D) =
          ENNReal.ofReal front * ENNReal.ofReal (1 + E2 ^ (2 : ℕ)) *
            ENNReal.ofReal D := by
      rw [ENNReal.ofReal_mul
          (mul_nonneg hfront0 (add_nonneg (by norm_num) (sq_nonneg E2))),
        ENNReal.ofReal_mul hfront0]
    rw [show C * Real.rpow s (-11 / 2) * (s2 - s)⁻¹ *
      Real.rpow 3 (s2 * (n : ℝ)) = front by rfl, hsecondOfReal]
    exact mul_le_mul' (mul_le_mul' le_rfl hsq) hD

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
