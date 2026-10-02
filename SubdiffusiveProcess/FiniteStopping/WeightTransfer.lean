import SubdiffusiveProcess.FiniteStopping.SourcedStageAt
import SubdiffusiveProcess.Sobolev.DirichletComparison

/-! Weight transfer between the coefficient `A_N` and the infrared-free coefficient `A_N^0 = e^{-H} A_N`
(paper `\label{mfd:lem-finite-source-comparison}`, last paragraph: "By the variational definition of the Dirichlet
energy, the local comparison transfers to the coefficients `wA_N` and `wA_M` with an exponentially small additional
error. Their scalar ratio is still `r_{N,M}(k)`, because `w(z)` cancels").

* `cutoffCoefficient_zero_eq`: `A_N^0(x) = e^{-H(x)} A_N(x)` pointwise;
* `reference_zero_eq`: the reference scalar of `A^0` is that of `A` times `e^{-H(z)}`;
* `respOn_zero_bounds`: on a cell where `H` oscillates by at most `c` around the centre,
  `e^{-c} e^{-H(z)} resp(A) ≤ resp(A^0) ≤ e^{c} e^{-H(z)} resp(A)`. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

theorem cutoffCoefficient_zero_eq
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) :
    cutoffCoefficient M (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega N x =
      Real.exp (-(H omega x)) * cutoffCoefficient M H omega N x := by
  unfold cutoffCoefficient cutoffPotential
  have h0 : ((0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega) x = 0 := rfl
  rw [h0]
  have : Real.exp (0 + ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j)) x -
        ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
      Real.exp (-(H omega x)) * Real.exp (H omega x + ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j)) x -
        ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [this]
  ring

theorem cutoffCoefficient_pos'
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) : 0 < cutoffCoefficient M H omega N x := by
  unfold cutoffCoefficient
  exact mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)

theorem reference_zero_eq
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N k : ℕ) (z : SpatialCoordinates d) :
    reference model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega N k z =
      reference model H omega N k z * Real.exp (-(H omega z)) := by
  unfold reference
  have h0 : ((0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega) z = 0 := rfl
  rw [h0]
  have : Real.exp (0 + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z) =
      Real.exp (H omega z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z) * Real.exp (-(H omega z)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [this]
  ring

/-- Two-sided response comparison of the infrared-free and the characterized coefficient on a cell where the
infrared field oscillates by at most `c` around the centre `zU`. -/
theorem respOn_zero_bounds
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (zU : SpatialCoordinates d) {rU : ℝ} (hrU : 0 < rU) (c : ℝ)
    (hosc : ∀ x ∈ centeredCube zU rU hrU, |H omega x - H omega zU| ≤ c)
    (S : ResponseSpace (centeredCube zU rU hrU)) (g : weakSobolevGraph (centeredCube zU rU hrU)) :
    Real.exp (-c) * (Real.exp (-(H omega zU)) *
        dirichletResponse S (cutoffPositiveCoefficient model H omega N zU hrU) g) ≤
      dirichletResponse S (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
        omega N zU hrU) g ∧
    dirichletResponse S (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
        omega N zU hrU) g ≤
      Real.exp c * (Real.exp (-(H omega zU)) *
        dirichletResponse S (cutoffPositiveCoefficient model H omega N zU hrU) g) := by
  set wz : ℝ := Real.exp (-(H omega zU)) with hwz
  have hwzpos : 0 < wz := Real.exp_pos _
  set aH := cutoffPositiveCoefficient model H omega N zU hrU with haH
  set a0 := cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega N zU hrU
    with ha0
  have haHae : ((aH.val : SpatialCoordinates d → ℝ)) =ᵐ[volume.restrict
      (centeredCube zU rU hrU : Set (SpatialCoordinates d))] (fun x => cutoffCoefficient model H omega N x) :=
    cutoffCoefficient_ae model H omega N zU hrU
  have ha0ae : ((a0.val : SpatialCoordinates d → ℝ)) =ᵐ[volume.restrict
      (centeredCube zU rU hrU : Set (SpatialCoordinates d))]
      (fun x => cutoffCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega N x) :=
    cutoffCoefficient_ae model _ omega N zU hrU
  set a' := scalePositiveCoefficient wz hwzpos aH with ha'
  have ha'ae := scalePositiveCoefficient_coeFn wz hwzpos aH
  have hmem : ∀ᵐ x ∂volume.restrict (centeredCube zU rU hrU : Set (SpatialCoordinates d)),
      x ∈ (centeredCube zU rU hrU : Set (SpatialCoordinates d)) :=
    ae_restrict_mem (centeredCube zU rU hrU).isOpen.measurableSet
  have hcomp := dirichletResponse_exp_comparison S a' a0 g c
    (by
      filter_upwards [ha0ae, ha'ae, haHae, hmem] with x h0 h' hH hx
      rw [h0, h', hH, cutoffCoefficient_zero_eq model H omega N x]
      have hb := hosc x hx
      have hexp : Real.exp (-c) * wz ≤ Real.exp (-(H omega x)) := by
        rw [hwz, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have := (abs_le.mp hb).2
        linarith
      have hpos : 0 ≤ cutoffCoefficient model H omega N x := (cutoffCoefficient_pos' model H omega N x).le
      nlinarith [mul_le_mul_of_nonneg_right hexp hpos])
    (by
      filter_upwards [ha0ae, ha'ae, haHae, hmem] with x h0 h' hH hx
      rw [h0, h', hH, cutoffCoefficient_zero_eq model H omega N x]
      have hb := hosc x hx
      have hexp : Real.exp (-(H omega x)) ≤ Real.exp c * wz := by
        rw [hwz, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have := (abs_le.mp hb).1
        linarith
      have hpos : 0 ≤ cutoffCoefficient model H omega N x := (cutoffCoefficient_pos' model H omega N x).le
      nlinarith [mul_le_mul_of_nonneg_right hexp hpos])
  rw [ha', dirichletResponse_scale_coefficient] at hcomp
  exact hcomp

end SubdiffusiveProcess.FiniteStopping
