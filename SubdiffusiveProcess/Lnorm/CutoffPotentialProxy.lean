module

public import SubdiffusiveProcess.ResponseMoments.BandFiltration
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import Homogenization.Sobolev.H1.BasicLemmas
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import Mathlib
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction
public import SubdiffusiveProcess.Probability.ConditionalPullback
public import SubdiffusiveProcess.Sobolev.AffineData
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.Lnorm.BoundaryMomentAlgebra
public import SubdiffusiveProcess.Lnorm.BoundaryResponseFamily
public import SubdiffusiveProcess.Lnorm.LayerRegroup

@[expose] public section

/-! This module establishes CutoffPotentialProxy for the cutoff-response compactness construction;
it does not identify subsequential limits or assert local-normalization convergence. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open Classical
open scoped ENNReal NNReal BigOperators ContDiff
noncomputable section

namespace SubdiffusiveProcess.Lnorm

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy subtype measurableSpace for the cutoff-response compactness construction. -/
instance proxy_subtype_measurableSpace (p : ℤ → Prop) :
    ∀ j : Subtype p, MeasurableSpace (SubdiffusiveProcess.Lnorm.regroup_Y d j.1) :=
  fun j => SubdiffusiveProcess.Lnorm.regroup_Y_measurableSpace d j.1

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy contFn for the cutoff-response compactness construction. -/
def proxy_contFn (Hterm : C(SpatialCoordinates d, ℝ))
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    C(closedCube z r hr, ℝ) :=
  (Hterm + ∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ))).restrict (closedCube z r hr) -
    ContinuousMap.const _ (Real.log (SubdiffusiveProcess.Lnorm.prop16_kap M N))

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy pot for the cutoff-response compactness construction. -/
def proxy_pot (Hterm : C(SpatialCoordinates d, ℝ))
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    _root_.SubdiffusiveProcess.ResponseMoments.Potential (centeredCube z r hr) :=
  compactPotentialLp (closedCube z r hr) (SubdiffusiveProcess.Lnorm.proxy_contFn Hterm M N omega z r hr)

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- proxy contFn apply for the cutoff-response compactness construction. -/
theorem proxy_contFn_apply {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (Hterm M N omega z r hr)
    (x : closedCube z r hr) :
    SubdiffusiveProcess.Lnorm.proxy_contFn Hterm M N omega z r hr x =
      Hterm (x : SpatialCoordinates d) +
        (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) (x : SpatialCoordinates d)) -
        Real.log (SubdiffusiveProcess.Lnorm.prop16_kap M N) := by
  have hsum : (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)))
      ((x : SpatialCoordinates d)) =
      ∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) (x : SpatialCoordinates d) := by
    have h := map_sum ContinuousMap.coeFnAddMonoidHom
      (fun j : ℕ => omega (-(j : ℤ))) (Finset.range (N + 1))
    simp only [ContinuousMap.coeFnAddMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
    have h' := congrFun h (x : SpatialCoordinates d)
    simpa only [Finset.sum_apply] using h'
  change Hterm (x : SpatialCoordinates d) +
      (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ))) ((x : SpatialCoordinates d)) -
      Real.log (SubdiffusiveProcess.Lnorm.prop16_kap M N) = _
  rw [hsum]

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- proxy cp lipschitz for the cutoff-response compactness construction. -/
theorem proxy_cp_lipschitz {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    LipschitzWith 1 (compactPotentialLp (Ω := centeredCube z r hr) (closedCube z r hr)) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have hsub : compactPotentialLp (Ω := centeredCube z r hr) (closedCube z r hr) (f - g) =
      compactPotentialLp (closedCube z r hr) f - compactPotentialLp (closedCube z r hr) g := by
    have hfg : f - g = f + (-1 : ℝ) • g := by rw [neg_one_smul, sub_eq_add_neg]
    rw [hfg, compactPotentialLp_add, compactPotentialLp_smul, neg_one_smul, ← sub_eq_add_neg]
  rw [← hsub]
  exact compactPotentialLp_norm_le _ _

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy pot eq coefficient for the cutoff-response compactness construction. -/
theorem proxy_pot_eq_coefficient
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    cutoffPositiveCoefficient M H omega N z hr =
      expPotentialCoefficient (SubdiffusiveProcess.Lnorm.proxy_pot (H omega) M N omega z r hr) := by
  unfold cutoffPositiveCoefficient normalizedContinuousPositiveCoefficient SubdiffusiveProcess.Lnorm.proxy_pot
  rw [compactPotentialToLp_apply]
  congr 2
  apply ContinuousMap.ext
  intro x
  rw [SubdiffusiveProcess.Lnorm.proxy_contFn_apply]
  show Real.log ((cutoffCoefficientCM M H omega N z hr) x) - Real.log 1 = _
  have hcm : (cutoffCoefficientCM M H omega N z hr) x =
      cutoffCoefficient M H omega N (x : SpatialCoordinates d) := rfl
  rw [hcm, Real.log_one, sub_zero]
  unfold cutoffCoefficient cutoffPotential SubdiffusiveProcess.Lnorm.prop16_kap
  have hA : (0 : ℝ) < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hcast : ∀ j : ℕ, omega (-(Int.ofNat j)) = omega (-(j : ℤ)) := fun j => by norm_num
  have hlog1 : ∀ c u : ℝ, 0 < c → Real.log (c⁻¹ * Real.exp u) = u - Real.log c := by
    intro c u hc
    rw [Real.log_mul (inv_ne_zero hc.ne') (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
    ring
  have hlog2 : ∀ c v : ℝ, 0 < c → Real.log (Real.exp v * c) = v + Real.log c := by
    intro c v hc
    rw [Real.log_mul (Real.exp_pos _).ne' hc.ne', Real.log_exp]
  simp only [hcast]
  rw [hlog1 _ _ hA, hlog2 _ _ hA]
  ring

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy fineCoord for the cutoff-response compactness construction. -/
def proxy_fineCoord (y : (j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j) (m : ℕ) :
    C(SpatialCoordinates d, ℝ) :=
  y (Int.ofNat (m + 1))

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- proxy fineCoord at regroup for the cutoff-response compactness construction. -/
theorem proxy_fineCoord_at_regroup {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (omega : BilateralField d) (m : ℕ) :
    SubdiffusiveProcess.Lnorm.proxy_fineCoord (SubdiffusiveProcess.Lnorm.regroup omega) m = omega (-((m : ℤ) + 1)) := by
  show SubdiffusiveProcess.Lnorm.regroup omega ((m : ℤ) + 1) = omega (-((m : ℤ) + 1))
  rw [SubdiffusiveProcess.Lnorm.regroup_apply_succ]
  congr 1

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy contFn' for the cutoff-response compactness construction. -/
def proxy_contFn' (Hterm : C(SpatialCoordinates d, ℝ))
    (N : ℕ) (y : (j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    C(closedCube z r hr, ℝ) :=
  (Hterm + (y 0).1 +
      ∑ m ∈ Finset.range N, SubdiffusiveProcess.Lnorm.proxy_fineCoord y m).restrict
      (closedCube z r hr) -
    ContinuousMap.const _ (Real.log (SubdiffusiveProcess.Lnorm.prop16_kap M N))

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- proxy contFn' apply for the cutoff-response compactness construction. -/
theorem proxy_contFn'_apply {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (Hterm N y z r hr M)
    (x : closedCube z r hr) :
    SubdiffusiveProcess.Lnorm.proxy_contFn' Hterm N y z r hr M x =
      Hterm (x : SpatialCoordinates d) + (y 0).1 (x : SpatialCoordinates d) +
        (∑ m ∈ Finset.range N, SubdiffusiveProcess.Lnorm.proxy_fineCoord y m (x : SpatialCoordinates d)) -
        Real.log (SubdiffusiveProcess.Lnorm.prop16_kap M N) := by
  have hsum : (Hterm + (y 0).1 + ∑ m ∈ Finset.range N, SubdiffusiveProcess.Lnorm.proxy_fineCoord y m)
      ((x : SpatialCoordinates d)) =
      Hterm (x : SpatialCoordinates d) + (y 0).1 (x : SpatialCoordinates d) +
        (∑ m ∈ Finset.range N, SubdiffusiveProcess.Lnorm.proxy_fineCoord y m (x : SpatialCoordinates d)) := by
    have h := map_sum ContinuousMap.coeFnAddMonoidHom
      (fun m : ℕ => SubdiffusiveProcess.Lnorm.proxy_fineCoord y m) (Finset.range N)
    simp only [ContinuousMap.coeFnAddMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
    have h' := congrFun h (x : SpatialCoordinates d)
    simp only [ContinuousMap.add_apply, Finset.sum_apply] at h' ⊢
    rw [h']
  change (Hterm + (y 0).1 + ∑ m ∈ Finset.range N, SubdiffusiveProcess.Lnorm.proxy_fineCoord y m)
      ((x : SpatialCoordinates d)) - Real.log (SubdiffusiveProcess.Lnorm.prop16_kap M N) = _
  rw [hsum]

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy contFn' at regroup for the cutoff-response compactness construction. -/
theorem proxy_contFn'_at_regroup (Hterm : C(SpatialCoordinates d, ℝ))
    (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    SubdiffusiveProcess.Lnorm.proxy_contFn' Hterm N (SubdiffusiveProcess.Lnorm.regroup omega) z r hr M =
      SubdiffusiveProcess.Lnorm.proxy_contFn Hterm M N omega z r hr := by
  apply ContinuousMap.ext
  intro x
  rw [SubdiffusiveProcess.Lnorm.proxy_contFn_apply, SubdiffusiveProcess.Lnorm.proxy_contFn'_apply]
  have h0 : (SubdiffusiveProcess.Lnorm.regroup omega 0).1 = omega 0 := by
    rw [SubdiffusiveProcess.Lnorm.regroup_apply_zero]
  have hreindex : (∑ m ∈ Finset.range N,
      SubdiffusiveProcess.Lnorm.proxy_fineCoord (SubdiffusiveProcess.Lnorm.regroup omega) m (x : SpatialCoordinates d)) =
      ∑ m ∈ Finset.range N, omega (-((m : ℤ) + 1)) (x : SpatialCoordinates d) :=
    Finset.sum_congr rfl (fun m _ => by rw [SubdiffusiveProcess.Lnorm.proxy_fineCoord_at_regroup])
  rw [h0, hreindex]
  have hsplit0 : (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) (x : SpatialCoordinates d)) =
      (∑ m ∈ Finset.range N, omega (-((m : ℤ) + 1)) (x : SpatialCoordinates d)) +
        omega (-(0 : ℤ)) (x : SpatialCoordinates d) := by
    rw [Finset.sum_range_succ']
    push_cast
    ring_nf
  rw [hsplit0]
  simp only [neg_zero]
  ring

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy bandSet zero mem for the cutoff-response compactness construction. -/
theorem proxy_bandSet_zero_mem (H : ℕ) : (0 : ℤ) ∈ bandSet H := by
  simp only [bandSet, Set.mem_Icc]; omega

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy bandCoord for the cutoff-response compactness construction. -/
def proxy_bandCoord (H : ℕ)
    (b : (j : bandSet H) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1) (m : ℕ) : C(SpatialCoordinates d, ℝ) :=
  if h : (Int.ofNat (m + 1) : ℤ) ∈ bandSet H then
    (b ⟨Int.ofNat (m + 1), h⟩ : C(SpatialCoordinates d, ℝ))
  else 0

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy tailCoord for the cutoff-response compactness construction. -/
def proxy_tailCoord (H : ℕ)
    (t : (j : {j : ℤ // j ∉ bandSet H}) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1) (m : ℕ) :
    C(SpatialCoordinates d, ℝ) :=
  if h : (Int.ofNat (m + 1) : ℤ) ∉ bandSet H then
    (t ⟨Int.ofNat (m + 1), h⟩ : C(SpatialCoordinates d, ℝ))
  else 0

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- proxy bandCoord apply for the cutoff-response compactness construction. -/
theorem proxy_bandCoord_apply {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (H : ℕ) (y : (j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j)
    (m : ℕ) (hm : m < H) :
    SubdiffusiveProcess.Lnorm.proxy_bandCoord H (fun j => y j.1) m = SubdiffusiveProcess.Lnorm.proxy_fineCoord y m := by
  have h : (Int.ofNat (m + 1) : ℤ) ∈ bandSet H := by
    simp only [bandSet, Set.mem_Icc, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
    omega
  erw [SubdiffusiveProcess.Lnorm.proxy_bandCoord, dite_eq_left h]
  rfl

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- proxy tailCoord apply for the cutoff-response compactness construction. -/
theorem proxy_tailCoord_apply {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (H : ℕ) (y : (j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j)
    (m : ℕ) (hm : H ≤ m) :
    SubdiffusiveProcess.Lnorm.proxy_tailCoord H (fun j => y j.1) m = SubdiffusiveProcess.Lnorm.proxy_fineCoord y m := by
  have h : (Int.ofNat (m + 1) : ℤ) ∉ bandSet H := by
    simp only [bandSet, Set.mem_Icc, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
    omega
  erw [SubdiffusiveProcess.Lnorm.proxy_tailCoord, dite_eq_left h]
  rfl

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- proxy bandCoord measurable for the cutoff-response compactness construction. -/
theorem proxy_bandCoord_measurable {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (H m : ℕ) :
    Measurable (fun b : (j : bandSet H) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1 =>
      SubdiffusiveProcess.Lnorm.proxy_bandCoord H b m) := by
  by_cases h : (Int.ofNat (m + 1) : ℤ) ∈ bandSet H
  · have heq : (fun b : (j : bandSet H) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1 =>
        SubdiffusiveProcess.Lnorm.proxy_bandCoord H b m) = (fun b => b ⟨Int.ofNat (m + 1), h⟩) := by
      funext b
      erw [SubdiffusiveProcess.Lnorm.proxy_bandCoord, dite_eq_left h]
    rw [heq]
    exact measurable_pi_apply _
  · have heq : (fun b : (j : bandSet H) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1 =>
        SubdiffusiveProcess.Lnorm.proxy_bandCoord H b m) = (fun _ => 0) := by
      funext b
      erw [SubdiffusiveProcess.Lnorm.proxy_bandCoord, dite_eq_right h]
    rw [heq]
    exact measurable_const

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- proxy tailCoord measurable for the cutoff-response compactness construction. -/
theorem proxy_tailCoord_measurable {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (H m : ℕ) :
    Measurable (fun t : (j : {j : ℤ // j ∉ bandSet H}) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1 =>
      SubdiffusiveProcess.Lnorm.proxy_tailCoord H t m) := by
  by_cases h : (Int.ofNat (m + 1) : ℤ) ∉ bandSet H
  · have heq : (fun t : (j : {j : ℤ // j ∉ bandSet H}) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1 =>
        SubdiffusiveProcess.Lnorm.proxy_tailCoord H t m) = (fun t => t ⟨Int.ofNat (m + 1), h⟩) := by
      funext t
      erw [SubdiffusiveProcess.Lnorm.proxy_tailCoord, dite_eq_left h]
    rw [heq]
    exact measurable_pi_apply _
  · have heq : (fun t : (j : {j : ℤ // j ∉ bandSet H}) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1 =>
        SubdiffusiveProcess.Lnorm.proxy_tailCoord H t m) = (fun _ => 0) := by
      funext t
      erw [SubdiffusiveProcess.Lnorm.proxy_tailCoord, dite_eq_right h]
    rw [heq]
    exact measurable_const

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy V for the cutoff-response compactness construction. -/
def proxy_V (H : ℕ) (b : (j : bandSet H) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) : C(closedCube z r hr, ℝ) :=
  (SubdiffusiveProcess.Lnorm.htilde d (b ⟨0, SubdiffusiveProcess.Lnorm.proxy_bandSet_zero_mem H⟩).2 +
    (b ⟨0, SubdiffusiveProcess.Lnorm.proxy_bandSet_zero_mem H⟩).1 +
    ∑ m ∈ Finset.range H, SubdiffusiveProcess.Lnorm.proxy_bandCoord H b m).restrict (closedCube z r hr)

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy V measurable for the cutoff-response compactness construction. -/
theorem proxy_V_measurable (H : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    [MeasurableSpace C(closedCube z r hr, ℝ)] [BorelSpace C(closedCube z r hr, ℝ)] :
    Measurable (fun b : (j : bandSet H) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1 =>
      SubdiffusiveProcess.Lnorm.proxy_V H b z r hr) := by
  unfold SubdiffusiveProcess.Lnorm.proxy_V
  refine (ContinuousMap.continuous_restrict _).measurable.comp ?_
  refine Measurable.add (Measurable.add ?_ ?_) ?_
  · exact (SubdiffusiveProcess.Lnorm.htilde_measurable d).comp
      (measurable_snd.comp
        (measurable_pi_apply (⟨0, SubdiffusiveProcess.Lnorm.proxy_bandSet_zero_mem H⟩ : bandSet H)))
  · exact measurable_fst.comp
      (measurable_pi_apply (⟨0, SubdiffusiveProcess.Lnorm.proxy_bandSet_zero_mem H⟩ : bandSet H))
  · exact Finset.measurable_sum _ fun m _ => SubdiffusiveProcess.Lnorm.proxy_bandCoord_measurable H m

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy tailSum for the cutoff-response compactness construction. -/
def proxy_tailSum (H N : ℕ)
    (t : (j : {j : ℤ // j ∉ bandSet H}) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1) :
    C(SpatialCoordinates d, ℝ) :=
  ∑ m ∈ Finset.Ico H N, SubdiffusiveProcess.Lnorm.proxy_tailCoord H t m

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy tailSum measurable for the cutoff-response compactness construction. -/
theorem proxy_tailSum_measurable (H N : ℕ) :
    Measurable (SubdiffusiveProcess.Lnorm.proxy_tailSum (d := d) H N) :=
  Finset.measurable_sum _ fun m _ => SubdiffusiveProcess.Lnorm.proxy_tailCoord_measurable H m

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy tail for the cutoff-response compactness construction. -/
def proxy_tail (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H N : ℕ)
    (t : (j : {j : ℤ // j ∉ bandSet H}) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    _root_.SubdiffusiveProcess.ResponseMoments.Potential (centeredCube z r hr) :=
  compactPotentialLp (closedCube z r hr)
    ((SubdiffusiveProcess.Lnorm.proxy_tailSum H N t).restrict (closedCube z r hr) -
      ContinuousMap.const _ (Real.log (SubdiffusiveProcess.Lnorm.prop16_kap M N)))

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy pot' for the cutoff-response compactness construction. -/
def proxy_pot' (N : ℕ) (y : (j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) :
    _root_.SubdiffusiveProcess.ResponseMoments.Potential (centeredCube z r hr) :=
  compactPotentialLp (closedCube z r hr)
    (SubdiffusiveProcess.Lnorm.proxy_contFn' (SubdiffusiveProcess.Lnorm.htilde d (y 0).2) N y z r hr M)

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy contFn' split for the cutoff-response compactness construction. -/
theorem proxy_contFn'_split (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H N : ℕ)
    (hHN : H ≤ N) (y : (j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    SubdiffusiveProcess.Lnorm.proxy_contFn' (SubdiffusiveProcess.Lnorm.htilde d (y 0).2) N y z r hr M =
      SubdiffusiveProcess.Lnorm.proxy_V H (fun j => y j.1) z r hr +
        ((SubdiffusiveProcess.Lnorm.proxy_tailSum H N (fun j => y j.1)).restrict (closedCube z r hr) -
          ContinuousMap.const _ (Real.log (SubdiffusiveProcess.Lnorm.prop16_kap M N))) := by
  have hbandsum : (∑ m ∈ Finset.range H, SubdiffusiveProcess.Lnorm.proxy_bandCoord H (fun j => y j.1) m) =
      (∑ m ∈ Finset.range H, SubdiffusiveProcess.Lnorm.proxy_fineCoord y m) :=
    Finset.sum_congr rfl
      (fun m hm => SubdiffusiveProcess.Lnorm.proxy_bandCoord_apply H y m (Finset.mem_range.mp hm))
  have htailsum : (∑ m ∈ Finset.Ico H N, SubdiffusiveProcess.Lnorm.proxy_tailCoord H (fun j => y j.1) m) =
      (∑ m ∈ Finset.Ico H N, SubdiffusiveProcess.Lnorm.proxy_fineCoord y m) :=
    Finset.sum_congr rfl
      (fun m hm => SubdiffusiveProcess.Lnorm.proxy_tailCoord_apply H y m (Finset.mem_Ico.mp hm).1)
  have hfullsplit : (∑ m ∈ Finset.range N, SubdiffusiveProcess.Lnorm.proxy_fineCoord y m) =
      (∑ m ∈ Finset.range H, SubdiffusiveProcess.Lnorm.proxy_fineCoord y m) +
        ∑ m ∈ Finset.Ico H N, SubdiffusiveProcess.Lnorm.proxy_fineCoord y m := by
    simp only [Finset.range_eq_Ico]
    rw [Finset.sum_Ico_consecutive _ (Nat.zero_le H) hHN]
  have hVzero : (fun j : bandSet H => y j.1) ⟨(0 : ℤ), SubdiffusiveProcess.Lnorm.proxy_bandSet_zero_mem H⟩ =
      y 0 := rfl
  have hV0 : (SubdiffusiveProcess.Lnorm.htilde d ((fun j : bandSet H => y j.1)
      ⟨0, SubdiffusiveProcess.Lnorm.proxy_bandSet_zero_mem H⟩).2 : C(SpatialCoordinates d, ℝ)) =
      SubdiffusiveProcess.Lnorm.htilde d (y 0).2 := by rw [hVzero]
  have hV1 : ((fun j : bandSet H => y j.1) ⟨0, SubdiffusiveProcess.Lnorm.proxy_bandSet_zero_mem H⟩).1 =
      (y 0).1 := by rw [hVzero]
  show (SubdiffusiveProcess.Lnorm.htilde d (y 0).2 + (y 0).1 +
      ∑ m ∈ Finset.range N, SubdiffusiveProcess.Lnorm.proxy_fineCoord y m).restrict (closedCube z r hr) -
      ContinuousMap.const _ (Real.log (SubdiffusiveProcess.Lnorm.prop16_kap M N)) = _
  unfold SubdiffusiveProcess.Lnorm.proxy_V SubdiffusiveProcess.Lnorm.proxy_tailSum
  rw [hV0, hV1, hbandsum, htailsum, hfullsplit]
  have hradd : ∀ f g : C(SpatialCoordinates d, ℝ),
      (f + g).restrict (closedCube z r hr) =
        f.restrict (closedCube z r hr) + g.restrict (closedCube z r hr) := by
    intro f g; ext x; rfl
  simp only [hradd]
  abel

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy pot' split for the cutoff-response compactness construction. -/
theorem proxy_pot'_split (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H N : ℕ)
    (hHN : H ≤ N) (y : (j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    SubdiffusiveProcess.Lnorm.proxy_pot' N y z r hr M =
      compactPotentialLp (closedCube z r hr) (SubdiffusiveProcess.Lnorm.proxy_V H (fun j => y j.1) z r hr) +
        SubdiffusiveProcess.Lnorm.proxy_tail M H N (fun j => y j.1) z r hr := by
  unfold SubdiffusiveProcess.Lnorm.proxy_pot' SubdiffusiveProcess.Lnorm.proxy_tail
  rw [SubdiffusiveProcess.Lnorm.proxy_contFn'_split M H N hHN y z r hr, compactPotentialLp_add]

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy Rf for the cutoff-response compactness construction. -/
def proxy_Rf
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (b : weakSobolevGraph (centeredCube z r hr))
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ)
    (y : (j : ℤ) → SubdiffusiveProcess.Lnorm.regroup_Y d j) : ℝ :=
  (SubdiffusiveProcess.Lnorm.lnaff_response (killedResponseSpace hP) b).eval (SubdiffusiveProcess.Lnorm.proxy_pot' N y z r hr M)

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- proxy response eval continuous for the cutoff-response compactness construction. -/
theorem proxy_response_eval_continuous {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    {Ω : Opens (SpatialCoordinates d)}
    (R : _root_.SubdiffusiveProcess.ResponseMoments.Response Ω) :
    Continuous R.eval := by
  have he := equicontinuous_of_exp_comparison
    (f := fun _ : Unit => R.eval) (C := 1) (by norm_num)
    (fun _ g => R.eval_nonneg g)
    (fun _ g h => by rw [one_mul, dist_eq_norm]; exact R.exp_comparison g h)
    (fun g => ⟨R.eval g, fun _ => le_rfl⟩)
  exact he.continuous ()

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy tailContFn for the cutoff-response compactness construction. -/
def proxy_tailContFn (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H N : ℕ)
    (t : (j : {j : ℤ // j ∉ bandSet H}) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) : C(closedCube z r hr, ℝ) :=
  (SubdiffusiveProcess.Lnorm.proxy_tailSum H N t).restrict (closedCube z r hr) -
    ContinuousMap.const _ (Real.log (SubdiffusiveProcess.Lnorm.prop16_kap M N))

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- proxy tailContFn measurable for the cutoff-response compactness construction. -/
theorem proxy_tailContFn_measurable (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (H N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    [MeasurableSpace C(closedCube z r hr, ℝ)] [BorelSpace C(closedCube z r hr, ℝ)] :
    Measurable (fun t : (j : {j : ℤ // j ∉ bandSet H}) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1 =>
      SubdiffusiveProcess.Lnorm.proxy_tailContFn M H N t z r hr) := by
  unfold SubdiffusiveProcess.Lnorm.proxy_tailContFn
  refine Measurable.sub ?_ measurable_const
  exact (ContinuousMap.continuous_restrict _).measurable.comp (SubdiffusiveProcess.Lnorm.proxy_tailSum_measurable H N)

end

section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

omit [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] in
/-- proxy tail eq compactPotentialLp for the cutoff-response compactness construction. -/
theorem proxy_tail_eq_compactPotentialLp {d : ℕ} [_ms : MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [_borel : BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H N : ℕ) (t : (j : {j : ℤ // j ∉ bandSet H}) → SubdiffusiveProcess.Lnorm.regroup_Y d j.1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    SubdiffusiveProcess.Lnorm.proxy_tail M H N t z r hr =
      compactPotentialLp (closedCube z r hr) (SubdiffusiveProcess.Lnorm.proxy_tailContFn M H N t z r hr) := rfl

end

end SubdiffusiveProcess.Lnorm
