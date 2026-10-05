module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Paper.lem_even
public import SubdiffusiveProcess.Paper.lem_extremes
public import SubdiffusiveProcess.Paper.rem_resolved_meshes
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import SubdiffusiveProcess.Paper.lem_even_energy_transport
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.VariationalResponses.OddExtension
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.VariationalResponses.KilledTransport
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Order.Filter.Finite

@[expose] public section

open MeasureTheory Set TopologicalSpace Filter Topology
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Microscopic power absorption inequality and equality.

Given d : ℕ, p1 t : ℝ with 2 ≤ p1 and t < d - 2d/p1 (so q1 - t > 0),
c > 0, eps > 0, DN ≥ 0, MN ≥ 0, any Hnorm, and 0 < r ≤ ell := c*eps/(1+DN),
set q1 := d - 2d/p1.

Then:
(1) MN * Hnorm² * (1+DN)^d * ell^(2d/p1) * r^(q1-t) ≤ c^(d-t) * MN * Hnorm² * eps^(d-t) * (1+DN)^t
(2) MN * Hnorm² * (1+DN)^d * ell^(2d/p1) * ell^(q1-t) = c^(d-t) * MN * Hnorm² * eps^(d-t) * (1+DN)^t

The proof uses rpow laws: r^(q1-t) ≤ ell^(q1-t) since r ≤ ell and q1-t > 0,
then ell^(2d/p1) * ell^(q1-t) = ell^(d-t) = (c*eps/(1+DN))^(d-t) = c^(d-t)*eps^(d-t)/(1+DN)^(d-t),
and (1+DN)^d * (1+DN)^(-(d-t)) = (1+DN)^t.
-/
theorem aux_rem_resolved_microscopic_power_absorption
    (d : ℕ) (p1 t c eps DN MN Hnorm r : ℝ)
    (_hp1 : 2 ≤ p1) (ht : t < (d : ℝ) - 2 * (d : ℝ) / p1)
    (hc : 0 < c) (heps : 0 < eps) (hDN : 0 ≤ DN) (hMN : 0 ≤ MN)
    (hrpos : 0 < r) (hrlell : r ≤ c * eps / (1 + DN)) :
    let q1 : ℝ := (d : ℝ) - 2 * (d : ℝ) / p1
    let ell : ℝ := c * eps / (1 + DN)
    MN * Hnorm ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) * r ^ (q1 - t)
    ≤ c ^ ((d : ℝ) - t) * MN * Hnorm ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t ∧
    MN * Hnorm ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) * ell ^ (q1 - t)
    = c ^ ((d : ℝ) - t) * MN * Hnorm ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t := by
  intro q1 ell
  have h_one_plus_DN_pos : 0 < 1 + DN := by linarith
  have hell_pos : 0 < ell := by
    dsimp [ell]
    refine div_pos (mul_pos hc heps) h_one_plus_DN_pos
  have hq1_sub_t_pos : 0 < q1 - t := by
    dsimp [q1]
    linarith
  have hq1_sub_t_nonneg : 0 ≤ q1 - t := hq1_sub_t_pos.le
  have h_sum_exp : 2 * (d : ℝ) / p1 + (q1 - t) = (d : ℝ) - t := by
    dsimp [q1]
    ring
  -- r^(q1-t) ≤ ell^(q1-t) because 0 < r ≤ ell and q1-t > 0
  have hrpow_le_ellrpow : r ^ (q1 - t) ≤ ell ^ (q1 - t) :=
    Real.rpow_le_rpow (by linarith) hrlell hq1_sub_t_nonneg
  -- Nonnegativity of the common factor
  have h_common_nonneg : 0 ≤ MN * Hnorm ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg hMN ?_) ?_) ?_
    · nlinarith [sq_nonneg Hnorm]
    · exact Real.rpow_nonneg (by linarith) _
    · exact Real.rpow_nonneg hell_pos.le _
  -- Combine to get the inequality
  have h_ineq : MN * Hnorm ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) * r ^ (q1 - t)
      ≤ MN * Hnorm ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) * ell ^ (q1 - t) := by
    nlinarith
  -- ell^(2d/p1) * ell^(q1-t) = ell^(d-t)
  have h_ell_pow_add : ell ^ (2 * (d : ℝ) / p1) * ell ^ (q1 - t) = ell ^ ((d : ℝ) - t) := by
    calc
      ell ^ (2 * (d : ℝ) / p1) * ell ^ (q1 - t) = ell ^ ((2 * (d : ℝ) / p1) + (q1 - t)) := by
        rw [Real.rpow_add hell_pos (2 * (d : ℝ) / p1) (q1 - t)]
      _ = ell ^ ((d : ℝ) - t) := by rw [h_sum_exp]
  -- Key identity: ell^(d-t) = c^(d-t) * eps^(d-t) * (1+DN)^(-(d-t))
  have h_ell_pow_d_sub_t : ell ^ ((d : ℝ) - t) = c ^ ((d : ℝ) - t) * eps ^ ((d : ℝ) - t) * (1 + DN) ^ (-((d : ℝ) - t)) := by
    calc
      ell ^ ((d : ℝ) - t) = ((c * eps) / (1 + DN)) ^ ((d : ℝ) - t) := rfl
      _ = (c * eps) ^ ((d : ℝ) - t) / (1 + DN) ^ ((d : ℝ) - t) := by
        rw [Real.div_rpow (by positivity) (by linarith) ((d : ℝ) - t)]
      _ = (c ^ ((d : ℝ) - t) * eps ^ ((d : ℝ) - t)) / (1 + DN) ^ ((d : ℝ) - t) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
      _ = c ^ ((d : ℝ) - t) * eps ^ ((d : ℝ) - t) * ((1 + DN) ^ ((d : ℝ) - t))⁻¹ := by ring
      _ = c ^ ((d : ℝ) - t) * eps ^ ((d : ℝ) - t) * (1 + DN) ^ (-((d : ℝ) - t)) := by
        rw [Real.rpow_neg (by linarith)]
  -- The ell case equality
  have h_ell_eq : MN * Hnorm ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) * ell ^ (q1 - t)
      = c ^ ((d : ℝ) - t) * MN * Hnorm ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t := by
    calc
      MN * Hnorm ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) * ell ^ (q1 - t)
          = MN * Hnorm ^ 2 * (1 + DN) ^ (d : ℝ) * (ell ^ (2 * (d : ℝ) / p1) * ell ^ (q1 - t)) := by ring
      _ = MN * Hnorm ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ ((d : ℝ) - t) := by rw [h_ell_pow_add]
      _ = MN * Hnorm ^ 2 * ((1 + DN) ^ (d : ℝ) * ell ^ ((d : ℝ) - t)) := by ring
      _ = MN * Hnorm ^ 2 * ((1 + DN) ^ (d : ℝ) * (c ^ ((d : ℝ) - t) * eps ^ ((d : ℝ) - t) * (1 + DN) ^ (-((d : ℝ) - t)))) := by
        rw [h_ell_pow_d_sub_t]
      _ = MN * Hnorm ^ 2 * (c ^ ((d : ℝ) - t) * eps ^ ((d : ℝ) - t) * ((1 + DN) ^ (d : ℝ) * (1 + DN) ^ (-((d : ℝ) - t)))) := by ring
      _ = MN * Hnorm ^ 2 * (c ^ ((d : ℝ) - t) * eps ^ ((d : ℝ) - t) * (1 + DN) ^ ((d : ℝ) + (-((d : ℝ) - t)))) := by
        rw [Real.rpow_add h_one_plus_DN_pos (d : ℝ) (-((d : ℝ) - t))]
      _ = MN * Hnorm ^ 2 * (c ^ ((d : ℝ) - t) * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t) := by ring
      _ = c ^ ((d : ℝ) - t) * MN * Hnorm ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t := by ring
  -- Combine inequality and equality for the final result
  refine ⟨?_, h_ell_eq⟩
  calc
    MN * Hnorm ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) * r ^ (q1 - t)
        ≤ MN * Hnorm ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) * ell ^ (q1 - t) := h_ineq
    _ = c ^ ((d : ℝ) - t) * MN * Hnorm ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t := h_ell_eq

/-- Absorb the macroscopic parent-energy contribution on a microscopic radius.
The datum term is handled separately by `aux_rem_resolved_microscopic_power_absorption`. -/
theorem aux_rem_resolved_microscopic_macro_absorption
    (d : ℕ) (p1 t t1 c eps DN r Kmac : ℝ)
    (_hp1 : 2 ≤ p1)
    (htpos : 0 < t)
    (htq : t < (d : ℝ) - 2 * (d : ℝ) / p1)
    (hc : 0 < c) (heps : 0 < eps) (hDN : 0 ≤ DN)
    (hKmac : 0 ≤ Kmac) (hr : 0 < r)
    (hrle : r ≤ c * eps / (1 + DN)) :
    let q1 : ℝ := (d : ℝ) - 2 * (d : ℝ) / p1
    let ell : ℝ := c * eps / (1 + DN)
    (r / ell) ^ q1 * (Kmac * eps ^ t1) ≤
      c ^ (-t) * (1 + DN) ^ t * eps ^ (t1 - t) * Kmac * r ^ t := by
  intro q1 ell
  have h_one_plus_DN_pos : 0 < 1 + DN := by linarith
  have hell_pos : 0 < ell := by
    dsimp [ell]
    refine div_pos (mul_pos hc heps) h_one_plus_DN_pos
  have hq1_pos : 0 < q1 := by
    dsimp [q1]
    linarith
  have h_ratio_pos : 0 < r / ell := div_pos hr hell_pos
  have h_ratio_le_one : r / ell ≤ 1 :=
    (div_le_one hell_pos).mpr hrle
  have ht_nonneg : 0 ≤ t := by linarith
  have hq1_ge_t : t ≤ q1 := by linarith
  have h_pow_le : (r / ell) ^ q1 ≤ (r / ell) ^ t :=
    Real.rpow_le_rpow_of_exponent_ge h_ratio_pos h_ratio_le_one hq1_ge_t
  have h_pow_eq : (r / ell) ^ t = c ^ (-t) * (1 + DN) ^ t * r ^ t * eps ^ (-t) := by
    calc
      (r / ell) ^ t = r ^ t / ell ^ t := by
        rw [Real.div_rpow (by linarith) hell_pos.le]
      _ = r ^ t / ((c * eps / (1 + DN)) ^ t) := rfl
      _ = r ^ t / (c ^ t * eps ^ t / (1 + DN) ^ t) := by
        rw [Real.div_rpow (by positivity) (by linarith),
          Real.mul_rpow (by positivity) (by positivity)]
      _ = r ^ t * ((1 + DN) ^ t / (c ^ t * eps ^ t)) := by
        rw [div_eq_mul_inv, inv_div]
      _ = r ^ t * (1 + DN) ^ t * (c ^ t * eps ^ t)⁻¹ := by
        rw [div_eq_mul_inv, mul_assoc]
      _ = r ^ t * (1 + DN) ^ t * ((c ^ t)⁻¹ * (eps ^ t)⁻¹) := by rw [mul_inv]
      _ = r ^ t * (1 + DN) ^ t * (c ^ t)⁻¹ * (eps ^ t)⁻¹ := by simp [mul_assoc]
      _ = r ^ t * (1 + DN) ^ t * c ^ (-t) * (eps ^ t)⁻¹ := by
        rw [← Real.rpow_neg (by linarith : 0 ≤ c) t]
      _ = r ^ t * (1 + DN) ^ t * c ^ (-t) * eps ^ (-t) := by
        rw [← Real.rpow_neg (by linarith : 0 ≤ eps) t]
      _ = c ^ (-t) * (1 + DN) ^ t * r ^ t * eps ^ (-t) := by ring
  have h_nonneg : 0 ≤ Kmac * eps ^ t1 :=
    mul_nonneg hKmac (Real.rpow_nonneg heps.le t1)
  calc
    (r / ell) ^ q1 * (Kmac * eps ^ t1) ≤ (r / ell) ^ t * (Kmac * eps ^ t1) :=
      mul_le_mul_of_nonneg_right h_pow_le h_nonneg
    _ = (c ^ (-t) * (1 + DN) ^ t * r ^ t * eps ^ (-t)) * (Kmac * eps ^ t1) := by rw [h_pow_eq]
    _ = c ^ (-t) * (1 + DN) ^ t * eps ^ (-t) * r ^ t * Kmac * eps ^ t1 := by ring
    _ = c ^ (-t) * (1 + DN) ^ t * Kmac * r ^ t * (eps ^ (-t) * eps ^ t1) := by ring
    _ = c ^ (-t) * (1 + DN) ^ t * Kmac * r ^ t * eps ^ ((-t) + t1) := by
      rw [← Real.rpow_add heps (-t) t1]
    _ = c ^ (-t) * (1 + DN) ^ t * Kmac * r ^ t * eps ^ (t1 - t) := by ring
    _ = c ^ (-t) * (1 + DN) ^ t * eps ^ (t1 - t) * Kmac * r ^ t := by ring

private theorem aux_rem_resolved_microscopic_exp_decay_aux (aRate s : ℝ)
    (ha : aRate < s * Real.log 3) (N : ℕ) :
    Real.exp (aRate * (N : ℝ)) * ((3 : ℝ) ^ (-(N : ℝ))) ^ s ≤ 1 := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hs : aRate - s * Real.log 3 ≤ 0 := le_of_lt (sub_neg.mpr ha)
  have hbase : (0 : ℝ) < 3 := by norm_num
  rw [Real.rpow_def_of_pos hbase, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  rw [← Real.exp_add]
  have harg : aRate * (N : ℝ) + (-(N : ℝ) * Real.log 3) * s ≤ 0 := by
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hs hN]
  convert (Real.exp_le_one_iff.mpr harg) using 1 ; ring

/-- The exact three microscopic scale factors absorb the permitted exponential rate. -/
theorem aux_rem_resolved_microscopic_three_exp_decay
    (d : ℕ) (t t1 aRate : ℝ)
    (ha : aRate < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3)
    (N : ℕ) :
    Real.exp (aRate * (N : ℝ)) * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) ≤ 1 ∧
    Real.exp (aRate * (N : ℝ)) * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t) ≤ 1 ∧
    Real.exp (aRate * (N : ℝ)) * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) ≤ 1 := by
  have hlog : 0 ≤ Real.log 3 := (Real.log_nonneg_iff (by norm_num)).2 (by norm_num)
  have h1 : min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) ≤ t1 - t := min_le_left _ _
  have h2 : min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) ≤ (d : ℝ) + 2 - t :=
    (min_le_right _ _).trans (min_le_left _ _)
  have h3 : min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) ≤ (d : ℝ) - t :=
    (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨aux_rem_resolved_microscopic_exp_decay_aux aRate _
      (lt_of_lt_of_le ha (mul_le_mul_of_nonneg_right h1 hlog)) N,
    aux_rem_resolved_microscopic_exp_decay_aux aRate _
      (lt_of_lt_of_le ha (mul_le_mul_of_nonneg_right h2 hlog)) N,
    aux_rem_resolved_microscopic_exp_decay_aux aRate _
      (lt_of_lt_of_le ha (mul_le_mul_of_nonneg_right h3 hlog)) N⟩

/-- The exact exponential gap between an extremum growth rate and a triadic scale. -/
theorem aux_rem_resolved_microscopic_scale_exp_identity
    (a s : ℝ) (N : ℕ) :
    Real.exp (a * (N : ℝ)) * ((3 : ℝ) ^ (-(N : ℝ))) ^ s =
      Real.exp (-(s * Real.log 3 - a) * (N : ℝ)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [Real.rpow_def_of_pos h3]
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The polynomial cost left after the strict microscopic exponential gap is
uniformly bounded over all cutoffs, for any real exponent. -/
theorem aux_rem_resolved_microscopic_poly_exp_bounded
    (s b : ℝ) (hb : 0 < b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      (1 + (N : ℝ)) ^ s * Real.exp (-b * (N : ℝ)) ≤ B := by
  have hlim : Tendsto
      (fun N : ℕ => (((N + 1 : ℕ) : ℝ) ^ s) *
        Real.exp (-b * ((N + 1 : ℕ) : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  obtain ⟨B, hB⟩ := hlim.bddAbove_range
  refine ⟨max 0 (Real.exp b * B), le_max_left _ _, ?_⟩
  intro N
  have hident : (1 + (N : ℝ)) ^ s * Real.exp (-b * (N : ℝ)) =
      Real.exp b * ((((N + 1 : ℕ) : ℝ) ^ s) *
        Real.exp (-b * ((N + 1 : ℕ) : ℝ))) := by
    have hcast : (1 + (N : ℝ)) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    have hexp : -b * (N : ℝ) = b + (-b * ((N + 1 : ℕ) : ℝ)) := by
      push_cast
      ring
    rw [hexp, Real.exp_add]
    ring
  calc
    (1 + (N : ℝ)) ^ s * Real.exp (-b * (N : ℝ)) =
        Real.exp b * ((((N + 1 : ℕ) : ℝ) ^ s) *
          Real.exp (-b * ((N + 1 : ℕ) : ℝ))) := hident
    _ ≤ Real.exp b * B := mul_le_mul_of_nonneg_left
      (hB (Set.mem_range_self N)) (Real.exp_pos _).le
    _ ≤ max 0 (Real.exp b * B) := le_max_right _ _

theorem aux_rem_resolved_microscopic_unit_closure_eq_pi (d : ℕ) :
    closure (unitNeumannCube d : Set (SpatialCoordinates d)) =
      Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1) := by
  have hQ : (unitNeumannCube d : Set (SpatialCoordinates d)) =
      Set.pi Set.univ (fun _ : Fin d => Set.Ioo (0 : ℝ) 1) := by
    rw [unitNeumannCube, centeredCube_eq_pi (fun _ => (1 / 2 : ℝ)) one_pos]
    congr 1
    funext i
    norm_num
  rw [hQ, closure_pi_set]
  congr 1
  funext i
  rw [closure_Ioo]
  norm_num

theorem aux_rem_resolved_microscopic_folded_closure_bounds (d : ℕ) (I P : Finset (Fin d))
    {x : SpatialCoordinates d}
    (hx : x ∈ closure (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P :
      Set (SpatialCoordinates d))) (j : Fin d) :
    (if j ∈ I then (if j ∈ P then (0 : ℝ) else -1)
      else 0) ≤ x j ∧
    x j ≤ (if j ∈ I then (if j ∈ P then (2 : ℝ) else 1)
      else 1) := by
  let S : Set (SpatialCoordinates d) := Set.pi Set.univ (fun j =>
    Set.Icc (if j ∈ I then (if j ∈ P then (0 : ℝ) else -1) else 0)
      (if j ∈ I then (if j ∈ P then (2 : ℝ) else 1) else 1))
  have hsub : (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P :
      Set (SpatialCoordinates d)) ⊆ S := by
    intro y hy k hk
    change (if k ∈ I then (if k ∈ P then (0 : ℝ) else -1) else 0) ≤ y k ∧
      y k ≤ (if k ∈ I then (if k ∈ P then (2 : ℝ) else 1) else 1)
    have hyk := hy k (Set.mem_univ k)
    by_cases hI : k ∈ I <;> by_cases hP : k ∈ P <;>
      simp only [hI, hP, ite_true, ite_false, Set.mem_Ioo] at hyk ⊢ <;>
      constructor <;> norm_num at * <;> linarith
  have hclosed : IsClosed S := isClosed_set_pi (fun _ _ => isClosed_Icc)
  have hmem : x ∈ S := closure_minimal hsub hclosed hx
  exact hmem j (Set.mem_univ j)

theorem aux_rem_resolved_microscopic_folded_cube_target_map (d : ℕ) (I P : Finset (Fin d)) :
    let zface := foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P
    let U := foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P
    let T := coordinateFold zface I P
    let Q := unitNeumannCube d
    ∀ x ∈ closure (U : Set (SpatialCoordinates d)),
      T x ∈ closure (Q : Set (SpatialCoordinates d)) := by
  dsimp
  intro x hx
  rw [aux_rem_resolved_microscopic_unit_closure_eq_pi]
  intro j hj
  obtain ⟨hlo, hhi⟩ := aux_rem_resolved_microscopic_folded_closure_bounds d I P hx j
  by_cases hI : j ∈ I
  · by_cases hP : j ∈ P
    · simp only [coordinateFold, foldedCubeCenter, coordinateReflectionSign,
        hI, hP, ite_true, Set.mem_Icc] at *
      have habs : |x j - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      constructor <;> norm_num at *; all_goals linarith [abs_nonneg (x j - 1)]
    · simp only [coordinateFold, foldedCubeCenter, coordinateReflectionSign,
        hI, hP, ite_true, ite_false, Set.mem_Icc] at *
      have habs : |x j| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      constructor <;> norm_num at *; all_goals linarith [abs_nonneg (x j)]
  · simpa only [coordinateFold, hI, ite_false, Set.mem_Icc] using And.intro hlo hhi

/-- Pull the logarithmic modulus through the actual folded cube.  The first
premise is precisely the unfurled modulus bound on the unit root; neither
folded-domain membership nor nonexpansiveness is assumed. -/
theorem aux_rem_resolved_microscopic_folded_log_modulus
    (d : ℕ) (I P : Finset (Fin d))
    (A : SpatialCoordinates d → ℝ) (DN eps : ℝ)
    (hDN : 0 ≤ DN) (heps : 0 < eps)
    (hlog : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) :
    let zface := foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P
    let T := coordinateFold zface I P
    let U := foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P
    ∀ x ∈ closure (U : Set (SpatialCoordinates d)),
      ∀ y ∈ closure (U : Set (SpatialCoordinates d)),
        |Real.log (A (T x)) - Real.log (A (T y))| ≤ DN / eps * dist x y := by
  dsimp
  intro x hx y hy
  have hx' := aux_rem_resolved_microscopic_folded_cube_target_map d I P x hx
  have hy' := aux_rem_resolved_microscopic_folded_cube_target_map d I P y hy
  have h := hlog _ hx' _ hy'
  exact h.trans (mul_le_mul_of_nonneg_left
    (coordinateFold_nonexpansive _ I P x y) (div_nonneg hDN heps.le))

/-- Hölder at the doubled exponent, followed by probability-space exponent monotonicity. -/
theorem aux_rem_resolved_microscopic_product_lq_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p q : ℝ) (hp : 0 < p) (hq : 2 * p ≤ q)
    (f g : Ω → ℝ)
    (hf : MemLp f (ENNReal.ofReal q) P)
    (hg : MemLp g (ENNReal.ofReal q) P) :
    eLpNorm (fun ω => f ω * g ω) (ENNReal.ofReal p) P ≤
      eLpNorm f (ENNReal.ofReal q) P * eLpNorm g (ENNReal.ofReal q) P := by
  have h2p : 0 < 2 * p := by positivity
  have hholder : ENNReal.HolderTriple (ENNReal.ofReal (2 * p))
      (ENNReal.ofReal (2 * p)) (ENNReal.ofReal p) := by
    constructor
    change (ENNReal.ofReal (2 * p))⁻¹ + (ENNReal.ofReal (2 * p))⁻¹ =
      (ENNReal.ofReal p)⁻¹
    rw [← ENNReal.ofReal_inv_of_pos h2p, ← ENNReal.ofReal_inv_of_pos hp,
      ← ENNReal.ofReal_add]
    · congr 1
      field_simp
      ring
    · positivity
    · positivity
  let := hholder
  have hf2 := eLpNorm_le_eLpNorm_of_exponent_le (μ := P)
    (f := f) (ENNReal.ofReal_le_ofReal hq)
  have hg2 := eLpNorm_le_eLpNorm_of_exponent_le (μ := P)
    (f := g) (ENNReal.ofReal_le_ofReal hq)
  have hprod := eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal (2 * p))
    (q := ENNReal.ofReal (2 * p)) (r := ENNReal.ofReal p) hf.aestronglyMeasurable hg.aestronglyMeasurable
  change eLpNorm (fun ω => f ω * g ω) (ENNReal.ofReal p) P ≤ _
  calc
    _ ≤ eLpNorm f (ENNReal.ofReal (2 * p)) P *
        eLpNorm g (ENNReal.ofReal (2 * p)) P := by
          exact hprod
    _ ≤ eLpNorm f (ENNReal.ofReal q) P * eLpNorm g (ENNReal.ofReal q) P :=
      mul_le_mul' hf2 hg2

/-- Hölder for the frozen microscopic moment exponent, uniformly in the level. -/
theorem aux_rem_resolved_microscopic_product_fixed_q
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p t : ℝ) (hp : 1 ≤ p)
    (f g : ℕ → Ω → ℝ)
    (hf : ∀ N, MemLp (f N) (ENNReal.ofReal (2 * p * max 1 t)) P)
    (hg : ∀ N, MemLp (g N) (ENNReal.ofReal (2 * p * max 1 t)) P)
    (N : ℕ) :
    eLpNorm (fun ω => f N ω * g N ω) (ENNReal.ofReal p) P ≤
      eLpNorm (f N) (ENNReal.ofReal (2 * p * max 1 t)) P *
      eLpNorm (g N) (ENNReal.ofReal (2 * p * max 1 t)) P := by
  have hmax : 1 ≤ max 1 t := le_max_left _ _
  have hq : 2 * p ≤ 2 * p * max 1 t := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * p by positivity) (sub_nonneg.mpr hmax)]
  exact aux_rem_resolved_microscopic_product_lq_bound P p _ (by linarith) hq
    (f N) (g N) (hf N) (hg N)

/-- A nonnegative geometric cutoff factor pulls exactly out of a real `eLpNorm`. -/
theorem aux_rem_resolved_microscopic_nonneg_scalar_eLpNorm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p s : ℝ) (hs : 0 ≤ s) (f : Ω → ℝ) :
    eLpNorm (fun ω => s * f ω) (ENNReal.ofReal p) P =
      ENNReal.ofReal s * eLpNorm f (ENNReal.ofReal p) P := by
  have h := eLpNorm_const_smul s f (ENNReal.ofReal p) P
  rw [Real.enorm_eq_ofReal hs] at h
  exact h

/-- The frozen moment order gives the nonlinear disorder factor in `L^{2p}`. -/
theorem aux_rem_resolved_microscopic_one_add_power_memLp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p t : ℝ) (hp : 1 ≤ p) (ht : 0 ≤ t)
    (D : Ω → ℝ) (hD : ∀ ω, 0 ≤ D ω)
    (hLp : MemLp D (ENNReal.ofReal (2 * p * max 1 t)) P) :
    MemLp (fun ω => (1 + D ω) ^ t) (ENNReal.ofReal (2 * p)) P := by
  let q : ℝ := 2 * p * max 1 t
  have hp0 : 0 < p := by linarith
  have h2p : 0 < 2 * p := by positivity
  have hqpos : 0 < q := by
    dsimp [q]
    have hmax : 1 ≤ max 1 t := le_max_left _ _
    positivity
  have hsum : MemLp (fun ω => (1 : ℝ) + D ω) (ENNReal.ofReal q) P := by
    have hconst : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal q) P := memLp_const 1
    exact hconst.add hLp
  by_cases ht0 : t = 0
  · subst t
    simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ))
      (ENNReal.ofReal (2 * p)) P)
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hmax : t ≤ max 1 t := le_max_right _ _
    have hle : 2 * p * t ≤ q := by
      dsimp [q]
      exact mul_le_mul_of_nonneg_left hmax h2p.le
    have hpowbase : MemLp (fun ω => (1 : ℝ) + D ω)
        (ENNReal.ofReal (2 * p * t)) P :=
      hsum.mono_exponent (ENNReal.ofReal_le_ofReal hle)
    have hpow : MemLp (fun ω => ‖(1 : ℝ) + D ω‖ ^ t)
        (ENNReal.ofReal (2 * p)) P := by
      have h := hpowbase.norm_rpow_div (ENNReal.ofReal t)
      convert h using 1
      · funext ω
        simp only [ENNReal.toReal_ofReal ht, Real.norm_eq_abs]
      · rw [ENNReal.ofReal_mul h2p.le]
        have ht_ne : ENNReal.ofReal t ≠ 0 := by
          simp [ENNReal.ofReal_eq_zero, not_le.mpr htpos]
        exact (ENNReal.mul_div_cancel_right ht_ne ENNReal.ofReal_ne_top).symm
    convert hpow using 1
    funext ω
    rw [Real.norm_eq_abs, abs_of_pos (by linarith [hD ω])]

/-- The exact `L^{2p}` norm of the nonlinear disorder factor is bounded by
the frozen `L^q` norm bound of the disorder. -/
theorem aux_rem_resolved_microscopic_one_add_power_norm_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p t CD : ℝ) (hp : 1 ≤ p) (ht : 0 ≤ t) (hCD : 0 ≤ CD)
    (D : Ω → ℝ) (hD : ∀ ω, 0 ≤ D ω)
    (hLp : MemLp D (ENNReal.ofReal (2 * p * max 1 t)) P)
    (hDbound : eLpNorm D (ENNReal.ofReal (2 * p * max 1 t)) P ≤ ENNReal.ofReal CD) :
    eLpNorm (fun ω => (1 + D ω) ^ t) (ENNReal.ofReal (2 * p)) P ≤
      ENNReal.ofReal ((1 + CD) ^ t) := by
  have hp0 : 0 < p := by linarith
  have h2p : 0 < 2 * p := by positivity
  let q : ℝ := 2 * p * max 1 t
  have hqpos : 0 < q := by
    dsimp [q]
    have hmax : 1 ≤ max 1 t := le_max_left _ _
    positivity
  have hqone : 1 ≤ q := by
    dsimp [q]
    have hmax : 1 ≤ max 1 t := le_max_left _ _
    nlinarith [mul_nonneg (show 0 ≤ 2 * p by positivity) (sub_nonneg.mpr hmax)]
  have hsum_meas : AEStronglyMeasurable (fun ω => (1 : ℝ) + D ω) P :=
    aestronglyMeasurable_const.add hLp.aestronglyMeasurable
  have hconst_norm : eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal q) P = 1 := by
    rw [eLpNorm_const _ (by simp [ENNReal.ofReal_eq_zero, not_le.mpr hqpos]) (NeZero.ne P)]
    simp
  have hsum_bound : eLpNorm (fun ω => (1 : ℝ) + D ω) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal (1 + CD) := by
    calc
      _ ≤ eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal q) P +
          eLpNorm D (ENNReal.ofReal q) P := by
            exact eLpNorm_add_le (by simpa using ENNReal.ofReal_le_ofReal hqone)
      _ ≤ 1 + ENNReal.ofReal CD := by rw [hconst_norm]; gcongr
      _ = ENNReal.ofReal (1 + CD) := by rw [ENNReal.ofReal_add (by norm_num) hCD]; norm_num
  by_cases ht0 : t = 0
  · subst t
    simpa [Real.rpow_zero, measure_univ] using
      (le_of_eq (eLpNorm_const (μ := P) (p := ENNReal.ofReal (2 * p)) (1 : ℝ)
        (by simp only [ne_eq, ENNReal.ofReal_eq_zero]; exact not_le.mpr h2p) (NeZero.ne P)))
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hle : 2 * p * t ≤ q := by
      dsimp [q]
      exact mul_le_mul_of_nonneg_left (le_max_right 1 t) h2p.le
    have hbase_bound : eLpNorm (fun ω => (1 : ℝ) + D ω)
        (ENNReal.ofReal (2 * p * t)) P ≤ ENNReal.ofReal (1 + CD) :=
      (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hle)).trans hsum_bound
    have hnorm_pow : eLpNorm (fun ω => (1 + D ω) ^ t)
        (ENNReal.ofReal (2 * p)) P =
        (eLpNorm (fun ω => (1 : ℝ) + D ω) (ENNReal.ofReal (2 * p * t)) P) ^ t := by
      have h := eLpNorm_norm_rpow (p := ENNReal.ofReal (2 * p))
        (μ := P) (fun ω => (1 : ℝ) + D ω) hsum_meas htpos
      convert h using 1
      · congr 1
        funext ω
        rw [Real.norm_eq_abs, abs_of_pos (by linarith [hD ω])]
      · rw [ENNReal.ofReal_mul h2p.le]
    rw [hnorm_pow]
    calc
      _ ≤ (ENNReal.ofReal (1 + CD)) ^ t := ENNReal.rpow_le_rpow hbase_bound ht
      _ = ENNReal.ofReal ((1 + CD) ^ t) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) ht]

theorem aux_rem_resolved_microscopic_K_product_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p t CD CK : ℝ) (hp : 1 ≤ p) (ht : 0 ≤ t)
    (hCD : 0 ≤ CD) (hCK : 0 ≤ CK)
    (D K : Ω → ℝ) (hD : ∀ w, 0 ≤ D w)
    (hDLp : MemLp D (ENNReal.ofReal (2 * p * max 1 t)) P)
    (hKLp : MemLp K (ENNReal.ofReal (2 * p * max 1 t)) P)
    (hDnorm : eLpNorm D (ENNReal.ofReal (2 * p * max 1 t)) P ≤ ENNReal.ofReal CD)
    (hKnorm : eLpNorm K (ENNReal.ofReal (2 * p * max 1 t)) P ≤ ENNReal.ofReal CK) :
    eLpNorm (fun w => (1 + D w) ^ t * K w) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (CK * (1 + CD) ^ t) := by
  have hp0 : 0 < p := by linarith
  have hmax : 1 ≤ max 1 t := le_max_left _ _
  have hq : 2 * p ≤ 2 * p * max 1 t := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * p by positivity) (sub_nonneg.mpr hmax)]
  have hpowerLp := aux_rem_resolved_microscopic_one_add_power_memLp
    P p t hp ht D hD hDLp
  have hpowerBound := aux_rem_resolved_microscopic_one_add_power_norm_bound
    P p t CD hp ht hCD D hD hDLp hDnorm
  have hK2 : MemLp K (ENNReal.ofReal (2 * p)) P :=
    hKLp.mono_exponent (ENNReal.ofReal_le_ofReal hq)
  have hKbound : eLpNorm K (ENNReal.ofReal (2 * p)) P ≤ ENNReal.ofReal CK :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hq)).trans hKnorm
  have hprod := aux_rem_resolved_microscopic_product_lq_bound P p (2 * p)
    hp0 (le_refl _) (fun w => (1 + D w) ^ t) K hpowerLp hK2
  calc
    _ ≤ eLpNorm (fun w => (1 + D w) ^ t) (ENNReal.ofReal (2 * p)) P *
        eLpNorm K (ENNReal.ofReal (2 * p)) P := hprod
    _ ≤ ENNReal.ofReal ((1 + CD) ^ t) * ENNReal.ofReal CK :=
      mul_le_mul' hpowerBound hKbound
    _ = ENNReal.ofReal (CK * (1 + CD) ^ t) := by
      rw [mul_comm (ENNReal.ofReal ((1 + CD) ^ t)) (ENNReal.ofReal CK),
        ENNReal.ofReal_mul hCK]


theorem aux_rem_resolved_microscopic_M_product_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p t CD CE : ℝ) (hp : 1 ≤ p) (ht : 0 ≤ t)
    (hCD : 0 ≤ CD) (hCE : 0 ≤ CE)
    (D M mInv : Ω → ℝ)
    (hD : ∀ w, 0 ≤ D w) (hM : ∀ w, 0 ≤ M w) (hm : ∀ w, 0 ≤ mInv w)
    (hDLp : MemLp D (ENNReal.ofReal (2 * p * max 1 t)) P)
    (hMLp : MemLp M (ENNReal.ofReal (2 * p * max 1 t)) P)
    (hDnorm : eLpNorm D (ENNReal.ofReal (2 * p * max 1 t)) P ≤ ENNReal.ofReal CD)
    (hMnorm : eLpNorm (fun w => M w + mInv w)
      (ENNReal.ofReal (2 * p * max 1 t)) P ≤ ENNReal.ofReal CE) :
    eLpNorm (fun w => M w * (1 + D w) ^ t) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (CE * (1 + CD) ^ t) := by
  have hp0 : 0 < p := by linarith
  have hmax : 1 ≤ max 1 t := le_max_left _ _
  have hq : 2 * p ≤ 2 * p * max 1 t := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * p by positivity) (sub_nonneg.mpr hmax)]
  have hpowerLp := aux_rem_resolved_microscopic_one_add_power_memLp
    P p t hp ht D hD hDLp
  have hpowerBound := aux_rem_resolved_microscopic_one_add_power_norm_bound
    P p t CD hp ht hCD D hD hDLp hDnorm
  have hM2 : MemLp M (ENNReal.ofReal (2 * p)) P :=
    hMLp.mono_exponent (ENNReal.ofReal_le_ofReal hq)
  have hMmono : eLpNorm M (ENNReal.ofReal (2 * p)) P ≤
      eLpNorm (fun w => M w + mInv w) (ENNReal.ofReal (2 * p * max 1 t)) P := by
    calc
      _ ≤ eLpNorm M (ENNReal.ofReal (2 * p * max 1 t)) P :=
        eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hq)
      _ ≤ eLpNorm (fun w => M w + mInv w)
          (ENNReal.ofReal (2 * p * max 1 t)) P := by
        apply eLpNorm_mono_enorm hMLp.aestronglyMeasurable
        intro w
        rw [Real.enorm_eq_ofReal (hM w), Real.enorm_eq_ofReal (add_nonneg (hM w) (hm w))]
        exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (hm w))
  have hMbound := hMmono.trans hMnorm
  have hprod := aux_rem_resolved_microscopic_product_lq_bound P p (2 * p)
    hp0 (le_refl _) M (fun w => (1 + D w) ^ t) hM2 hpowerLp
  calc
    _ ≤ eLpNorm M (ENNReal.ofReal (2 * p)) P *
        eLpNorm (fun w => (1 + D w) ^ t) (ENNReal.ofReal (2 * p)) P := hprod
    _ ≤ ENNReal.ofReal CE * ENNReal.ofReal ((1 + CD) ^ t) :=
      mul_le_mul' hMbound hpowerBound
    _ = ENNReal.ofReal (CE * (1 + CD) ^ t) := by rw [ENNReal.ofReal_mul hCE]

theorem aux_rem_resolved_microscopic_mInv_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p t CE : ℝ) (hp : 1 ≤ p)
    (M mInv : Ω → ℝ) (hM : ∀ w, 0 ≤ M w) (hm : ∀ w, 0 ≤ mInv w)
    (hmLp : MemLp mInv (ENNReal.ofReal (2 * p * max 1 t)) P)
    (hSum : eLpNorm (fun w => M w + mInv w)
      (ENNReal.ofReal (2 * p * max 1 t)) P ≤ ENNReal.ofReal CE) :
    eLpNorm mInv (ENNReal.ofReal p) P ≤ ENNReal.ofReal CE := by
  have hq : p ≤ 2 * p * max 1 t := by
    have hmax := le_max_left (1 : ℝ) t
    nlinarith [mul_nonneg (show 0 ≤ 2 * p by positivity) (sub_nonneg.mpr hmax)]
  calc
    _ ≤ eLpNorm mInv (ENNReal.ofReal (2 * p * max 1 t)) P :=
      eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hq)
    _ ≤ eLpNorm (fun w => M w + mInv w)
        (ENNReal.ofReal (2 * p * max 1 t)) P := by
      apply eLpNorm_mono_enorm hmLp.aestronglyMeasurable
      intro w
      rw [Real.enorm_eq_ofReal (hm w), Real.enorm_eq_ofReal (add_nonneg (hM w) (hm w))]
      exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (hM w))
    _ ≤ _ := hSum


private theorem microscopic_sqrt_power_bound
    (C t : ℝ) (hC : 0 ≤ C) (ht : 0 ≤ t) (N : ℕ) :
    (1 + C * Real.sqrt (1 + (N : ℝ))) ^ t ≤
      (1 + C) ^ t * (1 + (N : ℝ)) ^ (t / 2) := by
  have hsqrt : 1 ≤ Real.sqrt (1 + (N : ℝ)) := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 1 + (N : ℝ)),
      Real.sqrt_nonneg (1 + (N : ℝ))]
  have harg : 0 ≤ 1 + C * Real.sqrt (1 + (N : ℝ)) := by positivity
  have hcmp : 1 + C * Real.sqrt (1 + (N : ℝ)) ≤
      (1 + C) * Real.sqrt (1 + (N : ℝ)) := by nlinarith
  calc
    _ ≤ ((1 + C) * Real.sqrt (1 + (N : ℝ))) ^ t :=
      Real.rpow_le_rpow harg hcmp ht
    _ = (1 + C) ^ t * (Real.sqrt (1 + (N : ℝ))) ^ t := by
      rw [Real.mul_rpow (by linarith) (Real.sqrt_nonneg _)]
    _ = (1 + C) ^ t * (1 + (N : ℝ)) ^ (t / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith : 0 ≤ 1 + (N : ℝ))]
      ring

private theorem microscopic_rate_bound
    (A C t a s : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (ha : a < s * Real.log 3) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      A * (1 + C * Real.sqrt (1 + (N : ℝ))) ^ t *
        Real.exp (a * (N : ℝ)) * ((3 : ℝ) ^ (-(N : ℝ))) ^ s ≤ B := by
  obtain ⟨Brate, hBrate, hrate⟩ :=
    aux_rem_resolved_microscopic_poly_exp_bounded (t / 2)
      (s * Real.log 3 - a) (sub_pos.mpr ha)
  refine ⟨A * (1 + C) ^ t * Brate, by positivity, ?_⟩
  intro N
  have hid := aux_rem_resolved_microscopic_scale_exp_identity a s N
  have hfac : 0 ≤ A * Real.exp (a * (N : ℝ)) *
      ((3 : ℝ) ^ (-(N : ℝ))) ^ s := by positivity
  have hstep := mul_le_mul_of_nonneg_left
    (microscopic_sqrt_power_bound C t hC ht N) hfac
  have hright := mul_le_mul_of_nonneg_left (hrate N)
    (mul_nonneg hA (Real.rpow_nonneg (by linarith : 0 ≤ 1 + C) t))
  calc
    A * (1 + C * Real.sqrt (1 + (N : ℝ))) ^ t *
        Real.exp (a * (N : ℝ)) * ((3 : ℝ) ^ (-(N : ℝ))) ^ s =
      (A * Real.exp (a * (N : ℝ)) * ((3 : ℝ) ^ (-(N : ℝ))) ^ s) *
        (1 + C * Real.sqrt (1 + (N : ℝ))) ^ t := by ring
    _ ≤ (A * Real.exp (a * (N : ℝ)) * ((3 : ℝ) ^ (-(N : ℝ))) ^ s) *
          ((1 + C) ^ t * (1 + (N : ℝ)) ^ (t / 2)) := hstep
    _ = (A * (1 + C) ^ t) *
          ((1 + (N : ℝ)) ^ (t / 2) * Real.exp (a * (N : ℝ)) *
            ((3 : ℝ) ^ (-(N : ℝ))) ^ s) := by ring
    _ = (A * (1 + C) ^ t) *
          ((1 + (N : ℝ)) ^ (t / 2) *
            Real.exp (-(s * Real.log 3 - a) * (N : ℝ))) := by
              simp only [mul_assoc, hid]
    _ ≤ A * (1 + C) ^ t * Brate := by simpa [mul_assoc] using hright


private theorem microscopic_scaled_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p z : ℝ) (f : Ω → ℝ) (F B : ℝ)
    (hz : 0 ≤ z) (hF : 0 ≤ F)
    (hf : eLpNorm f (ENNReal.ofReal p) P ≤ ENNReal.ofReal F)
    (hnum : F * z ≤ B) :
    eLpNorm (fun w => f w * z)
      (ENNReal.ofReal p) P ≤ ENNReal.ofReal B := by
  calc
    _ = ENNReal.ofReal z * eLpNorm f (ENNReal.ofReal p) P := by
      have hfun : (fun w => f w * z) = (fun w => z * f w) := by funext w; ring
      rw [hfun]
      exact aux_rem_resolved_microscopic_nonneg_scalar_eLpNorm P p _ hz f
    _ ≤ ENNReal.ofReal z * ENNReal.ofReal F :=
      mul_le_mul_right hf _
    _ = ENNReal.ofReal (F * z) := by
      rw [ENNReal.ofReal_mul hF]
      ac_rfl
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hnum

theorem aux_rem_resolved_microscopic_statistical_conjunct
    (d : ℕ) (hd : 2 ≤ d) (t t1 : ℝ) (ht : (d : ℝ) - 1 < t) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ p : ℝ, 1 ≤ p →
      let q := 2 * p * max 1 t
      ∀ D M mInv Kmac : ℕ → Ω → ℝ,
      ∀ CD CE CK aRate : ℝ, 0 ≤ CD → 0 ≤ CE → 0 ≤ CK → 0 ≤ aRate →
      aRate < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 →
      (∀ N w, 0 ≤ D N w ∧ 0 ≤ M N w ∧ 0 ≤ mInv N w ∧ 0 ≤ Kmac N w) →
      (∀ N, MemLp (D N) (ENNReal.ofReal q) P ∧ MemLp (M N) (ENNReal.ofReal q) P ∧
        MemLp (mInv N) (ENNReal.ofReal q) P ∧ MemLp (Kmac N) (ENNReal.ofReal q) P) →
      (∀ N, eLpNorm (D N) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (CD * Real.sqrt (1 + (N : ℝ)))) →
      (∀ N, eLpNorm (fun w => M N w + mInv N w) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (CE * Real.exp (aRate * (N : ℝ)))) →
      (∀ N, eLpNorm (Kmac N) (ENNReal.ofReal q) P ≤ ENNReal.ofReal CK) →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
        eLpNorm (fun w => (1 + D N w) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N w)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal B ∧
        eLpNorm (fun w => mInv N w * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal B ∧
        eLpNorm (fun w => M N w * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) * (1 + D N w) ^ t)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal B := by
  intro Ω instMeas P instProb p hp
  dsimp
  intro D M mInv Kmac CD CE CK aRate hCD hCE hCK ha0 ha hnonneg hLp hDnorm hSumnorm hKnorm
  have ht0 : 0 ≤ t := by
    have hdreal : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hlog : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
  have hrate1 : 0 < (t1 - t) * Real.log 3 := by
    have hle : min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 ≤
        (t1 - t) * Real.log 3 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hlog
    exact lt_of_le_of_lt ha0 (lt_of_lt_of_le ha hle)
  have hrate2 : aRate < ((d : ℝ) + 2 - t) * Real.log 3 := by
    have hle : min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 ≤
        ((d : ℝ) + 2 - t) * Real.log 3 :=
      mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hlog
    exact lt_of_lt_of_le ha hle
  have hrate3 : aRate < ((d : ℝ) - t) * Real.log 3 := by
    have hle : min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 ≤
        ((d : ℝ) - t) * Real.log 3 :=
      mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hlog
    exact lt_of_lt_of_le ha hle
  obtain ⟨B1, hB1, hrateB1⟩ :=
    microscopic_rate_bound CK CD t 0 (t1 - t) hCK hCD ht0 hrate1
  obtain ⟨B2, hB2, hrateB2⟩ :=
    microscopic_rate_bound CE 0 0 aRate ((d : ℝ) + 2 - t) hCE (le_refl _) (le_refl _) hrate2
  obtain ⟨B3, hB3, hrateB3⟩ :=
    microscopic_rate_bound CE CD t aRate ((d : ℝ) - t) hCE hCD ht0 hrate3
  refine ⟨max B1 (max B2 B3), le_trans hB1 (le_max_left _ _), ?_⟩
  intro N
  have hDN := (hLp N).1
  have hMN := (hLp N).2.1
  have hmN := (hLp N).2.2.1
  have hKN := (hLp N).2.2.2
  have hKprod := aux_rem_resolved_microscopic_K_product_bound P p t
    (CD * Real.sqrt (1 + (N : ℝ))) CK hp ht0
    (mul_nonneg hCD (Real.sqrt_nonneg _)) hCK
    (D N) (Kmac N) (fun w => (hnonneg N w).1)
    hDN hKN (hDnorm N) (hKnorm N)
  have hMprod := aux_rem_resolved_microscopic_M_product_bound P p t
    (CD * Real.sqrt (1 + (N : ℝ)))
    (CE * Real.exp (aRate * (N : ℝ))) hp ht0
    (mul_nonneg hCD (Real.sqrt_nonneg _)) (mul_nonneg hCE (Real.exp_pos _).le)
    (D N) (M N) (mInv N)
    (fun w => (hnonneg N w).1) (fun w => (hnonneg N w).2.1)
    (fun w => (hnonneg N w).2.2.1)
    hDN hMN (hDnorm N) (hSumnorm N)
  have hmBound := aux_rem_resolved_microscopic_mInv_bound P p t
    (CE * Real.exp (aRate * (N : ℝ))) hp
    (M N) (mInv N) (fun w => (hnonneg N w).2.1)
    (fun w => (hnonneg N w).2.2.1) hmN (hSumnorm N)
  have hKnum : CK * (1 + CD * Real.sqrt (1 + (N : ℝ))) ^ t *
      ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) ≤ B1 := by
    simpa using hrateB1 N
  have hmNum : CE * Real.exp (aRate * (N : ℝ)) *
      ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t) ≤ B2 := by
    simpa using hrateB2 N
  have hMnum : (CE * Real.exp (aRate * (N : ℝ))) *
      (1 + CD * Real.sqrt (1 + (N : ℝ))) ^ t *
      ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) ≤ B3 := by
    convert hrateB3 N using 1 ; ring
  constructor
  · have hscale := microscopic_scaled_bound P p
        (((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t))
        (fun w => (1 + D N w) ^ t * Kmac N w)
        (CK * (1 + CD * Real.sqrt (1 + (N : ℝ))) ^ t) B1
        (by positivity) (by positivity) hKprod hKnum
    have hle : ENNReal.ofReal B1 ≤ ENNReal.ofReal (max B1 (max B2 B3)) :=
      ENNReal.ofReal_le_ofReal (le_max_left _ _)
    have := hscale.trans hle
    simpa only [mul_assoc, mul_left_comm, mul_comm] using this
  constructor
  · have hscale := microscopic_scaled_bound P p
        (((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
        (mInv N) (CE * Real.exp (aRate * (N : ℝ))) B2
        (by positivity) (by positivity) hmBound hmNum
    exact hscale.trans (ENNReal.ofReal_le_ofReal
      (le_trans (le_max_left _ _) (le_max_right _ _)))
  · have hscale := microscopic_scaled_bound P p
        (((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t))
        (fun w => M N w * (1 + D N w) ^ t)
        ((CE * Real.exp (aRate * (N : ℝ))) *
          (1 + CD * Real.sqrt (1 + (N : ℝ))) ^ t) B3
        (by positivity) (by positivity) hMprod hMnum
    have hle : ENNReal.ofReal B3 ≤ ENNReal.ofReal (max B1 (max B2 B3)) :=
      ENNReal.ofReal_le_ofReal (le_trans (le_max_right _ _) (le_max_right _ _))
    have := hscale.trans hle
    simpa only [mul_assoc, mul_left_comm, mul_comm] using this

section NeumannHelpers
open Metric



/-- Coordinates in which `x` lies within `ell` of a face of the unit cube. -/
def aux_rem_resolved_microscopic_neumann_faces {d : ℕ} (x : SpatialCoordinates d) (ell : ℝ) :
    Finset (Fin d) :=
  Finset.univ.filter fun j => x j < ell ∨ 1 - ell < x j

/-- Coordinates in which the nearer face is the upper face. -/
def aux_rem_resolved_microscopic_neumann_upper {d : ℕ} (x : SpatialCoordinates d) :
    Finset (Fin d) :=
  Finset.univ.filter fun j => 1 / 2 < x j

theorem aux_rem_resolved_microscopic_neumann_mem_unit {d : ℕ} {x : SpatialCoordinates d} :
    x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) ↔ ∀ j, 0 < x j ∧ x j < 1 := by
  rw [unitNeumannCube, centeredCube_eq_pi (fun _ => (1 / 2 : ℝ)) one_pos]
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
  constructor
  · intro h j
    have := h j
    constructor <;> linarith [this.1, this.2]
  · intro h j
    have := h j
    constructor <;> linarith [this.1, this.2]

theorem aux_rem_resolved_microscopic_neumann_mem_folded {d : ℕ} (I P : Finset (Fin d))
    {y : SpatialCoordinates d} :
    y ∈ (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)) ↔
      ∀ j, (if j ∈ I then (if j ∈ P then (0 < y j ∧ y j < 2) else (-1 < y j ∧ y j < 1))
        else (0 < y j ∧ y j < 1)) := by
  change y ∈ Set.pi Set.univ _ ↔ _
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  refine forall_congr' fun j => ?_
  by_cases hI : j ∈ I <;> by_cases hP : j ∈ P <;>
    simp only [hI, hP, ite_true, ite_false, Set.mem_Ioo] <;>
    constructor <;> intro h <;> constructor <;> norm_num at h ⊢ <;> linarith [h.1, h.2]

theorem aux_rem_resolved_microscopic_neumann_center {d : ℕ} (I P : Finset (Fin d)) (j : Fin d) :
    foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P j =
      if j ∈ I then (if j ∈ P then (1 : ℝ) else 0) else 1 / 2 := by
  simp only [foldedCubeCenter]
  split_ifs <;> norm_num

/-- Classification of the coordinates of a unit-cube centre at scale `ell ≤ 1/4`. -/
theorem aux_rem_resolved_microscopic_neumann_classify {d : ℕ} {x : SpatialCoordinates d}
    (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) {ell : ℝ}
    (hell : ell ≤ 1 / 4) (j : Fin d) :
    let I := aux_rem_resolved_microscopic_neumann_faces x ell
    let P := aux_rem_resolved_microscopic_neumann_upper x
    (j ∈ I ∧ j ∈ P ∧ 1 - ell < x j ∧ x j < 1) ∨
      (j ∈ I ∧ j ∉ P ∧ 0 < x j ∧ x j < ell) ∨
      (j ∉ I ∧ ell ≤ x j ∧ x j ≤ 1 - ell) := by
  intro I P
  have hxj := (aux_rem_resolved_microscopic_neumann_mem_unit.1 hx) j
  simp only [I, P, aux_rem_resolved_microscopic_neumann_faces,
    aux_rem_resolved_microscopic_neumann_upper, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h1 : x j < ell
  · right; left
    exact ⟨Or.inl h1, by linarith, hxj.1, h1⟩
  · by_cases h2 : 1 - ell < x j
    · left
      exact ⟨Or.inr h2, by linarith, h2, hxj.2⟩
    · right; right
      push Not at h1 h2
      exact ⟨by push Not; exact ⟨h1, h2⟩, h1, h2⟩

/-- Every active coordinate of the centre is within `ell` of its reflection plane. -/
theorem aux_rem_resolved_microscopic_neumann_near_plane {d : ℕ} {x : SpatialCoordinates d}
    (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) {ell : ℝ}
    (hell : ell ≤ 1 / 4) (j : Fin d)
    (hj : j ∈ aux_rem_resolved_microscopic_neumann_faces x ell) :
    |x j - foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1
      (aux_rem_resolved_microscopic_neumann_faces x ell)
      (aux_rem_resolved_microscopic_neumann_upper x) j| < ell := by
  rw [aux_rem_resolved_microscopic_neumann_center]
  rcases aux_rem_resolved_microscopic_neumann_classify hx hell j with
    ⟨hI, hP, h1, h2⟩ | ⟨hI, hP, h1, h2⟩ | ⟨hI, _⟩
  · simp only [hI, hP, ite_true]
    rw [abs_lt]; constructor <;> linarith
  · simp only [hI, hP, ite_true, ite_false]
    rw [abs_lt]; constructor <;> linarith
  · exact absurd hj hI

/-- The half-size cube `{|y - x|_∞ < ell}` lies in the actual folded cube. -/
theorem aux_rem_resolved_microscopic_neumann_ball_sub_folded {d : ℕ} {x : SpatialCoordinates d}
    (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) {ell : ℝ}
    (hell : ell ≤ 1 / 4) {y : SpatialCoordinates d} (hy : ∀ j, |y j - x j| < ell) :
    y ∈ (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos
      (aux_rem_resolved_microscopic_neumann_faces x ell)
      (aux_rem_resolved_microscopic_neumann_upper x) : Set (SpatialCoordinates d)) := by
  rw [aux_rem_resolved_microscopic_neumann_mem_folded]
  intro j
  have hyj := abs_lt.1 (hy j)
  rcases aux_rem_resolved_microscopic_neumann_classify hx hell j with
    ⟨hI, hP, h1, h2⟩ | ⟨hI, hP, h1, h2⟩ | ⟨hI, h1, h2⟩
  · simp only [hI, hP, ite_true]; constructor <;> linarith [hyj.1, hyj.2]
  · simp only [hI, hP, ite_true, ite_false]; constructor <;> linarith [hyj.1, hyj.2]
  · simp only [hI, ite_false]; constructor <;> linarith [hyj.1, hyj.2]

/-- The reflection-symmetric box around the centre used for the energy multiplicity. -/
def aux_rem_resolved_microscopic_neumann_box {d : ℕ} (x : SpatialCoordinates d) (ell : ℝ) :
    Set (SpatialCoordinates d) :=
  {y | ∀ j, if j ∈ aux_rem_resolved_microscopic_neumann_faces x ell then
      |y j - foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1
        (aux_rem_resolved_microscopic_neumann_faces x ell)
        (aux_rem_resolved_microscopic_neumann_upper x) j| < 2 * ell
    else |y j - x j| < ell}

theorem aux_rem_resolved_microscopic_neumann_box_measurable {d : ℕ} (x : SpatialCoordinates d)
    (ell : ℝ) : MeasurableSet (aux_rem_resolved_microscopic_neumann_box x ell) := by
  have : aux_rem_resolved_microscopic_neumann_box x ell = ⋂ j : Fin d,
      {y : SpatialCoordinates d | if j ∈ aux_rem_resolved_microscopic_neumann_faces x ell then
        |y j - foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1
          (aux_rem_resolved_microscopic_neumann_faces x ell)
          (aux_rem_resolved_microscopic_neumann_upper x) j| < 2 * ell
      else |y j - x j| < ell} := by
    ext y; simp [aux_rem_resolved_microscopic_neumann_box]
  rw [this]
  refine MeasurableSet.iInter fun j => ?_
  split_ifs
  · exact measurableSet_lt (by fun_prop) measurable_const
  · exact measurableSet_lt (by fun_prop) measurable_const

theorem aux_rem_resolved_microscopic_neumann_ball_sub_box {d : ℕ} {x : SpatialCoordinates d}
    (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) {ell : ℝ}
    (hell : ell ≤ 1 / 4) {y : SpatialCoordinates d} (hy : ∀ j, |y j - x j| < ell) :
    y ∈ aux_rem_resolved_microscopic_neumann_box x ell := by
  intro j
  split_ifs with hj
  · have h1 := aux_rem_resolved_microscopic_neumann_near_plane hx hell j hj
    have h2 := hy j
    calc _ = |(y j - x j) + (x j - foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1
          (aux_rem_resolved_microscopic_neumann_faces x ell)
          (aux_rem_resolved_microscopic_neumann_upper x) j)| := by ring_nf
      _ ≤ |y j - x j| + |x j - foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1
          (aux_rem_resolved_microscopic_neumann_faces x ell)
          (aux_rem_resolved_microscopic_neumann_upper x) j| := abs_add_le _ _
      _ < 2 * ell := by linarith
  · exact hy j

theorem aux_rem_resolved_microscopic_neumann_box_sub_folded {d : ℕ} {x : SpatialCoordinates d}
    (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) {ell : ℝ}
    (hell : ell ≤ 1 / 4) :
    aux_rem_resolved_microscopic_neumann_box x ell ⊆
      (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos
        (aux_rem_resolved_microscopic_neumann_faces x ell)
        (aux_rem_resolved_microscopic_neumann_upper x) : Set (SpatialCoordinates d)) := by
  intro y hy
  rw [aux_rem_resolved_microscopic_neumann_mem_folded]
  intro j
  have hyj := hy j
  rcases aux_rem_resolved_microscopic_neumann_classify hx hell j with
    ⟨hI, hP, h1, h2⟩ | ⟨hI, hP, h1, h2⟩ | ⟨hI, h1, h2⟩
  · simp only [hI, hP, ite_true, aux_rem_resolved_microscopic_neumann_center] at hyj ⊢
    have := abs_lt.1 hyj; constructor <;> linarith [this.1, this.2]
  · simp only [hI, hP, ite_true, ite_false, aux_rem_resolved_microscopic_neumann_center] at hyj ⊢
    have := abs_lt.1 hyj; constructor <;> linarith [this.1, this.2]
  · simp only [hI, ite_false] at hyj ⊢
    have := abs_lt.1 hyj; constructor <;> linarith [this.1, this.2]

theorem aux_rem_resolved_microscopic_neumann_box_sub_cube {d : ℕ} {x : SpatialCoordinates d}
    (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) {ell rho : ℝ}
    (hell : ell ≤ 1 / 4) (hrho : 6 * ell ≤ rho) :
    aux_rem_resolved_microscopic_neumann_box x ell ⊆
      {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < rho / 2} := by
  intro y hy i
  have hyi := hy i
  split_ifs at hyi with hj
  · have h1 := aux_rem_resolved_microscopic_neumann_near_plane hx hell i hj
    calc _ = |(y i - foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1
          (aux_rem_resolved_microscopic_neumann_faces x ell)
          (aux_rem_resolved_microscopic_neumann_upper x) i) -
          (x i - foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1
          (aux_rem_resolved_microscopic_neumann_faces x ell)
          (aux_rem_resolved_microscopic_neumann_upper x) i)| := by ring_nf
      _ ≤ _ := abs_sub _ _
      _ < 2 * ell + ell := add_lt_add hyi h1
      _ ≤ rho / 2 := by linarith
  · have hell0 : 0 ≤ ell := le_trans (abs_nonneg _) hyi.le
    linarith

theorem aux_rem_resolved_microscopic_neumann_box_symm {d : ℕ} (x : SpatialCoordinates d)
    (ell : ℝ) (J : Finset (Fin d))
    (hJ : J ⊆ aux_rem_resolved_microscopic_neumann_faces x ell) :
    coordinateReflection (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1
        (aux_rem_resolved_microscopic_neumann_faces x ell)
        (aux_rem_resolved_microscopic_neumann_upper x)) J ⁻¹'
      aux_rem_resolved_microscopic_neumann_box x ell =
      aux_rem_resolved_microscopic_neumann_box x ell := by
  ext y
  simp only [Set.mem_preimage, aux_rem_resolved_microscopic_neumann_box, mem_ofPred_eq]
  refine forall_congr' fun j => ?_
  by_cases hjI : j ∈ aux_rem_resolved_microscopic_neumann_faces x ell
  · simp only [hjI, ite_true, coordinateReflection]
    by_cases hjJ : j ∈ J
    · simp only [hjJ, ite_true]
      rw [show ∀ a b : ℝ, 2 * b - a - b = -(a - b) from fun a b => by ring, abs_neg]
    · simp only [hjJ, ite_false]
  · have hjJ : j ∉ J := fun h => hjI (hJ h)
    simp only [hjI, ite_false, coordinateReflection, hjJ]

/-- On the unit cube the fold is the identity, for any active faces and signs. -/
theorem aux_rem_resolved_microscopic_neumann_fold_id {d : ℕ} (I P : Finset (Fin d))
    {y : SpatialCoordinates d} (hy : y ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) :
    coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y = y := by
  have hyj := aux_rem_resolved_microscopic_neumann_mem_unit.1 hy
  funext j
  simp only [coordinateFold]
  split_ifs with hI
  · rw [aux_rem_resolved_microscopic_neumann_center]
    simp only [hI, ite_true, coordinateReflectionSign]
    by_cases hP : j ∈ P
    · simp only [hP, ite_true]
      rw [abs_of_neg (by linarith [(hyj j).2])]; ring
    · simp only [hP, ite_false]
      rw [abs_of_pos (by linarith [(hyj j).1])]; ring
  · rfl

/-- On the unit cube the signed gradient factor of the fold is one. -/
theorem aux_rem_resolved_microscopic_neumann_fold_sign {d : ℕ} (I P : Finset (Fin d))
    {y : SpatialCoordinates d} (hy : y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (j : Fin d) :
    (if j ∈ I then
        coordinateReflectionSign P j *
          (if y j < foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P j then -1 else 1)
      else 1) = (1 : ℝ) := by
  have hyj := (aux_rem_resolved_microscopic_neumann_mem_unit.1 hy) j
  rw [aux_rem_resolved_microscopic_neumann_center]
  by_cases hI : j ∈ I
  · simp only [hI, ite_true, coordinateReflectionSign]
    by_cases hP : j ∈ P
    · simp only [hP, ite_true]
      rw [ite_eq_left hyj.2]; norm_num
    · simp only [hP, ite_false]
      rw [ite_eq_right (by linarith [hyj.1])]; norm_num
  · simp only [hI, ite_false]

/-- Almost-every pullback through the actual fold: an a.e. property of the root cube
holds a.e. on the folded cube at the folded point, which lies in the open root cube. -/
theorem aux_rem_resolved_microscopic_neumann_fold_ae (d : ℕ) (w : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (I P : Finset (Fin d)) {p : SpatialCoordinates d → Prop}
    (h : ∀ᵐ y ∂volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d)), p y) :
    ∀ᵐ y ∂volume.restrict (foldedCube w r hr I P : Set (SpatialCoordinates d)),
      p (coordinateFold (foldedCubeCenter w r I P) I P y) ∧
        coordinateFold (foldedCubeCenter w r I P) I P y ∈
          (centeredCube w r hr : Set (SpatialCoordinates d)) := by
  set z := foldedCubeCenter w r I P
  have h0 : ∀ᵐ y ∂volume, y ∈ (centeredCube w r hr : Set (SpatialCoordinates d)) → p y :=
    (ae_restrict_iff' (centeredCube w r hr).isOpen.measurableSet).1 h
  have hJ : ∀ J : Finset (Fin d), ∀ᵐ y ∂volume,
      coordinateReflection z J y ∈ (centeredCube w r hr : Set (SpatialCoordinates d)) →
        p (coordinateReflection z J y) := fun J =>
    (coordinateReflection_measurePreserving z J).quasiMeasurePreserving.ae h0
  have hplanes : ∀ j : Fin d, ∀ᵐ y ∂(volume : Measure (SpatialCoordinates d)), y j ≠ z j := by
    intro j
    have hnull : (volume : Measure (SpatialCoordinates d)) {y | y j = z j} = 0 := by
      rw [volume_pi]
      exact Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) j (z j)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    exact hy
  have hall := ae_all_iff.2 hJ
  have hallp := ae_all_iff.2 hplanes
  refine (ae_restrict_iff' (foldedCube w r hr I P).isOpen.measurableSet).2 ?_
  filter_upwards [hall, hallp] with y hy hyp hyU
  obtain ⟨J, hJI, hyJ⟩ := aux_lem_even_energy_transport_sector_cover_point d w r hr I P y hyU
    (fun j _ => hyp j)
  have hT := aux_lem_even_energy_transport_sector_fold d w r hr I P J hJI y hyJ
  rw [hT]
  exact ⟨hy J hyJ, hyJ⟩




/-- The squared `L²` seminorm of a square-integrable real function is its square integral. -/
theorem aux_rem_resolved_microscopic_neumann_eLpNorm_two_sq {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {h : X → ℝ} (hh : MemLp h 2 ν) :
    ((eLpNorm h 2 ν).toReal) ^ 2 = ∫ y, h y ^ 2 ∂ν := by
  rw [hh.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have hnn : 0 ≤ ∫ y, ‖h y‖ ^ (2 : ℝ≥0∞).toReal ∂ν :=
    integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) _
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _)]
  have h2 : (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2] at hnn ⊢
  rw [Real.rpow_inv_natCast_pow hnn (by norm_num)]
  congr 1
  funext y
  rw [Real.rpow_natCast, Real.norm_eq_abs, sq_abs]

/-- The Euclidean length of finitely many square-integrable coordinates is square integrable. -/
theorem aux_rem_resolved_microscopic_neumann_sqrt_sum_memLp {X : Type*} [MeasurableSpace X]
    {ν : Measure X} {ι : Type*} [Fintype ι] {g : ι → X → ℝ} (hg : ∀ i, MemLp (g i) 2 ν) :
    MemLp (fun y => Real.sqrt (∑ i, (g i y) ^ 2)) 2 ν := by
  have hsum : MemLp (fun y => ∑ i, |g i y|) 2 ν :=
    memLp_finsetSum' (s := Finset.univ) (f := fun i y => |g i y|) (fun i _ => (hg i).abs)
      |>.congr_norm (by
        exact (Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hg i).aestronglyMeasurable.norm)) (by
          filter_upwards with y
          simp [Finset.sum_apply])
  refine hsum.mono' ?_ ?_
  · exact Real.continuous_sqrt.comp_aestronglyMeasurable
      (Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hg i).aestronglyMeasurable.pow 2)
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hle : ∑ i, (g i y) ^ 2 ≤ (∑ i, |g i y|) ^ 2 := by
      have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |g i y|)
        (fun i _ => abs_nonneg _)
      simpa [sq_abs] using this
    calc Real.sqrt (∑ i, (g i y) ^ 2) ≤ Real.sqrt ((∑ i, |g i y|) ^ 2) := Real.sqrt_le_sqrt hle
      _ = ∑ i, |g i y| := Real.sqrt_sq (Finset.sum_nonneg fun i _ => abs_nonneg _)

/-- Hölder on a measurable subset of a ball: the square integral on the subset is bounded
by the `L^{p_1}` norm on the ball and the volume of the subset. -/
theorem aux_rem_resolved_microscopic_neumann_holder_sq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S Bl : Set X} (hSB : S ⊆ Bl) (hSfin : μ S ≠ ∞)
    {h : X → ℝ} (hmeas : AEStronglyMeasurable h (μ.restrict Bl)) {p1 : ℝ} (hp1 : 2 ≤ p1)
    (hfin : eLpNorm h (ENNReal.ofReal p1) (μ.restrict Bl) ≠ ∞) :
    ∫ y in S, h y ^ 2 ∂μ ≤
      (μ.real S) ^ (1 - 2 / p1) * ((eLpNorm h (ENNReal.ofReal p1) (μ.restrict Bl)).toReal) ^ 2 := by
  have hν : μ.restrict S ≤ μ.restrict Bl := Measure.restrict_mono hSB le_rfl
  have hmeasS : AEStronglyMeasurable h (μ.restrict S) := hmeas.mono_measure hν
  have h2p : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p1 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    exact ENNReal.ofReal_le_ofReal hp1
  have hH := eLpNorm_le_eLpNorm_mul_rpow_measure_univ h2p hmeasS
  have hmono := eLpNorm_mono_measure (p := ENNReal.ofReal p1) h hν
  have hp1pos : 0 < p1 := by linarith
  have hexp : 1 / (2 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p1).toReal = 1 / 2 - 1 / p1 := by
    rw [ENNReal.toReal_ofReal hp1pos.le]; norm_num
  rw [hexp, Measure.restrict_apply_univ] at hH
  have hexp0 : 0 ≤ 1 / 2 - 1 / p1 := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le (by norm_num) hp1
  have hS_rpow_fin : μ S ^ (1 / 2 - 1 / p1) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hexp0 hSfin
  have hbound : eLpNorm h 2 (μ.restrict S) ≤
      eLpNorm h (ENNReal.ofReal p1) (μ.restrict Bl) * μ S ^ (1 / 2 - 1 / p1) :=
    hH.trans (mul_le_mul_left hmono _)
  have hRfin : eLpNorm h (ENNReal.ofReal p1) (μ.restrict Bl) * μ S ^ (1 / 2 - 1 / p1) ≠ ∞ :=
    ENNReal.mul_ne_top hfin hS_rpow_fin
  have hmem2 : MemLp h 2 (μ.restrict S) := lt_of_le_of_lt hbound hRfin.lt_top
  have hreal := ENNReal.toReal_mono hRfin hbound
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hreal
  rw [← aux_rem_resolved_microscopic_neumann_eLpNorm_two_sq hmem2]
  have h0 : 0 ≤ (eLpNorm h 2 (μ.restrict S)).toReal := ENNReal.toReal_nonneg
  calc ((eLpNorm h 2 (μ.restrict S)).toReal) ^ 2
      ≤ ((eLpNorm h (ENNReal.ofReal p1) (μ.restrict Bl)).toReal *
          (μ S).toReal ^ (1 / 2 - 1 / p1)) ^ 2 := pow_le_pow_left₀ h0 hreal 2
    _ = ((μ S).toReal ^ (1 / 2 - 1 / p1)) ^ 2 *
          ((eLpNorm h (ENNReal.ofReal p1) (μ.restrict Bl)).toReal) ^ 2 := by ring
    _ = (μ.real S) ^ (1 - 2 / p1) *
          ((eLpNorm h (ENNReal.ofReal p1) (μ.restrict Bl)).toReal) ^ 2 := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
        congr 1
        push_cast; ring

/-- The final real algebra of the one-centre estimate. -/
theorem aux_rem_resolved_microscopic_neumann_combine
    (Gr G e a0 mN Cw Kf Np1 N2 R L M ell C : ℝ)
    (he : 0 ≤ e) (ha0 : 0 < a0) (hmN : 0 < mN) (hmNa0 : mN ≤ a0) (hR : 0 ≤ R) (hL : 0 ≤ L) (hM : 0 < M) (hG : 0 ≤ G)
    (h1 : Gr ≤ e * a0 * (R * (Np1 ^ 2 * L)))
    (hNp1 : 0 ≤ Np1) (hN : Np1 ≤ Cw * N2 + Cw * (ell / 2) * a0⁻¹ * Kf)
    (hN2 : N2 ^ 2 ≤ e * G / (a0 * M))
    (hC1 : 2 * Cw ^ 2 * e ^ 2 ≤ C) (hC2 : Cw ^ 2 * e / 2 ≤ C) :
    Gr ≤ C * (R * L / M) * G + C * mN⁻¹ * Kf ^ 2 * (R * L * ell ^ 2) := by
  have hsq : Np1 ^ 2 ≤ 2 * Cw ^ 2 * N2 ^ 2 + 2 * Cw ^ 2 * (ell / 2) ^ 2 * a0⁻¹ ^ 2 * Kf ^ 2 := by
    have h' : Np1 ^ 2 ≤ (Cw * N2 + Cw * (ell / 2) * a0⁻¹ * Kf) ^ 2 := pow_le_pow_left₀ hNp1 hN 2
    nlinarith [sq_nonneg (Cw * N2 - Cw * (ell / 2) * a0⁻¹ * Kf)]
  have hsq2 : Np1 ^ 2 ≤ 2 * Cw ^ 2 * (e * G / (a0 * M)) +
      2 * Cw ^ 2 * (ell / 2) ^ 2 * a0⁻¹ ^ 2 * Kf ^ 2 := by
    have : 2 * Cw ^ 2 * N2 ^ 2 ≤ 2 * Cw ^ 2 * (e * G / (a0 * M)) :=
      mul_le_mul_of_nonneg_left hN2 (by positivity)
    linarith
  have hRL : 0 ≤ R * L := mul_nonneg hR hL
  have hpref : 0 ≤ e * a0 * R * L := by positivity
  have hstep : Gr ≤ e * a0 * R * L * (2 * Cw ^ 2 * (e * G / (a0 * M)) +
      2 * Cw ^ 2 * (ell / 2) ^ 2 * a0⁻¹ ^ 2 * Kf ^ 2) := by
    calc Gr ≤ e * a0 * (R * (Np1 ^ 2 * L)) := h1
      _ = e * a0 * R * L * Np1 ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq2 hpref
  have hident : e * a0 * R * L * (2 * Cw ^ 2 * (e * G / (a0 * M)) +
      2 * Cw ^ 2 * (ell / 2) ^ 2 * a0⁻¹ ^ 2 * Kf ^ 2) =
      (2 * Cw ^ 2 * e ^ 2) * (R * L / M) * G +
        (Cw ^ 2 * e / 2) * a0⁻¹ * Kf ^ 2 * (R * L * ell ^ 2) := by
    field_simp
  have hinv : a0⁻¹ ≤ mN⁻¹ := inv_anti₀ hmN hmNa0
  have hA : 0 ≤ R * L / M * G := by positivity
  have hB : 0 ≤ Kf ^ 2 * (R * L * ell ^ 2) := by positivity
  have hCnn : 0 ≤ C := le_trans (by positivity) hC2
  calc Gr ≤ _ := hstep
    _ = _ := hident
    _ = (2 * Cw ^ 2 * e ^ 2) * (R * L / M * G) +
          (Cw ^ 2 * e / 2) * a0⁻¹ * (Kf ^ 2 * (R * L * ell ^ 2)) := by ring
    _ ≤ C * (R * L / M * G) + C * mN⁻¹ * (Kf ^ 2 * (R * L * ell ^ 2)) := by
        gcongr
    _ = C * (R * L / M) * G + C * mN⁻¹ * Kf ^ 2 * (R * L * ell ^ 2) := by ring




/-- The frozen `SolvesNeumann` premise forces the source to have mean zero:
test the full-`H¹` equation with the constant function one. -/
theorem aux_rem_resolved_microscopic_neumann_mean_zero {d : ℕ}
    (a : PositiveCoefficient (unitNeumannCube d)) (f : SpatialCoordinates d → ℝ)
    (u : meanZeroSobolevGraph (unitNeumannCube d)) (hu : SolvesNeumann a f u) :
    (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x) = 0 := by
  have h := hu ⟨_, constantSobolevData_mem_weak (Om := unitNeumannCube d) 1⟩
  have hL : sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d))
      ((domainConstantL2 (Ω := unitNeumannCube d) 1,
        fun _ => (0 : DomainL2 (unitNeumannCube d))) : SobolevData (unitNeumannCube d)) = 0 := by
    rw [sobolevCoefficientForm_apply]
    refine Finset.sum_eq_zero fun i _ => integral_eq_zero_of_ae ?_
    filter_upwards [Lp.coeFn_zero ℝ 2
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)))] with x hx
    have h0 : ((0 : DomainL2 (unitNeumannCube d)) : SpatialCoordinates d → ℝ) x = 0 := hx
    show _ * (_ * ((0 : DomainL2 (unitNeumannCube d)) : SpatialCoordinates d → ℝ) x) = 0
    rw [h0, mul_zero, mul_zero]
  have hR : (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
      f x * (domainConstantL2 (Ω := unitNeumannCube d) 1 : SpatialCoordinates d → ℝ) x) =
      ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x := by
    apply integral_congr_ae
    filter_upwards [domainConstantL2_coeFn (Ω := unitNeumannCube d) 1] with x hx
    rw [hx, mul_one]
  change sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d))
      ((domainConstantL2 (Ω := unitNeumannCube d) 1,
        fun _ => (0 : DomainL2 (unitNeumannCube d))) : SobolevData (unitNeumannCube d)) =
    ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
      f x * (domainConstantL2 (Ω := unitNeumannCube d) 1 : SpatialCoordinates d → ℝ) x at h
  rw [hL, hR] at h
  exact h.symm

/-- The published interior `W^{1,p_1}` input applied to the restriction of a full-`H¹`
weak solution on a larger domain to an interior cube: the coefficient and the solution
are the actual restrictions, and the killed-test equation on the small cube comes from
zero extension of killed tests. -/
theorem aux_rem_resolved_microscopic_neumann_interior {d : ℕ} (W : SmallPerturbationInput d)
    (p1 : ℝ) (hp1 : 2 ≤ p1) {U : Opens (SpatialCoordinates d)} (x : SpatialCoordinates d)
    (l : ℝ) (hl : 0 < 4 * l) (hSub : centeredCube x (4 * l) hl ≤ U)
    (af : PositiveCoefficient U) (vf : weakSobolevGraph U) (F : SpatialCoordinates d → ℝ)
    (hweak : ∀ ψ : weakSobolevGraph U,
      sobolevCoefficientForm af (vf : SobolevData U) (ψ : SobolevData U) =
        ∫ y in (U : Set (SpatialCoordinates d)), F y * (ψ : SobolevData U).1 y)
    (a0 : ℝ) (ha0 : 0 < a0)
    (hosc : ∀ᵐ y ∂volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d)),
      |Real.log (af.val y) - Real.log a0| ≤ W.osc p1)
    (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFmeas : AEMeasurable F
      (volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d))))
    (hFbd : ∀ᵐ y ∂volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d)),
      |F y| ≤ Kf) :
    MemLp (fun y => Real.sqrt (∑ i : Fin d,
          ((sobolevGradient (sobolevDataRestrict hSub (vf : SobolevData U))) i y) ^ 2))
        (ENNReal.ofReal p1)
        ((volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d))).restrict
          (Metric.ball x l)) ∧
      normalizedGradientLpNorm (ENNReal.ofReal p1) (Metric.ball x l)
          (sobolevGradient (sobolevDataRestrict hSub (vf : SobolevData U))) ≤
        W.C p1 * normalizedGradientLpNorm 2 (Metric.ball x (2 * l))
            (sobolevGradient (sobolevDataRestrict hSub (vf : SobolevData U))) +
          W.C p1 * l * a0⁻¹ * Kf := by
  set as := positiveCoefficientRestrict hSub af
  have hosc' : ∀ᵐ y ∂volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d)),
      |Real.log (as.val y) - Real.log a0| ≤ W.osc p1 := by
    filter_upwards [positiveCoefficientRestrict_coeFn hSub af, hosc] with y h1 h2
    rw [h1]; exact h2
  have hweak_s : ∀ φ : killedSobolevGraph (centeredCube x (4 * l) hl),
      sobolevCoefficientForm as (sobolevDataRestrict hSub (vf : SobolevData U))
          (φ : SobolevData (centeredCube x (4 * l) hl)) =
        ∫ y in (centeredCube x (4 * l) hl : Set (SpatialCoordinates d)),
          F y * (φ : SobolevData (centeredCube x (4 * l) hl)).1 y := by
    intro φ
    have hψ := zeroExtensionSobolevData_mem_weak_of_killed hSub φ.2
    have h1 := hweak ⟨_, hψ⟩
    have h2 := sobolevCoefficientForm_zeroExtension hSub af as
      (positiveCoefficientRestrict_coeFn hSub af).symm
      (φ : SobolevData (centeredCube x (4 * l) hl)) (vf : SobolevData U)
    calc sobolevCoefficientForm as (sobolevDataRestrict hSub (vf : SobolevData U))
          (φ : SobolevData (centeredCube x (4 * l) hl))
        = sobolevCoefficientForm as (φ : SobolevData (centeredCube x (4 * l) hl))
            (sobolevDataRestrict hSub (vf : SobolevData U)) := sobolevCoefficientForm_symm _ _ _
      _ = sobolevCoefficientForm af
            (zeroExtensionSobolevData hSub (φ : SobolevData (centeredCube x (4 * l) hl)))
            (vf : SobolevData U) := h2.symm
      _ = sobolevCoefficientForm af (vf : SobolevData U)
            (zeroExtensionSobolevData hSub (φ : SobolevData (centeredCube x (4 * l) hl))) :=
          sobolevCoefficientForm_symm _ _ _
      _ = ∫ y in (U : Set (SpatialCoordinates d)), F y *
            zeroExtensionLp hSub (φ : SobolevData (centeredCube x (4 * l) hl)).1 y := h1
      _ = _ := integral_mul_zeroExtensionLp hSub F _
  exact W.interior_gradient p1 hp1 x l hl as a0 ha0 hosc' F Kf hFmeas hKf hFbd
    ⟨sobolevDataRestrict hSub (vf : SobolevData U), sobolevDataRestrict_mem_weak hSub vf.2⟩
    hweak_s

theorem aux_rem_resolved_microscopic_neumann_unit_sub_folded {d : ℕ} (I P : Finset (Fin d)) :
    (unitNeumannCube d : Set (SpatialCoordinates d)) ⊆
      (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)) := by
  intro y hy
  have hyj := aux_rem_resolved_microscopic_neumann_mem_unit.1 hy
  rw [aux_rem_resolved_microscopic_neumann_mem_folded]
  intro j
  have := hyj j
  split_ifs <;> constructor <;> linarith [this.1, this.2]

/-- An `L²` square times an essentially bounded positive coefficient is integrable. -/
theorem aux_rem_resolved_microscopic_neumann_coeff_sq_integrable {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} (b : PositiveCoefficient Ω) (g : DomainL2 Ω) :
    Integrable (fun y => b.val y * g y ^ 2) (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  have hle := positiveCoefficientRestrict_le_norm (le_refl Ω) b
  rw [positiveCoefficientRestrict_refl] at hle
  refine (Lp.memLp g).integrable_sq.bdd_mul (c := ‖b.val‖) (Lp.aestronglyMeasurable _) ?_
  filter_upwards [hle, positiveCoefficient_ae_nonneg b] with y h1 h2
  rw [Real.norm_eq_abs, abs_of_nonneg h2]; exact h1

/-- A continuous-tie coefficient bounded on the cube times an `L²` square is integrable. -/
theorem aux_rem_resolved_microscopic_neumann_tie_sq_integrable {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} (A : SpatialCoordinates d → ℝ) (hA : Continuous A)
    (MN : ℝ) (hAb : ∀ y ∈ (Ω : Set (SpatialCoordinates d)), |A y| ≤ MN) (g : DomainL2 Ω) :
    Integrable (fun y => A y * g y ^ 2) (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
  refine (Lp.memLp g).integrable_sq.bdd_mul (c := MN) hA.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with y hy
  rw [Real.norm_eq_abs]; exact hAb y hy

/-- Upper energy chain: the folded gradient energy on a set inside a reflection-symmetric
box is controlled by the original coefficient energy on a cube containing the box, using the
exact `2^{|I|}` identity of `lem_even_energy_transport`. -/
theorem aux_rem_resolved_microscopic_neumann_fold_energy {d : ℕ} (I P : Finset (Fin d))
    (a : PositiveCoefficient (unitNeumannCube d)) (A : SpatialCoordinates d → ℝ)
    (hAc : Continuous A) (MN : ℝ)
    (haA : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (hAb : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), 0 ≤ A y ∧ A y ≤ MN)
    (v : weakSobolevGraph (unitNeumannCube d))
    (af : PositiveCoefficient (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P))
    (vf : weakSobolevGraph (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P))
    (haf : ((af.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P :
          Set (SpatialCoordinates d))]
      fun x => a.val (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P x)))
    (hg : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P :
          Set (SpatialCoordinates d)),
        sobolevGradient (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)) j x =
          (if j ∈ I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P j then -1 else 1)
           else 1) *
            sobolevGradient (v : SobolevData (unitNeumannCube d)) j
              (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P x))
    (Bx : Set (SpatialCoordinates d)) (hB : MeasurableSet Bx)
    (hBU : Bx ⊆ (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)))
    (hBs : ∀ J : Finset (Fin d), J ⊆ I →
      coordinateReflection (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) J ⁻¹' Bx = Bx)
    (Sb S : Set (SpatialCoordinates d)) (hSbB : Sb ⊆ Bx) (hBS : Bx ⊆ S)
    (hS : MeasurableSet S) (e a0 : ℝ) (ha0 : 0 < a0) (he : 0 ≤ e)
    (hlow : ∀ᵐ y ∂volume.restrict Sb, a0 ≤ e * af.val y) :
    ∫ y in Sb, ∑ i : Fin d,
        ((vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y) ^ 2 ≤
      e / a0 * 2 ^ d * ∫ y in S ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
        A y * ∑ i : Fin d, ((v : SobolevData (unitNeumannCube d)).2 i y) ^ 2 := by
  have hSbU : Sb ⊆ (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)) := hSbB.trans hBU
  have hintU : ∀ i, Integrable (fun y => af.val y * (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y ^ 2)
      (volume.restrict (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d))) := fun i =>
    aux_rem_resolved_microscopic_neumann_coeff_sq_integrable af ((vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i)
  have hafnn : ∀ᵐ y ∂volume.restrict (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)), 0 ≤ af.val y :=
    positiveCoefficient_ae_nonneg af
  -- per-coordinate comparison on `Sb`, then enlargement to the box
  have hper : ∀ i, ∫ y in Sb, (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y ^ 2 ≤ e / a0 * ∫ y in Bx, af.val y * (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y ^ 2 := by
    intro i
    have h1 : ∫ y in Sb, (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y ^ 2 ≤ ∫ y in Sb, e / a0 * (af.val y * (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y ^ 2) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => sq_nonneg _) ?_ ?_
      · exact ((hintU i).mono_measure (Measure.restrict_mono hSbU le_rfl)).const_mul _
      · filter_upwards [hlow] with y hy
        have hq : 1 ≤ e / a0 * af.val y := by
          rw [div_mul_eq_mul_div, le_div_iff₀ ha0, one_mul]; exact hy
        calc (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y ^ 2 = 1 * (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y ^ 2 := (one_mul _).symm
          _ ≤ e / a0 * af.val y * (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y ^ 2 :=
            mul_le_mul_of_nonneg_right hq (sq_nonneg _)
          _ = e / a0 * (af.val y * (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y ^ 2) := by ring
    rw [integral_const_mul] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (div_nonneg he ha0.le))
    refine setIntegral_mono_set ((hintU i).mono_measure (Measure.restrict_mono hBU le_rfl)) ?_
      (Filter.Eventually.of_forall hSbB)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hBU hafnn] with y hy
    exact mul_nonneg hy (sq_nonneg _)
  -- the folded energy identity on the symmetric box
  have hE := lem_even_energy_transport d (fun _ => (1 / 2 : ℝ)) 1 one_pos I P a v af vf haf hg
    Bx hB hBs
  erw [localGradientEnergy_eq_integral, localGradientEnergy_eq_integral] at hE
  have hBmeasU : (volume.restrict (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d))).restrict Bx =
      volume.restrict Bx := by
    rw [Measure.restrict_restrict hB, Set.inter_eq_left.2 hBU]
  have hQmeas : MeasurableSet (unitNeumannCube d : Set (SpatialCoordinates d)) := (unitNeumannCube d).isOpen.measurableSet
  have hBQ : (volume.restrict ((centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
      Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))).restrict
      (Bx ∩ ((centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
        Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) =
      volume.restrict (Bx ∩ (unitNeumannCube d : Set (SpatialCoordinates d))) := by
    rw [Measure.restrict_restrict (hB.inter (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1
      one_pos).isOpen.measurableSet), Set.inter_assoc, Set.inter_self]
    rfl
  rw [hBmeasU, hBQ] at hE
  have hE' : ∑ i : Fin d, ∫ y in Bx, af.val y * (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y ^ 2 =
      2 ^ I.card * ∫ y in Bx ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (v : SobolevData (unitNeumannCube d)).2 i y ^ 2 := by
    have hconv : ∀ i : Fin d, ∫ y in Bx ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
        a.val y * (sobolevGradient (v : SobolevData (unitNeumannCube d)) i y) ^ 2 =
        ∫ y in Bx ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * (v : SobolevData (unitNeumannCube d)).2 i y ^ 2 := by
      intro i
      refine setIntegral_congr_ae (hB.inter hQmeas) ?_
      filter_upwards [(ae_restrict_iff' hQmeas).1 haA] with y hy hyBQ
      rw [hy hyBQ.2]; rfl
    have hsum : ∫ y in Bx ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (v : SobolevData (unitNeumannCube d)).2 i y ^ 2 =
        ∑ i : Fin d, ∫ y in Bx ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * (v : SobolevData (unitNeumannCube d)).2 i y ^ 2 := by
      simp_rw [Finset.mul_sum]
      refine integral_finsetSum _ fun i _ => ?_
      refine (aux_rem_resolved_microscopic_neumann_tie_sq_integrable (Ω := unitNeumannCube d) A hAc MN
        (fun y hy => by rw [abs_of_nonneg (hAb y hy).1]; exact (hAb y hy).2) ((v : SobolevData (unitNeumannCube d)).2 i)).mono_measure
        (Measure.restrict_mono Set.inter_subset_right le_rfl)
    rw [hsum, ← Finset.sum_congr rfl fun i _ => hconv i]
    exact hE
  -- assemble
  have hQint : 0 ≤ ∫ y in Bx ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (v : SobolevData (unitNeumannCube d)).2 i y ^ 2 := by
    refine setIntegral_nonneg (hB.inter hQmeas) fun y hy => ?_
    exact mul_nonneg (hAb y hy.2).1 (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hmonoS : ∫ y in Bx ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (v : SobolevData (unitNeumannCube d)).2 i y ^ 2 ≤
      ∫ y in S ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (v : SobolevData (unitNeumannCube d)).2 i y ^ 2 := by
    have hint : IntegrableOn (fun y => A y * ∑ i : Fin d, (v : SobolevData (unitNeumannCube d)).2 i y ^ 2)
        (S ∩ (unitNeumannCube d : Set (SpatialCoordinates d))) volume := by
      have : Integrable (fun y => A y * ∑ i : Fin d, (v : SobolevData (unitNeumannCube d)).2 i y ^ 2)
          (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) := by
        simp_rw [Finset.mul_sum]
        exact integrable_finsetSum _ fun i _ =>
          aux_rem_resolved_microscopic_neumann_tie_sq_integrable (Ω := unitNeumannCube d) A hAc MN
            (fun y hy => by rw [abs_of_nonneg (hAb y hy).1]; exact (hAb y hy).2) ((v : SobolevData (unitNeumannCube d)).2 i)
      exact this.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)
    refine setIntegral_mono_set hint ?_ (Filter.Eventually.of_forall
      (Set.inter_subset_inter_left _ hBS))
    filter_upwards [ae_restrict_mem (hS.inter hQmeas)] with y hy
    exact mul_nonneg (hAb y hy.2).1 (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hcard : (2 : ℝ) ^ I.card ≤ 2 ^ d := by
    have : I.card ≤ d := by simpa using Finset.card_le_univ I
    exact pow_le_pow_right₀ (by norm_num) this
  have hSbint : ∫ y in Sb, ∑ i : Fin d, (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y ^ 2 = ∑ i : Fin d, ∫ y in Sb, (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y ^ 2 :=
    integral_finsetSum _ fun i _ =>
      ((Lp.memLp ((vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i)).integrable_sq).mono_measure (Measure.restrict_mono hSbU le_rfl)
  rw [hSbint]
  calc ∑ i : Fin d, ∫ y in Sb, (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y ^ 2
      ≤ ∑ i : Fin d, e / a0 * ∫ y in Bx, af.val y * (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y ^ 2 :=
        Finset.sum_le_sum fun i _ => hper i
    _ = e / a0 * (2 ^ I.card *
          ∫ y in Bx ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (v : SobolevData (unitNeumannCube d)).2 i y ^ 2) := by
        rw [← Finset.mul_sum, hE']
    _ ≤ e / a0 * (2 ^ d *
          ∫ y in S ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (v : SobolevData (unitNeumannCube d)).2 i y ^ 2) := by
        gcongr
    _ = _ := by ring

/-- Lower chain: on the unit cube the fold is the identity with gradient factor one, so the
original energy on `S_r ∩ Q` is at most the folded energy on `S_r`. -/
theorem aux_rem_resolved_microscopic_neumann_lower {d : ℕ} (I P : Finset (Fin d))
    (A : SpatialCoordinates d → ℝ) (MN : ℝ)
    (hAb : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), 0 ≤ A y ∧ A y ≤ MN)
    (v : weakSobolevGraph (unitNeumannCube d))
    (vf : weakSobolevGraph (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P))
    (hg : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P :
          Set (SpatialCoordinates d)),
        sobolevGradient (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)) j x =
          (if j ∈ I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P j then -1 else 1)
           else 1) *
            sobolevGradient (v : SobolevData (unitNeumannCube d)) j
              (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P x))
    (Sr : Set (SpatialCoordinates d)) (hSr : MeasurableSet Sr)
    (hSrU : Sr ⊆ (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)))
    (b : ℝ) (hb : 0 ≤ b)
    (hup : ∀ y ∈ Sr ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y ≤ b) :
    ∫ y in Sr ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
        A y * ∑ i : Fin d, ((v : SobolevData (unitNeumannCube d)).2 i y) ^ 2 ≤
      b * ∫ y in Sr, ∑ i : Fin d,
        ((vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y) ^ 2 := by
  have hQmeas : MeasurableSet (unitNeumannCube d : Set (SpatialCoordinates d)) :=
    (unitNeumannCube d).isOpen.measurableSet
  have hUmeas : MeasurableSet (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P :
      Set (SpatialCoordinates d)) := (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P).isOpen.measurableSet
  have hintQ : Integrable (fun y => ∑ i : Fin d, ((v : SobolevData (unitNeumannCube d)).2 i y) ^ 2)
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
    integrable_finsetSum _ fun i _ => (Lp.memLp _).integrable_sq
  have hintU : Integrable (fun y => ∑ i : Fin d,
      ((vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y) ^ 2)
      (volume.restrict (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P :
        Set (SpatialCoordinates d))) :=
    integrable_finsetSum _ fun i _ => (Lp.memLp _).integrable_sq
  have h1 : ∫ y in Sr ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
        A y * ∑ i : Fin d, ((v : SobolevData (unitNeumannCube d)).2 i y) ^ 2 ≤
      ∫ y in Sr ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
        b * ∑ i : Fin d, ((v : SobolevData (unitNeumannCube d)).2 i y) ^ 2 := by
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards [ae_restrict_mem (hSr.inter hQmeas)] with y hy
      exact mul_nonneg (hAb y hy.2).1 (Finset.sum_nonneg fun i _ => sq_nonneg _)
    · exact (hintQ.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)).const_mul _
    · filter_upwards [ae_restrict_mem (hSr.inter hQmeas)] with y hy
      exact mul_le_mul_of_nonneg_right (hup y hy) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [integral_const_mul] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ hb)
  have hcongr : ∫ y in Sr ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
        ∑ i : Fin d, ((v : SobolevData (unitNeumannCube d)).2 i y) ^ 2 =
      ∫ y in Sr ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), ∑ i : Fin d,
        ((vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y) ^ 2 := by
    refine setIntegral_congr_ae (hSr.inter hQmeas) ?_
    filter_upwards [(ae_restrict_iff' hUmeas).1 (ae_all_iff.2 hg)] with y hy hyS
    have hyU := aux_rem_resolved_microscopic_neumann_unit_sub_folded I P hyS.2
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := hy hyU i
    rw [aux_rem_resolved_microscopic_neumann_fold_sign I P hyS.2 i, one_mul,
      aux_rem_resolved_microscopic_neumann_fold_id I P hyS.2] at h
    change ((vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i) y =
      ((v : SobolevData (unitNeumannCube d)).2 i) y at h
    rw [h]
  rw [hcongr]
  refine setIntegral_mono_set (hintU.mono_measure (Measure.restrict_mono hSrU le_rfl)) ?_
    (Filter.Eventually.of_forall Set.inter_subset_left)
  exact Filter.Eventually.of_forall fun y => Finset.sum_nonneg fun i _ => sq_nonneg _

theorem aux_rem_resolved_microscopic_neumann_ball_volume_real {d : ℕ} (x : SpatialCoordinates d)
    {ρ : ℝ} (hρ : 0 < ρ) : volume.real (Metric.ball x ρ) = (2 * ρ) ^ d := by
  rw [Measure.real, Real.volume_pi_ball x hρ, Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]

theorem aux_rem_resolved_microscopic_neumann_cube_eq_ball {d : ℕ} (x : SpatialCoordinates d)
    {ρ : ℝ} (hρ : 0 < ρ) :
    {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < ρ} = Metric.ball x ρ := by
  ext y
  rw [Metric.mem_ball, dist_pi_lt_iff hρ]
  simp [Real.dist_eq]

/-- Hölder on the small cube `S_r`, transported to the restriction on the interior cube. -/
theorem aux_rem_resolved_microscopic_neumann_holder_chain {d : ℕ} (p1 : ℝ) (hp1 : 2 ≤ p1)
    {U : Opens (SpatialCoordinates d)} (x : SpatialCoordinates d) (l : ℝ) (hl : 0 < 4 * l)
    (hSub : centeredCube x (4 * l) hl ≤ U) (vf : weakSobolevGraph U)
    (Sr : Set (SpatialCoordinates d)) (hSr : MeasurableSet Sr) (hSrB : Sr ⊆ Metric.ball x l)
    (hSrfin : volume Sr ≠ ∞)
    (hmem : MemLp (fun y => Real.sqrt (∑ i : Fin d,
          ((sobolevGradient (sobolevDataRestrict hSub (vf : SobolevData U))) i y) ^ 2))
        (ENNReal.ofReal p1)
        ((volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d))).restrict
          (Metric.ball x l))) :
    ∫ y in Sr, ∑ i : Fin d, ((vf : SobolevData U).2 i y) ^ 2 ≤
      (volume.real Sr) ^ (1 - 2 / p1) *
        ((eLpNorm (fun y => Real.sqrt (∑ i : Fin d,
          ((sobolevGradient (sobolevDataRestrict hSub (vf : SobolevData U))) i y) ^ 2))
          (ENNReal.ofReal p1)
          ((volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d))).restrict
            (Metric.ball x l))).toReal) ^ 2 := by
  have hl0 : 0 < l := by linarith
  have hballSub : Metric.ball x l ⊆ (centeredCube x (4 * l) hl : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_ball (by linarith)
  have hSrSub := hSrB.trans hballSub
  have hSubmeas : MeasurableSet (centeredCube x (4 * l) hl : Set (SpatialCoordinates d)) :=
    (centeredCube x (4 * l) hl).isOpen.measurableSet
  have hμS : (volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d))).restrict Sr =
      volume.restrict Sr := by
    rw [Measure.restrict_restrict hSr, Set.inter_eq_left.2 hSrSub]
  have hfinS : (volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d))) Sr ≠ ∞ := by
    rw [Measure.restrict_apply hSr, Set.inter_eq_left.2 hSrSub]; exact hSrfin
  have key := aux_rem_resolved_microscopic_neumann_holder_sq
    (volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d))) hSrB hfinS hmem.aestronglyMeasurable hp1
    hmem.eLpNorm_ne_top
  have hreal : (volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d))).real Sr =
      volume.real Sr := by
    rw [Measure.real, Measure.restrict_apply hSr, Set.inter_eq_left.2 hSrSub]; rfl
  rw [hreal, hμS] at key
  refine le_of_eq_of_le ?_ key
  refine setIntegral_congr_ae hSr ?_
  have hG : ∀ i : Fin d, ∀ᵐ y ∂volume, y ∈ Sr →
      (sobolevGradient (sobolevDataRestrict hSub (vf : SobolevData U))) i y =
        ((vf : SobolevData U).2 i) y := fun i =>
    (ae_restrict_iff' hSubmeas).1 (domainLpRestrict_coeFn hSub ((vf : SobolevData U).2 i))
      |>.mono fun y hy hyS => hy (hSrSub hyS)
  filter_upwards [ae_all_iff.2 hG] with y hy hyS
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun i _ => by rw [hy i hyS]

/-- The normalized `L²` norm on the interior cube, squared, is the energy average. -/
theorem aux_rem_resolved_microscopic_neumann_normalized_two {d : ℕ}
    {U : Opens (SpatialCoordinates d)} (x : SpatialCoordinates d) (l : ℝ) (hl : 0 < 4 * l)
    (hSub : centeredCube x (4 * l) hl ≤ U) (vf : weakSobolevGraph U) :
    (normalizedGradientLpNorm 2 (Metric.ball x (2 * l))
        (sobolevGradient (sobolevDataRestrict hSub (vf : SobolevData U)))) ^ 2 =
      (∫ y in (centeredCube x (4 * l) hl : Set (SpatialCoordinates d)),
          ∑ i : Fin d, ((vf : SobolevData U).2 i y) ^ 2) /
        volume.real (Metric.ball x (2 * l)) := by
  have hl0 : 0 < l := by linarith
  have hball : Metric.ball x (2 * l) = (centeredCube x (4 * l) hl : Set (SpatialCoordinates d)) := by
    change Metric.ball x (2 * l) = Metric.ball x (4 * l / 2)
    congr 1; ring
  have hSubmeas : MeasurableSet (centeredCube x (4 * l) hl : Set (SpatialCoordinates d)) :=
    (centeredCube x (4 * l) hl).isOpen.measurableSet
  have hV : 0 < volume.real (Metric.ball x (2 * l)) := by
    rw [aux_rem_resolved_microscopic_neumann_ball_volume_real x (by linarith)]; positivity
  unfold normalizedGradientLpNorm
  have hμ : (volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d))).restrict
      (Metric.ball x (2 * l)) =
      volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d)) := by
    rw [hball, Measure.restrict_restrict hSubmeas, Set.inter_self]
  rw [hμ, div_pow]
  have h2 : (1 : ℝ) / (2 : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ)⁻¹ := by norm_num
  rw [h2, Real.rpow_inv_natCast_pow hV.le (by norm_num)]
  congr 1
  rw [aux_rem_resolved_microscopic_neumann_eLpNorm_two_sq
    (aux_rem_resolved_microscopic_neumann_sqrt_sum_memLp fun i => Lp.memLp _)]
  refine integral_congr_ae ?_
  have hG : ∀ i : Fin d, ∀ᵐ y ∂volume.restrict
      (centeredCube x (4 * l) hl : Set (SpatialCoordinates d)),
      (sobolevGradient (sobolevDataRestrict hSub (vf : SobolevData U))) i y =
        ((vf : SobolevData U).2 i) y := fun i =>
    domainLpRestrict_coeFn hSub ((vf : SobolevData U).2 i)
  filter_upwards [ae_all_iff.2 hG] with y hy
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun i _ => by rw [hy i]

/-- The normalized `L^{p_1}` norm times the normalizing volume power is the norm itself. -/
theorem aux_rem_resolved_microscopic_neumann_normalized_p {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} (p : ℝ≥0∞) (s : Set (SpatialCoordinates d))
    (g : HilbertGradient Ω) (hs : 0 < volume.real s) :
    (eLpNorm (fun y => Real.sqrt (∑ i : Fin d, (g i y) ^ 2)) p
        ((volume.restrict (Ω : Set (SpatialCoordinates d))).restrict s)).toReal =
      normalizedGradientLpNorm p s g * (volume.real s) ^ (1 / p.toReal) := by
  unfold normalizedGradientLpNorm
  rw [div_mul_cancel₀]
  exact (Real.rpow_pos_of_pos hs _).ne'

theorem aux_rem_resolved_microscopic_neumann_rpow_ident (d : ℕ) (p1 r ell : ℝ)
    (hr : 0 < r) (hell : 0 < ell) :
    (r ^ d) ^ (1 - 2 / p1) * ((ell ^ d) ^ (1 / p1)) ^ 2 / ell ^ d =
        (r / ell) ^ ((d : ℝ) - 2 * (d : ℝ) / p1) ∧
      (r ^ d) ^ (1 - 2 / p1) * ((ell ^ d) ^ (1 / p1)) ^ 2 * ell ^ 2 =
        ell ^ (2 + 2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) := by
  have hR : (r ^ d) ^ (1 - 2 / p1) = r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) := by
    rw [← Real.rpow_natCast_mul hr.le]; congr 1; ring
  have hL : ((ell ^ d) ^ (1 / p1)) ^ 2 = ell ^ (2 * (d : ℝ) / p1) := by
    rw [← Real.rpow_natCast_mul hell.le, ← Real.rpow_natCast, ← Real.rpow_mul hell.le]
    congr 1; push_cast; ring
  have hM : ell ^ d = ell ^ (d : ℝ) := (Real.rpow_natCast ell d).symm
  have h2 : ell ^ 2 = ell ^ (2 : ℝ) := (Real.rpow_natCast ell 2).symm
  rw [hR, hL]
  constructor
  · rw [hM, Real.div_rpow hr.le hell.le, mul_div_assoc, ← Real.rpow_sub hell]
    rw [show 2 * (d : ℝ) / p1 - d = -((d : ℝ) - 2 * (d : ℝ) / p1) by ring, Real.rpow_neg hell.le]
    exact (div_eq_mul_inv _ _).symm
  · rw [h2, mul_assoc, ← Real.rpow_add hell, mul_comm]
    congr 2; ring

theorem aux_rem_resolved_microscopic_neumann_exp_of_log {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : |Real.log a - Real.log b| ≤ c) : b ≤ Real.exp c * a ∧ a ≤ Real.exp c * b := by
  have h' := abs_le.1 h
  constructor
  · calc b = Real.exp (Real.log b) := (Real.exp_log hb).symm
      _ ≤ Real.exp (c + Real.log a) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp c * a := by rw [Real.exp_add, Real.exp_log ha]
  · calc a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ ≤ Real.exp (c + Real.log b) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp c * b := by rw [Real.exp_add, Real.exp_log hb]

theorem aux_rem_resolved_microscopic_neumann_cube_measurable {d : ℕ} (x : SpatialCoordinates d)
    (ρ : ℝ) : MeasurableSet {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < ρ} := by
  rw [ofPred_forall]
  exact MeasurableSet.iInter fun i => measurableSet_lt (by fun_prop) measurable_const

/-- The one-centre Neumann estimate for arbitrary active faces `I` and signs `P` whose folded
cube contains the `ell`-cube around the centre, with a reflection-symmetric box between the
`ell`-cube and the parent cube of side `rho`. -/
theorem aux_rem_resolved_microscopic_neumann_core {d : ℕ} (W : SmallPerturbationInput d)
    (p1 : ℝ) (hp1 : 2 ≤ p1) (I P : Finset (Fin d)) (C c : ℝ)
    (hcosc : c ≤ W.osc p1)
    (hC1 : 2 * W.C p1 ^ 2 * Real.exp c ^ 2 ≤ C) (hC2 : W.C p1 ^ 2 * Real.exp c / 2 ≤ C)
    (a : PositiveCoefficient (unitNeumannCube d)) (A : SpatialCoordinates d → ℝ)
    (hAc : Continuous A)
    (haA : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (mN MN : ℝ) (hmN : 0 < mN)
    (hAQ : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hfb : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf)
    (u : meanZeroSobolevGraph (unitNeumannCube d)) (hu : SolvesNeumann a f u)
    (x : SpatialCoordinates d) (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (ell : ℝ) (hell : 0 < ell)
    (hmodQ : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), dist y x ≤ ell →
      |Real.log (A y) - Real.log (A x)| ≤ c)
    (hUball : ∀ y, dist y x < ell →
      y ∈ (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)))
    (Bx : Set (SpatialCoordinates d)) (hB : MeasurableSet Bx)
    (hBU : Bx ⊆ (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)))
    (hBs : ∀ J : Finset (Fin d), J ⊆ I →
      coordinateReflection (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) J ⁻¹' Bx = Bx)
    (hballB : ∀ y, dist y x < ell → y ∈ Bx) (rho : ℝ)
    (hBS : Bx ⊆ {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < rho / 2})
    (r : ℝ) (hr : 0 < r) (hrell : r ≤ ell) :
    ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩
        (unitNeumannCube d : Set (SpatialCoordinates d)),
        A y * ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2 ≤
      C * (r / ell) ^ ((d : ℝ) - 2 * (d : ℝ) / p1) *
          (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < rho / 2} ∩
            (unitNeumannCube d : Set (SpatialCoordinates d)),
            A y * ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2) +
        C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) *
          r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) := by
  have hQmeas : MeasurableSet (unitNeumannCube d : Set (SpatialCoordinates d)) :=
    (unitNeumannCube d).isOpen.measurableSet
  have ha0 : 0 < A x := hmN.trans_le (hAQ x hx).1
  have hAb : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), 0 ≤ A y ∧ A y ≤ MN :=
    fun y hy => ⟨hmN.le.trans (hAQ y hy).1, (hAQ y hy).2⟩
  let v : weakSobolevGraph (unitNeumannCube d) :=
    ⟨(u : SobolevData (unitNeumannCube d)),
      (inf_le_left : meanZeroSobolevGraph (unitNeumannCube d) ≤ weakSobolevGraph _) u.2⟩
  have hmean := aux_rem_resolved_microscopic_neumann_mean_zero a f u hu
  have hfae : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      |f y| ≤ Kf := ae_restrict_of_forall_mem hQmeas hfb
  obtain ⟨af, vf, haf, _hvf, hg⟩ :=
    lem_even_fold_construction d (fun _ => (1 / 2 : ℝ)) 1 one_pos I P a v
  have hweakf := lem_even_weak_transport d (fun _ => (1 / 2 : ℝ)) 1 one_pos I P a v af vf haf hg
    f Kf hKf hf.aemeasurable hfae hmean hu
  have hl : 0 < 4 * (ell / 2) := by positivity
  have hSubball : ∀ y, y ∈ (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)) ↔
      dist y x < ell := by
    intro y
    change y ∈ Metric.ball x (4 * (ell / 2) / 2) ↔ _
    rw [Metric.mem_ball, show 4 * (ell / 2) / 2 = ell by ring]
  have hSubset : (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)) ⊆
      (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)) :=
    fun y hy => hUball y ((hSubball y).1 hy)
  have hSub : centeredCube x (4 * (ell / 2)) hl ≤ foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P :=
    hSubset
  have hSubmeas : MeasurableSet (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)) :=
    (centeredCube x (4 * (ell / 2)) hl).isOpen.measurableSet
  -- almost-every pullbacks through the actual fold
  have hTa := aux_rem_resolved_microscopic_neumann_fold_ae d (fun _ => (1 / 2 : ℝ)) 1 one_pos I P haA
  have hTf := aux_rem_resolved_microscopic_neumann_fold_ae d (fun _ => (1 / 2 : ℝ)) 1 one_pos I P hfae
  have hTx : coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P x = x :=
    aux_rem_resolved_microscopic_neumann_fold_id I P hx
  have hlogSub : ∀ᵐ y ∂volume.restrict
      (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)),
      af.val y = A (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y) ∧
      0 < A (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y) ∧
      |Real.log (A (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y)) -
        Real.log (A x)| ≤ c := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hSubset haf,
      ae_restrict_of_ae_restrict_of_subset hSubset hTa, ae_restrict_mem hSubmeas] with y h1 h2 hy
    refine ⟨h1.trans h2.1, hmN.trans_le (hAQ _ h2.2).1, hmodQ _ h2.2 ?_⟩
    calc dist (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y) x
        = dist (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y)
            (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P x) := by rw [hTx]
      _ ≤ dist y x := coordinateFold_nonexpansive _ I P y x
      _ ≤ ell := ((hSubball y).1 hy).le
  have hosc : ∀ᵐ y ∂volume.restrict
      (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)),
      |Real.log (af.val y) - Real.log (A x)| ≤ W.osc p1 :=
    hlogSub.mono fun y h => by rw [h.1]; exact h.2.2.trans hcosc
  have hlow : ∀ᵐ y ∂volume.restrict
      (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)),
      A x ≤ Real.exp c * af.val y :=
    hlogSub.mono fun y h => by
      rw [h.1]; exact (aux_rem_resolved_microscopic_neumann_exp_of_log h.2.1 ha0 h.2.2).1
  have hFmeas : AEMeasurable
      (fun y => f (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y))
      (volume.restrict (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d))) :=
    (hf.comp (coordinateFold_continuous _ I P).measurable).aemeasurable
  have hFbd : ∀ᵐ y ∂volume.restrict
      (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)),
      |f (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y)| ≤ Kf :=
    ae_restrict_of_ae_restrict_of_subset hSubset (hTf.mono fun y h => h.1)
  obtain ⟨hmem, hest⟩ := aux_rem_resolved_microscopic_neumann_interior W p1 hp1 x (ell / 2) hl
    hSub af vf (fun y => f (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y))
    hweakf (A x) ha0 hosc Kf hKf hFmeas hFbd
  -- the small cube `S_r`
  have hSr_eq := aux_rem_resolved_microscopic_neumann_cube_eq_ball x (half_pos hr)
  have hSrmeas : MeasurableSet {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} :=
    aux_rem_resolved_microscopic_neumann_cube_measurable x _
  have hSrB : {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ⊆
      Metric.ball x (ell / 2) := by
    rw [hSr_eq]; exact Metric.ball_subset_ball (by linarith)
  have hSrU : {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ⊆
      (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)) :=
    fun y hy => hUball y (lt_of_lt_of_le (hSrB hy) (by linarith))
  have hSrfin : volume {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ≠ ∞ := by
    rw [hSr_eq, Real.volume_pi_ball x (half_pos hr)]; exact ENNReal.ofReal_ne_top
  have hSrvol : volume.real {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} =
      r ^ d := by
    rw [hSr_eq, aux_rem_resolved_microscopic_neumann_ball_volume_real x (half_pos hr)]
    congr 1; ring
  have hup : ∀ y ∈ {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩
      (unitNeumannCube d : Set (SpatialCoordinates d)), A y ≤ Real.exp c * A x := by
    intro y hy
    have hyd : dist y x ≤ ell := by
      have := hSrB hy.1
      rw [Metric.mem_ball] at this; linarith
    exact (aux_rem_resolved_microscopic_neumann_exp_of_log (hmN.trans_le (hAQ y hy.2).1) ha0
      (hmodQ y hy.2 hyd)).2
  have hL1 := aux_rem_resolved_microscopic_neumann_lower I P A MN hAb v vf hg
    {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} hSrmeas hSrU
    (Real.exp c * A x) (by positivity) hup
  have hH := aux_rem_resolved_microscopic_neumann_holder_chain p1 hp1 x (ell / 2) hl hSub vf
    {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} hSrmeas hSrB hSrfin hmem
  have hballvol : volume.real (Metric.ball x (ell / 2)) = ell ^ d := by
    rw [aux_rem_resolved_microscopic_neumann_ball_volume_real x (by positivity)]; congr 1; ring
  have hEp := aux_rem_resolved_microscopic_neumann_normalized_p (ENNReal.ofReal p1)
    (Metric.ball x (ell / 2)) (sobolevGradient (sobolevDataRestrict hSub
      (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P))))
    (by rw [hballvol]; positivity)
  rw [hballvol, ENNReal.toReal_ofReal (by linarith)] at hEp
  have hN2 := aux_rem_resolved_microscopic_neumann_normalized_two x (ell / 2) hl hSub vf
  have hball2vol : volume.real (Metric.ball x (2 * (ell / 2))) = 2 ^ d * ell ^ d := by
    rw [aux_rem_resolved_microscopic_neumann_ball_volume_real x (by positivity), ← mul_pow]
    congr 1; ring
  rw [hball2vol] at hN2
  have hrhomeas := aux_rem_resolved_microscopic_neumann_cube_measurable x (rho / 2)
  have hFE := aux_rem_resolved_microscopic_neumann_fold_energy I P a A hAc MN haA hAb v af vf haf hg
    Bx hB hBU hBs (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d))
    {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < rho / 2}
    (fun y hy => hballB y ((hSubball y).1 hy)) hBS hrhomeas (Real.exp c) (A x) ha0
    (Real.exp_pos c).le hlow
  -- names for the scalars
  set G := ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < rho / 2} ∩
      (unitNeumannCube d : Set (SpatialCoordinates d)),
      A y * ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2 with hGdef
  have hG : 0 ≤ G := by
    refine setIntegral_nonneg (hrhomeas.inter hQmeas) fun y hy => ?_
    exact mul_nonneg (hAb y hy.2).1 (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hN2' : (normalizedGradientLpNorm 2 (Metric.ball x (2 * (ell / 2)))
        (sobolevGradient (sobolevDataRestrict hSub
          (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P))))) ^ 2 ≤
      Real.exp c * G / (A x * ell ^ d) := by
    rw [hN2]
    have hpos : 0 < 2 ^ d * ell ^ d := by positivity
    rw [div_le_div_iff₀ hpos (by positivity)]
    have hFE' : ∫ y in (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)),
        ∑ i : Fin d, ((vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y) ^ 2
          ≤ Real.exp c / A x * 2 ^ d * G := hFE
    calc (∫ y in (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)),
          ∑ i : Fin d,
            ((vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y) ^ 2) *
          (A x * ell ^ d)
        ≤ (Real.exp c / A x * 2 ^ d * G) * (A x * ell ^ d) :=
          mul_le_mul_of_nonneg_right hFE' (by positivity)
      _ = Real.exp c * G * (2 ^ d * ell ^ d) := by field_simp
  have hNp1 : 0 ≤ normalizedGradientLpNorm (ENNReal.ofReal p1) (Metric.ball x (ell / 2))
      (sobolevGradient (sobolevDataRestrict hSub
        (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)))) := by
    unfold normalizedGradientLpNorm
    exact div_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg measureReal_nonneg _)
  have h1 : ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩
        (unitNeumannCube d : Set (SpatialCoordinates d)),
        A y * ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2 ≤
      Real.exp c * A x * ((r ^ d) ^ (1 - 2 / p1) *
        ((normalizedGradientLpNorm (ENNReal.ofReal p1) (Metric.ball x (ell / 2))
          (sobolevGradient (sobolevDataRestrict hSub
            (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P))))) ^ 2 *
          ((ell ^ d) ^ (1 / p1)) ^ 2)) := by
    refine hL1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine hH.trans (le_of_eq ?_)
    rw [hSrvol, hEp]; ring
  have hcomb := aux_rem_resolved_microscopic_neumann_combine _ G (Real.exp c) (A x) mN (W.C p1) Kf
    _ _ ((r ^ d) ^ (1 - 2 / p1)) (((ell ^ d) ^ (1 / p1)) ^ 2) (ell ^ d) ell C
    (Real.exp_pos c).le ha0 hmN (hAQ x hx).1
    (Real.rpow_nonneg (by positivity) _) (sq_nonneg _) (by positivity) hG h1 hNp1 hest hN2' hC1 hC2
  obtain ⟨hid1, hid2⟩ := aux_rem_resolved_microscopic_neumann_rpow_ident d p1 r ell hr hell
  rw [hid1, hid2] at hcomb
  refine hcomb.trans (le_of_eq ?_)
  ring

/-- **One-centre Neumann microscopic estimate**, in the exact
shape of the Neumann `r ≤ ell` conjunct of `rem_resolved_microscopic`.  The constants
`C0, c0` are chosen from `d`, `p1` and the published input `W` only, before the cutoff
scale, coefficient, source, solution and centre; every `C ≥ C0` and `0 < c ≤ c0` works. -/
theorem aux_rem_resolved_microscopic_neumann_local (d : ℕ) (W : SmallPerturbationInput d)
    (p1 : ℝ) (hp1 : 2 ≤ p1) :
    let q1 : ℝ := (d : ℝ) - 2 * (d : ℝ) / p1
    let Q := unitNeumannCube d
    let K := closure (Q : Set (SpatialCoordinates d))
    ∃ C0 c0 : ℝ, 0 < C0 ∧ 0 < c0 ∧ c0 ≤ 1 / 16 ∧
    ∀ C c : ℝ, C0 ≤ C → 0 < c → c ≤ c0 →
    (∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∀ (a : PositiveCoefficient Q) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ K, mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ K, ∀ z ∈ K, |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ Q, |f y| ≤ Kf) →
      let ell : ℝ := c * eps / (1 + DN)
      let gamma := fun (v : SobolevData Q) (x : SpatialCoordinates d) (r : ℝ) =>
        ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩
          (Q : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (v.2 i y) ^ 2
      ∀ u : meanZeroSobolevGraph Q, SolvesNeumann a f u →
        ∀ x ∈ Q, ∀ r : ℝ, 0 < r → r ≤ ell →
          gamma u x r ≤ C * (r / ell) ^ q1 * gamma u x (C * eps) +
            C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * r ^ q1) := by
  intro q1 Q K
  refine ⟨2 * W.C p1 ^ 2 * Real.exp 1 ^ 2 + W.C p1 ^ 2 * Real.exp 1 + 1,
    min (1 / 16) (W.osc p1), by positivity, lt_min (by norm_num) (W.osc_pos p1),
    min_le_left _ _, ?_⟩
  intro C c hC hc hcc eps heps heps1 a A haA DN mN MN hDN hmN hAK hlog f hf Kf hKf hfb
    ell gamma u hu x hx r hr hrell
  have hc16 : c ≤ 1 / 16 := hcc.trans (min_le_left _ _)
  have hcosc : c ≤ W.osc p1 := hcc.trans (min_le_right _ _)
  have hCw : 0 ≤ W.C p1 ^ 2 := sq_nonneg _
  have he1 : Real.exp c ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
  have hepos := Real.exp_pos c
  have hC1 : 2 * W.C p1 ^ 2 * Real.exp c ^ 2 ≤ C := by
    have h1 : Real.exp c ^ 2 ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ hepos.le he1 2
    have h2 : 2 * W.C p1 ^ 2 * Real.exp c ^ 2 ≤ 2 * W.C p1 ^ 2 * Real.exp 1 ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 0 ≤ W.C p1 ^ 2 * Real.exp 1 := by positivity
    linarith
  have hC2 : W.C p1 ^ 2 * Real.exp c / 2 ≤ C := by
    have h2 : W.C p1 ^ 2 * Real.exp c ≤ W.C p1 ^ 2 * Real.exp 1 :=
      mul_le_mul_of_nonneg_left he1 hCw
    have h3 : 0 ≤ 2 * W.C p1 ^ 2 * Real.exp 1 ^ 2 := by positivity
    have h4 : 0 ≤ W.C p1 ^ 2 * Real.exp c := by positivity
    linarith
  have hCone : 1 ≤ C := by
    have : 0 ≤ 2 * W.C p1 ^ 2 * Real.exp 1 ^ 2 + W.C p1 ^ 2 * Real.exp 1 := by positivity
    linarith
  have h1DN : 0 < 1 + DN := by linarith
  have hce : 0 < c * eps := mul_pos hc heps
  have hell : 0 < ell := div_pos hce h1DN
  have hell_le : ell ≤ c * eps := div_le_self hce.le (by linarith)
  have hceps : c * eps ≤ eps / 16 := by nlinarith
  have hell14 : ell ≤ 1 / 4 := by linarith
  have hδ : DN / eps * ell ≤ c := by
    change DN / eps * (c * eps / (1 + DN)) ≤ c
    rw [div_mul_div_comm, div_le_iff₀ (mul_pos heps h1DN)]
    nlinarith
  have hmodQ : ∀ y ∈ (Q : Set (SpatialCoordinates d)), dist y x ≤ ell →
      |Real.log (A y) - Real.log (A x)| ≤ c := fun y hy hd =>
    (hlog y (subset_closure hy) x (subset_closure hx)).trans
      ((mul_le_mul_of_nonneg_left hd (div_nonneg hDN heps.le)).trans hδ)
  have hAQ : ∀ y ∈ (Q : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN :=
    fun y hy => hAK y (subset_closure hy)
  have hdist : ∀ y : SpatialCoordinates d, dist y x < ell → ∀ j, |y j - x j| < ell := by
    intro y h j
    have := (dist_pi_lt_iff hell).1 h j
    rwa [Real.dist_eq] at this
  have hrho : 6 * ell ≤ C * eps := by nlinarith
  exact aux_rem_resolved_microscopic_neumann_core W p1 hp1
    (aux_rem_resolved_microscopic_neumann_faces x ell)
    (aux_rem_resolved_microscopic_neumann_upper x) C c hcosc hC1 hC2 a A A.continuous haA
    mN MN hmN hAQ f hf Kf hKf hfb u hu x hx ell hell hmodQ
    (fun y hy => aux_rem_resolved_microscopic_neumann_ball_sub_folded hx hell14 (hdist y hy))
    (aux_rem_resolved_microscopic_neumann_box x ell)
    (aux_rem_resolved_microscopic_neumann_box_measurable x ell)
    (aux_rem_resolved_microscopic_neumann_box_sub_folded hx hell14)
    (fun J hJ => aux_rem_resolved_microscopic_neumann_box_symm x ell J hJ)
    (fun y hy => aux_rem_resolved_microscopic_neumann_ball_sub_box hx hell14 (hdist y hy))
    (C * eps) (aux_rem_resolved_microscopic_neumann_box_sub_cube hx hell14 hrho) r hr hrell




/-- The local energy is monotone in the side of the observation cube. -/
theorem aux_rem_resolved_microscopic_neumann_gamma_mono {d : ℕ}
    (A : SpatialCoordinates d → ℝ) (hAc : Continuous A) (MN : ℝ)
    (hAb : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), 0 ≤ A y ∧ A y ≤ MN)
    (w : SobolevData (unitNeumannCube d)) (x : SpatialCoordinates d) {r1 r2 : ℝ}
    (h : r1 ≤ r2) :
    ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r1 / 2} ∩
        (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (w.2 i y) ^ 2 ≤
      ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r2 / 2} ∩
        (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (w.2 i y) ^ 2 := by
  have hQmeas : MeasurableSet (unitNeumannCube d : Set (SpatialCoordinates d)) :=
    (unitNeumannCube d).isOpen.measurableSet
  have hint : Integrable (fun y => A y * ∑ i : Fin d, (w.2 i y) ^ 2)
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun i _ =>
      aux_rem_resolved_microscopic_neumann_tie_sq_integrable (Ω := unitNeumannCube d) A hAc MN
        (fun y hy => by rw [abs_of_nonneg (hAb y hy).1]; exact (hAb y hy).2) (w.2 i)
  refine setIntegral_mono_set
    (hint.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)) ?_ ?_
  · filter_upwards [ae_restrict_mem
      ((aux_rem_resolved_microscopic_neumann_cube_measurable x (r2 / 2)).inter hQmeas)] with y hy
    exact mul_nonneg (hAb y hy.2).1 (Finset.sum_nonneg fun i _ => sq_nonneg _)
  · refine Filter.Eventually.of_forall (Set.inter_subset_inter_left _ ?_)
    intro y hy i
    exact lt_of_lt_of_le (hy i) (by linarith)



theorem aux_rem_resolved_microscopic_neumann_macro
    (d : ℕ) (p1 t t1 c eps DN r Kmac : ℝ)
    (htq : t < (d : ℝ) - 2 * (d : ℝ) / p1)
    (hc : 0 < c) (heps : 0 < eps) (hDN : 0 ≤ DN) (hKmac : 0 ≤ Kmac) (hr : 0 < r)
    (hrle : r ≤ c * eps / (1 + DN)) :
    (r / (c * eps / (1 + DN))) ^ ((d : ℝ) - 2 * (d : ℝ) / p1) * (Kmac * eps ^ t1) ≤
      c ^ (-t) * (1 + DN) ^ t * eps ^ (t1 - t) * Kmac * r ^ t := by
  have h1 : 0 < 1 + DN := by linarith
  have hell : 0 < c * eps / (1 + DN) := div_pos (mul_pos hc heps) h1
  have hratio : 0 < r / (c * eps / (1 + DN)) := div_pos hr hell
  have hratio1 : r / (c * eps / (1 + DN)) ≤ 1 := (div_le_one hell).2 hrle
  have hpow : (r / (c * eps / (1 + DN))) ^ ((d : ℝ) - 2 * (d : ℝ) / p1) ≤
      (r / (c * eps / (1 + DN))) ^ t :=
    Real.rpow_le_rpow_of_exponent_ge hratio hratio1 htq.le
  have hid : (r / (c * eps / (1 + DN))) ^ t = c ^ (-t) * (1 + DN) ^ t * r ^ t * eps ^ (-t) := by
    rw [Real.div_rpow hr.le hell.le, Real.div_rpow (mul_pos hc heps).le h1.le,
      Real.mul_rpow hc.le heps.le, Real.rpow_neg hc.le, Real.rpow_neg heps.le]
    field_simp
  have hnn : 0 ≤ Kmac * eps ^ t1 := mul_nonneg hKmac (Real.rpow_nonneg heps.le _)
  calc _ ≤ (r / (c * eps / (1 + DN))) ^ t * (Kmac * eps ^ t1) :=
        mul_le_mul_of_nonneg_right hpow hnn
    _ = c ^ (-t) * (1 + DN) ^ t * Kmac * r ^ t * (eps ^ (-t) * eps ^ t1) := by rw [hid]; ring
    _ = c ^ (-t) * (1 + DN) ^ t * eps ^ (t1 - t) * Kmac * r ^ t := by
        rw [← Real.rpow_add heps, show -t + t1 = t1 - t by ring]; ring

/-- The datum term below `ell` is at most `eps^(d+2-t) r^t`. -/
theorem aux_rem_resolved_microscopic_neumann_datum
    (d : ℕ) (p1 t ell eps r : ℝ) (htq : t < (d : ℝ) - 2 * (d : ℝ) / p1)
    (htd : t < (d : ℝ) + 2) (hell : 0 < ell) (helleps : ell ≤ eps) (hr : 0 < r)
    (hrell : r ≤ ell) :
    ell ^ (2 + 2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) ≤
      eps ^ ((d : ℝ) + 2 - t) * r ^ t := by
  have hsplit : r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) =
      r ^ ((d : ℝ) - 2 * (d : ℝ) / p1 - t) * r ^ t := by
    rw [← Real.rpow_add hr]; congr 1; ring
  have hle : r ^ ((d : ℝ) - 2 * (d : ℝ) / p1 - t) ≤ ell ^ ((d : ℝ) - 2 * (d : ℝ) / p1 - t) :=
    Real.rpow_le_rpow hr.le hrell (by linarith)
  have hcomb : ell ^ (2 + 2 * (d : ℝ) / p1) * ell ^ ((d : ℝ) - 2 * (d : ℝ) / p1 - t) =
      ell ^ ((d : ℝ) + 2 - t) := by
    rw [← Real.rpow_add hell]; congr 1; ring
  have hmono : ell ^ ((d : ℝ) + 2 - t) ≤ eps ^ ((d : ℝ) + 2 - t) :=
    Real.rpow_le_rpow hell.le helleps (by linarith)
  rw [hsplit]
  calc ell ^ (2 + 2 * (d : ℝ) / p1) * (r ^ ((d : ℝ) - 2 * (d : ℝ) / p1 - t) * r ^ t)
      ≤ ell ^ (2 + 2 * (d : ℝ) / p1) * (ell ^ ((d : ℝ) - 2 * (d : ℝ) / p1 - t) * r ^ t) := by
        gcongr
    _ = ell ^ ((d : ℝ) + 2 - t) * r ^ t := by rw [← hcomb]; ring
    _ ≤ eps ^ ((d : ℝ) + 2 - t) * r ^ t := by gcongr

/-- Real algebra of the matched estimate below `ell`. -/
theorem aux_rem_resolved_microscopic_neumann_matched_small
    (Gr G0 M Q' E R mNi Kf2 Kmac et1 ct DNt ett rt epsd C : ℝ)
    (h0 : Gr ≤ M * Q' * G0 + M * mNi * Kf2 * E * R)
    (hG : G0 ≤ Kmac * et1)
    (hmacro : Q' * (Kmac * et1) ≤ ct * DNt * ett * Kmac * rt)
    (hdat : E * R ≤ epsd * rt)
    (hM : 0 ≤ M) (hQ : 0 ≤ Q') (hmK : 0 ≤ mNi * Kf2) (hct : 1 ≤ ct) (hrt : 0 ≤ rt)
    (hX : 0 ≤ DNt * ett * Kmac) (hepsd : 0 ≤ epsd) (hC : M * ct ≤ C) :
    Gr ≤ C * (DNt * ett * Kmac + mNi * Kf2 * epsd) * rt := by
  have k1 : M * Q' * G0 ≤ M * (ct * DNt * ett * Kmac * rt) := by
    have := mul_le_mul_of_nonneg_left hG (mul_nonneg hM hQ)
    have h2 := mul_le_mul_of_nonneg_left hmacro hM
    calc M * Q' * G0 ≤ M * Q' * (Kmac * et1) := this
      _ = M * (Q' * (Kmac * et1)) := by ring
      _ ≤ _ := h2
  have k2 : M * mNi * Kf2 * E * R ≤ M * (mNi * Kf2) * (epsd * rt) := by
    have := mul_le_mul_of_nonneg_left hdat (mul_nonneg hM hmK)
    calc M * mNi * Kf2 * E * R = M * (mNi * Kf2) * (E * R) := by ring
      _ ≤ _ := this
  have k3 : M * (mNi * Kf2) * (epsd * rt) ≤ ct * (M * (mNi * Kf2) * (epsd * rt)) :=
    le_mul_of_one_le_left (by positivity) hct
  have hct0 : 0 ≤ ct := by linarith
  have k4 : M * ct * ((DNt * ett * Kmac + mNi * Kf2 * epsd) * rt) ≤
      C * ((DNt * ett * Kmac + mNi * Kf2 * epsd) * rt) :=
    mul_le_mul_of_nonneg_right hC (by positivity)
  have k5 : M * ct * ((DNt * ett * Kmac + mNi * Kf2 * epsd) * rt) =
      M * (ct * DNt * ett * Kmac * rt) + ct * (M * (mNi * Kf2) * (epsd * rt)) := by ring
  have k6 : C * ((DNt * ett * Kmac + mNi * Kf2 * epsd) * rt) =
      C * (DNt * ett * Kmac + mNi * Kf2 * epsd) * rt := by ring
  linarith

/-- Real algebra of the matched estimate between `ell` and `eps`. -/
theorem aux_rem_resolved_microscopic_neumann_matched_large
    (Gr Kmac ett et ct DNt rt Y M C : ℝ)
    (hG : Gr ≤ Kmac * (ett * et)) (het : et ≤ ct * DNt * rt)
    (hK : 0 ≤ Kmac) (hett : 0 ≤ ett) (hct : 0 ≤ ct) (hDNt : 0 ≤ DNt) (hrt : 0 ≤ rt)
    (hY : 0 ≤ Y) (hM : 1 ≤ M) (hC : M * ct ≤ C) :
    Gr ≤ C * (DNt * ett * Kmac + Y) * rt := by
  have k1 : Kmac * (ett * et) ≤ Kmac * (ett * (ct * DNt * rt)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left het hett) hK
  have k2 : Kmac * (ett * (ct * DNt * rt)) ≤ ct * ((DNt * ett * Kmac + Y) * rt) := by
    have : Kmac * (ett * (ct * DNt * rt)) = ct * ((DNt * ett * Kmac) * rt) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by linarith) hrt) hct
  have hW : 0 ≤ (DNt * ett * Kmac + Y) * rt := by positivity
  have k3 : ct * ((DNt * ett * Kmac + Y) * rt) ≤ M * ct * ((DNt * ett * Kmac + Y) * rt) := by
    rw [mul_assoc M]
    exact le_mul_of_one_le_left (mul_nonneg hct hW) hM
  have k4 : M * ct * ((DNt * ett * Kmac + Y) * rt) ≤ C * ((DNt * ett * Kmac + Y) * rt) :=
    mul_le_mul_of_nonneg_right hC hW
  have k5 : C * ((DNt * ett * Kmac + Y) * rt) = C * (DNt * ett * Kmac + Y) * rt := by ring
  linarith

/-- **The Neumann solution conjunct of `rem_resolved_microscopic`** : for every mean-zero weak Neumann solution, the one-centre estimate below
`ell` and the matched estimate for all `r ≤ eps`.  The constants are chosen from
`d, p1, t` and the published input `W` only; the principal may take any `c ≤ c0` and any
`C ≥ C0 c^{-t}`. -/
theorem aux_rem_resolved_microscopic_neumann_solution (d : ℕ) (hd : 2 ≤ d)
    (W : SmallPerturbationInput d)
    (p1 t t1 : ℝ) (hp1 : 2 ≤ p1) (ht : (d : ℝ) - 1 < t)
    (htt1 : t < t1) (ht1d : t1 < (d : ℝ))
    (htp : t < (d : ℝ) - 2 * (d : ℝ) / p1) :
    let q1 : ℝ := (d : ℝ) - 2 * (d : ℝ) / p1
    let Q := unitNeumannCube d
    let K := closure (Q : Set (SpatialCoordinates d))
    ∃ C0 c0 : ℝ, 1 ≤ C0 ∧ 0 < c0 ∧ c0 ≤ 1 / 16 ∧
    ∀ C c : ℝ, 0 < c → c ≤ c0 → C0 * c ^ (-t) ≤ C →
    (∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∀ (a : PositiveCoefficient Q) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ K, mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ K, ∀ z ∈ K, |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ Q, |f y| ≤ Kf) →
      let ell : ℝ := c * eps / (1 + DN)
      let gamma := fun (v : SobolevData Q) (x : SpatialCoordinates d) (r : ℝ) =>
        ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩
          (Q : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (v.2 i y) ^ 2
      (∀ u : meanZeroSobolevGraph Q, SolvesNeumann a f u →
        (∀ x ∈ Q, ∀ r : ℝ, 0 < r → r ≤ ell →
          gamma u x r ≤ C * (r / ell) ^ q1 * gamma u x (C * eps) +
            C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * r ^ q1) ∧
        (∀ Kmac : ℝ, 0 ≤ Kmac → ∀ x ∈ Q,
          gamma u x (C * eps) ≤ Kmac * eps ^ t1 →
          ∀ r : ℝ, 0 < r → r ≤ eps →
          gamma u x r ≤ C * ((1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
            mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t)) * r ^ t))) := by
  intro q1 Q K
  obtain ⟨C0, c0, _hC0, hc0, hc016, hloc⟩ := aux_rem_resolved_microscopic_neumann_local d W p1 hp1
  refine ⟨max C0 1, c0, le_max_right _ _, hc0, hc016, ?_⟩
  intro C c hc hcc hC eps heps heps1 a A haA DN mN MN hDN hmN hAK hlog f hf Kf hKf hfb ell gamma
    u hu
  have hd1 : (1 : ℝ) ≤ d - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have htpos : 0 < t := by linarith
  have hc1 : c ≤ 1 := by linarith [hcc.trans hc016]
  have hct : 1 ≤ c ^ (-t) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc hc1 (by linarith)
  have hC0' : 0 < max C0 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCge : max C0 1 ≤ C := le_trans (le_mul_of_one_le_right hC0'.le hct) hC
  have hCone : 1 ≤ C := (le_max_right C0 1).trans hCge
  have hA : ∀ C' : ℝ, max C0 1 ≤ C' → ∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ r : ℝ, 0 < r →
      r ≤ ell → gamma u x r ≤ C' * (r / ell) ^ q1 * gamma u x (C' * eps) +
        C' * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * r ^ q1 := fun C' hC' =>
    hloc C' c ((le_max_left _ _).trans hC') hc hcc eps heps heps1 a A haA DN mN MN hDN hmN hAK
      hlog f hf Kf hKf hfb u hu
  refine ⟨hA C hCge, ?_⟩
  intro Kmac hKmac x hx hmac r hr hreps
  have hAQ : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), 0 ≤ A y ∧ A y ≤ MN :=
    fun y hy => ⟨hmN.le.trans (hAK y (subset_closure hy)).1, (hAK y (subset_closure hy)).2⟩
  have hmono : ∀ r1 r2 : ℝ, r1 ≤ r2 → gamma u x r1 ≤ gamma u x r2 := fun r1 r2 h =>
    aux_rem_resolved_microscopic_neumann_gamma_mono A A.continuous MN hAQ
      (u : SobolevData (unitNeumannCube d)) x h
  have hGmac : gamma u x (max C0 1 * eps) ≤ Kmac * eps ^ t1 :=
    (hmono _ _ (mul_le_mul_of_nonneg_right hCge heps.le)).trans hmac
  have hGr : ell < r → gamma u x r ≤ Kmac * eps ^ t1 := fun _ =>
    (hmono _ _ (hreps.trans (le_mul_of_one_le_left heps.le hCone))).trans hmac
  have hA0 := hA (max C0 1) le_rfl x hx r hr
  clear_value gamma
  clear hA hmono hloc
  have h1DN : 0 < 1 + DN := by linarith
  have hell : 0 < ell := div_pos (mul_pos hc heps) h1DN
  have hbr : 0 ≤ (1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
      mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t) := by positivity
  have hrt : 0 < r ^ t := Real.rpow_pos_of_pos hr t
  by_cases hrell : r ≤ ell
  · have hmacro := aux_rem_resolved_microscopic_neumann_macro d p1 t t1 c eps DN r Kmac htp
      hc heps hDN hKmac hr hrell
    have helleps : ell ≤ eps := by
      have h1 : ell ≤ c * eps := div_le_self (mul_pos hc heps).le (by linarith)
      have h2 : c * eps ≤ eps := by nlinarith
      linarith
    have hdat := aux_rem_resolved_microscopic_neumann_datum d p1 t ell eps r htp (by linarith)
      hell helleps hr hrell
    exact aux_rem_resolved_microscopic_neumann_matched_small _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C
      (hA0 hrell) hGmac hmacro hdat hC0'.le (Real.rpow_nonneg (div_nonneg hr.le hell.le) _)
      (by positivity) hct hrt.le (by positivity) (by positivity) hC
  · push Not at hrell
    have heps_le : eps ≤ c⁻¹ * (1 + DN) * r := by
      have : c * eps < r * (1 + DN) := (div_lt_iff₀ h1DN).1 hrell
      rw [inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hc]
      linarith
    have hepst : eps ^ t ≤ c ^ (-t) * (1 + DN) ^ t * r ^ t := by
      calc eps ^ t ≤ (c⁻¹ * (1 + DN) * r) ^ t := Real.rpow_le_rpow heps.le heps_le htpos.le
        _ = c ^ (-t) * (1 + DN) ^ t * r ^ t := by
          rw [Real.mul_rpow (by positivity) hr.le, Real.mul_rpow (by positivity) h1DN.le,
            Real.inv_rpow hc.le, Real.rpow_neg hc.le]
    have hsplit : eps ^ t1 = eps ^ (t1 - t) * eps ^ t := by
      rw [← Real.rpow_add heps]; congr 1; ring
    have hG := hGr hrell
    rw [hsplit] at hG
    exact aux_rem_resolved_microscopic_neumann_matched_large _ _ _ _ _ _ _ _ _ C hG hepst hKmac
      (Real.rpow_nonneg heps.le _) (by positivity) (by positivity) hrt.le (by positivity)
      (le_max_right _ _) hC


end NeumannHelpers

section DirichletFluxHelpers
open scoped ContDiff Distributions

/-- One-sided elementary bound `x - y ≤ x (log x - log y)` for `0 < y ≤ x`. -/
theorem aux_rem_resolved_microscopic_sub_le_mul_log_sub
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x - y ≤ x * (Real.log x - Real.log y) := by
  have hlog : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at hlog
  have h2 : x * (Real.log y - Real.log x) ≤ y - x := by
    calc _ ≤ x * (y / x - 1) := mul_le_mul_of_nonneg_left hlog hx.le
      _ = y - x := by field_simp
  nlinarith

/-- `|x - y| ≤ M |log x - log y|` on `(0, M]`. -/
theorem aux_rem_resolved_microscopic_abs_sub_le_log
    {x y M : ℝ} (hx : 0 < x) (hy : 0 < y) (hxM : x ≤ M) (hyM : y ≤ M) :
    |x - y| ≤ M * |Real.log x - Real.log y| := by
  rcases le_total y x with hxy | hxy
  · have hl : 0 ≤ Real.log x - Real.log y := sub_nonneg.mpr (Real.log_le_log hy hxy)
    rw [abs_of_nonneg (sub_nonneg.mpr hxy), abs_of_nonneg hl]
    exact (aux_rem_resolved_microscopic_sub_le_mul_log_sub hx hy).trans
      (mul_le_mul_of_nonneg_right hxM hl)
  · have hl : 0 ≤ Real.log y - Real.log x := sub_nonneg.mpr (Real.log_le_log hx hxy)
    rw [abs_sub_comm x y, abs_sub_comm (Real.log x) (Real.log y),
      abs_of_nonneg (sub_nonneg.mpr hxy), abs_of_nonneg hl]
    exact (aux_rem_resolved_microscopic_sub_le_mul_log_sub hy hx).trans
      (mul_le_mul_of_nonneg_right hyM hl)

/-- The logarithmic modulus and the two-sided bounds make `A` Lipschitz on `K`. -/
theorem aux_rem_resolved_microscopic_coeff_lipschitzOn
    {d : ℕ} (A : SpatialCoordinates d → ℝ) (K : Set (SpatialCoordinates d))
    (mN MN DN eps : ℝ) (hmN : 0 < mN) (hMN : 0 ≤ MN)
    (hbd : ∀ y ∈ K, mN ≤ A y ∧ A y ≤ MN)
    (hlog : ∀ y ∈ K, ∀ z ∈ K, |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) :
    LipschitzOnWith (Real.toNNReal (MN * (DN / eps))) A K := by
  apply LipschitzOnWith.of_dist_le'
  intro y hy z hz
  rw [Real.dist_eq]
  calc |A y - A z| ≤ MN * |Real.log (A y) - Real.log (A z)| :=
        aux_rem_resolved_microscopic_abs_sub_le_log (hmN.trans_le (hbd y hy).1)
          (hmN.trans_le (hbd z hz).1) (hbd y hy).2 (hbd z hz).2
    _ ≤ MN * (DN / eps * dist y z) := mul_le_mul_of_nonneg_left (hlog y hy z hz) hMN
    _ = MN * (DN / eps) * dist y z := by ring

/-- The divergence of the datum flux, `∑ᵢ (∂ᵢÃ ∂ᵢh + Ã ∂ᵢ²h)`, with the line
derivative (zero where it does not exist) of the Lipschitz coefficient. -/
def aux_remResolvedMicroscopicFluxDiv {d : ℕ} (At h : SpatialCoordinates d → ℝ)
    (x : SpatialCoordinates d) : ℝ :=
  ∑ i : Fin d, (lineDeriv ℝ At x (Pi.single i 1) * fderiv ℝ h x (Pi.single i 1) +
    At x * fderiv ℝ (fderiv ℝ h) x (Pi.single i 1) (Pi.single i 1))

theorem aux_rem_resolved_microscopic_fluxDiv_measurable {d : ℕ}
    (At h : SpatialCoordinates d → ℝ) (hAt : Continuous At) (hh : ContDiff ℝ 2 h) :
    Measurable (aux_remResolvedMicroscopicFluxDiv At h) := by
  unfold aux_remResolvedMicroscopicFluxDiv
  apply Finset.measurable_sum
  intro i _
  have h1 : Continuous (fun x => fderiv ℝ h x (Pi.single i 1)) :=
    (hh.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h2 : Continuous (fun x => fderiv ℝ (fderiv ℝ h) x (Pi.single i 1) (Pi.single i 1)) := by
    have hc : Continuous (fderiv ℝ (fderiv ℝ h)) := by
      have : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (m := 1) (by norm_num)
      exact this.continuous_fderiv (by norm_num)
    exact (hc.clm_apply continuous_const).clm_apply continuous_const
  exact ((measurable_lineDeriv hAt).mul h1.measurable).add
    (hAt.measurable.mul h2.measurable)

/-- Pointwise flux bound at a point where the coefficient and the derivatives of `h`
are controlled. -/
theorem aux_rem_resolved_microscopic_fluxDiv_bound {d : ℕ}
    (At h : SpatialCoordinates d → ℝ) {L : ℝ≥0} (hAt : LipschitzWith L At)
    (x : SpatialCoordinates d) (MN Kg Kh2 : ℝ)
    (hA : |At x| ≤ MN) (hg : ‖fderiv ℝ h x‖ ≤ Kg)
    (hh2 : ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ Kh2) :
    |aux_remResolvedMicroscopicFluxDiv At h x| ≤ (d : ℝ) * ((L : ℝ) * Kg + MN * Kh2) := by
  unfold aux_remResolvedMicroscopicFluxDiv
  have hsingle : ∀ i : Fin d, ‖(Pi.single i (1 : ℝ) : SpatialCoordinates d)‖ ≤ 1 := by
    intro i
    rw [Pi.norm_single]; simp
  have hterm : ∀ i : Fin d,
      |lineDeriv ℝ At x (Pi.single i 1) * fderiv ℝ h x (Pi.single i 1) +
        At x * fderiv ℝ (fderiv ℝ h) x (Pi.single i 1) (Pi.single i 1)| ≤
        (L : ℝ) * Kg + MN * Kh2 := by
    intro i
    set v : SpatialCoordinates d := Pi.single i 1
    have hl : |lineDeriv ℝ At x v| ≤ (L : ℝ) := by
      have := norm_lineDeriv_le_of_lipschitz ℝ (x₀ := x) (v := v) hAt
      rw [Real.norm_eq_abs] at this
      exact this.trans (by
        have := hsingle i
        nlinarith [L.coe_nonneg, norm_nonneg v])
    have hd1 : |fderiv ℝ h x v| ≤ Kg := by
      have := (fderiv ℝ h x).le_opNorm v
      rw [Real.norm_eq_abs] at this
      exact this.trans (by nlinarith [hsingle i, norm_nonneg (fderiv ℝ h x), norm_nonneg v])
    have hd2 : |fderiv ℝ (fderiv ℝ h) x v v| ≤ Kh2 := by
      have h1 := (fderiv ℝ (fderiv ℝ h) x v).le_opNorm v
      have h2 := (fderiv ℝ (fderiv ℝ h) x).le_opNorm v
      rw [Real.norm_eq_abs] at h1
      have hv := hsingle i
      have hn := norm_nonneg v
      have hB := norm_nonneg (fderiv ℝ (fderiv ℝ h) x v)
      have hB2 := norm_nonneg (fderiv ℝ (fderiv ℝ h) x)
      calc |fderiv ℝ (fderiv ℝ h) x v v| ≤ ‖fderiv ℝ (fderiv ℝ h) x v‖ * ‖v‖ := h1
        _ ≤ ‖fderiv ℝ (fderiv ℝ h) x v‖ := by nlinarith
        _ ≤ ‖fderiv ℝ (fderiv ℝ h) x‖ * ‖v‖ := h2
        _ ≤ ‖fderiv ℝ (fderiv ℝ h) x‖ := by nlinarith
        _ ≤ Kh2 := hh2
    calc _ ≤ |lineDeriv ℝ At x v * fderiv ℝ h x v| +
          |At x * fderiv ℝ (fderiv ℝ h) x v v| := abs_add_le _ _
      _ = |lineDeriv ℝ At x v| * |fderiv ℝ h x v| +
          |At x| * |fderiv ℝ (fderiv ℝ h) x v v| := by rw [abs_mul, abs_mul]
      _ ≤ (L : ℝ) * Kg + MN * Kh2 := by
          gcongr
          · exact (abs_nonneg _).trans hA
  calc _ ≤ ∑ i : Fin d,
        |lineDeriv ℝ At x (Pi.single i 1) * fderiv ℝ h x (Pi.single i 1) +
          At x * fderiv ℝ (fderiv ℝ h) x (Pi.single i 1) (Pi.single i 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ((L : ℝ) * Kg + MN * Kh2) := Finset.sum_le_sum fun i _ => hterm i
    _ = (d : ℝ) * ((L : ℝ) * Kg + MN * Kh2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- One coordinate of the datum-flux integration by parts against a test. -/
theorem aux_rem_resolved_microscopic_flux_ibp_coord {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)}
    (At : SpatialCoordinates d → ℝ) {L : ℝ≥0} (hAt : LipschitzWith L At)
    (h : SpatialCoordinates d → ℝ) (hh : ContDiff ℝ 2 h)
    (φ : 𝓓(Ω, ℝ)) (i : Fin d) :
    ∫ x, At x * (fderiv ℝ h x (Pi.single i 1) * fderiv ℝ φ x (Pi.single i 1)) =
      -∫ x, (lineDeriv ℝ At x (Pi.single i 1) * fderiv ℝ h x (Pi.single i 1) +
        At x * fderiv ℝ (fderiv ℝ h) x (Pi.single i 1) (Pi.single i 1)) * φ x := by
  set v : SpatialCoordinates d := Pi.single i 1
  have hφ1 : ContDiff ℝ 1 (φ : SpatialCoordinates d → ℝ) := φ.contDiff.of_le (by simp)
  have hh1 : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (m := 1) (by norm_num)
  set hi : SpatialCoordinates d → ℝ := fun x => fderiv ℝ h x v with hhi
  have hhi1 : ContDiff ℝ 1 hi := hh1.clm_apply contDiff_const
  set g : SpatialCoordinates d → ℝ := fun x => hi x * φ x with hg
  have hg1 : ContDiff ℝ 1 g := hhi1.mul hφ1
  have hgc : HasCompactSupport g := φ.hasCompactSupport.mul_left
  obtain ⟨Cg, hgLip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg1 (by norm_num)
  have hibp := hAt.integral_lineDeriv_mul_eq (μ := (volume : Measure (SpatialCoordinates d)))
    hgLip hgc v
  -- the line derivative of the C¹ product
  have hhid : ∀ x, fderiv ℝ hi x v = fderiv ℝ (fderiv ℝ h) x v v := by
    intro x
    have hc : DifferentiableAt ℝ (fderiv ℝ h) x := hh1.differentiable (by norm_num) x
    have := fderiv_clm_apply (u := fun _ : SpatialCoordinates d => v) hc
      (differentiableAt_const v)
    simp only [hhi]
    rw [this]
    simp
  have hgd : ∀ x, lineDeriv ℝ g x (-v) =
      -(fderiv ℝ (fderiv ℝ h) x v v * φ x + hi x * fderiv ℝ φ x v) := by
    intro x
    rw [(hg1.differentiable (by norm_num) x).lineDeriv_eq_fderiv, map_neg]
    congr 1
    have hmul : fderiv ℝ g x = hi x • fderiv ℝ φ x + φ x • fderiv ℝ hi x := by
      have := fderiv_mul (hhi1.differentiable (by norm_num) x) (hφ1.differentiable (by norm_num) x)
      exact this
    rw [hmul]
    simp only [add_apply, smul_apply, smul_eq_mul, hhid]
    ring
  -- integrability
  have hφc : Continuous (φ : SpatialCoordinates d → ℝ) := φ.contDiff.continuous
  have hdφc : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdφs : HasCompactSupport (fun x => fderiv ℝ φ x v) :=
    φ.hasCompactSupport.fderiv_apply ℝ v
  have hh2c : Continuous (fun x => fderiv ℝ (fderiv ℝ h) x v v) :=
    ((hh1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  have hAtc : Continuous At := hAt.continuous
  have hgint : Integrable g := hg1.continuous.integrable_of_hasCompactSupport hgc
  have hI1 : Integrable (fun x => lineDeriv ℝ At x v * g x) :=
    hgint.bdd_mul (c := (L : ℝ) * ‖v‖) (measurable_lineDeriv hAtc).aestronglyMeasurable
      (Eventually.of_forall fun x => norm_lineDeriv_le_of_lipschitz ℝ hAt)
  have hI2 : Integrable (fun x => At x * fderiv ℝ (fderiv ℝ h) x v v * φ x) :=
    ((hAtc.mul hh2c).mul hφc).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  have hI3 : Integrable (fun x => -(fderiv ℝ (fderiv ℝ h) x v v * φ x +
      hi x * fderiv ℝ φ x v) * At x) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (((hh2c.mul hφc).add (hhi1.continuous.mul hdφc)).neg).mul hAtc
    · apply HasCompactSupport.mul_right
      apply HasCompactSupport.neg
      exact (φ.hasCompactSupport.mul_left).add (hdφs.mul_left)
  have hibp' : ∫ x, lineDeriv ℝ At x v * g x =
      ∫ x, -(fderiv ℝ (fderiv ℝ h) x v v * φ x + hi x * fderiv ℝ φ x v) * At x := by
    rw [hibp]
    congr 1
    funext x
    rw [hgd x]
  have key : ∫ x, (lineDeriv ℝ At x v * fderiv ℝ h x v +
        At x * fderiv ℝ (fderiv ℝ h) x v v) * φ x =
      -∫ x, At x * (fderiv ℝ h x v * fderiv ℝ φ x v) := by
    calc ∫ x, (lineDeriv ℝ At x v * fderiv ℝ h x v +
          At x * fderiv ℝ (fderiv ℝ h) x v v) * φ x
        = ∫ x, (lineDeriv ℝ At x v * g x + At x * fderiv ℝ (fderiv ℝ h) x v v * φ x) := by
          congr 1; funext x; simp only [hhi, hg]; ring
      _ = (∫ x, lineDeriv ℝ At x v * g x) +
          ∫ x, At x * fderiv ℝ (fderiv ℝ h) x v v * φ x := integral_add hI1 hI2
      _ = (∫ x, -(fderiv ℝ (fderiv ℝ h) x v v * φ x + hi x * fderiv ℝ φ x v) * At x) +
          ∫ x, At x * fderiv ℝ (fderiv ℝ h) x v v * φ x := by rw [hibp']
      _ = ∫ x, (-(fderiv ℝ (fderiv ℝ h) x v v * φ x + hi x * fderiv ℝ φ x v) * At x +
          At x * fderiv ℝ (fderiv ℝ h) x v v * φ x) := (integral_add hI3 hI2).symm
      _ = ∫ x, -(At x * (fderiv ℝ h x v * fderiv ℝ φ x v)) := by
          congr 1; funext x; simp only [hhi]; ring
      _ = -∫ x, At x * (fderiv ℝ h x v * fderiv ℝ φ x v) := integral_neg _
  rw [key, neg_neg]

/-- A `C²` datum tied a.e. to a weak-graph element: the weak gradient is the classical
gradient.  Uses only the weak-graph identity and uniqueness of weak gradients. -/
theorem aux_rem_resolved_microscopic_datum_gradient {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K) (hΩK : (Ω : Set _) ⊆ K)
    (h : SpatialCoordinates d → ℝ) (hh : ContDiff ℝ 2 h)
    (hdata : SobolevData Ω) (hmem : hdata ∈ weakSobolevGraph Ω)
    (hae : (hdata.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] h) (i : Fin d) :
    (hdata.2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => fderiv ℝ h x (Pi.single i 1) := by
  have hcont : ∀ j : Fin d, Continuous (fun x => fderiv ℝ h x (Pi.single j 1)) := fun j =>
    (hh.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hLp : ∀ j : Fin d, MemLp (fun x => fderiv ℝ h x (Pi.single j 1)) 2
      (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
    intro j
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hcont j).continuousOn
    refine MemLp.of_bound (hcont j).aestronglyMeasurable B ?_
    exact (ae_restrict_iff' Ω.isOpen.measurableSet).mpr
      (Eventually.of_forall fun x hx => hB x (hΩK hx))
  let gh : Fin d → DomainL2 Ω := fun j => (hLp j).toLp _
  have hmem2 : (hdata.1, gh) ∈ weakSobolevGraph Ω := by
    rw [mem_weakSobolevGraph_iff]
    intro φ j
    set v : SpatialCoordinates d := Pi.single j 1
    have hφ1 : ContDiff ℝ 1 (φ : SpatialCoordinates d → ℝ) := φ.contDiff.of_le (by simp)
    have hφc : Continuous (φ : SpatialCoordinates d → ℝ) := φ.contDiff.continuous
    have hdφc : Continuous (fun x => fderiv ℝ φ x v) :=
      (hφ1.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hdφs : HasCompactSupport (fun x => fderiv ℝ φ x v) :=
      φ.hasCompactSupport.fderiv_apply ℝ v
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure (SpatialCoordinates d))) (v := v)
      (f := (φ : SpatialCoordinates d → ℝ)) (g := h)
      ((hdφc.mul hh.continuous).integrable_of_hasCompactSupport hdφs.mul_right)
      ((hφc.mul (hcont j)).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right)
      ((hφc.mul hh.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right)
      (fun x _ => hφ1.differentiable (by norm_num) x)
      (fun x _ => hh.differentiable (by norm_num) x)
    have hleft : (∫ x in (Ω : Set (SpatialCoordinates d)), φ x * (gh j) x) =
        ∫ x, φ x * fderiv ℝ h x v := by
      calc
        _ = ∫ x in (Ω : Set (SpatialCoordinates d)), φ x * fderiv ℝ h x v := by
          apply integral_congr_ae
          filter_upwards [(hLp j).coeFn_toLp] with x hx
          rw [hx]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport
            (fun hs => hx (φ.tsupport_subset hs))
          simp only [hz, zero_mul]
    have hright : (∫ x in (Ω : Set (SpatialCoordinates d)),
        fderiv ℝ φ x v * hdata.1 x) = ∫ x, fderiv ℝ φ x v * h x := by
      calc
        _ = ∫ x in (Ω : Set (SpatialCoordinates d)), fderiv ℝ φ x v * h x := by
          apply integral_congr_ae
          filter_upwards [hae] with x hx
          rw [hx]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          have hz : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ
            (fun hs => hx (φ.tsupport_subset hs))
          simp only [hz, zero_apply, zero_mul]
    rw [hleft, hright, hibp, neg_add_cancel]
  have hmem' : (hdata.1, hdata.2) ∈ weakSobolevGraph Ω := hmem
  have hEq : hdata.2 = gh := weakSobolevGraph_gradient_unique hmem' hmem2
  rw [hEq]
  exact (hLp i).coeFn_toLp

/-- Integrability of one flux coordinate against a test. -/
theorem aux_rem_resolved_microscopic_flux_term_integrable {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)}
    (At : SpatialCoordinates d → ℝ) {L : ℝ≥0} (hAt : LipschitzWith L At)
    (h : SpatialCoordinates d → ℝ) (hh : ContDiff ℝ 2 h)
    (φ : 𝓓(Ω, ℝ)) (i : Fin d) :
    Integrable (fun x => (lineDeriv ℝ At x (Pi.single i 1) * fderiv ℝ h x (Pi.single i 1) +
        At x * fderiv ℝ (fderiv ℝ h) x (Pi.single i 1) (Pi.single i 1)) * φ x) := by
  set v : SpatialCoordinates d := Pi.single i 1
  have hφ1 : ContDiff ℝ 1 (φ : SpatialCoordinates d → ℝ) := φ.contDiff.of_le (by simp)
  have hφc : Continuous (φ : SpatialCoordinates d → ℝ) := φ.contDiff.continuous
  have hh1 : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (m := 1) (by norm_num)
  have hhi : Continuous (fun x => fderiv ℝ h x v) := hh1.continuous.clm_apply continuous_const
  have hh2c : Continuous (fun x => fderiv ℝ (fderiv ℝ h) x v v) :=
    ((hh1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  have hAtc : Continuous At := hAt.continuous
  have hI1 : Integrable (fun x => lineDeriv ℝ At x v * (fderiv ℝ h x v * φ x)) :=
    ((hhi.mul hφc).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left).bdd_mul
      (c := (L : ℝ) * ‖v‖) (measurable_lineDeriv hAtc).aestronglyMeasurable
      (Eventually.of_forall fun x => norm_lineDeriv_le_of_lipschitz ℝ hAt)
  have hI2 : Integrable (fun x => At x * fderiv ℝ (fderiv ℝ h) x v v * φ x) :=
    ((hAtc.mul hh2c).mul hφc).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  have := hI1.add hI2
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  ring

/-- The datum-flux identity against every smooth compactly supported test. -/
theorem aux_rem_resolved_microscopic_flux_smooth {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (At : SpatialCoordinates d → ℝ) {L : ℝ≥0}
    (hAt : LipschitzWith L At)
    (haAt : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] At)
    (h : SpatialCoordinates d → ℝ) (hh : ContDiff ℝ 2 h) (hdata : SobolevData Ω)
    (hgrad : ∀ i : Fin d, (hdata.2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        fun x => fderiv ℝ h x (Pi.single i 1))
    (φ : 𝓓(Ω, ℝ)) :
    sobolevCoefficientForm a hdata (smoothSobolevData φ) =
      -∫ x in (Ω : Set (SpatialCoordinates d)),
        aux_remResolvedMicroscopicFluxDiv At h x * (smoothSobolevData φ).1 x := by
  rw [sobolevCoefficientForm_apply]
  have hl : ∀ i : Fin d, (∫ x in (Ω : Set (SpatialCoordinates d)),
      a.val x * (hdata.2 i x * (smoothSobolevData φ).2 i x)) =
      -∫ x, (lineDeriv ℝ At x (Pi.single i 1) * fderiv ℝ h x (Pi.single i 1) +
        At x * fderiv ℝ (fderiv ℝ h) x (Pi.single i 1) (Pi.single i 1)) * φ x := by
    intro i
    rw [← aux_rem_resolved_microscopic_flux_ibp_coord At hAt h hh φ i]
    calc
      _ = ∫ x in (Ω : Set (SpatialCoordinates d)),
          At x * (fderiv ℝ h x (Pi.single i 1) * fderiv ℝ φ x (Pi.single i 1)) := by
        apply integral_congr_ae
        filter_upwards [haAt, hgrad i, testPartialL2_coeFn φ i] with x h1 h2 h3
        change a.val x * (hdata.2 i x * (testPartialL2 φ i) x) = _
        rw [h1, h2, h3]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have hz : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ
          (fun hs => hx (φ.tsupport_subset hs))
        simp only [hz, zero_apply, mul_zero]
  rw [Finset.sum_congr rfl fun i _ => hl i, Finset.sum_neg_distrib,
    ← integral_finsetSum _ fun i _ =>
      aux_rem_resolved_microscopic_flux_term_integrable At hAt h hh φ i]
  congr 1
  calc
    _ = ∫ x, aux_remResolvedMicroscopicFluxDiv At h x * φ x := by
      congr 1
      funext x
      rw [aux_remResolvedMicroscopicFluxDiv, Finset.sum_mul]
    _ = ∫ x in (Ω : Set (SpatialCoordinates d)),
        aux_remResolvedMicroscopicFluxDiv At h x * φ x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport
          (fun hs => hx (φ.tsupport_subset hs))
        simp only [hz, mul_zero]).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [testL2_coeFn φ] with x hx
      change _ = aux_remResolvedMicroscopicFluxDiv At h x * (testL2 φ) x
      rw [hx]

/-- The smooth identity passes to the killed closure: both sides are continuous in the
graph norm once the flux divergence is square integrable on the domain. -/
theorem aux_rem_resolved_microscopic_flux_killed {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (hdata : SobolevData Ω) (G : SpatialCoordinates d → ℝ)
    (hG : MemLp G 2 (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (hsmooth : ∀ φ : 𝓓(Ω, ℝ), sobolevCoefficientForm a hdata (smoothSobolevData φ) =
      -∫ x in (Ω : Set (SpatialCoordinates d)), G x * (smoothSobolevData φ).1 x) :
    ∀ ψ : killedSobolevGraph Ω, sobolevCoefficientForm a hdata (ψ : SobolevData Ω) =
      -∫ x in (Ω : Set (SpatialCoordinates d)), G x * (ψ : SobolevData Ω).1 x := by
  let R : SobolevData Ω →L[ℝ] ℝ :=
    (innerSL ℝ (hG.toLp G)).comp (ContinuousLinearMap.fst ℝ _ _)
  have hR : ∀ z : SobolevData Ω, R z = ∫ x in (Ω : Set (SpatialCoordinates d)), G x * z.1 x := by
    intro z
    change inner ℝ (hG.toLp G) z.1 = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with x hx
    rw [hx]
    simp [mul_comm]
  let T : SobolevData Ω →L[ℝ] ℝ := sobolevCoefficientForm a hdata + R
  have hle : killedSobolevGraph Ω ≤ LinearMap.ker (T : SobolevData Ω →ₗ[ℝ] ℝ) := by
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨φ, rfl⟩
      rw [LinearMap.mem_ker]
      change sobolevCoefficientForm a hdata (smoothSobolevData φ) + R (smoothSobolevData φ) = 0
      rw [hsmooth φ, hR, neg_add_cancel]
    · exact ContinuousLinearMap.isClosed_ker T
  intro ψ
  have hψ := hle ψ.property
  rw [LinearMap.mem_ker] at hψ
  change sobolevCoefficientForm a hdata ψ + R ψ = 0 at hψ
  rw [hR] at hψ
  linarith

theorem aux_rem_resolved_microscopic_unit_closure_isCompact (d : ℕ) :
    IsCompact (closure (unitNeumannCube d : Set (SpatialCoordinates d))) :=
  (centeredCube_isBounded (fun _ => (1 / 2 : ℝ)) one_pos).isCompact_closure

theorem aux_rem_resolved_microscopic_unit_center_mem (d : ℕ) :
    (fun _ => (1 / 2 : ℝ)) ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) := by
  change (fun _ => (1 / 2 : ℝ)) ∈ Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)
  exact Metric.mem_ball_self (by norm_num)

/-- **Dirichlet datum flux, clauses (1)+(2)** of the frozen Dirichlet conjunct of
`rem_resolved_microscopic`, for every constant `C ≥ d` and every `0 < c ≤ 1`, on the
actual frozen carriers.  Besides the frozen bound and weak identity, `G` is exported as
measurable and essentially bounded on `Q` (for the `v`-equation and the reflection). -/
theorem aux_rem_resolved_microscopic_datum_flux
    (d : ℕ) (C c : ℝ) (hC : (d : ℝ) ≤ C) (hc : 0 < c) (hc1 : c ≤ 1)
    (eps : ℝ) (heps : 0 < eps)
    (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ))
    (haA : a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (DN mN MN : ℝ) (hDN : 0 ≤ DN) (hmN : 0 < mN)
    (hbd : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      mN ≤ A y ∧ A y ≤ MN)
    (hlog : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z)
    (h : SpatialCoordinates d → ℝ) (hh : ContDiff ℝ 2 h)
    (hdata : weakSobolevGraph (unitNeumannCube d))
    (hhd : (hdata : SobolevData (unitNeumannCube d)).1
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] h) :
    let Q := unitNeumannCube d
    let K := closure (Q : Set (SpatialCoordinates d))
    let ell : ℝ := c * eps / (1 + DN)
    ∃ G : SpatialCoordinates d → ℝ,
      (∀ Kg Kh2 : ℝ, 0 ≤ Kg → 0 ≤ Kh2 →
        (∀ y ∈ K, ‖fderiv ℝ h y‖ ≤ Kg) →
        (∀ y ∈ K, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ Kh2) →
        ∀ x ∈ (Q : Set (SpatialCoordinates d)),
          |G x| ≤ C * MN * (Kh2 + ell⁻¹ * Kg)) ∧
      (∀ ψ : killedSobolevGraph Q,
        sobolevCoefficientForm a (hdata : SobolevData Q) (ψ : SobolevData Q) =
          -∫ x in (Q : Set (SpatialCoordinates d)),
            G x * (ψ : SobolevData Q).1 x) ∧
      Measurable G ∧
      ∃ B : ℝ, ∀ x ∈ (Q : Set (SpatialCoordinates d)), |G x| ≤ B := by
  intro Q K ell
  have hK : IsCompact K := aux_rem_resolved_microscopic_unit_closure_isCompact d
  have hQK : (Q : Set (SpatialCoordinates d)) ⊆ K := subset_closure
  have hx0 := aux_rem_resolved_microscopic_unit_center_mem d
  have hMN : 0 ≤ MN :=
    (hmN.le.trans (hbd _ (hQK hx0)).1).trans (hbd _ (hQK hx0)).2
  have hLipOn := aux_rem_resolved_microscopic_coeff_lipschitzOn (A : SpatialCoordinates d → ℝ)
    K mN MN DN eps hmN hMN hbd hlog
  obtain ⟨At, hAtLip, hEq⟩ := hLipOn.extend_real
  have hL : ((Real.toNNReal (MN * (DN / eps)) : ℝ≥0) : ℝ) = MN * (DN / eps) :=
    Real.coe_toNNReal _ (mul_nonneg hMN (div_nonneg hDN heps.le))
  have haAt : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] At := by
    filter_upwards [haA, ae_restrict_mem Q.isOpen.measurableSet] with x h1 h2
    rw [h1, hEq (hQK h2)]
  have hAtx : ∀ x ∈ (Q : Set (SpatialCoordinates d)), |At x| ≤ MN := by
    intro x hx
    rw [← hEq (hQK hx)]
    have hb := hbd x (hQK hx)
    rw [abs_of_pos (hmN.trans_le hb.1)]
    exact hb.2
  have hgrad := aux_rem_resolved_microscopic_datum_gradient K hK hQK h hh
    (hdata : SobolevData Q) hdata.property hhd
  set G := aux_remResolvedMicroscopicFluxDiv At h with hG
  have hGmeas : Measurable G :=
    aux_rem_resolved_microscopic_fluxDiv_measurable At h hAtLip.continuous hh
  have hh1 : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (m := 1) (by norm_num)
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn
    (hh.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn
    (hh1.continuous_fderiv (by norm_num)).continuousOn
  have hGbd : ∀ x ∈ (Q : Set (SpatialCoordinates d)),
      |G x| ≤ (d : ℝ) * ((Real.toNNReal (MN * (DN / eps)) : ℝ) * B1 + MN * B2) :=
    fun x hx => aux_rem_resolved_microscopic_fluxDiv_bound At h hAtLip x MN B1 B2
      (hAtx x hx) (hB1 x (hQK hx)) (hB2 x (hQK hx))
  have hG2 : MemLp G 2 (volume.restrict (Q : Set (SpatialCoordinates d))) := by
    refine MemLp.of_bound hGmeas.aestronglyMeasurable
      ((d : ℝ) * ((Real.toNNReal (MN * (DN / eps)) : ℝ) * B1 + MN * B2)) ?_
    exact (ae_restrict_iff' Q.isOpen.measurableSet).mpr
      (Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs]; exact hGbd x hx)
  refine ⟨G, ?_, ?_, hGmeas, _, hGbd⟩
  · intro Kg Kh2 hKg hKh2 hg hh2 x hx
    have hb := aux_rem_resolved_microscopic_fluxDiv_bound At h hAtLip x MN Kg Kh2
      (hAtx x hx) (hg x (hQK hx)) (hh2 x (hQK hx))
    rw [hL] at hb
    have hell : DN / eps ≤ ell⁻¹ := by
      change DN / eps ≤ (c * eps / (1 + DN))⁻¹
      rw [inv_div, div_le_div_iff₀ heps (mul_pos hc heps)]
      nlinarith [mul_le_mul_of_nonneg_left hc1 (mul_nonneg hDN heps.le)]
    have hinner : 0 ≤ Kh2 + ell⁻¹ * Kg :=
      add_nonneg hKh2 (mul_nonneg ((div_nonneg hDN heps.le).trans hell) hKg)
    calc |G x| ≤ (d : ℝ) * (MN * (DN / eps) * Kg + MN * Kh2) := hb
      _ = (d : ℝ) * MN * (Kh2 + DN / eps * Kg) := by ring
      _ ≤ (d : ℝ) * MN * (Kh2 + ell⁻¹ * Kg) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg d) hMN)
          gcongr
      _ ≤ C * MN * (Kh2 + ell⁻¹ * Kg) := by
          apply mul_le_mul_of_nonneg_right _ hinner
          exact mul_le_mul_of_nonneg_right hC hMN
  · exact aux_rem_resolved_microscopic_flux_killed a (hdata : SobolevData Q) G hG2
      (fun φ => aux_rem_resolved_microscopic_flux_smooth a At hAtLip haAt h hh
        (hdata : SobolevData Q) hgrad φ)

/-- The weak equation of `v = u - hdata` with the effective source `f + G`. -/
theorem aux_rem_resolved_microscopic_v_equation {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (a : PositiveCoefficient Ω) (f G : SpatialCoordinates d → ℝ)
    (hf : MemLp f 2 (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (hG : MemLp G 2 (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (hdata u : weakSobolevGraph Ω) (hsol : SolvesDirichlet a f hdata u)
    (hGid : ∀ ψ : killedSobolevGraph Ω,
      sobolevCoefficientForm a (hdata : SobolevData Ω) (ψ : SobolevData Ω) =
        -∫ x in (Ω : Set (SpatialCoordinates d)), G x * (ψ : SobolevData Ω).1 x) :
    ((u : SobolevData Ω) - (hdata : SobolevData Ω)) ∈ killedSobolevGraph Ω ∧
    ∀ ψ : killedSobolevGraph Ω,
      sobolevCoefficientForm a ((u : SobolevData Ω) - (hdata : SobolevData Ω))
          (ψ : SobolevData Ω) =
        ∫ x in (Ω : Set (SpatialCoordinates d)),
          (f x + G x) * (ψ : SobolevData Ω).1 x := by
  refine ⟨hsol.1, fun ψ => ?_⟩
  rw [map_sub, sub_apply, hsol.2 ψ, hGid ψ, sub_neg_eq_add]
  have h1 : Integrable (fun x => f x * (ψ : SobolevData Ω).1 x)
      (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
    hf.integrable_mul (Lp.memLp _)
  have h2 : Integrable (fun x => G x * (ψ : SobolevData Ω).1 x)
      (volume.restrict (Ω : Set (SpatialCoordinates d))) :=
    hG.integrable_mul (Lp.memLp _)
  rw [← integral_add h1 h2]
  congr 1
  funext x
  ring


def aux_remResolvedMicroscopicOddSource {d : ℕ} (D : EvenReflectionDomain d)
    (F : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) : ℝ :=
  if x D.i ≤ D.z D.i then F x else -F (coordinateReflection D.z {D.i} x)

/-- **One odd step with a scalar source.**  If `u` solves the forced equation on the
lower half with scalar source `F` against killed tests, its odd extension solves the
forced equation on the doubled domain with the signed reflected scalar source. -/
theorem aux_rem_resolved_microscopic_odd_step_scalar_source {d : ℕ}
    (D : EvenReflectionDomain d)
    (a : PositiveCoefficient D.Ω) {u : SobolevData D.Ω}
    (F : SpatialCoordinates d → ℝ)
    (hF : MemLp F 2 (volume.restrict (D.Ω : Set (SpatialCoordinates d))))
    (hL : ∀ v ∈ killedSobolevGraph D.Ω, sobolevCoefficientForm a u v =
      ∫ x in (D.Ω : Set (SpatialCoordinates d)), F x * v.1 x)
    {ψ : SobolevData D.U} (hψ : ψ ∈ killedSobolevGraph D.U) :
    sobolevCoefficientForm (D.evenExtensionCoefficient a) (D.oddExtension u) ψ =
      ∫ x in (D.U : Set (SpatialCoordinates d)),
        aux_remResolvedMicroscopicOddSource D F x * ψ.1 x := by
  rw [D.oddExtension_killed_equation a
    (fun v => ∫ x in (D.Ω : Set (SpatialCoordinates d)), F x * v.1 x) hL hψ]
  set R := coordinateReflection D.z {D.i} with hR
  set r1 := sobolevDataRestrict D.Ω_le ψ with hr1
  set r2 := D.reflectedRestrict ψ with hr2
  have hRR : ∀ x, R (R x) = x := coordinateReflection_involutive D.z {D.i}
  have hmpΩ : MeasurePreserving R (volume.restrict (D.Ω : Set (SpatialCoordinates d)))
      (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_reflected
  have hmpR : MeasurePreserving R (volume.restrict (D.reflected : Set (SpatialCoordinates d)))
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
  have hemb : MeasurableEmbedding R :=
    (coordinateReflectionEquiv D.z {D.i}).toHomeomorph.measurableEmbedding
  -- split the load
  have hi1 : Integrable (fun x => F x * r1.1 x)
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    hF.integrable_mul (Lp.memLp _)
  have hi2 : Integrable (fun x => F x * r2.1 x)
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    hF.integrable_mul (Lp.memLp _)
  have e0 : (∫ x in (D.Ω : Set (SpatialCoordinates d)), F x * (r1 - r2).1 x) =
      (∫ x in (D.Ω : Set (SpatialCoordinates d)), F x * r1.1 x) -
        ∫ x in (D.Ω : Set (SpatialCoordinates d)), F x * r2.1 x := by
    rw [← integral_sub hi1 hi2]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub r1.1 r2.1] with x hx
    change F x * (r1.1 - r2.1) x = _
    rw [hx, Pi.sub_apply, mul_sub]
  have e1 : (∫ x in (D.Ω : Set (SpatialCoordinates d)), F x * r1.1 x) =
      ∫ x in (D.Ω : Set (SpatialCoordinates d)), F x * ψ.1 x := by
    apply integral_congr_ae
    filter_upwards [domainLpRestrict_coeFn D.Ω_le ψ.1] with x hx
    change F x * (domainLpRestrict D.Ω_le ψ.1) x = _
    rw [hx]
  have e2 : (∫ x in (D.Ω : Set (SpatialCoordinates d)), F x * r2.1 x) =
      ∫ y in (D.reflected : Set (SpatialCoordinates d)), F (R y) * ψ.1 y := by
    set g := domainLpRestrict D.reflected_le ψ.1 with hg
    calc (∫ x in (D.Ω : Set (SpatialCoordinates d)), F x * r2.1 x)
        = ∫ x in (D.Ω : Set (SpatialCoordinates d)), F (R (R x)) * g (R x) := by
          apply integral_congr_ae
          filter_upwards [reflectionLp_coeFn D.z {D.i} D.preimage_reflected g] with x hx
          change F x * (reflectionLp D.z {D.i} D.preimage_reflected g) x = _
          rw [hx, hRR]
          rfl
      _ = ∫ y in (D.reflected : Set (SpatialCoordinates d)), F (R y) * g y :=
          hmpΩ.integral_comp hemb (fun y => F (R y) * g y)
      _ = _ := by
          apply integral_congr_ae
          filter_upwards [domainLpRestrict_coeFn D.reflected_le ψ.1] with y hy
          rw [hy]
  -- assemble the doubled-domain integral
  have hψΩ : MemLp (ψ.1 : SpatialCoordinates d → ℝ) 2
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    (Lp.memLp ψ.1).mono_measure (Measure.restrict_mono D.Ω_le le_rfl)
  have hψR : MemLp (ψ.1 : SpatialCoordinates d → ℝ) 2
      (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
    (Lp.memLp ψ.1).mono_measure (Measure.restrict_mono D.reflected_le le_rfl)
  have hFR : MemLp (fun y => F (R y)) 2
      (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
    hF.comp_measurePreserving hmpR
  have hsrcΩ : ∀ x ∈ (D.Ω : Set (SpatialCoordinates d)),
      aux_remResolvedMicroscopicOddSource D F x * ψ.1 x = F x * ψ.1 x := by
    intro x hx
    simp only [aux_remResolvedMicroscopicOddSource, ite_eq_left ((D.mem_iff x).mp hx).2.le]
  have hsrcR : ∀ x ∈ (D.reflected : Set (SpatialCoordinates d)),
      aux_remResolvedMicroscopicOddSource D F x * ψ.1 x = -(F (R x) * ψ.1 x) := by
    intro x hx
    have h := ((D.mem_reflected_iff x).mp hx).2
    simp only [aux_remResolvedMicroscopicOddSource, ite_eq_right (not_le.mpr h), hR]
    ring
  have hintΩ : IntegrableOn (fun x => aux_remResolvedMicroscopicOddSource D F x * ψ.1 x)
      (D.Ω : Set (SpatialCoordinates d)) := by
    refine (hF.integrable_mul hψΩ).congr ?_
    filter_upwards [ae_restrict_mem D.Ω.isOpen.measurableSet] with x hx
    exact (hsrcΩ x hx).symm
  have hintR : IntegrableOn (fun x => aux_remResolvedMicroscopicOddSource D F x * ψ.1 x)
      (D.reflected : Set (SpatialCoordinates d)) := by
    refine (hFR.integrable_mul hψR).neg.congr ?_
    filter_upwards [ae_restrict_mem D.reflected.isOpen.measurableSet] with x hx
    rw [hsrcR x hx]
    rfl
  have e3 : (∫ x in (D.U : Set (SpatialCoordinates d)),
      aux_remResolvedMicroscopicOddSource D F x * ψ.1 x) =
      (∫ x in (D.Ω : Set (SpatialCoordinates d)), F x * ψ.1 x) -
        ∫ y in (D.reflected : Set (SpatialCoordinates d)), F (R y) * ψ.1 y := by
    rw [← setIntegral_congr_set D.union_ae_eq,
      setIntegral_union D.disjoint_Ω_reflected D.reflected.isOpen.measurableSet hintΩ hintR,
      setIntegral_congr_fun D.Ω.isOpen.measurableSet hsrcΩ,
      setIntegral_congr_fun D.reflected.isOpen.measurableSet hsrcR, integral_neg, sub_eq_add_neg]
  change (∫ x in (D.Ω : Set (SpatialCoordinates d)), F x * (r1 - r2).1 x) = _
  rw [e0, e1, e2, e3]

/-- The signed reflected scalar source of one downward odd step (original box above
the plane). -/
def aux_remResolvedMicroscopicOddSourceDown {d : ℕ} (D : EvenReflectionDomain d)
    (F : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) : ℝ :=
  if D.z D.i ≤ x D.i then F x else -F (coordinateReflection D.z {D.i} x)

/-- **One downward odd step with a scalar source.**  The original box is the upper half
`D.reflected`; the extension is the one of `solves_step_down`. -/
theorem aux_rem_resolved_microscopic_odd_step_down_scalar_source {d : ℕ}
    (D : EvenReflectionDomain d)
    (b : PositiveCoefficient D.reflected) (w : SobolevData D.reflected)
    (F : SpatialCoordinates d → ℝ)
    (hF : MemLp F 2 (volume.restrict (D.reflected : Set (SpatialCoordinates d))))
    (hL : ∀ v ∈ killedSobolevGraph D.reflected, sobolevCoefficientForm b w v =
      ∫ x in (D.reflected : Set (SpatialCoordinates d)), F x * v.1 x)
    {ψ : SobolevData D.U} (hψ : ψ ∈ killedSobolevGraph D.U) :
    sobolevCoefficientForm
        (D.evenExtensionCoefficient (reflectionCoefficient D.z {D.i} D.preimage_reflected b))
        (-(D.oddExtension (reflectionSobolevData D.z {D.i} D.preimage_reflected w))) ψ =
      ∫ x in (D.U : Set (SpatialCoordinates d)),
        aux_remResolvedMicroscopicOddSourceDown D F x * ψ.1 x := by
  set R := coordinateReflection D.z {D.i} with hR
  set a := reflectionCoefficient D.z {D.i} D.preimage_reflected b with ha
  set v₀ := reflectionSobolevData D.z {D.i} D.preimage_reflected w with hv₀
  have hRR : ∀ x, R (R x) = x := coordinateReflection_involutive D.z {D.i}
  have hmpΩ : MeasurePreserving R (volume.restrict (D.Ω : Set (SpatialCoordinates d)))
      (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_reflected
  have hemb : MeasurableEmbedding R :=
    (coordinateReflectionEquiv D.z {D.i}).toHomeomorph.measurableEmbedding
  have hFR : MemLp (fun x => F (R x)) 2 (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    hF.comp_measurePreserving hmpΩ
  have hsolve : ∀ v ∈ killedSobolevGraph D.Ω, sobolevCoefficientForm a v₀ v =
      ∫ x in (D.Ω : Set (SpatialCoordinates d)), F (R x) * v.1 x := by
    intro v hv
    have hinv := reflectionSobolevData_inverse D.z {D.i} D.preimage_Ω v
    have hrefl := sobolevCoefficientForm_reflection D.z {D.i} D.preimage_reflected b w
      (reflectionSobolevData D.z {D.i} D.preimage_Ω v)
    rw [hinv] at hrefl
    rw [ha, hv₀, hrefl, hL _ (reflectionSobolevData_mem_killed D.z {D.i} D.preimage_Ω hv)]
    calc (∫ y in (D.reflected : Set (SpatialCoordinates d)),
          F y * (reflectionSobolevData D.z {D.i} D.preimage_Ω v).1 y)
        = ∫ y in (D.reflected : Set (SpatialCoordinates d)), F y * v.1 (R y) := by
          apply integral_congr_ae
          filter_upwards [reflectionLp_coeFn D.z {D.i} D.preimage_Ω v.1] with y hy
          change F y * (reflectionLp D.z {D.i} D.preimage_Ω v.1) y = _
          rw [hy]
          rfl
      _ = ∫ x in (D.Ω : Set (SpatialCoordinates d)), F (R x) * v.1 (R (R x)) :=
          (hmpΩ.integral_comp hemb (fun y => F y * v.1 (R y))).symm
      _ = _ := by simp_rw [hRR]
  have hup := aux_rem_resolved_microscopic_odd_step_scalar_source D a (u := v₀)
    (fun x => F (R x)) hFR hsolve hψ
  rw [show sobolevCoefficientForm (D.evenExtensionCoefficient a) (-(D.oddExtension v₀)) ψ =
      -(sobolevCoefficientForm (D.evenExtensionCoefficient a) (D.oddExtension v₀) ψ) by
        rw [map_neg]; rfl, hup, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [D.ae_mem_or_mem] with x hx
  rcases hx with hx | hx
  · have h := ((D.mem_iff x).mp hx).2
    simp only [aux_remResolvedMicroscopicOddSource, aux_remResolvedMicroscopicOddSourceDown,
      ite_eq_left h.le, ite_eq_right (not_le.mpr h)]
    ring
  · have h := ((D.mem_reflected_iff x).mp hx).2
    simp only [aux_remResolvedMicroscopicOddSource, aux_remResolvedMicroscopicOddSourceDown,
      ite_eq_right (not_le.mpr h), ite_eq_left h.le]
    rw [← hR, hRR]
    ring

end DirichletFluxHelpers

section DirichletMultifaceHelpers

variable {d : ℕ}




/-! ## The fold sign -/

/-- The fold sign over the active set `J`: literally the frozen `sgn` of clause (3). -/
def aux_rem_resolved_microscopic_mf_sgn (z : SpatialCoordinates d) (J P : Finset (Fin d))
    (x : SpatialCoordinates d) : ℝ :=
  ∏ i ∈ J, (if 0 ≤ coordinateReflectionSign P i * (x i - z i) then (1 : ℝ) else -1)

theorem aux_rem_resolved_microscopic_mf_sgn_empty (z : SpatialCoordinates d)
    (P : Finset (Fin d)) (x : SpatialCoordinates d) :
    aux_rem_resolved_microscopic_mf_sgn z ∅ P x = 1 := by
  simp [aux_rem_resolved_microscopic_mf_sgn]

theorem aux_rem_resolved_microscopic_mf_sgn_measurable (z : SpatialCoordinates d)
    (J P : Finset (Fin d)) : Measurable (aux_rem_resolved_microscopic_mf_sgn z J P) := by
  unfold aux_rem_resolved_microscopic_mf_sgn
  refine Finset.measurable_prod _ (fun i _ => ?_)
  exact Measurable.ite (measurableSet_le measurable_const
    (measurable_const.mul ((measurable_pi_apply i).sub measurable_const)))
    measurable_const measurable_const

theorem aux_rem_resolved_microscopic_mf_abs_sgn (z : SpatialCoordinates d)
    (J P : Finset (Fin d)) (x : SpatialCoordinates d) :
    |aux_rem_resolved_microscopic_mf_sgn z J P x| = 1 := by
  unfold aux_rem_resolved_microscopic_mf_sgn
  rw [Finset.abs_prod]
  refine Finset.prod_eq_one (fun i _ => ?_)
  split_ifs <;> simp

theorem aux_rem_resolved_microscopic_mf_sgn_reflect {z z' : SpatialCoordinates d}
    {J P : Finset (Fin d)} {i : Fin d} (hiJ : i ∉ J) (x : SpatialCoordinates d) :
    aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection z' {i} x) =
      aux_rem_resolved_microscopic_mf_sgn z J P x := by
  unfold aux_rem_resolved_microscopic_mf_sgn
  refine Finset.prod_congr rfl (fun j hj => ?_)
  have hji : j ≠ i := fun h => hiJ (h ▸ hj)
  rw [coordinateReflection_single_apply_of_ne _ hji]

theorem aux_rem_resolved_microscopic_mf_sgn_insert {z : SpatialCoordinates d}
    {J P : Finset (Fin d)} {i : Fin d} (hiJ : i ∉ J) (x : SpatialCoordinates d) :
    aux_rem_resolved_microscopic_mf_sgn z (insert i J) P x =
      (if 0 ≤ coordinateReflectionSign P i * (x i - z i) then (1 : ℝ) else -1) *
        aux_rem_resolved_microscopic_mf_sgn z J P x := by
  unfold aux_rem_resolved_microscopic_mf_sgn
  rw [Finset.prod_insert hiJ]

/-! ## Adjoining one coordinate: the signed pullback -/

/-- Upward fold, below the new plane: nothing changes. -/
theorem aux_rem_resolved_microscopic_mf_up_le {z : SpatialCoordinates d}
    {J P : Finset (Fin d)} {i : Fin d} (hiJ : i ∉ J) (hiP : i ∈ P)
    (g : SpatialCoordinates d → ℝ) {x : SpatialCoordinates d} (hx : x i ≤ z i) :
    aux_rem_resolved_microscopic_mf_sgn z (insert i J) P x *
        g (coordinateFold z (insert i J) P x) =
      aux_rem_resolved_microscopic_mf_sgn z J P x * g (coordinateFold z J P x) := by
  have hfold : coordinateFold z (insert i J) P x = coordinateFold z J P x := by
    have h := fold_insert_both_of_le (z := z) (I := J) (P := P) hiJ hx
    rwa [Finset.insert_eq_of_mem hiP] at h
  have hs : coordinateReflectionSign P i = -1 := by simp [coordinateReflectionSign, hiP]
  rw [hfold, aux_rem_resolved_microscopic_mf_sgn_insert hiJ, hs,
    ite_eq_left (by linarith)]
  ring

/-- Upward fold, above the new plane: reflect, and the sign flips. -/
theorem aux_rem_resolved_microscopic_mf_up_gt {z : SpatialCoordinates d}
    {J P : Finset (Fin d)} {i : Fin d} (hiJ : i ∉ J) (hiP : i ∈ P)
    (g : SpatialCoordinates d → ℝ) {x : SpatialCoordinates d} (hx : z i < x i) :
    aux_rem_resolved_microscopic_mf_sgn z (insert i J) P x *
        g (coordinateFold z (insert i J) P x) =
      -(aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection z {i} x) *
        g (coordinateFold z J P (coordinateReflection z {i} x))) := by
  have hfold : coordinateFold z (insert i J) P x =
      coordinateFold z J P (coordinateReflection z {i} x) := by
    have h := fold_insert_both_of_ge (z := z) (I := J) (P := P) hiJ hx.le
    rwa [Finset.insert_eq_of_mem hiP] at h
  have hs : coordinateReflectionSign P i = -1 := by simp [coordinateReflectionSign, hiP]
  rw [hfold, aux_rem_resolved_microscopic_mf_sgn_insert hiJ,
    aux_rem_resolved_microscopic_mf_sgn_reflect hiJ, hs, ite_eq_right (by linarith)]
  ring

/-- Downward fold, above the new plane: nothing changes. -/
theorem aux_rem_resolved_microscopic_mf_down_ge {z : SpatialCoordinates d}
    {J P : Finset (Fin d)} {i : Fin d} (hiJ : i ∉ J) (hiP : i ∉ P)
    (g : SpatialCoordinates d → ℝ) {x : SpatialCoordinates d} (hx : z i ≤ x i) :
    aux_rem_resolved_microscopic_mf_sgn z (insert i J) P x *
        g (coordinateFold z (insert i J) P x) =
      aux_rem_resolved_microscopic_mf_sgn z J P x * g (coordinateFold z J P x) := by
  have hs : coordinateReflectionSign P i = 1 := by simp [coordinateReflectionSign, hiP]
  rw [fold_insert_I_of_ge hiJ hiP hx, aux_rem_resolved_microscopic_mf_sgn_insert hiJ,
    hs, ite_eq_left (by linarith)]
  ring

/-- Downward fold, below the new plane: reflect, and the sign flips. -/
theorem aux_rem_resolved_microscopic_mf_down_lt {z : SpatialCoordinates d}
    {J P : Finset (Fin d)} {i : Fin d} (hiJ : i ∉ J) (hiP : i ∉ P)
    (g : SpatialCoordinates d → ℝ) {x : SpatialCoordinates d} (hx : x i < z i) :
    aux_rem_resolved_microscopic_mf_sgn z (insert i J) P x *
        g (coordinateFold z (insert i J) P x) =
      -(aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection z {i} x) *
        g (coordinateFold z J P (coordinateReflection z {i} x))) := by
  have hs : coordinateReflectionSign P i = 1 := by simp [coordinateReflectionSign, hiP]
  rw [fold_insert_I_of_le hiJ hiP hx.le, aux_rem_resolved_microscopic_mf_sgn_insert hiJ,
    aux_rem_resolved_microscopic_mf_sgn_reflect hiJ, hs, ite_eq_right (by linarith)]
  ring

/-- The one-step upward source of `OddStep.lean` is the signed pullback over `insert i J`. -/
theorem aux_rem_resolved_microscopic_mf_src_up (D : EvenReflectionDomain d)
    {z : SpatialCoordinates d} {J P : Finset (Fin d)} (hiJ : D.i ∉ J) (hiP : D.i ∈ P)
    (hz : z D.i = D.z D.i) (g : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) :
    aux_remResolvedMicroscopicOddSource D
        (fun y => aux_rem_resolved_microscopic_mf_sgn z J P y * g (coordinateFold z J P y)) x =
      aux_rem_resolved_microscopic_mf_sgn z (insert D.i J) P x *
        g (coordinateFold z (insert D.i J) P x) := by
  unfold aux_remResolvedMicroscopicOddSource
  rw [← coordinateReflection_single_congr z D.z D.i hz]
  split_ifs with h
  · rw [aux_rem_resolved_microscopic_mf_up_le hiJ hiP g (by rw [hz]; exact h)]
  · rw [aux_rem_resolved_microscopic_mf_up_gt hiJ hiP g
      (by rw [hz]; exact lt_of_not_ge h)]

/-- The one-step downward source of `OddStep.lean` is the signed pullback over
`insert i J`. -/
theorem aux_rem_resolved_microscopic_mf_src_down (D : EvenReflectionDomain d)
    {z : SpatialCoordinates d} {J P : Finset (Fin d)} (hiJ : D.i ∉ J) (hiP : D.i ∉ P)
    (hz : z D.i = D.z D.i) (g : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) :
    aux_remResolvedMicroscopicOddSourceDown D
        (fun y => aux_rem_resolved_microscopic_mf_sgn z J P y * g (coordinateFold z J P y)) x =
      aux_rem_resolved_microscopic_mf_sgn z (insert D.i J) P x *
        g (coordinateFold z (insert D.i J) P x) := by
  unfold aux_remResolvedMicroscopicOddSourceDown
  rw [← coordinateReflection_single_congr z D.z D.i hz]
  split_ifs with h
  · rw [aux_rem_resolved_microscopic_mf_down_ge hiJ hiP g (by rw [hz]; exact h)]
  · rw [aux_rem_resolved_microscopic_mf_down_lt hiJ hiP g
      (by rw [hz]; exact lt_of_not_ge h)]

/-! ## One step, with coefficient, datum and scalar source -/

/-- **Upward multiface step with a scalar source.** -/
theorem aux_rem_resolved_microscopic_mf_step_up (D : EvenReflectionDomain d)
    {B C : Opens (SpatialCoordinates d)} (hB : D.Ω = B) (hC : D.U = C)
    {z : SpatialCoordinates d} {J P : Finset (Fin d)}
    (hiJ : D.i ∉ J) (hiP : D.i ∈ P) (hz : z D.i = D.z D.i)
    (A F v0 : SpatialCoordinates d → ℝ)
    (a : PositiveCoefficient B) (w : SobolevData B) (hw : w ∈ killedSobolevGraph B)
    (ha : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))] foldedCoefficientP A z J P)
    (hwv : (w.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))]
        fun x => aux_rem_resolved_microscopic_mf_sgn z J P x * v0 (coordinateFold z J P x))
    (hS : MemLp (fun x => aux_rem_resolved_microscopic_mf_sgn z J P x *
        F (coordinateFold z J P x)) 2 (volume.restrict (B : Set (SpatialCoordinates d))))
    (hL : ∀ ψ ∈ killedSobolevGraph B, sobolevCoefficientForm a w ψ =
      ∫ x in (B : Set (SpatialCoordinates d)),
        aux_rem_resolved_microscopic_mf_sgn z J P x * F (coordinateFold z J P x) * ψ.1 x) :
    ∃ (a' : PositiveCoefficient C) (w' : SobolevData C), w' ∈ killedSobolevGraph C ∧
      ((a'.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (C : Set (SpatialCoordinates d))]
          foldedCoefficientP A z (insert D.i J) P) ∧
      ((w'.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (C : Set (SpatialCoordinates d))]
          fun x => aux_rem_resolved_microscopic_mf_sgn z (insert D.i J) P x *
            v0 (coordinateFold z (insert D.i J) P x)) ∧
      ∀ ψ ∈ killedSobolevGraph C, sobolevCoefficientForm a' w' ψ =
        ∫ x in (C : Set (SpatialCoordinates d)),
          aux_rem_resolved_microscopic_mf_sgn z (insert D.i J) P x *
            F (coordinateFold z (insert D.i J) P x) * ψ.1 x := by
  subst hB
  subst hC
  have hRz : coordinateReflection z {D.i} = coordinateReflection D.z {D.i} :=
    coordinateReflection_single_congr z D.z D.i hz
  refine ⟨D.evenExtensionCoefficient a, D.oddExtension w,
    _root_.SubdiffusiveProcess.EvenReflectionDomain.oddExtension_mem_killed D hw, ?_, ?_, ?_⟩
  · have h := evenExtensionCoefficient_fold_up D a hiJ hz ha
    rwa [Finset.insert_eq_of_mem hiP] at h
  · have hmp : MeasurePreserving (coordinateReflection D.z {D.i})
        (volume.restrict (D.reflected : Set (SpatialCoordinates d)))
        (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
      coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
    have hΩ : ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
        x ∈ (D.Ω : Set (SpatialCoordinates d)) →
          (w.1 : SpatialCoordinates d → ℝ) x =
            aux_rem_resolved_microscopic_mf_sgn z J P x * v0 (coordinateFold z J P x) :=
      ae_restrict_of_ae ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp hwv)
    have hR0 : ∀ᵐ x ∂(volume.restrict (D.reflected : Set (SpatialCoordinates d))),
        (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x) =
          aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection D.z {D.i} x) *
            v0 (coordinateFold z J P (coordinateReflection D.z {D.i} x)) :=
      hmp.quasiMeasurePreserving.ae hwv
    have hR : ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
        x ∈ (D.reflected : Set (SpatialCoordinates d)) →
          (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x) =
            aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection D.z {D.i} x) *
              v0 (coordinateFold z J P (coordinateReflection D.z {D.i} x)) :=
      ae_restrict_of_ae ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp hR0)
    filter_upwards [D.oddExtension_fst_coeFn w, D.ae_mem_or_mem, hΩ, hR]
      with x h1 hmem h2 h3
    rw [h1]
    rcases hmem with hx | hx
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_notMem (D.notMem_reflected_of_mem_Ω hx), sub_zero, h2 hx,
        aux_rem_resolved_microscopic_mf_up_le hiJ hiP v0
          (by rw [hz]; exact ((D.mem_iff x).mp hx).2.le)]
    · rw [Set.indicator_of_notMem (D.notMem_Ω_of_mem_reflected hx), Set.indicator_of_mem hx,
        zero_sub, Function.comp_apply, h3 hx,
        aux_rem_resolved_microscopic_mf_up_gt hiJ hiP v0
          (by rw [hz]; exact ((D.mem_reflected_iff x).mp hx).2), hRz]
  · intro ψ hψ
    rw [aux_rem_resolved_microscopic_odd_step_scalar_source D a
      (fun x => aux_rem_resolved_microscopic_mf_sgn z J P x * F (coordinateFold z J P x))
      hS hL hψ]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only []
    rw [aux_rem_resolved_microscopic_mf_src_up D hiJ hiP hz F x]

/-- **Downward multiface step with a scalar source.** -/
theorem aux_rem_resolved_microscopic_mf_step_down (D : EvenReflectionDomain d)
    {B C : Opens (SpatialCoordinates d)} (hB : D.reflected = B) (hC : D.U = C)
    {z : SpatialCoordinates d} {J P : Finset (Fin d)}
    (hiJ : D.i ∉ J) (hiP : D.i ∉ P) (hz : z D.i = D.z D.i)
    (A F v0 : SpatialCoordinates d → ℝ)
    (a : PositiveCoefficient B) (w : SobolevData B) (hw : w ∈ killedSobolevGraph B)
    (ha : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))] foldedCoefficientP A z J P)
    (hwv : (w.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))]
        fun x => aux_rem_resolved_microscopic_mf_sgn z J P x * v0 (coordinateFold z J P x))
    (hS : MemLp (fun x => aux_rem_resolved_microscopic_mf_sgn z J P x *
        F (coordinateFold z J P x)) 2 (volume.restrict (B : Set (SpatialCoordinates d))))
    (hL : ∀ ψ ∈ killedSobolevGraph B, sobolevCoefficientForm a w ψ =
      ∫ x in (B : Set (SpatialCoordinates d)),
        aux_rem_resolved_microscopic_mf_sgn z J P x * F (coordinateFold z J P x) * ψ.1 x) :
    ∃ (a' : PositiveCoefficient C) (w' : SobolevData C), w' ∈ killedSobolevGraph C ∧
      ((a'.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (C : Set (SpatialCoordinates d))]
          foldedCoefficientP A z (insert D.i J) P) ∧
      ((w'.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (C : Set (SpatialCoordinates d))]
          fun x => aux_rem_resolved_microscopic_mf_sgn z (insert D.i J) P x *
            v0 (coordinateFold z (insert D.i J) P x)) ∧
      ∀ ψ ∈ killedSobolevGraph C, sobolevCoefficientForm a' w' ψ =
        ∫ x in (C : Set (SpatialCoordinates d)),
          aux_rem_resolved_microscopic_mf_sgn z (insert D.i J) P x *
            F (coordinateFold z (insert D.i J) P x) * ψ.1 x := by
  subst hB
  subst hC
  have hRz : coordinateReflection z {D.i} = coordinateReflection D.z {D.i} :=
    coordinateReflection_single_congr z D.z D.i hz
  refine ⟨D.evenExtensionCoefficient (reflectionCoefficient D.z {D.i} D.preimage_reflected a),
    -(D.oddExtension (reflectionSobolevData D.z {D.i} D.preimage_reflected w)),
    neg_mem (oddExtension_reflected_mem_killed D hw), ?_, ?_, ?_⟩
  · exact evenExtensionCoefficient_fold_down D a hiJ hiP hz ha
  · have hneg : ((((-(D.oddExtension (reflectionSobolevData D.z {D.i} D.preimage_reflected w))).1 :
          DomainL2 D.U) : SpatialCoordinates d → ℝ))
        =ᵐ[volume.restrict (D.U : Set (SpatialCoordinates d))]
          fun x => -(((D.oddExtension
            (reflectionSobolevData D.z {D.i} D.preimage_reflected w)).1 :
              SpatialCoordinates d → ℝ) x) :=
      Lp.coeFn_neg _
    have hmpΩ : MeasurePreserving (coordinateReflection D.z {D.i})
        (volume.restrict (D.Ω : Set (SpatialCoordinates d)))
        (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
      coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_reflected
    -- lower (new) half: the odd extension is the pulled-back datum
    have hΩ1 : ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
        x ∈ (D.Ω : Set (SpatialCoordinates d)) →
          ((D.oddExtension (reflectionSobolevData D.z {D.i} D.preimage_reflected w)).1 :
              SpatialCoordinates d → ℝ) x =
            (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x) := by
      have e1 := D.oddExtension_ae_eq_on_Omega
        (reflectionSobolevData D.z {D.i} D.preimage_reflected w)
      have e2 : (((reflectionSobolevData D.z {D.i} D.preimage_reflected w).1 :
            DomainL2 D.Ω) : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (D.Ω : Set (SpatialCoordinates d))]
            (w.1 : SpatialCoordinates d → ℝ) ∘ coordinateReflection D.z {D.i} :=
        reflectionLp_coeFn D.z {D.i} D.preimage_reflected w.1
      have e3 := e1.trans e2
      exact ae_restrict_of_ae ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp e3)
    have hΩ2 : ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
        x ∈ (D.Ω : Set (SpatialCoordinates d)) →
          (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x) =
            aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection D.z {D.i} x) *
              v0 (coordinateFold z J P (coordinateReflection D.z {D.i} x)) := by
      have e : ∀ᵐ x ∂(volume.restrict (D.Ω : Set (SpatialCoordinates d))),
          (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x) =
            aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection D.z {D.i} x) *
              v0 (coordinateFold z J P (coordinateReflection D.z {D.i} x)) :=
        hmpΩ.quasiMeasurePreserving.ae hwv
      exact ae_restrict_of_ae ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp e)
    -- upper (original) half: the extension is minus the datum
    have hR1 : ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
        x ∈ (D.reflected : Set (SpatialCoordinates d)) →
          ((D.oddExtension (reflectionSobolevData D.z {D.i} D.preimage_reflected w)).1 :
              SpatialCoordinates d → ℝ) x = -((w.1 : SpatialCoordinates d → ℝ) x) :=
      ae_restrict_of_ae ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp
        (D.oddExtension_reflected_ae_eq_neg w))
    have hR2 : ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
        x ∈ (D.reflected : Set (SpatialCoordinates d)) →
          (w.1 : SpatialCoordinates d → ℝ) x =
            aux_rem_resolved_microscopic_mf_sgn z J P x * v0 (coordinateFold z J P x) :=
      ae_restrict_of_ae ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp hwv)
    filter_upwards [hneg, D.ae_mem_or_mem, hΩ1, hΩ2, hR1, hR2] with x h0 hmem h1 h2 h3 h4
    rw [h0]
    rcases hmem with hx | hx
    · rw [h1 hx, h2 hx, aux_rem_resolved_microscopic_mf_down_lt hiJ hiP v0
          (by rw [hz]; exact ((D.mem_iff x).mp hx).2), hRz]
    · rw [h3 hx, neg_neg, h4 hx, aux_rem_resolved_microscopic_mf_down_ge hiJ hiP v0
          (by rw [hz]; exact ((D.mem_reflected_iff x).mp hx).2.le)]
  · intro ψ hψ
    rw [aux_rem_resolved_microscopic_odd_step_down_scalar_source D a w
      (fun x => aux_rem_resolved_microscopic_mf_sgn z J P x * F (coordinateFold z J P x))
      hS hL hψ]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only []
    rw [aux_rem_resolved_microscopic_mf_src_down D hiJ hiP hz F x]


/-! ## The partially folded cubes as boxes -/

/-- Lower corner of `centeredCube c r` doubled across the lower faces in `J \ P`. -/
def aux_rem_resolved_microscopic_mf_lo (c : SpatialCoordinates d) (r : ℝ)
    (J P : Finset (Fin d)) : SpatialCoordinates d :=
  fun j => if j ∈ J ∧ j ∉ P then c j - 3 * r / 2 else c j - r / 2

/-- Upper corner of `centeredCube c r` doubled across the upper faces in `J ∩ P`. -/
def aux_rem_resolved_microscopic_mf_hi (c : SpatialCoordinates d) (r : ℝ)
    (J P : Finset (Fin d)) : SpatialCoordinates d :=
  fun j => if j ∈ J ∧ j ∈ P then c j + 3 * r / 2 else c j + r / 2

theorem aux_rem_resolved_microscopic_mf_box (c : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (J P : Finset (Fin d)) :
    foldedCube c r hr J P =
      openBox (aux_rem_resolved_microscopic_mf_lo c r J P)
        (aux_rem_resolved_microscopic_mf_hi c r J P) := by
  apply Opens.ext
  show Set.pi Set.univ _ = Set.pi Set.univ _
  congr 1
  funext j
  simp only [aux_rem_resolved_microscopic_mf_lo, aux_rem_resolved_microscopic_mf_hi]
  by_cases hJ : j ∈ J <;> by_cases hP : j ∈ P <;> simp [hJ, hP]

theorem aux_rem_resolved_microscopic_mf_cube_eq (c : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (P : Finset (Fin d)) :
    centeredCube c r hr = foldedCube c r hr ∅ P := by
  apply Opens.ext
  rw [centeredCube_eq_pi]
  show _ = Set.pi Set.univ _
  congr 1

theorem aux_rem_resolved_microscopic_mf_up_U (c : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    {J P : Finset (Fin d)} {i : Fin d} (hiJ : i ∉ J) (hiP : i ∈ P) :
    (boxEvenReflectionDomain (aux_rem_resolved_microscopic_mf_lo c r J P)
      (aux_rem_resolved_microscopic_mf_hi c r J P) i).U = foldedCube c r hr (insert i J) P := by
  rw [aux_rem_resolved_microscopic_mf_box]
  show openBox (aux_rem_resolved_microscopic_mf_lo c r J P)
    (doubledCorner (aux_rem_resolved_microscopic_mf_lo c r J P)
      (aux_rem_resolved_microscopic_mf_hi c r J P) i) = _
  congr 1
  · funext j
    simp only [aux_rem_resolved_microscopic_mf_lo]
    by_cases hj : j = i
    · subst hj
      rw [ite_eq_right (fun h => hiJ h.1), ite_eq_right (fun h => h.2 hiP)]
    · simp [Finset.mem_insert, hj]
  · funext j
    by_cases hj : j = i
    · subst hj
      rw [doubledCorner_apply_self]
      simp only [aux_rem_resolved_microscopic_mf_lo, aux_rem_resolved_microscopic_mf_hi]
      rw [ite_eq_right (fun h => hiJ h.1), ite_eq_right (fun h => hiJ h.1),
        ite_eq_left ⟨Finset.mem_insert_self j J, hiP⟩]
      ring
    · rw [doubledCorner_apply_of_ne _ _ hj]
      simp [aux_rem_resolved_microscopic_mf_hi, Finset.mem_insert, hj]

theorem aux_rem_resolved_microscopic_mf_up_z (c : SpatialCoordinates d) (r : ℝ)
    {I J P : Finset (Fin d)} {i : Fin d} (hiI : i ∈ I) (hiJ : i ∉ J) (hiP : i ∈ P) :
    foldedCubeCenter c r I P
        (boxEvenReflectionDomain (aux_rem_resolved_microscopic_mf_lo c r J P)
          (aux_rem_resolved_microscopic_mf_hi c r J P) i).i =
      (boxEvenReflectionDomain (aux_rem_resolved_microscopic_mf_lo c r J P)
          (aux_rem_resolved_microscopic_mf_hi c r J P) i).z
        (boxEvenReflectionDomain (aux_rem_resolved_microscopic_mf_lo c r J P)
          (aux_rem_resolved_microscopic_mf_hi c r J P) i).i := by
  show foldedCubeCenter c r I P i = upperFacePoint (aux_rem_resolved_microscopic_mf_lo c r J P)
    (aux_rem_resolved_microscopic_mf_hi c r J P) i i
  rw [upperFacePoint_apply_self]
  simp only [foldedCubeCenter, aux_rem_resolved_microscopic_mf_hi]
  rw [ite_eq_left hiI, ite_eq_left hiP, ite_eq_right (fun h => hiJ h.1)]

theorem aux_rem_resolved_microscopic_mf_down_U (c : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) {J P : Finset (Fin d)} {i : Fin d} (hiJ : i ∉ J) (hiP : i ∉ P) :
    (boxEvenReflectionDomain
      (lowerDoubledCorner (aux_rem_resolved_microscopic_mf_lo c r J P)
        (aux_rem_resolved_microscopic_mf_hi c r J P) i)
      (Function.update (aux_rem_resolved_microscopic_mf_hi c r J P) i
        (aux_rem_resolved_microscopic_mf_lo c r J P i)) i).U =
      foldedCube c r hr (insert i J) P := by
  rw [boxEvenReflectionDomain_mirror_U, aux_rem_resolved_microscopic_mf_box]
  congr 1
  · funext j
    by_cases hj : j = i
    · subst hj
      rw [lowerDoubledCorner, Function.update_self]
      simp only [aux_rem_resolved_microscopic_mf_lo, aux_rem_resolved_microscopic_mf_hi]
      rw [ite_eq_right (fun h => hiJ h.1), ite_eq_right (fun h => hiJ h.1),
        ite_eq_left ⟨Finset.mem_insert_self j J, hiP⟩]
      ring
    · rw [lowerDoubledCorner, Function.update_of_ne hj]
      simp [aux_rem_resolved_microscopic_mf_lo, Finset.mem_insert, hj]
  · funext j
    simp only [aux_rem_resolved_microscopic_mf_hi]
    by_cases hj : j = i
    · subst hj
      rw [ite_eq_right (fun h => hiJ h.1), ite_eq_right (fun h => hiP h.2)]
    · simp [Finset.mem_insert, hj]

theorem aux_rem_resolved_microscopic_mf_down_z (c : SpatialCoordinates d) (r : ℝ)
    {I J P : Finset (Fin d)} {i : Fin d} (hiI : i ∈ I) (hiJ : i ∉ J) (hiP : i ∉ P) :
    foldedCubeCenter c r I P
        (boxEvenReflectionDomain
          (lowerDoubledCorner (aux_rem_resolved_microscopic_mf_lo c r J P)
            (aux_rem_resolved_microscopic_mf_hi c r J P) i)
          (Function.update (aux_rem_resolved_microscopic_mf_hi c r J P) i
            (aux_rem_resolved_microscopic_mf_lo c r J P i)) i).i =
      (boxEvenReflectionDomain
          (lowerDoubledCorner (aux_rem_resolved_microscopic_mf_lo c r J P)
            (aux_rem_resolved_microscopic_mf_hi c r J P) i)
          (Function.update (aux_rem_resolved_microscopic_mf_hi c r J P) i
            (aux_rem_resolved_microscopic_mf_lo c r J P i)) i).z
        (boxEvenReflectionDomain
          (lowerDoubledCorner (aux_rem_resolved_microscopic_mf_lo c r J P)
            (aux_rem_resolved_microscopic_mf_hi c r J P) i)
          (Function.update (aux_rem_resolved_microscopic_mf_hi c r J P) i
            (aux_rem_resolved_microscopic_mf_lo c r J P i)) i).i := by
  show foldedCubeCenter c r I P i = upperFacePoint
    (lowerDoubledCorner (aux_rem_resolved_microscopic_mf_lo c r J P)
      (aux_rem_resolved_microscopic_mf_hi c r J P) i)
    (Function.update (aux_rem_resolved_microscopic_mf_hi c r J P) i
      (aux_rem_resolved_microscopic_mf_lo c r J P i)) i i
  rw [upperFacePoint_apply_self, Function.update_self]
  simp only [foldedCubeCenter, aux_rem_resolved_microscopic_mf_lo]
  rw [ite_eq_left hiI, ite_eq_right hiP, ite_eq_right (fun h => hiJ h.1)]

/-! ## The signed source is square integrable on every partial box -/

theorem aux_rem_resolved_microscopic_mf_memLp (c : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (z : SpatialCoordinates d) (J P : Finset (Fin d)) (F : SpatialCoordinates d → ℝ)
    (hFm : Measurable F) (M : ℝ) (hFM : ∀ y, |F y| ≤ M) :
    MemLp (fun x => aux_rem_resolved_microscopic_mf_sgn z J P x * F (coordinateFold z J P x)) 2
      (volume.restrict (foldedCube c r hr J P : Set (SpatialCoordinates d))) := by
  have hb : Bornology.IsBounded (foldedCube c r hr J P : Set (SpatialCoordinates d)) := by
    rw [aux_rem_resolved_microscopic_mf_box c r hr J P]
    exact isBounded_openBox _ _
  have : IsFiniteMeasure
      (volume.restrict (foldedCube c r hr J P : Set (SpatialCoordinates d))) :=
    isFiniteMeasure_restrict.mpr (hb.measure_lt_top (μ := volume)).ne
  refine MemLp.of_bound (((aux_rem_resolved_microscopic_mf_sgn_measurable z J P).mul
    (hFm.comp (coordinateFold_continuous z J P).measurable)).aestronglyMeasurable) M
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, aux_rem_resolved_microscopic_mf_abs_sgn, one_mul]
  exact hFM _

/-! ## The iteration over the active set -/

/-- **Multi-face odd reflection with a scalar source, on every partial fold.**  The
datum, coefficient and scalar source on the cube `foldedCube c r hr ∅ P` are carried to
`foldedCube c r hr J P` for every `J ⊆ I`, as `sgn_J · v ∘ fold_J`, `A ∘ fold_J` and
`sgn_J · F ∘ fold_J`, with the fold centre `foldedCubeCenter c r I P`. -/
theorem aux_rem_resolved_microscopic_mf_induction (c : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (I P : Finset (Fin d)) (A F v0 : SpatialCoordinates d → ℝ)
    (hFm : Measurable F) (M : ℝ) (hFM : ∀ y, |F y| ≤ M)
    (Q0 : Opens (SpatialCoordinates d)) (hQ0 : Q0 = foldedCube c r hr ∅ P)
    (a : PositiveCoefficient Q0) (w : SobolevData Q0) (hw : w ∈ killedSobolevGraph Q0)
    (ha : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q0 : Set (SpatialCoordinates d))] A)
    (hwv : (w.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q0 : Set (SpatialCoordinates d))] v0)
    (hL : ∀ ψ ∈ killedSobolevGraph Q0, sobolevCoefficientForm a w ψ =
      ∫ x in (Q0 : Set (SpatialCoordinates d)), F x * ψ.1 x) :
    ∀ J : Finset (Fin d), J ⊆ I →
      ∃ (aJ : PositiveCoefficient (foldedCube c r hr J P))
        (wJ : SobolevData (foldedCube c r hr J P)),
        wJ ∈ killedSobolevGraph (foldedCube c r hr J P) ∧
        ((aJ.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (foldedCube c r hr J P : Set (SpatialCoordinates d))]
            foldedCoefficientP A (foldedCubeCenter c r I P) J P) ∧
        ((wJ.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (foldedCube c r hr J P : Set (SpatialCoordinates d))]
            fun x => aux_rem_resolved_microscopic_mf_sgn (foldedCubeCenter c r I P) J P x *
              v0 (coordinateFold (foldedCubeCenter c r I P) J P x)) ∧
        ∀ ψ ∈ killedSobolevGraph (foldedCube c r hr J P), sobolevCoefficientForm aJ wJ ψ =
          ∫ x in (foldedCube c r hr J P : Set (SpatialCoordinates d)),
            aux_rem_resolved_microscopic_mf_sgn (foldedCubeCenter c r I P) J P x *
              F (coordinateFold (foldedCubeCenter c r I P) J P x) * ψ.1 x := by
  subst hQ0
  intro J
  induction J using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨a, w, hw, ?_, ?_, ?_⟩
    · rw [foldedCoefficientP_empty]
      exact ha
    · filter_upwards [hwv] with x hx
      rw [hx, aux_rem_resolved_microscopic_mf_sgn_empty, fold_empty, one_mul]
    · intro ψ hψ
      rw [hL ψ hψ]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [aux_rem_resolved_microscopic_mf_sgn_empty, fold_empty, one_mul]
  | @insert i J hiJ ih =>
    intro hsub
    have hiI : i ∈ I := hsub (Finset.mem_insert_self i J)
    have hIH := ih ((Finset.subset_insert i J).trans hsub)
    rcases hIH with ⟨aJ, wJ, hwJ, haJ, hwvJ, hLJ⟩
    have hS := aux_rem_resolved_microscopic_mf_memLp c r hr (foldedCubeCenter c r I P) J P F
      hFm M hFM
    by_cases hiP : i ∈ P
    · exact aux_rem_resolved_microscopic_mf_step_up
        (boxEvenReflectionDomain (aux_rem_resolved_microscopic_mf_lo c r J P)
          (aux_rem_resolved_microscopic_mf_hi c r J P) i)
        (aux_rem_resolved_microscopic_mf_box c r hr J P).symm
        (aux_rem_resolved_microscopic_mf_up_U c r hr hiJ hiP) hiJ hiP
        (aux_rem_resolved_microscopic_mf_up_z c r hiI hiJ hiP) A F v0 aJ wJ hwJ haJ hwvJ
        hS hLJ
    · exact aux_rem_resolved_microscopic_mf_step_down
        (boxEvenReflectionDomain
          (lowerDoubledCorner (aux_rem_resolved_microscopic_mf_lo c r J P)
            (aux_rem_resolved_microscopic_mf_hi c r J P) i)
          (Function.update (aux_rem_resolved_microscopic_mf_hi c r J P) i
            (aux_rem_resolved_microscopic_mf_lo c r J P i)) i)
        ((boxEvenReflectionDomain_mirror_reflected _ _ i).trans
          (aux_rem_resolved_microscopic_mf_box c r hr J P).symm)
        (aux_rem_resolved_microscopic_mf_down_U c r hr hiJ hiP) hiJ hiP
        (aux_rem_resolved_microscopic_mf_down_z c r hiI hiJ hiP) A F v0 aJ wJ hwJ haJ hwvJ
        hS hLJ

/-! ## The fold planes are null -/

/-- Off the null fold planes, the fold maps the folded cube into the open root cube. -/
theorem aux_rem_resolved_microscopic_mf_fold_mem_ae (c : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (I P : Finset (Fin d)) :
    ∀ᵐ x ∂volume.restrict (foldedCube c r hr I P : Set (SpatialCoordinates d)),
      coordinateFold (foldedCubeCenter c r I P) I P x ∈
        (centeredCube c r hr : Set (SpatialCoordinates d)) := by
  have hplanes : ∀ j : Fin d, ∀ᵐ y ∂(volume : Measure (SpatialCoordinates d)),
      y j ≠ foldedCubeCenter c r I P j := fun j =>
    Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) j (foldedCubeCenter c r I P j)
  have hall := ae_all_iff.2 hplanes
  refine (ae_restrict_iff' (foldedCube c r hr I P).isOpen.measurableSet).2 ?_
  filter_upwards [hall] with x hx hxV
  have hxV' : x ∈ Set.pi Set.univ (fun j =>
      if j ∈ I then
        (if j ∈ P then Set.Ioo (c j - r / 2) (c j + 3 * r / 2)
          else Set.Ioo (c j - 3 * r / 2) (c j + r / 2))
      else Set.Ioo (c j - r / 2) (c j + r / 2)) := hxV
  rw [centeredCube_eq_pi]
  intro j _
  have hxj := hxV' j (Set.mem_univ j)
  beta_reduce at hxj
  have hne := hx j
  rw [Set.mem_Ioo]
  by_cases hI : j ∈ I
  · by_cases hP : j ∈ P
    · have hzj : foldedCubeCenter c r I P j = c j + r / 2 := by
        simp [foldedCubeCenter, hI, hP]
      have hT : coordinateFold (foldedCubeCenter c r I P) I P x j =
          foldedCubeCenter c r I P j - |x j - foldedCubeCenter c r I P j| := by
        simp only [coordinateFold, ite_eq_left hI, coordinateReflectionSign, ite_eq_left hP]
        ring
      rw [ite_eq_left hI, ite_eq_left hP, Set.mem_Ioo] at hxj
      rw [hT, hzj]
      rw [hzj] at hne
      have h1 : |x j - (c j + r / 2)| < r := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
      have h2 : 0 < |x j - (c j + r / 2)| := abs_pos.2 (sub_ne_zero.2 hne)
      constructor <;> linarith
    · have hzj : foldedCubeCenter c r I P j = c j - r / 2 := by
        simp [foldedCubeCenter, hI, hP]
      have hT : coordinateFold (foldedCubeCenter c r I P) I P x j =
          foldedCubeCenter c r I P j + |x j - foldedCubeCenter c r I P j| := by
        simp only [coordinateFold, ite_eq_left hI, coordinateReflectionSign, ite_eq_right hP]
        ring
      rw [ite_eq_left hI, ite_eq_right hP, Set.mem_Ioo] at hxj
      rw [hT, hzj]
      rw [hzj] at hne
      have h1 : |x j - (c j - r / 2)| < r := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
      have h2 : 0 < |x j - (c j - r / 2)| := abs_pos.2 (sub_ne_zero.2 hne)
      constructor <;> linarith
  · rw [ite_eq_right hI, Set.mem_Ioo] at hxj
    rw [fold_apply_of_notMem_I hI]
    exact hxj

/-! ## Milestone 1: multi-face transport with a scalar source on the exact folded cube -/

/-- **Multi-face odd reflection with a scalar source.**  A killed solution `v` of
`E_a(v, ψ) = ∫_Q F ψ` (all killed `ψ`) on the cube `Q = centeredCube c r hr`, with `F`
measurable and bounded on `Q`, is carried to the exact folded cube
`V = foldedCube c r hr I P`: coefficient `A ∘ T`, datum `sgn · v ∘ T`, source
`sgn · F ∘ T`, where `T = coordinateFold (foldedCubeCenter c r I P) I P`. -/
theorem aux_rem_resolved_microscopic_multiface_scalar (c : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (I P : Finset (Fin d)) (A F : SpatialCoordinates d → ℝ)
    (a : PositiveCoefficient (centeredCube c r hr))
    (ha : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))] A)
    (v : SobolevData (centeredCube c r hr))
    (hv : v ∈ killedSobolevGraph (centeredCube c r hr))
    (hFm : Measurable F) (M : ℝ)
    (hFM : ∀ y ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), |F y| ≤ M)
    (hL : ∀ ψ ∈ killedSobolevGraph (centeredCube c r hr), sobolevCoefficientForm a v ψ =
      ∫ x in (centeredCube c r hr : Set (SpatialCoordinates d)), F x * ψ.1 x) :
    ∃ (af : PositiveCoefficient (foldedCube c r hr I P))
      (vf : weakSobolevGraph (foldedCube c r hr I P)),
      ((af.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (foldedCube c r hr I P : Set (SpatialCoordinates d))]
          fun x => A (coordinateFold (foldedCubeCenter c r I P) I P x)) ∧
      (((vf : SobolevData (foldedCube c r hr I P)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (foldedCube c r hr I P : Set (SpatialCoordinates d))]
          fun x => aux_rem_resolved_microscopic_mf_sgn (foldedCubeCenter c r I P) I P x *
            v.1 (coordinateFold (foldedCubeCenter c r I P) I P x)) ∧
      ∀ ψ : killedSobolevGraph (foldedCube c r hr I P),
        sobolevCoefficientForm af (vf : SobolevData (foldedCube c r hr I P))
            (ψ : SobolevData (foldedCube c r hr I P)) =
          ∫ x in (foldedCube c r hr I P : Set (SpatialCoordinates d)),
            aux_rem_resolved_microscopic_mf_sgn (foldedCubeCenter c r I P) I P x *
              F (coordinateFold (foldedCubeCenter c r I P) I P x) *
                (ψ : SobolevData (foldedCube c r hr I P)).1 x := by
  have hmQ : MeasurableSet (centeredCube c r hr : Set (SpatialCoordinates d)) :=
    (centeredCube c r hr).isOpen.measurableSet
  have hF'm : Measurable ((centeredCube c r hr : Set (SpatialCoordinates d)).indicator F) :=
    hFm.indicator hmQ
  have hF'M : ∀ y, |(centeredCube c r hr : Set (SpatialCoordinates d)).indicator F y| ≤
      max M 0 := by
    intro y
    by_cases hy : y ∈ (centeredCube c r hr : Set (SpatialCoordinates d))
    · rw [Set.indicator_of_mem hy]
      exact (hFM y hy).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hy, abs_zero]
      exact le_max_right _ _
  have hL' : ∀ ψ ∈ killedSobolevGraph (centeredCube c r hr), sobolevCoefficientForm a v ψ =
      ∫ x in (centeredCube c r hr : Set (SpatialCoordinates d)),
        (centeredCube c r hr : Set (SpatialCoordinates d)).indicator F x * ψ.1 x := by
    intro ψ hψ
    rw [hL ψ hψ]
    refine setIntegral_congr_fun hmQ (fun x hx => ?_)
    simp only [Set.indicator_of_mem hx]
  have hind := aux_rem_resolved_microscopic_mf_induction c r hr I P A
    ((centeredCube c r hr : Set (SpatialCoordinates d)).indicator F)
    (v.1 : SpatialCoordinates d → ℝ) hF'm (max M 0) hF'M (centeredCube c r hr)
    (aux_rem_resolved_microscopic_mf_cube_eq c r hr P) a v hv ha
    (Filter.EventuallyEq.refl _ _) hL' I (Finset.Subset.refl I)
  rcases hind with ⟨aI, wI, hwI, haI, hwvI, hLI⟩
  refine ⟨aI, ⟨wI, killedSobolevGraph_le_weakSobolevGraph hwI⟩, haI, hwvI, fun ψ => ?_⟩
  rw [hLI ψ ψ.2]
  refine integral_congr_ae ?_
  filter_upwards [aux_rem_resolved_microscopic_mf_fold_mem_ae c r hr I P] with x hx
  simp only [Set.indicator_of_mem hx]

end DirichletMultifaceHelpers



/-- A measurable function bounded on the unit cube is square integrable there. -/
theorem aux_rem_resolved_microscopic_bounded_memLp_two {d : ℕ} (g : SpatialCoordinates d → ℝ)
    (hg : Measurable g) (B : ℝ)
    (hB : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |g y| ≤ B) :
    MemLp g 2 (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
  MemLp.of_bound hg.aestronglyMeasurable B
    ((ae_restrict_iff' (unitNeumannCube d).isOpen.measurableSet).2
      (Eventually.of_forall fun y hy => by rw [Real.norm_eq_abs]; exact hB y hy))

/-- **Clauses (1)–(3) of the Dirichlet conjunct, exact frozen shape.**  The hypotheses
are the frozen binders of `rem_resolved_microscopic` (plus the constant side conditions
`d ≤ C`, `c ≤ 1` of the datum-flux lemma). -/
theorem aux_rem_resolved_microscopic_dirichlet_flux_fold
    (d : ℕ) (C c : ℝ) (hC : (d : ℝ) ≤ C) (hc : 0 < c) (hc1 : c ≤ 1)
    (eps : ℝ) (heps : 0 < eps)
    (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ))
    (haA : a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (DN mN MN : ℝ) (hDN : 0 ≤ DN) (hmN : 0 < mN)
    (hbd : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      mN ≤ A y ∧ A y ≤ MN)
    (hlog : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f)
    (Kf : ℝ) (hKf : ∀ y ∈ unitNeumannCube d, |f y| ≤ Kf)
    (h : SpatialCoordinates d → ℝ) (hh : ContDiff ℝ 2 h)
    (hdata u : weakSobolevGraph (unitNeumannCube d))
    (hhd : (hdata : SobolevData (unitNeumannCube d)).1
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] h)
    (hsol : SolvesDirichlet a f hdata u) :
    let Q := unitNeumannCube d
    let K := closure (Q : Set (SpatialCoordinates d))
    let ell : ℝ := c * eps / (1 + DN)
    let v : SobolevData Q := (u : SobolevData Q) - (hdata : SobolevData Q)
    (∃ G : SpatialCoordinates d → ℝ,
      --  9: ‖∇·(A_N ∇h)‖_∞ ≤ C a_* (‖D²h‖_∞ + ℓ_N⁻¹ ‖∇h‖_∞)
      (∀ Kg Kh2 : ℝ, 0 ≤ Kg → 0 ≤ Kh2 →
        (∀ y ∈ K, ‖fderiv ℝ h y‖ ≤ Kg) →
        (∀ y ∈ K, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ Kh2) →
        ∀ x ∈ (Q : Set (SpatialCoordinates d)),
          |G x| ≤ C * MN * (Kh2 + ell⁻¹ * Kg)) ∧
      (∀ ψ : killedSobolevGraph Q,
        sobolevCoefficientForm a (hdata : SobolevData Q) (ψ : SobolevData Q) =
          -∫ x in (Q : Set (SpatialCoordinates d)),
            G x * (ψ : SobolevData Q).1 x) ∧
      (∀ I P : Finset (Fin d),
        let zface := foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P
        let T := coordinateFold zface I P
        let V := foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P
        let sgn : SpatialCoordinates d → ℝ := fun x =>
          ∏ i ∈ I, (if 0 ≤ coordinateReflectionSign P i * (x i - zface i) then (1 : ℝ) else -1)
        ∃ (af : PositiveCoefficient V) (vf : weakSobolevGraph V),
          ((af.val : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] fun x => A (T x)) ∧
          (((vf : SobolevData V).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))]
            fun x => sgn x * v.1 (T x)) ∧
          (∀ ψ : killedSobolevGraph V,
            sobolevCoefficientForm af (vf : SobolevData V) (ψ : SobolevData V) =
              ∫ x in (V : Set (SpatialCoordinates d)),
                sgn x * (f (T x) + G (T x)) * (ψ : SobolevData V).1 x))) := by
  intro Q K ell v
  have hflux := aux_rem_resolved_microscopic_datum_flux d C c hC hc hc1 eps heps a A haA DN mN MN
    hDN hmN hbd hlog h hh hdata hhd
  rcases hflux with ⟨G, hG1, hG2, hGm, BG, hBG⟩
  refine ⟨G, hG1, hG2, ?_⟩
  have hfL2 := aux_rem_resolved_microscopic_bounded_memLp_two f hf Kf hKf
  have hGL2 := aux_rem_resolved_microscopic_bounded_memLp_two G hGm BG hBG
  have hv := aux_rem_resolved_microscopic_v_equation a f G hfL2 hGL2 hdata u hsol hG2
  rcases hv with ⟨hvk, hveq⟩
  have hFB : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
      |f y + G y| ≤ Kf + BG := fun y hy =>
    (abs_add_le _ _).trans (add_le_add (hKf y hy) (hBG y hy))
  intro I P
  exact aux_rem_resolved_microscopic_multiface_scalar (fun _ => (1 / 2 : ℝ)) 1 one_pos I P
    (A : SpatialCoordinates d → ℝ) (fun y => f y + G y) a haA v hvk (hf.add hGm) (Kf + BG)
    hFB (fun ψ hψ => hveq ⟨ψ, hψ⟩)

section DirichletEnergyHelpers
open MeasureTheory Set TopologicalSpace Metric
open scoped ContDiff

/-- Pointwise energy density of the exact smooth Dirichlet datum. -/
theorem aux_micro_dirichlet_datum_density
    {d : ℕ} (A : C(SpatialCoordinates d, ℝ)) (K : Set (SpatialCoordinates d))
    (MN Kg : ℝ) (hMN : 0 ≤ MN) (hKg : 0 ≤ Kg)
    (hA : ∀ y ∈ K, 0 ≤ A y ∧ A y ≤ MN)
    (h : SpatialCoordinates d → ℝ)
    (hgrad : ∀ y ∈ K, ‖fderiv ℝ h y‖ ≤ Kg) :
    ∀ y ∈ K,
      A y * (∑ i : Fin d, (fderiv ℝ h y (Pi.single i 1)) ^ 2) ≤
        MN * (d : ℝ) * Kg ^ 2 := by
  intro y hy
  have hsingle : ∀ i : Fin d, ‖(Pi.single i (1 : ℝ) : SpatialCoordinates d)‖ ≤ 1 := by
    intro i
    rw [Pi.norm_single]
    norm_num
  have hcoord : ∀ i : Fin d, |fderiv ℝ h y (Pi.single i 1)| ≤ Kg := by
    intro i
    calc
      |fderiv ℝ h y (Pi.single i 1)| = ‖fderiv ℝ h y (Pi.single i 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ h y‖ * ‖(Pi.single i (1 : ℝ) : SpatialCoordinates d)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ Kg := by
        calc
          _ ≤ Kg * 1 := mul_le_mul (hgrad y hy) (hsingle i)
            (norm_nonneg _) hKg
          _ = Kg := mul_one _
  have hsq : ∀ i : Fin d, (fderiv ℝ h y (Pi.single i 1)) ^ 2 ≤ Kg ^ 2 := by
    intro i
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) hKg).2 (hcoord i)
  have hsum : (∑ i : Fin d, (fderiv ℝ h y (Pi.single i 1)) ^ 2) ≤
      (d : ℝ) * Kg ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin d, Kg ^ 2 := Finset.sum_le_sum (fun i _ => hsq i)
      _ = (d : ℝ) * Kg ^ 2 := by simp
  have hsum0 : 0 ≤ ∑ i : Fin d, (fderiv ℝ h y (Pi.single i 1)) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  calc
    A y * (∑ i : Fin d, (fderiv ℝ h y (Pi.single i 1)) ^ 2) ≤
        MN * (∑ i : Fin d, (fderiv ℝ h y (Pi.single i 1)) ^ 2) :=
      mul_le_mul_of_nonneg_right (hA y hy).2 hsum0
    _ ≤ MN * ((d : ℝ) * Kg ^ 2) :=
      mul_le_mul_of_nonneg_left hsum hMN
    _ = MN * (d : ℝ) * Kg ^ 2 := by ring

/-- The actual Sobolev-data subtraction has the required factor-two local
energy inequality on any measurable parent box. -/
theorem aux_micro_dirichlet_parent_energy_triangle
    {d : ℕ} (a : PositiveCoefficient (unitNeumannCube d))
    (u hdata : SobolevData (unitNeumannCube d))
    {B : Set (SpatialCoordinates d)} (hB : MeasurableSet B) :
    localGradientEnergy a hB (sobolevGradient (u - hdata)) ≤
      2 * localGradientEnergy a hB (sobolevGradient u) +
        2 * localGradientEnergy a hB (sobolevGradient hdata) := by
  rw [map_sub]
  have h := localGradientEnergy_sub_le a hB (sobolevGradient u - sobolevGradient hdata)
    (sobolevGradient u)
  have hneg : localGradientEnergy a hB (-sobolevGradient hdata) =
      localGradientEnergy a hB (sobolevGradient hdata) := by
    simp only [localGradientEnergy]
    apply Finset.sum_congr rfl
    intro i _
    have hcoord : (-sobolevGradient hdata).ofLp i =
        -((sobolevGradient hdata).ofLp i) := by
      simp
    have hlocneg : localizeL2 hB (-((sobolevGradient hdata).ofLp i)) =
        -localizeL2 hB ((sobolevGradient hdata).ofLp i) := by
      have hzero : localizeL2 hB (0 : DomainL2 (unitNeumannCube d)) = 0 := by
        simpa using localizeL2_sub hB ((sobolevGradient hdata).ofLp i)
          ((sobolevGradient hdata).ofLp i)
      simpa [hzero] using localizeL2_sub hB (0 : DomainL2 (unitNeumannCube d))
        ((sobolevGradient hdata).ofLp i)
    rw [hcoord, hlocneg]
    change weightedL2Form a.val (-(localizeL2 hB ((sobolevGradient hdata) i)))
      (-(localizeL2 hB ((sobolevGradient hdata) i))) = _
    simp [weightedL2Form, map_neg]
  have hdifference : sobolevGradient u - sobolevGradient hdata - sobolevGradient u =
      -sobolevGradient hdata := by abel
  rw [hdifference, hneg] at h
  exact h

/-- Identify the frozen coefficient integral with the native local energy on
the actual unit cube, for an arbitrary measurable parent box. -/
theorem aux_micro_dirichlet_gamma_local_energy
    {d : ℕ} (a : PositiveCoefficient (unitNeumannCube d))
    (A : C(SpatialCoordinates d, ℝ))
    (haA : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (MN : ℝ)
    (hAb : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), 0 ≤ A y ∧ A y ≤ MN)
    (v : SobolevData (unitNeumannCube d))
    {B : Set (SpatialCoordinates d)} (hB : MeasurableSet B) :
    (∫ y in B ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
      A y * ∑ i : Fin d, (v.2 i y) ^ 2) =
      localGradientEnergy a (hB.inter (unitNeumannCube d).isOpen.measurableSet)
        (sobolevGradient v) := by
  let Q := unitNeumannCube d
  let S := B ∩ (Q : Set (SpatialCoordinates d))
  have hS : MeasurableSet S := hB.inter Q.isOpen.measurableSet
  have hAabs : ∀ y ∈ (Q : Set (SpatialCoordinates d)), |A y| ≤ MN := by
    intro y hy
    rw [abs_of_nonneg (hAb y hy).1]
    exact (hAb y hy).2
  have hint : ∀ i : Fin d, Integrable (fun y => A y * (v.2 i y) ^ 2)
      (volume.restrict (Q : Set (SpatialCoordinates d))) := fun i =>
    aux_rem_resolved_microscopic_neumann_tie_sq_integrable A A.continuous MN hAabs (v.2 i)
  have hsum : (∫ y in S, A y * ∑ i : Fin d, (v.2 i y) ^ 2) =
      ∑ i : Fin d, ∫ y in S, A y * (v.2 i y) ^ 2 := by
    simp_rw [Finset.mul_sum]
    refine integral_finsetSum _ fun i _ => ?_
    exact (hint i).mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)
  rw [hsum, localGradientEnergy_eq_integral]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.restrict_restrict hS, Set.inter_assoc, Set.inter_self]
  apply integral_congr_ae
  have hAS : (a.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict S] A :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right haA
  filter_upwards [hAS] with y hy
  rw [hy]
  rfl

/-- The exact datum energy on a measurable parent box, using only the
classical gradient bound and the true weak-gradient identification. -/
theorem aux_micro_dirichlet_datum_energy_bound
    {d : ℕ} (a : PositiveCoefficient (unitNeumannCube d))
    (A : C(SpatialCoordinates d, ℝ))
    (_haA : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (MN Kg R : ℝ) (hMN : 0 ≤ MN) (hKg : 0 ≤ Kg)
    (hAb : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      0 ≤ A y ∧ A y ≤ MN)
    (h : SpatialCoordinates d → ℝ) (hh : ContDiff ℝ 2 h)
    (hdata : weakSobolevGraph (unitNeumannCube d))
    (htrace : ((hdata : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] h)
    (hgradbound : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      ‖fderiv ℝ h y‖ ≤ Kg)
    {B : Set (SpatialCoordinates d)} (hB : MeasurableSet B)
    (hfiniteB : volume B ≠ (⊤ : ℝ≥0∞))
    (hvol : volume.real B ≤ R ^ d) :
    (∫ y in B ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
      A y * ∑ i : Fin d, ((hdata : SobolevData (unitNeumannCube d)).2 i y) ^ 2) ≤
        MN * (d : ℝ) * Kg ^ 2 * R ^ d := by
  let Q := unitNeumannCube d
  let S := B ∩ (Q : Set (SpatialCoordinates d))
  have hS : MeasurableSet S := hB.inter Q.isOpen.measurableSet
  have hQfinite : volume (Q : Set (SpatialCoordinates d)) < ⊤ := by
    change volume (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
      Set (SpatialCoordinates d)) < ⊤
    rw [centeredCube_volume]
    exact ENNReal.ofReal_lt_top
  have hfiniteS : volume S ≠ (⊤ : ℝ≥0∞) :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_right) hQfinite).ne
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hfiniteS
  have hQK : (Q : Set (SpatialCoordinates d)) ⊆ closure (Q : Set _) := subset_closure
  have hAabs : ∀ y ∈ (Q : Set (SpatialCoordinates d)), |A y| ≤ MN := by
    intro y hy
    rw [abs_of_nonneg (hAb y (hQK hy)).1]
    exact (hAb y (hQK hy)).2
  have hintcoord : ∀ i : Fin d,
      Integrable (fun y => A y * ((hdata : SobolevData Q).2 i y) ^ 2)
        (volume.restrict S) := by
    intro i
    exact (aux_rem_resolved_microscopic_neumann_tie_sq_integrable A A.continuous MN
      hAabs ((hdata : SobolevData Q).2 i)).mono_measure
      (Measure.restrict_mono Set.inter_subset_right le_rfl)
  have hint : Integrable (fun y => A y *
      ∑ i : Fin d, ((hdata : SobolevData Q).2 i y) ^ 2) (volume.restrict S) := by
    have hs : Integrable (fun y => ∑ i : Fin d,
        A y * ((hdata : SobolevData Q).2 i y) ^ 2) (volume.restrict S) :=
      integrable_finsetSum _ (fun i _ => hintcoord i)
    simpa only [Finset.mul_sum] using hs
  have hgrad : ∀ i : Fin d,
      ((hdata : SobolevData Q).2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          fun y => fderiv ℝ h y (Pi.single i 1) := by
    intro i
    exact aux_rem_resolved_microscopic_datum_gradient
      (closure (Q : Set (SpatialCoordinates d)))
      (aux_rem_resolved_microscopic_unit_closure_isCompact d) hQK h hh
      (hdata : SobolevData Q) hdata.property htrace i
  have hgradS : ∀ i : Fin d,
      ((hdata : SobolevData Q).2 i : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict S]
          fun y => fderiv ℝ h y (Pi.single i 1) := by
    intro i
    exact ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hgrad i)
  have hpoint : ∀ᵐ y ∂volume.restrict S,
      A y * ∑ i : Fin d, ((hdata : SobolevData Q).2 i y) ^ 2 ≤
        MN * (d : ℝ) * Kg ^ 2 := by
    have hmem : ∀ᵐ y ∂volume.restrict S, y ∈ S :=
      ae_restrict_mem hS
    filter_upwards [hmem, Filter.eventually_all.2 hgradS] with y hy hgy
    have hyK : y ∈ closure (Q : Set (SpatialCoordinates d)) := hQK hy.2
    have hden := aux_micro_dirichlet_datum_density A
      (closure (Q : Set (SpatialCoordinates d))) MN Kg hMN hKg hAb h hgradbound y hyK
    have heq : (∑ i : Fin d, ((hdata : SobolevData Q).2 i y) ^ 2) =
        ∑ i : Fin d, (fderiv ℝ h y (Pi.single i 1)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hgy i]
    simpa only [heq] using hden
  have hmono : (∫ y in S,
      A y * ∑ i : Fin d, ((hdata : SobolevData Q).2 i y) ^ 2) ≤
      ∫ _y in S, MN * (d : ℝ) * Kg ^ 2 :=
    integral_mono_ae hint (integrable_const _) hpoint
  rw [setIntegral_const, smul_eq_mul] at hmono
  have hvolS : volume.real S ≤ R ^ d :=
    (measureReal_mono Set.inter_subset_left hfiniteB).trans hvol
  have hcoef : 0 ≤ MN * (d : ℝ) * Kg ^ 2 := by positivity
  calc
    _ ≤ volume.real S * (MN * (d : ℝ) * Kg ^ 2) := hmono
    _ ≤ R ^ d * (MN * (d : ℝ) * Kg ^ 2) :=
      mul_le_mul_of_nonneg_right hvolS hcoef
    _ = MN * (d : ℝ) * Kg ^ 2 * R ^ d := by ring

/-- Full comparison on the actual unit-cube carriers. The only geometric
input is the parent-box volume bound; no energy estimate is assumed. -/
theorem aux_micro_dirichlet_parent_comparison
    {d : ℕ} (a : PositiveCoefficient (unitNeumannCube d))
    (A : C(SpatialCoordinates d, ℝ))
    (haA : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (MN Kg R C : ℝ) (hMN : 0 ≤ MN) (hKg : 0 ≤ Kg)
    (hC : 2 * (d : ℝ) ≤ C) (hR : 0 ≤ R)
    (hAb : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      0 ≤ A y ∧ A y ≤ MN)
    (h : SpatialCoordinates d → ℝ) (hh : ContDiff ℝ 2 h)
    (hdata u : weakSobolevGraph (unitNeumannCube d))
    (htrace : ((hdata : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] h)
    (hgradbound : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      ‖fderiv ℝ h y‖ ≤ Kg)
    {B : Set (SpatialCoordinates d)} (hB : MeasurableSet B)
    (hfiniteB : volume B ≠ (⊤ : ℝ≥0∞))
    (hvol : volume.real B ≤ R ^ d) :
    (∫ y in B ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
      A y * ∑ i : Fin d,
        (((u : SobolevData (unitNeumannCube d)) -
          (hdata : SobolevData (unitNeumannCube d))).2 i y) ^ 2) ≤
      2 * (∫ y in B ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
        A y * ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2) +
      C * MN * Kg ^ 2 * R ^ d := by
  have hQbound : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
      0 ≤ A y ∧ A y ≤ MN := by
    intro y hy
    exact hAb y (subset_closure hy)
  have htri := aux_micro_dirichlet_parent_energy_triangle a
    (u : SobolevData (unitNeumannCube d))
    (hdata : SobolevData (unitNeumannCube d))
    (hB.inter (unitNeumannCube d).isOpen.measurableSet)
  have hv := aux_micro_dirichlet_gamma_local_energy a A haA MN hQbound
    ((u : SobolevData (unitNeumannCube d)) -
      (hdata : SobolevData (unitNeumannCube d))) hB
  have hu := aux_micro_dirichlet_gamma_local_energy a A haA MN hQbound
    (u : SobolevData (unitNeumannCube d)) hB
  have hhdata := aux_micro_dirichlet_gamma_local_energy a A haA MN hQbound
    (hdata : SobolevData (unitNeumannCube d)) hB
  have hdatum := aux_micro_dirichlet_datum_energy_bound a A haA MN Kg R
    hMN hKg hAb h hh hdata htrace hgradbound hB hfiniteB hvol
  rw [← hv, ← hu, ← hhdata] at htri
  have herror : 2 * (MN * (d : ℝ) * Kg ^ 2 * R ^ d) ≤
      C * MN * Kg ^ 2 * R ^ d := by
    have hnonneg : 0 ≤ MN * Kg ^ 2 * R ^ d := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hC hnonneg]
  nlinarith

/-- The coordinate-box measure used in the frozen `gamma` is exactly the
side-length power of the centered cube. -/
theorem aux_micro_dirichlet_box_volume
    {d : ℕ} (x : SpatialCoordinates d) {R : ℝ} (hR : 0 < R) :
    volume.real {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < R / 2} =
      R ^ d := by
  have hBox : {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < R / 2} =
      (centeredCube x R hR : Set (SpatialCoordinates d)) := by
    ext y
    rw [centeredCube_eq_pi x hR]
    simp only [mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
    constructor
    · intro hy i
      have hi := hy i
      rw [abs_lt] at hi
      constructor <;> linarith
    · intro hy i
      have hi := hy i
      rw [abs_lt]
      constructor <;> linarith
  rw [hBox]
  exact centeredCube_volume_real x hR

/-- Exact frozen Dirichlet parent-energy comparison, with the common theorem
constant chosen at least twice the dimension. -/
theorem aux_micro_dirichlet_frozen_parent_energy
    {d : ℕ} (a : PositiveCoefficient (unitNeumannCube d))
    (A : C(SpatialCoordinates d, ℝ))
    (haA : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (MN Kg C eps : ℝ) (hMN : 0 ≤ MN) (hKg : 0 ≤ Kg)
    (hCpos : 0 < C) (hCdim : 2 * (d : ℝ) ≤ C) (heps : 0 < eps)
    (hAb : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      0 ≤ A y ∧ A y ≤ MN)
    (h : SpatialCoordinates d → ℝ) (hh : ContDiff ℝ 2 h)
    (hdata u : weakSobolevGraph (unitNeumannCube d))
    (htrace : ((hdata : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] h)
    (hgradbound : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      ‖fderiv ℝ h y‖ ≤ Kg) :
    let Q := unitNeumannCube d
    let v : SobolevData Q := (u : SobolevData Q) - (hdata : SobolevData Q)
    let gamma := fun (w : SobolevData Q) (x : SpatialCoordinates d) (r : ℝ) =>
      ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩
        (Q : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (w.2 i y) ^ 2
    ∀ x : SpatialCoordinates d,
      gamma v x (C * eps) ≤
        2 * gamma u x (C * eps) + C * MN * Kg ^ 2 * (C * eps) ^ (d : ℝ) := by
  intro Q v gamma x
  let R := C * eps
  have hR : 0 < R := mul_pos hCpos heps
  let B : Set (SpatialCoordinates d) :=
    {y | ∀ i : Fin d, |y i - x i| < R / 2}
  have hbox : B = (centeredCube x R hR : Set (SpatialCoordinates d)) := by
    ext y
    rw [centeredCube_eq_pi x hR]
    simp only [B, mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
    constructor
    · intro hy i
      have hi := hy i
      rw [abs_lt] at hi
      constructor <;> linarith
    · intro hy i
      have hi := hy i
      rw [abs_lt]
      constructor <;> linarith
  have hB : MeasurableSet B := by
    rw [hbox]
    exact (centeredCube x R hR).isOpen.measurableSet
  have hfiniteB : volume B ≠ (⊤ : ℝ≥0∞) := by
    rw [hbox, centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  have hvol : volume.real B ≤ R ^ d := by
    rw [hbox, centeredCube_volume_real]
  have hcmp := aux_micro_dirichlet_parent_comparison a A haA MN Kg R C hMN hKg
    hCdim hR.le hAb h hh hdata u htrace hgradbound hB hfiniteB hvol
  simpa only [Q, v, gamma, R, B, Real.rpow_natCast] using hcmp

end DirichletEnergyHelpers

section DirichletGradientFold

variable {d : ℕ}




/-- The fold derivative factor of coordinate `j` over the active set `J`. -/
def aux_rem_resolved_microscopic_mfg_fac (z : SpatialCoordinates d) (J P : Finset (Fin d))
    (j : Fin d) (x : SpatialCoordinates d) : ℝ :=
  if j ∈ J then coordinateReflectionSign P j * (if x j < z j then -1 else 1) else 1

theorem aux_rem_resolved_microscopic_mfg_fac_empty (z : SpatialCoordinates d)
    (P : Finset (Fin d)) (j : Fin d) (x : SpatialCoordinates d) :
    aux_rem_resolved_microscopic_mfg_fac z ∅ P j x = 1 := by
  simp [aux_rem_resolved_microscopic_mfg_fac]

theorem aux_rem_resolved_microscopic_mfg_fac_keep {z : SpatialCoordinates d}
    {J P : Finset (Fin d)} {i : Fin d} (hiJ : i ∉ J) (x : SpatialCoordinates d)
    (h : coordinateReflectionSign P i * (if x i < z i then (-1 : ℝ) else 1) = 1) (j : Fin d) :
    aux_rem_resolved_microscopic_mfg_fac z (insert i J) P j x =
      aux_rem_resolved_microscopic_mfg_fac z J P j x := by
  unfold aux_rem_resolved_microscopic_mfg_fac
  by_cases hji : j = i
  · subst hji
    rw [ite_eq_left (Finset.mem_insert_self _ _), ite_eq_right hiJ, h]
  · simp only [Finset.mem_insert, hji, false_or]

theorem aux_rem_resolved_microscopic_mfg_fac_flip {z : SpatialCoordinates d}
    {J P : Finset (Fin d)} {i : Fin d} (hiJ : i ∉ J) (z' x : SpatialCoordinates d)
    (h : coordinateReflectionSign P i * (if x i < z i then (-1 : ℝ) else 1) = -1) (j : Fin d) :
    aux_rem_resolved_microscopic_mfg_fac z (insert i J) P j x =
      coordinateReflectionSign {i} j *
        aux_rem_resolved_microscopic_mfg_fac z J P j (coordinateReflection z' {i} x) := by
  unfold aux_rem_resolved_microscopic_mfg_fac
  by_cases hji : j = i
  · subst hji
    rw [ite_eq_left (Finset.mem_insert_self _ _), ite_eq_right hiJ, h]
    simp [coordinateReflectionSign]
  · have hR : coordinateReflection z' {i} x j = x j :=
      coordinateReflection_single_apply_of_ne z' hji x
    have hs : coordinateReflectionSign {i} j = 1 := by
      simp [coordinateReflectionSign, hji]
    simp only [Finset.mem_insert, hji, false_or, hR, hs, one_mul]

theorem aux_rem_resolved_microscopic_mfg_sign_mul_self (i j : Fin d) :
    coordinateReflectionSign {i} j * coordinateReflectionSign {i} j = 1 := by
  rw [← sq]; exact coordinateReflectionSign_sq _ _

/-- Upward fold, strictly below the new plane: the signed gradient is unchanged. -/
theorem aux_rem_resolved_microscopic_mfg_up_lt {z : SpatialCoordinates d}
    {J P : Finset (Fin d)} {i : Fin d} (hiJ : i ∉ J) (hiP : i ∈ P)
    (g : SpatialCoordinates d → ℝ) (j : Fin d) {x : SpatialCoordinates d} (hx : x i < z i) :
    aux_rem_resolved_microscopic_mf_sgn z (insert i J) P x *
        aux_rem_resolved_microscopic_mfg_fac z (insert i J) P j x *
        g (coordinateFold z (insert i J) P x) =
      aux_rem_resolved_microscopic_mf_sgn z J P x *
        aux_rem_resolved_microscopic_mfg_fac z J P j x * g (coordinateFold z J P x) := by
  have hf := aux_rem_resolved_microscopic_mfg_fac_keep (z := z) (P := P) hiJ x
    (by simp [coordinateReflectionSign, hiP, hx]) j
  have hs := aux_rem_resolved_microscopic_mf_up_le hiJ hiP g hx.le
  calc _ = aux_rem_resolved_microscopic_mfg_fac z (insert i J) P j x *
        (aux_rem_resolved_microscopic_mf_sgn z (insert i J) P x *
          g (coordinateFold z (insert i J) P x)) := by ring
    _ = aux_rem_resolved_microscopic_mfg_fac z J P j x *
        (aux_rem_resolved_microscopic_mf_sgn z J P x * g (coordinateFold z J P x)) := by
          rw [hf, hs]
    _ = _ := by ring

/-- Upward fold, strictly above the new plane. -/
theorem aux_rem_resolved_microscopic_mfg_up_gt {z : SpatialCoordinates d}
    {J P : Finset (Fin d)} {i : Fin d} (hiJ : i ∉ J) (hiP : i ∈ P)
    (g : SpatialCoordinates d → ℝ) (j : Fin d) {x : SpatialCoordinates d} (hx : z i < x i) :
    aux_rem_resolved_microscopic_mf_sgn z (insert i J) P x *
        aux_rem_resolved_microscopic_mfg_fac z (insert i J) P j x *
        g (coordinateFold z (insert i J) P x) =
      -(coordinateReflectionSign {i} j *
        (aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection z {i} x) *
          aux_rem_resolved_microscopic_mfg_fac z J P j (coordinateReflection z {i} x) *
          g (coordinateFold z J P (coordinateReflection z {i} x)))) := by
  have hnlt : ¬ x i < z i := not_lt.2 hx.le
  have hf := aux_rem_resolved_microscopic_mfg_fac_flip (z := z) (P := P) hiJ z x
    (by simp [coordinateReflectionSign, hiP, hnlt]) j
  have hs := aux_rem_resolved_microscopic_mf_up_gt hiJ hiP g hx
  calc _ = aux_rem_resolved_microscopic_mfg_fac z (insert i J) P j x *
        (aux_rem_resolved_microscopic_mf_sgn z (insert i J) P x *
          g (coordinateFold z (insert i J) P x)) := by ring
    _ = (coordinateReflectionSign {i} j *
          aux_rem_resolved_microscopic_mfg_fac z J P j (coordinateReflection z {i} x)) *
        -(aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection z {i} x) *
          g (coordinateFold z J P (coordinateReflection z {i} x))) := by rw [hf, hs]
    _ = _ := by ring

/-- Downward fold, strictly above the new plane: unchanged. -/
theorem aux_rem_resolved_microscopic_mfg_down_gt {z : SpatialCoordinates d}
    {J P : Finset (Fin d)} {i : Fin d} (hiJ : i ∉ J) (hiP : i ∉ P)
    (g : SpatialCoordinates d → ℝ) (j : Fin d) {x : SpatialCoordinates d} (hx : z i < x i) :
    aux_rem_resolved_microscopic_mf_sgn z (insert i J) P x *
        aux_rem_resolved_microscopic_mfg_fac z (insert i J) P j x *
        g (coordinateFold z (insert i J) P x) =
      aux_rem_resolved_microscopic_mf_sgn z J P x *
        aux_rem_resolved_microscopic_mfg_fac z J P j x * g (coordinateFold z J P x) := by
  have hnlt : ¬ x i < z i := not_lt.2 hx.le
  have hf := aux_rem_resolved_microscopic_mfg_fac_keep (z := z) (P := P) hiJ x
    (by simp [coordinateReflectionSign, hiP, hnlt]) j
  have hs := aux_rem_resolved_microscopic_mf_down_ge hiJ hiP g hx.le
  calc _ = aux_rem_resolved_microscopic_mfg_fac z (insert i J) P j x *
        (aux_rem_resolved_microscopic_mf_sgn z (insert i J) P x *
          g (coordinateFold z (insert i J) P x)) := by ring
    _ = aux_rem_resolved_microscopic_mfg_fac z J P j x *
        (aux_rem_resolved_microscopic_mf_sgn z J P x * g (coordinateFold z J P x)) := by
          rw [hf, hs]
    _ = _ := by ring

/-- Downward fold, strictly below the new plane. -/
theorem aux_rem_resolved_microscopic_mfg_down_lt {z : SpatialCoordinates d}
    {J P : Finset (Fin d)} {i : Fin d} (hiJ : i ∉ J) (hiP : i ∉ P)
    (g : SpatialCoordinates d → ℝ) (j : Fin d) {x : SpatialCoordinates d} (hx : x i < z i) :
    aux_rem_resolved_microscopic_mf_sgn z (insert i J) P x *
        aux_rem_resolved_microscopic_mfg_fac z (insert i J) P j x *
        g (coordinateFold z (insert i J) P x) =
      -(coordinateReflectionSign {i} j *
        (aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection z {i} x) *
          aux_rem_resolved_microscopic_mfg_fac z J P j (coordinateReflection z {i} x) *
          g (coordinateFold z J P (coordinateReflection z {i} x)))) := by
  have hf := aux_rem_resolved_microscopic_mfg_fac_flip (z := z) (P := P) hiJ z x
    (by simp [coordinateReflectionSign, hiP, hx]) j
  have hs := aux_rem_resolved_microscopic_mf_down_lt hiJ hiP g hx
  calc _ = aux_rem_resolved_microscopic_mfg_fac z (insert i J) P j x *
        (aux_rem_resolved_microscopic_mf_sgn z (insert i J) P x *
          g (coordinateFold z (insert i J) P x)) := by ring
    _ = (coordinateReflectionSign {i} j *
          aux_rem_resolved_microscopic_mfg_fac z J P j (coordinateReflection z {i} x)) *
        -(aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection z {i} x) *
          g (coordinateFold z J P (coordinateReflection z {i} x))) := by rw [hf, hs]
    _ = _ := by ring

/-- Gradient of the upward odd step. -/
theorem aux_rem_resolved_microscopic_mfg_grad_up (D : EvenReflectionDomain d)
    {z : SpatialCoordinates d} {J P : Finset (Fin d)}
    (hiJ : D.i ∉ J) (hiP : D.i ∈ P) (hz : z D.i = D.z D.i)
    (g : Fin d → SpatialCoordinates d → ℝ) (w : SobolevData D.Ω)
    (hwg : ∀ j : Fin d, (w.2 j : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.Ω : Set (SpatialCoordinates d))]
        fun x => aux_rem_resolved_microscopic_mf_sgn z J P x *
          aux_rem_resolved_microscopic_mfg_fac z J P j x * g j (coordinateFold z J P x))
    (j : Fin d) :
    ((D.oddExtension w).2 j : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.U : Set (SpatialCoordinates d))]
        fun x => aux_rem_resolved_microscopic_mf_sgn z (insert D.i J) P x *
          aux_rem_resolved_microscopic_mfg_fac z (insert D.i J) P j x *
          g j (coordinateFold z (insert D.i J) P x) := by
  have hRz : coordinateReflection z {D.i} = coordinateReflection D.z {D.i} :=
    coordinateReflection_single_congr z D.z D.i hz
  have hmp : MeasurePreserving (coordinateReflection D.z {D.i})
      (volume.restrict (D.reflected : Set (SpatialCoordinates d)))
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
  have hΩ : ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
      x ∈ (D.Ω : Set (SpatialCoordinates d)) →
        (w.2 j : SpatialCoordinates d → ℝ) x =
          aux_rem_resolved_microscopic_mf_sgn z J P x *
            aux_rem_resolved_microscopic_mfg_fac z J P j x * g j (coordinateFold z J P x) :=
    ae_restrict_of_ae ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp (hwg j))
  have hR0 : ∀ᵐ x ∂(volume.restrict (D.reflected : Set (SpatialCoordinates d))),
      (w.2 j : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x) =
        aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection D.z {D.i} x) *
          aux_rem_resolved_microscopic_mfg_fac z J P j (coordinateReflection D.z {D.i} x) *
          g j (coordinateFold z J P (coordinateReflection D.z {D.i} x)) :=
    hmp.quasiMeasurePreserving.ae (hwg j)
  have hR : ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
      x ∈ (D.reflected : Set (SpatialCoordinates d)) →
        (w.2 j : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x) =
          aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection D.z {D.i} x) *
            aux_rem_resolved_microscopic_mfg_fac z J P j (coordinateReflection D.z {D.i} x) *
            g j (coordinateFold z J P (coordinateReflection D.z {D.i} x)) :=
    ae_restrict_of_ae ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp hR0)
  filter_upwards [D.oddExtension_snd_coeFn w j, D.ae_mem_or_mem, hΩ, hR]
    with x h1 hmem h2 h3
  rw [h1]
  rcases hmem with hx | hx
  · rw [Set.indicator_of_mem hx,
      Set.indicator_of_notMem (D.notMem_reflected_of_mem_Ω hx), sub_zero, h2 hx,
      aux_rem_resolved_microscopic_mfg_up_lt hiJ hiP (g j) j
        (by rw [hz]; exact ((D.mem_iff x).mp hx).2)]
  · rw [Set.indicator_of_notMem (D.notMem_Ω_of_mem_reflected hx), Set.indicator_of_mem hx,
      zero_sub]
    rw [h3 hx, aux_rem_resolved_microscopic_mfg_up_gt hiJ hiP (g j) j
        (by rw [hz]; exact ((D.mem_reflected_iff x).mp hx).2), hRz]

/-- Gradient of the downward odd step. -/
theorem aux_rem_resolved_microscopic_mfg_grad_down (D : EvenReflectionDomain d)
    {z : SpatialCoordinates d} {J P : Finset (Fin d)}
    (hiJ : D.i ∉ J) (hiP : D.i ∉ P) (hz : z D.i = D.z D.i)
    (g : Fin d → SpatialCoordinates d → ℝ) (w : SobolevData D.reflected)
    (hwg : ∀ j : Fin d, (w.2 j : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.reflected : Set (SpatialCoordinates d))]
        fun x => aux_rem_resolved_microscopic_mf_sgn z J P x *
          aux_rem_resolved_microscopic_mfg_fac z J P j x * g j (coordinateFold z J P x))
    (j : Fin d) :
    ((-(D.oddExtension (reflectionSobolevData D.z {D.i} D.preimage_reflected w))).2 j :
        SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.U : Set (SpatialCoordinates d))]
        fun x => aux_rem_resolved_microscopic_mf_sgn z (insert D.i J) P x *
          aux_rem_resolved_microscopic_mfg_fac z (insert D.i J) P j x *
          g j (coordinateFold z (insert D.i J) P x) := by
  have hRz : coordinateReflection z {D.i} = coordinateReflection D.z {D.i} :=
    coordinateReflection_single_congr z D.z D.i hz
  have hneg : (((-(D.oddExtension (reflectionSobolevData D.z {D.i} D.preimage_reflected w))).2 j :
        DomainL2 D.U) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (D.U : Set (SpatialCoordinates d))]
        fun x => -(((D.oddExtension (reflectionSobolevData D.z {D.i} D.preimage_reflected w)).2 j :
          SpatialCoordinates d → ℝ) x) :=
    Lp.coeFn_neg _
  have hRg := reflectionSobolevData_gradient_coeFn D.z {D.i} D.preimage_reflected w j
  have hmpΩ : MeasurePreserving (coordinateReflection D.z {D.i})
      (volume.restrict (D.Ω : Set (SpatialCoordinates d)))
      (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_reflected
  have hmpR : MeasurePreserving (coordinateReflection D.z {D.i})
      (volume.restrict (D.reflected : Set (SpatialCoordinates d)))
      (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
    coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
  have hwR : ∀ᵐ x ∂(volume.restrict (D.Ω : Set (SpatialCoordinates d))),
      (w.2 j : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x) =
        aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection D.z {D.i} x) *
          aux_rem_resolved_microscopic_mfg_fac z J P j (coordinateReflection D.z {D.i} x) *
          g j (coordinateFold z J P (coordinateReflection D.z {D.i} x)) :=
    hmpΩ.quasiMeasurePreserving.ae (hwg j)
  have hRg' : ∀ᵐ x ∂(volume.restrict (D.reflected : Set (SpatialCoordinates d))),
      ((reflectionSobolevData D.z {D.i} D.preimage_reflected w).2 j : SpatialCoordinates d → ℝ)
          (coordinateReflection D.z {D.i} x) =
        coordinateReflectionSign {D.i} j * (w.2 j : SpatialCoordinates d → ℝ)
          (coordinateReflection D.z {D.i} (coordinateReflection D.z {D.i} x)) :=
    hmpR.quasiMeasurePreserving.ae hRg
  have hΩ1 := ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
    ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp hRg)
  have hΩ2 := ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
    ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp hwR)
  have hR1 := ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
    ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp hRg')
  have hR2 := ae_restrict_of_ae (s := (D.U : Set (SpatialCoordinates d)))
    ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp (hwg j))
  filter_upwards [hneg, D.oddExtension_snd_coeFn
      (reflectionSobolevData D.z {D.i} D.preimage_reflected w) j,
    D.ae_mem_or_mem, hΩ1, hΩ2, hR1, hR2] with x h0 h1 hmem h2 h3 h4 h5
  rw [h0, h1]
  rcases hmem with hx | hx
  · rw [Set.indicator_of_mem hx,
      Set.indicator_of_notMem (D.notMem_reflected_of_mem_Ω hx), sub_zero, h2 hx, h3 hx,
      aux_rem_resolved_microscopic_mfg_down_lt hiJ hiP (g j) j
        (by rw [hz]; exact ((D.mem_iff x).mp hx).2), hRz]
  · rw [Set.indicator_of_notMem (D.notMem_Ω_of_mem_reflected hx), Set.indicator_of_mem hx,
      zero_sub, neg_neg]
    rw [h4 hx, coordinateReflection_involutive D.z {D.i} x, ← mul_assoc,
      aux_rem_resolved_microscopic_mfg_sign_mul_self, one_mul, h5 hx,
      aux_rem_resolved_microscopic_mfg_down_gt hiJ hiP (g j) j
        (by rw [hz]; exact ((D.mem_reflected_iff x).mp hx).2)]

/-- **Upward multiface step with a scalar source.** -/
theorem aux_rem_resolved_microscopic_mfg_step_up (D : EvenReflectionDomain d)
    {B C : Opens (SpatialCoordinates d)} (hB : D.Ω = B) (hC : D.U = C)
    {z : SpatialCoordinates d} {J P : Finset (Fin d)}
    (hiJ : D.i ∉ J) (hiP : D.i ∈ P) (hz : z D.i = D.z D.i)
    (A F v0 : SpatialCoordinates d → ℝ)
    (a : PositiveCoefficient B) (w : SobolevData B) (hw : w ∈ killedSobolevGraph B)
    (ha : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))] foldedCoefficientP A z J P)
    (hwv : (w.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))]
        fun x => aux_rem_resolved_microscopic_mf_sgn z J P x * v0 (coordinateFold z J P x))
    (hS : MemLp (fun x => aux_rem_resolved_microscopic_mf_sgn z J P x *
        F (coordinateFold z J P x)) 2 (volume.restrict (B : Set (SpatialCoordinates d))))
    (hL : ∀ ψ ∈ killedSobolevGraph B, sobolevCoefficientForm a w ψ =
      ∫ x in (B : Set (SpatialCoordinates d)),
        aux_rem_resolved_microscopic_mf_sgn z J P x * F (coordinateFold z J P x) * ψ.1 x)
    (g : Fin d → SpatialCoordinates d → ℝ)
    (hwg : ∀ j : Fin d, (w.2 j : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))]
        fun x => aux_rem_resolved_microscopic_mf_sgn z J P x *
          aux_rem_resolved_microscopic_mfg_fac z J P j x * g j (coordinateFold z J P x)) :
    ∃ (a' : PositiveCoefficient C) (w' : SobolevData C), w' ∈ killedSobolevGraph C ∧
      ((a'.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (C : Set (SpatialCoordinates d))]
          foldedCoefficientP A z (insert D.i J) P) ∧
      ((w'.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (C : Set (SpatialCoordinates d))]
          fun x => aux_rem_resolved_microscopic_mf_sgn z (insert D.i J) P x *
            v0 (coordinateFold z (insert D.i J) P x)) ∧
      (∀ j : Fin d, (w'.2 j : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (C : Set (SpatialCoordinates d))]
          fun x => aux_rem_resolved_microscopic_mf_sgn z (insert D.i J) P x *
            aux_rem_resolved_microscopic_mfg_fac z (insert D.i J) P j x *
            g j (coordinateFold z (insert D.i J) P x)) ∧
      ∀ ψ ∈ killedSobolevGraph C, sobolevCoefficientForm a' w' ψ =
        ∫ x in (C : Set (SpatialCoordinates d)),
          aux_rem_resolved_microscopic_mf_sgn z (insert D.i J) P x *
            F (coordinateFold z (insert D.i J) P x) * ψ.1 x := by
  subst hB
  subst hC
  have hRz : coordinateReflection z {D.i} = coordinateReflection D.z {D.i} :=
    coordinateReflection_single_congr z D.z D.i hz
  refine ⟨D.evenExtensionCoefficient a, D.oddExtension w,
    _root_.SubdiffusiveProcess.EvenReflectionDomain.oddExtension_mem_killed D hw, ?_, ?_, ?_, ?_⟩
  · have h := evenExtensionCoefficient_fold_up D a hiJ hz ha
    rwa [Finset.insert_eq_of_mem hiP] at h
  · have hmp : MeasurePreserving (coordinateReflection D.z {D.i})
        (volume.restrict (D.reflected : Set (SpatialCoordinates d)))
        (volume.restrict (D.Ω : Set (SpatialCoordinates d))) :=
      coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_Ω
    have hΩ : ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
        x ∈ (D.Ω : Set (SpatialCoordinates d)) →
          (w.1 : SpatialCoordinates d → ℝ) x =
            aux_rem_resolved_microscopic_mf_sgn z J P x * v0 (coordinateFold z J P x) :=
      ae_restrict_of_ae ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp hwv)
    have hR0 : ∀ᵐ x ∂(volume.restrict (D.reflected : Set (SpatialCoordinates d))),
        (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x) =
          aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection D.z {D.i} x) *
            v0 (coordinateFold z J P (coordinateReflection D.z {D.i} x)) :=
      hmp.quasiMeasurePreserving.ae hwv
    have hR : ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
        x ∈ (D.reflected : Set (SpatialCoordinates d)) →
          (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x) =
            aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection D.z {D.i} x) *
              v0 (coordinateFold z J P (coordinateReflection D.z {D.i} x)) :=
      ae_restrict_of_ae ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp hR0)
    filter_upwards [D.oddExtension_fst_coeFn w, D.ae_mem_or_mem, hΩ, hR]
      with x h1 hmem h2 h3
    rw [h1]
    rcases hmem with hx | hx
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_notMem (D.notMem_reflected_of_mem_Ω hx), sub_zero, h2 hx,
        aux_rem_resolved_microscopic_mf_up_le hiJ hiP v0
          (by rw [hz]; exact ((D.mem_iff x).mp hx).2.le)]
    · rw [Set.indicator_of_notMem (D.notMem_Ω_of_mem_reflected hx), Set.indicator_of_mem hx,
        zero_sub, Function.comp_apply, h3 hx,
        aux_rem_resolved_microscopic_mf_up_gt hiJ hiP v0
          (by rw [hz]; exact ((D.mem_reflected_iff x).mp hx).2), hRz]
  · exact fun j => aux_rem_resolved_microscopic_mfg_grad_up D hiJ hiP hz g w hwg j
  · intro ψ hψ
    rw [aux_rem_resolved_microscopic_odd_step_scalar_source D a
      (fun x => aux_rem_resolved_microscopic_mf_sgn z J P x * F (coordinateFold z J P x))
      hS hL hψ]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only []
    rw [aux_rem_resolved_microscopic_mf_src_up D hiJ hiP hz F x]


/-- **Downward multiface step with a scalar source.** -/
theorem aux_rem_resolved_microscopic_mfg_step_down (D : EvenReflectionDomain d)
    {B C : Opens (SpatialCoordinates d)} (hB : D.reflected = B) (hC : D.U = C)
    {z : SpatialCoordinates d} {J P : Finset (Fin d)}
    (hiJ : D.i ∉ J) (hiP : D.i ∉ P) (hz : z D.i = D.z D.i)
    (A F v0 : SpatialCoordinates d → ℝ)
    (a : PositiveCoefficient B) (w : SobolevData B) (hw : w ∈ killedSobolevGraph B)
    (ha : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))] foldedCoefficientP A z J P)
    (hwv : (w.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))]
        fun x => aux_rem_resolved_microscopic_mf_sgn z J P x * v0 (coordinateFold z J P x))
    (hS : MemLp (fun x => aux_rem_resolved_microscopic_mf_sgn z J P x *
        F (coordinateFold z J P x)) 2 (volume.restrict (B : Set (SpatialCoordinates d))))
    (hL : ∀ ψ ∈ killedSobolevGraph B, sobolevCoefficientForm a w ψ =
      ∫ x in (B : Set (SpatialCoordinates d)),
        aux_rem_resolved_microscopic_mf_sgn z J P x * F (coordinateFold z J P x) * ψ.1 x)
    (g : Fin d → SpatialCoordinates d → ℝ)
    (hwg : ∀ j : Fin d, (w.2 j : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (B : Set (SpatialCoordinates d))]
        fun x => aux_rem_resolved_microscopic_mf_sgn z J P x *
          aux_rem_resolved_microscopic_mfg_fac z J P j x * g j (coordinateFold z J P x)) :
    ∃ (a' : PositiveCoefficient C) (w' : SobolevData C), w' ∈ killedSobolevGraph C ∧
      ((a'.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (C : Set (SpatialCoordinates d))]
          foldedCoefficientP A z (insert D.i J) P) ∧
      ((w'.1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (C : Set (SpatialCoordinates d))]
          fun x => aux_rem_resolved_microscopic_mf_sgn z (insert D.i J) P x *
            v0 (coordinateFold z (insert D.i J) P x)) ∧
      (∀ j : Fin d, (w'.2 j : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (C : Set (SpatialCoordinates d))]
          fun x => aux_rem_resolved_microscopic_mf_sgn z (insert D.i J) P x *
            aux_rem_resolved_microscopic_mfg_fac z (insert D.i J) P j x *
            g j (coordinateFold z (insert D.i J) P x)) ∧
      ∀ ψ ∈ killedSobolevGraph C, sobolevCoefficientForm a' w' ψ =
        ∫ x in (C : Set (SpatialCoordinates d)),
          aux_rem_resolved_microscopic_mf_sgn z (insert D.i J) P x *
            F (coordinateFold z (insert D.i J) P x) * ψ.1 x := by
  subst hB
  subst hC
  have hRz : coordinateReflection z {D.i} = coordinateReflection D.z {D.i} :=
    coordinateReflection_single_congr z D.z D.i hz
  refine ⟨D.evenExtensionCoefficient (reflectionCoefficient D.z {D.i} D.preimage_reflected a),
    -(D.oddExtension (reflectionSobolevData D.z {D.i} D.preimage_reflected w)),
    neg_mem (oddExtension_reflected_mem_killed D hw), ?_, ?_, ?_, ?_⟩
  · exact evenExtensionCoefficient_fold_down D a hiJ hiP hz ha
  · have hneg : ((((-(D.oddExtension (reflectionSobolevData D.z {D.i} D.preimage_reflected w))).1 :
          DomainL2 D.U) : SpatialCoordinates d → ℝ))
        =ᵐ[volume.restrict (D.U : Set (SpatialCoordinates d))]
          fun x => -(((D.oddExtension
            (reflectionSobolevData D.z {D.i} D.preimage_reflected w)).1 :
              SpatialCoordinates d → ℝ) x) :=
      Lp.coeFn_neg _
    have hmpΩ : MeasurePreserving (coordinateReflection D.z {D.i})
        (volume.restrict (D.Ω : Set (SpatialCoordinates d)))
        (volume.restrict (D.reflected : Set (SpatialCoordinates d))) :=
      coordinateReflection_domain_measurePreserving D.z {D.i} D.preimage_reflected
    -- lower (new) half: the odd extension is the pulled-back datum
    have hΩ1 : ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
        x ∈ (D.Ω : Set (SpatialCoordinates d)) →
          ((D.oddExtension (reflectionSobolevData D.z {D.i} D.preimage_reflected w)).1 :
              SpatialCoordinates d → ℝ) x =
            (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x) := by
      have e1 := D.oddExtension_ae_eq_on_Omega
        (reflectionSobolevData D.z {D.i} D.preimage_reflected w)
      have e2 : (((reflectionSobolevData D.z {D.i} D.preimage_reflected w).1 :
            DomainL2 D.Ω) : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (D.Ω : Set (SpatialCoordinates d))]
            (w.1 : SpatialCoordinates d → ℝ) ∘ coordinateReflection D.z {D.i} :=
        reflectionLp_coeFn D.z {D.i} D.preimage_reflected w.1
      have e3 := e1.trans e2
      exact ae_restrict_of_ae ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp e3)
    have hΩ2 : ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
        x ∈ (D.Ω : Set (SpatialCoordinates d)) →
          (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x) =
            aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection D.z {D.i} x) *
              v0 (coordinateFold z J P (coordinateReflection D.z {D.i} x)) := by
      have e : ∀ᵐ x ∂(volume.restrict (D.Ω : Set (SpatialCoordinates d))),
          (w.1 : SpatialCoordinates d → ℝ) (coordinateReflection D.z {D.i} x) =
            aux_rem_resolved_microscopic_mf_sgn z J P (coordinateReflection D.z {D.i} x) *
              v0 (coordinateFold z J P (coordinateReflection D.z {D.i} x)) :=
        hmpΩ.quasiMeasurePreserving.ae hwv
      exact ae_restrict_of_ae ((ae_restrict_iff' D.Ω.isOpen.measurableSet).mp e)
    -- upper (original) half: the extension is minus the datum
    have hR1 : ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
        x ∈ (D.reflected : Set (SpatialCoordinates d)) →
          ((D.oddExtension (reflectionSobolevData D.z {D.i} D.preimage_reflected w)).1 :
              SpatialCoordinates d → ℝ) x = -((w.1 : SpatialCoordinates d → ℝ) x) :=
      ae_restrict_of_ae ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp
        (D.oddExtension_reflected_ae_eq_neg w))
    have hR2 : ∀ᵐ x ∂(volume.restrict (D.U : Set (SpatialCoordinates d))),
        x ∈ (D.reflected : Set (SpatialCoordinates d)) →
          (w.1 : SpatialCoordinates d → ℝ) x =
            aux_rem_resolved_microscopic_mf_sgn z J P x * v0 (coordinateFold z J P x) :=
      ae_restrict_of_ae ((ae_restrict_iff' D.reflected.isOpen.measurableSet).mp hwv)
    filter_upwards [hneg, D.ae_mem_or_mem, hΩ1, hΩ2, hR1, hR2] with x h0 hmem h1 h2 h3 h4
    rw [h0]
    rcases hmem with hx | hx
    · rw [h1 hx, h2 hx, aux_rem_resolved_microscopic_mf_down_lt hiJ hiP v0
          (by rw [hz]; exact ((D.mem_iff x).mp hx).2), hRz]
    · rw [h3 hx, neg_neg, h4 hx, aux_rem_resolved_microscopic_mf_down_ge hiJ hiP v0
          (by rw [hz]; exact ((D.mem_reflected_iff x).mp hx).2.le)]
  · exact fun j => aux_rem_resolved_microscopic_mfg_grad_down D hiJ hiP hz g w hwg j
  · intro ψ hψ
    rw [aux_rem_resolved_microscopic_odd_step_down_scalar_source D a w
      (fun x => aux_rem_resolved_microscopic_mf_sgn z J P x * F (coordinateFold z J P x))
      hS hL hψ]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only []
    rw [aux_rem_resolved_microscopic_mf_src_down D hiJ hiP hz F x]




/-- **Multi-face odd reflection with a scalar source, on every partial fold.**  The
datum, coefficient and scalar source on the cube `foldedCube c r hr ∅ P` are carried to
`foldedCube c r hr J P` for every `J ⊆ I`, as `sgn_J · v ∘ fold_J`, `A ∘ fold_J` and
`sgn_J · F ∘ fold_J`, with the fold centre `foldedCubeCenter c r I P`. -/
theorem aux_rem_resolved_microscopic_mfg_induction (c : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (I P : Finset (Fin d)) (A F v0 : SpatialCoordinates d → ℝ)
    (hFm : Measurable F) (M : ℝ) (hFM : ∀ y, |F y| ≤ M)
    (Q0 : Opens (SpatialCoordinates d)) (hQ0 : Q0 = foldedCube c r hr ∅ P)
    (a : PositiveCoefficient Q0) (w : SobolevData Q0) (hw : w ∈ killedSobolevGraph Q0)
    (ha : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q0 : Set (SpatialCoordinates d))] A)
    (hwv : (w.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q0 : Set (SpatialCoordinates d))] v0)
    (hL : ∀ ψ ∈ killedSobolevGraph Q0, sobolevCoefficientForm a w ψ =
      ∫ x in (Q0 : Set (SpatialCoordinates d)), F x * ψ.1 x)
    (g : Fin d → SpatialCoordinates d → ℝ)
    (hwg : ∀ j : Fin d, (w.2 j : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q0 : Set (SpatialCoordinates d))] g j) :
    ∀ J : Finset (Fin d), J ⊆ I →
      ∃ (aJ : PositiveCoefficient (foldedCube c r hr J P))
        (wJ : SobolevData (foldedCube c r hr J P)),
        wJ ∈ killedSobolevGraph (foldedCube c r hr J P) ∧
        ((aJ.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (foldedCube c r hr J P : Set (SpatialCoordinates d))]
            foldedCoefficientP A (foldedCubeCenter c r I P) J P) ∧
        ((wJ.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (foldedCube c r hr J P : Set (SpatialCoordinates d))]
            fun x => aux_rem_resolved_microscopic_mf_sgn (foldedCubeCenter c r I P) J P x *
              v0 (coordinateFold (foldedCubeCenter c r I P) J P x)) ∧
        (∀ j : Fin d, (wJ.2 j : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (foldedCube c r hr J P : Set (SpatialCoordinates d))]
            fun x => aux_rem_resolved_microscopic_mf_sgn (foldedCubeCenter c r I P) J P x *
              aux_rem_resolved_microscopic_mfg_fac (foldedCubeCenter c r I P) J P j x *
              g j (coordinateFold (foldedCubeCenter c r I P) J P x)) ∧
        ∀ ψ ∈ killedSobolevGraph (foldedCube c r hr J P), sobolevCoefficientForm aJ wJ ψ =
          ∫ x in (foldedCube c r hr J P : Set (SpatialCoordinates d)),
            aux_rem_resolved_microscopic_mf_sgn (foldedCubeCenter c r I P) J P x *
              F (coordinateFold (foldedCubeCenter c r I P) J P x) * ψ.1 x := by
  subst hQ0
  intro J
  induction J using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨a, w, hw, ?_, ?_, ?_, ?_⟩
    · rw [foldedCoefficientP_empty]
      exact ha
    · filter_upwards [hwv] with x hx
      rw [hx, aux_rem_resolved_microscopic_mf_sgn_empty, fold_empty, one_mul]
    · intro j
      filter_upwards [hwg j] with x hx
      rw [hx, aux_rem_resolved_microscopic_mf_sgn_empty, aux_rem_resolved_microscopic_mfg_fac_empty,
        fold_empty, one_mul, one_mul]
    · intro ψ hψ
      rw [hL ψ hψ]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [aux_rem_resolved_microscopic_mf_sgn_empty, fold_empty, one_mul]
  | @insert i J hiJ ih =>
    intro hsub
    have hiI : i ∈ I := hsub (Finset.mem_insert_self i J)
    have hIH := ih ((Finset.subset_insert i J).trans hsub)
    rcases hIH with ⟨aJ, wJ, hwJ, haJ, hwvJ, hwgJ, hLJ⟩
    have hS := aux_rem_resolved_microscopic_mf_memLp c r hr (foldedCubeCenter c r I P) J P F
      hFm M hFM
    by_cases hiP : i ∈ P
    · exact aux_rem_resolved_microscopic_mfg_step_up
        (boxEvenReflectionDomain (aux_rem_resolved_microscopic_mf_lo c r J P)
          (aux_rem_resolved_microscopic_mf_hi c r J P) i)
        (aux_rem_resolved_microscopic_mf_box c r hr J P).symm
        (aux_rem_resolved_microscopic_mf_up_U c r hr hiJ hiP) hiJ hiP
        (aux_rem_resolved_microscopic_mf_up_z c r hiI hiJ hiP) A F v0 aJ wJ hwJ haJ hwvJ
        hS hLJ g hwgJ
    · exact aux_rem_resolved_microscopic_mfg_step_down
        (boxEvenReflectionDomain
          (lowerDoubledCorner (aux_rem_resolved_microscopic_mf_lo c r J P)
            (aux_rem_resolved_microscopic_mf_hi c r J P) i)
          (Function.update (aux_rem_resolved_microscopic_mf_hi c r J P) i
            (aux_rem_resolved_microscopic_mf_lo c r J P i)) i)
        ((boxEvenReflectionDomain_mirror_reflected _ _ i).trans
          (aux_rem_resolved_microscopic_mf_box c r hr J P).symm)
        (aux_rem_resolved_microscopic_mf_down_U c r hr hiJ hiP) hiJ hiP
        (aux_rem_resolved_microscopic_mf_down_z c r hiI hiJ hiP) A F v0 aJ wJ hwJ haJ hwvJ
        hS hLJ g hwgJ


/-- **Multi-face odd reflection with a scalar source.**  A killed solution `v` of
`E_a(v, ψ) = ∫_Q F ψ` (all killed `ψ`) on the cube `Q = centeredCube c r hr`, with `F`
measurable and bounded on `Q`, is carried to the exact folded cube
`V = foldedCube c r hr I P`: coefficient `A ∘ T`, datum `sgn · v ∘ T`, source
`sgn · F ∘ T`, where `T = coordinateFold (foldedCubeCenter c r I P) I P`. -/
theorem aux_rem_resolved_microscopic_mfg_multiface_scalar (c : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (I P : Finset (Fin d)) (A F : SpatialCoordinates d → ℝ)
    (a : PositiveCoefficient (centeredCube c r hr))
    (ha : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube c r hr : Set (SpatialCoordinates d))] A)
    (v : SobolevData (centeredCube c r hr))
    (hv : v ∈ killedSobolevGraph (centeredCube c r hr))
    (hFm : Measurable F) (M : ℝ)
    (hFM : ∀ y ∈ (centeredCube c r hr : Set (SpatialCoordinates d)), |F y| ≤ M)
    (hL : ∀ ψ ∈ killedSobolevGraph (centeredCube c r hr), sobolevCoefficientForm a v ψ =
      ∫ x in (centeredCube c r hr : Set (SpatialCoordinates d)), F x * ψ.1 x) :
    ∃ (af : PositiveCoefficient (foldedCube c r hr I P))
      (vf : weakSobolevGraph (foldedCube c r hr I P)),
      ((af.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (foldedCube c r hr I P : Set (SpatialCoordinates d))]
          fun x => A (coordinateFold (foldedCubeCenter c r I P) I P x)) ∧
      (((vf : SobolevData (foldedCube c r hr I P)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (foldedCube c r hr I P : Set (SpatialCoordinates d))]
          fun x => aux_rem_resolved_microscopic_mf_sgn (foldedCubeCenter c r I P) I P x *
            v.1 (coordinateFold (foldedCubeCenter c r I P) I P x)) ∧
      (∀ j : Fin d,
        ∀ᵐ x ∂volume.restrict (foldedCube c r hr I P : Set (SpatialCoordinates d)),
          sobolevGradient (vf : SobolevData (foldedCube c r hr I P)) j x =
            aux_rem_resolved_microscopic_mf_sgn (foldedCubeCenter c r I P) I P x *
              ((if j ∈ I then
                coordinateReflectionSign P j *
                  (if x j < foldedCubeCenter c r I P j then -1 else 1)
               else 1) *
              sobolevGradient v j (coordinateFold (foldedCubeCenter c r I P) I P x))) ∧
      ∀ ψ : killedSobolevGraph (foldedCube c r hr I P),
        sobolevCoefficientForm af (vf : SobolevData (foldedCube c r hr I P))
            (ψ : SobolevData (foldedCube c r hr I P)) =
          ∫ x in (foldedCube c r hr I P : Set (SpatialCoordinates d)),
            aux_rem_resolved_microscopic_mf_sgn (foldedCubeCenter c r I P) I P x *
              F (coordinateFold (foldedCubeCenter c r I P) I P x) *
                (ψ : SobolevData (foldedCube c r hr I P)).1 x := by
  have hmQ : MeasurableSet (centeredCube c r hr : Set (SpatialCoordinates d)) :=
    (centeredCube c r hr).isOpen.measurableSet
  have hF'm : Measurable ((centeredCube c r hr : Set (SpatialCoordinates d)).indicator F) :=
    hFm.indicator hmQ
  have hF'M : ∀ y, |(centeredCube c r hr : Set (SpatialCoordinates d)).indicator F y| ≤
      max M 0 := by
    intro y
    by_cases hy : y ∈ (centeredCube c r hr : Set (SpatialCoordinates d))
    · rw [Set.indicator_of_mem hy]
      exact (hFM y hy).trans (le_max_left _ _)
    · rw [Set.indicator_of_notMem hy, abs_zero]
      exact le_max_right _ _
  have hL' : ∀ ψ ∈ killedSobolevGraph (centeredCube c r hr), sobolevCoefficientForm a v ψ =
      ∫ x in (centeredCube c r hr : Set (SpatialCoordinates d)),
        (centeredCube c r hr : Set (SpatialCoordinates d)).indicator F x * ψ.1 x := by
    intro ψ hψ
    rw [hL ψ hψ]
    refine setIntegral_congr_fun hmQ (fun x hx => ?_)
    simp only [Set.indicator_of_mem hx]
  have hind := aux_rem_resolved_microscopic_mfg_induction c r hr I P A
    ((centeredCube c r hr : Set (SpatialCoordinates d)).indicator F)
    (v.1 : SpatialCoordinates d → ℝ) hF'm (max M 0) hF'M (centeredCube c r hr)
    (aux_rem_resolved_microscopic_mf_cube_eq c r hr P) a v hv ha
    (Filter.EventuallyEq.refl _ _) hL' (fun j => ((v.2 j : DomainL2 (centeredCube c r hr)) :
      SpatialCoordinates d → ℝ)) (fun j => Filter.EventuallyEq.refl _ _) I (Finset.Subset.refl I)
  rcases hind with ⟨aI, wI, hwI, haI, hwvI, hwgI, hLI⟩
  refine ⟨aI, ⟨wI, killedSobolevGraph_le_weakSobolevGraph hwI⟩, haI, hwvI, fun j => ?_, fun ψ => ?_⟩
  · filter_upwards [hwgI j] with x hx
    change (wI.2 j : SpatialCoordinates d → ℝ) x = _
    rw [hx]
    unfold aux_rem_resolved_microscopic_mfg_fac
    change _ = _ * (_ * (v.2 j : SpatialCoordinates d → ℝ) _)
    ring
  rw [hLI ψ ψ.2]
  refine integral_congr_ae ?_
  filter_upwards [aux_rem_resolved_microscopic_mf_fold_mem_ae c r hr I P] with x hx
  simp only [Set.indicator_of_mem hx]

end DirichletGradientFold

section DirichletCoreHelpers



/-!
# The Dirichlet one-centre core

`aux_rem_resolved_microscopic_neumann_core`, rerun on the ODD multi-face fold: the interior
estimate is applied to the odd fold with the killed-test equation and a general bounded source
`F`; the energy comparisons (`_neumann_lower`, `_neumann_fold_energy`) are applied to the EVEN
fold of the same `u` and transferred, since the two folds have equal squared gradients
(`sgn² = 1`).  The source term keeps `a₀⁻¹ = (A x)⁻¹`.
-/

theorem aux_rem_resolved_microscopic_dir_interior {d : ℕ} (W : SmallPerturbationInput d)
    (p1 : ℝ) (hp1 : 2 ≤ p1) {U : Opens (SpatialCoordinates d)} (x : SpatialCoordinates d)
    (l : ℝ) (hl : 0 < 4 * l) (hSub : centeredCube x (4 * l) hl ≤ U)
    (af : PositiveCoefficient U) (vf : weakSobolevGraph U) (F : SpatialCoordinates d → ℝ)
    (hweak : ∀ ψ : killedSobolevGraph U,
      sobolevCoefficientForm af (vf : SobolevData U) (ψ : SobolevData U) =
        ∫ y in (U : Set (SpatialCoordinates d)), F y * (ψ : SobolevData U).1 y)
    (a0 : ℝ) (ha0 : 0 < a0)
    (hosc : ∀ᵐ y ∂volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d)),
      |Real.log (af.val y) - Real.log a0| ≤ W.osc p1)
    (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFmeas : AEMeasurable F
      (volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d))))
    (hFbd : ∀ᵐ y ∂volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d)),
      |F y| ≤ Kf) :
    MemLp (fun y => Real.sqrt (∑ i : Fin d,
          ((sobolevGradient (sobolevDataRestrict hSub (vf : SobolevData U))) i y) ^ 2))
        (ENNReal.ofReal p1)
        ((volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d))).restrict
          (Metric.ball x l)) ∧
      normalizedGradientLpNorm (ENNReal.ofReal p1) (Metric.ball x l)
          (sobolevGradient (sobolevDataRestrict hSub (vf : SobolevData U))) ≤
        W.C p1 * normalizedGradientLpNorm 2 (Metric.ball x (2 * l))
            (sobolevGradient (sobolevDataRestrict hSub (vf : SobolevData U))) +
          W.C p1 * l * a0⁻¹ * Kf := by
  set as := positiveCoefficientRestrict hSub af
  have hosc' : ∀ᵐ y ∂volume.restrict (centeredCube x (4 * l) hl : Set (SpatialCoordinates d)),
      |Real.log (as.val y) - Real.log a0| ≤ W.osc p1 := by
    filter_upwards [positiveCoefficientRestrict_coeFn hSub af, hosc] with y h1 h2
    rw [h1]; exact h2
  have hweak_s : ∀ φ : killedSobolevGraph (centeredCube x (4 * l) hl),
      sobolevCoefficientForm as (sobolevDataRestrict hSub (vf : SobolevData U))
          (φ : SobolevData (centeredCube x (4 * l) hl)) =
        ∫ y in (centeredCube x (4 * l) hl : Set (SpatialCoordinates d)),
          F y * (φ : SobolevData (centeredCube x (4 * l) hl)).1 y := by
    intro φ
    have hψ := zeroExtensionSobolevData_mem_killed hSub φ.2
    have h1 := hweak ⟨_, hψ⟩
    have h2 := sobolevCoefficientForm_zeroExtension hSub af as
      (positiveCoefficientRestrict_coeFn hSub af).symm
      (φ : SobolevData (centeredCube x (4 * l) hl)) (vf : SobolevData U)
    calc sobolevCoefficientForm as (sobolevDataRestrict hSub (vf : SobolevData U))
          (φ : SobolevData (centeredCube x (4 * l) hl))
        = sobolevCoefficientForm as (φ : SobolevData (centeredCube x (4 * l) hl))
            (sobolevDataRestrict hSub (vf : SobolevData U)) := sobolevCoefficientForm_symm _ _ _
      _ = sobolevCoefficientForm af
            (zeroExtensionSobolevData hSub (φ : SobolevData (centeredCube x (4 * l) hl)))
            (vf : SobolevData U) := h2.symm
      _ = sobolevCoefficientForm af (vf : SobolevData U)
            (zeroExtensionSobolevData hSub (φ : SobolevData (centeredCube x (4 * l) hl))) :=
          sobolevCoefficientForm_symm _ _ _
      _ = ∫ y in (U : Set (SpatialCoordinates d)), F y *
            zeroExtensionLp hSub (φ : SobolevData (centeredCube x (4 * l) hl)).1 y := h1
      _ = _ := integral_mul_zeroExtensionLp hSub F _
  exact W.interior_gradient p1 hp1 x l hl as a0 ha0 hosc' F Kf hFmeas hKf hFbd
    ⟨sobolevDataRestrict hSub (vf : SobolevData U), sobolevDataRestrict_mem_weak hSub vf.2⟩
    hweak_s

/-- The odd and even folds of the same `u` have equal squared gradients (`sgn² = 1`), hence
equal gradient energies on every subset of the folded cube. -/
theorem aux_rem_resolved_microscopic_dir_transfer {d : ℕ} (I P : Finset (Fin d))
    (u : weakSobolevGraph (unitNeumannCube d))
    (vf vfe : weakSobolevGraph (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P))
    (hg : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)),
        sobolevGradient (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)) j x =
          aux_rem_resolved_microscopic_mf_sgn (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P x *
            ((if j ∈ I then
              coordinateReflectionSign P j *
                (if x j < foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P j then -1 else 1)
             else 1) *
            sobolevGradient (u : SobolevData (unitNeumannCube d)) j
              (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P x)))
    (hge : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)),
        sobolevGradient (vfe : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)) j x =
          (if j ∈ I then
            coordinateReflectionSign P j *
              (if x j < foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P j then -1 else 1)
           else 1) *
            sobolevGradient (u : SobolevData (unitNeumannCube d)) j
              (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P x)) :
    ∀ S : Set (SpatialCoordinates d), S ⊆ (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)) →
      ∫ y in S, ∑ i : Fin d, ((vfe : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y) ^ 2 =
        ∫ y in S, ∑ i : Fin d, ((vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y) ^ 2 := by
  have hsq : ∀ᵐ y ∂volume.restrict (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)),
      ∑ i : Fin d, ((vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y) ^ 2 =
        ∑ i : Fin d, ((vfe : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y) ^ 2 := by
    have hall := ae_all_iff.2 hg
    have halle := ae_all_iff.2 hge
    filter_upwards [hall, halle] with y h1 h2
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 := h1 i
    have e2 := h2 i
    change ((vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i : SpatialCoordinates d → ℝ) y = _ at e1
    change ((vfe : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i : SpatialCoordinates d → ℝ) y = _ at e2
    rw [e1, e2, mul_pow]
    have hs2 : (aux_rem_resolved_microscopic_mf_sgn (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y) ^ 2 = 1 := by
      rw [← sq_abs, aux_rem_resolved_microscopic_mf_abs_sgn, one_pow]
    rw [hs2, one_mul]
  intro S hS
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hS hsq] with y hy
  exact hy.symm

theorem aux_rem_resolved_microscopic_dir_core {d : ℕ} (W : SmallPerturbationInput d)
    (p1 : ℝ) (hp1 : 2 ≤ p1) (I P : Finset (Fin d)) (C c : ℝ)
    (hcosc : c ≤ W.osc p1)
    (hC1 : 2 * W.C p1 ^ 2 * Real.exp c ^ 2 ≤ C) (hC2 : W.C p1 ^ 2 * Real.exp c / 2 ≤ C)
    (a : PositiveCoefficient (unitNeumannCube d)) (A : SpatialCoordinates d → ℝ)
    (hAc : Continuous A)
    (haA : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (mN MN : ℝ) (hmN : 0 < mN)
    (hAQ : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN)
    (u : weakSobolevGraph (unitNeumannCube d))
    (af : PositiveCoefficient (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P))
    (vf : weakSobolevGraph (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P))
    (haf : ((af.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d))]
      fun x => A (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P x)))
    (hg : ∀ j : Fin d,
      ∀ᵐ x ∂volume.restrict (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)),
        sobolevGradient (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)) j x =
          aux_rem_resolved_microscopic_mf_sgn (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P x *
            ((if j ∈ I then
              coordinateReflectionSign P j *
                (if x j < foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P j then -1 else 1)
             else 1) *
            sobolevGradient (u : SobolevData (unitNeumannCube d)) j (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P x)))
    (F : SpatialCoordinates d → ℝ) (hFm : Measurable F)
    (hweak : ∀ ψ : killedSobolevGraph (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P),
      sobolevCoefficientForm af (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P))
          (ψ : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)) =
        ∫ y in (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)),
          F y * (ψ : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).1 y)
    (x : SpatialCoordinates d) (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (ell : ℝ) (hell : 0 < ell)
    (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFbd : ∀ᵐ y ∂volume.restrict (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)), dist y x < ell → |F y| ≤ Kf)
    (hmodQ : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), dist y x ≤ ell →
      |Real.log (A y) - Real.log (A x)| ≤ c)
    (hUball : ∀ y, dist y x < ell →
      y ∈ (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)))
    (Bx : Set (SpatialCoordinates d)) (hB : MeasurableSet Bx)
    (hBU : Bx ⊆ (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)))
    (hBs : ∀ J : Finset (Fin d), J ⊆ I →
      coordinateReflection (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) J ⁻¹' Bx = Bx)
    (hballB : ∀ y, dist y x < ell → y ∈ Bx) (rho : ℝ)
    (hBS : Bx ⊆ {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < rho / 2})
    (r : ℝ) (hr : 0 < r) (hrell : r ≤ ell) :
    ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩
        (unitNeumannCube d : Set (SpatialCoordinates d)),
        A y * ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2 ≤
      C * (r / ell) ^ ((d : ℝ) - 2 * (d : ℝ) / p1) *
          (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < rho / 2} ∩
            (unitNeumannCube d : Set (SpatialCoordinates d)),
            A y * ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2) +
        C * (A x)⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) *
          r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) := by
  have hQmeas : MeasurableSet (unitNeumannCube d : Set (SpatialCoordinates d)) :=
    (unitNeumannCube d).isOpen.measurableSet
  have ha0 : 0 < A x := hmN.trans_le (hAQ x hx).1
  have hAb : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), 0 ≤ A y ∧ A y ≤ MN :=
    fun y hy => ⟨hmN.le.trans (hAQ y hy).1, (hAQ y hy).2⟩
  have hfe := lem_even_fold_construction d (fun _ => (1 / 2 : ℝ)) 1 one_pos I P a u
  rcases hfe with ⟨afe, vfe, hafe, _hvfe, hge⟩
  have htransfer := aux_rem_resolved_microscopic_dir_transfer I P u vf vfe hg hge
  have hl : 0 < 4 * (ell / 2) := by positivity
  have hSubball : ∀ y, y ∈ (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)) ↔
      dist y x < ell := by
    intro y
    change y ∈ Metric.ball x (4 * (ell / 2) / 2) ↔ _
    rw [Metric.mem_ball, show 4 * (ell / 2) / 2 = ell by ring]
  have hSubset : (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)) ⊆
      (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)) :=
    fun y hy => hUball y ((hSubball y).1 hy)
  have hSub : centeredCube x (4 * (ell / 2)) hl ≤ foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P :=
    hSubset
  have hSubmeas : MeasurableSet (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)) :=
    (centeredCube x (4 * (ell / 2)) hl).isOpen.measurableSet
  -- almost-every pullbacks through the actual fold
  have hTa := aux_rem_resolved_microscopic_neumann_fold_ae d (fun _ => (1 / 2 : ℝ)) 1 one_pos I P haA
  have hTx : coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P x = x :=
    aux_rem_resolved_microscopic_neumann_fold_id I P hx
  have hlogSub : ∀ᵐ y ∂volume.restrict
      (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)),
      af.val y = A (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y) ∧
      0 < A (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y) ∧
      |Real.log (A (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y)) -
        Real.log (A x)| ≤ c := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hSubset haf,
      ae_restrict_of_ae_restrict_of_subset hSubset hTa, ae_restrict_mem hSubmeas] with y h1 h2 hy
    refine ⟨h1, hmN.trans_le (hAQ _ h2.2).1, hmodQ _ h2.2 ?_⟩
    calc dist (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y) x
        = dist (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P y)
            (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P) I P x) := by rw [hTx]
      _ ≤ dist y x := coordinateFold_nonexpansive _ I P y x
      _ ≤ ell := ((hSubball y).1 hy).le
  have hosc : ∀ᵐ y ∂volume.restrict
      (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)),
      |Real.log (af.val y) - Real.log (A x)| ≤ W.osc p1 :=
    hlogSub.mono fun y h => by rw [h.1]; exact h.2.2.trans hcosc
  have hlow : ∀ᵐ y ∂volume.restrict
      (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)),
      A x ≤ Real.exp c * afe.val y := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hSubset hafe,
      ae_restrict_of_ae_restrict_of_subset hSubset hTa, hlogSub] with y h1 h2 h3
    erw [h1, h2.1]; exact (aux_rem_resolved_microscopic_neumann_exp_of_log h3.2.1 ha0 h3.2.2).1
  have hFmeas : AEMeasurable F
      (volume.restrict (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d))) :=
    hFm.aemeasurable
  have hFbd' : ∀ᵐ y ∂volume.restrict
      (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)), |F y| ≤ Kf := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hSubset hFbd,
      ae_restrict_mem hSubmeas] with y h hy
    exact h ((hSubball y).1 hy)
  have hint := aux_rem_resolved_microscopic_dir_interior W p1 hp1 x (ell / 2) hl
    hSub af vf F hweak (A x) ha0 hosc Kf hKf hFmeas hFbd'
  rcases hint with ⟨hmem, hest⟩
  -- the small cube `S_r`
  have hSr_eq := aux_rem_resolved_microscopic_neumann_cube_eq_ball x (half_pos hr)
  have hSrmeas : MeasurableSet {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} :=
    aux_rem_resolved_microscopic_neumann_cube_measurable x _
  have hSrB : {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ⊆
      Metric.ball x (ell / 2) := by
    rw [hSr_eq]; exact Metric.ball_subset_ball (by linarith)
  have hSrU : {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ⊆
      (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P : Set (SpatialCoordinates d)) :=
    fun y hy => hUball y (lt_of_lt_of_le (hSrB hy) (by linarith))
  have hSrfin : volume {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ≠ ∞ := by
    rw [hSr_eq, Real.volume_pi_ball x (half_pos hr)]; exact ENNReal.ofReal_ne_top
  have hSrvol : volume.real {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} =
      r ^ d := by
    rw [hSr_eq, aux_rem_resolved_microscopic_neumann_ball_volume_real x (half_pos hr)]
    congr 1; ring
  have hup : ∀ y ∈ {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩
      (unitNeumannCube d : Set (SpatialCoordinates d)), A y ≤ Real.exp c * A x := by
    intro y hy
    have hyd : dist y x ≤ ell := by
      have := hSrB hy.1
      rw [Metric.mem_ball] at this; linarith
    exact (aux_rem_resolved_microscopic_neumann_exp_of_log (hmN.trans_le (hAQ y hy.2).1) ha0
      (hmodQ y hy.2 hyd)).2
  have hL1 := aux_rem_resolved_microscopic_neumann_lower I P A MN hAb u vfe hge
    {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} hSrmeas hSrU
    (Real.exp c * A x) (by positivity) hup
  rw [htransfer _ hSrU] at hL1
  have hH := aux_rem_resolved_microscopic_neumann_holder_chain p1 hp1 x (ell / 2) hl hSub vf
    {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} hSrmeas hSrB hSrfin hmem
  have hballvol : volume.real (Metric.ball x (ell / 2)) = ell ^ d := by
    rw [aux_rem_resolved_microscopic_neumann_ball_volume_real x (by positivity)]; congr 1; ring
  have hEp := aux_rem_resolved_microscopic_neumann_normalized_p (ENNReal.ofReal p1)
    (Metric.ball x (ell / 2)) (sobolevGradient (sobolevDataRestrict hSub
      (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P))))
    (by rw [hballvol]; positivity)
  rw [hballvol, ENNReal.toReal_ofReal (by linarith)] at hEp
  have hN2 := aux_rem_resolved_microscopic_neumann_normalized_two x (ell / 2) hl hSub vf
  have hball2vol : volume.real (Metric.ball x (2 * (ell / 2))) = 2 ^ d * ell ^ d := by
    rw [aux_rem_resolved_microscopic_neumann_ball_volume_real x (by positivity), ← mul_pow]
    congr 1; ring
  rw [hball2vol] at hN2
  have hrhomeas := aux_rem_resolved_microscopic_neumann_cube_measurable x (rho / 2)
  have hFE := aux_rem_resolved_microscopic_neumann_fold_energy I P a A hAc MN haA hAb u afe vfe hafe hge
    Bx hB hBU hBs (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d))
    {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < rho / 2}
    (fun y hy => hballB y ((hSubball y).1 hy)) hBS hrhomeas (Real.exp c) (A x) ha0
    (Real.exp_pos c).le hlow
  rw [htransfer _ hSubset] at hFE
  -- names for the scalars
  set G := ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < rho / 2} ∩
      (unitNeumannCube d : Set (SpatialCoordinates d)),
      A y * ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2 with hGdef
  have hG : 0 ≤ G := by
    refine setIntegral_nonneg (hrhomeas.inter hQmeas) fun y hy => ?_
    exact mul_nonneg (hAb y hy.2).1 (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hN2' : (normalizedGradientLpNorm 2 (Metric.ball x (2 * (ell / 2)))
        (sobolevGradient (sobolevDataRestrict hSub
          (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P))))) ^ 2 ≤
      Real.exp c * G / (A x * ell ^ d) := by
    rw [hN2]
    have hpos : 0 < 2 ^ d * ell ^ d := by positivity
    rw [div_le_div_iff₀ hpos (by positivity)]
    have hFE' : ∫ y in (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)),
        ∑ i : Fin d, ((vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y) ^ 2
          ≤ Real.exp c / A x * 2 ^ d * G := hFE
    calc (∫ y in (centeredCube x (4 * (ell / 2)) hl : Set (SpatialCoordinates d)),
          ∑ i : Fin d,
            ((vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)).2 i y) ^ 2) *
          (A x * ell ^ d)
        ≤ (Real.exp c / A x * 2 ^ d * G) * (A x * ell ^ d) :=
          mul_le_mul_of_nonneg_right hFE' (by positivity)
      _ = Real.exp c * G * (2 ^ d * ell ^ d) := by field_simp
  have hNp1 : 0 ≤ normalizedGradientLpNorm (ENNReal.ofReal p1) (Metric.ball x (ell / 2))
      (sobolevGradient (sobolevDataRestrict hSub
        (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P)))) := by
    unfold normalizedGradientLpNorm
    exact div_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg measureReal_nonneg _)
  have h1 : ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩
        (unitNeumannCube d : Set (SpatialCoordinates d)),
        A y * ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2 ≤
      Real.exp c * A x * ((r ^ d) ^ (1 - 2 / p1) *
        ((normalizedGradientLpNorm (ENNReal.ofReal p1) (Metric.ball x (ell / 2))
          (sobolevGradient (sobolevDataRestrict hSub
            (vf : SobolevData (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P))))) ^ 2 *
          ((ell ^ d) ^ (1 / p1)) ^ 2)) := by
    refine hL1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine hH.trans (le_of_eq ?_)
    rw [hSrvol, hEp]; ring
  have hcomb := aux_rem_resolved_microscopic_neumann_combine _ G (Real.exp c) (A x) (A x) (W.C p1) Kf
    _ _ ((r ^ d) ^ (1 - 2 / p1)) (((ell ^ d) ^ (1 / p1)) ^ 2) (ell ^ d) ell C
    (Real.exp_pos c).le ha0 ha0 le_rfl
    (Real.rpow_nonneg (by positivity) _) (sq_nonneg _) (by positivity) hG h1 hNp1 hest hN2' hC1 hC2
  obtain ⟨hid1, hid2⟩ := aux_rem_resolved_microscopic_neumann_rpow_ident d p1 r ell hr hell
  rw [hid1, hid2] at hcomb
  refine hcomb.trans (le_of_eq ?_)
  ring

end DirichletCoreHelpers

section DirichletLocalFluxHelpers
open scoped ContDiff



/-- Pointwise flux bound from pointwise control of the line derivatives. -/
theorem aux_rem_resolved_microscopic_dir_fluxDiv_bound_pt {d : ℕ}
    (At h : SpatialCoordinates d → ℝ) (y : SpatialCoordinates d) (L MA Kg Kh2 : ℝ)
    (hL0 : 0 ≤ L) (hMA0 : 0 ≤ MA)
    (hL : ∀ i : Fin d, |lineDeriv ℝ At y (Pi.single i 1)| ≤ L)
    (hA : |At y| ≤ MA) (hg : ‖fderiv ℝ h y‖ ≤ Kg)
    (hh2 : ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ Kh2) :
    |aux_remResolvedMicroscopicFluxDiv At h y| ≤ (d : ℝ) * (L * Kg + MA * Kh2) := by
  unfold aux_remResolvedMicroscopicFluxDiv
  have hsingle : ∀ i : Fin d, ‖(Pi.single i (1 : ℝ) : SpatialCoordinates d)‖ ≤ 1 := by
    intro i
    rw [Pi.norm_single]; simp
  have hterm : ∀ i : Fin d,
      |lineDeriv ℝ At y (Pi.single i 1) * fderiv ℝ h y (Pi.single i 1) +
        At y * fderiv ℝ (fderiv ℝ h) y (Pi.single i 1) (Pi.single i 1)| ≤
        L * Kg + MA * Kh2 := by
    intro i
    set v : SpatialCoordinates d := Pi.single i 1
    have hv := hsingle i
    have hn := norm_nonneg v
    have hd1 : |fderiv ℝ h y v| ≤ Kg := by
      have h1 := (fderiv ℝ h y).le_opNorm v
      rw [Real.norm_eq_abs] at h1
      have h2 : ‖fderiv ℝ h y‖ * ‖v‖ ≤ ‖fderiv ℝ h y‖ :=
        mul_le_of_le_one_right (norm_nonneg _) hv
      linarith
    have hd2 : |fderiv ℝ (fderiv ℝ h) y v v| ≤ Kh2 := by
      have h1 := (fderiv ℝ (fderiv ℝ h) y v).le_opNorm v
      have h2 := (fderiv ℝ (fderiv ℝ h) y).le_opNorm v
      rw [Real.norm_eq_abs] at h1
      have h3 : ‖fderiv ℝ (fderiv ℝ h) y v‖ * ‖v‖ ≤ ‖fderiv ℝ (fderiv ℝ h) y v‖ :=
        mul_le_of_le_one_right (norm_nonneg _) hv
      have h4 : ‖fderiv ℝ (fderiv ℝ h) y‖ * ‖v‖ ≤ ‖fderiv ℝ (fderiv ℝ h) y‖ :=
        mul_le_of_le_one_right (ContinuousLinearMap.opNorm_nonneg _) hv
      linarith
    have hKg : 0 ≤ Kg := (norm_nonneg _).trans hg
    calc _ ≤ |lineDeriv ℝ At y v * fderiv ℝ h y v| +
          |At y * fderiv ℝ (fderiv ℝ h) y v v| := abs_add_le _ _
      _ = |lineDeriv ℝ At y v| * |fderiv ℝ h y v| +
          |At y| * |fderiv ℝ (fderiv ℝ h) y v v| := by rw [abs_mul, abs_mul]
      _ ≤ L * Kg + MA * Kh2 := by
          have e1 : |lineDeriv ℝ At y v| * |fderiv ℝ h y v| ≤ L * Kg :=
            mul_le_mul (hL i) hd1 (abs_nonneg _) hL0
          have e2 : |At y| * |fderiv ℝ (fderiv ℝ h) y v v| ≤ MA * Kh2 :=
            mul_le_mul hA hd2 (abs_nonneg _) hMA0
          linarith
  calc _ ≤ ∑ i : Fin d,
        |lineDeriv ℝ At y (Pi.single i 1) * fderiv ℝ h y (Pi.single i 1) +
          At y * fderiv ℝ (fderiv ℝ h) y (Pi.single i 1) (Pi.single i 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (L * Kg + MA * Kh2) := Finset.sum_le_sum fun i _ => hterm i
    _ = (d : ℝ) * (L * Kg + MA * Kh2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `DN/eps ≤ ell⁻¹` for `ell = c eps/(1+DN)` and `c ≤ 1`. -/
theorem aux_rem_resolved_microscopic_dir_rate_le_inv (c eps DN : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (heps : 0 < eps) (hDN : 0 ≤ DN) :
    DN / eps ≤ (c * eps / (1 + DN))⁻¹ := by
  rw [inv_div, div_le_div_iff₀ heps (mul_pos hc heps)]
  nlinarith [mul_le_mul_of_nonneg_left hc1 (mul_nonneg hDN heps.le)]

/-- `DN/eps · ell ≤ c`. -/
theorem aux_rem_resolved_microscopic_dir_rate_mul_ell (c eps DN : ℝ) (hc : 0 < c)
    (heps : 0 < eps) (hDN : 0 ≤ DN) :
    DN / eps * (c * eps / (1 + DN)) ≤ c := by
  have h1DN : 0 < 1 + DN := by linarith
  rw [div_mul_div_comm, div_le_iff₀ (mul_pos heps h1DN)]
  nlinarith

/-- **Local Lipschitz bound of the actual coefficient** on `K ∩ ball(x, ell)`. -/
theorem aux_rem_resolved_microscopic_dir_local_lipschitz {d : ℕ}
    (A : SpatialCoordinates d → ℝ) (K : Set (SpatialCoordinates d))
    (mN DN eps c ell : ℝ) (hmN : 0 < mN) (hDN : 0 ≤ DN) (heps : 0 < eps)
    (hbd : ∀ y ∈ K, mN ≤ A y)
    (hlog : ∀ y ∈ K, ∀ z ∈ K, |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z)
    (hδ : DN / eps * ell ≤ c) (x : SpatialCoordinates d) (hx : x ∈ K) :
    LipschitzOnWith (Real.toNNReal (Real.exp c * A x * (DN / eps))) A
      (K ∩ Metric.ball x ell) := by
  have hax : 0 < A x := hmN.trans_le (hbd x hx)
  have hup : ∀ z ∈ K ∩ Metric.ball x ell, A z ≤ Real.exp c * A x := by
    intro z hz
    have hd : dist z x ≤ ell := (Metric.mem_ball.1 hz.2).le
    have hl := (hlog z hz.1 x hx).trans
      ((mul_le_mul_of_nonneg_left hd (div_nonneg hDN heps.le)).trans hδ)
    exact (aux_rem_resolved_microscopic_neumann_exp_of_log (hmN.trans_le (hbd z hz.1)) hax hl).2
  apply LipschitzOnWith.of_dist_le'
  intro y hy z hz
  rw [Real.dist_eq]
  calc |A y - A z| ≤ Real.exp c * A x * |Real.log (A y) - Real.log (A z)| :=
        aux_rem_resolved_microscopic_abs_sub_le_log (hmN.trans_le (hbd y hy.1))
          (hmN.trans_le (hbd z hz.1)) (hup y hy) (hup z hz)
    _ ≤ Real.exp c * A x * (DN / eps * dist y z) :=
        mul_le_mul_of_nonneg_left (hlog y hy.1 z hz.1) (by positivity)
    _ = Real.exp c * A x * (DN / eps) * dist y z := by ring

/-- **Dirichlet datum flux, clauses (1)+(2)** of the frozen Dirichlet conjunct of
`rem_resolved_microscopic`, for every constant `C ≥ d` and every `0 < c ≤ 1`, on the
actual frozen carriers.  Besides the frozen bound and weak identity, `G` is exported as
measurable and essentially bounded on `Q` (for the `v`-equation and the reflection). -/
theorem aux_rem_resolved_microscopic_dir_flux_package
    (d : ℕ) (C c : ℝ) (hC : (d : ℝ) ≤ C) (hc : 0 < c) (hc1 : c ≤ 1)
    (eps : ℝ) (heps : 0 < eps)
    (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ))
    (haA : a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (DN mN MN : ℝ) (hDN : 0 ≤ DN) (hmN : 0 < mN)
    (hbd : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      mN ≤ A y ∧ A y ≤ MN)
    (hlog : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
        |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z)
    (h : SpatialCoordinates d → ℝ) (hh : ContDiff ℝ 2 h)
    (hdata : weakSobolevGraph (unitNeumannCube d))
    (hhd : (hdata : SobolevData (unitNeumannCube d)).1
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] h) :
    let Q := unitNeumannCube d
    let K := closure (Q : Set (SpatialCoordinates d))
    let ell : ℝ := c * eps / (1 + DN)
    ∃ G : SpatialCoordinates d → ℝ,
      (∀ Kg Kh2 : ℝ, 0 ≤ Kg → 0 ≤ Kh2 →
        (∀ y ∈ K, ‖fderiv ℝ h y‖ ≤ Kg) →
        (∀ y ∈ K, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ Kh2) →
        ∀ x ∈ (Q : Set (SpatialCoordinates d)),
          |G x| ≤ C * MN * (Kh2 + ell⁻¹ * Kg)) ∧
      (∀ ψ : killedSobolevGraph Q,
        sobolevCoefficientForm a (hdata : SobolevData Q) (ψ : SobolevData Q) =
          -∫ x in (Q : Set (SpatialCoordinates d)),
            G x * (ψ : SobolevData Q).1 x) ∧
      (∀ Kg Kh2 : ℝ, 0 ≤ Kg → 0 ≤ Kh2 →
        (∀ y ∈ K, ‖fderiv ℝ h y‖ ≤ Kg) →
        (∀ y ∈ K, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ Kh2) →
        ∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ y ∈ (Q : Set (SpatialCoordinates d)),
          dist y x < ell → |G y| ≤ (d : ℝ) * Real.exp c * A x * (Kh2 + ell⁻¹ * Kg)) ∧
      Measurable G ∧
      ∃ B : ℝ, ∀ x ∈ (Q : Set (SpatialCoordinates d)), |G x| ≤ B := by
  intro Q K ell
  have hK : IsCompact K := aux_rem_resolved_microscopic_unit_closure_isCompact d
  have hQK : (Q : Set (SpatialCoordinates d)) ⊆ K := subset_closure
  have hx0 := aux_rem_resolved_microscopic_unit_center_mem d
  have hMN : 0 ≤ MN :=
    (hmN.le.trans (hbd _ (hQK hx0)).1).trans (hbd _ (hQK hx0)).2
  have hLipOn := aux_rem_resolved_microscopic_coeff_lipschitzOn (A : SpatialCoordinates d → ℝ)
    K mN MN DN eps hmN hMN hbd hlog
  obtain ⟨At, hAtLip, hEq⟩ := hLipOn.extend_real
  have hL : ((Real.toNNReal (MN * (DN / eps)) : ℝ≥0) : ℝ) = MN * (DN / eps) :=
    Real.coe_toNNReal _ (mul_nonneg hMN (div_nonneg hDN heps.le))
  have haAt : (a.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] At := by
    filter_upwards [haA, ae_restrict_mem Q.isOpen.measurableSet] with x h1 h2
    rw [h1, hEq (hQK h2)]
  have hAtx : ∀ x ∈ (Q : Set (SpatialCoordinates d)), |At x| ≤ MN := by
    intro x hx
    rw [← hEq (hQK hx)]
    have hb := hbd x (hQK hx)
    rw [abs_of_pos (hmN.trans_le hb.1)]
    exact hb.2
  have hgrad := aux_rem_resolved_microscopic_datum_gradient K hK hQK h hh
    (hdata : SobolevData Q) hdata.property hhd
  set G := aux_remResolvedMicroscopicFluxDiv At h with hG
  have hGmeas : Measurable G :=
    aux_rem_resolved_microscopic_fluxDiv_measurable At h hAtLip.continuous hh
  have hh1 : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (m := 1) (by norm_num)
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn
    (hh.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn
    (hh1.continuous_fderiv (by norm_num)).continuousOn
  have hGbd : ∀ x ∈ (Q : Set (SpatialCoordinates d)),
      |G x| ≤ (d : ℝ) * ((Real.toNNReal (MN * (DN / eps)) : ℝ) * B1 + MN * B2) :=
    fun x hx => aux_rem_resolved_microscopic_fluxDiv_bound At h hAtLip x MN B1 B2
      (hAtx x hx) (hB1 x (hQK hx)) (hB2 x (hQK hx))
  have hG2 : MemLp G 2 (volume.restrict (Q : Set (SpatialCoordinates d))) := by
    refine MemLp.of_bound hGmeas.aestronglyMeasurable
      ((d : ℝ) * ((Real.toNNReal (MN * (DN / eps)) : ℝ) * B1 + MN * B2)) ?_
    exact (ae_restrict_iff' Q.isOpen.measurableSet).mpr
      (Eventually.of_forall fun x hx => by
        rw [Real.norm_eq_abs]; exact hGbd x hx)
  refine ⟨G, ?_, ?_, ?_, hGmeas, _, hGbd⟩
  · intro Kg Kh2 hKg hKh2 hg hh2 x hx
    have hb := aux_rem_resolved_microscopic_fluxDiv_bound At h hAtLip x MN Kg Kh2
      (hAtx x hx) (hg x (hQK hx)) (hh2 x (hQK hx))
    rw [hL] at hb
    have hell : DN / eps ≤ ell⁻¹ := by
      change DN / eps ≤ (c * eps / (1 + DN))⁻¹
      rw [inv_div, div_le_div_iff₀ heps (mul_pos hc heps)]
      nlinarith [mul_le_mul_of_nonneg_left hc1 (mul_nonneg hDN heps.le)]
    have hinner : 0 ≤ Kh2 + ell⁻¹ * Kg :=
      add_nonneg hKh2 (mul_nonneg ((div_nonneg hDN heps.le).trans hell) hKg)
    calc |G x| ≤ (d : ℝ) * (MN * (DN / eps) * Kg + MN * Kh2) := hb
      _ = (d : ℝ) * MN * (Kh2 + DN / eps * Kg) := by ring
      _ ≤ (d : ℝ) * MN * (Kh2 + ell⁻¹ * Kg) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg d) hMN)
          gcongr
      _ ≤ C * MN * (Kh2 + ell⁻¹ * Kg) := by
          apply mul_le_mul_of_nonneg_right _ hinner
          exact mul_le_mul_of_nonneg_right hC hMN
  · exact aux_rem_resolved_microscopic_flux_killed a (hdata : SobolevData Q) G hG2
      (fun φ => aux_rem_resolved_microscopic_flux_smooth a At hAtLip haAt h hh
        (hdata : SobolevData Q) hgrad φ)
  · intro Kg Kh2 hKg hKh2 hg hh2 x hx y hy hyx
    have hax : 0 < A x := hmN.trans_le (hbd x (hQK hx)).1
    have hδ : DN / eps * ell ≤ c :=
      aux_rem_resolved_microscopic_dir_rate_mul_ell c eps DN hc heps hDN
    have hLip := aux_rem_resolved_microscopic_dir_local_lipschitz (A : SpatialCoordinates d → ℝ)
      K mN DN eps c ell hmN hDN heps (fun z hz => (hbd z hz).1) hlog hδ x (hQK hx)
    have hLipAt : LipschitzOnWith (Real.toNNReal (Real.exp c * A x * (DN / eps))) At
        ((Q : Set (SpatialCoordinates d)) ∩ Metric.ball x ell) := by
      intro z1 hz1 z2 hz2
      rw [← hEq (hQK hz1.1), ← hEq (hQK hz2.1)]
      exact hLip (Set.inter_subset_inter_left _ hQK hz1) (Set.inter_subset_inter_left _ hQK hz2)
    have hnhds : (Q : Set (SpatialCoordinates d)) ∩ Metric.ball x ell ∈ nhds y :=
      (Q.isOpen.inter Metric.isOpen_ball).mem_nhds ⟨hy, Metric.mem_ball.2 hyx⟩
    have hLnn : 0 ≤ Real.exp c * A x * (DN / eps) := by
      have := div_nonneg hDN heps.le
      exact mul_nonneg (mul_nonneg (Real.exp_pos c).le hax.le) this
    have hld : ∀ i : Fin d, |lineDeriv ℝ At y (Pi.single i 1)| ≤
        Real.exp c * A x * (DN / eps) := by
      intro i
      have h1 := norm_lineDeriv_le_of_lipschitzOn ℝ hnhds hLipAt (v := Pi.single i (1 : ℝ))
      rw [Real.norm_eq_abs, Real.coe_toNNReal _ hLnn] at h1
      refine h1.trans ?_
      have hs : ‖(Pi.single i (1 : ℝ) : SpatialCoordinates d)‖ ≤ 1 := by
        rw [Pi.norm_single]; simp
      exact mul_le_of_le_one_right hLnn hs
    have hlyx : |Real.log (A y) - Real.log (A x)| ≤ c :=
      (hlog y (hQK hy) x (hQK hx)).trans
        ((mul_le_mul_of_nonneg_left (Metric.mem_ball.1 hyx).le
          (div_nonneg hDN heps.le)).trans hδ)
    have hAy : |At y| ≤ Real.exp c * A x := by
      rw [← hEq (hQK hy), abs_of_pos (hmN.trans_le (hbd y (hQK hy)).1)]
      exact (aux_rem_resolved_microscopic_neumann_exp_of_log
        (hmN.trans_le (hbd y (hQK hy)).1) hax hlyx).2
    have hb := aux_rem_resolved_microscopic_dir_fluxDiv_bound_pt At h y
      (Real.exp c * A x * (DN / eps)) (Real.exp c * A x) Kg Kh2 hLnn
      (mul_nonneg (Real.exp_pos c).le hax.le) hld hAy (hg y (hQK hy)) (hh2 y (hQK hy))
    have hrate := aux_rem_resolved_microscopic_dir_rate_le_inv c eps DN hc hc1 heps hDN
    have hpre : 0 ≤ (d : ℝ) * Real.exp c * A x :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (Real.exp_pos c).le) hax.le
    calc |G y| ≤ (d : ℝ) * (Real.exp c * A x * (DN / eps) * Kg + Real.exp c * A x * Kh2) := hb
      _ = (d : ℝ) * Real.exp c * A x * (Kh2 + DN / eps * Kg) := by ring
      _ ≤ (d : ℝ) * Real.exp c * A x * (Kh2 + ell⁻¹ * Kg) := by
          apply mul_le_mul_of_nonneg_left _ hpre
          have := mul_le_mul_of_nonneg_right hrate hKg
          linarith

end DirichletLocalFluxHelpers

section DirichletEstimateHelpers
open scoped ContDiff



/-- The two derivative parts of `c2Norm K h` bound `∇h`, `D²h` on the compact `K` and are
at most `c2Norm K h`. -/
theorem aux_rem_resolved_microscopic_dir_c2_parts {d : ℕ} (K : Set (SpatialCoordinates d))
    (hK : IsCompact K) (h : SpatialCoordinates d → ℝ) (hh : ContDiff ℝ 2 h) :
    ∃ Kg Kh2 : ℝ, 0 ≤ Kg ∧ 0 ≤ Kh2 ∧ (∀ y ∈ K, ‖fderiv ℝ h y‖ ≤ Kg) ∧
      (∀ y ∈ K, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ Kh2) ∧ Kg ≤ c2Norm K h ∧ Kh2 ≤ c2Norm K h := by
  have hh1 : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (m := 1) (by norm_num)
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn
    (hh.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn
    (hh1.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨B0, hB0⟩ := hK.exists_bound_of_continuousOn hh.continuous.continuousOn
  set S0 : Set ℝ := {v : ℝ | ∃ x ∈ K, v = |h x|}
  set S1 : Set ℝ := {v : ℝ | ∃ x ∈ K, v = ‖fderiv ℝ h x‖}
  set S2 : Set ℝ := {v : ℝ | ∃ x ∈ K, v = ‖fderiv ℝ (fderiv ℝ h) x‖}
  have hb1 : BddAbove S1 := ⟨B1, by rintro v ⟨x, hx, rfl⟩; simpa using hB1 x hx⟩
  have hb2 : BddAbove S2 := ⟨B2, by rintro v ⟨x, hx, rfl⟩; simpa using hB2 x hx⟩
  have h0 : 0 ≤ sSup S0 := Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact abs_nonneg _)
  have h1 : 0 ≤ sSup S1 := Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact norm_nonneg _)
  have h2 : 0 ≤ sSup S2 := Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact ContinuousLinearMap.opNorm_nonneg _)
  have hc2 : c2Norm K h = sSup S0 + sSup S1 + sSup S2 := rfl
  refine ⟨sSup S1, sSup S2, h1, h2, fun y hy => le_csSup hb1 ⟨y, hy, rfl⟩,
    fun y hy => le_csSup hb2 ⟨y, hy, rfl⟩, ?_, ?_⟩ <;> rw [hc2] <;> linarith

/-- `(r/ell)^q1 (6 ell)^d = 6^d r^q1 ell^(2d/p1)`. -/
theorem aux_rem_resolved_microscopic_dir_rpow_parent (d : ℕ) (p1 r ell : ℝ) (hr : 0 < r)
    (hell : 0 < ell) :
    (r / ell) ^ ((d : ℝ) - 2 * (d : ℝ) / p1) * (6 * ell) ^ d =
      (6 : ℝ) ^ d * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) * ell ^ (2 * (d : ℝ) / p1) := by
  rw [Real.div_rpow hr.le hell.le, mul_pow, ← Real.rpow_natCast ell d]
  have hsplit : ell ^ (d : ℝ) = ell ^ ((d : ℝ) - 2 * (d : ℝ) / p1) * ell ^ (2 * (d : ℝ) / p1) := by
    rw [← Real.rpow_add hell]; congr 1; ring
  rw [hsplit]
  have hq : 0 < ell ^ ((d : ℝ) - 2 * (d : ℝ) / p1) := Real.rpow_pos_of_pos hell _
  field_simp

/-- `r^d ≤ r^q1 ell^(2d/p1)` for `0 < r ≤ ell`. -/
theorem aux_rem_resolved_microscopic_dir_rpow_small (d : ℕ) (p1 r ell : ℝ) (hp1 : 2 ≤ p1)
    (hr : 0 < r) (hrell : r ≤ ell) :
    r ^ d ≤ r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) * ell ^ (2 * (d : ℝ) / p1) := by
  have hexp : 0 ≤ 2 * (d : ℝ) / p1 := by positivity
  rw [← Real.rpow_natCast r d]
  have hsplit : r ^ (d : ℝ) = r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) * r ^ (2 * (d : ℝ) / p1) := by
    rw [← Real.rpow_add hr]; congr 1; ring
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hrell hexp)
    (Real.rpow_nonneg hr.le _)

/-- `ell^(2+2d/p1) = ell^2 ell^(2d/p1)`. -/
theorem aux_rem_resolved_microscopic_dir_rpow_E (d : ℕ) (p1 ell : ℝ) (hell : 0 < ell) :
    ell ^ (2 + 2 * (d : ℝ) / p1) = ell ^ 2 * ell ^ (2 * (d : ℝ) / p1) := by
  rw [Real.rpow_add hell]
  norm_cast

/-- Real algebra of the Dirichlet one-centre estimate. -/
theorem aux_rem_resolved_microscopic_dir_alg
    (Gur Gvr Gv6 Gu6 GuC C0 R Ax KF Kf mN MN Kg Kh ell Y dd d2 sixd E Ld rq rd D6 : ℝ)
    (hu : Gur ≤ 2 * Gvr + d2 * MN * Kg ^ 2 * rd)
    (hv : Gvr ≤ C0 * R * Gv6 + C0 * Ax⁻¹ * KF ^ 2 * E * rq)
    (h6 : Gv6 ≤ 2 * Gu6 + d2 * MN * Kg ^ 2 * D6)
    (hmono : Gu6 ≤ GuC)
    (hRD6 : R * D6 = sixd * rq * Ld)
    (hrd : rd ≤ rq * Ld)
    (hKF : KF = Kf + dd * Ax * Y)
    (hE : E = ell ^ 2 * Ld)
    (hY : ell * Y ≤ 2 * Kh) (hY0 : 0 ≤ Y)
    (hC0 : 0 ≤ C0) (hR : 0 ≤ R) (hAx : 0 < Ax) (hmNAx : mN ≤ Ax) (hmN : 0 < mN)
    (hAxM : Ax ≤ MN) (hKg : 0 ≤ Kg) (hKgh : Kg ≤ Kh)
    (hell : 0 < ell) (hd2 : 0 ≤ d2) (hsix : 0 ≤ sixd) (hLd : 0 ≤ Ld) (hrq : 0 ≤ rq)
    (hE0 : 0 ≤ E) :
    Gur ≤ 4 * C0 * R * GuC + 4 * C0 * mN⁻¹ * Kf ^ 2 * E * rq +
      (2 * C0 * d2 * sixd + 16 * C0 * dd ^ 2 + d2) * MN * Kh ^ 2 * Ld * rq := by
  have hMN : 0 ≤ MN := hAx.le.trans hAxM
  have hKF2 : Ax⁻¹ * KF ^ 2 ≤ 2 * mN⁻¹ * Kf ^ 2 + 2 * dd ^ 2 * MN * Y ^ 2 := by
    rw [hKF]
    have h1 : (Kf + dd * Ax * Y) ^ 2 ≤ 2 * Kf ^ 2 + 2 * (dd * Ax * Y) ^ 2 := by
      nlinarith [sq_nonneg (Kf - dd * Ax * Y)]
    have h2 : Ax⁻¹ * (Kf + dd * Ax * Y) ^ 2 ≤ Ax⁻¹ * (2 * Kf ^ 2 + 2 * (dd * Ax * Y) ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hAx.le)
    have h3 : Ax⁻¹ * (2 * Kf ^ 2 + 2 * (dd * Ax * Y) ^ 2) =
        2 * Ax⁻¹ * Kf ^ 2 + 2 * dd ^ 2 * Ax * Y ^ 2 := by
      field_simp
    have h4 : Ax⁻¹ ≤ mN⁻¹ := inv_anti₀ hmN hmNAx
    have h5 : 2 * Ax⁻¹ * Kf ^ 2 ≤ 2 * mN⁻¹ * Kf ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    have h6 : 2 * dd ^ 2 * Ax * Y ^ 2 ≤ 2 * dd ^ 2 * MN * Y ^ 2 := by
      have : 0 ≤ 2 * dd ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAxM this) (sq_nonneg _)
    linarith
  have hYE : Y ^ 2 * E ≤ 4 * Kh ^ 2 * Ld := by
    rw [hE]
    have e : Y ^ 2 * (ell ^ 2 * Ld) = (ell * Y) ^ 2 * Ld := by ring
    rw [e]
    have h1 : (ell * Y) ^ 2 ≤ (2 * Kh) ^ 2 := pow_le_pow_left₀ (mul_nonneg hell.le hY0) hY 2
    have h2 := mul_le_mul_of_nonneg_right h1 hLd
    linarith
  have hKg2 : Kg ^ 2 ≤ Kh ^ 2 := pow_le_pow_left₀ hKg hKgh 2
  have c2 : C0 * R * Gv6 ≤ 2 * C0 * R * GuC + C0 * d2 * sixd * MN * Kg ^ 2 * Ld * rq := by
    have hCR : 0 ≤ C0 * R := mul_nonneg hC0 hR
    have k1 : Gv6 ≤ 2 * GuC + d2 * MN * Kg ^ 2 * D6 := by linarith
    have k2 := mul_le_mul_of_nonneg_left k1 hCR
    have k3 : C0 * R * (2 * GuC + d2 * MN * Kg ^ 2 * D6) =
        2 * C0 * R * GuC + C0 * d2 * MN * Kg ^ 2 * (R * D6) := by ring
    rw [k3, hRD6] at k2
    linarith
  have c3 : C0 * Ax⁻¹ * KF ^ 2 * E * rq ≤
      2 * C0 * mN⁻¹ * Kf ^ 2 * E * rq + 8 * C0 * dd ^ 2 * MN * Kh ^ 2 * Ld * rq := by
    have hCEr : 0 ≤ C0 * E * rq := mul_nonneg (mul_nonneg hC0 hE0) hrq
    have k1 := mul_le_mul_of_nonneg_left hKF2 hCEr
    have k2 : 2 * C0 * dd ^ 2 * MN * rq * (Y ^ 2 * E) ≤
        2 * C0 * dd ^ 2 * MN * rq * (4 * Kh ^ 2 * Ld) :=
      mul_le_mul_of_nonneg_left hYE (by positivity)
    have e1 : C0 * E * rq * (Ax⁻¹ * KF ^ 2) = C0 * Ax⁻¹ * KF ^ 2 * E * rq := by ring
    have e2 : C0 * E * rq * (2 * mN⁻¹ * Kf ^ 2 + 2 * dd ^ 2 * MN * Y ^ 2) =
        2 * C0 * mN⁻¹ * Kf ^ 2 * E * rq + 2 * C0 * dd ^ 2 * MN * rq * (Y ^ 2 * E) := by ring
    rw [e1, e2] at k1
    linarith
  have c4 : d2 * MN * Kg ^ 2 * rd ≤ d2 * MN * Kh ^ 2 * Ld * rq := by
    have k1 : d2 * MN * Kg ^ 2 * rd ≤ d2 * MN * Kg ^ 2 * (rq * Ld) :=
      mul_le_mul_of_nonneg_left hrd (by positivity)
    have k2 : d2 * MN * Kg ^ 2 * (rq * Ld) ≤ d2 * MN * Kh ^ 2 * (rq * Ld) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKg2 (mul_nonneg hd2 hMN))
        (mul_nonneg hrq hLd)
    linarith
  have c5 : C0 * d2 * sixd * MN * Kg ^ 2 * Ld * rq ≤ C0 * d2 * sixd * MN * Kh ^ 2 * Ld * rq := by
    have hpre : 0 ≤ C0 * d2 * sixd * MN := by positivity
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKg2 hpre)
      (mul_nonneg hLd hrq)
    linarith
  have c6 : 2 * C0 * R * Gu6 ≤ 2 * C0 * R * GuC := by
    have : 0 ≤ 2 * C0 * R := by positivity
    exact mul_le_mul_of_nonneg_left hmono this
  linarith

/-- **One-centre Dirichlet estimate for `v = u - hdata`**, through the odd multi-face fold, with
the parent cube of side `6 ell` and the local source bound `|f + G| ≤ Kf + d e^c A(x) Y`. -/
theorem aux_rem_resolved_microscopic_dir_one_centre_v {d : ℕ} (W : SmallPerturbationInput d)
    (p1 : ℝ) (hp1 : 2 ≤ p1) (C0 c : ℝ) (hcosc : c ≤ W.osc p1)
    (hC1 : 2 * W.C p1 ^ 2 * Real.exp c ^ 2 ≤ C0) (hC2 : W.C p1 ^ 2 * Real.exp c / 2 ≤ C0)
    (eps : ℝ) (heps : 0 < eps)
    (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ))
    (haA : a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (DN mN MN : ℝ) (hDN : 0 ≤ DN) (hmN : 0 < mN)
    (hAK : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN)
    (hlog : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) (Kf : ℝ)
    (hfb : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf)
    (hdata u : weakSobolevGraph (unitNeumannCube d))
    (hsol : SolvesDirichlet a f hdata u)
    (G : SpatialCoordinates d → ℝ)
    (hG2 : ∀ ψ : killedSobolevGraph (unitNeumannCube d),
      sobolevCoefficientForm a (hdata : SobolevData (unitNeumannCube d))
          (ψ : SobolevData (unitNeumannCube d)) =
        -∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), G x * (ψ : SobolevData (unitNeumannCube d)).1 x)
    (hGm : Measurable G) (BG : ℝ) (hBG : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |G y| ≤ BG)
    (ell Y : ℝ) (hell : 0 < ell) (hell14 : ell ≤ 1 / 4) (hδ : DN / eps * ell ≤ c)
    (hGloc : ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), dist y x < ell →
      |G y| ≤ (d : ℝ) * Real.exp c * A x * Y)
    (x : SpatialCoordinates d) (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) (hY : 0 ≤ Y) (hKf : 0 ≤ Kf)
    (r : ℝ) (hr : 0 < r) (hrell : r ≤ ell) :
    ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
        A y * ∑ i : Fin d,
          (((u : SobolevData (unitNeumannCube d)) - (hdata : SobolevData (unitNeumannCube d))).2 i y) ^ 2 ≤
      C0 * (r / ell) ^ ((d : ℝ) - 2 * (d : ℝ) / p1) *
          (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < 6 * ell / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
            A y * ∑ i : Fin d,
              (((u : SobolevData (unitNeumannCube d)) - (hdata : SobolevData (unitNeumannCube d))).2 i y) ^ 2) +
        C0 * (A x)⁻¹ * (Kf + (d : ℝ) * Real.exp c * A x * Y) ^ 2 *
          ell ^ (2 + 2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) := by
  have hAQ : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN := fun y hy => hAK y (subset_closure hy)
  have hmodQ : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), dist y x ≤ ell →
      |Real.log (A y) - Real.log (A x)| ≤ c := fun y hy hd =>
    (hlog y (subset_closure hy) x (subset_closure hx)).trans
      ((mul_le_mul_of_nonneg_left hd (div_nonneg hDN heps.le)).trans hδ)
  have hfL2 := aux_rem_resolved_microscopic_bounded_memLp_two f hf Kf hfb
  have hGL2 := aux_rem_resolved_microscopic_bounded_memLp_two G hGm BG hBG
  have hv := aux_rem_resolved_microscopic_v_equation a f G hfL2 hGL2 hdata u hsol hG2
  rcases hv with ⟨hvk, hveq⟩
  have hFB : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y + G y| ≤ Kf + BG := fun y hy =>
    (abs_add_le _ _).trans (add_le_add (hfb y hy) (hBG y hy))
  have hfold := aux_rem_resolved_microscopic_mfg_multiface_scalar (fun _ => (1 / 2 : ℝ)) 1 one_pos
    (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x) (A : SpatialCoordinates d → ℝ) (fun y => f y + G y) a haA
    ((u : SobolevData (unitNeumannCube d)) - (hdata : SobolevData (unitNeumannCube d))) hvk
    (hf.add hGm) (Kf + BG) hFB (fun ψ hψ => hveq ⟨ψ, hψ⟩)
  rcases hfold with ⟨af, vf, haf, _hvf, hg, hweak⟩
  have hdist : ∀ y : SpatialCoordinates d, dist y x < ell → ∀ j, |y j - x j| < ell := by
    intro y h j
    have := (dist_pi_lt_iff hell).1 h j
    rwa [Real.dist_eq] at this
  have hTx : coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x)) (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x) x = x := aux_rem_resolved_microscopic_neumann_fold_id _ _ hx
  have hTQ := aux_rem_resolved_microscopic_neumann_fold_ae d (fun _ => (1 / 2 : ℝ)) 1 one_pos
    (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x) (p := fun _ => True) (Eventually.of_forall fun _ => trivial)
  have hFbd : ∀ᵐ y ∂volume.restrict (foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x) : Set (SpatialCoordinates d)), dist y x < ell →
      |aux_rem_resolved_microscopic_mf_sgn (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x)) (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x) y *
        (f (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x)) (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x) y) + G (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x)) (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x) y))| ≤ Kf + (d : ℝ) * Real.exp c * A x * Y := by
    filter_upwards [hTQ] with y hy hyx
    have hd : dist (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x)) (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x) y) x < ell := by
      calc dist (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x)) (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x) y) x = dist (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x)) (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x) y) (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x)) (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x) x) := by rw [hTx]
        _ ≤ dist y x := coordinateFold_nonexpansive _ _ _ y x
        _ < ell := hyx
    rw [abs_mul, aux_rem_resolved_microscopic_mf_abs_sgn, one_mul]
    exact (abs_add_le _ _).trans (add_le_add (hfb _ hy.2) (hGloc x hx _ hy.2 hd))
  have hFm : Measurable (fun y => aux_rem_resolved_microscopic_mf_sgn (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x)) (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x) y *
      (f (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x)) (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x) y) + G (coordinateFold (foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x)) (aux_rem_resolved_microscopic_neumann_faces x ell) (aux_rem_resolved_microscopic_neumann_upper x) y))) :=
    (aux_rem_resolved_microscopic_mf_sgn_measurable _ _ _).mul
      ((hf.add hGm).comp (coordinateFold_continuous _ _ _).measurable)
  have hKF : 0 ≤ Kf + (d : ℝ) * Real.exp c * A x * Y := by
    have := (hmN.trans_le (hAQ x hx).1).le
    positivity
  exact aux_rem_resolved_microscopic_dir_core W p1 hp1 _ _ C0 c hcosc hC1 hC2 a A A.continuous haA
    mN MN hmN hAQ ⟨_, killedSobolevGraph_le_weakSobolevGraph hvk⟩ af vf haf hg _ hFm hweak x hx
    ell hell _ hKF hFbd hmodQ
    (fun y hy => aux_rem_resolved_microscopic_neumann_ball_sub_folded hx hell14 (hdist y hy))
    (aux_rem_resolved_microscopic_neumann_box x ell)
    (aux_rem_resolved_microscopic_neumann_box_measurable x ell)
    (aux_rem_resolved_microscopic_neumann_box_sub_folded hx hell14)
    (fun J hJ => aux_rem_resolved_microscopic_neumann_box_symm x ell J hJ)
    (fun y hy => aux_rem_resolved_microscopic_neumann_ball_sub_box hx hell14 (hdist y hy))
    (6 * ell) (aux_rem_resolved_microscopic_neumann_box_sub_cube hx hell14 le_rfl) r hr hrell

/-- The observation box of side `R` about `x`: measurable, finite, volume `R^d`. -/
theorem aux_rem_resolved_microscopic_dir_box_facts {d : ℕ} (x : SpatialCoordinates d) (R : ℝ)
    (hR : 0 < R) :
    MeasurableSet {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < R / 2} ∧
      volume {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < R / 2} ≠ (⊤ : ℝ≥0∞) ∧
      volume.real {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < R / 2} ≤ R ^ d := by
  have hbox : {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < R / 2} =
      (centeredCube x R hR : Set (SpatialCoordinates d)) := by
    ext y
    rw [centeredCube_eq_pi x hR]
    simp only [mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
    constructor
    · intro hy i
      have hi := hy i
      rw [abs_lt] at hi
      constructor <;> linarith
    · intro hy i
      have hi := hy i
      rw [abs_lt]
      constructor <;> linarith
  rw [hbox]
  refine ⟨(centeredCube x R hR).isOpen.measurableSet, ?_, ?_⟩
  · rw [centeredCube_volume]
    exact ENNReal.ofReal_ne_top
  · rw [centeredCube_volume_real]



theorem aux_rem_resolved_microscopic_dir_u_le_v {d : ℕ} (a : PositiveCoefficient (unitNeumannCube d))
    (A : C(SpatialCoordinates d, ℝ))
    (haA : (a.val : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (MN Kg : ℝ) (hMN : 0 ≤ MN) (hKg : 0 ≤ Kg)
    (hAb : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), 0 ≤ A y ∧ A y ≤ MN)
    (h : SpatialCoordinates d → ℝ) (hh : ContDiff ℝ 2 h)
    (hdata u : weakSobolevGraph (unitNeumannCube d))
    (htrace : ((hdata : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] h)
    (hgradbound : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), ‖fderiv ℝ h y‖ ≤ Kg)
    (x : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) :
    (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < R / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
      A y * ∑ i : Fin d, ((u : SobolevData (unitNeumannCube d)).2 i y) ^ 2) ≤
      2 * (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < R / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
        A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d)) - (hdata : SobolevData (unitNeumannCube d))).2 i y) ^ 2) +
      2 * (d : ℝ) * MN * Kg ^ 2 * R ^ d := by
  have hbf := aux_rem_resolved_microscopic_dir_box_facts x R hR
  rcases hbf with ⟨hB, hfin, hvol⟩
  have htr' : (((-hdata : weakSobolevGraph (unitNeumannCube d)) : SobolevData (unitNeumannCube d)).1 :
      SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] (fun y => -h y) := by
    filter_upwards [Lp.coeFn_neg ((hdata : SobolevData (unitNeumannCube d)).1), htrace] with y h1 h2
    change ((-(hdata : SobolevData (unitNeumannCube d)).1 : DomainL2 (unitNeumannCube d)) : SpatialCoordinates d → ℝ) y = _
    rw [h1, Pi.neg_apply, h2]
  have hg' : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), ‖fderiv ℝ (fun y => -h y) y‖ ≤ Kg := by
    intro y hy
    rw [fderiv_fun_neg, norm_neg]
    exact hgradbound y hy
  have hcmp := aux_micro_dirichlet_parent_comparison a A haA MN Kg R (2 * (d : ℝ)) hMN hKg le_rfl
    hR.le hAb (fun y => -h y) hh.neg (-hdata)
    ⟨(u : SobolevData (unitNeumannCube d)) - (hdata : SobolevData (unitNeumannCube d)), Submodule.sub_mem _ u.2 hdata.2⟩ htr' hg' hB hfin hvol
  have e : ((⟨(u : SobolevData (unitNeumannCube d)) - (hdata : SobolevData (unitNeumannCube d)), Submodule.sub_mem _ u.2 hdata.2⟩ :
      weakSobolevGraph (unitNeumannCube d)) : SobolevData (unitNeumannCube d)) -
      ((-hdata : weakSobolevGraph (unitNeumannCube d)) : SobolevData (unitNeumannCube d)) = (u : SobolevData (unitNeumannCube d)) := by
    change (u : SobolevData (unitNeumannCube d)) - (hdata : SobolevData (unitNeumannCube d)) - -(hdata : SobolevData (unitNeumannCube d)) = (u : SobolevData (unitNeumannCube d))
    rw [sub_neg_eq_add, sub_add_cancel]
  rw [e] at hcmp
  exact hcmp

/-- **Statement Dirichlet clause (5) at one centre**, with the parent energy at side `C eps`. -/
theorem aux_rem_resolved_microscopic_dir_clause5_at {d : ℕ} (W : SmallPerturbationInput d)
    (p1 : ℝ) (hp1 : 2 ≤ p1) (C0 c : ℝ) (hcosc : c ≤ W.osc p1) (hC0 : 0 ≤ C0)
    (hC1 : 2 * W.C p1 ^ 2 * Real.exp c ^ 2 ≤ C0) (hC2 : W.C p1 ^ 2 * Real.exp c / 2 ≤ C0)
    (eps : ℝ) (heps : 0 < eps)
    (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ))
    (haA : a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (DN mN MN : ℝ) (hDN : 0 ≤ DN) (hmN : 0 < mN)
    (hAK : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN)
    (hlog : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hfb : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf)
    (h : SpatialCoordinates d → ℝ) (hh : ContDiff ℝ 2 h)
    (hdata u : weakSobolevGraph (unitNeumannCube d))
    (hhd : ((hdata : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] h)
    (hsol : SolvesDirichlet a f hdata u)
    (G : SpatialCoordinates d → ℝ)
    (hG2 : ∀ ψ : killedSobolevGraph (unitNeumannCube d),
      sobolevCoefficientForm a (hdata : SobolevData (unitNeumannCube d)) (ψ : SobolevData (unitNeumannCube d)) =
        -∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), G x * (ψ : SobolevData (unitNeumannCube d)).1 x)
    (hGm : Measurable G) (BG : ℝ) (hBG : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |G y| ≤ BG)
    (ell : ℝ) (hell : 0 < ell) (hell14 : ell ≤ 1 / 4) (hδ : DN / eps * ell ≤ c)
    (Kg Kh2 Kh : ℝ) (hKg : 0 ≤ Kg) (hKh2 : 0 ≤ Kh2)
    (hgK : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), ‖fderiv ℝ h y‖ ≤ Kg) (hKgh : Kg ≤ Kh) (hKh2h : Kh2 ≤ Kh)
    (hGloc : ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), dist y x < ell →
      |G y| ≤ (d : ℝ) * Real.exp c * A x * (Kh2 + ell⁻¹ * Kg))
    (C : ℝ) (hC4 : 4 * C0 ≤ C)
    (hCd : 2 * C0 * (2 * (d : ℝ)) * (6 : ℝ) ^ d + 16 * C0 * ((d : ℝ) * Real.exp c) ^ 2 +
      2 * (d : ℝ) ≤ C)
    (h6 : 6 * ell ≤ C * eps)
    (x : SpatialCoordinates d) (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) (r : ℝ) (hr : 0 < r) (hrell : r ≤ ell) :
    (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d))).2 i y) ^ 2) ≤ C * (r / ell) ^ ((d : ℝ) - 2 * (d : ℝ) / p1) * (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < (C * eps) / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d))).2 i y) ^ 2) +
      C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) +
      C * MN * Kh ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) := by
  have hAQ : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN := fun y hy => hAK y (subset_closure hy)
  have hAx : 0 < A x := hmN.trans_le (hAQ x hx).1
  have hMN : 0 ≤ MN := hAx.le.trans (hAQ x hx).2
  have hAb : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), 0 ≤ A y ∧ A y ≤ MN :=
    fun y hy => ⟨hmN.le.trans (hAK y hy).1, (hAK y hy).2⟩
  have hAb' : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), 0 ≤ A y ∧ A y ≤ MN := fun y hy => hAb y (subset_closure hy)
  have hY0 : 0 ≤ Kh2 + ell⁻¹ * Kg := add_nonneg hKh2 (mul_nonneg (inv_nonneg.2 hell.le) hKg)
  have hv := aux_rem_resolved_microscopic_dir_one_centre_v W p1 hp1 C0 c hcosc hC1 hC2 eps heps
    a A haA DN mN MN hDN hmN hAK hlog f hf Kf hfb hdata u hsol G hG2 hGm BG hBG ell
    (Kh2 + ell⁻¹ * Kg) hell hell14 hδ hGloc x hx hY0 hKf r hr hrell
  have hu := aux_rem_resolved_microscopic_dir_u_le_v a A haA MN Kg hMN hKg hAb h hh hdata u hhd hgK
    x r hr
  have h6pos : 0 < 6 * ell := by positivity
  have hbf := aux_rem_resolved_microscopic_dir_box_facts x (6 * ell) h6pos
  rcases hbf with ⟨hB6, hfin6, hvol6⟩
  have h6v := aux_micro_dirichlet_parent_comparison a A haA MN Kg (6 * ell) (2 * (d : ℝ)) hMN hKg
    le_rfl h6pos.le hAb h hh hdata u hhd hgK hB6 hfin6 hvol6
  have hmono := aux_rem_resolved_microscopic_neumann_gamma_mono (A : SpatialCoordinates d → ℝ)
    A.continuous MN hAb' (u : SobolevData (unitNeumannCube d)) x h6
  have hRD6 := aux_rem_resolved_microscopic_dir_rpow_parent d p1 r ell hr hell
  have hrd := aux_rem_resolved_microscopic_dir_rpow_small d p1 r ell hp1 hr hrell
  have hE := aux_rem_resolved_microscopic_dir_rpow_E d p1 ell hell
  have hY : ell * (Kh2 + ell⁻¹ * Kg) ≤ 2 * Kh := by
    have e : ell * (Kh2 + ell⁻¹ * Kg) = ell * Kh2 + Kg := by field_simp
    rw [e]
    have : ell * Kh2 ≤ Kh2 := mul_le_of_le_one_left hKh2 (by linarith)
    linarith
  have hR : 0 ≤ (r / ell) ^ ((d : ℝ) - 2 * (d : ℝ) / p1) := Real.rpow_nonneg (div_nonneg hr.le hell.le) _
  have hLd : 0 ≤ ell ^ (2 * (d : ℝ) / p1) := Real.rpow_nonneg hell.le _
  have hrq : 0 ≤ r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) := Real.rpow_nonneg hr.le _
  have hE0 : 0 ≤ ell ^ (2 + 2 * (d : ℝ) / p1) := Real.rpow_nonneg hell.le _
  have halg := aux_rem_resolved_microscopic_dir_alg _ _ _ _ _ C0 _ (A x) _ Kf mN MN Kg Kh ell
    (Kh2 + ell⁻¹ * Kg) ((d : ℝ) * Real.exp c) (2 * (d : ℝ)) ((6 : ℝ) ^ d) _ _ _ _ _
    hu hv h6v hmono hRD6 hrd rfl hE hY hY0 hC0 hR hAx (hAQ x hx).1 hmN (hAQ x hx).2 hKg hKgh hell
    (by positivity) (by positivity) hLd hrq hE0
  have hGuC : 0 ≤ (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < (C * eps) / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d))).2 i y) ^ 2) := by
    refine setIntegral_nonneg ((aux_rem_resolved_microscopic_neumann_cube_measurable x _).inter
      (unitNeumannCube d).isOpen.measurableSet) fun y hy => ?_
    exact mul_nonneg (hAb' y hy.2).1 (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have k1 : 4 * C0 * (r / ell) ^ ((d : ℝ) - 2 * (d : ℝ) / p1) * (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < (C * eps) / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d))).2 i y) ^ 2) ≤
      C * (r / ell) ^ ((d : ℝ) - 2 * (d : ℝ) / p1) * (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < (C * eps) / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d))).2 i y) ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC4 hR) hGuC
  have k2 : 4 * C0 * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) ≤
      C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) := by
    have hpos : 0 ≤ mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) := by
      have := inv_nonneg.2 hmN.le
      positivity
    have := mul_le_mul_of_nonneg_right hC4 hpos
    linarith
  have hDNd : 1 ≤ (1 + DN) ^ (d : ℝ) := Real.one_le_rpow (by linarith) (Nat.cast_nonneg d)
  have k3 : (2 * C0 * (2 * (d : ℝ)) * (6 : ℝ) ^ d + 16 * C0 * ((d : ℝ) * Real.exp c) ^ 2 +
      2 * (d : ℝ)) * MN * Kh ^ 2 * ell ^ (2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) ≤
      C * MN * Kh ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) := by
    have hpos : 0 ≤ MN * Kh ^ 2 * ell ^ (2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) := by positivity
    have hC0' : 0 ≤ C := le_trans (by positivity) hC4
    have s1 := mul_le_mul_of_nonneg_right hCd hpos
    have s2 : C * (MN * Kh ^ 2 * ell ^ (2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1)) ≤
        C * (MN * Kh ^ 2 * ell ^ (2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1)) * (1 + DN) ^ (d : ℝ) :=
      le_mul_of_one_le_right (mul_nonneg hC0' hpos) hDNd
    have e1 : (2 * C0 * (2 * (d : ℝ)) * (6 : ℝ) ^ d + 16 * C0 * ((d : ℝ) * Real.exp c) ^ 2 +
      2 * (d : ℝ)) * MN * Kh ^ 2 * ell ^ (2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) =
        (2 * C0 * (2 * (d : ℝ)) * (6 : ℝ) ^ d + 16 * C0 * ((d : ℝ) * Real.exp c) ^ 2 +
      2 * (d : ℝ)) * (MN * Kh ^ 2 * ell ^ (2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1)) := by ring
    have e2 : C * MN * Kh ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) =
        C * (MN * Kh ^ 2 * ell ^ (2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1)) * (1 + DN) ^ (d : ℝ) := by ring
    rw [e1, e2]
    linarith
  linarith

end DirichletEstimateHelpers

section DirichletSolutionHelpers
open scoped ContDiff



/-- The interior-core constant (as in `aux_rem_resolved_microscopic_neumann_local`). -/
def aux_rem_resolved_microscopic_dir_Cb {d : ℕ} (W : SmallPerturbationInput d) (p1 : ℝ) : ℝ :=
  2 * W.C p1 ^ 2 * Real.exp 1 ^ 2 + W.C p1 ^ 2 * Real.exp 1 + 1

/-- The Dirichlet one-centre constant: `4 Cb` and the datum constant. -/
def aux_rem_resolved_microscopic_dir_Cbase {d : ℕ} (W : SmallPerturbationInput d) (p1 : ℝ) : ℝ :=
  max (4 * aux_rem_resolved_microscopic_dir_Cb W p1)
    (2 * aux_rem_resolved_microscopic_dir_Cb W p1 * (2 * (d : ℝ)) * (6 : ℝ) ^ d +
      16 * aux_rem_resolved_microscopic_dir_Cb W p1 * ((d : ℝ) * Real.exp 1) ^ 2 + 2 * (d : ℝ))

theorem aux_rem_resolved_microscopic_dir_Cb_props {d : ℕ} (W : SmallPerturbationInput d)
    (p1 c : ℝ) (hc1 : c ≤ 1) :
    1 ≤ aux_rem_resolved_microscopic_dir_Cb W p1 ∧
    2 * W.C p1 ^ 2 * Real.exp c ^ 2 ≤ aux_rem_resolved_microscopic_dir_Cb W p1 ∧
    W.C p1 ^ 2 * Real.exp c / 2 ≤ aux_rem_resolved_microscopic_dir_Cb W p1 := by
  unfold aux_rem_resolved_microscopic_dir_Cb
  have hCw : 0 ≤ W.C p1 ^ 2 := sq_nonneg _
  have he1 : Real.exp c ≤ Real.exp 1 := Real.exp_le_exp.2 hc1
  have hepos := Real.exp_pos c
  refine ⟨?_, ?_, ?_⟩
  · have : 0 ≤ 2 * W.C p1 ^ 2 * Real.exp 1 ^ 2 + W.C p1 ^ 2 * Real.exp 1 := by positivity
    linarith
  · have h1 : Real.exp c ^ 2 ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ hepos.le he1 2
    have h2 : 2 * W.C p1 ^ 2 * Real.exp c ^ 2 ≤ 2 * W.C p1 ^ 2 * Real.exp 1 ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 0 ≤ W.C p1 ^ 2 * Real.exp 1 := by positivity
    linarith
  · have h2 : W.C p1 ^ 2 * Real.exp c ≤ W.C p1 ^ 2 * Real.exp 1 :=
      mul_le_mul_of_nonneg_left he1 hCw
    have h3 : 0 ≤ 2 * W.C p1 ^ 2 * Real.exp 1 ^ 2 := by positivity
    have h4 : 0 ≤ W.C p1 ^ 2 * Real.exp c := by positivity
    linarith

theorem aux_rem_resolved_microscopic_dir_Cbase_props {d : ℕ} (W : SmallPerturbationInput d)
    (p1 c : ℝ) (hc1 : c ≤ 1) :
    4 * aux_rem_resolved_microscopic_dir_Cb W p1 ≤ aux_rem_resolved_microscopic_dir_Cbase W p1 ∧
    2 * aux_rem_resolved_microscopic_dir_Cb W p1 * (2 * (d : ℝ)) * (6 : ℝ) ^ d +
      16 * aux_rem_resolved_microscopic_dir_Cb W p1 * ((d : ℝ) * Real.exp c) ^ 2 + 2 * (d : ℝ) ≤
      aux_rem_resolved_microscopic_dir_Cbase W p1 ∧
    1 ≤ aux_rem_resolved_microscopic_dir_Cbase W p1 ∧
    2 * (d : ℝ) ≤ aux_rem_resolved_microscopic_dir_Cbase W p1 := by
  have hCb := (aux_rem_resolved_microscopic_dir_Cb_props W p1 c hc1).1
  set Cb := aux_rem_resolved_microscopic_dir_Cb W p1
  have hm1 := le_max_left (4 * Cb) (2 * Cb * (2 * (d : ℝ)) * (6 : ℝ) ^ d +
      16 * Cb * ((d : ℝ) * Real.exp 1) ^ 2 + 2 * (d : ℝ))
  have hm2 := le_max_right (4 * Cb) (2 * Cb * (2 * (d : ℝ)) * (6 : ℝ) ^ d +
      16 * Cb * ((d : ℝ) * Real.exp 1) ^ 2 + 2 * (d : ℝ))
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hexp : ((d : ℝ) * Real.exp c) ^ 2 ≤ ((d : ℝ) * Real.exp 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hc1) hd) 2
  have hA : 16 * Cb * ((d : ℝ) * Real.exp c) ^ 2 ≤ 16 * Cb * ((d : ℝ) * Real.exp 1) ^ 2 :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  have hB : 0 ≤ 2 * Cb * (2 * (d : ℝ)) * (6 : ℝ) ^ d := by positivity
  have hC' : 0 ≤ 16 * Cb * ((d : ℝ) * Real.exp 1) ^ 2 := by positivity
  refine ⟨hm1, ?_, ?_, ?_⟩
  · change _ ≤ max _ _
    linarith
  · change _ ≤ max _ _
    linarith
  · change _ ≤ max _ _
    linarith

/-- **Statement Dirichlet clause (5)** for every `C ≥ Cbase` and `0 < c ≤ min (1/16) (W.osc p1)`. -/
theorem aux_rem_resolved_microscopic_dir_clause5 {d : ℕ} (W : SmallPerturbationInput d)
    (p1 : ℝ) (hp1 : 2 ≤ p1) (C c : ℝ) (hc : 0 < c) (hc16 : c ≤ 1 / 16) (hcosc : c ≤ W.osc p1)
    (hC : aux_rem_resolved_microscopic_dir_Cbase W p1 ≤ C)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ))
    (haA : a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (DN mN MN : ℝ) (hDN : 0 ≤ DN) (hmN : 0 < mN)
    (hAK : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN)
    (hlog : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hfb : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf)
    (h : SpatialCoordinates d → ℝ) (hh : ContDiff ℝ 2 h)
    (hdata u : weakSobolevGraph (unitNeumannCube d))
    (hhd : ((hdata : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] h)
    (hsol : SolvesDirichlet a f hdata u)
    (G : SpatialCoordinates d → ℝ)
    (hG2 : ∀ ψ : killedSobolevGraph (unitNeumannCube d),
      sobolevCoefficientForm a (hdata : SobolevData (unitNeumannCube d)) (ψ : SobolevData (unitNeumannCube d)) =
        -∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), G x * (ψ : SobolevData (unitNeumannCube d)).1 x)
    (hGm : Measurable G) (BG : ℝ) (hBG : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |G y| ≤ BG)
    (hGloc : ∀ Kg Kh2 : ℝ, 0 ≤ Kg → 0 ≤ Kh2 →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), ‖fderiv ℝ h y‖ ≤ Kg) →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ Kh2) →
      ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), dist y x < (c * eps / (1 + DN)) →
        |G y| ≤ (d : ℝ) * Real.exp c * A x * (Kh2 + (c * eps / (1 + DN))⁻¹ * Kg))
    (x : SpatialCoordinates d) (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) (r : ℝ) (hr : 0 < r) (hrell : r ≤ (c * eps / (1 + DN))) :
    (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d))).2 i y) ^ 2) ≤ C * (r / (c * eps / (1 + DN))) ^ ((d : ℝ) - 2 * (d : ℝ) / p1) * (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < (C * eps) / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d))).2 i y) ^ 2) +
      C * mN⁻¹ * Kf ^ 2 * (c * eps / (1 + DN)) ^ (2 + 2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) +
      C * MN * c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) h ^ 2 * (1 + DN) ^ (d : ℝ) * (c * eps / (1 + DN)) ^ (2 * (d : ℝ) / p1) *
        r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) := by
  have hc1 : c ≤ 1 := by linarith
  have hCb := aux_rem_resolved_microscopic_dir_Cb_props W p1 c hc1
  rcases hCb with ⟨hCb1, hC1, hC2⟩
  have hCB := aux_rem_resolved_microscopic_dir_Cbase_props W p1 c hc1
  rcases hCB with ⟨hC4, hCd, hCone, _⟩
  have hc2 := aux_rem_resolved_microscopic_dir_c2_parts (closure (unitNeumannCube d : Set (SpatialCoordinates d)))
    (aux_rem_resolved_microscopic_unit_closure_isCompact d) h hh
  rcases hc2 with ⟨Kg, Kh2, hKg, hKh2, hgK, hh2K, hKgh, hKh2h⟩
  have h1DN : 0 < 1 + DN := by linarith
  have hce : 0 < c * eps := mul_pos hc heps
  have hell : 0 < (c * eps / (1 + DN)) := div_pos hce h1DN
  have hell_le : (c * eps / (1 + DN)) ≤ c * eps := div_le_self hce.le (by linarith)
  have hceps : c * eps ≤ eps / 16 := by nlinarith
  have hell14 : (c * eps / (1 + DN)) ≤ 1 / 4 := by linarith
  have hδ : DN / eps * (c * eps / (1 + DN)) ≤ c :=
    aux_rem_resolved_microscopic_dir_rate_mul_ell c eps DN hc heps hDN
  have h6 : 6 * (c * eps / (1 + DN)) ≤ C * eps := by
    have : eps ≤ C * eps := le_mul_of_one_le_left heps.le (hCone.trans hC)
    linarith
  exact aux_rem_resolved_microscopic_dir_clause5_at W p1 hp1 _ c hcosc (by linarith) hC1 hC2
    eps heps a A haA DN mN MN hDN hmN hAK hlog f hf Kf hKf hfb h hh hdata u hhd hsol G hG2 hGm
    BG hBG (c * eps / (1 + DN)) hell hell14 hδ Kg Kh2 _ hKg hKh2 hgK hKgh hKh2h
    (hGloc Kg Kh2 hKg hKh2 hgK hh2K) C (hC4.trans hC) (hCd.trans hC) h6 x hx r hr hrell

/-- Real algebra of the matched Dirichlet estimate below `ell`. -/
theorem aux_rem_resolved_microscopic_dir_matched_small
    (Gr G0 M Q' E R MN Kh2' DNd Ld mNi Kf2 Kmac et1 ct cdt DNt ett rt epsd Z3 C : ℝ)
    (h0 : Gr ≤ M * Q' * G0 + M * mNi * Kf2 * E * R + M * MN * Kh2' * DNd * Ld * R)
    (hG : G0 ≤ Kmac * et1)
    (hmacro : Q' * (Kmac * et1) ≤ ct * DNt * ett * Kmac * rt)
    (hdat : E * R ≤ epsd * rt)
    (hX3 : MN * Kh2' * DNd * Ld * R ≤ cdt * Z3 * rt)
    (hM : 0 ≤ M) (hQ : 0 ≤ Q') (hmK : 0 ≤ mNi * Kf2) (hct : 1 ≤ ct) (hcdt : cdt ≤ ct)
    (hZ3 : 0 ≤ Z3) (hrt : 0 ≤ rt) (hepsd : 0 ≤ epsd) (hX : 0 ≤ DNt * ett * Kmac)
    (hC : M * ct ≤ C) :
    Gr ≤ C * (DNt * ett * Kmac + mNi * Kf2 * epsd + Z3) * rt := by
  have k1 : M * Q' * G0 ≤ M * (ct * DNt * ett * Kmac * rt) := by
    have a1 := mul_le_mul_of_nonneg_left hG (mul_nonneg hM hQ)
    have a2 := mul_le_mul_of_nonneg_left hmacro hM
    calc M * Q' * G0 ≤ M * Q' * (Kmac * et1) := a1
      _ = M * (Q' * (Kmac * et1)) := by ring
      _ ≤ _ := a2
  have k2 : M * mNi * Kf2 * E * R ≤ ct * (M * (mNi * Kf2) * (epsd * rt)) := by
    have a1 := mul_le_mul_of_nonneg_left hdat (mul_nonneg hM hmK)
    have a2 : M * (mNi * Kf2) * (epsd * rt) ≤ ct * (M * (mNi * Kf2) * (epsd * rt)) :=
      le_mul_of_one_le_left (by positivity) hct
    calc M * mNi * Kf2 * E * R = M * (mNi * Kf2) * (E * R) := by ring
      _ ≤ M * (mNi * Kf2) * (epsd * rt) := a1
      _ ≤ _ := a2
  have k3 : M * MN * Kh2' * DNd * Ld * R ≤ M * (ct * Z3 * rt) := by
    have a1 : cdt * Z3 * rt ≤ ct * Z3 * rt :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcdt hZ3) hrt
    have a2 := mul_le_mul_of_nonneg_left (hX3.trans a1) hM
    calc M * MN * Kh2' * DNd * Ld * R = M * (MN * Kh2' * DNd * Ld * R) := by ring
      _ ≤ _ := a2
  have hct0 : 0 ≤ ct := by linarith
  have hW : 0 ≤ (DNt * ett * Kmac + mNi * Kf2 * epsd + Z3) * rt := by positivity
  have k4 : M * ct * ((DNt * ett * Kmac + mNi * Kf2 * epsd + Z3) * rt) ≤
      C * ((DNt * ett * Kmac + mNi * Kf2 * epsd + Z3) * rt) :=
    mul_le_mul_of_nonneg_right hC hW
  have k5 : M * ct * ((DNt * ett * Kmac + mNi * Kf2 * epsd + Z3) * rt) =
      M * (ct * DNt * ett * Kmac * rt) + ct * (M * (mNi * Kf2) * (epsd * rt)) +
        M * (ct * Z3 * rt) := by ring
  have k6 : C * ((DNt * ett * Kmac + mNi * Kf2 * epsd + Z3) * rt) =
      C * (DNt * ett * Kmac + mNi * Kf2 * epsd + Z3) * rt := by ring
  linarith

/-- **Statement Dirichlet clause (6)**, the matched estimate, for every `C ≥ Cbase c^{-t}`. -/
theorem aux_rem_resolved_microscopic_dir_clause6 {d : ℕ} (W : SmallPerturbationInput d)
    (p1 t t1 : ℝ) (hp1 : 2 ≤ p1) (htpos : 0 < t) (htd : t < (d : ℝ))
    (htp : t < ((d : ℝ) - 2 * (d : ℝ) / p1)) (C c : ℝ) (hc : 0 < c) (hc16 : c ≤ 1 / 16) (hcosc : c ≤ W.osc p1)
    (hC : aux_rem_resolved_microscopic_dir_Cbase W p1 * c ^ (-t) ≤ C)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (a : PositiveCoefficient (unitNeumannCube d)) (A : C(SpatialCoordinates d, ℝ))
    (haA : a.val =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] A)
    (DN mN MN : ℝ) (hDN : 0 ≤ DN) (hmN : 0 < mN)
    (hAK : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), mN ≤ A y ∧ A y ≤ MN)
    (hlog : ∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ z ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)),
      |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hfb : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf)
    (h : SpatialCoordinates d → ℝ) (hh : ContDiff ℝ 2 h)
    (hdata u : weakSobolevGraph (unitNeumannCube d))
    (hhd : ((hdata : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] h)
    (hsol : SolvesDirichlet a f hdata u)
    (G : SpatialCoordinates d → ℝ)
    (hG2 : ∀ ψ : killedSobolevGraph (unitNeumannCube d),
      sobolevCoefficientForm a (hdata : SobolevData (unitNeumannCube d)) (ψ : SobolevData (unitNeumannCube d)) =
        -∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), G x * (ψ : SobolevData (unitNeumannCube d)).1 x)
    (hGm : Measurable G) (BG : ℝ) (hBG : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), |G y| ≤ BG)
    (hGloc : ∀ Kg Kh2 : ℝ, 0 ≤ Kg → 0 ≤ Kh2 →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), ‖fderiv ℝ h y‖ ≤ Kg) →
      (∀ y ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)), ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ Kh2) →
      ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), dist y x < (c * eps / (1 + DN)) →
        |G y| ≤ (d : ℝ) * Real.exp c * A x * (Kh2 + (c * eps / (1 + DN))⁻¹ * Kg))
    (Kmac : ℝ) (hKmac : 0 ≤ Kmac) (x : SpatialCoordinates d) (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (hmac : (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < (C * eps) / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d))).2 i y) ^ 2) ≤ Kmac * eps ^ t1)
    (r : ℝ) (hr : 0 < r) (hreps : r ≤ eps) :
    (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d))).2 i y) ^ 2) ≤ C * ((1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
      mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t) +
      MN * c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) h ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t) * r ^ t := by
  have hc1 : c ≤ 1 := by linarith
  have hCB := aux_rem_resolved_microscopic_dir_Cbase_props W p1 c hc1
  rcases hCB with ⟨_, _, hCone, _⟩
  set Cb := aux_rem_resolved_microscopic_dir_Cbase W p1 with hCbdef
  have hct : 1 ≤ c ^ (-t) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc hc1 (by linarith)
  have hCb0 : 0 < Cb := lt_of_lt_of_le one_pos hCone
  have hCge : Cb ≤ C := le_trans (le_mul_of_one_le_right hCb0.le hct) hC
  have hCone' : 1 ≤ C := hCone.trans hCge
  have hAQ : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)), 0 ≤ A y ∧ A y ≤ MN :=
    fun y hy => ⟨hmN.le.trans (hAK y (subset_closure hy)).1, (hAK y (subset_closure hy)).2⟩
  have hMN : 0 ≤ MN := (hAQ x hx).1.trans (hAQ x hx).2
  have hmono : ∀ r1 r2 : ℝ, r1 ≤ r2 → (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r1 / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d))).2 i y) ^ 2) ≤ (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r2 / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d))).2 i y) ^ 2) := fun r1 r2 hle =>
    aux_rem_resolved_microscopic_neumann_gamma_mono A A.continuous MN hAQ (u : SobolevData (unitNeumannCube d)) x hle
  have hGmac : (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < (Cb * eps) / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d))).2 i y) ^ 2) ≤ Kmac * eps ^ t1 :=
    (hmono _ _ (mul_le_mul_of_nonneg_right hCge heps.le)).trans hmac
  have h1DN : 0 < 1 + DN := by linarith
  have hell : 0 < (c * eps / (1 + DN)) := div_pos (mul_pos hc heps) h1DN
  have hrt : 0 < r ^ t := Real.rpow_pos_of_pos hr t
  by_cases hrell : r ≤ (c * eps / (1 + DN))
  · have hA0 := aux_rem_resolved_microscopic_dir_clause5 W p1 hp1 Cb c hc hc16 hcosc le_rfl eps heps
      heps1 a A haA DN mN MN hDN hmN hAK hlog f hf Kf hKf hfb h hh hdata u hhd hsol G hG2 hGm
      BG hBG hGloc x hx r hr hrell
    have hmacro := aux_rem_resolved_microscopic_neumann_macro d p1 t t1 c eps DN r Kmac htp
      hc heps hDN hKmac hr hrell
    have helleps : (c * eps / (1 + DN)) ≤ eps := by
      have h1 : (c * eps / (1 + DN)) ≤ c * eps := div_le_self (mul_pos hc heps).le (by linarith)
      have h2 : c * eps ≤ eps := by nlinarith
      linarith
    have hdat := aux_rem_resolved_microscopic_neumann_datum d p1 t (c * eps / (1 + DN)) eps r htp (by linarith)
      hell helleps hr hrell
    have hpa := (aux_rem_resolved_microscopic_power_absorption d p1 t c eps DN MN
      (c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) h) r hp1 htp hc heps hDN hMN hr hrell).1
    have hX3 : MN * c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) h ^ 2 * (1 + DN) ^ (d : ℝ) * (c * eps / (1 + DN)) ^ (2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) ≤
        c ^ ((d : ℝ) - t) * (MN * c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) h ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t) * r ^ t := by
      have hsplit : r ^ ((d : ℝ) - 2 * (d : ℝ) / p1) = r ^ (((d : ℝ) - 2 * (d : ℝ) / p1) - t) * r ^ t := by
        rw [← Real.rpow_add hr]; congr 1; ring
      have := mul_le_mul_of_nonneg_right hpa hrt.le
      calc MN * c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) h ^ 2 * (1 + DN) ^ (d : ℝ) * (c * eps / (1 + DN)) ^ (2 * (d : ℝ) / p1) * r ^ ((d : ℝ) - 2 * (d : ℝ) / p1)
          = MN * c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) h ^ 2 * (1 + DN) ^ (d : ℝ) * (c * eps / (1 + DN)) ^ (2 * (d : ℝ) / p1) *
              r ^ (((d : ℝ) - 2 * (d : ℝ) / p1) - t) * r ^ t := by rw [hsplit]; ring
        _ ≤ c ^ ((d : ℝ) - t) * MN * c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) h ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t * r ^ t :=
            this
        _ = _ := by ring
    have hcdt : c ^ ((d : ℝ) - t) ≤ c ^ (-t) := by
      have h1 : c ^ ((d : ℝ) - t) ≤ 1 := Real.rpow_le_one hc.le hc1 (by linarith)
      linarith
    have hZ3 : 0 ≤ MN * c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) h ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t := by
      have := Real.rpow_nonneg heps.le ((d : ℝ) - t)
      have := Real.rpow_nonneg h1DN.le t
      positivity
    have hres := aux_rem_resolved_microscopic_dir_matched_small _ _ Cb _ _ _ MN (c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) h ^ 2)
      ((1 + DN) ^ (d : ℝ)) ((c * eps / (1 + DN)) ^ (2 * (d : ℝ) / p1)) mN⁻¹ (Kf ^ 2) Kmac (eps ^ t1) (c ^ (-t))
      (c ^ ((d : ℝ) - t)) ((1 + DN) ^ t) (eps ^ (t1 - t)) (r ^ t) (eps ^ ((d : ℝ) + 2 - t))
      (MN * c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) h ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t) C
      (by simpa only [mul_assoc] using hA0) hGmac hmacro hdat hX3 hCb0.le
      (Real.rpow_nonneg (div_nonneg hr.le hell.le) _)
      (mul_nonneg (inv_nonneg.2 hmN.le) (sq_nonneg _)) hct hcdt hZ3 hrt.le
      (Real.rpow_nonneg heps.le _)
      (by have := Real.rpow_nonneg h1DN.le t; have := Real.rpow_nonneg heps.le (t1 - t); positivity)
      hC
    exact hres
  · push Not at hrell
    have heps_le : eps ≤ c⁻¹ * (1 + DN) * r := by
      have : c * eps < r * (1 + DN) := (div_lt_iff₀ h1DN).1 hrell
      rw [inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hc]
      linarith
    have hepst : eps ^ t ≤ c ^ (-t) * (1 + DN) ^ t * r ^ t := by
      calc eps ^ t ≤ (c⁻¹ * (1 + DN) * r) ^ t := Real.rpow_le_rpow heps.le heps_le htpos.le
        _ = c ^ (-t) * (1 + DN) ^ t * r ^ t := by
          rw [Real.mul_rpow (by positivity) hr.le, Real.mul_rpow (by positivity) h1DN.le,
            Real.inv_rpow hc.le, Real.rpow_neg hc.le]
    have hsplit : eps ^ t1 = eps ^ (t1 - t) * eps ^ t := by
      rw [← Real.rpow_add heps]; congr 1; ring
    have hG : (∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩ (unitNeumannCube d : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (((u : SobolevData (unitNeumannCube d))).2 i y) ^ 2) ≤ Kmac * (eps ^ (t1 - t) * eps ^ t) := by
      rw [← hsplit]
      exact (hmono _ _ (hreps.trans (le_mul_of_one_le_left heps.le hCone'))).trans hmac
    have hY : 0 ≤ mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t) +
        MN * c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) h ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t := by
      have := inv_nonneg.2 hmN.le
      have := Real.rpow_nonneg heps.le ((d : ℝ) + 2 - t)
      have := Real.rpow_nonneg heps.le ((d : ℝ) - t)
      have := Real.rpow_nonneg h1DN.le t
      positivity
    have hres := aux_rem_resolved_microscopic_neumann_matched_large _ _ _ _ _ _ _ _ Cb C hG hepst
      hKmac (Real.rpow_nonneg heps.le _) (by positivity) (Real.rpow_nonneg h1DN.le t) hrt.le hY
      hCone (by rw [mul_comm] at hC; linarith [hC])
    have e : (1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
        (mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t) +
          MN * c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) h ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t) =
        (1 + DN) ^ t * eps ^ (t1 - t) * Kmac + mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t) +
          MN * c2Norm (closure (unitNeumannCube d : Set (SpatialCoordinates d))) h ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t := by ring
    rw [e] at hres
    exact hres

end DirichletSolutionHelpers

section DirichletBlockHelpers
open scoped ContDiff



/-- **The Dirichlet conjunct of `rem_resolved_microscopic`, exact frozen text**, for
`0 < c ≤ min (1/16) (W.osc p1)` and `C ≥ Cbase c^(-t)`.  One datum-flux source `G` (the
divergence of the flux with the McShane extension of `A`) serves clauses (1)--(3) and, through
its local bound, the estimates (5) and (6). -/
theorem aux_rem_resolved_microscopic_dir_block (d : ℕ) (hd : 2 ≤ d) (W : SmallPerturbationInput d)
    (p1 t t1 : ℝ) (hp1 : 2 ≤ p1) (ht : (d : ℝ) - 1 < t)
    (htp : t < (d : ℝ) - 2 * (d : ℝ) / p1)
    (C c : ℝ) (hc : 0 < c) (hc16 : c ≤ 1 / 16) (hcosc : c ≤ W.osc p1)
    (hC : aux_rem_resolved_microscopic_dir_Cbase W p1 * c ^ (-t) ≤ C) :
    let q1 : ℝ := (d : ℝ) - 2 * (d : ℝ) / p1
    let Q := unitNeumannCube d
    let K := closure (Q : Set (SpatialCoordinates d))
    ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∀ (a : PositiveCoefficient Q) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ K, mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ K, ∀ z ∈ K, |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ Q, |f y| ≤ Kf) →
      let ell : ℝ := c * eps / (1 + DN)
      let gamma := fun (v : SobolevData Q) (x : SpatialCoordinates d) (r : ℝ) =>
        ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩
          (Q : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (v.2 i y) ^ 2
      (∀ h : SpatialCoordinates d → ℝ, ContDiff ℝ 2 h →
        ∀ hdata u : weakSobolevGraph Q,
        (hdata : SobolevData Q).1 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] h →
        SolvesDirichlet a f hdata u →
        let Kh := c2Norm K h
        let v : SobolevData Q := (u : SobolevData Q) - (hdata : SobolevData Q)
        -- Subtract h first: E(v,ψ) = ∫(f+G)ψ when E(h,ψ) = -∫Gψ.
        -- The same datum-flux source G is used in its bound and the odd reflection.
        (∃ G : SpatialCoordinates d → ℝ,
          --  11-12: ‖∇·(A_N ∇h)‖_∞ ≤ C a_* (‖D²h‖_∞ + ℓ_N⁻¹ ‖∇h‖_∞) on the
          -- small-oscillation cube; a_* = A x, a value of A_N there (: a_0)
          (∀ Kg Kh2 : ℝ, 0 ≤ Kg → 0 ≤ Kh2 →
            (∀ y ∈ K, ‖fderiv ℝ h y‖ ≤ Kg) →
            (∀ y ∈ K, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ Kh2) →
            ∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ y ∈ (Q : Set (SpatialCoordinates d)),
              dist y x < ell → |G y| ≤ C * A x * (Kh2 + ell⁻¹ * Kg)) ∧
          (∀ ψ : killedSobolevGraph Q,
            sobolevCoefficientForm a (hdata : SobolevData Q) (ψ : SobolevData Q) =
              -∫ x in (Q : Set (SpatialCoordinates d)),
                G x * (ψ : SobolevData Q).1 x) ∧
          (∀ I P : Finset (Fin d),
            let zface := foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P
            let T := coordinateFold zface I P
            let V := foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P
            let sgn : SpatialCoordinates d → ℝ := fun x =>
              ∏ i ∈ I, (if 0 ≤ coordinateReflectionSign P i * (x i - zface i) then (1 : ℝ) else -1)
            ∃ (af : PositiveCoefficient V) (vf : weakSobolevGraph V),
              ((af.val : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] fun x => A (T x)) ∧
              (((vf : SobolevData V).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))]
                fun x => sgn x * v.1 (T x)) ∧
              (∀ ψ : killedSobolevGraph V,
                sobolevCoefficientForm af (vf : SobolevData V) (ψ : SobolevData V) =
                  ∫ x in (V : Set (SpatialCoordinates d)),
                    sgn x * (f (T x) + G (T x)) * (ψ : SobolevData V).1 x))) ∧
        --  10: Γ_N(v) ≤ 2 Γ_N(u) + C M_N ‖∇h‖_∞² ε_N^d on the parent cube
        -- (the parent has volume (C ε_N)^d; the paper's generic constant there is this
        
        (∀ Kg : ℝ, 0 ≤ Kg → (∀ y ∈ K, ‖fderiv ℝ h y‖ ≤ Kg) →
          ∀ x ∈ Q, gamma v x (C * eps) ≤ 2 * gamma u x (C * eps) +
            C * MN * Kg ^ 2 * (C * eps) ^ (d : ℝ)) ∧
        (∀ x ∈ Q, ∀ r : ℝ, 0 < r → r ≤ ell →
          gamma u x r ≤ C * (r / ell) ^ q1 * gamma u x (C * eps) +
            C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * r ^ q1 +
            C * MN * Kh ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) * r ^ q1) ∧
        (∀ Kmac : ℝ, 0 ≤ Kmac → ∀ x ∈ Q,
          gamma u x (C * eps) ≤ Kmac * eps ^ t1 →
          ∀ r : ℝ, 0 < r → r ≤ eps →
          gamma u x r ≤ C * ((1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
            mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t) +
            MN * Kh ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t) * r ^ t)) := by
  intro q1 Q K eps heps heps1 a A haA DN mN MN hDN hmN hAK hlog f hf Kf hKf hfb ell gamma
    h hh hdata u hhd hsol Kh v
  have hc1 : c ≤ 1 := by linarith
  have hd1 : (1 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have htpos : 0 < t := by linarith
  have htd : t < (d : ℝ) := by
    have : 0 ≤ 2 * (d : ℝ) / p1 := by positivity
    linarith
  have hCB := aux_rem_resolved_microscopic_dir_Cbase_props W p1 c hc1
  rcases hCB with ⟨_, _, hCone, hC2d⟩
  have hct : 1 ≤ c ^ (-t) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc hc1 (by linarith)
  have hCge : aux_rem_resolved_microscopic_dir_Cbase W p1 ≤ C :=
    le_trans (le_mul_of_one_le_right (le_trans zero_le_one hCone) hct) hC
  have hC2d' : 2 * (d : ℝ) ≤ C := hC2d.trans hCge
  have hCd : (d : ℝ) ≤ C := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hC0 : 0 < C := lt_of_lt_of_le one_pos (hCone.trans hCge)
  have hpkg := aux_rem_resolved_microscopic_dir_flux_package d C c hCd hc hc1 eps heps a A haA
    DN mN MN hDN hmN hAK hlog h hh hdata hhd
  rcases hpkg with ⟨G, _, hG2, hGloc, hGm, BG, hBG⟩
  have hMN : 0 ≤ MN := by
    have hx0 := aux_rem_resolved_microscopic_unit_center_mem d
    exact (hmN.le.trans (hAK _ (subset_closure hx0)).1).trans (hAK _ (subset_closure hx0)).2
  have hdC : (d : ℝ) * Real.exp c ≤ C := by
    have hexp : Real.exp c ≤ 2 :=
      calc Real.exp c ≤ Real.exp (Real.log 2) :=
            Real.exp_le_exp.2 (by linarith [Real.log_two_gt_d9])
        _ = 2 := Real.exp_log (by norm_num)
    have h2 := mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    linarith
  have hGlocC : ∀ Kg Kh2 : ℝ, 0 ≤ Kg → 0 ≤ Kh2 →
      (∀ y ∈ K, ‖fderiv ℝ h y‖ ≤ Kg) →
      (∀ y ∈ K, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ Kh2) →
      ∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ y ∈ (Q : Set (SpatialCoordinates d)),
        dist y x < ell → |G y| ≤ C * A x * (Kh2 + ell⁻¹ * Kg) := by
    intro Kg Kh2 hKg hKh2 hg hh2 x hx y hy hyx
    have hax : 0 < A x := hmN.trans_le (hAK x (subset_closure hx)).1
    have hell : 0 < ell := div_pos (mul_pos hc heps) (by linarith)
    have hinner : 0 ≤ Kh2 + ell⁻¹ * Kg :=
      add_nonneg hKh2 (mul_nonneg (inv_nonneg.2 hell.le) hKg)
    calc |G y| ≤ (d : ℝ) * Real.exp c * A x * (Kh2 + ell⁻¹ * Kg) :=
          hGloc Kg Kh2 hKg hKh2 hg hh2 x hx y hy hyx
      _ ≤ C * A x * (Kh2 + ell⁻¹ * Kg) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdC hax.le) hinner
  refine ⟨⟨G, hGlocC, hG2, ?_⟩, ?_, ?_, ?_⟩
  · have hfL2 := aux_rem_resolved_microscopic_bounded_memLp_two f hf Kf hfb
    have hGL2 := aux_rem_resolved_microscopic_bounded_memLp_two G hGm BG hBG
    have hv := aux_rem_resolved_microscopic_v_equation a f G hfL2 hGL2 hdata u hsol hG2
    rcases hv with ⟨hvk, hveq⟩
    have hFB : ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
        |f y + G y| ≤ Kf + BG := fun y hy =>
      (abs_add_le _ _).trans (add_le_add (hfb y hy) (hBG y hy))
    intro I P
    exact aux_rem_resolved_microscopic_multiface_scalar (fun _ => (1 / 2 : ℝ)) 1 one_pos I P
      (A : SpatialCoordinates d → ℝ) (fun y => f y + G y) a haA v hvk (hf.add hGm) (Kf + BG)
      hFB (fun ψ hψ => hveq ⟨ψ, hψ⟩)
  · intro Kg hKg hgK x _
    exact aux_micro_dirichlet_frozen_parent_energy a A haA MN Kg C eps hMN hKg hC0 hC2d' heps
      (fun y hy => ⟨hmN.le.trans (hAK y hy).1, (hAK y hy).2⟩) h hh hdata u hhd hgK x
  · intro x hx r hr hrell
    exact aux_rem_resolved_microscopic_dir_clause5 W p1 hp1 C c hc hc16 hcosc hCge eps heps heps1
      a A haA DN mN MN hDN hmN hAK hlog f hf Kf hKf hfb h hh hdata u hhd hsol G hG2 hGm BG hBG
      hGloc x hx r hr hrell
  · intro Kmac hKmac x hx hmac r hr hreps
    exact aux_rem_resolved_microscopic_dir_clause6 W p1 t t1 hp1 htpos htd htp C c hc hc16 hcosc hC
      eps heps heps1 a A haA DN mN MN hDN hmN hAK hlog f hf Kf hKf hfb h hh hdata u hhd hsol G hG2
      hGm BG hBG hGloc Kmac hKmac x hx hmac r hr hreps

end DirichletBlockHelpers



theorem rem_resolved_microscopic
    (d : ℕ) (hd : 2 ≤ d) (W : SmallPerturbationInput d)
    (p1 t t1 : ℝ) (hp1 : 2 ≤ p1) (ht : (d : ℝ) - 1 < t)
    (htt1 : t < t1) (ht1d : t1 < (d : ℝ))
    (htp : t < (d : ℝ) - 2 * (d : ℝ) / p1) :
    let q1 : ℝ := (d : ℝ) - 2 * (d : ℝ) / p1
    let Q := unitNeumannCube d
    let K := closure (Q : Set (SpatialCoordinates d))
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c ≤ 1 / 16 ∧
    (∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∀ (a : PositiveCoefficient Q) (A : C(SpatialCoordinates d, ℝ)),
      a.val =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] A →
      ∀ DN mN MN : ℝ, 0 ≤ DN → 0 < mN →
      (∀ y ∈ K, mN ≤ A y ∧ A y ≤ MN) →
      (∀ y ∈ K, ∀ z ∈ K, |Real.log (A y) - Real.log (A z)| ≤ DN / eps * dist y z) →
      ∀ f : SpatialCoordinates d → ℝ, Measurable f →
      ∀ Kf : ℝ, 0 ≤ Kf → (∀ y ∈ Q, |f y| ≤ Kf) →
      let ell : ℝ := c * eps / (1 + DN)
      let gamma := fun (v : SobolevData Q) (x : SpatialCoordinates d) (r : ℝ) =>
        ∫ y in {y : SpatialCoordinates d | ∀ i : Fin d, |y i - x i| < r / 2} ∩
          (Q : Set (SpatialCoordinates d)), A y * ∑ i : Fin d, (v.2 i y) ^ 2
      (∀ I P : Finset (Fin d),
        let zface := foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P
        let T := coordinateFold zface I P
        let U := foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P
        ∀ x ∈ closure (U : Set (SpatialCoordinates d)),
        ∀ y ∈ closure (U : Set (SpatialCoordinates d)),
          |Real.log (A (T x)) - Real.log (A (T y))| ≤ DN / eps * dist x y) ∧
      (∀ u : meanZeroSobolevGraph Q, SolvesNeumann a f u →
        (∀ x ∈ Q, ∀ r : ℝ, 0 < r → r ≤ ell →
          gamma u x r ≤ C * (r / ell) ^ q1 * gamma u x (C * eps) +
            C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * r ^ q1) ∧
        (∀ Kmac : ℝ, 0 ≤ Kmac → ∀ x ∈ Q,
          gamma u x (C * eps) ≤ Kmac * eps ^ t1 →
          ∀ r : ℝ, 0 < r → r ≤ eps →
          gamma u x r ≤ C * ((1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
            mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t)) * r ^ t)) ∧
      (∀ h : SpatialCoordinates d → ℝ, ContDiff ℝ 2 h →
        ∀ hdata u : weakSobolevGraph Q,
        (hdata : SobolevData Q).1 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] h →
        SolvesDirichlet a f hdata u →
        let Kh := c2Norm K h
        let v : SobolevData Q := (u : SobolevData Q) - (hdata : SobolevData Q)
        -- Subtract h first: E(v,ψ) = ∫(f+G)ψ when E(h,ψ) = -∫Gψ.
        -- The same datum-flux source G is used in its bound and the odd reflection.
        (∃ G : SpatialCoordinates d → ℝ,
          --  11-12: ‖∇·(A_N ∇h)‖_∞ ≤ C a_* (‖D²h‖_∞ + ℓ_N⁻¹ ‖∇h‖_∞) on the
          -- small-oscillation cube; a_* = A x, a value of A_N there (: a_0)
          (∀ Kg Kh2 : ℝ, 0 ≤ Kg → 0 ≤ Kh2 →
            (∀ y ∈ K, ‖fderiv ℝ h y‖ ≤ Kg) →
            (∀ y ∈ K, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ Kh2) →
            ∀ x ∈ (Q : Set (SpatialCoordinates d)), ∀ y ∈ (Q : Set (SpatialCoordinates d)),
              dist y x < ell → |G y| ≤ C * A x * (Kh2 + ell⁻¹ * Kg)) ∧
          (∀ ψ : killedSobolevGraph Q,
            sobolevCoefficientForm a (hdata : SobolevData Q) (ψ : SobolevData Q) =
              -∫ x in (Q : Set (SpatialCoordinates d)),
                G x * (ψ : SobolevData Q).1 x) ∧
          (∀ I P : Finset (Fin d),
            let zface := foldedCubeCenter (fun _ => (1 / 2 : ℝ)) 1 I P
            let T := coordinateFold zface I P
            let V := foldedCube (fun _ => (1 / 2 : ℝ)) 1 one_pos I P
            let sgn : SpatialCoordinates d → ℝ := fun x =>
              ∏ i ∈ I, (if 0 ≤ coordinateReflectionSign P i * (x i - zface i) then (1 : ℝ) else -1)
            ∃ (af : PositiveCoefficient V) (vf : weakSobolevGraph V),
              ((af.val : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))] fun x => A (T x)) ∧
              (((vf : SobolevData V).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (V : Set (SpatialCoordinates d))]
                fun x => sgn x * v.1 (T x)) ∧
              (∀ ψ : killedSobolevGraph V,
                sobolevCoefficientForm af (vf : SobolevData V) (ψ : SobolevData V) =
                  ∫ x in (V : Set (SpatialCoordinates d)),
                    sgn x * (f (T x) + G (T x)) * (ψ : SobolevData V).1 x))) ∧
        --  10: Γ_N(v) ≤ 2 Γ_N(u) + C M_N ‖∇h‖_∞² ε_N^d on the parent cube
        -- (the parent has volume (C ε_N)^d; the paper's generic constant there is this
        
        (∀ Kg : ℝ, 0 ≤ Kg → (∀ y ∈ K, ‖fderiv ℝ h y‖ ≤ Kg) →
          ∀ x ∈ Q, gamma v x (C * eps) ≤ 2 * gamma u x (C * eps) +
            C * MN * Kg ^ 2 * (C * eps) ^ (d : ℝ)) ∧
        (∀ x ∈ Q, ∀ r : ℝ, 0 < r → r ≤ ell →
          gamma u x r ≤ C * (r / ell) ^ q1 * gamma u x (C * eps) +
            C * mN⁻¹ * Kf ^ 2 * ell ^ (2 + 2 * (d : ℝ) / p1) * r ^ q1 +
            C * MN * Kh ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) * r ^ q1) ∧
        (∀ Kmac : ℝ, 0 ≤ Kmac → ∀ x ∈ Q,
          gamma u x (C * eps) ≤ Kmac * eps ^ t1 →
          ∀ r : ℝ, 0 < r → r ≤ eps →
          gamma u x r ≤ C * ((1 + DN) ^ t * eps ^ (t1 - t) * Kmac +
            mN⁻¹ * Kf ^ 2 * eps ^ ((d : ℝ) + 2 - t) +
            MN * Kh ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t) * r ^ t)) ∧
      (∀ Hnorm : ℝ,
        (∀ r : ℝ, 0 < r → r ≤ ell →
          MN * Hnorm ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) * r ^ (q1 - t) ≤
            c ^ ((d : ℝ) - t) * MN * Hnorm ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t) ∧
        MN * Hnorm ^ 2 * (1 + DN) ^ (d : ℝ) * ell ^ (2 * (d : ℝ) / p1) * ell ^ (q1 - t) =
          c ^ ((d : ℝ) - t) * MN * Hnorm ^ 2 * eps ^ ((d : ℝ) - t) * (1 + DN) ^ t)) ∧
    (∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ p : ℝ, 1 ≤ p →
      let q := 2 * p * max 1 t
      ∀ D M mInv Kmac : ℕ → Ω → ℝ,
      ∀ CD CE CK aRate : ℝ, 0 ≤ CD → 0 ≤ CE → 0 ≤ CK → 0 ≤ aRate →
      aRate < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 →
      (∀ N ω, 0 ≤ D N ω ∧ 0 ≤ M N ω ∧ 0 ≤ mInv N ω ∧ 0 ≤ Kmac N ω) →
      (∀ N, MemLp (D N) (ENNReal.ofReal q) P ∧ MemLp (M N) (ENNReal.ofReal q) P ∧
        MemLp (mInv N) (ENNReal.ofReal q) P ∧ MemLp (Kmac N) (ENNReal.ofReal q) P) →
      (∀ N, eLpNorm (D N) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (CD * Real.sqrt (1 + (N : ℝ)))) →
      (∀ N, eLpNorm (fun ω => M N ω + mInv N ω) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (CE * Real.exp (aRate * (N : ℝ)))) →
      (∀ N, eLpNorm (Kmac N) (ENNReal.ofReal q) P ≤ ENNReal.ofReal CK) →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
        eLpNorm (fun ω => (1 + D N ω) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmac N ω)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal B ∧
        eLpNorm (fun ω => mInv N ω * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal B ∧
        eLpNorm (fun ω => M N ω * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) * (1 + D N ω) ^ t)
          (ENNReal.ofReal p) P ≤ ENNReal.ofReal B) := by
  intro q1 Q K
  have hNS := aux_rem_resolved_microscopic_neumann_solution d hd W p1 t t1 hp1 ht htt1 ht1d htp
  rcases hNS with ⟨C0n, c0n, hC0n, hc0n, hc0n16, hNeu⟩
  have hcex : ∃ c : ℝ, c = min c0n (min (1 / 16) (W.osc p1)) := ⟨_, rfl⟩
  rcases hcex with ⟨c, hcdef⟩
  have hc : 0 < c := by
    rw [hcdef]
    exact lt_min hc0n (lt_min (by norm_num) (W.osc_pos p1))
  have hcc0 : c ≤ c0n := by rw [hcdef]; exact min_le_left _ _
  have hc16 : c ≤ 1 / 16 := by
    rw [hcdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hcosc : c ≤ W.osc p1 := by
    rw [hcdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hCex : ∃ C : ℝ,
      C = max C0n (aux_rem_resolved_microscopic_dir_Cbase W p1) * c ^ (-t) := ⟨_, rfl⟩
  rcases hCex with ⟨C, hCdef⟩
  have hcpow : 0 < c ^ (-t) := Real.rpow_pos_of_pos hc _
  have hCn : C0n * c ^ (-t) ≤ C := by
    rw [hCdef]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hcpow.le
  have hCd : aux_rem_resolved_microscopic_dir_Cbase W p1 * c ^ (-t) ≤ C := by
    rw [hCdef]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hcpow.le
  have hC : 0 < C := by
    rw [hCdef]
    exact mul_pos (lt_of_lt_of_le one_pos (hC0n.trans (le_max_left _ _))) hcpow
  have hstat := aux_rem_resolved_microscopic_statistical_conjunct d hd t t1 ht
  refine ⟨C, c, hC, hc, hc16, ?_, hstat⟩
  intro eps heps heps1 a A haA DN mN MN hDN hmN hAK hlog f hf Kf hKf hfb ell gamma
  have hMN : 0 ≤ MN := by
    have hx0 := aux_rem_resolved_microscopic_unit_center_mem d
    exact (hmN.le.trans (hAK _ (subset_closure hx0)).1).trans (hAK _ (subset_closure hx0)).2
  have hell : 0 < ell := div_pos (mul_pos hc heps) (by linarith)
  have hneu := hNeu C c hc hcc0 hCn eps heps heps1 a A haA DN mN MN hDN hmN hAK hlog f hf Kf hKf
    hfb
  have hdir := aux_rem_resolved_microscopic_dir_block d hd W p1 t t1 hp1 ht htp C c hc hc16 hcosc
    hCd eps heps heps1 a A haA DN mN MN hDN hmN hAK hlog f hf Kf hKf hfb
  refine ⟨fun I P => aux_rem_resolved_microscopic_folded_log_modulus d I P A DN eps hDN heps hlog,
    hneu, hdir, fun Hnorm => ⟨fun r hr hrell => ?_, ?_⟩⟩
  · exact (aux_rem_resolved_microscopic_power_absorption d p1 t c eps DN MN Hnorm r hp1 htp hc heps
      hDN hMN hr hrell).1
  · exact (aux_rem_resolved_microscopic_power_absorption d p1 t c eps DN MN Hnorm ell hp1 htp hc
      heps hDN hMN hell le_rfl).2

end SubdiffusiveProcess.Paper
