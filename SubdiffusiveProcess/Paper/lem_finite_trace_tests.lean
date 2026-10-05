module

public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Paper.lem_finite_trace_response_continuity
public import SubdiffusiveProcess.Paper.lem_finite_trace_smooth_net
public import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity Set TopologicalSpace
open scoped ContDiff Pointwise

namespace SubdiffusiveProcess.Paper

lemma aux_lem_finite_trace_tests_absSet_smul
    {d : ℕ} {S : Set (SpatialCoordinates d)}
    {F : SpatialCoordinates d → ℝ} {a : ℝ} (ha : 0 ≤ a) :
    {v : ℝ | ∃ x ∈ S, v = |(fun x => a * F x) x|} =
      a • {v : ℝ | ∃ x ∈ S, v = |F x|} := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [abs_mul, abs_of_nonneg ha]
    apply Set.mem_smul_set.mpr
    refine ⟨|F x|, ⟨x, hx, rfl⟩, ?_⟩
    simp only [smul_eq_mul]
  · intro hv
    rcases Set.mem_smul_set.mp hv with ⟨w, hw, hwv⟩
    rcases hw with ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [abs_mul, abs_of_nonneg ha]
    convert hwv.symm using 1

lemma aux_lem_finite_trace_tests_holderRatioSet_smul
    {d : ℕ} {beta : ℝ} {S : Set (SpatialCoordinates d)}
    {F : SpatialCoordinates d → ℝ} {a : ℝ} (ha : 0 ≤ a) :
    _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta S (fun x => a * F x) =
      a • _root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta S F := by
  ext v
  constructor
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    apply Set.mem_smul_set.mpr
    refine ⟨|F x - F y| /
          (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta,
      ⟨x, hx, y, hy, hxy, rfl⟩, ?_⟩
    rw [show a * F x - a * F y = a * (F x - F y) by ring]
    rw [abs_mul, abs_of_nonneg ha]
    simp only [smul_eq_mul]
    ring
  · intro hv
    rcases Set.mem_smul_set.mp hv with ⟨w, hw, hwv⟩
    rcases hw with ⟨x, hx, y, hy, hxy, rfl⟩
    refine ⟨x, hx, y, hy, hxy, ?_⟩
    rw [show a * F x - a * F y = a * (F x - F y) by ring]
    rw [abs_mul, abs_of_nonneg ha]
    convert hwv.symm using 1; simp only [smul_eq_mul]; ring

lemma aux_lem_finite_trace_tests_cAlphaNorm_smul
    {d : ℕ} {beta : ℝ} {S : Set (SpatialCoordinates d)}
    {F : SpatialCoordinates d → ℝ} {a : ℝ} (ha : 0 ≤ a) :
    _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S (fun x => a * F x) =
      a * _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S F := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
  rw [aux_lem_finite_trace_tests_absSet_smul ha,
    aux_lem_finite_trace_tests_holderRatioSet_smul ha,
    Real.sSup_smul_of_nonneg ha, Real.sSup_smul_of_nonneg ha]
  simp only [smul_eq_mul]
  ring

lemma aux_lem_finite_trace_tests_quotientSet_smul
    {d : ℕ} {beta : ℝ} {S : Set (SpatialCoordinates d)}
    {F : SpatialCoordinates d → ℝ} {a : ℝ} (ha : 0 < a) :
    {v : ℝ | ∃ c : ℝ, v = _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S
        (fun x => a * F x - c)} =
      a • {v : ℝ | ∃ c : ℝ, v = _root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S
        (fun x => F x - c)} := by
  ext v
  constructor
  · rintro ⟨c, rfl⟩
    apply Set.mem_smul_set.mpr
    refine ⟨_root_.SubdiffusiveProcess.EllipticRegularity.cAlphaNorm beta S (fun x => F x - c / a),
      ⟨c / a, rfl⟩, ?_⟩
    have heq : (fun x => a * F x - c) =
        (fun x => a * (F x - c / a)) := by
      funext x
      field_simp [ne_of_gt ha]
    rw [heq, aux_lem_finite_trace_tests_cAlphaNorm_smul (le_of_lt ha)]
    simp only [smul_eq_mul]
  · intro hv
    rcases Set.mem_smul_set.mp hv with ⟨w, hw, hwv⟩
    rcases hw with ⟨c, rfl⟩
    refine ⟨a * c, ?_⟩
    have heq : (fun x => a * F x - a * c) =
        (fun x => a * (F x - c)) := by
      funext x
      ring
    rw [heq, aux_lem_finite_trace_tests_cAlphaNorm_smul (le_of_lt ha)]
    simpa only [smul_eq_mul] using hwv.symm

lemma aux_lem_finite_trace_tests_quotientCBetaNorm_smul
    {d : ℕ} {beta : ℝ} {S : Set (SpatialCoordinates d)}
    {F : SpatialCoordinates d → ℝ} {a : ℝ} (ha : 0 < a) :
    quotientCBetaNorm beta S (fun x => a * F x) =
      a * quotientCBetaNorm beta S F := by
  unfold quotientCBetaNorm
  rw [aux_lem_finite_trace_tests_quotientSet_smul ha,
    Real.sInf_smul_of_nonneg (le_of_lt ha)]
  simp only [smul_eq_mul]

lemma aux_lem_finite_trace_tests_cellBoundaryQuotientNorm_smul
    {d : ℕ} (beta : ℝ) (z : SpatialCoordinates d) (r a : ℝ)
    (ha : 0 < a) (F : SpatialCoordinates d → ℝ) :
    cellBoundaryQuotientNorm beta z r (fun x => a * F x) =
      a * cellBoundaryQuotientNorm beta z r F := by
  have hres : rescaledDatum z r (fun x => a * F x) =
      (fun y => a * rescaledDatum z r F y) := by
    funext y
    simp only [rescaledDatum]
  unfold cellBoundaryQuotientNorm
  rw [hres, aux_lem_finite_trace_tests_quotientCBetaNorm_smul ha]

lemma aux_lem_finite_trace_tests_IsCellBoundaryClass_smul
    {d : ℕ} (beta : ℝ) (z : SpatialCoordinates d) (r a : ℝ)
    (ha : 0 ≤ a) {F : SpatialCoordinates d → ℝ}
    (hF : IsCellBoundaryClass beta z r F) :
    IsCellBoundaryClass beta z r (fun x => a * F x) := by
  obtain ⟨hFh, hFa⟩ := hF
  have hres : rescaledDatum z r (fun x => a * F x) =
      (fun y => a * rescaledDatum z r F y) := by
    funext y
    simp only [rescaledDatum]
  refine ⟨?_, ?_⟩
  · rw [hres]
    change BddAbove (_root_.SubdiffusiveProcess.EllipticRegularity.holderRatioSet beta _
      (fun y => a * (rescaledDatum z r F) y))
    rw [aux_lem_finite_trace_tests_holderRatioSet_smul ha]
    obtain ⟨M, hM⟩ := hFh
    refine ⟨a * M, ?_⟩
    intro v hv
    rcases Set.mem_smul_set.mp hv with ⟨w, hw, rfl⟩
    exact mul_le_mul_of_nonneg_left (hM hw) ha
  · rw [hres]
    rw [aux_lem_finite_trace_tests_absSet_smul ha]
    obtain ⟨M, hM⟩ := hFa
    refine ⟨a * M, ?_⟩
    intro v hv
    rcases Set.mem_smul_set.mp hv with ⟨w, hw, rfl⟩
    exact mul_le_mul_of_nonneg_left (hM hw) ha

lemma aux_lem_finite_trace_tests_quotient_nonneg
    {d : ℕ} (beta : ℝ) (S : Set (SpatialCoordinates d))
    (F : SpatialCoordinates d → ℝ) :
    0 ≤ quotientCBetaNorm beta S F := by
  unfold quotientCBetaNorm
  apply le_csInf
  · exact ⟨_, ⟨0, rfl⟩⟩
  · intro v hv
    obtain ⟨c, rfl⟩ := hv
    exact aux_lem_finite_trace_holder_beta_bound_cAlphaNorm_nonneg beta S
      (fun x => F x - c)

lemma aux_lem_finite_trace_tests_unit_estimate
    (d : ℕ) (hd : 2 ≤ d)
    (beta alpha : ℝ) (hbeta : 1 / 2 < beta) (hba : beta < alpha) (halpha : alpha < 1)
    (A eta : ℝ) (hA : 0 ≤ A) (heta : 0 < eta) :
    ∃ Hs : Finset (SpatialCoordinates d → ℝ),
      (∀ h ∈ Hs, ContDiff ℝ ∞ h) ∧
      ∀ R1 R2 : Seminorm ℝ (SpatialCoordinates d → ℝ),
        (∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
          (R1 g) ^ 2 ≤ A * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2 ∧
          (R2 g) ^ 2 ≤ A * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2) →
        (∀ h ∈ Hs, |(R1 h) ^ 2 - (R2 h) ^ 2| ≤ eta / 2) →
        ∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass alpha 0 1 g →
          cellBoundaryQuotientNorm alpha 0 1 g ≤ 1 →
          |(R1 g) ^ 2 - (R2 g) ^ 2| ≤ eta := by
  obtain ⟨C, hC, hUnit, hNet⟩ :=
    lem_finite_trace_smooth_net d hd beta alpha hbeta hba halpha
  let epsilon : ℝ := eta / (8 * (A * C + 1))
  have hden : 0 < 8 * (A * C + 1) := by
    have : 0 ≤ A * C := mul_nonneg hA (le_of_lt hC)
    positivity
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  obtain ⟨Hs, hHs, hcover⟩ := hNet epsilon hepsilon
  refine ⟨Hs, ?_, ?_⟩
  · intro h hh
    exact (hHs h hh).1
  · intro R1 R2 hR htest g hgα hgαnorm
    obtain ⟨hβg, hβgNorm⟩ := hUnit g hgα hgαnorm
    obtain ⟨h, hh, hghNorm⟩ := hcover g hgα hgαnorm
    have hβh := (hHs h hh).2.1
    have hβhNorm := (hHs h hh).2.2
    have hcont1 := lem_finite_trace_response_continuity d hd beta hbeta (lt_trans hba halpha) A hA R1
      (fun g hg => (hR g hg).1)
      g h hβg hβh
    have hcont2 := lem_finite_trace_response_continuity d hd beta hbeta (lt_trans hba halpha) A hA R2
      (fun g hg => (hR g hg).2)
      g h hβg hβh
    have hqdiff : cellBoundaryQuotientNorm beta 0 1 (fun x => g x - h x) ≤ epsilon := hghNorm
    have hsum : cellBoundaryQuotientNorm beta 0 1 g +
        cellBoundaryQuotientNorm beta 0 1 h ≤ C + C := by
      exact add_le_add hβgNorm hβhNorm
    have hsum0 : 0 ≤ cellBoundaryQuotientNorm beta 0 1 g +
        cellBoundaryQuotientNorm beta 0 1 h := by
      have hg0 := aux_lem_finite_trace_tests_quotient_nonneg beta
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d))) (rescaledDatum 0 1 g)
      have hh0 := aux_lem_finite_trace_tests_quotient_nonneg beta
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
          Set (SpatialCoordinates d))) (rescaledDatum 0 1 h)
      simpa only [cellBoundaryQuotientNorm] using add_nonneg hg0 hh0
    have hmul : A * cellBoundaryQuotientNorm beta 0 1 (fun x => g x - h x) *
        (cellBoundaryQuotientNorm beta 0 1 g + cellBoundaryQuotientNorm beta 0 1 h) ≤
        2 * A * C * epsilon := by
      have hAeps : A * cellBoundaryQuotientNorm beta 0 1 (fun x => g x - h x) ≤ A * epsilon :=
        mul_le_mul_of_nonneg_left hqdiff hA
      have hAeps0 : 0 ≤ A * epsilon := mul_nonneg hA (le_of_lt hepsilon)
      have hleft : A * cellBoundaryQuotientNorm beta 0 1 (fun x => g x - h x) *
          (cellBoundaryQuotientNorm beta 0 1 g + cellBoundaryQuotientNorm beta 0 1 h) ≤
          (A * epsilon) * (C + C) :=
        mul_le_mul hAeps hsum hsum0 hAeps0
      calc
        _ ≤ (A * epsilon) * (C + C) := hleft
        _ = 2 * A * C * epsilon := by ring
    have hbound1 : |(R1 g) ^ 2 - (R1 h) ^ 2| ≤ 2 * A * C * epsilon := by
      exact hcont1.trans hmul
    have hbound2 : |(R2 g) ^ 2 - (R2 h) ^ 2| ≤ 2 * A * C * epsilon := by
      exact hcont2.trans hmul
    have hgap : |(R1 g) ^ 2 - (R2 g) ^ 2| ≤ eta := by
      calc
        |(R1 g) ^ 2 - (R2 g) ^ 2| ≤
            |(R1 g) ^ 2 - (R1 h) ^ 2| +
              |(R1 h) ^ 2 - (R2 h) ^ 2| +
              |(R2 h) ^ 2 - (R2 g) ^ 2| := by
          rw [show (R1 g) ^ 2 - (R2 g) ^ 2 =
              ((R1 g) ^ 2 - (R1 h) ^ 2) +
                ((R1 h) ^ 2 - (R2 h) ^ 2) +
                ((R2 h) ^ 2 - (R2 g) ^ 2) by ring]
          calc
            |((R1 g) ^ 2 - (R1 h) ^ 2) +
                ((R1 h) ^ 2 - (R2 h) ^ 2) +
                ((R2 h) ^ 2 - (R2 g) ^ 2)| ≤
                |((R1 g) ^ 2 - (R1 h) ^ 2) +
                  ((R1 h) ^ 2 - (R2 h) ^ 2)| +
                  |(R2 h) ^ 2 - (R2 g) ^ 2| := abs_add_le _ _
            _ ≤ |(R1 g) ^ 2 - (R1 h) ^ 2| +
                |(R1 h) ^ 2 - (R2 h) ^ 2| +
                |(R2 h) ^ 2 - (R2 g) ^ 2| := by
              exact add_le_add (abs_add_le _ _) (le_refl _)
        _ ≤ 2 * A * C * epsilon + eta / 2 + 2 * A * C * epsilon := by
          exact add_le_add (add_le_add hbound1 (htest h hh))
            (by simpa only [abs_sub_comm] using hbound2)
        _ ≤ eta := by
          dsimp [epsilon]
          have hAC : 0 ≤ A * C := mul_nonneg hA (le_of_lt hC)
          field_simp [ne_of_gt hden]
          nlinarith
    exact hgap

/--
- Source: finite boundary tests, including the square-root response triangle inequality in its proof.
- The exact exponent order is 1/2 < beta < alpha < 1. The extension bound is in C^beta modulo constants, and the conclusion is in C^alpha modulo constants.
- The finite smooth family is selected after A and eta but before both response seminorms. Its size and smooth norms may depend on eta.
- The source responses are squares of seminorms; the Seminorm carrier retains triangle inequality, homogeneity and vanishing at zero, rather than arbitrary homogeneous functionals.
- Carriers and quotient norms are pinned to the actual unit-cube frontier by IsCellBoundaryClass and cellBoundaryQuotientNorm. The source norm's supremum is never used outside its Holder class.
- Every admissible alpha trace is included, also traces constant on the boundary. The final homogeneous rescaling remains a proof obligation here, including the zero quotient-norm case.
- Supplier lem_finite_trace_response_continuity concludes the response estimate  from the original extension bound; it is a fine child, not a new hypothesis.
- Supplier lem_finite_trace_smooth_net concludes the compact-embedding finite-net construction, including a uniform weaker-norm bound for the unit ball and its smooth net centers. No compactness or approximation premise is added.
- Both children are proof-step obligations. The downstream finite_trace_test_order depends on this lemma and cannot supply its construction.

-/
theorem lem_finite_trace_tests
    (d : ℕ) (hd : 2 ≤ d)
    (beta alpha : ℝ) (hbeta : 1 / 2 < beta) (hba : beta < alpha) (halpha : alpha < 1)
    (A eta : ℝ) (hA : 0 ≤ A) (heta : 0 < eta) :
    ∃ Hs : Finset (SpatialCoordinates d → ℝ),
      (∀ h ∈ Hs, ContDiff ℝ ∞ h) ∧
      ∀ R1 R2 : Seminorm ℝ (SpatialCoordinates d → ℝ),
        (∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass beta 0 1 g →
          (R1 g) ^ 2 ≤ A * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2 ∧
          (R2 g) ^ 2 ≤ A * (cellBoundaryQuotientNorm beta 0 1 g) ^ 2) →
        (∀ h ∈ Hs, |(R1 h) ^ 2 - (R2 h) ^ 2| ≤ eta / 2) →
        ∀ g : SpatialCoordinates d → ℝ, IsCellBoundaryClass alpha 0 1 g →
          |(R1 g) ^ 2 - (R2 g) ^ 2| ≤
            eta * (cellBoundaryQuotientNorm alpha 0 1 g) ^ 2 := by
  obtain ⟨Hs, hHs, hUnit⟩ :=
    aux_lem_finite_trace_tests_unit_estimate d hd beta alpha hbeta hba halpha
      A eta hA heta
  refine ⟨Hs, hHs, ?_⟩
  intro R1 R2 hR htest g hg
  let N : ℝ := cellBoundaryQuotientNorm alpha 0 1 g
  have hN0 : 0 ≤ N := by
    dsimp [N]
    exact aux_lem_finite_trace_tests_quotient_nonneg alpha
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))) (rescaledDatum 0 1 g)
  let D : ℝ := |(R1 g) ^ 2 - (R2 g) ^ 2|
  have hscaled : ∀ t : ℝ, 0 < t → t * N ≤ 1 → t ^ 2 * D ≤ eta := by
    intro t ht htN
    have hclass : IsCellBoundaryClass alpha 0 1 (fun x => t * g x) :=
      aux_lem_finite_trace_tests_IsCellBoundaryClass_smul alpha 0 1 t
        (le_of_lt ht) hg
    have hnorm : cellBoundaryQuotientNorm alpha 0 1
        (fun x => t * g x) ≤ 1 := by
      rw [aux_lem_finite_trace_tests_cellBoundaryQuotientNorm_smul
        alpha 0 1 t ht]
      change t * N ≤ 1
      exact htN
    have hunit := hUnit R1 R2 hR htest (fun x => t * g x) hclass hnorm
    have hR1 : R1 (fun x => t * g x) = t * R1 g := by
      have hfun : (fun x => t * g x) = t • g := by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul]
      rw [hfun, map_smul_eq_mul]
      simp only [Real.norm_eq_abs, abs_of_pos ht]
    have hR2 : R2 (fun x => t * g x) = t * R2 g := by
      have hfun : (fun x => t * g x) = t • g := by
        funext x
        simp only [Pi.smul_apply, smul_eq_mul]
      rw [hfun, map_smul_eq_mul]
      simp only [Real.norm_eq_abs, abs_of_pos ht]
    have hfactor :
        |(R1 (fun x => t * g x)) ^ 2 - (R2 (fun x => t * g x)) ^ 2| =
          t ^ 2 * D := by
      rw [hR1, hR2]
      dsimp [D]
      rw [show (t * R1 g) ^ 2 - (t * R2 g) ^ 2 =
          t ^ 2 * ((R1 g) ^ 2 - (R2 g) ^ 2) by ring]
      rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
    rw [hfactor] at hunit
    exact hunit
  by_cases hN : 0 < N
  · have ht : 0 < (1 / N : ℝ) := by positivity
    have htN : (1 / N : ℝ) * N ≤ 1 := by
      field_simp [ne_of_gt hN]
      norm_num
    have hsmall := hscaled (1 / N) ht htN
    have hN2 : 0 < N ^ 2 := sq_pos_of_pos hN
    have hprod : ((1 / N : ℝ) ^ 2 * D) * N ^ 2 ≤ eta * N ^ 2 :=
      mul_le_mul_of_nonneg_right hsmall (sq_nonneg N)
    have hinv : (1 / N : ℝ) ^ 2 * N ^ 2 = 1 := by
      field_simp [ne_of_gt hN]
    have hDle : D ≤ eta * N ^ 2 := by
      calc
        D = D * ((1 / N : ℝ) ^ 2 * N ^ 2) := by rw [hinv, mul_one]
        _ = ((1 / N : ℝ) ^ 2 * D) * N ^ 2 := by ring
        _ ≤ eta * N ^ 2 := hprod
    simpa only [D, N] using hDle
  · have hNzero : N = 0 := le_antisymm (not_lt.mp hN) hN0
    have hDzero : D = 0 := by
      by_contra hDne
      have hDpos : 0 < D := by
        dsimp [D]
        exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm hDne)
      let t : ℝ := eta / D + 1
      have ht : 0 < t := by
        dsimp [t]
        positivity
      have htN : t * N ≤ 1 := by rw [hNzero, mul_zero]; norm_num
      have hlarge : eta < t ^ 2 * D := by
        have ht1 : 1 ≤ t := by
          dsimp [t]
          have : 0 ≤ eta / D := le_of_lt (div_pos heta hDpos)
          linarith
        have htd : eta < t * D := by
          dsimp [t]
          have hDne' : D ≠ 0 := ne_of_gt hDpos
          field_simp [hDne']
          nlinarith
        have htsq : t ≤ t ^ 2 := by nlinarith
        exact lt_of_lt_of_le htd
          (mul_le_mul_of_nonneg_right htsq (le_of_lt hDpos))
      exact (not_lt_of_ge (hscaled t ht htN)) hlarge
    change D ≤ eta * N ^ 2
    rw [hNzero, hDzero]
    norm_num

end SubdiffusiveProcess.Paper

