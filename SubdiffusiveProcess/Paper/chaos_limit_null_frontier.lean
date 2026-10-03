module

public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Main.WeightedChaosCutoff
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Lane1.ChaosBasic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.ContinuousMap.CompactlySupported

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open SubdiffusiveProcess
open scoped CompactlySupported ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- Part of G-2 of Proposition `mfd:prop-chaos-growth` (paper 4803-4816): a
measure obeying `eq:mfd-39` gives no mass to the boundary of a cube.

This is the paper's "For $\partial Q$, cover it by $Cr^{1-d}$ balls of radius
$r$ to get $\mu(\partial Q)\le CK_\mu r^{1-\epsilon}\to0$".  It is separated
from the other two regularity assertions because it is the only one of the
three assertions that needs a COVERING of a $(d-1)$-dimensional set, and hence
a counting estimate, rather than the bound at a single ball; it is also the
assertion the portmanteau step of the path-space arguments consumes. -/
theorem chaos_limit_null_frontier
    {d : ℕ} (hd : 2 ≤ d) (epsilon : ℝ) (hepsilon : epsilon ∈ Set.Ioo 0 1)
    (mu : Measure (SpatialCoordinates d))
    (hgrowth : ∀ Rset : Set (SpatialCoordinates d), Bornology.IsBounded Rset →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Rset, ∀ r : ℝ, 0 < r → r ≤ 1 →
        mu (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ ((d : ℝ) - epsilon))) :
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      mu (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) = 0 := by
  classical
  obtain ⟨hep0, hep1⟩ := hepsilon
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdeps : 0 < (d : ℝ) - epsilon := by linarith
  intro z r hr
  set rho : ℝ := r / 2 with hrhodef
  have hrho : 0 < rho := by rw [hrhodef]; linarith
  obtain ⟨K, hK, hb⟩ := hgrowth (Metric.ball z (rho + 4)) Metric.isBounded_ball
  -- the frontier of a cube is the sup-norm sphere
  have hfront : frontier (centeredCube z r hr : Set (SpatialCoordinates d))
      = Metric.sphere z rho := by
    rw [centeredCube_coe_eq_ball, ← hrhodef]
    exact frontier_ball z (ne_of_gt hrho)
  -- a slab piece of the sphere
  have hslab : ∀ (i : Fin d) (c : ℝ), |c - z i| = rho →
      mu ({y : SpatialCoordinates d | y i = c} ∩
        Metric.closedBall z rho) = 0 := by
    intro i c hc
    -- for each scale t the piece is covered by a (d-1)-dimensional grid of balls
    have hcov : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
        mu ({y : SpatialCoordinates d | y i = c} ∩ Metric.closedBall z rho)
          ≤ ENNReal.ofReal ((2 * (⌈rho / t⌉₊ + 1) + 1 : ℕ) ^ (d - 1) *
              (K * (2 * t) ^ ((d : ℝ) - epsilon))) := by
      intro t ht ht1
      set m : ℕ := ⌈rho / t⌉₊ + 1 with hm
      set B : Finset ℤ := Finset.Icc (-(m : ℤ)) (m : ℤ) with hB
      set Idx : Finset (Fin d → ℤ) :=
        Fintype.piFinset (fun l => if l = i then ({0} : Finset ℤ) else B) with hIdx
      set w : (Fin d → ℤ) → SpatialCoordinates d :=
        fun k l => if l = i then c else z l + (k l : ℝ) * t with hw
      have hmem : ∀ y ∈ ({y : SpatialCoordinates d | y i = c} ∩
          Metric.closedBall z rho),
          ∃ k ∈ Idx, y ∈ Metric.ball (w k) (2 * t) := by
        intro y hy
        obtain ⟨hyi, hyball⟩ := hy
        have hyi' : y i = c := hyi
        have hdist : ∀ l, |y l - z l| ≤ rho := by
          intro l
          have := (dist_pi_le_iff hrho.le).mp (Metric.mem_closedBall.mp hyball) l
          rwa [Real.dist_eq] at this
        refine ⟨fun l => if l = i then 0 else ⌊(y l - z l) / t⌋, ?_, ?_⟩
        · rw [hIdx, Fintype.mem_piFinset]
          intro l
          by_cases hl : l = i
          · simp [hl]
          · simp only [hl, if_false, hB, Finset.mem_Icc]
            have hfl : |((⌊(y l - z l) / t⌋ : ℤ) : ℝ)| ≤ rho / t + 1 := by
              have h1 : ((⌊(y l - z l) / t⌋ : ℤ) : ℝ) ≤ (y l - z l) / t :=
                Int.floor_le _
              have h2 : (y l - z l) / t - 1 < ((⌊(y l - z l) / t⌋ : ℤ) : ℝ) :=
                Int.sub_one_lt_floor _
              have h3 : |(y l - z l) / t| ≤ rho / t := by
                rw [abs_div, abs_of_pos ht]
                gcongr
                exact hdist l
              rw [abs_le] at h3 ⊢
              constructor <;> [linarith [h3.1, h3.2]; linarith [h3.1, h3.2]]
            have hmle : rho / t + 1 ≤ (m : ℝ) := by
              rw [hm]
              push_cast
              have := Nat.le_ceil (rho / t)
              linarith
            rw [abs_le] at hfl
            constructor
            · have : -((m : ℝ)) ≤ ((⌊(y l - z l) / t⌋ : ℤ) : ℝ) := by linarith [hfl.1]
              exact_mod_cast this
            · have : ((⌊(y l - z l) / t⌋ : ℤ) : ℝ) ≤ (m : ℝ) := by linarith [hfl.2]
              exact_mod_cast this
        · refine Metric.mem_ball.mpr ?_
          refine lt_of_le_of_lt ((dist_pi_le_iff ht.le).mpr ?_) (by linarith)
          intro l
          rw [Real.dist_eq, hw]
          by_cases hl : l = i
          · subst hl
            simp [hyi', ht.le]
          · simp only [hl, if_false]
            have hF1 : ((⌊(y l - z l) / t⌋ : ℤ) : ℝ) * t ≤ y l - z l :=
              (le_div_iff₀ ht).mp (Int.floor_le _)
            have hF2 : (y l - z l) / t < ((⌊(y l - z l) / t⌋ : ℤ) : ℝ) + 1 :=
              Int.lt_floor_add_one _
            have hF3 : y l - z l < (((⌊(y l - z l) / t⌋ : ℤ) : ℝ) + 1) * t :=
              (div_lt_iff₀ ht).mp hF2
            rw [abs_le]
            constructor <;> nlinarith [hF1, hF3]
      have hsub : ({y : SpatialCoordinates d | y i = c} ∩ Metric.closedBall z rho)
          ⊆ ⋃ k ∈ Idx, Metric.ball (w k) (2 * t) := by
        intro y hy
        obtain ⟨k, hk, hyk⟩ := hmem y hy
        exact Set.mem_biUnion hk hyk
      have hballbd : ∀ k ∈ Idx,
          mu (Metric.ball (w k) (2 * t))
            ≤ ENNReal.ofReal (K * (2 * t) ^ ((d : ℝ) - epsilon)) := by
        intro k hk
        refine hb (w k) ?_ (2 * t) (by linarith) ?_
        · refine Metric.mem_ball.mpr ?_
          refine lt_of_le_of_lt ((dist_pi_le_iff (by linarith : (0:ℝ) ≤ rho + 2)).mpr ?_)
            (by linarith)
          intro l
          rw [Real.dist_eq, hw]
          by_cases hl : l = i
          · subst hl
            simp only [if_true]
            rw [hc]
            linarith
          · simp only [hl, if_false]
            rw [hIdx, Fintype.mem_piFinset] at hk
            have hkl := hk l
            simp only [hl, if_false, hB, Finset.mem_Icc] at hkl
            have h1 : |((k l : ℤ) : ℝ)| ≤ (m : ℝ) := by
              rw [abs_le]
              constructor
              · exact_mod_cast hkl.1
              · exact_mod_cast hkl.2
            have hmt : (m : ℝ) * t ≤ rho + 2 := by
              have hce : (⌈rho / t⌉₊ : ℝ) < rho / t + 1 :=
                Nat.ceil_lt_add_one (by positivity)
              have hdt : (rho / t) * t = rho := div_mul_cancel₀ rho (ne_of_gt ht)
              have hmR : (m : ℝ) = (⌈rho / t⌉₊ : ℝ) + 1 := by
                rw [hm]; push_cast; ring
              rw [hmR]
              nlinarith [hce, ht, ht1, hdt]
            have : |z l + ((k l : ℤ) : ℝ) * t - z l| = |((k l : ℤ) : ℝ)| * t := by
              rw [show z l + ((k l : ℤ) : ℝ) * t - z l = ((k l : ℤ) : ℝ) * t by ring,
                abs_mul, abs_of_pos ht]
            rw [this]
            nlinarith [h1, ht.le]
        · linarith
      calc mu ({y : SpatialCoordinates d | y i = c} ∩ Metric.closedBall z rho)
          ≤ mu (⋃ k ∈ Idx, Metric.ball (w k) (2 * t)) := measure_mono hsub
        _ ≤ ∑ k ∈ Idx, mu (Metric.ball (w k) (2 * t)) :=
            measure_biUnion_finset_le Idx _
        _ ≤ ∑ _k ∈ Idx, ENNReal.ofReal (K * (2 * t) ^ ((d : ℝ) - epsilon)) :=
            Finset.sum_le_sum hballbd
        _ = (Idx.card : ℝ≥0∞) *
              ENNReal.ofReal (K * (2 * t) ^ ((d : ℝ) - epsilon)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ENNReal.ofReal ((2 * (⌈rho / t⌉₊ + 1) + 1 : ℕ) ^ (d - 1) *
              (K * (2 * t) ^ ((d : ℝ) - epsilon))) := by
            have hcard : Idx.card ≤ (2 * (⌈rho / t⌉₊ + 1) + 1 : ℕ) ^ (d - 1) := by
              rw [hIdx, Fintype.card_piFinset]
              have hstep : ∀ l : Fin d,
                  (if l = i then ({0} : Finset ℤ) else B).card
                    ≤ (if l = i then 1 else (2 * m + 1 : ℕ)) := by
                intro l
                by_cases hl : l = i
                · simp [hl]
                · simp only [hl, if_false, hB]
                  rw [Int.card_Icc]
                  omega
              refine le_trans (Finset.prod_le_prod' (fun l _ => hstep l)) ?_
              rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
              simp only [if_pos rfl, one_mul]
              have hconst : ∀ l ∈ Finset.univ.erase i,
                  (if l = i then 1 else (2 * m + 1 : ℕ)) = (2 * m + 1 : ℕ) := by
                intro l hl
                have : l ≠ i := Finset.ne_of_mem_erase hl
                simp [this]
              rw [Finset.prod_congr rfl hconst, Finset.prod_const,
                Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
                Fintype.card_fin]
              rw [hm]
              simp
            have hnn : (0 : ℝ) ≤ K * (2 * t) ^ ((d : ℝ) - epsilon) :=
              mul_nonneg hK (Real.rpow_nonneg (by linarith) _)
            have hAnn : (0 : ℝ) ≤ ((2 * (⌈rho / t⌉₊ + 1) + 1 : ℕ) : ℝ) ^ (d - 1) := by
              positivity
            rw [ENNReal.ofReal_mul hAnn]
            refine mul_le_mul_left (b := (Idx.card : ℝ≥0∞)) (c := ENNReal.ofReal (((2 * (⌈rho / t⌉₊ + 1) + 1 : ℕ) : ℝ) ^ (d - 1))) ?_ _
            have hcast : (Idx.card : ℝ)
                ≤ ((2 * (⌈rho / t⌉₊ + 1) + 1 : ℕ) : ℝ) ^ (d - 1) := by
              exact_mod_cast hcard
            calc (Idx.card : ℝ≥0∞) = ENNReal.ofReal (Idx.card : ℝ) := by simp
              _ ≤ ENNReal.ofReal (((2 * (⌈rho / t⌉₊ + 1) + 1 : ℕ) : ℝ) ^ (d - 1)) :=
                  ENNReal.ofReal_le_ofReal hcast
    -- the covering bound is `C t ^ (1 - epsilon)`, which tends to zero
    have hCb : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
        ((2 * (⌈rho / t⌉₊ + 1) + 1 : ℕ) : ℝ) ^ (d - 1) *
            (K * (2 * t) ^ ((d : ℝ) - epsilon))
          ≤ ((2 * rho + 5) ^ (d - 1) * (K * (2 : ℝ) ^ ((d : ℝ) - epsilon))) *
            t ^ ((1 : ℝ) - epsilon) := by
      intro t ht ht1
      have hce : (⌈rho / t⌉₊ : ℝ) < rho / t + 1 := Nat.ceil_lt_add_one (by positivity)
      have hnum : ((2 * (⌈rho / t⌉₊ + 1) + 1 : ℕ) : ℝ) ≤ (2 * rho + 5) / t := by
        have h5 : (5 : ℝ) ≤ 5 / t := by
          rw [le_div_iff₀ ht]; nlinarith
        have hdt : (2 * rho) / t = 2 * (rho / t) := by ring
        push_cast
        rw [add_div, hdt]
        nlinarith [hce, h5]
      have hnn0 : (0 : ℝ) ≤ ((2 * (⌈rho / t⌉₊ + 1) + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hpow : ((2 * (⌈rho / t⌉₊ + 1) + 1 : ℕ) : ℝ) ^ (d - 1)
          ≤ ((2 * rho + 5) / t) ^ (d - 1) := by
        exact pow_le_pow_left₀ hnn0 hnum _
      have hsplit : (2 * t) ^ ((d : ℝ) - epsilon)
          = (2 : ℝ) ^ ((d : ℝ) - epsilon) * t ^ ((d : ℝ) - epsilon) :=
        Real.mul_rpow (by norm_num) ht.le
      have hdcast : (((d - 1 : ℕ)) : ℝ) = (d : ℝ) - 1 := by
        have : (1 : ℕ) ≤ d := by omega
        rw [Nat.cast_sub this]; push_cast; ring
      have hinv : ((2 * rho + 5) / t) ^ (d - 1)
          = (2 * rho + 5) ^ (d - 1) * t ^ (-((d : ℝ) - 1)) := by
        rw [div_pow, ← Real.rpow_natCast t (d - 1), hdcast, Real.rpow_neg ht.le,
          div_eq_mul_inv]
      have hmerge : t ^ (-((d : ℝ) - 1)) * t ^ ((d : ℝ) - epsilon)
          = t ^ ((1 : ℝ) - epsilon) := by
        rw [← Real.rpow_add ht]
        congr 1
        ring
      calc ((2 * (⌈rho / t⌉₊ + 1) + 1 : ℕ) : ℝ) ^ (d - 1) *
            (K * (2 * t) ^ ((d : ℝ) - epsilon))
          ≤ ((2 * rho + 5) / t) ^ (d - 1) * (K * (2 * t) ^ ((d : ℝ) - epsilon)) := by
            refine mul_le_mul_of_nonneg_right hpow ?_
            exact mul_nonneg hK (Real.rpow_nonneg (by linarith) _)
        _ = ((2 * rho + 5) ^ (d - 1) * (K * (2 : ℝ) ^ ((d : ℝ) - epsilon))) *
              (t ^ (-((d : ℝ) - 1)) * t ^ ((d : ℝ) - epsilon)) := by
            rw [hinv, hsplit]; ring
        _ = _ := by rw [hmerge]
    -- let the scale go to zero
    set Cbig : ℝ := (2 * rho + 5) ^ (d - 1) * (K * (2 : ℝ) ^ ((d : ℝ) - epsilon))
      with hCbig
    have hCbignn : 0 ≤ Cbig := by
      rw [hCbig]
      have h1 : (0 : ℝ) ≤ 2 * rho + 5 := by linarith
      have h2 : (0 : ℝ) < (2 : ℝ) ^ ((d : ℝ) - epsilon) :=
        Real.rpow_pos_of_pos (by norm_num) _
      positivity
    have hle : ∀ t : ℝ, 0 < t → t ≤ 1 / 2 →
        mu ({y : SpatialCoordinates d | y i = c} ∩ Metric.closedBall z rho)
          ≤ ENNReal.ofReal (Cbig * t ^ ((1 : ℝ) - epsilon)) := by
      intro t ht ht1
      exact le_trans (hcov t ht ht1) (ENNReal.ofReal_le_ofReal (hCb t ht ht1))
    have hcont : ContinuousAt (fun t : ℝ => t ^ ((1 : ℝ) - epsilon)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr (by linarith))
    have h1 : Filter.Tendsto (fun t : ℝ => Cbig * t ^ ((1 : ℝ) - epsilon))
        (nhds 0) (nhds 0) := by
      have h0 := hcont.tendsto
      rw [Real.zero_rpow (by linarith : (1 : ℝ) - epsilon ≠ 0)] at h0
      have := h0.const_mul Cbig
      rwa [mul_zero] at this
    have h1' : Filter.Tendsto (fun t : ℝ => Cbig * t ^ ((1 : ℝ) - epsilon))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
      h1.mono_left nhdsWithin_le_nhds
    have htend : Filter.Tendsto
        (fun t : ℝ => ENNReal.ofReal (Cbig * t ^ ((1 : ℝ) - epsilon)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal h1'
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        mu ({y : SpatialCoordinates d | y i = c} ∩ Metric.closedBall z rho)
          ≤ ENNReal.ofReal (Cbig * t ^ ((1 : ℝ) - epsilon)) := by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with t htmem
      exact hle t htmem.1 htmem.2.le
    exact le_antisymm (ge_of_tendsto htend hev) (zero_le)
  -- the sphere is the union of the slab pieces
  rw [hfront]
  have hcover : Metric.sphere z rho ⊆
      ⋃ i : Fin d, (({y : SpatialCoordinates d | y i = z i + rho} ∩
          Metric.closedBall z rho) ∪
        ({y : SpatialCoordinates d | y i = z i - rho} ∩ Metric.closedBall z rho)) := by
    intro y hy
    have hdy : dist y z = rho := Metric.mem_sphere.mp hy
    have hball : y ∈ Metric.closedBall z rho :=
      Metric.mem_closedBall.mpr (le_of_eq hdy)
    have hattained : ∃ i : Fin d, |y i - z i| = rho := by
      by_contra hcon
      push_neg at hcon
      have hlt : ∀ i : Fin d, dist (y i) (z i) < rho := by
        intro i
        have hle : dist (y i) (z i) ≤ rho := by
          have := (dist_pi_le_iff hrho.le).mp (le_of_eq hdy) i
          exact this
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exact absurd (by rw [Real.dist_eq] at h; exact h) (hcon i)
      have := (dist_pi_lt_iff hrho).mpr hlt
      linarith
    obtain ⟨i, hi⟩ := hattained
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rcases (abs_eq hrho.le).mp hi with h | h
    · exact Or.inl ⟨by simp [Set.mem_setOf_eq]; linarith, hball⟩
    · exact Or.inr ⟨by simp [Set.mem_setOf_eq]; linarith, hball⟩
  refine measure_mono_null hcover ?_
  refine measure_iUnion_null ?_
  intro i
  refine measure_union_null ?_ ?_
  · refine hslab i (z i + rho) ?_
    rw [show z i + rho - z i = rho by ring, abs_of_pos hrho]
  · refine hslab i (z i - rho) ?_
    rw [show z i - rho - z i = -rho by ring, abs_neg, abs_of_pos hrho]

end Paper
