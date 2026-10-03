module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionLocalFiniteness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionLaminarRepair

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab.LambdaStabilitySupport
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
open scoped ENNReal

noncomputable section

variable {d : ℕ} {Omega : Type*} {base : ℤ}

/-! ## 1. Counting triadic cubes of a fixed scale near a point -/

/-- A cube of scale `s` meeting `closedBall x rho` has every index coordinate
bounded by `(rho + ‖x‖)/3 ^ s + 1`. -/
theorem abs_index_le_of_meeting_closedBall {Q : TriadicCube d}
    {x : Vec d} {rho : ℝ}
    (h : (cubeSet Q ∩ Metric.closedBall x rho).Nonempty) (i : Fin d) :
    |(Q.index i : ℝ)| ≤ (rho + ‖x‖) / (3 : ℝ) ^ Q.scale + 1 := by
  obtain ⟨z, hzQ, hzB⟩ := h
  rw [Metric.mem_closedBall] at hzB
  have h3 : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
  have hzx : |z i - x i| ≤ rho := by
    have hd := dist_le_pi_dist z x i
    rw [Real.dist_eq] at hd
    linarith
  have hxi : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hz : |z i| ≤ rho + ‖x‖ := by
    have h1 := abs_le.mp hzx
    have h2 := abs_le.mp hxi
    exact abs_le.mpr ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
  have hmem := hzQ i
  rw [cubeScaleFactor] at hmem
  have hzl := abs_le.mp hz
  have hbound : |(Q.index i : ℝ)| * (3 : ℝ) ^ Q.scale ≤
      (rho + ‖x‖) + (3 : ℝ) ^ Q.scale := by
    rcases abs_cases ((Q.index i : ℝ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
      nlinarith [hmem.1, hmem.2, hzl.1, hzl.2, h3]
  have hfrac : (rho + ‖x‖) / (3 : ℝ) ^ Q.scale + 1
      = ((rho + ‖x‖) + (3 : ℝ) ^ Q.scale) / (3 : ℝ) ^ Q.scale := by
    field_simp
  rw [hfrac, le_div_iff₀ h3]
  exact hbound

/-- **The dimension-only count of triadic cubes of a fixed scale near a
point.**  This is the cardinality refinement of
`finite_triadicCube_scale_eq_meeting_isBounded` that makes the Borel--Cantelli
step of the local-finiteness producer go through. -/
theorem card_triadicCube_scale_eq_meeting_closedBall (s : ℤ)
    (x : Vec d) (rho : ℝ)
    (hfin : {Q : TriadicCube d | Q.scale = s ∧
        (cubeSet Q ∩ Metric.closedBall x rho).Nonempty}.Finite) :
    hfin.toFinset.card ≤ (2 * ⌈(rho + ‖x‖) / (3 : ℝ) ^ s⌉₊ + 3) ^ d := by
  classical
  set N : ℤ := (⌈(rho + ‖x‖) / (3 : ℝ) ^ s⌉₊ : ℤ) + 1 with hN
  have hcard : (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-N) N)).card
      = (2 * ⌈(rho + ‖x‖) / (3 : ℝ) ^ s⌉₊ + 3) ^ d := by
    rw [Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    have h0 : (0 : ℤ) ≤ (⌈(rho + ‖x‖) / (3 : ℝ) ^ s⌉₊ : ℤ) := Nat.cast_nonneg _
    have h5 : (N + 1 - -N).toNat = 2 * ⌈(rho + ‖x‖) / (3 : ℝ) ^ s⌉₊ + 3 := by omega
    rw [h5]
  refine le_trans (Finset.card_le_card_of_injOn (fun Q => Q.index) ?_ ?_) (le_of_eq hcard)
  · intro Q hQ
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hQ
    obtain ⟨hscale, hne⟩ := hQ
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h1 := abs_index_le_of_meeting_closedBall hne i
    rw [hscale] at h1
    have h2 : (rho + ‖x‖) / (3 : ℝ) ^ s ≤ (⌈(rho + ‖x‖) / (3 : ℝ) ^ s⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h3 : |(Q.index i : ℝ)| ≤ (N : ℝ) := by
      rw [hN]
      push_cast
      linarith
    constructor
    · exact_mod_cast (abs_le.mp h3).1
    · exact_mod_cast (abs_le.mp h3).2
  · intro Q hQ R hR hQR
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hQ hR
    obtain ⟨hs1, -⟩ := hQ
    obtain ⟨hs2, -⟩ := hR
    cases Q; cases R
    simp_all

/-! ## 2. The failing ancestor at the top of the chain -/

/-- A positive stopping depth is witnessed by a failure exactly one level
below it. -/
theorem mem_failure_ancestor_pred_triadicStoppingDepth
    (failure : TriadicCube d → Set Omega) {omega : Omega}
    {Q : StoppingBaseCube d base}
    (hfinite : triadicFailureHeight failure omega Q ≠ (⊤ : WithTop ℕ))
    (hpos : 0 < triadicStoppingDepth failure omega Q) :
    omega ∈ failure (ancestorCube (triadicStoppingDepth failure omega Q - 1) Q.1) := by
  set D := triadicStoppingDepth failure omega Q with hD
  have hEq : triadicFailureHeight failure omega Q = (D : WithTop ℕ) := by
    rcases h : triadicFailureHeight failure omega Q with (_ | n)
    · exact absurd h hfinite
    · rw [hD, triadicStoppingDepth, h]
      rfl
  have hlt : ((D - 1 : ℕ) : WithTop ℕ) < triadicFailureHeight failure omega Q := by
    rw [hEq]
    have h' : D - 1 < D := by omega
    exact_mod_cast h'
  unfold triadicFailureHeight at hlt
  have hmem := failureHeightTail_subset_iUnion (fun j ↦ failure (ancestorCube j Q.1)) (D - 1) hlt
  obtain ⟨j, hfail⟩ := Set.mem_iUnion.mp hmem
  have hltD := lt_triadicStoppingDepth_of_mem_failure failure hfinite hfail
  have hEqh : (j : ℕ) = D - 1 := by
    have hj := j.2
    omega
  rwa [hEqh] at hfail

/-! ## 3. The local failure events -/

/-- The finite family of triadic cubes of scale `s` meeting `closedBall x rho`. -/
def triadicScaleBallFinset (d : ℕ) (s : ℤ) (x : Vec d) (rho : ℝ) :
    Finset (TriadicCube d) :=
  (finite_triadicCube_scale_eq_meeting_isBounded (d := d) s
    (S := Metric.closedBall x rho) Metric.isBounded_closedBall).toFinset

@[simp]
theorem mem_triadicScaleBallFinset {s : ℤ} {x : Vec d} {rho : ℝ}
    {Q : TriadicCube d} :
    Q ∈ triadicScaleBallFinset d s x rho ↔
      Q.scale = s ∧ (cubeSet Q ∩ Metric.closedBall x rho).Nonempty :=
  Set.Finite.mem_toFinset _

theorem card_triadicScaleBallFinset_le (s : ℤ) (x : Vec d) (rho : ℝ) :
    (triadicScaleBallFinset d s x rho).card ≤
      (2 * ⌈(rho + ‖x‖) / (3 : ℝ) ^ s⌉₊ + 3) ^ d :=
  card_triadicCube_scale_eq_meeting_closedBall s x rho _



def stoppingLocalFailureEvent (failure : TriadicCube d → Set Omega) (base : ℤ)
    (x : Vec d) (n : ℕ) : Set Omega :=
  ⋃ P ∈ triadicScaleBallFinset d (base + (n : ℤ)) x
      (1 + 64 * (3 : ℝ) ^ (base + (n : ℤ))), failure P

theorem mem_stoppingLocalFailureEvent_of_mem_failure
    {failure : TriadicCube d → Set Omega} {omega : Omega} {x : Vec d} {n : ℕ}
    {P : TriadicCube d} (hscale : P.scale = base + (n : ℤ))
    (hmeet : (cubeSet P ∩
      Metric.closedBall x (1 + 64 * (3 : ℝ) ^ (base + (n : ℤ)))).Nonempty)
    (hfail : omega ∈ failure P) :
    omega ∈ stoppingLocalFailureEvent failure base x n :=
  Set.mem_biUnion (mem_triadicScaleBallFinset.mpr ⟨hscale, hmeet⟩) hfail




/-- The distance from a cube center to its parent's center is at most the
parent's radius. -/
theorem dist_cubeCenter_cubeCenter_parentCube_le (Q : TriadicCube d) :
    dist (cubeCenter Q) (cubeCenter (parentCube Q)) ≤
      (1 / 2 : ℝ) * (3 : ℝ) ^ (Q.scale + 1) := by
  have hmem : cubeCenter Q ∈ cubeSet (parentCube Q) :=
    cubeSet_subset_cubeSet_parentCube Q (cubeCenter_mem_cubeSet Q)
  have hball := cubeSet_subset_closedBall (parentCube Q) hmem
  rw [Metric.mem_closedBall] at hball
  simpa only [cubeRadius, cubeScaleFactor, parentCube_scale] using hball



theorem exists_candidate_scale_le_and_dist_le_of_stoppingRepairGenerated
    {failure : TriadicCube d → Set Omega} {omega : Omega} {Q : TriadicCube d}
    (hQ : StoppingRepairGenerated failure omega base Q) :
    ∃ P : StoppingBaseCube d base,
      Q.scale ≤ (triadicStoppingCandidate failure omega P).scale ∧
      dist (cubeCenter Q)
          (cubeCenter (triadicStoppingCandidate failure omega P)) ≤
        12 * (3 : ℝ) ^ (triadicStoppingCandidate failure omega P).scale -
          12 * (3 : ℝ) ^ Q.scale := by
  induction hQ with
  | initial S =>
      obtain ⟨P, hP⟩ := S.1.2
      exact ⟨P, by rw [hP], by rw [hP]; simp⟩
  | @parent A B _ _ hnear hscale _ ihB =>
      obtain ⟨P, hscaleP, hdistP⟩ := ihB
      set sP : ℤ := (triadicStoppingCandidate failure omega P).scale with hsP
      have h1 : (1 : ℝ) ≤ 3 := by norm_num
      have ha : (0 : ℝ) < (3 : ℝ) ^ A.scale := zpow_pos (by norm_num) _
      have hb : (0 : ℝ) < (3 : ℝ) ^ B.scale := zpow_pos (by norm_num) _
      have hab : 27 * (3 : ℝ) ^ A.scale ≤ (3 : ℝ) ^ B.scale := by
        have hstep : (3 : ℝ) ^ (A.scale + 3) ≤ (3 : ℝ) ^ B.scale :=
          zpow_le_zpow_right₀ h1 (by omega)
        have hexp : (3 : ℝ) ^ (A.scale + 3) = 27 * (3 : ℝ) ^ A.scale := by
          rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
          norm_num
          ring
        rwa [hexp] at hstep
      have hnearB : dist (cubeCenter A) (cubeCenter B) ≤ 10 * (3 : ℝ) ^ B.scale := by
        have hmax : max (cubeScaleFactor A) (cubeScaleFactor B) =
            (3 : ℝ) ^ B.scale := by
          rw [cubeScaleFactor, cubeScaleFactor, max_eq_right]
          linarith
        rw [StoppingCubesNear, hmax] at hnear
        exact hnear
      have hparent := dist_cubeCenter_cubeCenter_parentCube_le A
      have hexp1 : (3 : ℝ) ^ (A.scale + 1) = 3 * (3 : ℝ) ^ A.scale := by
        rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        norm_num
        ring
      refine ⟨P, ?_, ?_⟩
      · rw [parentCube_scale]
        omega
      · have htri1 : dist (cubeCenter (parentCube A))
            (cubeCenter (triadicStoppingCandidate failure omega P)) ≤
              dist (cubeCenter (parentCube A)) (cubeCenter A) +
                dist (cubeCenter A)
                  (cubeCenter (triadicStoppingCandidate failure omega P)) :=
          dist_triangle _ _ _
        have htri2 : dist (cubeCenter A)
            (cubeCenter (triadicStoppingCandidate failure omega P)) ≤
              dist (cubeCenter A) (cubeCenter B) +
                dist (cubeCenter B)
                  (cubeCenter (triadicStoppingCandidate failure omega P)) :=
          dist_triangle _ _ _
        rw [dist_comm (cubeCenter (parentCube A)) (cubeCenter A)] at htri1
        rw [parentCube_scale, hexp1]
        rw [hexp1] at hparent
        linarith

/-! ## 5. The Borel--Cantelli step -/

variable [MeasurableSpace Omega]

/-- The local failure event at level `n` has measure at most a dimension-only
multiple of the geometric failure bound, with a constant independent of `n`. -/
theorem measure_stoppingLocalFailureEvent_le
    (mu : Measure Omega) (failure : TriadicCube d → Set Omega)
    (C q : ENNReal)
    (hmeasure : ∀ (P : TriadicCube d) (n : ℕ), P.scale = base + (n : ℤ) →
      mu (failure P) ≤ C * q ^ n)
    (x : Vec d) (n : ℕ) :
    mu (stoppingLocalFailureEvent failure base x n) ≤
      ((2 * ⌈(1 + ‖x‖) / (3 : ℝ) ^ base⌉₊ + 131) ^ d : ℕ) * (C * q ^ n) := by
  set s : ℤ := base + (n : ℤ) with hs
  set rho : ℝ := 1 + 64 * (3 : ℝ) ^ s with hrho
  have hstep : mu (stoppingLocalFailureEvent failure base x n)
      ≤ ((triadicScaleBallFinset d s x rho).card : ℕ) • (C * q ^ n) := by
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    refine Finset.sum_le_card_nsmul _ _ _ ?_
    intro P hP
    exact hmeasure P n (mem_triadicScaleBallFinset.mp hP).1
  have hpow : (0 : ℝ) < (3 : ℝ) ^ s := zpow_pos (by norm_num) _
  have hbasepos : (0 : ℝ) < (3 : ℝ) ^ base := zpow_pos (by norm_num) _
  have hkey : (rho + ‖x‖) / (3 : ℝ) ^ s = (1 + ‖x‖) / (3 : ℝ) ^ s + (64 : ℕ) := by
    rw [hrho]
    field_simp
    ring
  have hcard : (triadicScaleBallFinset d s x rho).card
      ≤ (2 * ⌈(1 + ‖x‖) / (3 : ℝ) ^ base⌉₊ + 131) ^ d := by
    refine le_trans (card_triadicScaleBallFinset_le s x rho) ?_
    have hle : (1 + ‖x‖) / (3 : ℝ) ^ s ≤ (1 + ‖x‖) / (3 : ℝ) ^ base :=
      div_le_div_of_nonneg_left (by positivity) hbasepos
        (zpow_le_zpow_right₀ (by norm_num) (by omega : base ≤ s))
    have h1 : ⌈(rho + ‖x‖) / (3 : ℝ) ^ s⌉₊
        ≤ ⌈(1 + ‖x‖) / (3 : ℝ) ^ base⌉₊ + 64 := by
      rw [hkey,
        Nat.ceil_add_natCast (by positivity : (0 : ℝ) ≤ (1 + ‖x‖) / (3 : ℝ) ^ s)]
      exact Nat.add_le_add_right (Nat.ceil_le_ceil hle) 64
    refine Nat.pow_le_pow_left ?_ d
    omega
  rw [nsmul_eq_mul] at hstep
  refine le_trans hstep ?_
  gcongr

/-- The lattice point with integer coordinates `k`. -/
def latticePoint (k : Fin d → ℤ) : Vec d := fun i ↦ (k i : ℝ)

/-- **Borel--Cantelli for the local failure events.**  Almost surely, above
some level no triadic cube of that scale near a given lattice point fails. -/
theorem ae_forall_exists_forall_ge_not_mem_stoppingLocalFailureEvent
    (mu : Measure Omega) (failure : TriadicCube d → Set Omega) (C q : ENNReal)
    (hC : C ≠ ∞) (hq : q < 1)
    (hmeasure : ∀ (P : TriadicCube d) (n : ℕ), P.scale = base + (n : ℤ) →
      mu (failure P) ≤ C * q ^ n) :
    ∀ᵐ omega ∂mu, ∀ k : Fin d → ℤ, ∃ B : ℕ, ∀ n, B ≤ n →
      omega ∉ stoppingLocalFailureEvent failure base (latticePoint k) n := by
  rw [ae_all_iff]
  intro k
  set x : Vec d := latticePoint k with hx
  set K : ℕ := (2 * ⌈(1 + ‖x‖) / (3 : ℝ) ^ base⌉₊ + 131) ^ d with hK
  have hbound : (∑' n, mu (stoppingLocalFailureEvent failure base x n))
      ≤ (K : ENNReal) * C * (1 - q)⁻¹ := by
    calc (∑' n, mu (stoppingLocalFailureEvent failure base x n))
        ≤ ∑' n : ℕ, (K : ENNReal) * (C * q ^ n) :=
          ENNReal.tsum_le_tsum fun n ↦
            measure_stoppingLocalFailureEvent_le mu failure C q hmeasure x n
      _ = (K : ENNReal) * C * (1 - q)⁻¹ := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
            mul_assoc]
  have hsum : (∑' n, mu (stoppingLocalFailureEvent failure base x n)) ≠ ∞ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top K) hC)
        (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_of_lt hq))))
      hbound
  filter_upwards [ae_finite_setOf_mem hsum] with omega hfin
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨B + 1, fun n hn hmem ↦ ?_⟩
  have hle : n ≤ B := hB hmem
  omega

/-! ## 6. From the local failure events to the two certificates -/

/-- Ancestors compose. -/
theorem ancestorCube_ancestorCube (j k : ℕ) (Q : TriadicCube d) :
    ancestorCube j (ancestorCube k Q) = ancestorCube (j + k) Q := by
  simp only [ancestorCube, ← Function.iterate_add_apply]

/-- A lower ancestor sits inside a higher one. -/
theorem cubeSet_ancestorCube_subset_of_le {j k : ℕ} (hjk : j ≤ k)
    (Q : TriadicCube d) :
    cubeSet (ancestorCube j Q) ⊆ cubeSet (ancestorCube k Q) := by
  have hsub := cubeSet_subset_cubeSet_ancestorCube (k - j) (ancestorCube j Q)
  rwa [ancestorCube_ancestorCube, Nat.sub_add_cancel hjk] at hsub

omit [MeasurableSpace Omega] in


theorem triadicStoppingDepth_le_of_dist_cubeCenter_le
    {failure : TriadicCube d → Set Omega} {omega : Omega} {x : Vec d} {B : ℕ}
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    (hgood : ∀ n, B ≤ n →
      omega ∉ stoppingLocalFailureEvent failure base x n)
    {Q : StoppingBaseCube d base}
    (hcenter : dist (cubeCenter (triadicStoppingCandidate failure omega Q)) x ≤
      1 + 13 * (3 : ℝ) ^ (triadicStoppingCandidate failure omega Q).scale) :
    triadicStoppingDepth failure omega Q ≤ B := by
  by_contra hcon
  push_neg at hcon
  set D : ℕ := triadicStoppingDepth failure omega Q with hD
  set n : ℕ := D - 1 with hn
  have hBn : B ≤ n := by omega
  have hDn : D = n + 1 := by omega
  have hfail : omega ∈ failure (ancestorCube n Q.1) :=
    mem_failure_ancestor_pred_triadicStoppingDepth failure (hfinite Q) (by omega)
  set P : TriadicCube d := ancestorCube n Q.1 with hP
  have hscaleP : P.scale = base + (n : ℤ) := by
    rw [hP, ancestorCube_scale, Q.2]
  set Cand : TriadicCube d := triadicStoppingCandidate failure omega Q with hCand
  have hscaleC : Cand.scale = base + (D : ℤ) := by
    rw [hCand, triadicStoppingCandidate_scale]
  have hsub : cubeSet P ⊆ cubeSet Cand := by
    rw [hP, hCand, triadicStoppingCandidate]
    exact cubeSet_ancestorCube_subset_of_le (by omega) Q.1
  have hwC : cubeCenter P ∈ cubeSet Cand := hsub (cubeCenter_mem_cubeSet P)
  have hw := cubeSet_subset_closedBall Cand hwC
  rw [Metric.mem_closedBall] at hw
  have hexp : (3 : ℝ) ^ Cand.scale = 3 * (3 : ℝ) ^ (base + (n : ℤ)) := by
    rw [hscaleC, hDn]
    push_cast
    rw [show base + ((n : ℤ) + 1) = (base + (n : ℤ)) + 1 by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hradius : cubeRadius Cand = (1 / 2 : ℝ) * (3 * (3 : ℝ) ^ (base + (n : ℤ))) := by
    rw [cubeRadius, cubeScaleFactor, hexp]
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (base + (n : ℤ)) := zpow_pos (by norm_num) _
  have hdist : dist (cubeCenter P) x ≤ 1 + 64 * (3 : ℝ) ^ (base + (n : ℤ)) := by
    have htri : dist (cubeCenter P) x ≤
        dist (cubeCenter P) (cubeCenter Cand) + dist (cubeCenter Cand) x :=
      dist_triangle _ _ _
    rw [hradius] at hw
    rw [hexp] at hcenter
    linarith
  exact hgood n hBn
    (mem_stoppingLocalFailureEvent_of_mem_failure hscaleP
      ⟨cubeCenter P, cubeCenter_mem_cubeSet P, Metric.mem_closedBall.mpr hdist⟩
      hfail)

omit [MeasurableSpace Omega] in
/-- Every point is within `1/2` of a lattice point in the sup metric. -/
theorem dist_latticePoint_round_le (x : Vec d) :
    dist x (latticePoint (fun i ↦ round (x i))) ≤ 1 / 2 := by
  rw [dist_pi_le_iff (by norm_num)]
  intro i
  rw [Real.dist_eq]
  simpa only [latticePoint] using abs_sub_round (x i)

omit [MeasurableSpace Omega] in
/-- **The `hinitial` certificate from the local failure events.** -/
theorem locallyFinite_triadicStoppingCandidate_of_forall_ge_not_mem
    {failure : TriadicCube d → Set Omega} {omega : Omega}
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    (hgood : ∀ k : Fin d → ℤ, ∃ B : ℕ, ∀ n, B ≤ n →
      omega ∉ stoppingLocalFailureEvent failure base (latticePoint k) n) :
    LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q) := by
  refine locallyFinite_triadicStoppingCandidate_of_local_depth_bound failure omega ?_
  intro x
  obtain ⟨B, hB⟩ := hgood (fun i ↦ round (x i))
  refine ⟨1 / 2, by norm_num, B, ?_⟩
  intro Q hmeet
  refine triadicStoppingDepth_le_of_dist_cubeCenter_le hfinite hB ?_
  obtain ⟨z, hzC, hzx⟩ := hmeet
  set Cand : TriadicCube d := triadicStoppingCandidate failure omega Q with hCand
  have hz := cubeSet_subset_closedBall Cand hzC
  rw [Metric.mem_closedBall] at hz
  rw [Metric.mem_ball] at hzx
  have hlat := dist_latticePoint_round_le (d := d) x
  have htri1 : dist (cubeCenter Cand) (latticePoint fun i ↦ round (x i)) ≤
      dist (cubeCenter Cand) z + dist z (latticePoint fun i ↦ round (x i)) :=
    dist_triangle _ _ _
  have htri2 : dist z (latticePoint fun i ↦ round (x i)) ≤
      dist z x + dist x (latticePoint fun i ↦ round (x i)) :=
    dist_triangle _ _ _
  rw [dist_comm (cubeCenter Cand) z] at htri1
  have hrad : cubeRadius Cand = (1 / 2 : ℝ) * (3 : ℝ) ^ Cand.scale := by
    rw [cubeRadius, cubeScaleFactor]
  have hpos : (0 : ℝ) < (3 : ℝ) ^ Cand.scale := zpow_pos (by norm_num) _
  rw [hrad] at hz
  linarith

omit [MeasurableSpace Omega] in


theorem scale_le_of_stoppingRepairGenerated_of_forall_ge_not_mem
    {failure : TriadicCube d → Set Omega} {omega : Omega} {x : Vec d} {B : ℕ}
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    (hgood : ∀ n, B ≤ n →
      omega ∉ stoppingLocalFailureEvent failure base x n)
    {Q : TriadicCube d} (hQ : StoppingRepairGenerated failure omega base Q)
    (hmeet : (cubeSet Q ∩ Metric.closedBall x 1).Nonempty) :
    Q.scale ≤ base + (B : ℤ) := by
  obtain ⟨P, hscaleP, hdistP⟩ :=
    exists_candidate_scale_le_and_dist_le_of_stoppingRepairGenerated hQ
  set Cand : TriadicCube d := triadicStoppingCandidate failure omega P with hCand
  have hdepth : triadicStoppingDepth failure omega P ≤ B := by
    refine triadicStoppingDepth_le_of_dist_cubeCenter_le hfinite hgood ?_
    obtain ⟨z, hzQ, hzx⟩ := hmeet
    rw [Metric.mem_closedBall] at hzx
    have hz := cubeSet_subset_closedBall Q hzQ
    rw [Metric.mem_closedBall] at hz
    have htri1 : dist (cubeCenter Cand) x ≤
        dist (cubeCenter Cand) (cubeCenter Q) + dist (cubeCenter Q) x :=
      dist_triangle _ _ _
    have htri2 : dist (cubeCenter Q) x ≤ dist (cubeCenter Q) z + dist z x :=
      dist_triangle _ _ _
    rw [dist_comm (cubeCenter Cand) (cubeCenter Q)] at htri1
    rw [dist_comm (cubeCenter Q) z] at htri2
    have hrad : cubeRadius Q = (1 / 2 : ℝ) * (3 : ℝ) ^ Q.scale := by
      rw [cubeRadius, cubeScaleFactor]
    rw [hrad] at hz
    have hposQ : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
    have hposC : (0 : ℝ) < (3 : ℝ) ^ Cand.scale := zpow_pos (by norm_num) _
    linarith
  have hCandScale : Cand.scale = base + (triadicStoppingDepth failure omega P : ℤ) := by
    rw [hCand, triadicStoppingCandidate_scale]
  have : (triadicStoppingDepth failure omega P : ℤ) ≤ (B : ℤ) := by exact_mod_cast hdepth
  omega

omit [MeasurableSpace Omega] in
/-- **The `hrepair` certificate from the local failure events.** -/
theorem locallyFinite_stoppingRepairCube_of_forall_ge_not_mem
    {failure : TriadicCube d → Set Omega} {omega : Omega}
    (hfinite : ∀ P : StoppingBaseCube d base,
      triadicFailureHeight failure omega P ≠ (⊤ : WithTop ℕ))
    (hgood : ∀ k : Fin d → ℤ, ∃ B : ℕ, ∀ n, B ≤ n →
      omega ∉ stoppingLocalFailureEvent failure base (latticePoint k) n) :
    LocallyFinite fun Q : StoppingRepairCube failure omega base ↦ cubeSet Q.1 := by
  intro x
  obtain ⟨B, hB⟩ := hgood (fun i ↦ round (x i))
  set y : Vec d := latticePoint (fun i ↦ round (x i)) with hy
  have hxy : dist x y ≤ 1 / 2 := dist_latticePoint_round_le (d := d) x
  refine ⟨Metric.ball x (1 / 2), Metric.ball_mem_nhds x (by norm_num), ?_⟩
  have hfin : {P : TriadicCube d |
      (∃ j : ℕ, j ≤ B ∧ P.scale = base + (j : ℤ)) ∧
        (cubeSet P ∩ Metric.closedBall y 1).Nonempty}.Finite := by
    refine Set.Finite.subset
      (Set.Finite.biUnion (Finset.range (B + 1)).finite_toSet
        (fun j _ ↦ finite_triadicCube_scale_eq_meeting_isBounded (d := d)
          (base + (j : ℤ)) (S := Metric.closedBall y 1)
          Metric.isBounded_closedBall)) ?_
    rintro P ⟨⟨j, hjB, hscale⟩, hne⟩
    exact Set.mem_biUnion (by simpa using Nat.lt_succ_of_le hjB) ⟨hscale, hne⟩
  refine Set.Finite.of_finite_image
    (f := fun Q : StoppingRepairCube failure omega base ↦ Q.1)
    (hfin.subset ?_) (fun P _ R _ hPR ↦ Subtype.ext hPR)
  rintro P ⟨Q, hQ, rfl⟩
  obtain ⟨z, hzQ, hzx⟩ := hQ
  rw [Metric.mem_ball] at hzx
  have hzy : dist z y ≤ 1 := by
    have := dist_triangle z x y
    linarith
  have hmeet : (cubeSet Q.1 ∩ Metric.closedBall y 1).Nonempty :=
    ⟨z, hzQ, Metric.mem_closedBall.mpr hzy⟩
  have hlow : base ≤ Q.1.scale := base_le_scale_of_stoppingRepairGenerated Q.2
  have hhigh : Q.1.scale ≤ base + (B : ℤ) :=
    scale_le_of_stoppingRepairGenerated_of_forall_ge_not_mem hfinite hB Q.2 hmeet
  refine ⟨⟨(Q.1.scale - base).toNat, ?_, ?_⟩, hmeet⟩
  · omega
  · show Q.1.scale = base + (((Q.1.scale - base).toNat : ℕ) : ℤ)
    omega

/-! ## 7. The almost-sure producer -/



theorem ae_locallyFinite_stoppingCertificates_of_le_geometric
    (mu : Measure Omega) (failure : TriadicCube d → Set Omega) (C q : ENNReal)
    (hC : C ≠ ∞) (hq : q < 1)
    (hmeasure : ∀ (P : TriadicCube d) (n : ℕ), P.scale = base + (n : ℤ) →
      mu (failure P) ≤ C * q ^ n) :
    ∀ᵐ omega ∂mu,
      (LocallyFinite fun Q : StoppingBaseCube d base ↦
          cubeSet (triadicStoppingCandidate failure omega Q)) ∧
        (LocallyFinite fun Q : StoppingRepairCube failure omega base ↦
          cubeSet Q.1) := by
  have hfinite := ae_forall_triadicFailureHeight_ne_top_of_le_geometric
    (base := base) mu failure C q hC hq
    (fun Q j ↦ hmeasure (ancestorCube j Q.1) j (by rw [ancestorCube_scale, Q.2]))
  have hbc := ae_forall_exists_forall_ge_not_mem_stoppingLocalFailureEvent
    (base := base) mu failure C q hC hq hmeasure
  filter_upwards [hfinite, hbc] with omega hfin hgood
  exact ⟨locallyFinite_triadicStoppingCandidate_of_forall_ge_not_mem hfin hgood,
    locallyFinite_stoppingRepairCube_of_forall_ge_not_mem hfin hgood⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
