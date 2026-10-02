import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Lane3.Forms
import SubdiffusiveProcess.Lane3.Subdivision
import SubdiffusiveProcess.Lane3.DirichletForm
import SubdiffusiveProcess.Lane3.ResamplingV2
import SubdiffusiveProcess.Lane3.UpperDensity
import SubdiffusiveProcess.Lane3.BandFiltration
import SubdiffusiveProcess.Probability.LayerProductBlocks
import SubdiffusiveProcess.Probability.ResponseCompactness
import SubdiffusiveProcess.Variational.QuadraticSaving
import SubdiffusiveProcess.Compactness.OperatorLimits
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_lem_branch_windows
    {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (n : ι → ℤ) (hn : Function.Injective n)
    (h : ι → ℕ+ ) :
    ∃ s : Finset ι,
      s ⊆ t ∧
      (∀ ⦃i⦄, i ∈ s → ∀ ⦃k⦄, k ∈ s → i ≠ k →
        Disjoint
          (Finset.Icc (n i - (h i : ℤ)) (n i + 2 * (h i : ℤ)))
          (Finset.Icc (n k - (h k : ℤ)) (n k + 2 * (h k : ℤ)))) ∧
      t.card ≤ 12 * ∑ i ∈ s, (h i : ℕ) := by
  classical
  refine Finset.strongInductionOn t ?_
  intro t ih
  by_cases ht : t.card ≠ 0
  · have ht' : t.Nonempty := Finset.card_ne_zero.mp ht
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image t h ht'
    let A : ι → Finset ℤ := fun j =>
      Finset.Icc (n j - (h j : ℤ)) (n j + 2 * (h j : ℤ))
    let c : Finset ι := t.filter (fun j => ¬ Disjoint (A j) (A i))
    let v : Finset ι := t \ c
    have hAi : (A i).Nonempty := by
      refine ⟨n i, ?_⟩
      dsimp [A]
      have hi0 : (0 : ℤ) < (h i : ℤ) := by positivity
      simp only [Finset.mem_Icc]
      constructor <;> omega
    have hic : i ∈ c := by
      apply Finset.mem_filter.mpr
      refine ⟨hi, ?_⟩
      exact Finset.not_disjoint_iff.mpr ⟨n i, by
        dsimp [A]
        simp only [Finset.mem_Icc]
        have hi0 : (0 : ℤ) < (h i : ℤ) := by positivity
        constructor <;> omega, by
        dsimp [A]
        simp only [Finset.mem_Icc]
        have hi0 : (0 : ℤ) < (h i : ℤ) := by positivity
        constructor <;> omega⟩
    have hcsub : c ⊆ t := Finset.filter_subset _ _
    have hvsub : v ⊆ t := Finset.sdiff_subset
    have hiv : i ∉ v := by
      intro hiv
      exact (Finset.mem_sdiff.mp hiv).2 hic
    have hvne : v ≠ t := by
      intro heq
      exact hiv (heq ▸ hi)
    have hvproper : v ⊂ t := Finset.ssubset_iff_subset_ne.mpr ⟨hvsub, hvne⟩
    obtain ⟨s, hsv, hsdisj, hsbound⟩ := ih v hvproper
    have hdisjv : ∀ ⦃j⦄, j ∈ v → Disjoint (A j) (A i) := by
      intro j hj
      by_contra hnot
      exact (Finset.mem_sdiff.mp hj).2
        (Finset.mem_filter.mpr ⟨hvsub hj, hnot⟩)
    have hcwindow : c.image n ⊆ Finset.Icc
          (n i - 3 * (h i : ℤ)) (n i + 3 * (h i : ℤ)) := by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨j, hjc, rfl⟩ := hz
      have hjt : j ∈ t := (Finset.mem_filter.mp hjc).1
      have hjnot : ¬ Disjoint (A j) (A i) := (Finset.mem_filter.mp hjc).2
      obtain ⟨x, hxj, hxi⟩ := Finset.not_disjoint_iff.mp hjnot
      have hjmax : (h j : ℤ) ≤ (h i : ℤ) := by
        have := hmax j hjt
        exact_mod_cast this
      dsimp [A] at hxj hxi
      simp only [Finset.mem_Icc] at hxj hxi
      simp only [Finset.mem_Icc]
      constructor <;> omega
    have hc : c.card ≤ 12 * (h i : ℕ) := by
      rw [← Finset.card_image_of_injective c hn]
      refine (Finset.card_le_card hcwindow).trans ?_
      rw [Int.card_Icc]
      have hi_nat : 1 ≤ (h i : ℕ) := (h i).property
      omega
    have hsi : i ∉ s := fun his => hiv (hsv his)
    refine ⟨insert i s, ?_⟩
    constructor
    · intro j hj
      simp only [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact hi
      · exact hsv.trans hvsub hj
    constructor
    · intro j hjs k hks hjk
      simp only [Finset.mem_insert] at hjs hks
      rcases hjs with rfl | hjs <;> rcases hks with rfl | hks
      · exact (hjk rfl).elim
      · simpa [A] using (hdisjv (hsv hks)).symm
      · simpa [A] using hdisjv (hsv hjs)
      · simpa [A] using hsdisj hjs hks hjk
    · have htc : t.card = c.card + v.card := by
        rw [← Finset.card_union_of_disjoint]
        · rw [Finset.union_sdiff_of_subset hcsub]
        · apply Finset.disjoint_left.mpr
          intro j hjc hjv
          exact (Finset.mem_sdiff.mp hjv).2 hjc
      rw [htc]
      calc
        c.card + v.card ≤ 12 * (h i : ℕ) + 12 * ∑ j ∈ s, (h j : ℕ) :=
          Nat.add_le_add hc hsbound
        _ = 12 * ((h i : ℕ) + ∑ j ∈ s, (h j : ℕ)) := by omega
        _ = 12 * ∑ j ∈ insert i s, (h j : ℕ) := by
          rw [Finset.sum_insert hsi]
  · have ht0 : t.card = 0 := by omega
    exact ⟨∅, Finset.empty_subset _, by simp,
      by simp [Finset.card_eq_zero.mp ht0]⟩

theorem aux_lem_branch_witnesses
    {Om : Type*} (J : ℕ) (theta : ℝ)
    (ns : Fin J → ℤ) (hns : Function.Injective ns)
    (fail : Fin J → Set Om) (W : Fin J → ℕ+ → Set Om)
    (hfail : ∀ i : Fin J, fail i ⊆ ⋃ h : ℕ+, W i h)
    (ω : Om)
    (hbad : theta * (J : ℝ) ≤ (Set.ncard {i : Fin J | ω ∈ fail i} : ℝ)) :
    ∃ w : Fin J → Option ℕ+,
      (∀ (i : Fin J) (h : ℕ+), w i = some h → ω ∈ W i h) ∧
      (∀ (i k : Fin J) (hi hk : ℕ+), i ≠ k →
        w i = some hi → w k = some hk →
        Disjoint
          (Finset.Icc (ns i - (hi : ℤ)) (ns i + 2 * (hi : ℤ)))
          (Finset.Icc (ns k - (hk : ℤ)) (ns k + 2 * (hk : ℤ)))) ∧
      theta * (J : ℝ) ≤ 12 *
        ((∑ i : Fin J, (w i).elim (0 : ℕ) (fun h => (h : ℕ))) : ℝ) := by
  classical
  let bad : Set (Fin J) := {i | ω ∈ fail i}
  let t : Finset (Fin J) := (Set.toFinite bad).toFinset
  have hmem : ∀ i : Fin J, i ∈ t ↔ i ∈ bad := by
    intro i
    simp [t, bad]
  have hcard : Set.ncard bad = t.card := by
    rw [Set.ncard_eq_toFinset_card bad (Set.toFinite bad)]
  have hbad' : theta * (J : ℝ) ≤ (t.card : ℝ) := by
    change theta * (J : ℝ) ≤ (Set.ncard bad : ℝ) at hbad
    rw [hcard] at hbad
    exact hbad
  have hcover : ∀ i : Fin J, i ∈ t → ∃ h : ℕ+, ω ∈ W i h := by
    intro i hi
    have hfi : ω ∈ fail i := (hmem i).mp hi
    rcases Set.mem_iUnion.mp (hfail i hfi) with ⟨h, hh⟩
    exact ⟨h, hh⟩
  let q : Fin J → ℕ+ := fun i =>
    if hi : i ∈ t then Classical.choose (hcover i hi) else 1
  have hq : ∀ i : Fin J, i ∈ t → ω ∈ W i (q i) := by
    intro i hi
    dsimp [q]
    rw [dif_pos hi]
    exact Classical.choose_spec (hcover i hi)
  obtain ⟨s, hst, hsdisj, hbound⟩ := aux_lem_branch_windows t ns hns q
  let w : Fin J → Option ℕ+ := fun i => if i ∈ s then some (q i) else none
  refine ⟨w, ?_, ?_, ?_⟩
  · intro i h hiw
    by_cases his : i ∈ s
    · have hqi : q i = h := by simpa [w, his] using hiw
      rw [← hqi]
      exact hq i (hst his)
    · simp [w, his] at hiw
  · intro i k hi hk hne hwi hwk
    by_cases his : i ∈ s
    · by_cases hks : k ∈ s
      · have hqi : q i = hi := by simpa [w, his] using hwi
        have hqk : q k = hk := by simpa [w, hks] using hwk
        simpa [hqi, hqk] using hsdisj his hks hne
      · simp [w, hks] at hwk
    · simp [w, his] at hwi
  · have hsum :
        (∑ i : Fin J, (w i).elim (0 : ℝ) (fun h => (h : ℝ))) =
          ∑ i ∈ s, (q i : ℝ) := by
      have hw : ∀ i : Fin J,
          (w i).elim (0 : ℝ) (fun h => (h : ℝ)) =
            if i ∈ s then (q i : ℝ) else 0 := by
        intro i
        by_cases hi : i ∈ s <;> simp [w, hi]
      calc
        (∑ i : Fin J, (w i).elim (0 : ℝ) (fun h => (h : ℝ))) =
            ∑ i : Fin J, if i ∈ s then (q i : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hw i
        _ = ∑ i ∈ s, (q i : ℝ) := by
          rw [← Finset.sum_filter]
          simp
    have hboundR : (t.card : ℝ) ≤ (12 : ℝ) * ∑ i ∈ s, (q i : ℝ) := by
      exact_mod_cast hbound
    have hfinal : theta * (J : ℝ) ≤
        12 * (∑ i : Fin J, (w i).elim (0 : ℝ) (fun h => (h : ℝ))) := by
      rw [hsum]
      exact hbad'.trans hboundR
    simpa using hfinal

theorem aux_lem_branch_weights (J : ℕ) (A : ℝ) (hA : 0 < A) :
    (∑' w : Fin J → Option ℕ+,
      ∏ i : Fin J, (w i).elim (1 : ℝ≥0∞)
        (fun h => ENNReal.ofReal (Real.exp (-A * (h : ℝ) / 2)))) =
      ENNReal.ofReal (((1 - Real.exp (-A / 2))⁻¹) ^ J) := by
  let f : Option ℕ+ → ℝ≥0∞ := fun o =>
    o.elim (1 : ℝ≥0∞)
      (fun h => ENNReal.ofReal (Real.exp (-A * (h : ℝ) / 2)))
  have hopt (g : Option ℕ+ → ℝ≥0∞) :
      (∑' o, g o) = g none + ∑' p : ℕ+, g (some p) := by
    let eo := Equiv.optionEquivSumPUnit ℕ+
    let es := Equiv.sumEquivSigmaBool ℕ+ PUnit
    calc
      (∑' o, g o) = ∑' s : ℕ+ ⊕ PUnit, g (eo.symm s) :=
        (eo.symm.tsum_eq g).symm
      _ = ∑' z : (b : Bool) × bif b then PUnit else ℕ+,
          g (eo.symm (es.symm z)) := by
        exact (es.symm.tsum_eq (fun s => g (eo.symm s))).symm
      _ = g none + ∑' p : ℕ+, g (some p) := by
        change (∑' z : (b : Bool) × bif b then PUnit else ℕ+,
          (fun b x => g (eo.symm (es.symm ⟨b, x⟩))) z.1 z.2) = _
        have hs := ENNReal.tsum_sigma
          (fun b x => g (eo.symm (es.symm ⟨b, x⟩)))
        rw [hs]
        simp [eo, es, Equiv.sumEquivSigmaBool, Equiv.optionEquivSumPUnit,
          tsum_fintype]
  have hneg : -A / 2 < 0 := by linarith
  have hexp : Real.exp (-A / 2) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hneg
  have hq : ENNReal.ofReal (Real.exp (-A / 2)) < 1 :=
    ENNReal.ofReal_lt_one.mpr hexp
  have hcoord : (∑' o, f o) =
      (1 - ENNReal.ofReal (Real.exp (-A / 2)))⁻¹ := by
    rw [hopt]
    have hpnat : (∑' p : ℕ+, f (some p)) =
        ∑' n : ℕ, ENNReal.ofReal (Real.exp (-A * ((n + 1 : ℕ) : ℝ) / 2)) := by
      rw [← (Equiv.pnatEquivNat.symm.tsum_eq (fun n : ℕ+ => f (some n)))]
      simp [f, Equiv.pnatEquivNat]
    rw [hpnat]
    rw [show (∑' n : ℕ, ENNReal.ofReal (Real.exp (-A * ((n + 1 : ℕ) : ℝ) / 2))) =
        ∑' n : ℕ, (ENNReal.ofReal (Real.exp (-A / 2))) ^ (n + 1) by
      apply tsum_congr
      intro n
      rw [← ENNReal.ofReal_pow (by positivity)]
      congr 1
      rw [← Real.exp_nat_mul]
      ring_nf]
    rw [ENNReal.tsum_geometric_add_one]
    have hsub : 1 - ENNReal.ofReal (Real.exp (-A / 2)) ≠ 0 :=
      ne_of_gt (tsub_pos_iff_lt.mpr hq)
    have hmul :
        (1 - ENNReal.ofReal (Real.exp (-A / 2))) *
            (1 - ENNReal.ofReal (Real.exp (-A / 2)))⁻¹ = 1 := by
      exact ENNReal.mul_inv_cancel hsub (by simp)
    simp only [f, Option.elim_none, one_mul, Option.elim_some]
    calc
      1 + ENNReal.ofReal (Real.exp (-A / 2)) *
          (1 - ENNReal.ofReal (Real.exp (-A / 2)))⁻¹ =
          (1 - ENNReal.ofReal (Real.exp (-A / 2))) *
              (1 - ENNReal.ofReal (Real.exp (-A / 2)))⁻¹ +
            ENNReal.ofReal (Real.exp (-A / 2)) *
              (1 - ENNReal.ofReal (Real.exp (-A / 2)))⁻¹ := by
            rw [hmul]
      _ = (1 - ENNReal.ofReal (Real.exp (-A / 2)))⁻¹ := by
        rw [← add_mul, tsub_add_cancel_of_le hq.le, one_mul]
  have hfactor : ∀ n : ℕ,
      (∑' w : Fin n → Option ℕ+, ∏ i : Fin n, f (w i)) =
        (∑' o : Option ℕ+, f o) ^ n := by
    intro n
    induction n with
    | zero => simp [tsum_fintype]
    | succ n ih =>
        let ec := Fin.consEquiv (fun _ : Fin (n + 1) => Option ℕ+)
        calc
          (∑' w : Fin (n + 1) → Option ℕ+, ∏ i : Fin (n + 1), f (w i)) =
              ∑' p : Option ℕ+ × (Fin n → Option ℕ+),
                ∏ i : Fin (n + 1), f ((ec p) i) := by
            exact (ec.tsum_eq (fun w => ∏ i : Fin (n + 1), f (w i))).symm
          _ = ∑' b : Option ℕ+, ∑' v : Fin n → Option ℕ+,
                f b * ∏ i : Fin n, f (v i) := by
            change (∑' p : Option ℕ+ × (Fin n → Option ℕ+),
              (fun b v => ∏ i : Fin (n + 1), f ((ec (b, v)) i)) p.1 p.2) = _
            calc
              (∑' p : Option ℕ+ × (Fin n → Option ℕ+),
                (fun b v => ∏ i : Fin (n + 1), f ((ec (b, v)) i)) p.1 p.2) =
                  ∑' b : Option ℕ+, ∑' v : Fin n → Option ℕ+,
                    ∏ i : Fin (n + 1), f ((ec (b, v)) i) := by
                      simpa using (ENNReal.tsum_prod
                        (f := fun b v => ∏ i : Fin (n + 1), f ((ec (b, v)) i)))
              _ = ∑' b : Option ℕ+, ∑' v : Fin n → Option ℕ+,
                    f b * ∏ i : Fin n, f (v i) := by
                apply tsum_congr
                intro b
                apply tsum_congr
                intro v
                simp [ec, Fin.prod_univ_succ]
          _ = (∑' b : Option ℕ+, f b) *
                (∑' v : Fin n → Option ℕ+, ∏ i : Fin n, f (v i)) := by
            simp_rw [ENNReal.tsum_mul_left]
            rw [ENNReal.tsum_mul_right]
          _ = (∑' o : Option ℕ+, f o) ^ (n + 1) := by
            rw [ih, pow_succ, mul_comm]
  change (∑' w : Fin J → Option ℕ+, ∏ i : Fin J, f (w i)) = _
  rw [hfactor J, hcoord]
  have hbase : ENNReal.ofReal ((1 - Real.exp (-A / 2))⁻¹) =
      (1 - ENNReal.ofReal (Real.exp (-A / 2)))⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (sub_pos.mpr hexp)]
    rw [ENNReal.ofReal_sub (1 : ℝ) (le_of_lt (Real.exp_pos _))]
    simp
  rw [← hbase, ← ENNReal.ofReal_pow
    (le_of_lt (inv_pos.mpr (sub_pos.mpr hexp)))]



theorem lem_branch
    (Om : Type) [MeasurableSpace Om] (P : Measure Om) [IsProbabilityMeasure P]
    (blockSigma : ℤ → ℤ → MeasurableSpace Om)
    (hindep : ∀ (n : ℕ) (lo hi : Fin n → ℤ) (Wf : Fin n → Set Om),
      (∀ i, MeasurableSet[blockSigma (lo i) (hi i)] (Wf i)) →
      (∀ i k, i ≠ k →
        Disjoint (Finset.Icc (lo i) (hi i)) (Finset.Icc (lo k) (hi k))) →
      P (⋂ i, Wf i) = ∏ i, P (Wf i))
    (A theta : ℝ) (hA : 0 < A) (hth : 0 < theta) (hth1 : theta < 1)
    (J : ℕ) (ns : Fin J → ℤ) (hns : Function.Injective ns)
    (fail : Fin J → Set Om) (W : Fin J → ℕ+ → Set Om)
    (hWmeas : ∀ (i : Fin J) (h : ℕ+),
      MeasurableSet[blockSigma (ns i - (h : ℤ)) (ns i + 2 * (h : ℤ))] (W i h))
    (hWP : ∀ (i : Fin J) (h : ℕ+),
      P (W i h) ≤ ENNReal.ofReal (Real.exp (-(A * (h : ℝ)))))
    (hfail : ∀ i : Fin J, fail i ⊆ ⋃ h : ℕ+, W i h) :
    P {ω | theta * (J : ℝ) ≤ ({i : Fin J | ω ∈ fail i}.ncard : ℝ)} ≤
      ENNReal.ofReal (Real.exp
        (-((A * theta / 24 + Real.log (1 - Real.exp (-(A / 2)))) * (J : ℝ)))) := by
  classical
  have huniv : ∀ a b : ℤ, MeasurableSet[blockSigma a b] (Set.univ : Set Om) :=
    fun a b => MeasurableSet.univ
  let S : (Fin J → Option ℕ+) → Finset (Fin J) := fun w =>
    Finset.univ.filter (fun i => ∃ h : ℕ+, w i = some h)
  let rN : (Fin J → Option ℕ+) → Fin J → ℕ := fun w i =>
    (w i).elim (0 : ℕ) (fun h => (h : ℕ))
  let r : (Fin J → Option ℕ+) → Fin J → ℝ := fun w i => (rN w i : ℝ)
  let E : (Fin J → Option ℕ+) → Fin J → Set Om := fun w i =>
    (w i).elim Set.univ (fun h => W i h)
  let V : (Fin J → Option ℕ+) → Fin J → Finset ℤ := fun w i =>
    (w i).elim ∅ (fun h => Finset.Icc (ns i - (h : ℤ)) (ns i + 2 * (h : ℤ)))
  let I : (Fin J → Option ℕ+) → Set Om := fun w => ⋂ i, E w i
  let Admissible : (Fin J → Option ℕ+) → Prop := fun w =>
    (∀ ⦃i⦄, i ∈ S w → ∀ ⦃k⦄, k ∈ S w → i ≠ k →
      Disjoint (V w i) (V w k)) ∧
    theta * (J : ℝ) ≤ 12 * ∑ i ∈ S w, r w i
  let K : (Fin J → Option ℕ+) → Set Om := fun w =>
    if h : Admissible w then I w else ∅
  let weight : (Fin J → Option ℕ+) → ℝ≥0∞ := fun w =>
    ∏ i : Fin J, (w i).elim (1 : ℝ≥0∞)
      (fun h => ENNReal.ofReal (Real.exp (-A * (h : ℝ) / 2)))
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-A * theta * (J : ℝ) / 24))
  have hmem_iff : ∀ (w : Fin J → Option ℕ+) (i : Fin J),
      i ∈ S w ↔ ∃ h : ℕ+, w i = some h := by
    intro w i
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hnone_of_not_mem : ∀ (w : Fin J → Option ℕ+) (i : Fin J),
      i ∉ S w → w i = none := by
    intro w i hi
    cases hwi : w i with
    | none => rfl
    | some h => exact (hi ((hmem_iff w i).mpr ⟨h, hwi⟩)).elim
  have hIcc_none_left : ∀ t : Finset ℤ, Disjoint (Finset.Icc (1 : ℤ) 0) t := by
    intro t
    rw [Finset.disjoint_left]
    intro x hx _
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hx
    omega
  have hIcc_none_right : ∀ t : Finset ℤ, Disjoint t (Finset.Icc (1 : ℤ) 0) := by
    intro t
    rw [Finset.disjoint_right]
    intro x hx _
    obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp hx
    omega
  have hprodS : ∀ w : Fin J → Option ℕ+,
      (∏ i : Fin J, P (E w i)) = ∏ i ∈ S w, P (E w i) := by
    intro w
    rw [show S w = Finset.univ.filter (fun i => ∃ h : ℕ+, w i = some h) from rfl,
      Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hp : ∃ h : ℕ+, w i = some h
    · rw [if_pos hp]
    · rw [if_neg hp]
      have hnone : w i = none := by
        cases hwi : w i with
        | none => rfl
        | some h => exact (hp ⟨h, hwi⟩).elim
      simp only [E, hnone]
      exact measure_univ
  have hEmeas : ∀ (w : Fin J → Option ℕ+) (i : Fin J),
      MeasurableSet[blockSigma
        ((w i).elim (1 : ℤ) (fun h => ns i - (h : ℤ)))
        ((w i).elim (0 : ℤ) (fun h => ns i + 2 * (h : ℤ)))] (E w i) := by
    intro w i
    by_cases hi : i ∈ S w
    · obtain ⟨h, hwi⟩ := (hmem_iff w i).mp hi
      simpa [E, hwi] using hWmeas i h
    · have hnone := hnone_of_not_mem w i hi
      simp only [E, hnone]
      exact huniv 1 0
  have hbridge : ∀ w : Fin J → Option ℕ+,
      (∀ ⦃i⦄, i ∈ S w → ∀ ⦃k⦄, k ∈ S w → i ≠ k →
        Disjoint (V w i) (V w k)) →
      P (I w) = ∏ i ∈ S w, P (E w i) := by
    intro w hdisj
    have hdisj' : ∀ i k : Fin J, i ≠ k →
        Disjoint (Finset.Icc ((w i).elim (1 : ℤ) (fun h => ns i - (h : ℤ)))
            ((w i).elim (0 : ℤ) (fun h => ns i + 2 * (h : ℤ))))
          (Finset.Icc ((w k).elim (1 : ℤ) (fun h => ns k - (h : ℤ)))
            ((w k).elim (0 : ℤ) (fun h => ns k + 2 * (h : ℤ)))) := by
      intro i k hik
      by_cases hi : i ∈ S w
      · by_cases hk : k ∈ S w
        · obtain ⟨h1, hwi⟩ := (hmem_iff w i).mp hi
          obtain ⟨h2, hwk⟩ := (hmem_iff w k).mp hk
          simpa [V, hwi, hwk] using hdisj hi hk hik
        · have hnone := hnone_of_not_mem w k hk
          rw [hnone]
          exact hIcc_none_right _
      · have hnone := hnone_of_not_mem w i hi
        rw [hnone]
        exact hIcc_none_left _
    have hkey := hindep J
      (fun i => (w i).elim (1 : ℤ) (fun h => ns i - (h : ℤ)))
      (fun i => (w i).elim (0 : ℤ) (fun h => ns i + 2 * (h : ℤ)))
      (E w) (hEmeas w) hdisj'
    change P (⋂ i, E w i) = ∏ i ∈ S w, P (E w i)
    rw [hkey]
    exact hprodS w
  have hcover :
      {ω | theta * (J : ℝ) ≤ (Set.ncard {i : Fin J | ω ∈ fail i} : ℝ)} ⊆
        ⋃ w, K w := by
    intro ω hω
    obtain ⟨w, hwW, hwdisj, hwbound⟩ :=
      aux_lem_branch_witnesses J theta ns hns fail W hfail ω hω
    refine Set.mem_iUnion.2 ⟨w, ?_⟩
    have hadm : Admissible w := by
      constructor
      · intro i hi k hk hik
        have hi' : ∃ h : ℕ+, w i = some h := (hmem_iff w i).mp hi
        have hk' : ∃ h : ℕ+, w k = some h := (hmem_iff w k).mp hk
        obtain ⟨hi', hwi⟩ := hi'
        obtain ⟨hk', hwk⟩ := hk'
        simpa [V, hwi, hwk] using hwdisj i k hi' hk' hik hwi hwk
      · have hsumR :
            (∑ i : Fin J, (w i).elim (0 : ℝ) (fun h => (h : ℝ))) =
              ∑ i ∈ S w, r w i := by
          rw [show S w = Finset.univ.filter (fun i => ∃ h : ℕ+, w i = some h) from rfl,
            Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro i _
          by_cases his : ∃ h : ℕ+, w i = some h
          · obtain ⟨h, hwi⟩ := his
            simp [r, rN, hwi]
          · have hnone : w i = none := by
              cases hwi : w i with
              | none => rfl
              | some h => exact (his ⟨h, hwi⟩).elim
            simp [r, rN, hnone]
        calc
          theta * (J : ℝ) ≤
              12 * (∑ i : Fin J, (w i).elim (0 : ℝ) (fun h => (h : ℝ))) := by
            simpa using hwbound
          _ = 12 * ∑ i ∈ S w, r w i := by rw [hsumR]
    simp only [K]
    rw [dif_pos hadm]
    rw [show I w = ⋂ i, E w i from rfl]
    simp only [Set.mem_iInter]
    intro i
    by_cases hi : i ∈ S w
    · obtain ⟨h, hwi⟩ := (hmem_iff w i).mp hi
      have hiW : ω ∈ W i h := hwW i h hwi
      simpa [E, hwi] using hiW
    · have hnone := hnone_of_not_mem w i hi
      simp only [E, hnone]
      exact Set.mem_univ ω
  have hfixed : ∀ w : Fin J → Option ℕ+, P (K w) ≤ C * weight w := by
    intro w
    by_cases hadm : Admissible w
    · simp only [K]
      rw [dif_pos hadm]
      rcases hadm with ⟨hdisj, hsum_bound⟩
      have hsupport : ∀ i : Fin J, i ∈ S w → ∃ h : ℕ+, w i = some h :=
        fun i hi => (hmem_iff w i).mp hi
      have hbridgew := hbridge w hdisj
      have hprod_le :
          P (I w) ≤ ∏ i ∈ S w, ENNReal.ofReal (Real.exp (-A * r w i)) := by
        rw [hbridgew]
        apply Finset.prod_le_prod'
        intro i hi
        obtain ⟨h, hwi⟩ := hsupport i hi
        simpa [E, r, rN, hwi] using hWP i h
      have hexp_prod :
          (∏ i ∈ S w, ENNReal.ofReal (Real.exp (-A * r w i))) =
            ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i))) := by
        induction S w using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
            rw [Finset.prod_insert hi, ih, ← ENNReal.ofReal_mul (by positivity)]
            simp only [Finset.sum_insert hi]
            congr 1
            rw [← Real.exp_add]
            congr 1
            ring_nf
      have hscaled : A * (theta * (J : ℝ)) ≤ A * (12 * ∑ i ∈ S w, r w i) :=
        mul_le_mul_of_nonneg_left hsum_bound hA.le
      have harg : -A * (∑ i ∈ S w, r w i) / 2 ≤
          -A * theta * (J : ℝ) / 24 := by
        nlinarith [hscaled]
      have hfirst :
          ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i) / 2)) ≤ C := by
        apply ENNReal.ofReal_le_ofReal
        exact Real.exp_le_exp.mpr harg
      have hsplit :
          ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i))) =
            ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i) / 2)) *
              ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i) / 2)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← Real.exp_add]
        ring
      have hweight :
          (∏ i ∈ S w, ENNReal.ofReal (Real.exp (-A * r w i / 2))) = weight w := by
        rw [show S w = Finset.univ.filter (fun i => ∃ h : ℕ+, w i = some h) from rfl,
          Finset.prod_filter]
        apply Finset.prod_congr rfl
        intro i _
        by_cases his : ∃ h : ℕ+, w i = some h
        · obtain ⟨h, hwi⟩ := his
          simp [weight, r, rN, hwi]
        · have hnone : w i = none := by
            cases hwi : w i with
            | none => rfl
            | some h => exact (his ⟨h, hwi⟩).elim
          simp [weight, r, rN, hnone]
      have hhalf_prod :
          (∏ i ∈ S w, ENNReal.ofReal (Real.exp (-A * r w i / 2))) =
            ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i) / 2)) := by
        induction S w using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
            rw [Finset.prod_insert hi, ih, ← ENNReal.ofReal_mul (by positivity)]
            simp only [Finset.sum_insert hi]
            congr 1
            rw [← Real.exp_add]
            congr 1
            ring_nf
      calc
        P (I w) ≤ ∏ i ∈ S w, ENNReal.ofReal (Real.exp (-A * r w i)) := hprod_le
        _ = ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i))) := hexp_prod
        _ = ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i) / 2)) *
            ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i) / 2)) := hsplit
        _ ≤ C * ENNReal.ofReal (Real.exp (-A * (∑ i ∈ S w, r w i) / 2)) :=
          mul_le_mul_right' hfirst _
        _ = C * weight w := by rw [← hhalf_prod, hweight]
    · simp only [K]
      rw [dif_neg hadm]
      simp
  have hterm : (∑' w : Fin J → Option ℕ+, C * weight w) =
      C * ENNReal.ofReal (((1 - Real.exp (-A / 2))⁻¹) ^ J) := by
    rw [ENNReal.tsum_mul_left, aux_lem_branch_weights J A hA]
  have hlast : C * ENNReal.ofReal (((1 - Real.exp (-A / 2))⁻¹) ^ J) =
      ENNReal.ofReal (Real.exp
        (-((A * theta / 24 + Real.log (1 - Real.exp (-(A / 2)))) * (J : ℝ)))) := by
    have hpos : 0 < 1 - Real.exp (-A / 2) := by
      rw [sub_pos]
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    have hinv : (1 - Real.exp (-A / 2))⁻¹ =
        Real.exp (-Real.log (1 - Real.exp (-A / 2))) := by
      rw [Real.exp_neg, Real.exp_log hpos]
    rw [show C = ENNReal.ofReal (Real.exp (-A * theta * (J : ℝ) / 24)) from rfl]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hinv, ← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    P {ω | theta * (J : ℝ) ≤ (Set.ncard {i : Fin J | ω ∈ fail i} : ℝ)} ≤
        P (⋃ w, K w) := measure_mono hcover
    _ ≤ ∑' w, P (K w) := measure_iUnion_le _
    _ ≤ ∑' w, C * weight w := ENNReal.tsum_le_tsum hfixed
    _ = C * ENNReal.ofReal (((1 - Real.exp (-A / 2))⁻¹) ^ J) := hterm
    _ = ENNReal.ofReal (Real.exp
        (-((A * theta / 24 + Real.log (1 - Real.exp (-(A / 2)))) * (J : ℝ)))) := hlast

end Paper
