import SubdiffusiveProcess.Analysis.GlobalTriadicAverageBound
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.Pseudo.Basic

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Section9

private theorem dimH_coordinate_hyperplane {d : ℕ} (i : Fin d) (c : ℝ) :
    dimH {x : Fin d → ℝ | x i = c} = (d - 1 : ℕ) := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ n =>
      let f : (Fin n → ℝ) → (Fin (n + 1) → ℝ) := fun y => i.insertNth c y
      have hf : Isometry f := by
        intro x y
        simp [f, edist_dist, Fin.dist_insertNth_insertNth]
      have himage : f '' (Set.univ : Set (Fin n → ℝ)) = {x | x i = c} := by
        ext x
        constructor
        · rintro ⟨y, -, rfl⟩
          simp [f]
        · intro hx
          refine ⟨i.removeNth x, Set.mem_univ _, ?_⟩
          apply Fin.insertNth_eq_iff.mpr
          exact ⟨hx.symm, rfl⟩
      rw [← himage, hf.dimH_image, Real.dimH_univ_pi_fin]
      rfl

/- The name is deliberately internal: this is the source-ready carrier lemma for
the small-ball paragraph, not a frozen source-facing declaration. -/
theorem cubeGrowth_boundary_noAtoms {d : ℕ} (hd : 2 ≤ d)
    (qc : SpatialCoordinates d) {qs : ℝ} (hr : 0 < qs) (ν : Measure (SpatialCoordinates d))
    (hν : IsFiniteMeasure ν)
    (K t : ℝ) (hK : 0 ≤ K) (ht : (d : ℝ) - 1 < t)
    (hsupp : ν (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))ᶜ = 0)
    (hgrowth : ∀ x ∈ closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))), ∀ r : ℝ,
      0 < r → r ≤ 1 →
        ν (Metric.ball x r) ≤ ENNReal.ofReal (K * r ^ t)) :
    (∀ (i : Fin d) (c : ℝ), ν {x | x i = c} = 0) ∧ MeasureTheory.NoAtoms ν := by
  classical
  letI := hν
  have htpos : 0 < t := by
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith
  have hatom : ∀ x : SpatialCoordinates d, ν {x} = 0 := by
    intro x
    by_cases hx : x ∈ closure ((centeredCube qc qs hr : Set (SpatialCoordinates d)))
    · let r : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
      have hrpos : ∀ n, 0 < r n := by
        intro n
        dsimp [r]
        positivity
      have hrle : ∀ n, r n ≤ 1 := by
        intro n
        dsimp [r]
        have hn : (1 : ℝ) ≤ n + 1 := by norm_num
        exact (div_le_iff₀ (by positivity)).2 (by simpa using hn)
      have hle : ∀ n, ν {x} ≤ ENNReal.ofReal (K * (r n) ^ t) := by
        intro n
        exact (measure_mono (by
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst y
          simp [Metric.mem_ball, hrpos n])) |>.trans
          (hgrowth x hx (r n) (hrpos n) (hrle n))
      have hr_real : Tendsto (fun n : ℕ => r n) atTop (𝓝 0) := by
        simpa [r] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hr_tendsto : Tendsto (fun n : ℕ => ENNReal.ofReal (r n)) atTop (𝓝 0) := by
        simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr_real
      have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (K * (r n) ^ t)) atTop (𝓝 0) := by
        have hcomp := (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
            (c := ENNReal.ofReal K) ENNReal.ofReal_ne_top htpos).comp hr_tendsto
        convert hcomp using 1
        funext n
        simp only [Function.comp_apply]
        rw [ENNReal.ofReal_mul hK,
          ← ENNReal.ofReal_rpow_of_nonneg (hrpos n).le htpos.le]
      have hzero : ν {x} ≤ 0 :=
        ge_of_tendsto' (f := fun n : ℕ => ENNReal.ofReal (K * (r n) ^ t)) hlim hle
      exact le_antisymm hzero (zero_le _)
    · exact measure_mono_null (singleton_subset_iff.mpr hx) hsupp
  have hNoAtoms : MeasureTheory.NoAtoms ν := ⟨hatom⟩
  let dt : ℝ≥0 := ⟨t, htpos.le⟩
  let C : ℝ≥0∞ := ENNReal.ofReal (1 + K * (2 : ℝ) ^ t)
  let m : ℝ≥0∞ → ℝ≥0∞ := fun z => C * z ^ t
  have hC0 : C ≠ 0 := by
    have hnonneg : 0 ≤ K * (2 : ℝ) ^ t :=
      mul_nonneg hK (Real.rpow_nonneg (by norm_num) _)
    simp only [C, ne_eq, ENNReal.ofReal_eq_zero]
    nlinarith
  have hCtop : C ≠ ∞ := by simp [C]
  have hνmk : ν ≤ Measure.mkMetric m := by
    apply Measure.le_mkMetric m ν (1 / 2)
    · norm_num
    · intro s hs
      by_cases hsempty : s.Nonempty
      · rcases hsempty with ⟨z, hz⟩
        by_cases hD : EMetric.diam s = 0
        · have hsub : s ⊆ {z} := by
            intro y hy
            apply Set.mem_singleton_iff.mpr
            apply edist_eq_zero.mp
            have hdist0 : edist y z ≤ 0 := by
              rw [← hD]
              exact EMetric.edist_le_diam_of_mem hy hz
            exact le_antisymm hdist0
              (by exact bot_le)
          rw [measure_mono_null hsub (hatom z)]
          exact bot_le
        · by_cases hxs : ∃ x, x ∈ s ∧ x ∈ closure ((centeredCube qc qs hr : Set (SpatialCoordinates d)))
          · rcases hxs with ⟨x, hxs, hxS⟩
            let D : ℝ≥0∞ := EMetric.diam s
            have hD0 : D ≠ 0 := hD
            have hDtop : D ≠ ∞ := by
              exact ne_of_lt (lt_of_le_of_lt hs (by norm_num))
            have hDreal : 0 < D.toReal := ENNReal.toReal_pos hD0 hDtop
            have hdist : ∀ y ∈ s ∩ closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))),
                dist y x ≤ D.toReal := by
              intro y hy
              have hxy := EMetric.edist_le_diam_of_mem hy.1 hxs
              have hxy' : ENNReal.ofReal (dist y x) ≤ D := by
                simpa [D, edist_dist] using hxy
              simpa using ENNReal.toReal_mono hDtop hxy'
            have hball : s ∩ closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))) ⊆
                Metric.ball x (2 * D.toReal) := by
              intro y hy
              rw [Metric.mem_ball]
              exact (hdist y hy).trans_lt (by nlinarith)
            have hrad : 0 < 2 * D.toReal := by positivity
            have hradle : 2 * D.toReal ≤ 1 := by
              have hDreal_le : D.toReal ≤ (1 / 2 : ℝ) := by
                change D ≤ (1 / 2 : ℝ≥0∞) at hs
                exact ENNReal.toReal_mono (by norm_num) hs |>.trans_eq (by norm_num)
              linarith
            have hsmeasure : ν s ≤ ν (Metric.ball x (2 * D.toReal)) := by
              calc
                ν s ≤ ν ((s ∩ closure ((centeredCube qc qs hr : Set (SpatialCoordinates d)))) ∪
                    (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))ᶜ) := by
                  apply measure_mono
                  intro y hy
                  by_cases hyS : y ∈ closure ((centeredCube qc qs hr : Set (SpatialCoordinates d)))
                  · exact Or.inl ⟨hy, hyS⟩
                  · exact Or.inr hyS
                _ ≤ ν (s ∩ closure ((centeredCube qc qs hr : Set (SpatialCoordinates d)))) +
                    ν (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))ᶜ := measure_union_le _ _
                _ = ν (s ∩ closure ((centeredCube qc qs hr : Set (SpatialCoordinates d)))) := by simp [hsupp]
                _ ≤ ν (Metric.ball x (2 * D.toReal)) := measure_mono hball
            have hg := hgrowth x hxS (2 * D.toReal) hrad hradle
            have hpow : D ^ t = ENNReal.ofReal (D.toReal ^ t) := by
              rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg htpos.le,
                ENNReal.ofReal_toReal hDtop]
            have hbound : ENNReal.ofReal (K * (2 * D.toReal) ^ t) ≤ m D := by
              change ENNReal.ofReal (K * (2 * D.toReal) ^ t) ≤ C * D ^ t
              simp only [hpow, C]
              rw [← ENNReal.ofReal_mul (by positivity)]
              apply ENNReal.ofReal_le_ofReal
              rw [Real.mul_rpow (by norm_num) ENNReal.toReal_nonneg]
              have hp : 0 ≤ D.toReal ^ t := Real.rpow_nonneg (by positivity) t
              calc
                K * ((2 : ℝ) ^ t * D.toReal ^ t) =
                    (K * (2 : ℝ) ^ t) * D.toReal ^ t := by ring
                _ ≤ (1 + K * (2 : ℝ) ^ t) * D.toReal ^ t := by
                  exact mul_le_mul_of_nonneg_right (by linarith) hp
            exact hsmeasure.trans (hg.trans hbound)
          · have hsub : s ⊆ (closure ((centeredCube qc qs hr : Set (SpatialCoordinates d))))ᶜ := by
              intro y hy
              by_contra hyS
              exact hxs ⟨y, hy, not_mem_compl_iff.mp hyS⟩
            rw [measure_mono_null hsub hsupp]
            exact bot_le
      · have hs0 : s = ∅ := not_nonempty_iff_eq_empty.mp hsempty
        subst s
        simp [m]
  have hνac : ν ≪ MeasureTheory.Measure.hausdorffMeasure (dt : ℝ) := by
    apply Measure.absolutelyContinuous_of_le_smul
    have hmk : Measure.mkMetric m ≤ C •
        (Measure.mkMetric (fun z : ℝ≥0∞ => z ^ (dt : ℝ)) : Measure (SpatialCoordinates d)) := by
      apply Measure.mkMetric_mono_smul hCtop hC0
      filter_upwards [] with z
      simp [m, dt]
    have hmk' : Measure.mkMetric m ≤ C •
        (MeasureTheory.Measure.hausdorffMeasure (X := SpatialCoordinates d) (dt : ℝ)) := by
      simpa [Measure.hausdorffMeasure] using hmk
    exact hνmk.trans hmk'
  refine ⟨?_, hNoAtoms⟩
  intro i c
  have hdim : dimH {x : SpatialCoordinates d | x i = c} < (dt : ℝ≥0∞) := by
    rw [dimH_coordinate_hyperplane i c]
    have hcast : (↑(d - 1) : ℝ≥0∞) =
        ((↑(d - 1) : ℝ≥0) : ℝ≥0∞) := by norm_num
    rw [hcast, ENNReal.coe_lt_coe]
    have hd1 : 1 ≤ d := by omega
    exact_mod_cast (show ((d - 1 : ℕ) : ℝ) < t by
      rw [Nat.cast_sub hd1]
      simpa using ht)
  exact measure_zero_of_dimH_lt hνac hdim

theorem cubeTriadicIncrement_memLp_and_eLpNorm_sq_le_fractionalKernel
    {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (K t : ℝ) (hK : 0 ≤ K) (ht : (d : ℝ) - 1 < t)
    (n : ℕ) (ν : Measure (SpatialCoordinates d)) (hν : IsFiniteMeasure ν)
    (hsupp : ν (closure ((centeredCube z r hr : Set (SpatialCoordinates d))))ᶜ = 0)
    (hgrowth : ∀ x ∈ closure ((centeredCube z r hr : Set (SpatialCoordinates d))), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → ν (Metric.ball x ρ) ≤ ENNReal.ofReal (K * ρ ^ t))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f 2 (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)))) :
  let ell : ℝ := r / (2 * (triadicHalf n : ℝ) + 1)
  let Δ : SpatialCoordinates d → ℝ := fun x =>
    ∑ j : OddGridIndex d (triadicHalf (n + 1)),
      (oddGridCell z r hr (triadicHalf (n + 1)) j : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
            (oddGridCell z r hr (triadicHalf (n + 1)) j : Set (SpatialCoordinates d)) f -
          averageOn
            (oddGridCell z r hr (triadicHalf n) (triadicParent n j) :
              Set (SpatialCoordinates d)) f) x
  MemLp Δ 2 ν ∧
    eLpNorm Δ 2 ν ^ (2 : ℕ) ≤
      ENNReal.ofReal
          (((K + ν.real Set.univ) * (ell / 3) ^ t) *
            (((ell / 3) ^ d) * (ell ^ d))⁻¹) *
        (ENNReal.ofReal (Real.sqrt d * ell)) ^ ((d : ℝ) + 1) *
          (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ENNReal.ofReal ((f y - f x) ^ 2) /
                (ENNReal.ofReal
                  (Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2))) ^ ((d : ℝ) + 1)) := by
  classical
  letI := hν
  dsimp only
  let ell : ℝ := r / (2 * (triadicHalf n : ℝ) + 1)
  let B : ℝ := K + ν.real Set.univ
  let S : OddGridIndex d (triadicHalf (n + 1)) → Set (SpatialCoordinates d) := fun j =>
    oddGridCell z r hr (triadicHalf (n + 1)) j
  let a : OddGridIndex d (triadicHalf (n + 1)) → ℝ := fun j =>
    averageOn (S j) f - averageOn
      (oddGridCell z r hr (triadicHalf n) (triadicParent n j) : Set _) f
  let Δ : SpatialCoordinates d → ℝ := fun x =>
    ∑ j : OddGridIndex d (triadicHalf (n + 1)), (S j).indicator (fun _ => a j) x
  change MemLp Δ 2 ν ∧
    eLpNorm Δ 2 ν ^ (2 : ℕ) ≤
      ENNReal.ofReal
          ((B * (ell / 3) ^ t) * (((ell / 3) ^ d) * (ell ^ d))⁻¹) *
        (ENNReal.ofReal (Real.sqrt d * ell)) ^ ((d : ℝ) + 1) *
          (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ENNReal.ofReal ((f y - f x) ^ 2) /
                (ENNReal.ofReal
                  (Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2))) ^ ((d : ℝ) + 1))
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hB : 0 ≤ B := by dsimp [B]; exact add_nonneg hK measureReal_nonneg
  have htpos : 0 < t := by
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith
  have hparset (p : OddGridIndex d (triadicHalf n)) :
      (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _) =
        (oddGridCell z r hr (triadicHalf n) p : Set (SpatialCoordinates d)) := by
    simp [oddGridCell, ell]
  have hchildmass : ∀ j : OddGridIndex d (triadicHalf (n + 1)),
      ν.real (S j) ≤ B * (ell / 3) ^ t := by
    intro j
    have hjball : S j ⊆ Metric.ball
        (oddGridCenter z r (triadicHalf (n + 1)) j) (ell / 3) := by
      intro x hx
      have hx' : dist x (oddGridCenter z r (triadicHalf (n + 1)) j) <
          (r / (2 * (triadicHalf (n + 1) : ℝ) + 1)) / 2 := by
        simpa [S, oddGridCell, centeredCube, Metric.mem_ball] using hx
      rw [Metric.mem_ball]
      rw [triadic_side_succ r n] at hx'
      dsimp [ell]
      norm_num at hx' ⊢
      linarith
    have hjcenter : oddGridCenter z r (triadicHalf (n + 1)) j ∈
        closure ((centeredCube z r hr : Set (SpatialCoordinates d))) := by
      apply subset_closure
      apply oddGridCell_subset z hr (triadicHalf (n + 1)) j
      simpa [oddGridCell, centeredCube] using
        (Metric.mem_ball_self (by positivity) :
          oddGridCenter z r (triadicHalf (n + 1)) j ∈
            Metric.ball (oddGridCenter z r (triadicHalf (n + 1)) j)
              ((r / (2 * (triadicHalf (n + 1) : ℝ) + 1)) / 2))
    by_cases hsmall : ell / 3 ≤ 1
    · calc
        ν.real (S j) ≤ ν.real (Metric.ball
            (oddGridCenter z r (triadicHalf (n + 1)) j) (ell / 3)) := measureReal_mono hjball
        _ ≤ (ENNReal.ofReal (K * (ell / 3) ^ t)).toReal := by
          exact ENNReal.toReal_mono (by simp) (hgrowth _ hjcenter _ (by positivity) hsmall)
        _ = K * (ell / 3) ^ t := by rw [ENNReal.toReal_ofReal]; positivity
        _ ≤ B * (ell / 3) ^ t := by
          have hKB : K ≤ B := by dsimp [B]; linarith [measureReal_nonneg (μ := ν) (s := Set.univ)]
          exact mul_le_mul_of_nonneg_right hKB (Real.rpow_nonneg (by positivity) _)
    · have hlarge : 1 < ell / 3 := lt_of_not_ge hsmall
      have hpow : 1 ≤ (ell / 3) ^ t := Real.one_le_rpow hlarge.le htpos.le
      calc
        ν.real (S j) ≤ ν.real Set.univ := measureReal_mono (subset_univ _)
        _ ≤ B := by dsimp [B]; linarith
        _ = B * 1 := by ring
        _ ≤ B * (ell / 3) ^ t := mul_le_mul_of_nonneg_left hpow hB
  have hmemj : ∀ j, MemLp ((S j).indicator (fun _ => a j)) 2 ν := by
    intro j
    apply memLp_indicator_const
    · exact (oddGridCell z r hr (triadicHalf (n + 1)) j).isOpen.measurableSet
    · exact Or.inr (by finiteness)
  have hmem : MemLp Δ 2 ν := by
    simpa [Δ] using
      (memLp_finset_sum (Finset.univ : Finset (OddGridIndex d (triadicHalf (n + 1))))
        (fun j hj => hmemj j))
  refine ⟨hmem, ?_⟩
  have he : eLpNorm Δ 2 ν ^ (2 : ℕ) = ∫⁻ x, ‖Δ x‖ₑ ^ (2 : ℝ) ∂ν := by
    convert eLpNorm_nnreal_pow_eq_lintegral (f := Δ) (p := (2 : NNReal)) (by norm_num) using 1 <;> norm_num
  rw [he]
  have hnorm : ∀ x, ‖Δ x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (Δ x ^ 2) := by
    intro x
    rw [← ofReal_norm_eq_enorm, ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg (Δ x)) 2]
    congr 1
    rw [Real.norm_eq_abs, sq_abs]
  rw [show (fun x => ‖Δ x‖ₑ ^ (2 : ℝ)) = (fun x => ENNReal.ofReal (Δ x ^ 2)) by funext x; exact hnorm x]
  have hpoint : ∀ x, ENNReal.ofReal (Δ x ^ 2) =
      ∑ j : OddGridIndex d (triadicHalf (n + 1)),
        (S j).indicator (fun _ => ENNReal.ofReal (a j ^ 2)) x := by
    intro x
    by_cases hx : ∃ j, x ∈ S j
    · obtain ⟨j, hj⟩ := hx
      have hΔ : Δ x = a j := by
        change (∑ l : OddGridIndex d (triadicHalf (n + 1)), (S l).indicator (fun _ => a l) x) = a j
        rw [Finset.sum_eq_single j]
        · simp [Set.indicator_of_mem hj]
        · intro l hl hlj
          have hn : x ∉ S l := by
            intro hlx
            exact Set.disjoint_left.1
              (oddGridCell_pairwiseDisjoint z hr (triadicHalf (n + 1)) hlj) hlx hj
          simp [Set.indicator_of_notMem hn]
        · simp
      rw [hΔ, Finset.sum_eq_single j]
      · simp [Set.indicator_of_mem hj]
      · intro l hl hlj
        have hn : x ∉ S l := by
          intro hlx
          exact Set.disjoint_left.1
            (oddGridCell_pairwiseDisjoint z hr (triadicHalf (n + 1)) hlj) hlx hj
        simp [Set.indicator_of_notMem hn]
      · simp
    · have hn : ∀ j, x ∉ S j := fun j hj => hx ⟨j, hj⟩
      simp [Δ, hn]
  rw [show (fun x => ENNReal.ofReal (Δ x ^ 2)) =
      (fun x => ∑ j : OddGridIndex d (triadicHalf (n + 1)),
        (S j).indicator (fun _ => ENNReal.ofReal (a j ^ 2)) x) by funext x; exact hpoint x]
  rw [lintegral_finset_sum (Finset.univ : Finset (OddGridIndex d (triadicHalf (n + 1))))]
  · have hterm : ∀ j, ENNReal.ofReal (a j ^ 2) * ν (S j) =
        ENNReal.ofReal (ν.real (S j) * |a j| ^ 2) := by
      intro j
      calc
        ENNReal.ofReal (a j ^ 2) * ν (S j) = ENNReal.ofReal (a j ^ 2) * ENNReal.ofReal (ν.real (S j)) := by
          rw [measureReal_def, ENNReal.ofReal_toReal]; finiteness
        _ = ENNReal.ofReal (ν.real (S j) * a j ^ 2) := by
          rw [mul_comm, ← ENNReal.ofReal_mul measureReal_nonneg]
        _ = ENNReal.ofReal (ν.real (S j) * |a j| ^ 2) := by rw [sq_abs]
    have hlocal : ∀ p : OddGridIndex d (triadicHalf n),
        ENNReal.ofReal (∑ l : OddGridIndex d 1,
          ν.real (S (triadicChild n p l)) *
            |a (triadicChild n p l)| ^ 2) ≤
          ENNReal.ofReal ((B * (ell / 3) ^ t) *
              (((ell / 3) ^ d) * (ell ^ d))⁻¹) *
            (ENNReal.ofReal (Real.sqrt d * ell)) ^ ((d : ℝ) + 1) *
            (∫⁻ y in (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _),
              ∫⁻ x in (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _),
                ENNReal.ofReal ((f y - f x) ^ 2) /
                  (ENNReal.ofReal (Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2))) ^ ((d : ℝ) + 1)) := by
      intro p
      have hmass : ∀ l : OddGridIndex d 1,
          ν.real (oddGridCell (oddGridCenter z r (triadicHalf n) p) ell hell 1 l : Set _) ≤
            B * (ell / 3) ^ t := by
        intro l
        simpa [S, triadicChild_cell z hr n p l] using
          hchildmass (triadicChild n p l)
      have hflocal : MemLp f 2
          (volume.restrict (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _)) := by
        apply hf.mono_measure
        apply Measure.restrict_mono_set volume
        intro x hx
        exact oddGridCell_subset z hr (triadicHalf n) p (hparset p ▸ hx)
      have hfrac :=
        ofReal_sum_triadic_child_mass_mul_average_sub_average_sq_le_fractional_kernel
          (hd := hd) (z := oddGridCenter z r (triadicHalf n) p) (r := ell)
          (M := B * (ell / 3) ^ t) hell
          (mul_nonneg hB (Real.rpow_nonneg (by positivity) _)) ν f hflocal hmass
      simpa [S, a, ell, triadicChild_cell z hr n p,
        triadicParent_child, hparset p] using hfrac
    let F : SpatialCoordinates d → SpatialCoordinates d → ℝ≥0∞ := fun y x =>
      ENNReal.ofReal ((f y - f x) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2))) ^ ((d : ℝ) + 1)
    have hkernel :
        ∑ p : OddGridIndex d (triadicHalf n),
          (∫⁻ y in (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _),
            ∫⁻ x in (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _), F y x) ≤
          ∫⁻ y in (centeredCube z r hr : Set _),
            ∫⁻ x in (centeredCube z r hr : Set _), F y x := by
      have hdisj : Pairwise (fun p q : OddGridIndex d (triadicHalf n) =>
          Disjoint
            (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set (SpatialCoordinates d))
            (centeredCube (oddGridCenter z r (triadicHalf n) q) ell hell : Set (SpatialCoordinates d))) := by
        intro p q hpq
        simpa [hparset p, hparset q] using
          oddGridCell_pairwiseDisjoint z hr (triadicHalf n) hpq
      have hmeas : ∀ p : OddGridIndex d (triadicHalf n),
          MeasurableSet (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set (SpatialCoordinates d)) := by
        intro p
        exact (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell).isOpen.measurableSet
      have hsubset : (⋃ p : OddGridIndex d (triadicHalf n),
          (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _)) ⊆
            (centeredCube z r hr : Set (SpatialCoordinates d)) := by
        intro x hx
        rcases mem_iUnion.mp hx with ⟨p, hxp⟩
        exact oddGridCell_subset z hr (triadicHalf n) p (hparset p ▸ hxp)
      have houter : ∀ p : OddGridIndex d (triadicHalf n),
          (∫⁻ y in (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _),
            ∫⁻ x in (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _), F y x) ≤
          ∫⁻ y in (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _),
            ∫⁻ x in (centeredCube z r hr : Set _), F y x := by
        intro p
        apply setLIntegral_mono' (hmeas p)
        intro y hy
        exact lintegral_mono_set (fun x hx =>
          oddGridCell_subset z hr (triadicHalf n) p (hparset p ▸ hx))
      calc
        ∑ p : OddGridIndex d (triadicHalf n),
            (∫⁻ y in (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _),
              ∫⁻ x in (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _), F y x) ≤
            ∑ p : OddGridIndex d (triadicHalf n),
              (∫⁻ y in (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _),
                ∫⁻ x in (centeredCube z r hr : Set _), F y x) :=
          Finset.sum_le_sum (fun p hp => houter p)
        _ = ∫⁻ y in ⋃ p : OddGridIndex d (triadicHalf n),
              (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _),
              ∫⁻ x in (centeredCube z r hr : Set _), F y x := by
          symm
          simpa [tsum_fintype] using
            (lintegral_iUnion (fun p => hmeas p) hdisj
              (fun y => ∫⁻ x in (centeredCube z r hr : Set _), F y x))
        _ ≤ ∫⁻ y in (centeredCube z r hr : Set _),
              ∫⁻ x in (centeredCube z r hr : Set _), F y x :=
          lintegral_mono_set hsubset
    let e : OddGridIndex d (triadicHalf (n + 1)) ≃
        OddGridIndex d (triadicHalf n) × OddGridIndex d 1 :=
      { toFun := fun j => (triadicParent n j, triadicChildLabel n j)
        invFun := fun q => triadicChild n q.1 q.2
        left_inv := fun j => triadicChild_parent_label n j
        right_inv := by
          rintro ⟨p, l⟩
          simp only [triadicParent_child, triadicChildLabel_child] }
    have hreindex (g : OddGridIndex d (triadicHalf (n + 1)) → ℝ) :
        (∑ j, g j) = ∑ p : OddGridIndex d (triadicHalf n),
          ∑ l : OddGridIndex d 1, g (triadicChild n p l) := by
      calc
        (∑ j, g j) = ∑ q : OddGridIndex d (triadicHalf n) × OddGridIndex d 1,
            g (triadicChild n q.1 q.2) := by
          apply Fintype.sum_equiv e g
            (fun q => g (triadicChild n q.1 q.2))
          intro j
          exact congrArg g (triadicChild_parent_label n j).symm
        _ = _ := Fintype.sum_prod_type (fun q => g (triadicChild n q.1 q.2))
    calc
      (∑ j : OddGridIndex d (triadicHalf (n + 1)), ∫⁻ x, (S j).indicator (fun _ => ENNReal.ofReal (a j ^ 2)) x ∂ν) =
          ∑ j, ENNReal.ofReal (ν.real (S j) * |a j| ^ 2) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [lintegral_indicator_const]
        · exact hterm j
        · exact (oddGridCell z r hr (triadicHalf (n + 1)) j).isOpen.measurableSet
      _ = ENNReal.ofReal (∑ j : OddGridIndex d (triadicHalf (n + 1)),
          ν.real (S j) * |a j| ^ 2) := by
        symm
        apply ENNReal.ofReal_sum_of_nonneg
        intro j hj
        exact mul_nonneg measureReal_nonneg (sq_nonneg _)
      _ ≤ _ := by
        rw [hreindex]
        have hofs :
            (∑ p : OddGridIndex d (triadicHalf n), ENNReal.ofReal
              (∑ l : OddGridIndex d 1,
                ν.real (S (triadicChild n p l)) *
                  |a (triadicChild n p l)| ^ 2)) =
              ENNReal.ofReal (∑ p : OddGridIndex d (triadicHalf n),
                ∑ l : OddGridIndex d 1,
                  ν.real (S (triadicChild n p l)) *
                    |a (triadicChild n p l)| ^ 2) := by
          symm
          apply ENNReal.ofReal_sum_of_nonneg
          intro p hp
          exact Finset.sum_nonneg (fun l hl =>
            mul_nonneg measureReal_nonneg (sq_nonneg _))
        rw [← hofs]
        · let C : ℝ≥0∞ :=
            ENNReal.ofReal ((B * (ell / 3) ^ t) *
              (((ell / 3) ^ d) * (ell ^ d))⁻¹) *
              (ENNReal.ofReal (Real.sqrt d * ell)) ^ ((d : ℝ) + 1)
          calc
            (∑ p : OddGridIndex d (triadicHalf n),
                ENNReal.ofReal (∑ l : OddGridIndex d 1,
                  ν.real (S (triadicChild n p l)) *
                    |a (triadicChild n p l)| ^ 2)) ≤
                ∑ p : OddGridIndex d (triadicHalf n),
                  C * (∫⁻ y in (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _),
                    ∫⁻ x in (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _), F y x) := by
              exact Finset.sum_le_sum (fun p hp => by
                simpa [C, F] using hlocal p)
            _ = C * ∑ p : OddGridIndex d (triadicHalf n),
                  (∫⁻ y in (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _),
                    ∫⁻ x in (centeredCube (oddGridCenter z r (triadicHalf n) p) ell hell : Set _), F y x) := by
              rw [Finset.mul_sum]
            _ ≤ C * (∫⁻ y in (centeredCube z r hr : Set _),
                  ∫⁻ x in (centeredCube z r hr : Set _), F y x) := by
              exact mul_le_mul_left' hkernel C
  · intro j hj
    exact measurable_const.indicator
      (oddGridCell z r hr (triadicHalf (n + 1)) j).isOpen.measurableSet

theorem cubeTriadicAverages_memLp_and_increment_bound
    {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (K t : ℝ) (hK : 0 ≤ K) (ht : (d : ℝ) - 1 < t)
    (n : ℕ) (ν : Measure (SpatialCoordinates d)) (hν : IsFiniteMeasure ν)
    (hsupp : ν (closure ((centeredCube z r hr : Set (SpatialCoordinates d))))ᶜ = 0)
    (hgrowth : ∀ x ∈ closure ((centeredCube z r hr : Set (SpatialCoordinates d))), ∀ ρ : ℝ,
      0 < ρ → ρ ≤ 1 → ν (Metric.ball x ρ) ≤ ENNReal.ofReal (K * ρ ^ t))
    (f : SpatialCoordinates d → ℝ)
    (hf : MemLp f 2 (volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)))) :
  let E : ℕ → SpatialCoordinates d → ℝ := fun m x =>
    ∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) f) x
  let ell : ℝ := r / (2 * (triadicHalf n : ℝ) + 1)
  let Δ : SpatialCoordinates d → ℝ := fun x => E (n + 1) x - E n x
  (∀ m : ℕ, MemLp (E m) 2 ν) ∧ MemLp Δ 2 ν ∧
    eLpNorm Δ 2 ν ^ (2 : ℕ) ≤
      ENNReal.ofReal
          (((K + ν.real Set.univ) * (ell / 3) ^ t) *
            (((ell / 3) ^ d) * (ell ^ d))⁻¹) *
        (ENNReal.ofReal (Real.sqrt d * ell)) ^ ((d : ℝ) + 1) *
          (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ENNReal.ofReal ((f y - f x) ^ 2) /
                (ENNReal.ofReal
                  (Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2))) ^ ((d : ℝ) + 1)) := by
  letI := hν
  dsimp only
  let E : ℕ → SpatialCoordinates d → ℝ := fun m x =>
    ∑ k : OddGridIndex d (triadicHalf m),
      (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)).indicator
        (fun _ => averageOn
          (oddGridCell z r hr (triadicHalf m) k : Set (SpatialCoordinates d)) f) x
  let ell : ℝ := r / (2 * (triadicHalf n : ℝ) + 1)
  let Δ : SpatialCoordinates d → ℝ := fun x => E (n + 1) x - E n x
  change (∀ m : ℕ, MemLp (E m) 2 ν) ∧ MemLp Δ 2 ν ∧
    eLpNorm Δ 2 ν ^ (2 : ℕ) ≤
      ENNReal.ofReal
          (((K + ν.real Set.univ) * (ell / 3) ^ t) *
            (((ell / 3) ^ d) * (ell ^ d))⁻¹) *
        (ENNReal.ofReal (Real.sqrt d * ell)) ^ ((d : ℝ) + 1) *
          (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
              ENNReal.ofReal ((f y - f x) ^ 2) /
                (ENNReal.ofReal
                  (Real.sqrt (∑ i : Fin d, (y i - x i) ^ 2))) ^ ((d : ℝ) + 1))
  have hE : ∀ m : ℕ, MemLp (E m) 2 ν := by
    intro m
    dsimp [E]
    apply memLp_finset_sum
    intro k hk
    apply memLp_indicator_const
    · exact (oddGridCell z r hr (triadicHalf m) k).isOpen.measurableSet
    · exact Or.inr (by finiteness)
  have hplanes : ∀ (i : Fin d) (c : ℝ), ν {x | x i = c} = 0 :=
    (cubeGrowth_boundary_noAtoms hd z hr ν hν K t hK ht hsupp hgrowth).1
  have haeq : Δ =ᵐ[ν] (fun x =>
      ∑ j : OddGridIndex d (triadicHalf (n + 1)),
        (oddGridCell z r hr (triadicHalf (n + 1)) j : Set (SpatialCoordinates d)).indicator
          (fun _ => averageOn
              (oddGridCell z r hr (triadicHalf (n + 1)) j : Set (SpatialCoordinates d)) f -
            averageOn
              (oddGridCell z r hr (triadicHalf n) (triadicParent n j) :
                Set (SpatialCoordinates d)) f) x) := by
    simpa [E, Δ] using
      (globalTriadicAverages_sub_eq_increment_ae z hr n ν hplanes f)
  have hinc := cubeTriadicIncrement_memLp_and_eLpNorm_sq_le_fractionalKernel
    hd z hr K t hK ht n ν hν hsupp hgrowth f hf
  dsimp only at hinc
  refine ⟨hE, ?_⟩
  constructor
  · exact (MeasureTheory.memLp_congr_ae haeq).mpr hinc.1
  · rw [MeasureTheory.eLpNorm_congr_ae haeq]
    simpa [ell] using hinc.2


end SubdiffusiveProcess.Section9
