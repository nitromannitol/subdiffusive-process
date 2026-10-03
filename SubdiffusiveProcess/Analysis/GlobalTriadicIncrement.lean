module

public import SubdiffusiveProcess.Analysis.TriadicStepGrowth
public import SubdiffusiveProcess.Geometry.TriadicNesting

@[expose] public section

open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess

theorem globalTriadicIncrement_memLp_and_eLpNorm_sq_le_fractionalKernel
    {d : ℕ} (hd : 2 ≤ d) (Q : Homogenization.TriadicCube d)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hroot : (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
      closure (Homogenization.openCubeSet Q))
    (K t : ℝ) (hK : 0 ≤ K) (ht : (d : ℝ) - 1 < t)
    (n : ℕ) (ν : Measure (SpatialCoordinates d)) (hν : IsFiniteMeasure ν)
    (hsupp : ν (closure (Homogenization.openCubeSet Q))ᶜ = 0)
    (hgrowth : ∀ x ∈ closure (Homogenization.openCubeSet Q), ∀ ρ : ℝ,
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
        closure (Homogenization.openCubeSet Q) := by
      apply hroot
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
    convert eLpNorm_nnreal_pow_eq_lintegral (f := Δ) (p := (2 : NNReal)) (by norm_num)
      hmem.aestronglyMeasurable using 1 <;> norm_num
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
              exact mul_le_mul_right hkernel C
  · intro j hj
    exact measurable_const.indicator
      (oddGridCell z r hr (triadicHalf (n + 1)) j).isOpen.measurableSet

end SubdiffusiveProcess
