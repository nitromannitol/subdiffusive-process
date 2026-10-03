

module

public import SubdiffusiveProcess.Section9.CutoffCubeLaws
public import SubdiffusiveProcess.Section9.CutoffCornerSplitting
public import SubdiffusiveProcess.Section9.CutoffInitialMass

@[expose] public section

/-! # Actual cutoff lower-tail recursion -/

open MeasureTheory ProbabilityTheory Homogenization

namespace SubdiffusiveProcess.Section9

open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

/-- Uniform lower-tail probability of the actual centered cutoff masses. -/
noncomputable def cutoffLowerTailSup {d : ℕ} (M : GMCModel d) (u : ℝ) : ℝ :=
  ⨆ m : ℕ, M.P.toMeasure.real {omega |
    cutoffOriginCubeAverage M m omega ≤ Real.exp (-u)}

theorem cutoffLowerTailSup_nonneg {d : ℕ} (M : GMCModel d) (u : ℝ) :
    0 ≤ cutoffLowerTailSup M u := by
  have hbdd : BddAbove (Set.range fun m : ℕ ↦ M.P.toMeasure.real
      {omega | cutoffOriginCubeAverage M m omega ≤ Real.exp (-u)}) :=
    ⟨1, fun y hy ↦ by rcases hy with ⟨m, rfl⟩; exact measureReal_le_one⟩
  apply (measureReal_nonneg : 0 ≤ M.P.toMeasure.real
    {omega | cutoffOriginCubeAverage M 0 omega ≤ Real.exp (-u)}).trans
  exact le_ciSup hbdd 0

theorem cutoffLowerTailSup_le_one {d : ℕ} (M : GMCModel d) (u : ℝ) :
    cutoffLowerTailSup M u ≤ 1 := ciSup_le fun _ ↦ measureReal_le_one

private theorem cutoffCorner_vecNorm_separated {d m : ℕ}
    {x y : Homogenization.Vec d}
    (hx : x ∈ openCubeSet (cutoffLowerCornerCube d m))
    (hy : y ∈ openCubeSet (cutoffUpperCornerCube d m)) :
    Real.sqrt (d : ℝ) * (3 : ℝ) ^ m ≤
      Homogenization.Book.Ch02.vecNorm (x - y) := by
  have heuc := cutoffCornerCubes_euclidean_separated
    (openCubeSet_subset_cubeSet _ hx) (openCubeSet_subset_cubeSet _ hy)
  have hsqEu := euclideanNorm_sq (x - y)
  have hsqVec := Homogenization.Book.Ch02.vecNorm_sq_eq_vecNormSq (x - y)
  have heq : euclideanNorm (x - y) = Homogenization.Book.Ch02.vecNorm (x - y) := by
    nlinarith [euclideanNorm_nonneg (x - y),
      Homogenization.Book.Ch02.vecNorm_nonneg (x - y)]
  rwa [← heq]

private theorem cutoff_split_factor_eq {d : ℕ} (M : GMCModel d) (G : ℝ) :
    ((3 : ℝ) ^ d)⁻¹ * Real.exp (-tauSq M.P - G) =
      Real.exp (-((d : ℝ) * Real.log 3 + tauSq M.P + G)) := by
  rw [show (3 : ℝ) ^ d = Real.exp ((d : ℝ) * Real.log 3) by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]]
  rw [← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

/-- The successor low-mass event lies in the bad-shell event or in the
simultaneous low-mass events of both opposite children. -/
theorem cutoffOriginCubeAverage_succ_lowerTail_subset {d m : ℕ}
    (M : GMCModel d) (u : ℝ) :
    {omega | cutoffOriginCubeAverage M (m + 1) omega ≤ Real.exp (-u)} ⊆
      {omega | u / 4 < (d : ℝ) * Real.log 3 + tauSq M.P +
          translatedShellG2 (m + 1) 0 omega} ∪
        ({omega | cutoffCubeAverage M m (cutoffLowerCornerCube d m) omega ≤
            Real.exp (-(3 * u / 4))} ∩
         {omega | cutoffCubeAverage M m (cutoffUpperCornerCube d m) omega ≤
            Real.exp (-(3 * u / 4))}) := by
  intro omega hmass
  by_cases hbad : u / 4 < (d : ℝ) * Real.log 3 + tauSq M.P +
      translatedShellG2 (m + 1) 0 omega
  · exact Or.inl hbad
  · right
    constructor
    · by_contra hlo
      have hlo' : Real.exp (-(3 * u / 4)) <
          cutoffCubeAverage M m (cutoffLowerCornerCube d m) omega := lt_of_not_ge hlo
      have hhi0 := cutoffOriginCubeAverage_pos M m omega
      have hsplit := cutoffOriginCubeAverage_succ_ge_corner_split M omega (m := m)
      rw [cutoff_split_factor_eq M] at hsplit
      have hfactor : Real.exp (-u / 4) ≤ Real.exp
          (-((d : ℝ) * Real.log 3 + tauSq M.P + translatedShellG2 (m + 1) 0 omega)) :=
        Real.exp_le_exp.mpr (by linarith)
      have hpos : 0 ≤ cutoffCubeAverage M m (cutoffUpperCornerCube d m) omega := by
        unfold cutoffCubeAverage cubeAverage
        exact mul_nonneg (inv_nonneg.mpr (cubeVolume_pos _).le)
          (integral_nonneg fun x ↦ (aCutoff_pos M m omega x).le)
      have : Real.exp (-u) < cutoffOriginCubeAverage M (m + 1) omega := by
        calc
          Real.exp (-u) = Real.exp (-u / 4) * Real.exp (-(3 * u / 4)) := by
            rw [← Real.exp_add]; congr 1; ring
          _ ≤ Real.exp (-((d : ℝ) * Real.log 3 + tauSq M.P +
                translatedShellG2 (m + 1) 0 omega)) * Real.exp (-(3 * u / 4)) :=
            mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
          _ < Real.exp (-((d : ℝ) * Real.log 3 + tauSq M.P +
                translatedShellG2 (m + 1) 0 omega)) *
              (cutoffCubeAverage M m (cutoffLowerCornerCube d m) omega +
                cutoffCubeAverage M m (cutoffUpperCornerCube d m) omega) := by
            exact mul_lt_mul_of_pos_left
              (lt_of_lt_of_le hlo' (le_add_of_nonneg_right hpos)) (Real.exp_pos _)
          _ ≤ cutoffOriginCubeAverage M (m + 1) omega := hsplit
      exact (not_lt_of_ge hmass) this
    · by_contra hhi
      have hhi' : Real.exp (-(3 * u / 4)) <
          cutoffCubeAverage M m (cutoffUpperCornerCube d m) omega := lt_of_not_ge hhi
      have hsplit := cutoffOriginCubeAverage_succ_ge_corner_split M omega (m := m)
      rw [cutoff_split_factor_eq M] at hsplit
      have hfactor : Real.exp (-u / 4) ≤ Real.exp
          (-((d : ℝ) * Real.log 3 + tauSq M.P + translatedShellG2 (m + 1) 0 omega)) :=
        Real.exp_le_exp.mpr (by linarith)
      have hlo0 : 0 ≤ cutoffCubeAverage M m (cutoffLowerCornerCube d m) omega := by
        unfold cutoffCubeAverage cubeAverage
        exact mul_nonneg (inv_nonneg.mpr (cubeVolume_pos _).le)
          (integral_nonneg fun x ↦ (aCutoff_pos M m omega x).le)
      have : Real.exp (-u) < cutoffOriginCubeAverage M (m + 1) omega := by
        calc
          Real.exp (-u) = Real.exp (-u / 4) * Real.exp (-(3 * u / 4)) := by
            rw [← Real.exp_add]; congr 1; ring
          _ ≤ Real.exp (-((d : ℝ) * Real.log 3 + tauSq M.P +
                translatedShellG2 (m + 1) 0 omega)) * Real.exp (-(3 * u / 4)) :=
            mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
          _ < Real.exp (-((d : ℝ) * Real.log 3 + tauSq M.P +
                translatedShellG2 (m + 1) 0 omega)) *
              (cutoffCubeAverage M m (cutoffLowerCornerCube d m) omega +
                cutoffCubeAverage M m (cutoffUpperCornerCube d m) omega) := by
            exact mul_lt_mul_of_pos_left
              (lt_of_lt_of_le hhi' (le_add_of_nonneg_left hlo0)) (Real.exp_pos _)
          _ ≤ cutoffOriginCubeAverage M (m + 1) omega := hsplit
      exact (not_lt_of_ge hmass) this

private theorem cutoffOriginCubeAverage_probability_le_sup {d : ℕ}
    (M : GMCModel d) (m : ℕ) (u : ℝ) :
    M.P.toMeasure.real {omega |
        cutoffOriginCubeAverage M m omega ≤ Real.exp (-u)} ≤ cutoffLowerTailSup M u := by
  unfold cutoffLowerTailSup
  exact le_ciSup (f := fun j : ℕ ↦ M.P.toMeasure.real {omega |
      cutoffOriginCubeAverage M j omega ≤ Real.exp (-u)})
    (⟨1, fun y hy ↦ by rcases hy with ⟨j, rfl⟩; exact measureReal_le_one⟩) m

private theorem cutoffCorner_lowerTail_probability_eq {d m : ℕ}
    (M : GMCModel d) (Q : Homogenization.TriadicCube d)
    (hQ : Q.scale = (m : ℤ)) (u : ℝ) :
    M.P.toMeasure.real {omega | cutoffCubeAverage M m Q omega ≤ Real.exp (-u)} =
      M.P.toMeasure.real {omega | cutoffOriginCubeAverage M m omega ≤ Real.exp (-u)} := by
  have h := (cutoffCubeAverage_identDistrib_originCubeAverage M m Q hQ).measure_preimage_eq
    (measurableSet_Iic : MeasurableSet (Set.Iic (Real.exp (-u))))
  exact congrArg ENNReal.toReal h

/-- One successor mass obeys the forcing-plus-square recursion with the literal
uniform lower-tail function. -/
theorem cutoffOriginCubeAverage_succ_lowerTail_probability_le {d m : ℕ}
    (M : GMCModel d) (C c u : ℝ)
    (hforcing : M.P.toMeasure.real {omega |
        u / 4 < (d : ℝ) * Real.log 3 + tauSq M.P +
          translatedShellG2 (m + 1) 0 omega} ≤
      C * Real.exp (-c * max (u - C) 0 ^ 2 / M.delta ^ 2)) :
    M.P.toMeasure.real {omega |
        cutoffOriginCubeAverage M (m + 1) omega ≤ Real.exp (-u)} ≤
      C * Real.exp (-c * max (u - C) 0 ^ 2 / M.delta ^ 2) +
        cutoffLowerTailSup M (3 * u / 4) ^ 2 := by
  let Qlo := cutoffLowerCornerCube d m
  let Qhi := cutoffUpperCornerCube d m
  let s : Set ℝ := Set.Iic (Real.exp (-(3 * u / 4)))
  have hindep := indepFun_cutoffCubeAverage_of_separation M m Qlo Qhi
    (by intro x y hx hy; exact cutoffCorner_vecNorm_separated hx hy)
  have hinterENN := hindep.measure_inter_preimage_eq_mul s s measurableSet_Iic measurableSet_Iic
  have hinter : M.P.toMeasure.real
      ({omega | cutoffCubeAverage M m Qlo omega ≤ Real.exp (-(3 * u / 4))} ∩
       {omega | cutoffCubeAverage M m Qhi omega ≤ Real.exp (-(3 * u / 4))}) =
      M.P.toMeasure.real {omega | cutoffCubeAverage M m Qlo omega ≤
          Real.exp (-(3 * u / 4))} *
        M.P.toMeasure.real {omega | cutoffCubeAverage M m Qhi omega ≤
          Real.exp (-(3 * u / 4))} := by
    have := congrArg ENNReal.toReal hinterENN
    change ENNReal.toReal (M.P.toMeasure
        (cutoffCubeAverage M m Qlo ⁻¹' s ∩ cutoffCubeAverage M m Qhi ⁻¹' s)) =
      ENNReal.toReal (M.P.toMeasure (cutoffCubeAverage M m Qlo ⁻¹' s)) *
        ENNReal.toReal (M.P.toMeasure (cutoffCubeAverage M m Qhi ⁻¹' s))
    simpa only [ENNReal.toReal_mul] using this
  have hloLaw := cutoffCorner_lowerTail_probability_eq M Qlo (by rfl) (3 * u / 4)
  have hhiLaw := cutoffCorner_lowerTail_probability_eq M Qhi (by rfl) (3 * u / 4)
  have htail := cutoffOriginCubeAverage_probability_le_sup M m (3 * u / 4)
  calc
    M.P.toMeasure.real {omega |
        cutoffOriginCubeAverage M (m + 1) omega ≤ Real.exp (-u)} ≤
      M.P.toMeasure.real
          ({omega | u / 4 < (d : ℝ) * Real.log 3 + tauSq M.P +
              translatedShellG2 (m + 1) 0 omega} ∪
           ({omega | cutoffCubeAverage M m Qlo omega ≤ Real.exp (-(3 * u / 4))} ∩
            {omega | cutoffCubeAverage M m Qhi omega ≤ Real.exp (-(3 * u / 4))})) :=
      measureReal_mono (cutoffOriginCubeAverage_succ_lowerTail_subset M u)
        (measure_ne_top _ _)
    _ ≤ M.P.toMeasure.real {omega | u / 4 < (d : ℝ) * Real.log 3 + tauSq M.P +
          translatedShellG2 (m + 1) 0 omega} +
        M.P.toMeasure.real
          ({omega | cutoffCubeAverage M m Qlo omega ≤ Real.exp (-(3 * u / 4))} ∩
           {omega | cutoffCubeAverage M m Qhi omega ≤ Real.exp (-(3 * u / 4))}) :=
      measureReal_union_le _ _
    _ ≤ C * Real.exp (-c * max (u - C) 0 ^ 2 / M.delta ^ 2) +
        cutoffLowerTailSup M (3 * u / 4) ^ 2 := by
      rw [hinter, hloLaw, hhiLaw]
      exact add_le_add hforcing (by
        simpa only [pow_two] using mul_self_le_mul_self measureReal_nonneg htail)

/-- The literal uniform cutoff lower tail satisfies the actual one-scale
probability recursion, with dimensional constants common to all models. -/
theorem exists_cutoffLowerTailSup_recursion (d : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (M : GMCModel d) (u : ℝ), 0 ≤ u →
        cutoffLowerTailSup M u ≤
          C * Real.exp (-c * max (u - C) 0 ^ 2 / M.delta ^ 2) +
            cutoffLowerTailSup M (3 * u / 4) ^ 2 := by
  obtain ⟨C, c, hC, hc, hforcing⟩ := exists_cutoffLowerTail_forcing d
  refine ⟨C, c, hC, hc, ?_⟩
  intro M u hu
  unfold cutoffLowerTailSup
  apply ciSup_le
  intro m
  cases m with
  | zero =>
      have hbase := measureReal_mono
        (cutoffOriginCubeAverage_zero_lowerTail_subset_forcing M u hu)
        (measure_ne_top M.P.toMeasure _)
      exact (hbase.trans (hforcing M 0 u hu)).trans
        (le_add_of_nonneg_right (sq_nonneg _))
  | succ m =>
      exact cutoffOriginCubeAverage_succ_lowerTail_probability_le M C c u
        (hforcing M (m + 1) u hu)

end

end SubdiffusiveProcess.Section9
