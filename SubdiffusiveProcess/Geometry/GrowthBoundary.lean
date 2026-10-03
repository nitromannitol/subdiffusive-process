module

public import SubdiffusiveProcess.Geometry.UpstreamCube
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.MetricSpace.Pseudo.Basic


@[expose] public section

/-! # Boundary nullity from a measure growth bound

A finite measure supported on a closed cube and with growth exponent greater
than d - 1 charges no coordinate hyperplane and has no atoms. The proof uses
the Hausdorff-measure comparison behind the source's face-cover estimate.
-/

open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal NNReal Topology
noncomputable section

namespace SubdiffusiveProcess

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
theorem growth_cube_boundary_noAtoms {d : ℕ} (hd : 2 ≤ d)
    (Q : Homogenization.TriadicCube d) (ν : Measure (SpatialCoordinates d))
    (hν : IsFiniteMeasure ν)
    (K t : ℝ) (hK : 0 ≤ K) (ht : (d : ℝ) - 1 < t)
    (hsupp : ν (closure (Homogenization.openCubeSet Q))ᶜ = 0)
    (hgrowth : ∀ x ∈ closure (Homogenization.openCubeSet Q), ∀ r : ℝ,
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
    by_cases hx : x ∈ closure (Homogenization.openCubeSet Q)
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
        simpa using! ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr_real
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
      exact le_antisymm hzero bot_le
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
        by_cases hD : Metric.ediam s = 0
        · have hsub : s ⊆ {z} := by
            intro y hy
            apply Set.mem_singleton_iff.mpr
            apply edist_eq_zero.mp
            have hdist0 : edist y z ≤ 0 := by
              rw [← hD]
              exact Metric.edist_le_ediam_of_mem hy hz
            exact le_antisymm hdist0
              (by exact bot_le)
          rw [measure_mono_null hsub (hatom z)]
          exact bot_le
        · by_cases hxs : ∃ x, x ∈ s ∧ x ∈ closure (Homogenization.openCubeSet Q)
          · rcases hxs with ⟨x, hxs, hxS⟩
            let D : ℝ≥0∞ := Metric.ediam s
            have hD0 : D ≠ 0 := hD
            have hDtop : D ≠ ∞ := by
              exact ne_of_lt (lt_of_le_of_lt hs (by norm_num))
            have hDreal : 0 < D.toReal := ENNReal.toReal_pos hD0 hDtop
            have hdist : ∀ y ∈ s ∩ closure (Homogenization.openCubeSet Q),
                dist y x ≤ D.toReal := by
              intro y hy
              have hxy := Metric.edist_le_ediam_of_mem hy.1 hxs
              have hxy' : ENNReal.ofReal (dist y x) ≤ D := by
                simpa [D, edist_dist] using hxy
              simpa using ENNReal.toReal_mono hDtop hxy'
            have hball : s ∩ closure (Homogenization.openCubeSet Q) ⊆
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
                ν s ≤ ν ((s ∩ closure (Homogenization.openCubeSet Q)) ∪
                    (closure (Homogenization.openCubeSet Q))ᶜ) := by
                  apply measure_mono
                  intro y hy
                  by_cases hyS : y ∈ closure (Homogenization.openCubeSet Q)
                  · exact Or.inl ⟨hy, hyS⟩
                  · exact Or.inr hyS
                _ ≤ ν (s ∩ closure (Homogenization.openCubeSet Q)) +
                    ν (closure (Homogenization.openCubeSet Q))ᶜ := measure_union_le _ _
                _ = ν (s ∩ closure (Homogenization.openCubeSet Q)) := by simp [hsupp]
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
          · have hsub : s ⊆ (closure (Homogenization.openCubeSet Q))ᶜ := by
              intro y hy
              by_contra hyS
              exact hxs ⟨y, hy, notMem_compl_iff.mp hyS⟩
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
      change C * z ^ t ≤ C * z ^ t
      exact le_rfl
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

end SubdiffusiveProcess
