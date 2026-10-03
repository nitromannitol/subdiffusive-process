module

public import SubdiffusiveProcess.Besov.CenteredTruncation
public import SubdiffusiveProcess.Besov.BoundedPairing

@[expose] public section

open MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec TriadicCube
open scoped BigOperators ENNReal Topology
noncomputable section
namespace SubdiffusiveProcess.Besov

/-- A pointwise factor bound passes to all finite spatial exponents. -/
theorem averageLr_le_two_mul {ι : Type*} (S : Set ι) (hS : S.Finite)
    (r : ℝ≥0∞) (hr : 1 ≤ r) (a b : ι → ℝ≥0∞) (hab : ∀ z ∈ S, a z ≤ 2 * b z) :
    averageLr S r a ≤ 2 * averageLr S r b := by
  rw [averageLr_eq_finiteAggregation _ hS, averageLr_eq_finiteAggregation _ hS]
  exact (finiteAggregation_mono _ _ r hr (fun z hz => hab z (hS.mem_toFinset.mp hz))).trans_eq
    (finiteAggregation_const_mul _ _ r hr 2 (by norm_num) (by norm_num) _)

/-- The full three-index positive norm of the centered truncation costs at most two. -/
theorem centeredTruncation_besovNorm_le {d : ℕ} (m : ℤ) (N : ℕ) (s : ℝ)
    (q r : ℝ≥0∞) (hq : 1 ≤ q) (hr : 1 ≤ r) (g : Vec d → ℝ)
    (hg : IntegrableOn g (cubeSet (originCube d m))) :
    besovNorm d m s 1 q r (centeredTruncation (originCube d m) N g) ≤
      2 * besovNorm d m s 1 q r g := by
  have hgOpen : IntegrableOn g (cube d m) :=
    integrableOn_cubeSet_originCube_iff_integrableOn_openCubeSet_originCube.mp hg
  have hsemi : besovSeminorm d m s 1 q r (centeredTruncation (originCube d m) N g) ≤
      2 * besovSeminorm d m s 1 q r g := by
    unfold besovSeminorm
    refine (scaleAggregation_mono s m q ?_).trans_eq (scaleAggregation_const_mul s m q hq 2 _)
    intro k hk
    have hav := averageLr_le_two_mul (positiveCentres d m k) (positiveCentres_finite hk) r hr
      (fun z => normalizedLp (translatedCube d k z) 1
        (fun x => centeredTruncation (originCube d m) N g x -
          ⨍ y in translatedCube d k z, centeredTruncation (originCube d m) N g y))
      (fun z => normalizedLp (translatedCube d k z) 1
        (fun x => g x - ⨍ y in translatedCube d k z, g y))
      (fun z hz => centeredTruncation_local_oscillation_le _ N g k z (hgOpen.mono_set hz.2.2))
    exact (mul_le_mul_right hav _).trans_eq (by ac_rfl)
  rw [besovNorm_eq_seminorm_add_root, besovNorm_eq_seminorm_add_root]
  have hroot : rootEntry m s (centeredTruncation (originCube d m) N g) = rootEntry m s g := by
    unfold rootEntry
    rw [centeredTruncation_mean _ N g hg]
  rw [hroot, mul_add]
  exact add_le_add hsemi (le_mul_of_one_le_left' (by norm_num : (1 : ℝ≥0∞) ≤ 2))

end SubdiffusiveProcess.Besov
