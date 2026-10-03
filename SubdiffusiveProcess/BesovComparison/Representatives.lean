module

public import SubdiffusiveProcess.BesovComparison.DefinitionBridge
public import Homogenization.Sobolev.Fractional.CongruenceAE

@[expose] public section

/-! Exact representative invariance for the source quantities. -/
open Homogenization MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab hiding Vec Mat TriadicCube
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.BesovComparison
variable {d : ℕ}

def overlapIntegrableOfMemLp (Q : TriadicCube d) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (u : Vec d → ℝ) (hu : MemLp u p (normalizedCubeMeasure Q)) : ExactOverlapIntegrable Q u where
  root := hu.integrable hp
  overlap := fun _ _ hS => (Gagliardo.memLp_overlap_of_memLp hu hS).integrable hp

theorem memLp_normalized_root (m : ℤ) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hu : MemLp u p (volume.restrict (cube d m))) :
    MemLp u p (normalizedCubeMeasure (originCube d m)) := by
  unfold normalizedCubeMeasure cubeMeasure
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact hu.smul_measure ENNReal.ofReal_ne_top

theorem ae_root_of_ae_normalized (m : ℤ) {u v : Vec d → ℝ}
    (h : u =ᵐ[normalizedCubeMeasure (originCube d m)] v) :
    u =ᵐ[volume.restrict (cube d m)] v := by
  have hn := Gagliardo.ae_normalizedCubeMeasure_iff.mp h
  rwa [cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at hn

theorem ae_overlap_of_ae_normalized {Q : TriadicCube d} {u v : Vec d → ℝ}
    (h : u =ᵐ[normalizedCubeMeasure Q] v) (j : ℕ) (S : TriadicCube d)
    (hS : S ∈ ScalarOverlap.centersAtDepth Q j) :
    u =ᵐ[ScalarOverlap.normalizedCubeMeasure S] v := by
  rw [ScalarOverlap.normalizedCubeMeasure, ScalarOverlap.cubeMeasure]
  exact Measure.ae_smul_measure
    (Gagliardo.ae_overlap_of_ae_cube hS (Gagliardo.ae_normalizedCubeMeasure_iff.mp h)) _

theorem besov_congr_normalized (m : ℤ) (s p : ℝ) (hp : 0 ≤ p)
    (P : ExactOverlapFiniteParameters) (hPs : P.s = s) (hPp : P.p = p) (hPq : P.q = p)
    {u v : Vec d → ℝ} (hu : ExactOverlapIntegrable (originCube d m) u)
    (hv : ExactOverlapIntegrable (originCube d m) v)
    (h : u =ᵐ[normalizedCubeMeasure (originCube d m)] v) :
    besov d m s (ENNReal.ofReal p) (ENNReal.ofReal p) (ENNReal.ofReal p) u =
      besov d m s (ENNReal.ofReal p) (ENNReal.ofReal p) (ENNReal.ofReal p) v := by
  rw [besov_eq_overlap m s p hp P hPs hPp hPq u hu,
    besov_eq_overlap m s p hp P hPs hPp hPq v hv,
    exactOverlapFiniteSeminorm_congr_ae P _ hu hv (ae_overlap_of_ae_normalized h)]

theorem wsp_congr_ae (m : ℤ) (s p : ℝ) {u v : Vec d → ℝ}
    (h : u =ᵐ[volume.restrict (cube d m)] v) : wsp d m s p u = wsp d m s p v := by
  unfold wsp
  congr 2
  apply lintegral_congr_ae
  filter_upwards [h] with x hx
  apply lintegral_congr_ae
  filter_upwards [h] with y hy
  rw [hx, hy]

end SubdiffusiveProcess.BesovComparison
