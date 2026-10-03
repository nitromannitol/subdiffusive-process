module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundarySplit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.SlopeStabilityEndpoints

@[expose] public section

/-!
# The scalar normalization defect in a boundary cell

The boundary Caccioppoli parent norm has one translation-invariant scalar
which is absent from the printed display.  This module isolates that scalar
before any PDE estimate: the remaining two terms are the solution oscillation
and the mean-zero boundary-datum oscillation.

PROVENANCE: this is the carrier-level analogue of
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryClauseSkeleton.lean`,
section "The mean-control reduction".  Unlike that provider, this lemma is
independent of the probabilistic model and of a particular projected cube.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book
open Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The exact scalar left after comparing the normalizations of `u` and `h`.

The coefficient `2` comes from using Jensen once on the mean of `u-a`.  This
is the only place where the boundary mean defect enters the parent `L²` norm.
-/
theorem normalizedL2On_sub_le_oscillation_add_boundaryOscillation_add_meanDefect
    {W : Set (Vec d)} (hWm : MeasurableSet W)
    (hWpos : 0 < (volume W).toReal) (hWtop : volume W ≠ ⊤)
    {u h : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict W))
    (hh : MemLp h 2 (volume.restrict W)) (a : ℝ) :
    normalizedL2On W (fun x => u x - h x) ≤
      2 * normalizedL2On W (fun x => u x - a) +
        normalizedL2On W (fun x => h x - volumeAverage W h) +
        |volumeAverage W (fun x => u x - h x)| := by
  let b : ℝ := volumeAverage W h
  let f : Vec d → ℝ := fun x => u x - a
  let g : Vec d → ℝ := fun x => -(h x - b)
  let c : Vec d → ℝ := fun _ => a - b
  haveI : IsFiniteMeasure (volume.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr hWtop
  have hf : MemLp f 2 (volume.restrict W) := hu.sub (memLp_const a)
  have hg : MemLp g 2 (volume.restrict W) :=
    (hh.sub (memLp_const b)).neg
  have hc : MemLp c 2 (volume.restrict W) := memLp_const (a - b)
  have hfg := normalizedL2On_add_le hf hg
  have hfgc := normalizedL2On_add_le (hf.add hg) hc
  have hdecomp : (fun x => u x - h x) = fun x => f x + g x + c x := by
    funext x
    dsimp [f, g, c, b]
    ring
  have hgnorm : normalizedL2On W g =
      normalizedL2On W (fun x => h x - b) := by
    dsimp [g]
    exact normalizedL2On_neg W (fun x => h x - b)
  have hcnorm : normalizedL2On W c = |a - b| := by
    dsimp [c]
    exact normalizedL2On_const_of_pos hWpos (a - b)
  have htriangle : normalizedL2On W (fun x => u x - h x) ≤
      normalizedL2On W f + normalizedL2On W (fun x => h x - b) + |a - b| := by
    rw [hdecomp]
    calc
      normalizedL2On W (fun x => f x + g x + c x) ≤
          normalizedL2On W (fun x => f x + g x) + normalizedL2On W c := hfgc
      _ ≤ (normalizedL2On W f + normalizedL2On W g) +
          normalizedL2On W c := add_le_add hfg le_rfl
      _ = normalizedL2On W f + normalizedL2On W (fun x => h x - b) +
          |a - b| := by rw [hgnorm, hcnorm]
  have huInt : IntegrableOn u W := hu.integrable (by norm_num)
  have hhInt : IntegrableOn h W := hh.integrable (by norm_num)
  have hfInt : IntegrableOn f W := hf.integrable (by norm_num)
  have hfSq : IntegrableOn (fun x => f x ^ 2) W := by
    simpa [IntegrableOn] using hf.integrable_sq
  have havgSub : volumeAverage W (fun x => u x - h x) =
      volumeAverage W u - volumeAverage W h := by
    simpa only [Pi.sub_def] using! volumeAverage_sub huInt hhInt
  have havgF : volumeAverage W f = volumeAverage W u - a := by
    dsimp [f]
    rw [show (fun x => u x - a) = u - (fun _ => a) by rfl,
      volumeAverage_sub huInt (integrable_const _),
      volumeAverage_const (ne_of_gt hWpos)]
  have hscalar : a - b =
      volumeAverage W (fun x => u x - h x) - volumeAverage W f := by
    rw [havgSub, havgF]
    dsimp [b]
    ring
  have hJensen : |volumeAverage W f| ≤ normalizedL2On W f :=
    abs_volumeAverage_le_normalizedL2On hWm hWpos hfInt hfSq
  have hmean : |a - b| ≤
      |volumeAverage W (fun x => u x - h x)| + normalizedL2On W f := by
    rw [hscalar]
    exact (abs_sub _ _).trans (add_le_add le_rfl hJensen)
  have hfinal := add_le_add_left hmean
    (normalizedL2On W f + normalizedL2On W (fun x => h x - b))
  dsimp [f, b] at htriangle ⊢
  linarith only [htriangle, hfinal]

/-- The preceding scalar decomposition inserted into the actual projected
Dirichlet parent norm.  The final `cubeLpNorm` is the already-priced
zero-trace difference `v-h₀`; the only new residue is the displayed scalar
mean of `u₀-h₀`. -/
theorem sqrt_normalizedL2SqOnSet_sub_dirichletSolution_le_meanDefect
    (Q : TriadicCube d) {aCoeff : CoeffFamily d} {g : Vec d → Vec d}
    (v : DirichletForcedCubeSolution Q aCoeff g)
    (u₀ h₀ : H1Function (openCubeSet Q)) (hv : v.boundaryData = h₀)
    (a : ℝ) :
    Real.sqrt (normalizedL2SqOnSet (openCubeSet Q)
        (fun y => u₀.toFun y - v.toH1.toFun y)) ≤
      2 * normalizedL2On (openCubeSet Q) (fun y => u₀.toFun y - a) +
        normalizedL2On (openCubeSet Q)
          (fun y => h₀.toFun y - volumeAverage (openCubeSet Q) h₀.toFun) +
        |volumeAverage (openCubeSet Q)
          (fun y => u₀.toFun y - h₀.toFun y)| +
        cubeLpNorm Q (2 : ℝ≥0∞)
          (fun y => v.toH1.toFun y - h₀.toFun y) := by
  have hWpos : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hWtop : volume (openCubeSet Q) ≠ ⊤ := (volume_openCubeSet_lt_top Q).ne
  have hmean :=
    normalizedL2On_sub_le_oscillation_add_boundaryOscillation_add_meanDefect
      (isOpen_openCubeSet Q).measurableSet hWpos hWtop u₀.memL2 h₀.memL2 a
  have hsplit := sqrt_normalizedL2SqOnSet_sub_dirichletSolution_le_split Q v u₀
  rw [hv] at hsplit
  linarith only [hsplit, hmean]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
