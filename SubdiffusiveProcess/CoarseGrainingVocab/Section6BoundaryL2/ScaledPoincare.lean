module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows
public import Homogenization.Sobolev.MatchedPair.ScaledPoincare
public import Homogenization.Sobolev.W1p.ZeroExtensionGraph




@[expose] public section

/-!
# The two scaled Poincaré legs on a translated triadic cube

Pricing the boundary corrector in `L̲²` needs two Poincaré inequalities with an
**explicit** `3^j` scale, both of which CoarseGraining proves on `axisCube`:

* the **Dirichlet** leg, for an `H¹₀` datum on a measurable window `W` merely
  *inscribed* in `z + □_j` — obtained from
  `Homogenization.scaled_dirichlet_poincare` by extending the datum by zero to
  the inscribing cube, which changes neither `L²` norm
  (`eLpNorm_indicator_eq_eLpNorm_restrict`);
* the **mean-zero** leg, which must be taken on the **full** cube `z + □_j`:
  no diameter-explicit mean-zero Poincaré for a truncated window exists in any
  of the three trees, and `‖·‖_{L²(W)} ≤ ‖·‖_{L²(z+□_j)}` is free.

The only geometric input is `translatedCube_eq_axisCube`: a translate of the
centered paper cube at scale `j` is the axis cube of side `3^j` anchored at its
lower corner.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2

open MeasureTheory
open Homogenization (Vec H1Function H10Function axisCube openCubeSet originCube volumeAverage
  integralAverage unitDirichletPoincareConst unitMeanZeroPoincareConst)
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-! ### The translated paper cube is an axis cube -/

/-- The lower corner of the translate `z + □_j`. -/
def cubeCorner (j : ℤ) (z : Vec d) : Vec d := fun i => z i - (1 / 2 : ℝ) * (3 : ℝ) ^ j

/-- **A translate of the centered paper cube is an axis cube of side `3^j`.** -/
theorem translatedCube_eq_axisCube (d : ℕ) (j : ℤ) (z : Vec d) :
    translatedCube d j z = axisCube (cubeCorner j z) ((3 : ℝ) ^ j) := by
  ext p
  rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
    Homogenization.mem_openCubeSet_originCube_iff]
  simp only [Homogenization.axisCube, Set.mem_pi, Set.mem_univ, Set.mem_Ioo,
    forall_const, cubeCorner, Pi.sub_apply]
  constructor
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    exact ⟨by linarith only [h1], by linarith only [h2]⟩
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    exact ⟨by linarith only [h1], by linarith only [h2]⟩

/-! ### Coordinates of an indicator vector field -/

theorem indicator_apply_coord {W : Set (Vec d)} (F : Vec d → Vec d) (i : Fin d) :
    (fun p => Set.indicator W F p i) = Set.indicator W (fun p => F p i) := by
  funext p
  by_cases hp : p ∈ W
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
  · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
    rfl

/-! ### The Dirichlet leg on an inscribed window -/

/-- **The scaled Dirichlet Poincaré inequality on a window inscribed in a
translated triadic cube.**

An `H¹₀(W)` datum on a measurable `W ⊆ z + □_j` obeys the un-subtracted `L²`
Poincaré inequality at the inscribing cube's scale `3^j`, with a constant
depending on `d` alone. -/
theorem eLpNorm_le_dirichletPoincare_translatedCube [NeZero d] {W : Set (Vec d)} {j : ℤ}
    {z : Vec d} (hWmeas : MeasurableSet W) (hWY : W ⊆ translatedCube d j z)
    (sigma : H10Function W) :
    (eLpNorm sigma.toH1Function.toFun 2 (volume.restrict W)).toReal
      ≤ unitDirichletPoincareConst d * (3 : ℝ) ^ j *
          ∑ i : Fin d,
            (eLpNorm (fun p => sigma.toH1Function.grad p i) 2 (volume.restrict W)).toReal := by
  have hcube : translatedCube d j z = axisCube (cubeCorner j z) ((3 : ℝ) ^ j) :=
    translatedCube_eq_axisCube d j z
  have hLpos : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hsub : W ⊆ axisCube (cubeCorner j z) ((3 : ℝ) ^ j) := by rw [← hcube]; exact hWY
  set sigmaY : H10Function (axisCube (cubeCorner j z) ((3 : ℝ) ^ j)) :=
    sigma.extendByZeroToOpenSuperset hWmeas
      (Homogenization.isOpen_axisCube (cubeCorner j z) ((3 : ℝ) ^ j)) hsub with hsigmaY
  have hpo := Homogenization.scaled_dirichlet_poincare (cubeCorner j z) hLpos sigmaY
  have hval : eLpNorm sigmaY.toH1Function.toFun 2
        (Homogenization.volumeMeasureOn (axisCube (cubeCorner j z) ((3 : ℝ) ^ j)))
      = eLpNorm sigma.toH1Function.toFun 2 (volume.restrict W) := by
    show eLpNorm (Set.indicator W sigma.toH1Function.toFun) 2
        (volume.restrict (axisCube (cubeCorner j z) ((3 : ℝ) ^ j))) = _
    rw [MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hWmeas,
      Measure.restrict_restrict hWmeas, Set.inter_eq_left.mpr hsub]
  have hgrad : ∀ i : Fin d,
      eLpNorm (fun p => sigmaY.toH1Function.grad p i) 2
          (Homogenization.volumeMeasureOn (axisCube (cubeCorner j z) ((3 : ℝ) ^ j)))
        = eLpNorm (fun p => sigma.toH1Function.grad p i) 2 (volume.restrict W) := by
    intro i
    show eLpNorm (fun p => Set.indicator W sigma.toH1Function.grad p i) 2
        (volume.restrict (axisCube (cubeCorner j z) ((3 : ℝ) ^ j))) = _
    rw [indicator_apply_coord, MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hWmeas,
      Measure.restrict_restrict hWmeas, Set.inter_eq_left.mpr hsub]
  rw [hval] at hpo
  rw [show (∑ i : Fin d, (eLpNorm (fun p => sigmaY.toH1Function.grad p i) 2
      (Homogenization.volumeMeasureOn (axisCube (cubeCorner j z) ((3 : ℝ) ^ j)))).toReal)
      = ∑ i : Fin d, (eLpNorm (fun p => sigma.toH1Function.grad p i) 2
          (volume.restrict W)).toReal from
    Finset.sum_congr rfl fun i _ => by rw [hgrad i]] at hpo
  exact hpo

/-! ### The mean-zero leg on the full cube -/

/-- **The scaled mean-zero Poincaré inequality on a translated triadic cube.**

For `f ∈ H¹(z + □_j)`, the `L²` norm of `f - ⨍_{z+□_j} f` is at most
`C(d)·3^j` times the coordinate-sum `L²` norm of `∇f`.  The mean-zero leg is
available only on the **full** cube: no diameter-explicit constant is known for a
truncated window. -/
theorem eLpNorm_sub_average_le_meanZeroPoincare_translatedCube {j : ℤ} {z : Vec d}
    (f : H1Function (translatedCube d j z)) :
    (eLpNorm (fun p => f.toFun p - volumeAverage (translatedCube d j z) f.toFun) 2
        (volume.restrict (translatedCube d j z))).toReal
      ≤ unitMeanZeroPoincareConst d * (3 : ℝ) ^ j *
          ∑ i : Fin d,
            (eLpNorm (fun p => f.grad p i) 2
              (volume.restrict (translatedCube d j z))).toReal := by
  have hcube : translatedCube d j z = axisCube (cubeCorner j z) ((3 : ℝ) ^ j) :=
    translatedCube_eq_axisCube d j z
  have hLpos : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  have hsub : axisCube (cubeCorner j z) ((3 : ℝ) ^ j) ⊆ translatedCube d j z := by
    rw [hcube]
  set fY : H1Function (axisCube (cubeCorner j z) ((3 : ℝ) ^ j)) :=
    f.restrict (Homogenization.isOpen_axisCube (cubeCorner j z) ((3 : ℝ) ^ j)) hsub with hfY
  have hpo := Homogenization.scaled_meanZero_poincare (cubeCorner j z) hLpos fY
  have hfun : fY.subAverage.toFun
      = fun p => f.toFun p
          - integralAverage (axisCube (cubeCorner j z) ((3 : ℝ) ^ j)) f.toFun := by
    funext p
    exact Homogenization.H1Function.subAverage_apply _ p
  rw [hfun] at hpo
  have hpo2 : (eLpNorm (fun p => f.toFun p
          - volumeAverage (axisCube (cubeCorner j z) ((3 : ℝ) ^ j)) f.toFun) 2
        (volume.restrict (axisCube (cubeCorner j z) ((3 : ℝ) ^ j)))).toReal
      ≤ unitMeanZeroPoincareConst d * (3 : ℝ) ^ j *
          ∑ i : Fin d,
            (eLpNorm (fun p => f.grad p i) 2
              (volume.restrict (axisCube (cubeCorner j z) ((3 : ℝ) ^ j)))).toReal := hpo
  rw [← hcube] at hpo2
  exact hpo2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2
