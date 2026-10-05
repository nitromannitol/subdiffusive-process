module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn.FaceAlignment
public import Homogenization.Geometry.CubeColoring

@[expose] public section

/-!
# The glued cellwise-affine function

This module assembles the per-cell interpolants of `Kuhn/Interpolation.lean`
into one function on a finite **equal-scale** family of triadic simplices, and
proves it continuous.  It is the constructive form of the space
`mathcal V_{R,pi}` of `s.notation` and `p.homogenized.coefficient.strict.decay`: continuous on the closed
simplex, affine on every cell of the mesh.

`gluedKuhnAffine S g` picks, at each point covered by the family, the
interpolant of some cell containing it.  Well-definedness of that choice is
*proved*, not assumed: it is the equal-scale face-alignment lemma
`closedCarrier_inter_subset_commonClosedFace` of `Kuhn/FaceAlignment.lean`.
Continuity on the union follows from local finiteness of a finite family of
closed cells.

* `gluedKuhnAffine_eqOn_closedCarrier` -- on each cell of the family the glued
  function *is* that cell's affine interpolant, so its gradient there is the
  constant `kuhnSlope`;
* `continuousOn_gluedKuhnAffine` -- the glued function is continuous on the
  union of the closed cells.

Scope: the family `S` and the datum `g` are arbitrary; nothing here is specific
to any coefficient field, and no cross-scale (hanging-vertex) mesh is treated.
The equal-scale hypothesis is exactly the hypothesis of the face-alignment
lemma.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

open Homogenization

noncomputable section

variable {d : ℕ}

/-! ## Continuity and disjointness of single cells -/

/-- The interpolant on one cell is continuous: it is an affine function of the
coordinates. -/
theorem continuous_kuhnInterp (T : KuhnCell d) (g : Vec d → ℝ) :
    Continuous (kuhnInterp T g) := by
  show Continuous fun x : Vec d =>
    g (T.vertex 0) + ∑ i, kuhnSlope T g i * (x - T.vertex 0) i
  refine continuous_const.add (continuous_finsetSum _ fun i _ => ?_)
  exact continuous_const.mul ((continuous_apply i).comp (continuous_id.sub continuous_const))

/-- Distinct Kuhn cells of one scale have disjoint open simplices: either they
share their support cube and differ in the coordinate order, or their support
cubes are distinct members of one aligned triadic grid. -/
theorem disjoint_openCarrier_of_supportCube_scale_eq {T U : KuhnCell d}
    (hscale : T.supportCube.scale = U.supportCube.scale) (hTU : T ≠ U) :
    Disjoint T.openCarrier U.openCarrier := by
  by_cases hsupport : T.supportCube = U.supportCube
  · exact (KuhnCell.disjoint_carrier_of_supportCube_eq hTU hsupport).mono
      T.openCarrier_subset_carrier U.openCarrier_subset_carrier
  · exact (disjoint_cubeSet_of_scale_eq_of_ne hscale hsupport).mono
      (T.openCarrier_subset_openCubeSet.trans (openCubeSet_subset_cubeSet _))
      (U.openCarrier_subset_openCubeSet.trans (openCubeSet_subset_cubeSet _))

/-! ## The glued function -/

open Classical in
/-- **The conforming piecewise-affine function of `s.notation` and `p.homogenized.coefficient.strict.decay`**: on
each cell of the mesh `S` it is that cell's affine interpolant of the global
vertex datum `g`, and away from the mesh it is the datum itself.

Well-definedness is *proved*, not assumed: two cells of one scale agree on the
overlap of their closed carriers
(`kuhnInterp_eqOn_closedCarrier_inter`), so the cell selected here is
immaterial.  See `gluedKuhnAffine_eqOn_closedCarrier`,
`gluedKuhnAffine_of_forall_notMem` and `existsUnique_gluedKuhnAffine` for the
characterization that pins the definition. -/
def gluedKuhnAffine (S : Finset (KuhnCell d)) (g : Vec d → ℝ) (x : Vec d) : ℝ :=
  if h : ∃ T ∈ S, x ∈ T.closedCarrier then kuhnInterp h.choose g x else g x

/-- **The first defining equation**: on every closed cell of a single-scale mesh
the glued function is that cell's interpolant. -/
theorem gluedKuhnAffine_eqOn_closedCarrier {S : Finset (KuhnCell d)} {s : ℤ}
    (hscale : ∀ T ∈ S, T.supportCube.scale = s) (g : Vec d → ℝ)
    {T : KuhnCell d} (hT : T ∈ S) :
    Set.EqOn (gluedKuhnAffine S g) (kuhnInterp T g) T.closedCarrier := by
  classical
  intro x hx
  have hex : ∃ U ∈ S, x ∈ U.closedCarrier := ⟨T, hT, hx⟩
  have hspec := hex.choose_spec
  show (if h : ∃ U ∈ S, x ∈ U.closedCarrier then kuhnInterp h.choose g x else g x) =
    kuhnInterp T g x
  rw [dite_eq_left hex]
  exact kuhnInterp_eqOn_closedCarrier_inter hex.choose T g
    ((hscale _ hspec.1).trans (hscale T hT).symm) ⟨hspec.2, hx⟩

/-- Pointwise form of `gluedKuhnAffine_eqOn_closedCarrier`. -/
theorem gluedKuhnAffine_of_mem_closedCarrier {S : Finset (KuhnCell d)} {s : ℤ}
    (hscale : ∀ T ∈ S, T.supportCube.scale = s) (g : Vec d → ℝ)
    {T : KuhnCell d} (hT : T ∈ S) {x : Vec d} (hx : x ∈ T.closedCarrier) :
    gluedKuhnAffine S g x = kuhnInterp T g x :=
  gluedKuhnAffine_eqOn_closedCarrier hscale g hT hx

/-! ## Continuity -/

/-- **"this extension is well-defined and continuous"** (; the M half — the
off-mesh join is the boundary matching;).  The closed cells of a
finite mesh are a locally finite closed cover of their union, and on each of
them the glued function is an affine map. -/
theorem continuousOn_gluedKuhnAffine {S : Finset (KuhnCell d)} {s : ℤ}
    (hscale : ∀ T ∈ S, T.supportCube.scale = s) (g : Vec d → ℝ) :
    ContinuousOn (gluedKuhnAffine S g)
      (⋃ T ∈ (S : Set (KuhnCell d)), T.closedCarrier) := by
  classical
  rw [Set.biUnion_eq_iUnion]
  refine (locallyFinite_of_finite
    (fun T : ↥(S : Set (KuhnCell d)) => (T : KuhnCell d).closedCarrier)).continuousOn_iUnion
    (fun T => isClosed_closedCarrier (T : KuhnCell d)) fun T => ?_
  exact (continuous_kuhnInterp (T : KuhnCell d) g).continuousOn.congr
    (gluedKuhnAffine_eqOn_closedCarrier hscale g T.2)

/-! ## Linearity and affine reproduction at the glued level -/

/-- The cell interpolant is homogeneous in the vertex datum; the additive half
is `kuhnInterp_add` of `Kuhn/Interpolation.lean`. -/
theorem kuhnInterp_smul (T : KuhnCell d) (c : ℝ) (g : Vec d → ℝ) :
    kuhnInterp T (fun x => c * g x) = fun x => c * kuhnInterp T g x := by
  funext x
  have hdot : vecDot (c • kuhnSlope T g) (x - T.vertex 0) =
      c * vecDot (kuhnSlope T g) (x - T.vertex 0) := by
    simp only [vecDot, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [kuhnInterp, kuhnSlope_smul, hdot]
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn
