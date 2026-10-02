import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn.CellEnvelope
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn.WeakGradient
import Mathlib.Analysis.Convex.Measure

/-!
# The zero-extended cellwise-affine competitor of a full mesh

`Kuhn/WeakGradient.lean` shows that `zeroExtendedKuhnAffine cells g` has an
ambient weak gradient which is cellwise the constant `kuhnSlope T g`, *provided*
that function is continuous.  This file supplies the two facts that a density
argument needs on top of it, both missing upstream:

* **a continuity criterion.**  The closed cells of a finite mesh form a closed
  set; away from its interior the glued function has to vanish, and if it does,
  the zero extension is continuous on all of `Vec d`
  (`continuous_zeroExtendedKuhnAffine_of_kuhnInterp_eq_zero`).  The two closed
  pieces `meshClosedCarrier S` and `(interior (meshClosedCarrier S))^c` cover the
  space, and the function is continuous on each.
* **a null boundary.**  The interior of a closed Kuhn cell is exactly its open
  simplex (`interior_closedCarrier`), so `closedCarrier \ openCarrier` is the
  frontier of a convex set and therefore Lebesgue null
  (`volume_closedCarrier_diff_openCarrier`).  This is what turns the cellwise
  identification of the weak gradient on `openCarrier`
  (`zeroExtendedKuhnAffineCoordDeriv_eq_of_mem_openCarrier`) into an
  almost-everywhere identification on the mesh.

Both statements are about an arbitrary equal-scale mesh and an arbitrary vertex
datum; nothing here is specific to the strict-decay proposition.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

open Homogenization MeasureTheory Metric Set

noncomputable section

variable {d : ℕ}

/-! ## Interior and frontier of one closed cell -/

/-- Moving one coordinate by less than `eps` stays in the `eps`-ball. -/
private theorem update_mem_ball {x : Vec d} {eps t : ℝ} (heps : 0 < eps)
    (ht : |t| < eps) (k : Fin d) :
    (Function.update x k (x k + t) : Vec d) ∈ Metric.ball x eps := by
  rw [Metric.mem_ball, dist_pi_lt_iff heps]
  intro m
  rw [Real.dist_eq, Function.update_apply]
  by_cases hm : m = k
  · subst hm
    simpa using ht
  · simpa [hm] using heps

/-- **The interior of a closed Kuhn cell is its open simplex.**  At a point of
the interior no defining inequality of `closedCarrier` can be tight: pushing the
offending coordinate leaves the cell while staying in a small ball. -/
theorem interior_closedCarrier_subset_openCarrier (T : KuhnCell d) :
    interior T.closedCarrier ⊆ T.openCarrier := by
  intro x hx
  obtain ⟨eps, heps, hball⟩ :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hxC : x ∈ T.closedCarrier := interior_subset hx
  have hpush : ∀ (t : ℝ), |t| < eps → ∀ k : Fin d,
      (Function.update x k (x k + t) : Vec d) ∈ T.closedCarrier :=
    fun t ht k => hball (update_mem_ball heps ht k)
  have hcoord : ∀ (t : ℝ) (k m : Fin d),
      (Function.update x k (x k + t) : Vec d) m = x m + (if m = k then t else 0) := by
    intro t k m
    rw [Function.update_apply]
    by_cases hm : m = k <;> simp [hm]
  rw [KuhnCell.mem_openCarrier_iff]
  constructor
  · -- the strict box constraints
    intro i
    have hcl : ∀ y ∈ T.closedCarrier,
        |y i - cubeCenter T.supportCube i| ≤ cubeRadius T.supportCube := by
      intro y hy
      have := dist_le_pi_dist y (cubeCenter T.supportCube) i
      have hdist : dist y (cubeCenter T.supportCube) ≤ cubeRadius T.supportCube :=
        Metric.mem_closedBall.mp hy.1
      rw [Real.dist_eq] at this
      linarith
    have hup : x i - cubeCenter T.supportCube i < cubeRadius T.supportCube := by
      by_contra hcon
      push_neg at hcon
      have hmem := hpush (eps / 2) (by rw [abs_of_pos (by linarith)]; linarith) i
      have hval := hcl _ hmem
      rw [hcoord (eps / 2) i i, if_pos rfl] at hval
      have := (abs_le.mp hval).2
      linarith
    have hdown : -(cubeRadius T.supportCube) < x i - cubeCenter T.supportCube i := by
      by_contra hcon
      push_neg at hcon
      have hmem := hpush (-(eps / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith) i
      have hval := hcl _ hmem
      rw [hcoord (-(eps / 2)) i i, if_pos rfl] at hval
      have := (abs_le.mp hval).1
      linarith
    simp only [cubeCenter, cubeRadius] at hup hdown
    constructor <;> nlinarith
  · -- the strict order constraints
    intro i j hij
    have hweak := hxC.2 i j (le_of_lt hij)
    rcases lt_or_eq_of_le hweak with h | h
    · exact h
    · exfalso
      have hne : T.order i ≠ T.order j := by
        intro heq
        have : i = j := T.order.injective heq
        omega
      have hmem := hpush (-(eps / 2))
        (by rw [abs_neg, abs_of_pos (by linarith)]; linarith) (T.order j)
      have hord := hmem.2 i j (le_of_lt hij)
      simp only [triadicLocalCoordinate] at hord h ⊢
      rw [hcoord (-(eps / 2)) (T.order j) (T.order i),
        hcoord (-(eps / 2)) (T.order j) (T.order j), if_neg hne, if_pos rfl] at hord
      linarith

theorem openCarrier_subset_interior_closedCarrier (T : KuhnCell d) :
    T.openCarrier ⊆ interior T.closedCarrier :=
  interior_maximal T.openCarrier_subset_closedCarrier (isOpen_openCarrier T)

/-- The interior of a closed Kuhn cell is the source's open simplex. -/
theorem interior_closedCarrier (T : KuhnCell d) :
    interior T.closedCarrier = T.openCarrier :=
  Set.Subset.antisymm (interior_closedCarrier_subset_openCarrier T)
    (openCarrier_subset_interior_closedCarrier T)

/-- The closed cell minus the open simplex is the frontier of a convex body. -/
theorem closedCarrier_diff_openCarrier_eq_frontier (T : KuhnCell d) :
    T.closedCarrier \ T.openCarrier = frontier T.closedCarrier := by
  rw [frontier, (isClosed_closedCarrier T).closure_eq, interior_closedCarrier T]

/-- **The boundary of a Kuhn cell is Lebesgue null.**  This is what upgrades the
cellwise identification of the weak gradient on the open simplex to an
almost-everywhere identification on the closed cell. -/
theorem volume_closedCarrier_diff_openCarrier (T : KuhnCell d) :
    volume (T.closedCarrier \ T.openCarrier) = 0 := by
  rw [closedCarrier_diff_openCarrier_eq_frontier T]
  exact Convex.addHaar_frontier volume (convex_closedCarrier T)

/-! ## The closed hull of a mesh -/

/-- The union of the closed cells of a finite mesh. -/
def meshClosedCarrier (S : Finset (KuhnCell d)) : Set (Vec d) :=
  ⋃ T ∈ (S : Set (KuhnCell d)), T.closedCarrier

theorem mem_meshClosedCarrier_iff {S : Finset (KuhnCell d)} {x : Vec d} :
    x ∈ meshClosedCarrier S ↔ ∃ T ∈ S, x ∈ T.closedCarrier := by
  simp [meshClosedCarrier]

theorem isClosed_meshClosedCarrier (S : Finset (KuhnCell d)) :
    IsClosed (meshClosedCarrier S) :=
  S.finite_toSet.isClosed_biUnion fun T _ => isClosed_closedCarrier T

/-! ## Vanishing vertex data -/

/-- An interpolant with vanishing vertex data is identically zero. -/
theorem kuhnInterp_eq_zero_of_vertex_eq_zero (T : KuhnCell d) {g : Vec d → ℝ}
    (h : ∀ k : Fin (d + 1), g (T.vertex k) = 0) : kuhnInterp T g = 0 := by
  funext x
  rw [kuhnInterp_apply, kuhnSlope_eq_zero_of_vertex_const T h, h 0]
  simp [vecDot]

/-- Off the closed cells of the mesh the zero extension vanishes. -/
theorem zeroExtendedKuhnAffine_eq_zero_of_notMem_meshClosedCarrier
    (S : Finset (KuhnCell d)) (g : Vec d → ℝ) {x : Vec d}
    (hx : x ∉ meshClosedCarrier S) : zeroExtendedKuhnAffine S g x = 0 :=
  zeroExtendedKuhnAffine_of_forall_notMem S g fun T hT hxT =>
    hx (mem_meshClosedCarrier_iff.mpr ⟨T, hT, hxT⟩)

/-! ## The continuity criterion -/

/-- **Continuity of the zero extension.**  If on every closed cell the
interpolant already vanishes at the points outside the interior of the mesh
hull, then the zero extension is continuous on all of `Vec d`.

The two closed sets `meshClosedCarrier S` and `(interior (meshClosedCarrier S))^c`
cover the space; the function is the glued interpolant on the first, and
identically zero on the second. -/
theorem continuous_zeroExtendedKuhnAffine_of_kuhnInterp_eq_zero
    {S : Finset (KuhnCell d)} {s : ℤ} (hscale : ∀ T ∈ S, T.supportCube.scale = s)
    (g : Vec d → ℝ)
    (hzero : ∀ T ∈ S, ∀ x ∈ T.closedCarrier,
      x ∉ interior (meshClosedCarrier S) → kuhnInterp T g x = 0) :
    Continuous (zeroExtendedKuhnAffine S g) := by
  classical
  set F : Vec d → ℝ := zeroExtendedKuhnAffine S g with hF
  set C : Set (Vec d) := meshClosedCarrier S with hC
  have hFmesh : ∀ x ∈ C, F x = gluedKuhnAffine S g x := by
    intro x hx
    obtain ⟨T, hT, hxT⟩ := mem_meshClosedCarrier_iff.mp hx
    rw [hF, zeroExtendedKuhnAffine_of_mem_closedCarrier hscale g hT hxT,
      gluedKuhnAffine_of_mem_closedCarrier hscale g hT hxT]
  have hFout : ∀ x ∈ (interior C)ᶜ, F x = 0 := by
    intro x hx
    by_cases hxC : x ∈ C
    · obtain ⟨T, hT, hxT⟩ := mem_meshClosedCarrier_iff.mp hxC
      rw [hF, zeroExtendedKuhnAffine_of_mem_closedCarrier hscale g hT hxT]
      have := hzero T hT x hxT hx
      rw [this]
    · exact zeroExtendedKuhnAffine_eq_zero_of_notMem_meshClosedCarrier S g hxC
  have hcontC : ContinuousOn F C := by
    refine (continuousOn_gluedKuhnAffine hscale g).congr ?_
    intro x hx
    exact hFmesh x hx
  have hcontOut : ContinuousOn F (interior C)ᶜ :=
    continuousOn_const.congr fun x hx => hFout x hx
  have hcover : (⋃ b : Bool, cond b C ((interior C)ᶜ)) = (Set.univ : Set (Vec d)) := by
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ interior C
    · exact Set.mem_iUnion.mpr ⟨true, interior_subset hx⟩
    · exact Set.mem_iUnion.mpr ⟨false, hx⟩
  have hfin := (locallyFinite_of_finite
    (fun b : Bool => cond b C ((interior C)ᶜ))).continuousOn_iUnion
      (fun b => by cases b with
        | false => exact isOpen_interior.isClosed_compl
        | true => exact isClosed_meshClosedCarrier S)
      (fun b => by cases b with
        | false => exact hcontOut
        | true => exact hcontC)
  rw [hcover] at hfin
  exact continuousOn_univ.mp hfin

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn
