module

public import SubdiffusiveProcess.Lane2.FoldedCoefficient
public import SubdiffusiveProcess.Lane2.MeshGeometry

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology Distributions ContDiff

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ}

/-- **Assembly step 1 for `CellDirichletBoundaryContinuity`.**  The packaging: an
interior continuous representative together with the boundary limit gives the
representative continuous on the CLOSED cube with boundary value `φ`.  This
reduces the whole structure to the single boundary-limit hypothesis `hlimit`,
which is what the reflection chain produces. -/
theorem exists_boundaryContinuous_of_interior_and_boundaryLimit
    (c : SpatialCoordinates d) {h : ℝ} (hh : 0 < h)
    (u : H1Function (centeredCube c h hh : Set (SpatialCoordinates d)))
    (φfun : SpatialCoordinates d → ℝ) (hφcont : Continuous φfun)
    (rep : SpatialCoordinates d → ℝ)
    (hrepcont : ContinuousOn rep (centeredCube c h hh : Set (SpatialCoordinates d)))
    (hrepae : rep =ᵐ[volume.restrict
      (centeredCube c h hh : Set (SpatialCoordinates d))] u.toFun)
    (hlimit : ∀ x₀ ∈ frontier (centeredCube c h hh : Set (SpatialCoordinates d)),
      Tendsto rep
        (nhdsWithin x₀ (centeredCube c h hh : Set (SpatialCoordinates d)))
        (nhds (φfun x₀))) :
    ∃ v : SpatialCoordinates d → ℝ,
      ContinuousOn v (closure (centeredCube c h hh : Set (SpatialCoordinates d))) ∧
      v =ᵐ[volume.restrict
        (centeredCube c h hh : Set (SpatialCoordinates d))] u.toFun ∧
      ∀ x ∈ frontier (centeredCube c h hh : Set (SpatialCoordinates d)),
        v x = φfun x := by
  classical
  set U : Set (SpatialCoordinates d) := (centeredCube c h hh : Set (SpatialCoordinates d))
    with hU
  have hUopen : IsOpen U := (centeredCube c h hh).isOpen
  have hnot : ∀ y ∈ frontier U, y ∉ U := by
    intro y hy
    have : y ∈ closure U \ U := by rwa [hUopen.frontier_eq] at hy
    exact this.2
  refine ⟨fun x => if x ∈ U then rep x else φfun x, ?_, ?_, ?_⟩
  · rw [closure_eq_self_union_frontier U]
    intro x hx
    rcases hx with hxU | hxF
    · have hmem : U ∈ nhds x := hUopen.mem_nhds hxU
      have hrepAt : ContinuousAt rep x := hrepcont.continuousAt hmem
      have heq : rep =ᶠ[nhds x] fun y => if y ∈ U then rep y else φfun y := by
        filter_upwards [hmem] with y hy
        rw [if_pos hy]
      exact (hrepAt.congr heq).continuousWithinAt
    · have hval : (if x ∈ U then rep x else φfun x) = φfun x := if_neg (hnot x hxF)
      rw [continuousWithinAt_union]
      constructor
      · show Tendsto (fun y => if y ∈ U then rep y else φfun y) (nhdsWithin x U)
          (nhds (if x ∈ U then rep x else φfun x))
        rw [hval]
        refine (hlimit x hxF).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        rw [if_pos hy]
      · show Tendsto (fun y => if y ∈ U then rep y else φfun y)
          (nhdsWithin x (frontier U))
          (nhds (if x ∈ U then rep x else φfun x))
        rw [hval]
        refine ((hφcont.tendsto x).mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        rw [if_neg (hnot y hy)]
  · filter_upwards [hrepae, ae_restrict_mem hUopen.measurableSet] with x hxrep hxU
    rw [if_pos hxU]
    exact hxrep
  · intro x hxF
    exact if_neg (hnot x hxF)

/-- **Assembly step 2 for `CellDirichletBoundaryContinuity`.**  The boundary limit
from a LOCAL continuous vanishing representative of `rep - φ`.  This is the shape
the reflection chain delivers: near a boundary point `x₀` the odd extension has a
continuous representative (GMC's small-contrast Schauder estimate), that
representative vanishes at `x₀` (`lane2_eq_zero_on_activeFaces`), and on the cell
side it is `u - φ`. -/
theorem tendsto_boundary_of_local_continuous_vanishing
    {U S : Set (SpatialCoordinates d)} (hS : IsOpen S)
    {x₀ : SpatialCoordinates d} (hx₀ : x₀ ∈ S)
    {rep φfun g : SpatialCoordinates d → ℝ}
    (hg : ContinuousOn g S) (hgx : g x₀ = 0)
    (hagree : ∀ y ∈ S ∩ U, g y = rep y - φfun y)
    (hφ : ContinuousAt φfun x₀) :
    Tendsto rep (nhdsWithin x₀ U) (nhds (φfun x₀)) := by
  have hSnhds : S ∈ nhds x₀ := hS.mem_nhds hx₀
  have hrestrict : nhdsWithin x₀ U = nhdsWithin x₀ (U ∩ S) :=
    nhdsWithin_restrict' U hSnhds
  rw [hrestrict]
  have hgS : Tendsto g (nhdsWithin x₀ S) (nhds 0) := by
    have := (hg.continuousWithinAt hx₀)
    rwa [ContinuousWithinAt, hgx] at this
  have hsub : nhdsWithin x₀ (U ∩ S) ≤ nhdsWithin x₀ S :=
    nhdsWithin_mono _ Set.inter_subset_right
  have hgUS : Tendsto g (nhdsWithin x₀ (U ∩ S)) (nhds 0) := hgS.mono_left hsub
  have hdiff : Tendsto (fun y => rep y - φfun y) (nhdsWithin x₀ (U ∩ S)) (nhds 0) := by
    refine hgUS.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hagree y ⟨hy.2, hy.1⟩
  have hφlim : Tendsto φfun (nhdsWithin x₀ (U ∩ S)) (nhds (φfun x₀)) :=
    hφ.tendsto.mono_left nhdsWithin_le_nhds
  have hsum := hdiff.add hφlim
  simp only [zero_add] at hsum
  refine hsum.congr ?_
  intro y
  ring



structure CellDirichletBoundaryContinuity (d : ℕ) : Prop where
  continuous_up_to_boundary :
    ∀ (c : SpatialCoordinates d) (h : ℝ) (hh : 0 < h)
      (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ), 0 < lam → Continuous a →
      (∀ x ∈ (centeredCube c h hh : Set (SpatialCoordinates d)),
        lam ≤ a x ∧ a x ≤ Lam) →
      ∀ (φ u : H1Function (centeredCube c h hh : Set (SpatialCoordinates d))),
        ContDiff ℝ ∞ φ.toFun →
        IsWeaklyHarmonicOn a (centeredCube c h hh : Set (SpatialCoordinates d)) u →
        HasZeroTraceDifferenceOn
          (centeredCube c h hh : Set (SpatialCoordinates d)) u φ →
        ∃ v : SpatialCoordinates d → ℝ,
          ContinuousOn v
            (closure (centeredCube c h hh : Set (SpatialCoordinates d))) ∧
          v =ᵐ[volume.restrict
            (centeredCube c h hh : Set (SpatialCoordinates d))] u.toFun ∧
          ∀ x ∈ frontier (centeredCube c h hh : Set (SpatialCoordinates d)),
            v x = φ.toFun x

/-- The local boundary representative that the reflection chain produces: an
interior continuous representative of `u`, together with, at each boundary point,
a continuous function vanishing there and equal to `u - φ` on the cell side of a
neighbourhood. -/
def HasLocalBoundaryRepresentative (d : ℕ) : Prop :=
  ∀ (c : SpatialCoordinates d) (h : ℝ) (hh : 0 < h)
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ), 0 < lam → Continuous a →
    (∀ x ∈ (centeredCube c h hh : Set (SpatialCoordinates d)),
      lam ≤ a x ∧ a x ≤ Lam) →
    ∀ (φ u : H1Function (centeredCube c h hh : Set (SpatialCoordinates d))),
      ContDiff ℝ ∞ φ.toFun →
      IsWeaklyHarmonicOn a (centeredCube c h hh : Set (SpatialCoordinates d)) u →
      HasZeroTraceDifferenceOn
        (centeredCube c h hh : Set (SpatialCoordinates d)) u φ →
      ∃ rep : SpatialCoordinates d → ℝ,
        ContinuousOn rep (centeredCube c h hh : Set (SpatialCoordinates d)) ∧
        rep =ᵐ[volume.restrict
          (centeredCube c h hh : Set (SpatialCoordinates d))] u.toFun ∧
        ∀ x₀ ∈ frontier (centeredCube c h hh : Set (SpatialCoordinates d)),
          ∃ S : Set (SpatialCoordinates d), IsOpen S ∧ x₀ ∈ S ∧
            ∃ g : SpatialCoordinates d → ℝ, ContinuousOn g S ∧ g x₀ = 0 ∧
              ∀ y ∈ S ∩ (centeredCube c h hh : Set (SpatialCoordinates d)),
                g y = rep y - φ.toFun y

/-- **Assembly steps 1 and 2 combined.**  `CellDirichletBoundaryContinuity`
follows from the local boundary representative, so the whole deferred input is
reduced to what the reflection chain produces at a single boundary point. -/
theorem cellDirichletBoundaryContinuity_of_localRepresentative
    (hloc : HasLocalBoundaryRepresentative d) :
    CellDirichletBoundaryContinuity d := by
  refine ⟨fun c h hh a lam Lam hlam ha habounds φ u hφ hharm htrace => ?_⟩
  obtain ⟨rep, hrepcont, hrepae, hbdry⟩ :=
    hloc c h hh a lam Lam hlam ha habounds φ u hφ hharm htrace
  refine exists_boundaryContinuous_of_interior_and_boundaryLimit c hh u φ.toFun
    (hφ.continuous) rep hrepcont hrepae ?_
  intro x₀ hx₀
  obtain ⟨S, hSopen, hx₀S, g, hgcont, hgx, hagree⟩ := hbdry x₀ hx₀
  exact tendsto_boundary_of_local_continuous_vanishing hSopen hx₀S hgcont hgx hagree
    (hφ.continuous.continuousAt)

end SubdiffusiveProcess
