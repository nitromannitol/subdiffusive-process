module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn.Gluing

@[expose] public section

/-!
# The cellwise-supremum envelope of a continuous coefficient

Step 2 of the strict-decay proposition (`s.notation` and `p.homogenized.coefficient.strict.decay`) replaces
the coefficient `B_0` by its *cellwise upper approximation* on the mesh
`mathcal T_{R,pi}`: the discrete energy of `s.notation` and `p.homogenized.coefficient.strict.decay` weights each cell `T` by
`sup_{closure T} B_0`, and the proof at `s.notation` and `p.homogenized.coefficient.strict.decay` uses

> since `B_0` is almost surely continuous, its cellwise upper approximations
> converge uniformly to `B_0`.

This file supplies that statement for an
arbitrary continuous field on an arbitrary equal-scale family of Kuhn cells.

* `cellSup B T` is `sup_{closure T} B`, and is *attained* (`exists_mem_cellSup_eq`)
  because a closed Kuhn cell is compact and nonempty;
* `kuhnEnvelope S B` is the paper's literal `B_0^{(R)} = sum_T 1_T sup_{closure T} B_0`,
  written with the half-open carriers that tile exactly;
* `abs_kuhnEnvelope_sub_le_of_scale_le` is the uniform convergence: for a
  continuous `B` and a compact `K`, every equal-scale family of cells of small
  enough scale that lies in `K` has `|B^{(R)} - B| <= eps` at every point it
  covers.  The input is uniform continuity of `B` on `K` together with the mesh
  diameter of a Kuhn cell, which is the cube side `3^{scale}`.
* `abs_kuhnEnvelope_sub_le_cubeSet` is the corollary for the canonical mesh
  `triadicSimplexPartition Q j` of a triadic cube: uniform convergence on the
  whole cube as `j -> -infinity`.

Scope.  Nothing here is probabilistic and nothing is specific to `shellFactor`:
the hypothesis is plain continuity of `B`, which the GMC carrier supplies
sample by sample through `PotentialField.contDiff_one`.  No statement is made
about the discrete minimization itself; that is (S2c).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

open Homogenization Metric Set

noncomputable section

variable {d : ℕ}

/-! ## Geometry of one closed cell -/

/-- A closed Kuhn cell sits in the closed ball of its support cube; this is the
first clause of `KuhnCell.closedCarrier`. -/
theorem KuhnCell.closedCarrier_subset_closedBall (T : KuhnCell d) :
    T.closedCarrier ⊆
      Metric.closedBall (cubeCenter T.supportCube) (cubeRadius T.supportCube) :=
  fun _ hx => hx.1

/-- A closed Kuhn cell is nonempty: it contains its lower corner. -/
theorem KuhnCell.closedCarrier_nonempty (T : KuhnCell d) : T.closedCarrier.Nonempty :=
  ⟨T.vertex 0, T.vertex_mem_closedCarrier 0⟩

/-- A closed Kuhn cell is compact: it is the convex hull of its `d + 1`
corners. -/
theorem isCompact_closedCarrier (T : KuhnCell d) : IsCompact T.closedCarrier := by
  rw [closedCarrier_eq_convexHull_vertexSet T]
  exact (Set.finite_range T.vertex).isCompact_convexHull ℝ

/-- A closed Kuhn cell is convex: it is the convex hull of its `d + 1`
corners. -/
theorem convex_closedCarrier (T : KuhnCell d) : Convex ℝ T.closedCarrier := by
  rw [closedCarrier_eq_convexHull_vertexSet T]
  exact convex_convexHull ℝ _

/-- **The mesh diameter of a Kuhn cell.**  Two points of one closed cell are at
distance at most the cube side `3^{scale}`; the ambient metric on `Vec d` is the
supremum metric, so this is the exact diameter of the support cube. -/
theorem dist_le_cubeScaleFactor_of_mem_closedCarrier (T : KuhnCell d) {x y : Vec d}
    (hx : x ∈ T.closedCarrier) (hy : y ∈ T.closedCarrier) :
    dist x y ≤ cubeScaleFactor T.supportCube := by
  have hxb := mem_closedBall.mp (T.closedCarrier_subset_closedBall hx)
  have hyb := mem_closedBall.mp (T.closedCarrier_subset_closedBall hy)
  have htri : dist x y ≤ dist x (cubeCenter T.supportCube) +
      dist (cubeCenter T.supportCube) y := dist_triangle _ _ _
  rw [dist_comm (cubeCenter T.supportCube) y] at htri
  rw [cubeScaleFactor_eq_two_mul_cubeRadius]
  linarith

/-! ## Cells of a triadic mesh lie in the closed ancestor cube -/

/-- The closed ball of a triadic cube is contained in the closure of its
half-open realization. -/
theorem closedBall_subset_closure_cubeSet (Q : TriadicCube d) :
    Metric.closedBall (cubeCenter Q) (cubeRadius Q) ⊆ closure (cubeSet Q) := by
  rw [cubeSet_eq_pi_Ico, closure_pi_set, closedBall_cubeCenter_eq_pi_Icc]
  refine Set.pi_mono fun i _ => ?_
  have hlt :
      (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q) ≠
        (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) := by
    have hs : (0 : ℝ) < cubeScaleFactor Q := zpow_pos (by norm_num) _
    intro h
    nlinarith
  rw [closure_Ico hlt]
  intro x hx
  refine ⟨?_, ?_⟩
  · have := hx.1
    simp only [cubeCenter, cubeRadius] at this ⊢
    linarith
  · have := hx.2
    simp only [cubeCenter, cubeRadius] at this ⊢
    linarith

/-- A triadic descendant's closed ball lies in its ancestor's closed ball. -/
theorem closedBall_subset_closedBall_of_mem_descendantsAtScale {Q R : TriadicCube d}
    {k : ℤ} (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) :
    Metric.closedBall (cubeCenter R) (cubeRadius R) ⊆
      Metric.closedBall (cubeCenter Q) (cubeRadius Q) := by
  refine (closedBall_subset_closure_cubeSet R).trans ?_
  refine closure_minimal ?_ Metric.isClosed_closedBall
  exact (cubeSet_subset_of_mem_descendantsAtScale hk hR).trans
    (cubeSet_subset_closedBall Q)

/-- **Every cell of the mesh of `Q` lies in the closed cube `Q`.**  This is the
compactness input of the uniform convergence below. -/
theorem closedCarrier_subset_closedBall_of_mem_triadicSimplexPartition
    {Q : TriadicCube d} {j : ℤ} (hj : j ≤ Q.scale) {T : KuhnCell d}
    (hT : T ∈ triadicSimplexPartition Q j) :
    T.closedCarrier ⊆ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
  T.closedCarrier_subset_closedBall.trans
    (closedBall_subset_closedBall_of_mem_descendantsAtScale hj
      (mem_triadicSimplexPartition_iff.mp hT))

/-! ## The cellwise supremum -/

/-- **`sup_{closure T} B`** of `s.notation` and `p.homogenized.coefficient.strict.decay`: the supremum of the
coefficient over one closed cell. -/
def cellSup (B : Vec d → ℝ) (T : KuhnCell d) : ℝ := sSup (B '' T.closedCarrier)

/-- The cellwise supremum is attained: a closed Kuhn cell is compact and
nonempty. -/
theorem exists_mem_cellSup_eq {B : Vec d → ℝ} (T : KuhnCell d)
    (hB : ContinuousOn B T.closedCarrier) :
    ∃ x ∈ T.closedCarrier, cellSup B T = B x := by
  obtain ⟨x, hx, hmax⟩ :=
    (isCompact_closedCarrier T).exists_isMaxOn T.closedCarrier_nonempty hB
  refine ⟨x, hx, ?_⟩
  refine IsGreatest.csSup_eq ⟨⟨x, hx, rfl⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hmax hy

/-- The coefficient is dominated by its cellwise supremum on the closed cell. -/
theorem le_cellSup {B : Vec d → ℝ} (T : KuhnCell d)
    (hB : ContinuousOn B T.closedCarrier) {x : Vec d} (hx : x ∈ T.closedCarrier) :
    B x ≤ cellSup B T := by
  refine le_csSup ?_ ⟨x, hx, rfl⟩
  exact ((isCompact_closedCarrier T).image_of_continuousOn hB).bddAbove

/-! ## The envelope `B^{(R)}` -/

/-- **`B_0^{(R)} = sum_T 1_T sup_{closure T} B_0`** (`s.notation` and `p.homogenized.coefficient.strict.decay`):
the cellwise-supremum envelope of `B` on a mesh `S`, written with the half-open
carriers of `Kuhn/Cells.lean`, which tile exactly. -/
def kuhnEnvelope (S : Finset (KuhnCell d)) (B : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ T ∈ S, T.carrier.indicator (fun _ => cellSup B T) x

/-- Distinct Kuhn cells of one scale have disjoint half-open carriers. -/
theorem disjoint_carrier_of_supportCube_scale_eq {T U : KuhnCell d}
    (hscale : T.supportCube.scale = U.supportCube.scale) (hTU : T ≠ U) :
    Disjoint T.carrier U.carrier := by
  by_cases hsupport : T.supportCube = U.supportCube
  · exact KuhnCell.disjoint_carrier_of_supportCube_eq hTU hsupport
  · exact (disjoint_cubeSet_of_scale_eq_of_ne hscale hsupport).mono
      T.carrier_subset_cubeSet U.carrier_subset_cubeSet

/-- On the carrier of one cell of an equal-scale mesh, the envelope is that
cell's supremum: the indicator sum has exactly one nonzero term. -/
theorem kuhnEnvelope_of_mem_carrier {S : Finset (KuhnCell d)} {s : ℤ}
    (hscale : ∀ T ∈ S, T.supportCube.scale = s) (B : Vec d → ℝ)
    {T : KuhnCell d} (hT : T ∈ S) {x : Vec d} (hx : x ∈ T.carrier) :
    kuhnEnvelope S B x = cellSup B T := by
  classical
  rw [kuhnEnvelope, Finset.sum_eq_single T]
  · exact Set.indicator_of_mem hx _
  · intro U hU hUT
    refine Set.indicator_of_notMem (fun hxU => ?_) _
    exact Set.disjoint_left.mp
      (disjoint_carrier_of_supportCube_scale_eq
        ((hscale U hU).trans (hscale T hT).symm) hUT) hxU hx
  · intro hTS
    exact absurd hT hTS

/-- **The envelope dominates the coefficient.**  This is the half of the
cellwise upper approximation that makes the discrete energy of
`s.notation` and `p.homogenized.coefficient.strict.decay` an upper bound for the continuum one. -/
theorem le_kuhnEnvelope {S : Finset (KuhnCell d)} {s : ℤ}
    (hscale : ∀ T ∈ S, T.supportCube.scale = s) {B : Vec d → ℝ} (hB : Continuous B)
    {T : KuhnCell d} (hT : T ∈ S) {x : Vec d} (hx : x ∈ T.carrier) :
    B x ≤ kuhnEnvelope S B x := by
  rw [kuhnEnvelope_of_mem_carrier hscale B hT hx]
  exact le_cellSup T hB.continuousOn (T.carrier_subset_closedCarrier hx)

/-! ## Uniform convergence of the envelope -/

/-- The scale at which the cube side drops below a prescribed length. -/
theorem exists_zpow_three_lt {delta : ℝ} (hdelta : 0 < delta) :
    ∃ s₀ : ℤ, (3 : ℝ) ^ s₀ < delta := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hdelta (show (1 / 3 : ℝ) < 1 by norm_num)
  refine ⟨-(n : ℤ), ?_⟩
  have hrw : (3 : ℝ) ^ (-(n : ℤ)) = (1 / 3 : ℝ) ^ n := by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
  rw [hrw]
  exact hn

/-- **(S2b): the cellwise upper approximations converge uniformly**
(`s.notation` and `p.homogenized.coefficient.strict.decay`).  For a continuous field `B` and a compact set
`K`, there is a scale `s₀` such that *every* equal-scale family of Kuhn cells of
scale at most `s₀` whose closed cells lie in `K` has its envelope within `eps`
of `B` at every point of every cell.

The proof is uniform continuity of `B` on `K` together with the mesh diameter
`dist_le_cubeScaleFactor_of_mem_closedCarrier`; the supremum is attained, so the
comparison is between two values of `B` at points of one cell. -/
theorem abs_kuhnEnvelope_sub_le_of_scale_le {B : Vec d → ℝ} (hB : Continuous B)
    {K : Set (Vec d)} (hK : IsCompact K) {eps : ℝ} (heps : 0 < eps) :
    ∃ s₀ : ℤ, ∀ (S : Finset (KuhnCell d)) (s : ℤ), s ≤ s₀ →
      (∀ T ∈ S, T.supportCube.scale = s) →
      (∀ T ∈ S, T.closedCarrier ⊆ K) →
      ∀ T ∈ S, ∀ x ∈ T.carrier, |kuhnEnvelope S B x - B x| ≤ eps := by
  obtain ⟨delta, hdelta, hunif⟩ :=
    uniformContinuousOn_iff.mp
      (hK.uniformContinuousOn_of_continuous hB.continuousOn) eps heps
  obtain ⟨s₀, hs₀⟩ := exists_zpow_three_lt hdelta
  refine ⟨s₀, fun S s hs hscale hsub T hT x hx => ?_⟩
  have hxc : x ∈ T.closedCarrier := T.carrier_subset_closedCarrier hx
  have hBT : ContinuousOn B T.closedCarrier := hB.continuousOn
  obtain ⟨y, hy, hyeq⟩ := exists_mem_cellSup_eq T hBT
  have hside : cubeScaleFactor T.supportCube ≤ (3 : ℝ) ^ s₀ := by
    rw [cubeScaleFactor, hscale T hT]
    exact zpow_le_zpow_right₀ (by norm_num) hs
  have hdist : dist y x < delta :=
    lt_of_le_of_lt
      ((dist_le_cubeScaleFactor_of_mem_closedCarrier T hy hxc).trans hside) hs₀
  have hclose : dist (B y) (B x) < eps :=
    hunif y (hsub T hT hy) x (hsub T hT hxc) hdist
  rw [kuhnEnvelope_of_mem_carrier hscale B hT hx, hyeq]
  rw [Real.dist_eq] at hclose
  exact hclose.le

/-- **(S2b) on a triadic cube.**  The canonical mesh `triadicSimplexPartition Q j`
covers `cubeSet Q` exactly, so its envelope converges to `B` uniformly on the
cube as `j -> -infinity`. -/
theorem abs_kuhnEnvelope_sub_le_cubeSet (Q : TriadicCube d) {B : Vec d → ℝ}
    (hB : Continuous B) {eps : ℝ} (heps : 0 < eps) :
    ∃ s₀ : ℤ, ∀ j : ℤ, j ≤ s₀ → j ≤ Q.scale → ∀ x ∈ cubeSet Q,
      |kuhnEnvelope (triadicSimplexPartition Q j) B x - B x| ≤ eps := by
  obtain ⟨s₀, hs₀⟩ :=
    abs_kuhnEnvelope_sub_le_of_scale_le (K := Metric.closedBall (cubeCenter Q)
      (cubeRadius Q)) hB (isCompact_closedBall _ _) heps
  refine ⟨s₀, fun j hj hjQ x hx => ?_⟩
  obtain ⟨T, hT, hxT⟩ := by
    simpa only [Set.mem_iUnion] using
      (cubeSet_eq_iUnion_triadicSimplexPartition Q hjQ ▸ hx :
        x ∈ ⋃ T ∈ (triadicSimplexPartition Q j : Set (KuhnCell d)), T.carrier)
  exact hs₀ (triadicSimplexPartition Q j) j hj
    (fun U hU => supportCube_scale_eq_of_mem_triadicSimplexPartition hjQ hU)
    (fun U hU => closedCarrier_subset_closedBall_of_mem_triadicSimplexPartition hjQ hU)
    T hT x hxT

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn
