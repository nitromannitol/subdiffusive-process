import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionExteriorCover
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionHalfGridCover




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
open SubdiffusiveProcess.Frozen.Section8

noncomputable section

variable {d : ℕ} {Omega Cell : Type*}

/-- Feed a locally finite half-grid stopping graph to the exterior row at
every triadic radius above its last short crossing. -/
theorem wholeSpaceSolution_exterior_decay_of_halfGrid_stoppingGraph
    [DecidableEq Cell]
    {a f : Vec d → ℝ} {t : ℝ} (ht : 0 < t) (haNonneg : ∀ x, 0 ≤ a x)
    (u : WholeSpaceDivergenceResolventSolution a t f)
    (G : SimpleGraph Cell) [G.LocallyFinite] (hconnected : G.Connected)
    (source : Finset Cell) (hsourceNonempty : source.Nonempty)
    (levelCells : ℕ → Finset Cell)
    (hlevelCells : ∀ j q, q ∈ levelCells j ↔
      stoppingGraphDistance G source hsourceNonempty q = j)
    (scale : Cell → ℤ) (centre : Cell → Vec d) (lam : Cell → ℝ)
    (neighbour : Cell → (Fin d → ℤ) → Cell)
    (hneighbourScale : ∀ q k, k ∈ gridNeighbours d (0 : Fin d → ℤ) →
      scale (neighbour q k) = scale q)
    (hneighbourCentre : ∀ q k, k ∈ gridNeighbours d (0 : Fin d → ℤ) →
      centre (neighbour q k) =
        stoppingRelativeGridCentre (scale q) (centre q) k)
    (hneighbourAdj : ∀ q k, k ∈ gridNeighbours d (0 : Fin d → ℤ) →
      G.Adj q (neighbour q k))
    {K : ℝ} (hK : 0 ≤ K) (haLinear : ∀ x, a x ≤ K * (1 + ‖x‖))
    {omega : Omega} (x0 : Vec d) {R epsilon : ℝ} {k : ℕ}
    (hcoverAll : ∀ x, ∃ q, x ∈ translatedCube d (scale q) (centre q))
    (hfinite : failureHeightAt
      (stoppingShortCrossingEvent (fun _ : Omega ↦ G) (fun _ ↦ source)
        (fun _ ↦ hsourceNonempty)
        (fun _ q ↦ translatedCube d (scale q) (centre q)) x0 R epsilon) omega ≠
          (⊤ : WithTop ℕ))
    (hk : stoppingCrossingDepth (fun _ : Omega ↦ G) (fun _ ↦ source)
      (fun _ ↦ hsourceNonempty)
      (fun _ q ↦ translatedCube d (scale q) (centre q)) x0 R epsilon omega ≤ k)
    {A theta0 : ℝ} {D : ℕ}
    (hA : 0 ≤ A) (htheta0 : 0 < theta0) (hD : 0 < D)
    (heffective : (D : ℝ) * ((((7 ^ d : ℕ) : ℝ)) * theta0) < 1)
    (hsource : ∀ q, stoppingGraphDistance G source hsourceNonempty q = 0 →
      ∫ x in translatedCube d (scale q) (centre q), u.toFun x ^ 2 ∂volume ≤ A)
    (hell : ∀ q, 0 < stoppingGraphDistance G source hsourceNonempty q →
      IsEllipticFieldOn (lam q)
        (stoppingCellLinearUpperBound K (scale q) (centre q))
        (translatedCube d (scale q + 1) (centre q)) (scalarCoeffField a))
    (hquiet : ∀ q, 0 < stoppingGraphDistance G source hsourceNonempty q →
      ∀ x ∈ translatedCube d (scale q + 1) (centre q), f x = 0)
    (hsmall : ∀ q, 0 < stoppingGraphDistance G source hsourceNonempty q →
      4096 * (d : ℝ) *
          stoppingCellLinearUpperBound K (scale q) (centre q) * t *
            ((3 : ℝ) ^ scale q)⁻¹ ^ 2 ≤ theta0)
    (hdegree : ∀ q, (G.neighborFinset q).card ≤ D) :
    ∫ x in (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ, u.toFun x ^ 2 ∂volume ≤
      ((levelCells 0).card : ℝ) * A *
        (1 - (D : ℝ) * (((7 ^ d : ℕ) : ℝ) * theta0))⁻¹ *
          Real.exp
            (Real.log ((D : ℝ) * (((7 ^ d : ℕ) : ℝ) * theta0)) *
              (epsilon * (3 : ℝ) ^ k)) := by
  classical
  let cell : Omega → Cell → Set (Vec d) :=
    fun _ q ↦ translatedCube d (scale q) (centre q)
  have htailCover : ∀ x ∈ (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ, ∃ q,
      ⌈epsilon * (3 : ℝ) ^ k⌉₊ ≤
          stoppingGraphDistance G source hsourceNonempty q ∧
        x ∈ translatedCube d (scale q) (centre q) := by
    simpa only [cell] using
      (stoppingExteriorCover_of_crossingDepth_le
        (fun _ : Omega ↦ G) (fun _ ↦ source) (fun _ ↦ hsourceNonempty)
        cell (fun _ ↦ hcoverAll) x0 hfinite hk)
  refine wholeSpaceSolution_exterior_decay_of_overlapping_stopping_graph
    ht haNonneg u G hconnected source hsourceNonempty levelCells hlevelCells
    scale centre lam
    (fun q ↦ stoppingCellLinearUpperBound K (scale q) (centre q))
    ((Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ)
    (levelCells 0).card D (7 ^ d) hA htheta0
    (Nat.pow_pos (by norm_num)) hD heffective hsource ?_ hell ?_ hquiet
    hsmall ?_ ?_ htailCover
  · intro q
    exact stoppingCellLinearUpperBound_nonneg hK (scale q) (centre q)
  · intro q _ x hx
    exact le_stoppingCellLinearUpperBound_of_mem_enlargement hK haLinear
      (scale q) (centre q) hx
  · intro q _
    let s := (gridNeighbours d (0 : Fin d → ℤ)).image (neighbour q)
    refine ⟨s, ?_, ?_, ?_, ?_⟩
    · exact Finset.image_nonempty.mpr
        ⟨(0 : Fin d → ℤ), self_mem_gridNeighbours d 0⟩
    · exact Finset.card_image_le.trans_eq (card_gridNeighbours d 0)
    · intro p hp
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
      exact hneighbourAdj q r hr
    · intro x hx
      obtain ⟨r, hr, hxr⟩ := Set.mem_iUnion₂.mp
        (translatedCube_succ_subset_stoppingRelativeGridNeighbours
          d (scale q) (centre q) hx)
      refine Set.mem_iUnion₂.mpr
        ⟨neighbour q r, Finset.mem_image_of_mem _ hr, ?_⟩
      rw [hneighbourScale q r hr, hneighbourCentre q r hr]
      exact hxr
  · exact card_stoppingLevelCells_le_degree_pow G hconnected
      hsourceNonempty levelCells hlevelCells le_rfl hdegree

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
