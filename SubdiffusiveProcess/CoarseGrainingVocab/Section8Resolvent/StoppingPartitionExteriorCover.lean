module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionSphereGrowth

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Stopping
open scoped ENNReal

noncomputable section

variable {Omega Cell X : Type*}

/-- A global cell cover and a graph-distance lower bound on cells meeting an
exterior set give the exact existential cover consumed by
`wholeSpaceSolution_exterior_decay_of_overlapping_stopping_graph`. -/
theorem stoppingExteriorCover_of_distance
    {G : SimpleGraph Cell} {source : Finset Cell}
    (hsource : source.Nonempty) {cell : Cell → Set X}
    {exterior : Set X} {rate : ℝ}
    (hcover : ∀ x, ∃ q, x ∈ cell q)
    (hdistance : ∀ q, (cell q ∩ exterior).Nonempty →
      ⌈rate⌉₊ ≤ stoppingGraphDistance G source hsource q) :
    ∀ x ∈ exterior, ∃ q,
      ⌈rate⌉₊ ≤ stoppingGraphDistance G source hsource q ∧ x ∈ cell q := by
  intro x hx
  obtain ⟨q, hxq⟩ := hcover x
  exact ⟨q, hdistance q ⟨x, hxq, hx⟩, hxq⟩

/-- Once the last short crossing is below `k`, cells at graph distance at
least `ceil (epsilon * 3^k)` cover the complement of the radius-`3^k R`
ball.  This is the deterministic graph-distance conclusion at manuscript
lines `11644-11654`. -/
theorem stoppingExteriorCover_of_crossingDepth_le
    [PseudoMetricSpace X]
    (G : Omega → SimpleGraph Cell) (source : Omega → Finset Cell)
    (hsource : ∀ omega, (source omega).Nonempty)
    (cell : Omega → Cell → Set X) (hcover : ∀ omega x, ∃ q, x ∈ cell omega q)
    (x0 : X) {R epsilon : ℝ} {omega : Omega} {k : ℕ}
    (hfinite : failureHeightAt
      (stoppingShortCrossingEvent G source hsource cell x0 R epsilon) omega ≠
        (⊤ : WithTop ℕ))
    (hk : stoppingCrossingDepth G source hsource cell x0 R epsilon omega ≤ k) :
    ∀ x ∈ (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ, ∃ q,
      ⌈epsilon * (3 : ℝ) ^ k⌉₊ ≤
          stoppingGraphDistance (G omega) (source omega) (hsource omega) q ∧
        x ∈ cell omega q := by
  apply stoppingExteriorCover_of_distance (hsource omega) (hcover omega)
  intro q hq
  exact natCeil_le_stoppingGraphDistance_of_not_mem_shortCrossing
    G source hsource cell x0 R epsilon
    (not_mem_shortCrossing_of_depth_le G source hsource cell x0 R epsilon
      hfinite hk) hq

/-- A geometric short-crossing bound yields one full-measure event on which
the graph-distance exterior cover holds at every scale above the random
crossing depth. -/
theorem ae_forall_stoppingExteriorCover_above_crossingDepth
    [PseudoMetricSpace X] [MeasurableSpace Omega] (mu : Measure Omega)
    (G : Omega → SimpleGraph Cell) (source : Omega → Finset Cell)
    (hsource : ∀ omega, (source omega).Nonempty)
    (cell : Omega → Cell → Set X) (hcover : ∀ omega x, ∃ q, x ∈ cell omega q)
    (x0 : X) (R epsilon : ℝ) (C q : ENNReal)
    (hC : C ≠ ∞) (hq : q < 1)
    (hmeasure : ∀ k,
      mu (stoppingShortCrossingEvent G source hsource cell x0 R epsilon k) ≤
        C * q ^ k) :
    ∀ᵐ omega ∂mu, ∀ k,
      stoppingCrossingDepth G source hsource cell x0 R epsilon omega ≤ k →
        ∀ x ∈ (Metric.ball x0 ((3 : ℝ) ^ k * R))ᶜ, ∃ cellIndex,
          ⌈epsilon * (3 : ℝ) ^ k⌉₊ ≤
              stoppingGraphDistance (G omega) (source omega) (hsource omega)
                cellIndex ∧
            x ∈ cell omega cellIndex := by
  filter_upwards [ae_stoppingCrossingHeight_ne_top_of_geometric mu G source
    hsource cell x0 R epsilon C q hC hq hmeasure] with omega hfinite
  intro k hk
  exact stoppingExteriorCover_of_crossingDepth_le G source hsource cell hcover
    x0 hfinite hk

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
