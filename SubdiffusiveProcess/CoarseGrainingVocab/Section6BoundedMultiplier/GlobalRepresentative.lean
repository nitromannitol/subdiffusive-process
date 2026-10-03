module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.RepresentativeReadout

@[expose] public section

/-!
# Global canonical representative for continuous positive scalar coefficients

Every interior point admits a sufficiently small ball on which normalization
by the coefficient at the center enters the small-contrast Schauder regime.
A countable subcover then identifies the canonical ball-average
representative globally, both continuously and almost everywhere.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

open MeasureTheory Topology Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast

noncomputable section

variable {d : ℕ}

private theorem exists_localContinuousRepresentative
    [NeZero d] (hd : 2 ≤ d)
    {W : Set (Vec d)} (hW : IsOpen W) {s : Vec d → ℝ}
    (hs : ContinuousOn s W) (hspos : ∀ x ∈ W, 0 < s x)
    {u : H1Function W} (hu : IsWeaklyHarmonicOn s W u)
    {x : Vec d} (hx : x ∈ W) :
    ∃ r : ℝ, 0 < r ∧ euclideanBall x r ⊆ W ∧
      ∃ g : Vec d → ℝ,
        ContinuousOn g (euclideanBall x r) ∧
        g =ᵐ[volume.restrict (euclideanBall x r)] u.toFun ∧
        ∀ y ∈ euclideanBall x r,
          euclideanBallAverageRepresentative u.toFun y = g y := by
  let delta := smallContrastThreshold d (1 / 2)
  have hdelta : 0 < delta := by
    dsimp only [delta, smallContrastThreshold]
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)
  have hdelta1 : delta < 1 :=
    (smallContrastThreshold_le_eighth_gap d (by norm_num)).trans_lt (by norm_num)
  have hsx : 0 < s x := hspos x hx
  have htcont : ContinuousAt (fun y ↦ (s x)⁻¹ * s y) x :=
    continuousAt_const.mul (hs.continuousAt (hW.mem_nhds hx))
  obtain ⟨eta, heta, hcloseEta⟩ :=
    (Metric.continuousAt_iff.1 htcont) delta hdelta
  obtain ⟨etaW, hetaW, hballW⟩ := Metric.isOpen_iff.1 hW x hx
  let rho := min eta etaW
  have hrho : 0 < rho := lt_min heta hetaW
  have houter : euclideanBall x rho ⊆ W := by
    intro y hy
    apply hballW
    exact (euclideanBall_subset_metricBall hrho hy).trans_le
      (min_le_right eta etaW)
  have hcenter : (s x)⁻¹ * s x = 1 := inv_mul_cancel₀ hsx.ne'
  have hclose : ∀ y ∈ euclideanBall x rho,
      |(s x)⁻¹ * s y - 1| ≤ delta := by
    intro y hy
    have hydist : dist y x < eta :=
      (euclideanBall_subset_metricBall hrho hy).trans_le
        (min_le_left eta etaW)
    have h := hcloseEta hydist
    rw [Real.dist_eq, hcenter] at h
    exact h.le
  obtain ⟨g, hgcont, hgae, _hholder, hgcanonical⟩ :=
    exists_physicalBallRepresentative_smallContrast hW hs hu hrho houter
      (s x) delta (1 / 2) hd (by constructor <;> norm_num)
      hdelta.le le_rfl hdelta1 hclose
  refine ⟨rho / 2, by positivity, ?_, g, hgcont, hgae, hgcanonical⟩
  exact (euclideanBall_subset_euclideanBall (by positivity)
    (by linarith)).trans houter

/-- A weakly harmonic `H¹` function for a continuous positive scalar
coefficient has the canonical shrinking-ball representative on the whole
open carrier. -/
theorem continuousOn_and_ae_eq_euclideanBallAverageRepresentative
    [NeZero d] (hd : 2 ≤ d)
    {W : Set (Vec d)} (hW : IsOpen W) {s : Vec d → ℝ}
    (hs : ContinuousOn s W) (hspos : ∀ x ∈ W, 0 < s x)
    {u : H1Function W} (hu : IsWeaklyHarmonicOn s W u) :
    ContinuousOn (euclideanBallAverageRepresentative u.toFun) W ∧
      euclideanBallAverageRepresentative u.toFun =ᵐ[volume.restrict W]
        u.toFun := by
  have hlocal : ∀ q : W,
      ∃ r : ℝ, 0 < r ∧ euclideanBall (q : Vec d) r ⊆ W ∧
        ∃ g : Vec d → ℝ,
          ContinuousOn g (euclideanBall (q : Vec d) r) ∧
          g =ᵐ[volume.restrict (euclideanBall (q : Vec d) r)] u.toFun ∧
          ∀ y ∈ euclideanBall (q : Vec d) r,
            euclideanBallAverageRepresentative u.toFun y = g y := by
    intro q
    exact exists_localContinuousRepresentative hd hW hs hspos hu q.2
  choose r hr hsub g hgcont hgae hgcanonical using hlocal
  let V : W → Set (Vec d) := fun q ↦ euclideanBall (q : Vec d) (r q)
  have hVopen : ∀ q, IsOpen (V q) := by
    intro q
    dsimp only [V]
    exact isOpen_euclideanBall (q : Vec d) (r q)
  have hVsub : ∀ q, V q ⊆ W := fun q ↦ hsub q
  have hVself : ∀ q, (q : Vec d) ∈ V q := by
    intro q
    change vecNormSq ((q : Vec d) - (q : Vec d)) < (r q) ^ 2
    simpa [vecNormSq, vecDot] using sq_pos_of_pos (hr q)
  have hVunion : (⋃ q, V q) = W := by
    apply Set.Subset.antisymm
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨q, hxq⟩ := hx
      exact hVsub q hxq
    · intro x hx
      exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hVself ⟨x, hx⟩⟩
  obtain ⟨T, hTcount, hTunion⟩ :=
    TopologicalSpace.isOpen_iUnion_countable V hVopen
  let I := T
  letI : Countable I := hTcount.to_subtype
  let VT : I → Set (Vec d) := fun q ↦ V q.1
  let gT : I → Vec d → ℝ := fun q ↦ g q.1
  have hcover : W ⊆ ⋃ q : I, VT q := by
    intro x hx
    have hxall : x ∈ ⋃ q, V q := by rw [hVunion]; exact hx
    rw [← hTunion] at hxall
    simp only [Set.mem_iUnion] at hxall ⊢
    obtain ⟨q, hqT, hxq⟩ := hxall
    exact ⟨⟨q, hqT⟩, hxq⟩
  constructor
  · exact continuousOn_euclideanBallAverageRepresentative_of_countableCover
      VT gT (fun q ↦ hVopen q.1) (fun q ↦ hVsub q.1) hcover
      (fun q ↦ hgae q.1) (fun q ↦ hgcont q.1)
  · exact euclideanBallAverageRepresentative_ae_eq_of_countableCover
      hW.measurableSet VT gT (fun q ↦ hVopen q.1) (fun q ↦ hVsub q.1)
      hcover (fun q ↦ hgae q.1) (fun q ↦ hgcont q.1)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
