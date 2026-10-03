module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.InhomogeneousLocalRegularity

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Topology Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast
open scoped CompactlySupported

noncomputable section

variable {d : ℕ}

private theorem exists_localContinuousRepresentative_inhomogeneous
    [NeZero d] (hd : 2 ≤ d)
    {W : Set (Vec d)} (hW : IsOpen W) {s : Vec d → ℝ}
    (hs : ContinuousOn s W) (hspos : ∀ x ∈ W, 0 < s x)
    {u : H1Function W} {g : Vec d → Vec d}
    (hu : IsDivFormWeakSolutionOn s W u g)
    (hg : MemVectorLpOn W (schauderSourceExponent d (1 / 2)) g)
    {x : Vec d} (hx : x ∈ W) :
    ∃ r : ℝ, 0 < r ∧ euclideanBall x r ⊆ W ∧
      ∃ uRep : Vec d → ℝ,
        ContinuousOn uRep (euclideanBall x r) ∧
        uRep =ᵐ[volume.restrict (euclideanBall x r)] u.toFun ∧
        ∀ y ∈ euclideanBall x r,
          euclideanBallAverageRepresentative u.toFun y = uRep y := by
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
  obtain ⟨uRep, huRepCont, huRepAE, _huRepHolder, huRepCanonical⟩ :=
    exists_physicalBallRepresentative_smallContrast_inhomogeneous
      hW hs hu hrho houter (s x) delta (1 / 2) hd
      (by constructor <;> norm_num) hdelta.le le_rfl hdelta1 hclose hg
  refine ⟨rho / 2, by positivity, ?_, uRep, huRepCont, huRepAE,
    huRepCanonical⟩
  exact (euclideanBall_subset_euclideanBall (by positivity)
    (by linarith)).trans houter

/-- An inhomogeneous scalar weak solution with finite Schauder source has a
continuous canonical representative on its whole open carrier. -/
theorem continuousOn_and_ae_eq_euclideanBallAverageRepresentative_inhomogeneous
    [NeZero d] (hd : 2 ≤ d)
    {W : Set (Vec d)} (hW : IsOpen W) {s : Vec d → ℝ}
    (hs : ContinuousOn s W) (hspos : ∀ x ∈ W, 0 < s x)
    {u : H1Function W} {g : Vec d → Vec d}
    (hu : IsDivFormWeakSolutionOn s W u g)
    (hg : MemVectorLpOn W (schauderSourceExponent d (1 / 2)) g) :
    ContinuousOn (euclideanBallAverageRepresentative u.toFun) W ∧
      euclideanBallAverageRepresentative u.toFun =ᵐ[volume.restrict W]
        u.toFun := by
  have hlocal : ∀ q : W,
      ∃ r : ℝ, 0 < r ∧ euclideanBall (q : Vec d) r ⊆ W ∧
        ∃ uRep : Vec d → ℝ,
          ContinuousOn uRep (euclideanBall (q : Vec d) r) ∧
          uRep =ᵐ[volume.restrict (euclideanBall (q : Vec d) r)] u.toFun ∧
          ∀ y ∈ euclideanBall (q : Vec d) r,
            euclideanBallAverageRepresentative u.toFun y = uRep y := by
    intro q
    exact exists_localContinuousRepresentative_inhomogeneous
      hd hW hs hspos hu hg q.2
  choose r hr hsub uRep huRepCont huRepAE huRepCanonical using hlocal
  let V : W → Set (Vec d) := fun q ↦ euclideanBall (q : Vec d) (r q)
  have hVopen : ∀ q, IsOpen (V q) := by
    intro q
    dsimp only [V]
    exact isOpen_euclideanBall (q : Vec d) (r q)
  have hVsub : ∀ q, V q ⊆ W := fun q ↦ hsub q
  have hVself : ∀ q, (q : Vec d) ∈ V q := by
    intro q
    change vecNormSq ((q : Vec d) - (q : Vec d)) < (r q) ^ 2
    simpa [vecNormSq, vecDot] using! sq_pos_of_pos (hr q)
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
  let gT : I → Vec d → ℝ := fun q ↦ uRep q.1
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
      (fun q ↦ huRepAE q.1) (fun q ↦ huRepCont q.1)
  · exact euclideanBallAverageRepresentative_ae_eq_of_countableCover
      hW.measurableSet VT gT (fun q ↦ hVopen q.1)
      (fun q ↦ hVsub q.1) hcover (fun q ↦ huRepAE q.1)
      (fun q ↦ huRepCont q.1)

/-- A locally bounded massive weak solution on a centered cube has a
continuous canonical representative in every dimension at least two. -/
theorem continuousOn_and_ae_eq_massiveWeakSolutionRepresentative_of_two_le
    [NeZero d] (hd : 2 ≤ d) {m : ℤ} {c rho : Vec d → ℝ}
    (hc : ContinuousOn c (cube d m))
    (hcpos : ∀ x ∈ cube d m, 0 < c x)
    {mu rhoMax U : ℝ} {u : H1Function (cube d m)}
    (f : C_c(Vec d, ℝ))
    (hrhoMeas : AEStronglyMeasurable rho (volume.restrict (cube d m)))
    (hrhoBdd : ∀ᵐ x ∂(volume.restrict (cube d m)), |rho x| ≤ rhoMax)
    (huBound : ∀ᵐ x ∂(volume.restrict (cube d m)), |u.toFun x| ≤ U)
    (hu : IsMassiveWeakSolutionOn c rho mu (cube d m) u f) :
    ContinuousOn (euclideanBallAverageRepresentative u.toFun) (cube d m) ∧
      euclideanBallAverageRepresentative u.toFun =ᵐ[volume.restrict (cube d m)]
        u.toFun := by
  obtain ⟨g, _hgLift, hgWeak, hgLp⟩ :=
    exists_schauder_divergence_lift_of_bounded_massiveWeakSolution
      d hd f hrhoMeas hrhoBdd huBound hu
  have hexponent : schauderSourceExponent d (1 / 2) = 2 * (d : ℝ) := by
    simp only [schauderSourceExponent]
    rw [div_eq_mul_inv]
    norm_num
    ring
  have hgSchauder : MemVectorLpOn (cube d m)
      (schauderSourceExponent d (1 / 2)) g := by
    simpa only [hexponent] using! hgLp
  exact continuousOn_and_ae_eq_euclideanBallAverageRepresentative_inhomogeneous
    hd (isOpen_openCubeSet (originCube d m)) hc hcpos hgWeak hgSchauder

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
