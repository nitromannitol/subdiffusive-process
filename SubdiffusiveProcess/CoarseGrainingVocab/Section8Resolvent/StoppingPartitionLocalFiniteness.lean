module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.StoppingPartitionTriadicFailureHeight

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open Set Homogenization
noncomputable section

/-- Triadic cubes of one fixed scale meeting a bounded set form a finite
family: a cube meeting the set has each index coordinate bounded by the
diameter of the set divided by the side length. -/
theorem finite_triadicCube_scale_eq_meeting_isBounded {d : ℕ} (s : ℤ)
    {S : Set (Vec d)} (hS : Bornology.IsBounded S) :
    {Q : TriadicCube d | Q.scale = s ∧ (cubeSet Q ∩ S).Nonempty}.Finite := by
  classical
  obtain ⟨r, hr⟩ := hS.subset_closedBall (0 : Vec d)
  set N : ℕ := ⌈r / (3 : ℝ) ^ s + 1⌉₊ with hN
  have h3 : (0 : ℝ) < (3 : ℝ) ^ s := zpow_pos (by norm_num) s
  have hNle : r / (3 : ℝ) ^ s + 1 ≤ (N : ℝ) := Nat.le_ceil _
  have hsub : (fun Q : TriadicCube d ↦ Q.index) ''
      {Q : TriadicCube d | Q.scale = s ∧ (cubeSet Q ∩ S).Nonempty} ⊆
      Set.univ.pi (fun _ : Fin d ↦ Set.Icc (-(N : ℤ)) (N : ℤ)) := by
    rintro f ⟨Q, ⟨hscale, z, hzQ, hzS⟩, rfl⟩
    intro i _
    have hzr : |z i| ≤ r := by
      have hball := hr hzS
      rw [Metric.mem_closedBall, dist_zero_right] at hball
      exact le_trans (by simpa using norm_le_pi_norm z i) hball
    have hzQi := hzQ i
    rw [cubeScaleFactor, hscale] at hzQi
    have hlow : ((Q.index i : ℝ) - 1 / 2) * (3 : ℝ) ^ s ≤ z i := hzQi.1
    have hhigh : z i < ((Q.index i : ℝ) + 1 / 2) * (3 : ℝ) ^ s := hzQi.2
    have hbound : |(Q.index i : ℝ)| * (3 : ℝ) ^ s ≤ r + (3 : ℝ) ^ s := by
      have hzle : z i ≤ r := le_of_abs_le hzr
      have hzge : -r ≤ z i := neg_le_of_abs_le hzr
      rcases abs_cases ((Q.index i : ℝ)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
        nlinarith [hlow, hhigh, hzle, hzge, h3]
    have hfrac : r / (3 : ℝ) ^ s + 1 = (r + (3 : ℝ) ^ s) / (3 : ℝ) ^ s := by
      field_simp
    have habs : |(Q.index i : ℝ)| ≤ r / (3 : ℝ) ^ s + 1 := by
      rw [hfrac, le_div_iff₀ h3]
      exact hbound
    have hcast : |(Q.index i : ℝ)| ≤ (N : ℝ) := by linarith
    have : |Q.index i| ≤ (N : ℤ) := by
      have := hcast
      rw [← Int.cast_abs] at this
      exact_mod_cast this
    exact Set.mem_Icc.mpr ⟨(abs_le.mp this).1, (abs_le.mp this).2⟩
  refine Set.Finite.of_finite_image
    (f := fun Q : TriadicCube d ↦ Q.index)
    ((Set.Finite.pi fun _ ↦ Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset hsub) ?_
  intro Q hQ R hR hQR
  cases Q with
  | mk sQ iQ =>
    cases R with
    | mk sR iR =>
      simp only [Set.mem_setOf_eq] at hQ hR
      simp only at hQR
      subst hQR
      simp only [hQ.1, hR.1]

/-- The center of a triadic cube belongs to its half-open realization. -/
theorem cubeCenter_mem_cubeSet {d : ℕ} (Q : TriadicCube d) :
    cubeCenter Q ∈ cubeSet Q := by
  intro i
  have h3 : (0 : ℝ) < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  constructor
  · dsimp [cubeCenter]
    nlinarith
  · dsimp [cubeCenter]
    nlinarith

/-- **Local finiteness of the initial candidate family from a local depth
bound.**  If around every point some ball meets only candidates of bounded
stopping depth, then the candidate family is locally finite.  This is the
deterministic half of the missing producer for the `hinitial` hypothesis of
the repaired stopping partition. -/
theorem locallyFinite_triadicStoppingCandidate_of_local_depth_bound
    {d : ℕ} {Omega : Type*} {base : ℤ}
    (failure : TriadicCube d → Set Omega) (omega : Omega)
    (hdepth : ∀ x : Vec d, ∃ r : ℝ, 0 < r ∧ ∃ B : ℕ,
      ∀ Q : StoppingBaseCube d base,
        (cubeSet (triadicStoppingCandidate failure omega Q) ∩
          Metric.ball x r).Nonempty →
        triadicStoppingDepth failure omega Q ≤ B) :
    LocallyFinite fun Q : StoppingBaseCube d base ↦
      cubeSet (triadicStoppingCandidate failure omega Q) := by
  intro x
  obtain ⟨r, hrpos, B, hB⟩ := hdepth x
  refine ⟨Metric.ball x r, Metric.ball_mem_nhds x hrpos, ?_⟩
  set M : ℝ := (3 : ℝ) ^ (base + (B : ℤ)) + r with hM
  refine Set.Finite.of_finite_image (f := fun Q : StoppingBaseCube d base ↦ Q.1)
    ((finite_triadicCube_scale_eq_meeting_isBounded (d := d) base
      (S := Metric.closedBall x M) Metric.isBounded_closedBall).subset ?_)
    (fun P _ R _ hPR ↦ Subtype.ext hPR)
  rintro P ⟨Q, hQ, rfl⟩
  obtain ⟨z, hzC, hzx⟩ := hQ
  refine ⟨Q.2, ⟨cubeCenter Q.1, cubeCenter_mem_cubeSet Q.1, ?_⟩⟩
  set C : TriadicCube d := triadicStoppingCandidate failure omega Q with hC
  have hyC : cubeCenter Q.1 ∈ cubeSet C :=
    cubeSet_subset_triadicStoppingCandidate failure omega Q
      (cubeCenter_mem_cubeSet Q.1)
  have hy := cubeSet_subset_closedBall C hyC
  have hz := cubeSet_subset_closedBall C hzC
  rw [Metric.mem_closedBall] at hy hz ⊢
  rw [Metric.mem_ball] at hzx
  have hscaleC : C.scale = base + (triadicStoppingDepth failure omega Q : ℤ) :=
    triadicStoppingCandidate_scale failure omega Q
  have hscaleLe : C.scale ≤ base + (B : ℤ) := by
    rw [hscaleC]
    have hdle : triadicStoppingDepth failure omega Q ≤ B :=
      hB Q ⟨z, hzC, Metric.mem_ball.mpr hzx⟩
    have : ((triadicStoppingDepth failure omega Q : ℤ)) ≤ (B : ℤ) := by
      exact_mod_cast hdle
    omega
  have hpow : (3 : ℝ) ^ C.scale ≤ (3 : ℝ) ^ (base + (B : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) hscaleLe
  have hradius : 2 * cubeRadius C = (3 : ℝ) ^ C.scale := by
    simp [cubeRadius, cubeScaleFactor]
  have h1 : dist (cubeCenter Q.1) (cubeCenter C) ≤ cubeRadius C := hy
  have h2 : dist (cubeCenter C) z ≤ cubeRadius C := by rw [dist_comm]; exact hz
  have h3 : dist (cubeCenter C) x ≤ cubeRadius C + r := by
    have htri : dist (cubeCenter C) x ≤ dist (cubeCenter C) z + dist z x :=
      dist_triangle _ _ _
    linarith [hzx.le]
  have htri2 : dist (cubeCenter Q.1) x ≤
      dist (cubeCenter Q.1) (cubeCenter C) + dist (cubeCenter C) x :=
    dist_triangle _ _ _
  have hsum : dist (cubeCenter Q.1) x ≤ 2 * cubeRadius C + r := by linarith
  rw [hradius] at hsum
  simp only [hM]
  linarith

end
end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
