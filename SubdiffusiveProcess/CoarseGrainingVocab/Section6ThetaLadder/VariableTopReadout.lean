module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.FiniteCampanatoReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder.AmbientOscillationEnergy

@[expose] public section

/-!
# Theta ladder: variable stopping-top readout

The probabilistic stopping depth is dimension-only but need not be four.  This
module keeps the top of the finite Campanato telescope at `m - J`, where
`J ≥ 4` also guarantees that every such moving cube remains in the parent.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier

noncomputable section

variable {d : ℕ}

/-- A point in the middle-half target has its scale-`m-J` cube inside the
parent whenever `J ≥ 4`. -/
theorem translatedCube_natSub_subset_parent_of_middleHalf
    {m j J : ℕ} (hJm : J ≤ m) (hJ : 4 ≤ J) {z x : Vec d}
    {B' : Set (Vec d)} (hB' : IsMiddleHalfSubcube (m : ℤ) z j B')
    (hx : x ∈ B') :
    translatedCube d ((m - J : ℕ) : ℤ) x ⊆
      translatedCube d (m : ℤ) z := by
  have hxCollar : ‖x - z‖ ≤ (3 : ℝ) ^ (m : ℤ) / 4 :=
    hB'.choose_spec.2 x hx
  rw [translatedCube_eq_metricBall, translatedCube_eq_metricBall]
  apply Metric.ball_subset_ball'
  rw [dist_eq_norm]
  have hcast : ((m - J : ℕ) : ℤ) = (m : ℤ) - (J : ℤ) := by omega
  rw [hcast, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
  have hpowJ : (81 : ℝ) ≤ (3 : ℝ) ^ (J : ℤ) := by
    rw [zpow_natCast]
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hJ
    norm_num at hp ⊢
    exact hp
  have hpowM : 0 < (3 : ℝ) ^ (m : ℤ) := by positivity
  have hpowJpos : 0 < (3 : ℝ) ^ (J : ℤ) := by positivity
  have hsmall : (3 : ℝ) ^ (m : ℤ) / (3 : ℝ) ^ (J : ℤ) ≤
      (3 : ℝ) ^ (m : ℤ) / 81 := by
    exact div_le_div_of_nonneg_left hpowM.le (by norm_num) hpowJ
  nlinarith

/-- Mean comparison from the variable telescope top to the parent. -/
theorem abs_averageOn_natSub_sub_parent_le
    {m J : ℕ} (hJm : J ≤ m) {z x : Vec d} {f : Vec d → ℝ}
    (hsub : translatedCube d ((m - J : ℕ) : ℤ) x ⊆
      translatedCube d (m : ℤ) z)
    (hf : IntegrableOn f (translatedCube d (m : ℤ) z))
    (hf2 : IntegrableOn (fun y ↦ f y ^ 2)
      (translatedCube d (m : ℤ) z)) :
    |averageOn (translatedCube d ((m - J : ℕ) : ℤ) x) f -
        averageOn (translatedCube d (m : ℤ) z) f| ≤
      Real.sqrt (((3 : ℝ) ^ (J : ℤ)) ^ d) *
        normalizedL2On (translatedCube d (m : ℤ) z)
          (fun y ↦ f y - averageOn (translatedCube d (m : ℤ) z) f) := by
  have hraw := abs_averageOn_subset_sub_averageOn_le
    (by rw [translatedCube_eq_metricBall]; exact measurableSet_ball)
    hsub (volume_translatedCube_ne_top (m : ℤ) z)
    (volume_translatedCube_toReal_pos (m : ℤ) z)
    (volume_translatedCube_toReal_pos ((m - J : ℕ) : ℤ) x) hf hf2
  have hratio : Real.sqrt
      ((volume (translatedCube d (m : ℤ) z)).toReal /
        (volume (translatedCube d ((m - J : ℕ) : ℤ) x)).toReal) =
      Real.sqrt (((3 : ℝ) ^ (J : ℤ)) ^ d) := by
    rw [volume_translatedCube_toReal, volume_translatedCube_toReal]
    have hcast : ((m - J : ℕ) : ℤ) = (m : ℤ) - (J : ℤ) := by omega
    rw [hcast, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), div_pow]
    have hm0 : (3 : ℝ) ^ (m : ℤ) ≠ 0 := zpow_ne_zero _ (by norm_num)
    congr 1
    field_simp
  rwa [hratio] at hraw

/-- The finite target and parent-mean readouts with a variable top gap. -/
theorem variableTop_finiteCampanato_readouts
    {m j J : ℕ} (hJ : 4 ≤ J) (hJm : J ≤ m)
    (hJj : J + 1 ≤ j) (hjm : j ≤ m)
    {z : Vec d} {B' : Set (Vec d)}
    (hB' : IsMiddleHalfSubcube (m : ℤ) z j B')
    {h : H1Function (translatedCube d (m : ℤ) z)}
    {hRep : Vec d → ℝ} {Aosc Aparent P0 : ℝ}
    (hRepAE : hRep =ᵐ[volume.restrict (translatedCube d (m : ℤ) z)] h.toFun)
    (hAosc : 0 ≤ Aosc) (hAparent : 0 ≤ Aparent) (hP0 : 0 ≤ P0)
    (hrowsOsc : ∀ x ∈ B', ∀ s : ℕ, s ≤ m - J →
      normalizedL2On (translatedCube d (s : ℤ) x)
          (fun y ↦ h.toFun y - averageOn
            (translatedCube d (s : ℤ) x) h.toFun) ≤
        Aosc * (3 : ℝ) ^
          (-(1 / 2 : ℝ) * (((m - J : ℕ) : ℝ) - (s : ℝ))))
    (hrowsParent : ∀ x ∈ B', ∀ s : ℕ, s ≤ m - J →
      normalizedL2On (translatedCube d (s : ℤ) x)
          (fun y ↦ h.toFun y - averageOn
            (translatedCube d (s : ℤ) x) h.toFun) ≤
        Aparent * (3 : ℝ) ^
          (-(1 / 2 : ℝ) * (((m - J : ℕ) : ℝ) - (s : ℝ))))
    (hpoint0 : ∀ x ∈ B',
      |hRep x - averageOn (translatedCube d 0 x) h.toFun| ≤
        P0 * normalizedL2On (translatedCube d 0 x)
          (fun y ↦ h.toFun y - averageOn
            (translatedCube d 0 x) h.toFun))
    (htopParent : ∀ x ∈ B',
      |averageOn (translatedCube d ((m - J : ℕ) : ℤ) x) h.toFun -
          averageOn (translatedCube d (m : ℤ) z) h.toFun| ≤ Aparent) :
    let n := m - j
    let top := m - J
    let Kosc :=
      P0 * (Aosc * (3 : ℝ) ^ (-(1 / 2 : ℝ) * (top : ℝ))) +
        5 / 2 * Real.sqrt ((3 : ℝ) ^ d) *
          (Aosc * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * ((top : ℝ) - (n : ℝ)))) +
        Real.sqrt ((3 : ℝ) ^ d) *
          (Aosc * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * ((top : ℝ) - ((n + 1 : ℕ) : ℝ))))
    let Kmean :=
      P0 * (Aparent * (3 : ℝ) ^ (-(1 / 2 : ℝ) * (top : ℝ))) +
        5 / 2 * Real.sqrt ((3 : ℝ) ^ d) *
          (Aparent * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * ((top : ℝ) - (n : ℝ)))) +
        Real.sqrt ((3 : ℝ) ^ d) *
          (Aparent * (3 : ℝ) ^
            (-(1 / 2 : ℝ) * ((top : ℝ) - ((n + 1 : ℕ) : ℝ))))
    oscillationOn B' hRep ≤ 2 * Kosc ∧
      sSup {r : ℝ | ∃ x ∈ B',
        r = |hRep x - averageOn (translatedCube d (m : ℤ) z) hRep|} ≤
        Kmean + 5 / 2 * Real.sqrt ((3 : ℝ) ^ d) * Aparent + Aparent := by
  dsimp only
  obtain ⟨z', hB'eq, _hz'collar, _⟩ :=
    exists_middleHalfSubcube_center_and_subset_ball hB'
  let n := m - j
  let top := m - J
  have hB'cast : B' = translatedCube d (n : ℤ) z' := by
    have hncast : ((n : ℕ) : ℤ) = (m : ℤ) - (j : ℤ) := by
      dsimp only [n]
      omega
    rw [hncast]
    exact hB'eq
  have hntop : n + 1 ≤ top := by
    dsimp only [n, top]
    omega
  have hmemParent := h.memL2
  let : IsFiniteMeasure (volume.restrict (translatedCube d (m : ℤ) z)) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact lt_top_iff_ne_top.mpr
          (volume_translatedCube_ne_top (m : ℤ) z)⟩
  have hfParent : IntegrableOn h.toFun (translatedCube d (m : ℤ) z) :=
    hmemParent.integrable one_le_two
  have hf2Parent : IntegrableOn (fun y ↦ h.toFun y ^ 2)
      (translatedCube d (m : ℤ) z) := hmemParent.integrable_sq
  have hInt : ∀ x ∈ B', ∀ s : ℕ, s ≤ top →
      IntegrableOn h.toFun (translatedCube d (s : ℤ) x) ∧
      IntegrableOn (fun y ↦ h.toFun y ^ 2)
        (translatedCube d (s : ℤ) x) := by
    intro x hx s hs
    have htopSub := translatedCube_natSub_subset_parent_of_middleHalf
      hJm hJ hB' hx
    have hsTop : s ≤ m - J := by simpa only [top] using hs
    have hsub : translatedCube d (s : ℤ) x ⊆
        translatedCube d ((m - J : ℕ) : ℤ) x := by
      exact translatedCube_subset_translatedCube_sameCenter
        (by exact_mod_cast hsTop) x
    exact ⟨hfParent.mono_set (hsub.trans htopSub),
      hf2Parent.mono_set (hsub.trans htopSub)⟩
  have hoscRaw := finiteCampanato_targetOscillation_and_parentMean
    hntop hB'cast (A := Aosc) hAosc hP0 hInt hrowsOsc hpoint0
      (Pparent := averageOn (translatedCube d (top : ℤ) z') h.toFun)
      (by simpa using hAosc)
  have hmeanTop : |averageOn (translatedCube d (top : ℤ) z') h.toFun -
      averageOn (translatedCube d (m : ℤ) z) h.toFun| ≤ Aparent := by
    have hz'mem : z' ∈ B' := by
      rw [hB'cast, translatedCube_eq_metricBall]
      exact Metric.mem_ball_self (by positivity)
    simpa only [top] using htopParent z' hz'mem
  have hmeanRaw := finiteCampanato_targetOscillation_and_parentMean
    hntop hB'cast (A := Aparent) hAparent hP0 hInt hrowsParent hpoint0 hmeanTop
  refine ⟨?_, ?_⟩
  · simpa only [n, top] using hoscRaw.1
  · have havg := averageOn_eq_of_ae_eq hRepAE
    rw [← havg] at hmeanRaw
    simpa only [n, top] using hmeanRaw.2

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ThetaLadder
