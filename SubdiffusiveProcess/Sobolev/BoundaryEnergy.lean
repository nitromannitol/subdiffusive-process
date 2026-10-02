import SubdiffusiveProcess.Geometry.BoundaryChain
import SubdiffusiveProcess.Analysis.RadiusEnergyComposition
import SubdiffusiveProcess.Sobolev.GradientEnergyMeasure
open Set MeasureTheory TopologicalSpace Metric
open scoped BigOperators
namespace SubdiffusiveProcess
/-- Transfer admissible interior estimates to the actual local gradient energy at every radius above a specified minimum scale. The finite boundary chain is constructed in the proof, and its multiplicative and source losses are explicit. -/
theorem localGradientEnergy_boundary_bound_of_admissible_estimates
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (g : HilbertGradient Ω)
    (x : SpatialCoordinates d)
    (hx : ∀ j : Fin d, |x j| < (1 / 2 : ℝ))
    (P : Finset (Fin d)) (hP : ∀ j : Fin d, j ∈ P ↔ 0 ≤ x j)
    (m : ℤ) (L t Z F rmin : ℝ) (hL : 10 ≤ L) (ht : 0 ≤ t)
    (hZ : 1 ≤ Z) (hF : 0 ≤ F) :
    let δ : Fin d → ℝ := fun j => (1 / 2 : ℝ) - |x j|
    let z : Finset (Fin d) → SpatialCoordinates d := fun I j =>
      if j ∈ I then (if j ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x j
    let Rstar : ℝ := (3 : ℝ) ^ m / 2
    let Q : Set (SpatialCoordinates d) := Metric.ball 0 (1 / 2)
    (∀ (I : Finset (Fin d)) (u v : ℤ),
      let s : ℝ := (3 : ℝ) ^ u / 2
      let R : ℝ := (3 : ℝ) ^ v / 2
      rmin ≤ s → 8 * s < R → R ≤ Rstar →
      (∀ i : Fin d, i ∉ I → 4 * L * R ≤ δ i) →
      localGradientEnergy a (s := Metric.ball (z I) s ∩ Q)
          (isOpen_ball.measurableSet.inter isOpen_ball.measurableSet) g ≤
        Z * ((s / R) ^ t * (localGradientEnergy a (s := Metric.ball (z I) (L * R) ∩ Q)
          (isOpen_ball.measurableSet.inter isOpen_ball.measurableSet) g) + s ^ t * F)) →
    ∀ r : ℝ, 0 < r → rmin ≤ r →
      localGradientEnergy a (s := Metric.ball x r ∩ Q)
          (isOpen_ball.measurableSet.inter isOpen_ball.measurableSet) g ≤
        (3 * r) ^ t * (Z * (3 * (1 + 100 * L)) ^ t) ^ d * Z *
          ((24 / Rstar) ^ t * localGradientEnergy a (s := Q) isOpen_ball.measurableSet g + (d + 1 : ℝ) * F) := by
  classical
  dsimp only
  intro hlocal r hr hrmin
  let δ : Fin d → ℝ := fun j => (1 / 2 : ℝ) - |x j|
  let z : Finset (Fin d) → SpatialCoordinates d := fun I j =>
    if j ∈ I then (if j ∈ P then (1 / 2 : ℝ) else -(1 / 2 : ℝ)) else x j
  let Rstar : ℝ := (3 : ℝ) ^ m / 2
  let Q : Set (SpatialCoordinates d) := Metric.ball 0 (1 / 2)
  let Γ : Measure (SpatialCoordinates d) :=
    (volume.restrict (Ω : Set (SpatialCoordinates d))).withDensity
      (fun y => ENNReal.ofReal (∑ i : Fin d, a.val y * (g i y) ^ 2))
  have hΓdata := gradientEnergy_withDensity_finite_and_real a g
  change IsFiniteMeasure Γ ∧ _ at hΓdata
  letI : IsFiniteMeasure Γ := hΓdata.1
  have hΓ (s : Set (SpatialCoordinates d)) (hs : MeasurableSet s) :
      Γ.real s = localGradientEnergy a hs g := hΓdata.2 s hs
  have hRstar : 0 < Rstar := div_pos (zpow_pos (by norm_num) m) (by norm_num)
  obtain ⟨p, hplo, hphi⟩ :=
    exists_mem_Ioc_zpow (show 0 < (2 : ℝ) * r by positivity)
      (show (1 : ℝ) < 3 by norm_num)
  let q : ℤ := p + 1
  have hqpow : (3 : ℝ) ^ q = 3 * (3 : ℝ) ^ p := by
    dsimp [q]
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hs0lo : r ≤ (3 : ℝ) ^ q / 2 := by
    rw [hqpow]
    nlinarith
  have hs0hi : (3 : ℝ) ^ q / 2 < 3 * r := by
    rw [hqpow]
    nlinarith
  obtain ⟨n, hn, J, k, hJ0, hk0, hterminal, hsteps⟩ :=
    exists_finite_boundary_chain x hx ∅ P hP m q L hL
  let s : ℕ → ℝ := fun j => (3 : ℝ) ^ (k j) / 2
  let E : ℕ → ℝ := fun j => Γ.real (Metric.ball (z (J j)) (s j) ∩ Q)
  let A : ℝ := 3 * (1 + 100 * L)
  have hspos : ∀ j, 0 < s j := fun j => div_pos (zpow_pos (by norm_num) _) (by norm_num)
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have hE : ∀ j, 0 ≤ E j := fun j => measureReal_nonneg
  have hlocalΓ : ∀ (I : Finset (Fin d)) (u v : ℤ),
      let ss : ℝ := (3 : ℝ) ^ u / 2
      let R : ℝ := (3 : ℝ) ^ v / 2
      rmin ≤ ss → 8 * ss < R → R ≤ Rstar →
      (∀ i : Fin d, i ∉ I → 4 * L * R ≤ δ i) →
      Γ.real (Metric.ball (z I) ss ∩ Q) ≤
        Z * ((ss / R) ^ t * Γ.real (Metric.ball (z I) (L * R) ∩ Q) + ss ^ t * F) := by
    intro I u v
    dsimp only
    intro hmin h8 hRm hclear
    rw [hΓ, hΓ]
    exact hlocal I u v (by exact hmin) h8 hRm hclear
  have hδpos : ∀ i : Fin d, 0 < δ i := by
    intro i
    exact sub_pos.mpr (hx i)
  have hs_mono_step : ∀ j < n, s j ≤ s (j + 1) := by
    intro j hj
    obtain ⟨_hsmall, i, _hi, _hJnext, _hnearest, hnear | hfar⟩ := hsteps j hj
    · have hcover : s j + δ i ≤ s (j + 1) := hnear.2.1
      linarith [hcover, hδpos i]
    · obtain ⟨v, h8, _hRm, _hclear, hcover, _hscale, _hincl⟩ := hfar
      let R : ℝ := (3 : ℝ) ^ v / 2
      have hRpos : 0 < R := div_pos (zpow_pos (by norm_num) _) (by norm_num)
      have hLR : R ≤ L * R := by
        have h1L : (1 : ℝ) ≤ L := by linarith
        simpa using mul_le_mul_of_nonneg_right h1L (le_of_lt hRpos)
      have h8' : 8 * s j < R := h8
      have hcover' : L * R + δ i ≤ s (j + 1) := hcover
      linarith [h8', hcover', hδpos i, hLR]
  have hs0_le : ∀ j ≤ n, s 0 ≤ s j := by
    intro j hj
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
        exact (ih (Nat.le_of_succ_le hj)).trans
          (hs_mono_step j (Nat.lt_of_succ_le hj))
  have hrmin_s : ∀ j ≤ n, rmin ≤ s j := by
    intro j hj
    exact hrmin.trans (hs0lo.trans (by simpa [s, hk0] using hs0_le j hj))
  have htransition : ∀ j < n, ∃ R : ℝ, 0 < R ∧ s (j + 1) ≤ A * R ∧
      E j ≤ Z * ((s j / R) ^ t * E (j + 1) + (s j) ^ t * F) := by
    intro j hj
    obtain ⟨hsmall, i, hi, hJnext, hnearest, hnear | hfar⟩ := hsteps j hj
    · refine ⟨s j, hspos j, ?_, ?_⟩
      · exact le_of_lt hnear.2.2.1
      · have hmono : E j ≤ E (j + 1) := by
          exact measureReal_mono
            (Set.inter_subset_inter hnear.2.2.2 Set.Subset.rfl) (by finiteness)
        have hsPow : 0 ≤ (s j) ^ t := Real.rpow_nonneg (le_of_lt (hspos j)) _
        have hZ0 : 0 ≤ Z := le_trans zero_le_one hZ
        rw [div_self (ne_of_gt (hspos j)), Real.one_rpow, one_mul]
        calc
          E j ≤ E (j + 1) := hmono
          _ ≤ Z * (E (j + 1) + (s j) ^ t * F) := by
            have hsum : E (j + 1) ≤ E (j + 1) + (s j) ^ t * F :=
              le_add_of_nonneg_right (mul_nonneg hsPow hF)
            exact hsum.trans (by
              simpa only [one_mul] using mul_le_mul_of_nonneg_right hZ
                (add_nonneg (hE (j + 1)) (mul_nonneg hsPow hF)))
    · obtain ⟨v, h8, hRm, hclear, hcover, hscale, hincl⟩ := hfar
      let R : ℝ := (3 : ℝ) ^ v / 2
      have hRp : 0 < R := div_pos (zpow_pos (by norm_num : (0 : ℝ) < 3) v) (by norm_num)
      refine ⟨R, hRp, ?_, ?_⟩
      · calc
          s (j + 1) ≤ 39 * L * R := le_of_lt hscale
          _ ≤ A * R := by
            apply mul_le_mul_of_nonneg_right _ hRp.le
            dsimp [A]
            nlinarith
      · calc
          E j ≤ Z * ((s j / R) ^ t * Γ.real (Metric.ball (z (J j)) (L * R) ∩ Q) + (s j) ^ t * F) :=
            hlocalΓ (J j) (k j) v (hrmin_s j (Nat.le_of_lt hj)) h8 (le_of_lt hRm) hclear
          _ ≤ Z * ((s j / R) ^ t * E (j + 1) + (s j) ^ t * F) := by
            apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hZ)
            have hmass : Γ.real (Metric.ball (z (J j)) (L * R) ∩ Q) ≤ E (j + 1) := by
              exact measureReal_mono (μ := Γ)
                (Set.inter_subset_inter hincl Set.Subset.rfl)
            exact add_le_add_left
              (mul_le_mul_of_nonneg_left hmass
                (Real.rpow_nonneg (div_nonneg (hspos j).le hRp.le) t)) _
  have htransition' : ∀ j : ℕ, ∃ R : ℝ, 0 < R ∧
      (j < n → s (j + 1) ≤ A * R) ∧
      (j < n → E j ≤ Z * ((s j / R) ^ t * E (j + 1) + (s j) ^ t * F)) := by
    intro j
    by_cases hj : j < n
    · obtain ⟨R, hR, hnxt, hst⟩ := htransition j hj
      exact ⟨R, hR, fun _ => hnxt, fun _ => hst⟩
    · exact ⟨1, zero_lt_one, fun h => (hj h).elim, fun h => (hj h).elim⟩
  choose R hRpos hnext hstep using htransition'
  have hcomp := finite_radius_energy_composition n t ht s R E
      (fun _ => Z) (fun _ => A) (fun _ => F)
      (fun j _ => hspos j) (fun j _ => hRpos j)
      (fun j _ => hE j) (fun _ _ => hZ) (fun _ _ => hA) (fun _ _ => hF)
      (fun j hj => hnext j hj) (fun j hj => hstep j hj)
  have hprod : (∏ j ∈ Finset.range n, Z * A ^ t) = (Z * A ^ t) ^ n := by
    simp
  have hsum : (∑ _j ∈ Finset.range n, F) = (n : ℝ) * F := by simp
  rw [hprod, hsum] at hcomp
  have hterminalBound : E n / (s n) ^ t ≤
      Z * ((24 / Rstar) ^ t * Γ.real Q + F) := by
    rcases hterminal with hlarge | hadm
    · have hmono : E n ≤ Γ.real Q := measureReal_mono inter_subset_right
      have hscale : 1 / (s n) ^ t ≤ (24 / Rstar) ^ t := by
        have hlarge' := hlarge
        change Rstar / 24 ≤ s n at hlarge'
        have hden : 1 / s n ≤ 24 / Rstar := by
          rw [div_le_div_iff₀ (hspos n) hRstar]
          nlinarith
        calc
          1 / (s n) ^ t = (1 / s n) ^ t := by
            rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (hspos n).le, Real.one_rpow]
          _ ≤ (24 / Rstar) ^ t := Real.rpow_le_rpow (by positivity) hden ht
      calc
        E n / (s n) ^ t = E n * (1 / (s n) ^ t) := by ring
        _ ≤ Γ.real Q * (24 / Rstar) ^ t := by
          have hinv : 0 ≤ 1 / (s n) ^ t := by positivity
          have hmassQ : 0 ≤ Γ.real Q := measureReal_nonneg
          exact mul_le_mul hmono hscale hinv hmassQ
        _ ≤ Z * ((24 / Rstar) ^ t * Γ.real Q + F) := by
          let H : ℝ := (24 / Rstar) ^ t * Γ.real Q
          have hH : 0 ≤ H := mul_nonneg (Real.rpow_nonneg (by positivity) t) measureReal_nonneg
          have hHF : H ≤ H + F := le_add_of_nonneg_right hF
          have hZHF : H + F ≤ Z * (H + F) :=
            by simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hZ (add_nonneg hH hF)
          simpa only [H, mul_comm] using hHF.trans hZHF
    · have hloc := hlocalΓ (J n) (k n) m (hrmin_s n le_rfl) hadm.1 le_rfl hadm.2
      have hmono : Γ.real (Metric.ball (z (J n)) (L * Rstar) ∩ Q) ≤ Γ.real Q :=
        measureReal_mono inter_subset_right
      have hratio : (s n / Rstar) ^ t / (s n) ^ t = (1 / Rstar) ^ t := by
        rw [Real.div_rpow (hspos n).le hRstar.le,
          Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hRstar.le, Real.one_rpow]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos (hspos n) t),
          ne_of_gt (Real.rpow_pos_of_pos hRstar t)]
      calc
        E n / (s n) ^ t ≤ (Z * ((s n / Rstar) ^ t * Γ.real (Metric.ball (z (J n)) (L * Rstar) ∩ Q) + (s n) ^ t * F)) / (s n) ^ t :=
          div_le_div_of_nonneg_right hloc (Real.rpow_nonneg (le_of_lt (hspos n)) t)
        _ = Z * ((1 / Rstar) ^ t * Γ.real (Metric.ball (z (J n)) (L * Rstar) ∩ Q) + F) := by
          rw [mul_div_assoc, add_div, mul_div_assoc]
          have hterm : (s n / Rstar) ^ t *
                (Γ.real (Metric.ball (z (J n)) (L * Rstar) ∩ Q) / (s n) ^ t) =
              (1 / Rstar) ^ t * Γ.real (Metric.ball (z (J n)) (L * Rstar) ∩ Q) := by
            calc
              _ = ((s n / Rstar) ^ t / (s n) ^ t) *
                  Γ.real (Metric.ball (z (J n)) (L * Rstar) ∩ Q) := by ring
              _ = _ := by rw [hratio]
          rw [hterm]
          field_simp [ne_of_gt (Real.rpow_pos_of_pos (hspos n) t)]
        _ ≤ Z * ((24 / Rstar) ^ t * Γ.real Q + F) := by
          apply mul_le_mul_of_nonneg_left _ (le_trans zero_le_one hZ)
          have h24 : (1 : ℝ) / Rstar ≤ 24 / Rstar :=
            div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 24) hRstar.le
          exact add_le_add_left
            (mul_le_mul (Real.rpow_le_rpow (by positivity) h24 ht)
              hmono measureReal_nonneg (Real.rpow_nonneg (by positivity) t)) F
  have hbase : 1 ≤ Z * A ^ t := by
    simpa only [one_mul] using
      mul_le_mul hZ (Real.one_le_rpow hA ht) zero_le_one (le_trans zero_le_one hZ)
  have hpow : (Z * A ^ t) ^ n ≤ (Z * A ^ t) ^ d := pow_le_pow_right₀ hbase hn
  have hEnBound : E n / (s n) ^ t + (n : ℝ) * F ≤
      Z * ((24 / Rstar) ^ t * Γ.real Q + (d + 1 : ℝ) * F) := by
    have hnR : (n : ℝ) ≤ d := Nat.cast_le.2 hn
    have hndF : (n : ℝ) * F ≤ (d : ℝ) * F :=
      mul_le_mul_of_nonneg_right hnR hF
    have hsource : (n : ℝ) * F ≤ Z * ((d : ℝ) * F) :=
      hndF.trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hZ
          (mul_nonneg (Nat.cast_nonneg d) hF))
    nlinarith [hterminalBound]
  have hE0 : E 0 ≤ (s 0) ^ t * (Z * A ^ t) ^ d * Z *
      ((24 / Rstar) ^ t * Γ.real Q + (d + 1 : ℝ) * F) := by
    calc
      E 0 ≤ (s 0) ^ t * (Z * A ^ t) ^ n * (E n / (s n) ^ t + (n : ℝ) * F) := hcomp
      _ ≤ (s 0) ^ t * (Z * A ^ t) ^ d * (Z * ((24 / Rstar) ^ t * Γ.real Q + (d + 1 : ℝ) * F)) := by
        gcongr
      _ = _ := by ring
  calc
    localGradientEnergy a (Metric.isOpen_ball.measurableSet.inter Metric.isOpen_ball.measurableSet) g =
        Γ.real (Metric.ball x r ∩ Q) := (hΓ _ _).symm
    _ ≤ E 0 := by
      change Γ.real (Metric.ball x r ∩ Q) ≤ Γ.real (Metric.ball (z (J 0)) (s 0) ∩ Q)
      have hcenter : z (J 0) = x := by
        rw [hJ0]
        ext j
        simp [z]
      have hszero : s 0 = (3 : ℝ) ^ q / 2 := by simp [s, hk0]
      exact measureReal_mono (μ := Γ) (by
        rw [hcenter, hszero]
        exact Set.inter_subset_inter (Metric.ball_subset_ball hs0lo) Set.Subset.rfl) (by finiteness)
    _ ≤ (s 0) ^ t * (Z * A ^ t) ^ d * Z * ((24 / Rstar) ^ t * Γ.real Q + (d + 1 : ℝ) * F) := hE0
    _ ≤ (3 * r) ^ t * (Z * A ^ t) ^ d * Z * ((24 / Rstar) ^ t * Γ.real Q + (d + 1 : ℝ) * F) := by
      gcongr
      have hs0hi' : s 0 < 3 * r := by simpa [s, hk0] using hs0hi
      exact le_of_lt hs0hi'
    _ = _ := by
      rw [← hΓ Q Metric.isOpen_ball.measurableSet]

end SubdiffusiveProcess
