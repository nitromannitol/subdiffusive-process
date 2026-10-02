import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.Convergence

/-!
# Lipschitz seminorm convergence of the anchored coefficient gradients

The product `ã_L ∇log ã_L` is handled on closed balls, where the mean value
inequality converts the uniform derivative bounds into Lipschitz bounds; an
arbitrary compact window is then covered by one ball.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open Filter SubdiffusiveProcess.Frozen.Assumptions Homogenization Topology

noncomputable section

variable {d : ℕ} (M : GMCModel d) (omega : AnchoredC11Sample d)

/-- The coefficient gradients converge in the Lipschitz seminorm of every
closed ball. -/
theorem exists_lipschitzOnWith_cutoffDeriv_sub_closedBall (R : ℝ)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ N : ℕ, ∀ L : ℕ, N ≤ L →
      LipschitzOnWith (Real.toNNReal eps)
        (fun x => cutoffDeriv M omega L x - limitDeriv M omega x)
        (Metric.closedBall (0 : Vec d) R) := by
  set S : Set (Vec d) := Metric.closedBall (0 : Vec d) R with hSdef
  have hScompact : IsCompact S := isCompact_closedBall _ _
  have hSconvex : Convex ℝ S := convex_closedBall _ _
  obtain ⟨A, hA0, hA⟩ := exists_bound_aAnchored M omega hScompact
  obtain ⟨Bd, hBd0, hBd⟩ := exists_bound_anchoredLog_deriv omega hScompact
  obtain ⟨C, hC⟩ := (anchoredLog omega).2.2 S hScompact
  set ca : ℝ := (A + 1) * (Bd + 1) with hca
  have hca0 : 0 ≤ ca := by positivity
  set Theta : ℝ := ca + A + 1 + Bd + (C : ℝ) + 1 with hTheta
  have hThetaPos : 0 < Theta := by
    have : (0 : ℝ) ≤ (C : ℝ) := C.coe_nonneg
    simp only [hTheta]
    linarith
  set delta : ℝ := eps / Theta with hdeltaDef
  have hdelta : 0 < delta := div_pos heps hThetaPos
  -- eventual uniform bounds
  have h1 : ∀ᶠ L in atTop, ∀ x ∈ S, ‖anchoredCutoff M L omega.1 x‖ ≤ A + 1 :=
    eventually_norm_le_of_tendstoUniformlyOn hA
      (tendstoUniformlyOn_anchoredCutoff M omega hScompact)
  have h2 : ∀ᶠ L in atTop, ∀ x ∈ S,
      ‖PotentialField.deriv (anchoredPartialSumField omega.1 L) x‖ ≤ Bd + 1 :=
    eventually_norm_le_of_tendstoUniformlyOn hBd
      (tendstoUniformlyOn_deriv omega hScompact)
  have h3 : ∀ᶠ L in atTop, ∀ x ∈ S,
      ‖PotentialField.deriv (anchoredPartialSumField omega.1 L) x -
        PotentialField.deriv (anchoredLog omega) x‖ ≤ delta := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1
      (tendstoUniformlyOn_deriv omega hScompact) delta hdelta] with L hL x hx
    have := hL x hx
    rw [dist_eq_norm] at this
    rw [← norm_neg]
    simpa only [neg_sub] using this.le
  have h4 : ∀ᶠ L in atTop, ∀ x ∈ S,
      ‖cutoffDeriv M omega L x - limitDeriv M omega x‖ ≤ delta := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1
      (tendstoUniformlyOn_cutoffDeriv M omega hScompact) delta hdelta]
      with L hL x hx
    have := hL x hx
    rw [dist_eq_norm] at this
    rw [← norm_neg]
    simpa only [neg_sub] using this.le
  have h5 : ∀ᶠ L in atTop, ∀ x ∈ S,
      |anchoredCutoff M L omega.1 x - aAnchored M omega x| ≤ delta := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1
      (tendstoUniformlyOn_anchoredCutoff M omega hScompact) delta hdelta]
      with L hL x hx
    have := hL x hx
    rw [Real.dist_eq] at this
    rw [← abs_neg]
    simpa only [neg_sub] using this.le
  obtain ⟨N0, hN0⟩ := exists_lipschitzOnWith_deriv_sub omega hScompact hdelta
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (h1.and (h2.and (h3.and (h4.and h5))))
  refine ⟨max N0 N1, fun L hL => ?_⟩
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hN1 L (le_trans (le_max_right _ _) hL)
  have hlip := hN0 L (le_trans (le_max_left _ _) hL)
  have hdeltaCoe : ((Real.toNNReal delta : NNReal) : ℝ) = delta :=
    Real.coe_toNNReal delta hdelta.le
  -- the two factorised pieces
  have hmvt1 : ∀ x ∈ S, ∀ y ∈ S,
      |anchoredCutoff M L omega.1 x - anchoredCutoff M L omega.1 y| ≤
        ca * dist x y := by
    intro x hx y hy
    have hbound : ∀ z ∈ S, ‖cutoffDeriv M omega L z‖ ≤ ca := by
      intro z hz
      rw [cutoffDeriv, norm_smul, Real.norm_eq_abs]
      refine mul_le_mul ?_ (hb2 z hz) (norm_nonneg _) (by positivity)
      simpa only [Real.norm_eq_abs] using hb1 z hz
    have hstep := hSconvex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun y => anchoredCutoff M L omega.1 y) (f' := cutoffDeriv M omega L)
      (fun z hz => (hasFDerivAt_anchoredCutoff M omega L z).hasFDerivWithinAt)
      hbound hy hx
    simpa only [Real.norm_eq_abs, dist_eq_norm] using hstep
  have hmvt2 : ∀ x ∈ S, ∀ y ∈ S,
      |(anchoredCutoff M L omega.1 x - aAnchored M omega x) -
        (anchoredCutoff M L omega.1 y - aAnchored M omega y)| ≤
        delta * dist x y := by
    intro x hx y hy
    have hstep := hSconvex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun y => anchoredCutoff M L omega.1 y - aAnchored M omega y)
      (f' := fun z => cutoffDeriv M omega L z - limitDeriv M omega z)
      (fun z _ => ((hasFDerivAt_anchoredCutoff M omega L z).sub
        (hasFDerivAt_aAnchored M omega z)).hasFDerivWithinAt)
      hb4 hy hx
    simpa only [Real.norm_eq_abs, dist_eq_norm] using hstep
  have hpsi1 : ∀ x ∈ S, ∀ y ∈ S,
      ‖(PotentialField.deriv (anchoredPartialSumField omega.1 L) x -
          PotentialField.deriv (anchoredLog omega) x) -
        (PotentialField.deriv (anchoredPartialSumField omega.1 L) y -
          PotentialField.deriv (anchoredLog omega) y)‖ ≤ delta * dist x y := by
    intro x hx y hy
    have := hlip.dist_le_mul x hx y hy
    rw [dist_eq_norm] at this
    rw [hdeltaCoe] at this
    exact this
  have hpsi2 : ∀ x ∈ S, ∀ y ∈ S,
      ‖PotentialField.deriv (anchoredLog omega) x -
        PotentialField.deriv (anchoredLog omega) y‖ ≤ (C : ℝ) * dist x y := by
    intro x hx y hy
    have := hC.dist_le_mul x hx y hy
    rwa [dist_eq_norm] at this
  -- assemble
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hsplit : ∀ z : Vec d,
      cutoffDeriv M omega L z - limitDeriv M omega z =
        anchoredCutoff M L omega.1 z •
            (PotentialField.deriv (anchoredPartialSumField omega.1 L) z -
              PotentialField.deriv (anchoredLog omega) z) +
          (anchoredCutoff M L omega.1 z - aAnchored M omega z) •
            PotentialField.deriv (anchoredLog omega) z := by
    intro z
    simp only [cutoffDeriv, limitDeriv]
    module
  have hterm1 := dist_smul_sub_smul_le
    (φ := fun z => anchoredCutoff M L omega.1 z)
    (ψ := fun z => PotentialField.deriv (anchoredPartialSumField omega.1 L) z -
      PotentialField.deriv (anchoredLog omega) z)
    (S := S) (ca := ca) (cb := delta) (A := A + 1) (B := delta)
    hmvt1 hpsi1 (fun z hz => by simpa only [Real.norm_eq_abs] using hb1 z hz)
    hb3 x hx y hy
  have hterm2 := dist_smul_sub_smul_le
    (φ := fun z => anchoredCutoff M L omega.1 z - aAnchored M omega z)
    (ψ := fun z => PotentialField.deriv (anchoredLog omega) z)
    (S := S) (ca := delta) (cb := (C : ℝ)) (A := delta) (B := Bd)
    hmvt2 hpsi2 hb5 hBd x hx y hy
  have hbig : dist (cutoffDeriv M omega L x - limitDeriv M omega x)
      (cutoffDeriv M omega L y - limitDeriv M omega y) ≤
      (ca * delta + (A + 1) * delta) * dist x y +
        (delta * Bd + delta * (C : ℝ)) * dist x y := by
    rw [dist_eq_norm, hsplit x, hsplit y]
    refine le_trans ?_ (add_le_add hterm1 hterm2)
    have : (anchoredCutoff M L omega.1 x •
          (PotentialField.deriv (anchoredPartialSumField omega.1 L) x -
            PotentialField.deriv (anchoredLog omega) x) +
        (anchoredCutoff M L omega.1 x - aAnchored M omega x) •
          PotentialField.deriv (anchoredLog omega) x) -
        (anchoredCutoff M L omega.1 y •
          (PotentialField.deriv (anchoredPartialSumField omega.1 L) y -
            PotentialField.deriv (anchoredLog omega) y) +
        (anchoredCutoff M L omega.1 y - aAnchored M omega y) •
          PotentialField.deriv (anchoredLog omega) y) =
        (anchoredCutoff M L omega.1 x •
          (PotentialField.deriv (anchoredPartialSumField omega.1 L) x -
            PotentialField.deriv (anchoredLog omega) x) -
          anchoredCutoff M L omega.1 y •
          (PotentialField.deriv (anchoredPartialSumField omega.1 L) y -
            PotentialField.deriv (anchoredLog omega) y)) +
        ((anchoredCutoff M L omega.1 x - aAnchored M omega x) •
          PotentialField.deriv (anchoredLog omega) x -
          (anchoredCutoff M L omega.1 y - aAnchored M omega y) •
          PotentialField.deriv (anchoredLog omega) y) := by abel
    rw [this]
    exact norm_add_le _ _
  refine hbig.trans ?_
  have hcoe : ((Real.toNNReal eps : NNReal) : ℝ) = eps :=
    Real.coe_toNNReal eps heps.le
  rw [hcoe]
  have hdist0 : (0 : ℝ) ≤ dist x y := dist_nonneg
  have hCnn : (0 : ℝ) ≤ (C : ℝ) := C.coe_nonneg
  have hsum : ca * delta + (A + 1) * delta + (delta * Bd + delta * (C : ℝ)) ≤ eps := by
    have hle : ca * delta + (A + 1) * delta + (delta * Bd + delta * (C : ℝ)) ≤
        Theta * delta := by
      rw [hTheta]
      nlinarith [hdelta.le]
    have heq : Theta * delta = eps := by
      rw [hdeltaDef]
      field_simp
    linarith [hle, heq.le, heq.ge]
  calc (ca * delta + (A + 1) * delta) * dist x y +
        (delta * Bd + delta * (C : ℝ)) * dist x y
      = (ca * delta + (A + 1) * delta + (delta * Bd + delta * (C : ℝ))) * dist x y := by
        ring
    _ ≤ eps * dist x y := mul_le_mul_of_nonneg_right hsum hdist0

/-- The coefficient gradients converge in the Lipschitz seminorm of every
compact window. -/
theorem exists_lipschitzOnWith_coefficientGradient_sub {K : Set (Vec d)}
    (hK : IsCompact K) {eps : ℝ} (heps : 0 < eps) :
    ∃ N : ℕ, ∀ L : ℕ, N ≤ L →
      LipschitzOnWith (Real.toNNReal eps)
        (fun x => anchoredCutoff M L omega.1 x •
            shellGradient (anchoredPartialSumField omega.1 L) x -
          aAnchored M omega x • shellGradient (anchoredLog omega) x) K := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Vec d)
  obtain ⟨N, hN⟩ := exists_lipschitzOnWith_cutoffDeriv_sub_closedBall M omega R heps
  refine ⟨N, fun L hL => ?_⟩
  have hball := lipschitzOnWith_gradOfCLM_comp (hN L hL)
  have hfun : (fun x => gradOfCLM (cutoffDeriv M omega L x - limitDeriv M omega x)) =
      fun x => anchoredCutoff M L omega.1 x •
          shellGradient (anchoredPartialSumField omega.1 L) x -
        aAnchored M omega x • shellGradient (anchoredLog omega) x := by
    funext x
    rw [gradOfCLM_sub, gradOfCLM_cutoffDeriv, gradOfCLM_limitDeriv]
  rw [hfun] at hball
  exact hball.mono hR

/-! ### The two printed convergence blocks -/



theorem anchoredCutoff_locally_C11 (K : Set (Vec d)) (hK : IsCompact K) :
    TendstoUniformlyOn (fun L x => anchoredCutoff M L omega.1 x)
        (aAnchored M omega) atTop K ∧
      TendstoUniformlyOn
        (fun L x => anchoredCutoff M L omega.1 x •
          shellGradient (anchoredPartialSumField omega.1 L) x)
        (fun x => aAnchored M omega x • shellGradient (anchoredLog omega) x)
        atTop K ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ L : ℕ, N ≤ L →
        LipschitzOnWith (Real.toNNReal epsilon)
          (fun x => anchoredCutoff M L omega.1 x •
              shellGradient (anchoredPartialSumField omega.1 L) x -
            aAnchored M omega x • shellGradient (anchoredLog omega) x) K :=
  ⟨tendstoUniformlyOn_anchoredCutoff M omega hK,
    tendstoUniformlyOn_coefficientGradient M omega hK,
    fun _ heps => exists_lipschitzOnWith_coefficientGradient_sub M omega hK heps⟩



theorem anchoredLogGradient_locally_C01 (K : Set (Vec d)) (hK : IsCompact K) :
    TendstoUniformlyOn
        (fun L x => shellGradient (anchoredPartialSumField omega.1 L) x)
        (shellGradient (anchoredLog omega)) atTop K ∧
      ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ L : ℕ, N ≤ L →
        LipschitzOnWith (Real.toNNReal epsilon)
          (fun x => shellGradient (anchoredPartialSumField omega.1 L) x -
            shellGradient (anchoredLog omega) x) K :=
  ⟨tendstoUniformlyOn_shellGradient omega hK,
    fun _ heps => exists_lipschitzOnWith_shellGradient_sub omega hK heps⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
