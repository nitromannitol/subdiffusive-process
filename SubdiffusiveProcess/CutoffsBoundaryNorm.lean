module

public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Lane4.CubeDilation
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Tactic

@[expose] public section

open SubdiffusiveProcess Homogenization Set
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Lane4
open scoped ContDiff

noncomputable section
namespace SubdiffusiveProcess

private theorem cutoffs_boundary_cubeDilation_eq {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (x : SpatialCoordinates d) : cubeDilation z 0 r x = z + r • x := by
  funext i
  simp [cubeDilation]

private theorem cutoffs_boundary_mem_frontier {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (y : SpatialCoordinates d) :
    y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)) ↔ dist y z = r / 2 := by
  change y ∈ frontier (Metric.ball z (r / 2)) ↔ _
  rw [frontier_ball z (by positivity : r / 2 ≠ 0)]
  rfl

private lemma cutoffs_boundary_cAlpha_bound
    {d : ℕ} (b : ℝ) (hb : 0 < b) (S : Set (SpatialCoordinates d))
    (q : SpatialCoordinates d → ℝ) (E C : ℝ) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hval : ∀ x ∈ S, |q x| ≤ E)
    (hpair : ∀ x ∈ S, ∀ y ∈ S,
      |q x - q y| ≤ C * (dist x y)^b) :
    Lane4.cAlphaNorm b S q ≤ E + C := by
  unfold Lane4.cAlphaNorm Lane4.holderSeminorm
  apply add_le_add
  · apply Real.sSup_le
    · intro v hv
      rcases hv with ⟨x, hx, rfl⟩
      exact hval x hx
    · exact hE
  · apply Real.sSup_le
    · intro v hv
      rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
      let R : ℝ := Real.sqrt (∑ i : Fin d, (x i - y i)^2)
      have hRpos : 0 < R := by
        dsimp [R]
        apply Real.sqrt_pos.mpr
        have hne : ∃ i : Fin d, x i - y i ≠ 0 := by
          by_contra hn
          apply hxy
          funext i
          have hi : x i - y i = 0 := by
            by_contra hi
            exact hn ⟨i, hi⟩
          linarith
        obtain ⟨i, hi⟩ := hne
        apply Finset.sum_pos'
        · intro j _
          exact sq_nonneg _
        · exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
      have hRE : dist x y ≤ R := by
        simpa [R, Homogenization.euclideanNorm, Homogenization.vecNormSq,
          Homogenization.vecDot, dist_eq_norm, Pi.sub_apply, pow_two] using
          (Homogenization.norm_le_euclideanNorm (x - y))
      have hquot : |q x - q y| / R ^ b ≤ C := by
        apply (div_le_iff₀ (Real.rpow_pos_of_pos hRpos b)).2
        exact (hpair x hx y hy).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow dist_nonneg hRE (le_of_lt hb)) hC)
      exact hquot
    · exact hC

private lemma cutoffs_boundary_direct_isHolderOn
    {d : ℕ} {b : ℝ} (hb : 0 < b) (S : Set (SpatialCoordinates d))
    (f : SpatialCoordinates d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hpair : ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ C * (dist x y)^b) :
    Lane4.IsHolderOn b S f := by
  unfold Lane4.IsHolderOn
  refine ⟨C, ?_⟩
  intro v hv
  rcases hv with ⟨x, hx, y, hy, hxy, rfl⟩
  let R : ℝ := Real.sqrt (∑ i : Fin d, (x i - y i)^2)
  have hRpos : 0 < R := by
    dsimp [R]
    apply Real.sqrt_pos.mpr
    have hne : ∃ i : Fin d, x i - y i ≠ 0 := by
      by_contra hn
      apply hxy
      funext i
      have hi : x i - y i = 0 := by
        by_contra hi
        exact hn ⟨i, hi⟩
      linarith
    obtain ⟨i, hi⟩ := hne
    apply Finset.sum_pos'
    · intro j _
      exact sq_nonneg _
    · exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hRE : dist x y ≤ R := by
    simpa [R, Homogenization.euclideanNorm, Homogenization.vecNormSq,
      Homogenization.vecDot, dist_eq_norm, Pi.sub_apply, pow_two] using
      (Homogenization.norm_le_euclideanNorm (x - y))
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hRpos b)).2
  exact (hpair x hx y hy).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg hRE hb.le) hC)


/-- The derivative hypothesis in the frozen collar clause gives a global
Lipschitz estimate in the actual spatial (sup) norm. -/
theorem aux_cutoffs_boundary_global_lipschitz {d : ℕ}
    (rho Cgrad : ℝ) (_hrho : 0 < rho)
    (thetaR : SpatialCoordinates d → ℝ)
    (hsmooth : ContDiff ℝ ∞ thetaR)
    (hgrad : ∀ x, ‖fderiv ℝ thetaR x‖ ≤ Cgrad / rho) :
    ∀ x y, |thetaR x - thetaR y| ≤ Cgrad / rho * dist x y := by
  have hdiff : ∀ x : SpatialCoordinates d, DifferentiableAt ℝ thetaR x :=
    fun x => (hsmooth.differentiable (by simp)).differentiableAt
  intro x y
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := (Set.univ : Set (SpatialCoordinates d)))
    (fun x _ => hdiff x) (fun x _ => hgrad x) convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs, dist_eq_norm] using h


/-- The rescaled datum has the same Lipschitz constant on the unit cube. -/
theorem aux_cutoffs_boundary_rescaled_lipschitz {d : ℕ}
    (z : SpatialCoordinates d) (rho Cgrad : ℝ) (hrho : 0 < rho)
    (thetaR : SpatialCoordinates d → ℝ)
    (hsmooth : ContDiff ℝ ∞ thetaR)
    (hgrad : ∀ x, ‖fderiv ℝ thetaR x‖ ≤ Cgrad / rho) :
    ∀ x y : SpatialCoordinates d,
      |rescaledDatum z rho thetaR x - rescaledDatum z rho thetaR y| ≤
        Cgrad * dist x y := by
  intro x y
  have h := aux_cutoffs_boundary_global_lipschitz rho Cgrad hrho thetaR hsmooth hgrad
    (cubeDilation z 0 rho x) (cubeDilation z 0 rho y)
  have hdist :
      dist (cubeDilation z 0 rho x) (cubeDilation z 0 rho y) =
        rho * dist x y := by
    rw [cutoffs_boundary_cubeDilation_eq, cutoffs_boundary_cubeDilation_eq,
      dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hrho]
  rw [hdist] at h
  have heq (u : SpatialCoordinates d) :
      cubeDilation z 0 rho u = (fun i => z i + rho * u i) := by
    funext i
    simp [cubeDilation]
  rw [heq x, heq y] at h
  have h' : |rescaledDatum z rho thetaR x - rescaledDatum z rho thetaR y| ≤
      Cgrad / rho * (rho * dist x y) := by
    exact h
  calc
    |rescaledDatum z rho thetaR x - rescaledDatum z rho thetaR y| ≤
        Cgrad / rho * (rho * dist x y) := h'
    _ = Cgrad * dist x y := by
      field_simp


private theorem aux_cutoffs_unit_frontier_diam {d : ℕ}
    {x y : SpatialCoordinates d}
    (hx : x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)))
    (hy : y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))) : dist x y ≤ 1 := by
  have hx' := (cutoffs_boundary_mem_frontier 0 one_pos x).mp hx
  have hy' := (cutoffs_boundary_mem_frontier 0 one_pos y).mp hy
  calc
    dist x y ≤ dist x 0 + dist 0 y := dist_triangle x 0 y
    _ = 1 := by rw [hx', dist_comm 0 y, hy']; norm_num

theorem aux_cutoffs_boundary_rescaled_holder_pair {d : ℕ}
    (z : SpatialCoordinates d) (rho Cgrad beta : ℝ)
    (hrho : 0 < rho) (hCgrad : 0 ≤ Cgrad) (hbeta : beta ≤ 1)
    (thetaR : SpatialCoordinates d → ℝ)
    (hsmooth : ContDiff ℝ ∞ thetaR)
    (hgrad : ∀ x, ‖fderiv ℝ thetaR x‖ ≤ Cgrad / rho) :
    ∀ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)),
    ∀ y ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)),
      |rescaledDatum z rho thetaR x - rescaledDatum z rho thetaR y| ≤
        Cgrad * (dist x y) ^ beta := by
  intro x hx y hy
  have hdist := aux_cutoffs_unit_frontier_diam hx hy
  calc
    _ ≤ Cgrad * dist x y :=
      aux_cutoffs_boundary_rescaled_lipschitz z rho Cgrad hrho thetaR hsmooth hgrad x y
    _ ≤ Cgrad * (dist x y) ^ beta :=
      mul_le_mul_of_nonneg_left
        (Real.self_le_rpow_of_le_one dist_nonneg hdist hbeta) hCgrad


theorem aux_cutoffs_boundary_class_and_norm {d : ℕ}
    (z : SpatialCoordinates d) (rho Cgrad beta : ℝ)
    (hrho : 0 < rho) (hCgrad : 0 ≤ Cgrad)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (thetaR : SpatialCoordinates d → ℝ)
    (hsmooth : ContDiff ℝ ∞ thetaR)
    (hrange : ∀ x, 0 ≤ thetaR x ∧ thetaR x ≤ 1)
    (hgrad : ∀ x, ‖fderiv ℝ thetaR x‖ ≤ Cgrad / rho) :
    IsCellBoundaryClass beta z rho thetaR ∧
      cellBoundaryQuotientNorm beta z rho thetaR ≤ 1 + Cgrad := by
  let S : Set (SpatialCoordinates d) :=
    frontier (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d))
  let G := rescaledDatum z rho thetaR
  have hpair : ∀ x ∈ S, ∀ y ∈ S,
      |G x - G y| ≤ Cgrad * (dist x y) ^ beta :=
    aux_cutoffs_boundary_rescaled_holder_pair z rho Cgrad beta hrho hCgrad
      hbeta1 thetaR hsmooth hgrad
  have hval : ∀ x ∈ S, |G x| ≤ 1 := by
    intro x _
    change |thetaR (fun i => z i + rho * x i)| ≤ 1
    exact abs_le.mpr ⟨by linarith [(hrange (fun i => z i + rho * x i)).1],
      (hrange (fun i => z i + rho * x i)).2⟩
  have hholder : Lane4.IsHolderOn beta S G :=
    cutoffs_boundary_direct_isHolderOn hbeta0 S G Cgrad hCgrad hpair
  have hvals : BddAbove {v : ℝ | ∃ x ∈ S, v = |G x|} := by
    refine ⟨1, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    exact hval x hx
  have hnorm : Lane4.cAlphaNorm beta S G ≤ 1 + Cgrad :=
    cutoffs_boundary_cAlpha_bound beta hbeta0 S G 1 Cgrad
      (by norm_num) hCgrad hval hpair
  constructor
  · exact ⟨hholder, hvals⟩
  · have hbelow : BddBelow {v : ℝ | ∃ c : ℝ,
        v = Lane4.cAlphaNorm beta S (fun x => G x - c)} := by
      refine ⟨0, ?_⟩
      rintro v ⟨c, rfl⟩
      unfold Lane4.cAlphaNorm Lane4.holderSeminorm
      apply add_nonneg
      · apply Real.sSup_nonneg
        rintro w ⟨x, hx, rfl⟩
        exact abs_nonneg _
      · apply Real.sSup_nonneg
        rintro w ⟨x, hx, y, hy, hxy, rfl⟩
        exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    have hq : quotientCBetaNorm beta S G ≤ Lane4.cAlphaNorm beta S G := by
      unfold quotientCBetaNorm
      apply csInf_le hbelow
      exact ⟨0, by simp⟩
    exact hq.trans hnorm


end SubdiffusiveProcess
