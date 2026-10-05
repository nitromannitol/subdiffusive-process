module

public import SubdiffusiveProcess.CoarseGrainingVocab.AnnealedMatrixBoundsSupport
public import SubdiffusiveProcess.CoarseGrainingVocab.PrefixSuffixMeasurability

@[expose] public section

/-!
# Variational cutoff ordering at a fixed domain

This module packages the coefficient-prefix Jensen step in the proof of
`l.annealed.matrix.bounds`.  The proof route mirrors the separation between
fixed-competitor energies and annealed assembly in
`Algsuperdiff/Section3/Provider/Annealed/Monotonicity.lean`, with the cutoff
index replacing Superdiffusion's cube index.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open MeasureTheory ProbabilityTheory Homogenization Homogenization.Book
open scoped Matrix.Norms.Elementwise MatrixOrder

noncomputable section

private abbrev Sample (d : ℕ) :=
  _root_.SubdiffusiveProcess.Model.PotentialSample d

/-- Pure-potential doubled `Mu` is the primal cutoff quadratic form. -/
theorem cutoffMu_primal_eq_randomAMatrix_quadratic {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Mu (U : Set (Vec d)) (-p, 0)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) =
      (1 / 2 : ℝ) * vecDot p (matVecMul (randomAMatrix M L U omega) p) := by
  let hdata := aCutoffCoeffOnData M L omega U
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U hdata.toCoeffOn hdata.isSymmetric
  calc
    Mu (U : Set (Vec d)) (-p, 0)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) =
        Ch02.doubledMu U hdata.toCoeffOn (-p, 0) := by
      rw [Ch02.doubledMu_eq_Mu]
      rfl
    _ = Ch02.responseJ U hdata.toCoeffOn p 0 := by
      rw [Ch02.responseJ_eq_doubledMu_neg_left_sub_vecDot]
      simp [vecDot]
    _ = Ch02.symmetricDirichletNu U hdata.toCoeffOn p := by
      rw [hTheory.response_dirichlet_neumann_split]
      have hzero := hTheory.neumann_value_by_sigmaStarInv (0 : Vec d)
      rw [hzero]
      simp [vecDot, matVecMul]
    _ = (1 / 2 : ℝ) * vecDot p
        (matVecMul (randomAMatrix M L U omega) p) := by
      rw [hTheory.dirichlet_value_by_sigma]
      change _ = (1 / 2 : ℝ) * vecDot p
        (matVecMul (aMatrix U hdata.toCoeffOn) p)
      rw [show aMatrix U hdata.toCoeffOn = Ch02.aCoarse U hdata.toCoeffOn by rfl,
        hTheory.derived_matrices.1]

/-- Pure-flux doubled `Mu` is the inverse-star cutoff quadratic form. -/
theorem cutoffMu_dual_eq_randomAStarInv_quadratic {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (q : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    Mu (U : Set (Vec d)) (0, q)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) =
      (1 / 2 : ℝ) * vecDot q
        (matVecMul ((randomAStarMatrix M L U omega)⁻¹) q) := by
  let hdata := aCutoffCoeffOnData M L omega U
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U hdata.toCoeffOn hdata.isSymmetric
  have hstar : (aStarMatrix U hdata.toCoeffOn)⁻¹ =
      Ch02.sigmaStarInvCoarse U hdata.toCoeffOn := by
    rw [show aStarMatrix U hdata.toCoeffOn = Ch02.aStarCoarse U hdata.toCoeffOn by rfl,
      hTheory.derived_matrices.2.1]
    unfold Ch02.sigmaStarCoarse
    exact Matrix.nonsing_inv_nonsing_inv _
      (Ch02.isUnit_det_sigmaStarInvCoarse U hdata.toCoeffOn)
  calc
    Mu (U : Set (Vec d)) (0, q)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) =
        Ch02.doubledMu U hdata.toCoeffOn (0, q) := by
      rw [Ch02.doubledMu_eq_Mu]
      rfl
    _ = Ch02.responseJ U hdata.toCoeffOn 0 q := by
      rw [Ch02.responseJ_eq_doubledMu_neg_left_sub_vecDot]
      simp [vecDot]
    _ = Ch02.symmetricNeumannNu U hdata.toCoeffOn q := by
      rw [hTheory.response_dirichlet_neumann_split]
      have hzero := hTheory.dirichlet_value_by_sigma (0 : Vec d)
      rw [hzero]
      simp [vecDot, matVecMul]
    _ = (1 / 2 : ℝ) * vecDot q
        (matVecMul ((randomAStarMatrix M L U omega)⁻¹) q) := by
      rw [hTheory.neumann_value_by_sigmaStarInv]
      change _ = (1 / 2 : ℝ) * vecDot q
        (matVecMul ((aStarMatrix U hdata.toCoeffOn)⁻¹) q)
      rw [hstar]

theorem integrable_randomAMatrix_quadratic {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p : Vec d) :
    Integrable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      (1 / 2 : ℝ) * vecDot p (matVecMul (randomAMatrix M L U omega) p))
      M.P.toMeasure := by
  apply Integrable.const_mul
  simp only [vecDot, matVecMul]
  apply integrable_finsetSum Finset.univ
  intro i _hi
  apply Integrable.const_mul
  apply integrable_finsetSum Finset.univ
  intro j _hj
  exact (((integrable_randomAMatrix M L U).eval i).eval j).mul_const (p j)

/-- Annealing a primal random quadratic form gives the corresponding
quadratic form of `abar`. -/
theorem integral_randomAMatrix_quadratic {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p : Vec d) :
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        (1 / 2 : ℝ) * vecDot p (matVecMul (randomAMatrix M L U omega) p)
        ∂M.P.toMeasure =
      (1 / 2 : ℝ) * vecDot p (matVecMul (abar M L U) p) := by
  rw [integral_const_mul]
  congr 1
  simp only [vecDot, matVecMul]
  rw [integral_finsetSum Finset.univ]
  · congr 1
    ext i
    rw [integral_const_mul, integral_finsetSum Finset.univ]
    · simp_rw [integral_mul_const]
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      change (∫ omega, randomAMatrix M L U omega i j ∂M.P.toMeasure) * p j =
        (∫ omega, randomAMatrix M L U omega ∂M.P.toMeasure) i j * p j
      rw [Homogenization.integral_matrix_apply (integrable_randomAMatrix M L U) i j]
    · intro j _hj
      exact (((integrable_randomAMatrix M L U).eval i).eval j).mul_const (p j)
  · intro i _hi
    exact (integrable_finsetSum Finset.univ fun j _hj =>
      (((integrable_randomAMatrix M L U).eval i).eval j).mul_const (p j)).const_mul (p i)

/-- The pure-potential cutoff variational value is integrable. -/
theorem integrable_cutoffMu_primal {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (p : Vec d) :
    Integrable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      Mu (U : Set (Vec d)) (-p, 0)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)))
      M.P.toMeasure := by
  apply (integrable_randomAMatrix_quadratic M L U p).congr
  filter_upwards with omega
  exact (cutoffMu_primal_eq_randomAMatrix_quadratic M L U p omega).symm

private theorem cutoffMu_dual_nonneg {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (q : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d) :
    0 ≤ Mu (U : Set (Vec d)) (0, q)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) := by
  rw [cutoffMu_dual_eq_randomAStarInv_quadratic M L U q omega]
  let hdata := aCutoffCoeffOnData M L omega U
  have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
    U hdata.toCoeffOn hdata.isSymmetric
  have hstar : (randomAStarMatrix M L U omega)⁻¹ =
      Ch02.sigmaStarInvCoarse U hdata.toCoeffOn := by
    change (aStarMatrix U hdata.toCoeffOn)⁻¹ = _
    rw [show aStarMatrix U hdata.toCoeffOn = Ch02.aStarCoarse U hdata.toCoeffOn by rfl,
      hTheory.derived_matrices.2.1]
    unfold Ch02.sigmaStarCoarse
    exact Matrix.nonsing_inv_nonsing_inv _
      (Ch02.isUnit_det_sigmaStarInvCoarse U hdata.toCoeffOn)
  rw [hstar]
  exact mul_nonneg (by norm_num)
    (by simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
      (Ch02.sigmaStarInvCoarse_posDef U hdata.toCoeffOn).posSemidef.dotProduct_mulVec_nonneg q)

/-- The pure-flux cutoff variational value is integrable. -/
theorem integrable_cutoffMu_dual {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (q : Vec d) :
    Integrable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      Mu (U : Set (Vec d)) (0, q)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)))
      M.P.toMeasure := by
  obtain ⟨Y, hY, hYzero, hMu⟩ := cutoffMu_dual_countableReduction M L U q
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    Mu (U : Set (Vec d)) (0, q)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega))
  let g : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    blockEnergyAverage (U : Set (Vec d))
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) (Y 0)
  have hgInt : Integrable g M.P.toMeasure := by
    simpa only [g, hYzero 0] using
      integrable_zeroPotential_blockEnergyAverage M L U (hY 0)
  have hfMeas : AEStronglyMeasurable f M.P.toMeasure :=
    (measurable_cutoff_Mu M L U (0, q)).aestronglyMeasurable
  apply hgInt.mono' hfMeas
  filter_upwards with omega
  have hRange : BddBelow (Set.range fun k =>
      blockEnergyAverage (U : Set (Vec d))
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) (Y k)) := by
    refine ⟨0, ?_⟩
    rintro value ⟨k, rfl⟩
    exact blockEnergyAverage_cutoff_nonneg M L omega U (hY k)
  have hupper : f omega ≤ g omega := by
    dsimp only [f, g]
    rw [hMu omega]
    exact ciInf_le hRange 0
  rw [Real.norm_eq_abs, abs_of_nonneg (cutoffMu_dual_nonneg M L U q omega)]
  exact hupper

/-- Conditional Jensen for the primal variational infimum: after conditioning
on the prefix through `n`, the cutoff-`m` minimum is below the cutoff-`n`
minimum. -/
theorem condExp_cutoffMu_primal_le {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n m : ℕ} (hnm : n < m)
    (U : Ch02.Domain d) (p : Vec d) :
    M.P.toMeasure[(fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      Mu (U : Set (Vec d)) (-p, 0)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega))) |
          potentialIndexSigma (Set.Iic n)] ≤ᵐ[M.P.toMeasure]
      fun omega => Mu (U : Set (Vec d)) (-p, 0)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)) := by
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    Mu (U : Set (Vec d)) (-p, 0)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega))
  obtain ⟨Y, hY, hYzero, hMuN⟩ := cutoffMu_primal_countableReduction M n U p
  have hfInt : Integrable f M.P.toMeasure := integrable_cutoffMu_primal M m U p
  have hEach : ∀ k : ℕ,
      M.P.toMeasure[f | potentialIndexSigma (Set.Iic n)] ≤ᵐ[M.P.toMeasure]
        fun omega => blockEnergyAverage (U : Set (Vec d))
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)) (Y k) := by
    intro k
    let g : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
      blockEnergyAverage (U : Set (Vec d))
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega)) (Y k)
    have hgInt : Integrable g M.P.toMeasure := by
      simpa only [g, hYzero k] using
        integrable_zeroFlux_blockEnergyAverage M m U (hY k)
    have hfg : f ≤ g := by
      intro omega
      let aomega := scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega)
      have hbdd : BddBelow (muValueSet (U : Set (Vec d)) (-p, 0) aomega) := by
        refine ⟨0, ?_⟩
        rintro value ⟨X, hX, rfl⟩
        exact blockEnergyAverage_cutoff_nonneg M m omega U hX
      exact csInf_le hbdd (muValueSet_mem (hY k))
    have hmono := condExp_mono (m := potentialIndexSigma (Set.Iic n))
      hfInt hgInt (ae_of_all M.P.toMeasure hfg)
    have hcond := condExp_zeroFlux_blockEnergyAverage M hnm U (hY k)
    filter_upwards [hmono, hcond] with omega hmonoOmega hcondOmega
    exact hmonoOmega.trans_eq (by
      simpa only [g, hYzero k] using hcondOmega)
  filter_upwards [ae_all_iff.2 hEach] with omega homega
  rw [hMuN omega]
  change M.P.toMeasure[f | potentialIndexSigma (Set.Iic n)] omega ≤ _
  exact le_ciInf homega

/-- Conditional Jensen for the dual variational infimum, with the exact
inverse-shell expectation factor from G3. -/
theorem condExp_cutoffMu_dual_le {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n m : ℕ} (hnm : n < m)
    (U : Ch02.Domain d) (q : Vec d) :
    M.P.toMeasure[(fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d =>
      Mu (U : Set (Vec d)) (0, q)
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega))) |
          potentialIndexSigma (Set.Iic n)] ≤ᵐ[M.P.toMeasure]
      fun omega => Real.exp
          (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ)) *
        Mu (U : Set (Vec d)) (0, q)
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)) := by
  let C := Real.exp
    (2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ))
  have hCpos : 0 < C := Real.exp_pos _
  let f : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    Mu (U : Set (Vec d)) (0, q)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega))
  obtain ⟨Y, hY, hYzero, hMuN⟩ := cutoffMu_dual_countableReduction M n U q
  have hfInt : Integrable f M.P.toMeasure := integrable_cutoffMu_dual M m U q
  have hEach : ∀ k : ℕ,
      M.P.toMeasure[f | potentialIndexSigma (Set.Iic n)] ≤ᵐ[M.P.toMeasure]
        fun omega => C * blockEnergyAverage (U : Set (Vec d))
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)) (Y k) := by
    intro k
    let g : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
      blockEnergyAverage (U : Set (Vec d))
        (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega)) (Y k)
    have hgInt : Integrable g M.P.toMeasure := by
      simpa only [g, hYzero k] using
        integrable_zeroPotential_blockEnergyAverage M m U (hY k)
    have hfg : f ≤ g := by
      intro omega
      let aomega := scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega)
      have hbdd : BddBelow (muValueSet (U : Set (Vec d)) (0, q) aomega) := by
        refine ⟨0, ?_⟩
        rintro value ⟨X, hX, rfl⟩
        exact blockEnergyAverage_cutoff_nonneg M m omega U hX
      exact csInf_le hbdd (muValueSet_mem (hY k))
    have hmono := condExp_mono (m := potentialIndexSigma (Set.Iic n))
      hfInt hgInt (ae_of_all M.P.toMeasure hfg)
    have hcond := condExp_zeroPotential_blockEnergyAverage M hnm U (hY k)
    filter_upwards [hmono, hcond] with omega hmonoOmega hcondOmega
    exact hmonoOmega.trans_eq (by
      simpa only [C, g, hYzero k] using hcondOmega)
  filter_upwards [ae_all_iff.2 hEach] with omega homega
  rw [hMuN omega]
  change M.P.toMeasure[f | potentialIndexSigma (Set.Iic n)] omega ≤
    C * (⨅ k, blockEnergyAverage (U : Set (Vec d))
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega)) (Y k))
  rw [mul_comm C]
  apply (div_le_iff₀ hCpos).1
  exact le_ciInf fun k => (div_le_iff₀ hCpos).2 (by
    simpa only [mul_comm] using homega k)

/-- The inverse random star matrix is integrable entrywise.  The proof uses
the pure-flux variational quadratic forms and polarization, so it does not
introduce a separate matrix-moment assumption. -/
theorem integrable_randomAStarMatrix_inv {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d) :
    Integrable (fun omega : _root_.SubdiffusiveProcess.Model.PotentialSample d => (randomAStarMatrix M L U omega)⁻¹)
      M.P.toMeasure := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩
  apply Integrable.of_eval
  intro i
  apply Integrable.of_eval
  intro j
  by_cases hij : i = j
  · subst j
    have hmu := (integrable_cutoffMu_dual M L U (Pi.single i 1)).const_mul 2
    apply hmu.congr
    filter_upwards with omega
    have hEq := cutoffMu_dual_eq_randomAStarInv_quadratic
      M L U (Pi.single i 1) omega
    rw [hEq, vecDot_single_left, matVecMul_single]
    ring
  · have hsum := integrable_cutoffMu_dual M L U
      (Pi.single i 1 + Pi.single j 1)
    have hi := integrable_cutoffMu_dual M L U (Pi.single i 1)
    have hj := integrable_cutoffMu_dual M L U (Pi.single j 1)
    have hint := (hsum.sub hi).sub hj
    apply hint.congr
    filter_upwards with omega
    let A := (randomAStarMatrix M L U omega)⁻¹
    have hsymm : A.IsSymm := by
      let hdata := aCutoffCoeffOnData M L omega U
      have hTheory := Ch02.responseSymmetricDirichletNeumannTheory
        U hdata.toCoeffOn hdata.isSymmetric
      change ((aStarMatrix U hdata.toCoeffOn)⁻¹).IsSymm
      rw [show (aStarMatrix U hdata.toCoeffOn)⁻¹ =
          Ch02.sigmaStarInvCoarse U hdata.toCoeffOn by
        rw [show aStarMatrix U hdata.toCoeffOn = Ch02.aStarCoarse U hdata.toCoeffOn by rfl,
          hTheory.derived_matrices.2.1]
        unfold Ch02.sigmaStarCoarse
        exact Matrix.nonsing_inv_nonsing_inv _
          (Ch02.isUnit_det_sigmaStarInvCoarse U hdata.toCoeffOn)]
      exact Ch02.sigmaStarInvCoarse_isSymm U hdata.toCoeffOn
    change
      Mu (U : Set (Vec d)) (0, Pi.single i 1 + Pi.single j 1)
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) -
        Mu (U : Set (Vec d)) (0, Pi.single i 1)
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) -
        Mu (U : Set (Vec d)) (0, Pi.single j 1)
          (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M L omega)) = A i j
    rw [cutoffMu_dual_eq_randomAStarInv_quadratic M L U
          (Pi.single i 1 + Pi.single j 1) omega,
      cutoffMu_dual_eq_randomAStarInv_quadratic M L U (Pi.single i 1) omega,
      cutoffMu_dual_eq_randomAStarInv_quadratic M L U (Pi.single j 1) omega]
    change
      (1 / 2 : ℝ) * vecDot (Pi.single i 1 + Pi.single j 1)
          (matVecMul A (Pi.single i 1 + Pi.single j 1)) -
        (1 / 2 : ℝ) * vecDot (Pi.single i 1) (matVecMul A (Pi.single i 1)) -
        (1 / 2 : ℝ) * vecDot (Pi.single j 1) (matVecMul A (Pi.single j 1)) = A i j
    rw [basis_sum_pairing, vecDot_single_left, matVecMul_single,
      vecDot_single_left, matVecMul_single, hsymm.apply j i]
    ring

/-- Annealing a dual inverse-star quadratic form gives the corresponding
quadratic form of `abarStarInv`. -/
theorem integral_randomAStarMatrix_inv_quadratic {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L : ℕ) (U : Ch02.Domain d)
    (q : Vec d) :
    ∫ omega : _root_.SubdiffusiveProcess.Model.PotentialSample d,
        (1 / 2 : ℝ) * vecDot q
          (matVecMul ((randomAStarMatrix M L U omega)⁻¹) q) ∂M.P.toMeasure =
      (1 / 2 : ℝ) * vecDot q (matVecMul (abarStarInv M L U) q) := by
  have hInt := integrable_randomAStarMatrix_inv M L U
  rw [integral_const_mul]
  congr 1
  simp only [vecDot, matVecMul]
  rw [integral_finsetSum Finset.univ]
  · congr 1
    ext i
    rw [integral_const_mul, integral_finsetSum Finset.univ]
    · simp_rw [integral_mul_const]
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      change (∫ omega, (randomAStarMatrix M L U omega)⁻¹ i j ∂M.P.toMeasure) * q j =
        (∫ omega, (randomAStarMatrix M L U omega)⁻¹ ∂M.P.toMeasure) i j * q j
      rw [Homogenization.integral_matrix_apply hInt i j]
    · intro j _hj
      exact ((hInt.eval i).eval j).mul_const (q j)
  · intro i _hi
    exact (integrable_finsetSum Finset.univ fun j _hj =>
      ((hInt.eval i).eval j).mul_const (q j)).const_mul (q i)

/-- Annealing preserves the prefix Jensen comparison of the primal cutoff
matrices.  This is the first finite-volume inequality in
`e.annealed.matrix.bounds`. -/
theorem matLoewnerLE_abar_cutoff {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (U : Ch02.Domain d)
    {n m : ℕ} (hnm : n < m) :
    MatLoewnerLE (abar M m U) (abar M n U) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩
  intro p
  let fm : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    Mu (U : Set (Vec d)) (-p, 0)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega))
  let fn : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    Mu (U : Set (Vec d)) (-p, 0)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
  have hcond : M.P.toMeasure[fm | potentialIndexSigma (Set.Iic n)]
      ≤ᵐ[M.P.toMeasure] fn := condExp_cutoffMu_primal_le M hnm U p
  have hle := integral_mono_ae integrable_condExp
    (integrable_cutoffMu_primal M n U p) hcond
  rw [integral_condExp (potentialIndexSigma_le_borel (d := d) (Set.Iic n))] at hle
  have hm : ∫ omega, fm omega ∂M.P.toMeasure =
      (1 / 2 : ℝ) * vecDot p (matVecMul (abar M m U) p) := by
    calc
      ∫ omega, fm omega ∂M.P.toMeasure =
          ∫ omega, (1 / 2 : ℝ) * vecDot p
            (matVecMul (randomAMatrix M m U omega) p) ∂M.P.toMeasure := by
        apply integral_congr_ae
        filter_upwards with omega
        exact cutoffMu_primal_eq_randomAMatrix_quadratic M m U p omega
      _ = _ := integral_randomAMatrix_quadratic M m U p
  have hn : ∫ omega, fn omega ∂M.P.toMeasure =
      (1 / 2 : ℝ) * vecDot p (matVecMul (abar M n U) p) := by
    calc
      ∫ omega, fn omega ∂M.P.toMeasure =
          ∫ omega, (1 / 2 : ℝ) * vecDot p
            (matVecMul (randomAMatrix M n U omega) p) ∂M.P.toMeasure := by
        apply integral_congr_ae
        filter_upwards with omega
        exact cutoffMu_primal_eq_randomAMatrix_quadratic M n U p omega
      _ = _ := integral_randomAMatrix_quadratic M n U p
  rw [hm, hn] at hle
  linarith

/-- The inverse-star annealed matrix at the finer cutoff, normalized by the
fresh-shell inverse moment, lies below its coarser-cutoff counterpart.  This
is the third finite-volume inequality in `e.annealed.matrix.bounds`. -/
theorem matLoewnerLE_exp_smul_abarStarInv_cutoff {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (U : Ch02.Domain d)
    {n m : ℕ} (hnm : n < m) :
    MatLoewnerLE
      (Real.exp (-2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ)) •
        abarStarInv M m U)
      (abarStarInv M n U) := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension)⟩
  intro q
  let x : ℝ := 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ)
  let C : ℝ := Real.exp x
  let D : ℝ := Real.exp (-x)
  let fm : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    Mu (U : Set (Vec d)) (0, q)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M m omega))
  let fn : _root_.SubdiffusiveProcess.Model.PotentialSample d → ℝ := fun omega =>
    Mu (U : Set (Vec d)) (0, q)
      (scalarCoeffField (_root_.SubdiffusiveProcess.Model.aCutoff M n omega))
  have hcond : M.P.toMeasure[fm | potentialIndexSigma (Set.Iic n)]
      ≤ᵐ[M.P.toMeasure] fun omega => C * fn omega := by
    simpa only [x, C, fm, fn] using condExp_cutoffMu_dual_le M hnm U q
  have hle := integral_mono_ae integrable_condExp
    ((integrable_cutoffMu_dual M n U q).const_mul C) hcond
  rw [integral_condExp (potentialIndexSigma_le_borel (d := d) (Set.Iic n)),
    integral_const_mul] at hle
  have hm : ∫ omega, fm omega ∂M.P.toMeasure =
      (1 / 2 : ℝ) * vecDot q (matVecMul (abarStarInv M m U) q) := by
    calc
      ∫ omega, fm omega ∂M.P.toMeasure =
          ∫ omega, (1 / 2 : ℝ) * vecDot q
            (matVecMul ((randomAStarMatrix M m U omega)⁻¹) q) ∂M.P.toMeasure := by
        apply integral_congr_ae
        filter_upwards with omega
        exact cutoffMu_dual_eq_randomAStarInv_quadratic M m U q omega
      _ = _ := integral_randomAStarMatrix_inv_quadratic M m U q
  have hn : ∫ omega, fn omega ∂M.P.toMeasure =
      (1 / 2 : ℝ) * vecDot q (matVecMul (abarStarInv M n U) q) := by
    calc
      ∫ omega, fn omega ∂M.P.toMeasure =
          ∫ omega, (1 / 2 : ℝ) * vecDot q
            (matVecMul ((randomAStarMatrix M n U omega)⁻¹) q) ∂M.P.toMeasure := by
        apply integral_congr_ae
        filter_upwards with omega
        exact cutoffMu_dual_eq_randomAStarInv_quadratic M n U q omega
      _ = _ := integral_randomAStarMatrix_inv_quadratic M n U q
  rw [hm, hn] at hle
  have hquad : vecDot q (matVecMul (abarStarInv M m U) q) ≤
      C * vecDot q (matVecMul (abarStarInv M n U) q) := by
    linarith
  have hDC : D * C = 1 := by
    dsimp [D, C]
    rw [← Real.exp_add]
    simp
  have hscaled := mul_le_mul_of_nonneg_left hquad (Real.exp_pos (-x)).le
  change D * vecDot q (matVecMul (abarStarInv M m U) q) ≤
    D * (C * vecDot q (matVecMul (abarStarInv M n U) q)) at hscaled
  rw [← mul_assoc, hDC, one_mul] at hscaled
  have hD : D = Real.exp
      (-2 * _root_.SubdiffusiveProcess.Model.tauSq M.P * ((m - n : ℕ) : ℝ)) := by
    dsimp [D, x]
    congr 1
    ring
  rw [hD] at hscaled
  have hhalf := mul_le_mul_of_nonneg_left hscaled (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [smul_matVecMul, vecDot_smul_right, mul_assoc] using hhalf

/-- The primal infinite-volume scalar coefficient is nonincreasing in the
cutoff index. -/
theorem ahom_antitone_cutoff {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) {n m : ℕ} (hnm : n < m) :
    ahom M m ≤ ahom M n := by
  have hreadout : ∀ k : ℕ,
      abarScalarReadout M m k ≤ abarScalarReadout M n k := by
    intro k
    let U := Ch02.cubeDomain (originCube d (k : ℤ))
    have hmat := matLoewnerLE_abar_cutoff M U hnm
    have hd : 0 < (d : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
    unfold abarScalarReadout Matrix.trace
    apply (div_le_div_iff_of_pos_right hd).2
    apply Finset.sum_le_sum
    intro i _hi
    simpa [U, matVecMul_single, vecDot_single_left] using hmat (Pi.single i 1)
  exact le_of_tendsto_of_tendsto
    (tendsto_abarScalarReadout_ahom M m)
    (tendsto_abarScalarReadout_ahom M n)
    (Filter.Eventually.of_forall hreadout)

end

end SubdiffusiveProcess.CoarseGrainingVocab
