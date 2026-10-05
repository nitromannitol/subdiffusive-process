module

public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumannDefinitions
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import Homogenization.Book.Ch02.Theorems.SubadditivityScaling
public import Homogenization.Book.Ch02.Theorems.MatrixExtractionProofs
public import Homogenization.Book.Ch02.Theorems.Quadraticity

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Homogenization Homogenization.Book.Ch02 MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Pointwise coefficient comparison, integrated: the Dirichlet energy integrand
of `a` at a fixed test function `u` is `≤` that of `b`, given the a.e. quadratic
form comparison and integrability of both integrands. -/
theorem aux_dirichletEnergy_mono {d : ℕ} {U : Domain d} (a b : CoeffOn U)
    (hab : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
      MatLoewnerLE (a.toCoeffField x) (b.toCoeffField x))
    (u : H1Function (U : Set (Vec d)))
    (hintA : Integrable (fun x => (1 / 2 : ℝ) *
        vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)))
      (MeasureTheory.volume.restrict (U : Set (Vec d))))
    (hintB : Integrable (fun x => (1 / 2 : ℝ) *
        vecDot (u.grad x) (matVecMul (b.toCoeffField x) (u.grad x)))
      (MeasureTheory.volume.restrict (U : Set (Vec d)))) :
    symmetricDirichletEnergyValue U a u ≤ symmetricDirichletEnergyValue U b u := by
  unfold symmetricDirichletEnergyValue Book.Ch02.average
  have hvol : (0:ℝ) ≤ (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hvol
  exact MeasureTheory.integral_mono_ae hintA hintB (hab.mono fun x hx => hx (u.grad x))

/-- Pointwise coefficient comparison, integrated, for the Neumann energy
(unscaled, `c = 1`): the quadratic part reverses (it enters with a minus
sign), the linear `q·∇u` part is unaffected by the coefficient. NOTE: unlike
the Dirichlet energy, the Neumann energy is NOT purely quadratic in the
coefficient (it has the coefficient-independent linear term `q·∇u`), so a
scale factor `c ≠ 1` does not distribute over it this way; homogeneity of
`ν_N`/`Book.Ch02.sigmaStarInvCoarse` under constant rescaling must come from
`responseJ_homogeneous`/`responseJ_zero_q_eq_sigmaStarInvCoarse` instead
(existing library facts), not from this lemma. -/
theorem aux_neumannEnergy_anti {d : ℕ} {U : Domain d} (a b : CoeffOn U) (q : Vec d)
    (hab : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
      MatLoewnerLE (a.toCoeffField x) (b.toCoeffField x))
    (u : H1Function (U : Set (Vec d)))
    (hintA : Integrable (fun x => vecDot q (u.grad x) - (1 / 2 : ℝ) *
        vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)))
      (MeasureTheory.volume.restrict (U : Set (Vec d))))
    (hintB : Integrable (fun x => vecDot q (u.grad x) - (1 / 2 : ℝ) *
        vecDot (u.grad x) (matVecMul (b.toCoeffField x) (u.grad x)))
      (MeasureTheory.volume.restrict (U : Set (Vec d)))) :
    symmetricNeumannEnergyValue U b q u ≤ symmetricNeumannEnergyValue U a q u := by
  unfold symmetricNeumannEnergyValue Book.Ch02.average
  have hvol : (0:ℝ) ≤ (MeasureTheory.volume (U : Set (Vec d))).toReal⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hvol
  refine MeasureTheory.integral_mono_ae hintB hintA (hab.mono fun x hx => ?_)
  have := hx (u.grad x)
  linarith

/-- Dirichlet value `ν_D` is monotone in the coefficient: if `a`'s quadratic
form is pointwise `≤` `b`'s a.e. on `U`, and both energies are integrable at
every admissible test function, then `ν_D(U,p;a) ≤ ν_D(U,p;b)`. Competitor-reuse
proof: `a`'s minimizer beats `b`'s minimizer used as a competitor for `a`; that
competitor's `a`-energy is `≤` its `b`-energy pointwise; and `b`'s minimizer
realizes `ν_D(U,p;b)`. -/
theorem aux_symmetricDirichletNu_mono {d : ℕ} {U : Domain d} (a b : CoeffOn U)
    (hab : ∀ u : H1Function (U : Set (Vec d)),
      symmetricDirichletEnergyValue U a u ≤ symmetricDirichletEnergyValue U b u)
    (p : Vec d)
    (hTa : ∃ u : H1Function (U : Set (Vec d)), IsSymmetricDirichletMinimizer U a p u)
    (hTb : ∃ u : H1Function (U : Set (Vec d)), IsSymmetricDirichletMinimizer U b p u) :
    symmetricDirichletNu U a p ≤ symmetricDirichletNu U b p := by
  obtain ⟨uA, huA_adm, huA_min⟩ := hTa
  obtain ⟨uB, huB_adm, huB_min⟩ := hTb
  have hEqA : symmetricDirichletNu U a p = symmetricDirichletEnergyValue U a uA := by
    have hle : IsLeast (symmetricDirichletValueSet U a p)
        (symmetricDirichletEnergyValue U a uA) :=
      ⟨⟨uA, huA_adm, rfl⟩, fun E hE => by
        obtain ⟨w, hw, rfl⟩ := hE
        exact huA_min w hw⟩
    exact hle.csInf_eq
  have hEqB : symmetricDirichletNu U b p = symmetricDirichletEnergyValue U b uB := by
    have hle : IsLeast (symmetricDirichletValueSet U b p)
        (symmetricDirichletEnergyValue U b uB) :=
      ⟨⟨uB, huB_adm, rfl⟩, fun E hE => by
        obtain ⟨w, hw, rfl⟩ := hE
        exact huB_min w hw⟩
    exact hle.csInf_eq
  rw [hEqA, hEqB]
  exact (huA_min uB huB_adm).trans (hab uB)

/-- Neumann value `ν_N` is anti-monotone in the coefficient: if `a`'s quadratic
form is pointwise `≤` `b`'s a.e. on `U`, then `ν_N(U,q;b) ≤ ν_N(U,q;a)`. Same
competitor-reuse proof, direction reversed since `ν_N` is a supremum with a
`-` sign on the quadratic term. -/
theorem aux_symmetricNeumannNu_anti {d : ℕ} {U : Domain d} (a b : CoeffOn U)
    (q : Vec d)
    (hab : ∀ u : H1Function (U : Set (Vec d)),
      symmetricNeumannEnergyValue U a q u ≥ symmetricNeumannEnergyValue U b q u)
    (hTa : ∃ u : H1Function (U : Set (Vec d)), IsSymmetricNeumannMaximizer U a q u)
    (hTb : ∃ u : H1Function (U : Set (Vec d)), IsSymmetricNeumannMaximizer U b q u) :
    symmetricNeumannNu U b q ≤ symmetricNeumannNu U a q := by
  obtain ⟨uA, huA_max⟩ := hTa
  obtain ⟨uB, huB_max⟩ := hTb
  have hEqA : symmetricNeumannNu U a q = symmetricNeumannEnergyValue U a q uA := by
    have hge : IsGreatest (symmetricNeumannValueSet U a q)
        (symmetricNeumannEnergyValue U a q uA) :=
      ⟨⟨uA, rfl⟩, fun E hE => by
        obtain ⟨w, rfl⟩ := hE
        exact huA_max w⟩
    exact hge.csSup_eq
  have hEqB : symmetricNeumannNu U b q = symmetricNeumannEnergyValue U b q uB := by
    have hge : IsGreatest (symmetricNeumannValueSet U b q)
        (symmetricNeumannEnergyValue U b q uB) :=
      ⟨⟨uB, rfl⟩, fun E hE => by
        obtain ⟨w, rfl⟩ := hE
        exact huB_max w⟩
    exact hge.csSup_eq
  rw [hEqA, hEqB]
  exact (hab uB).trans (huA_max uB)

end SubdiffusiveProcess.Paper

/-- Scale a coefficient field on `U` by a positive constant `c`. Used to build
the two comparison partners `exp(D) • b` / `exp(-D) • b` needed to sandwich `a`
between them and invoke both the monotonicity lemmas above and the existing
`responseSubadditivityAndScalingTheory` homogeneity facts. -/
noncomputable def CoeffOn.scale {d : ℕ} {U : Domain d} (c : ℝ) (hc : 0 < c)
    (a : CoeffOn U) : CoeffOn U where
  toCoeffField := fun x => c • a.toCoeffField x
  lam := c * a.lam
  Lam := c * a.Lam
  lam_pos := mul_pos hc a.lam_pos
  lam_le_Lam := mul_le_mul_of_nonneg_left a.lam_le_Lam hc.le
  aeStronglyMeasurable := by
    classical
    intro i j
    have h := a.aeStronglyMeasurable i j
    unfold restrictCoeffField at h ⊢
    have heq : (fun x : Vec d => (if x ∈ (U : Set (Vec d))
        then (c • a.toCoeffField x) else 0) i j) =
        fun x : Vec d => c * (if x ∈ (U : Set (Vec d))
        then a.toCoeffField x else 0) i j := by
      funext x
      by_cases hx : x ∈ (U : Set (Vec d)) <;> simp [hx]
    rw [heq]
    exact h.const_mul c
  aeElliptic := by
    filter_upwards [a.aeElliptic] with x hx
    obtain ⟨hlam, hle, hlow, hinv⟩ := hx
    have : Invertible c := invertibleOfNonzero hc.ne'
    have hunit : IsUnit (a.toCoeffField x).det := isUnit_det_of_isEllipticMatrix ⟨hlam, hle, hlow, hinv⟩
    refine ⟨mul_pos hc hlam, mul_le_mul_of_nonneg_left hle hc.le, fun ξ => ?_, fun ξ => ?_⟩
    · have := hlow ξ
      have hcm : matVecMul (c • a.toCoeffField x) ξ = c • matVecMul (a.toCoeffField x) ξ :=
        smul_matVecMul c (a.toCoeffField x) ξ
      rw [hcm, vecDot_smul_right]
      nlinarith
    · have := hinv ξ
      have hcm : (c • a.toCoeffField x)⁻¹ = ⅟c • (a.toCoeffField x)⁻¹ := by
        exact Matrix.inv_smul (A := a.toCoeffField x) c hunit
      have hcm2 : matVecMul (⅟c • (a.toCoeffField x)⁻¹) ξ =
          ⅟c • matVecMul (a.toCoeffField x)⁻¹ ξ :=
        smul_matVecMul (⅟c) (a.toCoeffField x)⁻¹ ξ
      rw [hcm, hcm2, vecDot_smul_right, invOf_eq_inv c, mul_inv]
      nlinarith [inv_pos.mpr hc, mul_le_mul_of_nonneg_left this (inv_pos.mpr hc).le]

theorem CoeffOn.scale_toCoeffField {d : ℕ} {U : Domain d} (c : ℝ) (hc : 0 < c)
    (a : CoeffOn U) (x : Vec d) :
    (CoeffOn.scale c hc a).toCoeffField x = c • a.toCoeffField x := rfl

theorem CoeffOn.aeScaled_scale {d : ℕ} {U : Domain d} (c : ℝ) (hc : 0 < c)
    (a : CoeffOn U) : CoeffOn.AEScaled c a (CoeffOn.scale c hc a) :=
  Filter.Eventually.of_forall fun _x => rfl

end

namespace SubdiffusiveProcess.Paper

theorem CoeffOn.isSymmetric_scale {d : ℕ} {U : Domain d} (c : ℝ) (hc : 0 < c)
    {a : CoeffOn U} (hsym : CoeffOn.IsSymmetric a) :
    CoeffOn.IsSymmetric (CoeffOn.scale c hc a) := by
  filter_upwards [hsym] with x hx
  rw [CoeffOn.scale_toCoeffField]
  exact hx.smul c



theorem aux_responseJ_neumann_scaled {d : ℕ} {U : Domain d} (c : ℝ) (hc : 0 < c)
    (a : CoeffOn U) (q : Vec d) :
    responseJ U (CoeffOn.scale c hc a) 0 q = c⁻¹ * responseJ U a 0 q := by
  have h := CoeffOn.aeScaled_scale c hc a
  rw [(responseSubadditivityAndScalingTheory U a).responseJ_homogeneous hc h 0 q, smul_zero]
  have hs := responseJ_smul (U := U) (a := a) ((Real.sqrt c)⁻¹) 0 q
  rw [smul_zero] at hs
  rw [hs, inv_pow, Real.sq_sqrt hc.le]

/-- `Book.Ch02.sigmaStarInvCoarse U (c•a) = c⁻¹ • Book.Ch02.sigmaStarInvCoarse U a`. -/
theorem aux_sigmaStarInvCoarse_scaled {d : ℕ} {U : Domain d} (c : ℝ) (hc : 0 < c)
    (a : CoeffOn U) :
    Book.Ch02.sigmaStarInvCoarse U (CoeffOn.scale c hc a) = c⁻¹ • Book.Ch02.sigmaStarInvCoarse U a := by
  ext i j
  simp only [Book.Ch02.sigmaStarInvCoarse, sigmaStarInvEntry, Matrix.smul_apply, smul_eq_mul]
  split_ifs
  · rw [aux_responseJ_neumann_scaled c hc a]; ring
  · rw [aux_responseJ_neumann_scaled c hc a, aux_responseJ_neumann_scaled c hc a,
      aux_responseJ_neumann_scaled c hc a]
    ring

/-- **The exp-comparison theorem.** If `a`'s quadratic form lies within a
factor `exp(±D)` of `b`'s a.e. on `U` and `a`, `b` are both symmetric (e.g.
isotropic scalar coefficients), then `Book.Ch02.sigmaCoarse U a` lies within `exp(±D)` of
`Book.Ch02.sigmaCoarse U b`, and `Book.Ch02.sigmaStarInvCoarse U a` lies within `exp(±D)` of
`Book.Ch02.sigmaStarInvCoarse U b`, both in the Loewner order. See `e.J.general`/`e.variational.a`. -/
theorem aux_sigma_exp_comparison {d : ℕ} {U : Domain d} (a b : CoeffOn U)
    (hsym_a : CoeffOn.IsSymmetric a) (hsym_b : CoeffOn.IsSymmetric b) (D : ℝ)
    (hab_hi : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
      MatLoewnerLE (a.toCoeffField x) (Real.exp D • b.toCoeffField x))
    (hab_lo : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
      MatLoewnerLE (Real.exp (-D) • b.toCoeffField x) (a.toCoeffField x))
    (hintDir : ∀ c : ℝ, ∀ hc : 0 < c, ∀ u : H1Function (U : Set (Vec d)),
      Integrable (fun x => (1 / 2 : ℝ) * vecDot (u.grad x)
          (matVecMul ((CoeffOn.scale c hc b).toCoeffField x) (u.grad x)))
        (MeasureTheory.volume.restrict (U : Set (Vec d))))
    (hintDirA : ∀ u : H1Function (U : Set (Vec d)),
      Integrable (fun x => (1 / 2 : ℝ) * vecDot (u.grad x)
          (matVecMul (a.toCoeffField x) (u.grad x)))
        (MeasureTheory.volume.restrict (U : Set (Vec d))))
    (hintNeu : ∀ c : ℝ, ∀ hc : 0 < c, ∀ q : Vec d, ∀ u : H1Function (U : Set (Vec d)),
      Integrable (fun x => vecDot q (u.grad x) - (1 / 2 : ℝ) *
          vecDot (u.grad x) (matVecMul ((CoeffOn.scale c hc b).toCoeffField x) (u.grad x)))
        (MeasureTheory.volume.restrict (U : Set (Vec d))))
    (hintNeuA : ∀ q : Vec d, ∀ u : H1Function (U : Set (Vec d)),
      Integrable (fun x => vecDot q (u.grad x) - (1 / 2 : ℝ) *
          vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)))
        (MeasureTheory.volume.restrict (U : Set (Vec d)))) :
    MatLoewnerLE (Book.Ch02.sigmaCoarse U a) (Real.exp D • Book.Ch02.sigmaCoarse U b) ∧
    MatLoewnerLE (Real.exp (-D) • Book.Ch02.sigmaCoarse U b) (Book.Ch02.sigmaCoarse U a) ∧
    MatLoewnerLE (Book.Ch02.sigmaStarInvCoarse U a) (Real.exp D • Book.Ch02.sigmaStarInvCoarse U b) ∧
    MatLoewnerLE (Real.exp (-D) • Book.Ch02.sigmaStarInvCoarse U b) (Book.Ch02.sigmaStarInvCoarse U a) := by
  have hDpos := Real.exp_pos D
  have hDnegpos := Real.exp_pos (-D)
  have hsym_hi : CoeffOn.IsSymmetric (CoeffOn.scale (Real.exp D) hDpos b) :=
    _root_.SubdiffusiveProcess.Paper.CoeffOn.isSymmetric_scale _ hDpos hsym_b
  have hsym_lo : CoeffOn.IsSymmetric (CoeffOn.scale (Real.exp (-D)) hDnegpos b) :=
    _root_.SubdiffusiveProcess.Paper.CoeffOn.isSymmetric_scale _ hDnegpos hsym_b
  have hTa := responseSymmetricDirichletNeumannTheory U a hsym_a
  have hThi := responseSymmetricDirichletNeumannTheory U (CoeffOn.scale (Real.exp D) hDpos b) hsym_hi
  have hTlo := responseSymmetricDirichletNeumannTheory U (CoeffOn.scale (Real.exp (-D)) hDnegpos b) hsym_lo
  have hhomSigmaHi : Book.Ch02.sigmaCoarse U (CoeffOn.scale (Real.exp D) hDpos b) = Real.exp D • Book.Ch02.sigmaCoarse U b :=
    (responseSubadditivityAndScalingTheory U b).sigma_homogeneous hDpos (CoeffOn.aeScaled_scale _ hDpos b)
  have hhomSigmaLo : Book.Ch02.sigmaCoarse U (CoeffOn.scale (Real.exp (-D)) hDnegpos b) = Real.exp (-D) • Book.Ch02.sigmaCoarse U b :=
    (responseSubadditivityAndScalingTheory U b).sigma_homogeneous hDnegpos (CoeffOn.aeScaled_scale _ hDnegpos b)
  have hhomStarInvHi : Book.Ch02.sigmaStarInvCoarse U (CoeffOn.scale (Real.exp D) hDpos b) =
      (Real.exp D)⁻¹ • Book.Ch02.sigmaStarInvCoarse U b := aux_sigmaStarInvCoarse_scaled _ hDpos b
  have hhomStarInvLo : Book.Ch02.sigmaStarInvCoarse U (CoeffOn.scale (Real.exp (-D)) hDnegpos b) =
      (Real.exp (-D))⁻¹ • Book.Ch02.sigmaStarInvCoarse U b := aux_sigmaStarInvCoarse_scaled _ hDnegpos b
  refine ⟨fun p => ?_, fun p => ?_, fun q => ?_, fun q => ?_⟩
  · -- MatLoewnerLE (Book.Ch02.sigmaCoarse a) (exp D • Book.Ch02.sigmaCoarse b)
    have hab' : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
        MatLoewnerLE (a.toCoeffField x) ((CoeffOn.scale (Real.exp D) hDpos b).toCoeffField x) := by
      filter_upwards [hab_hi] with x hx
      rwa [CoeffOn.scale_toCoeffField]
    have h1 := aux_symmetricDirichletNu_mono a (CoeffOn.scale (Real.exp D) hDpos b)
      (fun u => aux_dirichletEnergy_mono a (CoeffOn.scale (Real.exp D) hDpos b) hab' u
        (hintDirA u) (hintDir (Real.exp D) hDpos u))
      p (hTa.dirichlet_minimizer_exists p) (hThi.dirichlet_minimizer_exists p)
    rw [hTa.dirichlet_value_by_sigma p, hThi.dirichlet_value_by_sigma p, hhomSigmaHi] at h1
    exact h1
  · -- MatLoewnerLE (exp (-D) • Book.Ch02.sigmaCoarse b) (Book.Ch02.sigmaCoarse a)
    have hab' : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
        MatLoewnerLE ((CoeffOn.scale (Real.exp (-D)) hDnegpos b).toCoeffField x) (a.toCoeffField x) := by
      filter_upwards [hab_lo] with x hx
      rwa [CoeffOn.scale_toCoeffField]
    have h1 := aux_symmetricDirichletNu_mono (CoeffOn.scale (Real.exp (-D)) hDnegpos b) a
      (fun u => aux_dirichletEnergy_mono (CoeffOn.scale (Real.exp (-D)) hDnegpos b) a hab' u
        (hintDir (Real.exp (-D)) hDnegpos u) (hintDirA u))
      p (hTlo.dirichlet_minimizer_exists p) (hTa.dirichlet_minimizer_exists p)
    rw [hTlo.dirichlet_value_by_sigma p, hTa.dirichlet_value_by_sigma p, hhomSigmaLo] at h1
    exact h1
  · -- MatLoewnerLE (Book.Ch02.sigmaStarInvCoarse a) (exp D • Book.Ch02.sigmaStarInvCoarse b)
    -- Neumann is ANTI-monotone: a ≤ bLo (hab_lo) gives Book.Ch02.sigmaStarInvCoarse a ≤ Book.Ch02.sigmaStarInvCoarse bLo,
    -- and Book.Ch02.sigmaStarInvCoarse bLo = exp(-D)⁻¹ • Book.Ch02.sigmaStarInvCoarse b = exp D • Book.Ch02.sigmaStarInvCoarse b.
    have hab' : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
        MatLoewnerLE ((CoeffOn.scale (Real.exp (-D)) hDnegpos b).toCoeffField x) (a.toCoeffField x) := by
      filter_upwards [hab_lo] with x hx
      rwa [CoeffOn.scale_toCoeffField]
    have h1 := aux_symmetricNeumannNu_anti (CoeffOn.scale (Real.exp (-D)) hDnegpos b) a q
      (fun u => aux_neumannEnergy_anti (CoeffOn.scale (Real.exp (-D)) hDnegpos b) a q hab' u
        (hintNeu (Real.exp (-D)) hDnegpos q u) (hintNeuA q u))
      (let ⟨u, _, hu⟩ := hTlo.neumann_meanZero_maximizer_exists q; ⟨u, hu⟩)
      (let ⟨u, _, hu⟩ := hTa.neumann_meanZero_maximizer_exists q; ⟨u, hu⟩)
    rw [hTlo.neumann_value_by_sigmaStarInv q, hTa.neumann_value_by_sigmaStarInv q, hhomStarInvLo] at h1
    rw [show (Real.exp (-D))⁻¹ = Real.exp D by rw [← Real.exp_neg]; ring_nf] at h1
    exact h1
  · -- MatLoewnerLE (exp (-D) • Book.Ch02.sigmaStarInvCoarse b) (Book.Ch02.sigmaStarInvCoarse a)
    have hab' : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
        MatLoewnerLE (a.toCoeffField x) ((CoeffOn.scale (Real.exp D) hDpos b).toCoeffField x) := by
      filter_upwards [hab_hi] with x hx
      rwa [CoeffOn.scale_toCoeffField]
    have h1 := aux_symmetricNeumannNu_anti a (CoeffOn.scale (Real.exp D) hDpos b) q
      (fun u => aux_neumannEnergy_anti a (CoeffOn.scale (Real.exp D) hDpos b) q hab' u
        (hintNeuA q u) (hintNeu (Real.exp D) hDpos q u))
      (let ⟨u, _, hu⟩ := hTa.neumann_meanZero_maximizer_exists q; ⟨u, hu⟩)
      (let ⟨u, _, hu⟩ := hThi.neumann_meanZero_maximizer_exists q; ⟨u, hu⟩)
    rw [hThi.neumann_value_by_sigmaStarInv q, hTa.neumann_value_by_sigmaStarInv q, hhomStarInvHi] at h1
    rwa [show (Real.exp D)⁻¹ = Real.exp (-D) by rw [Real.exp_neg]] at h1

/-- The quadratic form of a Ch02 coefficient against an `H1Function` gradient is
integrable: `a`'s a.e. ellipticity bounds `|a i j| ≤ Lam` a.e., and both gradient
components are `L²`, so `A i j * (∂_i u)(∂_j u)` is dominated a.e. by
`(Lam/2)*((∂_i u)² + (∂_j u)²)`, an integrable function; summing over the finitely
many `(i,j)` pairs gives the full quadratic form. This supplies the integrability side conditions for `aux_sigma_exp_comparison`. -/
theorem aux_coeffOn_quadraticForm_integrable {d : ℕ} {U : Domain d} (a : CoeffOn U)
    (u : H1Function (U : Set (Vec d))) :
    Integrable (fun x => vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)))
      (MeasureTheory.volume.restrict (U : Set (Vec d))) := by
  classical
  have hmem : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))), x ∈ (U : Set (Vec d)) :=
    MeasureTheory.ae_restrict_mem U.measurableSet
  have hterm : ∀ i j : Fin d,
      Integrable (fun x => a.toCoeffField x i j * (u.grad x i * u.grad x j))
        (MeasureTheory.volume.restrict (U : Set (Vec d))) := by
    intro i j
    have hij_aesm : AEStronglyMeasurable (fun x => a.toCoeffField x i j)
        (MeasureTheory.volume.restrict (U : Set (Vec d))) := by
      have h := a.aeStronglyMeasurable i j
      refine h.congr ?_
      filter_upwards [hmem] with x hx
      simp [restrictCoeffField_apply_of_mem hx]
    have hgi_aesm : AEStronglyMeasurable (fun x => u.grad x i)
        (MeasureTheory.volume.restrict (U : Set (Vec d))) := (u.gradMemL2 i).aestronglyMeasurable
    have hgj_aesm : AEStronglyMeasurable (fun x => u.grad x j)
        (MeasureTheory.volume.restrict (U : Set (Vec d))) := (u.gradMemL2 j).aestronglyMeasurable
    have hi : Integrable (fun x => (u.grad x i) ^ 2)
        (MeasureTheory.volume.restrict (U : Set (Vec d))) := (u.gradMemL2 i).integrable_sq
    have hj : Integrable (fun x => (u.grad x j) ^ 2)
        (MeasureTheory.volume.restrict (U : Set (Vec d))) := (u.gradMemL2 j).integrable_sq
    have hLam_nonneg : 0 ≤ a.Lam := le_trans a.lam_pos.le a.lam_le_Lam
    have hbound : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
        ‖a.toCoeffField x i j * (u.grad x i * u.grad x j)‖ ≤
          (a.Lam / 2) * ((u.grad x i) ^ 2 + (u.grad x j) ^ 2) := by
      filter_upwards [hmem, a.aeElliptic] with x hx hell
      have hco : |a.toCoeffField x i j| ≤ a.Lam := abs_apply_le_of_isEllipticMatrix hell i j
      have hamgm : |u.grad x i * u.grad x j| ≤ ((u.grad x i) ^ 2 + (u.grad x j) ^ 2) / 2 := by
        rw [abs_le]
        constructor
        · nlinarith [sq_nonneg (u.grad x i + u.grad x j)]
        · nlinarith [sq_nonneg (u.grad x i - u.grad x j)]
      calc
        ‖a.toCoeffField x i j * (u.grad x i * u.grad x j)‖
            = |a.toCoeffField x i j| * |u.grad x i * u.grad x j| := by
              rw [Real.norm_eq_abs, abs_mul]
        _ ≤ a.Lam * (((u.grad x i) ^ 2 + (u.grad x j) ^ 2) / 2) :=
              mul_le_mul hco hamgm (abs_nonneg _) hLam_nonneg
        _ = (a.Lam / 2) * ((u.grad x i) ^ 2 + (u.grad x j) ^ 2) := by ring
    exact MeasureTheory.Integrable.mono' (((hi.add hj)).const_mul (a.Lam / 2))
      (hij_aesm.mul (hgi_aesm.mul hgj_aesm)) hbound
  have hsum : Integrable
      (fun x => ∑ i : Fin d, ∑ j : Fin d, a.toCoeffField x i j * (u.grad x i * u.grad x j))
      (MeasureTheory.volume.restrict (U : Set (Vec d))) := by
    apply integrable_finsetSum Finset.univ
    intro i _
    apply integrable_finsetSum Finset.univ
    intro j _
    exact hterm i j
  have hexpand : ∀ x, vecDot (u.grad x) (matVecMul (a.toCoeffField x) (u.grad x)) =
      ∑ i : Fin d, ∑ j : Fin d, a.toCoeffField x i j * (u.grad x i * u.grad x j) := by
    intro x
    simp only [vecDot, matVecMul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  exact hsum.congr (Filter.Eventually.of_forall fun x => (hexpand x).symm)

/-- The linear (flux) term `q · ∇u` is integrable on any `Domain d` (finite measure),
directly from `u`'s `L²` gradient membership. -/
theorem aux_gradLinear_integrable {d : ℕ} {U : Domain d}
    (u : H1Function (U : Set (Vec d))) (q : Vec d) :
    Integrable (fun x => vecDot q (u.grad x))
      (MeasureTheory.volume.restrict (U : Set (Vec d))) := by
  have hterm : ∀ i : Fin d, Integrable (fun x => q i * u.grad x i)
      (MeasureTheory.volume.restrict (U : Set (Vec d))) :=
    fun i => ((u.gradMemL2 i).integrable (by norm_num)).const_mul (q i)
  have hsum : Integrable (fun x => ∑ i : Fin d, q i * u.grad x i)
      (MeasureTheory.volume.restrict (U : Set (Vec d))) :=
    integrable_finsetSum Finset.univ (fun i _ => hterm i)
  exact hsum.congr (Filter.Eventually.of_forall fun x => by simp [vecDot])

/-- Corollary: `aux_sigma_exp_comparison` with its four integrability side
conditions discharged automatically from ellipticity + `H1Function` membership
alone. No caller needs to supply
`hintDir`/`hintDirA`/`hintNeu`/`hintNeuA` by hand anymore. -/
theorem aux_sigma_exp_comparison' {d : ℕ} {U : Domain d} (a b : CoeffOn U)
    (hsym_a : CoeffOn.IsSymmetric a) (hsym_b : CoeffOn.IsSymmetric b) (D : ℝ)
    (hab_hi : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
      MatLoewnerLE (a.toCoeffField x) (Real.exp D • b.toCoeffField x))
    (hab_lo : ∀ᵐ x ∂ (MeasureTheory.volume.restrict (U : Set (Vec d))),
      MatLoewnerLE (Real.exp (-D) • b.toCoeffField x) (a.toCoeffField x)) :
    MatLoewnerLE (Book.Ch02.sigmaCoarse U a) (Real.exp D • Book.Ch02.sigmaCoarse U b) ∧
    MatLoewnerLE (Real.exp (-D) • Book.Ch02.sigmaCoarse U b) (Book.Ch02.sigmaCoarse U a) ∧
    MatLoewnerLE (Book.Ch02.sigmaStarInvCoarse U a) (Real.exp D • Book.Ch02.sigmaStarInvCoarse U b) ∧
    MatLoewnerLE (Real.exp (-D) • Book.Ch02.sigmaStarInvCoarse U b) (Book.Ch02.sigmaStarInvCoarse U a) := by
  refine aux_sigma_exp_comparison a b hsym_a hsym_b D hab_hi hab_lo ?_ ?_ ?_ ?_
  · intro c hc u
    have h := aux_coeffOn_quadraticForm_integrable (CoeffOn.scale c hc b) u
    simpa [mul_comm, mul_left_comm, mul_assoc] using h.const_mul (1 / 2 : ℝ)
  · intro u
    have h := aux_coeffOn_quadraticForm_integrable a u
    simpa [mul_comm, mul_left_comm, mul_assoc] using h.const_mul (1 / 2 : ℝ)
  · intro c hc q u
    have h1 := aux_gradLinear_integrable u q
    have h2 := aux_coeffOn_quadraticForm_integrable (CoeffOn.scale c hc b) u
    exact h1.sub (by simpa [mul_comm, mul_left_comm, mul_assoc] using h2.const_mul (1 / 2 : ℝ))
  · intro q u
    have h1 := aux_gradLinear_integrable u q
    have h2 := aux_coeffOn_quadraticForm_integrable a u
    exact h1.sub (by simpa [mul_comm, mul_left_comm, mul_assoc] using h2.const_mul (1 / 2 : ℝ))

end SubdiffusiveProcess.Paper
