module

public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import Homogenization.Sobolev.H1.Translation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import Mathlib.Tactic

@[expose] public section




open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Pointwise

noncomputable section
namespace SubdiffusiveProcess

open Homogenization Homogenization.Book

/-- Scalar multiplication of the first vector in `vecDot` pulls out as a factor. -/
theorem vecDot_smul_left {d : ℕ} (c : ℝ) (x y : Homogenization.Vec d) :
    Homogenization.vecDot (c • x) y = c * Homogenization.vecDot x y := by
  simp only [Homogenization.vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Scalar multiplication of the second vector in `vecDot` pulls out as a factor. -/
theorem vecDot_smul_right {d : ℕ} (c : ℝ) (x y : Homogenization.Vec d) :
    Homogenization.vecDot x (c • y) = c * Homogenization.vecDot x y := by
  simp only [Homogenization.vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Scalar multiplication of the vector argument of `matVecMul` pulls out as a factor. -/
theorem matVecMul_smul_vec {d : ℕ} (A : Homogenization.Mat d) (c : ℝ) (x : Homogenization.Vec d) :
    Homogenization.matVecMul A (c • x) = c • Homogenization.matVecMul A x := by
  funext i
  simp only [Homogenization.matVecMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Scalar multiplication of the matrix argument of `matVecMul` pulls out as a factor. -/
theorem matVecMul_smul_mat {d : ℕ} (c : ℝ) (A : Homogenization.Mat d) (x : Homogenization.Vec d) :
    Homogenization.matVecMul (c • A) x = c • Homogenization.matVecMul A x := by
  funext i
  simp only [Homogenization.matVecMul, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The symmetric Neumann candidate energy depends on a trial function only through its
gradient. -/
theorem aux_symmetricNeumannEnergyValue_eq_of_grad_eq {d : ℕ} (U : Ch02.Domain d)
    (A : Ch02.CoeffOn U) (q : Homogenization.Vec d)
    {u v : Homogenization.H1Function (U : Set (Homogenization.Vec d))}
    (hgrad : u.grad = v.grad) :
    Ch02.symmetricNeumannEnergyValue U A q u = Ch02.symmetricNeumannEnergyValue U A q v := by
  unfold Ch02.symmetricNeumannEnergyValue
  rw [hgrad]

/-- Rescaling and translating a Neumann trial function transforms the symmetric candidate
energy by the coefficient's constant of proportionality. -/
theorem aux_symmetricNeumannEnergyValue_translate_smul {d : ℕ}
    (U : Ch02.Domain d) (z : Homogenization.Vec d)
    (hdom' : Homogenization.IsOpenBoundedConvexDomain
      (Homogenization.translateSet z (U : Set (Homogenization.Vec d))))
    (hne' : (Homogenization.translateSet z (U : Set (Homogenization.Vec d))).Nonempty)
    (A : Ch02.CoeffOn U)
    (A' : Ch02.CoeffOn (⟨Homogenization.translateSet z (U : Set (Homogenization.Vec d)),
      hdom', hne'⟩ : Ch02.Domain d))
    (c : ℝ) (hA : ∀ x : Homogenization.Vec d, A'.toCoeffField (x + z) = c • A.toCoeffField x)
    (q : Homogenization.Vec d) (w : Homogenization.H1Function (U : Set (Homogenization.Vec d))) :
    Ch02.symmetricNeumannEnergyValue U A q (c • w) =
      c * Ch02.symmetricNeumannEnergyValue
        (⟨Homogenization.translateSet z (U : Set (Homogenization.Vec d)), hdom', hne'⟩ :
          Ch02.Domain d) A' q (w.translate z) := by
  have hpt : ∀ x ∈ (U : Set (Homogenization.Vec d)),
      (Homogenization.vecDot q ((c • w).grad x) -
        (1 / 2 : ℝ) * Homogenization.vecDot ((c • w).grad x)
          (Homogenization.matVecMul (A.toCoeffField x) ((c • w).grad x))) =
      c * (Homogenization.vecDot q ((w.translate z).grad (x + z)) -
        (1 / 2 : ℝ) * Homogenization.vecDot ((w.translate z).grad (x + z))
          (Homogenization.matVecMul (A'.toCoeffField (x + z)) ((w.translate z).grad (x + z)))) := by
    intro x _
    have hg2 : (w.translate z).grad (x + z) = w.grad x := by
      rw [H1Function.translate_grad]
      congr 1
      abel
    have hmv : Homogenization.matVecMul (A'.toCoeffField (x + z)) (w.grad x) =
        c • Homogenization.matVecMul (A.toCoeffField x) (w.grad x) := by
      rw [hA x, matVecMul_smul_mat]
    simp only [H1Function.smul_grad, hg2, hmv, matVecMul_smul_vec, vecDot_smul_left,
      vecDot_smul_right]
    ring
  unfold Ch02.symmetricNeumannEnergyValue Ch02.average
  rw [MeasureTheory.setIntegral_congr_fun U.measurableSet hpt,
    MeasureTheory.integral_const_mul,
    Homogenization.setIntegral_comp_addRight_translateSet z (U : Set (Homogenization.Vec d))
      (fun y => Homogenization.vecDot q ((w.translate z).grad y) -
        (1 / 2 : ℝ) * Homogenization.vecDot ((w.translate z).grad y)
          (Homogenization.matVecMul (A'.toCoeffField y) ((w.translate z).grad y))),
    ← Homogenization.volume_translateSet_eq z (U : Set (Homogenization.Vec d))]
  ring

/-- Translation and constant rescaling of the Chapter 2 symmetric Neumann value. -/
theorem symmetricNeumannNu_translate_smul {d : ℕ}
    (U U' : Homogenization.Book.Ch02.Domain d) (z : Homogenization.Vec d)
    (hUU' : (U' : Set (Homogenization.Vec d)) =
      Homogenization.translateSet z (U : Set (Homogenization.Vec d)))
    (A : Homogenization.Book.Ch02.CoeffOn U) (A' : Homogenization.Book.Ch02.CoeffOn U')
    (c : ℝ) (hc : 0 < c)
    (hA : ∀ x : Homogenization.Vec d, A'.toCoeffField (x + z) = c • A.toCoeffField x)
    (q : Homogenization.Vec d) :
    Homogenization.Book.Ch02.symmetricNeumannNu U A q =
      c * Homogenization.Book.Ch02.symmetricNeumannNu U' A' q := by
  obtain ⟨C', hC'dom, hC'ne⟩ := U'
  subst hUU'
  have hSval : Ch02.symmetricNeumannValueSet U A q =
      c • Ch02.symmetricNeumannValueSet
        (⟨Homogenization.translateSet z (U : Set (Homogenization.Vec d)), hC'dom, hC'ne⟩ :
          Ch02.Domain d) A' q := by
    ext E
    simp only [Ch02.symmetricNeumannValueSet, Set.mem_ofPred_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨Ch02.symmetricNeumannEnergyValue _ A' q ((c⁻¹ • u).translate z),
        ⟨(c⁻¹ • u).translate z, rfl⟩, ?_⟩
      have h := aux_symmetricNeumannEnergyValue_translate_smul U z hC'dom hC'ne A A' c hA q
        (c⁻¹ • u)
      rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] at h
      exact h.symm
    · rintro ⟨y, ⟨u1, rfl⟩, rfl⟩
      refine ⟨c • (H1Function.untranslate z u1), ?_⟩
      have hgrad : ((H1Function.untranslate z u1).translate z).grad = u1.grad := by
        funext y
        rw [H1Function.translate_grad, H1Function.untranslate_grad]
        congr 1
        abel
      rw [aux_symmetricNeumannEnergyValue_translate_smul U z hC'dom hC'ne A A' c hA q
        (H1Function.untranslate z u1),
        aux_symmetricNeumannEnergyValue_eq_of_grad_eq _ A' q hgrad]
  unfold Ch02.symmetricNeumannNu
  rw [hSval, Real.sSup_smul_of_nonneg hc.le, smul_eq_mul]

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
  [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

/-- The scaled-slope inverse-Neumann candidate value scales quadratically. -/
theorem aux_affineNeumannValue_smul (a : PositiveCoefficient Ω) (t : ℝ) (p : Fin d → ℝ)
    (v : meanZeroSobolevGraph Ω) :
    2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        (t • p) i * (t • v : SobolevData Ω).2 i x) -
      ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        a.val x * ((t • v : SobolevData Ω).2 i x * (t • v : SobolevData Ω).2 i x) =
    t ^ 2 * (2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        p i * (v : SobolevData Ω).2 i x) -
      ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        a.val x * ((v : SobolevData Ω).2 i x * (v : SobolevData Ω).2 i x)) := by
  have hcoe : ∀ i : Fin d, (t • v : SobolevData Ω).2 i
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
      fun x => t * (v : SobolevData Ω).2 i x := by
    intro i
    have heq : (t • v : SobolevData Ω).2 i = t • ((v : SobolevData Ω).2 i) := rfl
    rw [heq]
    filter_upwards [Lp.coeFn_smul t ((v : SobolevData Ω).2 i)] with x hx
    simpa using hx
  have hlin : ∀ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
      (t • p) i * (t • v : SobolevData Ω).2 i x =
      t ^ 2 * ∫ x in (Ω : Set (SpatialCoordinates d)), p i * (v : SobolevData Ω).2 i x := by
    intro i
    have hae : (fun x => (t • p) i * (t • v : SobolevData Ω).2 i x)
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        (fun x => (t • p) i * (t * (v : SobolevData Ω).2 i x)) :=
      (hcoe i).mono fun x hx => by simp only [hx]
    rw [MeasureTheory.integral_congr_ae hae]
    have hfun : (fun x => (t • p) i * (t * (v : SobolevData Ω).2 i x)) =
        fun x => t ^ 2 * (p i * (v : SobolevData Ω).2 i x) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun, MeasureTheory.integral_const_mul]
  have hquad : ∀ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
      a.val x * ((t • v : SobolevData Ω).2 i x * (t • v : SobolevData Ω).2 i x) =
      t ^ 2 * ∫ x in (Ω : Set (SpatialCoordinates d)),
        a.val x * ((v : SobolevData Ω).2 i x * (v : SobolevData Ω).2 i x) := by
    intro i
    have hae : (fun x => a.val x *
          ((t • v : SobolevData Ω).2 i x * (t • v : SobolevData Ω).2 i x))
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
        (fun x => a.val x * (t * (v : SobolevData Ω).2 i x * (t * (v : SobolevData Ω).2 i x))) :=
      (hcoe i).mono fun x hx => by simp only [hx]
    rw [MeasureTheory.integral_congr_ae hae]
    have hfun : (fun x => a.val x *
          (t * (v : SobolevData Ω).2 i x * (t * (v : SobolevData Ω).2 i x))) =
        fun x => t ^ 2 * (a.val x * ((v : SobolevData Ω).2 i x * (v : SobolevData Ω).2 i x)) := by
      funext x
      ring
    rw [hfun, MeasureTheory.integral_const_mul]
  calc
    2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          (t • p) i * (t • v : SobolevData Ω).2 i x) -
        ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * ((t • v : SobolevData Ω).2 i x * (t • v : SobolevData Ω).2 i x)
      = 2 * (∑ i : Fin d, t ^ 2 * ∫ x in (Ω : Set (SpatialCoordinates d)),
            p i * (v : SobolevData Ω).2 i x) -
        ∑ i : Fin d, t ^ 2 * ∫ x in (Ω : Set (SpatialCoordinates d)),
            a.val x * ((v : SobolevData Ω).2 i x * (v : SobolevData Ω).2 i x) := by
        rw [Finset.sum_congr rfl (fun i _ => hlin i), Finset.sum_congr rfl (fun i _ => hquad i)]
    _ = t ^ 2 * (2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
            p i * (v : SobolevData Ω).2 i x) -
          ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
            a.val x * ((v : SobolevData Ω).2 i x * (v : SobolevData Ω).2 i x)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring

/-- The zero-slope inverse-Neumann candidate value is zero. -/
theorem aux_affineInverseNeumannResponse_zero
    (hP : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph Ω,
      ‖(w : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) w‖)
    (a : PositiveCoefficient Ω) :
    affineInverseNeumannResponse hP a (0 : Fin d → ℝ) = 0 := by
  have hg := affineInverseNeumannResponse_isGreatest hP a (0 : Fin d → ℝ)
  have hzero : IsGreatest (Set.range fun v : meanZeroSobolevGraph Ω =>
      2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        (0 : Fin d → ℝ) i * (v : SobolevData Ω).2 i x) -
      ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
        a.val x * ((v : SobolevData Ω).2 i x * (v : SobolevData Ω).2 i x)) 0 := by
    constructor
    · refine ⟨0, ?_⟩
      show (2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
            (0 : Fin d → ℝ) i * (0 : SobolevData Ω).2 i x) -
          ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
            a.val x * ((0 : SobolevData Ω).2 i x * (0 : SobolevData Ω).2 i x)) = 0
      have hae2 : ∀ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * ((0 : SobolevData Ω).2 i x * (0 : SobolevData Ω).2 i x) = 0 := by
        intro i
        have h0eq : (0 : SobolevData Ω).2 i = (0 : DomainL2 Ω) := rfl
        have h0 : (0 : SobolevData Ω).2 i
            =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] (0 : SpatialCoordinates d → ℝ) := by
          rw [h0eq]
          exact Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (SpatialCoordinates d)))
        have hae : (fun x => a.val x * ((0 : SobolevData Ω).2 i x * (0 : SobolevData Ω).2 i x))
            =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
            (fun x => a.val x *
              ((0 : SpatialCoordinates d → ℝ) x * (0 : SpatialCoordinates d → ℝ) x)) :=
          h0.mono fun x hx => by simp only [hx]
        rw [MeasureTheory.integral_congr_ae hae]
        simp
      simp only [Pi.zero_apply, zero_mul, MeasureTheory.integral_zero, Finset.sum_const_zero]
      rw [Finset.sum_congr rfl (fun i _ => hae2 i)]
      simp
    · rintro y ⟨v, rfl⟩
      have hnn : (0 : ℝ) ≤ ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * ((v : SobolevData Ω).2 i x * (v : SobolevData Ω).2 i x) := by
        apply Finset.sum_nonneg
        intro i _
        apply MeasureTheory.integral_nonneg_of_ae
        obtain ⟨c0, hc0, hac0⟩ := a.property
        filter_upwards [hac0] with x hx
        have hax : (0 : ℝ) ≤ a.val x := le_of_lt (lt_of_lt_of_le hc0 hx)
        exact mul_nonneg hax (mul_self_nonneg _)
      show (2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
            (0 : Fin d → ℝ) i * (v : SobolevData Ω).2 i x) -
          ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
            a.val x * ((v : SobolevData Ω).2 i x * (v : SobolevData Ω).2 i x)) ≤ 0
      simp only [Pi.zero_apply, zero_mul, MeasureTheory.integral_zero, Finset.sum_const_zero]
      linarith
  exact hg.unique hzero

/-- The inverse affine Neumann response is quadratic in the slope. -/
theorem affineInverseNeumannResponse_smul_slope
    (hP : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph Ω,
      ‖(w : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) w‖)
    (a : PositiveCoefficient Ω) (t : ℝ) (p : Fin d → ℝ) :
    affineInverseNeumannResponse hP a (t • p) = t ^ 2 * affineInverseNeumannResponse hP a p := by
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    rw [zero_smul, zero_pow (two_ne_zero), zero_mul]
    exact aux_affineInverseNeumannResponse_zero hP a
  · have hg1 := affineInverseNeumannResponse_isGreatest hP a (t • p)
    have hg0 := affineInverseNeumannResponse_isGreatest hP a p
    have hg2 : IsGreatest (Set.range fun v : meanZeroSobolevGraph Ω =>
        2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          (t • p) i * (v : SobolevData Ω).2 i x) -
        ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
          a.val x * ((v : SobolevData Ω).2 i x * (v : SobolevData Ω).2 i x))
        (t ^ 2 * affineInverseNeumannResponse hP a p) := by
      constructor
      · obtain ⟨v0, hv0⟩ := hg0.1
        refine ⟨t • v0, ?_⟩
        show (2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
              (t • p) i * (t • v0 : SobolevData Ω).2 i x) -
            ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
              a.val x * ((t • v0 : SobolevData Ω).2 i x * (t • v0 : SobolevData Ω).2 i x)) =
          t ^ 2 * affineInverseNeumannResponse hP a p
        have hv0' : (2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
              p i * (v0 : SobolevData Ω).2 i x) -
            ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
              a.val x * ((v0 : SobolevData Ω).2 i x * (v0 : SobolevData Ω).2 i x)) =
          affineInverseNeumannResponse hP a p := hv0
        rw [aux_affineNeumannValue_smul a t p v0, hv0']
      · rintro y ⟨w, rfl⟩
        show (2 * (∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
              (t • p) i * (w : SobolevData Ω).2 i x) -
            ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)),
              a.val x * ((w : SobolevData Ω).2 i x * (w : SobolevData Ω).2 i x)) ≤
          t ^ 2 * affineInverseNeumannResponse hP a p
        have hvw : t • (t⁻¹ • w) = w := by
          rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
        have hvw2 : t • ((t⁻¹ • w : meanZeroSobolevGraph Ω) : SobolevData Ω) =
            (w : SobolevData Ω) := by
          show ((t • (t⁻¹ • w) : meanZeroSobolevGraph Ω) : SobolevData Ω) = (w : SobolevData Ω)
          rw [hvw]
        rw [← hvw2, aux_affineNeumannValue_smul a t p (t⁻¹ • w)]
        have hle := hg0.2 (Set.mem_range_self (t⁻¹ • w))
        have ht2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
        nlinarith [hle, ht2]
    exact hg1.unique hg2

/-- Translating an open coordinate cube by its own half-diagonal recentres it: the unit
Neumann cube is the origin cube translated by `(1/2,…,1/2)`. -/
theorem aux_unitNeumannCube_eq_translate (d : ℕ) :
    (_root_.SubdiffusiveProcess.EllipticRegularity.unitNeumannCube d : Set (SpatialCoordinates d)) =
      Homogenization.translateSet (fun _ : Fin d => (1 / 2 : ℝ))
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) := by
  ext x
  rw [Homogenization.mem_translateSet_iff_sub_mem]
  show x ∈ Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) ↔
    x - (fun _ : Fin d => (1 / 2 : ℝ)) ∈ Metric.ball (0 : SpatialCoordinates d) (1 / 2)
  rw [Metric.mem_ball, Metric.mem_ball, dist_eq_norm, dist_eq_norm, sub_zero]

/-- Origin cube versus unit Neumann cube: translation by `(1/2,…,1/2)` and rescaling by `c`. -/
theorem affineInverseNeumannResponse_origin_eq_unit {d : ℕ} [NeZero d]
    (f g : SpatialCoordinates d → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfpos : ∀ x, 0 < f x) (hgpos : ∀ x, 0 < g x) (c : ℝ) (hc : 0 < c)
    (hfg : ∀ y : SpatialCoordinates d, f ((fun _ : Fin d => (1 / 2 : ℝ)) + y) = c * g y)
    (hN0 : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) w‖)
    (hNn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (_root_.SubdiffusiveProcess.EllipticRegularity.unitNeumannCube d),
      ‖(w : SobolevData (_root_.SubdiffusiveProcess.EllipticRegularity.unitNeumannCube d)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (_root_.SubdiffusiveProcess.EllipticRegularity.unitNeumannCube d)) w‖)
    (aP : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (haP : (aP.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Set (SpatialCoordinates d))] g)
    (bP : PositiveCoefficient (_root_.SubdiffusiveProcess.EllipticRegularity.unitNeumannCube d))
    (hbP : (bP.val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (_root_.SubdiffusiveProcess.EllipticRegularity.unitNeumannCube d : Set (SpatialCoordinates d))] f)
    (q : Fin d → ℝ) :
    affineInverseNeumannResponse hN0 aP q = c * affineInverseNeumannResponse hNn bP q := by
  have hne : ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      (centeredCube z r hr : Set (SpatialCoordinates d)).Nonempty :=
    fun z r hr => ⟨z, Metric.mem_ball_self (half_pos hr)⟩
  let U0 : Ch02.Domain d :=
    ⟨(centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      isOpenBoundedConvexDomain_centeredCube 0 one_pos, hne 0 1 one_pos⟩
  let U1 : Ch02.Domain d :=
    ⟨(_root_.SubdiffusiveProcess.EllipticRegularity.unitNeumannCube d : Set (SpatialCoordinates d)),
      isOpenBoundedConvexDomain_centeredCube (fun _ => (1 / 2 : ℝ)) one_pos,
      hne (fun _ => (1 / 2 : ℝ)) 1 one_pos⟩
  have data0 : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U0 g :=
    Classical.choice
      (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
        hg hgpos U0)
  have data1 : SubdiffusiveProcess.CoarseGrainingVocab.ScalarCoeffOnData U1 f :=
    Classical.choice
      (SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_scalarCoeffOnData_of_continuous_pos
        hf hfpos U1)
  have hUU' : (U1 : Set (SpatialCoordinates d)) =
      Homogenization.translateSet (fun _ : Fin d => (1 / 2 : ℝ))
        (U0 : Set (SpatialCoordinates d)) :=
    aux_unitNeumannCube_eq_translate d
  have hA : ∀ x : SpatialCoordinates d,
      data1.toCoeffOn.toCoeffField (x + (fun _ : Fin d => (1 / 2 : ℝ))) =
        c • data0.toCoeffOn.toCoeffField x := by
    intro x
    show SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField f (x + (fun _ : Fin d => (1 / 2 : ℝ))) =
      c • SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField g x
    unfold SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField
    rw [show x + (fun _ : Fin d => (1 / 2 : ℝ)) = (fun _ : Fin d => (1 / 2 : ℝ)) + x from by abel,
      hfg x]
    show Homogenization.scalarMatrix (c * g x) = c • Homogenization.scalarMatrix (g x)
    unfold Homogenization.scalarMatrix
    rw [mul_smul]
  have hV0 : volume.real (U0 : Set (SpatialCoordinates d)) = 1 := by
    show volume.real (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)) = 1
    rw [centeredCube_volume_real]
    exact one_pow d
  have hV1 : volume.real (U1 : Set (SpatialCoordinates d)) = 1 := by
    show volume.real (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
      Set (SpatialCoordinates d)) = 1
    rw [centeredCube_volume_real]
    exact one_pow d
  have hb0 := _root_.SubdiffusiveProcess.EllipticRegularity.symmetricNeumannNu_eq_affineInverseNeumannResponse
    (Om := centeredCube (0 : SpatialCoordinates d) 1 one_pos)
    (isOpenBoundedConvexDomain_centeredCube 0 one_pos) (hne 0 1 one_pos) data0 hN0 aP haP
    (centeredCube_volume_pos 0 one_pos) q
  have hb1 := _root_.SubdiffusiveProcess.EllipticRegularity.symmetricNeumannNu_eq_affineInverseNeumannResponse
    (Om := _root_.SubdiffusiveProcess.EllipticRegularity.unitNeumannCube d)
    (isOpenBoundedConvexDomain_centeredCube (fun _ => (1 / 2 : ℝ)) one_pos)
    (hne (fun _ => (1 / 2 : ℝ)) 1 one_pos) data1 hNn bP hbP
    (centeredCube_volume_pos (fun _ => (1 / 2 : ℝ)) one_pos) q
  have hb0' : Ch02.symmetricNeumannNu U0 data0.toCoeffOn q =
      affineInverseNeumannResponse hN0 aP q / 2 := by rw [hb0, hV0]; norm_num
  have hb1' : Ch02.symmetricNeumannNu U1 data1.toCoeffOn q =
      affineInverseNeumannResponse hNn bP q / 2 := by rw [hb1, hV1]; norm_num
  have hT1 := symmetricNeumannNu_translate_smul U0 U1 (fun _ => (1 / 2 : ℝ)) hUU'
    data0.toCoeffOn data1.toCoeffOn c hc hA q
  rw [hb0', hb1'] at hT1
  linarith [hT1]

end SubdiffusiveProcess
