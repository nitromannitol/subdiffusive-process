module

public import SubdiffusiveProcess.Paper.lem_localized_perturbation
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Sobolev.PotentialPerturbation
public import SubdiffusiveProcess.Sobolev.PotentialResponses
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane2.LimitForm
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal

namespace Paper

private theorem aux_scalar_sharp (A W C U V : ℝ) (hA : 0 ≤ A) (hW : 0 < W)
    (hQ : |W - 1| / Real.sqrt W ≤ C) :
    A * |W - 1| * |U * V| ≤
      C ^ 2 / 2 * (A * U ^ 2) + 1 / 2 * (W * A * V ^ 2) := by
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.2 hW
  have hq : |W - 1| ≤ C * Real.sqrt W :=
    (div_le_iff₀ hsW).mp hQ
  have hYoung := relative_young_mul C (Real.sqrt A * |U|)
    (Real.sqrt (W * A) * |V|) (by norm_num : (0 : ℝ) < 1)
  have hsA : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
  have hsWA : 0 ≤ Real.sqrt (W * A) := Real.sqrt_nonneg _
  have hsA_sq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
  have hsWA_sq : (Real.sqrt (W * A)) ^ 2 = W * A :=
    Real.sq_sqrt (mul_nonneg hW.le hA)
  have hleft : A * (C * Real.sqrt W) * |U * V| =
      C * (Real.sqrt A * |U|) * (Real.sqrt (W * A) * |V|) := by
    have hAroot : Real.sqrt A * Real.sqrt A = A := by
      nlinarith [hsA_sq]
    have hsqrtWA : Real.sqrt (W * A) = Real.sqrt W * Real.sqrt A := by
      rw [show W * A = A * W by ring, Real.sqrt_mul hA W]
      ring
    calc
      A * (C * Real.sqrt W) * |U * V| =
          (Real.sqrt A * Real.sqrt A) * (C * Real.sqrt W) * (|U| * |V|) := by
            rw [hAroot, abs_mul]
      _ = C * (Real.sqrt A * |U|) * (Real.sqrt (W * A) * |V|) := by
        rw [hsqrtWA]
        ring
  have hYoung' : C * (Real.sqrt A * |U|) * (Real.sqrt (W * A) * |V|) ≤
      C ^ 2 / 2 * (Real.sqrt A * |U|) ^ 2 +
        1 / 2 * (Real.sqrt (W * A) * |V|) ^ 2 := by
    simpa [abs_mul, abs_of_nonneg hsA, abs_abs,
      abs_of_nonneg hsWA, one_mul, div_one, mul_assoc] using hYoung
  have hright : C ^ 2 / 2 * (Real.sqrt A * |U|) ^ 2 +
      1 / 2 * (Real.sqrt (W * A) * |V|) ^ 2 =
      C ^ 2 / 2 * (A * U ^ 2) + 1 / 2 * (W * A * V ^ 2) := by
    rw [mul_pow, hsA_sq, mul_pow, hsWA_sq, sq_abs, sq_abs]
  calc
    A * |W - 1| * |U * V| ≤ A * (C * Real.sqrt W) * |U * V| := by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq (abs_nonneg _)) hA)
    _ = C * (Real.sqrt A * |U|) * (Real.sqrt (W * A) * |V|) := hleft
    _ ≤ C ^ 2 / 2 * (Real.sqrt A * |U|) ^ 2 +
        1 / 2 * (Real.sqrt (W * A) * |V|) ^ 2 := hYoung'
    _ = _ := hright

private theorem aux_weightedL2_sharp
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (a b : Lp ℝ ∞ μ) (w : α → ℝ) (C : ℝ) {s : Set α}
    (hs : MeasurableSet s)
    (ha : ∀ᵐ x ∂μ, 0 ≤ a x)
    (hweight : ∀ᵐ x ∂μ, b x = w x * a x)
    (hw : ∀ᵐ x ∂μ, 0 < w x)
    (hsharp : ∀ᵐ x ∂μ, |w x - 1| / Real.sqrt (w x) ≤ C)
    (hsupp : ∀ᵐ x ∂μ, x ∉ s → b x = a x)
    (u v : Lp ℝ 2 μ) :
    |weightedL2Form b u v - weightedL2Form a u v| ≤
      C ^ 2 / 2 * weightedL2Form a (localizeL2 hs u) (localizeL2 hs u) +
        1 / 2 * weightedL2Form b v v := by
  rw [weightedL2Form_difference_localize_left a b hs hsupp]
  rw [weightedL2Form_apply, weightedL2Form_apply]
  rw [← integral_sub (integrable_weighted_inner b (localizeL2 hs u) v)
    (integrable_weighted_inner a (localizeL2 hs u) v)]
  calc
    _ ≤ ∫ x, |b x * inner ℝ ((localizeL2 hs u) x) (v x) -
        a x * inner ℝ ((localizeL2 hs u) x) (v x)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, C ^ 2 / 2 * (a x * inner ℝ ((localizeL2 hs u) x)
          ((localizeL2 hs u) x)) +
        1 / 2 * (b x * inner ℝ (v x) (v x)) ∂μ := by
      apply integral_mono_ae
        ((integrable_weighted_inner b (localizeL2 hs u) v).sub
          (integrable_weighted_inner a (localizeL2 hs u) v)).norm
        (((integrable_weighted_inner a (localizeL2 hs u) (localizeL2 hs u)).const_mul _).add
          ((integrable_weighted_inner b v v).const_mul _))
      filter_upwards [hweight, hw, hsharp, ha, localizeL2_coeFn hs u] with
          x hba hwx hcx hax hloc
      simp only [Pi.sub_apply, Real.norm_eq_abs]
      rw [← sub_mul, hba]
      dsimp
      by_cases hx : x ∈ s
      ·
        have hloc' : localizeL2 hs u x = u x := by
          simpa [Set.indicator_of_mem hx] using hloc
        simp only [hloc', RCLike.inner_apply, conj_trivial, real_inner_self_eq_norm_sq,
          Real.norm_eq_abs, sq_abs, abs_mul, abs_of_nonneg hax]
        rw [hba, show w x * a x - a x = (w x - 1) * a x by ring,
          abs_mul, abs_of_nonneg hax]
        have hpoint := aux_scalar_sharp (a x) (w x) C (u x) (v x)
          hax hwx hcx
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hpoint
      · have hloc0 : localizeL2 hs u x = 0 := by
          simpa [Set.indicator_of_notMem hx] using hloc
        have hbx : 0 ≤ b x := by rw [hba]; positivity
        have hnonneg : 0 ≤ (1 / 2 : ℝ) * (b x * (v x) ^ 2) :=
          mul_nonneg (by norm_num) (mul_nonneg hbx (sq_nonneg (v x)))
        simpa [pow_two, hloc0, RCLike.inner_apply, conj_trivial, hba] using hnonneg
    _ = _ := by
      rw [integral_add]
      · rw [integral_const_mul, integral_const_mul, weightedL2Form_apply,
          weightedL2Form_apply]
      · exact (integrable_weighted_inner a (localizeL2 hs u) (localizeL2 hs u)).const_mul _
      · exact (integrable_weighted_inner b v v).const_mul _

private theorem aux_weightedGradient_sharp
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a b : PositiveCoefficient Ω) (w : SpatialCoordinates d → ℝ) (C : ℝ)
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s)
    (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), 0 ≤ a.val x)
    (hweight : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      b.val x = w x * a.val x)
    (hw : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), 0 < w x)
    (hsharp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      |w x - 1| / Real.sqrt (w x) ≤ C)
    (hsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      x ∉ s → b.val x = a.val x)
    (u v : HilbertGradient Ω) :
    |weightedGradientForm b.val u v - weightedGradientForm a.val u v| ≤
      C ^ 2 / 2 * localGradientEnergy a hs u +
        1 / 2 * weightedGradientForm b.val v v := by
  simp only [weightedGradientForm, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.bilinearComp_apply, PiLp.proj_apply, localGradientEnergy]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin d, |weightedL2Form b.val (u i) (v i) -
        weightedL2Form a.val (u i) (v i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d, (C ^ 2 / 2 * weightedL2Form a.val
          (localizeL2 hs (u i)) (localizeL2 hs (u i)) +
        1 / 2 * weightedL2Form b.val (v i) (v i)) := by
      exact Finset.sum_le_sum fun i _ =>
        aux_weightedL2_sharp (volume.restrict (Ω : Set (SpatialCoordinates d)))
          a.val b.val w C hs ha hweight hw hsharp hsupp (u i) (v i)
    _ = C ^ 2 / 2 * ∑ i : Fin d, weightedL2Form a.val
          (localizeL2 hs (u i)) (localizeL2 hs (u i)) +
        1 / 2 * ∑ i : Fin d, weightedL2Form b.val (v i) (v i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private theorem aux_gradient_difference_energy
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a b : PositiveCoefficient Ω) (w : SpatialCoordinates d → ℝ) (C : ℝ)
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s)
    (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), 0 ≤ a.val x)
    (hweight : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      b.val x = w x * a.val x)
    (hw : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), 0 < w x)
    (hsharp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      |w x - 1| / Real.sqrt (w x) ≤ C)
    (hsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      x ∉ s → b.val x = a.val x)
    (u v : HilbertGradient Ω)
    (heq : weightedGradientForm b.val v (v - u) =
      weightedGradientForm a.val u (v - u)) :
    weightedGradientForm b.val (v - u) (v - u) ≤
      C ^ 2 * localGradientEnergy a hs u := by
  have hd := bilinear_solution_difference (weightedGradientForm a.val)
    (weightedGradientForm b.val) u v heq
  have hsharp' := aux_weightedGradient_sharp a b w C hs ha hweight hw hsharp hsupp
    u (v - u)
  have hnonneg : 0 ≤ weightedGradientForm b.val (v - u) (v - u) := by
    simp only [weightedGradientForm, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.bilinearComp_apply, PiLp.proj_apply]
    exact Finset.sum_nonneg fun i _ =>
      weightedL2Form_nonneg b.val (positiveCoefficient_ae_nonneg b) ((v - u) i)
  have hkey : weightedGradientForm b.val (v - u) (v - u) ≤
      C ^ 2 / 2 * localGradientEnergy a hs u +
        1 / 2 * weightedGradientForm b.val (v - u) (v - u) := by
    calc
      weightedGradientForm b.val (v - u) (v - u) =
          -(weightedGradientForm b.val u (v - u) -
            weightedGradientForm a.val u (v - u)) := hd
      _ ≤
          |weightedGradientForm b.val u (v - u) -
            weightedGradientForm a.val u (v - u)| := neg_le_abs _
      _ ≤ C ^ 2 / 2 * localGradientEnergy a hs u +
          1 / 2 * weightedGradientForm b.val (v - u) (v - u) := hsharp'
  nlinarith

private theorem aux_gradient_sharp_pair
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a b : PositiveCoefficient Ω) (w : SpatialCoordinates d → ℝ) (C k : ℝ)
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s)
    (ha : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), 0 ≤ a.val x)
    (hweight : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      b.val x = w x * a.val x)
    (hw : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)), 0 < w x)
    (hsharp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      |w x - 1| / Real.sqrt (w x) ≤ C)
    (hsupp : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      x ∉ s → b.val x = a.val x)
    (hupper : ∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      b.val x ≤ k ^ 2 * a.val x)
    (hC : 0 ≤ C) (hk : 0 ≤ k) (hC2 : C ^ 2 ≤ k ^ 2)
    (u v : HilbertGradient Ω)
    (heq : weightedGradientForm b.val v (v - u) =
      weightedGradientForm a.val u (v - u)) :
    Real.sqrt (weightedGradientForm b.val (v - u) (v - u)) ≤
        C * Real.sqrt (localGradientEnergy a hs u) ∧
      Real.sqrt (localGradientEnergy b hs v) ≤
        2 * k * Real.sqrt (localGradientEnergy a hs u) := by
  let mass := localGradientEnergy a hs u
  have hmass : 0 ≤ mass := localGradientEnergy_nonneg a hs u
  have hdiff := aux_gradient_difference_energy a b w C hs ha hweight hw hsharp hsupp
    u v heq
  have hdiffsqrt : Real.sqrt (weightedGradientForm b.val (v - u) (v - u)) ≤
      C * Real.sqrt mass := by
    calc
      _ ≤ Real.sqrt (C ^ 2 * mass) := Real.sqrt_le_sqrt hdiff
      _ = C * Real.sqrt mass := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs, abs_of_nonneg hC]
  have hbu : localGradientEnergy b hs u ≤ k ^ 2 * mass :=
    localGradientEnergy_le_mul b a (k ^ 2) hupper hs u
  have hbd : localGradientEnergy b hs (v - u) ≤
      weightedGradientForm b.val (v - u) (v - u) :=
    localGradientEnergy_le b hs (v - u)
  have htri := localGradientEnergy_sub_le b hs v u
  have hlocal : localGradientEnergy b hs v ≤ 4 * k ^ 2 * mass := by
    calc
      localGradientEnergy b hs v ≤
          2 * localGradientEnergy b hs u +
            2 * localGradientEnergy b hs (v - u) := htri
      _ ≤ 2 * k ^ 2 * mass +
          2 * (C ^ 2 * mass) := by
        exact add_le_add
          (by simpa [mul_assoc] using
            (mul_le_mul_of_nonneg_left hbu (by norm_num : (0 : ℝ) ≤ 2)))
          (mul_le_mul_of_nonneg_left (hbd.trans hdiff)
            (by norm_num : (0 : ℝ) ≤ 2))
      _ ≤ 4 * k ^ 2 * mass := by
        nlinarith [mul_nonneg hmass (sq_nonneg k)]
  have hlocalsqrt : Real.sqrt (localGradientEnergy b hs v) ≤
      2 * k * Real.sqrt mass := by
    calc
      _ ≤ Real.sqrt (4 * k ^ 2 * mass) := Real.sqrt_le_sqrt hlocal
      _ = 2 * k * Real.sqrt mass := by
        have hk2 : 0 ≤ k ^ 2 := sq_nonneg k
        have hksq : Real.sqrt (4 * k ^ 2) = 2 * k := by
          rw [show 4 * k ^ 2 = (2 * k) ^ 2 by ring,
            Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hk)]
        rw [Real.sqrt_mul (mul_nonneg (by norm_num) hk2), hksq]
  exact ⟨hdiffsqrt, hlocalsqrt⟩

private theorem aux_exp_half_identity (y : ℝ) :
    (Real.exp y - 1) / Real.sqrt (Real.exp y) =
      Real.exp (y / 2) - Real.exp (-y / 2) := by
  rw [← Real.exp_half y]
  field_simp [Real.exp_ne_zero]
  rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
  rw [show y / 2 + y / 2 = y by ring,
    show y / 2 + -(y / 2) = 0 by ring, Real.exp_zero]

private theorem aux_exp_sharp {y s : ℝ} (hy : |y| ≤ s) :
    |Real.exp y - 1| / Real.sqrt (Real.exp y) ≤
      Real.exp (s / 2) - Real.exp (-s / 2) := by
  have hden : 0 < Real.sqrt (Real.exp y) := Real.sqrt_pos.2 (Real.exp_pos y)
  have hylo : -s ≤ y := (abs_le.mp hy).1
  have hyhi : y ≤ s := (abs_le.mp hy).2
  calc
    |Real.exp y - 1| / Real.sqrt (Real.exp y) =
        |(Real.exp y - 1) / Real.sqrt (Real.exp y)| := by
      rw [abs_div, abs_of_pos hden]
    _ = |Real.exp (y / 2) - Real.exp (-y / 2)| := by
      rw [aux_exp_half_identity]
    _ ≤ Real.exp (s / 2) - Real.exp (-s / 2) := by
      by_cases hy0 : 0 ≤ y
      · have hdiff : 0 ≤ Real.exp (y / 2) - Real.exp (-y / 2) :=
          sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith [hy0]))
        rw [abs_of_nonneg hdiff]
        have h1 : Real.exp (y / 2) ≤ Real.exp (s / 2) :=
          Real.exp_le_exp.mpr (by linarith [hyhi])
        have h2 : Real.exp (-s / 2) ≤ Real.exp (-y / 2) :=
          Real.exp_le_exp.mpr (by linarith [hy0])
        exact sub_le_sub h1 h2
      · have hy0' : y ≤ 0 := le_of_not_ge hy0
        have hdiff : Real.exp (y / 2) - Real.exp (-y / 2) ≤ 0 :=
          sub_nonpos.mpr (Real.exp_le_exp.mpr (by linarith [hy0']))
        rw [abs_of_nonpos hdiff]
        have h1 : Real.exp (-y / 2) ≤ Real.exp (s / 2) :=
          Real.exp_le_exp.mpr (by linarith [hylo])
        have h2 : Real.exp (-s / 2) ≤ Real.exp (y / 2) :=
          Real.exp_le_exp.mpr (by linarith [hyhi])
        simpa only [neg_sub] using sub_le_sub h1 h2




theorem cor_14_gradient_sharp_energy :
    ∀ (d : ℕ) (Q : Opens (SpatialCoordinates d)) (S : ResponseSpace Q)
        (h g : Lp ℝ ∞ (volume.restrict (Q : Set (SpatialCoordinates d))))
        (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B)
        (hsupp : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), x ∉ B → g x = 0),
      let a := expPotentialCoefficient h
      let b := expPotentialCoefficient (h + g)
      let s := ‖g‖
      (∀ L : S.space →L[ℝ] ℝ,
        let u := responseSolution S a L
        let ug := responseSolution S b L
        let mass := localGradientEnergy a hB (subspaceGradient S.space u)
        Real.sqrt (responseForm S b (ug - u) (ug - u)) ≤
            (Real.exp (s / 2) - Real.exp (-s / 2)) * Real.sqrt mass ∧
          Real.sqrt (localGradientEnergy b hB (subspaceGradient S.space ug)) ≤
            2 * Real.exp (s / 2) * Real.sqrt mass) ∧
      (∀ f : weakSobolevGraph Q,
        let u := dirichletMinimizer S a f
        let ug := dirichletMinimizer S b f
        let mass := localGradientEnergy a hB (sobolevGradient u.val)
        Real.sqrt (sobolevCoefficientForm b (ug.val - u.val) (ug.val - u.val)) ≤
            (Real.exp (s / 2) - Real.exp (-s / 2)) * Real.sqrt mass ∧
          Real.sqrt (localGradientEnergy b hB (sobolevGradient ug.val)) ≤
          2 * Real.exp (s / 2) * Real.sqrt mass) := by
  intro d Q S h g B hB hsupp
  dsimp
  let a := expPotentialCoefficient h
  let b := expPotentialCoefficient (h + g)
  let C := Real.exp (‖g‖ / 2) - Real.exp (-‖g‖ / 2)
  let k := Real.exp (‖g‖ / 2)
  let w : SpatialCoordinates d → ℝ := fun x => Real.exp (g x)
  have hnorm : 0 ≤ ‖g‖ := norm_nonneg _
  have hC : 0 ≤ C := by
    dsimp [C]
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hk : 0 ≤ k := by
    dsimp [k]
    exact (Real.exp_pos _).le
  have hmeas : Measurable w := by
    dsimp [w]
    fun_prop
  have ha : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), 0 ≤ a.val x :=
    positiveCoefficient_ae_nonneg a
  have hweight :
      ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        b.val x = w x * a.val x := by
    filter_upwards [expPotentialCoefficient_coeFn (h + g),
      expPotentialCoefficient_coeFn h, Lp.coeFn_add h g] with x hbg hah hsum
    rw [hbg, hsum, Pi.add_apply, Real.exp_add, hah]
    dsimp [w]
    ring
  have hw : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), 0 < w x := by
    filter_upwards [] with x
    dsimp [w]
    exact Real.exp_pos _
  have hsharp :
      ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        |w x - 1| / Real.sqrt (w x) ≤ C := by
    filter_upwards [boundedPotential_ae_bound g] with x hx
    dsimp [w, C]
    exact aux_exp_sharp hx
  have hsupp' :
      ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        x ∉ B → b.val x = a.val x := by
    filter_upwards [expPotentialCoefficient_coeFn (h + g),
      expPotentialCoefficient_coeFn h, Lp.coeFn_add h g, hsupp] with
      x hbg hah hsum hg
    intro hx
    rw [hbg, hsum, Pi.add_apply, hg hx, add_zero]
    exact hah.symm
  have hupper :
      ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
        b.val x ≤ k ^ 2 * a.val x := by
    filter_upwards [hweight, ha, boundedPotential_ae_bound g] with x hba hax hx
    have hwupper : Real.exp (g x) ≤ Real.exp ‖g‖ :=
      Real.exp_le_exp.mpr ((le_abs_self _).trans hx)
    have hk_sq : k ^ 2 = Real.exp ‖g‖ := by
      dsimp [k]
      rw [pow_two, ← Real.exp_add]
      congr 1 <;> ring
    rw [hba, hk_sq]
    dsimp [w]
    exact mul_le_mul_of_nonneg_right hwupper hax
  have hC2 : C ^ 2 ≤ k ^ 2 := by
    have hCl : C ≤ k := by
      dsimp [C, k]
      linarith [Real.exp_nonneg (-‖g‖ / 2)]
    exact sq_le_sq₀ hC (by exact hk) |>.mpr hCl
  constructor
  · intro L
    let u := responseSolution S a L
    let ug := responseSolution S b L
    let hu := subspaceGradient S.space u
    let hv := subspaceGradient S.space ug
    have heq₀ : responseForm S b ug (ug - u) =
        responseForm S a u (ug - u) :=
      (responseSolution_spec S b L (ug - u)).trans
        (responseSolution_spec S a L (ug - u)).symm
    have heq : weightedGradientForm b.val hv (hv - hu) =
        weightedGradientForm a.val hu (hv - hu) := by
      change weightedGradientForm b.val hv
          (subspaceGradient S.space (ug - u)) =
        weightedGradientForm a.val hu
          (subspaceGradient S.space (ug - u)) at heq₀
      simpa only [map_sub] using heq₀
    have hp := aux_gradient_sharp_pair a b w C k hB ha hweight hw hsharp hsupp'
      hupper hC hk hC2 hu hv heq
    simpa only [a, b, C, k, u, ug, hu, hv, responseForm,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.bilinearComp_apply, map_sub] using hp
  · intro f
    let u := dirichletMinimizer S a f
    let ug := dirichletMinimizer S b f
    let hu := sobolevGradient u.val
    let hv := sobolevGradient ug.val
    let z : S.space := ⟨ug.val - u.val, by
      convert S.space.sub_mem (dirichletMinimizer_mem_affine S b f)
        (dirichletMinimizer_mem_affine S a f) using 1
      abel⟩
    have ha0 := dirichletMinimizer_euler S a f z
    have hb0 := dirichletMinimizer_euler S b f z
    change weightedGradientForm a.val hu
        (sobolevGradient (ug.val - u.val)) = 0 at ha0
    change weightedGradientForm b.val hv
        (sobolevGradient (ug.val - u.val)) = 0 at hb0
    have heq : weightedGradientForm b.val hv (hv - hu) =
        weightedGradientForm a.val hu (hv - hu) := by
      have heq₀ : weightedGradientForm b.val hv
          (sobolevGradient (ug.val - u.val)) =
          weightedGradientForm a.val hu
            (sobolevGradient (ug.val - u.val)) := hb0.trans ha0.symm
      simpa only [map_sub] using heq₀
    have hp := aux_gradient_sharp_pair a b w C k hB ha hweight hw hsharp hsupp'
      hupper hC hk hC2 hu hv heq
    simpa only [a, b, C, k, u, ug, hu, hv, sobolevCoefficientForm,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.bilinearComp_apply, map_sub] using hp

end Paper
