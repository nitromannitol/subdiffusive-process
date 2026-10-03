module

public import SubdiffusiveProcess.PartProcess.LpRestriction

@[expose] public section

open MeasureTheory Filter Topology Set
noncomputable section
namespace SubdiffusiveProcess.PartProcess
variable {X : Type*} [MeasurableSpace X] {m : Measure X}

theorem memLp_mul_bounded (q : X → ℝ) (hq : Measurable q)
    (B : ℝ) (hB : 0 ≤ B) (hqb : ∀ x, |q x| ≤ B)
    (u : Lp ℝ 2 m) : MemLp (fun x => q x * u x) 2 m := by
  apply (Lp.memLp u).of_le_mul (c := B)
    (hq.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
  exact ae_of_all _ (fun x => by
    change ‖q x * u x‖ ≤ B * ‖u x‖
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hqb x) (norm_nonneg _))

def multiplyLp (q : X → ℝ) (hq : Measurable q)
    (B : ℝ) (hB : 0 ≤ B) (hqb : ∀ x, |q x| ≤ B)
    (u : Lp ℝ 2 m) : Lp ℝ 2 m :=
  (memLp_mul_bounded q hq B hB hqb u).toLp (fun x => q x * u x)

theorem multiplyLp_coe (q : X → ℝ) (hq : Measurable q)
    (B : ℝ) (hB : 0 ≤ B) (hqb : ∀ x, |q x| ≤ B) (u : Lp ℝ 2 m) :
    ⇑(multiplyLp q hq B hB hqb u) =ᵐ[m] fun x => q x * u x :=
  MemLp.coeFn_toLp _

theorem multiplyLp_add (q : X → ℝ) (hq : Measurable q)
    (B : ℝ) (hB : 0 ≤ B) (hqb : ∀ x, |q x| ≤ B) (u v : Lp ℝ 2 m) :
    multiplyLp q hq B hB hqb (u + v) =
      multiplyLp q hq B hB hqb u + multiplyLp q hq B hB hqb v := by
  apply Lp.ext
  filter_upwards [multiplyLp_coe q hq B hB hqb (u + v),
    multiplyLp_coe q hq B hB hqb u, multiplyLp_coe q hq B hB hqb v,
    Lp.coeFn_add (multiplyLp q hq B hB hqb u) (multiplyLp q hq B hB hqb v),
    Lp.coeFn_add u v] with x h0 h1 h2 h3 h4
  rw [h0, h3]
  simp only [Pi.add_apply, h1, h2, h4, Pi.add_apply]
  ring

theorem multiplyLp_smul (q : X → ℝ) (hq : Measurable q)
    (B : ℝ) (hB : 0 ≤ B) (hqb : ∀ x, |q x| ≤ B) (a : ℝ) (u : Lp ℝ 2 m) :
    multiplyLp q hq B hB hqb (a • u) = a • multiplyLp q hq B hB hqb u := by
  apply Lp.ext
  filter_upwards [multiplyLp_coe q hq B hB hqb (a • u),
    multiplyLp_coe q hq B hB hqb u,
    Lp.coeFn_smul a (multiplyLp q hq B hB hqb u), Lp.coeFn_smul a u] with x h0 h1 h2 h3
  rw [h0, h2]
  simp only [Pi.smul_apply, h1, h3, Pi.smul_apply, smul_eq_mul]
  ring

theorem norm_multiplyLp_le (q : X → ℝ) (hq : Measurable q)
    (B : ℝ) (hB : 0 ≤ B) (hqb : ∀ x, |q x| ≤ B) (u : Lp ℝ 2 m) :
    ‖multiplyLp q hq B hB hqb u‖ ≤ B * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplyLp_coe q hq B hB hqb u] with x hx
  rw [hx, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hqb x) (norm_nonneg _)

def multiplication (q : X → ℝ) (hq : Measurable q)
    (B : ℝ) (hB : 0 ≤ B) (hqb : ∀ x, |q x| ≤ B) : Lp ℝ 2 m →L[ℝ] Lp ℝ 2 m :=
  LinearMap.mkContinuous
    { toFun := multiplyLp q hq B hB hqb
      map_add' := multiplyLp_add q hq B hB hqb
      map_smul' := multiplyLp_smul q hq B hB hqb }
    B (norm_multiplyLp_le q hq B hB hqb)

theorem inner_multiplication (q : X → ℝ) (hq : Measurable q)
    (B : ℝ) (hB : 0 ≤ B) (hqb : ∀ x, |q x| ≤ B) (u v : Lp ℝ 2 m) :
    inner ℝ (multiplication q hq B hB hqb u) v = ∫ x, q x * u x * v x ∂m := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiplyLp_coe q hq B hB hqb u] with x hx
  change inner ℝ (multiplyLp q hq B hB hqb u x) (v x) = _
  rw [hx, RCLike.inner_apply]
  simp only [conj_trivial]
  ring

theorem inner_multiplication_symm (q : X → ℝ) (hq : Measurable q)
    (B : ℝ) (hB : 0 ≤ B) (hqb : ∀ x, |q x| ≤ B) (u v : Lp ℝ 2 m) :
    inner ℝ (multiplication q hq B hB hqb u) v =
      inner ℝ (multiplication q hq B hB hqb v) u := by
  rw [inner_multiplication, inner_multiplication]
  apply integral_congr_ae
  exact ae_of_all _ (fun _ => by ring)

theorem inner_multiplication_nonneg (q : X → ℝ) (hq : Measurable q)
    (B : ℝ) (hB : 0 ≤ B) (hqb : ∀ x, |q x| ≤ B) (hq0 : ∀ x, 0 ≤ q x)
    (u : Lp ℝ 2 m) : 0 ≤ inner ℝ (multiplication q hq B hB hqb u) u := by
  rw [inner_multiplication]
  apply integral_nonneg
  intro x
  change 0 ≤ q x * u x * u x
  rw [mul_assoc]
  exact mul_nonneg (hq0 x) (mul_self_nonneg _)

theorem inner_multiplication_le (q : X → ℝ) (hq : Measurable q)
    (B : ℝ) (hB : 0 ≤ B) (hqb : ∀ x, |q x| ≤ B) (u : Lp ℝ 2 m) :
    inner ℝ (multiplication q hq B hB hqb u) u ≤ B * ‖u‖ ^ 2 := by
  calc
    inner ℝ (multiplication q hq B hB hqb u) u ≤
        ‖multiplication q hq B hB hqb u‖ * ‖u‖ := real_inner_le_norm _ _
    _ ≤ (B * ‖u‖) * ‖u‖ :=
      mul_le_mul_of_nonneg_right (norm_multiplyLp_le q hq B hB hqb u) (norm_nonneg _)
    _ = _ := by ring

end SubdiffusiveProcess.PartProcess
