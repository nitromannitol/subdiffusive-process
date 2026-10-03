module

public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

open Set Topology

noncomputable section
namespace DirichletForm.FOTConstruction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def family_polar (q : E → ℝ) (u v : E) : ℝ := (q (u + v) - q (u - v)) / 4

theorem family_quadratic_even (q : E → ℝ) (h0 : q 0 = 0)
    (hp : ∀ u v, q (u + v) + q (u - v) = 2 * q u + 2 * q v) (u : E) : q (-u) = q u := by
  have he := hp 0 u
  rw [zero_add, zero_sub, h0] at he
  linarith only [he]

theorem family_polar_symm (q : E → ℝ) (h0 : q 0 = 0)
    (hp : ∀ u v, q (u + v) + q (u - v) = 2 * q u + 2 * q v) (u v : E) :
    family_polar q u v = family_polar q v u := by
  unfold family_polar
  rw [add_comm u v, show u - v = -(v - u) by abel, family_quadratic_even q h0 hp]

theorem family_polar_self (q : E → ℝ) (h0 : q 0 = 0)
    (hp : ∀ u v, q (u + v) + q (u - v) = 2 * q u + 2 * q v) (u : E) :
    family_polar q u u = q u := by
  have he := hp u u
  simp only [sub_self, h0, add_zero] at he
  unfold family_polar
  rw [sub_self, h0]
  linarith only [he]

theorem family_polar_add_left (q : E → ℝ)
    (hp : ∀ u v, q (u + v) + q (u - v) = 2 * q u + 2 * q v) (x y z : E) :
    family_polar q (x + y) z = family_polar q x z + family_polar q y z := by
  have h1 := hp (x + y + z) (x - z)
  have h2 := hp (x + y - z) (x + z)
  have h3 := hp (y + z) z
  have h4 := hp (y - z) z
  rw [show (x + y + z) + (x - z) = (x + x) + y by abel,
    show (x + y + z) - (x - z) = y + (z + z) by abel] at h1
  rw [show (x + y - z) + (x + z) = (x + x) + y by abel,
    show (x + y - z) - (x + z) = y - (z + z) by abel] at h2
  rw [show (y + z) + z = y + (z + z) by abel, add_sub_cancel_right] at h3
  rw [sub_add_cancel, show y - z - z = y - (z + z) by abel] at h4
  unfold family_polar
  linarith only [h1, h2, h3, h4]

theorem family_polar_add_right (q : E → ℝ) (h0 : q 0 = 0)
    (hp : ∀ u v, q (u + v) + q (u - v) = 2 * q u + 2 * q v) (x y z : E) :
    family_polar q x (y + z) = family_polar q x y + family_polar q x z := by
  rw [family_polar_symm q h0 hp x (y + z), family_polar_add_left q hp,
    family_polar_symm q h0 hp y x, family_polar_symm q h0 hp z x]

theorem family_polar_smul_left (q : E → ℝ) (h0 : q 0 = 0)
    (hp : ∀ u v, q (u + v) + q (u - v) = 2 * q u + 2 * q v)
    (hq : Continuous q) (c : ℝ) (x y : E) :
    family_polar q (c • x) y = c * family_polar q x y := by
  let L : E →+ ℝ := {
    toFun := fun z => family_polar q z y
    map_zero' := by
      simp only [family_polar, zero_add, zero_sub, family_quadratic_even q h0 hp,
        sub_self, zero_div]
    map_add' := fun z z' => family_polar_add_left q hp z z' y }
  have hL : Continuous L :=
    ((hq.comp (continuous_id.add continuous_const)).sub
      (hq.comp (continuous_id.sub continuous_const))).div_const 4
  exact map_real_smul L hL c x

theorem family_polar_smul_right (q : E → ℝ) (h0 : q 0 = 0)
    (hp : ∀ u v, q (u + v) + q (u - v) = 2 * q u + 2 * q v)
    (hq : Continuous q) (c : ℝ) (x y : E) :
    family_polar q x (c • y) = c * family_polar q x y := by
  rw [family_polar_symm q h0 hp x (c • y), family_polar_smul_left q h0 hp hq,
    family_polar_symm q h0 hp y x]

theorem family_polar_bound (q : E → ℝ) (h0 : q 0 = 0)
    (hp : ∀ u v, q (u + v) + q (u - v) = 2 * q u + 2 * q v)
    (hq : Continuous q) (hn : ∀ u, 0 ≤ q u) (x y : E) :
    |family_polar q x y| ≤ Real.sqrt (q x) * Real.sqrt (q y) := by
  have hpoly : ∀ t : ℝ, 0 ≤ q x * (t * t) + (2 * family_polar q x y) * t + q y := by
    intro t
    have hnonneg := hn (t • x + y)
    rw [← family_polar_self q h0 hp (t • x + y), family_polar_add_left q hp,
      family_polar_add_right q h0 hp, family_polar_add_right q h0 hp,
      family_polar_smul_left q h0 hp hq, family_polar_smul_left q h0 hp hq,
      family_polar_smul_right q h0 hp hq, family_polar_smul_right q h0 hp hq,
      family_polar_self q h0 hp, family_polar_self q h0 hp,
      family_polar_symm q h0 hp y x] at hnonneg
    convert hnonneg using 1 <;> ring
  have hdisc := discrim_le_zero hpoly
  unfold discrim at hdisc
  have hs : family_polar q x y ^ 2 ≤ q x * q y := by nlinarith only [hdisc]
  have hsqrt : |family_polar q x y| ^ 2 ≤ (Real.sqrt (q x) * Real.sqrt (q y)) ^ 2 := by
    rw [sq_abs, mul_pow, Real.sq_sqrt (hn x), Real.sq_sqrt (hn y)]
    exact hs
  exact nonneg_le_nonneg_of_sq_le_sq
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (by simpa only [pow_two] using hsqrt)

end DirichletForm.FOTConstruction
