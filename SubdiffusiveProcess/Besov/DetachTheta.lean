import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.Besov.OscillationPoincare

/-!
# Squared cube averages over descendants (`Θ`) for the detach inequality

`theta Q k g` is the mean over the `3^(d k)` depth-`k` descendants `T` of `Q` of `(cubeAverage T g)^2`.
It is monotone in `k` (Jensen) and bounded by the mean square of `g` on `Q`; it commutes with integral
translations of triadic cubes, and its depth-`k+1` value on an origin-centred cube is the mean of the
depth-`k` values on the `3^d` children.  Used for `\eqref{e.nabla.u.detach}` (`inputs_poincare_detach_interior`).
-/

open MeasureTheory
open Homogenization

namespace SubdiffusiveProcess.Besov.Detach

noncomputable section

/-- Mean over the depth-`k` descendants of `Q` of the squared cube averages of `g`. -/
def theta {d : ℕ} (Q : TriadicCube d) (k : ℕ) (g : Vec d → ℝ) : ℝ :=
  descendantsAverage Q k (fun T => (cubeAverage T g) ^ 2)

/-- The neighbour cube of `S` shifted by `δ - 1` in every coordinate (same scale). -/
def nbr {d : ℕ} (S : TriadicCube d) (δ : Fin d → Fin 3) : TriadicCube d :=
  { scale := S.scale, index := fun i => S.index i + (δ i : ℤ) - 1 }

theorem theta_nonneg {d : ℕ} (Q : TriadicCube d) (k : ℕ) (g : Vec d → ℝ) : 0 ≤ theta Q k g := by
  unfold theta
  exact descendantsAverage_nonneg Q k _ (fun R _ => sq_nonneg _)

theorem theta_zero {d : ℕ} (Q : TriadicCube d) (g : Vec d → ℝ) :
    theta Q 0 g = (cubeAverage Q g) ^ 2 := by
  simp [theta, descendantsAverage]

theorem theta_add {d : ℕ} (Q : TriadicCube d) (a b : ℕ) (g : Vec d → ℝ) :
    theta Q (a + b) g = descendantsAverage Q a (fun R => theta R b g) := by
  unfold theta
  exact descendantsAverage_add_eq_descendantsAverage_descendantsAverage Q a b (fun T => (cubeAverage T g) ^ 2)

theorem sq_cubeAverage_le_theta_one {d : ℕ} (Q : TriadicCube d) (g : Vec d → ℝ)
    (hg : IntegrableOn g (cubeSet Q) volume) :
    (cubeAverage Q g) ^ 2 ≤ theta Q 1 g := by
  unfold theta
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q 1 g hg]
  unfold descendantsAverage
  set D : Finset (TriadicCube d) := descendantsAtDepth Q 1
  have hsq : (D.sum (fun R => cubeAverage R g)) ^ 2
      ≤ (D.card : ℝ) * D.sum (fun R => (cubeAverage R g) ^ 2) :=
    sq_sum_le_card_mul_sum_sq (s := D) (f := fun R => cubeAverage R g)
  have hc : (0:ℝ) < (D.card : ℝ) := by
    have h : D.card = 3 ^ d := by
      simp only [D, descendantsAtDepth_card, pow_one]
    rw [h]; positivity
  rw [inv_mul_eq_div, inv_mul_eq_div, div_pow]
  field_simp
  nlinarith [hsq]

theorem theta_mono {d : ℕ} (Q : TriadicCube d) (k : ℕ) (g : Vec d → ℝ)
    (hg : IntegrableOn g (cubeSet Q) volume) :
    theta Q k g ≤ theta Q (k + 1) g := by
  classical
  have hle : descendantsAverage Q k (fun R => (cubeAverage R g) ^ 2) ≤
      descendantsAverage Q k (fun R => theta R 1 g) := by
    refine descendantsAverage_le_descendantsAverage Q k ?_
    intro R hR
    refine sq_cubeAverage_le_theta_one R g ?_
    exact hg.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
  have hk : theta Q k g = descendantsAverage Q k (fun R => (cubeAverage R g) ^ 2) := rfl
  have hkp : theta Q (k + 1) g = descendantsAverage Q k (fun R => theta R 1 g) :=
    theta_add Q k 1 g
  rw [hk, hkp]
  exact hle

theorem cubeAverage_sq_le_cubeAverage_sq {d : ℕ} (Q : TriadicCube d) (g : Vec d → ℝ)
    (hg : MemLp g 2 (volume.restrict (cubeSet Q))) :
    (cubeAverage Q g) ^ 2 ≤ cubeAverage Q (fun x => g x ^ 2) := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure Q g,
      cubeAverage_eq_integral_normalizedCubeMeasure Q (fun x => g x ^ 2)]
  letI : IsProbabilityMeasure (normalizedCubeMeasure Q) := ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hg' : MemLp g 2 (normalizedCubeMeasure Q) := by
    rw [normalizedCubeMeasure]
    exact hg.smul_measure (by simp)
  have hconv : ConvexOn ℝ Set.univ (fun y : ℝ => y ^ 2) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith [mul_nonneg ha hb, sq_nonneg (x - y)]
  have hcont : ContinuousOn (fun y : ℝ => y ^ 2) Set.univ := (continuous_pow 2).continuousOn
  have hgint : Integrable g (normalizedCubeMeasure Q) := hg'.integrable (by norm_num)
  have hg2int : Integrable (fun x => g x ^ 2) (normalizedCubeMeasure Q) := hg'.integrable_sq
  exact ConvexOn.map_integral_le hconv hcont isClosed_univ
    (Filter.Eventually.of_forall (fun x => Set.mem_univ x)) hgint hg2int

theorem theta_le_cubeAverage_sq {d : ℕ} (Q : TriadicCube d) (k : ℕ) (g : Vec d → ℝ)
    (hg : MemLp g 2 (volume.restrict (cubeSet Q))) :
    theta Q k g ≤ cubeAverage Q (fun x => g x ^ 2) := by
  have hstep : descendantsAverage Q k (fun R => (cubeAverage R g) ^ 2) ≤
      descendantsAverage Q k (fun R => cubeAverage R (fun x => g x ^ 2)) := by
    unfold descendantsAverage
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro R hR
    exact cubeAverage_sq_le_cubeAverage_sq R g
      (hg.mono_measure (Measure.restrict_mono (cubeSet_subset_of_mem_descendantsAtDepth hR) le_rfl))
  have heq : descendantsAverage Q k (fun R => cubeAverage R (fun x => g x ^ 2)) =
      cubeAverage Q (fun x => g x ^ 2) := by
    rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q k (fun x => g x ^ 2) hg.integrable_sq]
  rw [theta]
  calc descendantsAverage Q k (fun R => (cubeAverage R g) ^ 2)
      ≤ descendantsAverage Q k (fun R => cubeAverage R (fun x => g x ^ 2)) := hstep
    _ = cubeAverage Q (fun x => g x ^ 2) := heq

theorem cubeAverage_translateCube {d : ℕ} (z : Fin d → ℤ) (R : TriadicCube d) (g : Vec d → ℝ) :
    cubeAverage (translateCube z R) g =
      cubeAverage R (fun x => g (x + (fun i => (z i : ℝ) * cubeScaleFactor R))) := by
  unfold cubeAverage
  have hvol : cubeVolume (translateCube z R) = cubeVolume R := by
    simp only [cubeVolume, cubeScaleFactor_translateCube]
  rw [hvol]
  have hset : cubeSet (translateCube z R) =
      translateSet (fun i => (z i : ℝ) * cubeScaleFactor R) (cubeSet R) := by
    ext x
    rw [mem_cubeSet_translateCube_iff, mem_translateSet_iff_sub_mem]
  rw [hset, ← setIntegral_comp_addRight_translateSet (fun i => (z i : ℝ) * cubeScaleFactor R) (cubeSet R) g]

theorem theta_translateCube {d : ℕ} (z : Fin d → ℤ) (R : TriadicCube d) (n : ℕ) (g : Vec d → ℝ) :
    theta (translateCube z R) n g =
      theta R n (fun x => g (x + (fun i => (z i : ℝ) * cubeScaleFactor R))) := by
  simp only [theta, descendantsAverage]
  rw [descendantsAtDepth_translateCube]
  rw [Finset.card_image_of_injective _ (Book.Ch02.translateCube_injective _)]
  rw [Finset.sum_image (fun a _ b _ h => Book.Ch02.translateCube_injective _ h)]
  have hsum : (descendantsAtDepth R n).sum
        (fun T => (cubeAverage (translateCube (descendantTranslationShift n z) T) g) ^ 2)
      = (descendantsAtDepth R n).sum
        (fun T => (cubeAverage T (fun x => g (x + (fun i => (z i : ℝ) * cubeScaleFactor R)))) ^ 2) := by
    apply Finset.sum_congr rfl
    intro T hT
    have hscale : T.scale = R.scale - (n : ℤ) := scale_eq_sub_of_mem_descendantsAtDepth hT
    have hA : (fun i => ((descendantTranslationShift n z) i : ℝ) * cubeScaleFactor T)
        = (fun i => (z i : ℝ) * cubeScaleFactor R) := by
      funext i
      show ((3 ^ n * z i : ℤ) : ℝ) * (3 : ℝ) ^ T.scale = (z i : ℝ) * (3 : ℝ) ^ R.scale
      rw [hscale]
      push_cast
      have h3 : (3 : ℝ) ^ n * 3 ^ (R.scale - (n : ℤ)) = 3 ^ R.scale := by
        rw [← zpow_natCast (3 : ℝ) n, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
        congr 1
        ring
      rw [mul_comm ((3 : ℝ) ^ n) ((z i : ℤ) : ℝ), mul_assoc, h3]
    rw [cubeAverage_translateCube, hA]
  rw [hsum]

theorem sum_theta_descendants {d : ℕ} (Q : TriadicCube d) (a b : ℕ) (g : Vec d → ℝ) :
    ∑ P ∈ descendantsAtDepth Q a, theta P b g =
      ((3 ^ d) ^ a : ℕ) * theta Q (a + b) g := by
  rw [theta_add]
  simp only [descendantsAverage]
  rw [descendantsAtDepth_card]
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

theorem theta_originCube_children {d : ℕ} (m : ℤ) (k : ℕ) (f : Vec d → ℝ) :
    theta (originCube d m) (k + 1) f =
      ((3 : ℝ) ^ d)⁻¹ * ∑ δ : Fin d → Fin 3,
        theta ({ scale := m - 1, index := fun i => (δ i : ℤ) - 1 } : TriadicCube d) k f := by
  rw [show k + 1 = 1 + k by omega, theta_add]
  simp only [descendantsAverage]
  rw [descendantsAtDepth_one, childCubes_card]
  have hchild : childCubes (originCube d m) =
      Finset.univ.image (fun δ : Fin d → Fin 3 =>
        ({ scale := m - 1, index := fun i => (δ i : ℤ) - 1 } : TriadicCube d)) := by
    ext R
    simp [childCubes, originCube]
  rw [hchild]
  have hinj : Set.InjOn (fun δ : Fin d → Fin 3 =>
      ({ scale := m - 1, index := fun i => (δ i : ℤ) - 1 } : TriadicCube d)) (↑(Finset.univ : Finset (Fin d → Fin 3))) := by
    intro x _ y _ hxy
    funext i
    have h2 := congrFun (congrArg TriadicCube.index hxy) i
    have h1 : ((x i : ℤ) - 1) = ((y i : ℤ) - 1) := by simpa using h2
    have h3 : (x i : ℤ) = (y i : ℤ) := by linarith
    exact Fin.ext (by exact_mod_cast h3)
  rw [Finset.sum_image hinj]
  simp only [Nat.cast_pow]
  congr 1

theorem theta_block {d : ℕ} (S : TriadicCube d) (k : ℕ) (f : Vec d → ℝ) :
    theta (originCube d (S.scale + 1)) (k + 1) (fun x => f (x + cubeCenter S)) =
      ((3 : ℝ) ^ d)⁻¹ * ∑ δ : Fin d → Fin 3, theta (nbr S δ) k f := by
  rw [theta_originCube_children (S.scale + 1) k (fun x => f (x + cubeCenter S))]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro δ _
  have hshift : (fun i => (S.index i : ℝ) *
        cubeScaleFactor ({ scale := S.scale + 1 - 1, index := fun i => (δ i : ℤ) - 1 } : TriadicCube d))
      = cubeCenter S := by
    funext i
    simp only [cubeCenter, cubeScaleFactor]
    have hscale : (S.scale + 1 - 1 : ℤ) = S.scale := by ring
    rw [hscale]
  have htr := theta_translateCube S.index
      ({ scale := S.scale + 1 - 1, index := fun i => (δ i : ℤ) - 1 } : TriadicCube d) k f
  rw [hshift] at htr
  rw [← htr]
  have hcube : translateCube S.index
      ({ scale := S.scale + 1 - 1, index := fun i => (δ i : ℤ) - 1 } : TriadicCube d) = nbr S δ := by
    simp only [translateCube, nbr]
    congr 1
    · ring
    · funext i
      ring
  rw [hcube]

end

end SubdiffusiveProcess.Besov.Detach
