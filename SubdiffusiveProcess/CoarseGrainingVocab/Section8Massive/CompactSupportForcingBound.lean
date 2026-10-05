module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.GMCCubeBounds
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# A uniform forcing bound for the massive cube exhaustion

A compactly supported datum is supported in one member of the centered cube
exhaustion.  Local boundedness of the massive weight on that fixed cube then
controls the forcing integral on every exhaustion cube by one finite constant.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped CompactlySupported ZeroAtInfty

noncomputable section

variable {d : ℕ}

private theorem exists_nat_tsupport_subset_cube (f : C_c(Vec d, ℝ)) :
    ∃ n : ℕ, tsupport f ⊆ cube d (n : ℤ) := by
  obtain ⟨R, hR⟩ := f.hasCompactSupport.isBounded.subset_ball (0 : Vec d)
  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt (2 * R) (by norm_num : (1 : ℝ) < 3)
  refine ⟨n, fun x hx ↦ ?_⟩
  have hxNorm : ‖x‖ < R := mem_ball_zero_iff.mp (hR hx)
  rw [cube, mem_openCubeSet_originCube_iff]
  intro i
  have hi : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  have hi' : -‖x‖ ≤ x i ∧ x i ≤ ‖x‖ := abs_le.mp hi
  have hpow : (3 : ℝ) ^ (n : ℤ) = (3 : ℝ) ^ n := zpow_natCast 3 n
  rw [hpow]
  constructor <;> linarith only [hn, hxNorm, hi'.1, hi'.2]

/-- The compact forcing term `integral rho f²` is bounded uniformly over the
centered cube exhaustion, using only the local weight bounds already contained
in `MassiveCubeBounds`. -/
theorem exists_uniform_massiveCube_forcing_integral_bound
    {c rho : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    (f : C_c(Vec d, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ∫ x in cube d (n : ℤ), rho x * f x * f x ∂volume ≤ C := by
  obtain ⟨supportScale, hsupport⟩ := exists_nat_tsupport_subset_cube f
  let C : ℝ := |B.rhoMax supportScale| * ∫ x, f x ^ 2 ∂volume
  have hfGlobal : MemLp (fun x : Vec d ↦ f x) 2 volume :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hboundIntegrable : Integrable
      (fun x : Vec d ↦ |B.rhoMax supportScale| * f x ^ 2) volume :=
    hfGlobal.integrable_sq.const_mul |B.rhoMax supportScale|
  have hboundNonneg : 0 ≤ᵐ[volume]
      fun x : Vec d ↦ |B.rhoMax supportScale| * f x ^ 2 :=
    Filter.Eventually.of_forall fun x ↦
      mul_nonneg (abs_nonneg _) (sq_nonneg (f x))
  have hC : 0 ≤ C := by
    exact mul_nonneg (abs_nonneg _)
      (integral_nonneg fun x : Vec d ↦ sq_nonneg (f x))
  refine ⟨C, hC, fun n ↦ ?_⟩
  have hcube := Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (n : ℤ)
  have hsupportCube :=
    Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (supportScale : ℤ)
  have hfLocal : MemL2On (cube d (n : ℤ)) f := hfGlobal.restrict _
  have hforcingIntegrable : IntegrableOn
      (fun x ↦ rho x * f x * f x) (cube d (n : ℤ)) :=
    integrableOn_mass_term (B.rho_measurable n) (B.rho_bounded n)
      hfLocal hfLocal
  have hrhoGlobal : ∀ᵐ x ∂volume,
      x ∈ cube d (supportScale : ℤ) → |rho x| ≤ B.rhoMax supportScale :=
    (ae_restrict_iff' hsupportCube.isOpen.measurableSet).1
      (B.rho_bounded supportScale)
  have hpoint : ∀ᵐ x ∂volume, x ∈ cube d (n : ℤ) →
      rho x * f x * f x ≤ |B.rhoMax supportScale| * f x ^ 2 := by
    filter_upwards [hrhoGlobal] with x hrho
    intro _hx
    by_cases hxSupport : x ∈ cube d (supportScale : ℤ)
    · have hrhoLe : rho x ≤ |B.rhoMax supportScale| :=
        (le_abs_self (rho x)).trans <|
          (hrho hxSupport).trans (le_abs_self (B.rhoMax supportScale))
      calc
        rho x * f x * f x = rho x * f x ^ 2 := by ring
        _ ≤ |B.rhoMax supportScale| * f x ^ 2 :=
          mul_le_mul_of_nonneg_right hrhoLe (sq_nonneg (f x))
    · have hfx : f x = 0 := by
        by_contra hne
        exact hxSupport (hsupport (subset_closure hne))
      rw [hfx]
      norm_num
  calc
    ∫ x in cube d (n : ℤ), rho x * f x * f x ∂volume ≤
        ∫ x in cube d (n : ℤ), |B.rhoMax supportScale| * f x ^ 2 ∂volume :=
      setIntegral_mono_on_ae hforcingIntegrable hboundIntegrable.integrableOn
        hcube.isOpen.measurableSet hpoint
    _ ≤ ∫ x, |B.rhoMax supportScale| * f x ^ 2 ∂volume :=
      setIntegral_le_integral hboundIntegrable hboundNonneg
    _ = C := by
      rw [integral_const_mul]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
