module

public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.lem_compact_responses
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Analysis.RadialKernel
public import SubdiffusiveProcess.Sobolev.FractionalLipschitzFinite
public import SubdiffusiveProcess.Sobolev.FractionalRepresentatives
public import SubdiffusiveProcess.Main.CubeFractionalL2Seminorm
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.aux_macro_moment_bank
public import SubdiffusiveProcess.Sobolev.CompactResponses
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.lambda_inv_moments
public import SubdiffusiveProcess.Paper.aux_coercivity_dilation_killed_pullback
public import SubdiffusiveProcess.Paper.aux_coercivity_dilation_energy_scaling
public import SubdiffusiveProcess.Paper.aux_coercivity_dilation_integral_scaling
public import SubdiffusiveProcess.Paper.dilation_coefficient_transport
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.VariationalResponses.OddExtension
public import SubdiffusiveProcess.Sobolev.LocalEnergy
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.Probability.InfraredCharacterizationCompactExponentialMoment
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_scale_shift
public import SubdiffusiveProcess.Paper.finite_cutoff_log_abs_majorant

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal NNReal ContDiff
open TopologicalSpace
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

namespace SubdiffusiveProcess.Paper

noncomputable section

section RBK_part
open MeasureTheory
open scoped ENNReal NNReal ContDiff
open TopologicalSpace
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity


/-- Real arithmetic: `0 ≤ E ≤ A √E` with `0 ≤ A` gives `E ≤ A²`. -/
theorem aux_rem_bank_response_moments_sq_of_le_mul_sqrt {E A : ℝ} (hE : 0 ≤ E) (hA : 0 ≤ A)
    (h : E ≤ A * Real.sqrt E) : E ≤ A ^ 2 := by
  have hs := Real.sqrt_nonneg E
  have hsq : Real.sqrt E * Real.sqrt E = E := Real.mul_self_sqrt hE
  rcases eq_or_lt_of_le hs with h0 | hpos
  · rw [← h0, mul_zero] at hsq
    rw [← hsq]
    positivity
  · have h1 : Real.sqrt E ≤ A := by
      have : Real.sqrt E * Real.sqrt E ≤ A * Real.sqrt E := by rw [hsq]; exact h
      exact le_of_mul_le_mul_right this hpos
    calc E = Real.sqrt E * Real.sqrt E := hsq.symm
      _ ≤ A * A := mul_le_mul h1 h1 hs hA
      _ = A ^ 2 := by ring

/-- **Killed inverse response from the coarse-grained trace-zero Poincaré inequality**
(`in_poincare.poincare_killed_all_radii`, all radii): the inverse response of the volume
load of `fL2` is at most `(‖fL2‖ C r)² λ_{1,1}^{-1}`. -/
theorem aux_rem_bank_response_moments_inverse_le {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (P : in_poincare d hd E) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr)) (fL2 : DomainL2 (centeredCube z r hr)) :
    inverseResponse (killedResponseSpace hP) a
        ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL) ≤
      (‖fL2‖ * (P.C * r)) ^ 2 * (E.lam z r hr a z r 1 1)⁻¹ := by
  obtain ⟨u, hu⟩ : ∃ u : killedSobolevGraph (centeredCube z r hr),
      u = responseSolution (killedResponseSpace hP) a
        ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : ℝ,
      V = volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := ⟨_, rfl⟩
  have hVpos : 0 < V := by
    rw [hV, centeredCube_volume_real z hr]; positivity
  have hlam := E.lam_pos z r hr a z r 1 1
  -- the energy and the load
  have hEdef : inverseResponse (killedResponseSpace hP) a
        ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL) =
      sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
        (u : SobolevData (centeredCube z r hr)) := by
    rw [hu]; rfl
  have hLoad : inverseResponse (killedResponseSpace hP) a
        ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL) =
      inner ℝ fL2 (u : SobolevData (centeredCube z r hr)).1 := by
    rw [inverseResponse_eq_load, ← hu]; rfl
  obtain ⟨Ee, hEe⟩ : ∃ Ee : ℝ, Ee = sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
      (u : SobolevData (centeredCube z r hr)) := ⟨_, rfl⟩
  have hE0 : 0 ≤ Ee := by rw [hEe]; exact sobolevCoefficientForm_nonneg _ _
  -- the trace-zero Poincaré inequality, unnormalized
  have hpo := P.poincare_killed_all_radii z r hr a u
  have hnorm : normalizedEnergyNorm a (centeredCube z r hr).isOpen.measurableSet
      (sobolevGradient (u : SobolevData (centeredCube z r hr))) =
      Real.sqrt Ee / Real.sqrt V := by
    unfold normalizedEnergyNorm
    rw [localGradientEnergy_domain_eq_sobolevCoefficientForm, ← hEe, ← hV,
      Real.sqrt_div hE0]
  rw [hnorm, ← hV] at hpo
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = (E.lam z r hr a z r 1 1) ^ (-(1 / 2) : ℝ) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; exact Real.rpow_nonneg hlam.le _
  have hLsq : L ^ 2 = (E.lam z r hr a z r 1 1)⁻¹ := by
    rw [hL, ← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    norm_num
    exact Real.rpow_neg_one _
  have hsV := Real.sqrt_pos.2 hVpos
  have hu_le : ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤ P.C * r * L * Real.sqrt Ee := by
    rw [← hL] at hpo
    have h1 := (div_le_iff₀ hsV).1 hpo
    calc ‖(u : SobolevData (centeredCube z r hr)).1‖
        ≤ P.C * r * L * (Real.sqrt Ee / Real.sqrt V) * Real.sqrt V := h1
      _ = P.C * r * L * Real.sqrt Ee := by field_simp
  have hEle : Ee ≤ (‖fL2‖ * (P.C * r * L)) * Real.sqrt Ee := by
    have h1 : Ee = inner ℝ fL2 (u : SobolevData (centeredCube z r hr)).1 := by
      rw [hEe, ← hEdef, hLoad]
    refine h1.le.trans ((real_inner_le_norm _ _).trans ?_)
    calc ‖fL2‖ * ‖(u : SobolevData (centeredCube z r hr)).1‖
        ≤ ‖fL2‖ * (P.C * r * L * Real.sqrt Ee) :=
          mul_le_mul_of_nonneg_left hu_le (norm_nonneg _)
      _ = (‖fL2‖ * (P.C * r * L)) * Real.sqrt Ee := by ring
  have hA0 : 0 ≤ ‖fL2‖ * (P.C * r * L) :=
    mul_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg P.C_pos.le hr.le) hL0)
  have hfin := aux_rem_bank_response_moments_sq_of_le_mul_sqrt hE0 hA0 hEle
  rw [hEdef, ← hEe]
  calc Ee ≤ (‖fL2‖ * (P.C * r * L)) ^ 2 := hfin
    _ = (‖fL2‖ * (P.C * r)) ^ 2 * L ^ 2 := by ring
    _ = _ := by rw [hLsq]

/-- `λ_{1,1}^{-1} ≤ λ_{s,1}^{-1}` for `s ≤ 1` (`in_J.lam_mono`). -/
theorem aux_rem_bank_response_moments_lam_inv_mono {d : ℕ} (E : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (s : ℝ) (hs : s ≤ 1) :
    (E.lam z r hr a z r 1 1)⁻¹ ≤ (E.lam z r hr a z r s 1)⁻¹ :=
  inv_anti₀ (E.lam_pos z r hr a z r s 1) (E.lam_mono z r hr a z r 1 s 1 hs)

end RBK_part

section RBFrac_part
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal
open SubdiffusiveProcess


/-- The radial kernel mass `∫_{B(0,r)} ‖w‖^{2-d-2s}` of the Lipschitz Gagliardo bound. -/
def aux_rem_bank_response_moments_kernelMass (d : ℕ) (r s : ℝ) : ℝ≥0∞ :=
  ∫⁻ w : SpatialCoordinates d, (Metric.ball (0 : SpatialCoordinates d) r).indicator
      (fun w => ENNReal.ofReal (‖w‖ ^ (2 - (d : ℝ) - 2 * s))) w

theorem aux_rem_bank_response_moments_kernelMass_lt_top {d : ℕ} (hd : 2 ≤ d) (r s : ℝ)
    (hs1 : s < 1) : aux_rem_bank_response_moments_kernelMass d r s < ⊤ := by
  have hq : -(d : ℝ) < 2 - (d : ℝ) - 2 * s := by linarith
  have hkernel := integrableOn_norm_rpow_ball (Nat.zero_lt_of_lt hd) (2 - (d : ℝ) - 2 * s) r hq
  have hI : Integrable
      ((Metric.ball (0 : SpatialCoordinates d) r).indicator
        (fun w : SpatialCoordinates d => ‖w‖ ^ (2 - (d : ℝ) - 2 * s))) :=
    hkernel.integrable_indicator Metric.isOpen_ball.measurableSet
  have hnonneg : 0 ≤ᵐ[volume]
      (Metric.ball (0 : SpatialCoordinates d) r).indicator
        (fun w : SpatialCoordinates d => ‖w‖ ^ (2 - (d : ℝ) - 2 * s)) := by
    filter_upwards [] with w
    by_cases hw : w ∈ Metric.ball (0 : SpatialCoordinates d) r
    · rw [indicator_of_mem hw]
      exact Real.rpow_nonneg (norm_nonneg _) _
    · rw [indicator_of_notMem hw]
      change (0 : ℝ) ≤ 0
      exact le_rfl
  have hIfin := hI.hasFiniteIntegral
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnonneg] at hIfin
  have heq : (fun w : SpatialCoordinates d =>
      ENNReal.ofReal ((Metric.ball (0 : SpatialCoordinates d) r).indicator
        (fun u : SpatialCoordinates d => ‖u‖ ^ (2 - (d : ℝ) - 2 * s)) w)) =
      (Metric.ball (0 : SpatialCoordinates d) r).indicator
        (fun w => ENNReal.ofReal (‖w‖ ^ (2 - (d : ℝ) - 2 * s))) := by
    funext w
    by_cases hw : w ∈ Metric.ball (0 : SpatialCoordinates d) r
    · simp only [indicator_of_mem hw]
    · simp only [indicator_of_notMem hw, ENNReal.ofReal_zero]
  unfold aux_rem_bank_response_moments_kernelMass
  rwa [heq] at hIfin

/-- **Quantitative Gagliardo bound for Lipschitz fields**: the raw fractional square
integral over a cube of side `r` is at most `k K² · kernelMass · |Q|`. -/
theorem aux_rem_bank_response_moments_fractional_integral_le
    {d k : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : ℝ) (hs : 0 < s)
    (f : SpatialCoordinates d → Fin k → ℝ) (K : ℝ≥0)
    (hf : LipschitzOnWith K f (centeredCube z r hr : Set (SpatialCoordinates d))) :
    (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin k, (f x i - f y i) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * s)) ≤
      ENNReal.ofReal ((k : ℝ) * (K : ℝ) ^ 2) * aux_rem_bank_response_moments_kernelMass d r s *
        volume (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  let q : ℝ := 2 - (d : ℝ) - 2 * s
  let C : ℝ := (k : ℝ) * (K : ℝ) ^ 2
  let H : SpatialCoordinates d → ℝ≥0∞ := fun w =>
    (Metric.ball (0 : SpatialCoordinates d) r).indicator
      (fun w => ENNReal.ofReal (‖w‖ ^ q)) w
  have hH_meas : Measurable H := by
    dsimp [H]
    apply Measurable.indicator
    · fun_prop
    · exact Metric.isOpen_ball.measurableSet
  have hdist (x y : SpatialCoordinates d) :
      ‖x - y‖ ≤ Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    apply (Real.le_sqrt (abs_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).2
    calc
      |(x - y) i| ^ 2 = (x i - y i) ^ 2 := by simp [sq_abs]
      _ ≤ ∑ j : Fin d, (x j - y j) ^ 2 := by
        exact Finset.single_le_sum (fun j _ => sq_nonneg (x j - y j)) (Finset.mem_univ i)
  have hnum (x y : SpatialCoordinates d)
      (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)))
      (hy : y ∈ (centeredCube z r hr : Set (SpatialCoordinates d))) :
      ∑ i : Fin k, (f x i - f y i) ^ 2 ≤ C * ‖x - y‖ ^ 2 := by
    have hL : ‖f x - f y‖ ≤ (K : ℝ) * ‖x - y‖ := by
      simpa only [dist_eq_norm] using hf.dist_le_mul x hx y hy
    calc
      _ ≤ ∑ _i : Fin k, ((K : ℝ) * ‖x - y‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : |f x i - f y i| ≤ (K : ℝ) * ‖x - y‖ :=
          (((pi_norm_le_iff_of_nonneg (norm_nonneg (f x - f y))).mp le_rfl) i).trans hL
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg (NNReal.coe_nonneg K) (norm_nonneg _))).2 hi'
      _ = C * ‖x - y‖ ^ 2 := by simp [C]; ring
  have hdiff_mem (x y : SpatialCoordinates d)
      (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)))
      (hy : y ∈ (centeredCube z r hr : Set (SpatialCoordinates d))) :
      x - y ∈ Metric.ball (0 : SpatialCoordinates d) r := by
    have hx' : ‖x - z‖ < r / 2 := by
      simpa only [centeredCube, Opens.coe_mk, Metric.mem_ball, dist_eq_norm] using hx
    have hy' : ‖z - y‖ < r / 2 := by
      have := Metric.mem_ball.mp hy
      simpa only [dist_eq_norm, norm_sub_rev] using this
    apply Metric.mem_ball.mpr
    simp only [dist_zero_right]
    calc
      ‖x - y‖ = ‖(x - z) + (z - y)‖ := by congr 1; module
      _ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
      _ < r := by linarith
  have hpoint (x y : SpatialCoordinates d)
      (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)))
      (hy : y ∈ (centeredCube z r hr : Set (SpatialCoordinates d))) :
      ENNReal.ofReal (∑ i : Fin k, (f x i - f y i) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * s) ≤ ENNReal.ofReal C * H (x - y) := by
    by_cases hxy : x = y
    · subst y
      simp
    · have ht : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
      have hp : 0 ≤ (d : ℝ) + 2 * s := by positivity
      have hquot :
          ENNReal.ofReal (∑ i : Fin k, (f x i - f y i) ^ 2) /
              (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                ((d : ℝ) + 2 * s) ≤
            ENNReal.ofReal (C * ‖x - y‖ ^ 2) /
              ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + 2 * s) := by
        apply ENNReal.div_le_div
        · exact ENNReal.ofReal_le_ofReal (hnum x y hx hy)
        · exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hdist x y)) hp
      calc
        _ ≤ ENNReal.ofReal (C * ‖x - y‖ ^ 2) /
              ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + 2 * s) := hquot
        _ = ENNReal.ofReal C * ENNReal.ofReal (‖x - y‖ ^ q) := by
          rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow (norm_nonneg _) 2]
          rw [mul_div_assoc, ← ENNReal.rpow_natCast]
          have hpow := ENNReal.rpow_sub (x := ENNReal.ofReal ‖x - y‖)
            (2 : ℝ) ((d : ℝ) + 2 * s)
            (ENNReal.ofReal_ne_zero_iff.mpr ht) ENNReal.ofReal_ne_top
          change ENNReal.ofReal C *
              (ENNReal.ofReal ‖x - y‖ ^ (2 : ℝ) /
                ENNReal.ofReal ‖x - y‖ ^ ((d : ℝ) + 2 * s)) = _
          rw [← hpow]
          rw [ENNReal.ofReal_rpow_of_pos ht]
          congr 2
          dsimp [q]
          ring_nf
        _ = ENNReal.ofReal C * H (x - y) := by
          rw [show H (x - y) = ENNReal.ofReal (‖x - y‖ ^ q) by
            simp only [H, indicator_of_mem (hdiff_mem x y hx hy)]]
  have hinner (x : SpatialCoordinates d)
      (hx : x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))) :
      (∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin k, (f x i - f y i) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * s)) ≤ ENNReal.ofReal C * (∫⁻ w, H w) := by
    calc
      _ ≤ ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal C * H (x - y) := by
        apply setLIntegral_mono' (centeredCube z r hr).isOpen.measurableSet
        intro y hy
        exact hpoint x y hx hy
      _ ≤ ∫⁻ y, ENNReal.ofReal C * H (x - y) :=
        setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal C * (∫⁻ y, H (x - y)) := by
        simpa only [Function.comp_apply] using
          (lintegral_const_mul'' (μ := volume) (ENNReal.ofReal C)
            (hH_meas.comp (by fun_prop : Measurable fun y : SpatialCoordinates d => x - y)).aemeasurable)
      _ = ENNReal.ofReal C * (∫⁻ w, H w) := by
        congr 1
        exact (volume.measurePreserving_sub_left x).lintegral_comp_emb
          (MeasurableEquiv.subLeft x).measurableEmbedding H
  calc
    _ ≤ ∫⁻ _x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal C * (∫⁻ w, H w) := by
      apply setLIntegral_mono' (centeredCube z r hr).isOpen.measurableSet
      intro x hx
      exact hinner x hx
    _ = (ENNReal.ofReal C * (∫⁻ w, H w)) *
        volume (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      rw [setLIntegral_const]
    _ = _ := rfl

theorem aux_rem_bank_response_moments_toReal_sqrt_sq (x : ℝ≥0∞) :
    ((x ^ (1 / 2 : ℝ)).toReal) ^ 2 = x.toReal := by
  rw [← ENNReal.toReal_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num

/-- The normalized fractional seminorm of a scalar `L²` class that is a.e. a Lipschitz
function on the cube, squared: at most `s K² · kernelMass`. -/
theorem aux_rem_bank_response_moments_seminorm_sq_le
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1) (v : DomainL2 (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) (K : ℝ≥0)
    (hvg : (v : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g)
    (hg : LipschitzOnWith K g (centeredCube z r hr : Set (SpatialCoordinates d))) :
    cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) < ⊤ ∧
    ((cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v)).toReal) ^ 2 ≤
      (s : ℝ) * (K : ℝ) ^ 2 *
        (aux_rem_bank_response_moments_kernelMass d r (s : ℝ)).toReal := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ≥0∞, M = aux_rem_bank_response_moments_kernelMass d r (s : ℝ) :=
    ⟨_, rfl⟩
  have hMtop : M < ⊤ := by
    rw [hM]; exact aux_rem_bank_response_moments_kernelMass_lt_top hd r _ s.2.2
  obtain ⟨Vol, hVol⟩ : ∃ Vol : ℝ≥0∞,
      Vol = volume (centeredCube z r hr : Set (SpatialCoordinates d)) := ⟨_, rfl⟩
  have hVol0 : Vol ≠ 0 := by
    rw [hVol, centeredCube_volume z hr]
    exact (ENNReal.ofReal_pos.mpr (pow_pos hr d)).ne'
  have hVoltop : Vol ≠ ⊤ := by
    rw [hVol, centeredCube_volume z hr]; exact ENNReal.ofReal_ne_top
  let F : SpatialCoordinates d → Fin 1 → ℝ := fun x _ => g x
  have hF : LipschitzOnWith K F (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    intro x hx y hy
    have h := hg hx hy
    refine le_trans (le_of_eq ?_) h
    simp only [F, edist_pi_const]
  have hraw := aux_rem_bank_response_moments_fractional_integral_le hd z r hr (s : ℝ) s.2.1
    F K hF
  have hcongr := fractional_square_integral_congr_ae
    (fun (_ : Fin 1) x => (v : SpatialCoordinates d → ℝ) x) (fun _ x => F x 0)
    (fun _ => hvg) (s : ℝ)
  -- the raw integral of `v`
  obtain ⟨I, hI⟩ : ∃ I : ℝ≥0∞, I = ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin 1, (v x - v y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ)) := ⟨_, rfl⟩
  have hIle : I ≤ ENNReal.ofReal ((1 : ℝ) * (K : ℝ) ^ 2) * M * Vol := by
    rw [hI, hM, hVol]
    have h1 : (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal (∑ i : Fin 1, (v x - v y) ^ 2) /
            (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
              ((d : ℝ) + 2 * (s : ℝ))) =
        ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
            ENNReal.ofReal (∑ i : Fin 1, (F x i - F y i) ^ 2) /
              (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                ((d : ℝ) + 2 * (s : ℝ)) := by
      simpa only [F] using hcongr
    rw [h1]
    simpa only [Fintype.card_fin, Nat.cast_one] using hraw
  have hsem : cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) =
      ((ENNReal.ofReal (s : ℝ) / Vol) * I) ^ (1 / 2 : ℝ) := by
    rw [hI, hVol]; rfl
  have hprod_le : (ENNReal.ofReal (s : ℝ) / Vol) * I ≤
      ENNReal.ofReal ((s : ℝ) * (K : ℝ) ^ 2 * M.toReal) := by
    calc (ENNReal.ofReal (s : ℝ) / Vol) * I
        ≤ (ENNReal.ofReal (s : ℝ) / Vol) * (ENNReal.ofReal ((1 : ℝ) * (K : ℝ) ^ 2) * M * Vol) :=
          mul_le_mul_right hIle _
      _ = ENNReal.ofReal (s : ℝ) * ENNReal.ofReal ((K : ℝ) ^ 2) * M := by
          rw [one_mul, ENNReal.div_eq_inv_mul]
          calc Vol⁻¹ * ENNReal.ofReal (s : ℝ) * (ENNReal.ofReal ((K : ℝ) ^ 2) * M * Vol)
              = (Vol⁻¹ * Vol) * (ENNReal.ofReal (s : ℝ) * ENNReal.ofReal ((K : ℝ) ^ 2) * M) := by
                ring
            _ = _ := by rw [ENNReal.inv_mul_cancel hVol0 hVoltop, one_mul]
      _ = ENNReal.ofReal ((s : ℝ) * (K : ℝ) ^ 2 * M.toReal) := by
          rw [ENNReal.ofReal_mul (by nlinarith [s.2.1]), ENNReal.ofReal_mul s.2.1.le,
            ENNReal.ofReal_toReal hMtop.ne]
  have hB0 : 0 ≤ (s : ℝ) * (K : ℝ) ^ 2 * M.toReal :=
    mul_nonneg (mul_nonneg s.2.1.le (sq_nonneg _)) ENNReal.toReal_nonneg
  have hfin : (ENNReal.ofReal (s : ℝ) / Vol) * I < ⊤ :=
    lt_of_le_of_lt hprod_le ENNReal.ofReal_lt_top
  refine ⟨?_, ?_⟩
  · rw [hsem]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne
  · rw [hsem, aux_rem_bank_response_moments_toReal_sqrt_sq, ← hM]
    calc ((ENNReal.ofReal (s : ℝ) / Vol) * I).toReal
        ≤ (ENNReal.ofReal ((s : ℝ) * (K : ℝ) ^ 2 * M.toReal)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hprod_le
      _ = (s : ℝ) * (K : ℝ) ^ 2 * M.toReal := ENNReal.toReal_ofReal hB0

end RBFrac_part

section RBCell_part
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity


/-- The three `C²` bounds read off `c2Norm` on the closed cube. -/
theorem aux_rem_bank_response_moments_c2_bounds {d : ℕ} (w : SpatialCoordinates d) (ρ : ℝ)
    (hρ : 0 < ρ) (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 2 phi) (Cphi : ℝ)
    (hC : c2Norm (closedCube w ρ hρ : Set (SpatialCoordinates d)) phi ≤ Cphi) :
    0 ≤ Cphi ∧
      (∀ y ∈ (closedCube w ρ hρ : Set (SpatialCoordinates d)), |phi y| ≤ Cphi) ∧
      (∀ y ∈ (closedCube w ρ hρ : Set (SpatialCoordinates d)), ‖fderiv ℝ phi y‖ ≤ Cphi) ∧
      (∀ y ∈ (closedCube w ρ hρ : Set (SpatialCoordinates d)),
        ‖fderiv ℝ (fderiv ℝ phi) y‖ ≤ Cphi) := by
  have hKc : IsCompact (closedCube w ρ hρ : Set (SpatialCoordinates d)) :=
    (closedCube w ρ hρ).isCompact
  have key : ∀ g : SpatialCoordinates d → ℝ, Continuous g →
      (∀ x, 0 ≤ g x) →
      0 ≤ sSup {v : ℝ | ∃ x ∈ (closedCube w ρ hρ : Set (SpatialCoordinates d)), v = g x} ∧
      ∀ y ∈ (closedCube w ρ hρ : Set (SpatialCoordinates d)),
        g y ≤ sSup {v : ℝ | ∃ x ∈ (closedCube w ρ hρ : Set (SpatialCoordinates d)), v = g x} := by
    intro g hg hg0
    have hbdd : BddAbove {v : ℝ | ∃ x ∈ (closedCube w ρ hρ : Set (SpatialCoordinates d)),
        v = g x} := by
      refine (hKc.bddAbove_image hg.continuousOn).mono ?_
      rintro v ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    exact ⟨Real.sSup_nonneg (by rintro v ⟨x, _, rfl⟩; exact hg0 x),
      fun y hy => le_csSup hbdd ⟨y, hy, rfl⟩⟩
  obtain ⟨hA0, hA⟩ := key (fun x => |phi x|) hphi.continuous.abs (fun x => abs_nonneg _)
  obtain ⟨hB0, hB⟩ := key (fun x => ‖fderiv ℝ phi x‖)
    (hphi.continuous_fderiv (by norm_num)).norm (fun x => norm_nonneg _)
  obtain ⟨hD0, hD⟩ := key (fun x => ‖fderiv ℝ (fderiv ℝ phi) x‖)
    ((hphi.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).norm
    (fun x => norm_nonneg (fderiv ℝ (fderiv ℝ phi) x))
  have hsum : c2Norm (closedCube w ρ hρ : Set (SpatialCoordinates d)) phi =
      sSup {v : ℝ | ∃ x ∈ (closedCube w ρ hρ : Set (SpatialCoordinates d)), v = |phi x|} +
      sSup {v : ℝ | ∃ x ∈ (closedCube w ρ hρ : Set (SpatialCoordinates d)),
        v = ‖fderiv ℝ phi x‖} +
      sSup {v : ℝ | ∃ x ∈ (closedCube w ρ hρ : Set (SpatialCoordinates d)),
        v = ‖fderiv ℝ (fderiv ℝ phi) x‖} := rfl
  refine ⟨by linarith, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have := hA y hy; linarith
  · have := hB y hy; linarith
  · have := hD y hy; linarith

/-- The dilated point of a unit-cube point lies in the closed cell. -/
theorem aux_rem_bank_response_moments_dil_mem {d : ℕ} (w : SpatialCoordinates d) (ρ : ℝ)
    (hρ : 0 < ρ) (h1 : (0 : ℝ) < 1) (x : SpatialCoordinates d)
    (hx : x ∈ (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) :
    w + ρ • x ∈ (closedCube w ρ hρ : Set (SpatialCoordinates d)) := by
  have hx' : ‖x‖ < 1 / 2 := by
    have := Metric.mem_ball.1 hx
    simpa [dist_zero_right] using this
  change w + ρ • x ∈ Metric.closedBall w (ρ / 2)
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos hρ]
  nlinarith

/-- Chain rule for the dilated datum. -/
theorem aux_rem_bank_response_moments_fderiv_dil {d : ℕ} (w : SpatialCoordinates d) (ρ : ℝ)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 2 phi) (x : SpatialCoordinates d) :
    fderiv ℝ (fun y : SpatialCoordinates d => phi (w + ρ • y)) x =
      ρ • fderiv ℝ phi (w + ρ • x) := by
  have hT : HasFDerivAt (fun y : SpatialCoordinates d => w + ρ • y)
      (ρ • ContinuousLinearMap.id ℝ (SpatialCoordinates d)) x := by
    have := ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul ρ).const_add w
    exact this
  have hphid : HasFDerivAt phi (fderiv ℝ phi (w + ρ • x)) (w + ρ • x) :=
    ((hphi.differentiable (by norm_num)) _).hasFDerivAt
  have hc := hphid.comp x hT
  rw [show (fun y : SpatialCoordinates d => phi (w + ρ • y)) =
      phi ∘ (fun y : SpatialCoordinates d => w + ρ • y) from rfl, hc.fderiv]
  ext v
  simp

/-- The gradient components of the dilated datum. -/
def aux_rem_bank_response_moments_dilGrad {d : ℕ} (w : SpatialCoordinates d) (ρ : ℝ)
    (phi : SpatialCoordinates d → ℝ) (i : Fin d) (x : SpatialCoordinates d) : ℝ :=
  ρ * (fderiv ℝ phi (w + ρ • x)) (Pi.single i (1 : ℝ))

theorem aux_rem_bank_response_moments_norm_single_le {d : ℕ} (i : Fin d) :
    ‖(Pi.single i (1 : ℝ) : SpatialCoordinates d)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- Pointwise and Lipschitz bounds for the dilated gradient components on the unit cube. -/
theorem aux_rem_bank_response_moments_dilGrad_bounds {d : ℕ} (w : SpatialCoordinates d)
    (ρ : ℝ) (hρ : 0 < ρ) (h1 : (0 : ℝ) < 1) (phi : SpatialCoordinates d → ℝ)
    (hphi : ContDiff ℝ 2 phi) (Cphi : ℝ)
    (hC : c2Norm (closedCube w ρ hρ : Set (SpatialCoordinates d)) phi ≤ Cphi) (i : Fin d) :
    (∀ x ∈ (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      |aux_rem_bank_response_moments_dilGrad w ρ phi i x| ≤ ρ * Cphi) ∧
    LipschitzOnWith ⟨ρ ^ 2 * Cphi, by
        have := (aux_rem_bank_response_moments_c2_bounds w ρ hρ phi hphi Cphi hC).1
        positivity⟩
      (aux_rem_bank_response_moments_dilGrad w ρ phi i)
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) := by
  obtain ⟨hC0, -, hD1, hD2⟩ := aux_rem_bank_response_moments_c2_bounds w ρ hρ phi hphi Cphi hC
  have hsingle := aux_rem_bank_response_moments_norm_single_le (d := d) i
  refine ⟨fun x hx => ?_, ?_⟩
  · have hmem := aux_rem_bank_response_moments_dil_mem w ρ hρ h1 x hx
    unfold aux_rem_bank_response_moments_dilGrad
    rw [abs_mul, abs_of_pos hρ]
    refine mul_le_mul_of_nonneg_left ?_ hρ.le
    calc |(fderiv ℝ phi (w + ρ • x)) (Pi.single i (1 : ℝ))|
        ≤ ‖fderiv ℝ phi (w + ρ • x)‖ * ‖(Pi.single i (1 : ℝ) : SpatialCoordinates d)‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ Cphi * 1 := mul_le_mul (hD1 _ hmem) hsingle (norm_nonneg _) hC0
      _ = Cphi := mul_one _
  · -- mean value inequality for `fderiv phi` on the convex closed cell
    have hdiff : Differentiable ℝ (fderiv ℝ phi) :=
      (hphi.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have hmv : ∀ y ∈ (closedCube w ρ hρ : Set (SpatialCoordinates d)),
        ∀ y' ∈ (closedCube w ρ hρ : Set (SpatialCoordinates d)),
        ‖fderiv ℝ phi y' - fderiv ℝ phi y‖ ≤ Cphi * ‖y' - y‖ := by
      intro y hy y' hy'
      refine Convex.norm_image_sub_le_of_norm_fderiv_le (fun v _ => hdiff v) hD2 ?_ hy hy'
      exact convex_closedBall w (ρ / 2)
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have hxm := aux_rem_bank_response_moments_dil_mem w ρ hρ h1 x hx
    have hym := aux_rem_bank_response_moments_dil_mem w ρ hρ h1 y hy
    rw [Real.dist_eq, dist_eq_norm]
    unfold aux_rem_bank_response_moments_dilGrad
    rw [← mul_sub, abs_mul, abs_of_pos hρ, ← sub_apply]
    have h2 := hmv _ hym _ hxm
    have hxy : (w + ρ • x) - (w + ρ • y) = ρ • (x - y) := by
      rw [add_sub_add_left_eq_sub, smul_sub]
    rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_pos hρ] at h2
    calc ρ * |(fderiv ℝ phi (w + ρ • x) - fderiv ℝ phi (w + ρ • y)) (Pi.single i (1 : ℝ))|
        ≤ ρ * (‖fderiv ℝ phi (w + ρ • x) - fderiv ℝ phi (w + ρ • y)‖ *
            ‖(Pi.single i (1 : ℝ) : SpatialCoordinates d)‖) := by
          refine mul_le_mul_of_nonneg_left ?_ hρ.le
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ ρ * ((Cphi * (ρ * ‖x - y‖)) * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hρ.le
          exact mul_le_mul h2 hsingle (norm_nonneg _) (by positivity)
      _ = ρ ^ 2 * Cphi * ‖x - y‖ := by ring

/-- The dilated smooth datum as a weak Sobolev datum on the unit cube. -/
theorem aux_rem_bank_response_moments_dil_datum {d : ℕ} (w : SpatialCoordinates d)
    (ρ : ℝ) (hρ : 0 < ρ) (h1 : (0 : ℝ) < 1) (phi : SpatialCoordinates d → ℝ)
    (hphi : ContDiff ℝ 2 phi) (Cphi : ℝ)
    (hC : c2Norm (closedCube w ρ hρ : Set (SpatialCoordinates d)) phi ≤ Cphi) :
    ∃ hh : weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1),
      ((hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
          SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d))] (fun x => phi (w + ρ • x)) ∧
      ∀ i : Fin d,
        ((hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i :
          SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
            Set (SpatialCoordinates d))] aux_rem_bank_response_moments_dilGrad w ρ phi i := by
  obtain ⟨hC0, hphib, -, -⟩ := aux_rem_bank_response_moments_c2_bounds w ρ hρ phi hphi Cphi hC
  have hU : MeasurableSet (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)) := (centeredCube (0 : SpatialCoordinates d) 1 h1).isOpen.measurableSet
  have : IsFiniteMeasure (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, centeredCube_volume _ h1]
    exact ENNReal.ofReal_lt_top
  have hmap : Continuous (fun x : SpatialCoordinates d => w + ρ • x) := by fun_prop
  have hψc : Continuous (fun x : SpatialCoordinates d => phi (w + ρ • x)) :=
    hphi.continuous.comp hmap
  have hψmem : MemLp (fun x : SpatialCoordinates d => phi (w + ρ • x)) 2
      (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d))) := by
    refine MemLp.of_bound hψc.aestronglyMeasurable Cphi ?_
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [Real.norm_eq_abs]
    exact hphib _ (aux_rem_bank_response_moments_dil_mem w ρ hρ h1 x hx)
  have hgc : ∀ i : Fin d, Continuous (aux_rem_bank_response_moments_dilGrad w ρ phi i) := by
    intro i
    unfold aux_rem_bank_response_moments_dilGrad
    refine continuous_const.mul ?_
    exact ((hphi.continuous_fderiv (by norm_num)).comp hmap).clm_apply continuous_const
  have hgmem : ∀ i : Fin d, MemLp (aux_rem_bank_response_moments_dilGrad w ρ phi i) 2
      (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d))) := by
    intro i
    refine MemLp.of_bound (hgc i).aestronglyMeasurable (ρ * Cphi) ?_
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [Real.norm_eq_abs]
    exact (aux_rem_bank_response_moments_dilGrad_bounds w ρ hρ h1 phi hphi Cphi hC i).1 x hx
  let D : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1) :=
    (hψmem.toLp _, fun i => (hgmem i).toLp _)
  have hDmem : D ∈ weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1) := by
    rw [mem_weakSobolevGraph_iff_hasWeakGradientOn]
    intro i
    have hmap1 : ContDiff ℝ 1 (fun x : SpatialCoordinates d => w + ρ • x) := by fun_prop
    have hC1 : ContDiff ℝ 1 (fun x : SpatialCoordinates d => phi (w + ρ • x)) :=
      (hphi.of_le (by norm_num)).comp hmap1
    have hw := Homogenization.HasWeakGradientOn.of_contDiff
      (U := (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) hC1 i
    refine hasWeakPartialDerivOn_congr_ae (MemLp.coeFn_toLp hψmem).symm ?_ hw
    refine (Filter.EventuallyEq.of_eq ?_).trans (MemLp.coeFn_toLp (hgmem i)).symm
    funext x
    show (fderiv ℝ (fun y : SpatialCoordinates d => phi (w + ρ • y)) x)
      (Homogenization.basisVec i) = aux_rem_bank_response_moments_dilGrad w ρ phi i x
    rw [aux_rem_bank_response_moments_fderiv_dil w ρ phi hphi x]
    simp [aux_rem_bank_response_moments_dilGrad, Homogenization.basisVec]
  exact ⟨⟨D, hDmem⟩, MemLp.coeFn_toLp hψmem, fun i => MemLp.coeFn_toLp (hgmem i)⟩

end RBCell_part

section RBCellBound_part
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity


/-- The smooth-datum cell constant `C² σ^{-3} d (σ M + 1)` at `σ = 1/8`, where `c` is the
constant `X.C` of `in_extension` (paper `e.cg.RHS` carries `C(d)` on the boundary-datum term). -/
def aux_rem_bank_response_moments_Csm (d : ℕ) (c : ℝ) : ℝ :=
  c ^ 2 * (2 * (1 / 8 : ℝ) ^ (-3 : ℝ) * d *
    ((1 / 8 : ℝ) * (aux_rem_bank_response_moments_kernelMass d 1 (1 / 8)).toReal + 1))

theorem aux_rem_bank_response_moments_Csm_nonneg (d : ℕ) (c : ℝ) :
    0 ≤ aux_rem_bank_response_moments_Csm d c := by
  unfold aux_rem_bank_response_moments_Csm
  have : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ (-3 : ℝ) := Real.rpow_nonneg (by norm_num) _
  positivity

/-- One gradient component of the dilated smooth datum has normalized `H^{1/8}` norm
squared at most `ρ² Cφ² (M/8 + 1)` on the unit cube. -/
theorem aux_rem_bank_response_moments_component_sqNorm {d : ℕ} (hd : 2 ≤ d)
    (h1 : (0 : ℝ) < 1) (v : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (g : SpatialCoordinates d → ℝ) (ρ Cphi : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hC0 : 0 ≤ Cphi)
    (hvg : (v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))] g)
    (hgb : ∀ x ∈ (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      |g x| ≤ ρ * Cphi)
    (hgl : LipschitzOnWith ⟨ρ ^ 2 * Cphi, by positivity⟩ g
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) :
    cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 h1
        ⟨1 / 8, by norm_num, by norm_num⟩ (fun _ : Fin 1 => v) < ⊤ ∧
    cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 h1 ⟨1 / 8, by norm_num, by norm_num⟩ v ≤
      ρ ^ 2 * Cphi ^ 2 *
        ((1 / 8 : ℝ) * (aux_rem_bank_response_moments_kernelMass d 1 (1 / 8)).toReal + 1) := by
  obtain ⟨hlt, hsq⟩ := aux_rem_bank_response_moments_seminorm_sq_le hd (0 : SpatialCoordinates d)
    1 h1 ⟨1 / 8, by norm_num, by norm_num⟩ v g ⟨ρ ^ 2 * Cphi, by positivity⟩ hvg hgl
  refine ⟨hlt, ?_⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (aux_rem_bank_response_moments_kernelMass d 1 (1 / 8)).toReal :=
    ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; exact ENNReal.toReal_nonneg
  rw [← hM] at hsq ⊢
  have hvol : volume.real (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)) = 1 := by
    rw [centeredCube_volume_real _ h1, one_pow]
  have : IsFiniteMeasure (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, centeredCube_volume _ h1]
    exact ENNReal.ofReal_lt_top
  have hU : MeasurableSet (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)) :=
    (centeredCube (0 : SpatialCoordinates d) 1 h1).isOpen.measurableSet
  have hnorm : ‖v‖ ≤ ρ * Cphi := by
    have hb := Lp.norm_le_of_ae_bound (μ := volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)))
      (f := v) (mul_nonneg hρ.le hC0) (by
        filter_upwards [hvg, ae_restrict_mem hU] with x hx hxU
        rw [hx, Real.norm_eq_abs]
        exact hgb x hxU)
    have hμ : measureUnivNNReal (volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))) = 1 := by
      unfold measureUnivNNReal
      rw [Measure.restrict_apply_univ, centeredCube_volume _ h1, one_pow,
        ENNReal.ofReal_one, ENNReal.toNNReal_one]
    rw [hμ, NNReal.coe_one, Real.one_rpow, one_mul] at hb
    exact hb
  have hn2 : ‖v‖ ^ 2 ≤ (ρ * Cphi) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
  rw [hvol, div_one, Fin.sum_univ_one]
  have hρ2 : ρ ^ 2 ≤ 1 := pow_le_one₀ hρ.le hρ1
  have hA : (1 / 8 : ℝ) * (ρ ^ 2 * Cphi) ^ 2 * M ≤ ρ ^ 2 * Cphi ^ 2 * ((1 / 8 : ℝ) * M) := by
    have h0 : 0 ≤ ρ ^ 2 * Cphi ^ 2 * ((1 / 8 : ℝ) * M) := by positivity
    have : (1 / 8 : ℝ) * (ρ ^ 2 * Cphi) ^ 2 * M = ρ ^ 2 * (ρ ^ 2 * Cphi ^ 2 * ((1 / 8 : ℝ) * M)) := by
      ring
    rw [this]
    exact mul_le_of_le_one_left h0 hρ2
  have hsq' : (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 h1
      ⟨1 / 8, by norm_num, by norm_num⟩ (fun _ : Fin 1 => v)).toReal ^ 2 ≤
      (1 / 8 : ℝ) * (ρ ^ 2 * Cphi) ^ 2 * M := by
    exact hsq
  nlinarith [hsq', hA, hn2]

/-- **The smooth-datum cell bound** (the `S`-free replacement of `eq:mfd-2` for a
`C²` datum): on a cube of side `ρ ≤ 1`, the Dirichlet response of a datum that is a.e. the
restriction of a `C²` function is at most `Csm Λ_{1/16,2} ρ^{d-2} ρ² Cφ²`.  The proof
dilates the datum itself to the unit cube (no trace extension), applies `in_extension`
there (`aux_lem_extension_unit_energy`) with the quantitative Lipschitz Gagliardo bound,
and pushes the harmonic correction back (`aux_lem_extension_response_le`). -/
theorem aux_rem_bank_response_moments_cell_smooth {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (X : in_extension d hd E) (w : SpatialCoordinates d) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube w ρ hρ),
      ‖(u : SobolevData (centeredCube w ρ hρ)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube w ρ hρ)) u‖)
    (a : PositiveCoefficient (centeredCube w ρ hρ))
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 2 phi) (Cphi : ℝ)
    (hC : c2Norm (closedCube w ρ hρ : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b : weakSobolevGraph (centeredCube w ρ hρ))
    (hb : ((b : SobolevData (centeredCube w ρ hρ)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube w ρ hρ : Set (SpatialCoordinates d))] phi) :
    dirichletResponse (killedResponseSpace hP) a b ≤
      aux_rem_bank_response_moments_Csm d X.C * E.Lam w ρ hρ a w ρ ((3 / 4 - 1 / 2) / 4) 2 *
        ρ ^ ((d : ℝ) - 2) * ρ ^ 2 * Cphi ^ 2 := by
  have h1 : (0 : ℝ) < 1 := one_pos
  have : NeZero d := ⟨by omega⟩
  have hσ : (1 / 8 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hC0 := (aux_rem_bank_response_moments_c2_bounds w ρ hρ phi hphi Cphi hC).1
  obtain ⟨ah, hah⟩ := dilation_coefficient_transport d w 0 ρ hρ h1 a
  have hLam : E.Lam w ρ hρ a w ρ ((3 / 4 - 1 / 2) / 4) 2 =
      E.Lam 0 1 h1 ah 0 1 ((1 / 8 : ℝ) / 2) 2 := by
    rw [show ((3 / 4 - 1 / 2) / 4 : ℝ) = (1 / 8 : ℝ) / 2 by norm_num]
    exact E.Lam_dilation w ρ hρ a 0 h1 ah hah _ 2
  obtain ⟨hh, hhv, hhg⟩ := aux_rem_bank_response_moments_dil_datum w ρ hρ h1 phi hphi Cphi hC
  have hcomp : ∀ i : Fin d,
      cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 h1
          ⟨1 / 8, by norm_num, by norm_num⟩
          (fun _ : Fin 1 => (hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i)
          < ⊤ ∧
      cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 h1 ⟨1 / 8, by norm_num, by norm_num⟩
          ((hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i) ≤
        ρ ^ 2 * Cphi ^ 2 *
          ((1 / 8 : ℝ) * (aux_rem_bank_response_moments_kernelMass d 1 (1 / 8)).toReal + 1) := by
    intro i
    have hbd := aux_rem_bank_response_moments_dilGrad_bounds w ρ hρ h1 phi hphi Cphi hC i
    exact aux_rem_bank_response_moments_component_sqNorm hd h1 _ _ ρ Cphi hρ hρ1 hC0
      (hhg i) hbd.1 hbd.2
  obtain ⟨hP1, -⟩ := exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    (centeredCube (0 : SpatialCoordinates d) 1 h1)
    (aux_lem_extension_isOpenBoundedConvexDomain_centeredCube 0 h1)
  have hEn := aux_lem_extension_unit_energy hd E X h1 hP1 ah (1 / 8) hσ hh
    (fun i => (hcomp i).1)
  have hker := dirichletMinimizer_mem_affine (killedResponseSpace hP1) ah hh
  obtain ⟨k, hktie⟩ := aux_lem_extension_killed_pushforward w hρ h1 ⟨_, hker⟩
  have hhtie : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)),
      (hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 x =
        (b : SobolevData (centeredCube w ρ hρ)).1 (cubeDilation w 0 ρ x) := by
    have hbx := (aux_lem_extension_ae_dilation_iff w hρ h1
      (fun y => ((b : SobolevData (centeredCube w ρ hρ)).1 : SpatialCoordinates d → ℝ) y =
        phi y)).1 hb
    filter_upwards [hhv, hbx] with x hx1 hx2
    rw [hx1, hx2, aux_lem_extension_cubeDilation_eq]
  have hhb : (b : SobolevData (centeredCube w ρ hρ)) - (b : SobolevData (centeredCube w ρ hρ)) ∈
      killedSobolevGraph (centeredCube w ρ hρ) := by
    rw [sub_self]; exact zero_mem _
  have hresp := aux_lem_extension_response_le w hρ h1 hP a ah hah b b k hhb hh
    (dirichletMinimizer (killedResponseSpace hP1) ah hh) hhtie hktie
  -- the sum of the component norms
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (1 / 8 : ℝ) *
      (aux_rem_bank_response_moments_kernelMass d 1 (1 / 8)).toReal + 1 := ⟨_, rfl⟩
  have hsum : ∑ i : Fin d, cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 h1
      ⟨1 / 8, hσ.1, hσ.2⟩ ((hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i) ≤
      (d : ℝ) * (ρ ^ 2 * Cphi ^ 2 * Q) := by
    calc _ ≤ ∑ _i : Fin d, ρ ^ 2 * Cphi ^ 2 * Q :=
          Finset.sum_le_sum fun i _ => by rw [hQ]; exact (hcomp i).2
      _ = (d : ℝ) * (ρ ^ 2 * Cphi ^ 2 * Q) := by simp
  have hLpos := E.Lam_pos 0 1 h1 ah 0 1 ((1 / 8 : ℝ) / 2) 2
  have hs3 : (0 : ℝ) ≤ (1 / 8 : ℝ) ^ (-3 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hrd : 0 ≤ ρ ^ ((d : ℝ) - 2) := Real.rpow_nonneg hρ.le _
  refine hresp.trans ?_
  rw [hLam]
  calc ρ ^ ((d : ℝ) - 2) * sobolevCoefficientForm ah
        (dirichletMinimizer (killedResponseSpace hP1) ah hh : SobolevData _)
        (dirichletMinimizer (killedResponseSpace hP1) ah hh : SobolevData _)
      ≤ ρ ^ ((d : ℝ) - 2) * (2 * X.C ^ 2 * (1 / 8 : ℝ) ^ (-3 : ℝ) *
          E.Lam 0 1 h1 ah 0 1 ((1 / 8 : ℝ) / 2) 2 * ((d : ℝ) * (ρ ^ 2 * Cphi ^ 2 * Q))) := by
        refine mul_le_mul_of_nonneg_left (hEn.trans ?_) hrd
        exact mul_le_mul_of_nonneg_left hsum
          (mul_nonneg (mul_nonneg (mul_nonneg two_pos.le (sq_nonneg _)) hs3) hLpos.le)
    _ = aux_rem_bank_response_moments_Csm d X.C * E.Lam 0 1 h1 ah 0 1 ((1 / 8 : ℝ) / 2) 2 *
          ρ ^ ((d : ℝ) - 2) * ρ ^ 2 * Cphi ^ 2 := by
        unfold aux_rem_bank_response_moments_Csm
        rw [← hQ]
        ring

end RBCellBound_part

section RBWhitney_part
open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity


section RouteWSmooth
open Homogenization Homogenization.Book.Ch02

/-- `ρ² ≤ (ρ^{3/4})²` for `0 < ρ ≤ 1`. -/
theorem aux_rem_bank_response_moments_sq_le_rpow {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ρ ^ 2 ≤ (ρ ^ (3 / 4 : ℝ)) ^ 2 := by
  rw [← Real.rpow_natCast (ρ ^ (3 / 4 : ℝ)) 2, ← Real.rpow_mul hρ.le, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)

/-- **Per-cell bound, smooth datum** (replaces `aux_aux_macro_moment_bank_cell_response`,
which consumes `lem_extension`'s general Hölder-datum clause). -/
theorem aux_rem_bank_response_moments_cell_response {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (X : in_extension d hd E)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (K : ℝ)
    (hK : ∀ (k : ℕ) (nidx : Fin d → ℤ), k ≤ N →
      aux_aux_macro_moment_bank_cell z k nidx ≤ centeredCube z 1 one_pos →
      E.Lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((5 / 8 - 1 / 2) / 4) 2 +
        (E.lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((5 / 8 - 1 / 2) / 4) 2)⁻¹ ≤
        K * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-(1 / 8 : ℝ)))
    (k : ℕ) (T : TriadicCube d) (hT : T ∈ descendantsAtDepth (originCube d 0) k)
    (w : SpatialCoordinates d) (hw : w = fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ))
    (ρ : ℝ) (hρdef : ρ = (3 : ℝ) ^ (-(k : ℤ))) (hρ : 0 < ρ)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube w ρ hρ),
      ‖(u : SobolevData (centeredCube w ρ hρ)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube w ρ hρ)) u‖)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hC : c2Norm (closedCube w ρ hρ : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b : weakSobolevGraph (centeredCube w ρ hρ))
    (hb : ((b : SobolevData (centeredCube w ρ hρ)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube w ρ hρ : Set (SpatialCoordinates d))] phi) :
    dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N w hρ) b ≤
      aux_rem_bank_response_moments_Csm d X.C * aux_aux_macro_moment_bank_Cs * K *
        Cphi ^ 2 * ((((3 : ℝ) ^ k) ^ (d - 1))⁻¹ * ((3 : ℝ) ^ (-(5 / 16 : ℝ))) ^ k) := by
  subst hw hρdef
  have hρ1 : (3 : ℝ) ^ (-(k : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hresp := aux_rem_bank_response_moments_cell_smooth hd E X
    (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ))) hρ hρ1 hP
    (cutoffPositiveCoefficient M H om N
      (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) hρ) phi hphi Cphi hC b hb
  obtain ⟨hKpos, hLam⟩ := aux_aux_macro_moment_bank_cell_Lam_le E M H om N z K hK k T hT
  have hC0 := (aux_rem_bank_response_moments_c2_bounds _ _ hρ phi hphi Cphi hC).1
  rw [← aux_aux_macro_moment_bank_cell_exponent (by omega) k]
  have hCsm := aux_rem_bank_response_moments_Csm_nonneg d X.C
  have hCs := aux_aux_macro_moment_bank_Cs_nonneg
  have hrd : 0 ≤ ((3 : ℝ) ^ (-(k : ℤ))) ^ ((d : ℝ) - 2) := Real.rpow_nonneg hρ.le _
  have h2 := aux_rem_bank_response_moments_sq_le_rpow hρ hρ1
  have hT3 : (0 : ℝ) ≤ (3 : ℝ) ^ ((3 / 16 : ℝ) * k) := Real.rpow_nonneg (by norm_num) _
  have hLam0 := E.Lam_pos (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ))
    ((3 : ℝ) ^ (-(k : ℤ))) hρ
    (cutoffPositiveCoefficient M H om N
      (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) hρ)
    (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
    ((3 / 4 - 1 / 2) / 4) 2
  refine hresp.trans ?_
  calc aux_rem_bank_response_moments_Csm d X.C *
        E.Lam (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ))) hρ
          (cutoffPositiveCoefficient M H om N
            (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) hρ)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((3 / 4 - 1 / 2) / 4) 2 *
        ((3 : ℝ) ^ (-(k : ℤ))) ^ ((d : ℝ) - 2) * ((3 : ℝ) ^ (-(k : ℤ))) ^ 2 * Cphi ^ 2
      ≤ aux_rem_bank_response_moments_Csm d X.C *
          (aux_aux_macro_moment_bank_Cs * K * (3 : ℝ) ^ ((3 / 16 : ℝ) * k)) *
        ((3 : ℝ) ^ (-(k : ℤ))) ^ ((d : ℝ) - 2) *
          (((3 : ℝ) ^ (-(k : ℤ))) ^ (3 / 4 : ℝ)) ^ 2 * Cphi ^ 2 := by
        have hA : aux_rem_bank_response_moments_Csm d X.C *
            E.Lam (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ))) hρ
              (cutoffPositiveCoefficient M H om N
                (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) hρ)
              (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (T.index i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
              ((3 / 4 - 1 / 2) / 4) 2 * ((3 : ℝ) ^ (-(k : ℤ))) ^ ((d : ℝ) - 2) ≤
            aux_rem_bank_response_moments_Csm d X.C *
              (aux_aux_macro_moment_bank_Cs * K * (3 : ℝ) ^ ((3 / 16 : ℝ) * k)) *
              ((3 : ℝ) ^ (-(k : ℤ))) ^ ((d : ℝ) - 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLam hCsm) hrd
        have hB0 : 0 ≤ aux_rem_bank_response_moments_Csm d X.C *
            (aux_aux_macro_moment_bank_Cs * K * (3 : ℝ) ^ ((3 / 16 : ℝ) * k)) *
            ((3 : ℝ) ^ (-(k : ℤ))) ^ ((d : ℝ) - 2) := by
          have := hKpos.le
          positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul hA h2 (sq_nonneg _) hB0) (sq_nonneg _)
    _ = aux_rem_bank_response_moments_Csm d X.C * aux_aux_macro_moment_bank_Cs * K * Cphi ^ 2 *
          (((3 : ℝ) ^ (-(k : ℤ))) ^ ((d : ℝ) - 2) *
            (((3 : ℝ) ^ (-(k : ℤ))) ^ (3 / 4 : ℝ)) ^ 2 * (3 : ℝ) ^ ((3 / 16 : ℝ) * k)) := by
        ring

/-- The constant of the smooth working-cube boundary response. -/
def aux_rem_bank_response_moments_Cstar (d : ℕ) (c : ℝ) : ℝ :=
  aux_rem_bank_response_moments_Csm d c * aux_aux_macro_moment_bank_Cs *
    (4 * d * (1 - (3 : ℝ) ^ (-(5 / 16 : ℝ)))⁻¹)

theorem aux_rem_bank_response_moments_Cstar_nonneg (d : ℕ) (c : ℝ) :
    0 ≤ aux_rem_bank_response_moments_Cstar d c := by
  unfold aux_rem_bank_response_moments_Cstar
  have h1 := aux_aux_macro_moment_bank_rho_facts.2
  have h2 : 0 < 1 - (3 : ℝ) ^ (-(5 / 16 : ℝ)) := by linarith
  have h3 := aux_aux_macro_moment_bank_Cs_nonneg
  have h4 := aux_rem_bank_response_moments_Csm_nonneg d c
  positivity

/-- **(M7, fixed depth, smooth datum)** Gluing the cell minimizers over the Whitney family. -/
theorem aux_rem_bank_response_moments_whitney_glue {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (X : in_extension d hd E)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (K : ℝ)
    (hK : ∀ (k : ℕ) (nidx : Fin d → ℤ), k ≤ N →
      aux_aux_macro_moment_bank_cell z k nidx ≤ centeredCube z 1 one_pos →
      E.Lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((5 / 8 - 1 / 2) / 4) 2 +
        (E.lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((5 / 8 - 1 / 2) / 4) 2)⁻¹ ≤
        K * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-(1 / 8 : ℝ)))
    (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hC : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (Mw : ℕ) :
    dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr) b ≤
      aux_rem_bank_response_moments_Cstar d X.C * K * Cphi ^ 2 +
        ∑ i : Fin d, ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)) \
            ⋃ q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw),
              (centeredCube (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
                ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity) : Set (SpatialCoordinates d)),
          (cutoffPositiveCoefficient M H om N z hr).val x *
            ((b : SobolevData (centeredCube z r hr)).2 i x *
              (b : SobolevData (centeredCube z r hr)).2 i x) := by
  classical
  have hle : ∀ q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw),
      centeredCube (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
        ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity) ≤ centeredCube z r hr := by
    intro q
    have hmem := (aux_aux_macro_moment_bank_mem_whitney r Mw q.1).1 q.2
    exact aux_aux_macro_moment_bank_cell_le z r hr q.1.1 q.1.2
      (aux_aux_macro_moment_bank_scale_of_mem _ _ hmem.2.1) hmem.2.2.1
  have hdisj : Pairwise (fun q q' : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw) =>
      Disjoint (centeredCube (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
          ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity) : Set (SpatialCoordinates d))
        (centeredCube (fun i => z i + (3 : ℝ) ^ (-(q'.1.1 : ℤ)) * (q'.1.2.index i : ℝ))
          ((3 : ℝ) ^ (-(q'.1.1 : ℤ))) (by positivity) : Set (SpatialCoordinates d))) := by
    intro q q' hne
    exact aux_aux_macro_moment_bank_whitney_disjoint z r Mw q.1 q'.1 q.2 q'.2
      (fun h => hne (Subtype.ext h))
  have hPc : ∀ q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw),
      ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube
        (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
        ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity)),
      ‖(u : SobolevData (centeredCube
        (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
        ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity))).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube
          (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
          ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity))) u‖ := fun q =>
    aux_aux_macro_moment_bank_killed_poincare hd _ _ _
  have hac : ∀ q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw),
      ∀ᵐ x ∂volume.restrict (centeredCube
        (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
        ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity) : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H om N
          (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
          (by positivity : (0 : ℝ) < (3 : ℝ) ^ (-(q.1.1 : ℤ)))).val x =
        (cutoffPositiveCoefficient M H om N z hr).val x := fun q =>
    aux_aux_macro_moment_bank_cutoff_ae_eq M H om N _ _ _ z r hr (fun x hx => hle q hx)
  have hg := aux_aux_macro_moment_bank_glue_le
    (fun q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw) =>
      centeredCube (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
        ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity)) hle hdisj hP hPc
    (cutoffPositiveCoefficient M H om N z hr)
    (fun q => cutoffPositiveCoefficient M H om N
      (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
      (by positivity : (0 : ℝ) < (3 : ℝ) ^ (-(q.1.1 : ℤ)))) hac b
  refine hg.trans (add_le_add ?_ le_rfl)
  have hCphi : 0 ≤ Cphi := (aux_rem_bank_response_moments_c2_bounds z r hr phi hphi Cphi hC).1
  have hKpos : 0 < K := (aux_aux_macro_moment_bank_cell_Lam_le E M H om N z K hK 0
    (originCube d 0) (by rw [descendantsAtDepth_zero]; exact Finset.mem_singleton_self _)).1
  have hcell : ∀ q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw),
      dirichletResponse (killedResponseSpace (hPc q))
          (cutoffPositiveCoefficient M H om N
            (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
            (by positivity : (0 : ℝ) < (3 : ℝ) ^ (-(q.1.1 : ℤ))))
          ⟨sobolevDataRestrict (hle q) (b : SobolevData (centeredCube z r hr)),
            sobolevDataRestrict_mem_weak (hle q) b.property⟩ ≤
        aux_rem_bank_response_moments_Csm d X.C * aux_aux_macro_moment_bank_Cs * K *
          Cphi ^ 2 * ((((3 : ℝ) ^ q.1.1) ^ (d - 1))⁻¹ * ((3 : ℝ) ^ (-(5 / 16 : ℝ))) ^ q.1.1) := by
    intro q
    have hmem := (aux_aux_macro_moment_bank_mem_whitney r Mw q.1).1 q.2
    have hsub : (centeredCube (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
        ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity) : Set (SpatialCoordinates d)) ⊆
        centeredCube z r hr := fun x hx => hle q hx
    have hCq : c2Norm (closedCube (fun i => z i + (3 : ℝ) ^ (-(q.1.1 : ℤ)) * (q.1.2.index i : ℝ))
        ((3 : ℝ) ^ (-(q.1.1 : ℤ))) (by positivity) : Set (SpatialCoordinates d)) phi ≤ Cphi :=
      (aux_aux_macro_moment_bank_c2Norm_mono _ _ (closedCube z r hr).isCompact
        ⟨_, Metric.mem_closedBall_self (by positivity)⟩
        (aux_aux_macro_moment_bank_closedCube_subset _ _ _ z r hr hsub) phi hphi).trans hC
    exact aux_rem_bank_response_moments_cell_response hd E X M H om N z K hK q.1.1
      q.1.2 hmem.2.1 _ rfl _ rfl _ (hPc q) phi Cphi hphi hCq _
      (aux_aux_macro_moment_bank_restrict_datum_ae (hle q) b phi hb)
  have hsum := aux_aux_macro_moment_bank_whitney_sum (d := d) (by omega) r Mw
    ((3 : ℝ) ^ (-(5 / 16 : ℝ))) aux_aux_macro_moment_bank_rho_facts.1
    aux_aux_macro_moment_bank_rho_facts.2
  have hC0 : 0 ≤ aux_rem_bank_response_moments_Csm d X.C * aux_aux_macro_moment_bank_Cs * K *
      Cphi ^ 2 := by
    have := aux_aux_macro_moment_bank_Cs_nonneg
    have := aux_rem_bank_response_moments_Csm_nonneg d X.C
    have := hKpos.le
    positivity
  calc _ ≤ ∑ q : ↥(aux_aux_macro_moment_bank_whitney (d := d) r Mw),
        aux_rem_bank_response_moments_Csm d X.C * aux_aux_macro_moment_bank_Cs * K *
          Cphi ^ 2 * ((((3 : ℝ) ^ q.1.1) ^ (d - 1))⁻¹ * ((3 : ℝ) ^ (-(5 / 16 : ℝ))) ^ q.1.1) :=
        Finset.sum_le_sum fun q _ => hcell q
    _ = aux_rem_bank_response_moments_Csm d X.C * aux_aux_macro_moment_bank_Cs * K *
          Cphi ^ 2 * ∑ p ∈ aux_aux_macro_moment_bank_whitney (d := d) r Mw,
            ((((3 : ℝ) ^ p.1) ^ (d - 1))⁻¹ * ((3 : ℝ) ^ (-(5 / 16 : ℝ))) ^ p.1) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_coe_sort (aux_aux_macro_moment_bank_whitney (d := d) r Mw)
          (fun p => (((3 : ℝ) ^ p.1) ^ (d - 1))⁻¹ * ((3 : ℝ) ^ (-(5 / 16 : ℝ))) ^ p.1)
    _ ≤ aux_rem_bank_response_moments_Csm d X.C * aux_aux_macro_moment_bank_Cs * K *
          Cphi ^ 2 * (4 * d * (1 - (3 : ℝ) ^ (-(5 / 16 : ℝ)))⁻¹) :=
        mul_le_mul_of_nonneg_left hsum hC0
    _ = aux_rem_bank_response_moments_Cstar d X.C * K * Cphi ^ 2 := by
        unfold aux_rem_bank_response_moments_Cstar
        ring

end RouteWSmooth

/-- **(M7, smooth datum) The working-cube boundary response.**  On the `eq:mfd-3` grid
event of the root `(z, 1)` at the cutoff `N`, the Dirichlet response of every `C²` datum on
a working cube of side `r ≤ 1` is at most `C_* K Cφ²`.  No `SobolevFoundationalInput`. -/
theorem aux_rem_bank_response_moments_boundary_response {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (X : in_extension d hd E)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (K : ℝ)
    (hK : ∀ (k : ℕ) (nidx : Fin d → ℤ), k ≤ N →
      aux_aux_macro_moment_bank_cell z k nidx ≤ centeredCube z 1 one_pos →
      E.Lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((5 / 8 - 1 / 2) / 4) 2 +
        (E.lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
          ((5 / 8 - 1 / 2) / 4) 2)⁻¹ ≤
        K * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-(1 / 8 : ℝ)))
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hC : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi) :
    dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr) b ≤
      aux_rem_bank_response_moments_Cstar d X.C * K * Cphi ^ 2 := by
  obtain ⟨Ca, hCa⟩ := coeff_ae_bound (cutoffPositiveCoefficient M H om N z hr)
  have hint : ∀ i : Fin d, IntegrableOn (fun x =>
      (cutoffPositiveCoefficient M H om N z hr).val x *
        ((b : SobolevData (centeredCube z r hr)).2 i x *
          (b : SobolevData (centeredCube z r hr)).2 i x))
      (centeredCube z r hr : Set (SpatialCoordinates d)) volume := fun i =>
    integrableOn_coeff_mul (Lp.aestronglyMeasurable _) hCa (Lp.memLp _) (Lp.memLp _)
  have hε := tendsto_finsetSum (Finset.univ : Finset (Fin d)) (fun i _ =>
    aux_aux_macro_moment_bank_uncovered_tendsto z r hr hr1 _ (hint i))
  simp only [Finset.sum_const_zero] at hε
  have hlim := hε.const_add (aux_rem_bank_response_moments_Cstar d X.C * K * Cphi ^ 2)
  rw [add_zero] at hlim
  exact ge_of_tendsto' hlim (fun Mw => aux_rem_bank_response_moments_whitney_glue hd E X
    M H om N z K hK r hr hP phi Cphi hphi hC b hb Mw)

end RBWhitney_part

section RBMeas_part
open MeasureTheory TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal ContDiff


variable {d : ℕ}

/-- The inclusion of the compact root cube into the ambient coordinate space. -/
def aux_rem_bank_response_moments_incl (K : Compacts (SpatialCoordinates d)) : C(K, SpatialCoordinates d) :=
  ⟨fun x => (x : SpatialCoordinates d), continuous_subtype_val⟩

/-- The log of the normalized cutoff coefficient, as a jointly continuous function of the
infrared field value and the bilateral sample. -/
def aux_rem_bank_response_moments_logPot (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (pr : C(SpatialCoordinates d, ℝ) × BilateralField d) : C(closedCube z r hr, ℝ) :=
  (pr.1.comp (aux_rem_bank_response_moments_incl _)) +
    (∑ j ∈ Finset.range (N + 1), (pr.2 (-(Int.ofNat j))).comp (aux_rem_bank_response_moments_incl _)) +
    ContinuousMap.const _
      (-Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)

theorem aux_rem_bank_response_moments_continuous_logPot (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    Continuous (aux_rem_bank_response_moments_logPot M N z hr) := by
  unfold aux_rem_bank_response_moments_logPot
  refine Continuous.add (Continuous.add ?_ ?_) continuous_const
  · exact (ContinuousMap.continuous_precomp (aux_rem_bank_response_moments_incl (closedCube z r hr))).comp continuous_fst
  · refine continuous_finsetSum _ fun j _ => ?_
    exact (ContinuousMap.continuous_precomp (aux_rem_bank_response_moments_incl (closedCube z r hr))).comp
      ((continuous_apply (-(Int.ofNat j))).comp continuous_snd)

theorem aux_rem_bank_response_moments_cutoffPositiveCoefficient_eq (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    cutoffPositiveCoefficient M H omega N z hr =
      @expPotentialCoefficient d (centeredCube z r hr)
        (@compactPotentialToLp d (centeredCube z r hr) (closedCube z r hr)
          ⟨centeredCube_subset_closedCube z hr⟩
          (aux_rem_bank_response_moments_logPot M N z hr (H omega, omega))) := by
  unfold cutoffPositiveCoefficient normalizedContinuousPositiveCoefficient
  congr 1
  congr 1
  ext x
  simp only [aux_rem_bank_response_moments_logPot, ContinuousMap.sub_apply, ContinuousMap.add_apply,
    ContinuousMap.const_apply, ContinuousMap.comp_apply, ContinuousMap.coe_sum,
    Finset.sum_apply, continuousPositiveLog, ContinuousMap.coe_mk, cutoffCoefficientCM,
    cutoffCoefficient, cutoffPotential, Real.log_one, sub_zero, aux_rem_bank_response_moments_incl]
  rw [Real.log_mul (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne')
      (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
  ring

/-- `L^e` transfer from a dominating nonnegative envelope. -/
theorem aux_rem_bank_response_moments_memLp_of_envelope {X : Type} [MeasurableSpace X] (mu : Measure X)
    (R Kf : X → ℝ) (C Cb : ℝ) (hC : 0 ≤ C) (e : ℝ≥0∞)
    (hR : AEStronglyMeasurable R mu) (hKmem : MemLp Kf e mu)
    (hKnorm : eLpNorm Kf e mu ≤ ENNReal.ofReal Cb)
    (hae : ∀ᵐ x ∂mu, 0 ≤ R x ∧ 0 ≤ Kf x ∧ R x ≤ Kf x * C) :
    MemLp R e mu ∧ eLpNorm R e mu ≤ ENNReal.ofReal (C * Cb) := by
  have hg : MemLp (fun x => C * Kf x) e mu := hKmem.const_mul C
  have hle : ∀ᵐ x ∂mu, ‖R x‖ ≤ ‖C * Kf x‖ := by
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx.1,
      abs_of_nonneg (mul_nonneg hC hx.2.1)]
    rw [mul_comm]; exact hx.2.2
  refine ⟨MemLp.of_le hg hR hle, ?_⟩
  refine (eLpNorm_mono_ae hR hle).trans ?_
  rw [show (fun x => C * Kf x) = C • Kf from rfl, eLpNorm_const_smul, ENNReal.ofReal_mul hC]
  refine mul_le_mul' ?_ hKnorm
  simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg hC]

variable [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

theorem aux_rem_bank_response_moments_measurable_dirichletResponse
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr)) :
    Measurable (fun omega : BilateralField d =>
      dirichletResponse S (cutoffPositiveCoefficient M H omega N z hr) b) := by
  have : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hcomp : (fun omega : BilateralField d =>
      dirichletResponse S (cutoffPositiveCoefficient M H omega N z hr) b) =
      (fun g : C(closedCube z r hr, ℝ) =>
        dirichletResponse S (expPotentialCoefficient (compactPotentialToLp _ g)) b) ∘
        (aux_rem_bank_response_moments_logPot M N z hr) ∘ (fun omega : BilateralField d => (H omega, omega)) := by
    funext omega
    simp only [Function.comp_apply]
    rw [aux_rem_bank_response_moments_cutoffPositiveCoefficient_eq M H omega N z hr]
  rw [hcomp]
  exact (((continuous_dirichletResponse_compact S (closedCube z r hr) b).comp
    (aux_rem_bank_response_moments_continuous_logPot M N z hr)).measurable).comp (hH.prodMk measurable_id)

theorem aux_rem_bank_response_moments_measurable_inverseResponse
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (L : S.space →L[ℝ] ℝ) :
    Measurable (fun omega : BilateralField d =>
      inverseResponse S (cutoffPositiveCoefficient M H omega N z hr) L) := by
  have : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hcomp : (fun omega : BilateralField d =>
      inverseResponse S (cutoffPositiveCoefficient M H omega N z hr) L) =
      (fun g : C(closedCube z r hr, ℝ) =>
        inverseResponse S (expPotentialCoefficient (compactPotentialToLp _ g)) L) ∘
        (aux_rem_bank_response_moments_logPot M N z hr) ∘ (fun omega : BilateralField d => (H omega, omega)) := by
    funext omega
    simp only [Function.comp_apply]
    rw [aux_rem_bank_response_moments_cutoffPositiveCoefficient_eq M H omega N z hr]
  rw [hcomp]
  exact (((continuous_inverseResponse_compact S (closedCube z r hr) L).comp
    (aux_rem_bank_response_moments_continuous_logPot M N z hr)).measurable).comp (hH.prodMk measurable_id)

end RBMeas_part

section RBSmall_part
open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity


/-- Envelope transfer at a lower exponent: `L^{p'}` control of the envelope gives `L^e`
membership and the same bound for every `e ≤ p'` on a probability space. -/
theorem aux_rem_bank_response_moments_envelope_lower {Ω : Type} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (R Kf : Ω → ℝ) (C Cb : ℝ) (hC : 0 ≤ C)
    (e p' : ℝ≥0∞) (hep : e ≤ p') (hR : AEStronglyMeasurable R mu)
    (hKmem : MemLp Kf p' mu) (hKnorm : eLpNorm Kf p' mu ≤ ENNReal.ofReal Cb)
    (hae : ∀ᵐ x ∂mu, 0 ≤ R x ∧ 0 ≤ Kf x ∧ R x ≤ Kf x * C) :
    MemLp R e mu ∧ eLpNorm R e mu ≤ ENNReal.ofReal (C * Cb) :=
  aux_rem_bank_response_moments_memLp_of_envelope mu R Kf C Cb hC e hR
    (hKmem.mono_exponent hep)
    ((eLpNorm_le_eLpNorm_of_exponent_le hep).trans hKnorm) hae

/-- **Generic assembly** of the four moment clauses and the single bound from two
envelopes controlled at one exponent `p'` dominating both target exponents. -/
theorem aux_rem_bank_response_moments_assemble {Ω : Type} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (RD RK KD KK : ℕ → Ω → ℝ) (cD cK BD BK : ℝ) (hcD : 0 ≤ cD) (hcK : 0 ≤ cK)
    (hBD : 0 ≤ BD) (hBK : 0 ≤ BK) (e1 e2 p' : ℝ≥0∞) (h1 : e1 ≤ p') (h2 : e2 ≤ p')
    (hmD : ∀ N, AEStronglyMeasurable (RD N) mu) (hmK : ∀ N, AEStronglyMeasurable (RK N) mu)
    (hKDmem : ∀ N, MemLp (KD N) p' mu) (hKKmem : ∀ N, MemLp (KK N) p' mu)
    (hKDn : ∀ N, eLpNorm (KD N) p' mu ≤ ENNReal.ofReal BD)
    (hKKn : ∀ N, eLpNorm (KK N) p' mu ≤ ENNReal.ofReal BK)
    (haeD : ∀ N, ∀ᵐ x ∂mu, 0 ≤ RD N x ∧ 0 ≤ KD N x ∧ RD N x ≤ KD N x * cD)
    (haeK : ∀ N, ∀ᵐ x ∂mu, 0 ≤ RK N x ∧ 0 ≤ KK N x ∧ RK N x ≤ KK N x * cK) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      MemLp (RD N) e1 mu ∧ MemLp (RK N) e1 mu ∧ MemLp (RD N) e2 mu ∧ MemLp (RK N) e2 mu ∧
      eLpNorm (RD N) e1 mu + eLpNorm (RK N) e1 mu + eLpNorm (RD N) e2 mu +
        eLpNorm (RK N) e2 mu ≤ ENNReal.ofReal B := by
  refine ⟨cD * BD + cK * BK + cD * BD + cK * BK, by positivity, fun N => ?_⟩
  obtain ⟨m1, b1⟩ := aux_rem_bank_response_moments_envelope_lower mu (RD N) (KD N) cD BD hcD
    e1 p' h1 (hmD N) (hKDmem N) (hKDn N) (haeD N)
  obtain ⟨m2, b2⟩ := aux_rem_bank_response_moments_envelope_lower mu (RK N) (KK N) cK BK hcK
    e1 p' h1 (hmK N) (hKKmem N) (hKKn N) (haeK N)
  obtain ⟨m3, b3⟩ := aux_rem_bank_response_moments_envelope_lower mu (RD N) (KD N) cD BD hcD
    e2 p' h2 (hmD N) (hKDmem N) (hKDn N) (haeD N)
  obtain ⟨m4, b4⟩ := aux_rem_bank_response_moments_envelope_lower mu (RK N) (KK N) cK BK hcK
    e2 p' h2 (hmK N) (hKKmem N) (hKKn N) (haeK N)
  refine ⟨m1, m2, m3, m4, ?_⟩
  calc eLpNorm (RD N) e1 mu + eLpNorm (RK N) e1 mu + eLpNorm (RD N) e2 mu +
        eLpNorm (RK N) e2 mu
      ≤ ENNReal.ofReal (cD * BD) + ENNReal.ofReal (cK * BK) +
        ENNReal.ofReal (cD * BD) + ENNReal.ofReal (cK * BK) := by gcongr
    _ = ENNReal.ofReal (cD * BD + cK * BK + cD * BD + cK * BK) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- **Pathwise Dirichlet envelope** on a working cube of side `r ≤ 1`, on the grid event of
`lem_extension`'s crude grid clause for the root `(z, 1)`. -/
theorem aux_rem_bank_response_moments_dirichlet_env (hd : 2 ≤ d) (E : in_J d)
    (X : in_extension d hd E) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (z : SpatialCoordinates d)
    (K : ℕ → BilateralField d → ℝ)
    (hae : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N k : ℕ) (index : Fin 1) (nidx : Fin d → ℤ), k ≤ N →
        (centeredCube (fun i => (fun _ : Fin 1 => z) index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z 1 one_pos) →
        E.Lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
            (fun i => (fun _ : Fin 1 => z) index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) ((5 / 8 - 1 / 2) / 4) 2 +
          (E.lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
            (fun i => (fun _ : Fin 1 => z) index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) ((5 / 8 - 1 / 2) / 4) 2)⁻¹ ≤
          K N om * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-(1 / 8 : ℝ)))
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 2 phi)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      0 ≤ dirichletResponse (killedResponseSpace hP)
          (cutoffPositiveCoefficient M H om N z hr) b ∧
      0 ≤ |K N om| ∧
      dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr) b ≤
        |K N om| * (aux_rem_bank_response_moments_Cstar d X.C *
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ^ 2) := by
  filter_upwards [hae] with om hom
  intro N
  have h := aux_rem_bank_response_moments_boundary_response hd E X M H om N z (K N om)
    (fun k nidx hkN hsub => hom N k 0 nidx hkN hsub) r hr hr1 hP phi _ hphi le_rfl b hb
  have hC := aux_rem_bank_response_moments_Cstar_nonneg d X.C
  refine ⟨dirichletResponse_nonneg _ _ _, abs_nonneg _, h.trans ?_⟩
  have h2 : aux_rem_bank_response_moments_Cstar d X.C * K N om *
      c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ^ 2 =
      K N om * (aux_rem_bank_response_moments_Cstar d X.C *
        c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ^ 2) := by ring
  rw [h2]
  exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)

/-- **The bank on a working cube of side `r ≤ 1`**, per model, from the two moment
suppliers (grid clause `K` and `λ_{1/8,1}^{-1}`) at the single exponent `max (3p) q`. -/
theorem aux_rem_bank_response_moments_rooted (hd : 2 ≤ d) (E : in_J d)
    (P : in_poincare d hd E) (X : in_extension d hd E) (p q : ℝ)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (K : ℕ → BilateralField d → ℝ) (CK : ℝ)
    (hKmem : ∀ N, MemLp (K N) (ENNReal.ofReal (max (3 * p) q)) (chaosSampleLaw M).toMeasure)
    (hKn : ∀ N, eLpNorm (K N) (ENNReal.ofReal (max (3 * p) q)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal CK)
    (hae : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N k : ℕ) (index : Fin 1) (nidx : Fin d → ℤ), k ≤ N →
        (centeredCube (fun i => (fun _ : Fin 1 => z) index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z 1 one_pos) →
        E.Lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
            (fun i => (fun _ : Fin 1 => z) index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) ((5 / 8 - 1 / 2) / 4) 2 +
          (E.lam z 1 one_pos (cutoffPositiveCoefficient M H om N z one_pos)
            (fun i => (fun _ : Fin 1 => z) index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) ((5 / 8 - 1 / 2) / 4) 2)⁻¹ ≤
          K N om * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-(1 / 8 : ℝ)))
    (CL : ℝ)
    (hLmem : ∀ N, MemLp (fun om : BilateralField d =>
        (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8) 1)⁻¹)
      (ENNReal.ofReal (max (3 * p) q)) (chaosSampleLaw M).toMeasure)
    (hLn : ∀ N, eLpNorm (fun om : BilateralField d =>
        (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8) 1)⁻¹)
      (ENNReal.ofReal (max (3 * p) q)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CL)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 2 phi)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (fL2 : DomainL2 (centeredCube z r hr)) :
    ∃ Bresp : ℝ, 0 ≤ Bresp ∧
      ∀ N : ℕ,
        MemLp
          (fun omega : BilateralField d =>
            dirichletResponse (killedResponseSpace hP)
              (cutoffPositiveCoefficient M H omega N z hr) b)
          (ENNReal.ofReal (3 * p)) (chaosSampleLaw M).toMeasure ∧
        MemLp
          (fun omega : BilateralField d =>
            inverseResponse (killedResponseSpace hP)
              (cutoffPositiveCoefficient M H omega N z hr)
              ((sobolevVolumeLoad fL2).comp
                (killedResponseSpace hP).space.subtypeL))
          (ENNReal.ofReal (3 * p)) (chaosSampleLaw M).toMeasure ∧
        MemLp
          (fun omega : BilateralField d =>
            dirichletResponse (killedResponseSpace hP)
              (cutoffPositiveCoefficient M H omega N z hr) b)
          (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
        MemLp
          (fun omega : BilateralField d =>
            inverseResponse (killedResponseSpace hP)
              (cutoffPositiveCoefficient M H omega N z hr)
              ((sobolevVolumeLoad fL2).comp
                (killedResponseSpace hP).space.subtypeL))
          (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
        eLpNorm
            (fun omega : BilateralField d =>
              dirichletResponse (killedResponseSpace hP)
                (cutoffPositiveCoefficient M H omega N z hr) b)
            (ENNReal.ofReal (3 * p)) (chaosSampleLaw M).toMeasure +
          eLpNorm
            (fun omega : BilateralField d =>
              inverseResponse (killedResponseSpace hP)
                (cutoffPositiveCoefficient M H omega N z hr)
                ((sobolevVolumeLoad fL2).comp
                  (killedResponseSpace hP).space.subtypeL))
            (ENNReal.ofReal (3 * p)) (chaosSampleLaw M).toMeasure +
          eLpNorm
            (fun omega : BilateralField d =>
              dirichletResponse (killedResponseSpace hP)
                (cutoffPositiveCoefficient M H omega N z hr) b)
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure +
          eLpNorm
            (fun omega : BilateralField d =>
              inverseResponse (killedResponseSpace hP)
                (cutoffPositiveCoefficient M H omega N z hr)
                ((sobolevVolumeLoad fL2).comp
                  (killedResponseSpace hP).space.subtypeL))
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Bresp := by
  have henvD := aux_rem_bank_response_moments_dirichlet_env hd E X M H z K hae r hr hr1 hP
    phi hphi b hb
  have hCs := aux_rem_bank_response_moments_Cstar_nonneg d X.C
  have h3 : ENNReal.ofReal (3 * p) ≤ ENNReal.ofReal (max (3 * p) q) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have h4 : ENNReal.ofReal q ≤ ENNReal.ofReal (max (3 * p) q) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  exact aux_rem_bank_response_moments_assemble (chaosSampleLaw M).toMeasure
    (fun N om => dirichletResponse (killedResponseSpace hP)
      (cutoffPositiveCoefficient M H om N z hr) b)
    (fun N om => inverseResponse (killedResponseSpace hP)
      (cutoffPositiveCoefficient M H om N z hr)
      ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL))
    (fun N om => |K N om|)
    (fun N om => (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8) 1)⁻¹)
    (aux_rem_bank_response_moments_Cstar d X.C *
      c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ^ 2)
    ((‖fL2‖ * (P.C * r)) ^ 2) (max CK 0) (max CL 0) (by positivity) (by positivity)
    (le_max_right _ _) (le_max_right _ _)
    (ENNReal.ofReal (3 * p)) (ENNReal.ofReal q) (ENNReal.ofReal (max (3 * p) q)) h3 h4
    (fun N => (aux_rem_bank_response_moments_measurable_dirichletResponse M H hH N z hr
      (killedResponseSpace hP) b).aestronglyMeasurable)
    (fun N => (aux_rem_bank_response_moments_measurable_inverseResponse M H hH N z hr
      (killedResponseSpace hP) _).aestronglyMeasurable)
    (fun N => (hKmem N).norm)
    hLmem
    (fun N => by
      change eLpNorm (fun om => ‖K N om‖) (ENNReal.ofReal (max (3 * p) q))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (max CK 0)
      rw [eLpNorm_norm _ (hKmem N).aestronglyMeasurable]
      exact (hKn N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    (fun N => (hLn N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    (fun N => by
      filter_upwards [henvD] with om hom
      exact hom N)
    (fun N => by
      filter_upwards with om
      refine ⟨inverseResponse_nonneg _ _ _,
        (inv_pos.2 (E.lam_pos _ _ _ _ _ _ _ _)).le, ?_⟩
      have h1 := aux_rem_bank_response_moments_inverse_le hd E P z r hr hP
        (cutoffPositiveCoefficient M H om N z hr) fL2
      have h2 := aux_rem_bank_response_moments_lam_inv_mono E z r hr
        (cutoffPositiveCoefficient M H om N z hr) (1 / 8) (by norm_num)
      calc _ ≤ _ := h1
        _ ≤ (‖fL2‖ * (P.C * r)) ^ 2 *
            (E.lam z r hr (cutoffPositiveCoefficient M H om N z hr) z r (1 / 8) 1)⁻¹ :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        _ = _ := mul_comm _ _)

end RBSmall_part

section RBTile_part
open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity


/-- Centre of the tile `m` of the uniform `n`-subdivision of the cube `z + r Q₀`. -/
def aux_rem_bank_response_moments_tileCenter {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (n : ℕ) (m : Fin d → Fin n) : SpatialCoordinates d :=
  fun i => z i - r / 2 + r / n * ((m i : ℝ) + 1 / 2)

/-- Coordinate description of a tile. -/
theorem aux_rem_bank_response_moments_mem_tile_iff {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (n : ℕ) (hℓ : 0 < r / n) (m : Fin d → Fin n) (x : SpatialCoordinates d) :
    x ∈ (centeredCube (aux_rem_bank_response_moments_tileCenter z r n m) (r / n) hℓ :
        Set (SpatialCoordinates d)) ↔
      ∀ i, z i - r / 2 + r / n * (m i : ℝ) < x i ∧ x i < z i - r / 2 + r / n * ((m i : ℝ) + 1) := by
  rw [centeredCube_eq_pi, Set.mem_univ_pi]
  simp only [Set.mem_Ioo, aux_rem_bank_response_moments_tileCenter]
  constructor
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    constructor <;> nlinarith
  · intro h i
    obtain ⟨h1, h2⟩ := h i
    constructor <;> nlinarith

theorem aux_rem_bank_response_moments_tile_le {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (n : ℕ) (hn : 0 < n) (hℓ : 0 < r / n) (m : Fin d → Fin n) :
    centeredCube (aux_rem_bank_response_moments_tileCenter z r n m) (r / n) hℓ ≤
      centeredCube z r hr := by
  intro x hx
  have hx' := (aux_rem_bank_response_moments_mem_tile_iff z r n hℓ m x).1 hx
  show x ∈ (centeredCube z r hr : Set (SpatialCoordinates d))
  rw [centeredCube_eq_pi, Set.mem_univ_pi]
  intro i
  obtain ⟨h1, h2⟩ := hx' i
  have hm0 : (0 : ℝ) ≤ (m i : ℝ) := Nat.cast_nonneg _
  have hm1 : (m i : ℝ) + 1 ≤ n := by exact_mod_cast (m i).isLt
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hrn : r / n * ((m i : ℝ) + 1) ≤ r := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hnpos]
    exact mul_le_mul_of_nonneg_left hm1 hr.le
  have hrn0 : 0 ≤ r / n * (m i : ℝ) := mul_nonneg hℓ.le hm0
  constructor <;> linarith

theorem aux_rem_bank_response_moments_tile_disjoint {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (n : ℕ) (hℓ : 0 < r / n) (m m' : Fin d → Fin n) (hmm : m ≠ m') :
    Disjoint (centeredCube (aux_rem_bank_response_moments_tileCenter z r n m) (r / n) hℓ :
        Set (SpatialCoordinates d))
      (centeredCube (aux_rem_bank_response_moments_tileCenter z r n m') (r / n) hℓ :
        Set (SpatialCoordinates d)) := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ m' i := by
    by_contra h
    push Not at h
    exact hmm (funext h)
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨a1, a2⟩ := (aux_rem_bank_response_moments_mem_tile_iff z r n hℓ m x).1 hx i
  obtain ⟨b1, b2⟩ := (aux_rem_bank_response_moments_mem_tile_iff z r n hℓ m' x).1 hx' i
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hi) with h | h
  · have h' : ((m i : ℕ) : ℝ) + 1 ≤ ((m' i : ℕ) : ℝ) := by exact_mod_cast h
    have := mul_le_mul_of_nonneg_left h' hℓ.le
    linarith
  · have h' : ((m' i : ℕ) : ℝ) + 1 ≤ ((m i : ℕ) : ℝ) := by exact_mod_cast h
    have := mul_le_mul_of_nonneg_left h' hℓ.le
    linarith

/-- The tile faces form a Lebesgue-null set. -/
theorem aux_rem_bank_response_moments_tile_faces_null {d : ℕ} (z : SpatialCoordinates d)
    (r ℓ : ℝ) :
    volume {x : SpatialCoordinates d | ∃ (i : Fin d) (j : ℕ), x i = z i - r / 2 + ℓ * j} = 0 := by
  have hset : {x : SpatialCoordinates d | ∃ (i : Fin d) (j : ℕ), x i = z i - r / 2 + ℓ * j} =
      ⋃ i : Fin d, ⋃ j : ℕ, {x : SpatialCoordinates d | x i = z i - r / 2 + ℓ * j} := by
    ext x
    simp
  rw [hset]
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => ?_
  rw [volume_pi]
  exact Measure.pi_hyperplane _ i _

/-- The tiles cover the cube up to a null set. -/
theorem aux_rem_bank_response_moments_tile_uncovered_null {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (n : ℕ) (hn : 0 < n) (hℓ : 0 < r / n) :
    volume ((centeredCube z r hr : Set (SpatialCoordinates d)) \
      ⋃ m : Fin d → Fin n,
        (centeredCube (aux_rem_bank_response_moments_tileCenter z r n m) (r / n) hℓ :
          Set (SpatialCoordinates d))) = 0 := by
  refine measure_mono_null ?_ (aux_rem_bank_response_moments_tile_faces_null z r (r / n))
  intro x ⟨hx, hxn⟩
  by_contra hface
  apply hxn
  simp only [mem_ofPred_eq, not_exists] at hface
  rw [centeredCube_eq_pi, Set.mem_univ_pi] at hx
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hcoord : ∀ i : Fin d, ∃ k : Fin n,
      z i - r / 2 + r / n * (k : ℝ) < x i ∧ x i < z i - r / 2 + r / n * ((k : ℝ) + 1) := by
    intro i
    obtain ⟨h1, h2⟩ := hx i
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (x i - (z i - r / 2)) / (r / n) := ⟨_, rfl⟩
    have ht0 : 0 < t := by rw [ht]; exact div_pos (by linarith) hℓ
    have htn : t < n := by
      rw [ht, div_lt_iff₀ hℓ]
      have : (n : ℝ) * (r / n) = r := by field_simp
      rw [this]; linarith
    have hxt : x i = z i - r / 2 + r / n * t := by
      rw [ht]; field_simp; ring
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌊t⌋₊ := ⟨_, rfl⟩
    have hk1 : (k : ℝ) ≤ t := by rw [hk]; exact Nat.floor_le ht0.le
    have hk2 : t < (k : ℝ) + 1 := by rw [hk]; exact Nat.lt_floor_add_one t
    have hkne : (k : ℝ) ≠ t := by
      intro h
      apply hface i k
      rw [hxt, ← h]
    have hkn : k < n := by
      have : (k : ℝ) < n := lt_of_le_of_lt hk1 htn
      exact_mod_cast this
    refine ⟨⟨k, hkn⟩, ?_, ?_⟩
    · rw [hxt]
      have : (k : ℝ) < t := lt_of_le_of_ne hk1 hkne
      have := mul_lt_mul_of_pos_left this hℓ
      linarith
    · rw [hxt]
      have := mul_lt_mul_of_pos_left hk2 hℓ
      linarith
  choose m hm using hcoord
  exact Set.mem_iUnion.2 ⟨m, (aux_rem_bank_response_moments_mem_tile_iff z r n hℓ m x).2 hm⟩

end RBTile_part

section RBLarge_part
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity


/-- The energy of a zero extension is the energy on the subdomain, for a coefficient that
agrees a.e. on the subdomain. -/
theorem aux_rem_bank_response_moments_zeroExt_form {d : ℕ}
    {V U : Opens (SpatialCoordinates d)} (hV : V ≤ U)
    (aV : PositiveCoefficient V) (aU : PositiveCoefficient U)
    (haa : ∀ᵐ x ∂volume.restrict (V : Set (SpatialCoordinates d)), aU.val x = aV.val x)
    (u : SobolevData V) :
    sobolevCoefficientForm aU (zeroExtensionSobolevData hV u) (zeroExtensionSobolevData hV u) =
      sobolevCoefficientForm aV u u := by
  rw [sobolevCoefficientForm_apply, sobolevCoefficientForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (∫ x in (U : Set (SpatialCoordinates d)),
      aU.val x * (zeroExtensionLp hV (u.2 i) x * zeroExtensionLp hV (u.2 i) x)) = _
  have h1 : (∫ x in (U : Set (SpatialCoordinates d)),
      aU.val x * (zeroExtensionLp hV (u.2 i) x * zeroExtensionLp hV (u.2 i) x)) =
      ∫ x in (U : Set (SpatialCoordinates d)),
        (aU.val x * zeroExtensionLp hV (u.2 i) x) * zeroExtensionLp hV (u.2 i) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [h1, integral_mul_zeroExtensionLp hV]
  refine integral_congr_ae ?_
  have hz := ae_restrict_of_ae_restrict_of_subset hV (zeroExtensionLp_coeFn hV (u.2 i))
  filter_upwards [hz, haa, ae_restrict_mem V.isOpen.measurableSet] with x hx hax hxV
  rw [hx, Set.indicator_of_mem hxV, hax]
  ring

/-- `‖f‖² = ∫ f²` on a domain `L²` space. -/
theorem aux_rem_bank_response_moments_norm_sq_eq {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (f : DomainL2 Ω) :
    ‖f‖ ^ 2 = ∫ x in (Ω : Set (SpatialCoordinates d)), f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

/-- `L²` scaling along the dilation of the unit cube onto a cube of side `R`. -/
theorem aux_rem_bank_response_moments_norm_sq_dilation {d : ℕ} (z : SpatialCoordinates d)
    (R : ℝ) (hR : 0 < R) (h1 : (0 : ℝ) < 1) (v : DomainL2 (centeredCube z R hR))
    (w : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (hw : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)), w x = v (cubeDilation z 0 R x)) :
    ‖v‖ ^ 2 = R ^ d * ‖w‖ ^ 2 := by
  rw [aux_rem_bank_response_moments_norm_sq_eq, aux_rem_bank_response_moments_norm_sq_eq,
    aux_coercivity_dilation_integral_scaling d z R hR h1 (fun y => v y ^ 2)
      ((Lp.aestronglyMeasurable v).pow 2)]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hw] with x hx
  rw [hx]

/-- The unit-cube trace-zero coarse Poincaré inequality, squared. -/
theorem aux_rem_bank_response_moments_unit_poincare_sq {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (P : in_poincare d hd E) (h1 : (0 : ℝ) < 1)
    (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1)) :
    ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1‖ ^ 2 ≤
      P.C ^ 2 * (E.lam 0 1 h1 b 0 1 1 1)⁻¹ *
        sobolevCoefficientForm b (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))
          (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) := by
  have hpo := P.poincare_killed_all_radii 0 1 h1 b w
  have hvol : volume.real (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)) = 1 := by
    rw [centeredCube_volume_real _ h1, one_pow]
  unfold normalizedEnergyNorm at hpo
  rw [localGradientEnergy_domain_eq_sobolevCoefficientForm, hvol, Real.sqrt_one, div_one,
    div_one, mul_one] at hpo
  have hlam := E.lam_pos 0 1 h1 b 0 1 1 1
  have hE0 := sobolevCoefficientForm_nonneg b
    (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))
  have hL0 : 0 ≤ (E.lam 0 1 h1 b 0 1 1 1) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hlam.le _
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hpo 2
  have hLsq : ((E.lam 0 1 h1 b 0 1 1 1) ^ (-(1 / 2) : ℝ)) ^ 2 = (E.lam 0 1 h1 b 0 1 1 1)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    norm_num
    exact Real.rpow_neg_one _
  calc _ ≤ (P.C * (E.lam 0 1 h1 b 0 1 1 1) ^ (-(1 / 2) : ℝ) *
        Real.sqrt (sobolevCoefficientForm b
          (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))
          (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)))) ^ 2 := hsq
    _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hE0, hLsq]

/-- Real arithmetic of the large-cube Poincaré transport. -/
theorem aux_rem_bank_response_moments_large_arith {U2 W2 Rd Rd2 R C Λ F Eb Ec Eu : ℝ}
    (hL2 : U2 = Rd * W2) (hpo : W2 ≤ C ^ 2 * Λ * Eb) (hcmp : Eb ≤ F * Ec)
    (hEu : Eu = Rd2 * Ec) (hRd : R ^ 2 * Rd2 = Rd) (hRd0 : 0 ≤ Rd) (hC : 0 ≤ C ^ 2)
    (hΛ : 0 ≤ Λ) :
    U2 ≤ (R * C) ^ 2 * (F * Λ) * Eu := by
  rw [hL2, hEu, ← hRd]
  have h1 : Rd * W2 ≤ Rd * (C ^ 2 * Λ * (F * Ec)) :=
    mul_le_mul_of_nonneg_left (hpo.trans (mul_le_mul_of_nonneg_left hcmp (mul_nonneg hC hΛ))) hRd0
  rw [← hRd] at h1
  calc R ^ 2 * Rd2 * W2 ≤ R ^ 2 * Rd2 * (C ^ 2 * Λ * (F * Ec)) := h1
    _ = (R * C) ^ 2 * (F * Λ) * (Rd2 * Ec) := by ring

/-- **Killed inverse response on a large working cube** via zero extension into a cube
`Q'` of side `R` and the upward comparison with a unit-cube coefficient `b ≤ F a'∘T`. -/
theorem aux_rem_bank_response_moments_inverse_le_large {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (P : in_poincare d hd E) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (R : ℝ) (hR : 0 < R) (hsub : centeredCube z r hr ≤ centeredCube z R hR)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (a' : PositiveCoefficient (centeredCube z R hR))
    (haa : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      a'.val x = a.val x)
    (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (F : ℝ) (hF : 0 ≤ F)
    (hb : ∀ᵐ y ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Set (SpatialCoordinates d)), b.val y ≤ F * a'.val (cubeDilation z 0 R y))
    (fL2 : DomainL2 (centeredCube z r hr)) :
    inverseResponse (killedResponseSpace hP) a
        ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL) ≤
      ‖fL2‖ ^ 2 * (R * P.C) ^ 2 * (F * (E.lam 0 1 one_pos b 0 1 1 1)⁻¹) := by
  obtain ⟨u, hu⟩ : ∃ u : killedSobolevGraph (centeredCube z r hr),
      u = responseSolution (killedResponseSpace hP) a
        ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL) := ⟨_, rfl⟩
  have hEdef : inverseResponse (killedResponseSpace hP) a
        ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL) =
      sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
        (u : SobolevData (centeredCube z r hr)) := by
    rw [hu]; rfl
  have hLoad : inverseResponse (killedResponseSpace hP) a
        ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL) =
      inner ℝ fL2 (u : SobolevData (centeredCube z r hr)).1 := by
    rw [inverseResponse_eq_load, ← hu]; rfl
  obtain ⟨Eu, hEu⟩ : ∃ Eu : ℝ, Eu = sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
      (u : SobolevData (centeredCube z r hr)) := ⟨_, rfl⟩
  have hE0 : 0 ≤ Eu := by rw [hEu]; exact sobolevCoefficientForm_nonneg _ _
  -- zero extension
  have hmem : zeroExtensionSobolevData hsub (u : SobolevData (centeredCube z r hr)) ∈
      killedSobolevGraph (centeredCube z R hR) :=
    zeroExtensionSobolevData_mem_killed hsub u.property
  obtain ⟨w, hw1, hw2⟩ := aux_coercivity_dilation_killed_pullback d z R hR one_pos
    ⟨_, hmem⟩
  obtain ⟨c, hc⟩ := dilation_coefficient_transport d z 0 R hR one_pos a'
  have hen := aux_rem_bank_response_moments_zeroExt_form hsub a a' haa
    (u : SobolevData (centeredCube z r hr))
  have hscale := aux_coercivity_dilation_energy_scaling d z R hR one_pos a' c
    (zeroExtensionSobolevData hsub (u : SobolevData (centeredCube z r hr)))
    (w : SobolevData _) hc hw1 hw2
  have hcmp : sobolevCoefficientForm b (w : SobolevData _) (w : SobolevData _) ≤
      F * sobolevCoefficientForm c (w : SobolevData _) (w : SobolevData _) := by
    apply weightedGradientForm_le_mul
    filter_upwards [hb, hc] with x hx hcx
    rw [hcx]
    exact hx
  have hpo := aux_rem_bank_response_moments_unit_poincare_sq hd E P one_pos b w
  have hL2 := aux_rem_bank_response_moments_norm_sq_dilation z R hR one_pos
    (zeroExtensionSobolevData hsub (u : SobolevData (centeredCube z r hr))).1
    (w : SobolevData _).1 hw1
  have hnorm : ‖(zeroExtensionSobolevData hsub (u : SobolevData (centeredCube z r hr))).1‖ =
      ‖(u : SobolevData (centeredCube z r hr)).1‖ := norm_zeroExtensionLp hsub _
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = (E.lam 0 1 one_pos b 0 1 1 1)⁻¹ := ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; exact (inv_pos.2 (E.lam_pos _ _ _ _ _ _ _ _)).le
  rw [← hΛ] at hpo
  -- `‖u‖² ≤ R² C² F Λ E(u)`
  have hRd : R ^ 2 * R ^ ((d : ℝ) - 2) = R ^ d := by
    rw [← Real.rpow_natCast R d, ← Real.rpow_natCast R 2, ← Real.rpow_add hR]
    congr 1
    push_cast
    ring
  have hu2 : ‖(u : SobolevData (centeredCube z r hr)).1‖ ^ 2 ≤
      (R * P.C) ^ 2 * (F * Λ) * Eu := by
    have hEc : Eu = R ^ ((d : ℝ) - 2) * sobolevCoefficientForm c (w : SobolevData _)
        (w : SobolevData _) := by rw [hEu, ← hen, hscale]
    rw [← hnorm]
    exact aux_rem_bank_response_moments_large_arith hL2 hpo hcmp hEc hRd (by positivity)
      (sq_nonneg _) hΛ0
  -- from the squared bound to the energy
  obtain ⟨A0, hA0⟩ : ∃ A0 : ℝ, A0 = Real.sqrt ((R * P.C) ^ 2 * (F * Λ)) := ⟨_, rfl⟩
  have hA00 : 0 ≤ A0 := by rw [hA0]; exact Real.sqrt_nonneg _
  have hnn : 0 ≤ (R * P.C) ^ 2 * (F * Λ) := mul_nonneg (sq_nonneg _) (mul_nonneg hF hΛ0)
  have hu_le : ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤ A0 * Real.sqrt Eu := by
    rw [hA0, ← Real.sqrt_mul hnn Eu]
    exact Real.le_sqrt_of_sq_le hu2
  have hEle : Eu ≤ (‖fL2‖ * A0) * Real.sqrt Eu := by
    have h1 : Eu = inner ℝ fL2 (u : SobolevData (centeredCube z r hr)).1 := by
      rw [hEu, ← hEdef, hLoad]
    refine h1.le.trans ((real_inner_le_norm _ _).trans ?_)
    calc ‖fL2‖ * ‖(u : SobolevData (centeredCube z r hr)).1‖
        ≤ ‖fL2‖ * (A0 * Real.sqrt Eu) := mul_le_mul_of_nonneg_left hu_le (norm_nonneg _)
      _ = (‖fL2‖ * A0) * Real.sqrt Eu := by ring
  have hfin := aux_rem_bank_response_moments_sq_of_le_mul_sqrt hE0
    (mul_nonneg (norm_nonneg _) hA00) hEle
  rw [hEdef, ← hEu]
  calc Eu ≤ (‖fL2‖ * A0) ^ 2 := hfin
    _ = ‖fL2‖ ^ 2 * A0 ^ 2 := by ring
    _ = ‖fL2‖ ^ 2 * ((R * P.C) ^ 2 * (F * Λ)) := by
        rw [hA0, Real.sq_sqrt hnn]
    _ = _ := by rw [hΛ]; ring

end RBLarge_part

section RBLC_part
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff





section
open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

/-- The chart from the unit cube to a cube of side `3^k`. -/
def aux_rem_bank_response_moments_lc_upMap {d : ℕ} (k : ℕ) (z : SpatialCoordinates d) :
    C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨fun y => z + (3 : ℝ) ^ k • y,
    by fun_prop⟩

theorem aux_rem_bank_response_moments_lc_upMap_apply {d : ℕ} (k : ℕ)
    (z y : SpatialCoordinates d) :
    aux_rem_bank_response_moments_lc_upMap k z y = z + (3 : ℝ) ^ k • y := rfl

/-- Upward scale shift: read layer `j+k` in the large-cube chart. -/
def aux_rem_bank_response_moments_lc_upShift {d : ℕ} (k : ℕ) (z : SpatialCoordinates d)
    (omega : BilateralField d) : BilateralField d :=
  fun j => (omega (j + k)).comp (aux_rem_bank_response_moments_lc_upMap k z)

theorem aux_rem_bank_response_moments_lc_upShift_apply {d : ℕ} (k : ℕ)
    (z y : SpatialCoordinates d) (omega : BilateralField d) (j : ℤ) :
    aux_rem_bank_response_moments_lc_upShift k z omega j y = omega (j + k) (z + (3 : ℝ) ^ k • y) := rfl

theorem aux_rem_bank_response_moments_lc_upShift_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (k : ℕ) (z : SpatialCoordinates d) :
    Measurable (aux_rem_bank_response_moments_lc_upShift (d := d) k z) := by
  have hc : Measurable fun f : C(SpatialCoordinates d, ℝ) =>
      f.comp (aux_rem_bank_response_moments_lc_upMap k z) := by fun_prop
  exact Measurable.of_eval fun j => hc.comp (measurable_pi_apply (j + k))

theorem aux_rem_bank_response_moments_lc_upShift_downShift {d : ℕ} (k : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d) :
    aux_rem_bank_response_moments_lc_upShift k z
      (aux_lem_as_coarse_shallow_grid_scaleShift k (-((3 : ℝ) ^ (-(k : ℤ))) • z)
        omega) = omega := by
  funext j
  ext y
  simp only [aux_rem_bank_response_moments_lc_upShift, aux_lem_as_coarse_shallow_grid_scaleShift,
    ContinuousMap.comp_apply, add_sub_cancel_right]
  congr 1
  ext i
  simp only [aux_lem_as_coarse_shallow_grid_cellMap, ContinuousMap.coe_mk,
    cubeDilation_apply, aux_rem_bank_response_moments_lc_upMap, Pi.add_apply, Pi.smul_apply,
    Pi.zero_apply, sub_zero, smul_eq_mul, _root_.zpow_neg, zpow_natCast]
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero k (by norm_num : (3 : ℝ) ≠ 0))]
  ring

/-- The upward shift preserves the same field law, by inversion of the downward shift. -/
theorem aux_rem_bank_response_moments_lc_upShift_measurePreserving {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (z : SpatialCoordinates d) :
    MeasurePreserving (aux_rem_bank_response_moments_lc_upShift k z)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
  let down := aux_lem_as_coarse_shallow_grid_scaleShift k
    (-((3 : ℝ) ^ (-(k : ℤ))) • z)
  have hd : MeasurePreserving down (chaosSampleLaw M).toMeasure
      (chaosSampleLaw M).toMeasure :=
    lem_as_coarse_shallow_grid_scale_shift M k _
  have hcomp : aux_rem_bank_response_moments_lc_upShift k z ∘ down = id := by
    funext omega
    exact aux_rem_bank_response_moments_lc_upShift_downShift k z omega
  refine ⟨aux_rem_bank_response_moments_lc_upShift_measurable k z, ?_⟩
  calc
    Measure.map (aux_rem_bank_response_moments_lc_upShift k z) (chaosSampleLaw M).toMeasure =
        Measure.map (aux_rem_bank_response_moments_lc_upShift k z)
          (Measure.map down (chaosSampleLaw M).toMeasure) := by rw [hd.map_eq]
    _ = Measure.map (aux_rem_bank_response_moments_lc_upShift k z ∘ down) (chaosSampleLaw M).toMeasure :=
      Measure.map_map (aux_rem_bank_response_moments_lc_upShift_measurable k z) hd.measurable
    _ = (chaosSampleLaw M).toMeasure := by rw [hcomp, Measure.map_id]

/-- Transfer an arbitrary event through the upward shift, without a measurability premise. -/
theorem aux_rem_bank_response_moments_lc_upShift_prob_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ) (z : SpatialCoordinates d)
    (S : Set (BilateralField d)) :
    (chaosSampleLaw M).toMeasure (aux_rem_bank_response_moments_lc_upShift k z ⁻¹' S) ≤
      (chaosSampleLaw M).toMeasure S := by
  set P := (chaosSampleLaw M).toMeasure
  calc
    P (aux_rem_bank_response_moments_lc_upShift k z ⁻¹' S) ≤
        P (aux_rem_bank_response_moments_lc_upShift k z ⁻¹' toMeasurable P S) :=
      measure_mono (Set.preimage_mono (subset_toMeasurable P S))
    _ = P (toMeasurable P S) :=
      (aux_rem_bank_response_moments_lc_upShift_measurePreserving M k z).measure_preimage
        (measurableSet_toMeasurable P S).nullMeasurableSet
    _ = P S := measure_toMeasurable S

theorem aux_rem_bank_response_moments_lc_upShift_fine_sum {d : ℕ} (N k : ℕ)
    (z y : SpatialCoordinates d) (omega : BilateralField d) :
    (∑ j ∈ Finset.range (N + k + 1), aux_rem_bank_response_moments_lc_upShift k z omega (-(j : ℤ)) y) =
      (∑ a ∈ Finset.range k, omega ((a : ℤ) + 1) (aux_rem_bank_response_moments_lc_upMap k z y)) +
        ∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) (aux_rem_bank_response_moments_lc_upMap k z y) := by
  simp only [aux_rem_bank_response_moments_lc_upShift, ContinuousMap.comp_apply]
  rw [show N + k + 1 = k + (N + 1) by omega, Finset.sum_range_add]
  congr 1
  · calc
      (∑ j ∈ Finset.range k, omega (-(j : ℤ) + k) (aux_rem_bank_response_moments_lc_upMap k z y)) =
          ∑ j ∈ Finset.range k,
            omega (((k - 1 - j : ℕ) : ℤ) + 1) (aux_rem_bank_response_moments_lc_upMap k z y) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjk := Finset.mem_range.mp hj
        congr 2
        omega
      _ = _ := Finset.sum_range_reflect
        (fun a => omega ((a : ℤ) + 1) (aux_rem_bank_response_moments_lc_upMap k z y)) k
  · apply Finset.sum_congr rfl
    intro j hj
    congr 2
    push_cast
    ring

/-- Exact coefficient factorization into the old cutoff and the `k` new coarse layers. -/
theorem aux_rem_bank_response_moments_lc_upShift_cutoff_factor {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (N k : ℕ)
    (z y : SpatialCoordinates d) (omega : BilateralField d) :
    cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
        (aux_rem_bank_response_moments_lc_upShift k z omega) (N + k) y =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + k)) *
        Real.exp ((∑ a ∈ Finset.range k,
          omega ((a : ℤ) + 1) (aux_rem_bank_response_moments_lc_upMap k z y)) -
          (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
        cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
          omega N (aux_rem_bank_response_moments_lc_upMap k z y) := by
  have hsplit := aux_rem_bank_response_moments_lc_upShift_fine_sum N k z y omega
  have hposN : SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≠ 0 :=
    ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
  simp only [cutoffCoefficient, cutoffPotential, ContinuousMap.zero_apply, zero_add,
    Int.ofNat_eq_natCast, hsplit, Nat.cast_add]
  rw [show (∑ a ∈ Finset.range k, omega ((a : ℤ) + 1) (aux_rem_bank_response_moments_lc_upMap k z y)) +
      (∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) (aux_rem_bank_response_moments_lc_upMap k z y)) -
      ((N : ℝ) + k + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P =
      ((∑ a ∈ Finset.range k, omega ((a : ℤ) + 1) (aux_rem_bank_response_moments_lc_upMap k z y)) -
        (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) +
      ((∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ)) (aux_rem_bank_response_moments_lc_upMap k z y)) -
        ((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) by ring,
    Real.exp_add]
  field_simp

/-- The annealed ordering controls the change in the cutoff normalizer. -/
theorem aux_rem_bank_response_moments_lc_ahom_ratio_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M) (N k : ℕ) :
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M N / SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N + k) ≤
      Real.exp (2 * ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) := by
  by_cases hk : k = 0
  · simp only [hk, Nat.add_zero, Nat.cast_zero, zero_mul, mul_zero, Real.exp_zero]
    rw [div_self (ne_of_gt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N))]
  · have hNk : N < N + k := Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hk)
    have hord := (Rm.ahom_ordering N (N + k) hNk).2
    apply (div_le_iff₀ (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N + k))).2
    have he : 2 * _root_.SubdiffusiveProcess.Model.tauSq M.P *
        (((N + k : ℕ) : ℝ) - (N : ℝ)) =
        2 * ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) := by
      push_cast
      ring
    rw [he] at hord
    exact hord

theorem aux_rem_bank_response_moments_lc_exp_factor_le {r s b t : ℝ}
    (hr : r ≤ Real.exp (2 * t)) (hs : s ≤ b) :
    r * Real.exp (s - t) ≤ Real.exp (t + b) := by
  calc
    r * Real.exp (s - t) ≤ Real.exp (2 * t) * Real.exp (s - t) :=
      mul_le_mul_of_nonneg_right hr (Real.exp_nonneg _)
    _ = Real.exp (t + s) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (t + b) := Real.exp_le_exp.mpr (add_le_add le_rfl hs)

/-- A compact restriction norm bounds the extra coarse layers uniformly in the old cutoff. -/
theorem aux_rem_bank_response_moments_lc_upShift_cutoff_le {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M) (N k : ℕ)
    (z y : SpatialCoordinates d) (omega : BilateralField d)
    (K : Compacts (SpatialCoordinates d)) (hy : aux_rem_bank_response_moments_lc_upMap k z y ∈ K) :
    cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
        (aux_rem_bank_response_moments_lc_upShift k z omega) (N + k) y ≤
      Real.exp ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
        ∑ a ∈ Finset.range k, ‖(omega ((a : ℤ) + 1)).restrict
          (K : Set (SpatialCoordinates d))‖) *
        cutoffCoefficient M (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
          omega N (aux_rem_bank_response_moments_lc_upMap k z y) := by
  have hsum : (∑ a ∈ Finset.range k, omega ((a : ℤ) + 1) (aux_rem_bank_response_moments_lc_upMap k z y)) ≤
      ∑ a ∈ Finset.range k,
        ‖(omega ((a : ℤ) + 1)).restrict (K : Set (SpatialCoordinates d))‖ := by
    apply Finset.sum_le_sum
    intro a ha
    exact (le_abs_self _).trans (by
      simpa only [ContinuousMap.restrict_apply, Real.norm_eq_abs] using
        ((omega ((a : ℤ) + 1)).restrict (K : Set (SpatialCoordinates d))).norm_coe_le_norm
          ⟨aux_rem_bank_response_moments_lc_upMap k z y, hy⟩)
  rw [aux_rem_bank_response_moments_lc_upShift_cutoff_factor]
  apply mul_le_mul_of_nonneg_right
    (aux_rem_bank_response_moments_lc_exp_factor_le (aux_rem_bank_response_moments_lc_ahom_ratio_le M Rm N k) hsum)
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)))
    (Real.exp_nonneg _)

end

section
open MeasureTheory Set TopologicalSpace ProbabilityTheory
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

theorem aux_rem_bank_response_moments_lc_exp_memLp_two
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : Measurable X) (t : ℝ)
    (hI : Integrable (fun w => Real.exp ((2 * t) * X w)) μ) :
    MemLp (fun w => Real.exp (t * X w)) 2 μ := by
  apply (memLp_two_iff_integrable_sq (hX.const_mul t |>.exp.aestronglyMeasurable)).2
  convert hI using 1
  funext w
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

/-- Finite sums preserve all nonnegative exponential moments; no independence is needed. -/
theorem aux_rem_bank_response_moments_lc_exp_sum_integrable
    {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Finset ι) (X : ι → Ω → ℝ)
    (hXm : ∀ i ∈ S, Measurable (X i))
    (hXI : ∀ i ∈ S, ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * X i w)) μ) :
    ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * ∑ i ∈ S, X i w)) μ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro t _
      simpa only [Finset.sum_empty, mul_zero, Real.exp_zero] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ)
  | @insert i S hi ih =>
      intro t ht
      have him : Measurable (X i) := hXm i (Finset.mem_insert_self _ _)
      have hSm : Measurable (fun w => ∑ j ∈ S, X j w) :=
        Finset.measurable_sum _ fun j hj => hXm j (Finset.mem_insert_of_mem hj)
      have hII := hXI i (Finset.mem_insert_self _ _) (2 * t) (by positivity)
      have hSI := ih (fun j hj => hXm j (Finset.mem_insert_of_mem hj))
        (fun j hj => hXI j (Finset.mem_insert_of_mem hj)) (2 * t) (by positivity)
      have hprod := (aux_rem_bank_response_moments_lc_exp_memLp_two μ (X i) him t hII).integrable_mul
        (aux_rem_bank_response_moments_lc_exp_memLp_two μ (fun w => ∑ j ∈ S, X j w) hSm t hSI)
      convert hprod using 1
      funext w
      rw [Finset.sum_insert hi, mul_add, Real.exp_add]
      rfl

/-- A fixed compact restriction of a native root field has all exponential norm moments.
This uses a finite cover by translates of the standing `g2` observable. -/
theorem aux_rem_bank_response_moments_lc_root_exp_norm_integrable
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (K : Compacts (SpatialCoordinates d))
    (D : C(SpatialCoordinates d, SpatialCoordinates d)) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
      Real.exp (t * ‖(g.1.1.comp D).restrict (K : Set (SpatialCoordinates d))‖))
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
  classical
  obtain ⟨S, hS⟩ := (K.isCompact.image D.continuous).elim_finite_subcover
    (fun z : SpatialCoordinates d => Metric.ball z (1 / 2 : ℝ))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.2 ⟨x, Metric.mem_ball_self (by norm_num)⟩)
  let X : SpatialCoordinates d → _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ :=
    fun z g => _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)
  have hXm : ∀ z, Measurable (X z) := fun z =>
    _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable.comp
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z)
  have hX0 : ∀ z g, 0 ≤ X z g := fun z g =>
    _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg _
  have hXI : ∀ z, ∀ q : ℝ, 0 ≤ q → Integrable
      (fun g => Real.exp (q * X z g))
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
    intro z q hq
    have hT : MeasurePreserving (_root_.SubdiffusiveProcess.Model.PotentialField.translate z)
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
        (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure :=
      ⟨_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z, M.G1.stationary z⟩
    have hI := (aux_finite_cutoff_log_abs_majorant_exp_of_ogamma
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable
      _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_nonneg
      M.delta q M.shellPrefix.delta_pos hq M.G2.regularity_expectation).1
    exact hT.integrable_comp_of_integrable hI
  have hbound : ∀ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
      ‖(g.1.1.comp D).restrict (K : Set (SpatialCoordinates d))‖ ≤ ∑ z ∈ S, X z g := by
    intro g
    apply (ContinuousMap.norm_le _ (Finset.sum_nonneg fun z _ => hX0 z g)).2
    intro x
    obtain ⟨z, hzS, hzx⟩ : ∃ z, ∃ (_ : z ∈ S), D x ∈ Metric.ball z (1 / 2 : ℝ) := by
      simpa only [mem_iUnion] using hS (mem_image_of_mem D x.2)
    have hmem : (D x - z) ∈ Homogenization.openCubeSet (Homogenization.originCube d 0) := by
      rw [← Homogenization.ball_cubeCenter_eq_openCubeSet]
      have hc : Homogenization.cubeCenter (Homogenization.originCube d 0) =
          (0 : SpatialCoordinates d) := by
        ext i
        simp [Homogenization.cubeCenter, Homogenization.originCube]
      have hr : Homogenization.cubeRadius (Homogenization.originCube d 0) = (1 / 2 : ℝ) := by
        unfold Homogenization.cubeRadius
        rw [Homogenization.cubeScaleFactor_eq_one_of_scale_eq_zero rfl, mul_one]
      rw [hc, hr]
      simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hzx
    have hx := _root_.SubdiffusiveProcess.Model.PotentialField.abs_apply_le_g2Observable
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) hmem
    simp only [_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply, sub_add_cancel] at hx
    change ‖g (D x)‖ ≤ _
    rw [Real.norm_eq_abs]
    exact hx.trans (Finset.single_le_sum (fun y _ => hX0 y g) hzS)
  have hI := aux_rem_bank_response_moments_lc_exp_sum_integrable
    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure S X
    (fun z _ => hXm z) (fun z _ => hXI z) t ht
  have hm : Measurable (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
      Real.exp (t * ‖(g.1.1.comp D).restrict (K : Set (SpatialCoordinates d))‖)) := by
    have hc : Continuous (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d => g.1.1.comp D) := by
      fun_prop
    exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_norm.comp ((ContinuousMap.continuous_restrict _).comp hc)))).measurable
  apply hI.mono' hm.aestronglyMeasurable
  filter_upwards with g
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hbound g) ht)

end

section
open MeasureTheory Set TopologicalSpace ProbabilityTheory
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

theorem aux_rem_bank_response_moments_lc_layer_norm_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (j : ℤ) (K : Compacts (SpatialCoordinates d)) :
    Measurable (fun omega : BilateralField d =>
      ‖(omega j).restrict (K : Set (SpatialCoordinates d))‖) :=
  (continuous_norm.comp (ContinuousMap.continuous_restrict
    (K : Set (SpatialCoordinates d)))).measurable.comp (measurable_pi_apply j)

/-- Every actual bilateral layer has all compact exponential norm moments. -/
theorem aux_rem_bank_response_moments_lc_layer_exp_norm_integrable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (j : ℤ)
    (K : Compacts (SpatialCoordinates d)) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun omega : BilateralField d =>
      Real.exp (t * ‖(omega j).restrict (K : Set (SpatialCoordinates d))‖))
      (chaosSampleLaw M).toMeasure := by
  let D : C(SpatialCoordinates d, SpatialCoordinates d) :=
    ⟨fun x => (3 : ℝ) ^ (-j) • x, by fun_prop⟩
  let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
      C(SpatialCoordinates d, ℝ)) :=
    ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
  let F : C(SpatialCoordinates d, ℝ) → ℝ := fun f =>
    Real.exp (t * ‖f.restrict (K : Set (SpatialCoordinates d))‖)
  have hF : Measurable F :=
    (Real.continuous_exp.comp (continuous_const.mul
      (continuous_norm.comp (ContinuousMap.continuous_restrict
        (K : Set (SpatialCoordinates d)))))).measurable
  have hroot : Integrable (fun f : C(SpatialCoordinates d, ℝ) => F (layerScaling d j f))
      (chaosRootFieldLaw M).toMeasure := by
    change Integrable (fun f : C(SpatialCoordinates d, ℝ) => F (layerScaling d j f))
      (Measure.map forget (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure)
    apply (integrable_map_measure
      (hF.comp (layerScaling d j).continuous.measurable).aestronglyMeasurable
      forget.continuous.measurable.aemeasurable).2
    exact aux_rem_bank_response_moments_lc_root_exp_norm_integrable M K D t ht
  have hlayer : Integrable F (scaledLayerLaw d (chaosRootFieldLaw M) j).toMeasure := by
    change Integrable F (Measure.map (layerScaling d j) (chaosRootFieldLaw M).toMeasure)
    exact (integrable_map_measure hF.aestronglyMeasurable
      (layerScaling d j).continuous.measurable.aemeasurable).2 hroot
  exact (measurePreserving_eval_infinitePi
    (fun i : ℤ => (scaledLayerLaw d (chaosRootFieldLaw M) i).toMeasure) j).integrable_comp_of_integrable
      hlayer

/-- The finitely many coarse layers added by an upward shift have every exponential
moment on a fixed compact set. -/
theorem aux_rem_bank_response_moments_lc_coarse_exp_norm_integrable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (k : ℕ)
    (K : Compacts (SpatialCoordinates d)) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun omega : BilateralField d =>
      Real.exp (t * ∑ a ∈ Finset.range k,
        ‖(omega ((a : ℤ) + 1)).restrict (K : Set (SpatialCoordinates d))‖))
      (chaosSampleLaw M).toMeasure := by
  exact aux_rem_bank_response_moments_lc_exp_sum_integrable (chaosSampleLaw M).toMeasure (Finset.range k)
    (fun a omega => ‖(omega ((a : ℤ) + 1)).restrict (K : Set (SpatialCoordinates d))‖)
    (fun a _ => aux_rem_bank_response_moments_lc_layer_norm_measurable ((a : ℤ) + 1) K)
    (fun a _ q hq => aux_rem_bank_response_moments_lc_layer_exp_norm_integrable M ((a : ℤ) + 1) K q hq) t ht

end

section
open MeasureTheory Set TopologicalSpace ProbabilityTheory
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

theorem aux_rem_bank_response_moments_lc_upMap_eq {d : ℕ} (k : ℕ) (z : SpatialCoordinates d) :
    (aux_rem_bank_response_moments_lc_upMap k z : SpatialCoordinates d → SpatialCoordinates d) =
      cubeDilation z 0 ((3 : ℝ) ^ k) := by
  funext y i
  simp only [aux_rem_bank_response_moments_lc_upMap, ContinuousMap.coe_mk, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, cubeDilation_apply, Pi.zero_apply, sub_zero]

theorem aux_rem_bank_response_moments_lc_cutoff_positive_coe
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    (fun x => (cutoffPositiveCoefficient M H omega N z hr).val x) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      cutoffCoefficient M H omega N := by
  have : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have hval := normalizedContinuousPositiveCoefficient_coeFn
    (Ω := centeredCube z r hr) (closedCube z r hr) (cutoffCoefficientCM M H omega N z hr)
    (cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
  filter_upwards [hval, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
    with x hx hxQ
  simpa only [cutoffPositiveCoefficient, cutoffCoefficientCM, ContinuousMap.coe_mk,
    div_one] using hx hxQ

theorem aux_rem_bank_response_moments_lc_cutoff_infrared_mul
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M H omega N x = Real.exp (H omega x) *
      cutoffCoefficient M (fun _ => 0) omega N x := by
  simp only [cutoffCoefficient, cutoffPotential, ContinuousMap.zero_apply, zero_add,
    Int.ofNat_eq_natCast]
  rw [show H omega x + (∑ j ∈ Finset.range (N + 1), omega (-↑j) x) -
      (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P =
    H omega x + ((∑ j ∈ Finset.range (N + 1), omega (-↑j) x) -
      (N + 1 : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P) by ring, Real.exp_add]
  ring

/-- The finite factor used to compare a large cube with its scale-shifted unit cube. -/
def aux_rem_bank_response_moments_lc_environment_factor
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ k)
    (omega : BilateralField d) : ℝ :=
  Real.exp ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P +
    (∑ a ∈ Finset.range k,
      ‖(omega ((a : ℤ) + 1)).restrict
        (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d))‖) +
    ‖(H (aux_rem_bank_response_moments_lc_upShift k z omega)).restrict
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))‖ +
    ‖(H omega).restrict
      (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d))‖)

theorem aux_rem_bank_response_moments_lc_environment_factor_pos
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ k)
    (omega : BilateralField d) :
    0 < aux_rem_bank_response_moments_lc_environment_factor M H k z hr omega := Real.exp_pos _

theorem aux_rem_bank_response_moments_lc_coefficients_le
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ k)
    (infrared : Bool) (N : ℕ) (omega : BilateralField d) :
    ∀ᵐ y ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H (aux_rem_bank_response_moments_lc_upShift k z omega) (N + k) 0 one_pos).val y ≤
        aux_rem_bank_response_moments_lc_environment_factor M H k z hr omega *
          (cutoffPositiveCoefficient M (if infrared then H else 0) omega N z hr).val
            (cubeDilation z 0 ((3 : ℝ) ^ k) y) := by
  have hq := dilation_quasi_measure_preserving d z 0 ((3 : ℝ) ^ k) hr one_pos
  filter_upwards [aux_rem_bank_response_moments_lc_cutoff_positive_coe M H
      (aux_rem_bank_response_moments_lc_upShift k z omega) (N + k) 0 one_pos,
    hq.ae (aux_rem_bank_response_moments_lc_cutoff_positive_coe M (if infrared then H else 0) omega N z hr),
    ae_restrict_mem (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet]
    with y hyunit hybig hy
  rw [hyunit, hybig]
  have hyeq := congrFun (aux_rem_bank_response_moments_lc_upMap_eq k z) y
  rw [← hyeq]
  have hyK := centeredCube_subset_closedCube (0 : SpatialCoordinates d) one_pos hy
  have hxK : aux_rem_bank_response_moments_lc_upMap k z y ∈
      (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d)) := by
    rw [hyeq]
    exact centeredCube_subset_closedCube z hr (cubeDilation_mapsTo z 0 hr one_pos y hy)
  have hcoarse := aux_rem_bank_response_moments_lc_upShift_cutoff_le M Rm N k z y omega
    (closedCube z ((3 : ℝ) ^ k) hr) hxK
  have hu : H (aux_rem_bank_response_moments_lc_upShift k z omega) y ≤
      ‖(H (aux_rem_bank_response_moments_lc_upShift k z omega)).restrict
        (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))‖ := by
    exact (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm
      ((H (aux_rem_bank_response_moments_lc_upShift k z omega)).restrict
        (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) ⟨y, hyK⟩)
  have hb : -((if infrared then H else 0) omega (aux_rem_bank_response_moments_lc_upMap k z y)) ≤
      ‖(H omega).restrict
        (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d))‖ := by
    cases infrared
    · simpa only [Bool.false_eq_true, ↓reduceIte, Pi.zero_apply,
        ContinuousMap.zero_apply, neg_zero] using
        norm_nonneg ((H omega).restrict
          (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d)))
    · exact (neg_le_abs _).trans (ContinuousMap.norm_coe_le_norm
        ((H omega).restrict (closedCube z ((3 : ℝ) ^ k) hr : Set (SpatialCoordinates d)))
          ⟨aux_rem_bank_response_moments_lc_upMap k z y, hxK⟩)
  have hremove : cutoffCoefficient M (fun _ => 0) omega N (aux_rem_bank_response_moments_lc_upMap k z y) =
      Real.exp (-((if infrared then H else 0) omega (aux_rem_bank_response_moments_lc_upMap k z y))) *
        cutoffCoefficient M (if infrared then H else 0) omega N (aux_rem_bank_response_moments_lc_upMap k z y) := by
    rw [aux_rem_bank_response_moments_lc_cutoff_infrared_mul M (if infrared then H else 0), ← mul_assoc,
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  rw [aux_rem_bank_response_moments_lc_cutoff_infrared_mul M H]
  refine (mul_le_mul_of_nonneg_left hcoarse (Real.exp_pos _).le).trans ?_
  rw [hremove]
  have hpos : 0 ≤ cutoffCoefficient M (if infrared then H else 0) omega N
      (aux_rem_bank_response_moments_lc_upMap k z y) :=
    (mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)).le
  rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ hpos
  apply Real.exp_le_exp.2
  linarith only [hu, hb]

end

section
open MeasureTheory Set TopologicalSpace ProbabilityTheory
open SubdiffusiveProcess
open scoped ENNReal NNReal BigOperators

theorem aux_rem_bank_response_moments_lc_exp_add_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X Y : Ω → ℝ) (hXm : Measurable X) (hYm : Measurable Y)
    (hXI : ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * X w)) μ)
    (hYI : ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * Y w)) μ)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun w => Real.exp (t * (X w + Y w))) μ := by
  have h2t : 0 ≤ 2 * t := mul_nonneg (by norm_num) ht
  have hprod := (aux_rem_bank_response_moments_lc_exp_memLp_two μ X hXm t (hXI (2 * t) h2t)).integrable_mul
    (aux_rem_bank_response_moments_lc_exp_memLp_two μ Y hYm t (hYI (2 * t) h2t))
  simp only [mul_add, Real.exp_add]
  exact hprod

/-- The comparison factor is measurable for the given measurable infrared version. -/
theorem aux_rem_bank_response_moments_lc_environment_factor_measurable
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ k) :
    Measurable (aux_rem_bank_response_moments_lc_environment_factor M H k z hr) := by
  unfold aux_rem_bank_response_moments_lc_environment_factor
  apply Measurable.exp
  refine ((measurable_const.add ?_).add ?_).add ?_
  · exact Finset.measurable_sum _ fun a _ =>
      aux_rem_bank_response_moments_lc_layer_norm_measurable ((a : ℤ) + 1) (closedCube z ((3 : ℝ) ^ k) hr)
  · exact (continuous_norm.comp (ContinuousMap.continuous_restrict _)).measurable.comp
      (HI.1.comp (aux_rem_bank_response_moments_lc_upShift_measurable k z))
  · exact (continuous_norm.comp (ContinuousMap.continuous_restrict _)).measurable.comp HI.1

/-- The large-cube comparison factor is integrable, with no small-disorder requirement. -/
theorem aux_rem_bank_response_moments_lc_environment_factor_integrable
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ k) :
    Integrable (aux_rem_bank_response_moments_lc_environment_factor M H k z hr)
      (chaosSampleLaw M).toMeasure := by
  let Kbig := closedCube z ((3 : ℝ) ^ k) hr
  let Kunit := closedCube (0 : SpatialCoordinates d) 1 one_pos
  let S : BilateralField d → ℝ := fun omega =>
    ∑ a ∈ Finset.range k, ‖(omega ((a : ℤ) + 1)).restrict
      (Kbig : Set (SpatialCoordinates d))‖
  let U : BilateralField d → ℝ := fun omega =>
    ‖(H (aux_rem_bank_response_moments_lc_upShift k z omega)).restrict
      (Kunit : Set (SpatialCoordinates d))‖
  let B : BilateralField d → ℝ := fun omega =>
    ‖(H omega).restrict (Kbig : Set (SpatialCoordinates d))‖
  have hSm : Measurable S := Finset.measurable_sum _ fun a _ =>
    aux_rem_bank_response_moments_lc_layer_norm_measurable ((a : ℤ) + 1) Kbig
  have hUm : Measurable U :=
    (continuous_norm.comp (ContinuousMap.continuous_restrict _)).measurable.comp
      (HI.1.comp (aux_rem_bank_response_moments_lc_upShift_measurable k z))
  have hBm : Measurable B :=
    (continuous_norm.comp (ContinuousMap.continuous_restrict _)).measurable.comp HI.1
  have hSI : ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * S w))
      (chaosSampleLaw M).toMeasure :=
    fun t ht => aux_rem_bank_response_moments_lc_coarse_exp_norm_integrable M k Kbig t ht
  have hUI : ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * U w))
      (chaosSampleLaw M).toMeasure := by
    intro t ht
    exact (aux_rem_bank_response_moments_lc_upShift_measurePreserving M k z).integrable_comp_of_integrable
      (exists_compactExponentialMoment_of_infraredCharacterization hd M H HI Kunit t ht)
  have hBI : ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * B w))
      (chaosSampleLaw M).toMeasure :=
    fun t ht => exists_compactExponentialMoment_of_infraredCharacterization hd M H HI Kbig t ht
  have hSU := aux_rem_bank_response_moments_lc_exp_add_integrable
    (chaosSampleLaw M).toMeasure S U hSm hUm hSI hUI
  have hSum := aux_rem_bank_response_moments_lc_exp_add_integrable (chaosSampleLaw M).toMeasure
    (fun w => S w + U w) B (hSm.add hUm) hBm hSU hBI 1 zero_le_one
  have hfactor := hSum.const_mul (Real.exp ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P))
  change Integrable (fun w => Real.exp
    ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P + S w + U w + B w))
      (chaosSampleLaw M).toMeasure
  simpa only [one_mul, add_assoc, Real.exp_add, mul_assoc] using hfactor

end

end RBLC_part

section RBBig_part
open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity


/-- **Tiling glue**: the Dirichlet response of a cube is at most the sum of the Dirichlet
responses of the restricted datum on the tiles of a uniform subdivision (the tile faces are
null). -/
theorem aux_rem_bank_response_moments_tile_glue {d : ℕ} (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (n : ℕ) (hn : 0 < n) (hℓ : 0 < r / n)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (b : weakSobolevGraph (centeredCube z r hr)) :
    dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr) b ≤
      ∑ m : Fin d → Fin n, dirichletResponse
        (killedResponseSpace (aux_aux_macro_moment_bank_killed_poincare hd
          (aux_rem_bank_response_moments_tileCenter z r n m) (r / n) hℓ))
        (cutoffPositiveCoefficient M H om N (aux_rem_bank_response_moments_tileCenter z r n m) hℓ)
        ⟨sobolevDataRestrict (aux_rem_bank_response_moments_tile_le z r hr n hn hℓ m)
            (b : SobolevData (centeredCube z r hr)),
          sobolevDataRestrict_mem_weak (aux_rem_bank_response_moments_tile_le z r hr n hn hℓ m)
            b.property⟩ := by
  classical
  have hg := aux_aux_macro_moment_bank_glue_le
    (fun m : Fin d → Fin n =>
      centeredCube (aux_rem_bank_response_moments_tileCenter z r n m) (r / n) hℓ)
    (aux_rem_bank_response_moments_tile_le z r hr n hn hℓ)
    (fun m m' hmm => aux_rem_bank_response_moments_tile_disjoint z r n hℓ m m' hmm)
    hP (fun m => aux_aux_macro_moment_bank_killed_poincare hd _ _ hℓ)
    (cutoffPositiveCoefficient M H om N z hr)
    (fun m => cutoffPositiveCoefficient M H om N (aux_rem_bank_response_moments_tileCenter z r n m) hℓ)
    (fun m => aux_aux_macro_moment_bank_cutoff_ae_eq M H om N _ _ hℓ z r hr
      (fun x hx => aux_rem_bank_response_moments_tile_le z r hr n hn hℓ m hx)) b
  refine hg.trans (le_of_eq ?_)
  have hnull := aux_rem_bank_response_moments_tile_uncovered_null z r hr n hn hℓ
  have h0 : ∀ i : Fin d, (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)) \
      ⋃ m : Fin d → Fin n,
        (centeredCube (aux_rem_bank_response_moments_tileCenter z r n m) (r / n) hℓ :
          Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H om N z hr).val x *
        ((b : SobolevData (centeredCube z r hr)).2 i x *
          (b : SobolevData (centeredCube z r hr)).2 i x)) = 0 := fun i =>
    setIntegral_measure_zero _ hnull
  rw [Finset.sum_congr rfl (fun i _ => h0 i), Finset.sum_const_zero, add_zero]

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- **Pathwise Dirichlet envelope on a large cube**: tile the cube into cells of side
`r/n ≤ 1` and apply the small-cube envelope on every tile, each with its own grid event. -/
theorem aux_rem_bank_response_moments_dirichlet_env_large (hd : 2 ≤ d) (E : in_J d)
    (X : in_extension d hd E) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (n : ℕ) (hn : 0 < n) (hℓ : 0 < r / n) (hℓ1 : r / n ≤ 1)
    (K : (Fin d → Fin n) → ℕ → BilateralField d → ℝ)
    (hae : ∀ m : Fin d → Fin n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
      ∀ (N k : ℕ) (index : Fin 1) (nidx : Fin d → ℤ), k ≤ N →
        (centeredCube (fun i => (fun _ : Fin 1 => aux_rem_bank_response_moments_tileCenter z r n m)
              index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤
          centeredCube (aux_rem_bank_response_moments_tileCenter z r n m) 1 one_pos) →
        E.Lam (aux_rem_bank_response_moments_tileCenter z r n m) 1 one_pos
            (cutoffPositiveCoefficient M H om N (aux_rem_bank_response_moments_tileCenter z r n m)
              one_pos)
            (fun i => (fun _ : Fin 1 => aux_rem_bank_response_moments_tileCenter z r n m) index i +
              (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) ((5 / 8 - 1 / 2) / 4) 2 +
          (E.lam (aux_rem_bank_response_moments_tileCenter z r n m) 1 one_pos
            (cutoffPositiveCoefficient M H om N (aux_rem_bank_response_moments_tileCenter z r n m)
              one_pos)
            (fun i => (fun _ : Fin 1 => aux_rem_bank_response_moments_tileCenter z r n m) index i +
              (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
            ((3 : ℝ) ^ (-(k : ℤ))) ((5 / 8 - 1 / 2) / 4) 2)⁻¹ ≤
          K m N om * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-(1 / 8 : ℝ)))
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 2 phi)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      0 ≤ dirichletResponse (killedResponseSpace hP)
          (cutoffPositiveCoefficient M H om N z hr) b ∧
      0 ≤ ∑ m : Fin d → Fin n, |K m N om| ∧
      dirichletResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr) b ≤
        (∑ m : Fin d → Fin n, |K m N om|) * (aux_rem_bank_response_moments_Cstar d X.C *
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ^ 2) := by
  classical
  have henv : ∀ m : Fin d → Fin n, ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      0 ≤ dirichletResponse (killedResponseSpace (aux_aux_macro_moment_bank_killed_poincare hd
          (aux_rem_bank_response_moments_tileCenter z r n m) (r / n) hℓ))
          (cutoffPositiveCoefficient M H om N (aux_rem_bank_response_moments_tileCenter z r n m) hℓ)
          ⟨sobolevDataRestrict (aux_rem_bank_response_moments_tile_le z r hr n hn hℓ m)
              (b : SobolevData (centeredCube z r hr)),
            sobolevDataRestrict_mem_weak (aux_rem_bank_response_moments_tile_le z r hr n hn hℓ m)
              b.property⟩ ∧
      0 ≤ |K m N om| ∧
      dirichletResponse (killedResponseSpace (aux_aux_macro_moment_bank_killed_poincare hd
          (aux_rem_bank_response_moments_tileCenter z r n m) (r / n) hℓ))
          (cutoffPositiveCoefficient M H om N (aux_rem_bank_response_moments_tileCenter z r n m) hℓ)
          ⟨sobolevDataRestrict (aux_rem_bank_response_moments_tile_le z r hr n hn hℓ m)
              (b : SobolevData (centeredCube z r hr)),
            sobolevDataRestrict_mem_weak (aux_rem_bank_response_moments_tile_le z r hr n hn hℓ m)
              b.property⟩ ≤
        |K m N om| * (aux_rem_bank_response_moments_Cstar d X.C *
          c2Norm (closedCube (aux_rem_bank_response_moments_tileCenter z r n m) (r / n) hℓ :
            Set (SpatialCoordinates d)) phi ^ 2) := fun m =>
    aux_rem_bank_response_moments_dirichlet_env hd E X M H
      (aux_rem_bank_response_moments_tileCenter z r n m) (K m) (hae m) (r / n) hℓ hℓ1
      (aux_aux_macro_moment_bank_killed_poincare hd _ _ hℓ) phi hphi _
      (aux_aux_macro_moment_bank_restrict_datum_ae
        (aux_rem_bank_response_moments_tile_le z r hr n hn hℓ m) b phi hb)
  have hc2 : ∀ m : Fin d → Fin n,
      c2Norm (closedCube (aux_rem_bank_response_moments_tileCenter z r n m) (r / n) hℓ :
          Set (SpatialCoordinates d)) phi ^ 2 ≤
        c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ^ 2 := by
    intro m
    have h0 := (aux_rem_bank_response_moments_c2_bounds
      (aux_rem_bank_response_moments_tileCenter z r n m) (r / n) hℓ phi hphi _ le_rfl).1
    have hsub : (centeredCube (aux_rem_bank_response_moments_tileCenter z r n m) (r / n) hℓ :
        Set (SpatialCoordinates d)) ⊆ centeredCube z r hr :=
      fun x hx => aux_rem_bank_response_moments_tile_le z r hr n hn hℓ m hx
    have hmono := aux_aux_macro_moment_bank_c2Norm_mono _ _ (closedCube z r hr).isCompact
      ⟨_, Metric.mem_closedBall_self (by positivity)⟩
      (aux_aux_macro_moment_bank_closedCube_subset _ _ hℓ z r hr hsub) phi hphi
    exact pow_le_pow_left₀ h0 hmono 2
  have hCs := aux_rem_bank_response_moments_Cstar_nonneg d X.C
  filter_upwards [ae_all_iff.2 henv] with om hom
  intro N
  refine ⟨dirichletResponse_nonneg _ _ _,
    Finset.sum_nonneg fun m _ => abs_nonneg _, ?_⟩
  refine (aux_rem_bank_response_moments_tile_glue hd M H om N z r hr n hn hℓ hP b).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun m _ => (hom m N).2.2.trans ?_
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hc2 m) hCs) (abs_nonneg _)

/-- A Hölder triple `(2s, 2s, s)`. -/
theorem aux_rem_bank_response_moments_holder (s : ℝ) :
    ENNReal.HolderTriple (ENNReal.ofReal (2 * s)) (ENNReal.ofReal (2 * s)) (ENNReal.ofReal s) := by
  refine ⟨?_⟩
  have h2 : ENNReal.ofReal (2 * s) = 2 * ENNReal.ofReal s := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [h2, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), ← add_mul,
    ENNReal.inv_two_add_inv_two, one_mul]

/-- All moments of the upward-shift environment factor. -/
theorem aux_rem_bank_response_moments_envFactor_memLp (hd : 2 ≤ d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (k : ℕ) (z : SpatialCoordinates d) (hr : 0 < (3 : ℝ) ^ k) (s : ℝ) (hs : 0 < s) :
    MemLp (aux_rem_bank_response_moments_lc_environment_factor M H k z hr)
      (ENNReal.ofReal s) (chaosSampleLaw M).toMeasure := by
  have hm := aux_rem_bank_response_moments_lc_environment_factor_measurable M H HI k z hr
  rw [← integrable_norm_rpow_iff hm.aestronglyMeasurable (by simpa using hs)
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hs.le]
  let Kbig := closedCube z ((3 : ℝ) ^ k) hr
  let Kunit := closedCube (0 : SpatialCoordinates d) 1 one_pos
  let S : BilateralField d → ℝ := fun omega =>
    ∑ a ∈ Finset.range k, ‖(omega ((a : ℤ) + 1)).restrict
      (Kbig : Set (SpatialCoordinates d))‖
  let U : BilateralField d → ℝ := fun omega =>
    ‖(H (aux_rem_bank_response_moments_lc_upShift k z omega)).restrict
      (Kunit : Set (SpatialCoordinates d))‖
  let B : BilateralField d → ℝ := fun omega =>
    ‖(H omega).restrict (Kbig : Set (SpatialCoordinates d))‖
  have hSm : Measurable S := Finset.measurable_sum _ fun a _ =>
    aux_rem_bank_response_moments_lc_layer_norm_measurable ((a : ℤ) + 1) Kbig
  have hUm : Measurable U :=
    (continuous_norm.comp (ContinuousMap.continuous_restrict _)).measurable.comp
      (HI.1.comp (aux_rem_bank_response_moments_lc_upShift_measurable k z))
  have hBm : Measurable B :=
    (continuous_norm.comp (ContinuousMap.continuous_restrict _)).measurable.comp HI.1
  have hSI : ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * S w))
      (chaosSampleLaw M).toMeasure :=
    fun t ht => aux_rem_bank_response_moments_lc_coarse_exp_norm_integrable M k Kbig t ht
  have hUI : ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * U w))
      (chaosSampleLaw M).toMeasure := by
    intro t ht
    exact (aux_rem_bank_response_moments_lc_upShift_measurePreserving M k z).integrable_comp_of_integrable
      (exists_compactExponentialMoment_of_infraredCharacterization hd M H HI Kunit t ht)
  have hBI : ∀ t : ℝ, 0 ≤ t → Integrable (fun w => Real.exp (t * B w))
      (chaosSampleLaw M).toMeasure :=
    fun t ht => exists_compactExponentialMoment_of_infraredCharacterization hd M H HI Kbig t ht
  have hSU := aux_rem_bank_response_moments_lc_exp_add_integrable
    (chaosSampleLaw M).toMeasure S U hSm hUm hSI hUI
  have hSum := aux_rem_bank_response_moments_lc_exp_add_integrable (chaosSampleLaw M).toMeasure
    (fun w => S w + U w) B (hSm.add hUm) hBm hSU hBI s hs.le
  have hfactor := hSum.const_mul
    (Real.exp (s * ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)))
  refine hfactor.congr (Filter.Eventually.of_forall fun w => ?_)
  change Real.exp (s * ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) *
      Real.exp (s * ((S w + U w) + B w)) =
    ‖Real.exp ((k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P + S w + U w + B w)‖ ^ s
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

end RBBig_part

section RBBigRooted_part
open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity


/-- Moments of a finite sum of absolute values. -/
theorem aux_rem_bank_response_moments_sum_abs_moments {Ω ι : Type} [MeasurableSpace Ω]
    (mu : Measure Ω) [Fintype ι] (K : ι → ℕ → Ω → ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (CK : ι → ℝ)
    (hKmem : ∀ i N, MemLp (K i N) p mu) (hKn : ∀ i N, eLpNorm (K i N) p mu ≤ ENNReal.ofReal (CK i)) :
    (∀ N, MemLp (fun om => ∑ i, |K i N om|) p mu) ∧
      (∀ N, eLpNorm (fun om => ∑ i, |K i N om|) p mu ≤
        ENNReal.ofReal (∑ i, max (CK i) 0)) := by
  refine ⟨fun N => memLp_finsetSum Finset.univ (fun i _ => (hKmem i N).norm), fun N => ?_⟩
  have hfun : (fun om => ∑ i, |K i N om|) = ∑ i, (fun om => ‖K i N om‖) := by
    funext om
    simp [Real.norm_eq_abs]
  rw [hfun]
  refine (eLpNorm_sum_le hp1).trans ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => le_max_right _ _)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [eLpNorm_norm _ (hKmem i N).aestronglyMeasurable]
  exact (hKn i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

/-- Hölder moments of a product `F · L_N` from `L^{2s}` control of both factors. -/
theorem aux_rem_bank_response_moments_prod_moments {Ω : Type} [MeasurableSpace Ω]
    (mu : Measure Ω) (F : Ω → ℝ) (L : ℕ → Ω → ℝ) (s : ℝ) (CF CL : ℝ)
    (hCF : 0 ≤ CF)
    (hF : MemLp F (ENNReal.ofReal (2 * s)) mu)
    (hFn : eLpNorm F (ENNReal.ofReal (2 * s)) mu ≤ ENNReal.ofReal CF)
    (hL : ∀ N, MemLp (L N) (ENNReal.ofReal (2 * s)) mu)
    (hLn : ∀ N, eLpNorm (L N) (ENNReal.ofReal (2 * s)) mu ≤ ENNReal.ofReal CL) :
    (∀ N, MemLp (fun om => F om * L N om) (ENNReal.ofReal s) mu) ∧
      (∀ N, eLpNorm (fun om => F om * L N om) (ENNReal.ofReal s) mu ≤
        ENNReal.ofReal (CF * CL)) := by
  have := aux_rem_bank_response_moments_holder s
  refine ⟨fun N => MemLp.fun_mul (p := ENNReal.ofReal (2 * s)) (q := ENNReal.ofReal (2 * s))
    (r := ENNReal.ofReal s) hF (hL N), fun N => ?_⟩
  have h := eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal (2 * s)) (q := ENNReal.ofReal (2 * s))
    (r := ENNReal.ofReal s) hF.aestronglyMeasurable (hL N).aestronglyMeasurable
  refine h.trans ?_
  rw [ENNReal.ofReal_mul hCF]
  exact mul_le_mul' hFn (hLn N)

variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- **Killed inverse response on a large working cube, pathwise envelope.** -/
theorem aux_rem_bank_response_moments_inverse_env_large (hd : 2 ≤ d) (E : in_J d)
    (P : in_poincare d hd E) (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (k : ℕ) (hrk : r ≤ (3 : ℝ) ^ k)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (fL2 : DomainL2 (centeredCube z r hr)) (N : ℕ) (om : BilateralField d) :
    0 ≤ inverseResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr)
        ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL) ∧
      0 ≤ aux_rem_bank_response_moments_lc_environment_factor M H k z (by positivity) om *
        (E.lam 0 1 one_pos (cutoffPositiveCoefficient M H
          (aux_rem_bank_response_moments_lc_upShift k z om) (N + k) 0 one_pos) 0 1 (1 / 8) 1)⁻¹ ∧
      inverseResponse (killedResponseSpace hP) (cutoffPositiveCoefficient M H om N z hr)
          ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL) ≤
        aux_rem_bank_response_moments_lc_environment_factor M H k z (by positivity) om *
          (E.lam 0 1 one_pos (cutoffPositiveCoefficient M H
            (aux_rem_bank_response_moments_lc_upShift k z om) (N + k) 0 one_pos) 0 1 (1 / 8) 1)⁻¹ *
          (‖fL2‖ ^ 2 * ((3 : ℝ) ^ k * P.C) ^ 2) := by
  have hR : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hsub : centeredCube z r hr ≤ centeredCube z ((3 : ℝ) ^ k) hR := by
    intro x hx
    exact Metric.ball_subset_ball (by linarith) hx
  have hF0 := (aux_rem_bank_response_moments_lc_environment_factor_pos M H k z hR om).le
  have hΛ8 := inv_pos.2 (E.lam_pos 0 1 one_pos (cutoffPositiveCoefficient M H
    (aux_rem_bank_response_moments_lc_upShift k z om) (N + k) 0 one_pos) 0 1 (1 / 8) 1)
  have hb := aux_rem_bank_response_moments_lc_coefficients_le M Rm H k z hR true N om
  have hle := aux_rem_bank_response_moments_inverse_le_large hd E P z r hr ((3 : ℝ) ^ k) hR hsub hP
    (cutoffPositiveCoefficient M H om N z hr) (cutoffPositiveCoefficient M H om N z hR)
    ((aux_aux_macro_moment_bank_cutoff_ae_eq M H om N z r hr z ((3 : ℝ) ^ k) hR
      (fun x hx => hsub hx)).mono fun x hx => hx.symm)
    (cutoffPositiveCoefficient M H (aux_rem_bank_response_moments_lc_upShift k z om) (N + k) 0
      one_pos)
    _ hF0 hb fL2
  have hmono := aux_rem_bank_response_moments_lam_inv_mono E 0 1 one_pos
    (cutoffPositiveCoefficient M H (aux_rem_bank_response_moments_lc_upShift k z om) (N + k) 0
      one_pos) (1 / 8) (by norm_num)
  refine ⟨inverseResponse_nonneg _ _ _, mul_nonneg hF0 hΛ8.le, hle.trans ?_⟩
  have h2 : aux_rem_bank_response_moments_lc_environment_factor M H k z hR om *
      (E.lam 0 1 one_pos (cutoffPositiveCoefficient M H
        (aux_rem_bank_response_moments_lc_upShift k z om) (N + k) 0 one_pos) 0 1 1 1)⁻¹ ≤
      aux_rem_bank_response_moments_lc_environment_factor M H k z hR om *
      (E.lam 0 1 one_pos (cutoffPositiveCoefficient M H
        (aux_rem_bank_response_moments_lc_upShift k z om) (N + k) 0 one_pos) 0 1 (1 / 8) 1)⁻¹ :=
    mul_le_mul_of_nonneg_left hmono hF0
  calc _ ≤ ‖fL2‖ ^ 2 * ((3 : ℝ) ^ k * P.C) ^ 2 *
        (aux_rem_bank_response_moments_lc_environment_factor M H k z hR om *
          (E.lam 0 1 one_pos (cutoffPositiveCoefficient M H
            (aux_rem_bank_response_moments_lc_upShift k z om) (N + k) 0 one_pos) 0 1 (1 / 8) 1)⁻¹) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

end RBBigRooted_part

section RBMain_part
open MeasureTheory
open scoped ENNReal NNReal ContDiff
open TopologicalSpace
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity


section
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
  [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- **The bank on a working cube of side `r > 1`**, per model: tiles of side `≤ 1` for the
Dirichlet response (each with its own grid event), and the upward scale shift for the killed
inverse response. -/
theorem aux_rem_bank_response_moments_rooted_large (hd : 2 ≤ d) (E : in_J d)
    (P : in_poincare d hd E) (X : in_extension d hd E) (p q : ℝ) (hp1 : 1 ≤ max (3 * p) q)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (Rm : in_responses d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (HI : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hGridAt : ∀ c : SpatialCoordinates d, ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : ℝ),
      (∀ N, MemLp (K N) (ENNReal.ofReal (max (3 * p) q)) (chaosSampleLaw M).toMeasure) ∧
      (∀ N, eLpNorm (K N) (ENNReal.ofReal (max (3 * p) q)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal Cbound) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N k : ℕ) (index : Fin 1) (nidx : Fin d → ℤ), k ≤ N →
          (centeredCube (fun i => (fun _ : Fin 1 => c) index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
              ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube c 1 one_pos) →
          E.Lam c 1 one_pos (cutoffPositiveCoefficient M H om N c one_pos)
              (fun i => (fun _ : Fin 1 => c) index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
              ((3 : ℝ) ^ (-(k : ℤ))) ((5 / 8 - 1 / 2) / 4) 2 +
            (E.lam c 1 one_pos (cutoffPositiveCoefficient M H om N c one_pos)
              (fun i => (fun _ : Fin 1 => c) index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
              ((3 : ℝ) ^ (-(k : ℤ))) ((5 / 8 - 1 / 2) / 4) 2)⁻¹ ≤
            K N om * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-(1 / 8 : ℝ)))
    (CL : ℝ)
    (hLmem : ∀ n : ℕ, MemLp (fun om : BilateralField d =>
        (E.lam 0 1 one_pos (cutoffPositiveCoefficient M H om n 0 one_pos) 0 1 (1 / 8) 1)⁻¹)
      (ENNReal.ofReal (2 * max (3 * p) q)) (chaosSampleLaw M).toMeasure)
    (hLn : ∀ n : ℕ, eLpNorm (fun om : BilateralField d =>
        (E.lam 0 1 one_pos (cutoffPositiveCoefficient M H om n 0 one_pos) 0 1 (1 / 8) 1)⁻¹)
      (ENNReal.ofReal (2 * max (3 * p) q)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CL)
    (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
      ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 2 phi)
    (b : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (fL2 : DomainL2 (centeredCube z r hr)) :
    ∃ Bresp : ℝ, 0 ≤ Bresp ∧
            ∀ N : ℕ,
              MemLp
                (fun omega : BilateralField d =>
                  dirichletResponse (killedResponseSpace hP)
                    (cutoffPositiveCoefficient M H omega N z hr) b)
                (ENNReal.ofReal (3 * p)) (chaosSampleLaw M).toMeasure ∧
              MemLp
                (fun omega : BilateralField d =>
                  inverseResponse (killedResponseSpace hP)
                    (cutoffPositiveCoefficient M H omega N z hr)
                    ((sobolevVolumeLoad fL2).comp
                      (killedResponseSpace hP).space.subtypeL))
                (ENNReal.ofReal (3 * p)) (chaosSampleLaw M).toMeasure ∧
              MemLp
                (fun omega : BilateralField d =>
                  dirichletResponse (killedResponseSpace hP)
                    (cutoffPositiveCoefficient M H omega N z hr) b)
                (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
              MemLp
                (fun omega : BilateralField d =>
                  inverseResponse (killedResponseSpace hP)
                    (cutoffPositiveCoefficient M H omega N z hr)
                    ((sobolevVolumeLoad fL2).comp
                      (killedResponseSpace hP).space.subtypeL))
                (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
              eLpNorm
                  (fun omega : BilateralField d =>
                    dirichletResponse (killedResponseSpace hP)
                      (cutoffPositiveCoefficient M H omega N z hr) b)
                  (ENNReal.ofReal (3 * p)) (chaosSampleLaw M).toMeasure +
                eLpNorm
                  (fun omega : BilateralField d =>
                    inverseResponse (killedResponseSpace hP)
                      (cutoffPositiveCoefficient M H omega N z hr)
                      ((sobolevVolumeLoad fL2).comp
                        (killedResponseSpace hP).space.subtypeL))
                  (ENNReal.ofReal (3 * p)) (chaosSampleLaw M).toMeasure +
                eLpNorm
                  (fun omega : BilateralField d =>
                    dirichletResponse (killedResponseSpace hP)
                      (cutoffPositiveCoefficient M H omega N z hr) b)
                  (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure +
                eLpNorm
                  (fun omega : BilateralField d =>
                    inverseResponse (killedResponseSpace hP)
                      (cutoffPositiveCoefficient M H omega N z hr)
                      ((sobolevVolumeLoad fL2).comp
                        (killedResponseSpace hP).space.subtypeL))
                  (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Bresp := by
  classical
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt r (by norm_num : (1 : ℝ) < 3)
  have hR : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈r⌉₊ := ⟨_, rfl⟩
  have hnpos : 0 < n := by rw [hn]; exact Nat.ceil_pos.2 hr
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hℓ : 0 < r / n := div_pos hr hnR
  have hℓ1 : r / n ≤ 1 := by
    rw [div_le_one hnR, hn]
    exact Nat.le_ceil r
  have hG := fun m : Fin d → Fin n => hGridAt (aux_rem_bank_response_moments_tileCenter z r n m)
  choose K CK hKmem hKn hKae using hG
  have henvD := aux_rem_bank_response_moments_dirichlet_env_large hd E X M H z r hr n hnpos hℓ hℓ1
    K hKae hP phi hphi b hb
  have hKD := aux_rem_bank_response_moments_sum_abs_moments (chaosSampleLaw M).toMeasure K
    (ENNReal.ofReal (max (3 * p) q)) (ENNReal.one_le_ofReal.2 hp1) CK hKmem hKn
  have hFmem := aux_rem_bank_response_moments_envFactor_memLp hd M H HI k z hR
    (2 * max (3 * p) q) (by positivity)
  obtain ⟨CF, hCF⟩ : ∃ CF : ℝ, CF = (eLpNorm (aux_rem_bank_response_moments_lc_environment_factor
      M H k z hR) (ENNReal.ofReal (2 * max (3 * p) q)) (chaosSampleLaw M).toMeasure).toReal :=
    ⟨_, rfl⟩
  have hFn : eLpNorm (aux_rem_bank_response_moments_lc_environment_factor M H k z hR)
      (ENNReal.ofReal (2 * max (3 * p) q)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CF := by
    rw [hCF, ENNReal.ofReal_toReal hFmem.eLpNorm_ne_top]
  have hmp := aux_rem_bank_response_moments_lc_upShift_measurePreserving M k z
  have hΛmem : ∀ N : ℕ, MemLp (fun om : BilateralField d =>
      (E.lam 0 1 one_pos (cutoffPositiveCoefficient M H
        (aux_rem_bank_response_moments_lc_upShift k z om) (N + k) 0 one_pos) 0 1 (1 / 8) 1)⁻¹)
      (ENNReal.ofReal (2 * max (3 * p) q)) (chaosSampleLaw M).toMeasure :=
    fun N => (hLmem (N + k)).comp_measurePreserving hmp
  have hΛn : ∀ N : ℕ, eLpNorm (fun om : BilateralField d =>
      (E.lam 0 1 one_pos (cutoffPositiveCoefficient M H
        (aux_rem_bank_response_moments_lc_upShift k z om) (N + k) 0 one_pos) 0 1 (1 / 8) 1)⁻¹)
      (ENNReal.ofReal (2 * max (3 * p) q)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (max CL 0) := by
    intro N
    have h := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal (2 * max (3 * p) q))
      (hLmem (N + k)).aestronglyMeasurable hmp
    refine le_of_eq_of_le h ?_
    exact (hLn (N + k)).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hKK := aux_rem_bank_response_moments_prod_moments (chaosSampleLaw M).toMeasure
    (aux_rem_bank_response_moments_lc_environment_factor M H k z hR)
    (fun N om => (E.lam 0 1 one_pos (cutoffPositiveCoefficient M H
        (aux_rem_bank_response_moments_lc_upShift k z om) (N + k) 0 one_pos) 0 1 (1 / 8) 1)⁻¹)
    (max (3 * p) q) CF (max CL 0) (by rw [hCF]; exact ENNReal.toReal_nonneg)
    hFmem hFn hΛmem hΛn
  have hCs := aux_rem_bank_response_moments_Cstar_nonneg d X.C
  have h3 : ENNReal.ofReal (3 * p) ≤ ENNReal.ofReal (max (3 * p) q) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have h4 : ENNReal.ofReal q ≤ ENNReal.ofReal (max (3 * p) q) :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  exact aux_rem_bank_response_moments_assemble (chaosSampleLaw M).toMeasure
    (fun N om => dirichletResponse (killedResponseSpace hP)
      (cutoffPositiveCoefficient M H om N z hr) b)
    (fun N om => inverseResponse (killedResponseSpace hP)
      (cutoffPositiveCoefficient M H om N z hr)
      ((sobolevVolumeLoad fL2).comp (killedResponseSpace hP).space.subtypeL))
    (fun N om => ∑ m : Fin d → Fin n, |K m N om|)
    (fun N om => aux_rem_bank_response_moments_lc_environment_factor M H k z hR om *
      (E.lam 0 1 one_pos (cutoffPositiveCoefficient M H
        (aux_rem_bank_response_moments_lc_upShift k z om) (N + k) 0 one_pos) 0 1 (1 / 8) 1)⁻¹)
    (aux_rem_bank_response_moments_Cstar d X.C *
      c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ^ 2)
    (‖fL2‖ ^ 2 * ((3 : ℝ) ^ k * P.C) ^ 2)
    (∑ m : Fin d → Fin n, max (CK m) 0) (CF * max CL 0) (by positivity) (by positivity)
    (Finset.sum_nonneg fun m _ => le_max_right _ _)
    (mul_nonneg (by rw [hCF]; exact ENNReal.toReal_nonneg) (le_max_right _ _))
    (ENNReal.ofReal (3 * p)) (ENNReal.ofReal q) (ENNReal.ofReal (max (3 * p) q)) h3 h4
    (fun N => (aux_rem_bank_response_moments_measurable_dirichletResponse M H HI.1 N z hr
      (killedResponseSpace hP) b).aestronglyMeasurable)
    (fun N => (aux_rem_bank_response_moments_measurable_inverseResponse M H HI.1 N z hr
      (killedResponseSpace hP) _).aestronglyMeasurable)
    hKD.1 hKK.1 hKD.2 hKK.2
    (fun N => by
      filter_upwards [henvD] with om hom
      exact hom N)
    (fun N => Filter.Eventually.of_forall fun om =>
      aux_rem_bank_response_moments_inverse_env_large hd E P M Rm H z r hr k hk.le hP fL2 N om)

end

/-- **The principal statement, exact frozen header** (`rem_bank_response_moments`). -/
theorem aux_rem_bank_response_moments_main
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : _root_.SubdiffusiveProcess.Paper.in_J d) (P : _root_.SubdiffusiveProcess.Paper.in_poincare d hd E)
    (X : _root_.SubdiffusiveProcess.Paper.in_extension d hd E)
    (_W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (t : ℝ) (ht0 : (d : ℝ) - 1 < t) (ht1 : t < (d : ℝ))
    (p q : ℝ) (hp : 2 ≤ p) (_hpq : p < q) :
    ∃ deltaResp : ℝ, 0 < deltaResp ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M)
        (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ min 1 deltaResp →
        let Pm : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
          ∀ hP : (∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
            ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
              K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖),
          ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
          ∀ b : weakSobolevGraph (centeredCube z r hr),
            (b.val.1 =ᵐ[volume.restrict
              (centeredCube z r hr : Set (SpatialCoordinates d))] phi) →
          ∀ f : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ f →
            HasCompactSupport f →
            tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ fL2 : DomainL2 (centeredCube z r hr),
            ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f) →
          ∃ Bresp : ℝ, 0 ≤ Bresp ∧
            ∀ N : ℕ,
              MemLp
                (fun omega : BilateralField d =>
                  dirichletResponse (killedResponseSpace hP)
                    (cutoffPositiveCoefficient M H omega N z hr) b)
                (ENNReal.ofReal (3 * p)) Pm ∧
              MemLp
                (fun omega : BilateralField d =>
                  inverseResponse (killedResponseSpace hP)
                    (cutoffPositiveCoefficient M H omega N z hr)
                    ((sobolevVolumeLoad fL2).comp
                      (killedResponseSpace hP).space.subtypeL))
                (ENNReal.ofReal (3 * p)) Pm ∧
              MemLp
                (fun omega : BilateralField d =>
                  dirichletResponse (killedResponseSpace hP)
                    (cutoffPositiveCoefficient M H omega N z hr) b)
                (ENNReal.ofReal q) Pm ∧
              MemLp
                (fun omega : BilateralField d =>
                  inverseResponse (killedResponseSpace hP)
                    (cutoffPositiveCoefficient M H omega N z hr)
                    ((sobolevVolumeLoad fL2).comp
                      (killedResponseSpace hP).space.subtypeL))
                (ENNReal.ofReal q) Pm ∧
              eLpNorm
                  (fun omega : BilateralField d =>
                    dirichletResponse (killedResponseSpace hP)
                      (cutoffPositiveCoefficient M H omega N z hr) b)
                  (ENNReal.ofReal (3 * p)) Pm +
                eLpNorm
                  (fun omega : BilateralField d =>
                    inverseResponse (killedResponseSpace hP)
                      (cutoffPositiveCoefficient M H omega N z hr)
                      ((sobolevVolumeLoad fL2).comp
                        (killedResponseSpace hP).space.subtypeL))
                  (ENNReal.ofReal (3 * p)) Pm +
                eLpNorm
                  (fun omega : BilateralField d =>
                    dirichletResponse (killedResponseSpace hP)
                      (cutoffPositiveCoefficient M H omega N z hr) b)
                  (ENNReal.ofReal q) Pm +
                eLpNorm
                  (fun omega : BilateralField d =>
                    inverseResponse (killedResponseSpace hP)
                      (cutoffPositiveCoefficient M H omega N z hr)
                      ((sobolevVolumeLoad fL2).comp
                        (killedResponseSpace hP).space.subtypeL))
                  (ENNReal.ofReal q) Pm ≤ ENNReal.ofReal Bresp := by
  have hp1 : (1 : ℝ) ≤ max (3 * p) q := le_trans (by linarith) (le_max_left _ _)
  have hp2 : (1 : ℝ) ≤ 2 * max (3 * p) q := by linarith
  have hG0 := aux_lem_extension_grid_clause d hd E (1 / 8) (max (3 * p) q) (by norm_num) hp1
    (5 / 8) ⟨by norm_num, by norm_num⟩
  rcases hG0 with ⟨dG, hdG, hGrid⟩
  have hL0 := lambda_inv_moments d hd E (1 / 8) ⟨by norm_num, by norm_num⟩
  rcases hL0 with ⟨dL, hdL, hLam⟩
  refine ⟨min dG (min (dL (max (3 * p) q)) (dL (2 * max (3 * p) q))),
    lt_min hdG (lt_min (hdL _ hp1) (hdL _ hp2)), ?_⟩
  intro M Rm Sreg It H hIC hδ Pm z r hr hP phi hphi b hb f hf hfc hfs fL2 hfL2
  have hδ' : M.delta ≤ min dG (min (dL (max (3 * p) q)) (dL (2 * max (3 * p) q))) :=
    hδ.trans (min_le_right _ _)
  have hδ1 : M.delta ≤ dG := hδ'.trans (min_le_left _ _)
  have hδ2 : M.delta ≤ dL (max (3 * p) q) :=
    hδ'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ3 : M.delta ≤ dL (2 * max (3 * p) q) :=
    hδ'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hphi2 : ContDiff ℝ 2 phi := hphi.of_le (WithTop.coe_le_coe.2 le_top)
  by_cases hr1 : r ≤ 1
  · have hG1 := hGrid M Rm H hIC hδ1 z 1 one_pos 1 (fun _ => z)
    rcases hG1 with ⟨K, CK, hKmem, hKn, hKae⟩
    have hL1 := hLam M Rm H hIC z r hr hr1 (max (3 * p) q) hp1 hδ2
    rcases hL1 with ⟨CL, hLmem, hLn⟩
    exact aux_rem_bank_response_moments_rooted hd E P X p q M H hIC.1 z r hr hr1 K CK hKmem hKn
      hKae CL hLmem hLn hP phi hphi2 b hb fL2
  · have hL1 := hLam M Rm H hIC 0 1 one_pos le_rfl (2 * max (3 * p) q) hp2 hδ3
    rcases hL1 with ⟨CL, hLmem, hLn⟩
    exact aux_rem_bank_response_moments_rooted_large hd E P X p q hp1 M Rm H hIC z r hr
      (fun c => hGrid M Rm H hIC hδ1 c 1 one_pos 1 (fun _ => c)) CL hLmem hLn hP phi hphi2 b hb fL2

end RBMain_part

end



theorem rem_bank_response_moments
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : _root_.SubdiffusiveProcess.Paper.in_J d) (P : _root_.SubdiffusiveProcess.Paper.in_poincare d hd E)
    (X : _root_.SubdiffusiveProcess.Paper.in_extension d hd E)
    (W : _root_.SubdiffusiveProcess.EllipticRegularity.SmallPerturbationInput d)
    (t : ℝ) (ht0 : (d : ℝ) - 1 < t) (ht1 : t < (d : ℝ))
    (p q : ℝ) (hp : 2 ≤ p) (hpq : p < q) :
    ∃ deltaResp : ℝ, 0 < deltaResp ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d M) (Sreg : in_6_16 d M)
        (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ min 1 deltaResp →
        let Pm : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
          ∀ hP : (∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
            ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
              K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖),
          ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
          ∀ b : weakSobolevGraph (centeredCube z r hr),
            (b.val.1 =ᵐ[volume.restrict
              (centeredCube z r hr : Set (SpatialCoordinates d))] phi) →
          ∀ f : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ f →
            HasCompactSupport f →
            tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
          ∀ fL2 : DomainL2 (centeredCube z r hr),
            ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[
              volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f) →
          ∃ Bresp : ℝ, 0 ≤ Bresp ∧
            ∀ N : ℕ,
              MemLp
                (fun omega : BilateralField d =>
                  dirichletResponse (killedResponseSpace hP)
                    (cutoffPositiveCoefficient M H omega N z hr) b)
                (ENNReal.ofReal (3 * p)) Pm ∧
              MemLp
                (fun omega : BilateralField d =>
                  inverseResponse (killedResponseSpace hP)
                    (cutoffPositiveCoefficient M H omega N z hr)
                    ((sobolevVolumeLoad fL2).comp
                      (killedResponseSpace hP).space.subtypeL))
                (ENNReal.ofReal (3 * p)) Pm ∧
              MemLp
                (fun omega : BilateralField d =>
                  dirichletResponse (killedResponseSpace hP)
                    (cutoffPositiveCoefficient M H omega N z hr) b)
                (ENNReal.ofReal q) Pm ∧
              MemLp
                (fun omega : BilateralField d =>
                  inverseResponse (killedResponseSpace hP)
                    (cutoffPositiveCoefficient M H omega N z hr)
                    ((sobolevVolumeLoad fL2).comp
                      (killedResponseSpace hP).space.subtypeL))
                (ENNReal.ofReal q) Pm ∧
              eLpNorm
                  (fun omega : BilateralField d =>
                    dirichletResponse (killedResponseSpace hP)
                      (cutoffPositiveCoefficient M H omega N z hr) b)
                  (ENNReal.ofReal (3 * p)) Pm +
                eLpNorm
                  (fun omega : BilateralField d =>
                    inverseResponse (killedResponseSpace hP)
                      (cutoffPositiveCoefficient M H omega N z hr)
                      ((sobolevVolumeLoad fL2).comp
                        (killedResponseSpace hP).space.subtypeL))
                  (ENNReal.ofReal (3 * p)) Pm +
                eLpNorm
                  (fun omega : BilateralField d =>
                    dirichletResponse (killedResponseSpace hP)
                      (cutoffPositiveCoefficient M H omega N z hr) b)
                  (ENNReal.ofReal q) Pm +
                eLpNorm
                  (fun omega : BilateralField d =>
                    inverseResponse (killedResponseSpace hP)
                      (cutoffPositiveCoefficient M H omega N z hr)
                      ((sobolevVolumeLoad fL2).comp
                        (killedResponseSpace hP).space.subtypeL))
                  (ENNReal.ofReal q) Pm ≤ ENNReal.ofReal Bresp := by
  exact aux_rem_bank_response_moments_main d hd E P X W t ht0 ht1 p q hp hpq

end SubdiffusiveProcess.Paper
