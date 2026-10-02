import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.CompactSupportForcingBound
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.BoundedPointwiseMassiveLimit




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open Filter MeasureTheory
open Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped CompactlySupported ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-- Restricting the expanding massive cube solutions to one fixed cube gives
a sequence with uniformly bounded Hilbert `L²` gradient norm. -/
theorem exists_uniform_local_gradient_norm_bound [NeZero d]
    {c rho : Vec d → ℝ} (B : MassiveCubeBounds c rho)
    {mu : ℝ} (hmu : 0 < mu) (f : C_c(Vec d, ℝ))
    (uCube : ∀ n : ℕ, H10Function (cube d (n : ℤ)))
    (hu : ∀ n, IsControlledMassiveCubeSolution c rho mu f n (uCube n))
    (k : ℕ) :
    ∃ Cgrad : ℝ, 0 ≤ Cgrad ∧ ∀ n : ℕ,
      let hsubset : cube d (k : ℤ) ⊆ cube d ((k + n : ℕ) : ℤ) :=
        Section6ExcessDecay.cube_subset_cube_of_le (by omega)
      ‖((uCube (k + n)).toH1Function.restrict
          (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)).isOpen
          hsubset).gradToHilbertVectorL2‖ ≤ Cgrad := by
  obtain ⟨Cforcing, hCforcing, hforcing⟩ :=
    exists_uniform_massiveCube_forcing_integral_bound B f
  let denominator : ℝ := 2 * mu * B.lam k
  have hdenominator : 0 < denominator := by
    dsimp only [denominator]
    exact mul_pos (mul_pos two_pos hmu) (B.lam_pos k)
  let Cgrad : ℝ := Real.sqrt (Cforcing / denominator)
  have hCgrad : 0 ≤ Cgrad := Real.sqrt_nonneg _
  refine ⟨Cgrad, hCgrad, fun n ↦ ?_⟩
  let hsubset : cube d (k : ℤ) ⊆ cube d ((k + n : ℕ) : ℤ) :=
    Section6ExcessDecay.cube_subset_cube_of_le (by omega)
  let w : H1Function (cube d (k : ℤ)) :=
    (uCube (k + n)).toH1Function.restrict
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d (k : ℤ)).isOpen
      hsubset
  have hcoercive : B.lam k * ‖w.gradToHilbertVectorL2‖ ^ 2 ≤
      ∫ x in cube d (k : ℤ), c x * vecNormSq (w.grad x) ∂volume := by
    have hcoercive' := MassiveH1Hilbert.coeffGradientBilin_self_ge
      (B.ell k) (MassiveH1Hilbert.ofH1Function w)
    simpa only [MassiveH1Hilbert.gradient_ofH1Function,
      MassiveH1Hilbert.coeffGradientBilin_apply_ofH1Function,
      vecDot_smul_left, vecNormSq] using hcoercive'
  have henergyIntegrable : IntegrableOn
      (fun x ↦ c x * vecNormSq ((uCube (k + n)).toH1Function.grad x))
      (cube d ((k + n : ℕ) : ℤ)) := by
    have hflux : MemVectorL2 (cube d ((k + n : ℕ) : ℤ))
        (fun x ↦ c x • (uCube (k + n)).toH1Function.grad x) := by
      simpa only [scalarCoeffField, matVecMul_scalarMatrix] using
        memVectorL2_matVecMul_of_isEllipticFieldOn (B.ell (k + n))
          (uCube (k + n)).toH1Function.grad_memVectorL2
    simpa only [vecDot_smul_left, vecNormSq] using
      integrableOn_vecDot_of_memVectorL2 hflux
        (uCube (k + n)).toH1Function.grad_memVectorL2
  have henergyNonneg : 0 ≤ᵐ[volume.restrict (cube d ((k + n : ℕ) : ℤ))]
      fun x ↦ c x * vecNormSq ((uCube (k + n)).toH1Function.grad x) := by
    filter_upwards [ae_restrict_mem
      (Section6ExcessDecay.isOpenBoundedConvexDomain_cube d
        ((k + n : ℕ) : ℤ)).isOpen.measurableSet] with x hx
    exact mul_nonneg
      ((B.lam_pos (k + n)).le.trans (B.coeff_lower (k + n) x hx))
      (vecNormSq_nonneg _)
  have hlocalEnergy :
      (∫ x in cube d (k : ℤ), c x * vecNormSq (w.grad x) ∂volume) ≤
        ∫ x in cube d ((k + n : ℕ) : ℤ),
          c x * vecNormSq ((uCube (k + n)).toH1Function.grad x) ∂volume := by
    have hmono := setIntegral_mono_set henergyIntegrable henergyNonneg
      (Filter.Eventually.of_forall hsubset)
    simpa only [w, H1Function.restrict] using hmono
  have hcontrolled := (hu (k + n)).2.2.1
  have hscaled : denominator * ‖w.gradToHilbertVectorL2‖ ^ 2 ≤ Cforcing := by
    calc
      denominator * ‖w.gradToHilbertVectorL2‖ ^ 2 =
          2 * mu * (B.lam k * ‖w.gradToHilbertVectorL2‖ ^ 2) := by
        dsimp only [denominator]
        ring
      _ ≤ 2 * mu *
          ∫ x in cube d (k : ℤ), c x * vecNormSq (w.grad x) ∂volume :=
        mul_le_mul_of_nonneg_left hcoercive (mul_nonneg two_pos.le hmu.le)
      _ ≤ 2 * mu * ∫ x in cube d ((k + n : ℕ) : ℤ),
          c x * vecNormSq ((uCube (k + n)).toH1Function.grad x) ∂volume :=
        mul_le_mul_of_nonneg_left hlocalEnergy (mul_nonneg two_pos.le hmu.le)
      _ ≤ ∫ x in cube d ((k + n : ℕ) : ℤ), rho x * f x * f x ∂volume :=
        hcontrolled
      _ ≤ Cforcing := hforcing (k + n)
  have hsquare : ‖w.gradToHilbertVectorL2‖ ^ 2 ≤
      Cforcing / denominator := by
    exact (le_div_iff₀ hdenominator).2 <| by
      simpa only [mul_comm] using hscaled
  exact Real.le_sqrt_of_sq_le hsquare

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
