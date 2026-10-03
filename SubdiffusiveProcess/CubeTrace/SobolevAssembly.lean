module

public import Mathlib
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.Lane2.NativeBridge
public import SubdiffusiveProcess.CubeTrace.Scale
public import SubdiffusiveProcess.CubeTrace.Fractional
public import SubdiffusiveProcess.CubeTrace.Sobolev

@[expose] public section

/-!
# Cube trace extension: from pointwise regularity to a weak-gradient element

A function `b` that is `C²` on the open cube with `|∇b| ≤ M m^{β-1}`, `|D²b| ≤ M m^{β-2}` (and
bounded) defines an element of `weakSobolevGraph` whose gradient components have finite `H^σ`
norm, `σ < β - 1/2`, with `∑_i ‖∂_i b‖²_{H^σ} ≤ C M²`.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff Topology
open SubdiffusiveProcess.Lane4
noncomputable section
namespace SubdiffusiveProcess.CubeTrace

variable {d : ℕ}

/-- The order `σ = (β - 1/2)/2 ∈ (0,1)`. -/
def ctSigma {β : ℝ} (hβ : β ∈ Set.Ioo (1 / 2 : ℝ) 1) : Set.Ioo (0 : ℝ) 1 :=
  ⟨(β - 1 / 2) / 2, by have h1 := hβ.1; have h2 := hβ.2; exact ⟨by linarith, by linarith⟩⟩

/-- The Gagliardo seminorm of an `L²` class equals the kernel double integral of any a.e.
representative (unit cube). -/
theorem ct_seminorm_eq {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1)
    (s : Set.Ioo (0 : ℝ) 1) (f : DomainL2 (centeredCube z 1 h1)) (F : SpatialCoordinates d → ℝ)
    (hF : (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (ctQ z)] F) :
    cubeFractionalL2Seminorm hd z 1 h1 s (fun _ : Fin 1 => f) =
      (ENNReal.ofReal (s : ℝ) / volume (ctQ z) *
        ∫⁻ x in ctQ z, ∫⁻ y in ctQ z, ctFracKer (s : ℝ) F x y) ^ (1 / 2 : ℝ) := by
  unfold cubeFractionalL2Seminorm
  have hint : (∫⁻ x in (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z 1 h1 : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin 1, (((fun _ : Fin 1 => f) i : SpatialCoordinates d → ℝ) x -
          ((fun _ : Fin 1 => f) i : SpatialCoordinates d → ℝ) y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ))) =
      ∫⁻ x in ctQ z, ∫⁻ y in ctQ z, ctFracKer (s : ℝ) F x y := by
    apply lintegral_congr_ae
    filter_upwards [hF] with x hx
    apply lintegral_congr_ae
    filter_upwards [hF] with y hy
    simp [ctFracKer, hx, hy]
  rw [hint]
  rfl

/-- The `L²` norm of a class squared is the integral of the square of any representative. -/
theorem ct_norm_sq_eq {d : ℕ} (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1)
    (f : DomainL2 (centeredCube z 1 h1)) (F : SpatialCoordinates d → ℝ)
    (hF : (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (ctQ z)] F) :
    ‖f‖ ^ 2 = ∫ x in ctQ z, F x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF] with x hx
  simp [hx, sq]

/-- The normalized `H^s` squared norm from the pieces. -/
theorem ct_sqnorm_le {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (h1 : (0 : ℝ) < 1)
    (s : Set.Ioo (0 : ℝ) 1) (f : DomainL2 (centeredCube z 1 h1)) {C1 C2 : ℝ} (hC1 : 0 ≤ C1)
    (hsem : cubeFractionalL2Seminorm hd z 1 h1 s (fun _ : Fin 1 => f) ≤
      ENNReal.ofReal (Real.sqrt C1))
    (hnorm : ‖f‖ ^ 2 ≤ C2) :
    cubeFractionalSqNorm hd z 1 h1 s f ≤ C1 + C2 := by
  have hvol : volume.real (centeredCube z 1 h1 : Set (SpatialCoordinates d)) = 1 := by
    simp [Measure.real, centeredCube_volume]
  unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
  rw [hvol]
  have hle : (cubeFractionalL2Seminorm hd z 1 h1 s (fun _ : Fin 1 => f)).toReal ≤
      Real.sqrt C1 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsem
    rwa [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at this
  have h2 : (cubeFractionalL2Seminorm hd z 1 h1 s (fun _ : Fin 1 => f)).toReal ^ 2 ≤ C1 := by
    calc _ ≤ Real.sqrt C1 ^ 2 := pow_le_pow_left₀ ENNReal.toReal_nonneg hle 2
      _ = C1 := Real.sq_sqrt hC1
  simp only [Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul, div_one]
  linarith

/-- **From pointwise regularity to a weak-gradient element with a fractional gradient bound.** -/
theorem ct_sobolev_of_reg [NeZero d] (hd : 2 ≤ d) {β : ℝ} (hβ : β ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (z : SpatialCoordinates d) (M : ℝ) (b : SpatialCoordinates d → ℝ),
      0 ≤ M → CTReg z β M b →
      ∃ bg : weakSobolevGraph (centeredCube z 1 one_pos),
        (((bg : SobolevData (centeredCube z 1 one_pos)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))] b) ∧
        (∀ i : Fin d, cubeFractionalL2Seminorm hd z 1 one_pos (ctSigma hβ)
          (fun _ : Fin 1 => (bg : SobolevData (centeredCube z 1 one_pos)).2 i) < ⊤) ∧
        ∑ i : Fin d, cubeFractionalSqNorm hd z 1 one_pos (ctSigma hβ)
          ((bg : SobolevData (centeredCube z 1 one_pos)).2 i) ≤ Cs * M ^ 2 := by
  have hβ1 := hβ.1
  have hβ2 := hβ.2
  have hσ0 : 0 < (ctSigma hβ : ℝ) := (ctSigma hβ).2.1
  have hσβ : (ctSigma hβ : ℝ) < β - 1 / 2 := by
    show (β - 1 / 2) / 2 < β - 1 / 2
    linarith
  obtain ⟨Cf, hCf0, hCf⟩ := ct_fractional_double_integral (d := d) hβ hσ0 hσβ
  set Lc : ℝ := 1 + (d : ℝ) * 2 ^ (2 - β) with hLc
  have hLc1 : 1 ≤ Lc := by
    have : 0 ≤ (d : ℝ) * 2 ^ (2 - β) := by positivity
    linarith
  set Kd : ℝ := (d : ℝ) * (4 ^ (2 - 2 * β) / (1 - (2 - 2 * β))) with hKd
  have hden : 0 < 1 - (2 - 2 * β) := by linarith
  have hKd0 : 0 ≤ Kd := by positivity
  set s : ℝ := (ctSigma hβ : ℝ) with hs
  have hs0 : 0 ≤ s := hσ0.le
  refine ⟨(d : ℝ) * (s * (Cf * Lc ^ 2) + Kd), by positivity, ?_⟩
  intro z M b hM hreg
  obtain ⟨u, hu1, hu2⟩ := hreg.exists_h1 hβ hM
  set Q : TopologicalSpace.Opens (SpatialCoordinates d) := centeredCube z 1 one_pos with hQ
  let u' : Homogenization.H1Function (Q : Set (SpatialCoordinates d)) := u
  have hu1' : u'.toFun = b := hu1
  have hu2' : u'.grad = fun x j => fderiv ℝ b x (Pi.single j 1) := hu2
  let bg : weakSobolevGraph Q := ⟨sobolevDataOfH1 u', sobolevDataOfH1_mem_weak u'⟩
  have hvolQ : volume (Q : Set (SpatialCoordinates d)) = 1 := by
    rw [hQ, centeredCube_volume]; simp
  -- the components are a.e. equal to the classical partial derivatives
  have hcomp : ∀ i : Fin d, (((bg : SobolevData Q).2 i : DomainL2 Q) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (ctQ z)] fun x => fderiv ℝ b x (Pi.single i 1) := by
    intro i
    refine (sobolevDataOfH1_snd_coeFn u' i).trans ?_
    exact Filter.EventuallyEq.of_eq (by funext x; rw [hu2'])
  -- the double integral bound for each component
  have hdbl : ∀ i : Fin d, ∫⁻ x in ctQ z, ∫⁻ y in ctQ z,
      ctFracKer s (fun x => fderiv ℝ b x (Pi.single i 1)) x y ≤ ENNReal.ofReal (Cf * (M * Lc) ^ 2) := by
    intro i
    refine hCf z (M * Lc) _ (by positivity) (hreg.continuousOn_grad i) ?_ ?_
    · intro x hx
      refine (hreg.grad_bound x hx i).trans ?_
      have : 0 ≤ M * ctM z x ^ (β - 1) := mul_nonneg hM (Real.rpow_nonneg (ctM_pos hx).le _)
      nlinarith
    · intro x hx y hy
      refine (hreg.lipschitz_near hM (by linarith) i hx hy).trans ?_
      have hm : 0 ≤ ctM z x ^ (β - 2) * ‖x - y‖ :=
        mul_nonneg (Real.rpow_nonneg (ctM_pos hx).le _) (norm_nonneg _)
      have : (d : ℝ) * 2 ^ (2 - β) * M ≤ M * Lc := by rw [hLc]; nlinarith [hM]
      calc (d : ℝ) * 2 ^ (2 - β) * M * ctM z x ^ (β - 2) * ‖x - y‖
          = ((d : ℝ) * 2 ^ (2 - β) * M) * (ctM z x ^ (β - 2) * ‖x - y‖) := by ring
        _ ≤ (M * Lc) * (ctM z x ^ (β - 2) * ‖x - y‖) := mul_le_mul_of_nonneg_right this hm
        _ = M * Lc * ctM z x ^ (β - 2) * ‖x - y‖ := by ring
  refine ⟨bg, ?_, ?_, ?_⟩
  · refine (sobolevDataOfH1_fst_coeFn u').trans ?_
    exact Filter.EventuallyEq.of_eq hu1'
  · intro i
    rw [ct_seminorm_eq hd z one_pos (ctSigma hβ) _ _ (hcomp i)]
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
    refine ne_of_lt (lt_of_le_of_lt (mul_le_mul_right (hdbl i) _) ?_)
    rw [show volume (ctQ z) = 1 from hvolQ, div_one]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  · have hterm : ∀ i : Fin d, cubeFractionalSqNorm hd z 1 one_pos (ctSigma hβ)
        ((bg : SobolevData Q).2 i) ≤ s * (Cf * (M * Lc) ^ 2) + M ^ 2 * Kd := by
      intro i
      refine ct_sqnorm_le hd z one_pos (ctSigma hβ) _ (by positivity) ?_ ?_
      · rw [ct_seminorm_eq hd z one_pos (ctSigma hβ) _ _ (hcomp i), show volume (ctQ z) = 1 from hvolQ]
        calc (ENNReal.ofReal (s) / 1 * ∫⁻ x in ctQ z, ∫⁻ y in ctQ z,
              ctFracKer s (fun x => fderiv ℝ b x (Pi.single i 1)) x y) ^ (1 / 2 : ℝ)
            ≤ (ENNReal.ofReal s / 1 * ENNReal.ofReal (Cf * (M * Lc) ^ 2)) ^ (1 / 2 : ℝ) :=
              ENNReal.rpow_le_rpow (mul_le_mul_right (hdbl i) _) (by norm_num)
          _ = ENNReal.ofReal (Real.sqrt (s * (Cf * (M * Lc) ^ 2))) := by
              rw [div_one, ← ENNReal.ofReal_mul hs0,
                ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.sqrt_eq_rpow]
      · rw [ct_norm_sq_eq z one_pos _ _ (hcomp i)]
        exact (hreg.grad_sq_integral hβ hM i).2
    calc ∑ i : Fin d, cubeFractionalSqNorm hd z 1 one_pos (ctSigma hβ) ((bg : SobolevData Q).2 i)
        ≤ ∑ _i : Fin d, (s * (Cf * (M * Lc) ^ 2) + M ^ 2 * Kd) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (d : ℝ) * (s * (Cf * Lc ^ 2) + Kd) * M ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

end SubdiffusiveProcess.CubeTrace
