/-
Copyright (c) 2026 Scott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott
-/
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsFluxPrice
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsHodge




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory
open Homogenization
open Homogenization.Book
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet
open Homogenization.Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The normalization bookkeeping -/

/-- The cube average as a normalized integral over the **open** cube. -/
private theorem cubeAverage_eq_inv_mul_setIntegral_openCubeSet
    (Q : TriadicCube d) (f : Vec d → ℝ) :
    cubeAverage Q f = (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q, f x ∂volume := by
  rw [cubeAverage, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]

/-- The exact scaling identity behind the conversion: the split price is
homogeneous of degree `-1` in the cube volume, on **both** sides. -/
private theorem scaled_price_eq (vol P R Sc t beta E M : ℝ) (hvol : 0 < vol) :
    vol * (beta * P * (vol⁻¹ * E + Sc * (t⁻¹ * (vol⁻¹ * M))) +
        beta⁻¹ * R * Real.sqrt (vol⁻¹ * E + Sc * (t⁻¹ * (vol⁻¹ * M))) *
          Real.sqrt (vol⁻¹ * M)) =
      beta * P * (E + Sc * (t⁻¹ * M)) +
        beta⁻¹ * R * Real.sqrt (E + Sc * (t⁻¹ * M)) * Real.sqrt M := by
  have hinv : (0 : ℝ) ≤ vol⁻¹ := (inv_pos.mpr hvol).le
  have harg : vol⁻¹ * E + Sc * (t⁻¹ * (vol⁻¹ * M)) = vol⁻¹ * (E + Sc * (t⁻¹ * M)) := by
    ring
  have hss : Real.sqrt vol⁻¹ * Real.sqrt vol⁻¹ = vol⁻¹ := Real.mul_self_sqrt hinv
  have hv : vol⁻¹ * vol = 1 := inv_mul_cancel₀ hvol.ne'
  rw [harg, Real.sqrt_mul hinv, Real.sqrt_mul hinv]
  have hstep : vol * (beta * P * (vol⁻¹ * (E + Sc * (t⁻¹ * M))) +
        beta⁻¹ * R * (Real.sqrt vol⁻¹ * Real.sqrt (E + Sc * (t⁻¹ * M))) *
          (Real.sqrt vol⁻¹ * Real.sqrt M)) =
      (vol⁻¹ * vol) * (beta * P * (E + Sc * (t⁻¹ * M))) +
        ((Real.sqrt vol⁻¹ * Real.sqrt vol⁻¹) * vol) *
          (beta⁻¹ * R * Real.sqrt (E + Sc * (t⁻¹ * M)) * Real.sqrt M) := by
    ring
  rw [hstep, hss, hv, one_mul]
  ring

/-! ## The price on one cell, from its cube-average form -/

/-- **The mesoscopic cross-term price on a triadic cube, from the cube-average
split price.**

The hypothesis is exactly the conclusion of P-221's
`abs_cubeAverage_vecDot_cutoffProduct_mesoscopic_le_of_coarse_conversions`
after the pairing has been written out at `flux = a ∇u`, `ξ = chi ∇chi`, and
after the flux conversion has carried the datum energy `Sc t⁻¹ M` inside the
square root (P-222 §5).  The conclusion is the literal predicate
`MesoscopicCrossPriceEnergyOn` at `V = W = openCubeSet Q`, with `P` and `R`
doubled — the factor `2` of the cross term, which the cube-average form does
not carry. -/
theorem mesoscopicCrossPriceEnergyOn_openCubeSet_of_cubeAverage
    (Q : TriadicCube d) (a chi : Vec d → ℝ) (u : H1Function (openCubeSet Q))
    {t P R Sc : ℝ}
    (hprice : ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
      |cubeAverage Q (fun x => a x * chi x * u.toFun x *
          vecDot (u.grad x) (fun i => (fderiv ℝ chi x) (basisVec i)))| ≤
        beta * P * (cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) +
            Sc * (t⁻¹ * cubeAverage Q (fun x => u.toFun x ^ 2))) +
          beta⁻¹ * R *
            Real.sqrt (cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) +
              Sc * (t⁻¹ * cubeAverage Q (fun x => u.toFun x ^ 2))) *
            Real.sqrt (cubeAverage Q (fun x => u.toFun x ^ 2))) :
    MesoscopicCrossPriceEnergyOn a (openCubeSet Q) (openCubeSet Q) u.toFun u.grad
      chi t (2 * P) (2 * R) Sc := by
  intro beta hbeta0 hbeta1
  have hvol : 0 < cubeVolume Q := cubeVolume_pos Q
  set vol : ℝ := cubeVolume Q with hvoldef
  set C : ℝ := ∫ x in openCubeSet Q, a x * chi x * u.toFun x *
    vecDot (u.grad x) (fun i => (fderiv ℝ chi x) (basisVec i)) ∂volume with hCdef
  set E : ℝ := ∫ x in openCubeSet Q, a x * vecNormSq (u.grad x) ∂volume with hEdef
  set M : ℝ := ∫ x in openCubeSet Q, u.toFun x ^ 2 ∂volume with hMdef
  have hC : cubeAverage Q (fun x => a x * chi x * u.toFun x *
      vecDot (u.grad x) (fun i => (fderiv ℝ chi x) (basisVec i))) = vol⁻¹ * C :=
    cubeAverage_eq_inv_mul_setIntegral_openCubeSet Q _
  have hE : cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) = vol⁻¹ * E :=
    cubeAverage_eq_inv_mul_setIntegral_openCubeSet Q _
  have hM : cubeAverage Q (fun x => u.toFun x ^ 2) = vol⁻¹ * M :=
    cubeAverage_eq_inv_mul_setIntegral_openCubeSet Q _
  have hraw := hprice beta hbeta0 hbeta1
  rw [hC, hE, hM] at hraw
  have hmul := mul_le_mul_of_nonneg_left hraw (by positivity : (0 : ℝ) ≤ 2 * vol)
  have hleft : 2 * vol * |vol⁻¹ * C| = |2 * C| := by
    rw [abs_mul, abs_of_nonneg (inv_pos.mpr hvol).le, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
    field_simp
  have hright : 2 * vol * (beta * P * (vol⁻¹ * E + Sc * (t⁻¹ * (vol⁻¹ * M))) +
        beta⁻¹ * R * Real.sqrt (vol⁻¹ * E + Sc * (t⁻¹ * (vol⁻¹ * M))) *
          Real.sqrt (vol⁻¹ * M)) =
      beta * (2 * P) * (E + Sc * (t⁻¹ * M)) +
        beta⁻¹ * (2 * R) * Real.sqrt (E + Sc * (t⁻¹ * M)) * Real.sqrt M := by
    have := scaled_price_eq vol P R Sc t beta E M hvol
    nlinarith [this]
  rw [hleft, hright] at hmul
  exact hmul

/-! ## The two `L^2` inputs of the split price -/

/-- `(cubeLpNorm Q 2 f)^2` is the cube average of `f^2`. -/
theorem cubeLpNorm_two_sq_eq_cubeAverage_sq (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℕ) = cubeAverage Q (fun x => f x ^ (2 : ℕ)) := by
  have h := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow Q (2 : ℝ≥0∞) f
    (by norm_num) (by norm_num) hf
  have htwo : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  rw [htwo] at h
  have hleft : (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℝ) =
      (cubeLpNorm Q (2 : ℝ≥0∞) f) ^ (2 : ℕ) := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hright : (fun x => ‖f x‖ ^ (2 : ℝ)) = fun x => f x ^ (2 : ℕ) := by
    funext x
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp [sq_abs]
  rw [hleft, hright] at h
  exact h

/-- `cubeLpNorm Q 2 f = sqrt (cubeAverage Q f^2)`. -/
theorem cubeLpNorm_two_eq_sqrt_cubeAverage_sq (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) f =
      Real.sqrt (cubeAverage Q (fun x => f x ^ (2 : ℕ))) := by
  rw [← cubeLpNorm_two_sq_eq_cubeAverage_sq Q f hf,
    Real.sqrt_sq (cubeLpNorm_nonneg Q (2 : ℝ≥0∞) f)]



theorem cubeLpNorm_two_cubeFluctuation_le (Q : TriadicCube d) (f : Vec d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q f) ≤
      2 * cubeLpNorm Q (2 : ℝ≥0∞) f := by
  have hconst : MemLp (fun _ : Vec d => -cubeAverage Q f) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := MeasureTheory.memLp_const _
  have hfun : cubeFluctuation Q f =
      fun x => f x + (fun _ : Vec d => -cubeAverage Q f) x := by
    funext x; simp [cubeFluctuation, sub_eq_add_neg]
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q f)
        ≤ cubeLpNorm Q (2 : ℝ≥0∞) f +
            cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => -cubeAverage Q f) := by
          rw [hfun]
          exact cubeLpNorm_add_le Q (2 : ℝ≥0∞) f
            (fun _ : Vec d => -cubeAverage Q f) hf hconst (by norm_num)
    _ = cubeLpNorm Q (2 : ℝ≥0∞) f + ‖cubeAverage Q f‖ := by
          rw [cubeLpNorm_const (Q := Q) (p := (2 : ℝ≥0∞))
            (c := -cubeAverage Q f) (by norm_num)]
          simp
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) f + cubeLpNorm Q (2 : ℝ≥0∞) f := by
          gcongr
          exact norm_cubeAverage_le_cubeLpNorm_two Q f hf
    _ = 2 * cubeLpNorm Q (2 : ℝ≥0∞) f := by ring

private theorem sqrt_four_mul (m : ℝ) :
    Real.sqrt (4 * m) = 2 * Real.sqrt m := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
  congr 1
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]

/-- The fluctuation input of the split price, at mass `4 * cubeAverage Q f²`. -/
theorem cubeLpNorm_two_cubeFluctuation_le_sqrt_four_mul (Q : TriadicCube d)
    (f : Vec d → ℝ) (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q f) ≤
      Real.sqrt (4 * cubeAverage Q (fun x => f x ^ (2 : ℕ))) := by
  rw [sqrt_four_mul, ← cubeLpNorm_two_eq_sqrt_cubeAverage_sq Q f hf]
  exact cubeLpNorm_two_cubeFluctuation_le Q f hf

/-- The mean input of the split price, at the same mass. -/
theorem abs_cubeAverage_le_sqrt_four_mul (Q : TriadicCube d)
    (f : Vec d → ℝ) (hf : MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ‖cubeAverage Q f‖ ≤
      Real.sqrt (4 * cubeAverage Q (fun x => f x ^ (2 : ℕ))) := by
  rw [sqrt_four_mul, ← cubeLpNorm_two_eq_sqrt_cubeAverage_sq Q f hf]
  have h := norm_cubeAverage_le_cubeLpNorm_two Q f hf
  have h0 : 0 ≤ cubeLpNorm Q (2 : ℝ≥0∞) f := cubeLpNorm_nonneg Q (2 : ℝ≥0∞) f
  linarith

/-- The cube-average price with the mass slot inflated by a factor `kappa`
still gives the predicate, at `R -> sqrt kappa * R` and `Sc -> kappa * Sc`.

This is the form the split price actually delivers: the `L²` inputs of
`abs_cubeAverage_vecDot_cutoffProduct_mesoscopic_le_of_coarse_conversions` are
the fluctuation and the mean, each bounded by `2 ‖u‖_{L̲²}`, so `kappa = 4`. -/
theorem mesoscopicCrossPriceEnergyOn_openCubeSet_of_cubeAverage_mass_scaled
    (Q : TriadicCube d) (a chi : Vec d → ℝ) (u : H1Function (openCubeSet Q))
    {t P R Sc kappa : ℝ} (hkappa : 0 ≤ kappa)
    (hprice : ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
      |cubeAverage Q (fun x => a x * chi x * u.toFun x *
          vecDot (u.grad x) (fun i => (fderiv ℝ chi x) (basisVec i)))| ≤
        beta * P * (cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) +
            Sc * (t⁻¹ * (kappa * cubeAverage Q (fun x => u.toFun x ^ (2 : ℕ))))) +
          beta⁻¹ * R *
            Real.sqrt (cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) +
              Sc * (t⁻¹ * (kappa * cubeAverage Q (fun x => u.toFun x ^ (2 : ℕ))))) *
            Real.sqrt (kappa * cubeAverage Q (fun x => u.toFun x ^ (2 : ℕ)))) :
    MesoscopicCrossPriceEnergyOn a (openCubeSet Q) (openCubeSet Q) u.toFun u.grad
      chi t (2 * P) (2 * (Real.sqrt kappa * R)) (kappa * Sc) := by
  refine mesoscopicCrossPriceEnergyOn_openCubeSet_of_cubeAverage Q a chi u
    (P := P) (R := Real.sqrt kappa * R) (Sc := kappa * Sc) (t := t) ?_
  intro beta hb0 hb1
  have h := hprice beta hb0 hb1
  set m : ℝ := cubeAverage Q (fun x => u.toFun x ^ (2 : ℕ)) with hmdef
  set Eavg : ℝ := cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) with hEdef
  have harg : Eavg + Sc * (t⁻¹ * (kappa * m)) = Eavg + kappa * Sc * (t⁻¹ * m) := by
    ring
  have hsq : Real.sqrt (kappa * m) = Real.sqrt kappa * Real.sqrt m :=
    Real.sqrt_mul hkappa m
  rw [harg, hsq] at h
  have hrhs : beta * P * (Eavg + kappa * Sc * (t⁻¹ * m)) +
      beta⁻¹ * R * Real.sqrt (Eavg + kappa * Sc * (t⁻¹ * m)) *
        (Real.sqrt kappa * Real.sqrt m) =
      beta * P * (Eavg + kappa * Sc * (t⁻¹ * m)) +
        beta⁻¹ * (Real.sqrt kappa * R) *
          Real.sqrt (Eavg + kappa * Sc * (t⁻¹ * m)) * Real.sqrt m := by
    ring
  rw [hrhs] at h
  exact h

/-! ## The price on one cell from the two coarse conversions -/

/-- **`MesoscopicCrossPriceEnergyOn` on a triadic cube from the two coarse
conversions.**

This is the assembly of P-221's split duality price
(`abs_cubeAverage_vecDot_cutoffProduct_mesoscopic_le_of_coarse_conversions`) at
`flux = a grad u`, `xi = chi grad chi`, into the literal predicate the coarse
contraction consumes, with `V = W = openCubeSet Q`.

The two hypotheses `hgrad` and `hflux` are the two coarse conversions:

* `hgrad` is clause 1 of `SubdiffusiveProcess.Frozen.Section2.coarse_grained_poincare` for
  `grad u`, with `cP` of size `lambda^{-1/2}`;
* `hflux` is the flux clause with right-hand side,
  `WholeSpaceRowsFluxPrice.sum_circNegativeBesovNorm_flux_le_of_isForcedEquation`,
  with `cL` of size `Lambda^{1/2}` and with the **datum energy carried inside
  the square root** — the energy-carried shape of P-222 §5, which is why the
  conclusion is `MesoscopicCrossPriceEnergyOn` and not `MesoscopicCrossPriceOn`.

The `L²` inputs of the split price are the fluctuation and the mean of `u`,
each bounded by `2` times its normalized `L²` norm; hence the mass slot is
inflated by `kappa = 4`, which shows up as `Sc -> 4 Sc` and one factor `2` in
`R`.  The remaining factor `2` in both `P` and `R` is the `2` of the cross
term. -/
theorem mesoscopicCrossPriceEnergyOn_openCubeSet_of_coarse_conversions [NeZero d]
    (Q : TriadicCube d) {a chi : Vec d → ℝ} (u : H1Function (openCubeSet Q))
    (ξ : Vec d → Vec d)
    (hξdef : ξ = fun x => fun i => chi x * (fderiv ℝ chi x) (basisVec i))
    {s t Sc cP cL B : ℝ}
    (haNonneg : ∀ x, 0 ≤ a x) (hB : 0 ≤ B)
    (hfluxLp : MemLp (fun x : Vec d => (fun i => a x * u.grad x i : Vec d))
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (huLp : MemLp u.toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξLp : MemLp ξ (∞ : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξsmooth : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hs0 : 0 < s) (hs : 3 * s ≤ 1) (ht : 0 < t)
    (hcL : 0 ≤ cL) (hSc : 0 ≤ Sc)
    (hGnonneg : 0 ≤ (Book.Ch01.Legacy.fullVectorPoincareConstant Q *
        (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ∑ j : Fin d, Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => u.grad x j))
    (hNnonneg : 0 ≤ ∑ i : Fin d,
      Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => a x * u.grad x i))
    (hgrad : (Book.Ch01.Legacy.fullVectorPoincareConstant Q *
          (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ∑ j : Fin d, Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x j) ≤
        cP * Real.sqrt (cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) +
          Sc * (t⁻¹ * (4 * cubeAverage Q (fun x => u.toFun x ^ (2 : ℕ))))))
    (hflux : ∑ i : Fin d,
        Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => a x * u.grad x i) ≤
        cL * Real.sqrt (cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) +
          Sc * (t⁻¹ * (4 * cubeAverage Q (fun x => u.toFun x ^ (2 : ℕ)))))) :
    MesoscopicCrossPriceEnergyOn a (openCubeSet Q) (openCubeSet Q) u.toFun u.grad
      chi t
      (2 * ((3 : ℝ) ^ ((d : ℝ) + s) * cL * cP *
        (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
          (cubeScaleFactor Q) ^ (1 - 2 * s)))
      (2 * (2 * ((3 : ℝ) ^ ((d : ℝ) + s) * cL *
        (2 * (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
            cubeBesovScaleWeight s Q +
          cubeBesovScaleWeight s Q *
            (cubeScaleFactor Q * B + cubeLpNorm Q ∞ ξ)))))
      (4 * Sc) := by
  classical
  set flux : Vec d → Vec d := fun x => fun i => a x * u.grad x i with hfluxdef
  set m : ℝ := cubeAverage Q (fun x => u.toFun x ^ (2 : ℕ)) with hmdef
  set Eavg : ℝ := cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) with hEdef
  set Ea : ℝ := Eavg + Sc * (t⁻¹ * (4 * m)) with hEadef
  have hmnn : 0 ≤ m := by
    rw [hmdef, cubeAverage]
    have : (0 : ℝ) ≤ ∫ x in cubeSet Q, u.toFun x ^ (2 : ℕ) ∂volume :=
      setIntegral_nonneg (measurableSet_cubeSet Q) fun x _ ↦ sq_nonneg _
    have hv : (0 : ℝ) ≤ (cubeVolume Q)⁻¹ := (inv_pos.mpr (cubeVolume_pos Q)).le
    exact mul_nonneg hv this
  have hEavgnn : 0 ≤ Eavg := by
    rw [hEdef, cubeAverage]
    have : (0 : ℝ) ≤ ∫ x in cubeSet Q, a x * vecNormSq (u.grad x) ∂volume :=
      setIntegral_nonneg (measurableSet_cubeSet Q) fun x _ ↦
        mul_nonneg (haNonneg x) (vecNormSq_nonneg _)
    have hv : (0 : ℝ) ≤ (cubeVolume Q)⁻¹ := (inv_pos.mpr (cubeVolume_pos Q)).le
    exact mul_nonneg hv this
  have hEann : 0 ≤ Ea := by
    have h2 : 0 ≤ Sc * (t⁻¹ * (4 * m)) :=
      mul_nonneg hSc (mul_nonneg (inv_pos.mpr ht).le (by linarith))
    rw [hEadef]; linarith
  have hfluc : cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q (fun y => u y)) ≤
      Real.sqrt (4 * m) :=
    cubeLpNorm_two_cubeFluctuation_le_sqrt_four_mul Q u.toFun huLp
  have hmean : ‖cubeAverage Q (fun y => u y)‖ ≤ Real.sqrt (4 * m) :=
    abs_cubeAverage_le_sqrt_four_mul Q u.toFun huLp
  have hpair : (fun x => vecDot (flux x) ((u x) • ξ x)) =
      fun x => a x * chi x * u.toFun x *
        vecDot (u.grad x) (fun i => (fderiv ℝ chi x) (basisVec i)) := by
    funext x
    rw [hfluxdef, hξdef, vecDot, vecDot, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hbase : ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
      |cubeAverage Q (fun x => a x * chi x * u.toFun x *
          vecDot (u.grad x) (fun i => (fderiv ℝ chi x) (basisVec i)))| ≤
        beta * ((3 : ℝ) ^ ((d : ℝ) + s) * cL * cP *
            (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
              (cubeScaleFactor Q) ^ (1 - 2 * s)) * Ea +
          beta⁻¹ * ((3 : ℝ) ^ ((d : ℝ) + s) * cL *
            (2 * (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
                cubeBesovScaleWeight s Q +
              cubeBesovScaleWeight s Q *
                (cubeScaleFactor Q * B + cubeLpNorm Q ∞ ξ))) *
            Real.sqrt Ea * Real.sqrt (4 * m) := by
    intro beta hbeta0 hbeta1
    have h := abs_cubeAverage_vecDot_cutoffProduct_mesoscopic_le_of_coarse_conversions
      Q s flux u ξ hB hfluxLp hξLp hξsmooth hderiv hs0 hs
      (Ea := Ea) (M := 4 * m) (cP := cP) hEann (cL := cL) hcL
      hGnonneg hNnonneg hgrad hflux hfluc hmean hbeta0 hbeta1
    rwa [hpair] at h
  have hres := mesoscopicCrossPriceEnergyOn_openCubeSet_of_cubeAverage_mass_scaled
    Q a chi u (kappa := (4 : ℝ)) (by norm_num) hbase
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num,
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [hs4] at hres
  exact hres

/-! ## The datum energy at the balanced mesoscopic scale -/

/-- **The datum energy is a dimension-only multiple of the mass, at the balanced
scale.**

With the mesoscopic Dirichlet lift `[g]_{B^{s,+}(Q)} ≤ Clift · side(Q) · T⁻¹ ·
‖u‖_{L̲²(Q)}` (P-222 §2.2) and the balance `λ⁻¹ side(Q)² ≤ T`, the corrector
energy `Ccorr λ⁻¹ [g]²` is at most `(Ccorr Clift²/4) · T⁻¹ · (4 m)`, i.e. the
`Sc t⁻¹ M` slot of `MesoscopicCrossPriceEnergyOn` with a **dimension-only**
`Sc`.  This is the display of P-226 §3 at the scale where it is usable. -/
theorem datum_energy_le_mass_of_balanced_scale
    {Ccorr Clift lamInv side T m G : ℝ}
    (hCcorr : 0 ≤ Ccorr) (hlam : 0 ≤ lamInv)
    (hT : 0 < T) (hm : 0 ≤ m) (hG : 0 ≤ G)
    (hGle : G ≤ Clift * side * (T⁻¹ * Real.sqrt m))
    (hbal : lamInv * side ^ 2 ≤ T) :
    Ccorr * lamInv * G ^ 2 ≤ (Ccorr * Clift ^ 2 / 4) * (T⁻¹ * (4 * m)) := by
  have hsq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm
  have hG2 : G ^ 2 ≤ (Clift * side * (T⁻¹ * Real.sqrt m)) ^ 2 := by
    have h0 : 0 ≤ Clift * side * (T⁻¹ * Real.sqrt m) := le_trans hG hGle
    nlinarith [hG, hGle, h0]
  have hexp : (Clift * side * (T⁻¹ * Real.sqrt m)) ^ 2 =
      Clift ^ 2 * side ^ 2 * (T⁻¹ * T⁻¹) * m := by
    have : (Clift * side * (T⁻¹ * Real.sqrt m)) ^ 2 =
        Clift ^ 2 * side ^ 2 * (T⁻¹ * T⁻¹) * (Real.sqrt m * Real.sqrt m) := by
      ring
    rw [this, hsq]
  have hTinv : 0 < T⁻¹ := inv_pos.mpr hT
  have hkey : lamInv * (Clift ^ 2 * side ^ 2 * (T⁻¹ * T⁻¹) * m) ≤
      Clift ^ 2 * (T⁻¹ * m) := by
    have hstep : lamInv * side ^ 2 * (Clift ^ 2 * (T⁻¹ * T⁻¹) * m) ≤
        T * (Clift ^ 2 * (T⁻¹ * T⁻¹) * m) := by
      refine mul_le_mul_of_nonneg_right hbal ?_
      positivity
    have hTT : T * (Clift ^ 2 * (T⁻¹ * T⁻¹) * m) = Clift ^ 2 * (T⁻¹ * m) := by
      field_simp
    calc
      lamInv * (Clift ^ 2 * side ^ 2 * (T⁻¹ * T⁻¹) * m)
          = lamInv * side ^ 2 * (Clift ^ 2 * (T⁻¹ * T⁻¹) * m) := by ring
      _ ≤ T * (Clift ^ 2 * (T⁻¹ * T⁻¹) * m) := hstep
      _ = Clift ^ 2 * (T⁻¹ * m) := hTT
  have hmain : lamInv * G ^ 2 ≤ Clift ^ 2 * (T⁻¹ * m) := by
    have h1 : lamInv * G ^ 2 ≤ lamInv * (Clift * side * (T⁻¹ * Real.sqrt m)) ^ 2 :=
      mul_le_mul_of_nonneg_left hG2 hlam
    rw [hexp] at h1
    exact le_trans h1 hkey
  have hfinal : Ccorr * (lamInv * G ^ 2) ≤ Ccorr * (Clift ^ 2 * (T⁻¹ * m)) :=
    mul_le_mul_of_nonneg_left hmain hCcorr
  have hrw : (Ccorr * Clift ^ 2 / 4) * (T⁻¹ * (4 * m)) =
      Ccorr * (Clift ^ 2 * (T⁻¹ * m)) := by ring
  rw [hrw]
  calc Ccorr * lamInv * G ^ 2 = Ccorr * (lamInv * G ^ 2) := by ring
    _ ≤ Ccorr * (Clift ^ 2 * (T⁻¹ * m)) := hfinal

/-! ## The flux conversion in the shape the price consumes -/

/-- The scalar flux written componentwise. -/
private theorem matVecMul_scalar_component {a : Vec d → ℝ} {A : CoeffField d}
    (hA : ∀ y, A y = scalarCoeffField a y) (v : Vec d → Vec d) (x : Vec d)
    (i : Fin d) :
    matVecMul (A x) (v x) i = a x * v x i := by
  rw [hA x]
  simp [scalarCoeffField, matVecMul_scalarMatrix]

/-- The scalar flux is in `L²` for the normalized cube measure. -/
theorem memLp_scalar_flux [NeZero d]
    {Q : TriadicCube d} {afam : Ch03.CoeffFamily d} {a : Vec d → ℝ} {lam Lam : ℝ}
    (hA : ∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) ((afam.coeffOn Q).toCoeffField))
    (u : H1Function (openCubeSet Q)) :
    MemLp (fun x : Vec d => (fun i => a x * u.grad x i : Vec d))
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have hguCubeQ : MemVectorL2 (cubeSet Q) u.grad := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using
      u.grad_memVectorL2
  have hEllQ : IsEllipticFieldOn lam Lam (cubeSet Q) (afam.coeffOn Q).toCoeffField :=
    hEll
  have hFmemCube : MemVectorL2 (cubeSet Q)
      (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEllQ hguCubeQ
  have hFmemOpen : MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x)) := by
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] using hFmemCube
  have hFLp : MemLp (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x))
      (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q hFmemOpen
  have hEq : (fun x : Vec d => (fun i => a x * u.grad x i : Vec d))
      = (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x)) := by
    funext x
    funext i
    exact (matVecMul_scalar_component hA u.grad x i).symm
  rw [hEq]
  exact hFLp

/-- **The flux conversion at the balanced mesoscopic scale.**

`sum_circNegativeBesovNorm_flux_le_of_isForcedEquation` (P-226) composed with
the mesoscopic Dirichlet lift and the balance `λ_{s/2,2}⁻¹ side² ≤ T`: the
result is exactly the hypothesis `hflux` of
`mesoscopicCrossPriceEnergyOn_openCubeSet_of_coarse_conversions`, with the
**dimension-only** datum coefficient `Sc = Ccorr(d,s) Clift²/4`. -/
theorem sum_circNegativeBesovNorm_scalar_flux_le_of_balanced_datum [NeZero d]
    {Q : TriadicCube d} {afam : Ch03.CoeffFamily d} {a : Vec d → ℝ} {lam Lam : ℝ}
    (haSymm : ∀ S, Ch02.CoeffOn.IsSymmetric (afam.coeffOn S))
    (hAfam : ∀ S : TriadicCube d,
      (afam.coeffOn S).toCoeffField = (afam.coeffOn Q).toCoeffField)
    (hA : ∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y)
    (hapos : ∀ y, 0 < a y)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) ((afam.coeffOn Q).toCoeffField))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hforced : Ch03.IsForcedEquation Q afam u g)
    (hreg : ∀ (j : ℕ), ∀ R ∈ descendantsAtDepth Q j, Ch03.ForceBesovRegularity R s g)
    (hGlobalBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hlam : ∀ (j : ℕ), ∀ R ∈ descendantsAtDepth Q j,
      (lambdaSq R (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹ ≤
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          (lambdaSq Q (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹)
    {T Clift : ℝ} (hT : 0 < T)
    (huLp : MemLp u.toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hGnn : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g)
    (hdatum : cubeBesovPositiveVectorSeminormTwo Q s g ≤
      Clift * (cubeScaleFactor Q * (|T⁻¹| * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun)))
    (hbal : (lambdaSq Q (s / 2) (.finite 2)
        ((afam.coeffOn Q).toCoeffField))⁻¹ * cubeScaleFactor Q ^ 2 ≤ T) :
    ∑ i : Fin d, Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => a x * u.grad x i) ≤
      ((d : ℝ) * cubeBesovScaleWeight (-s) Q *
          (Ch03.poincareDiscountFactor s (.finite 1) *
            Ch03.poincareUpperEllipticityFactor Q afam s (.finite 1)) *
          Real.sqrt 2) *
        Real.sqrt (cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) +
          (correctorEnergyConstant d s * Clift ^ 2 / 4) *
            (T⁻¹ * (4 * cubeAverage Q (fun x => u.toFun x ^ (2 : ℕ))))) := by
  classical
  have hbase := sum_circNegativeBesovNorm_flux_le_of_isForcedEquation
    haSymm hAfam hA hapos hEll hs0 hs1 hforced hreg hGlobalBdd hlam
  have hcomp : (fun i : Fin d =>
      Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x) i)) =
      fun i : Fin d =>
        Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => a x * u.grad x i) := by
    funext i
    congr 1
    funext x
    exact matVecMul_scalar_component hA u.grad x i
  rw [hcomp] at hbase
  -- the datum energy is dimension-only at the balanced scale
  set lamInv : ℝ := (lambdaSq Q (s / 2) (.finite 2)
    ((afam.coeffOn Q).toCoeffField))⁻¹ with hlamInvDef
  set m : ℝ := cubeAverage Q (fun x => u.toFun x ^ (2 : ℕ)) with hmdef
  have hmnn : 0 ≤ m := by
    rw [hmdef, cubeAverage]
    exact mul_nonneg (inv_pos.mpr (cubeVolume_pos Q)).le
      (setIntegral_nonneg (measurableSet_cubeSet Q) fun x _ ↦ sq_nonneg _)
  have hlamInvNn : 0 ≤ lamInv := by
    rw [hlamInvDef]
    exact inv_nonneg.mpr
      (multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2
        ((afam.coeffOn Q).toCoeffField) (by norm_num) (by linarith))
  have hTinv : |T⁻¹| = T⁻¹ := abs_of_pos (inv_pos.mpr hT)
  have hLp : cubeLpNorm Q (2 : ℝ≥0∞) u.toFun = Real.sqrt m :=
    cubeLpNorm_two_eq_sqrt_cubeAverage_sq Q u.toFun huLp
  have hGle : cubeBesovPositiveVectorSeminormTwo Q s g ≤
      Clift * cubeScaleFactor Q * (T⁻¹ * Real.sqrt m) := by
    have := hdatum
    rw [hTinv, hLp] at this
    calc cubeBesovPositiveVectorSeminormTwo Q s g
        ≤ Clift * (cubeScaleFactor Q * (T⁻¹ * Real.sqrt m)) := this
      _ = Clift * cubeScaleFactor Q * (T⁻¹ * Real.sqrt m) := by ring
  have hdat := datum_energy_le_mass_of_balanced_scale
    (Ccorr := correctorEnergyConstant d s) (Clift := Clift) (lamInv := lamInv)
    (side := cubeScaleFactor Q) (T := T) (m := m)
    (G := cubeBesovPositiveVectorSeminormTwo Q s g)
    (correctorEnergyConstant_nonneg d s) hlamInvNn hT hmnn hGnn hGle hbal
  -- monotonicity of the square root and of the (nonnegative) prefactor
  have hKnn : 0 ≤ (d : ℝ) * cubeBesovScaleWeight (-s) Q *
      (Ch03.poincareDiscountFactor s (.finite 1) *
        Ch03.poincareUpperEllipticityFactor Q afam s (.finite 1)) * Real.sqrt 2 := by
    have h1 : 0 ≤ Ch03.poincareDiscountFactor s (.finite 1) := by
      dsimp [Ch03.poincareDiscountFactor]
      exact Real.rpow_nonneg (geometricDiscount_pos (by linarith : 0 < s * 1)).le _
    have h2 : 0 ≤ Ch03.poincareUpperEllipticityFactor Q afam s (.finite 1) := by
      dsimp [Ch03.poincareUpperEllipticityFactor]
      exact Real.rpow_nonneg
        (Ch02.LambdaSq_finite_nonneg Q afam hs0 (by norm_num : (1 : ℝ) ≤ 1)) _
    have h3 : 0 ≤ cubeBesovScaleWeight (-s) Q := cubeBesovScaleWeight_nonneg (-s) Q
    have h4 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    positivity
  refine hbase.trans (mul_le_mul_of_nonneg_left ?_ hKnn)
  refine Real.sqrt_le_sqrt ?_
  have : correctorEnergyConstant d s * lamInv *
      (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 ≤
      correctorEnergyConstant d s * Clift ^ 2 / 4 * (T⁻¹ * (4 * m)) := hdat
  linarith

/-- The zero field is in vector `L²`. -/
theorem zero_memVectorL2 (U : Set (Vec d)) :
    MemVectorL2 U (fun _ => (0 : Vec d)) := by
  show MeasureTheory.MemLp (fun _ => (0 : Vec d)) 2 (volumeMeasureOn U)
  simp

/-- The zero field is solenoidal.  (Clause 1 of the frozen coarse Poincare
inequality is stated together with clause 2, which needs *some* solenoidal
field; the zero field is the cheapest witness.) -/
theorem zero_isSolenoidalOn (U : Set (Vec d)) :
    IsSolenoidalOn U (fun _ => (0 : Vec d)) := by
  intro φ
  show ∫ x in U, vecDot ((fun _ => (0 : Vec d)) x)
    (φ.toH1Function.grad x) ∂MeasureTheory.volume = 0
  have hdot : ∀ x : Vec d, vecDot ((fun _ => (0 : Vec d)) x)
      (φ.toH1Function.grad x) = 0 := by
    intro x
    show ∑ i, (0 : Vec d) i * φ.toH1Function.grad x i = 0
    simp
  simp [hdot]

/-! ## The gradient conversion in the shape the price consumes -/



theorem sum_circNegativeBesovNorm_grad_le [NeZero d]
    {Q : TriadicCube d} {afam : Ch03.CoeffFamily d} {a : Vec d → ℝ}
    (haSymm : ∀ S, Ch02.CoeffOn.IsSymmetric (afam.coeffOn S))
    (hA : ∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y)
    {s : ℝ} (hs0 : 0 < s)
    (u : H1Function (openCubeSet Q)) :
    ∑ j : Fin d, Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => u.grad x j) ≤
      ((d : ℝ) * cubeBesovScaleWeight (-s) Q *
          (Ch03.poincareDiscountFactor s (.finite 1) *
            Ch03.poincareLowerEllipticityFactor Q afam s (.finite 1))) *
        Real.sqrt (cubeAverage Q (fun x => a x * vecNormSq (u.grad x))) := by
  classical
  have hraw := (SubdiffusiveProcess.Providers.Section2.coarsePoincareRaw Q afam haSymm s hs0
    (.finite 1) (by simp) u (fun _ => (0 : Vec d))
    (zero_memVectorL2 (openCubeSet Q)) (zero_isSolenoidalOn (openCubeSet Q))).1
  have henergy : (∫ x, vecDot (u.grad x)
        (matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x))
        ∂normalizedCubeMeasure Q) =
      cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    show vecDot (u.grad x) (matVecMul ((afam.coeffOn Q).toCoeffField x) (u.grad x)) =
      a x * vecNormSq (u.grad x)
    rw [hA x]
    simp only [scalarCoeffField, matVecMul_scalarMatrix, vecNormSq, vecDot,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [henergy] at hraw
  
  have huNorm : MemLp u.grad (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_openCubeSet Q u.grad_memVectorL2
  have hbdd : BddAbove (Set.range fun N : ℕ =>
      Ch03.negativeBesovVectorPartialNormFinite Q s 1 N u.grad) := by
    simpa [Ch03.negativeBesovVectorPartialNormFinite,
      cubeBesovNegativeVectorPartialSeminorm, Real.rpow_one] using
      cubeBesovNegativeVectorPartialSeminorm_bddAbove_of_memLp Q hs0 u.grad huNorm
  have hcomp : ∀ j : Fin d,
      Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.grad x j) ≤
        cubeBesovScaleWeight (-s) Q *
          Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite 1) u.grad := by
    intro j
    have hb := circNegativeBesovNorm_component_le_paperNegativeBesovVectorNorm
      Q hs0 u.grad j hbdd
    refine hb.trans (le_of_eq ?_)
    have hpaper : SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
        Q s (Ch02.MultiscaleExponent.finite 1) u.grad =
        s * Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite 1) u.grad := by
      simp [SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm,
        Real.rpow_one]
    rw [hpaper]
    field_simp
  have hsum : ∑ j : Fin d,
      Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => u.grad x j) ≤
      (d : ℝ) * (cubeBesovScaleWeight (-s) Q *
        Ch03.scaleNormalizedNegativeBesovVectorNorm Q s (.finite 1) u.grad) := by
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hcomp j)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have hwnn : 0 ≤ cubeBesovScaleWeight (-s) Q := cubeBesovScaleWeight_nonneg (-s) Q
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  refine hsum.trans ?_
  have hstep := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hraw hwnn) hdnn
  refine hstep.trans (le_of_eq ?_)
  ring

/-- The `q = 1` lower-ellipticity prefactor of clause 1 is nonnegative. -/
theorem coarsePoincareLowerConst_nonneg [NeZero d] (Q : TriadicCube d)
    (afam : Ch03.CoeffFamily d) {s : ℝ} (hs0 : 0 < s) :
    0 ≤ (d : ℝ) * cubeBesovScaleWeight (-s) Q *
      (Ch03.poincareDiscountFactor s (.finite 1) *
        Ch03.poincareLowerEllipticityFactor Q afam s (.finite 1)) := by
  have h1 : 0 ≤ Ch03.poincareDiscountFactor s (.finite 1) := by
    dsimp [Ch03.poincareDiscountFactor]
    exact Real.rpow_nonneg (geometricDiscount_pos (by linarith : 0 < s * 1)).le _
  have h2 : 0 ≤ Ch03.poincareLowerEllipticityFactor Q afam s (.finite 1) := by
    dsimp [Ch03.poincareLowerEllipticityFactor]
    exact Real.rpow_nonneg
      (Ch02.lambdaSq_finite_nonneg Q afam hs0 (by norm_num : (1 : ℝ) ≤ 1)) _
  have h3 : 0 ≤ cubeBesovScaleWeight (-s) Q := cubeBesovScaleWeight_nonneg (-s) Q
  have h4 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  positivity

/-- The `q = 1` upper-ellipticity prefactor of the flux clause is
nonnegative. -/
theorem coarsePoincareUpperConst_nonneg [NeZero d] (Q : TriadicCube d)
    (afam : Ch03.CoeffFamily d) {s : ℝ} (hs0 : 0 < s) :
    0 ≤ (d : ℝ) * cubeBesovScaleWeight (-s) Q *
      (Ch03.poincareDiscountFactor s (.finite 1) *
        Ch03.poincareUpperEllipticityFactor Q afam s (.finite 1)) * Real.sqrt 2 := by
  have h1 : 0 ≤ Ch03.poincareDiscountFactor s (.finite 1) := by
    dsimp [Ch03.poincareDiscountFactor]
    exact Real.rpow_nonneg (geometricDiscount_pos (by linarith : 0 < s * 1)).le _
  have h2 : 0 ≤ Ch03.poincareUpperEllipticityFactor Q afam s (.finite 1) := by
    dsimp [Ch03.poincareUpperEllipticityFactor]
    exact Real.rpow_nonneg
      (Ch02.LambdaSq_finite_nonneg Q afam hs0 (by norm_num : (1 : ℝ) ≤ 1)) _
  have h3 : 0 ≤ cubeBesovScaleWeight (-s) Q := cubeBesovScaleWeight_nonneg (-s) Q
  have h4 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  positivity

/-- The Poincare prefactor of the split price is nonnegative. -/
theorem fullVectorPoincareConst_nonneg [NeZero d] (Q : TriadicCube d) :
    0 ≤ Book.Ch01.Legacy.fullVectorPoincareConstant Q *
      (3 : ℝ) ^ ((d : ℝ) + 1) := by
  have h1 := Book.Ch01.Legacy.fullVectorPoincareConstant_nonneg Q
  positivity

/-- **The gradient conversion in the shape `hgrad` consumes**, with the energy
slot relaxed to any upper bound `E` of the cube-average coefficient energy. -/
theorem coarsePoincare_grad_conversion_le [NeZero d]
    {Q : TriadicCube d} {afam : Ch03.CoeffFamily d} {a : Vec d → ℝ}
    (haSymm : ∀ S, Ch02.CoeffOn.IsSymmetric (afam.coeffOn S))
    (hA : ∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y)
    {s : ℝ} (hs0 : 0 < s) (u : H1Function (openCubeSet Q)) {E : ℝ}
    (hE : cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) ≤ E) :
    (Book.Ch01.Legacy.fullVectorPoincareConstant Q *
        (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ∑ j : Fin d, Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => u.grad x j) ≤
      ((Book.Ch01.Legacy.fullVectorPoincareConstant Q *
          (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ((d : ℝ) * cubeBesovScaleWeight (-s) Q *
          (Ch03.poincareDiscountFactor s (.finite 1) *
            Ch03.poincareLowerEllipticityFactor Q afam s (.finite 1)))) *
        Real.sqrt E := by
  have hPoinNn := fullVectorPoincareConst_nonneg (d := d) Q
  have hlowNn := coarsePoincareLowerConst_nonneg Q afam hs0
  have h1 := mul_le_mul_of_nonneg_left
    (sum_circNegativeBesovNorm_grad_le haSymm hA hs0 u) hPoinNn
  have h3 : (Book.Ch01.Legacy.fullVectorPoincareConstant Q *
        (3 : ℝ) ^ ((d : ℝ) + 1)) *
      (((d : ℝ) * cubeBesovScaleWeight (-s) Q *
          (Ch03.poincareDiscountFactor s (.finite 1) *
            Ch03.poincareLowerEllipticityFactor Q afam s (.finite 1))) *
        Real.sqrt (cubeAverage Q (fun x => a x * vecNormSq (u.grad x)))) =
      ((Book.Ch01.Legacy.fullVectorPoincareConstant Q *
          (3 : ℝ) ^ ((d : ℝ) + 1)) *
        ((d : ℝ) * cubeBesovScaleWeight (-s) Q *
          (Ch03.poincareDiscountFactor s (.finite 1) *
            Ch03.poincareLowerEllipticityFactor Q afam s (.finite 1)))) *
        Real.sqrt (cubeAverage Q (fun x => a x * vecNormSq (u.grad x))) := by ring
  rw [h3] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE)
    (mul_nonneg hPoinNn hlowNn))

/-! ## The per-cell price, assembled -/

/-- **The mesoscopic cross-term price on one triadic cell.**

This is the assembly of §§2-4 of this file: the two coarse conversions are
discharged (the gradient one from clause 1 of the frozen coarse Poincare
inequality, the flux one from the flux clause with right-hand side at the
balanced mesoscopic scale), and the bookkeeping of
`mesoscopicCrossPriceEnergyOn_openCubeSet_of_cubeAverage_mass_scaled` turns the
resulting cube-average bound into the literal predicate.

What is left to the caller is exactly the hypothesis package of the *already
landed* flux clause (`hforced`, `hreg`, `hGlobalBdd`, `hlam`), the mesoscopic
Dirichlet lift bound `hdatum` (P-222 `exists_mesoscopic_forced_datum`), the
balance `lambda_{s/2,2}^{-1} side^2 <= T` that makes the datum coefficient
dimension-only, and the regularity of the cutoff test field `xi = chi grad chi`.

The constants are displayed: `cP` of size `lambda^{-1/2}`, `cL` of size
`Lambda^{1/2}`, and the datum coefficient `Sc = Ccorr(d,s) Clift^2 / 4`, which
depends only on `d` and `s`. -/
theorem mesoscopicCrossPriceEnergyOn_openCubeSet_of_massive_datum [NeZero d]
    {Q : TriadicCube d} {afam : Ch03.CoeffFamily d} {a chi : Vec d → ℝ}
    {lam Lam : ℝ}
    (haSymm : ∀ S, Ch02.CoeffOn.IsSymmetric (afam.coeffOn S))
    (hAfam : ∀ S : TriadicCube d,
      (afam.coeffOn S).toCoeffField = (afam.coeffOn Q).toCoeffField)
    (hA : ∀ y, (afam.coeffOn Q).toCoeffField y = scalarCoeffField a y)
    (hapos : ∀ y, 0 < a y)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) ((afam.coeffOn Q).toCoeffField))
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hs3 : 3 * s ≤ 1)
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hforced : Ch03.IsForcedEquation Q afam u g)
    (hreg : ∀ (j : ℕ), ∀ R ∈ descendantsAtDepth Q j, Ch03.ForceBesovRegularity R s g)
    (hGlobalBdd : BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hlam : ∀ (j : ℕ), ∀ R ∈ descendantsAtDepth Q j,
      (lambdaSq R (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹ ≤
        Real.rpow (3 : ℝ) (s * (j : ℝ)) *
          (lambdaSq Q (s / 2) (.finite 2) ((afam.coeffOn Q).toCoeffField))⁻¹)
    {T Clift B : ℝ} (hT : 0 < T)
    (huLp : MemLp u.toFun (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hGnn : 0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g)
    (hdatum : cubeBesovPositiveVectorSeminormTwo Q s g ≤
      Clift * (cubeScaleFactor Q * (|T⁻¹| * cubeLpNorm Q (2 : ℝ≥0∞) u.toFun)))
    (hbal : (lambdaSq Q (s / 2) (.finite 2)
        ((afam.coeffOn Q).toCoeffField))⁻¹ * cubeScaleFactor Q ^ 2 ≤ T)
    (ξ : Vec d → Vec d)
    (hξdef : ξ = fun x => fun i => chi x * (fderiv ℝ chi x) (basisVec i))
    (hB : 0 ≤ B)
    (hξLp : MemLp ξ (∞ : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hξsmooth : ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => ξ x i))
    (hderiv : ∀ i : Fin d, ∀ z ∈ cubeSet Q,
      ‖fderiv ℝ (fun x => ξ x i) z‖ ≤ B)
    (hGnonneg : 0 ≤ (Book.Ch01.Legacy.fullVectorPoincareConstant Q *
        (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ∑ j : Fin d, Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => u.grad x j))
    (hNnonneg : 0 ≤ ∑ i : Fin d,
      Book.Ch01.Legacy.circNegativeBesovNorm Q s (2 : ℝ≥0∞) (1 : ℝ≥0∞)
        (fun x => a x * u.grad x i)) :
    MesoscopicCrossPriceEnergyOn a (openCubeSet Q) (openCubeSet Q) u.toFun u.grad
      chi T
      (2 * ((3 : ℝ) ^ ((d : ℝ) + s) *
        ((d : ℝ) * cubeBesovScaleWeight (-s) Q *
          (Ch03.poincareDiscountFactor s (.finite 1) *
            Ch03.poincareUpperEllipticityFactor Q afam s (.finite 1)) *
          Real.sqrt 2) *
        ((Book.Ch01.Legacy.fullVectorPoincareConstant Q *
            (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((d : ℝ) * cubeBesovScaleWeight (-s) Q *
            (Ch03.poincareDiscountFactor s (.finite 1) *
              Ch03.poincareLowerEllipticityFactor Q afam s (.finite 1)))) *
        (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
          (cubeScaleFactor Q) ^ (1 - 2 * s)))
      (2 * (2 * ((3 : ℝ) ^ ((d : ℝ) + s) *
        ((d : ℝ) * cubeBesovScaleWeight (-s) Q *
          (Ch03.poincareDiscountFactor s (.finite 1) *
            Ch03.poincareUpperEllipticityFactor Q afam s (.finite 1)) *
          Real.sqrt 2) *
        (2 * (2 * cubeScaleFactor Q * B + 3 * cubeLpNorm Q ∞ ξ) *
            cubeBesovScaleWeight s Q +
          cubeBesovScaleWeight s Q *
            (cubeScaleFactor Q * B + cubeLpNorm Q ∞ ξ)))))
      (4 * (correctorEnergyConstant d s * Clift ^ 2 / 4)) := by
  classical
  have haNonneg : ∀ x, 0 ≤ a x := fun x ↦ (hapos x).le
  have hmnn : (0 : ℝ) ≤ cubeAverage Q (fun x => u.toFun x ^ (2 : ℕ)) := by
    rw [cubeAverage]
    exact mul_nonneg (inv_pos.mpr (cubeVolume_pos Q)).le
      (setIntegral_nonneg (measurableSet_cubeSet Q) fun x _ ↦ sq_nonneg _)
  have hEavgnn : (0 : ℝ) ≤ cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) := by
    rw [cubeAverage]
    exact mul_nonneg (inv_pos.mpr (cubeVolume_pos Q)).le
      (setIntegral_nonneg (measurableSet_cubeSet Q) fun x _ ↦
        mul_nonneg (haNonneg x) (vecNormSq_nonneg _))
  have hScnn : (0 : ℝ) ≤ correctorEnergyConstant d s * Clift ^ 2 / 4 := by
    have := correctorEnergyConstant_nonneg d s
    positivity
  have hEale : cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) ≤
      cubeAverage Q (fun x => a x * vecNormSq (u.grad x)) +
        correctorEnergyConstant d s * Clift ^ 2 / 4 *
          (T⁻¹ * (4 * cubeAverage Q (fun x => u.toFun x ^ (2 : ℕ)))) := by
    have h2 : (0 : ℝ) ≤ correctorEnergyConstant d s * Clift ^ 2 / 4 *
        (T⁻¹ * (4 * cubeAverage Q (fun x => u.toFun x ^ (2 : ℕ)))) :=
      mul_nonneg hScnn (mul_nonneg (inv_pos.mpr hT).le (by linarith))
    linarith
  exact mesoscopicCrossPriceEnergyOn_openCubeSet_of_coarse_conversions
    (a := a) (chi := chi) (s := s) (t := T)
    (Sc := correctorEnergyConstant d s * Clift ^ 2 / 4) (B := B)
    (cP := (Book.Ch01.Legacy.fullVectorPoincareConstant Q *
        (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ((d : ℝ) * cubeBesovScaleWeight (-s) Q *
        (Ch03.poincareDiscountFactor s (.finite 1) *
          Ch03.poincareLowerEllipticityFactor Q afam s (.finite 1))))
    (cL := (d : ℝ) * cubeBesovScaleWeight (-s) Q *
      (Ch03.poincareDiscountFactor s (.finite 1) *
        Ch03.poincareUpperEllipticityFactor Q afam s (.finite 1)) * Real.sqrt 2)
    Q u ξ hξdef
    haNonneg hB (memLp_scalar_flux hA hEll u) huLp hξLp hξsmooth hderiv hs0 hs3 hT
    (coarsePoincareUpperConst_nonneg Q afam hs0) hScnn hGnonneg hNnonneg
    (coarsePoincare_grad_conversion_le haSymm hA hs0 u hEale)
    (sum_circNegativeBesovNorm_scalar_flux_le_of_balanced_datum
      haSymm hAfam hA hapos hEll hs0 hs1 hforced hreg hGlobalBdd hlam hT huLp
      hGnn hdatum hbal)

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
