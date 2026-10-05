module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_extremes
public import SubdiffusiveProcess.Paper.lem_load
public import SubdiffusiveProcess.Paper.lem_neumann_error
public import SubdiffusiveProcess.Paper.lem_primitive
public import SubdiffusiveProcess.Paper.smoothed_load_properties
public import SubdiffusiveProcess.Paper.rem_resolved_meshes
public import SubdiffusiveProcess.Paper.rem_resolved_microscopic
public import SubdiffusiveProcess.Paper.rem_resolved_eps_power
public import SubdiffusiveProcess.Paper.aux_macro_moment_bank


@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

private theorem assembled_product_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (p q B : ℝ) (hp : 1 ≤ p) (hqp : 4 * p ≤ q) (hB : 0 ≤ B)
    (X Y : α → ℝ)
    (hX : MemLp X (ENNReal.ofReal q) μ)
    (hY : MemLp Y (ENNReal.ofReal q) μ)
    (hXbd : eLpNorm X (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B)
    (hYbd : eLpNorm Y (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B) :
    MemLp (fun x => X x * Y x) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun x => X x * Y x) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (B * B) := by
  have h2p : 2 * p ≤ q := by linarith
  have hX2 : eLpNorm X (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal B :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal h2p)).trans hXbd
  have hY2 : eLpNorm Y (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal B :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal h2p)).trans hYbd
  have hprod := aux_aux_macro_moment_bank_product_moment μ p X Y hX.aestronglyMeasurable hY.aestronglyMeasurable
  have hbound : eLpNorm (fun x => X x * Y x) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (B * B) := by
    calc
      _ ≤ eLpNorm X (ENNReal.ofReal (2 * p)) μ *
          eLpNorm Y (ENNReal.ofReal (2 * p)) μ := hprod
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal B := mul_le_mul' hX2 hY2
      _ = ENNReal.ofReal (B * B) := (ENNReal.ofReal_mul hB).symm
  exact ⟨hbound.trans_lt ENNReal.ofReal_lt_top, hbound⟩

private theorem assembled_sum_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (q B : ℝ) (hq : 1 ≤ q) (hB : 0 ≤ B)
    (X Y : α → ℝ)
    (hX : MemLp X (ENNReal.ofReal q) μ)
    (hY : MemLp Y (ENNReal.ofReal q) μ)
    (hXbd : eLpNorm X (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B)
    (hYbd : eLpNorm Y (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B) :
    MemLp (X + Y) (ENNReal.ofReal q) μ ∧
      eLpNorm (X + Y) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (2 * B) := by
  have hq' : 1 ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  have hnorm := eLpNorm_add_le (f := X) (g := Y) (μ := μ) hq'
  have hbound : eLpNorm (X + Y) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (2 * B) := by
    calc
      _ ≤ eLpNorm X (ENNReal.ofReal q) μ +
          eLpNorm Y (ENNReal.ofReal q) μ := hnorm
      _ ≤ ENNReal.ofReal B + ENNReal.ofReal B := add_le_add hXbd hYbd
      _ = ENNReal.ofReal (2 * B) := by
        rw [← ENNReal.ofReal_add hB]
        congr 1
        ring
        exact hB
  exact ⟨hX.add hY, hbound⟩

/- The pointwise majorant used by the theorem.  This shape makes the
   two wavelength ranges share one random variable. -/
private def assembledK {d : ℕ}
    (Ahi Bhi Alo Blo Y Kcoerc : ℕ → BilateralField d → ℝ)
    (Cload D : ℝ) : ℕ → BilateralField d → ℝ :=
  fun N omega =>
    ((Ahi N omega + Alo N omega) *
      (2 * Y N omega + 2 * Cload * Kcoerc N omega) +
      (Bhi N omega + Blo N omega) * D ^ 2)

private theorem assembledK_nonneg {d : ℕ}
    (Ahi Bhi Alo Blo Y Kcoerc : ℕ → BilateralField d → ℝ)
    (Cload D : ℝ)
    (hAhi : ∀ N omega, 0 ≤ Ahi N omega)
    (hBhi : ∀ N omega, 0 ≤ Bhi N omega)
    (hAlo : ∀ N omega, 0 ≤ Alo N omega)
    (hBlo : ∀ N omega, 0 ≤ Blo N omega)
    (hY : ∀ N omega, 0 ≤ Y N omega)
    (hK : ∀ N omega, 0 ≤ Kcoerc N omega)
    (hC : 0 ≤ Cload) :
    ∀ N omega, 0 ≤ assembledK Ahi Bhi Alo Blo Y Kcoerc Cload D N omega := by
  intro N omega
  have ha := hAhi N omega
  have hb := hBhi N omega
  have hc := hAlo N omega
  have hd := hBlo N omega
  have hy := hY N omega
  have hk := hK N omega
  dsimp [assembledK]
  positivity

/- This is the final source-cost absorption after the face-bump C^j estimate.
   It is independent of the analytic origin of the gradient estimate. -/
private theorem assembledK_derivative_absorption
    (G K Cj eps r t : ℝ) (jmax : ℕ)
    (hG : G ≤ K * eps ^ (-2 : ℝ) * r ^ t)
    (hK : 0 ≤ K) (hCj : 1 ≤ Cj)
    (heps : 0 < eps) (heps8 : eps < 1 / 8)
    (hr : 0 < r) :
    G ≤ Cj ^ 2 * K * eps ^ (-2 * ((jmax : ℝ) + 1)) * r ^ t := by
  have heps1 : eps ≤ 1 := by linarith
  have hexp : -2 * ((jmax : ℝ) + 1) ≤ (-2 : ℝ) := by
    have : 0 ≤ (jmax : ℝ) := Nat.cast_nonneg _
    linarith
  have hp : eps ^ (-2 : ℝ) ≤ eps ^ (-2 * ((jmax : ℝ) + 1)) :=
    Real.rpow_le_rpow_of_exponent_ge heps heps1 hexp
  have hpow : 1 ≤ Cj ^ 2 := by nlinarith
  have hR : 0 ≤ r ^ t := (Real.rpow_pos_of_pos hr t).le
  have hscale : K * eps ^ (-2 : ℝ) ≤ Cj ^ 2 * K *
      eps ^ (-2 * ((jmax : ℝ) + 1)) := by
    have hp0 : 0 ≤ eps ^ (-2 * ((jmax : ℝ) + 1)) :=
      (Real.rpow_pos_of_pos heps _).le
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hp),
      mul_nonneg (sub_nonneg.mpr hpow) (mul_nonneg hK hp0)]
  calc
    G ≤ K * eps ^ (-2 : ℝ) * r ^ t := hG
    _ ≤ Cj ^ 2 * K * eps ^ (-2 * ((jmax : ℝ) + 1)) * r ^ t :=
      mul_le_mul_of_nonneg_right hscale hR






private lemma aux_energy_comparison {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Q) (v veps : SobolevData Q)
    (Y Cload Kcoerc eps : ℝ)
    (hY : Y = sobolevCoefficientForm a v v)
    (hC : 0 ≤ Cload) (hK : 0 ≤ Kcoerc)
    (heps : 0 < eps) (heps8 : eps < 1 / 8)
    (hdiff : sobolevCoefficientForm a (v - veps) (v - veps) ≤
      Cload * Kcoerc * eps ^ (1 / 2 : ℝ)) :
    sobolevCoefficientForm a veps veps ≤ 2 * Y + 2 * Cload * Kcoerc := by
  have htri := aux_lem_neumann_error_energy_triangle
    (sobolevCoefficientForm a) (sobolevCoefficientForm_symm a)
    (sobolevCoefficientForm_nonneg a) v (v - veps)
  have hveps : sobolevCoefficientForm a veps veps ≤
      2 * sobolevCoefficientForm a v v +
        2 * sobolevCoefficientForm a (v - veps) (v - veps) := by
    simpa only [sub_sub_cancel] using htri
  have heps1 : eps ≤ 1 := by linarith
  have hsqrt : eps ^ (1 / 2 : ℝ) ≤ 1 := by
    calc
      eps ^ (1 / 2 : ℝ) = Real.sqrt eps := by rw [Real.sqrt_eq_rpow]
      _ ≤ 1 := by nlinarith [Real.sq_sqrt heps.le]
  have hprod : Cload * Kcoerc * eps ^ (1 / 2 : ℝ) ≤ Cload * Kcoerc := by
    nlinarith [mul_nonneg hC hK]
  calc
    _ ≤ 2 * sobolevCoefficientForm a v v +
        2 * sobolevCoefficientForm a (v - veps) (v - veps) := hveps
    _ ≤ 2 * Y + 2 * Cload * Kcoerc := by rw [hY]; linarith


private lemma aux_faceBump_sup {d : ℕ} (rho : ℝ → ℝ)
    (hrho : ContDiff ℝ ∞ rho)
    (hsupp : ∀ tau : ℝ, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0)
    (Krho : ℝ) (hKrho : ∀ tau : ℝ, |rho tau| ≤ Krho)
    (p : Fin d → ℝ) (eps : ℝ) (heps : 0 < eps) (heps8 : eps < 1 / 8) :
    ∀ x : SpatialCoordinates d,
      |faceBump rho p eps x| ≤
        (∑ i : Fin d, |p i|) * (2 * Krho) * eps⁻¹ := by
  have h := (smoothed_load_properties d rho hrho hsupp Krho hKrho p eps
    heps heps8).2.1
  simpa only [faceBump, smoothed_neumann_load] using h

private lemma aux_faceBump_aemeasurable {d : ℕ} (rho : ℝ → ℝ)
    (hrho : ContDiff ℝ ∞ rho)
    (hsupp : ∀ tau : ℝ, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0)
    (Krho : ℝ) (hKrho : ∀ tau : ℝ, |rho tau| ≤ Krho)
    (p : Fin d → ℝ) (eps : ℝ) (heps : 0 < eps) (heps8 : eps < 1 / 8) :
    AEMeasurable (faceBump rho p eps)
      (volume.restrict ((unitNeumannCube d : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) := by
  have hc := (smoothed_load_properties d rho hrho hsupp Krho hKrho p eps
    heps heps8).1.continuous
  simpa only [faceBump, smoothed_neumann_load] using! hc.aemeasurable

private lemma aux_gradient_algebra
    (Ahi Bhi Alo Blo Y Cload Kcoerc D eps E G R : ℝ)
    (hAhi : 0 ≤ Ahi) (hBhi : 0 ≤ Bhi)
    (hAlo : 0 ≤ Alo) (hBlo : 0 ≤ Blo)
    (hY : 0 ≤ Y) (hC : 0 ≤ Cload) (hK : 0 ≤ Kcoerc)
    (_hD : 0 ≤ D) (heps : 0 < eps) (heps8 : eps < 1 / 8)
    (hE : E ≤ 2 * Y + 2 * Cload * Kcoerc)
    (hR : 0 ≤ R)
    (hG : G ≤ (Ahi * E + Bhi * (D * eps⁻¹) ^ 2) * R ∨
      G ≤ (Alo * E + Blo * (D * eps⁻¹) ^ 2) * R) :
    G ≤ ((Ahi + Alo) * (2 * Y + 2 * Cload * Kcoerc) +
      (Bhi + Blo) * D ^ 2) * eps ^ (-2 : ℝ) * R := by
  have hi : 1 ≤ eps⁻¹ := by
    apply (one_le_inv_iff₀).2
    constructor
    · exact heps
    · linarith
  have hP : 1 ≤ eps⁻¹ * eps⁻¹ := by nlinarith
  have hE0 : 0 ≤ 2 * Y + 2 * Cload * Kcoerc := by positivity
  have hP_eq : eps⁻¹ * eps⁻¹ = eps ^ (-2 : ℝ) := by
    rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg heps.le, Real.rpow_natCast]
    ring
  have hsource : (D * eps⁻¹) ^ 2 = D ^ 2 * (eps⁻¹ * eps⁻¹) := by ring
  have hbound (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
      (hAle : A ≤ Ahi + Alo) (hBle : B ≤ Bhi + Blo)
      (h : G ≤ (A * E + B * (D * eps⁻¹) ^ 2) * R) :
      G ≤ ((Ahi + Alo) * (2 * Y + 2 * Cload * Kcoerc) +
        (Bhi + Blo) * D ^ 2) * eps ^ (-2 : ℝ) * R := by
    let T := 2 * Y + 2 * Cload * Kcoerc
    let P := eps⁻¹ * eps⁻¹
    have hAT : A * E ≤ A * T := mul_le_mul_of_nonneg_left hE hA
    have hAT' : A * T ≤ (Ahi + Alo) * T :=
      mul_le_mul_of_nonneg_right hAle hE0
    have hAT0 : 0 ≤ (Ahi + Alo) * T :=
      mul_nonneg (add_nonneg hAhi hAlo) hE0
    have hAT'' : (Ahi + Alo) * T ≤ (Ahi + Alo) * T * P := by
      nlinarith [mul_nonneg hAT0 (sub_nonneg.mpr hP)]
    have hB : B * D ^ 2 ≤ (Bhi + Blo) * D ^ 2 :=
      mul_le_mul_of_nonneg_right hBle (sq_nonneg D)
    have hBP : B * D ^ 2 * P ≤ (Bhi + Blo) * D ^ 2 * P :=
      mul_le_mul_of_nonneg_right hB (le_trans zero_le_one hP)
    have hcoef : A * E + B * (D * eps⁻¹) ^ 2 ≤
        ((Ahi + Alo) * T + (Bhi + Blo) * D ^ 2) * P := by
      rw [hsource]
      nlinarith [hAT, hAT', hAT'', hBP]
    have hscaled := mul_le_mul_of_nonneg_right hcoef hR
    calc
      G ≤ (A * E + B * (D * eps⁻¹) ^ 2) * R := h
      _ ≤ ((Ahi + Alo) * T + (Bhi + Blo) * D ^ 2) * P * R := by
        simpa only [mul_assoc] using hscaled
      _ = _ := by dsimp [T, P]; rw [hP_eq]
  rcases hG with hh | hl
  · exact hbound Ahi Bhi hAhi hBhi (by linarith) (by linarith) hh
  · exact hbound Alo Blo hAlo hBlo (by linarith) (by linarith) hl

private lemma aux_two_range_gradient {d : ℕ}
    (rho : ℝ → ℝ) (p : Fin d → ℝ)
    (N : ℕ) (_omega : BilateralField d)
    (a : PositiveCoefficient (unitNeumannCube d))
    (u : meanZeroSobolevGraph (unitNeumannCube d))
    (t Ahi Bhi Alo Blo Y Cload Kcoerc D eps : ℝ)
    (hAhi : 0 ≤ Ahi) (hBhi : 0 ≤ Bhi)
    (hAlo : 0 ≤ Alo) (hBlo : 0 ≤ Blo)
    (hY : 0 ≤ Y) (hC : 0 ≤ Cload) (hK : 0 ≤ Kcoerc)
    (hD : 0 ≤ D) (heps : 0 < eps) (heps8 : eps < 1 / 8)
    (hsource : AEMeasurable (faceBump rho p eps)
      (volume.restrict ((unitNeumannCube d : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))))
    (hface : ∀ x : SpatialCoordinates d,
      |faceBump rho p eps x| ≤ D * eps⁻¹)
    (hsolve : SolvesNeumann a (faceBump rho p eps) u)
    (hE : sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d))
      (u : SobolevData (unitNeumannCube d)) ≤ 2 * Y + 2 * Cload * Kcoerc)
    (hmacro : ∀ f : SpatialCoordinates d → ℝ,
      AEMeasurable f (volume.restrict ((unitNeumannCube d : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) →
      ∀ Kf : ℝ, 0 ≤ Kf →
      (∀ᵐ y ∂volume.restrict ((unitNeumannCube d : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      ∀ w : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f w →
      ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
      ∀ r : ℝ, 0 < r → r ≤ 1 → (3 : ℝ)^(-(N : ℤ)) ≤ r →
        localGradientEnergy a
          (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
          (sobolevGradient (w : SobolevData (unitNeumannCube d))) ≤
          (Ahi * sobolevCoefficientForm a (w : SobolevData (unitNeumannCube d))
              (w : SobolevData (unitNeumannCube d)) + Bhi * Kf ^ 2) * r ^ t)
    (hmicro : ∀ f : SpatialCoordinates d → ℝ,
      AEMeasurable f (volume.restrict ((unitNeumannCube d : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) →
      ∀ Kf : ℝ, 0 ≤ Kf →
      (∀ᵐ y ∂volume.restrict ((unitNeumannCube d : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      ∀ w : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f w →
      ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
      ∀ r : ℝ, 0 < r → r ≤ min ((3 : ℝ)^(-(N : ℤ))) 1 →
        localGradientEnergy a
          (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
          (sobolevGradient (w : SobolevData (unitNeumannCube d))) ≤
          (Alo * sobolevCoefficientForm a (w : SobolevData (unitNeumannCube d))
              (w : SobolevData (unitNeumannCube d)) + Blo * Kf ^ 2) * r ^ t) :
    ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        localGradientEnergy a
          (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
          ((Ahi + Alo) * (2 * Y + 2 * Cload * Kcoerc) +
            (Bhi + Blo) * D ^ 2) * eps ^ (-2 : ℝ) * r ^ t := by
  intro x hx r hr hr1
  have hKf : 0 ≤ D * eps⁻¹ := mul_nonneg hD (inv_nonneg.mpr heps.le)
  have hface_ae : ∀ᵐ y ∂volume.restrict
      ((unitNeumannCube d : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
      |faceBump rho p eps y| ≤ D * eps⁻¹ := Filter.Eventually.of_forall hface
  have hR : 0 ≤ r ^ t := (Real.rpow_pos_of_pos hr t).le
  apply aux_gradient_algebra Ahi Bhi Alo Blo Y Cload Kcoerc D eps
    (sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d))
      (u : SobolevData (unitNeumannCube d)))
    (localGradientEnergy a
      (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      (sobolevGradient (u : SobolevData (unitNeumannCube d))))
    (r ^ t) hAhi hBhi hAlo hBlo hY hC hK hD heps heps8 hE hR
  by_cases hbig : (3 : ℝ)^(-(N : ℤ)) ≤ r
  · exact Or.inl (hmacro _ hsource _ hKf hface_ae _ hsolve x hx r hr hr1 hbig)
  · apply Or.inr
    have hsmall : r ≤ min ((3 : ℝ)^(-(N : ℤ))) 1 := by
      apply le_min
      · exact le_of_lt (lt_of_not_ge hbig)
      · exact hr1
    exact hmicro _ hsource _ hKf hface_ae _ hsolve x hx r hr hsmall


private lemma aux_product_moment_from_bank {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (p q B : ℝ) (hp : 1 ≤ p) (hqp : 4 * p ≤ q) (hB : 0 ≤ B)
    (X Y : α → ℝ)
    (hX : MemLp X (ENNReal.ofReal q) μ)
    (hY : MemLp Y (ENNReal.ofReal q) μ)
    (hXbd : eLpNorm X (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B)
    (hYbd : eLpNorm Y (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B) :
    MemLp (fun x => X x * Y x) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun x => X x * Y x) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (B * B) := by
  have h2p : 2 * p ≤ q := by linarith
  have hX2 : eLpNorm X (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal B :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal h2p)).trans hXbd
  have hY2 : eLpNorm Y (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal B :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal h2p)).trans hYbd
  have hprod := aux_aux_macro_moment_bank_product_moment μ p X Y hX.aestronglyMeasurable hY.aestronglyMeasurable
  have hbound : eLpNorm (fun x => X x * Y x) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (B * B) := by
    calc
      _ ≤ eLpNorm X (ENNReal.ofReal (2 * p)) μ *
          eLpNorm Y (ENNReal.ofReal (2 * p)) μ := hprod
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal B := mul_le_mul' hX2 hY2
      _ = ENNReal.ofReal (B * B) := (ENNReal.ofReal_mul hB).symm
  exact ⟨hbound.trans_lt ENNReal.ofReal_lt_top, hbound⟩

private lemma aux_two_product_moment_from_bank {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (p q B : ℝ) (hp : 1 ≤ p) (hqp : 4 * p ≤ q) (hB : 0 ≤ B)
    (X Y U V : α → ℝ)
    (hX : MemLp X (ENNReal.ofReal q) μ)
    (hY : MemLp Y (ENNReal.ofReal q) μ)
    (hU : MemLp U (ENNReal.ofReal q) μ)
    (hV : MemLp V (ENNReal.ofReal q) μ)
    (hXbd : eLpNorm X (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B)
    (hYbd : eLpNorm Y (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B)
    (hUbd : eLpNorm U (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B)
    (hVbd : eLpNorm V (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B) :
    MemLp (fun x => X x * Y x + U x * V x) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun x => X x * Y x + U x * V x) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (2 * B * B) := by
  obtain ⟨hXY, hXYbd⟩ := aux_product_moment_from_bank μ p q B hp hqp hB
    X Y hX hY hXbd hYbd
  obtain ⟨hUV, hUVbd⟩ := aux_product_moment_from_bank μ p q B hp hqp hB
    U V hU hV hUbd hVbd
  have hp' : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hsum : eLpNorm (fun x => X x * Y x + U x * V x)
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (2 * B * B) := by
    calc
      _ ≤ eLpNorm (fun x => X x * Y x) (ENNReal.ofReal p) μ +
          eLpNorm (fun x => U x * V x) (ENNReal.ofReal p) μ :=
        eLpNorm_add_le hp'
      _ ≤ ENNReal.ofReal (B * B) + ENNReal.ofReal (B * B) :=
        add_le_add hXYbd hUVbd
      _ = ENNReal.ofReal (2 * B * B) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hB hB)]
        congr 1
        ring
        all_goals positivity
  exact ⟨hXY.add hUV, hsum⟩


private theorem norm_product {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (p q U V : ℝ) (hp : 1 ≤ p) (hqp : 4 * p ≤ q)
    (hU : 0 ≤ U) (_hV : 0 ≤ V) (X Y : α → ℝ)
    (hX : MemLp X (ENNReal.ofReal q) μ)
    (hY : MemLp Y (ENNReal.ofReal q) μ)
    (hXbd : eLpNorm X (ENNReal.ofReal q) μ ≤ ENNReal.ofReal U)
    (hYbd : eLpNorm Y (ENNReal.ofReal q) μ ≤ ENNReal.ofReal V) :
    MemLp (fun x => X x * Y x) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun x => X x * Y x) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (U * V) := by
  have h2p : 2 * p ≤ q := by linarith
  have hX2 : eLpNorm X (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal U :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal h2p)).trans hXbd
  have hY2 : eLpNorm Y (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal V :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal h2p)).trans hYbd
  have hprod := aux_aux_macro_moment_bank_product_moment μ p X Y hX.aestronglyMeasurable hY.aestronglyMeasurable
  have hbound : eLpNorm (fun x => X x * Y x) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (U * V) := by
    calc
      _ ≤ eLpNorm X (ENNReal.ofReal (2 * p)) μ *
          eLpNorm Y (ENNReal.ofReal (2 * p)) μ := hprod
      _ ≤ ENNReal.ofReal U * ENNReal.ofReal V := mul_le_mul' hX2 hY2
      _ = ENNReal.ofReal (U * V) := (ENNReal.ofReal_mul hU).symm
  exact ⟨hbound.trans_lt ENNReal.ofReal_lt_top, hbound⟩

private theorem norm_sum {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (q U V : ℝ) (hq : 1 ≤ q) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (X Y : α → ℝ)
    (hX : MemLp X (ENNReal.ofReal q) μ)
    (hY : MemLp Y (ENNReal.ofReal q) μ)
    (hXbd : eLpNorm X (ENNReal.ofReal q) μ ≤ ENNReal.ofReal U)
    (hYbd : eLpNorm Y (ENNReal.ofReal q) μ ≤ ENNReal.ofReal V) :
    MemLp (X + Y) (ENNReal.ofReal q) μ ∧
      eLpNorm (X + Y) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (U + V) := by
  have hq' : 1 ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  have hbound : eLpNorm (X + Y) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (U + V) := by
    calc
      _ ≤ eLpNorm X (ENNReal.ofReal q) μ + eLpNorm Y (ENNReal.ofReal q) μ :=
        eLpNorm_add_le hq'
      _ ≤ ENNReal.ofReal U + ENNReal.ofReal V := add_le_add hXbd hYbd
      _ = ENNReal.ofReal (U + V) := (ENNReal.ofReal_add hU hV).symm
  exact ⟨hX.add hY, hbound⟩

private theorem norm_scale {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (q c U : ℝ) (hc : 0 ≤ c) (_hU : 0 ≤ U)
    (X : α → ℝ) (hX : MemLp X (ENNReal.ofReal q) μ)
    (hXbd : eLpNorm X (ENNReal.ofReal q) μ ≤ ENNReal.ofReal U) :
    MemLp (fun x => c * X x) (ENNReal.ofReal q) μ ∧
      eLpNorm (fun x => c * X x) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (c * U) := by
  have heq : (fun x => c * X x) = c • X := rfl
  rw [heq]
  refine ⟨hX.const_smul c, ?_⟩
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
  calc
    ENNReal.ofReal c * eLpNorm X (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal c * ENNReal.ofReal U := mul_le_mul' le_rfl hXbd
    _ = ENNReal.ofReal (c * U) := (ENNReal.ofReal_mul hc).symm

theorem aux_smoothed_neumann_source_scaling_scalar_norm {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (p q B C D : ℝ) (hp : 1 ≤ p) (hqp : 4 * p ≤ q)
    (hB : 1 ≤ B) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (Ahi Alo Bhi Blo Y Kcoerc : α → ℝ)
    (hAhi : MemLp Ahi (ENNReal.ofReal q) μ)
    (hAlo : MemLp Alo (ENNReal.ofReal q) μ)
    (hBhi : MemLp Bhi (ENNReal.ofReal q) μ)
    (hBlo : MemLp Blo (ENNReal.ofReal q) μ)
    (hY : MemLp Y (ENNReal.ofReal q) μ)
    (hKc : MemLp Kcoerc (ENNReal.ofReal q) μ)
    (hAhibd : eLpNorm Ahi (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B)
    (hAlobd : eLpNorm Alo (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B)
    (hBhibd : eLpNorm Bhi (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B)
    (hBlobd : eLpNorm Blo (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B)
    (hYbd : eLpNorm Y (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B)
    (hKcbd : eLpNorm Kcoerc (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B) :
    MemLp (fun x => (Ahi x + Alo x) * (2 * Y x + 2 * C * Kcoerc x) +
        (Bhi x + Blo x) * D ^ 2) (ENNReal.ofReal p) μ ∧
      eLpNorm (fun x => (Ahi x + Alo x) * (2 * Y x + 2 * C * Kcoerc x) +
        (Bhi x + Blo x) * D ^ 2) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (4 * B ^ 2 + 4 * C * B ^ 2 + 2 * D ^ 2 * B) := by
  have hB0 : 0 ≤ B := by linarith
  have hq : 1 ≤ q := by linarith
  have hpq : p ≤ q := by linarith
  obtain ⟨hA, hAbd⟩ := norm_sum μ q B B hq hB0 hB0 Ahi Alo hAhi hAlo hAhibd hAlobd
  obtain ⟨hBB, hBBbd⟩ := norm_sum μ q B B hq hB0 hB0 Bhi Blo hBhi hBlo hBhibd hBlobd
  obtain ⟨h2Y, h2Ybd⟩ := norm_scale μ q 2 B (by norm_num) hB0 Y hY hYbd
  obtain ⟨h2CK, h2CKbd⟩ := norm_scale μ q (2 * C) B (by positivity) hB0
    Kcoerc hKc hKcbd
  have hYsum : MemLp (fun x => 2 * Y x + 2 * C * Kcoerc x)
      (ENNReal.ofReal q) μ ∧
      eLpNorm (fun x => 2 * Y x + 2 * C * Kcoerc x)
        (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (2 * B + 2 * C * B) := by
    convert norm_sum μ q (2 * B) (2 * C * B) hq (by positivity) (by positivity)
      (fun x => 2 * Y x) (fun x => (2 * C) * Kcoerc x)
      h2Y h2CK h2Ybd h2CKbd using 1
  obtain ⟨hAY, hAYbd⟩ := norm_product μ p q (B + B) (2 * B + 2 * C * B)
    hp hqp (by positivity) (by positivity) (Ahi + Alo)
    (fun x => 2 * Y x + 2 * C * Kcoerc x) hA hYsum.1 hAbd hYsum.2
  have hBBp : MemLp (Bhi + Blo) (ENNReal.ofReal p) μ :=
    hBB.mono_exponent (ENNReal.ofReal_le_ofReal hpq)
  have hBBpbd : eLpNorm (Bhi + Blo) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (B + B) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq)).trans hBBbd
  obtain ⟨hBD, hBDbd⟩ := norm_scale μ p (D ^ 2) (B + B)
    (by positivity) (by positivity) (Bhi + Blo) hBBp hBBpbd
  have hfun : (fun x => (Bhi x + Blo x) * D ^ 2) =
      (fun x => D ^ 2 * (Bhi + Blo) x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  have hBD' : MemLp (fun x => (Bhi x + Blo x) * D ^ 2)
      (ENNReal.ofReal p) μ := by
    rw [hfun]
    exact hBD
  have hBDbd' : eLpNorm (fun x => (Bhi x + Blo x) * D ^ 2)
      (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (D ^ 2 * (B + B)) := by
    rw [hfun]
    exact hBDbd
  have hp' : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp
  have hbound : eLpNorm (fun x => (Ahi x + Alo x) *
      (2 * Y x + 2 * C * Kcoerc x) + (Bhi x + Blo x) * D ^ 2)
      (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (4 * B ^ 2 + 4 * C * B ^ 2 + 2 * D ^ 2 * B) := by
    calc
      _ ≤ eLpNorm (fun x => (Ahi x + Alo x) * (2 * Y x + 2 * C * Kcoerc x))
            (ENNReal.ofReal p) μ +
          eLpNorm (fun x => (Bhi x + Blo x) * D ^ 2) (ENNReal.ofReal p) μ :=
        eLpNorm_add_le hp'
      _ ≤ ENNReal.ofReal ((B + B) * (2 * B + 2 * C * B)) +
          ENNReal.ofReal (D ^ 2 * (B + B)) := add_le_add hAYbd hBDbd'
      _ = ENNReal.ofReal (4 * B ^ 2 + 4 * C * B ^ 2 + 2 * D ^ 2 * B) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  exact ⟨hAY.add hBD', hbound⟩

/-- Every derivative of a smooth profile supported in `(1,2)` is globally bounded. -/
theorem aux_smoothed_neumann_source_scaling_rho_deriv_bound
    (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hsupp : ∀ tau : ℝ, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |iteratedDeriv n rho t| ≤ M := by
  have hcs : HasCompactSupport rho :=
    HasCompactSupport.intro isCompact_Icc
      (fun t ht => hsupp t (fun h => ht (Ioo_subset_Icc_self h)))
  have hcont : Continuous (iteratedFDeriv ℝ n rho) :=
    hrho.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (hcs.iteratedFDeriv n)
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  have h := hC t
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

/-- One-dimensional affine scaling: `|(d/dt)^n rho(a + b t)| ≤ |b|^n · sup|rho^{(n)}|`. -/
theorem aux_smoothed_neumann_source_scaling_affine_deriv
    (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho) (n : ℕ) (M : ℝ)
    (hM : ∀ t : ℝ, |iteratedDeriv n rho t| ≤ M) (a b t : ℝ) :
    |iteratedDeriv n (fun s : ℝ => rho (a + b * s)) t| ≤ |b| ^ n * M := by
  have hshift : ContDiff ℝ n (fun s : ℝ => rho (a + s)) :=
    (hrho.comp (contDiff_const.add contDiff_id)).of_le (by exact_mod_cast le_top)
  have h1 := iteratedDeriv_comp_const_mul hshift b
  have h2 := iteratedDeriv_comp_const_add n rho a
  have hfun : (fun s : ℝ => rho (a + b * s)) =
      (fun s : ℝ => (fun u : ℝ => rho (a + u)) (b * s)) := rfl
  rw [hfun, h1]
  simp only
  rw [h2, abs_mul, abs_pow]
  exact mul_le_mul_of_nonneg_left (hM _) (pow_nonneg (abs_nonneg b) n)

/-- The one-dimensional profile of the `i`-th face-bump summand. -/
theorem aux_smoothed_neumann_source_scaling_profile_deriv
    (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho) (n : ℕ) (M : ℝ)
    (hM : ∀ t : ℝ, |iteratedDeriv n rho t| ≤ M) (c eps : ℝ) (heps : 0 < eps)
    (t : ℝ) :
    |iteratedDeriv n
        (fun s : ℝ => c * (eps⁻¹ * rho ((1 - s) / eps) - eps⁻¹ * rho (s / eps))) t| ≤
      |c| * (2 * M) * eps⁻¹ ^ (n + 1) := by
  have hA : (fun s : ℝ => rho ((1 - s) / eps)) =
      (fun s : ℝ => rho (eps⁻¹ + (-eps⁻¹) * s)) := by
    funext s; congr 1; ring
  have hB : (fun s : ℝ => rho (s / eps)) =
      (fun s : ℝ => rho (0 + eps⁻¹ * s)) := by
    funext s; congr 1; ring
  have hAc : ContDiff ℝ ∞ (fun s : ℝ => rho ((1 - s) / eps)) :=
    hrho.comp ((contDiff_const.sub contDiff_id).div_const eps)
  have hBc : ContDiff ℝ ∞ (fun s : ℝ => rho (s / eps)) :=
    hrho.comp (contDiff_id.div_const eps)
  have hn : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_top
  have hA' : ContDiffAt ℝ n (fun s : ℝ => eps⁻¹ * rho ((1 - s) / eps)) t :=
    ((contDiff_const.mul hAc).of_le hn).contDiffAt
  have hB' : ContDiffAt ℝ n (fun s : ℝ => eps⁻¹ * rho (s / eps)) t :=
    ((contDiff_const.mul hBc).of_le hn).contDiffAt
  have hAB : ContDiffAt ℝ n
      (fun s : ℝ => eps⁻¹ * rho ((1 - s) / eps) - eps⁻¹ * rho (s / eps)) t :=
    hA'.sub hB'
  rw [iteratedDeriv_const_mul c hAB]
  have hsub : iteratedDeriv n
      (fun s : ℝ => eps⁻¹ * rho ((1 - s) / eps) - eps⁻¹ * rho (s / eps)) t =
      iteratedDeriv n (fun s : ℝ => eps⁻¹ * rho ((1 - s) / eps)) t -
        iteratedDeriv n (fun s : ℝ => eps⁻¹ * rho (s / eps)) t :=
    iteratedDeriv_sub (f := fun s : ℝ => eps⁻¹ * rho ((1 - s) / eps))
      (g := fun s : ℝ => eps⁻¹ * rho (s / eps)) hA' hB'
  rw [hsub, iteratedDeriv_const_mul eps⁻¹ (hAc.of_le hn).contDiffAt,
    iteratedDeriv_const_mul eps⁻¹ (hBc.of_le hn).contDiffAt, hA, hB]
  have hbA := aux_smoothed_neumann_source_scaling_affine_deriv rho hrho n M hM
    eps⁻¹ (-eps⁻¹) t
  have hbB := aux_smoothed_neumann_source_scaling_affine_deriv rho hrho n M hM
    0 eps⁻¹ t
  have hinv : 0 < eps⁻¹ := inv_pos.mpr heps
  rw [abs_neg, abs_of_pos hinv] at hbA
  rw [abs_of_pos hinv] at hbB
  rw [abs_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  calc
    |eps⁻¹ * iteratedDeriv n (fun s : ℝ => rho (eps⁻¹ + -eps⁻¹ * s)) t -
        eps⁻¹ * iteratedDeriv n (fun s : ℝ => rho (0 + eps⁻¹ * s)) t|
        ≤ |eps⁻¹ * iteratedDeriv n (fun s : ℝ => rho (eps⁻¹ + -eps⁻¹ * s)) t| +
          |eps⁻¹ * iteratedDeriv n (fun s : ℝ => rho (0 + eps⁻¹ * s)) t| :=
          abs_sub _ _
    _ = eps⁻¹ * |iteratedDeriv n (fun s : ℝ => rho (eps⁻¹ + -eps⁻¹ * s)) t| +
          eps⁻¹ * |iteratedDeriv n (fun s : ℝ => rho (0 + eps⁻¹ * s)) t| := by
          rw [abs_mul, abs_mul, abs_of_pos hinv]
    _ ≤ eps⁻¹ * (eps⁻¹ ^ n * M) + eps⁻¹ * (eps⁻¹ ^ n * M) :=
          add_le_add (mul_le_mul_of_nonneg_left hbA hinv.le)
            (mul_le_mul_of_nonneg_left hbB hinv.le)
    _ = 2 * M * eps⁻¹ ^ (n + 1) := by ring

/-- Explicit all-orders bound: for every `x` and every `eps > 0`,
`‖D^n f_eps(x)‖ ≤ (∑ |p_i|) · 2 sup|rho^{(n)}| · eps^{-(n+1)}`. -/
theorem aux_smoothed_neumann_source_scaling_facebump_deriv
    {d : ℕ} (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho) (n : ℕ) (M : ℝ)
    (hM : ∀ t : ℝ, |iteratedDeriv n rho t| ≤ M) (p : Fin d → ℝ) (eps : ℝ)
    (heps : 0 < eps) (x : SpatialCoordinates d) :
    ‖iteratedFDeriv ℝ n (faceBump rho p eps) x‖ ≤
      (∑ i : Fin d, |p i|) * (2 * M) * eps⁻¹ ^ (n + 1) := by
  classical
  set h : Fin d → ℝ → ℝ := fun i s =>
    p i * (eps⁻¹ * rho ((1 - s) / eps) - eps⁻¹ * rho (s / eps)) with hh
  set L : Fin d → (SpatialCoordinates d →L[ℝ] ℝ) := fun i =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i with hL
  have hsmooth : ∀ i, ContDiff ℝ ∞ (h i) := fun i =>
    contDiff_const.mul
      ((contDiff_const.mul (hrho.comp ((contDiff_const.sub contDiff_id).div_const eps))).sub
        (contDiff_const.mul (hrho.comp (contDiff_id.div_const eps))))
  have hn : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast le_top
  have hfb : faceBump rho p eps = fun y : SpatialCoordinates d =>
      ∑ i : Fin d, (h i ∘ L i) y := by
    funext y; rfl
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)), ContDiff ℝ n (h i ∘ L i) :=
    fun i _ => ((hsmooth i).comp (L i).contDiff).of_le hn
  rw [hfb, iteratedFDeriv_sum hterm, Finset.sum_apply, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hLn : ‖L i‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun y => by
      simpa [hL] using norm_le_pi_norm y i)
  rw [(L i).iteratedFDeriv_comp_right (hsmooth i) x hn]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _k : Fin n, ‖L i‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hLn)
  have hprof := aux_smoothed_neumann_source_scaling_profile_deriv rho hrho n M hM
    (p i) eps heps (L i x)
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hprof
  calc
    ‖iteratedFDeriv ℝ n (h i) (L i x)‖ * ∏ _k : Fin n, ‖L i‖
        ≤ ‖iteratedFDeriv ℝ n (h i) (L i x)‖ * 1 :=
          mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ ≤ |p i| * (2 * M) * eps⁻¹ ^ (n + 1) := by rw [mul_one]; exact hprof

/-- Uniform-in-`eps` form with a monotone constant: one `C0 ≥ 1`, chosen before
`eps`, `j`, `x`, such that every `Cj ≥ C0` satisfies the derivative clause.
Only smoothness and the support condition of `rho` are used; `pvec` is arbitrary
and `x` ranges over all of space. -/
theorem aux_smoothed_neumann_source_scaling_facebump_uniform_mono
    (d : ℕ) (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (hsupp : ∀ tau : ℝ, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0)
    (pvec : Fin d → ℝ) (jmax : ℕ) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ Cj : ℝ, C0 ≤ Cj →
      ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
        ∀ j : ℕ, j ≤ jmax →
        ∀ x : SpatialCoordinates d,
          ‖iteratedFDeriv ℝ j (faceBump rho pvec eps) x‖ ≤
            Cj * eps ^ (-((jmax : ℝ) + 1)) := by
  choose M hM0 hM using aux_smoothed_neumann_source_scaling_rho_deriv_bound rho hrho hsupp
  set S : ℝ := ∑ i : Fin d, |pvec i| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨1 + ∑ n ∈ Finset.range (jmax + 1), S * (2 * M n), ?_, ?_⟩
  · have : 0 ≤ ∑ n ∈ Finset.range (jmax + 1), S * (2 * M n) :=
      Finset.sum_nonneg (fun n _ => mul_nonneg hS0 (mul_nonneg zero_le_two (hM0 n)))
    linarith
  intro Cj hCj eps heps heps8 j hj x
  have hinv1 : 1 ≤ eps⁻¹ := by
    rw [one_le_inv₀ heps]; linarith
  have hpow : eps⁻¹ ^ (j + 1) ≤ eps⁻¹ ^ (jmax + 1) :=
    pow_le_pow_right₀ hinv1 (Nat.succ_le_succ hj)
  have hrpow : eps ^ (-((jmax : ℝ) + 1)) = eps⁻¹ ^ (jmax + 1) := by
    rw [Real.rpow_neg heps.le, inv_pow]
    congr 1
    exact_mod_cast Real.rpow_natCast eps (jmax + 1)
  rw [hrpow]
  have hbound := aux_smoothed_neumann_source_scaling_facebump_deriv rho hrho j (M j)
    (hM j) pvec eps heps x
  have hterm : S * (2 * M j) ≤ Cj := by
    have := Finset.single_le_sum
      (f := fun n => S * (2 * M n))
      (fun n _ => mul_nonneg hS0 (mul_nonneg zero_le_two (hM0 n)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    linarith
  have hpos : 0 ≤ S * (2 * M j) := mul_nonneg hS0 (mul_nonneg zero_le_two (hM0 j))
  calc
    ‖iteratedFDeriv ℝ j (faceBump rho pvec eps) x‖
        ≤ S * (2 * M j) * eps⁻¹ ^ (j + 1) := hbound
    _ ≤ S * (2 * M j) * eps⁻¹ ^ (jmax + 1) := mul_le_mul_of_nonneg_left hpow hpos
    _ ≤ Cj * eps⁻¹ ^ (jmax + 1) :=
          mul_le_mul_of_nonneg_right hterm (pow_nonneg (inv_nonneg.mpr heps.le) _)

/-- The first half of the third conclusion of `smoothed_neumann_source_scaling`,
in its exact form, under the hypotheses on `rho` and `pvec`
(only smoothness and the support condition are used). -/
theorem aux_smoothed_neumann_source_scaling_facebump_uniform
    (d : ℕ) (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho)
    (_hrho_nonneg : ∀ tau : ℝ, 0 ≤ rho tau)
    (hsupp : ∀ tau : ℝ, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0)
    (_hint : (∫ tau, rho tau) = 1)
    (pvec : Fin d → ℝ) (_hp : (∑ i : Fin d, (pvec i) ^ 2) = 1) :
    ∀ jmax : ℕ, ∃ Cj : ℝ, 1 ≤ Cj ∧
      (∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
        ∀ j : ℕ, j ≤ jmax →
        ∀ x : SpatialCoordinates d,
          x ∈ closure (unitNeumannCube d : Set (SpatialCoordinates d)) →
          ‖iteratedFDeriv ℝ j (faceBump rho pvec eps) x‖ ≤
            Cj * eps ^ (-((jmax : ℝ) + 1))) := by
  intro jmax
  obtain ⟨C0, hC0, hmono⟩ :=
    aux_smoothed_neumann_source_scaling_facebump_uniform_mono d rho hrho hsupp pvec jmax
  exact ⟨C0, hC0, fun eps heps heps8 j hj x _hx => hmono C0 le_rfl eps heps heps8 j hj x⟩



theorem aux_smoothed_neumann_source_scaling_energy_upgrade
    (jmax : ℕ) (Cj Kv eps r t E : ℝ) (hCj : 1 ≤ Cj) (hKv : 0 ≤ Kv)
    (heps : 0 < eps) (heps8 : eps < 1 / 8) (hr : 0 < r)
    (hE : E ≤ Kv * eps ^ (-2 : ℝ) * r ^ t) :
    E ≤ Cj ^ 2 * Kv * eps ^ (-2 * ((jmax : ℝ) + 1)) * r ^ t := by
  have hexp : eps ^ (-2 : ℝ) ≤ eps ^ (-2 * ((jmax : ℝ) + 1)) := by
    apply Real.rpow_le_rpow_of_exponent_ge heps (by linarith)
    have : (0 : ℝ) ≤ jmax := Nat.cast_nonneg jmax
    linarith
  have hrt : 0 ≤ r ^ t := Real.rpow_nonneg hr.le t
  have hpow : 0 ≤ eps ^ (-2 * ((jmax : ℝ) + 1)) := Real.rpow_nonneg heps.le _
  have hC2 : 1 ≤ Cj ^ 2 := one_le_pow₀ hCj
  have hbase : 0 ≤ Kv * eps ^ (-2 * ((jmax : ℝ) + 1)) * r ^ t :=
    mul_nonneg (mul_nonneg hKv hpow) hrt
  calc
    E ≤ Kv * eps ^ (-2 : ℝ) * r ^ t := hE
    _ ≤ Kv * eps ^ (-2 * ((jmax : ℝ) + 1)) * r ^ t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hKv) hrt
    _ = 1 * (Kv * eps ^ (-2 * ((jmax : ℝ) + 1)) * r ^ t) := by ring
    _ ≤ Cj ^ 2 * (Kv * eps ^ (-2 * ((jmax : ℝ) + 1)) * r ^ t) :=
        mul_le_mul_of_nonneg_right hC2 hbase
    _ = Cj ^ 2 * Kv * eps ^ (-2 * ((jmax : ℝ) + 1)) * r ^ t := by ring

theorem aux_smoothed_neumann_source_scaling_conditional :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_HI : InfraredCharacterization M H),
  let Q : Opens (SpatialCoordinates d) := unitNeumannCube d
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  ∀ (rho : ℝ → ℝ), ContDiff ℝ ∞ rho →
    (∀ tau : ℝ, 0 ≤ rho tau) →
    (∀ tau : ℝ, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
    (∫ tau, rho tau) = 1 →
  ∀ (pvec : Fin d → ℝ), (∑ i : Fin d, (pvec i) ^ 2) = 1 →
  (∀ jmax : ℕ, ∃ Cj : ℝ, 1 ≤ Cj ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
        ∀ j : ℕ, j ≤ jmax →
        ∀ x : SpatialCoordinates d,
          x ∈ closure (Q : Set (SpatialCoordinates d)) →
          ‖iteratedFDeriv ℝ j (faceBump rho pvec eps) x‖ ≤
            Cj * eps ^ (-((jmax : ℝ) + 1))) →
  ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤
        Kp * ‖subspaceGradient (meanZeroSobolevGraph Q) u‖),
  ∀ (k : ℕ) (ps : Fin k → ℝ),
    (∀ i : Fin k, 1 ≤ ps i) →
  ∀ (q t : ℝ),
    1 ≤ q →
    (∀ i : Fin k, 4 * ps i ≤ q) →
    (d : ℝ) - 1 < t → t < (d : ℝ) →
  ∀ (Cload Bmom : ℝ), 0 ≤ Cload → 1 ≤ Bmom →
  ∀ (Kcoerc Ahi Bhi Alo Blo : ℕ → BilateralField d → ℝ),
    ((∀ N omega, 0 ≤ Kcoerc N omega) ∧
    (∀ N omega, 0 ≤ Ahi N omega) ∧
    (∀ N omega, 0 ≤ Bhi N omega) ∧
    (∀ N omega, 0 ≤ Alo N omega) ∧
    (∀ N omega, 0 ≤ Blo N omega)) →
  let a : ℕ → BilateralField d → PositiveCoefficient Q :=
    fun N omega => cutoffPositiveCoefficient M H omega N
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
  let v : ℕ → BilateralField d → meanZeroSobolevGraph Q :=
    fun N omega =>
      responseSolution (meanZeroResponseSpace hP) (a N omega)
        ((affineNeumannLoad pvec).comp
          (subspaceGradient (meanZeroSobolevGraph Q)))
  let Y : ℕ → BilateralField d → ℝ :=
    fun N omega =>
      sobolevCoefficientForm (a N omega)
        (v N omega : SobolevData Q) (v N omega : SobolevData Q)
  ∀ (veps : ℕ → ℝ → BilateralField d → meanZeroSobolevGraph Q),
  ((∀ N, MemLp (Kcoerc N) (ENNReal.ofReal q) P) ∧
  (∀ N, MemLp (Ahi N) (ENNReal.ofReal q) P) ∧
  (∀ N, MemLp (Bhi N) (ENNReal.ofReal q) P) ∧
  (∀ N, MemLp (Alo N) (ENNReal.ofReal q) P) ∧
  (∀ N, MemLp (Blo N) (ENNReal.ofReal q) P) ∧
  (∀ N, MemLp (Y N) (ENNReal.ofReal q) P) ∧
  (∀ N, eLpNorm (Kcoerc N) (ENNReal.ofReal q) P ≤ ENNReal.ofReal Bmom) ∧
  (∀ N, eLpNorm (Ahi N) (ENNReal.ofReal q) P ≤ ENNReal.ofReal Bmom) ∧
  (∀ N, eLpNorm (Bhi N) (ENNReal.ofReal q) P ≤ ENNReal.ofReal Bmom) ∧
  (∀ N, eLpNorm (Alo N) (ENNReal.ofReal q) P ≤ ENNReal.ofReal Bmom) ∧
  (∀ N, eLpNorm (Blo N) (ENNReal.ofReal q) P ≤ ENNReal.ofReal Bmom) ∧
  (∀ N, eLpNorm (Y N) (ENNReal.ofReal q) P ≤ ENNReal.ofReal Bmom)) →
  (∀ᵐ omega ∂P,
    (∀ N : ℕ, ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
      SolvesNeumann (a N omega) (faceBump rho pvec eps)
        (veps N eps omega)) ∧
    (∀ N : ℕ, ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
      sobolevCoefficientForm (a N omega)
        ((v N omega : SobolevData Q) - (veps N eps omega : SobolevData Q))
        ((v N omega : SobolevData Q) - (veps N eps omega : SobolevData Q)) ≤
        Cload * Kcoerc N omega * eps ^ (1 / 2 : ℝ)) ∧
    (∀ N : ℕ,
      ∀ f : SpatialCoordinates d → ℝ,
        AEMeasurable f (volume.restrict (Q : Set (SpatialCoordinates d))) →
      ∀ Kf : ℝ, 0 ≤ Kf →
        (∀ᵐ y ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |f y| ≤ Kf) →
      ∀ u : meanZeroSobolevGraph Q, SolvesNeumann (a N omega) f u →
      ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
      ∀ r : ℝ, 0 < r → r ≤ 1 → (3 : ℝ)^(-(N : ℤ)) ≤ r →
        localGradientEnergy (a N omega)
          (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
          (sobolevGradient (u : SobolevData Q)) ≤
          (Ahi N omega *
              sobolevCoefficientForm (a N omega)
                (u : SobolevData Q) (u : SobolevData Q) +
            Bhi N omega * Kf ^ 2) * r ^ t) ∧
    (∀ N : ℕ,
      ∀ f : SpatialCoordinates d → ℝ,
        AEMeasurable f (volume.restrict (Q : Set (SpatialCoordinates d))) →
      ∀ Kf : ℝ, 0 ≤ Kf →
        (∀ᵐ y ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |f y| ≤ Kf) →
      ∀ u : meanZeroSobolevGraph Q, SolvesNeumann (a N omega) f u →
      ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
      ∀ r : ℝ, 0 < r → r ≤ min ((3 : ℝ)^(-(N : ℤ))) 1 →
        localGradientEnergy (a N omega)
          (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
          (sobolevGradient (u : SobolevData Q)) ≤
          (Alo N omega *
              sobolevCoefficientForm (a N omega)
                (u : SobolevData Q) (u : SobolevData Q) +
            Blo N omega * Kf ^ 2) * r ^ t)) →
  ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
    (∀ N omega, 0 ≤ K N omega) ∧
    (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) P) ∧
    (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) P ≤
      ENNReal.ofReal (Cbound i)) ∧
    (∀ᵐ omega ∂P,
      ∀ N : ℕ, ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
        sobolevCoefficientForm (a N omega)
          (veps N eps omega : SobolevData Q)
          (veps N eps omega : SobolevData Q) ≤
          2 * Y N omega + 2 * Cload * Kcoerc N omega) ∧
    (∀ᵐ omega ∂P,
      ∀ N : ℕ, ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
      ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        localGradientEnergy (a N omega)
          (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
          (sobolevGradient (veps N eps omega : SobolevData Q)) ≤
          K N omega * eps ^ (-2 : ℝ) * r ^ t) ∧
    (∀ jmax : ℕ, ∃ Cj : ℝ, 1 ≤ Cj ∧
      (∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
        ∀ j : ℕ, j ≤ jmax →
        ∀ x : SpatialCoordinates d,
          x ∈ closure (Q : Set (SpatialCoordinates d)) →
          ‖iteratedFDeriv ℝ j (faceBump rho pvec eps) x‖ ≤
            Cj * eps ^ (-((jmax : ℝ) + 1))) ∧
      (∀ᵐ omega ∂P,
        ∀ N : ℕ, ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
        ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
        ∀ r : ℝ, 0 < r → r ≤ 1 →
          localGradientEnergy (a N omega)
            (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
            (sobolevGradient (veps N eps omega : SobolevData Q)) ≤
            Cj ^ 2 * K N omega *
              eps ^ (-2 * ((jmax : ℝ) + 1)) * r ^ t)) := by
  intro d hd _ _ M H HI
  dsimp
  intro rho hrho hnonneg hsupp hunit pvec hpvec hderiv hP k ps hps q t hq hqps htlo hthi
    Cload Bmom hC hB Kcoerc Ahi Bhi Alo Blo hnonnegFields veps hmom hgood
  let Q : Opens (SpatialCoordinates d) := unitNeumannCube d
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  let a : ℕ → BilateralField d → PositiveCoefficient Q :=
    fun N omega => cutoffPositiveCoefficient M H omega N
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
  let v : ℕ → BilateralField d → meanZeroSobolevGraph Q :=
    fun N omega => responseSolution (meanZeroResponseSpace hP) (a N omega)
      ((affineNeumannLoad pvec).comp
        (subspaceGradient (meanZeroSobolevGraph Q)))
  let Y : ℕ → BilateralField d → ℝ :=
    fun N omega => sobolevCoefficientForm (a N omega)
      (v N omega : SobolevData Q) (v N omega : SobolevData Q)
  have hcs : HasCompactSupport rho := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) ?_
    intro tau htau
    exact hsupp tau (fun h => htau ⟨h.1.le, h.2.le⟩)
  obtain ⟨Mrho, hMrho⟩ := hrho.continuous.bounded_above_of_compact_support hcs
  let Krho : ℝ := max Mrho 0
  have hKrho0 : 0 ≤ Krho := le_max_right _ _
  have hKrho : ∀ tau : ℝ, |rho tau| ≤ Krho := by
    intro tau
    rw [← Real.norm_eq_abs]
    exact (hMrho tau).trans (le_max_left _ _)
  let D : ℝ := (∑ i : Fin d, |pvec i|) * (2 * Krho)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let K : ℕ → BilateralField d → ℝ := assembledK Ahi Bhi Alo Blo Y Kcoerc Cload D
  let Cbound : Fin k → ℝ := fun _ =>
    4 * Bmom ^ 2 + 4 * Cload * Bmom ^ 2 + 2 * D ^ 2 * Bmom
  have hY_nonneg : ∀ N omega, 0 ≤ Y N omega := by
    intro N omega
    exact sobolevCoefficientForm_nonneg (a N omega) _
  rcases hmom with ⟨hKmem, hAmem, hBmem, hLmem, hBLmem, hYmem,
    hKbd, hAbd, hBbd, hLbd, hBLbd, hYbd⟩
  have hmoment (i : Fin k) (N : ℕ) :
      MemLp (K N) (ENNReal.ofReal (ps i)) P ∧
        eLpNorm (K N) (ENNReal.ofReal (ps i)) P ≤
          ENNReal.ofReal (Cbound i) := by
    have h := aux_smoothed_neumann_source_scaling_scalar_norm P (ps i) q Bmom Cload D (hps i)
      (hqps i) hB hC hD (Ahi N) (Alo N) (Bhi N) (Blo N)
      (Y N) (Kcoerc N)
      (hAmem N) (hLmem N) (hBmem N) (hBLmem N) (hYmem N) (hKmem N)
      (hAbd N) (hLbd N) (hBbd N) (hBLbd N) (hYbd N) (hKbd N)
    simpa only [K, assembledK, Cbound] using! h
  refine ⟨K, Cbound, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact assembledK_nonneg Ahi Bhi Alo Blo Y Kcoerc Cload D
      hnonnegFields.2.1 hnonnegFields.2.2.1 hnonnegFields.2.2.2.1
      hnonnegFields.2.2.2.2 hY_nonneg hnonnegFields.1 hC
  · exact fun i N => (hmoment i N).1
  · exact fun i N => (hmoment i N).2
  · filter_upwards [hgood] with omega hω
    intro N eps heps heps8
    exact aux_energy_comparison (a N omega)
      (v N omega : SobolevData Q) (veps N eps omega : SobolevData Q)
      (Y N omega) Cload (Kcoerc N omega) eps rfl hC
      (hnonnegFields.1 N omega) heps heps8
      (hω.2.1 N eps heps heps8)
  · filter_upwards [hgood] with omega hω
    intro N eps heps heps8 x hx r hr hr1
    have hface : ∀ z : SpatialCoordinates d,
        |faceBump rho pvec eps z| ≤ D * eps⁻¹ := by
      simpa only [D] using aux_faceBump_sup rho hrho hsupp Krho hKrho
        pvec eps heps heps8
    have hsource := aux_faceBump_aemeasurable rho hrho hsupp Krho hKrho
      pvec eps heps heps8
    have hE := aux_energy_comparison (a N omega)
      (v N omega : SobolevData Q) (veps N eps omega : SobolevData Q)
      (Y N omega) Cload (Kcoerc N omega) eps rfl hC
      (hnonnegFields.1 N omega) heps heps8
      (hω.2.1 N eps heps heps8)
    have hg := aux_two_range_gradient rho pvec N omega (a N omega)
      (veps N eps omega) t (Ahi N omega) (Bhi N omega)
      (Alo N omega) (Blo N omega) (Y N omega) Cload
      (Kcoerc N omega) D eps
      (hnonnegFields.2.1 N omega) (hnonnegFields.2.2.1 N omega)
      (hnonnegFields.2.2.2.1 N omega) (hnonnegFields.2.2.2.2 N omega)
      (hY_nonneg N omega) hC (hnonnegFields.1 N omega) hD heps heps8
      hsource hface (hω.1 N eps heps heps8) hE
      (hω.2.2.1 N) (hω.2.2.2 N)
    simpa only [K, assembledK] using hg x hx r hr hr1
  · intro jmax
    obtain ⟨Cj, hCj, hder⟩ := hderiv jmax
    refine ⟨Cj, hCj, hder, ?_⟩
    filter_upwards [hgood] with omega hω
    intro N eps heps heps8 x hx r hr hr1
    have hface : ∀ z : SpatialCoordinates d,
        |faceBump rho pvec eps z| ≤ D * eps⁻¹ := by
      simpa only [D] using aux_faceBump_sup rho hrho hsupp Krho hKrho
        pvec eps heps heps8
    have hsource := aux_faceBump_aemeasurable rho hrho hsupp Krho hKrho
      pvec eps heps heps8
    have hE := aux_energy_comparison (a N omega)
      (v N omega : SobolevData Q) (veps N eps omega : SobolevData Q)
      (Y N omega) Cload (Kcoerc N omega) eps rfl hC
      (hnonnegFields.1 N omega) heps heps8
      (hω.2.1 N eps heps heps8)
    have hg := aux_two_range_gradient rho pvec N omega (a N omega)
      (veps N eps omega) t (Ahi N omega) (Bhi N omega)
      (Alo N omega) (Blo N omega) (Y N omega) Cload
      (Kcoerc N omega) D eps
      (hnonnegFields.2.1 N omega) (hnonnegFields.2.2.1 N omega)
      (hnonnegFields.2.2.2.1 N omega) (hnonnegFields.2.2.2.2 N omega)
      (hY_nonneg N omega) hC (hnonnegFields.1 N omega) hD heps heps8
      hsource hface (hω.1 N eps heps heps8) hE
      (hω.2.2.1 N) (hω.2.2.2 N)
    have hguniform := hg x hx r hr hr1
    exact assembledK_derivative_absorption _ _ Cj eps r t jmax
      (by simpa only [K, assembledK] using hguniform)
      (assembledK_nonneg Ahi Bhi Alo Blo Y Kcoerc Cload D
        hnonnegFields.2.1 hnonnegFields.2.2.1
        hnonnegFields.2.2.2.1 hnonnegFields.2.2.2.2
        hY_nonneg hnonnegFields.1 hC N omega)
      hCj heps heps8 hr

/--
- Exact suppliers: `lem_neumann_error` (difference energy and affine/K moments),
  `lem_coercivity`, `rem_resolved_meshes`, `rem_resolved_microscopic` (two
  source-blind ranges), `smoothed_load_properties` (eps^-1 and constants
  killed), `lem_primitive` (macro source), `lem_extremes` (micro moment absorption).
- The actual cube, positive coefficient, affine response, face-bump response,
  coefficient energy and local gradient energy are used throughout.
- One common almost-everywhere event carries the response pinning and both
  source-blind wavelength ranges.
- The hmacro and hmicro ranges use the cutoff wavelength
  `(3 : ℝ)^(-(N : ℤ))`, which is distinct from the independently quantified
  face-bump smoothing width `eps` retained in the veps pinning, difference
  energy, and final smoothed conclusions.
- The finite moment bank has one common numerical bound `Bmom`, supplied before
  the coefficient families and never existentially chosen ahead of a hypothesis.
- The conclusion includes the epsilon-uniform affine-energy comparison, one
  random majorant for every listed moment, and the quantified `C^k` source-cost
  convention with exponent `2 * (jmax + 1)`.
- Numerical absorption supplier: rem_resolved_eps_power. No proof claim.
-/
theorem smoothed_neumann_source_scaling :
  ∀ (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (_HI : InfraredCharacterization M H),
  let Q : Opens (SpatialCoordinates d) := unitNeumannCube d
  let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  ∀ (rho : ℝ → ℝ), ContDiff ℝ ∞ rho →
    (∀ tau : ℝ, 0 ≤ rho tau) →
    (∀ tau : ℝ, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
    (∫ tau, rho tau) = 1 →
  ∀ (pvec : Fin d → ℝ), (∑ i : Fin d, (pvec i) ^ 2) = 1 →
  ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤
        Kp * ‖subspaceGradient (meanZeroSobolevGraph Q) u‖),
  ∀ (k : ℕ) (ps : Fin k → ℝ),
    (∀ i : Fin k, 1 ≤ ps i) →
  ∀ (q t : ℝ),
    1 ≤ q →
    (∀ i : Fin k, 4 * ps i ≤ q) →
    (d : ℝ) - 1 < t → t < (d : ℝ) →
  ∀ (Cload Bmom : ℝ), 0 ≤ Cload → 1 ≤ Bmom →
  ∀ (Kcoerc Ahi Bhi Alo Blo : ℕ → BilateralField d → ℝ),
    ((∀ N omega, 0 ≤ Kcoerc N omega) ∧
    (∀ N omega, 0 ≤ Ahi N omega) ∧
    (∀ N omega, 0 ≤ Bhi N omega) ∧
    (∀ N omega, 0 ≤ Alo N omega) ∧
    (∀ N omega, 0 ≤ Blo N omega)) →
  let a : ℕ → BilateralField d → PositiveCoefficient Q :=
    fun N omega => cutoffPositiveCoefficient M H omega N
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
  let v : ℕ → BilateralField d → meanZeroSobolevGraph Q :=
    fun N omega =>
      responseSolution (meanZeroResponseSpace hP) (a N omega)
        ((affineNeumannLoad pvec).comp
          (subspaceGradient (meanZeroSobolevGraph Q)))
  let Y : ℕ → BilateralField d → ℝ :=
    fun N omega =>
      sobolevCoefficientForm (a N omega)
        (v N omega : SobolevData Q) (v N omega : SobolevData Q)
  ∀ (veps : ℕ → ℝ → BilateralField d → meanZeroSobolevGraph Q),
  ((∀ N, MemLp (Kcoerc N) (ENNReal.ofReal q) P) ∧
  (∀ N, MemLp (Ahi N) (ENNReal.ofReal q) P) ∧
  (∀ N, MemLp (Bhi N) (ENNReal.ofReal q) P) ∧
  (∀ N, MemLp (Alo N) (ENNReal.ofReal q) P) ∧
  (∀ N, MemLp (Blo N) (ENNReal.ofReal q) P) ∧
  (∀ N, MemLp (Y N) (ENNReal.ofReal q) P) ∧
  (∀ N, eLpNorm (Kcoerc N) (ENNReal.ofReal q) P ≤ ENNReal.ofReal Bmom) ∧
  (∀ N, eLpNorm (Ahi N) (ENNReal.ofReal q) P ≤ ENNReal.ofReal Bmom) ∧
  (∀ N, eLpNorm (Bhi N) (ENNReal.ofReal q) P ≤ ENNReal.ofReal Bmom) ∧
  (∀ N, eLpNorm (Alo N) (ENNReal.ofReal q) P ≤ ENNReal.ofReal Bmom) ∧
  (∀ N, eLpNorm (Blo N) (ENNReal.ofReal q) P ≤ ENNReal.ofReal Bmom) ∧
  (∀ N, eLpNorm (Y N) (ENNReal.ofReal q) P ≤ ENNReal.ofReal Bmom)) →
  (∀ᵐ omega ∂P,
    (∀ N : ℕ, ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
      SolvesNeumann (a N omega) (faceBump rho pvec eps)
        (veps N eps omega)) ∧
    (∀ N : ℕ, ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
      sobolevCoefficientForm (a N omega)
        ((v N omega : SobolevData Q) - (veps N eps omega : SobolevData Q))
        ((v N omega : SobolevData Q) - (veps N eps omega : SobolevData Q)) ≤
        Cload * Kcoerc N omega * eps ^ (1 / 2 : ℝ)) ∧
    (∀ N : ℕ,
      ∀ f : SpatialCoordinates d → ℝ,
        AEMeasurable f (volume.restrict (Q : Set (SpatialCoordinates d))) →
      ∀ Kf : ℝ, 0 ≤ Kf →
        (∀ᵐ y ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |f y| ≤ Kf) →
      ∀ u : meanZeroSobolevGraph Q, SolvesNeumann (a N omega) f u →
      ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
      ∀ r : ℝ, 0 < r → r ≤ 1 → (3 : ℝ)^(-(N : ℤ)) ≤ r →
        localGradientEnergy (a N omega)
          (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
          (sobolevGradient (u : SobolevData Q)) ≤
          (Ahi N omega *
              sobolevCoefficientForm (a N omega)
                (u : SobolevData Q) (u : SobolevData Q) +
            Bhi N omega * Kf ^ 2) * r ^ t) ∧
    (∀ N : ℕ,
      ∀ f : SpatialCoordinates d → ℝ,
        AEMeasurable f (volume.restrict (Q : Set (SpatialCoordinates d))) →
      ∀ Kf : ℝ, 0 ≤ Kf →
        (∀ᵐ y ∂volume.restrict (Q : Set (SpatialCoordinates d)),
          |f y| ≤ Kf) →
      ∀ u : meanZeroSobolevGraph Q, SolvesNeumann (a N omega) f u →
      ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
      ∀ r : ℝ, 0 < r → r ≤ min ((3 : ℝ)^(-(N : ℤ))) 1 →
        localGradientEnergy (a N omega)
          (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
          (sobolevGradient (u : SobolevData Q)) ≤
          (Alo N omega *
              sobolevCoefficientForm (a N omega)
                (u : SobolevData Q) (u : SobolevData Q) +
            Blo N omega * Kf ^ 2) * r ^ t)) →
  ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
    (∀ N omega, 0 ≤ K N omega) ∧
    (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) P) ∧
    (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) P ≤
      ENNReal.ofReal (Cbound i)) ∧
    (∀ᵐ omega ∂P,
      ∀ N : ℕ, ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
        sobolevCoefficientForm (a N omega)
          (veps N eps omega : SobolevData Q)
          (veps N eps omega : SobolevData Q) ≤
          2 * Y N omega + 2 * Cload * Kcoerc N omega) ∧
    (∀ᵐ omega ∂P,
      ∀ N : ℕ, ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
      ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        localGradientEnergy (a N omega)
          (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
          (sobolevGradient (veps N eps omega : SobolevData Q)) ≤
          K N omega * eps ^ (-2 : ℝ) * r ^ t) ∧
    (∀ jmax : ℕ, ∃ Cj : ℝ, 1 ≤ Cj ∧
      (∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
        ∀ j : ℕ, j ≤ jmax →
        ∀ x : SpatialCoordinates d,
          x ∈ closure (Q : Set (SpatialCoordinates d)) →
          ‖iteratedFDeriv ℝ j (faceBump rho pvec eps) x‖ ≤
            Cj * eps ^ (-((jmax : ℝ) + 1))) ∧
      (∀ᵐ omega ∂P,
        ∀ N : ℕ, ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
        ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
        ∀ r : ℝ, 0 < r → r ≤ 1 →
          localGradientEnergy (a N omega)
            (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
            (sobolevGradient (veps N eps omega : SobolevData Q)) ≤
            Cj ^ 2 * K N omega *
              eps ^ (-2 * ((jmax : ℝ) + 1)) * r ^ t)) := by
  intro d hd _ _ M H HI
  dsimp
  intro rho hrho hnonneg hsupp hint pvec hpvec
  exact aux_smoothed_neumann_source_scaling_conditional d hd M H HI
    rho hrho hnonneg hsupp hint pvec hpvec
    (aux_smoothed_neumann_source_scaling_facebump_uniform
      d rho hrho hnonneg hsupp hint pvec hpvec)

end SubdiffusiveProcess.Paper
