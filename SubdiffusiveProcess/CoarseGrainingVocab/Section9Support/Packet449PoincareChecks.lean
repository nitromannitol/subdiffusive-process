module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTorsionEnergyL2
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5RobustTorsionInputs
public import SubdiffusiveProcess.CoarseGrainingVocab.Section12.FiniteCutoffVocab
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIterationLevelEnergy
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeEllipticityPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeSobolevCoefficient
public import Homogenization.Sobolev.Foundations.CubePoisson.AnalyticInput

@[expose] public section

/-!
# P-449: coarse zero-trace Poincare and the finite-cutoff Holder step

Source: `mfd:in-deterministic` and `s.tightness`.
The coarse zero-trace estimate already exists as
`Section9Support.goodCube_h10_l2_le_coarse_energy`. This file converts it to
`PoincareAssumption`, without replacing a coarse cap by pointwise ellipticity.
The finite-cutoff Holder step keeps the reference measure fixed.
-/

set_option autoImplicit false
open Homogenization hiding Vec
open Homogenization.Book Homogenization.Book.Ch03 MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.WeightedEnergy
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalResolventIteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section12.FiniteCutoffVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Packet449

/-- Lebesgue-reference `lpSq` is the actual square integral, including its finiteness. -/
theorem lpSq_one_two_eq_integral {d : ℕ} {U : Set (Vec d)} (f : H1Function U) :
    lpSq (fun _ => 1) U 2 f.toFun =
      ENNReal.ofReal (∫ x in U, f.toFun x * f.toFun x) := by
  rw [lpSq_two_eq_lintegral]
  have hm : weightedMeasure (fun _ : Vec d => (1 : ℝ)) = volume := by
    simp [weightedMeasure]
  rw [hm]
  exact (ofReal_integral_eq_lintegral_ofReal (f.memL2.integrable_mul f.memL2)
    (Filter.Eventually.of_forall fun x => mul_self_nonneg (f.toFun x))).symm

/-- The already proved coarse `H10` estimate, in the exact unweighted Poincare interface.
The constant depends only on dimension; the price is `side^2 / lambda_{1/2,1}`. -/
theorem poincareAssumption_of_coarse_energy {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (coeff : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (coeff.coeffOn Q).toCoeffField x = scalarMatrix (b x)) :
    PoincareAssumption b (fun _ => 1) (openCubeSet Q)
      ((2 * weightedLocalSobolevEnergyConstant d) ^ 2)
      ((cubeScaleFactor Q) ^ 2 * (Ch02.lambdaSq Q (1 / 2) (.finite 1) coeff)⁻¹) := by
  intro f
  rw [lpSq_one_two_eq_integral]
  apply ENNReal.ofReal_le_ofReal
  have h := goodCube_h10_l2_le_coarse_energy Q coeff b hb f
  have hnonneg := scalar_half_energy_nonneg_of_scalarParent Q coeff b hb f.toH1Function
  have hnorm : 0 ≤ cubeLpNorm Q 2 f.toH1Function.toFun := cubeLpNorm_nonneg _ _ _
  have hsq := pow_le_pow_left₀ hnorm h 2
  rw [mul_pow, Real.sq_sqrt hnonneg] at hsq
  have hint := setIntegral_openCubeSet_sq_eq_cubeVolume_mul_cubeLpNorm_two_rpow
    Q f.toH1Function.toFun (h1_memLp_normalizedCubeMeasure Q f.toH1Function)
  rw [Real.rpow_two] at hint
  rw [hint]
  have hv : 0 < cubeVolume Q := cubeVolume_pos Q
  have hscaled := mul_le_mul_of_nonneg_left hsq hv.le
  unfold volumeAverage at hscaled
  rw [volume_openCubeSet_toReal] at hscaled
  unfold energy
  convert hscaled using 1
  field_simp

/-- A named at-use cap suffices; it is not an extra field of the post-perturbation tests. -/
theorem poincareAssumption_of_coarse_price {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (coeff : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (coeff.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    {A F : ℝ}
    (hprice : (2 * weightedLocalSobolevEnergyConstant d) ^ 2 *
      ((cubeScaleFactor Q) ^ 2 * (Ch02.lambdaSq Q (1 / 2) (.finite 1) coeff)⁻¹) ≤ A * F) :
    PoincareAssumption b (fun _ => 1) (openCubeSet Q) A F := by
  intro f
  refine (poincareAssumption_of_coarse_energy Q coeff b hb f).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hnonneg := scalar_half_energy_nonneg_of_scalarParent Q coeff b hb f.toH1Function
  have hL : 0 < (Ch02.lambdaSq Q (1 / 2) (.finite 1) coeff)⁻¹ :=
    inv_pos.mpr (Ch02.lambdaSq_finite_pos Q coeff (by norm_num) (by norm_num))
  have hE : 0 ≤ energy b (openCubeSet Q) f.toH1Function := by
    have havg : 0 ≤ volumeAverage (openCubeSet Q)
        (fun x => b x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x)) :=
      (mul_nonneg_iff_of_pos_left hL).mp hnonneg
    unfold volumeAverage at havg
    rw [volume_openCubeSet_toReal] at havg
    exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr (cubeVolume_pos Q))).mp havg
  exact mul_le_mul_of_nonneg_right hprice hE


/-- The print's lower bound `lambda_{1/2,1} >= cForm * D` gives time `side^2 / D`. -/
theorem poincareAssumption_of_coarse_lower {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (coeff : CoeffFamily d) (b : Vec d → ℝ)
    (hb : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      (coeff.coeffOn Q).toCoeffField x = scalarMatrix (b x))
    {cForm D : ℝ} (hcForm : 0 < cForm) (hD : 0 < D)
    (hcap : cForm * D ≤ Ch02.lambdaSq Q (1 / 2) (.finite 1) coeff) :
    PoincareAssumption b (fun _ => 1) (openCubeSet Q)
      ((2 * weightedLocalSobolevEnergyConstant d) ^ 2 / cForm)
      ((cubeScaleFactor Q) ^ 2 / D) := by
  apply poincareAssumption_of_coarse_price Q coeff b hb
  have hinv := one_div_le_one_div_of_le (mul_pos hcForm hD) hcap
  simp only [one_div] at hinv
  calc
    _ ≤ (2 * weightedLocalSobolevEnergyConstant d) ^ 2 *
        ((cubeScaleFactor Q) ^ 2 * (cForm * D)⁻¹) := by gcongr
    _ = _ := by rw [mul_inv_rev]; ring

/-- The ordinary positive-scale response test supplies the unweighted input on that very
sample and translated cube. It need not be recovered from the four exported tests. -/
theorem cutoff_poincare_of_ellipticity_test {d : ℕ} [NeZero d]
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (n m : ℕ) (hmn : m ≤ n)
    (z : Vec d) (omega : _root_.SubdiffusiveProcess.Model.PotentialSample d)
    {e : ℝ} (he : 0 ≤ e)
    (hE : ellipticityMomentObservable M n (m : ℤ) (1 / 8)
      (translatePotentialSample z omega) ≤ ENNReal.ofReal e) :
    PoincareAssumption (fun x => _root_.SubdiffusiveProcess.Model.aCutoff M n omega (x + z))
      (fun _ => 1) (openCubeSet (originCube d (m : ℤ)))
      ((2 * weightedLocalSobolevEnergyConstant d) ^ 2 * (1 + Real.sqrt 2 * e) ^ 2)
      ((cubeScaleFactor (originCube d (m : ℤ))) ^ 2 / ahom M n) := by
  let Q := originCube d (m : ℤ)
  obtain ⟨_, _, hcoeff⟩ := goodCube_cutoff_sobolev_data M n omega z Q
  apply poincareAssumption_of_coarse_price Q
    (aCutoffFamily M n (translatePotentialSample z omega)) _ (Filter.Eventually.of_forall hcoeff)
  have hraw := goodCube_cutoff_lambda_price_le_of_ellipticity_test M n m hmn z omega he hE
  have hcap : (Ch02.lambdaSq Q (1 / 2) (.finite 1)
      (aCutoffFamily M n (translatePotentialSample z omega)))⁻¹ ≤
      (1 + Real.sqrt 2 * e) ^ 2 / ahom M n := by
    apply (le_div_iff₀ (ahom_pos M n)).mpr
    simpa only [mul_comm] using hraw
  calc
    _ ≤ (2 * weightedLocalSobolevEnergyConstant d) ^ 2 *
        ((cubeScaleFactor Q) ^ 2 * ((1 + Real.sqrt 2 * e) ^ 2 / ahom M n)) := by gcongr
    _ = _ := by ring

/-- Changing only the elliptic coefficient by a constant changes the unweighted clock
by its inverse. Simultaneous form/mass scaling is a different operation. -/
theorem poincareAssumption_const_mul_iff {d : ℕ} {U : Set (Vec d)}
    (a rho : Vec d → ℝ) (A F : ℝ) {k : ℝ} (hk : 0 < k) :
    PoincareAssumption (fun x => k * a x) rho U A (F / k) ↔
      PoincareAssumption a rho U A F := by
  have he (f : H1Function U) : energy (fun x => k * a x) U f = k * energy a U f := by
    simp only [energy, mul_assoc, integral_const_mul]
  unfold PoincareAssumption
  simp only [he]
  have hr (E : ℝ) : A * (F / k) * (k * E) = A * F * E := by
    field_simp
  simp only [hr]

/-- Holder cancels the exact mass power in the zero-boundary half of `FiniteCutoffBothSobolev`.
It produces a Poincare bound for the SAME reference density `rho`. -/
theorem finiteCutoffBothSobolev_poincare {d : ℕ} {a rho : Vec d → ℝ}
    {p0 B F : ℝ} {Q : Section9GoodCube.Cube d}
    (hp0 : 2 < p0) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hW0 : weightedMeasure rho (Section9GoodCube.cubeSet Q) ≠ 0)
    (hWtop : weightedMeasure rho (Section9GoodCube.cubeSet Q) ≠ ⊤)
    (h : FiniteCutoffBothSobolev a rho p0 B F Q) :
    PoincareAssumption a rho (Section9GoodCube.cubeSet Q) B F := by
  intro f
  set W := weightedMeasure rho (Section9GoodCube.cubeSet Q)
  have hstep := lpSq_two_le_lpSq_mul_rpow (a := rho) hp0 f
  have hmul := mul_le_mul_left (h.1 f) (W ^ (1 - 2 / p0))
  have hcancel : (ENNReal.ofReal (B * F) * W ^ (-(1 - 2 / p0)) *
      ENNReal.ofReal (energy a (Section9GoodCube.cubeSet Q) f.toH1Function)) *
      W ^ (1 - 2 / p0) =
      ENNReal.ofReal (B * F * energy a (Section9GoodCube.cubeSet Q) f.toH1Function) := by
    rw [show ENNReal.ofReal (B * F) * W ^ (-(1 - 2 / p0)) *
        ENNReal.ofReal (energy a (Section9GoodCube.cubeSet Q) f.toH1Function) *
        W ^ (1 - 2 / p0) =
        ENNReal.ofReal (B * F) * ENNReal.ofReal
          (energy a (Section9GoodCube.cubeSet Q) f.toH1Function) *
          (W ^ (-(1 - 2 / p0)) * W ^ (1 - 2 / p0)) by ring]
    rw [← ENNReal.rpow_add _ _ hW0 hWtop]
    simp only [neg_add_cancel, ENNReal.rpow_zero, mul_one]
    exact (ENNReal.ofReal_mul (mul_nonneg hB hF)).symm
  exact hstep.trans (hmul.trans hcancel.le)

/-- The same homogeneous display also supplies the inhomogeneous Sobolev assumption
used by the local-resolvent exit-time estimate; no diffusion-law hypothesis is needed here. -/
theorem finiteCutoffBothSobolev_resolventAssumptions {d : ℕ} {a rho : Vec d → ℝ}
    {p0 B F : ℝ} {Q : Section9GoodCube.Cube d}
    (hp0 : 2 < p0) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hW0 : weightedMeasure rho (Section9GoodCube.cubeSet Q) ≠ 0)
    (hWtop : weightedMeasure rho (Section9GoodCube.cubeSet Q) ≠ ⊤)
    (h : FiniteCutoffBothSobolev a rho p0 B F Q) :
    SobolevAssumption a rho (Section9GoodCube.cubeSet Q) p0 B F ∧
      PoincareAssumption a rho (Section9GoodCube.cubeSet Q) B F := by
  refine ⟨?_, finiteCutoffBothSobolev_poincare hp0 hB hF hW0 hWtop h⟩
  intro f
  have hWpos : 0 < (weightedMeasure rho (Section9GoodCube.cubeSet Q)).toReal :=
    ENNReal.toReal_pos hW0 hWtop
  have hW : weightedMeasure rho (Section9GoodCube.cubeSet Q) ^ (-(1 - 2 / p0)) =
      ENNReal.ofReal ((weightedMeasure rho (Section9GoodCube.cubeSet Q)).toReal ^
        (-(1 - 2 / p0))) := by
    rw [← ENNReal.ofReal_rpow_of_pos hWpos, ENNReal.ofReal_toReal hWtop]
  have hdisp := h.1 f
  rw [hW, ENNReal.ofReal_mul hB] at hdisp
  have heq : ENNReal.ofReal B * ENNReal.ofReal F *
      ENNReal.ofReal ((weightedMeasure rho (Section9GoodCube.cubeSet Q)).toReal ^
        (-(1 - 2 / p0))) * ENNReal.ofReal
        (energy a (Section9GoodCube.cubeSet Q) f.toH1Function) =
      ENNReal.ofReal (B * (weightedMeasure rho (Section9GoodCube.cubeSet Q)).toReal ^
        (-(1 - 2 / p0))) * ENNReal.ofReal
        (F * energy a (Section9GoodCube.cubeSet Q) f.toH1Function) := by
    rw [ENNReal.ofReal_mul hB, ENNReal.ofReal_mul hF]
    ring
  rw [heq] at hdisp
  exact hdisp.trans (mul_le_mul_right le_add_self _)


/-- For a normalized near-one multiplier, the unweighted Poincare constant loses only
`(1-epsilon)^{-1}`. Integrability is explicit because the energy is a Bochner integral. -/
theorem poincareAssumption_near_one {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {a theta rho : Vec d → ℝ} {A F epsilon : ℝ}
    (hA : 0 ≤ A) (hF : 0 ≤ F) (heps : epsilon < 1)
    (ha : ∀ x ∈ U, 0 ≤ a x) (htheta : ∀ x ∈ U, |theta x - 1| ≤ epsilon)
    (hint1 : ∀ f : H10Function U, IntegrableOn
      (fun x => a x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x)) U)
    (hint2 : ∀ f : H10Function U, IntegrableOn
      (fun x => a x * theta x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x)) U)
    (h : PoincareAssumption a rho U A F) :
    PoincareAssumption (fun x => a x * theta x) rho U (A / (1 - epsilon)) F := by
  intro f
  have hl : 0 < 1 - epsilon := sub_pos.mpr heps
  have he := energy_mul_ge hU (Set.Subset.refl U) (l := 1 - epsilon) ha
    (fun x hx => by linarith [(abs_le.mp (htheta x hx)).1])
    f.toH1Function (hint1 f) (hint2 f)
  refine (h f).trans (ENNReal.ofReal_le_ofReal ?_)
  have hmul := mul_le_mul_of_nonneg_left he
    (div_nonneg (mul_nonneg hA hF) hl.le)
  convert hmul using 1 <;> field_simp

/-- In the divergence-form application, finite positive mass is automatic for a cube of
positive side. This is the exact `rho = 1` input pair of the exit-upper corollary. -/
theorem finiteCutoffBothSobolev_lebesgue_resolventAssumptions {d : ℕ} {a : Vec d → ℝ}
    {p0 B F : ℝ} {Q : Section9GoodCube.Cube d}
    (hQ : 0 < Q.2) (hp0 : 2 < p0) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (h : FiniteCutoffBothSobolev a (fun _ => 1) p0 B F Q) :
    SobolevAssumption a (fun _ => 1) (Section9GoodCube.cubeSet Q) p0 B F ∧
      PoincareAssumption a (fun _ => 1) (Section9GoodCube.cubeSet Q) B F := by
  have hW : weightedMeasure (fun _ : Vec d => 1) (Section9GoodCube.cubeSet Q) =
      ENNReal.ofReal (Q.2 ^ d) := by
    have hm : weightedMeasure (fun _ : Vec d => (1 : ℝ)) = volume := by
      simp [weightedMeasure]
    rw [hm]
    exact volume_cubeSet hQ.le
  apply finiteCutoffBothSobolev_resolventAssumptions hp0 hB hF _ _ h
  · rw [hW]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hQ d))
  · rw [hW]
    exact ENNReal.ofReal_ne_top

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Packet449
