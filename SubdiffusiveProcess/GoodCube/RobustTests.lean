module

public import SubdiffusiveProcess.GoodCube.StepT
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeV5RobustHarmonic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReferenceCatalogueEvent
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.SparseLayerReduction

@[expose] public section

/-!
# Robust finite local tests from the raw good-cube events

The multiplier-robust tests of
`GoodCubeV5RobustFiniteLocalTests` are produced from the **same** raw events that produce the
ordinary cutoff tests: Step S (Sobolev) and Step M (mass) are the proved deterministic
transfers; Step T (torsion) is `GoodCubeStepT` at positive scale and the uniform-contrast test
at bounded scale.  The multiplier tolerance is chosen after the torsion tolerance and the
Sobolev constant, exactly as Chooses `ε₁, ε₃`.
-/

open Homogenization hiding Vec cubeSet
open MeasureTheory Set Filter
open _root_.SubdiffusiveProcess.Model
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation (Lattice)
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.RobustGoodCube

variable {d : ℕ}

/-! ## Geometry of the origin cube -/

theorem openCubeSet_originCube_eq_cubeSet (m : ℤ) :
    openCubeSet (originCube d m) = cubeSet ((0 : Vec d), (3 : ℝ) ^ m) := by
  rw [← translatedCube_eq_cubeSet m (0 : Vec d)]
  simp [translatedCube, cube]

theorem add_mem_cubeSet_of_mem_openCubeSet {m : ℤ} {x : Vec d} (z : Vec d)
    (hx : x ∈ openCubeSet (originCube d m)) : x + z ∈ cubeSet (z, (3 : ℝ) ^ m) := by
  rw [← translatedCube_eq_cubeSet m z]
  exact ⟨x, hx, add_comm z x⟩

theorem goodCubeSobolevDisplay_mono_const {a : Vec d → ℝ} {p A A' : ℝ} {clock : ℝ → ℝ}
    {Q : Cube d} (h : GoodCubeSobolevDisplay a p A clock Q) (hAA' : A ≤ A') :
    GoodCubeSobolevDisplay a p A' clock Q := by
  intro f
  refine (h f).trans ?_
  gcongr

/-- Back-translation of the Sobolev display to the origin cube. -/
theorem goodCubeSobolevDisplay_untranslate (z : Vec d) (m : ℤ) (a : Vec d → ℝ)
    (ha : Measurable a) {p A : ℝ} (hp : 0 < p) (clock : ℝ → ℝ)
    (h : GoodCubeSobolevDisplay a p A clock (z, (3 : ℝ) ^ m)) :
    GoodCubeSobolevDisplay (fun x => a (x + z)) p A clock ((0 : Vec d), (3 : ℝ) ^ m) := by
  have ha' : Measurable (fun x => a (x + z)) := ha.comp (measurable_id.add measurable_const)
  have hfun : (fun x => (fun y => a (y + z)) (x + -z)) = a := by
    funext x
    simp
  have h' : GoodCubeSobolevDisplay (fun x => (fun y => a (y + z)) (x + -z)) p A clock
      (z, (3 : ℝ) ^ m) := by
    rw [hfun]; exact h
  have := goodCube_sobolevDisplay_translate (-z) (z, (3 : ℝ) ^ m) (fun y => a (y + z)) ha' p A
    hp clock h'
  simpa using this

/-- A continuous function is bounded on the closure of a half-open triadic cube. -/
theorem exists_abs_bound_on_cube {b : Vec d → ℝ} (hb : Continuous b) (Q : TriadicCube d) :
    ∃ B : ℝ, ∀ x ∈ closure (Homogenization.cubeSet Q), |b x| ≤ B := by
  obtain ⟨B, hB⟩ := (isBounded_cubeSet Q).isCompact_closure.exists_bound_of_continuousOn
    hb.continuousOn
  exact ⟨B, fun x hx => by simpa only [Real.norm_eq_abs] using hB x hx⟩

/-- The open-cube integral of a nonnegative continuous function is bounded by the half-open
cube average. -/
theorem setIntegral_openCubeSet_le_of_cubeAverage_le {b : Vec d → ℝ} (hb : Continuous b)
    (hb0 : ∀ x, 0 ≤ b x) (Q : TriadicCube d) {Mb : ℝ} (havg : cubeAverage Q b ≤ Mb) :
    ∫ x in openCubeSet Q, b x ≤ Mb * cubeVolume Q := by
  have hcpt := (isBounded_cubeSet Q).isCompact_closure
  have hint : IntegrableOn b (Homogenization.cubeSet Q) :=
    (hb.continuousOn.integrableOn_compact hcpt).mono_set subset_closure
  have hmono : ∫ x in openCubeSet Q, b x ≤ ∫ x in Homogenization.cubeSet Q, b x :=
    setIntegral_mono_set hint (Eventually.of_forall fun x => hb0 x)
      (Eventually.of_forall (openCubeSet_subset_cubeSet Q))
  have hv : 0 < cubeVolume Q := cubeVolume_pos Q
  have heq : ∫ x in Homogenization.cubeSet Q, b x = cubeVolume Q * cubeAverage Q b := by
    unfold cubeAverage
    field_simp
  calc ∫ x in openCubeSet Q, b x ≤ cubeVolume Q * cubeAverage Q b := hmono.trans heq.le
    _ ≤ cubeVolume Q * Mb := mul_le_mul_of_nonneg_left havg hv.le
    _ = Mb * cubeVolume Q := mul_comm _ _

/-! ## Step T at positive scale -/

/-- The dimensional price of the positive-scale torsion transfer. -/
def positiveTorsionPrice (d : ℕ) [NeZero d] (A : ℝ) : ℝ :=
  (2 * Section8Support.WeightedEnergy.weightedLocalSobolevEnergyConstant d) ^ 2 *
    (1 + Real.sqrt 2 * 1) ^ 2 * A * (3 / 2)

theorem positiveTorsionPrice_nonneg (d : ℕ) [NeZero d] {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ positiveTorsionPrice d A := by
  unfold positiveTorsionPrice
  positivity

/-- **Robust torsion at positive scale.**  The raw event data on one positive test cube — the
Sobolev display, the ellipticity response test at level one, the average bound `≤ 3/2`, and
the raw torsion test at tolerance `epsT` — give the torsion test at `epsT + epsX` for every
admissible multiplier of tolerance `ε ≤ 1/2`, as soon as `4 ε √(price) ≤ epsX`. -/
theorem robust_torsion_of_positiveScale_data [NeZero d] (M : GMCModel d) {n m : ℕ}
    (hmn : m ≤ n) (omega : PotentialSample d) (z : Vec d) {p A epsT epsX eps : ℝ}
    (hp : 2 < p) (hA : 0 < A)
    (hsob : GoodCubeSobolevDisplay (aCutoff M n omega) p A
      (Section7Process.timeScale (ahom M)) (z, (3 : ℝ) ^ m))
    (hE : ellipticityMomentObservable M n (m : ℤ) (1 / 8)
      (translatePotentialSample z omega) ≤ ENNReal.ofReal 1)
    (havg : cubeAverage (originCube d (m : ℤ)) (fun x => aCutoff M n omega (x + z)) ≤ 3 / 2)
    (htest : GoodCubeTorsionComparisonTest (originCube d (m : ℤ))
      (fun x => aCutoff M n omega (x + z)) (ahom M n) epsT)
    (heps : 0 < eps) (heps2 : eps ≤ 1 / 2)
    (hmargin : 4 * eps * Real.sqrt (positiveTorsionPrice d A) ≤ epsX)
    {S : Set (Vec d)} (hS : cubeSet (z, (3 : ℝ) ^ m) ⊆ S) {th : Vec d → ℝ}
    (hadm : GoodCubeV5AdmissibleMultiplier S eps th) :
    GoodCubeTorsionComparisonTest (originCube d (m : ℤ))
      (fun x => aCutoff M n omega (x + z) * th (x + z)) (ahom M n) (epsT + epsX) := by
  set Q : TriadicCube d := originCube d (m : ℤ) with hQ
  set W : Set (Vec d) := openCubeSet Q with hW
  set b : Vec d → ℝ := fun x => aCutoff M n omega (x + z) with hbdef
  have hQm : MeasurableSet W := measurableSet_openCubeSet Q
  have hbcont : Continuous b :=
    (continuous_aCutoff M n omega).comp (continuous_id.add continuous_const)
  have hbpos : ∀ x, 0 < b x := fun x => aCutoff_pos M n omega (x + z)
  have hbeq : b = aCutoff M n (translatePotentialSample z omega) := by
    funext x
    exact (Section6Covariance.aCutoff_translatePotentialSample M n z omega x).symm
  obtain ⟨B, hB⟩ := exists_abs_bound_on_cube hbcont Q
  have hWsub : W ⊆ closure (Homogenization.cubeSet Q) :=
    (openCubeSet_subset_cubeSet Q).trans subset_closure
  have hbB : ∀ x ∈ W, b x ≤ B := fun x hx => (le_abs_self _).trans (hB x (hWsub hx))
  -- the multiplier on the origin cube
  obtain ⟨hthc, _hthpos, k, hk, hkb⟩ := hadm
  have hmaps : Set.MapsTo (fun x : Vec d => x + z) W S :=
    fun x hx => hS (add_mem_cubeSet_of_mem_openCubeSet z hx)
  have hthm : AEStronglyMeasurable (fun x => th (x + z)) (volume.restrict W) :=
    (hthc.comp (Continuous.continuousOn (by fun_prop)) hmaps).aestronglyMeasurable hQm
  have hth : ∀ x ∈ W, |k⁻¹ * th (x + z) - 1| ≤ eps := fun x hx => hkb _ (hmaps hx)
  -- weighted Poincare from the Sobolev display
  have hclock0 : 0 < Section7Process.timeScale (ahom M) ((3 : ℝ) ^ (m : ℤ)) :=
    Section7Process.timeScale_pos (ahom_pos M) (by positivity)
  have hsob0 : GoodCubeSobolevDisplay b p A (Section7Process.timeScale (ahom M))
      ((0 : Vec d), (3 : ℝ) ^ (m : ℤ)) := by
    have hsobZ : GoodCubeSobolevDisplay (aCutoff M n omega) p A
        (Section7Process.timeScale (ahom M)) (z, (3 : ℝ) ^ (m : ℤ)) := by
      rw [zpow_natCast]; exact hsob
    exact goodCubeSobolevDisplay_untranslate (p := p) (A := A) z (m : ℤ) (aCutoff M n omega)
      (continuous_aCutoff M n omega).measurable (by linarith)
      (Section7Process.timeScale (ahom M)) hsobZ
  obtain ⟨hW0, hWtop⟩ := goodCube_weightedMeasure_aCutoff_ne_zero_ne_top M n
    (translatePotentialSample z omega) ((0 : Vec d), (3 : ℝ) ^ (m : ℤ)) (by positivity)
  rw [← hbeq] at hW0 hWtop
  have hPW := poincareAssumption_of_goodCubeSobolevDisplay hp hA.le hW0 hWtop hsob0
  rw [← openCubeSet_originCube_eq_cubeSet] at hPW
  have hPoinW := poincare_real_of_weighted hQm hbcont.aestronglyMeasurable
    (fun x _ => (hbpos x).le) hbB (mul_nonneg hA.le hclock0.le) hPW
  -- unweighted Poincare from the ellipticity response test
  have hPU := Packet449.cutoff_poincare_of_ellipticity_test M n m hmn z omega
    (by norm_num : (0 : ℝ) ≤ 1) hE
  set Au : ℝ := (2 * Section8Support.WeightedEnergy.weightedLocalSobolevEnergyConstant d) ^ 2 *
    (1 + Real.sqrt 2 * 1) ^ 2 with hAu
  have hAu0 : 0 ≤ Au := by rw [hAu]; positivity
  have hs0 : 0 < cubeScaleFactor Q := by rw [hQ, cubeScaleFactor_originCube]; positivity
  have hahom : 0 < ahom M n := ahom_pos M n
  have hFu0 : 0 ≤ cubeScaleFactor Q ^ 2 / ahom M n := by positivity
  have hPoinU := poincare_real_of_unweighted hQm (fun x _ => (hbpos x).le)
    (mul_nonneg hAu0 hFu0) hPU
  -- the ellipticity field and the square-integrability of `b`
  obtain ⟨lam, Lam, _hlam, hEllAll⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_isEllipticFieldOn_aCutoff_descendants
      (j := 0) M n (translatePotentialSample z omega) Q
  have hEll : IsEllipticFieldOn lam Lam W (scalarCoeffField b) := by
    rw [hbeq]; exact hEllAll Q (by simp)
  let : IsFiniteMeasure (volume.restrict W) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hb2 : MemLp b 2 (volume.restrict W) := by
    refine MemLp.of_bound hbcont.aestronglyMeasurable B ?_
    filter_upwards [ae_restrict_mem hQm] with x hx
    simpa only [Real.norm_eq_abs] using hB x (hWsub hx)
  have hmass := setIntegral_openCubeSet_le_of_cubeAverage_le hbcont (fun x => (hbpos x).le) Q
    havg
  -- the margin
  have hclock : Section7Process.timeScale (ahom M) ((3 : ℝ) ^ (m : ℤ)) ≤
      cubeScaleFactor Q ^ 2 / ahom M n := by
    rw [zpow_natCast, Section7Process.timeScale_triadic, hQ, cubeScaleFactor_originCube,
      zpow_natCast]
    unfold Section7Process.timeScaleTriadic
    have hmn' := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ahom_le_ahom_of_le M hmn
    rw [pow_mul, ← pow_mul, mul_comm 2 m, pow_mul]
    exact div_le_div_of_nonneg_left (by positivity) hahom hmn'
  have hmargin' : 4 * eps * Real.sqrt (Au * (cubeScaleFactor Q ^ 2 / ahom M n) *
      (A * Section7Process.timeScale (ahom M) ((3 : ℝ) ^ (m : ℤ))) * (3 / 2)) ≤
      epsX * cubeScaleFactor Q ^ 2 / ahom M n := by
    set F : ℝ := cubeScaleFactor Q ^ 2 / ahom M n with hF
    have hF0 : 0 ≤ F := hFu0
    have hprod : Au * F * (A * Section7Process.timeScale (ahom M) ((3 : ℝ) ^ (m : ℤ))) * (3 / 2) ≤
        positiveTorsionPrice d A * F ^ 2 := by
      have h1 : A * Section7Process.timeScale (ahom M) ((3 : ℝ) ^ (m : ℤ)) ≤ A * F :=
        mul_le_mul_of_nonneg_left hclock hA.le
      have h2 : Au * F * (A * Section7Process.timeScale (ahom M) ((3 : ℝ) ^ (m : ℤ))) * (3 / 2) ≤
          Au * F * (A * F) * (3 / 2) := by
        have hAuF : 0 ≤ Au * F := mul_nonneg hAu0 hF0
        nlinarith [mul_le_mul_of_nonneg_left h1 hAuF]
      have h3 : Au * F * (A * F) * (3 / 2) = positiveTorsionPrice d A * F ^ 2 := by
        rw [positiveTorsionPrice, ← hAu]; ring
      linarith
    have hsqrt : Real.sqrt (Au * F * (A * Section7Process.timeScale (ahom M) ((3 : ℝ) ^ (m : ℤ))) *
        (3 / 2)) ≤ Real.sqrt (positiveTorsionPrice d A) * F := by
      calc _ ≤ Real.sqrt (positiveTorsionPrice d A * F ^ 2) := Real.sqrt_le_sqrt hprod
        _ = Real.sqrt (positiveTorsionPrice d A) * F := by
          rw [Real.sqrt_mul (positiveTorsionPrice_nonneg d hA.le), Real.sqrt_sq hF0]
    have h4e : 0 ≤ 4 * eps := by linarith
    calc 4 * eps * Real.sqrt (Au * F *
          (A * Section7Process.timeScale (ahom M) ((3 : ℝ) ^ (m : ℤ))) * (3 / 2))
        ≤ 4 * eps * (Real.sqrt (positiveTorsionPrice d A) * F) :=
          mul_le_mul_of_nonneg_left hsqrt h4e
      _ = (4 * eps * Real.sqrt (positiveTorsionPrice d A)) * F := by ring
      _ ≤ epsX * F := mul_le_mul_of_nonneg_right hmargin hF0
      _ = epsX * cubeScaleFactor Q ^ 2 / ahom M n := by rw [hF]; ring
  have hPw0 : 0 < A * Section7Process.timeScale (ahom M) ((3 : ℝ) ^ (m : ℤ)) :=
    mul_pos hA hclock0
  have hres := goodCubeTorsionComparisonTest_mul_of_poincare (Q := Q) (b := b)
    (th := fun x => th (x + z)) (k := k) (Mb := 3 / 2) heps heps2 hPw0
    (mul_nonneg hAu0 hFu0) (by norm_num) hbcont.aestronglyMeasurable hthm
    (fun x _ => (hbpos x).le) hbB hth hPoinW hPoinU hEll hb2 hmass
    (by
      have := hmargin'
      convert this using 3)
    htest
  exact hres

/-! ## Deterministic robust wrappers for the Sobolev and mass fields -/

theorem isBounded_goodCube_cubeSet (Q : Cube d) : Bornology.IsBounded (cubeSet Q) :=
  isBounded_centeredAxisCube Q.1 Q.2

/-- Step S for the actual cutoff: the display at `A` gives the display for every admissible
multiple at `3A` (`ε ≤ 1/2`); all side conditions are discharged from continuity. -/
theorem sobolev_mul_admissible_cutoff (M : GMCModel d) (L : ℕ) (omega : PotentialSample d)
    {S : Set (Vec d)} {Q : Cube d} (hQ2 : 0 < Q.2) (hQS : cubeSet Q ⊆ S)
    {p A eps : ℝ} {clock : ℝ → ℝ} (hp : 2 < p) (hA : 0 ≤ A) (hclock : 0 ≤ clock Q.2)
    (heps0 : 0 ≤ eps) (heps : eps ≤ 1 / 2) {th : Vec d → ℝ}
    (hadm : GoodCubeV5AdmissibleMultiplier S eps th)
    (hdisp : GoodCubeSobolevDisplay (aCutoff M L omega) p A clock Q) :
    GoodCubeSobolevDisplay (fun x => aCutoff M L omega x * th x) p (3 * A) clock Q := by
  have hQm : MeasurableSet (cubeSet Q) := measurableSet_cubeSet Q
  have hacont := continuous_aCutoff M L omega
  obtain ⟨B, hB⟩ := (isBounded_goodCube_cubeSet Q).isCompact_closure.exists_bound_of_continuousOn
    hacont.continuousOn
  have hBa : ∀ x ∈ cubeSet Q, |aCutoff M L omega x| ≤ B := fun x hx => by
    simpa only [Real.norm_eq_abs] using hB x (subset_closure hx)
  obtain ⟨k, hk, hkb⟩ := admissibleMultiplier_bounds hadm
  have hthB : ∀ x ∈ cubeSet Q, |th x| ≤ k * (1 + eps) := fun x hx => by
    have h := hkb x (hQS hx)
    rw [abs_of_nonneg (le_trans (by nlinarith) h.1)]
    exact h.2
  have hB0 : ∀ x ∈ cubeSet Q, 0 ≤ B := fun x hx => (abs_nonneg _).trans (hBa x hx)
  have hprodB : ∀ x ∈ cubeSet Q, |aCutoff M L omega x * th x| ≤ B * (k * (1 + eps)) :=
    fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (hBa x hx) (hthB x hx) (abs_nonneg _) (hB0 x hx)
  have hthm : AEStronglyMeasurable th (volume.restrict (cubeSet Q)) :=
    (hadm.1.mono hQS).aestronglyMeasurable hQm
  have hint1 : ∀ f : H10Function (cubeSet Q), IntegrableOn
      (fun x => aCutoff M L omega x * vecDot (f.toH1Function.grad x) (f.toH1Function.grad x))
      (cubeSet Q) := fun f =>
    integrable_coeff_mul hQm hacont.aestronglyMeasurable hBa
      (integrable_vecDot_grad f.toH1Function f.toH1Function)
  have hint2 : ∀ f : H10Function (cubeSet Q), IntegrableOn
      (fun x => aCutoff M L omega x * th x *
        vecDot (f.toH1Function.grad x) (f.toH1Function.grad x)) (cubeSet Q) := fun f =>
    integrable_coeff_mul hQm (hacont.aestronglyMeasurable.mul hthm) hprodB
      (integrable_vecDot_grad f.toH1Function f.toH1Function)
  have hWfin := (goodCube_weightedMeasure_aCutoff_ne_zero_ne_top M L omega Q hQ2).2
  have h := goodCubeSobolevDisplay_mul_of_admissible hQm hQS hp hA hclock heps0
    (by linarith) (fun x _ => (aCutoff_pos M L omega x).le) hadm hWfin hint1 hint2 hdisp
  refine goodCubeSobolevDisplay_mono_const h ?_
  have h1e : 0 < 1 - eps := by linarith
  rw [div_le_iff₀ h1e]
  nlinarith

/-- Step M for any nonnegative coefficient, with the fraction divided by three (`ε ≤ 1/2`). -/
theorem mass_mul_admissible {a : Vec d → ℝ} {S Eq Er : Set (Vec d)}
    (hEq : MeasurableSet Eq) (hEr : MeasurableSet Er) (hqS : Eq ⊆ S) (hrS : Er ⊆ S)
    (ha : ∀ x ∈ S, 0 ≤ a x) {eps mf : ℝ} (hmf : 0 ≤ mf) (heps0 : 0 ≤ eps)
    (heps : eps ≤ 1 / 2) {th : Vec d → ℝ} (hadm : GoodCubeV5AdmissibleMultiplier S eps th)
    (hmass : ENNReal.ofReal mf * weightedMeasure a Er ≤ weightedMeasure a Eq) :
    ENNReal.ofReal (mf / 3) * weightedMeasure (fun x => a x * th x) Er ≤
      weightedMeasure (fun x => a x * th x) Eq := by
  have h := mass_comparison_of_admissible hEq hEr hqS hrS ha hmf heps0 (by linarith) hadm hmass
  refine le_trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _) h
  have h1 : 0 < 1 + eps := by linarith
  rw [le_div_iff₀ h1]
  nlinarith

/-- Bounded-scale torsion: a native contrast `k ≤ a ≤ (1+τ/4)k` and an admissible multiplier of
tolerance `≤ τ/8` keep the product's contrast below `1 + τ`. -/
theorem contrast_mul_admissible {a th : Vec d → ℝ} {S : Set (Vec d)} {k tau eps : ℝ}
    (hk : 0 < k) (htau : 0 < tau) (htau1 : tau ≤ 1) (heps : eps ≤ tau / 8)
    (ha : ∀ x ∈ S, k ≤ a x ∧ a x ≤ (1 + tau / 4) * k)
    (hadm : GoodCubeV5AdmissibleMultiplier S eps th) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ∈ S, K ≤ a x * th x ∧ a x * th x ≤ (1 + tau) * K := by
  obtain ⟨k', hk', hkb⟩ := admissibleMultiplier_bounds hadm
  have he1 : 0 < 1 - eps := by linarith
  refine ⟨k * (k' * (1 - eps)), by positivity, fun x hx => ?_⟩
  obtain ⟨ha1, ha2⟩ := ha x hx
  obtain ⟨ht1, ht2⟩ := hkb x hx
  have hth0 : 0 ≤ k' * (1 - eps) := by positivity
  constructor
  · exact mul_le_mul ha1 ht1 hth0 (hk.le.trans ha1)
  · have hup : a x * th x ≤ (1 + tau / 4) * k * (k' * (1 + eps)) :=
      mul_le_mul ha2 ht2 (hth0.trans ht1) (by positivity)
    refine hup.trans ?_
    have hkk : 0 < k * k' := mul_pos hk hk'
    have hineq : (1 + tau / 4) * (1 + eps) ≤ (1 + tau) * (1 - eps) := by nlinarith
    calc (1 + tau / 4) * k * (k' * (1 + eps)) = (k * k') * ((1 + tau / 4) * (1 + eps)) := by ring
      _ ≤ (k * k') * ((1 + tau) * (1 - eps)) := mul_le_mul_of_nonneg_left hineq hkk.le
      _ = (1 + tau) * (k * (k' * (1 - eps))) := by ring

/-! ## The positive-scale ambient event, retaining the ellipticity test -/

/-- `exists_goodCube_positiveScale_finite_ambient_tests` with the level-one ellipticity response
test exported as well (it is already on the same event; the original proof discards it). -/
theorem exists_goodCube_positiveScale_finite_ambient_data
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p A : ℝ, 2 < p ∧ 1 ≤ A ∧
      (∀ (M : GMCModel d) (L : ℕ) (omega : PotentialSample d) (m : ℤ) (z : Vec d),
        (∃ c : ℝ, 0 < c ∧ ∀ x ∈ openCubeSet (originCube d m),
          c ≤ aCutoff M L omega (x + z) ∧ aCutoff M L omega (x + z) ≤ 2 * c) →
        GoodCubeSobolevDisplay (aCutoff M L omega) p A
          (Section7Process.timeScale (ahom M)) (z, (3 : ℝ) ^ m)) ∧
      ∀ (J N : ℕ) (eps : ℝ), 0 < eps →
        ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
          ∀ M : GMCModel d, M.delta ≤ c → ∀ (n : ℕ) (F : Finset (ℕ × Vec d)),
            F.card ≤ N → (∀ q ∈ F, q.1 ≤ n ∧ n - q.1 ≤ J) →
            ∃ Bad : Set (PotentialSample d), MeasurableSet Bad ∧
              M.P.toMeasure Bad ≤ ENNReal.ofReal
                (Real.exp (-(c ^ 2 / (M.delta ^ 2 * (Real.log M.delta) ^ 2)))) ∧
              ∀ omega, omega ∉ Bad → ∀ q ∈ F,
                GoodCubeSobolevDisplay (aCutoff M n omega) p A
                  (Section7Process.timeScale (ahom M)) (q.2, (3 : ℝ) ^ q.1) ∧
                ellipticityMomentObservable M n (q.1 : ℤ) (1 / 8)
                  (translatePotentialSample q.2 omega) ≤ ENNReal.ofReal 1 ∧
                ((1 / 2 : ℝ) ≤ cubeAverage (originCube d (q.1 : ℤ))
                    (fun x => aCutoff M n omega (x + q.2)) ∧
                  cubeAverage (originCube d (q.1 : ℤ))
                    (fun x => aCutoff M n omega (x + q.2)) ≤ 3 / 2) ∧
                GoodCubeTorsionComparisonTest (originCube d (q.1 : ℤ))
                  (fun x => aCutoff M n omega (x + q.2)) (ahom M n) eps := by
  classical
  obtain ⟨p, A, hp, hA, hratio, hpositive⟩ := exists_goodCube_sobolev_common_tests d hd
  refine ⟨p, A, hp, hA, hratio, ?_⟩
  intro J N eps heps
  obtain ⟨cS, hcS, _, hS⟩ := exists_goodCube_positiveScale_ambient_tail d J hd 1 1
    (by norm_num) (by norm_num)
  obtain ⟨cT, hcT, _, hT⟩ := exists_goodCube_positiveScale_weightedTorsion_ambient_tail
    d J hd eps heps
  obtain ⟨c, hc, hccS, hccT, hchalf, hbudget⟩ :=
    goodCube_exists_finite_test_threshold J N cS cT hcS hcT
  refine ⟨c, hc, hchalf, ?_⟩
  intro M hM n F hF hdepth
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  obtain ⟨hclockBudget, htailBudget⟩ := hbudget M.delta hdelta hM
  let a : ℝ := (min cS cT) ^ 2
  let D : ℝ := M.delta ^ 2 * (Real.log M.delta) ^ 2
  let B : ℝ≥0∞ := ENNReal.ofReal (2 * Real.exp (-a / D))
  let P : (ℕ × Vec d) → PotentialSample d → Prop := fun q omega =>
    GoodCubeSobolevDisplay (aCutoff M n omega) p A
        (Section7Process.timeScale (ahom M)) (q.2, (3 : ℝ) ^ q.1) ∧
      ellipticityMomentObservable M n (q.1 : ℤ) (1 / 8)
        (translatePotentialSample q.2 omega) ≤ ENNReal.ofReal 1 ∧
      ((1 / 2 : ℝ) ≤ cubeAverage (originCube d (q.1 : ℤ))
          (fun x => aCutoff M n omega (x + q.2)) ∧
        cubeAverage (originCube d (q.1 : ℤ))
          (fun x => aCutoff M n omega (x + q.2)) ≤ 3 / 2) ∧
      GoodCubeTorsionComparisonTest (originCube d (q.1 : ℤ))
        (fun x => aCutoff M n omega (x + q.2)) (ahom M n) eps
  have hD : 0 < D := by
    have hlog : Real.log M.delta < 0 :=
      Real.log_neg hdelta ((hM.trans hchalf).trans_lt (by norm_num))
    exact mul_pos (sq_pos_of_pos hdelta) (sq_pos_of_ne_zero (ne_of_lt hlog))
  have haS : a ≤ cS ^ 2 := by
    dsimp [a]
    nlinarith [min_le_left cS cT, lt_min hcS hcT]
  have haT : a ≤ cT ^ 2 := by
    dsimp [a]
    nlinarith [min_le_right cS cT, lt_min hcS hcT]
  have hES : Real.exp (-(cS ^ 2 / D)) ≤ Real.exp (-a / D) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg (div_le_div_of_nonneg_right haS hD.le)
  have hET : Real.exp (-(cT ^ 2 / D)) ≤ Real.exp (-a / D) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg (div_le_div_of_nonneg_right haT hD.le)
  have hsingle : ∀ q ∈ F, ∃ Bad : Set (PotentialSample d), MeasurableSet Bad ∧
      M.P.toMeasure Bad ≤ B ∧ ∀ omega, omega ∉ Bad → P q omega := by
    intro q hq
    obtain ⟨hmn, hmJ⟩ := hdepth q hq
    obtain ⟨BadS, hBadSmeas, hBadStail, hBadSgood⟩ :=
      hS M (hM.trans hccS) n q.1 hmn hmJ q.2
    obtain ⟨BadT, hBadTmeas, hBadTtail, hBadTgood⟩ :=
      hT M (hM.trans hccT) n q.1 hmn hmJ q.2
    refine ⟨BadS ∪ BadT, hBadSmeas.union hBadTmeas, ?_, ?_⟩
    · calc
        _ ≤ M.P.toMeasure BadS + M.P.toMeasure BadT := measure_union_le _ _
        _ ≤ ENNReal.ofReal (Real.exp (-a / D)) +
            ENNReal.ofReal (Real.exp (-a / D)) :=
          add_le_add (hBadStail.trans (ENNReal.ofReal_le_ofReal hES))
            (hBadTtail.trans (ENNReal.ofReal_le_ofReal hET))
        _ = B := by
          dsimp [B]
          rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, two_mul]
    · intro omega homega
      have hnotS : omega ∉ BadS := fun h => homega (Or.inl h)
      have hnotT : omega ∉ BadT := fun h => homega (Or.inr h)
      obtain ⟨hE, _, hmass, _, hnorm⟩ := hBadSgood omega hnotS
      have hcoeff : aCutoff M n (translatePotentialSample q.2 omega) =
          fun x => aCutoff M n omega (x + q.2) := by
        funext x
        exact Section6Covariance.aCutoff_translatePotentialSample M n q.2 omega x
      rw [hcoeff] at hmass hnorm
      obtain ⟨_, hb, _⟩ := goodCube_cutoff_sobolev_data M n omega q.2
        (originCube d (q.1 : ℤ))
      have hclock := goodCube_ahom_scale_comparison M n q.1 J hmn hmJ hclockBudget
      have hsob := hpositive M n q.1 hmn omega q.2
        (by simpa only [ENNReal.ofReal_one] using hE)
        hmass.2 hclock hb (hnorm hb)
      refine ⟨hsob, hE, hmass, ?_⟩
      unfold GoodCubeTorsionComparisonTest
      simpa only [hcoeff] using hBadTgood omega hnotT
  obtain ⟨Bad, hBadmeas, hBadtail, hBadgood⟩ :=
    goodCube_exists_finite_bad_majorant M.P.toMeasure F B P hsingle
  refine ⟨Bad, hBadmeas, ?_, hBadgood⟩
  have hcard : (F.card : ℝ) ≤ (N : ℝ) + 1 := by
    have hFN : (F.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hF
    linarith
  have hfinite : (F.card : ℝ≥0∞) * B ≤
      ENNReal.ofReal ((2 * ((N : ℝ) + 1)) * Real.exp (-a / D)) := by
    dsimp [B]
    rw [← ENNReal.ofReal_natCast F.card, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      (F.card : ℝ) * (2 * Real.exp (-a / D)) ≤
          ((N : ℝ) + 1) * (2 * Real.exp (-a / D)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (2 * ((N : ℝ) + 1)) * Real.exp (-a / D) := by ring
  exact hBadtail.trans (hfinite.trans (ENNReal.ofReal_le_ofReal htailBudget))

/-! ## The robust ambient catalogue event -/

/-- The multiplier tolerance for the catalogue, chosen after the torsion tolerance `eps`, the
contrast `tau` of the bounded-scale torsion test and the positive-scale price. -/
def catalogueTolerance (P tau eps : ℝ) : ℝ :=
  min (min (1 / 4) (tau / 8)) (eps / (8 * (Real.sqrt P + 1)))

theorem catalogueTolerance_spec {P tau eps : ℝ} (htau : 0 < tau) (heps : 0 < eps) :
    0 < catalogueTolerance P tau eps ∧ catalogueTolerance P tau eps ≤ 1 / 4 ∧
      catalogueTolerance P tau eps ≤ tau / 8 ∧
      4 * catalogueTolerance P tau eps * Real.sqrt P ≤ eps / 2 := by
  have hs : 0 ≤ Real.sqrt P := Real.sqrt_nonneg P
  have hden : 0 < 8 * (Real.sqrt P + 1) := by positivity
  refine ⟨lt_min (lt_min (by norm_num) (by positivity)) (div_pos heps hden),
    (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _), ?_⟩
  have h1 : catalogueTolerance P tau eps ≤ eps / (8 * (Real.sqrt P + 1)) := min_le_right _ _
  have h0 : 0 ≤ catalogueTolerance P tau eps :=
    (lt_min (lt_min (by norm_num) (by positivity)) (div_pos heps hden)).le
  calc 4 * catalogueTolerance P tau eps * Real.sqrt P
      ≤ 4 * (eps / (8 * (Real.sqrt P + 1))) * Real.sqrt P := by gcongr
    _ ≤ 4 * (eps / (8 * (Real.sqrt P + 1))) * (Real.sqrt P + 1) := by
        gcongr; linarith
    _ = eps / 2 := by field_simp; ring

/-- **The robust ambient catalogue.**  One ambient event, with the same tail as the ordinary
catalogue, on which the Sobolev (`3A`), torsion (`eps`) and mass (`θ_J/9`) tests hold for the
product of the actual cutoff with **every** multiplier admissible on the native parent at the
tolerance `epsilon`, which is chosen after `eps`. -/
theorem exists_goodCube_finite_catalogue_ambient_tests_robust
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ p A : ℝ, 2 < p ∧ 1 ≤ A ∧
      ∀ (J N : ℕ) (eps : ℝ), 0 < eps →
        ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 / 4 ∧
        ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
          ∀ M : GMCModel d, M.delta ≤ c →
          ∀ (n : ℕ) (G : Finset (ℕ × Vec d)), G.card ≤ N →
            (∀ q ∈ G, q.1 ≤ J) →
            (∀ q ∈ G, cubeSet (q.2, (3 : ℝ) ^ (-(q.1 : ℤ))) ⊆
              cubeSet ((0 : Vec d), (1 : ℝ))) →
            ∃ Bad : Set (PotentialSample d), MeasurableSet Bad ∧
              M.P.toMeasure Bad ≤ ENNReal.ofReal
                (Real.exp (-(c ^ 2 / (M.delta ^ 2 * (Real.log M.delta) ^ 2)))) ∧
              ∀ omega, omega ∉ Bad → ∀ th : Vec d → ℝ,
                GoodCubeV5AdmissibleMultiplier (cubeSet ((0 : Vec d), (3 : ℝ) ^ n)) epsilon th →
                (∀ q ∈ G,
                  GoodCubeSobolevDisplay (fun x => aCutoff M n omega x * th x) p A
                    (Section7Process.timeScale (ahom M))
                    ((3 : ℝ) ^ n • q.2, (3 : ℝ) ^ ((n : ℤ) - q.1)) ∧
                  GoodCubeTorsionComparisonTest (originCube d ((n : ℤ) - q.1))
                    (fun x => aCutoff M n omega (x + (3 : ℝ) ^ n • q.2) *
                      th (x + (3 : ℝ) ^ n • q.2))
                    (if J ≤ n then ahom M n else 1) eps) ∧
                ∀ q ∈ G, ∀ r ∈ G,
                  ENNReal.ofReal ((((3 : ℝ) ^ (-(J : ℤ))) ^ d) / 9) *
                      weightedMeasure (fun x => aCutoff M n omega x * th x)
                        (cubeSet ((3 : ℝ) ^ n • r.2, (3 : ℝ) ^ ((n : ℤ) - r.1))) ≤
                    weightedMeasure (fun x => aCutoff M n omega x * th x)
                      (cubeSet ((3 : ℝ) ^ n • q.2, (3 : ℝ) ^ ((n : ℤ) - q.1))) := by
  classical
  obtain ⟨p, A, hp, hA, hnear, hpositive⟩ := exists_goodCube_positiveScale_finite_ambient_data d hd
  refine ⟨p, 3 * A, hp, by linarith, ?_⟩
  intro J N eps heps
  obtain ⟨tau, htau, htau1, hcontrastTest⟩ :=
    exists_goodCube_uniformContrast_torsionComparison d eps heps
  set epsilon : ℝ := catalogueTolerance (positiveTorsionPrice d A) tau eps with hepsilondef
  obtain ⟨hepsilon0, hepsilon4, hepsilonTau, hepsilonPrice⟩ :=
    catalogueTolerance_spec (P := positiveTorsionPrice d A) htau heps
  have hepsilon2 : epsilon ≤ 1 / 2 := hepsilon4.trans (by norm_num)
  refine ⟨epsilon, hepsilon0, hepsilon4, ?_⟩
  obtain ⟨cB, hcB, _, hcontrast⟩ :=
    exists_goodCube_boundedScale_coefficient_contrast d J (eps := tau / 4) (by positivity)
  obtain ⟨cP, hcP, _, hpositiveTail⟩ := hpositive J N (eps / 2) (by positivity)
  let a : ℝ := min (cP ^ 2) 1
  let b : ℝ := min cP cB
  obtain ⟨c, hc, hcb, hchalf, habsorb⟩ := goodCube_exists_finite_tail_absorption
    2 a b (by norm_num) (lt_min (sq_pos_of_pos hcP) zero_lt_one) (lt_min hcP hcB)
  have hccP : c ≤ cP := hcb.trans (min_le_left _ _)
  have hccB : c ≤ cB := hcb.trans (min_le_right _ _)
  refine ⟨c, hc, hchalf, ?_⟩
  intro M hM n G hcard hdepth hinside
  let D : ℝ := M.delta ^ 2 * (Real.log M.delta) ^ 2
  let thetaJ : ℝ := ((3 : ℝ) ^ (-(J : ℤ))) ^ d
  have hthetaJ : 0 ≤ thetaJ := by positivity
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hD : 0 < D := by
    have hlog : Real.log M.delta < 0 :=
      Real.log_neg hdelta ((hM.trans hchalf).trans_lt (by norm_num))
    exact mul_pos (sq_pos_of_pos hdelta) (sq_pos_of_ne_zero (ne_of_lt hlog))
  have hdecay (t : ℝ) (hat : a ≤ t) : Real.exp (-(t / D)) ≤ Real.exp (-a / D) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg (div_le_div_of_nonneg_right hat hD.le)
  have hbudget : 2 * Real.exp (-a / D) ≤ Real.exp (-(c ^ 2 / D)) :=
    habsorb M.delta hdelta hM
  have hptail : ENNReal.ofReal (Real.exp (-(cP ^ 2 / D))) ≤
      ENNReal.ofReal (Real.exp (-(c ^ 2 / D))) := by
    apply ENNReal.ofReal_le_ofReal
    exact (hdecay (cP ^ 2) (min_le_left _ _)).trans
      ((by linarith [Real.exp_pos (-a / D)] : Real.exp (-a / D) ≤
        2 * Real.exp (-a / D)).trans hbudget)
  have hbtail : ENNReal.ofReal (2 * Real.exp (-(1 / D))) ≤
      ENNReal.ofReal (Real.exp (-(c ^ 2 / D))) :=
    ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left
      (hdecay 1 (min_le_right _ _)) (by norm_num)).trans hbudget)
  have hvolume (q : ℕ × Vec d) (hq : q ∈ G) (r : ℕ × Vec d) (hr : r ∈ G) :
      ENNReal.ofReal thetaJ *
        volume (cubeSet ((3 : ℝ) ^ n • r.2, (3 : ℝ) ^ ((n : ℤ) - r.1))) ≤
      volume (cubeSet ((3 : ℝ) ^ n • q.2, (3 : ℝ) ^ ((n : ℤ) - q.1))) :=
    goodCube_catalogue_volume_floor n J q.1 r.1 q.2 r.2 (hdepth q hq) (hdepth r hr)
  have hsub (q : ℕ × Vec d) (hq : q ∈ G) :
      cubeSet ((3 : ℝ) ^ n • q.2, (3 : ℝ) ^ ((n : ℤ) - q.1)) ⊆
        cubeSet ((0 : Vec d), (3 : ℝ) ^ n) :=
    goodCube_catalogue_cube_subset_parent n q.1 q.2 (hinside q hq)
  have hside (q : ℕ × Vec d) : 0 < (3 : ℝ) ^ ((n : ℤ) - q.1) := by positivity
  have hSm : MeasurableSet (cubeSet ((0 : Vec d), (3 : ℝ) ^ n)) := measurableSet_cubeSet _
  by_cases hn : J ≤ n
  · let F := G.image (fun q => (n - q.1, (3 : ℝ) ^ n • q.2))
    obtain ⟨hFcard, hFdepth, hscale⟩ :=
      goodCube_catalogue_positive_indices n J N hn G hcard hdepth
    obtain ⟨Bad, hBadmeas, hBadtail, hBadgood⟩ :=
      hpositiveTail M (hM.trans hccP) n F hFcard hFdepth
    refine ⟨Bad, hBadmeas, hBadtail.trans hptail, ?_⟩
    intro omega homega th hadm
    have hmem (q : ℕ × Vec d) (hq : q ∈ G) :
        (n - q.1, (3 : ℝ) ^ n • q.2) ∈ F := Finset.mem_image_of_mem _ hq
    constructor
    · intro q hq
      obtain ⟨hsob, hE, hmass, htor⟩ := hBadgood omega homega _ (hmem q hq)
      have hqn : q.1 ≤ n := (hdepth q hq).trans hn
      have hsobZ : GoodCubeSobolevDisplay (aCutoff M n omega) p A
          (Section7Process.timeScale (ahom M))
          ((3 : ℝ) ^ n • q.2, (3 : ℝ) ^ ((n : ℤ) - q.1)) := by
        simpa only [(hscale q hq).2] using hsob
      refine ⟨sobolev_mul_admissible_cutoff M n omega (hside q) (hsub q hq) hp
        (by linarith) (Section7Process.timeScale_pos (ahom_pos M) (hside q)).le
        hepsilon0.le hepsilon2 hadm hsobZ, ?_⟩
      have hS' : cubeSet ((3 : ℝ) ^ n • q.2, (3 : ℝ) ^ (n - q.1)) ⊆
          cubeSet ((0 : Vec d), (3 : ℝ) ^ n) := by
        simpa only [(hscale q hq).2] using hsub q hq
      have hrob := robust_torsion_of_positiveScale_data M (Nat.sub_le n q.1) omega
        ((3 : ℝ) ^ n • q.2) (epsT := eps / 2) (epsX := eps / 2) hp (by linarith) hsob hE
        hmass.2 htor hepsilon0 hepsilon2 hepsilonPrice hS' hadm
      rw [ite_eq_left hn, (hscale q hq).1]
      simpa only [add_halves] using hrob
    · intro q hq r hr
      have hqavg := (hBadgood omega homega _ (hmem q hq)).2.2.1
      have hravg := (hBadgood omega homega _ (hmem r hr)).2.2.1
      have hm := goodCube_cutoff_physical_mass_ratio M n omega
        ((n : ℤ) - q.1) ((n : ℤ) - r.1)
        ((3 : ℝ) ^ n • q.2) ((3 : ℝ) ^ n • r.2) hthetaJ (hvolume q hq r hr)
        (by simpa only [(hscale q hq).1] using hqavg.1)
        (by simpa only [(hscale r hr).1] using hravg.2)
      have hrob := mass_mul_admissible (measurableSet_cubeSet _) (measurableSet_cubeSet _)
        (hsub q hq) (hsub r hr) (fun x _ => (aCutoff_pos M n omega x).le)
        (by positivity) hepsilon0.le hepsilon2 hadm hm
      have heq : thetaJ / 3 / 3 = thetaJ / 9 := by ring
      rw [heq] at hrob
      exact hrob
  · let Raw := coefficientLocalBadEvent M n 1 (goodCubeBad M n) (0 : Lattice d)
    let Bad := toMeasurable M.P.toMeasure Raw
    have hRawTail : M.P.toMeasure Raw ≤ ENNReal.ofReal (2 * Real.exp (-(1 / D))) := by
      have ht := measure_coefficientLocalBadEvent_goodCubeBad_le M n (0 : Lattice d)
      rw [tailIndex_sq] at ht
      exact ht
    have hBadTail : M.P.toMeasure Bad ≤ ENNReal.ofReal (Real.exp (-(c ^ 2 / D))) := by
      rw [show M.P.toMeasure Bad = M.P.toMeasure Raw from measure_toMeasurable Raw]
      exact hRawTail.trans hbtail
    refine ⟨Bad, measurableSet_toMeasurable _ _, hBadTail, ?_⟩
    intro omega homega th hadm
    have hnotRaw : omega ∉ Raw := fun h => homega (subset_toMeasurable _ _ h)
    obtain ⟨k, hk, hbound⟩ := hcontrast M (hM.trans hccB) n (by omega) 0 omega hnotRaw
    have hnative : nativeBox n 1 (0 : Lattice d) = cubeSet ((0 : Vec d), (3 : ℝ) ^ n) := by
      simp only [nativeBox, one_mul, goodCubeCentre_zero_lattice, cubeSet]
    have hboundParent : ∀ x ∈ cubeSet ((0 : Vec d), (3 : ℝ) ^ n),
        k ≤ aCutoff M n omega x ∧ aCutoff M n omega x ≤ (1 + tau / 4) * k := by
      intro x hx
      have hh := hbound x (by rwa [hnative])
      exact ⟨hh.1, hh.2.1⟩
    have hfactor : (1 + tau / 4) * k ≤ 2 * k := by nlinarith
    have hboundTwo : ∀ x ∈ cubeSet ((0 : Vec d), (3 : ℝ) ^ n),
        k ≤ aCutoff M n omega x ∧ aCutoff M n omega x ≤ 2 * k :=
      fun x hx => ⟨(hboundParent x hx).1, (hboundParent x hx).2.trans hfactor⟩
    obtain ⟨K, hK, hKb⟩ := contrast_mul_admissible hk htau htau1 hepsilonTau hboundParent hadm
    constructor
    · intro q hq
      have hlocal : ∀ x ∈ openCubeSet (originCube d ((n : ℤ) - q.1)),
          x + (3 : ℝ) ^ n • q.2 ∈ cubeSet ((0 : Vec d), (3 : ℝ) ^ n) :=
        fun x hx => hsub q hq (goodCube_catalogue_pullback_mem_physical n q.1 q.2 x hx)
      have hsob := hnear M n omega ((n : ℤ) - q.1) ((3 : ℝ) ^ n • q.2)
        ⟨k, hk, fun x hx => hboundTwo _ (hlocal x hx)⟩
      refine ⟨sobolev_mul_admissible_cutoff M n omega (hside q) (hsub q hq) hp
        (by linarith) (Section7Process.timeScale_pos (ahom_pos M) (hside q)).le
        hepsilon0.le hepsilon2 hadm hsob, ?_⟩
      rw [ite_eq_right hn]
      refine hcontrastTest (originCube d ((n : ℤ) - q.1))
        (fun x => aCutoff M n omega (x + (3 : ℝ) ^ n • q.2) * th (x + (3 : ℝ) ^ n • q.2))
        K hK ?_ (fun x hx => hKb _ (hlocal x hx))
      have hmaps : Set.MapsTo (fun x : Vec d => x + (3 : ℝ) ^ n • q.2)
          (openCubeSet (originCube d ((n : ℤ) - q.1))) (cubeSet ((0 : Vec d), (3 : ℝ) ^ n)) :=
        fun x hx => hlocal x hx
      exact ((continuous_aCutoff M n omega).comp
          (continuous_id.add continuous_const)).continuousOn.mul
        (hadm.1.comp (Continuous.continuousOn (by fun_prop)) hmaps)
    · intro q hq r hr
      have hm := goodCube_cutoff_physical_mass_ratio_of_local_factor_two M n omega
        ((3 : ℝ) ^ n • q.2, (3 : ℝ) ^ ((n : ℤ) - q.1))
        ((3 : ℝ) ^ n • r.2, (3 : ℝ) ^ ((n : ℤ) - r.1))
        (hsub q hq) (hsub r hr) hk hthetaJ hboundTwo (hvolume q hq r hr)
      have hrob := mass_mul_admissible (measurableSet_cubeSet _) (measurableSet_cubeSet _)
        (hsub q hq) (hsub r hr) (fun x _ => (aCutoff_pos M n omega x).le)
        (by positivity) hepsilon0.le hepsilon2 hadm hm
      refine le_trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _) hrob
      have : 0 ≤ thetaJ := hthetaJ
      linarith

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.RobustGoodCube
