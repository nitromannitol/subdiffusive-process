import SubdiffusiveProcess.Paper.prop_neumann_growth_assembly
import SubdiffusiveProcess.Paper.rem_resolved_uniform
import SubdiffusiveProcess.Paper.lane4_lambda_inv_moments_uniform

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper



theorem prop_neumann_growth_assembly_uniform :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (t : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (rho : ℝ → ℝ), ContDiff ℝ ∞ rho → (∀ tau, 0 ≤ rho tau) →
      (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) → (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ), (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∃ (Cbound : Fin k → ℝ),
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∃ (K : ℕ → BilateralField d → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ) (eps : ℝ), 0 < eps → eps < 1 / 8 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
              (faceBump rho pvec eps) v →
          ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ unitNeumannCube d →
            0 < rad → rad ≤ 1 →
            localGradientEnergy
                (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                (s := Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
                (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
              K N om * eps ^ (-2 : ℝ) * rad ^ t := by
  intro d hd _ _ E P X W D t k ps htlo hthi hps
  have hps2 : ∀ i : Fin k, 1 ≤ 2 * ps i := fun i => by linarith [hps i]
  obtain ⟨δres, hδres, Cres, hres⟩ :=
    rem_resolved_uniform d hd E P X W D t k (fun i => 2 * ps i) htlo hthi hps2
  have hlamI := fun i : Fin k =>
    lane4_lambda_inv_moments_uniform d hd E (1 / 8 : ℝ) ⟨by norm_num, by norm_num⟩
      (fun _ => (1 / 2 : ℝ)) 1 one_pos le_rfl (2 * ps i) (hps2 i)
  choose deltaS hdeltaS_pos KS hKS_pos hlamMain using hlamI
  refine ⟨min δres (1 / (1 + ∑ j : Fin k, 1 / deltaS j)),
    lt_min hδres (aux_prop_neumann_growth_delta_pos _ hdeltaS_pos), ?_⟩
  intro rho hrho hrho0 hsupp hint pvec hpvec
  -- the face-bump amplitude (unchanged: never depended on `M`)
  have hcs : HasCompactSupport rho := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) ?_
    intro tau htau
    exact hsupp tau (fun h => htau ⟨h.1.le, h.2.le⟩)
  obtain ⟨Mrho, hMrho⟩ := hrho.continuous.bounded_above_of_compact_support hcs
  set Krho : ℝ := max Mrho 0 with hKrhodef
  have hKrho : ∀ tau : ℝ, |rho tau| ≤ Krho := by
    intro tau
    rw [← Real.norm_eq_abs]
    exact (hMrho tau).trans (le_max_left _ _)
  set Dr : ℝ := (∑ i : Fin d, |pvec i|) * (2 * Krho) with hDrdef
  have hDr : 0 ≤ Dr := by
    have : 0 ≤ Krho := le_max_right _ _
    positivity
  have hload := fun (eps : ℝ) (heps : 0 < eps) (heps8 : eps < 1 / 8) =>
    lane4_smoothed_load_properties d rho hrho hsupp Krho hKrho pvec eps heps heps8
  have hface : ∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ∀ y : SpatialCoordinates d,
      |faceBump rho pvec eps y| ≤ Dr * eps⁻¹ := by
    intro eps heps heps8 y
    simpa only [faceBump, lane4_smoothed_neumann_load] using (hload eps heps heps8).2.1 y
  have hfaceMeas : ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
      AEStronglyMeasurable (faceBump rho pvec eps)
        (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) := by
    intro eps heps heps8
    have hc := (hload eps heps heps8).1.continuous
    simpa only [faceBump, lane4_smoothed_neumann_load] using hc.aestronglyMeasurable
  obtain ⟨Cp, hCpdef⟩ : ∃ Cp : Fin k → ℝ,
      Cp = fun i => max (max (Cres i) (P.C ^ 2 * KS i)) 0 :=
    ⟨_, rfl⟩
  refine ⟨fun i => Dr ^ 2 * (Cp i * (1 + Cp i)), ?_⟩
  intro M Rm Sreg It H HI hδ
  have hδM : M.delta ≤ δres := hδ.trans (min_le_left _ _)
  have hδMi : ∀ i : Fin k, M.delta ≤ deltaS i := fun i =>
    (hδ.trans (min_le_right _ _)).trans (aux_prop_neumann_growth_delta_min _ hdeltaS_pos i)
  obtain ⟨Kres, hKres0, hKresMem, hKresBd, hae⟩ := hres M Rm Sreg It H HI hδM
  -- the random constant (unchanged construction)
  obtain ⟨Lam, hLamdef⟩ : ∃ Lam : ℕ → BilateralField d → ℝ, Lam = fun N om =>
      (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
        (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
        (fun _ => (1 / 2 : ℝ)) 1 (1 / 8 : ℝ) 1)⁻¹ := ⟨_, rfl⟩
  have hLamMem' : ∀ i N, MemLp (Lam N) (ENNReal.ofReal (2 * ps i))
      (chaosSampleLaw M).toMeasure := by
    intro i N; rw [hLamdef]; exact (hlamMain i M Rm H HI (hδMi i) N).1
  have hLamBd' : ∀ i N, eLpNorm (Lam N) (ENNReal.ofReal (2 * ps i))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (KS i) := by
    intro i N; rw [hLamdef]; exact (hlamMain i M Rm H HI (hδMi i) N).2
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ → BilateralField d → ℝ, K = fun N om =>
      Dr ^ 2 * (Kres N om * (1 + P.C ^ 2 * Lam N om)) := ⟨_, rfl⟩
  have hmom : ∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Dr ^ 2 * (Cp i * (1 + Cp i))) := by
    intro i N
    have hCp0 : 0 ≤ Cp i := by rw [hCpdef]; exact le_max_right _ _
    have hV : MemLp (fun om => P.C ^ 2 * Lam N om) (ENNReal.ofReal (2 * ps i))
        (chaosSampleLaw M).toMeasure := (hLamMem' i N).const_mul _
    have hVb : eLpNorm (fun om => P.C ^ 2 * Lam N om) (ENNReal.ofReal (2 * ps i))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp i) := by
      calc
        eLpNorm (fun om => P.C ^ 2 * Lam N om) (ENNReal.ofReal (2 * ps i))
            (chaosSampleLaw M).toMeasure ≤
            ‖P.C ^ 2‖ₑ * eLpNorm (Lam N) (ENNReal.ofReal (2 * ps i))
              (chaosSampleLaw M).toMeasure := by
          exact eLpNorm_const_smul_le (c := P.C ^ 2) (f := Lam N)
            (p := ENNReal.ofReal (2 * ps i)) (μ := (chaosSampleLaw M).toMeasure)
        _ ≤ ‖P.C ^ 2‖ₑ * ENNReal.ofReal (KS i) := by gcongr; exact hLamBd' i N
        _ = ENNReal.ofReal (P.C ^ 2 * KS i) := by
          rw [Real.enorm_eq_ofReal (by positivity)]
          exact (ENNReal.ofReal_mul (by positivity)).symm
        _ ≤ ENNReal.ofReal (Cp i) := by
          rw [hCpdef]
          exact ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_left _ _))
    have hUb : eLpNorm (Kres N) (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cp i) :=
      (hKresBd i N).trans (by
        rw [hCpdef]
        exact ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_left _ _)))
    obtain ⟨hUVmem, hUVb⟩ := aux_rem_resolved_UV_moment (chaosSampleLaw M).toMeasure
      (ps i) (Cp i) (hps i) hCp0 (Kres N) (fun om => P.C ^ 2 * Lam N om)
      (hKresMem i N) hV hUb hVb
    refine ⟨by rw [hKdef]; exact hUVmem.const_mul (Dr ^ 2), ?_⟩
    calc
      eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ‖Dr ^ 2‖ₑ * eLpNorm (fun om => Kres N om * (1 + P.C ^ 2 * Lam N om))
            (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure := by
        rw [hKdef]
        exact eLpNorm_const_smul_le (c := Dr ^ 2)
          (f := fun om => Kres N om * (1 + P.C ^ 2 * Lam N om))
          (p := ENNReal.ofReal (ps i)) (μ := (chaosSampleLaw M).toMeasure)
      _ ≤ ‖Dr ^ 2‖ₑ * ENNReal.ofReal (Cp i * (1 + Cp i)) := by gcongr
      _ = ENNReal.ofReal (Dr ^ 2 * (Cp i * (1 + Cp i))) := by
        rw [Real.enorm_eq_ofReal (by positivity)]
        exact (ENNReal.ofReal_mul (by positivity)).symm
  refine ⟨K, fun i N => (hmom i N).1, fun i N => (hmom i N).2, ?_⟩
  filter_upwards [hae] with om hom
  intro N eps heps heps8 v hsol x rad hx hrad hrad1
  have hloc := hom.2 N rho hrho hrho0 hsupp hint pvec hpvec Dr hDr
    (fun e he he8 y _ => hface e he he8 y) eps heps heps8 v hsol x hx rad hrad hrad1
  have hEn := aux_prop_neumann_growth_global_energy hd E P
    (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
    (faceBump rho pvec eps) (hfaceMeas eps heps heps8) (Dr * eps⁻¹)
    (mul_nonneg hDr (inv_nonneg.mpr heps.le)) (hface eps heps heps8) v hsol
  have hlampos := E.lam_pos (fun _ => (1 / 2 : ℝ)) 1 one_pos
    (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
    (fun _ => (1 / 2 : ℝ)) 1 (1 / 8 : ℝ) 1
  have hmono := E.lam_mono (fun _ => (1 / 2 : ℝ)) 1 one_pos
    (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
    (fun _ => (1 / 2 : ℝ)) 1 1 (1 / 8 : ℝ) 1 (by norm_num)
  have hinv : (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
      (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
      (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹ ≤ Lam N om :=
    by rw [hLamdef]; exact inv_anti₀ hlampos hmono
  have he2 : eps ^ (-2 : ℝ) = (eps⁻¹) ^ 2 := by
    rw [Real.rpow_neg heps.le, inv_pow]
    norm_cast
  have hEn' : sobolevCoefficientForm
      (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
      (v : SobolevData (unitNeumannCube d)) (v : SobolevData (unitNeumannCube d)) ≤
      Dr ^ 2 * eps ^ (-2 : ℝ) * P.C ^ 2 *
        (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
          (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
          (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹ := by
    rw [he2]; convert hEn using 2; ring
  rw [hKdef]
  exact aux_prop_neumann_growth_combine _ (Kres N om) _ Dr (eps ^ (-2 : ℝ)) P.C _ (Lam N om)
    (rad ^ t) (hKres0 N om) (Real.rpow_nonneg heps.le _) (Real.rpow_nonneg hrad.le _)
    hinv hloc hEn'

end Paper
