import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.CubeNegativeL2Norm
import SubdiffusiveProcess.Main.HalfFractionalOrder
import SubdiffusiveProcess.Sobolev.BoundaryEnergy
import SubdiffusiveProcess.Sobolev.FoldDiscounts
import SubdiffusiveProcess.Sobolev.LoadApproximation
import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.AffineResponses
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.CoarseGrainingVocab.Core
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
import SubdiffusiveProcess.Frozen.Section6.Defs.GoodEvent
import SubdiffusiveProcess.Frozen.Section6.Defs.HolderRegularityConclusions
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.rem_resolved
import SubdiffusiveProcess.Paper.lane4_smoothed_neumann_source_scaling
import SubdiffusiveProcess.Paper.lane4_lambda_inv_moments
import SubdiffusiveProcess.Paper.lane4_smoothed_load_properties
import SubdiffusiveProcess.Paper.aux_prop_neumann_growth_solution_bridge
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Paper.lem_coercivity
import SubdiffusiveProcess.Paper.lem_even
import SubdiffusiveProcess.Paper.lem_extension
import SubdiffusiveProcess.Paper.lem_neumann_error
import SubdiffusiveProcess.Paper.prop_folded_iteration
import SubdiffusiveProcess.Paper.prop_growth
import SubdiffusiveProcess.Paper.rem_repair
import SubdiffusiveProcess.Paper.rem_resolved_strata
import SubdiffusiveProcess.Paper.rem_resolved_meshes
import SubdiffusiveProcess.Paper.rem_resolved_microscopic
import SubdiffusiveProcess.Paper.rem_resolved_eps_power
import SubdiffusiveProcess.Paper.lem_infrared

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Paper

/-- Bounded-source pairing on the unit cube: `|∫_Q f u| ≤ Kf ‖u‖_{L²(Q)}` (`|Q| = 1`). -/
theorem aux_prop_neumann_growth_source_pairing {d : ℕ}
    (f : SpatialCoordinates d → ℝ)
    (hf : AEStronglyMeasurable f
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (Kf : ℝ) (hKf : 0 ≤ Kf) (hb : ∀ y, |f y| ≤ Kf)
    (u : DomainL2 (unitNeumannCube d)) :
    |∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x * u x| ≤ Kf * ‖u‖ := by
  set μ : Measure (SpatialCoordinates d) :=
    volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) with hμdef
  have hvol : volume.real (unitNeumannCube d : Set (SpatialCoordinates d)) = 1 :=
    centeredCube_one_volume_real (fun _ => (1 / 2 : ℝ)) one_pos
  haveI : IsProbabilityMeasure μ := by
    constructor
    rw [hμdef, Measure.restrict_apply_univ]
    have hfin : volume (unitNeumannCube d : Set (SpatialCoordinates d)) ≠ ⊤ := by
      have := (inferInstance : IsFiniteMeasure μ).measure_univ_lt_top
      rw [hμdef, Measure.restrict_apply_univ] at this
      exact this.ne
    rw [← ENNReal.ofReal_toReal hfin]
    change ENNReal.ofReal (volume.real (unitNeumannCube d : Set (SpatialCoordinates d))) = 1
    rw [hvol, ENNReal.ofReal_one]
  have hu2 : MemLp (u : SpatialCoordinates d → ℝ) 2 μ := Lp.memLp u
  have hu1 : MemLp (u : SpatialCoordinates d → ℝ) 1 μ := hu2.mono_exponent (by norm_num)
  have hint_u : Integrable (fun x => |(u : SpatialCoordinates d → ℝ) x|) μ :=
    (memLp_one_iff_integrable.mp hu1).abs
  have hL1 : ∫ x, |(u : SpatialCoordinates d → ℝ) x| ∂μ ≤ ‖u‖ := by
    have heq : ∫ x, |(u : SpatialCoordinates d → ℝ) x| ∂μ =
        (eLpNorm (u : SpatialCoordinates d → ℝ) 1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm]
      simp only [← Real.norm_eq_abs]
      exact integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable u)
    rw [heq, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
      (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.aestronglyMeasurable u))
  have hpt : ∀ x, |f x * (u : SpatialCoordinates d → ℝ) x| ≤
      Kf * |(u : SpatialCoordinates d → ℝ) x| := by
    intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)
  have hint_fu : Integrable (fun x => f x * (u : SpatialCoordinates d → ℝ) x) μ := by
    refine Integrable.mono' (hint_u.const_mul Kf) (hf.mul (Lp.aestronglyMeasurable u)) ?_
    exact Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hpt x
  calc
    |∫ x, f x * (u : SpatialCoordinates d → ℝ) x ∂μ|
        ≤ ∫ x, |f x * (u : SpatialCoordinates d → ℝ) x| ∂μ :=
          abs_integral_le_integral_abs
    _ ≤ ∫ x, Kf * |(u : SpatialCoordinates d → ℝ) x| ∂μ :=
          integral_mono hint_fu.abs (hint_u.const_mul Kf) hpt
    _ = Kf * ∫ x, |(u : SpatialCoordinates d → ℝ) x| ∂μ := integral_const_mul Kf _
    _ ≤ Kf * ‖u‖ := mul_le_mul_of_nonneg_left hL1 hKf

/-- Real absorption: `E ≤ A √E` with `A ≥ 0` gives `E ≤ A²`. -/
theorem aux_prop_neumann_growth_absorb (E A : ℝ) (hE : 0 ≤ E)
    (h : E ≤ A * Real.sqrt E) : E ≤ A ^ 2 := by
  have hs := Real.sqrt_nonneg E
  have hsq : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE
  by_cases h0 : Real.sqrt E = 0
  · have hE0 : E = 0 := by rw [← hsq, h0]; ring
    rw [hE0]; positivity
  · have hpos : 0 < Real.sqrt E := lt_of_le_of_ne hs (Ne.symm h0)
    have h1 : Real.sqrt E ≤ A := by
      have : Real.sqrt E * Real.sqrt E ≤ A * Real.sqrt E := by
        rw [← sq, hsq]; exact h
      exact le_of_mul_le_mul_right this hpos
    calc E = Real.sqrt E ^ 2 := hsq.symm
      _ ≤ A ^ 2 := pow_le_pow_left₀ hs h1 2

/-- Global energy of a Neumann solution with a bounded source, from the carried mean-zero
coarse Poincaré inequality of `in_poincare` on the unit cube (`|Q| = 1`). -/
theorem aux_prop_neumann_growth_global_energy {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (P : in_poincare d hd E)
    (a : PositiveCoefficient (centeredCube (fun _ => (1 / 2 : ℝ)) 1 one_pos))
    (f : SpatialCoordinates d → ℝ)
    (hf : AEStronglyMeasurable f
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (Kf : ℝ) (hKf : 0 ≤ Kf) (hb : ∀ y, |f y| ≤ Kf)
    (v : meanZeroSobolevGraph (unitNeumannCube d)) (hsol : SolvesNeumann a f v) :
    sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
        (v : SobolevData (unitNeumannCube d)) ≤
      Kf ^ 2 * P.C ^ 2 *
        (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos a (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹ := by
  set lam : ℝ := E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos a (fun _ => (1 / 2 : ℝ)) 1 1 1
    with hlamdef
  have hlam : 0 < lam := E.lam_pos _ _ _ _ _ _ _ _
  set En : ℝ := sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
    (v : SobolevData (unitNeumannCube d)) with hEn
  have hEn0 : 0 ≤ En := sobolevCoefficientForm_nonneg a _
  have hvw : (v : SobolevData (unitNeumannCube d)) ∈ weakSobolevGraph (unitNeumannCube d) :=
    (inf_le_left : meanZeroSobolevGraph (unitNeumannCube d) ≤
      weakSobolevGraph (unitNeumannCube d)) v.property
  have hid : En = ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
      f x * (v : SobolevData (unitNeumannCube d)).1 x :=
    hsol ⟨(v : SobolevData (unitNeumannCube d)), hvw⟩
  have hpair := aux_prop_neumann_growth_source_pairing f hf Kf hKf hb
    (v : SobolevData (unitNeumannCube d)).1
  have hvol : volume.real (unitNeumannCube d : Set (SpatialCoordinates d)) = 1 :=
    centeredCube_one_volume_real (fun _ => (1 / 2 : ℝ)) one_pos
  have hpoin := P.poincare_meanZero (fun _ => (1 / 2 : ℝ)) one_pos a v
  have hnorm : normalizedEnergyNorm a (unitNeumannCube d).isOpen.measurableSet
      (sobolevGradient (v : SobolevData (unitNeumannCube d))) = Real.sqrt En := by
    unfold normalizedEnergyNorm
    rw [hvol, div_one, localGradientEnergy_domain_eq_sobolevCoefficientForm]
  rw [centeredCube_one_volume_real, Real.sqrt_one, div_one] at hpoin
  have hpoin' : ‖(v : SobolevData (unitNeumannCube d)).1‖ ≤
      P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt En := by
    rw [← hnorm]; exact hpoin
  have hA0 : 0 ≤ Kf * (P.C * lam ^ (-(1 / 2) : ℝ)) :=
    mul_nonneg hKf (mul_nonneg P.C_pos.le (Real.rpow_nonneg hlam.le _))
  have hmain : En ≤ Kf * (P.C * lam ^ (-(1 / 2) : ℝ)) * Real.sqrt En := by
    calc En ≤ |En| := le_abs_self En
      _ ≤ Kf * ‖(v : SobolevData (unitNeumannCube d)).1‖ := by rw [hid]; exact hpair
      _ ≤ Kf * (P.C * lam ^ (-(1 / 2) : ℝ) * Real.sqrt En) :=
          mul_le_mul_of_nonneg_left hpoin' hKf
      _ = Kf * (P.C * lam ^ (-(1 / 2) : ℝ)) * Real.sqrt En := by ring
  have habs := aux_prop_neumann_growth_absorb En _ hEn0 hmain
  have hsq : (lam ^ (-(1 / 2) : ℝ)) ^ 2 = lam⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]
    norm_num
    exact Real.rpow_neg_one lam
  calc En ≤ (Kf * (P.C * lam ^ (-(1 / 2) : ℝ))) ^ 2 := habs
    _ = Kf ^ 2 * P.C ^ 2 * (lam ^ (-(1 / 2) : ℝ)) ^ 2 := by ring
    _ = Kf ^ 2 * P.C ^ 2 * lam⁻¹ := by rw [hsq]

/-- `M.delta ≤ 1/(1+∑ 1/δ_i)` forces `M.delta ≤ δ_i` for each listed order. -/
theorem aux_prop_neumann_growth_delta_min {k : ℕ} (δ : Fin k → ℝ) (hδ : ∀ i, 0 < δ i)
    (i : Fin k) : 1 / (1 + ∑ j : Fin k, 1 / δ j) ≤ δ i := by
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin k)), 0 ≤ 1 / δ j :=
    fun j _ => (one_div_pos.mpr (hδ j)).le
  have hsingle : 1 / δ i ≤ ∑ j : Fin k, 1 / δ j :=
    Finset.single_le_sum hnn (Finset.mem_univ i)
  have hpos : 0 < 1 / δ i := one_div_pos.mpr (hδ i)
  calc 1 / (1 + ∑ j : Fin k, 1 / δ j) ≤ 1 / (1 / δ i) :=
        one_div_le_one_div_of_le hpos (by linarith)
    _ = δ i := one_div_one_div (δ i)

theorem aux_prop_neumann_growth_delta_pos {k : ℕ} (δ : Fin k → ℝ) (hδ : ∀ i, 0 < δ i) :
    0 < 1 / (1 + ∑ j : Fin k, 1 / δ j) := by
  have : 0 ≤ ∑ j : Fin k, 1 / δ j :=
    Finset.sum_nonneg fun j _ => (one_div_pos.mpr (hδ j)).le
  positivity

/-- Final real combination of the local and global bounds. -/
theorem aux_prop_neumann_growth_combine
    (G Kr En Dr e2 Pc lam1inv Lam R : ℝ)
    (hKr : 0 ≤ Kr) (he2 : 0 ≤ e2) (hR : 0 ≤ R)
    (hlam : lam1inv ≤ Lam)
    (hG : G ≤ Kr * (En + Dr ^ 2 * e2) * R)
    (hEn : En ≤ Dr ^ 2 * e2 * Pc ^ 2 * lam1inv) :
    G ≤ Dr ^ 2 * (Kr * (1 + Pc ^ 2 * Lam)) * e2 * R := by
  have h1 : En + Dr ^ 2 * e2 ≤ Dr ^ 2 * e2 * (1 + Pc ^ 2 * Lam) := by
    have h2 : Dr ^ 2 * e2 * Pc ^ 2 * lam1inv ≤ Dr ^ 2 * e2 * Pc ^ 2 * Lam :=
      mul_le_mul_of_nonneg_left hlam (by positivity)
    nlinarith
  calc G ≤ Kr * (En + Dr ^ 2 * e2) * R := hG
    _ ≤ Kr * (Dr ^ 2 * e2 * (1 + Pc ^ 2 * Lam)) * R := by gcongr
    _ = Dr ^ 2 * (Kr * (1 + Pc ^ 2 * Lam)) * e2 * R := by ring




theorem prop_neumann_growth_assembly :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (t : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
    ∀ (rho : ℝ → ℝ), ContDiff ℝ ∞ rho → (∀ tau, 0 ≤ rho tau) →
      (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) → (∫ tau, rho tau) = 1 →
    ∀ (pvec : Fin d → ℝ), (∑ i : Fin d, (pvec i) ^ 2) = 1 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
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
  obtain ⟨δres, hδres, hres⟩ :=
    rem_resolved d hd E P X W D t k (fun i => 2 * ps i) htlo hthi hps2
  obtain ⟨δlam, hδlam, hlam⟩ :=
    lane4_lambda_inv_moments d hd E (1 / 8 : ℝ) ⟨by norm_num, by norm_num⟩
  have hδi : ∀ i : Fin k, 0 < δlam (2 * ps i) := fun i => hδlam _ (hps2 i)
  refine ⟨min δres (1 / (1 + ∑ j : Fin k, 1 / δlam (2 * ps j))),
    lt_min hδres (aux_prop_neumann_growth_delta_pos _ hδi), ?_⟩
  intro M Rm Sreg It H HI hδ rho hrho hrho0 hsupp hint pvec hpvec
  have hδM : M.delta ≤ δres := hδ.trans (min_le_left _ _)
  have hδMi : ∀ i : Fin k, M.delta ≤ δlam (2 * ps i) := fun i =>
    (hδ.trans (min_le_right _ _)).trans (aux_prop_neumann_growth_delta_min _ hδi i)
  obtain ⟨Kres, Cres, hKres0, hKresMem, hKresBd, hae⟩ := hres M Rm Sreg It H HI hδM
  have hlamI := fun i : Fin k =>
    hlam M Rm H HI (fun _ => (1 / 2 : ℝ)) 1 one_pos le_rfl (2 * ps i) (hps2 i) (hδMi i)
  choose Clam hLamMem hLamBd using hlamI
  -- the face-bump amplitude
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
  -- the random constant
  obtain ⟨Lam, hLamdef⟩ : ∃ Lam : ℕ → BilateralField d → ℝ, Lam = fun N om =>
      (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
        (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
        (fun _ => (1 / 2 : ℝ)) 1 (1 / 8 : ℝ) 1)⁻¹ := ⟨_, rfl⟩
  have hLamMem' : ∀ i N, MemLp (Lam N) (ENNReal.ofReal (2 * ps i))
      (chaosSampleLaw M).toMeasure := by
    intro i N; rw [hLamdef]; exact hLamMem i N
  have hLamBd' : ∀ i N, eLpNorm (Lam N) (ENNReal.ofReal (2 * ps i))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Clam i) := by
    intro i N; rw [hLamdef]; exact hLamBd i N
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ → BilateralField d → ℝ, K = fun N om =>
      Dr ^ 2 * (Kres N om * (1 + P.C ^ 2 * Lam N om)) := ⟨_, rfl⟩
  obtain ⟨Cp, hCpdef⟩ : ∃ Cp : Fin k → ℝ,
      Cp = fun i => max (max (Cres i) (P.C ^ 2 * Clam i)) 0 :=
    ⟨_, rfl⟩
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
        _ ≤ ‖P.C ^ 2‖ₑ * ENNReal.ofReal (Clam i) := by gcongr; exact hLamBd' i N
        _ = ENNReal.ofReal (P.C ^ 2 * Clam i) := by
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
  refine ⟨K, fun i => Dr ^ 2 * (Cp i * (1 + Cp i)), fun i N => (hmom i N).1,
    fun i N => (hmom i N).2, ?_⟩
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
