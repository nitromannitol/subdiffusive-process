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
import SubdiffusiveProcess.Main.InfraredAdmissible
import SubdiffusiveProcess.Probability.InfraredCharacterizationUniformExponentialMoment
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Paper.prop_growth
import SubdiffusiveProcess.Paper.prop_neumann_growth
import SubdiffusiveProcess.Paper.lem_infrared
import SubdiffusiveProcess.Paper.lem_coercivity
import SubdiffusiveProcess.Paper.prop_neumann_growth_assembly
import SubdiffusiveProcess.Paper.aux_macro_moment_bank
import SubdiffusiveProcess.Paper.prop_growth_holder_micro_campanato
import SubdiffusiveProcess.Paper.prop_growth_holder_assembly
import SubdiffusiveProcess.Paper.lem_as_coarse_first_clause_assembly

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- (hole 1) One-sided bounded-source pairing on the unit cube `Q` (`|Q| = 1`) for an
`AEMeasurable` source with an almost-everywhere bound. -/
theorem aux_cor_neumann_source_pairing_ae {d : ℕ}
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hF : AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))), |F x| ≤ Kf)
    (u : DomainL2 (unitNeumannCube d)) :
    ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x * u x ≤ Kf * ‖u‖ := by
  set μ : Measure (SpatialCoordinates d) := volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))
    with hμdef
  have hvol : (measureUnivNNReal μ : ℝ) = 1 := by
    calc
      (measureUnivNNReal μ : ℝ) = (μ univ).toReal := rfl
      _ = (volume (unitNeumannCube d : Set (SpatialCoordinates d))).toReal := by simp [hμdef]
      _ = volume.real (unitNeumannCube d : Set (SpatialCoordinates d)) := rfl
      _ = 1 := centeredCube_one_volume_real (fun _ => (1 / 2 : ℝ)) one_pos
  have hpair := aux_aux_macro_moment_bank_source_pairing_le F Kf hKf hF hFb u
  calc
    ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x * u x
        ≤ ((measureUnivNNReal μ : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹) * Kf) * ‖u‖ := hpair
    _ = ((1 : ℝ) ^ ((2 : ℝ≥0∞).toReal⁻¹) * Kf) * ‖u‖ := by rw [hvol]
    _ = (1 * Kf) * ‖u‖ := by simp
    _ = Kf * ‖u‖ := by simp

/-- (hole 2) Global energy of the Neumann solution with an `L^∞(Q)` source
(almost-everywhere version of `aux_prop_neumann_growth_global_energy`). -/
theorem aux_cor_neumann_source_global_energy_ae {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (P : in_poincare d hd E)
    (a : PositiveCoefficient (centeredCube (fun _ => (1 / 2 : ℝ)) 1 one_pos))
    (F : SpatialCoordinates d → ℝ)
    (hF : AEMeasurable F (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFb : ∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))), |F x| ≤ Kf)
    (v : meanZeroSobolevGraph (unitNeumannCube d)) (hsol : SolvesNeumann a F v) :
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
      F x * (v : SobolevData (unitNeumannCube d)).1 x :=
    hsol ⟨(v : SobolevData (unitNeumannCube d)), hvw⟩
  have hpair := aux_cor_neumann_source_pairing_ae F Kf hKf hF hFb
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
    calc En ≤ Kf * ‖(v : SobolevData (unitNeumannCube d)).1‖ := by rw [hid]; exact hpair
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

/-- (hole 3) Moment bound for the random constant `U * (1 + c * V)` from moments of `U` and `V`
at the doubled order, with an explicit bound depending only on `C1`, `c`, `C2`. -/
theorem aux_cor_neumann_source_K_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (q c C1 C2 : ℝ) (hq : 1 ≤ q) (hc : 0 ≤ c) (U V : Ω → ℝ)
    (hU : MemLp U (ENNReal.ofReal (2 * q)) P) (hV : MemLp V (ENNReal.ofReal (2 * q)) P)
    (hUb : eLpNorm U (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal C1)
    (hVb : eLpNorm V (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal C2) :
    MemLp (fun om => U om * (1 + c * V om)) (ENNReal.ofReal q) P ∧
      eLpNorm (fun om => U om * (1 + c * V om)) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (max (max C1 (c * C2)) 0 * (1 + max (max C1 (c * C2)) 0)) := by
  set Cm : ℝ := max (max C1 (c * C2)) 0 with hCm
  have hCm0 : 0 ≤ Cm := by
    rw [hCm]
    exact le_max_right _ _
  have hCm1 : C1 ≤ Cm := by
    rw [hCm]
    exact (le_max_left _ _).trans (le_max_left _ _)
  have hCm2 : c * C2 ≤ Cm := by
    rw [hCm]
    exact (le_max_right _ _).trans (le_max_left _ _)
  have hV' : MemLp (fun om => c * V om) (ENNReal.ofReal (2 * q)) P :=
    hV.const_mul c
  have hVb' : eLpNorm (fun om => c * V om) (ENNReal.ofReal (2 * q)) P ≤ ENNReal.ofReal Cm := by
    calc
      eLpNorm (fun om => c * V om) (ENNReal.ofReal (2 * q)) P
          ≤ ‖c‖ₑ * eLpNorm V (ENNReal.ofReal (2 * q)) P :=
        eLpNorm_const_smul_le (c := c) (f := V) (p := ENNReal.ofReal (2 * q)) (μ := P)
      _ = ENNReal.ofReal |c| * eLpNorm V (ENNReal.ofReal (2 * q)) P := by
          rw [Real.enorm_eq_ofReal hc, abs_of_nonneg hc]
      _ = ENNReal.ofReal c * eLpNorm V (ENNReal.ofReal (2 * q)) P := by rw [abs_of_nonneg hc]
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal C2 := by gcongr
      _ = ENNReal.ofReal (c * C2) := by rw [ENNReal.ofReal_mul hc]
      _ ≤ ENNReal.ofReal Cm := ENNReal.ofReal_le_ofReal hCm2
  obtain ⟨hUVmem, hUVb⟩ := aux_rem_resolved_UV_moment P q Cm hq hCm0 U (fun om => c * V om)
    hU hV' (hUb.trans (ENNReal.ofReal_le_ofReal hCm1)) hVb'
  refine ⟨hUVmem, ?_⟩
  calc
    eLpNorm (fun om => U om * (1 + c * V om)) (ENNReal.ofReal q) P
        = eLpNorm (fun om => U om * (1 + c * V om)) (ENNReal.ofReal q) P := rfl
    _ ≤ ENNReal.ofReal (Cm * (1 + Cm)) := hUVb
    _ = ENNReal.ofReal (max (max C1 (c * C2)) 0 * (1 + max (max C1 (c * C2)) 0)) := by rw [hCm]

/-- Consumer (already proved from the holes): the bounded-source Neumann energy growth
`Γ_N(u_N)(B_r(x) ∩ Q) ≤ K_N ‖f‖_∞² r^t` (paper lines 1207-1229), with the deterministic
one-step input `D` of `mfd:in-iteration(v)` as an explicit helper hypothesis. -/
theorem aux_cor_neumann_source_energy :
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
      InfraredAdmissible M H → M.delta ≤ delta0 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ K N om) ∧
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          ∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ unitNeumannCube d →
            0 < rad → rad ≤ 1 →
            localGradientEnergy
                (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                (s := Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
                (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
              K N om * Kf ^ 2 * rad ^ t := by
  intro d hd _ _ E P X W D t k ps htlo hthi hps
  have hps2 : ∀ i : Fin k, 1 ≤ 2 * ps i := fun i => by linarith [hps i]
  obtain ⟨δres, hδres, hres⟩ :=
    aux_rem_resolved_adm d hd E P X W D t k (fun i => 2 * ps i) htlo hthi hps2
  obtain ⟨δlam, hδlam, hlam⟩ :=
    aux_lane4_lambda_inv_moments_adm d hd E (1 / 8 : ℝ) ⟨by norm_num, by norm_num⟩
  have hδi : ∀ i : Fin k, 0 < δlam (2 * ps i) := fun i => hδlam _ (hps2 i)
  refine ⟨min δres (1 / (1 + ∑ j : Fin k, 1 / δlam (2 * ps j))),
    lt_min hδres (aux_prop_neumann_growth_delta_pos _ hδi), ?_⟩
  intro M Rm Sreg It H HI hδ
  have hδM : M.delta ≤ δres := hδ.trans (min_le_left _ _)
  have hδMi : ∀ i : Fin k, M.delta ≤ δlam (2 * ps i) := fun i =>
    (hδ.trans (min_le_right _ _)).trans (aux_prop_neumann_growth_delta_min _ hδi i)
  obtain ⟨Kres, Cres, hKres0, hKresMem, hKresBd, hae⟩ := hres M Rm Sreg It H HI hδM
  have hlamI := fun i : Fin k =>
    hlam M Rm H HI (fun _ => (1 / 2 : ℝ)) 1 one_pos le_rfl (2 * ps i) (hps2 i) (hδMi i)
  choose Clam hLamMem hLamBd using hlamI
  obtain ⟨Lam, hLamdef⟩ : ∃ Lam : ℕ → BilateralField d → ℝ, Lam = fun N om =>
      (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
        (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
        (fun _ => (1 / 2 : ℝ)) 1 (1 / 8 : ℝ) 1)⁻¹ := ⟨_, rfl⟩
  have hLam0 : ∀ N om, 0 ≤ Lam N om := by
    intro N om; rw [hLamdef]
    exact (inv_pos.mpr (E.lam_pos _ _ _ _ _ _ _ _)).le
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ → BilateralField d → ℝ, K = fun N om =>
      Kres N om * (1 + P.C ^ 2 * Lam N om) := ⟨_, rfl⟩
  have hK0 : ∀ N om, 0 ≤ K N om := by
    intro N om; rw [hKdef]
    exact mul_nonneg (hKres0 N om) (by have := hLam0 N om; positivity)
  have hmom := fun (i : Fin k) (N : ℕ) =>
    aux_cor_neumann_source_K_moment (chaosSampleLaw M).toMeasure (ps i) (P.C ^ 2)
      (Cres i) (Clam i) (hps i) (by positivity) (Kres N) (Lam N)
      (hKresMem i N) (by rw [hLamdef]; exact hLamMem i N) (hKresBd i N)
      (by rw [hLamdef]; exact hLamBd i N)
  refine ⟨K, fun i => max (max (Cres i) (P.C ^ 2 * Clam i)) 0 *
      (1 + max (max (Cres i) (P.C ^ 2 * Clam i)) 0), hK0,
    fun i N => by rw [hKdef]; exact (hmom i N).1,
    fun i N => by rw [hKdef]; exact (hmom i N).2, ?_⟩
  filter_upwards [hae] with om hom
  intro N F Kf hKf hFm hFb hmean v hsol x rad hx hrad hrad1
  have hloc := hom.1 N F hFm Kf hKf hFb hmean v hsol x hx rad hrad hrad1
  have hEn := aux_cor_neumann_source_global_energy_ae hd E P
    (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
    F hFm Kf hKf hFb v hsol
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
  have hEn' : sobolevCoefficientForm
      (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
      (v : SobolevData (unitNeumannCube d)) (v : SobolevData (unitNeumannCube d)) ≤
      Kf ^ 2 * 1 * P.C ^ 2 *
        (E.lam (fun _ => (1 / 2 : ℝ)) 1 one_pos
          (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
          (fun _ => (1 / 2 : ℝ)) 1 1 1)⁻¹ := by
    rw [mul_one]; exact hEn
  have hloc' : localGradientEnergy
      (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
      (s := Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
      Kres N om * (sobolevCoefficientForm
        (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
        (v : SobolevData (unitNeumannCube d)) (v : SobolevData (unitNeumannCube d)) +
        Kf ^ 2 * 1) * rad ^ t := by
    rw [mul_one]; exact hloc
  have hfin := aux_prop_neumann_growth_combine _ (Kres N om) _ Kf 1 P.C _ (Lam N om)
    (rad ^ t) (hKres0 N om) zero_le_one (Real.rpow_nonneg hrad.le _) hinv hloc' hEn'
  rw [hKdef]
  calc _ ≤ Kf ^ 2 * (Kres N om * (1 + P.C ^ 2 * Lam N om)) * 1 * rad ^ t := hfin
    _ = Kres N om * (1 + P.C ^ 2 * Lam N om) * Kf ^ 2 * rad ^ t := by ring

theorem aux_cor_neumann_source_t1_exponent (d : ℕ) (alpha : ℝ) (ha1 : alpha < 1) :
    (d : ℝ) - 1 < (max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) + d) / 2 ∧
      (max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) + d) / 2 < d ∧
      0 < 2 + (max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) + d) / 2 - 2 * alpha - d := by
  have h1 : (d : ℝ) - 1 ≤ max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) :=
    le_max_left _ _
  have h2 : (d : ℝ) - 2 + 2 * alpha ≤ max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) :=
    le_max_right _ _
  have hm : max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) < d :=
    max_lt (by linarith) (by linarith)
  refine ⟨by linarith, by linarith, by linarith⟩


theorem aux_cor_neumann_source_micro_floor {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (Mx : ℝ) (hMx : 0 < Mx)
    (hbounds : ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
        Set (SpatialCoordinates d)), Mx⁻¹ ≤ cutoffCoefficient M H om N x) :
    ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      1 ≤ Mx * (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos).val y := by
  filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae M H om N (fun _ => (1/2:ℝ)) one_pos,
    ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet] with y hy hyQ
  rw [hy]
  have hlo := hbounds y (centeredCube_subset_closedCube (fun _ => (1/2:ℝ)) one_pos hyQ)
  calc (1:ℝ) = Mx * Mx⁻¹ := (mul_inv_cancel₀ hMx.ne').symm
    _ ≤ Mx * cutoffCoefficient M H om N y := mul_le_mul_of_nonneg_left hlo hMx.le


theorem aux_cor_neumann_source_campanato_split (L K1 K2 Kf R V eps rad : ℝ)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hKf : 0 ≤ Kf) (hR : 0 ≤ R) (hV : 0 ≤ V)
    (hlow : rad ≤ eps → L ≤ (K1 * Kf) ^ 2 * R * V)
    (hhigh : eps ≤ rad → L ≤ (K2 * Kf) ^ 2 * R * V) :
    L ≤ ((K1 + K2) * Kf) ^ 2 * R * V := by
  have hmono1 : (K1 * Kf) ^ 2 ≤ ((K1 + K2) * Kf) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hK1 hKf) (mul_le_mul_of_nonneg_right (by linarith) hKf) 2
  have hmono2 : (K2 * Kf) ^ 2 ≤ ((K1 + K2) * Kf) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hK2 hKf) (mul_le_mul_of_nonneg_right (by linarith) hKf) 2
  have hRV : 0 ≤ R * V := mul_nonneg hR hV
  rcases le_total rad eps with h | h
  · calc L ≤ (K1 * Kf) ^ 2 * R * V := hlow h
      _ = (K1 * Kf) ^ 2 * (R * V) := by ring
      _ ≤ ((K1 + K2) * Kf) ^ 2 * (R * V) := mul_le_mul_of_nonneg_right hmono1 hRV
      _ = ((K1 + K2) * Kf) ^ 2 * R * V := by ring
  · calc L ≤ (K2 * Kf) ^ 2 * R * V := hhigh h
      _ = (K2 * Kf) ^ 2 * (R * V) := by ring
      _ ≤ ((K1 + K2) * Kf) ^ 2 * (R * V) := mul_le_mul_of_nonneg_right hmono2 hRV
      _ = ((K1 + K2) * Kf) ^ 2 * R * V := by ring


theorem aux_cor_neumann_source_micro_pathwise {d : ℕ} (CP : ℝ) (hCP0 : 0 ≤ CP)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (w : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((w : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        CP * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((w : SobolevData (centeredCube c s hs)).2 i y) ^ 2)
    (a : PositiveCoefficient (unitNeumannCube d)) (Mx : ℝ) (hMx : 0 ≤ Mx)
    (hlow : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      1 ≤ Mx * a.val y)
    (v : meanZeroSobolevGraph (unitNeumannCube d))
    (K Kf t alpha e eps rad : ℝ) (hrad : 0 < rad) (hre : rad ≤ eps) (hrad1 : rad ≤ 1)
    (he : 0 ≤ e) (hexp : 2 + t = 2 * alpha + d + e)
    (hen : ∀ c ∈ unitNeumannCube d,
      localGradientEnergy a
          (s := Metric.ball c rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
          (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤ K * Kf ^ 2 * rad ^ t)
    (x : SpatialCoordinates d) (hx : x ∈ unitNeumannCube d) :
    ∫ y in Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
        ((v : SobolevData (unitNeumannCube d)).1 y - setAverage
          (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
          (v : SobolevData (unitNeumannCube d)).1) ^ 2
        ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) ≤
      ((1 + CP) * (Mx + |K|) * eps ^ (e / 2) * Kf) ^ 2 * rad ^ (2 * alpha) *
        volume.real (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  have hpw := aux_prop_growth_holder_micro_campanato_pathwise (d := d) CP hCP0 hPoinc
    (fun _ => (1 / 2 : ℝ)) one_pos a Mx hMx hlow
    (⟨(v : SobolevData (unitNeumannCube d)),
        (inf_le_left : meanZeroSobolevGraph (unitNeumannCube d) ≤ weakSobolevGraph (unitNeumannCube d))
          v.property⟩)
    rad (K * Kf ^ 2 * rad ^ t) hrad hen x hx
  have hV := aux_prop_growth_holder_micro_campanato_volume_ge (d := d)
    (fun _ => (1 / 2 : ℝ)) x (R := 1 / 2) hrad (by linarith) hx
  exact aux_prop_growth_holder_micro_campanato_final_alg d CP Mx K Kf rad eps
    (volume.real (ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))) t alpha e
    (∫ y in ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
        ((v : SobolevData (unitNeumannCube d)).1 y - setAverage
          (ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
          (v : SobolevData (unitNeumannCube d)).1) ^ 2
        ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)))
    hCP0 hMx hrad hre he hexp hV hpw



theorem aux_cor_neumann_source_micro_campanato :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H → M.delta ≤ delta0 →
      ∃ (Kosc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kosc N om) ∧
        (∀ i N, MemLp (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          ∀ x ∈ unitNeumannCube d, ∀ rad : ℝ, 0 < rad →
            rad ≤ (3 : ℝ) ^ (-(N : ℤ)) → rad ≤ 1 →
            ∫ y in Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
                ((v : SobolevData (unitNeumannCube d)).1 y - setAverage
                  (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
                  (v : SobolevData (unitNeumannCube d)).1) ^ 2
                ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) ≤
              (Kosc N om * Kf) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  intro d hd _ _ E P X W D alpha k ps ha0 ha1 hps
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) + d) / 2 :=
    ⟨_, rfl⟩
  obtain ⟨ht1, htd, he0⟩ := aux_cor_neumann_source_t1_exponent d alpha ha1
  rw [← htdef] at ht1 htd he0
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 2 + t - 2 * alpha - d := ⟨_, rfl⟩
  have he : 0 < e := by rw [hedef]; exact he0
  have hexp : 2 + t = 2 * alpha + d + e := by rw [hedef]; ring
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 + ∑ i, ps i := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => le_trans zero_le_one (hps i)
  have hq : 1 ≤ q := by rw [hqdef]; linarith
  have hpq : ∀ i, ps i ≤ q := by
    intro i
    have := Finset.single_le_sum (fun j _ => le_trans zero_le_one (hps j)) (Finset.mem_univ i)
    rw [hqdef]; linarith
  have hq0 : 0 < 2 * q := by linarith
  obtain ⟨deltaE, hdeltaE, hEA⟩ :=
    aux_cor_neumann_source_energy d hd E P X W D t k ps ht1 htd hps
  obtain ⟨Cpe, Cd, cd, hCpe, hCd, hcd, hroot⟩ :=
    aux_prop_growth_energy_assembly_root_extremes d hd q hq
  obtain ⟨CP, hCP0, hPoinc⟩ :=
    aux_prop_growth_holder_micro_campanato_scaled_poincare d (by omega)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨dabs, hdabs⟩ : ∃ s : ℝ, s = min 1 ((e / 2) * Real.log 3 / (Cd + Cpe)) := ⟨_, rfl⟩
  have hdabs0 : 0 < dabs := by
    rw [hdabs]
    exact lt_min one_pos (div_pos (mul_pos (half_pos he) hlog3) (add_pos hCd hCpe))
  refine ⟨min deltaE (min (cd / (2 * q)) dabs),
    lt_min hdeltaE (lt_min (div_pos hcd hq0) hdabs0), ?_⟩
  intro M Rm Sreg It H hH hdelta
  have hdE : M.delta ≤ deltaE := hdelta.trans (min_le_left _ _)
  have hdc : M.delta ≤ cd / (2 * q) :=
    hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hda : M.delta ≤ dabs := hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hrate : Cd * M.delta + Cpe * M.delta ^ 2 ≤ (e / 2) * Real.log 3 :=
    aux_prop_growth_holder_micro_campanato_rate Cd Cpe e M.delta hCd hCpe hdpos
      (hda.trans_eq hdabs)
  obtain ⟨K, CbK, -, hKL, hKB, hen⟩ := hEA M Rm Sreg It H hH hdE
  obtain ⟨Dx, Mx, CE, hCE, hDMx0, hext, hmem, -, hMxmom⟩ :=
    hroot M H hH hdc (fun _ => (1 / 2 : ℝ)) 1 one_pos le_rfl
  have hfac := aux_prop_growth_holder_micro_campanato_fac e _ he hrate
  have hCP1 : 0 ≤ 1 + CP := add_nonneg zero_le_one hCP0
  refine ⟨fun N om => (1 + CP) * (Mx N om + |K N om|) * ((3 : ℝ) ^ (-(N : ℤ))) ^ (e / 2),
    fun i => (1 + CP) * (CE + max (CbK i) 0), ?_, ?_, ?_, ?_⟩
  · intro N om
    have := (hDMx0 N om).2
    have := (hfac N).1
    positivity
  · intro i N
    exact (aux_prop_growth_holder_micro_campanato_moment (chaosSampleLaw M).toMeasure (ps i) q
      (hps i) (hpq i) (Mx N) (K N) (1 + CP) _ ((Cd * M.delta + Cpe * M.delta ^ 2) * N) CE
      (CbK i) hCP1 (hfac N).1 (hfac N).2.1 (hfac N).2.2 hCE (hmem N).2 (hMxmom N)
      (hKL i N) (hKB i N)).1
  · intro i N
    exact (aux_prop_growth_holder_micro_campanato_moment (chaosSampleLaw M).toMeasure (ps i) q
      (hps i) (hpq i) (Mx N) (K N) (1 + CP) _ ((Cd * M.delta + Cpe * M.delta ^ 2) * N) CE
      (CbK i) hCP1 (hfac N).1 (hfac N).2.1 (hfac N).2.2 hCE (hmem N).2 (hMxmom N)
      (hKL i N) (hKB i N)).2
  · filter_upwards [hen, hext] with om hom hext'
    intro N F Kf hKf hFm hFb hmean v hsol x hx rad hrad hradN hrad1
    obtain ⟨hMxpos, hbounds, -⟩ := hext' N
    have hlow := aux_cor_neumann_source_micro_floor M H om N (Mx N om) hMxpos
      (fun y hy => (hbounds y hy).1)
    exact aux_cor_neumann_source_micro_pathwise CP hCP0 hPoinc
      (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) (Mx N om)
      hMxpos.le hlow v (K N om) Kf t alpha e ((3 : ℝ) ^ (-(N : ℤ))) rad hrad hradN hrad1
      he.le hexp
      (fun c hc => hom N F Kf hKf hFm hFb hmean v hsol c rad hc hrad hrad1) x hx


/-- Centered cubes with equal centre and side coincide (proof irrelevance). -/
theorem aux_cor_neumann_source_cube_congr {d : ℕ} {w w' : SpatialCoordinates d}
    {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t') (hw : w = w') (htt : t = t') :
    centeredCube w t ht = centeredCube w' t' ht' := by
  subst hw; subst htt; rfl

/-- Two charts of the same grid cell, read from two roots carrying the cutoff coefficient,
have the same `|σ_*⁻¹|` on the unit origin cube. -/
theorem aux_cor_neumann_source_sigma_cross {d : ℕ} (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z1 : SpatialCoordinates d) (r1 : ℝ) (hr1 : 0 < r1)
    (z2 : SpatialCoordinates d) (r2 : ℝ) (hr2 : 0 < r2)
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (h1 : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z1 r1 hr1 : Set (SpatialCoordinates d)))
    (h2 : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z2 r2 hr2 : Set (SpatialCoordinates d))) :
    Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
        (E.chart z1 r1 hr1 (cutoffPositiveCoefficient M H om N z1 hr1) w r') =
      Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
        (E.chart z2 r2 hr2 (cutoffPositiveCoefficient M H om N z2 hr2) w r') := by
  have ha1 := aux_lem_extension_cell_moment_chart_scalar_identity E M H om N z1 r1 hr1 w r' hr'
    h1 (Homogenization.originCube d 0) subset_rfl
  have ha2 := aux_lem_extension_cell_moment_chart_scalar_identity E M H om N z2 r2 hr2 w r' hr'
    h2 (Homogenization.originCube d 0) subset_rfl
  have hAE : Homogenization.Book.Ch02.CoeffOn.AEEq
      ((E.chart z1 r1 hr1 (cutoffPositiveCoefficient M H om N z1 hr1) w r').coeffOn
        (Homogenization.originCube d 0))
      ((E.chart z2 r2 hr2 (cutoffPositiveCoefficient M H om N z2 hr2) w r').coeffOn
        (Homogenization.originCube d 0)) := by
    unfold Homogenization.Book.Ch02.CoeffOn.AEEq
    filter_upwards [ha1, ha2] with x hx1 hx2
    rw [hx1, hx2]
  have hJ := fun p q => Homogenization.Book.Ch02.responseJ_eq_ofAEEq hAE p q
  unfold Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm
  rw [(aux_lem_as_coarse_ms_coarse_congr hJ).2]

/-- `halfRange (j + m) = 3^m halfRange j + halfRange m`. -/
theorem aux_cor_neumann_source_halfRange_add (j m : ℕ) :
    Homogenization.Gagliardo.halfRange (j + m) =
      3 ^ m * Homogenization.Gagliardo.halfRange j + Homogenization.Gagliardo.halfRange m := by
  have ej := Homogenization.Gagliardo.two_mul_halfRange j
  have em := Homogenization.Gagliardo.two_mul_halfRange m
  have ejm := Homogenization.Gagliardo.two_mul_halfRange (j + m)
  rw [pow_add] at ejm
  have key : 2 * Homogenization.Gagliardo.halfRange (j + m) =
      2 * (3 ^ m * Homogenization.Gagliardo.halfRange j + Homogenization.Gagliardo.halfRange m) := by
    linear_combination ejm - (3 : ℤ) ^ m * ej - em
  exact mul_left_cancel₀ two_ne_zero key

/-- The composite index of a depth-`m` descendant of an admissible depth-`j` cell is a
depth-`(j+m)` descendant of the unit root. -/
theorem aux_cor_neumann_source_desc_compose {d : ℕ} {j m : ℕ} {k : Fin d → ℤ}
    (hk : aux_prop_growth_holder_macro_campanato_Adm j k)
    {R' : Homogenization.TriadicCube d}
    (hR' : R' ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) (-(m : ℤ))) :
    (⟨-((j + m : ℕ) : ℤ), fun i => 3 ^ m * k i + R'.index i⟩ : Homogenization.TriadicCube d) ∈
      Homogenization.descendantsAtScale (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - ((j + m : ℕ) : ℤ)) := by
  apply Homogenization.mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth
  have hle : (-(m : ℤ)) ≤ (Homogenization.originCube d 0).scale := by
    simp [Homogenization.originCube]
  rw [Homogenization.mem_descendantsAtScale_iff hle] at hR'
  have htn : Int.toNat ((Homogenization.originCube d 0).scale - -(m : ℤ)) = m := by
    simp [Homogenization.originCube]
  rw [htn] at hR'
  have hrange := Homogenization.Gagliardo.index_range_of_mem_descendantsAtDepth hR'
  apply Homogenization.Gagliardo.mem_descendantsAtDepth_of_index_range
  · simp [Homogenization.originCube]
  · intro i
    have hi := hrange i
    simp only [Homogenization.originCube, Pi.zero_apply, mul_zero, zero_sub, zero_add] at hi ⊢
    have hkj := hk i
    have ej := Homogenization.Gagliardo.two_mul_halfRange j
    have habs : |k i| ≤ Homogenization.Gagliardo.halfRange j := by linarith
    obtain ⟨hk1, hk2⟩ := abs_le.1 habs
    have h3 : (0 : ℤ) ≤ 3 ^ m := by positivity
    have hA := mul_le_mul_of_nonneg_left hk2 h3
    have hB := mul_le_mul_of_nonneg_left hk1 h3
    rw [aux_cor_neumann_source_halfRange_add]
    constructor <;> nlinarith [hi.1, hi.2]

/-- `3^{-j} 3^{-m} = 1 · 3^{-(j+m)}`. -/
theorem aux_cor_neumann_source_side_mul (j m : ℕ) :
    aux_prop_growth_holder_macro_campanato_side j * (3 : ℝ) ^ (-(m : ℤ)) =
      1 * (3 : ℝ) ^ (-((j + m : ℕ) : ℤ)) := by
  unfold aux_prop_growth_holder_macro_campanato_side
  rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, pow_add, mul_inv, one_mul]

/-- The grid-cell centres of the two readings coincide. -/
theorem aux_cor_neumann_source_center_eq {d : ℕ} (j m : ℕ) (k v : Fin d → ℤ) :
    aux_lem_as_coarse_ms_cellCenter
        (aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) j k)
        (aux_prop_growth_holder_macro_campanato_side j) m v =
      aux_lem_as_coarse_ms_cellCenter (fun _ => (1 / 2 : ℝ)) 1 (j + m)
        (fun i => 3 ^ m * k i + v i) := by
  have h1 := aux_cor_neumann_source_side_mul j m
  have h2 : aux_prop_growth_holder_macro_campanato_side j =
      1 * (3 : ℝ) ^ (-((j + m : ℕ) : ℤ)) * (3 : ℝ) ^ m := by
    rw [← h1, mul_assoc, zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity), mul_one]
  funext i
  simp only [aux_lem_as_coarse_ms_cellCenter, aux_prop_growth_holder_macro_campanato_center]
  rw [h1, h2]
  push_cast
  ring

/-- **Chart domination.**  The depth-`m` descendant maximum of `|σ_*⁻¹|` in the chart of an
admissible depth-`j` cell is at most the depth-`(j+m)` descendant maximum in the unit-root
chart. -/
theorem aux_cor_neumann_source_chart_dom {d : ℕ} (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (j m : ℕ) (k : Fin d → ℤ) (hk : aux_prop_growth_holder_macro_campanato_Adm j k) :
    Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(m : ℤ))
        (E.chart (aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) j k)
          (aux_prop_growth_holder_macro_campanato_side j)
          (aux_prop_growth_holder_macro_campanato_side_pos j)
          (cutoffPositiveCoefficient M H om N
            (aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) j k)
            (aux_prop_growth_holder_macro_campanato_side_pos j))
          (aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) j k)
          (aux_prop_growth_holder_macro_campanato_side j)) ≤
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-((j + m : ℕ) : ℤ))
        (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
          (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
          (fun _ => (1 / 2 : ℝ)) 1) := by
  set c := aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) j k with hc
  set s := aux_prop_growth_holder_macro_campanato_side j with hs
  have hs0 : 0 < s := aux_prop_growth_holder_macro_campanato_side_pos j
  have hne : (Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      (-(m : ℤ))).Nonempty :=
    Homogenization.descendantsAtScale_nonempty _ (by simp [Homogenization.originCube])
  unfold Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
    Homogenization.Book.Ch02.finsetSupReal
  refine csSup_le ?_ ?_
  · obtain ⟨R, hR⟩ := hne
    exact ⟨_, R, hR, rfl⟩
  rintro _ ⟨R', hR', rfl⟩
  have hsc : (Homogenization.originCube d 0).scale - (m : ℤ) = -(m : ℤ) := by
    simp [Homogenization.originCube]
  have hR'' : R' ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (m : ℤ)) := by rw [hsc]; exact hR'
  have ht1 := (aux_lem_as_coarse_ms_chart_transport E M H om N c s hs0 m hR'').2
  have hRmem := aux_cor_neumann_source_desc_compose hk hR'
  set R : Homogenization.TriadicCube d :=
    ⟨-((j + m : ℕ) : ℤ), fun i => 3 ^ m * k i + R'.index i⟩ with hRdef
  have ht2 := (aux_lem_as_coarse_ms_chart_transport E M H om N (fun _ => (1 / 2 : ℝ)) 1 one_pos
    (j + m) hRmem).2
  have hw : aux_lem_as_coarse_ms_cellCenter c s m R'.index =
      aux_lem_as_coarse_ms_cellCenter (fun _ => (1 / 2 : ℝ)) 1 (j + m) R.index :=
    aux_cor_neumann_source_center_eq j m k R'.index
  have hrr : s * (3 : ℝ) ^ (-(m : ℤ)) = 1 * (3 : ℝ) ^ (-((j + m : ℕ) : ℤ)) :=
    aux_cor_neumann_source_side_mul j m
  have hr1 : 0 < s * (3 : ℝ) ^ (-(m : ℤ)) := by positivity
  have hr2 : 0 < 1 * (3 : ℝ) ^ (-((j + m : ℕ) : ℤ)) := by positivity
  have hsub1 := aux_lem_as_coarse_ms_cell_sub c s hs0 m hR'' hr1
  have hsub2 := aux_lem_as_coarse_ms_cell_sub (fun _ => (1 / 2 : ℝ)) 1 one_pos (j + m) hRmem hr2
  rw [aux_cor_neumann_source_cube_congr hr1 hr2 hw hrr] at hsub1
  have hcross := aux_cor_neumann_source_sigma_cross E M H om N c s hs0 (fun _ => (1 / 2 : ℝ)) 1
    one_pos _ _ hr2 hsub1 hsub2
  have hRmem' : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      (-((j + m : ℕ) : ℤ)) := by
    have : (Homogenization.originCube d 0).scale - ((j + m : ℕ) : ℤ) = -((j + m : ℕ) : ℤ) := by
      simp [Homogenization.originCube]
    rw [← this]; exact hRmem
  calc Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R'
        (E.chart c s hs0 (cutoffPositiveCoefficient M H om N c hs0) c s)
      = _ := ht1
    _ = _ := by rw [hw, hrr]; exact hcross
    _ = _ := ht2.symm
    _ ≤ _ := Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale_of_mem_descendantsAtScale
          _ hRmem'

/-- `side_j^e · w¹_m ≤ C_g · w^{e'}_{m+j}` termwise, `C_g = (1 - 3⁻¹)/(1 - 3^{-e'})`. -/
theorem aux_cor_neumann_source_weight_term (e e' : ℝ) (j m : ℕ) (he' : 0 < e') (hee : e' ≤ e)
    (he1 : e' ≤ 1) (y : ℝ) (hy : 0 ≤ y) :
    aux_prop_growth_holder_macro_campanato_side j ^ e *
        (Homogenization.Book.Ch02.geometricWeight 1 1 m * y) ≤
      ((1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e'))) *
        (Homogenization.Book.Ch02.geometricWeight e' 1 (m + j) * y) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hside : aux_prop_growth_holder_macro_campanato_side j ^ e = (3 : ℝ) ^ (-(j : ℝ) * e) := by
    unfold aux_prop_growth_holder_macro_campanato_side
    rw [← Real.rpow_natCast, ← Real.rpow_neg h3.le, ← Real.rpow_mul h3.le]
  have hq1 : (3 : ℝ) ^ (-e') < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < 1 - (3 : ℝ) ^ (-e') := by linarith
  have hc1 : 0 ≤ 1 - (3 : ℝ) ^ (-(1 : ℝ)) := by
    have : (3 : ℝ) ^ (-(1 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    linarith
  unfold Homogenization.Book.Ch02.geometricWeight Homogenization.Book.Ch02.geometricDiscount
  simp only [Real.rpow_eq_pow, mul_one, neg_mul, one_mul]
  rw [hside]
  have hexp : (3 : ℝ) ^ (-(j : ℝ) * e) * (3 : ℝ) ^ (-(m : ℝ)) ≤
      (3 : ℝ) ^ (-(e' * ((m + j : ℕ) : ℝ))) := by
    rw [← Real.rpow_add h3]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith [mul_le_mul_of_nonneg_left hee hj, mul_le_mul_of_nonneg_left he1 hm]
  have hpos : 0 ≤ (1 - (3 : ℝ) ^ (-(1 : ℝ))) * y := mul_nonneg hc1 hy
  calc (3 : ℝ) ^ (-(j : ℝ) * e) * ((1 - (3 : ℝ) ^ (-(1 : ℝ))) * (3 : ℝ) ^ (-(m : ℝ)) * y)
      = ((1 - (3 : ℝ) ^ (-(1 : ℝ))) * y) *
          ((3 : ℝ) ^ (-(j : ℝ) * e) * (3 : ℝ) ^ (-(m : ℝ))) := by ring
    _ ≤ ((1 - (3 : ℝ) ^ (-(1 : ℝ))) * y) * (3 : ℝ) ^ (-(e' * ((m + j : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp hpos
    _ = (1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e')) *
          ((1 - (3 : ℝ) ^ (-e')) * (3 : ℝ) ^ (-(e' * ((m + j : ℕ) : ℝ))) * y) := by
        field_simp

/-- **Cell ellipticity bound.**  For an admissible depth-`j` cell, `side_j^e λ_{1,1}⁻¹` of the
cell's own chart is dominated by the unit-root discounted series `Σ_n w^{e'}_n Y_n`. -/
theorem aux_cor_neumann_source_lam_cell {d : ℕ} (E : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (j : ℕ) (k : Fin d → ℤ) (hk : aux_prop_growth_holder_macro_campanato_Adm j k)
    (e e' : ℝ) (he' : 0 < e') (hee : e' ≤ e) (he1 : e' ≤ 1)
    (hsum : Summable (fun n : ℕ => Homogenization.Book.Ch02.geometricWeight e' 1 n *
      Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
        (Homogenization.originCube d 0) (-(n : ℤ))
        (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
          (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
          (fun _ => (1 / 2 : ℝ)) 1))) :
    aux_prop_growth_holder_macro_campanato_side j ^ e *
        (E.lam (aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) j k)
          (aux_prop_growth_holder_macro_campanato_side j)
          (aux_prop_growth_holder_macro_campanato_side_pos j)
          (cutoffPositiveCoefficient M H om N
            (aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) j k)
            (aux_prop_growth_holder_macro_campanato_side_pos j))
          (aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) j k)
          (aux_prop_growth_holder_macro_campanato_side j) 1 1)⁻¹ ≤
      ((1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e'))) *
        ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight e' 1 n *
          Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
            (Homogenization.originCube d 0) (-(n : ℤ))
            (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
              (fun _ => (1 / 2 : ℝ)) 1) := by
  set c := aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) j k with hc
  set s := aux_prop_growth_holder_macro_campanato_side j with hsdef
  have hs0 : 0 < s := aux_prop_growth_holder_macro_campanato_side_pos j
  obtain ⟨Ssum, _hS0, hsq, hSeq, hinv⟩ := aux_lane4_lambda_inv_moments_lam_inv_eq E c s hs0
    (cutoffPositiveCoefficient M H om N c hs0) 1 one_pos le_rfl
  set YT : ℕ → ℝ := fun m => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
    (Homogenization.originCube d 0) (-(m : ℤ))
    (E.chart c s hs0 (cutoffPositiveCoefficient M H om N c hs0) c s) with hYT
  set Y : ℕ → ℝ := fun n => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
    (Homogenization.originCube d 0) (-(n : ℤ))
    (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
      (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
      (fun _ => (1 / 2 : ℝ)) 1) with hY
  set w1 : ℕ → ℝ := Homogenization.Book.Ch02.geometricWeight 1 1 with hw1def
  set w' : ℕ → ℝ := Homogenization.Book.Ch02.geometricWeight e' 1 with hw'def
  set Cg : ℝ := (1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e')) with hCg
  have hYT0 : ∀ m, 0 ≤ YT m := fun m => aux_lane4_lambda_inv_moments_Y_nonneg _ _
  have hY0 : ∀ n, 0 ≤ Y n := fun n => aux_lane4_lambda_inv_moments_Y_nonneg _ _
  have hdom : ∀ m, YT m ≤ Y (m + j) := fun m => by
    rw [add_comm m j]; exact aux_cor_neumann_source_chart_dom E M H om N j m k hk
  have hw1 : ∀ m, 0 ≤ w1 m := (aux_lane4_lambda_inv_moments_weight_sum 1 one_pos).2.2
  have hsp : 0 < s ^ e := Real.rpow_pos_of_pos hs0 e
  have hq1 : (3 : ℝ) ^ (-e') < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hCg0 : 0 ≤ Cg := by
    have : (3 : ℝ) ^ (-(1 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    exact div_nonneg (by linarith) (by linarith)
  have hterm : ∀ m, s ^ e * (w1 m * Y (m + j)) ≤ Cg * (w' (m + j) * Y (m + j)) := fun m =>
    aux_cor_neumann_source_weight_term e e' j m he' hee he1 (Y (m + j)) (hY0 _)
  have hshift : Summable (fun m => w' (m + j) * Y (m + j)) := (summable_nat_add_iff j).mpr hsum
  have hsumA : Summable (fun m => w1 m * Y (m + j)) := by
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (hw1 m) (hY0 _)) (fun m => ?_)
      (hshift.mul_left (Cg / s ^ e))
    have h := hterm m
    rw [div_mul_eq_mul_div, le_div_iff₀ hsp]
    linarith
  have hsumT : Summable (fun m => w1 m * YT m) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (hw1 m) (hYT0 m))
      (fun m => mul_le_mul_of_nonneg_left (hdom m) (hw1 m)) hsumA
  have hcs := aux_lane4_lambda_inv_moments_cs one_pos 0 YT hYT0 (by simpa using hsq)
    (by simpa using hsumT)
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, Nat.add_zero] at hcs
  have hshift_le : ∑' m, w' (m + j) * Y (m + j) ≤ ∑' n, w' n * Y n := by
    rw [← hsum.sum_add_tsum_nat_add j]
    have : 0 ≤ ∑ i ∈ Finset.range j, w' i * Y i :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg ((aux_lane4_lambda_inv_moments_weight_sum e' he').2.2 i) (hY0 i)
    linarith
  calc s ^ e * (E.lam c s hs0 (cutoffPositiveCoefficient M H om N c hs0) c s 1 1)⁻¹
      = s ^ e * Ssum ^ 2 := by rw [hinv]
    _ ≤ s ^ e * ∑' m, w1 m * YT m := by
        rw [hSeq]; exact mul_le_mul_of_nonneg_left hcs hsp.le
    _ ≤ s ^ e * ∑' m, w1 m * Y (m + j) :=
        mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum
          (fun m => mul_le_mul_of_nonneg_left (hdom m) (hw1 m)) hsumT hsumA) hsp.le
    _ = ∑' m, s ^ e * (w1 m * Y (m + j)) := tsum_mul_left.symm
    _ ≤ ∑' m, Cg * (w' (m + j) * Y (m + j)) :=
        Summable.tsum_le_tsum hterm (hsumA.mul_left _) (hshift.mul_left _)
    _ = Cg * ∑' m, w' (m + j) * Y (m + j) := tsum_mul_left
    _ ≤ Cg * ∑' n, w' n * Y n := mul_le_mul_of_nonneg_left hshift_le hCg0

/-- Energy on a set does not depend on how the set is written. -/
theorem aux_cor_neumann_source_energy_congr {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) {s t : Set (SpatialCoordinates d)} (hst : s = t)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (g : HilbertGradient Ω) :
    localGradientEnergy a hs g = localGradientEnergy a ht g := by
  subst hst; rfl

/-- **Cell Poincaré.**  On a sub-cube `T = c + s Q₀` of the domain, the plain variance of an
`H¹` function is at most `C² s² λ_{1,1}(T)⁻¹` times its energy on `T`, with `λ` read in the
cell's own chart and a cell coefficient that agrees a.e. with the domain coefficient. -/
theorem aux_cor_neumann_source_cell_poincare {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (P : in_poincare d hd E) {Ω : Opens (SpatialCoordinates d)}
    (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s) (hle : centeredCube c s hs ≤ Ω)
    (aΩ : PositiveCoefficient Ω) (aT : PositiveCoefficient (centeredCube c s hs))
    (hcoef : ∀ᵐ y ∂volume.restrict (centeredCube c s hs : Set (SpatialCoordinates d)),
      aT.val y = aΩ.val y)
    (u : weakSobolevGraph Ω) :
    aux_prop_growth_holder_macro_campanato_var (centeredCube c s hs : Set (SpatialCoordinates d))
        ((u : SobolevData Ω).1 : SpatialCoordinates d → ℝ) ≤
      P.C ^ 2 * s ^ 2 * (E.lam c s hs aT c s 1 1)⁻¹ *
        localGradientEnergy aΩ (s := (centeredCube c s hs : Set (SpatialCoordinates d)))
          (centeredCube c s hs).isOpen.measurableSet (sobolevGradient (u : SobolevData Ω)) := by
  have hTm : MeasurableSet (centeredCube c s hs : Set (SpatialCoordinates d)) :=
    (centeredCube c s hs).isOpen.measurableSet
  have hTfin : volume (centeredCube c s hs : Set (SpatialCoordinates d)) ≠ ⊤ := by
    rw [centeredCube_coe_eq_ball]; exact measure_ball_lt_top.ne
  haveI : IsFiniteMeasure (volume.restrict (centeredCube c s hs : Set (SpatialCoordinates d))) :=
    isFiniteMeasure_restrict.2 hTfin
  have hV : volume.real (centeredCube c s hs : Set (SpatialCoordinates d)) = s ^ d := by
    rw [measureReal_def, centeredCube_coe_eq_ball, Real.volume_pi_ball _ (half_pos hs),
      Fintype.card_fin, ENNReal.toReal_ofReal (by positivity)]
    ring_nf
  have hV0 : 0 < volume.real (centeredCube c s hs : Set (SpatialCoordinates d)) := by
    rw [hV]; positivity
  obtain ⟨v, hv1, hv2⟩ := aux_prop_growth_holder_micro_campanato_centered_restrict hle hV0.ne' u
  have hP := P.poincare_meanZero_all_radii c s hs aT v
  have hEeq : localGradientEnergy aT (centeredCube c s hs).isOpen.measurableSet
      (sobolevGradient (v : SobolevData (centeredCube c s hs))) =
      localGradientEnergy aΩ (s := (centeredCube c s hs : Set (SpatialCoordinates d))) hTm
        (sobolevGradient (u : SobolevData Ω)) := by
    rw [localGradientEnergy_eq_integral, localGradientEnergy_eq_integral]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Measure.restrict_restrict hTm, Measure.restrict_restrict hTm, Set.inter_self,
      Set.inter_eq_left.2 hle]
    refine integral_congr_ae ?_
    filter_upwards [hcoef, hv2 i] with y h1 h2
    change aT.val y * ((v : SobolevData (centeredCube c s hs)).2 i y) ^ 2 =
      aΩ.val y * ((u : SobolevData Ω).2 i y) ^ 2
    rw [h1, h2]
  have hvar : ‖(v : SobolevData (centeredCube c s hs)).1‖ ^ 2 =
      aux_prop_growth_holder_macro_campanato_var (centeredCube c s hs : Set (SpatialCoordinates d))
        ((u : SobolevData Ω).1 : SpatialCoordinates d → ℝ) := by
    rw [aux_prop_growth_holder_micro_campanato_norm_sq]
    unfold aux_prop_growth_holder_macro_campanato_var
    refine integral_congr_ae ?_
    filter_upwards [hv1] with y hy
    rw [hy, aux_prop_growth_holder_macro_campanato_setAverage_eq hTm hle]
  set En := localGradientEnergy aΩ (s := (centeredCube c s hs : Set (SpatialCoordinates d))) hTm
    (sobolevGradient (u : SobolevData Ω)) with hEn
  have hEn0 : 0 ≤ En := localGradientEnergy_nonneg _ _ _
  set L := E.lam c s hs aT c s 1 1 with hL
  have hL0 : 0 < L := E.lam_pos _ _ _ _ _ _ _ _
  have hnorm : normalizedEnergyNorm aT (centeredCube c s hs).isOpen.measurableSet
      (sobolevGradient (v : SobolevData (centeredCube c s hs))) =
      Real.sqrt (En / volume.real (centeredCube c s hs : Set (SpatialCoordinates d))) := by
    unfold normalizedEnergyNorm; rw [hEeq]
  rw [hnorm] at hP
  set a := ‖(v : SobolevData (centeredCube c s hs)).1‖ with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  set V := volume.real (centeredCube c s hs : Set (SpatialCoordinates d)) with hVdef
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.2 hV0
  have h1 : a ≤ P.C * s * L ^ (-(1 / 2) : ℝ) * Real.sqrt En := by
    have h2 := (div_le_iff₀ hsV).1 hP
    have h3 : Real.sqrt (En / V) * Real.sqrt V = Real.sqrt En := by
      rw [← Real.sqrt_mul (div_nonneg hEn0 hV0.le), div_mul_cancel₀ _ hV0.ne']
    calc a ≤ P.C * s * L ^ (-(1 / 2) : ℝ) * Real.sqrt (En / V) * Real.sqrt V := h2
      _ = P.C * s * L ^ (-(1 / 2) : ℝ) * (Real.sqrt (En / V) * Real.sqrt V) := by ring
      _ = _ := by rw [h3]
  have hsq : (L ^ (-(1 / 2) : ℝ)) ^ 2 = L⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num
    exact Real.rpow_neg_one L
  rw [← hvar]
  calc a ^ 2 ≤ (P.C * s * L ^ (-(1 / 2) : ℝ) * Real.sqrt En) ^ 2 :=
        pow_le_pow_left₀ ha0 h1 2
    _ = P.C ^ 2 * s ^ 2 * (L ^ (-(1 / 2) : ℝ)) ^ 2 * (Real.sqrt En) ^ 2 := by ring
    _ = P.C ^ 2 * s ^ 2 * L⁻¹ * En := by rw [hsq, Real.sq_sqrt hEn0]


/-- **Uniform-in-`N` moments of the unit-root discounted series**
`Z_N = Σ_n w^{e'}_n max_{R ∈ D_n(Q₀)} |σ_*⁻¹(R; A_N)|` (paper lines 419-457, the summation of
`mfd:lem-coercivity` at order `e'`), with a.s. summability for every `N`. -/
theorem aux_cor_neumann_source_Z_moments (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (e' Q : ℝ) (he' : 0 < e') (hQ1 : 1 ≤ Q) (hDQ : 2 * (d : ℝ) ≤ e' * Q) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H → M.delta ≤ delta0 →
        ∃ CZ : ℝ, ∀ N : ℕ,
          MemLp (fun om => ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight e' 1 n *
              Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                (Homogenization.originCube d 0) (-(n : ℤ))
                (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
                  (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                  (fun _ => (1 / 2 : ℝ)) 1))
            (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (fun om => ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight e' 1 n *
              Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                (Homogenization.originCube d 0) (-(n : ℤ))
                (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
                  (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                  (fun _ => (1 / 2 : ℝ)) 1))
            (ENNReal.ofReal Q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CZ ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
            Summable (fun n : ℕ => Homogenization.Book.Ch02.geometricWeight e' 1 n *
              Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                (Homogenization.originCube d 0) (-(n : ℤ))
                (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
                  (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                  (fun _ => (1 / 2 : ℝ)) 1)) := by
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQ1
  obtain ⟨deltaQ, Cd, hdQ, hCd, hmain⟩ := lane4_lambda_inv_cell_moment d hd E Q hQ1
  set dA : ℝ := Real.sqrt (e' * Real.log 3 / (4 * (Cd * (Q + Q ^ 2)) + 4)) with hdA
  set dB : ℝ := min 1 (e' * Real.log 3 / (2 * Cd + 1)) with hdB
  have hQ2 : 0 < Q + Q ^ 2 := by positivity
  have hdA0 : 0 < dA := Real.sqrt_pos.2 (div_pos (mul_pos he' hlog3pos) (by positivity))
  have hdB0 : 0 < dB := lt_min one_pos (div_pos (mul_pos he' hlog3pos) (by linarith))
  refine ⟨min deltaQ (min dA dB), lt_min hdQ (lt_min hdA0 hdB0), ?_⟩
  intro M Rm H hH hδ
  have hδQ : M.delta ≤ deltaQ := hδ.trans (min_le_left _ _)
  have hδA : M.delta ≤ dA := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδB : M.delta ≤ dB := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ0 : 0 ≤ M.delta := (M.shellPrefix.delta_pos).le
  have hδ1 : M.delta ≤ 1 := hδB.trans (min_le_left _ _)
  have hδZ : M.delta ≤ e' * Real.log 3 / (2 * Cd + 1) := hδB.trans (min_le_right _ _)
  have hdl2 : M.delta ^ 2 ≤ e' * Real.log 3 / (4 * (Cd * (Q + Q ^ 2)) + 4) := by
    have h := pow_le_pow_left₀ hδ0 hδA 2
    rwa [hdA, Real.sq_sqrt (div_nonneg (mul_nonneg he'.le hlog3pos.le) (by positivity))] at h
  have hcondA : Cd * (Q + Q ^ 2) * M.delta ^ 2 ≤ (e' / 4) * Real.log 3 := by
    have := aux_lane4_lambda_inv_moments_condA_helper (Cd * (Q + Q ^ 2)) (e' * Real.log 3)
      (M.delta ^ 2) (by positivity) (by positivity) (sq_nonneg _) hdl2
    linarith
  have hcondB : Cd * M.delta * (1 + M.delta) ≤ e' * Real.log 3 :=
    aux_lane4_lambda_inv_moments_condB_helper Cd (e' * Real.log 3) M.delta hCd.le
      (by positivity) hδ1 hδ0 hδZ
  obtain ⟨Cq, hCq, hcb⟩ := hmain M Rm H hH (fun _ => (1 / 2 : ℝ)) 1 one_pos le_rfl hδQ
  refine ⟨(1 - (3 : ℝ) ^ (-e')) * Cq /
      (1 - Real.exp (-(e' / 2) * Real.log 3 + Cd * (Q + Q ^ 2) * M.delta ^ 2)) +
    (1 - (3 : ℝ) ^ (-e')) * Cq * (3 : ℝ) ^ (-e') / (1 - (3 : ℝ) ^ (-e')), fun N => ?_⟩
  obtain ⟨h1, h2, h3⟩ := aux_lane4_lambda_inv_moments_series_bound (chaosSampleLaw M).toMeasure
    e' (d : ℝ) Q Cd Cq M.delta N he' (Nat.cast_nonneg d) hDQ hQ1 hCd hCq hδ0 hcondA hcondB
    (fun n om => Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
      (Homogenization.originCube d 0) (-(n : ℤ))
      (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
        (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
        (fun _ => (1 / 2 : ℝ)) 1))
    (fun n om => aux_lane4_lambda_inv_moments_Y_nonneg _ _) (fun n => (hcb N n).1)
    (fun n => (hcb N n).2)
  exact ⟨h1, h2, h3⟩

/-- Final per-cell algebra: `C² s² λ⁻¹ · K Kf² (s/2)^t ≤ (s^α Xc Kf)² s^d` once
`s^e λ⁻¹ ≤ C_g Z`, `2 + t = e + 2α + d` and `Xc = 1 + A (K + Z)` with `A ≥ max 1 (C² C_g)`. -/
theorem aux_cor_neumann_source_cell_alg (d : ℕ) (Vr CP s Li En K Kf t e alpha Z Cg A : ℝ)
    (hs : 0 < s) (hLi : 0 ≤ Li) (hK : 0 ≤ K) (hZ : 0 ≤ Z) (ht : 0 ≤ t) (hA1 : 1 ≤ A)
    (hA : CP ^ 2 * Cg ≤ A) (hexp : 2 + t = e + 2 * alpha + d)
    (hVar : Vr ≤ CP ^ 2 * s ^ 2 * Li * En) (hEn : En ≤ K * Kf ^ 2 * (s / 2) ^ t)
    (hlam : s ^ e * Li ≤ Cg * Z) :
    Vr ≤ (s ^ alpha * ((1 + A * (K + Z)) * Kf)) ^ 2 * s ^ d := by
  have h1 : (s / 2) ^ t ≤ s ^ t := Real.rpow_le_rpow (by positivity) (by linarith) ht
  have hpre : 0 ≤ CP ^ 2 * s ^ 2 * Li := by positivity
  have hEn' : En ≤ K * Kf ^ 2 * s ^ t :=
    hEn.trans (mul_le_mul_of_nonneg_left h1 (mul_nonneg hK (sq_nonneg _)))
  have h2 : s ^ 2 * s ^ t = s ^ e * (s ^ alpha) ^ 2 * s ^ d := by
    rw [← Real.rpow_natCast s 2, ← Real.rpow_add hs, ← Real.rpow_natCast (s ^ alpha) 2,
      ← Real.rpow_mul hs.le, ← Real.rpow_natCast s d, ← Real.rpow_add hs, ← Real.rpow_add hs]
    congr 1
    push_cast
    linarith
  have hKZ : CP ^ 2 * (Cg * Z) * K ≤ (1 + A * (K + Z)) ^ 2 := by
    have hA0 : 0 ≤ A := by linarith
    have hX : A * (K + Z) ≤ 1 + A * (K + Z) := by linarith
    have hX0 : 0 ≤ A * (K + Z) := mul_nonneg hA0 (add_nonneg hK hZ)
    have hsq : (A * (K + Z)) ^ 2 ≤ (1 + A * (K + Z)) ^ 2 := pow_le_pow_left₀ hX0 hX 2
    have hAA : A * ((K + Z) ^ 2) ≤ A ^ 2 * (K + Z) ^ 2 := by
      have : A ≤ A ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have hKZ1 : K * Z ≤ (K + Z) ^ 2 := by nlinarith [mul_nonneg hK hZ]
    have hstep : CP ^ 2 * Cg * (K * Z) ≤ A * (K * Z) :=
      mul_le_mul_of_nonneg_right hA (mul_nonneg hK hZ)
    have hstep2 : A * (K * Z) ≤ A * ((K + Z) ^ 2) := mul_le_mul_of_nonneg_left hKZ1 hA0
    calc CP ^ 2 * (Cg * Z) * K = CP ^ 2 * Cg * (K * Z) := by ring
      _ ≤ A * (K * Z) := hstep
      _ ≤ A * ((K + Z) ^ 2) := hstep2
      _ ≤ A ^ 2 * (K + Z) ^ 2 := hAA
      _ = (A * (K + Z)) ^ 2 := by ring
      _ ≤ (1 + A * (K + Z)) ^ 2 := hsq
  have hfac : 0 ≤ Kf ^ 2 * (s ^ alpha) ^ 2 * s ^ d := by positivity
  calc Vr ≤ CP ^ 2 * s ^ 2 * Li * En := hVar
    _ ≤ CP ^ 2 * s ^ 2 * Li * (K * Kf ^ 2 * s ^ t) := mul_le_mul_of_nonneg_left hEn' hpre
    _ = CP ^ 2 * (s ^ e * Li) * K * (Kf ^ 2 * (s ^ alpha) ^ 2 * s ^ d) := by
        rw [show CP ^ 2 * s ^ 2 * Li * (K * Kf ^ 2 * s ^ t) =
          CP ^ 2 * Li * K * Kf ^ 2 * (s ^ 2 * s ^ t) by ring, h2]
        ring
    _ ≤ CP ^ 2 * (Cg * Z) * K * (Kf ^ 2 * (s ^ alpha) ^ 2 * s ^ d) := by
        apply mul_le_mul_of_nonneg_right _ hfac
        apply mul_le_mul_of_nonneg_right _ hK
        exact mul_le_mul_of_nonneg_left hlam (sq_nonneg _)
    _ ≤ (1 + A * (K + Z)) ^ 2 * (Kf ^ 2 * (s ^ alpha) ^ 2 * s ^ d) :=
        mul_le_mul_of_nonneg_right hKZ hfac
    _ = (s ^ alpha * ((1 + A * (K + Z)) * Kf)) ^ 2 * s ^ d := by ring



theorem aux_cor_neumann_source_macro_cells :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H → M.delta ≤ delta0 →
      ∃ (Xc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Xc N om) ∧
        (∀ i N, MemLp (Xc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Xc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          ∀ j : ℕ, j ≤ N → ∀ kk : Fin d → ℤ, aux_prop_growth_holder_macro_campanato_Adm j kk →
            aux_prop_growth_holder_macro_campanato_var
                (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) j kk)
                ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
              (aux_prop_growth_holder_macro_campanato_side j ^ alpha * (Xc N om * Kf)) ^ 2 *
                volume.real
                  (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) j kk) := by
  intro d hd _ _ E P X W D alpha k ps ha0 ha1 hps
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) + d) / 2 :=
    ⟨_, rfl⟩
  obtain ⟨ht1, htd, he0⟩ := aux_cor_neumann_source_t1_exponent d alpha ha1
  rw [← htdef] at ht1 htd he0
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 2 + t - 2 * alpha - d := ⟨_, rfl⟩
  have he : 0 < e := by rw [hedef]; exact he0
  have hexp : 2 + t = e + 2 * alpha + d := by rw [hedef]; ring
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have ht0 : 0 ≤ t := by linarith
  obtain ⟨e', he'def⟩ : ∃ e' : ℝ, e' = min e 1 := ⟨_, rfl⟩
  have he' : 0 < e' := by rw [he'def]; exact lt_min he one_pos
  have he'e : e' ≤ e := by rw [he'def]; exact min_le_left _ _
  have he'1 : e' ≤ 1 := by rw [he'def]; exact min_le_right _ _
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => le_trans zero_le_one (hps i)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = 2 * (d : ℝ) / e' + ∑ i, ps i + 1 := ⟨_, rfl⟩
  have hdq0 : 0 ≤ 2 * (d : ℝ) / e' := div_nonneg (by positivity) he'.le
  have hQ1 : 1 ≤ Q := by rw [hQdef]; linarith
  have hDQ : 2 * (d : ℝ) ≤ e' * Q := by
    rw [hQdef, mul_add, mul_add, mul_div_cancel₀ _ he'.ne']
    have : 0 ≤ e' * ∑ i, ps i := mul_nonneg he'.le hsum0
    linarith
  have hpQ : ∀ i, ps i ≤ Q := by
    intro i
    have := Finset.single_le_sum (fun j _ => le_trans zero_le_one (hps j)) (Finset.mem_univ i)
    rw [hQdef]; linarith
  obtain ⟨deltaE, hdeltaE, hEA⟩ :=
    aux_cor_neumann_source_energy d hd E P X W D t k ps ht1 htd hps
  obtain ⟨deltaZ, hdeltaZ, hZ⟩ := aux_cor_neumann_source_Z_moments d hd E e' Q he' hQ1 hDQ
  refine ⟨min deltaE deltaZ, lt_min hdeltaE hdeltaZ, ?_⟩
  intro M Rm Sreg It H hH hdelta
  obtain ⟨K, CK, hK0, hKL, hKB, hen⟩ := hEA M Rm Sreg It H hH (hdelta.trans (min_le_left _ _))
  obtain ⟨CZ, hZN⟩ := hZ M Rm H hH (hdelta.trans (min_le_right _ _))
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℕ → BilateralField d → ℝ, Z = fun N om =>
      ∑' n : ℕ, Homogenization.Book.Ch02.geometricWeight e' 1 n *
        Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
          (Homogenization.originCube d 0) (-(n : ℤ))
          (E.chart (fun _ => (1 / 2 : ℝ)) 1 one_pos
            (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
            (fun _ => (1 / 2 : ℝ)) 1) := ⟨_, rfl⟩
  have hZ0 : ∀ N om, 0 ≤ Z N om := by
    intro N om; rw [hZdef]
    exact tsum_nonneg fun n => mul_nonneg ((aux_lane4_lambda_inv_moments_weight_sum e' he').2.2 n)
      (aux_lane4_lambda_inv_moments_Y_nonneg _ _)
  obtain ⟨Cg, hCgdef⟩ : ∃ Cg : ℝ, Cg = (1 - (3 : ℝ) ^ (-(1 : ℝ))) / (1 - (3 : ℝ) ^ (-e')) :=
    ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = max 1 (P.C ^ 2 * Cg) := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hAC : P.C ^ 2 * Cg ≤ A := by rw [hAdef]; exact le_max_right _ _
  have hA0 : 0 ≤ A := by linarith
  have hZL : ∀ i N, MemLp (Z N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure := by
    intro i N; rw [hZdef]
    exact (hZN N).1.mono_exponent (ENNReal.ofReal_le_ofReal (hpQ i))
  have hZB : ∀ i N, eLpNorm (Z N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal CZ := by
    intro i N; rw [hZdef]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (hpQ i))
      (hZN N).1.1).trans (hZN N).2.1
  refine ⟨fun N om => 1 + A * (K N om + Z N om),
    fun i => 1 + A * (max (CK i) 0 + max CZ 0), ?_, ?_, ?_, ?_⟩
  · intro N om
    have := mul_nonneg hA0 (add_nonneg (hK0 N om) (hZ0 N om))
    linarith
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (K N) (Z N) hA0
      (hKL i N) (hZL i N) (hKB i N) (hZB i N)).1
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (K N) (Z N) hA0
      (hKL i N) (hZL i N) (hKB i N) (hZB i N)).2
  · have hsummAE := ae_all_iff.2 fun N => (hZN N).2.2
    filter_upwards [hen, hsummAE] with om hom hsumm
    intro N F Kf hKf hFm hFb hmean v hsol j _hj kk hkk
    set c := aux_prop_growth_holder_macro_campanato_center (fun _ => (1 / 2 : ℝ)) j kk with hc
    set s := aux_prop_growth_holder_macro_campanato_side j with hsdef
    have hs0 : 0 < s := aux_prop_growth_holder_macro_campanato_side_pos j
    have hs1 : s ≤ 1 := aux_prop_growth_holder_macro_campanato_side_le_one j
    have hcellT : aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) j kk =
        (centeredCube c s hs0 : Set (SpatialCoordinates d)) :=
      (centeredCube_coe_eq_ball c s hs0).symm
    have hQball : (unitNeumannCube d : Set (SpatialCoordinates d)) =
        ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) := by
      rw [unitNeumannCube, centeredCube_coe_eq_ball]
    have hTQ : (centeredCube c s hs0 : Set (SpatialCoordinates d)) ⊆
        (unitNeumannCube d : Set (SpatialCoordinates d)) := by
      rw [← hcellT, hQball]
      exact aux_prop_growth_holder_macro_campanato_cell_subset _ hkk
    have hle : centeredCube c s hs0 ≤ unitNeumannCube d := hTQ
    have hcQ : c ∈ unitNeumannCube d := by
      apply hTQ
      rw [centeredCube_coe_eq_ball]
      exact mem_ball_self (half_pos hs0)
    have hcoef : ∀ᵐ y ∂volume.restrict (centeredCube c s hs0 : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M H om N c hs0).val y =
          (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos).val y := by
      filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae M H om N c hs0,
        ae_restrict_of_ae_restrict_of_subset hTQ
          (aux_prop_growth_holder_micro_campanato_coeff_ae M H om N (fun _ => (1 / 2 : ℝ))
            one_pos)] with y h1 h2
      rw [h1, h2]
    have hPc := aux_cor_neumann_source_cell_poincare hd E P c s hs0 hle
      (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
      (cutoffPositiveCoefficient M H om N c hs0) hcoef
      ⟨(v : SobolevData (unitNeumannCube d)),
        (inf_le_left : meanZeroSobolevGraph (unitNeumannCube d) ≤
          weakSobolevGraph (unitNeumannCube d)) v.property⟩
    have hE1 := hom N F Kf hKf hFm hFb hmean v hsol c (s / 2) hcQ (half_pos hs0) (by linarith)
    have hset : Metric.ball c (s / 2) ∩ (unitNeumannCube d : Set (SpatialCoordinates d)) =
        (centeredCube c s hs0 : Set (SpatialCoordinates d)) := by
      rw [← centeredCube_coe_eq_ball c s hs0]; exact Set.inter_eq_left.2 hTQ
    have hE2 : localGradientEnergy
        (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
        (s := (centeredCube c s hs0 : Set (SpatialCoordinates d)))
        (centeredCube c s hs0).isOpen.measurableSet
        (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤ K N om * Kf ^ 2 * (s / 2) ^ t := by
      rw [← aux_cor_neumann_source_energy_congr _ hset
        (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)]
      exact hE1
    have hlam := aux_cor_neumann_source_lam_cell E M H om N j kk hkk e e' he' he'e he'1 (hsumm N)
    have hV := aux_prop_growth_holder_macro_campanato_cell_volume (fun _ : Fin d => (1 / 2 : ℝ)) j kk
    rw [hV, hcellT]
    have hfin := aux_cor_neumann_source_cell_alg d _ P.C s _ _ (K N om) Kf t e alpha (Z N om) Cg A
      hs0 (inv_nonneg.2 (E.lam_pos _ _ _ _ _ _ _ _).le) (hK0 N om) (hZ0 N om) ht0 hA1 hAC hexp
      hPc hE2 (by rw [← hCgdef] at hlam; rw [hZdef]; exact hlam)
    exact hfin

/-- Arithmetic for the macro constant: `Kd (X + W + Y X0) ≤ (1 + Kd (1+Y)(Xc+Km)) Kf` when
`X = X0 = Xc Kf`, `W = Km Kf`. -/
theorem aux_cor_neumann_source_macro_arith (Kd Y Xc Km Kf : ℝ) (hKd : 0 ≤ Kd) (hY : 0 ≤ Y)
    (hXc : 0 ≤ Xc) (hKm : 0 ≤ Km) (hKf : 0 ≤ Kf) :
    Kd * (1 * (Xc * Kf) + Km * Kf + Y * (Xc * Kf)) ≤ (1 + Kd * (1 + Y) * (Xc + Km)) * Kf := by
  have e1 : Kd * (1 * (Xc * Kf) + Km * Kf + Y * (Xc * Kf)) =
      (Kd * (1 + Y) * Xc + Kd * Km) * Kf := by ring
  have e2 : Kd * Km ≤ Kd * (1 + Y) * Km :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hKd (by linarith)) hKm
  have e3 : Kd * (1 + Y) * Xc + Kd * Km ≤ 1 + Kd * (1 + Y) * (Xc + Km) := by
    have : Kd * (1 + Y) * (Xc + Km) = Kd * (1 + Y) * Xc + Kd * (1 + Y) * Km := by ring
    linarith
  rw [e1]
  exact mul_le_mul_of_nonneg_right e3 hKf



theorem aux_cor_neumann_source_macro_campanato :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H → M.delta ≤ delta0 →
      ∃ (Kmac : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kmac N om) ∧
        (∀ i N, MemLp (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          ∀ x ∈ unitNeumannCube d, ∀ rad : ℝ,
            (3 : ℝ) ^ (-(N : ℤ)) ≤ rad → rad ≤ 1 →
            ∫ y in Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
                ((v : SobolevData (unitNeumannCube d)).1 y - setAverage
                  (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
                  (v : SobolevData (unitNeumannCube d)).1) ^ 2
                ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) ≤
              (Kmac N om * Kf) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  intro d hd _ _ E P X W D alpha k ps ha0 ha1 hps
  obtain ⟨Kd, hKd1, hunit⟩ := aux_prop_growth_holder_macro_campanato_unit (d := d) alpha ha0 ha1.le
  obtain ⟨delta1, hdelta1, hcell⟩ :=
    aux_cor_neumann_source_macro_cells d hd E P X W D alpha k ps ha0 ha1 hps
  obtain ⟨delta2, hdelta2, hmic⟩ :=
    aux_cor_neumann_source_micro_campanato d hd E P X W D alpha k ps ha0 ha1 hps
  refine ⟨min delta1 delta2, lt_min hdelta1 hdelta2, ?_⟩
  intro M Rm Sreg It H hH hdelta
  obtain ⟨Xc, CX, hXc0, hXcL, hXcB, hcellE⟩ :=
    hcell M Rm Sreg It H hH (hdelta.trans (min_le_left _ _))
  obtain ⟨Kmic, Cmic, hKmic0, hKmicL, hKmicB, hmicE⟩ :=
    hmic M Rm Sreg It H hH (hdelta.trans (min_le_right _ _))
  have hKd0 : 0 ≤ Kd := by linarith
  have hY0 : 0 ≤ ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2) :=
    Real.rpow_nonneg (by norm_num) _
  have hc0 : 0 ≤ Kd * (1 + ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2)) :=
    mul_nonneg hKd0 (by linarith)
  refine ⟨fun N om => 1 + Kd * (1 + ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2)) *
      (Xc N om + Kmic N om),
    fun i => 1 + Kd * (1 + ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2)) *
      (max (CX i) 0 + max (Cmic i) 0), ?_, ?_, ?_, ?_⟩
  · intro N om
    have := mul_nonneg hc0 (add_nonneg (hXc0 N om) (hKmic0 N om))
    linarith
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (Xc N) (Kmic N) hc0
      (hXcL i N) (hKmicL i N) (hXcB i N) (hKmicB i N)).1
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (Xc N) (Kmic N) hc0
      (hXcL i N) (hKmicL i N) (hXcB i N) (hKmicB i N)).2
  · filter_upwards [hcellE, hmicE] with om hC hM
    intro N F Kf hKf hFm hFb hmean v hsol x hx rad hradN hrad1
    have hside : aux_prop_growth_holder_macro_campanato_side N = (3 : ℝ) ^ (-(N : ℤ)) := by
      unfold aux_prop_growth_holder_macro_campanato_side
      rw [zpow_neg, zpow_natCast]
    have hsidepos := aux_prop_growth_holder_macro_campanato_side_pos N
    have hrad0 : 0 < rad := hsidepos.trans_le (hside.trans_le hradN)
    have hA : 0 ≤ Xc N om * Kf := mul_nonneg (hXc0 N om) hKf
    have hB : 0 ≤ Kmic N om * Kf := mul_nonneg (hKmic0 N om) hKf
    have hu : MemLp ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) 2
        (volume.restrict (ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2))) := Lp.memLp _
    have H1 : ∀ j : ℕ, 0 ≤ j → j ≤ N → ∀ kk : Fin d → ℤ,
        aux_prop_growth_holder_macro_campanato_Adm j kk →
        aux_prop_growth_holder_macro_campanato_var
            (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) j kk)
            ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
          (1 * aux_prop_growth_holder_macro_campanato_side j ^ alpha * (Xc N om * Kf)) ^ 2 *
            volume.real
              (aux_prop_growth_holder_macro_campanato_cell (fun _ => (1 / 2 : ℝ)) j kk) := by
      intro j _ hj kk hkk
      rw [one_mul]
      exact hC N F Kf hKf hFm hFb hmean v hsol j hj kk hkk
    have H2 : ∀ p ∈ ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2), ∀ ρ : ℝ,
        aux_prop_growth_holder_macro_campanato_side N ≤ ρ →
        ρ ≤ aux_prop_growth_holder_macro_campanato_side N →
        aux_prop_growth_holder_macro_campanato_var
            (ball p ρ ∩ ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2))
            ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
          (Kmic N om * Kf) ^ 2 * ρ ^ (2 * alpha) *
            volume.real (ball p ρ ∩ ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)) := by
      intro p hp ρ hρ1 hρ2
      have hρ0 : 0 < ρ := hsidepos.trans_le hρ1
      have hρN : ρ ≤ (3 : ℝ) ^ (-(N : ℤ)) := hρ2.trans_eq hside
      have hρ1' : ρ ≤ 1 := hρ2.trans (aux_prop_growth_holder_macro_campanato_side_le_one N)
      have h := hM N F Kf hKf hFm hFb hmean v hsol p hp ρ hρ0 hρN hρ1'
      rw [aux_prop_growth_holder_macro_campanato_target_eq
        (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
        Set.inter_subset_right] at h
      exact h
    have H3 : aux_prop_growth_holder_macro_campanato_var
        (ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2))
        ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) ≤
          (Xc N om * Kf) ^ 2 := by
      have h0 := hC N F Kf hKf hFm hFb hmean v hsol 0 (Nat.zero_le N) (fun _ => 0)
        (by intro i; simp)
      have hcenter0 : aux_prop_growth_holder_macro_campanato_center
          (fun _ : Fin d => (1 / 2 : ℝ)) 0 (fun _ => 0) =
          (fun _ : Fin d => (1 / 2 : ℝ)) := by
        funext i
        simp [aux_prop_growth_holder_macro_campanato_center,
          aux_prop_growth_holder_macro_campanato_side]
      have hcell0 : aux_prop_growth_holder_macro_campanato_cell
          (fun _ : Fin d => (1 / 2 : ℝ)) 0 (fun _ => 0) =
          ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) := by
        unfold aux_prop_growth_holder_macro_campanato_cell
        rw [hcenter0]
        norm_num [aux_prop_growth_holder_macro_campanato_side]
      have hvol : volume.real (ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)) = 1 :=
        centeredCube_one_volume_real (fun _ => (1 / 2 : ℝ)) one_pos
      rw [hcell0, hvol, mul_one] at h0
      simpa [aux_prop_growth_holder_macro_campanato_side] using h0
    have hmain := hunit (fun _ => (1 / 2 : ℝ)) _ hu N 0 1 (Xc N om * Kf) (Kmic N om * Kf)
      (Xc N om * Kf) (aux_prop_growth_holder_macro_campanato_side N) zero_le_one hA hB hA
      hsidepos le_rfl H1 H2 H3 x hx rad (hside.trans_le hradN) hrad1
    rw [aux_prop_growth_holder_macro_campanato_target_eq
      (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
      Set.inter_subset_right]
    have harith := aux_cor_neumann_source_macro_arith Kd
      (((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2)) (Xc N om) (Kmic N om) Kf hKd0 hY0
      (hXc0 N om) (hKmic0 N om) hKf
    have hL0 : 0 ≤ Kd * (1 * (Xc N om * Kf) + Kmic N om * Kf +
        ((2 : ℝ) * 3 ^ (0 : ℕ)) ^ (alpha + (d : ℝ) / 2) * (Xc N om * Kf)) :=
      mul_nonneg hKd0 (add_nonneg (add_nonneg (by linarith) hB) (mul_nonneg hY0 hA))
    exact hmain.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hL0 harith 2) (Real.rpow_nonneg hrad0.le _)) measureReal_nonneg)

/-- All-radii Campanato decay of the bounded-source Neumann solution: the macro (G6) and micro
(G3) halves glued at `rad = 3^{-N}` with `Kc := Kmic + Kmac`. -/
theorem aux_cor_neumann_source_campanato :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩) (alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H → M.delta ≤ delta0 →
      ∃ (Kc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kc N om) ∧
        (∀ i N, MemLp (Kc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          ∀ x ∈ unitNeumannCube d, ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
            ∫ y in Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
                ((v : SobolevData (unitNeumannCube d)).1 y - setAverage
                  (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
                  (v : SobolevData (unitNeumannCube d)).1) ^ 2
                ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) ≤
              (Kc N om * Kf) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d))) := by
  intro d hd _ _ E P X W D alpha k ps ha0 ha1 hps
  obtain ⟨delta1, hdelta1, hmac⟩ :=
    aux_cor_neumann_source_macro_campanato d hd E P X W D alpha k ps ha0 ha1 hps
  obtain ⟨delta2, hdelta2, hmic⟩ :=
    aux_cor_neumann_source_micro_campanato d hd E P X W D alpha k ps ha0 ha1 hps
  refine ⟨min delta1 delta2, lt_min hdelta1 hdelta2, ?_⟩
  intro M Rm Sreg It H hH hdelta
  obtain ⟨Kmac, Cmac, hKmac0, hKmacL, hKmacB, hmacE⟩ :=
    hmac M Rm Sreg It H hH (hdelta.trans (min_le_left _ _))
  obtain ⟨Kmic, Cmic, hKmic0, hKmicL, hKmicB, hmicE⟩ :=
    hmic M Rm Sreg It H hH (hdelta.trans (min_le_right _ _))
  refine ⟨fun N om => Kmic N om + Kmac N om, fun i => max (Cmic i) 0 + max (Cmac i) 0,
    fun N om => add_nonneg (hKmic0 N om) (hKmac0 N om), ?_, ?_, ?_⟩
  · intro i N
    exact (hKmicL i N).add (hKmacL i N)
  · intro i N
    have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (ps i) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hps i)
    calc eLpNorm (fun om => Kmic N om + Kmac N om) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure
        ≤ eLpNorm (Kmic N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure +
            eLpNorm (Kmac N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure :=
          eLpNorm_add_le (hKmicL i N).1 (hKmacL i N).1 hp1
      _ ≤ ENNReal.ofReal (max (Cmic i) 0) + ENNReal.ofReal (max (Cmac i) 0) :=
          add_le_add ((hKmicB i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
            ((hKmacB i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      _ = ENNReal.ofReal (max (Cmic i) 0 + max (Cmac i) 0) :=
          (ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)).symm
  · filter_upwards [hmacE, hmicE] with om hom1 hom2
    intro N F Kf hKf hFm hFb hmean v hsol x hx rad hrad hrad1
    exact aux_cor_neumann_source_campanato_split _ (Kmic N om) (Kmac N om) Kf
      (rad ^ (2 * alpha)) _ ((3 : ℝ) ^ (-(N : ℤ))) rad (hKmic0 N om) (hKmac0 N om) hKf
      (Real.rpow_nonneg hrad.le _) measureReal_nonneg
      (fun h => hom2 N F Kf hKf hFm hFb hmean v hsol x hx rad hrad h hrad1)
      (fun h => hom1 N F Kf hKf hFm hFb hmean v hsol x hx rad h hrad1)

/-- (hole 1) A pointwise representative of a mean-zero Neumann class has zero integral on
the unit cube `Q`. -/
theorem aux_cor_neumann_source_integral_rep_zero {d : ℕ}
    (v : meanZeroSobolevGraph (unitNeumannCube d)) {U : SpatialCoordinates d → ℝ}
    (hUae : ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U) :
    ∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), U y = 0 := by
  have hmem := (mem_meanZeroSobolevGraph_iff (v : SobolevData (unitNeumannCube d))).mp v.property
  have hint : ∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)),
      ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) y = 0 := hmem.2
  calc
    ∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), U y
        = ∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)),
          ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ) y :=
      integral_congr_ae hUae.symm
    _ = 0 := hint

/-- (hole 2) Supremum from mean zero (paper 1230-1231: "there is no boundary datum to
subtract"): on `|Q| = 1`, a continuous `U` with `∫_Q U = 0` whose increments on the closed
cube are at most `S` satisfies `|U x| ≤ S` on the closed cube. -/
theorem aux_cor_neumann_source_abs_le_of_mean_zero {d : ℕ} {U : SpatialCoordinates d → ℝ}
    (hU : Continuous U)
    (hmean : ∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), U y = 0) {S : ℝ}
    (hinc : ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
        Set (SpatialCoordinates d)),
      ∀ y ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
        Set (SpatialCoordinates d)), |U x - U y| ≤ S)
    {x : SpatialCoordinates d}
    (hx : x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
      Set (SpatialCoordinates d))) :
    |U x| ≤ S := by
  set Q := (unitNeumannCube d : Set (SpatialCoordinates d)) with hQ
  have hvol : volume.real Q = 1 :=
    centeredCube_one_volume_real (fun _ => (1 / 2 : ℝ)) one_pos
  have hU_int : IntegrableOn U Q volume := by
    have hc := hU.locallyIntegrable (μ := volume)
    have h_compact : IsCompact (@closedBall (SpatialCoordinates d) _ (fun _ => (1 / 2 : ℝ)) (1 / 2) : Set (SpatialCoordinates d)) :=
      isCompact_closedBall _ _
    have hcp := hc.integrableOn_isCompact h_compact
    refine hcp.mono_set ?_
    rw [hQ, unitNeumannCube, centeredCube_coe_eq_ball]
    exact Metric.ball_subset_closedBall
  have hUeq : U x = ∫ y in Q, (U x - U y) ∂volume := by
    have h_const_int : IntegrableOn (fun _ : SpatialCoordinates d => U x) Q volume := by
      have hc : LocallyIntegrable (fun _ : SpatialCoordinates d => U x) volume :=
        (continuous_const.locallyIntegrable (μ := volume))
      have h_compact : IsCompact (@closedBall (SpatialCoordinates d) _ (fun _ => (1 / 2 : ℝ)) (1 / 2) : Set (SpatialCoordinates d)) :=
        isCompact_closedBall _ _
      have hcp := hc.integrableOn_isCompact h_compact
      refine hcp.mono_set ?_
      rw [hQ, unitNeumannCube, centeredCube_coe_eq_ball]
      exact Metric.ball_subset_closedBall
    calc
      U x = (∫ y in Q, U x ∂volume) := by
        rw [setIntegral_const, smul_eq_mul, hvol, one_mul]
      _ = (∫ y in Q, U x ∂volume) - 0 := by ring
      _ = (∫ y in Q, U x ∂volume) - (∫ y in Q, U y ∂volume) := by rw [hmean]
      _ = ∫ y in Q, (U x - U y) ∂volume := by
        rw [← integral_sub h_const_int hU_int]
  rw [hUeq]
  have h_abs : |∫ y in Q, (U x - U y) ∂volume| ≤ ∫ y in Q, |U x - U y| ∂volume :=
    abs_integral_le_integral_abs (f := fun y => U x - U y) (μ := volume.restrict Q)
  have h_bound : ∫ y in Q, |U x - U y| ∂volume ≤ S := by
    have h_abs_int : IntegrableOn (fun y => |U x - U y|) Q volume := by
      have h_cont : Continuous (fun y : SpatialCoordinates d => |U x - U y|) :=
        Continuous.abs (Continuous.sub continuous_const hU)
      have hc : LocallyIntegrable (fun y : SpatialCoordinates d => |U x - U y|) volume :=
        h_cont.locallyIntegrable (μ := volume)
      have h_compact : IsCompact (closedBall (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) : Set (SpatialCoordinates d)) :=
        isCompact_closedBall _ _
      have hcp := hc.integrableOn_isCompact h_compact
      refine hcp.mono_set ?_
      rw [hQ, unitNeumannCube, centeredCube_coe_eq_ball]
      exact Metric.ball_subset_closedBall
    have h_const_int : IntegrableOn (fun _ : SpatialCoordinates d => S) Q volume := by
      have hc : LocallyIntegrable (fun _ : SpatialCoordinates d => S) volume :=
        (continuous_const.locallyIntegrable (μ := volume))
      have h_compact : IsCompact (closedBall (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2) : Set (SpatialCoordinates d)) :=
        isCompact_closedBall _ _
      have hcp := hc.integrableOn_isCompact h_compact
      refine hcp.mono_set ?_
      rw [hQ, unitNeumannCube, centeredCube_coe_eq_ball]
      exact Metric.ball_subset_closedBall
    have h_meas : MeasurableSet Q := (unitNeumannCube d).isOpen.measurableSet
    have h_pointwise : ∀ y ∈ Q, |U x - U y| ≤ S := by
      intro y hy
      have hy' : y ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) := by
        have h_sub : Q ⊆ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) := by
          intro z hz
          exact (centeredCube_subset_closedCube (fun _ => (1 / 2 : ℝ)) one_pos hz : _)
        exact h_sub hy
      exact hinc x hx y hy'
    calc
      ∫ y in Q, |U x - U y| ∂volume ≤ ∫ y in Q, S ∂volume :=
        setIntegral_mono_on h_abs_int h_const_int h_meas h_pointwise
      _ = S := by
        rw [setIntegral_const, smul_eq_mul, hvol, one_mul]
  linarith

/-- (hole 3) `C^α` norm from the pointwise sup bound `(1+√d)[U]_α` and a seminorm bound. -/
theorem aux_cor_neumann_source_cAlpha_tail {d : ℕ} {alpha : ℝ}
    {U : SpatialCoordinates d → ℝ} {B : ℝ}
    (hsup : ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
        Set (SpatialCoordinates d)),
      |U x| ≤ (1 + Real.sqrt d) * holderSeminorm alpha
        (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) U)
    (hB : holderSeminorm alpha
        (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) U ≤ B) :
    cAlphaNorm alpha
        (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) U ≤
      (2 + Real.sqrt d) * B := by
  set S := (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d))
  set T := {v : ℝ | ∃ x ∈ S, v = |U x|} with hT
  have hsup' : sSup T ≤ (1 + Real.sqrt d) * holderSeminorm alpha S U := by
    have h_nonempty : T.Nonempty := by
      have hcenter : (fun _ : Fin d => (1/2 : ℝ)) ∈ S := by
        dsimp [S, closedCube]
        simp
      exact ⟨|U (fun _ => (1/2 : ℝ))|, ⟨fun _ : Fin d => (1/2 : ℝ), hcenter, rfl⟩⟩
    refine csSup_le h_nonempty ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hsup x hx
  unfold cAlphaNorm
  have hsum : sSup {v : ℝ | ∃ x ∈ S, v = |U x|} + holderSeminorm alpha S U ≤
      (2 + Real.sqrt d) * B := by
    have h1 : sSup {v : ℝ | ∃ x ∈ S, v = |U x|} ≤ (1 + Real.sqrt d) * B := by
      apply hsup'.trans
      have hsq : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
      have hpos : 0 ≤ 1 + Real.sqrt d := by linarith
      exact mul_le_mul_of_nonneg_left hB hpos
    have h2 : holderSeminorm alpha S U ≤ B := hB
    linarith
  exact hsum

/-- Consumer (already proved from the holes): the Hölder half of `mfd:cor-neumann-source`
(paper 1207-1236) from all-radii Campanato decay of the mean-zero Neumann solution on the
unit cube, through Campanato's criterion `CampanatoInput` (paper 740-742), which is a
helper hypothesis here. -/
theorem aux_cor_neumann_source_holder_of_campanato {d : ℕ} (Cp : CampanatoInput d)
    {alpha : ℝ} (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (v : meanZeroSobolevGraph (unitNeumannCube d)) {Kc Kf : ℝ} (hKc : 0 ≤ Kc) (hKf : 0 ≤ Kf)
    (hcamp : ∀ x ∈ unitNeumannCube d, ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
      ∫ y in Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
          ((v : SobolevData (unitNeumannCube d)).1 y - setAverage
            (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
            (v : SobolevData (unitNeumannCube d)).1) ^ 2
          ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)) ≤
        (Kc * Kf) ^ 2 * rad ^ (2 * alpha) *
          volume.real (Metric.ball x rad ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))) :
    ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
      IsHolderOn alpha
          (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) U ∧
      ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
      cAlphaNorm alpha
          (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) U ≤
        (2 + Real.sqrt d) * Cp.C alpha * Kc * Kf := by
  have hKK : 0 ≤ Kc * Kf := mul_nonneg hKc hKf
  obtain ⟨U, hUc, hUae, hUH, hUsem⟩ :=
    Cp.holder_of_campanato alpha ha0 ha1 (fun _ => (1 / 2 : ℝ)) 1 one_pos le_rfl
      (v : SobolevData (unitNeumannCube d)).1 (Kc * Kf) hKK hcamp
  refine ⟨U, hUc, hUH, hUae, ?_⟩
  have hmean := aux_cor_neumann_source_integral_rep_zero v hUae
  have hsup : ∀ x ∈ (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
      Set (SpatialCoordinates d)),
      |U x| ≤ (1 + Real.sqrt d) * holderSeminorm alpha
        (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) U :=
    fun x hx => aux_cor_neumann_source_abs_le_of_mean_zero hUc hmean
      (fun x' hx' y' hy' =>
        aux_prop_growth_holder_assembly_increment (fun _ => (1 / 2 : ℝ)) one_pos le_rfl
          ha0 ha1.le hUH hx' hy') hx
  have htail := aux_cor_neumann_source_cAlpha_tail hsup hUsem
  calc _ ≤ (2 + Real.sqrt d) * (Cp.C alpha * (Kc * Kf)) := htail
    _ = (2 + Real.sqrt d) * Cp.C alpha * Kc * Kf := by ring

/-- Admissible-infrared form of `cor_neumann_source`: `H` is the characterized infrared field or a
finite truncation `H_L` of its layers. -/
theorem aux_cor_neumann_source_adm :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (_Cp : CampanatoInput d) (t alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredAdmissible M H → M.delta ≤ delta0 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ)
          (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            IsHolderOn alpha
                (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)) U ∧
            ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
            cAlphaNorm alpha
                (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)) U ≤ K N om * Kf) ∧
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ unitNeumannCube d →
            0 < rad → rad ≤ 1 →
            localGradientEnergy
                (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                (s := Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
                (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
              K N om * Kf ^ 2 * rad ^ t) := by
  intro d hd _ _ E P X W D Cp t alpha k ps ht1 htd ha0 ha1 hps
  obtain ⟨deltaE, hdeltaE, hEn⟩ :=
    aux_cor_neumann_source_energy d hd E P X W D t k ps ht1 htd hps
  obtain ⟨deltaC, hdeltaC, hCa⟩ :=
    aux_cor_neumann_source_campanato d hd E P X W D alpha k ps ha0 ha1 hps
  refine ⟨min deltaE deltaC, lt_min hdeltaE hdeltaC, ?_⟩
  intro M Rm Sreg It H hH hdelta
  obtain ⟨KE, CE, hKE0, hKEL, hKEB, hEae⟩ :=
    hEn M Rm Sreg It H hH (hdelta.trans (min_le_left _ _))
  obtain ⟨Kc, Cc, hKc0, hKcL, hKcB, hCae⟩ :=
    hCa M Rm Sreg It H hH (hdelta.trans (min_le_right _ _))
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = max 1 ((2 + Real.sqrt d) * Cp.C alpha) := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := hcdef ▸ le_max_left _ _
  have hc0 : 0 ≤ c := by linarith
  have hcC : (2 + Real.sqrt d) * Cp.C alpha ≤ c := hcdef ▸ le_max_right _ _
  refine ⟨fun N om => 1 + c * (KE N om + Kc N om),
    fun i => 1 + c * (max (CE i) 0 + max (Cc i) 0), ?_, ?_, ?_⟩
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (KE N) (Kc N) hc0
      (hKEL i N) (hKcL i N) (hKEB i N) (hKcB i N)).1
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (KE N) (Kc N) hc0
      (hKEL i N) (hKcL i N) (hKEB i N) (hKcB i N)).2
  · filter_upwards [hEae, hCae] with om hE hC
    intro N F Kf hKf hFm hFb hmean v hsol
    have hKE := hKE0 N om
    have hKc := hKc0 N om
    obtain ⟨U, hUc, hUH, hUae, hUn⟩ := aux_cor_neumann_source_holder_of_campanato Cp ha0 ha1 v
      hKc hKf (hC N F Kf hKf hFm hFb hmean v hsol)
    refine ⟨⟨U, hUc, hUH, hUae, hUn.trans ?_⟩, ?_⟩
    · have h1 : (2 + Real.sqrt d) * Cp.C alpha * Kc N om ≤ c * Kc N om :=
        mul_le_mul_of_nonneg_right hcC hKc
      have h2 : c * Kc N om ≤ c * (KE N om + Kc N om) :=
        mul_le_mul_of_nonneg_left (by linarith) hc0
      have h3 : (2 + Real.sqrt d) * Cp.C alpha * Kc N om ≤ 1 + c * (KE N om + Kc N om) := by
        linarith
      exact mul_le_mul_of_nonneg_right h3 hKf
    · intro x rad hx hrad hrad1
      have h := hE N F Kf hKf hFm hFb hmean v hsol x rad hx hrad hrad1
      have h1 : KE N om ≤ c * KE N om := le_mul_of_one_le_left hKE hc1
      have h2 : c * KE N om ≤ c * (KE N om + Kc N om) :=
        mul_le_mul_of_nonneg_left (by linarith) hc0
      have hKle : KE N om ≤ 1 + c * (KE N om + Kc N om) := by linarith
      calc _ ≤ KE N om * Kf ^ 2 * rad ^ t := h
        _ ≤ (1 + c * (KE N om + Kc N om)) * Kf ^ 2 * rad ^ t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKle (sq_nonneg _))
            (Real.rpow_nonneg hrad.le _)



theorem cor_neumann_source :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (_Cp : CampanatoInput d) (t alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ)
          (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            IsHolderOn alpha
                (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)) U ∧
            ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
            cAlphaNorm alpha
                (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)) U ≤ K N om * Kf) ∧
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ unitNeumannCube d →
            0 < rad → rad ≤ 1 →
            localGradientEnergy
                (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                (s := Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
                (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
              K N om * Kf ^ 2 * rad ^ t) := by
  intro d hd _ _ E P X W D Cp t alpha k ps ht1 htd ha0 ha1 hps
  obtain ⟨delta0, hdelta0, hall⟩ :=
    aux_cor_neumann_source_adm d hd E P X W D Cp t alpha k ps ht1 htd ha0 ha1 hps
  exact ⟨delta0, hdelta0, fun M Rm Sreg It H hH hδ =>
    hall M Rm Sreg It H (InfraredAdmissible.of_char hH) hδ⟩

end Paper
