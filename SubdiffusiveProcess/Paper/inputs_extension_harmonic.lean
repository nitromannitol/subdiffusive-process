import SubdiffusiveProcess.Paper.inputs_extension_source
import SubdiffusiveProcess.Paper.inputs_extension_ellipticity
import SubdiffusiveProcess.Paper.inputs_extension_seminorm
import SubdiffusiveProcess.Paper.inputs_extension_transport
import SubdiffusiveProcess.Paper.in_extension

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper

/-- The gradient of a datum of finite `H^s` seminorm, pulled back to the origin cube, is in the
full Euclidean `W^{s,2}` class. -/
theorem aux_inputs_extension_harmonic_full {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    (z : SpatialCoordinates d) (m : ℕ) (hr : (0 : ℝ) < (3 : ℝ) ^ m) (s : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (f : Fin d → DomainL2 (centeredCube z ((3 : ℝ) ^ m) hr))
    (hf : cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩ (fun i => f i) ≠ ⊤) :
    Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
      (Homogenization.originCube d (m : ℤ)) ⟨s, hs.1, hs.2⟩
      Homogenization.FiniteLpExponent.two
      (fun y i => ((f i : DomainL2 (centeredCube z ((3 : ℝ) ^ m) hr)) :
        SpatialCoordinates d → ℝ) (y + z)) := by
  let Ω : Opens (SpatialCoordinates d) := centeredCube z ((3 : ℝ) ^ m) hr
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d (m : ℤ)
  let U : Set (Homogenization.Vec d) := Homogenization.openCubeSet Q
  let sOrder : Homogenization.FractionalOrder := ⟨s, hs.1, hs.2⟩
  let gFun : SpatialCoordinates d → SpatialCoordinates d := fun x i => (f i : DomainL2 Ω) x
  let gQ : Homogenization.Vec d → Homogenization.Vec d := fun y i => (f i : DomainL2 Ω) (y + z)
  have hdom : (Ω : Set (SpatialCoordinates d)) = Homogenization.translateSet z U :=
    aux_inputs_extension_transport_domain z m hr
  have hfracLocal : SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
      (Ω : Set (SpatialCoordinates d)) s gFun ≠ ⊤ := by
    rw [← aux_inputs_extension_transport_raw_eq_fractionalOn hd z ((3 : ℝ) ^ m) hr
      ⟨s, hs.1, hs.2⟩ (fun i => f i)]
    exact hf
  have hfracTrans : SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
      (Homogenization.translateSet z U) s gFun ≠ ⊤ := by
    simpa only [hdom] using hfracLocal
  have hfracQ : SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn U s gQ ≠ ⊤ := by
    rw [SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.fractionalSeminormOn_translateSet
      z U s gFun] at hfracTrans
    simpa only [gFun, gQ] using hfracTrans
  have hgCoord (i : Fin d) : MemLp
      (fun y : Homogenization.Vec d => (f i : DomainL2 Ω) (y + z))
      2 (volume.restrict U) := by
    have hgi : MemLp (fun x : SpatialCoordinates d => (f i : DomainL2 Ω) x)
        2 (volume.restrict (Homogenization.translateSet z U)) := by
      simpa only [← hdom] using (Lp.memLp (f i))
    simpa only using hgi.comp_measurePreserving
      (Homogenization.measurePreserving_addRight_restrict_translateSet z U)
  have hHilbert : MemLp (fun y => Homogenization.HilbertVec.ofVec (gQ y)) 2
      (volume.restrict U) := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    simpa only [gQ, Homogenization.HilbertVec.ofVec, PiLp.toLp_apply] using hgCoord i
  have hLp : MemLp (fun y => Homogenization.HilbertVec.ofVec (gQ y)) 2
      (Homogenization.normalizedCubeMeasure Q) := by
    simpa only [Homogenization.normalizedCubeMeasure, Homogenization.cubeMeasure,
      Homogenization.volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
        hHilbert.smul_measure ENNReal.ofReal_ne_top
  have hsemi : Homogenization.cubeEuclideanWspESeminorm Q sOrder
      Homogenization.FiniteLpExponent.two gQ < ⊤ := by
    have hEq :=
      SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.fractionalSeminormOn_openCubeSet_eq_sqrt_mul_cubeEuclideanWspESeminorm
        Q sOrder gQ
    have hcoef : (ENNReal.ofReal sOrder.1) ^ (1 / 2 : ℝ) ≠ 0 := by
      exact ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hs.1)
        ENNReal.ofReal_ne_top)
    have hne : Homogenization.cubeEuclideanWspESeminorm Q sOrder
        Homogenization.FiniteLpExponent.two gQ ≠ ⊤ := by
      intro htop
      apply hfracQ
      rw [hEq, htop]
      exact ENNReal.mul_top hcoef
    exact lt_top_iff_ne_top.mpr hne
  exact ⟨hLp,
    Homogenization.memCubeEuclideanWsp_of_memLp_of_eSeminorm_lt_top hLp hsemi⟩

/-- Gagliardo seminorm of the pulled-back field (no sign change). -/
theorem aux_inputs_extension_harmonic_fractional {d : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (m : ℕ) (hr : (0 : ℝ) < (3 : ℝ) ^ m)
    (s : Set.Ioo (0 : ℝ) 1) (f : Fin d → DomainL2 (centeredCube z ((3 : ℝ) ^ m) hr)) :
    SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
      (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))) s.1
        (fun y i => ((f i : DomainL2 (centeredCube z ((3 : ℝ) ^ m) hr)) :
          SpatialCoordinates d → ℝ) (y + z)) =
      cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr s f := by
  let U := Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))
  let G : Homogenization.Vec d → Homogenization.Vec d := fun x i => f i x
  calc
    _ = SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn (Homogenization.translateSet z U) s.1 G :=
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.fractionalSeminormOn_translateSet
        z U s.1 G).symm
    _ = SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
          (centeredCube z ((3 : ℝ) ^ m) hr : Set (SpatialCoordinates d)) s.1 G := by
      rw [← SubdiffusiveProcess.AffineSobolevNorms.centeredCube_eq_translate_originCube z m hr]
    _ = _ := inputs_extension_seminorm hd z ((3 : ℝ) ^ m) hr s f

/-- The norm of the cube average is at most the normalized `L²` norm. -/
theorem aux_inputs_extension_harmonic_mean {d : ℕ} [NeZero d]
    (z : SpatialCoordinates d) (m : ℕ) (hr : (0 : ℝ) < (3 : ℝ) ^ m)
    (f : Fin d → DomainL2 (centeredCube z ((3 : ℝ) ^ m) hr)) :
    Real.sqrt (Homogenization.vecNormSq (Homogenization.cubeAverageVec
      (Homogenization.originCube d (m : ℤ))
      (fun y i => ((f i : DomainL2 (centeredCube z ((3 : ℝ) ^ m) hr)) :
        SpatialCoordinates d → ℝ) (y + z)))) ≤
      Real.sqrt (∑ i : Fin d, ‖f i‖ ^ 2) /
        Real.sqrt (volume.real (centeredCube z ((3 : ℝ) ^ m) hr : Set (SpatialCoordinates d))) := by
  classical
  let F : Homogenization.Vec d → Homogenization.Vec d := fun y i =>
    ((f i : DomainL2 (centeredCube z ((3 : ℝ) ^ m) hr)) : SpatialCoordinates d → ℝ) (y + z)
  set V : ℝ := volume.real (centeredCube z ((3 : ℝ) ^ m) hr : Set (SpatialCoordinates d)) with hVdef
  have hVpos : 0 < V := by
    rw [hVdef]
    exact centeredCube_volume_pos z hr
  have hvol : Homogenization.cubeVolume (Homogenization.originCube d (m : ℤ)) = V := by
    rw [hVdef, Homogenization.cubeVolume, Homogenization.cubeScaleFactor_originCube, zpow_natCast,
      centeredCube_volume_real z hr]
  have hdom := aux_inputs_extension_transport_domain z m hr
  have hres : volume.restrict (Homogenization.cubeSet (Homogenization.originCube d (m : ℤ))) =
      volume.restrict (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))) :=
    Measure.restrict_congr_set (Homogenization.cubeSet_ae_eq_openCubeSet _)
  have hMemLp (i : Fin d) : MeasureTheory.MemLp (fun y : Homogenization.Vec d => F y i) 2
      (Homogenization.normalizedCubeMeasure (Homogenization.originCube d (m : ℤ))) := by
    set g : SpatialCoordinates d → ℝ := fun x =>
      ((f i : DomainL2 (centeredCube z ((3 : ℝ) ^ m) hr)) : SpatialCoordinates d → ℝ) x with hgdef
    have hF : (fun y : Homogenization.Vec d => F y i) = fun y => g (y + z) := rfl
    rw [hF]
    have h1 : MeasureTheory.MemLp g 2
        (volume.restrict (centeredCube z ((3 : ℝ) ^ m) hr : Set (SpatialCoordinates d))) :=
      Lp.memLp (f i)
    rw [hdom] at h1
    have h2 : MeasureTheory.MemLp (fun y : Homogenization.Vec d => g (y + z)) 2
        (volume.restrict (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ)))) :=
      h1.comp_measurePreserving (Homogenization.measurePreserving_addRight_restrict_translateSet z
        (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ))))
    rw [← hres] at h2
    have h3 := h2.smul_measure (c := ENNReal.ofReal ((Homogenization.cubeVolume
      (Homogenization.originCube d (m : ℤ)))⁻¹)) ENNReal.ofReal_ne_top
    simpa [Homogenization.normalizedCubeMeasure, Homogenization.cubeMeasure] using h3
  have hsq (i : Fin d) : (∫ x in (centeredCube z ((3 : ℝ) ^ m) hr : Set (SpatialCoordinates d)),
      (((f i : DomainL2 (centeredCube z ((3 : ℝ) ^ m) hr)) : SpatialCoordinates d → ℝ) x) ^ 2
        ∂volume) = ‖f i‖ ^ 2 := by
    rw [L2.norm_sq_eq_inner' (𝕜 := ℝ)]
    rw [L2.inner_def (𝕜 := ℝ)]
    simp only [RCLike.re_to_real]
    apply integral_congr_ae
    filter_upwards with x
    simp [sq_abs]
  have hInt (i : Fin d) : (∫ y in Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)),
      (F y i) ^ 2) = ‖f i‖ ^ 2 := by
    set g : SpatialCoordinates d → ℝ := fun x =>
      ((f i : DomainL2 (centeredCube z ((3 : ℝ) ^ m) hr)) : SpatialCoordinates d → ℝ) x with hgdef
    have hF : (fun y : Homogenization.Vec d => (F y i) ^ 2) = fun y => (g (y + z)) ^ 2 := rfl
    rw [hF]
    rw [setIntegral_congr_set (μ := volume)
      (Homogenization.cubeSet_ae_eq_openCubeSet (Homogenization.originCube d (m : ℤ)))]
    rw [Homogenization.setIntegral_comp_addRight_translateSet z
      (Homogenization.openCubeSet (Homogenization.originCube d (m : ℤ)))
      (fun x : SpatialCoordinates d => (g x) ^ 2)]
    rw [← hdom, hsq i]
  have hcoord (i : Fin d) : (Homogenization.cubeAverage (Homogenization.originCube d (m : ℤ))
      (fun y : Homogenization.Vec d => F y i)) ^ 2 ≤ ‖f i‖ ^ 2 / V := by
    have hj := Homogenization.sq_cubeAverage_le_cubeAverage_sq_of_memLp
      (Homogenization.originCube d (m : ℤ)) (fun y : Homogenization.Vec d => F y i) (hMemLp i)
    calc
      (Homogenization.cubeAverage (Homogenization.originCube d (m : ℤ))
          (fun y : Homogenization.Vec d => F y i)) ^ 2 ≤
          Homogenization.cubeAverage (Homogenization.originCube d (m : ℤ))
            (fun y : Homogenization.Vec d => (F y i) ^ 2) := hj
      _ = V⁻¹ * (∫ y in Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)),
              (F y i) ^ 2) := by
            rw [Homogenization.cubeAverage, hvol]
      _ = V⁻¹ * ‖f i‖ ^ 2 := by rw [hInt i]
      _ = ‖f i‖ ^ 2 / V := by rw [div_eq_inv_mul]
  have hsum : Homogenization.vecNormSq (Homogenization.cubeAverageVec
      (Homogenization.originCube d (m : ℤ)) F) ≤ (∑ i : Fin d, ‖f i‖ ^ 2) / V := by
    calc
      Homogenization.vecNormSq (Homogenization.cubeAverageVec (Homogenization.originCube d (m : ℤ)) F)
          = ∑ i : Fin d, (Homogenization.cubeAverage (Homogenization.originCube d (m : ℤ))
              (fun y : Homogenization.Vec d => F y i)) ^ 2 := by
            simp [Homogenization.cubeAverageVec, Homogenization.vecNormSq, Homogenization.vecDot,
              pow_two]
      _ ≤ ∑ i : Fin d, ‖f i‖ ^ 2 / V := Finset.sum_le_sum (fun i _ => hcoord i)
      _ = (∑ i : Fin d, ‖f i‖ ^ 2) / V := by rw [Finset.sum_div]
  have hb := Real.sqrt_le_sqrt hsum
  rw [Real.sqrt_div' _ hVpos.le] at hb
  rw [hVdef] at hb
  exact hb

theorem aux_inputs_extension_harmonic_arith {C0 D s Ls Lh w G Mean mean' semiB first : ℝ}
    (hC0 : 0 < C0) (hD : 0 < D) (hs0 : 0 < s) (hs1 : s < 1) (hLs : 0 ≤ Ls) (hLsLh : Ls ≤ Lh)
    (hw : 0 ≤ w) (hG : 0 ≤ G) (hMean : 0 ≤ Mean) (hmean' : mean' ≤ Mean)
    (hsemiB : semiB ≤ D * w * (s ^ (-(1 / 2) : ℝ) * G)) (hfirst : first ≤ 0) :
    first + C0 * s ^ (-(1 / 2) : ℝ) * Ls ^ ((1 / 2) : ℝ) * (mean' + semiB) ≤
      C0 * (1 + D) * s ^ (-(3 / 2) : ℝ) * Lh ^ ((1 / 2) : ℝ) * (w * G + Mean) := by
  have hp : 0 < s ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos hs0 _
  have hpq : s ^ (-(1 / 2) : ℝ) ≤ s ^ (-(3 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hs0 hs1.le (by norm_num)
  have hpp : s ^ (-(1 / 2) : ℝ) * s ^ (-(1 / 2) : ℝ) ≤ s ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_add hs0]
    exact Real.rpow_le_rpow_of_exponent_ge hs0 hs1.le (by norm_num)
  have hq : 0 ≤ s ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hs0.le _
  have hLsh : Ls ^ ((1 / 2) : ℝ) ≤ Lh ^ ((1 / 2) : ℝ) :=
    Real.rpow_le_rpow hLs hLsLh (by norm_num)
  have hLs0 : 0 ≤ Ls ^ ((1 / 2) : ℝ) := Real.rpow_nonneg hLs _
  have hmean : mean' + semiB ≤ Mean + D * w * (s ^ (-(1 / 2) : ℝ) * G) := add_le_add hmean' hsemiB
  have hinner : s ^ (-(1 / 2) : ℝ) * (Mean + D * w * (s ^ (-(1 / 2) : ℝ) * G)) ≤
      (1 + D) * s ^ (-(3 / 2) : ℝ) * (w * G + Mean) := by
    have h1 : s ^ (-(1 / 2) : ℝ) * Mean ≤ s ^ (-(3 / 2) : ℝ) * Mean :=
      mul_le_mul_of_nonneg_right hpq hMean
    have hwG : 0 ≤ w * G := mul_nonneg hw hG
    have h2 : s ^ (-(1 / 2) : ℝ) * (D * w * (s ^ (-(1 / 2) : ℝ) * G)) ≤
        s ^ (-(3 / 2) : ℝ) * (D * (w * G)) := by
      have : s ^ (-(1 / 2) : ℝ) * (D * w * (s ^ (-(1 / 2) : ℝ) * G)) =
          (s ^ (-(1 / 2) : ℝ) * s ^ (-(1 / 2) : ℝ)) * (D * (w * G)) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hpp (mul_nonneg hD.le hwG)
    nlinarith [mul_nonneg hq hMean, mul_nonneg hq hwG, mul_nonneg hq (mul_nonneg hD.le hwG),
      mul_nonneg hq (mul_nonneg hD.le hMean)]
  have hcoef : 0 ≤ C0 * Ls ^ ((1 / 2) : ℝ) := mul_nonneg hC0.le hLs0
  calc first + C0 * s ^ (-(1 / 2) : ℝ) * Ls ^ ((1 / 2) : ℝ) * (mean' + semiB)
      ≤ 0 + C0 * Ls ^ ((1 / 2) : ℝ) * (s ^ (-(1 / 2) : ℝ) * (Mean + D * w * (s ^ (-(1 / 2) : ℝ) * G))) := by
        have : C0 * s ^ (-(1 / 2) : ℝ) * Ls ^ ((1 / 2) : ℝ) * (mean' + semiB) =
            C0 * Ls ^ ((1 / 2) : ℝ) * (s ^ (-(1 / 2) : ℝ) * (mean' + semiB)) := by ring
        rw [this]
        refine add_le_add hfirst (mul_le_mul_of_nonneg_left ?_ hcoef)
        exact mul_le_mul_of_nonneg_left hmean hp.le
    _ ≤ C0 * Ls ^ ((1 / 2) : ℝ) * ((1 + D) * s ^ (-(3 / 2) : ℝ) * (w * G + Mean)) := by
        rw [zero_add]; exact mul_le_mul_of_nonneg_left hinner hcoef
    _ ≤ C0 * Lh ^ ((1 / 2) : ℝ) * ((1 + D) * s ^ (-(3 / 2) : ℝ) * (w * G + Mean)) := by
        have hR : 0 ≤ (1 + D) * s ^ (-(3 / 2) : ℝ) * (w * G + Mean) :=
          mul_nonneg (mul_nonneg (by linarith) hq) (add_nonneg (mul_nonneg hw hG) hMean)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLsh hC0.le) hR
    _ = _ := by ring


theorem inputs_extension_harmonic (d : ℕ) (hd : 2 ≤ d) (Jc : Paper.in_J d) :
    ∃ C : ℝ, 0 < C ∧
    (∀ (z : SpatialCoordinates d) (m : ℕ) (hr : (0 : ℝ) < 3 ^ m)
      (a : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hr))
      (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1),      ∀ (hDatum v : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr))
        (hhfin : cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
          (fun i => sobolevGradient (hDatum : SobolevData _) i) ≠ ⊤),
      
      (∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr),
        sobolevCoefficientForm a (v : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) (φ : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) = 0) →
      ((v : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) - (hDatum : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr))) ∈ killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hr) →
      normalizedEnergyNorm a
          (centeredCube z ((3 : ℝ) ^ m) hr).isOpen.measurableSet
          (sobolevGradient (v : SobolevData _)) ≤
        C * s ^ (-(3 / 2) : ℝ) *
            (Jc.Lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ ((1 / 2) : ℝ) *
            (3 : ℝ) ^ (s * (m : ℝ)) *
            cubeFractionalL2Norm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
              ⟨fun i => sobolevGradient (hDatum : SobolevData (centeredCube z ((3 : ℝ) ^ m) hr)) i,
                lt_top_iff_ne_top.2 hhfin⟩) := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨C0, hC0, hDir, _⟩ :=
    (Homogenization.Book.Ch03.energyConsequencesRHSTheory (d := d)).exists_constant
  let D := SubdiffusiveProcess.CoarseGrainingVocab.caccioppoliExactDatumConstant d
  have hD : 0 < D := SubdiffusiveProcess.CoarseGrainingVocab.caccioppoliExactDatumConstant_pos d
  refine ⟨C0 * (1 + D), mul_pos hC0 (by linarith), ?_⟩
  intro z m hr a s hs hDatum v hhfin hweak htrace
  let Ω := centeredCube z ((3 : ℝ) ^ m) hr
  let Q := Homogenization.originCube d (m : ℤ)
  let A := Homogenization.Book.Ch02.TriadicCoeffFamily.dilate (m : ℤ)
    (Jc.chart z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m))
  let g0 : HilbertGradient Ω := 0
  have hzero : (fun x i => (g0 i : SpatialCoordinates d → ℝ) x) =ᵐ[
      volume.restrict (Ω : Set (SpatialCoordinates d))] (0 : SpatialCoordinates d → SpatialCoordinates d) := by
    have hi (i : Fin d) : (fun x => (g0 i : SpatialCoordinates d → ℝ) x) =ᵐ[
        volume.restrict (Ω : Set (SpatialCoordinates d))] 0 := Lp.coeFn_zero ℝ 2 _
    filter_upwards [ae_all_iff.2 hi] with x hx
    exact funext hx
  have hsem0 : cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
      (fun i => g0 i) = 0 := by
    rw [inputs_extension_seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩ (fun i => g0 i) |>.symm,
      SubdiffusiveProcess.FractionalAECongruence.fractionalSeminormOn_congr _ _ hzero,
      SubdiffusiveProcess.FractionalAECongruence.fractionalSeminormOn_zero]
  have hz0 : cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
      (fun i => g0 i) ≠ ⊤ := by rw [hsem0]; exact ENNReal.zero_ne_top
  have hweak0 : ∀ φ : killedSobolevGraph Ω,
      sobolevCoefficientForm a (v : SobolevData Ω) (φ : SobolevData Ω) =
        -inner ℝ g0 (subspaceGradient (killedSobolevGraph Ω) φ) := by
    intro φ
    rw [inner_zero_left, neg_zero]
    exact hweak φ
  obtain ⟨hFull0, sol, hbd, hgrad, he⟩ := inputs_extension_transport d hd Jc
    z m hr a s hs g0 hz0 hDatum v hhfin hweak0 htrace
  -- Besov regularity of the zero source and of the boundary gradient
  let gs0 : Homogenization.Vec d → Homogenization.Vec d :=
    fun y i => -((g0 i : SpatialCoordinates d → ℝ) (y + z))
  let W0 : Homogenization.CubeEuclideanWspField Q ⟨s, hs.1, hs.2⟩
      Homogenization.FiniteLpExponent.two :=
    { toField := gs0, euclideanMemLp := hFull0.1, euclideanMemWsp := hFull0.2 }
  have hgB := (SubdiffusiveProcess.CoarseGrainingVocab.cubeEuclideanWspField_forceSobolevRegularity
    ⟨s, hs.1, hs.2⟩ W0).toForceBesovRegularity hs.1 hs.2.le
  let gb : Homogenization.Vec d → Homogenization.Vec d := fun y i =>
    ((sobolevGradient (hDatum : SobolevData Ω) i : DomainL2 Ω) :
      SpatialCoordinates d → ℝ) (y + z)
  have hFullB := aux_inputs_extension_harmonic_full hd z m hr s hs
    (fun i => sobolevGradient (hDatum : SobolevData Ω) i) hhfin
  let WB : Homogenization.CubeEuclideanWspField Q ⟨s, hs.1, hs.2⟩
      Homogenization.FiniteLpExponent.two :=
    { toField := gb, euclideanMemLp := hFullB.1, euclideanMemWsp := hFullB.2 }
  have hbd' : Homogenization.Book.Ch03.dirichletBoundaryGradientField sol = gb := hbd
  have hzB : Homogenization.Book.Ch03.ForceBesovRegularity Q s
      (Homogenization.Book.Ch03.dirichletBoundaryGradientField sol) := by
    rw [hbd']
    exact (SubdiffusiveProcess.CoarseGrainingVocab.cubeEuclideanWspField_forceSobolevRegularity
      ⟨s, hs.1, hs.2⟩ WB).toForceBesovRegularity hs.1 hs.2.le
  have hn := hDir sol hs.1 hs.2 hgB hzB
  unfold Homogenization.Book.Ch03.dirichletEnergyWithRHSRHS at hn
  rw [hbd'] at hn
  -- the two Besov quantities against the Gagliardo seminorm
  have hweight : Homogenization.cubeBesovScaleWeight (-s) Q = (3 : ℝ) ^ (s * (m : ℝ)) := by
    simp only [Homogenization.cubeBesovScaleWeight, Homogenization.cubeScaleFactor, Q,
      Homogenization.originCube, neg_neg]
    rw [← Real.rpow_intCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  have hf0 := aux_inputs_extension_source_fractional hd z m hr ⟨s, hs.1, hs.2⟩ (fun i => g0 i)
  have hp0 := SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.scaleNormalizedPositiveBesovVectorSeminormTwo_le_fractionalSeminormOn
    Q ⟨s, hs.1, hs.2⟩ gs0 hFull0
  change Homogenization.Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s gs0 ≤
    D * Homogenization.cubeBesovScaleWeight (-s) Q *
      (s ^ (-(1 / 2) : ℝ) * (SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
        (Homogenization.openCubeSet Q) s gs0).toReal) at hp0
  rw [hf0, hsem0] at hp0
  have hp1 := SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.scaleNormalizedPositiveBesovVectorSeminormTwo_le_fractionalSeminormOn
    Q ⟨s, hs.1, hs.2⟩ gb hFullB
  have hf1 := aux_inputs_extension_harmonic_fractional hd z m hr ⟨s, hs.1, hs.2⟩
    (fun i => sobolevGradient (hDatum : SobolevData Ω) i)
  change Homogenization.Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s gb ≤
    D * Homogenization.cubeBesovScaleWeight (-s) Q *
      (s ^ (-(1 / 2) : ℝ) * (SubdiffusiveProcess.CoarseGrainingVocab.fractionalSeminormOn
        (Homogenization.openCubeSet Q) s gb).toReal) at hp1
  rw [hf1, hweight] at hp1
  have hmean := aux_inputs_extension_harmonic_mean (d := d) z m hr
    (fun i => sobolevGradient (hDatum : SobolevData Ω) i)
  -- ellipticities
  have hs01 : s ∈ Set.Ioc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
  have hs201 : s / 2 ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hLamS := (inputs_extension_ellipticity d Jc z m hr a s hs01).2
  have hLamH := (inputs_extension_ellipticity d Jc z m hr a (s / 2) hs201).2
  have hlamH := (inputs_extension_ellipticity d Jc z m hr a (s / 2) hs201).1
  change Jc.Lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) s 2 =
    Homogenization.Book.Ch02.LambdaSq Q s (.finite 2) A at hLamS
  change Jc.Lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2 =
    Homogenization.Book.Ch02.LambdaSq Q (s / 2) (.finite 2) A at hLamH
  change Jc.lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2 =
    Homogenization.Book.Ch02.lambdaSq Q (s / 2) (.finite 2) A at hlamH
  have hanti : Homogenization.Book.Ch02.LambdaSq Q s (.finite 2) A ≤
      Homogenization.Book.Ch02.LambdaSq Q (s / 2) (.finite 2) A :=
    Homogenization.Book.Ch02.LambdaSq_antitone Q A (by linarith [hs.1]) (by linarith [hs.1])
      (by simp [Homogenization.Book.Ch02.MultiscaleExponent.IsAdmissible])
  have hLsPos : 0 < Homogenization.Book.Ch02.LambdaSq Q s (.finite 2) A := by
    rw [← hLamS]; exact Jc.Lam_pos _ _ _ _ _ _ _ _
  have hlowerNN : 0 ≤ Homogenization.Book.Ch03.poincareLowerEllipticityFactor Q A (s / 2) (.finite 2) := by
    unfold Homogenization.Book.Ch03.poincareLowerEllipticityFactor
    exact Real.rpow_nonneg (by rw [← hlamH]; exact (Jc.lam_pos _ _ _ _ _ _ _ _).le) _
  have hsemi0 : Homogenization.Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s gs0 ≤ 0 := by
    refine hp0.trans (le_of_eq ?_)
    simp
  have hfirst : C0 * Real.rpow s (-(3 / 2 : ℝ)) *
      Homogenization.Book.Ch03.poincareLowerEllipticityFactor Q A (s / 2) (.finite 2) *
      Homogenization.Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s gs0 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg hC0.le (Real.rpow_nonneg hs.1.le _)) hlowerNN) hsemi0
  have hGnn : 0 ≤ (cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
      (fun i => sobolevGradient (hDatum : SobolevData Ω) i)).toReal := ENNReal.toReal_nonneg
  have hMeanNN : 0 ≤ Real.sqrt (∑ i : Fin d, ‖sobolevGradient (hDatum : SobolevData Ω) i‖ ^ 2) /
      Real.sqrt (volume.real (Ω : Set (SpatialCoordinates d))) :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hArith := aux_inputs_extension_harmonic_arith (C0 := C0) (D := D) (s := s)
    (Ls := Homogenization.Book.Ch02.LambdaSq Q s (.finite 2) A)
    (Lh := Jc.Lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2)
    (w := (3 : ℝ) ^ (s * (m : ℝ)))
    (G := (cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
      (fun i => sobolevGradient (hDatum : SobolevData Ω) i)).toReal)
    (Mean := Real.sqrt (∑ i : Fin d, ‖sobolevGradient (hDatum : SobolevData Ω) i‖ ^ 2) /
      Real.sqrt (volume.real (Ω : Set (SpatialCoordinates d))))
    (mean' := Real.sqrt (Homogenization.vecNormSq (Homogenization.cubeAverageVec Q gb)))
    (semiB := Homogenization.Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s gb)
    (first := C0 * Real.rpow s (-(3 / 2 : ℝ)) *
      Homogenization.Book.Ch03.poincareLowerEllipticityFactor Q A (s / 2) (.finite 2) *
      Homogenization.Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s gs0)
    hC0 hD hs.1 hs.2 hLsPos.le (by rw [hLamH]; exact hanti) (Real.rpow_nonneg (by norm_num) _)
    hGnn hMeanNN hmean hp1 hfirst
  have hrs : (3 : ℝ) ^ (s * (m : ℝ)) * ((3 : ℝ) ^ m) ^ (-s) = 1 := by
    rw [← Real.rpow_natCast (3 : ℝ) m, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    have h0 : s * (m : ℝ) + (m : ℝ) * -s = 0 := by ring
    rw [h0, Real.rpow_zero]
  refine he.trans (hn.trans ?_)
  calc _ = C0 * Real.rpow s (-(3 / 2 : ℝ)) *
      Homogenization.Book.Ch03.poincareLowerEllipticityFactor Q A (s / 2) (.finite 2) *
      Homogenization.Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s gs0 +
      C0 * s ^ (-(1 / 2) : ℝ) * (Homogenization.Book.Ch02.LambdaSq Q s (.finite 2) A) ^ ((1 / 2) : ℝ) *
      (Real.sqrt (Homogenization.vecNormSq (Homogenization.cubeAverageVec Q gb)) +
        Homogenization.Book.Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q s gb) := rfl
    _ ≤ _ := hArith
    _ = _ := by
      unfold cubeFractionalL2Norm
      have : C0 * (1 + D) * s ^ (-(3 / 2) : ℝ) * (Jc.Lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ ((1 / 2) : ℝ) *
          (3 : ℝ) ^ (s * (m : ℝ)) *
          ((cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
              (fun i => sobolevGradient (hDatum : SobolevData Ω) i)).toReal +
            ((3 : ℝ) ^ m) ^ (-s) * (Real.sqrt (∑ i : Fin d, ‖sobolevGradient (hDatum : SobolevData Ω) i‖ ^ 2) /
              Real.sqrt (volume.real (Ω : Set (SpatialCoordinates d))))) =
          C0 * (1 + D) * s ^ (-(3 / 2) : ℝ) * (Jc.Lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ ((1 / 2) : ℝ) *
          ((3 : ℝ) ^ (s * (m : ℝ)) * (cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ m) hr ⟨s, hs.1, hs.2⟩
              (fun i => sobolevGradient (hDatum : SobolevData Ω) i)).toReal +
            (Real.sqrt (∑ i : Fin d, ‖sobolevGradient (hDatum : SobolevData Ω) i‖ ^ 2) /
              Real.sqrt (volume.real (Ω : Set (SpatialCoordinates d))))) := by
        have := hrs
        linear_combination (C0 * (1 + D) * s ^ (-(3 / 2) : ℝ) * (Jc.Lam z ((3 : ℝ) ^ m) hr a z ((3 : ℝ) ^ m) (s / 2) 2) ^ ((1 / 2) : ℝ) *
          (Real.sqrt (∑ i : Fin d, ‖sobolevGradient (hDatum : SobolevData Ω) i‖ ^ 2) /
              Real.sqrt (volume.real (Ω : Set (SpatialCoordinates d))))) * this
      exact this.symm

end Paper
