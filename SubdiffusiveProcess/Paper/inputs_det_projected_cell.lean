module

public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.InteriorCaccioppoli
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEnergyReadout
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryCellGeometry
public import SubdiffusiveProcess.Analysis.ScalarEnergyTransport
public import SubdiffusiveProcess.Analysis.InteriorComparisonErrorTransport
public import SubdiffusiveProcess.Analysis.SmoothDualInteriorGeneric
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.PhysicalDirichletCarrier

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book Homogenization.Book.Ch03
open SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
open scoped BigOperators ENNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess.Paper

/-- A normalized average over a subset is controlled by the volume ratio and the ambient normalized
average; the integrand is only required to be nonnegative almost everywhere on the ambient set. -/
theorem aux_inputs_det_projected_cell_le_mul_ae {d : ℕ}
    {S T : Set (Vec d)} {f : Vec d → ℝ} {K : ℝ}
    (hST : S ⊆ T) (hSpos : 0 < volume S) (hTtop : volume T < ∞)
    (hf : ∀ᵐ y ∂(volume.restrict T), 0 ≤ f y)
    (hint : IntegrableOn f T volume)
    (hK : (volume T).toReal ≤ K * (volume S).toReal) :
    normalizedSetAverage S f ≤ K * normalizedSetAverage T f := by
  have hSle : volume S ≤ volume T := measure_mono hST
  have hSreal : 0 < (volume S).toReal :=
    ENNReal.toReal_pos (ne_of_gt hSpos) (ne_of_lt (lt_of_le_of_lt hSle hTtop))
  have hTreal : 0 < (volume T).toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le hSpos hSle)) (ne_of_lt hTtop)
  have hraw : ∫ y in S, f y ∂volume ≤ ∫ y in T, f y ∂volume :=
    setIntegral_mono_set hint hf (Filter.Eventually.of_forall hST)
  have hIT : 0 ≤ ∫ y in T, f y ∂volume := integral_nonneg_of_ae hf
  have hratio : (volume S).toReal⁻¹ * (volume T).toReal ≤ K := by
    have h := mul_le_mul_of_nonneg_left hK (le_of_lt (inv_pos.2 hSreal))
    have heq : (volume S).toReal⁻¹ * (K * (volume S).toReal) = K := by
      field_simp
    rwa [heq] at h
  have hTavg : 0 ≤ (volume T).toReal⁻¹ * ∫ y in T, f y ∂volume :=
    mul_nonneg (le_of_lt (inv_pos.2 hTreal)) hIT
  unfold normalizedSetAverage volumeAverage
  calc
    (volume S).toReal⁻¹ * ∫ y in S, f y ∂volume ≤
        (volume S).toReal⁻¹ * ∫ y in T, f y ∂volume :=
      mul_le_mul_of_nonneg_left hraw (le_of_lt (inv_pos.2 hSreal))
    _ = ((volume S).toReal⁻¹ * (volume T).toReal) *
          ((volume T).toReal⁻¹ * ∫ y in T, f y ∂volume) := by
      field_simp
    _ ≤ K * ((volume T).toReal⁻¹ * ∫ y in T, f y ∂volume) :=
      mul_le_mul_of_nonneg_right hratio hTavg

/-- Almost-everywhere positivity of the scalar coefficient on a translated subset of the cube. -/
theorem aux_inputs_det_projected_cell_ae_nonneg {d : ℕ} (Q : Homogenization.TriadicCube d) (c : Vec d)
    {a : Vec d → ℝ} (data : ScalarTriadicCoeffData (fun p => a (p + c)))
    (V : Set (Vec d)) (hV : V ⊆ openCubeSet Q) :
    ∀ᵐ x ∂(volume.restrict (translateSet c V)), 0 ≤ a x := by
  have hb := (data.onCube Q).aeBounds
  have h1 : ∀ᵐ x ∂(volume.restrict V), 0 ≤ a (x + c) := by
    have hsub : V ⊆ (Ch02.cubeDomain Q : Set (Vec d)) := by
      rw [Ch02.cubeDomain_coe]
      exact hV
    have hb' : ∀ᵐ x ∂(volume.restrict V), _ := ae_restrict_of_ae_restrict_of_subset hsub hb
    filter_upwards [hb'] with x hx
    exact le_trans (data.onCube Q).lam_pos.le hx.1
  rw [← image_addRight_eq_translateSet]
  have hmp := (measurePreserving_add_right (volume : Measure (Vec d)) c).restrict_image_emb
    (measurableEmbedding_addRight c) V
  rw [← hmp.map_eq]
  exact ((measurableEmbedding_addRight c).ae_map_iff).2 h1

/-- The recentred localized coefficient energy is the physical normalized average of `a |∇u|²` on
the translated set (frame change for an arbitrary scalar family). -/
theorem aux_inputs_det_projected_cell_frame {d : ℕ} [NeZero d] (a : Vec d → ℝ) (k : ℤ) (y : Vec d)
    (dataY : ScalarTriadicCoeffData (fun q => a (q + y)))
    (V : Set (Vec d))
    (u0 : H1Function (openCubeSet (originCube d k)))
    (gradU : Vec d → Vec d)
    (hgrad : ∀ x, u0.grad x = gradU (x + y)) :
    localizedCoeffEnergyValue V
        ((dataY.toTriadicCoeffFamily.coeffOn (originCube d k))) u0 =
      Homogenization.volumeAverage (translateSet y V)
        (fun x => a x * vecNormSq (gradU x)) := by
  have hdens : coefficientEnergyDensity
      ((dataY.toTriadicCoeffFamily.coeffOn (originCube d k)).toCoeffField) u0.grad =
      fun x => a (x + y) * vecNormSq (gradU (x + y)) := by
    rw [show (dataY.toTriadicCoeffFamily.coeffOn (originCube d k)).toCoeffField =
        (dataY.onCube (originCube d k)).toCoeffOn.toCoeffField from rfl,
      SubdiffusiveProcess.ScalarEnergyTransport.energy_density_eq
        (originCube d k) (dataY.onCube (originCube d k)) u0.grad]
    funext x
    rw [hgrad x]
  rw [Homogenization.Book.Ch03.localizedCoeffEnergyValue_eq_volumeAverage_coefficientEnergyDensity
    V (dataY.toTriadicCoeffFamily.coeffOn (originCube d k)) u0, hdens]
  exact (Homogenization.Book.Ch01.volumeAverage_translateSet_eq_comp_addRight y V
    (fun x => a x * vecNormSq (gradU x))).symm

/-- The physical energy on one scale-`k-2` truncated cell is read from the translated projected
Caccioppoli core with the dimension-only loss `81^d`, for an arbitrary scalar family. -/
theorem aux_inputs_det_projected_cell_readout {d : ℕ} [NeZero d] {a : Vec d → ℝ}
    {m k : ℤ} {q : Vec d} (hq : q ∈ cube d m) (hkm : k ≤ m)
    (u : H1Function (openCubeSet (originCube d m)))
    (u0 : H1Function (openCubeSet (originCube d k)))
    (dataC : ScalarTriadicCoeffData
      (fun p => a (p + Section6ExcessDecay.wellPlacedCentre q m k)))
    (hu0 : ∀ x, u0.grad x = u.grad (x + Section6ExcessDecay.wellPlacedCentre q m k)) :
    normalizedSetAverage (truncatedCube d m (k - 2) q)
        (fun x => a x * vecNormSq (u.grad x)) ≤
      (81 : ℝ) ^ d * localizedCoeffEnergyValue
        (caccioppoliCoreSet (originCube d k)
          (q - Section6ExcessDecay.wellPlacedCentre q m k))
        (dataC.toTriadicCoeffFamily.coeffOn (originCube d k)) u0 := by
  let c := Section6ExcessDecay.wellPlacedCentre q m k
  let core := caccioppoliCoreSet (originCube d k) (q - c)
  let S := truncatedCube d m (k - 2) q
  let T := translateSet c core
  let f : Vec d → ℝ := fun x => a x * vecNormSq (u.grad x)
  have hcoreSub : core ⊆ openCubeSet (originCube d k) := fun _ h => h.1
  have hST : S ⊆ T := by
    simpa only [S, T, core, c] using
      (truncatedCube_subset_translate_caccioppoliCore q hkm le_rfl)
  have hSreal : 0 < (volume S).toReal := by
    simpa only [S] using
      Section6ExcessDecay.volume_toReal_truncatedCube_pos q hq
        (by omega : k - 2 - 1 ≤ m)
  have hSpair := ENNReal.toReal_ne_zero.mp hSreal.ne'
  have hSpos : 0 < volume S := pos_iff_ne_zero.mpr hSpair.1
  have hTtop : volume T < ∞ := by
    change volume (translateSet c core) < ∞
    rw [volume_translateSet_eq]
    exact lt_of_le_of_lt (measure_mono (fun _ h => h.1))
      (isOpenBoundedConvexDomain_openCubeSet (originCube d k)).volume_lt_top
  have hf : ∀ᵐ x ∂(volume.restrict T), 0 ≤ f x := by
    have hae := aux_inputs_det_projected_cell_ae_nonneg (originCube d k) c dataC core hcoreSub
    filter_upwards [hae] with x hx
    exact mul_nonneg hx (vecNormSq_nonneg _)
  have hint : IntegrableOn f T volume := by
    have hbase := SubdiffusiveProcess.ScalarEnergyTransport.integrable_energy
      (originCube d k) (dataC.onCube (originCube d k)) u0
    have hshift : IntegrableOn (fun z => f (z + c)) (openCubeSet (originCube d k)) volume := by
      have h2 : IntegrableOn (fun x => a (x + c) * vecNormSq (u0.grad x))
          (openCubeSet (originCube d k)) volume := by
        change MeasureTheory.Integrable _ (volume.restrict (openCubeSet (originCube d k)))
        rw [← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet (originCube d k)]
        exact hbase
      refine h2.congr_fun (fun x _ => ?_) (measurableSet_openCubeSet _)
      simp only [f, hu0 x]
      rfl
    have hmp := (measurePreserving_add_right (volume : Measure (Vec d)) c).integrableOn_image
      (measurableEmbedding_addRight c) (f := f) (s := openCubeSet (originCube d k))
    rw [image_addRight_eq_translateSet] at hmp
    have hTsub : T ⊆ translateSet c (openCubeSet (originCube d k)) := by
      intro x hx
      have hx' : x ∈ translateSet c core := hx
      rw [← image_addRight_eq_translateSet] at hx' ⊢
      exact Set.image_mono hcoreSub hx'
    exact (hmp.mpr hshift).mono_set hTsub
  have havg := aux_inputs_det_projected_cell_le_mul_ae hST hSpos hTtop hf hint
    (by simpa only [S, T, core, c] using
      volume_translate_core_le_eightyOne_pow_mul_truncatedCube hq hkm)
  rw [aux_inputs_det_projected_cell_frame a k c dataC core u0 u.grad hu0]
  simpa only [S, T, core, c, f] using havg

theorem inputs_det_projected_cell
    (d : ℕ) [NeZero d] :
    (∃ C : ℝ, 0 < C ∧
      ∀ (a : Vec d → ℝ)
        (m : ℕ) (k : ℤ) (q : Vec d) (sOrder : FractionalOrder)
        (u : H1Function (openCubeSet (originCube d (m : ℤ))))
        (g : Vec d → Vec d) (c0 : ℝ),
        IsDivFormWeakSolutionOn (a)
            (cube d (m : ℤ)) u g →
        Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d (m : ℤ)) sOrder FiniteLpExponent.two g →
        sOrder.1 ≤ 1 / 4 → k ≤ (m : ℤ) → q ∈ cube d (m : ℤ) →
        openCubeAtScale
            (q - Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k) (k - 1) ⊆
          openCubeSet (originCube d k) →
        ∀ dataC : ScalarTriadicCoeffData (fun p => a (p +
          Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)),
        ∃ g0 : Vec d → Vec d,
          ∃ u0 : H1Function (openCubeSet (originCube d k)),
            (∀ x, g0 x = g (x +
              Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            Ch03.ABK26.MemCubeEuclideanFullWsp (originCube d k) sOrder
              FiniteLpExponent.two (fun x => g (x +
                Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            (∀ x, u0.toFun x = u.toFun (x +
              Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k)) ∧
            IsForcedEquation (originCube d k)
                (dataC.toTriadicCoeffFamily)
                u0 (fun x => -g0 x) ∧
            ForceBesovRegularity (originCube d k) sOrder.1 (fun x => -g0 x) ∧
            normalizedSetAverage (truncatedCube d (m : ℤ) (k - 2) q)
                (fun x => a x *
                  vecNormSq (u.grad x)) ≤
              (81 : ℝ) ^ d *
                (caccioppoliWithRHSPrefactor C (originCube d k)
                    (dataC.toTriadicCoeffFamily)
                    (1 / 2) (sOrder.1 / 2) *
                  (Ch02.lambdaS (originCube d k) (sOrder.1 / 2)
                      (dataC.toTriadicCoeffFamily) *
                    Real.rpow (3 : ℝ) (-2 * (((originCube d k).scale : ℤ) : ℝ)) *
                    normalizedL2SqOnSet (openCubeSet (originCube d k))
                      (fun y => u0.toFun y - c0) +
                  Real.rpow (sOrder.1 / 2) (-11 : ℝ) *
                    Real.rpow
                      (Ch02.lambdaS (originCube d k) (sOrder.1 / 2)
                        (dataC.toTriadicCoeffFamily))
                      (-1 : ℝ) *
                    scaleNormalizedPositiveBesovVectorSeminormTwo
                      (originCube d k) sOrder.1 (fun x => -g0 x) ^ 2))) := by
  obtain ⟨C, hC, hcacc⟩ := exists_interior_caccioppoli_quarter_subConst d
  refine ⟨C, hC, ?_⟩
  intro a m k q sOrder u g c0 hweak hg hs4 hkm hq hpatch dataC
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre q (m : ℤ) k
  let Q : Homogenization.TriadicCube d := originCube d k
  have hD : translatedCube d k c = translateSet c (openCubeSet Q) :=
    by rw [translatedCube, cube, Section6SchauderDatum.image_add_eq_translateSet]
  have hsubt : translateSet c (openCubeSet Q) ⊆ openCubeSet (originCube d (m : ℤ)) := by
    rw [← hD]
    exact Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_cube q hkm
  have hDopen : IsOpen (translateSet c (openCubeSet Q)) :=
    ((isOpenBoundedConvexDomain_openCubeSet Q).translateSet c).isOpen
  let uDt : H1Function (translateSet c (openCubeSet Q)) := u.restrict hDopen hsubt
  have huDt : IsDivFormWeakSolutionOn a (translateSet c (openCubeSet Q)) uDt g :=
    isDivFormWeakSolutionOn_restrict
      (isOpenBoundedConvexDomain_openCubeSet (originCube d (m : ℤ))).isOpen
      hDopen hsubt hweak
  let g0 : Vec d → Vec d := fun x => g (x + c)
  have hg0 : Ch03.ABK26.MemCubeEuclideanFullWsp Q sOrder FiniteLpExponent.two g0 :=
    memCubeEuclideanFullWsp_translate_of_subset Q (originCube d (m : ℤ)) c sOrder
      FiniteLpExponent.two g hsubt hg
  let u0 : H1Function (openCubeSet Q) := H1Function.untranslate c uDt
  have hu0val : ∀ x, u0.toFun x = u.toFun (x + c) := fun x => rfl
  have hu0grad : ∀ x, u0.grad x = u.grad (x + c) := by
    intro x
    rw [H1Function.untranslate_grad]
    rfl
  have hABK : Ch03.ABK26.IsForcedEquation Q (dataC.toTriadicCoeffFamily.coeffOn Q) u0 g0 :=
    SubdiffusiveProcess.InteriorComparisonEngine.aux_icc_isForcedEquation_scalarData_untranslate
      Q c dataC huDt
  have heq : IsForcedEquation Q dataC.toTriadicCoeffFamily u0 (fun x => -g0 x) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.publicIsForcedEquation_neg_of_ABK26 hABK
  have hreg : ForceBesovRegularity Q sOrder.1 (fun x => -g0 x) :=
    _root_.SubdiffusiveProcess.CoarseGrainingVocab.Section6HolderBelowCutoff.SmoothDualComparison.aux_gen_forceBesovRegularity_neg_of_interiorFull
      (Q := Q) (s := sOrder) (f := g0) hg0
  have hreg' : ForceBesovRegularity Q (2 * (sOrder.1 / 2)) (fun x => -g0 x) := by
    rw [show 2 * (sOrder.1 / 2) = sOrder.1 by ring]
    exact hreg
  have hmain := hcacc u0 c0 heq (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (by linarith only [sOrder.2.1] : 0 < sOrder.1 / 2)
    (by linarith only [hs4] : sOrder.1 / 2 ≤ 1 / 4)
    (by linarith only [hs4] : (1 : ℝ) / 2 + sOrder.1 / 2 < 1)
    hpatch hreg'
  have hread := aux_inputs_det_projected_cell_readout (a := a) hq hkm u u0 dataC hu0grad
  have hfactor : (0 : ℝ) ≤ (81 : ℝ) ^ d := by positivity
  have hfinal := hread.trans (mul_le_mul_of_nonneg_left hmain hfactor)
  refine ⟨g0, u0, fun x => rfl, hg0, hu0val, heq, hreg, ?_⟩
  simpa only [c, Q, show 2 * (sOrder.1 / 2) = sOrder.1 by ring] using hfinal

end SubdiffusiveProcess.Paper
