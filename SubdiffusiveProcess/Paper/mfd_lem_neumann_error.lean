import SubdiffusiveProcess.Paper.neumann_centered_response
import SubdiffusiveProcess.Paper.lem_coercivity_uniform
import SubdiffusiveProcess.Paper.prop_16
import SubdiffusiveProcess.Probability.ResponseMomentBound
import SubdiffusiveProcess.Paper.lem_neumann_error
import SubdiffusiveProcess.Paper.lem_neumann_error_load_bound
import SubdiffusiveProcess.Paper.in_responses

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- The centered-response constant is uniform over the affine direction and Poincaré witness. -/
theorem aux_mfd_lem_neumann_error_centered_uniform :
    ∀ (d : ℕ) (hd : 2 ≤ d)
      [MeasurableSpace C(SpatialCoordinates d, ℝ)]
      [BorelSpace C(SpatialCoordinates d, ℝ)]
      (I : Paper.in_J d) (Cresp : ℝ) (hCresp : 0 < Cresp)
      (p : ℝ) (hp : 2 ≤ p),
      let Q := unitNeumannCube d
      ∃ C : ℝ, 0 < C ∧
      ∀ (pvec : Fin d → ℝ)
      (hpvec : (∑ i : Fin d, (pvec i) ^ 2) = 1)
      (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
          Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖),
      let S := meanZeroResponseSpace hP
      let L : S.space →L[ℝ] ℝ :=
        (affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph Q))
        ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
          (0 < M.delta ∧ M.delta ≤ 1) →
          ∀ (Rinput : Paper.in_responses d M),
            Rinput.C ≤ Cresp →
            4 * p ≤ Cresp⁻¹ * (M.delta ^ 2)⁻¹ * |Real.log M.delta|⁻¹ →
            ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
              InfraredCharacterization M H →
              ∀ (relab : ℕ → BilateralField d → BilateralField d),
                (∀ N, MeasurePreserving (relab N)
                  (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure) →
                (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
                  ∀ i : ℤ, ∀ x : SpatialCoordinates d,
                    relab N omega i x = omega (i - (N : ℤ))
                      ((3 : ℝ) ^ (-(N : ℤ)) • x)) →
              let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
              let aN : ℕ → BilateralField d → PositiveCoefficient Q := fun N om =>
                cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos
              let aN0 : ℕ → BilateralField d → PositiveCoefficient Q := fun N om =>
                cutoffPositiveCoefficient M (fun _ => 0) om N
                  (fun _ => (1 / 2 : ℝ)) one_pos
              let yN : ℕ → BilateralField d → ℝ := fun N om =>
                inverseResponse S (aN N om) L
              let yN0 : ℕ → BilateralField d → ℝ := fun N om =>
                inverseResponse S (aN0 N om) L
              ∀ N : ℕ,
                (∀ᵐ om ∂P, ∀ Sbound : ℝ, 0 ≤ Sbound →
                  (∀ x ∈ (Q : Set (SpatialCoordinates d)), |H om x| ≤ Sbound) →
                  |yN N om - yN0 N om| ≤
                    (Real.exp Sbound - 1) * yN0 N om) ∧
                (MemLp (yN N) (ENNReal.ofReal (2 * p)) P ∧
                  MemLp (yN0 N) (ENNReal.ofReal (2 * p)) P) ∧
                eLpNorm (yN0 N - (fun _ => (1 : ℝ))) (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal (C * M.delta) ∧
                  eLpNorm (yN N - yN0 N) (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal (C * M.delta) ∧
                  eLpNorm
                      (fun om => yN N om - ∫ omega, yN N omega ∂P)
                      (ENNReal.ofReal p) P ≤
                    ENNReal.ofReal (C * M.delta) := by
  intro d hd _ _ I Cresp hCresp p hp Q
  obtain ⟨Cdev, hCdev, hdev⟩ := I.deviation_by_J
  obtain ⟨Cinfra, hCinfra, hExpAll⟩ :=
    exists_uniform_compactExponentialMoment_of_infraredCharacterization hd
  have hQK : (Q : Set (SpatialCoordinates d)) ⊆
      (((closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) : Compacts (SpatialCoordinates d)) : Set (SpatialCoordinates d)) :=
    centeredCube_subset_closedCube _ one_pos
  have hconst0 : 0 ≤ aux_neumann_centered_response_const Cdev Cresp p
      (Cinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) :=
    aux_neumann_centered_response_const_nonneg _ _ _ _ hCresp.le hp
  refine ⟨4 * aux_neumann_centered_response_const Cdev Cresp p
      (Cinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) + 1,
    by linarith, ?_⟩
  intro pvec hpvec hP S L M hM Rinput hRC hscale H hH relab hrelabMP hrelabId P aN aN0 yN yN0 N
  have hdelta0 : 0 < M.delta := hM.1
  have hdelta1 : M.delta ≤ 1 := hM.2
  obtain ⟨hDmem, hDnorm⟩ :=
    aux_neumann_centered_response_defect_moments M Rinput Cresp p hCresp hRC hscale
      relab hrelabMP N
  have hdev_ae : ∀ᵐ om ∂P, (yN0 N om - 1) ^ 2 ≤
      Cdev * (fun om => Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2) (relab N om)) om * (1 + (fun om => Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2) (relab N om)) om) := by
    filter_upwards [hrelabId] with om hom
    exact aux_neumann_centered_response_dev M Rinput pvec hpvec hP Cdev hdev N om
      (relab N om)
      (fun x => aux_neumann_centered_response_reindex N om (relab N om) x
        (fun i y => hom N i y))
  have hY0meas : Measurable (yN0 N) :=
    aux_neumann_centered_response_meas M (fun _ => 0) measurable_const S L N
  have hYmeas : Measurable (yN N) :=
    aux_neumann_centered_response_meas M H hH.1 S L N
  have hXmeas : Measurable (fun om => ‖(H om).restrict (((closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) : Compacts (SpatialCoordinates d)) : Set (SpatialCoordinates d))‖) :=
    (continuous_norm.comp (ContinuousMap.continuous_restrict
      (((closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) : Compacts (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)))).measurable.comp hH.1
  have hXbound : ∀ om, ∀ x ∈ (Q : Set (SpatialCoordinates d)),
      |H om x| ≤ (fun om => ‖(H om).restrict (((closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) : Compacts (SpatialCoordinates d)) : Set (SpatialCoordinates d))‖) om := by
    intro om x hx
    exact ContinuousMap.norm_coe_le_norm
      ((H om).restrict (((closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) : Compacts (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))) ⟨x, hQK hx⟩
  have hPoint : ∀ᵐ om ∂P, ∀ Sbound : ℝ, 0 ≤ Sbound →
      (∀ x ∈ (Q : Set (SpatialCoordinates d)), |H om x| ≤ Sbound) →
      |yN N om - yN0 N om| ≤ (Real.exp Sbound - 1) * yN0 N om := by
    filter_upwards [] with om
    intro Sbound _ hbound
    exact aux_neumann_centered_response_compare M H S L om N Sbound hbound
  have hcmp : ∀ᵐ om ∂P,
      |yN N om - yN0 N om| ≤ (Real.exp ((fun om => ‖(H om).restrict (((closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) : Compacts (SpatialCoordinates d)) : Set (SpatialCoordinates d))‖) om) - 1) * yN0 N om := by
    filter_upwards [hPoint] with om hom
    exact hom _ (norm_nonneg _) (hXbound om)
  obtain ⟨hmem, h3, h4, h5⟩ :=
    aux_neumann_centered_response_lp P (yN0 N) (yN N) (fun om => Rinput.defect N (fun _ => (3 : ℝ) ^ N / 2) (relab N om)) (fun om => ‖(H om).restrict (((closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) : Compacts (SpatialCoordinates d)) : Set (SpatialCoordinates d))‖)
      hY0meas hYmeas (fun om => inverseResponse_nonneg S (aN0 N om) L) hXmeas
      (fun om => norm_nonneg _)
      (fun om => Rinput.defect_nonneg N (fun _ => (3 : ℝ) ^ N / 2) (relab N om))
      p Cresp Cdev (Cinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) M.delta hp hCresp hCdev
      (hCinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) hdelta0 hdelta1 hdev_ae hDmem hDnorm
      (fun lam hlam => hExpAll M H hH (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) lam hlam) hcmp
  have hmono1 : aux_neumann_centered_response_const Cdev Cresp p
        (Cinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) * M.delta ≤
      (4 * aux_neumann_centered_response_const Cdev Cresp p
        (Cinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) + 1) * M.delta := by
    nlinarith [hconst0, hdelta0.le]
  have hmono2 : 4 * aux_neumann_centered_response_const Cdev Cresp p
        (Cinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) * M.delta ≤
      (4 * aux_neumann_centered_response_const Cdev Cresp p
        (Cinfra (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)) + 1) * M.delta := by
    nlinarith [hconst0, hdelta0.le]
  exact ⟨hPoint, hmem, h3.trans (ENNReal.ofReal_mono hmono1),
    h4.trans (ENNReal.ofReal_mono hmono1), h5.trans (ENNReal.ofReal_mono hmono2)⟩


/-- The model, direction and mollifier uniform moment conclusion, with its premises derived. -/
theorem aux_mfd_lem_neumann_error_moments (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (Sfi : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (p : ℝ) (hp : 1 ≤ p) :
∀ Cresp : ℝ, 0 < Cresp →
    ∃ (delta0 Cerr Cunif : ℝ), 0 < delta0 ∧ 0 < Cerr ∧ 0 < Cunif ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M), Rm.C ≤ Cresp →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
    ∀ (rho : ℝ → ℝ), ContDiff ℝ ∞ rho → (∀ tau, 0 ≤ rho tau) →
        (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) → (∫ tau, rho tau) = 1 →
      ∀ (pvec : Fin d → ℝ), (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
          ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
            Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖),
      ∀ (eps : ℝ), 0 < eps → eps < 1 / 8 →
      ∀ (fL2 : ℕ → BilateralField d → DomainL2 (unitNeumannCube d)),
        (∀ N om, ((fL2 N om : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
            faceBump rho pvec eps)) →
      ∀ (N : ℕ),
      eLpNorm (fun om' =>
          inverseResponse (meanZeroResponseSpace hP)
              (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
              ((affineNeumannLoad pvec).comp
                (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) -
            inverseResponse (meanZeroResponseSpace hP)
              (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
              ((sobolevVolumeLoad (fL2 N om')).comp
                (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ)) ∧
      eLpNorm (fun om' =>
          inverseResponse (meanZeroResponseSpace hP)
            (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
            ((sobolevVolumeLoad (fL2 N om')).comp
                (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal Cunif := by
  intro Cresp hCresp
  have h4p : 1 ≤ 4 * p := by linarith only [hp]
  have h4p2 : 2 ≤ 4 * p := by linarith only [hp]
  obtain ⟨D, hD, B, hB, hcoercSupplier⟩ :=
    lem_coercivity_uniform d hd E P Sfi (fun _ : Fin d => (1 / 2 : ℝ))
      1 one_pos le_rfl
  obtain ⟨C, hC, hcentered⟩ :=
    aux_mfd_lem_neumann_error_centered_uniform d hd E Cresp hCresp (4 * p) h4p2
  obtain ⟨de, Ke, Cerr, Cunif, hde, -, hCerr, hCunif, herror⟩ :=
    lem_neumann_error d hd E P Sfi p hp (B (4 * p)) (2 * C + 1)
      (hB _ h4p).le (by positivity)
  refine ⟨min (min 1 (D (4 * p))) (min de (Cresp * (4 * (4 * p)))⁻¹),
    Cerr, Cunif, lt_min (lt_min one_pos (hD _ h4p))
      (lt_min hde (inv_pos.mpr (mul_pos hCresp (by linarith only [hp])))),
    hCerr, hCunif, ?_⟩
  intro M Rm hRC H hIH hδ rho hrho hrho0 hrhos hrhoi pvec hpvec hP eps heps heps8 fL2 hfL2 N
  have hδ1 : M.delta ≤ 1 := (le_min_iff.mp (le_min_iff.mp hδ).1).1
  have hδD : M.delta ≤ D (4 * p) := (le_min_iff.mp (le_min_iff.mp hδ).1).2
  have hδe : M.delta ≤ de := (le_min_iff.mp (le_min_iff.mp hδ).2).1
  have hδscale : M.delta ≤ (Cresp * (4 * (4 * p)))⁻¹ :=
    (le_min_iff.mp (le_min_iff.mp hδ).2).2
  have hscale := aux_lem_extension_cell_moment_response_admissible M Cresp (4 * (4 * p))
    hCresp (by linarith only [hp]) hδscale
  obtain ⟨Kraw, hKrawCoerc, hKrawMom⟩ := hcoercSupplier M Rm H hIH
  let Kcoerc : ℕ → BilateralField d → ℝ := fun n om => |Kraw n om|
  have hcoerc : ∀ n om, ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
      cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder v.val.1 ≤
        Kcoerc n om * sobolevCoefficientForm
          (cutoffPositiveCoefficient M H om n (fun _ => (1 / 2 : ℝ)) one_pos) v.val v.val := by
    intro n om v
    exact (((hKrawCoerc n om).2 v).2).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _)
        (sobolevCoefficientForm_nonneg _ _))
  have hKmom : ∀ n, MemLp (Kcoerc n) (ENNReal.ofReal (4 * p)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (Kcoerc n) (ENNReal.ofReal (4 * p)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (B (4 * p)) := by
    intro n
    obtain ⟨hm, hb⟩ := hKrawMom (4 * p) h4p hδD n
    refine ⟨?_, ?_⟩
    · simpa only [Real.norm_eq_abs] using hm.norm
    · change eLpNorm (fun om => |Kraw n om|) _ _ ≤ _
      simpa only [← Real.norm_eq_abs, eLpNorm_norm] using hb
  have hYmom : ∀ n, MemLp (fun om => inverseResponse (meanZeroResponseSpace hP)
        (cutoffPositiveCoefficient M H om n (fun _ => (1 / 2 : ℝ)) one_pos)
        ((affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))))
      (ENNReal.ofReal (4 * p)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => inverseResponse (meanZeroResponseSpace hP)
        (cutoffPositiveCoefficient M H om n (fun _ => (1 / 2 : ℝ)) one_pos)
        ((affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))))
      (ENNReal.ofReal (4 * p)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (2 * C + 1) := by
    intro n
    obtain ⟨-, ⟨hy, hy0⟩, h3, h4, -⟩ :=
      hcentered pvec hpvec hP M ⟨M.shellPrefix.delta_pos, hδ1⟩ Rm hRC hscale H hIH
        aux_prop_16_relab (aux_prop_16_relab_mp M)
        (Filter.Eventually.of_forall fun om n i x => aux_prop_16_relab_apply n om i x) n
    refine ⟨hy.mono_exponent (ENNReal.ofReal_le_ofReal (by linarith only [hp])), ?_⟩
    exact SubdiffusiveProcess.Probability.eLpNorm_le_of_two_centered_bounds (chaosSampleLaw M).toMeasure
      _ _ hy.aestronglyMeasurable hy0.aestronglyMeasurable (4 * p) C M.delta h4p hC.le hδ1 h3 h4
  exact (herror M Rm H hIH hδe rho hrho hrho0 hrhos hrhoi pvec hpvec hP Kcoerc hcoerc
    (fun n => (hKmom n).1) (fun n => (hKmom n).2)
    (fun n => (hYmom n).1) (fun n => (hYmom n).2) eps heps heps8 fL2 hfL2 N 0).2





theorem mfd_lem_neumann_error :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_S : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (p : ℝ), 1 ≤ p →
  -- `eq:mfd-7`: the deterministic load estimate, for every `v ∈ H¹(Q)` (mean-zero representative)
  (∃ Cload : ℝ, 0 < Cload ∧
    ∀ (rho : ℝ → ℝ), ContDiff ℝ ∞ rho → (∀ tau, 0 ≤ rho tau) →
        (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) → (∫ tau, rho tau) = 1 →
      ∀ (pvec : Fin d → ℝ), (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∀ (eps : ℝ), 0 < eps → eps < 1 / 8 →
      ∀ (fL2 : ℕ → BilateralField d → DomainL2 (unitNeumannCube d)),
        (∀ N om, ((fL2 N om : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
            faceBump rho pvec eps)) →
    ∀ (N : ℕ) (om : BilateralField d),
    ∀ z : meanZeroSobolevGraph (unitNeumannCube d),
      |(((((affineNeumannLoad pvec).comp
                (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d))))) -
        (((sobolevVolumeLoad (fL2 N om)).comp
                (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL))) z)| ≤
        Cload * eps ^ (1 / 4 : ℝ) *
          Real.sqrt (cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1
            one_pos threeQuarterOrder
            (z : SobolevData (unitNeumannCube d)).1)) ∧
  -- `eq:mfd-8`: `E_N^Q(v_N - v_{N,ε}) ≤ C K_N ε^{1/2}` for ANY coercivity constant `K_N` of `eq:mfd-1`
  (∃ K : ℝ, 0 < K ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H →
    ∀ (rho : ℝ → ℝ), ContDiff ℝ ∞ rho → (∀ tau, 0 ≤ rho tau) →
        (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) → (∫ tau, rho tau) = 1 →
      ∀ (pvec : Fin d → ℝ), (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
          ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
            Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖),
      ∀ (Kcoerc : ℕ → BilateralField d → ℝ),
      (∀ N om, ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
        cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
            (v : SobolevData (unitNeumannCube d)).1 ≤
          Kcoerc N om *
            sobolevCoefficientForm
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
              (v : SobolevData (unitNeumannCube d))
              (v : SobolevData (unitNeumannCube d))) →
      ∀ (eps : ℝ), 0 < eps → eps < 1 / 8 →
      ∀ (fL2 : ℕ → BilateralField d → DomainL2 (unitNeumannCube d)),
        (∀ N om, ((fL2 N om : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
            faceBump rho pvec eps)) →
      ∀ (N : ℕ) (om : BilateralField d),
      responseForm (meanZeroResponseSpace hP)
            (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
            ((responseSolution (meanZeroResponseSpace hP)
                (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                ((affineNeumannLoad pvec).comp
                (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d))))) -
              (responseSolution (meanZeroResponseSpace hP)
                (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                ((sobolevVolumeLoad (fL2 N om)).comp
                (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL)))
            ((responseSolution (meanZeroResponseSpace hP)
                (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                ((affineNeumannLoad pvec).comp
                (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d))))) -
              (responseSolution (meanZeroResponseSpace hP)
                (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
                ((sobolevVolumeLoad (fL2 N om)).comp
                (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL))) ≤
        K * Kcoerc N om * eps ^ (1 / 2 : ℝ)) ∧
  -- `eq:mfd-9`: for the prescribed moment order `p`, at sufficiently small disorder (NO moment premises)
  (∀ Cresp : ℝ, 0 < Cresp →
    ∃ (delta0 Cerr Cunif : ℝ), 0 < delta0 ∧ 0 < Cerr ∧ 0 < Cunif ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M), Rm.C ≤ Cresp →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
    ∀ (rho : ℝ → ℝ), ContDiff ℝ ∞ rho → (∀ tau, 0 ≤ rho tau) →
        (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) → (∫ tau, rho tau) = 1 →
      ∀ (pvec : Fin d → ℝ), (∑ i : Fin d, (pvec i) ^ 2) = 1 →
    ∀ (hP : ∃ Kp : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
          ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
            Kp * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖),
      ∀ (eps : ℝ), 0 < eps → eps < 1 / 8 →
      ∀ (fL2 : ℕ → BilateralField d → DomainL2 (unitNeumannCube d)),
        (∀ N om, ((fL2 N om : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
            faceBump rho pvec eps)) →
      ∀ (N : ℕ),
      eLpNorm (fun om' =>
          inverseResponse (meanZeroResponseSpace hP)
              (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
              ((affineNeumannLoad pvec).comp
                (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) -
            inverseResponse (meanZeroResponseSpace hP)
              (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
              ((sobolevVolumeLoad (fL2 N om')).comp
                (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cerr * eps ^ (1 / 4 : ℝ)) ∧
      eLpNorm (fun om' =>
          inverseResponse (meanZeroResponseSpace hP)
            (cutoffPositiveCoefficient M H om' N (fun _ => (1 / 2 : ℝ)) one_pos)
            ((sobolevVolumeLoad (fL2 N om')).comp
                (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL))
          (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal Cunif) := by
  intro d hd _ _ E P Sfi p hp
  obtain ⟨Cload, hCload, hload⟩ := lem_neumann_error_load_bound d hd Sfi
  refine ⟨⟨Cload, hCload, hload⟩, ⟨Cload ^ 2, sq_pos_of_pos hCload, ?_⟩,
    aux_mfd_lem_neumann_error_moments d hd E P Sfi p hp⟩
  intro M Rm H hIH rho hrho hrho0 hrhos hrhoi pvec hpvec hP Kcoerc hcoerc eps heps heps8 fL2 hfL2 N om
  exact lem_neumann_error_energy d hd hP
    (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
    (Kcoerc N om) Cload eps
    ((affineNeumannLoad pvec).comp (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d))))
    ((sobolevVolumeLoad (fL2 N om)).comp (meanZeroSobolevGraph (unitNeumannCube d)).subtypeL)
    hCload heps heps8 (hcoerc N om)
    (hload rho hrho hrho0 hrhos hrhoi pvec hpvec eps heps heps8 fL2 hfL2 N om)

end Paper
