import SubdiffusiveProcess.Paper.lane4_smoothed_load_properties
import SubdiffusiveProcess.Paper.lem_load

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper



lemma aux_g9_neumann_facebump_bridge_solves_neumann
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP0 : ∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z r hr)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (f : DomainL2 (centeredCube z r hr)) (F : SpatialCoordinates d → ℝ) (K : ℝ)
    (hFm : Measurable F) (hFb : ∀ x, |F x| ≤ K)
    (hFeq : F =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      (f : SpatialCoordinates d → ℝ))
    (hFmean : (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x) = 0) :
    SolvesNeumann a F (responseSolution (meanZeroResponseSpace hP0) a
      ((sobolevVolumeLoad f).comp (meanZeroResponseSpace hP0).space.subtypeL)) := by
  let S := meanZeroResponseSpace hP0
  let L : S.space →L[ℝ] ℝ := (sobolevVolumeLoad f).comp S.space.subtypeL
  let us : S.space := responseSolution S a L
  intro ψ
  have hvol : 0 < volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [Measure.real, centeredCube_volume, ENNReal.toReal_ofReal (by positivity)]
    positivity
  set c : ℝ := (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))⁻¹ *
    ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      (ψ : SobolevData (centeredCube z r hr)).1 x with hc
  let k : SobolevData (centeredCube z r hr) :=
    (domainConstantL2 (Ω := centeredCube z r hr) c,
      fun _ => (0 : DomainL2 (centeredCube z r hr)))
  have hk_coe : ((((ψ : SobolevData (centeredCube z r hr)) - k).1 :
      DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        fun x => (ψ : SobolevData (centeredCube z r hr)).1 x - c := by
    filter_upwards [Lp.coeFn_sub ((ψ : SobolevData (centeredCube z r hr)).1)
      (domainConstantL2 (Ω := centeredCube z r hr) c),
      domainConstantL2_coeFn (Ω := centeredCube z r hr) c] with x h1 h2
    change ((((ψ : SobolevData (centeredCube z r hr)).1 -
      domainConstantL2 (Ω := centeredCube z r hr) c) : DomainL2 (centeredCube z r hr)) :
        SpatialCoordinates d → ℝ) x = _
    rw [h1, Pi.sub_apply, h2]
  have hψint : Integrable (fun x => ((ψ : SobolevData (centeredCube z r hr)).1 :
      SpatialCoordinates d → ℝ) x)
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    have h := (Lp.memLp ((ψ : SobolevData (centeredCube z r hr)).1)).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simpa using h
  have hmem : (ψ : SobolevData (centeredCube z r hr)) - k ∈ S.space := by
    change _ ∈ meanZeroSobolevGraph (centeredCube z r hr)
    rw [mem_meanZeroSobolevGraph_iff]
    refine ⟨Submodule.sub_mem _ ψ.property (constantSobolevData_mem_weak c), ?_⟩
    rw [integral_congr_ae hk_coe, integral_sub hψint (integrable_const c),
      MeasureTheory.setIntegral_const, hc, smul_eq_mul]
    field_simp
    ring
  let ψ0 : S.space := ⟨(ψ : SobolevData (centeredCube z r hr)) - k, hmem⟩
  have hkform : sobolevCoefficientForm a (us : SobolevData (centeredCube z r hr)) k = 0 := by
    have hgk : sobolevGradient k = 0 := by
      have h0 : (fun _ : Fin d => (0 : DomainL2 (centeredCube z r hr))) = 0 := rfl
      simp [k, sobolevGradient, h0]
    change (weightedGradientForm a.val) (sobolevGradient (us : SobolevData _))
      (sobolevGradient k) = 0
    rw [hgk, map_zero]
  have hspec : sobolevCoefficientForm a (us : SobolevData (centeredCube z r hr))
      ((ψ : SobolevData (centeredCube z r hr)) - k) =
      sobolevVolumeLoad f ((ψ : SobolevData (centeredCube z r hr)) - k) :=
    responseSolution_spec S a L ψ0
  have hsplit : (ψ : SobolevData (centeredCube z r hr)) =
      ((ψ : SobolevData (centeredCube z r hr)) - k) + k := (sub_add_cancel _ _).symm
  have hlhs : sobolevCoefficientForm a (us : SobolevData (centeredCube z r hr))
      (ψ : SobolevData (centeredCube z r hr)) =
      sobolevVolumeLoad f ((ψ : SobolevData (centeredCube z r hr)) - k) := by
    conv_lhs => rw [hsplit]
    rw [map_add, hkform, add_zero, hspec]
  change sobolevCoefficientForm a (us : SobolevData (centeredCube z r hr))
    (ψ : SobolevData (centeredCube z r hr)) = _
  rw [hlhs, sobolevVolumeLoad_apply]
  have hFint : Integrable (fun x => F x * ((ψ : SobolevData (centeredCube z r hr)).1 :
      SpatialCoordinates d → ℝ) x)
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    hψint.bdd_mul hFm.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hFb x)
  have hFint1 : Integrable F
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    have h := (integrable_const (1 : ℝ)).bdd_mul hFm.aestronglyMeasurable
      (ae_of_all (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))
        fun x => by rw [Real.norm_eq_abs]; exact hFb x)
    simpa using h
  calc (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        f x * (((ψ : SobolevData (centeredCube z r hr)) - k).1 :
          DomainL2 (centeredCube z r hr)) x)
      = ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          F x * ((ψ : SobolevData (centeredCube z r hr)).1 x) - c * F x := by
        apply integral_congr_ae
        filter_upwards [hFeq, hk_coe] with x h1 h2
        rw [h2, ← h1]
        ring
    _ = ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          F x * (ψ : SobolevData (centeredCube z r hr)).1 x := by
        rw [integral_sub hFint (hFint1.const_mul c), integral_const_mul, hFmean, mul_zero,
          sub_zero]



lemma aux_g9_neumann_facebump_bridge_faceBump_mean {d : ℕ} (rho : ℝ → ℝ)
    (hrho : Continuous rho) (Mρ : ℝ) (hM : ∀ tau, |rho tau| ≤ Mρ) (p : Fin d → ℝ)
    (eps : ℝ) :
    (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), faceBump rho p eps x) = 0 := by
  have hfin : IsFiniteMeasure (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
    inferInstance
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ → ℝ, A = fun t => eps⁻¹ * rho ((1 - t) / eps) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ → ℝ, B = fun t => eps⁻¹ * rho (t / eps) := ⟨_, rfl⟩
  have hAcont : Continuous A := by
    rw [hAdef]
    exact continuous_const.mul (hrho.comp ((continuous_const.sub continuous_id).div_const _))
  have hBcont : Continuous B := by
    rw [hBdef]
    exact continuous_const.mul (hrho.comp (continuous_id.div_const _))
  have hbdd : ∀ (g : ℝ → ℝ), (∀ t, |g t| ≤ Mρ * |eps⁻¹|) → Continuous g → ∀ i : Fin d,
      Integrable (fun x : SpatialCoordinates d => g (x i))
        (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) := by
    intro g hg hgc i
    refine Integrable.of_bound (C := Mρ * |eps⁻¹|)
      ((hgc.comp (continuous_apply i)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hg (x i)
  have hA : ∀ t, |A t| ≤ Mρ * |eps⁻¹| := fun t => by
    simp only [hAdef, abs_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  have hB : ∀ t, |B t| ≤ Mρ * |eps⁻¹| := fun t => by
    simp only [hBdef, abs_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  have hrefl : (∫ t in Set.Ioo (0 : ℝ) 1, A t) = ∫ t in Set.Ioo (0 : ℝ) 1, B t := by
    rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]
    have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1) B 1
    simp only [sub_zero, sub_self] at this
    rw [← this, hAdef, hBdef]
  have hsum : (fun x : SpatialCoordinates d => faceBump rho p eps x) =
      fun x => ∑ i : Fin d, (p i * A (x i) - p i * B (x i)) := by
    funext x
    unfold faceBump
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hAdef, hBdef]
    ring
  rw [hsum, integral_finset_sum (s := Finset.univ)
    (f := fun i (x : SpatialCoordinates d) => p i * A (x i) - p i * B (x i)) (fun i _ =>
    ((hbdd A hA hAcont i).const_mul (p i)).sub ((hbdd B hB hBcont i).const_mul (p i)))]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_sub ((hbdd A hA hAcont i).const_mul (p i)) ((hbdd B hB hBcont i).const_mul (p i)),
    integral_const_mul (p i) (fun x : SpatialCoordinates d => A (x i)),
    integral_const_mul (p i) (fun x : SpatialCoordinates d => B (x i)),
    aux_lem_load_integral_coord i A, aux_lem_load_integral_coord i B, hrefl, sub_self]

/-- Bridges a face-bump load's `SolvesNeumann` witness to its `responseSolution`, for the
SPECIFIC `(fL2, rho, pvec)` shape `lem_neumann_15` uses: given `fL2 eps =ᵐ faceBump rho pvec
eps`, produces `SolvesNeumann a (faceBump rho pvec eps) (responseSolution S a
((sobolevVolumeLoad (fL2 eps)).comp S.space.subtypeL))` directly at `S := meanZeroResponseSpace
hPn` on `unitNeumannCube d` -- exactly what is needed to instantiate a growth-block-style
`∀ v, SolvesNeumann ... v → ...` bound at `lem_neumann_15`'s own `ueps`. Purely deterministic
PDE-solution identification, from `aux_prop_as_response_bank_cauchy_solves_neumann` (already
proven) plus the face-bump amplitude/continuity/mean-zero facts. -/
theorem g9_neumann_facebump_bridge {d : ℕ}
    (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho) (hrho0 : ∀ v : ℝ, 0 ≤ rho v)
    (hrhos : ∀ v : ℝ, v ∉ Set.Ioo (1 : ℝ) 2 → rho v = 0) (hrhoi : (∫ v, rho v) = 1)
    (pvec : Fin d → ℝ)
    (hPn : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
        ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
          K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖)
    (a : PositiveCoefficient (unitNeumannCube d))
    (eps : ℝ) (heps : 0 < eps) (heps8 : eps < 1 / 8)
    (fL2 : DomainL2 (unitNeumannCube d))
    (hfL2eq : (fL2 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
      faceBump rho pvec eps) :
    SolvesNeumann a (faceBump rho pvec eps)
      (responseSolution (meanZeroResponseSpace hPn) a
        ((sobolevVolumeLoad fL2).comp (meanZeroResponseSpace hPn).space.subtypeL)) := by
  obtain ⟨Mrho, hMrho⟩ := hrho.continuous.bounded_above_of_compact_support
    (HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2))
      (fun tau htau => hrhos tau (fun h => htau ⟨h.1.le, h.2.le⟩)))
  set Krho : ℝ := max Mrho 0 with hKrhodef
  have hKrho : ∀ tau : ℝ, |rho tau| ≤ Krho := by
    intro tau
    rw [← Real.norm_eq_abs]
    exact (hMrho tau).trans (le_max_left _ _)
  have hload := lane4_smoothed_load_properties d rho hrho hrhos Krho hKrho pvec eps heps heps8
  set Dr : ℝ := (∑ i : Fin d, |pvec i|) * (2 * Krho) with hDrdef
  have hFcont : Continuous (faceBump rho pvec eps) := by
    have hc := hload.1.continuous
    simpa only [faceBump, lane4_smoothed_neumann_load] using hc
  have hFb : ∀ x, |faceBump rho pvec eps x| ≤ Dr * eps⁻¹ := by
    intro x
    simpa only [faceBump, lane4_smoothed_neumann_load] using hload.2.1 x
  have hFmean : (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
      faceBump rho pvec eps x) = 0 :=
    aux_g9_neumann_facebump_bridge_faceBump_mean rho hrho.continuous Krho hKrho pvec eps
  exact aux_g9_neumann_facebump_bridge_solves_neumann (fun _ => (1 / 2 : ℝ)) 1 one_pos hPn a
    fL2 (faceBump rho pvec eps) (Dr * eps⁻¹) hFcont.measurable hFb hfL2eq.symm hFmean

end Paper
