module

public import SubdiffusiveProcess.Paper.Support.UniformResolventHolder
public import SubdiffusiveProcess.Paper.Support.UniformResolventCoercivity
public import SubdiffusiveProcess.Paper.prop_conc_form_cutoff_continuity
public import SubdiffusiveProcess.Paper.car_variational

@[expose] public section

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Topology Set SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_mfd_prop_uniform_resolvent_holder_family
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sf : SobolevFoundationalInput d hd) (t : ℝ) (ht : (d : ℝ) - 1 < t) (ht' : t < d)
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)), InfraredCharacterization M H →
        M.delta ≤ delta0 → ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∃ (Kh : ℕ → BilateralField d → ℝ) (Ch : ℝ), 0 ≤ Ch ∧
        (∀ N, Measurable (Kh N)) ∧ (∀ N omega, 0 ≤ Kh N omega) ∧
        (∀ N, MemLp (Kh N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (Kh N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Ch) ∧
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          ∀ F : SpatialCoordinates d → ℝ, Measurable F → ∀ MF : ℝ, 0 ≤ MF →
            (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), |F x| ≤ MF) →
          ∀ v : killedSobolevGraph (centeredCube z r hr),
            (∀ w : killedSobolevGraph (centeredCube z r hr),
              sobolevCoefficientForm (cutoffPositiveCoefficient M H omega N z hr) v.val w.val =
                ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), F x * w.val.1 x) →
            ∃ vc : C(SpatialCoordinates d, ℝ), (v.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc ∧
              (∀ x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)), vc x = 0) ∧
              ∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
                ∀ y ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)),
                  |vc x - vc y| ≤ Kh N omega * MF * dist x y ^ (1 / 2 : ℝ) := by
  obtain ⟨delta0, hdelta0, hregular⟩ := aux_mfd_prop_uniform_resolvent_holder_moments
    d hd E Pc X W Cp Sf t (1 / 2) 1 (fun _ => q) ht ht' (by norm_num) (by norm_num)
    (fun _ => hq)
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It H hH hM z r hr
  obtain ⟨K, Cb, hmem, hbound, -, hDir⟩ := hregular M Rm Sreg It H hH hM z r hr
  obtain ⟨Km, hKm, hKn, hKae, hKmom⟩ := aux_mfd_prop_uniform_resolvent_coercivity_modification
    (chaosSampleLaw M).toMeasure K (Cb 0) (ENNReal.ofReal q) (fun N => hmem 0 N)
    (fun N => hbound 0 N)
  let D := (Real.sqrt (d : ℝ)) ^ (1 / 2 : ℝ)
  have hD : 0 ≤ D := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  let Kh := fun N omega => D * Km N omega
  have hKh : ∀ N, MemLp (Kh N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure :=
    fun N => (hKmom N).1.const_mul D
  have hb : ∀ N, eLpNorm (Kh N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (D * max (Cb 0) 0) := by
    intro N
    change eLpNorm (D • Km N) (ENNReal.ofReal q) _ ≤ _
    rw [eLpNorm_const_smul]
    calc
      ‖D‖ₑ * eLpNorm (Km N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal D * ENNReal.ofReal (max (Cb 0) 0) := by
        rw [Real.enorm_eq_ofReal hD]
        exact mul_le_mul_right ((hKmom N).2.trans
          (ENNReal.ofReal_le_ofReal (le_max_left _ _))) _
      _ = _ := (ENNReal.ofReal_mul hD).symm
  refine ⟨Kh, D * max (Cb 0) 0, mul_nonneg hD (le_max_right _ _),
    fun N => measurable_const.mul (hKm N), fun N omega => mul_nonneg hD (hKn N omega),
    fun N => ⟨hKh N, hb N⟩, ?_⟩
  filter_upwards [hDir, ae_all_iff.mpr hKae] with omega hω hDom
  intro N F hF MF hMF hFb v hv
  let Q : Set (SpatialCoordinates d) := centeredCube z r hr
  let F0 := Q.indicator F
  have hF0 : Measurable F0 := hF.indicator (centeredCube z r hr).isOpen.measurableSet
  have hF0b : ∀ x, |F0 x| ≤ MF := by
    intro x
    by_cases hx : x ∈ Q
    · simpa only [F0, Set.indicator_of_mem hx] using hFb x hx
    · simp only [F0, Set.indicator_of_notMem hx, abs_zero]; exact hMF
  have hDreg : aux_prop_conc_form_cutoff_continuity_DirProp z r hr
      (cutoffPositiveCoefficient M H omega N z hr) (K N omega) :=
    fun F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol =>
      ((hω N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol).2)
  obtain ⟨vc, hvc, hae, hzero, hHol⟩ := aux_prop_conc_form_cutoff_continuity_killed_holder
    z r hr _ (K N omega) hDreg F0 hF0 MF hMF hF0b v (fun w => by
      rw [hv]
      apply setIntegral_congr_fun (centeredCube z r hr).isOpen.measurableSet
      intro x hx
      change F x * w.val.1 x = F0 x * w.val.1 x
      rw [show F0 x = F x from Set.indicator_of_mem hx F])
  refine ⟨⟨vc, hvc⟩, hae, hzero, ?_⟩
  intro x hx y hy
  have hE := aux_car_variational_hol_hcamp_euclid_le x y
  have hscale : (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ (1 / 2 : ℝ) ≤
      D * dist x y ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (Real.sqrt (d : ℝ) * dist x y) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (Real.sqrt_nonneg _) hE (by norm_num)
      _ = _ := Real.mul_rpow (Real.sqrt_nonneg _) dist_nonneg
  calc
    |vc x - vc y| ≤ (K N omega * MF) *
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ (1 / 2 : ℝ) := hHol x hx y hy
    _ ≤ (Km N omega * MF) * (D * dist x y ^ (1 / 2 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hDom N) hMF) hscale
        (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (mul_nonneg (hKn N omega) hMF)
    _ = Kh N omega * MF * dist x y ^ (1 / 2 : ℝ) := by dsimp [Kh]; ring

end SubdiffusiveProcess.Paper
