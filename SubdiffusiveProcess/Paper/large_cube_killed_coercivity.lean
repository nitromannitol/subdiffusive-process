module

public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.rem_bank_response_moments
public import SubdiffusiveProcess.Paper.lane4_coercivity_dilation
public import SubdiffusiveProcess.Paper.lane4_gagliardo_dilation_scaling
public import SubdiffusiveProcess.Paper.lane4_dilation_coefficient_transport
public import SubdiffusiveProcess.Sobolev.LocalEnergy
public import SubdiffusiveProcess.Lnorm.CoercivityNormalization

@[expose] public section

open MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace SubdiffusiveProcess.Paper

private theorem aux_large_cube_killed_coercivity_fractional_sqNorm_le_unit
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (hr1 : 1 ≤ r)
    (f : DomainL2 (centeredCube z r hr))
    (g : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (hfg : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      g x = f (cubeDilation z 0 r x)) :
    cubeFractionalSqNorm hd z r hr threeQuarterOrder f ≤
      cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder g := by
  have hsc := lane4_gagliardo_dilation_scaling d 1 hd z 0 r hr one_pos
    threeQuarterOrder (fun _ => f) (fun _ => g) (fun _ => hfg)
  obtain ⟨hsemi, hl2⟩ := hsc
  have hR : r ^ (-(2 * (threeQuarterOrder : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hr1 (by
      change -(2 * (3 / 4 : ℝ)) ≤ 0
      norm_num)
  have hreal := congrArg ENNReal.toReal hsemi
  simp only [ENNReal.toReal_pow, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hr.le _)] at hreal
  unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
  rw [hreal, hl2]
  exact add_le_add (mul_le_of_le_one_left (sq_nonneg _) hR) le_rfl

/-- Deterministic transfer of a killed-space fractional coercivity bound from the unit cube
to an expanding triadic cube. The coefficient comparison is the only random input. -/
private theorem aux_large_cube_killed_coercivity_fractional_transport
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (k : ℕ)
    (a : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ k) (by positivity)))
    (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
    (K F : ℝ) (hK : 0 ≤ K)
    (hb : ∀ w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder
        (w : SobolevData _).1 ≤ K * sobolevCoefficientForm b (w : SobolevData _) w)
    (hcoeff : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      b.val x ≤ F * a.val (cubeDilation z 0 ((3 : ℝ) ^ k) x)) :
    ∀ v : killedSobolevGraph
        (centeredCube z ((3 : ℝ) ^ k) (by positivity)),
      cubeFractionalSqNorm hd z ((3 : ℝ) ^ k) (by positivity) threeQuarterOrder
        (v : SobolevData _).1 ≤
      (K * F * (((3 : ℝ) ^ k) ^ ((d : ℝ) - 2))⁻¹) *
        sobolevCoefficientForm a (v : SobolevData _) v := by
  let r : ℝ := (3 : ℝ) ^ k
  have hr : 0 < r := by positivity
  have hr1 : 1 ≤ r := by
    dsimp [r]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
  obtain ⟨c, hc⟩ := lane4_dilation_coefficient_transport d z 0 r hr one_pos a
  intro v
  obtain ⟨w, hwval, hwgrad⟩ :=
    aux_lane4_coercivity_dilation_killed_pullback d z r hr one_pos v
  have hnorm := aux_large_cube_killed_coercivity_fractional_sqNorm_le_unit hd z r hr hr1
    (v : SobolevData (centeredCube z r hr)).1
    (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 hwval
  have henergy := aux_lane4_coercivity_dilation_energy_scaling d z r hr one_pos a c
    (v : SobolevData (centeredCube z r hr))
    (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) hc hwval hwgrad
  have hcoeff' : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      b.val x ≤ F * c.val x := by
    filter_upwards [hcoeff, hc] with x hx hcx
    have hmap : cubeDilation z 0 ((3 : ℝ) ^ k) x = cubeDilation z 0 r x := by rfl
    rw [hmap] at hx
    rw [hcx]
    exact hx
  have hcmp := weightedGradientForm_le_mul b c F hcoeff'
    (subspaceGradient (killedSobolevGraph
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) w)
  have hpow : (((3 : ℝ) ^ k) ^ ((d : ℝ) - 2)) ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < (3 : ℝ) ^ k) _).ne'
  calc
    cubeFractionalSqNorm hd z r hr threeQuarterOrder
        (v : SobolevData (centeredCube z r hr)).1 ≤
        cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 one_pos threeQuarterOrder
          (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1 := hnorm
    _ ≤ K * sobolevCoefficientForm b (w : SobolevData _) w := hb w
    _ ≤ K * (F * sobolevCoefficientForm c (w : SobolevData _) w) := by
      exact mul_le_mul_of_nonneg_left hcmp hK
    _ = (K * F * (((3 : ℝ) ^ k) ^ ((d : ℝ) - 2))⁻¹) *
        sobolevCoefficientForm a (v : SobolevData _) v := by
      rw [henergy]
      field_simp
      ring

private theorem aux_large_cube_killed_coercivity_seminorm_finite
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r)
    (hunit : ∀ w : killedSobolevGraph
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      cubeFractionalL2Seminorm hd 0 1 one_pos threeQuarterOrder
        (fun _ : Fin 1 => (w : SobolevData _).1) < ⊤) :
    ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
        (fun _ : Fin 1 => (v : SobolevData _).1) < ⊤ := by
  intro v
  obtain ⟨w, hwval, _hwgrad⟩ :=
    aux_lane4_coercivity_dilation_killed_pullback d z r hr one_pos v
  have hsc := lane4_gagliardo_dilation_scaling d 1 hd z 0 r hr one_pos
    threeQuarterOrder
    (fun _ : Fin 1 => (v : SobolevData (centeredCube z r hr)).1)
    (fun _ : Fin 1 => (w : SobolevData
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1)
    (fun _ => hwval)
  have hsq := hsc.1
  have hfiniteSq :
      (cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
        (fun _ : Fin 1 => (v : SobolevData _).1)) ^ (2 : ℕ) < ⊤ := by
    rw [hsq]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top (hunit w))
  exact (ENNReal.pow_lt_top_iff.mp hfiniteSq).resolve_right (by norm_num)

/-- Tight fractional and `L²` killed-space coercivity on each fixed expanding triadic cube.
The bound is uniform in the cutoff index; its `L¹` moment gives tightness for operator
extraction and its fractional part supplies collective compactness. -/
theorem large_cube_killed_coercivity
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pc : in_poincare d hd E)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta →
      ∀ (k : ℕ), 0 < k → ∀ (hr3 : (0 : ℝ) < (3 : ℝ) ^ k),
      ∀ z : SpatialCoordinates d,
      ∃ Kc : ℕ → BilateralField d → ℝ, ∃ Cbound : ℝ, 0 ≤ Cbound ∧
        (∀ N omega, 0 < Kc N omega) ∧
        (∀ N omega (v : killedSobolevGraph
            (centeredCube z ((3 : ℝ) ^ k) hr3)),
          cubeFractionalL2Seminorm hd z ((3 : ℝ) ^ k) hr3 threeQuarterOrder
            (fun _ : Fin 1 => (v : SobolevData
              (centeredCube z ((3 : ℝ) ^ k) hr3)).1) < ⊤ ∧
          cubeFractionalSqNorm hd z ((3 : ℝ) ^ k) hr3 threeQuarterOrder
              (v : SobolevData (centeredCube z ((3 : ℝ) ^ k) hr3)).1 ≤
            Kc N omega * sobolevCoefficientForm
              (cutoffPositiveCoefficient M H omega N z hr3)
              (v : SobolevData (centeredCube z ((3 : ℝ) ^ k) hr3))
              (v : SobolevData (centeredCube z ((3 : ℝ) ^ k) hr3)) ∧
          ‖(v : SobolevData (centeredCube z ((3 : ℝ) ^ k) hr3)).1‖ ^ 2 ≤
            Kc N omega * sobolevCoefficientForm
              (cutoffPositiveCoefficient M H omega N z hr3)
              (v : SobolevData (centeredCube z ((3 : ℝ) ^ k) hr3))
              (v : SobolevData (centeredCube z ((3 : ℝ) ^ k) hr3))) ∧
        (∀ N, MemLp (Kc N) 1 (chaosSampleLaw M).toMeasure ∧
          eLpNorm (Kc N) 1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cbound) := by
  obtain ⟨delta0, hdelta0, hcoercivity⟩ := aux_lem_coercivity_compat d hd E Pc Sf
  refine ⟨delta0 2, hdelta0 2 (by norm_num), ?_⟩
  intro M Rm H hH hdelta k hk hr3 z
  have hunit := hcoercivity M Rm H hH 0 1 one_pos le_rfl
  obtain ⟨Kunit, hKunit, hKmom⟩ := hunit
  obtain ⟨Cunit0, hKmem, hKbound⟩ := hKmom 2 (by norm_num) hdelta
  let r : ℝ := (3 : ℝ) ^ k
  have hr : 0 < r := by simp [r]
  let shift : BilateralField d → BilateralField d :=
    aux_rem_bank_response_moments_lc_upShift k z
  let F : BilateralField d → ℝ :=
    aux_rem_bank_response_moments_lc_environment_factor M H k z hr
  let Kplus : ℕ → BilateralField d → ℝ := fun N omega => |Kunit N omega| + 1
  let Kshift : ℕ → BilateralField d → ℝ := fun N omega => Kplus (N + k) (shift omega)
  let Rfac : ℝ := r ^ ((d : ℝ) - 2)
  let vol : ℝ := volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
  let c0 : ℝ := (max vol 1) * Rfac⁻¹
  let Kc : ℕ → BilateralField d → ℝ := fun N omega => c0 * (F omega * Kshift N omega)
  have hRfac : 0 < Rfac := Real.rpow_pos_of_pos hr _
  have hvol : 0 < vol := centeredCube_volume_pos z hr
  have hVfac : 1 ≤ max vol 1 := le_max_right _ _
  have hVfacPos : 0 < max vol 1 := lt_of_lt_of_le zero_lt_one hVfac
  have hc0 : 0 < c0 := mul_pos hVfacPos (inv_pos.mpr hRfac)
  have hmu : (chaosSampleLaw M).toMeasure ≠ 0 := by
    intro hzero
    have h := congrArg (fun μ : Measure (BilateralField d) => μ Set.univ) hzero
    simp at h
  have hp2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by norm_num
  -- Assemble the shifted unit constants in L². The scalar `+1` makes the coercivity
  -- coefficient positive without relying on any sign convention for the source witness.
  have hKplusMem : ∀ N, MemLp (Kplus N) (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure := by
    intro N
    have hconst : MemLp (fun _ : BilateralField d => (1 : ℝ)) (ENNReal.ofReal 2)
        (chaosSampleLaw M).toMeasure := memLp_const 1
    have h := (hKmem N).abs.add hconst
    convert h using 1 ; ext omega ; simp [Kplus]
  have hKplusBound : ∀ N,
      eLpNorm (Kplus N) (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (max Cunit0 0 + 2) := by
    intro N
    have hconst : MemLp (fun _ : BilateralField d => (1 : ℝ)) (ENNReal.ofReal 2)
        (chaosSampleLaw M).toMeasure := memLp_const 1
    have hconstBound : eLpNorm (fun _ : BilateralField d => (1 : ℝ))
        (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal 1 := by
      rw [eLpNorm_const (1 : ℝ) (by norm_num) hmu]
      simp
    have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by norm_num
    have hAbs := (hKmem N).abs
    have hsum := eLpNorm_add_le (f := fun omega => |Kunit N omega|) (g := fun _ => (1 : ℝ)) (μ := (chaosSampleLaw M).toMeasure) hp1
    have habs : eLpNorm (fun omega => |Kunit N omega|) (ENNReal.ofReal 2)
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cunit0 := by
      have habsEq : eLpNorm (fun omega => |Kunit N omega|) (ENNReal.ofReal 2)
          (chaosSampleLaw M).toMeasure =
          eLpNorm (Kunit N) (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure := by
        calc
          _ = eLpNorm (fun omega => ‖Kunit N omega‖) (ENNReal.ofReal 2)
              (chaosSampleLaw M).toMeasure := by
            simp [Real.norm_eq_abs]
          _ = _ := eLpNorm_norm _ (hKmem N).aestronglyMeasurable
      rw [habsEq]
      exact hKbound N
    have hC : ENNReal.ofReal Cunit0 ≤ ENNReal.ofReal (max Cunit0 0) :=
      ENNReal.ofReal_le_ofReal (le_max_left _ _)
    have hone : (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) := by norm_num
    have hsum' : eLpNorm (Kplus N)
        (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (max Cunit0 0) + ENNReal.ofReal 1 := by
      have hsum0 : eLpNorm (Kplus N) (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
          eLpNorm (fun omega => |Kunit N omega|) (ENNReal.ofReal 2)
            (chaosSampleLaw M).toMeasure +
            eLpNorm (fun _ : BilateralField d => (1 : ℝ)) (ENNReal.ofReal 2)
              (chaosSampleLaw M).toMeasure := by
        simpa [Kplus, Pi.add_apply] using! hsum
      exact hsum0.trans (add_le_add (habs.trans hC) hconstBound)
    have hnonneg : 0 ≤ max Cunit0 0 := le_max_right _ _
    have hsumReal : ENNReal.ofReal (max Cunit0 0) + ENNReal.ofReal 1 =
        ENNReal.ofReal (max Cunit0 0 + 1) := by
      rw [← ENNReal.ofReal_add hnonneg (by norm_num)]
    rw [hsumReal] at hsum'
    exact hsum'.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hshift := aux_rem_bank_response_moments_lc_upShift_measurePreserving M k z
  have hKshiftMem : ∀ N, MemLp (Kshift N) (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure := by
    intro N
    exact (hKplusMem (N + k)).comp_measurePreserving hshift
  have hKshiftBound : ∀ N,
      eLpNorm (Kshift N) (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (max Cunit0 0 + 2) := by
    intro N
    have hEq := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal 2)
      (hKplusMem (N + k)).aestronglyMeasurable hshift
    change eLpNorm (Kplus (N + k) ∘ shift) (ENNReal.ofReal 2)
        (chaosSampleLaw M).toMeasure ≤ _
    rw [hEq]
    exact hKplusBound (N + k)
  have hFmem := aux_rem_bank_response_moments_envFactor_memLp hd M H hH k z hr 2 (by norm_num)
  let CF : ℝ := (eLpNorm F (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure).toReal
  have hCF : 0 ≤ CF := ENNReal.toReal_nonneg
  have hFbound : eLpNorm F (ENNReal.ofReal 2) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CF := by
    dsimp [CF]
    rw [ENNReal.ofReal_toReal hFmem.eLpNorm_ne_top]
  have hFmem' : MemLp F (ENNReal.ofReal (2 * 1)) (chaosSampleLaw M).toMeasure := by
    simpa [mul_one] using hFmem
  have hFbound' : eLpNorm F (ENNReal.ofReal (2 * 1))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CF := by
    simpa [mul_one] using hFbound
  have hKshiftMem' : ∀ N, MemLp (Kshift N) (ENNReal.ofReal (2 * 1))
      (chaosSampleLaw M).toMeasure := by
    intro N
    simpa [mul_one] using hKshiftMem N
  have hKshiftBound' : ∀ N,
      eLpNorm (Kshift N) (ENNReal.ofReal (2 * 1)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (max Cunit0 0 + 2) := by
    intro N
    simpa [mul_one] using hKshiftBound N
  have hprod := aux_rem_bank_response_moments_prod_moments
    (chaosSampleLaw M).toMeasure F Kshift 1 CF (max Cunit0 0 + 2) hCF
    hFmem' hFbound' hKshiftMem' hKshiftBound'
  let Cbound : ℝ := c0 * (CF * (max Cunit0 0 + 2))
  have hCbound : 0 ≤ Cbound := by
    dsimp [Cbound]
    positivity
  refine ⟨Kc, Cbound, hCbound, ?_, ?_, ?_⟩
  · intro N omega
    have hKshiftPos : 0 < Kshift N omega := by
      dsimp [Kshift, Kplus]
      positivity
    have hFpos : 0 < F omega := by
      exact aux_rem_bank_response_moments_lc_environment_factor_pos M H k z hr omega
    dsimp [Kc]
    exact mul_pos hc0 (mul_pos hFpos hKshiftPos)
  · intro N omega v
    let Q := centeredCube z r hr
    let vL2 : DomainL2 Q := (v : SobolevData Q).1
    let a := cutoffPositiveCoefficient M H omega N z hr
    let b := cutoffPositiveCoefficient M H (shift omega) (N + k) 0 one_pos
    have hb : ∀ w : killedSobolevGraph
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
        cubeFractionalSqNorm hd 0 1 one_pos threeQuarterOrder
          (w : SobolevData _).1 ≤
          Kplus (N + k) (shift omega) * sobolevCoefficientForm b (w : SobolevData _) w := by
      intro w
      have hunit0 := ((hKunit (N + k) (shift omega)).1 w).2
      have hform0 := sobolevCoefficientForm_nonneg b (w : SobolevData _)
      have hKle : Kunit (N + k) (shift omega) ≤ Kplus (N + k) (shift omega) := by
        dsimp [Kplus]
        exact (le_abs_self _).trans (le_add_of_nonneg_right (by norm_num))
      exact hunit0.trans (mul_le_mul_of_nonneg_right hKle hform0)
    have hcoeff := aux_rem_bank_response_moments_lc_coefficients_le M Rm H k z hr true N omega
    have hcoeff' : ∀ᵐ x ∂volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
        b.val x ≤ F omega * a.val (cubeDilation z 0 r x) := by
      simpa [a, b, F, shift, r] using hcoeff
    have hfinite := aux_large_cube_killed_coercivity_seminorm_finite hd z hr
      (fun w => ((hKunit (N + k) (shift omega)).1 w).1)
    have hfrac := aux_large_cube_killed_coercivity_fractional_transport hd z k a b
      (Kplus (N + k) (shift omega)) (F omega)
      (by positivity) hb hcoeff'
    have hfracv : cubeFractionalSqNorm hd z r hr threeQuarterOrder vL2 ≤
        (Kshift N omega * F omega * Rfac⁻¹) *
          sobolevCoefficientForm a (v : SobolevData Q) v := by
      simpa [vL2, Q, r, Kshift, Kplus, Rfac] using hfrac v
    have hform : 0 ≤ sobolevCoefficientForm a (v : SobolevData Q) v :=
      sobolevCoefficientForm_nonneg a (v : SobolevData Q)
    have hKshiftPos : 0 < Kshift N omega := by
      dsimp [Kshift, Kplus]
      positivity
    have hFpos : 0 < F omega :=
      aux_rem_bank_response_moments_lc_environment_factor_pos M H k z hr omega
    have hscale_nonneg : 0 ≤ Kshift N omega * F omega * Rfac⁻¹ := by positivity
    have hscale_le : Kshift N omega * F omega * Rfac⁻¹ ≤ Kc N omega := by
      have hmul := mul_le_mul_of_nonneg_right hVfac hscale_nonneg
      dsimp [Kc, c0]
      nlinarith [show Kshift N omega * F omega * Rfac⁻¹ =
          Rfac⁻¹ * (F omega * Kshift N omega) by ring]
    have hfracK : cubeFractionalSqNorm hd z r hr threeQuarterOrder vL2 ≤
        Kc N omega * sobolevCoefficientForm a (v : SobolevData Q) v :=
      hfracv.trans (mul_le_mul_of_nonneg_right hscale_le hform)
    have hun := SubdiffusiveProcess.Lnorm.fractional_coercivity_unnormalized hd z r hr
      vL2 (Kshift N omega * F omega * Rfac⁻¹)
      (sobolevCoefficientForm a (v : SobolevData Q) v) hfracv
    have hvol_le : vol * (Kshift N omega * F omega * Rfac⁻¹) ≤ Kc N omega := by
      have hv : vol ≤ max vol 1 := le_max_left _ _
      have h := mul_le_mul_of_nonneg_right hv hscale_nonneg
      dsimp [Kc, c0]
      nlinarith [show Kshift N omega * F omega * Rfac⁻¹ =
          Rfac⁻¹ * (F omega * Kshift N omega) by ring]
    have hL2 : ‖vL2‖ ^ 2 ≤
        (vol * (Kshift N omega * F omega * Rfac⁻¹)) *
          sobolevCoefficientForm a (v : SobolevData Q) v := by
      have hsemi : 0 ≤ vol *
          ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
            (fun _ : Fin 1 => vL2)).toReal) ^ 2 := by positivity
      have hleft : ‖vL2‖ ^ 2 ≤
          ‖vL2‖ ^ 2 + vol *
            ((cubeFractionalL2Seminorm hd z r hr threeQuarterOrder
              (fun _ : Fin 1 => vL2)).toReal) ^ 2 := le_add_of_nonneg_right hsemi
      exact hleft.trans hun
    have hL2K : ‖vL2‖ ^ 2 ≤ Kc N omega *
        sobolevCoefficientForm a (v : SobolevData Q) v :=
      hL2.trans (mul_le_mul_of_nonneg_right hvol_le hform)
    constructor
    · simpa [vL2, Q, r] using hfinite v
    · constructor
      · simpa [vL2, Q, r, a] using hfracK
      · simpa [vL2, Q, r, a] using hL2K
  · intro N
    have hKceq : ∀ N, Kc N = fun omega => c0 * (F omega * Kshift N omega) := by
      intro N
      rfl
    have hmem : MemLp (Kc N) 1 (chaosSampleLaw M).toMeasure := by
      rw [hKceq N]
      convert (hprod.1 N).const_mul c0 using 1 ; norm_num
    have hKceqSmul : Kc N = c0 • (fun omega => F omega * Kshift N omega) := by
      funext omega
      simp [Kc, smul_eq_mul]
    have hbound : eLpNorm (Kc N) 1 (chaosSampleLaw M).toMeasure ≤
        ‖c0‖ₑ * eLpNorm (fun omega => F omega * Kshift N omega) 1
          (chaosSampleLaw M).toMeasure := by
      rw [hKceqSmul]
      exact eLpNorm_const_smul_le
    have hc0norm : ‖c0‖ₑ = ENNReal.ofReal c0 := by
      exact Real.enorm_eq_ofReal hc0.le
    have hprodN := hprod.2 N
    have hprodN' : eLpNorm (fun omega => F omega * Kshift N omega) 1
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (CF * (max Cunit0 0 + 2)) := by
      convert hprodN using 1 ; norm_num
    have hbound' : eLpNorm (Kc N) 1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cbound := by
      calc
        _ ≤ ‖c0‖ₑ * ENNReal.ofReal (CF * (max Cunit0 0 + 2)) := by
          exact hbound.trans (mul_le_mul_of_nonneg_left hprodN' (by positivity))
        _ = ENNReal.ofReal c0 * ENNReal.ofReal (CF * (max Cunit0 0 + 2)) := by
          rw [hc0norm]
        _ = ENNReal.ofReal Cbound := by
          rw [← ENNReal.ofReal_mul hc0.le]
    exact ⟨hmem, hbound'⟩

end SubdiffusiveProcess.Paper
