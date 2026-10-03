module

public import SubdiffusiveProcess.Analysis.CubeFacePatch
public import SubdiffusiveProcess.Analysis.FractionalCellVariance
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

open MeasureTheory Filter Set Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess


/-- The compact support condition gives a zero value on the chosen cube face. -/
theorem cubeFaceInsert_zero_of_support {n : ℕ} (upper : Bool) (i : Fin (n + 1))
    (phi : SpatialCoordinates (n + 1) → ℝ) (hsupp : tsupport phi ⊆ cubeExtensionBox (n + 1))
    (z : SpatialCoordinates n) : phi (cubeFaceInsert upper i 0 z) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hQ := hsupp hmem
  have ht := (cubeExtensionBox_faceInsert_iff upper i 0 z).mp hQ
  exact (lt_irrefl (0 : ℝ)) ht.1.1

/-- The one-dimensional fundamental theorem and Cauchy--Schwarz along a normal line. -/
theorem cubeFaceInsert_sq_le_derivative_integral {n : ℕ} (upper : Bool) (i : Fin (n + 1))
    (phi : SpatialCoordinates (n + 1) → ℝ) (hphi : ContDiff ℝ 1 phi)
    (hsupp : tsupport phi ⊆ cubeExtensionBox (n + 1)) (z : SpatialCoordinates n)
    (t : ℝ) (ht : 0 < t) :
    phi (cubeFaceInsert upper i t z) ^ 2 ≤
      t * ∫ u in (0 : ℝ)..t,
        (fderiv ℝ phi (cubeFaceInsert upper i u z) (basisVec i)) ^ 2 := by
  let D : ℝ → ℝ := fun u =>
    fderiv ℝ phi (cubeFaceInsert upper i u z) (basisVec i)
  let F : ℝ → ℝ := if upper then -D else D
  have hdiff : Differentiable ℝ phi := hphi.differentiable (by norm_num)
  have hderiv : ∀ u : ℝ, HasDerivAt (fun u => phi (cubeFaceInsert upper i u z)) (F u) u := by
    intro u
    cases upper
    · have h := (hasDerivAt_id u).sub_const (1 / 2 : ℝ)
      simpa [cubeFaceInsert, cubeFaceCoordinate, F, D] using!
        (hasDerivAt_comp_insertNth hdiff i z (u - 1 / 2)).scomp u h
    · have h := (hasDerivAt_id u).const_sub (1 / 2 : ℝ)
      simpa [cubeFaceInsert, cubeFaceCoordinate, F, D] using!
        (hasDerivAt_comp_insertNth hdiff i z (1 / 2 - u)).scomp u h
  have hDc : Continuous D := by
    have hc : Continuous (fun u : ℝ => cubeFaceInsert upper i u z) :=
      (continuous_cubeFaceInsert upper i).comp (continuous_id.prodMk continuous_const)
    exact ((hphi.continuous_fderiv (by norm_num)).comp hc).clm_apply continuous_const
  have hFc : Continuous F := by cases upper <;> simp [F] <;> fun_prop
  have hF2 : ∀ u, F u ^ 2 = D u ^ 2 := by cases upper <;> simp [F]
  have hFTC : phi (cubeFaceInsert upper i t z) = ∫ u in (0 : ℝ)..t, F u := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
      (hFc.intervalIntegrable 0 t)
    rw [cubeFaceInsert_zero_of_support upper i phi hsupp z, sub_zero] at h
    exact h.symm
  let J := ∫ u in (0 : ℝ)..t, F u
  let c := J / t
  have hct : J = t * c := by dsimp [c]; field_simp
  have h0 : 0 ≤ ∫ u in (0 : ℝ)..t, (F u - c) ^ 2 :=
    intervalIntegral.integral_nonneg ht.le (fun _ _ => sq_nonneg _)
  have hexp : (∫ u in (0 : ℝ)..t, (F u - c) ^ 2) =
      (∫ u in (0 : ℝ)..t, F u ^ 2) - 2 * c * J + t * c ^ 2 := by
    have he : ∀ u, (F u - c) ^ 2 = F u ^ 2 - 2 * c * F u + c ^ 2 := fun _ => by ring
    simp_rw [he]
    rw [intervalIntegral.integral_add
      (show IntervalIntegrable (fun u => F u ^ 2 - 2 * c * F u) volume 0 t from by
        simpa using! ((hFc.pow 2).intervalIntegrable 0 t).sub ((hFc.intervalIntegrable 0 t).const_mul (2 * c)))
        intervalIntegrable_const,
      intervalIntegral.integral_sub (show IntervalIntegrable (fun u => F u ^ 2) volume 0 t from by simpa using! (hFc.pow 2).intervalIntegrable 0 t)
        ((hFc.intervalIntegrable 0 t).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    rfl
  rw [hexp, hct] at h0
  have hI : t * c ^ 2 ≤ ∫ u in (0 : ℝ)..t, F u ^ 2 := by nlinarith
  rw [hFTC]
  change J ^ 2 ≤ _
  calc
    J ^ 2 = t * (t * c ^ 2) := by rw [hct]; ring
    _ ≤ t * ∫ u in (0 : ℝ)..t, F u ^ 2 := mul_le_mul_of_nonneg_left hI ht.le
    _ = _ := by simp_rw [hF2]; rfl

theorem lintegral_Ioo_zero_one_ofReal_rpow {p : ℝ} (hp : -1 < p) :
    (∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal t ^ p) = ENNReal.ofReal ((p + 1)⁻¹) := by
  have hi : IntervalIntegrable (fun t : ℝ => t ^ p) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hint : IntegrableOn (fun t : ℝ => t ^ p) (Ioo 0 1) :=
    hi.1.mono_set Ioo_subset_Ioc_self
  have hn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] fun t : ℝ => t ^ p := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _
  calc
    _ = ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ p) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      exact ENNReal.ofReal_rpow_of_pos ht.1
    _ = ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, t ^ p) :=
      (ofReal_integral_eq_lintegral_ofReal hint hn).symm
    _ = ENNReal.ofReal (∫ t in (0 : ℝ)..1, t ^ p) := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    _ = _ := by
      rw [integral_rpow (Or.inl hp)]
      simp [Real.zero_rpow (by linarith : p + 1 ≠ 0)]

/-- A smooth zero-trace datum has a finite face-weighted integral for every s < 1. -/
theorem cubeFaceWeightedIntegral_smooth_le {d : ℕ} (s : ℝ) (hs : s < 1)
    (upper : Bool) (i : Fin d) (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ 1 phi)
    (hsupp : tsupport phi ⊆ cubeExtensionBox d) :
    cubeFaceWeightedIntegral s upper i phi ≤
      ENNReal.ofReal ((2 - 2 * s)⁻¹) *
        ∫⁻ x in cubeExtensionBox d, ENNReal.ofReal ((fderiv ℝ phi x (basisVec i)) ^ 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt))
  let F : SpatialCoordinates (n + 1) → ℝ≥0∞ := fun x => ENNReal.ofReal (phi x ^ 2)
  let D : SpatialCoordinates (n + 1) → ℝ := fun x => fderiv ℝ phi x (basisVec i)
  have hFm : Measurable F := (hphi.continuous.measurable.pow_const 2).ennreal_ofReal
  have hDm : Measurable D := (hphi.continuous_fderiv (by norm_num)).clm_apply
    continuous_const |>.measurable
  have hnorm : (∫⁻ x in cubeExtensionBox (n + 1), ENNReal.ofReal (D x ^ 2)) =
      ∫⁻ z in cubeExtensionBox n, ∫⁻ t in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (D (cubeFaceInsert upper i t z) ^ 2) :=
    setLIntegral_cubeFaceCoordinates upper i _ ((hDm.pow_const 2).ennreal_ofReal)
  unfold cubeFaceWeightedIntegral
  rw [setLIntegral_cubeFaceCoordinates upper i _
    (show Measurable (fun x => ENNReal.ofReal (phi x ^ 2) * cubeFaceWeight s upper i x) from by simpa only [F] using! hFm.mul (measurable_cubeFaceWeight s upper i))]
  simp only [cubeFaceWeight, cubeFaceDistance_insert]
  calc
    _ ≤ ∫⁻ z in cubeExtensionBox n, ENNReal.ofReal ((2 - 2 * s)⁻¹) *
        ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (D (cubeFaceInsert upper i t z) ^ 2) := by
      apply lintegral_mono
      intro z
      let Dz : ℝ → ℝ := fun t => D (cubeFaceInsert upper i t z)
      have hDc : Continuous Dz := by
        exact ((hphi.continuous_fderiv (by norm_num)).clm_apply continuous_const).comp
          ((continuous_cubeFaceInsert upper i).comp (continuous_id.prodMk continuous_const))
      let J : ℝ := ∫ u in (0 : ℝ)..1, Dz u ^ 2
      have hJ : ENNReal.ofReal J = ∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (Dz u ^ 2) := by
        dsimp only [J]
        rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
        exact ofReal_integral_eq_lintegral_ofReal
          (((hDc.pow 2).intervalIntegrable 0 1).1.mono_set Ioo_subset_Ioc_self)
          (ae_of_all _ (fun u => sq_nonneg _))
      have hpoint : ∀ t ∈ Ioo (0 : ℝ) 1,
          ENNReal.ofReal (phi (cubeFaceInsert upper i t z) ^ 2) *
            ENNReal.ofReal t ^ (-(2 * s)) ≤
          ENNReal.ofReal J * ENNReal.ofReal t ^ (1 - 2 * s) := by
        intro t ht
        have hftc := cubeFaceInsert_sq_le_derivative_integral upper i phi hphi hsupp z t ht.1
        have hmono : (∫ u in (0 : ℝ)..t, Dz u ^ 2) ≤ J :=
          intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2.le
            (ae_of_all _ (fun u => sq_nonneg _)) ((hDc.pow 2).intervalIntegrable 0 1)
        have hsq : phi (cubeFaceInsert upper i t z) ^ 2 ≤ t * J :=
          hftc.trans (mul_le_mul_of_nonneg_left hmono ht.1.le)
        calc
          _ ≤ ENNReal.ofReal (t * J) * ENNReal.ofReal t ^ (-(2 * s)) :=
            mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hsq) zero_le
          _ = _ := by
            have hpow : ENNReal.ofReal t * ENNReal.ofReal t ^ (-(2 * s)) =
                ENNReal.ofReal t ^ (1 - 2 * s) := by
              calc
                _ = ENNReal.ofReal t ^ (1 : ℝ) * ENNReal.ofReal t ^ (-(2 * s)) := by
                  rw [ENNReal.rpow_one]
                _ = ENNReal.ofReal t ^ (1 + -(2 * s)) :=
                  (ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr ht.1)
                    ENNReal.ofReal_ne_top).symm
                _ = _ := by congr 1
            rw [ENNReal.ofReal_mul ht.1.le]
            calc
              _ = (ENNReal.ofReal t * ENNReal.ofReal t ^ (-(2 * s))) * ENNReal.ofReal J := by
                ac_rfl
              _ = _ := by rw [hpow, mul_comm]
      calc
        _ ≤ ∫⁻ t in Ioo (0 : ℝ) 1,
            ENNReal.ofReal J * ENNReal.ofReal t ^ (1 - 2 * s) :=
          setLIntegral_mono' measurableSet_Ioo hpoint
        _ = ENNReal.ofReal J * ENNReal.ofReal ((2 - 2 * s)⁻¹) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_Ioo_zero_one_ofReal_rpow (by linarith : -1 < 1 - 2 * s)]
          congr 2
          ring
        _ = _ := by rw [hJ, mul_comm]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hnorm]

end SubdiffusiveProcess
