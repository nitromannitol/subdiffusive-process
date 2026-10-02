import SubdiffusiveProcess.Analysis.FractionalFaceTransport

open MeasureTheory Filter Set Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess


theorem exists_cubeFace_contraction (d : ℕ) (s : ℝ) (hs : 1 / 2 < s) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
      ((2 : ℝ) ^ d / (2 * s)) * lam ^ (2 * s - 1) ≤ 1 / 2 := by
  have hp : 0 < 2 * s - 1 := by linarith
  have hc : Continuous (fun lam : ℝ => ((2 : ℝ) ^ d / (2 * s)) * lam ^ (2 * s - 1)) :=
    continuous_const.mul (Real.continuous_rpow_const hp.le)
  have ht : Tendsto (fun lam : ℝ => ((2 : ℝ) ^ d / (2 * s)) * lam ^ (2 * s - 1))
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa [Real.zero_rpow hp.ne'] using hc.tendsto 0
  have he := ht.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have he1 : ∀ᶠ lam : ℝ in 𝓝 (0 : ℝ), lam < 1 :=
    eventually_lt_nhds zero_lt_one
  have he' : ∀ᶠ lam : ℝ in 𝓝[>] (0 : ℝ), 0 < lam ∧ lam < 1 ∧
      ((2 : ℝ) ^ d / (2 * s)) * lam ^ (2 * s - 1) ≤ 1 / 2 := by
    filter_upwards [self_mem_nhdsWithin,
      he.filter_mono nhdsWithin_le_nhds, he1.filter_mono nhdsWithin_le_nhds] with lam hpos hh hlt
    exact ⟨hpos, hlt, hh⟩
  obtain ⟨lam, hpos, hlt, hh⟩ := he'.exists
  exact ⟨lam, hpos, hlt.le, hh⟩

theorem cubeFaceWeighted_sq_le_split {d : ℕ} (hd : 0 < d) (s lam : ℝ)
    (hs : 0 < s) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (upper : Bool) (i : Fin d)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f)
    {x : SpatialCoordinates d} (hx : x ∈ cubeExtensionBox d) :
    ENNReal.ofReal (f x ^ 2) * cubeFaceWeight s upper i x ≤
      (2 * ENNReal.ofReal (d : ℝ) ^ ((d : ℝ) + 2 * s) / ENNReal.ofReal lam) *
        (∫⁻ y in cubeExtensionBox d, cubeFractionalKernel s f x y) +
      (2 / ENNReal.ofReal lam) *
        ENNReal.ofReal (cubeFaceDistance upper i x) ^ (-((d : ℝ) + 2 * s)) *
        ∫⁻ y in cubeFacePatch lam upper i x, ENNReal.ofReal (f y ^ 2) := by
  let a := ENNReal.ofReal (cubeFaceDistance upper i x)
  let b := ENNReal.ofReal lam
  let p : ℝ := (d : ℝ) + 2 * s
  let R := ENNReal.ofReal (d : ℝ) ^ p * a ^ p
  let P := cubeFacePatch lam upper i x
  let F : SpatialCoordinates d → ℝ≥0∞ := fun y => ENNReal.ofReal (f y ^ 2)
  let K : SpatialCoordinates d → ℝ≥0∞ := fun y => cubeFractionalKernel s f x y
  have ha0 : a ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr
    (cubeFaceDistance_pos_lt_one upper i hx).1
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hb0 : b ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hlam0
  have hbt : b ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hR : R ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top)
    (ENNReal.rpow_ne_top_of_ne_zero ha0 hat)
  have hF : Measurable F := (hf.pow_const 2).ennreal_ofReal
  have hK : Measurable K := by
    dsimp only [K]
    unfold cubeFractionalKernel euclideanDist euclideanNorm vecNormSq vecDot
    fun_prop
  have hdiff : ∀ y ∈ P, ENNReal.ofReal ((f x - f y) ^ 2) ≤ R * K y := by
    intro y hy
    by_cases hxy : x = y
    · subst y
      simp only [sub_self, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero, zero_le]
    have hdist0 : ENNReal.ofReal (euclideanDist x y) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (lt_of_le_of_ne (euclideanDist_nonneg x y)
        (Ne.symm (euclideanDist_eq_zero_iff.not.mpr hxy)))
    have hdistpow0 : ENNReal.ofReal (euclideanDist x y) ^ p ≠ 0 :=
      (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hdist0) ENNReal.ofReal_ne_top).ne'
    have hdistpowt : ENNReal.ofReal (euclideanDist x y) ^ p ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top
    have hdist : ENNReal.ofReal (euclideanDist x y) ^ p ≤ R := by
      calc
        _ ≤ ENNReal.ofReal ((d : ℝ) * cubeFaceDistance upper i x) ^ p :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
            (euclideanDist_le_of_mem_cubeFacePatch lam hlam0 hlam1 upper i hx hy)) hp
        _ = _ := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg d),
            ENNReal.mul_rpow_of_nonneg _ _ hp]
    calc
      _ = ENNReal.ofReal (euclideanDist x y) ^ p * K y := by
        dsimp [K, cubeFractionalKernel, p]
        rw [mul_comm, ENNReal.div_mul_cancel hdistpow0 hdistpowt]
      _ ≤ R * K y := mul_le_mul_of_nonneg_right hdist (zero_le _)
  have hnum : ∀ y ∈ P, F x ≤ 2 * (R * K y + F y) := by
    intro y hy
    calc
      _ ≤ 2 * (ENNReal.ofReal ((f x - f y) ^ 2) + F y) := by
        calc
          _ ≤ ENNReal.ofReal (2 * (((f x - f y) ^ 2) + f y ^ 2)) :=
            ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (f x - 2 * f y)])
          _ = _ := by
            rw [ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
            norm_num only [ENNReal.ofReal_ofNat]
            rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (hdiff y hy) le_rfl) (zero_le _)
  have hintegral : (b * a ^ d) * F x ≤
      2 * (R * (∫⁻ y in P, K y) + ∫⁻ y in P, F y) := by
    calc
      _ ≤ volume P * F x := mul_le_mul_of_nonneg_right
        (cubeFacePatch_volume_ge lam hlam0 hlam1 upper i hx) (zero_le _)
      _ = ∫⁻ y in P, F x := by simp [lintegral_const, mul_comm]
      _ ≤ ∫⁻ y in P, 2 * (R * K y + F y) :=
        setLIntegral_mono' (measurableSet_cubeFacePatch lam upper i x) hnum
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          lintegral_add_left (hK.const_mul R), lintegral_const_mul' _ _ hR]
  have hm0 : b * a ^ d ≠ 0 := mul_ne_zero hb0 (pow_ne_zero d ha0)
  have hmt : b * a ^ d ≠ ⊤ := ENNReal.mul_ne_top hbt (ENNReal.pow_ne_top hat)
  have hweighted := mul_le_mul_of_nonneg_left hintegral
    (zero_le ((b * a ^ d)⁻¹ * a ^ (-(2 * s))))
  have hcancel : ((b * a ^ d)⁻¹ * a ^ (-(2 * s))) * ((b * a ^ d) * F x) =
      F x * a ^ (-(2 * s)) := by
    calc
      _ = a ^ (-(2 * s)) * ((b * a ^ d)⁻¹ * (b * a ^ d)) * F x := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel hm0 hmt, mul_one, mul_comm]
  rw [hcancel] at hweighted
  have hpow : (a ^ d)⁻¹ * a ^ (-(2 * s)) = a ^ (-p) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_neg,
      ← ENNReal.rpow_add _ _ ha0 hat]
    congr 1
    dsimp [p]
    ring
  have hcoef : (b * a ^ d)⁻¹ * a ^ (-(2 * s)) = b⁻¹ * a ^ (-p) := by
    rw [ENNReal.mul_inv (Or.inl hb0) (Or.inl hbt), mul_assoc, hpow]
  have hpcancel : a ^ (-p) * a ^ p = 1 := by
    rw [← ENNReal.rpow_add _ _ ha0 hat]
    simp
  have heq : ((b * a ^ d)⁻¹ * a ^ (-(2 * s))) *
      (2 * (R * (∫⁻ y in P, K y) + ∫⁻ y in P, F y)) =
      (2 * ENNReal.ofReal (d : ℝ) ^ p / b) * (∫⁻ y in P, K y) +
        (2 / b) * a ^ (-p) * (∫⁻ y in P, F y) := by
    rw [hcoef]
    dsimp only [R]
    rw [mul_add]
    have hterm : (b⁻¹ * a ^ (-p)) *
        (2 * (ENNReal.ofReal (d : ℝ) ^ p * a ^ p * (∫⁻ y in P, K y))) =
        (2 * ENNReal.ofReal (d : ℝ) ^ p / b) * (∫⁻ y in P, K y) := by
      calc
        _ = (a ^ (-p) * a ^ p) * ((2 * ENNReal.ofReal (d : ℝ) ^ p / b) *
          (∫⁻ y in P, K y)) := by simp only [div_eq_mul_inv]; ac_rfl
        _ = _ := by rw [hpcancel, one_mul]
    rw [mul_add, hterm]
    simp only [div_eq_mul_inv]
    congr 1
    ac_rfl
  rw [heq] at hweighted
  exact hweighted.trans (add_le_add
    (mul_le_mul_of_nonneg_left
      (lintegral_mono_set (cubeFacePatch_subset lam hlam0 hlam1 upper i hx)) (zero_le _)) le_rfl)

theorem cubeFaceWeightedIntegral_le_split {d : ℕ} (hd : 0 < d) (s lam : ℝ)
    (hs : 0 < s) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (upper : Bool) (i : Fin d)
    (f : SpatialCoordinates d → ℝ) (hf : Measurable f) :
    cubeFaceWeightedIntegral s upper i f ≤
      (2 * ENNReal.ofReal (d : ℝ) ^ ((d : ℝ) + 2 * s) / ENNReal.ofReal lam) *
        unitCubeFractionalEnergy s f +
      ENNReal.ofReal (((2 : ℝ) ^ d / (2 * s)) * lam ^ (2 * s - 1)) *
        cubeFaceWeightedIntegral s upper i f := by
  let A := 2 * ENNReal.ofReal (d : ℝ) ^ ((d : ℝ) + 2 * s) / ENNReal.ofReal lam
  let B := (2 : ℝ≥0∞) / ENNReal.ofReal lam
  let T := (2 : ℝ≥0∞) ^ (d - 1) * (ENNReal.ofReal (2 * s))⁻¹ *
    ENNReal.ofReal lam ^ (2 * s)
  have hB : B ≠ ⊤ := ENNReal.div_ne_top ENNReal.ofNat_ne_top
    (ENNReal.ofReal_ne_zero_iff.mpr hlam0)
  have hkernel := measurable_cubeFractionalKernel s f hf
  have hinner : Measurable (fun x : SpatialCoordinates d =>
      ∫⁻ y in cubeExtensionBox d, cubeFractionalKernel s f x y) :=
    hkernel.lintegral_prod_right
  have hcoef : B * T =
      ENNReal.ofReal (((2 : ℝ) ^ d / (2 * s)) * lam ^ (2 * s - 1)) := by
    have hpow : (ENNReal.ofReal lam)⁻¹ * ENNReal.ofReal lam ^ (2 * s) =
        ENNReal.ofReal lam ^ (2 * s - 1) := by
      rw [← ENNReal.rpow_neg_one,
        ← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr hlam0) ENNReal.ofReal_ne_top]
      congr 1
      ring
    have htwo : (2 : ℝ≥0∞) * 2 ^ (d - 1) = 2 ^ d := by
      calc
        (2 : ℝ≥0∞) * 2 ^ (d - 1) = (2 : ℝ≥0∞) ^ ((d - 1) + 1) := by rw [pow_succ, mul_comm]
        _ = _ := by rw [Nat.sub_add_cancel hd]
    rw [ENNReal.ofReal_mul (div_nonneg (pow_nonneg (by norm_num) d) (by positivity)),
      ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat, ← ENNReal.ofReal_rpow_of_pos hlam0]
    dsimp only [B, T]
    calc
      _ = (2 * 2 ^ (d - 1)) / ENNReal.ofReal (2 * s) *
          ((ENNReal.ofReal lam)⁻¹ * ENNReal.ofReal lam ^ (2 * s)) := by
        simp only [div_eq_mul_inv]
        ring
      _ = _ := by rw [htwo, hpow]
  calc
    cubeFaceWeightedIntegral s upper i f ≤
        ∫⁻ x in cubeExtensionBox d,
          A * (∫⁻ y in cubeExtensionBox d, cubeFractionalKernel s f x y) +
            B * (ENNReal.ofReal (cubeFaceDistance upper i x) ^ (-((d : ℝ) + 2 * s)) *
              ∫⁻ y in cubeFacePatch lam upper i x, ENNReal.ofReal (f y ^ 2)) := by
      apply setLIntegral_mono' (measurableSet_cubeExtensionBox d)
      intro x hx
      simpa only [mul_assoc] using cubeFaceWeighted_sq_le_split hd s lam hs
        hlam0 hlam1 upper i f hf hx
    _ = A * unitCubeFractionalEnergy s f + B *
        (∫⁻ x in cubeExtensionBox d,
          ENNReal.ofReal (cubeFaceDistance upper i x) ^ (-((d : ℝ) + 2 * s)) *
            ∫⁻ y in cubeFacePatch lam upper i x, ENNReal.ofReal (f y ^ 2)) := by
      rw [lintegral_add_left (hinner.const_mul A), lintegral_const_mul _ hinner,
        lintegral_const_mul' _ _ hB]
      rfl
    _ ≤ A * unitCubeFractionalEnergy s f + B * (T * cubeFaceWeightedIntegral s upper i f) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (double_lintegral_cubeFacePatch_mass_le hd s lam hs hlam0 hlam1 upper i f hf) (zero_le _))
    _ = _ := by rw [← mul_assoc B, hcoef]

/-- Fractional Hardy on each face, with finiteness separated from absorption. -/
theorem exists_cubeFace_fractional_hardy (d : ℕ) (hd : 0 < d) (s : ℝ) (hs : 1 / 2 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (upper : Bool) (i : Fin d)
      (f : SpatialCoordinates d → ℝ), Measurable f →
      cubeFaceWeightedIntegral s upper i f ≠ ⊤ →
      cubeFaceWeightedIntegral s upper i f ≤ ENNReal.ofReal C * unitCubeFractionalEnergy s f := by
  obtain ⟨lam, hlam0, hlam1, htheta⟩ := exists_cubeFace_contraction d s hs
  have hs0 : 0 < s := by linarith
  let A : ℝ≥0∞ := 2 * ENNReal.ofReal (d : ℝ) ^ ((d : ℝ) + 2 * s) / ENNReal.ofReal lam
  have hAt : A ≠ ⊤ := ENNReal.div_ne_top
    (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top))
    (ENNReal.ofReal_ne_zero_iff.mpr hlam0)
  have hA0 : A ≠ 0 := (ENNReal.div_pos
    (mul_ne_zero (by norm_num) (ENNReal.rpow_pos
      (ENNReal.ofReal_pos.mpr (Nat.cast_pos.mpr hd)) ENNReal.ofReal_ne_top).ne')
    ENNReal.ofReal_ne_top).ne'
  let D : ℝ≥0∞ := 2 * A
  have hDt : D ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top hAt
  have hD0 : D ≠ 0 := mul_ne_zero (by norm_num) hA0
  refine ⟨D.toReal, ENNReal.toReal_pos hD0 hDt, ?_⟩
  intro upper i f hf hIt
  let I := cubeFaceWeightedIntegral s upper i f
  let G := unitCubeFractionalEnergy s f
  change I ≤ ENNReal.ofReal D.toReal * G
  rw [ENNReal.ofReal_toReal hDt]
  by_cases hGt : G = ⊤
  · simp [hGt, ENNReal.mul_top hD0]
  have hsplit : I ≤ A * G + ENNReal.ofReal (1 / 2 : ℝ) * I := by
    exact (cubeFaceWeightedIntegral_le_split hd s lam hs0 hlam0 hlam1 upper i f hf).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (ENNReal.ofReal_le_ofReal htheta) (zero_le I)))
  have hAGt : A * G ≠ ⊤ := ENNReal.mul_ne_top hAt hGt
  have hhalfIt : ENNReal.ofReal (1 / 2 : ℝ) * I ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIt
  have hreal := (ENNReal.toReal_le_toReal hIt (ENNReal.add_ne_top.mpr ⟨hAGt, hhalfIt⟩)).mpr hsplit
  rw [ENNReal.toReal_add hAGt hhalfIt, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num)] at hreal
  apply (ENNReal.toReal_le_toReal hIt (ENNReal.mul_ne_top hDt hGt)).mp
  dsimp only [D]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  norm_num only [ENNReal.toReal_ofNat]
  nlinarith

end SubdiffusiveProcess
