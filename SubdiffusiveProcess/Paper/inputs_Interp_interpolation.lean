module

public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.Sobolev.FractionalRepresentatives
public import SubdiffusiveProcess.Paper.inputs_classical_e4_interpolation

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

lemma aux_inputs_Interp_interpolation_norm_half_bound
    (a b c m N : ℝ) (ha : 0 ≤ a) (hNa : a ≤ N) (hNb : b ≤ N)
    (hb : 0 ≤ b) (hm : 1 ≤ m) (hc : c ≤ m) :
    a + c * b ≤ 2 * m * N := by
  have hN : 0 ≤ N := le_trans ha hNa
  have h1 : a ≤ m * N := by
    calc
      a ≤ N := hNa
      _ = 1 * N := by ring
      _ ≤ m * N := mul_le_mul_of_nonneg_right hm hN
  have h2 : c * b ≤ m * N := by
    calc
      c * b ≤ m * b := mul_le_mul_of_nonneg_right hc hb
      _ ≤ m * N := mul_le_mul_of_nonneg_left hNb (le_trans (by norm_num) hm)
  calc
    a + c * b ≤ m * N + m * N := add_le_add h1 h2
    _ = 2 * m * N := by ring

lemma aux_inputs_Interp_interpolation_norm_three_bound
    (a b c m N : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : N ≤ a + b)
    (hm : 1 ≤ m) (hcinv : c⁻¹ ≤ m) (hc : 0 < c) :
    N ≤ m * (a + c * b) := by
  have hmc : 1 ≤ m * c := by
    calc
      1 = c⁻¹ * c := by rw [inv_mul_cancel₀ hc.ne']
      _ ≤ m * c := mul_le_mul_of_nonneg_right hcinv hc.le
  have ha' : a ≤ m * a := by
    calc
      a = 1 * a := by ring
      _ ≤ m * a := mul_le_mul_of_nonneg_right hm ha
  have hb' : b ≤ m * (c * b) := by
    calc
      b = 1 * b := by ring
      _ ≤ (m * c) * b := mul_le_mul_of_nonneg_right hmc hb
      _ = m * (c * b) := by ring
  calc
    N ≤ a + b := hN
    _ ≤ m * a + m * (c * b) := add_le_add ha' hb'
    _ = m * (a + c * b) := by ring

lemma aux_inputs_Interp_interpolation_sqrt_pair_le
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ a + b := by
  rw [Real.sqrt_le_iff]
  constructor
  · exact add_nonneg ha hb
  · nlinarith [mul_nonneg ha hb]

lemma aux_inputs_Interp_interpolation_rpow_mono
    (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ (2 / 3 : ℝ) ≤ y ^ (2 / 3 : ℝ) :=
  Real.rpow_le_rpow hx hxy (by norm_num)

lemma aux_inputs_Interp_interpolation_rpow_mul
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x * y) ^ (2 / 3 : ℝ) = x ^ (2 / 3 : ℝ) * y ^ (2 / 3 : ℝ) :=
  Real.mul_rpow hx hy

lemma aux_inputs_Interp_interpolation_norm_conversion
    (a athree b ch ct K : ℝ) (ha : 0 ≤ a) (hat : 0 ≤ athree) (hb : 0 ≤ b)
    (_hch : 0 < ch) (hct : 0 < ct) (hK : 0 ≤ K)
    (hI : Real.sqrt (a ^ 2 + b ^ 2) ≤
      K * b ^ (1 / 3 : ℝ) * Real.sqrt (athree ^ 2 + b ^ 2) ^ (2 / 3 : ℝ)) :
    a + ch * b ≤
      (2 * max 1 ch * K * (max 1 (ct⁻¹)) ^ (2 / 3 : ℝ)) *
        b ^ (1 / 3 : ℝ) * (athree + ct * b) ^ (2 / 3 : ℝ) := by
  let Nhalf : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
  let Nthree : ℝ := Real.sqrt (athree ^ 2 + b ^ 2)
  let mh : ℝ := max 1 ch
  let mt : ℝ := max 1 (ct⁻¹)
  have hNa : a ≤ Nhalf :=
    (Real.le_sqrt ha (by positivity)).2 (by nlinarith [sq_nonneg b])
  have hNb : b ≤ Nhalf :=
    (Real.le_sqrt hb (by positivity)).2 (by nlinarith [sq_nonneg a])
  have hsum : Nthree ≤ athree + b := by
    dsimp [Nthree]
    rw [Real.sqrt_le_iff]
    constructor
    · exact add_nonneg hat hb
    · nlinarith [mul_nonneg hat hb]
  have hmh1 : 1 ≤ mh := le_max_left _ _
  have hmhc : ch ≤ mh := le_max_right _ _
  have hmt1 : 1 ≤ mt := le_max_left _ _
  have hmtinv : ct⁻¹ ≤ mt := le_max_right _ _
  have hnormHle : a + ch * b ≤ 2 * mh * Nhalf :=
    aux_inputs_Interp_interpolation_norm_half_bound a b ch mh Nhalf
      ha hNa hNb hb hmh1 hmhc
  have hnormTle : Nthree ≤ mt * (athree + ct * b) :=
    aux_inputs_Interp_interpolation_norm_three_bound
      athree b ct mt Nthree hat hb hsum hmt1 hmtinv hct
  have hpownorm : Nthree ^ (2 / 3 : ℝ) ≤
      (mt * (athree + ct * b)) ^ (2 / 3 : ℝ) :=
    aux_inputs_Interp_interpolation_rpow_mono Nthree
      (mt * (athree + ct * b)) (Real.sqrt_nonneg _) hnormTle
  have hmulpow : (mt * (athree + ct * b)) ^ (2 / 3 : ℝ) =
      mt ^ (2 / 3 : ℝ) * (athree + ct * b) ^ (2 / 3 : ℝ) :=
    aux_inputs_Interp_interpolation_rpow_mul mt (athree + ct * b)
      (le_trans (by norm_num) hmt1) (add_nonneg hat (mul_nonneg hct.le hb))
  calc
    a + ch * b ≤ 2 * mh * Nhalf := hnormHle
    _ ≤ 2 * mh * (K * b ^ (1 / 3 : ℝ) * Nthree ^ (2 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ ≤ 2 * mh * (K * b ^ (1 / 3 : ℝ) *
        (mt * (athree + ct * b)) ^ (2 / 3 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hpownorm
          (mul_nonneg hK (Real.rpow_nonneg hb _))
      · positivity
    _ = (2 * max 1 ch * K * (max 1 (ct⁻¹)) ^ (2 / 3 : ℝ)) *
          b ^ (1 / 3 : ℝ) * (athree + ct * b) ^ (2 / 3 : ℝ) := by
      rw [hmulpow]
      dsimp [mh, mt]
      ring

lemma aux_inputs_Interp_interpolation_pullback_l2
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (v : DomainL2 (centeredCube z r hr)) :
    ∃ u : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)),
      u =ᵐ[volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d))]
        (fun x => (v : SpatialCoordinates d → ℝ) (cubeDilation z 0 r x)) ∧
      ‖v‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) = ‖u‖ := by
  let h1 : (0 : ℝ) < 1 := by norm_num
  let μu : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d))
  let μr : Measure (SpatialCoordinates d) :=
    volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  let c : ℝ≥0∞ := ENNReal.ofReal (r ^ d)
  let T : SpatialCoordinates d → SpatialCoordinates d := cubeDilation z 0 r
  have hcpos : 0 < r ^ d := pow_pos hr d
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact ENNReal.ofReal_ne_zero_iff.mpr hcpos
  have hctop : c ≠ ⊤ := by
    dsimp [c]
    exact ENNReal.ofReal_ne_top
  have hprod : ENNReal.ofReal (r ^ d) * ENNReal.ofReal |(r ^ d)⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    rw [abs_of_pos (by positivity : 0 < (r ^ d)⁻¹)]
    rw [mul_inv_cancel₀ hcpos.ne']
    simp
  have hmap : Measure.map T (c • μu) = μr := by
    dsimp [T, μu, μr, c]
    rw [Measure.map_smul, _root_.SubdiffusiveProcess.EllipticRegularity.map_cubeDilation_restrict z 0 hr h1,
      smul_smul, hprod, one_smul]
    exact (_root_.SubdiffusiveProcess.EllipticRegularity.continuous_cubeDilation z 0 r).measurable.aemeasurable
  have hMP : MeasurePreserving T (c • μu) μr :=
    ⟨(_root_.SubdiffusiveProcess.EllipticRegularity.continuous_cubeDilation z 0 r).measurable, hmap⟩
  let raw : SpatialCoordinates d → ℝ := fun x =>
    (v : SpatialCoordinates d → ℝ) (T x)
  have hmem : MemLp raw 2 (c • μu) := by
    dsimp [raw]
    exact (Lp.memLp v).comp_measurePreserving hMP
  have hmeasure : c⁻¹ • (c • μu) = μu := by
    rw [smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul]
  have hmemu : MemLp raw 2 μu := by
    have h := hmem.smul_measure (c := c⁻¹) (ENNReal.inv_ne_top.mpr hc0)
    rw [hmeasure] at h
    exact h
  have hcompMP : eLpNorm raw 2 (c • μu) =
      eLpNorm (v : SpatialCoordinates d → ℝ) 2 μr := by
    dsimp [raw, T]
    exact eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable v) hMP
  have hscale : eLpNorm raw 2 (c • μu) =
      c ^ (1 / 2 : ℝ) • eLpNorm raw 2 μu := by
    rw [eLpNorm_smul_measure_of_ne_zero hc0 raw (2 : ℝ≥0∞) μu]
    congr 1
    norm_num
  rw [hscale] at hcompMP
  have hreal := congrArg ENNReal.toReal hcompMP
  rw [smul_eq_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hreal
  have hcReal : c.toReal = volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    dsimp [c]
    rw [ENNReal.toReal_ofReal (pow_nonneg hr.le _),
      SubdiffusiveProcess.centeredCube_volume_real]
  have huNorm : (eLpNorm raw 2 μu).toReal = ‖hmemu.toLp raw‖ :=
    (Lp.norm_toLp raw hmemu).symm
  have hvNorm : (eLpNorm (v : SpatialCoordinates d → ℝ) 2 μr).toReal = ‖v‖ :=
    (Lp.norm_def v).symm
  have hnormvol : Real.sqrt (volume.real
        (centeredCube z r hr : Set (SpatialCoordinates d))) *
        ‖hmemu.toLp raw‖ = ‖v‖ := by
    rw [← hcReal, Real.sqrt_eq_rpow]
    rw [← huNorm, ← hvNorm]
    exact hreal
  have hsqrtpos : 0 < Real.sqrt (volume.real
      (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    Real.sqrt_pos.2 (SubdiffusiveProcess.centeredCube_volume_pos z hr)
  have hnorm : ‖hmemu.toLp raw‖ = ‖v‖ /
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    apply (eq_div_iff hsqrtpos.ne').2
    calc
      ‖hmemu.toLp raw‖ * Real.sqrt (volume.real
          (centeredCube z r hr : Set (SpatialCoordinates d))) =
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) *
            ‖hmemu.toLp raw‖ := by ring
      _ = ‖v‖ := hnormvol
  refine ⟨hmemu.toLp raw, ?_, hnorm.symm⟩
  exact MemLp.coeFn_toLp hmemu

lemma aux_inputs_Interp_interpolation_scale_coefficient
    {d : ℕ} (r : ℝ) (hr : 0 < r) (s : ℝ) :
    ENNReal.ofReal (r ^ d) * (ENNReal.ofReal r ^ ((d : ℝ) + 2 * s))⁻¹ =
      ENNReal.ofReal (r ^ (-2 * s)) := by
  calc
    ENNReal.ofReal (r ^ d) * (ENNReal.ofReal r ^ ((d : ℝ) + 2 * s))⁻¹ =
        ENNReal.ofReal r ^ ((d : ℝ) + (-( (d : ℝ) + 2 * s))) := by
      rw [ENNReal.ofReal_pow hr.le]
      rw [← ENNReal.rpow_natCast (ENNReal.ofReal r) d]
      rw [← ENNReal.rpow_neg (ENNReal.ofReal r) ((d : ℝ) + 2 * s)]
      rw [← ENNReal.rpow_add (d : ℝ) (-((d : ℝ) + 2 * s))
        (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal r ^ (-2 * s) := by congr 1 ; ring
    _ = ENNReal.ofReal (r ^ (-2 * s)) := ENNReal.ofReal_rpow_of_pos hr

lemma aux_inputs_Interp_interpolation_fractional_integral_scale
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1) (f : SpatialCoordinates d → ℝ) :
    (∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal ((f x - f y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ))) =
      ENNReal.ofReal (r ^ d) * ENNReal.ofReal (r ^ d) *
        (ENNReal.ofReal r ^ ((d : ℝ) + 2 * (s : ℝ)))⁻¹ *
          (∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)),
            ∫⁻ y in (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d)),
              ENNReal.ofReal
                  ((f (cubeDilation z 0 r x) - f (cubeDilation z 0 r y)) ^ 2) /
                (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                  ((d : ℝ) + 2 * (s : ℝ))) := by
  let h1 : (0 : ℝ) < 1 := by norm_num
  let U : Set (SpatialCoordinates d) := centeredCube (0 : SpatialCoordinates d) 1 h1
  let Q : Set (SpatialCoordinates d) := centeredCube z r hr
  let T : SpatialCoordinates d → SpatialCoordinates d := cubeDilation z 0 r
  let α : ℝ := (d : ℝ) + 2 * (s : ℝ)
  let R : ℝ≥0∞ := ENNReal.ofReal (r ^ d)
  let D : ℝ≥0∞ := ENNReal.ofReal r ^ α
  let G : SpatialCoordinates d → SpatialCoordinates d → ℝ≥0∞ := fun x y =>
    ENNReal.ofReal ((f x - f y) ^ 2) /
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ α
  let GU : SpatialCoordinates d → SpatialCoordinates d → ℝ≥0∞ := fun x y =>
    ENNReal.ofReal ((f (T x) - f (T y)) ^ 2) /
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ α
  have hα : 0 < α := by
    dsimp [α]
    have : (0 : ℝ) < (s : ℝ) := s.2.1
    positivity
  have hRpos : 0 < R := by
    dsimp [R]
    exact ENNReal.ofReal_pos.mpr (pow_pos hr d)
  have hRtop : R ≠ ⊤ := by
    dsimp [R]
    exact ENNReal.ofReal_ne_top
  have hDpos : 0 < D := by
    apply pos_iff_ne_zero.mpr
    dsimp [D]
    rw [ENNReal.rpow_eq_zero_iff_of_pos hα]
    exact ENNReal.ofReal_ne_zero_iff.mpr hr
  have hDtop : D ≠ ⊤ := by
    dsimp [D]
    apply ENNReal.rpow_ne_top_of_nonneg hα.le
    exact ENNReal.ofReal_ne_top
  have hdist (x y : SpatialCoordinates d) :
      Real.sqrt (∑ j : Fin d, (T x j - T y j) ^ 2) =
        r * Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
    simpa [T] using _root_.SubdiffusiveProcess.EllipticRegularity.sqrt_sum_sq_cubeDilation z (0 : SpatialCoordinates d) hr x y
  have hden (x y : SpatialCoordinates d) :
      (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (T x j - T y j) ^ 2))) ^ α =
        D * (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ α := by
    rw [hdist, ENNReal.ofReal_mul hr.le,
      ENNReal.mul_rpow_of_nonneg (ENNReal.ofReal r)
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) hα.le]
  have hpoint (x y : SpatialCoordinates d) :
      G (T x) (T y) = D⁻¹ * GU x y := by
    dsimp [G, GU]
    rw [hden]
    have hdiv : ∀ a b : ℝ≥0∞,
        a / (D * b) = D⁻¹ * (a / b) := by
      intro a b
      simp only [div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl hDpos.ne') (Or.inl hDtop)]
      ac_rfl
    exact hdiv _ _
  have hinner (x : SpatialCoordinates d) :
      (∫⁻ y in Q, G (T x) y) = R * (∫⁻ y in U, G (T x) (T y)) := by
    simpa [Q, U, R, T] using
      _root_.SubdiffusiveProcess.EllipticRegularity.lintegral_centeredCube_cubeDilation z 0 hr h1 (G (T x))
  have houter :=
    _root_.SubdiffusiveProcess.EllipticRegularity.lintegral_centeredCube_cubeDilation z 0 hr h1
      (fun x => ∫⁻ y in Q, G x y)
  have hchange :
      (∫⁻ x in Q, ∫⁻ y in Q, G x y) =
      R * (∫⁻ x in U, ∫⁻ y in Q, G (T x) y) := by
    simpa [Q, U, R, T] using houter
  have hdouble :
      (∫⁻ x in U, ∫⁻ y in U, G (T x) (T y)) =
        D⁻¹ * (∫⁻ x in U, ∫⁻ y in U, GU x y) := by
    calc
      (∫⁻ x in U, ∫⁻ y in U, G (T x) (T y)) =
          ∫⁻ x in U, ∫⁻ y in U, D⁻¹ * GU x y := by
        apply lintegral_congr_ae (μ := volume.restrict U)
        filter_upwards with x
        apply lintegral_congr_ae (μ := volume.restrict U)
        filter_upwards with y
        exact hpoint x y
      _ = ∫⁻ x in U, D⁻¹ * (∫⁻ y in U, GU x y) := by
        apply lintegral_congr_ae (μ := volume.restrict U)
        filter_upwards with x
        rw [lintegral_const_mul' D⁻¹ _ (ENNReal.inv_ne_top.mpr hDpos.ne')]
      _ = D⁻¹ * (∫⁻ x in U, ∫⁻ y in U, GU x y) := by
        rw [lintegral_const_mul' D⁻¹ _ (ENNReal.inv_ne_top.mpr hDpos.ne')]
  
  rw [hchange]
  calc
    R * (∫⁻ x in U, ∫⁻ y in Q, G (T x) y) =
        R * (∫⁻ x in U, R * (∫⁻ y in U, G (T x) (T y))) := by
          apply congrArg (fun q : ℝ≥0∞ => R * q)
          apply lintegral_congr_ae
          filter_upwards with x
          exact hinner x
    _ = R * R * (∫⁻ x in U, ∫⁻ y in U, G (T x) (T y)) := by
      rw [lintegral_const_mul' R _ hRtop]
      ring
    _ = R * R * (D⁻¹ *
          (∫⁻ x in U, ∫⁻ y in U, GU x y)) := by
      rw [hdouble]
    _ = R * R * D⁻¹ *
          (∫⁻ x in U, ∫⁻ y in U, GU x y) := by
      ring

lemma aux_inputs_Interp_interpolation_seminorm_scale
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1)
    (v : DomainL2 (centeredCube z r hr))
    (u : DomainL2 (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)))
    (hcomp : u =ᵐ[volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d))]
      (fun x => (v : SpatialCoordinates d → ℝ) (cubeDilation z 0 r x))) :
    cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) =
      ENNReal.ofReal (r ^ (-(s : ℝ))) *
        cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 (by norm_num) s
          (fun _ : Fin 1 => u) := by
  let h1 : (0 : ℝ) < 1 := by norm_num
  let U : Set (SpatialCoordinates d) := centeredCube (0 : SpatialCoordinates d) 1 h1
  let Q : Set (SpatialCoordinates d) := centeredCube z r hr
  let T : SpatialCoordinates d → SpatialCoordinates d := cubeDilation z 0 r
  let R : ℝ≥0∞ := ENNReal.ofReal (r ^ d)
  let D : ℝ≥0∞ := ENNReal.ofReal r ^ ((d : ℝ) + 2 * (s : ℝ))
  have hIraw := aux_inputs_Interp_interpolation_fractional_integral_scale
    hd z r hr s (fun x => (v : SpatialCoordinates d → ℝ) x)
  have hI :
      (∫⁻ x in Q, ∫⁻ y in Q,
        ENNReal.ofReal (∑ i : Fin 1, (v x - v y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ))) =
        R * R * D⁻¹ *
          (∫⁻ x in U, ∫⁻ y in U,
            ENNReal.ofReal (∑ i : Fin 1,
                ((v : SpatialCoordinates d → ℝ) (T x) -
                  (v : SpatialCoordinates d → ℝ) (T y)) ^ 2) /
              (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                ((d : ℝ) + 2 * (s : ℝ))) := by
    simpa [Q, U, R, D, T] using hIraw
  have hUnitCong :
      (∫⁻ x in U, ∫⁻ y in U,
        ENNReal.ofReal (∑ i : Fin 1,
            ((v : SpatialCoordinates d → ℝ) (T x) -
              (v : SpatialCoordinates d → ℝ) (T y)) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ))) =
      (∫⁻ x in U, ∫⁻ y in U,
        ENNReal.ofReal (∑ i : Fin 1, ((u : SpatialCoordinates d → ℝ) x -
            (u : SpatialCoordinates d → ℝ) y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ))) := by
    have h := SubdiffusiveProcess.fractional_square_integral_congr_ae
      (fun _ : Fin 1 => (u : SpatialCoordinates d → ℝ))
      (fun _ : Fin 1 => fun x => (v : SpatialCoordinates d → ℝ) (T x))
      (by
        intro i
        fin_cases i
        exact hcomp)
      (s : ℝ)
    simpa [U, T] using h.symm
  have hVolQ : volume (Q : Set (SpatialCoordinates d)) = R := by
    dsimp [Q, R]
    rw [SubdiffusiveProcess.centeredCube_volume z hr]
  have hVolU : volume U = 1 := by
    dsimp [U]
    rw [SubdiffusiveProcess.centeredCube_volume (0 : SpatialCoordinates d) h1]
    simp
  have hRpos : 0 < R := by
    dsimp [R]
    exact ENNReal.ofReal_pos.mpr (pow_pos hr d)
  have hRtop : R ≠ ⊤ := by
    dsimp [R]
    exact ENNReal.ofReal_ne_top
  have hcoeff : R * D⁻¹ = ENNReal.ofReal (r ^ (-2 * (s : ℝ))) := by
    simpa [R, D] using
      (aux_inputs_Interp_interpolation_scale_coefficient r hr (s : ℝ))
  let Iunit : ℝ≥0∞ :=
    ∫⁻ x in U, ∫⁻ y in U,
      ENNReal.ofReal (∑ i : Fin 1,
          ((u : SpatialCoordinates d → ℝ) x - (u : SpatialCoordinates d → ℝ) y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (s : ℝ))
  let Bbig : ℝ≥0∞ := (ENNReal.ofReal (s : ℝ) / volume (Q : Set (SpatialCoordinates d))) *
    (∫⁻ x in Q, ∫⁻ y in Q,
      ENNReal.ofReal (∑ i : Fin 1, (v x - v y) ^ 2) /
        (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
          ((d : ℝ) + 2 * (s : ℝ)))
  let Bunit : ℝ≥0∞ :=
    (ENNReal.ofReal (s : ℝ) / volume U) * Iunit
  have hbase : Bbig = ENNReal.ofReal (r ^ (-2 * (s : ℝ))) * Bunit := by
    dsimp [Bbig, Bunit, Iunit]
    rw [hVolQ, hVolU, hI, hUnitCong]
    rw [div_eq_mul_inv]
    calc
      ENNReal.ofReal (s : ℝ) * R⁻¹ * (R * R * D⁻¹ *
          (∫⁻ x in U, ∫⁻ y in U,
            ENNReal.ofReal (∑ i : Fin 1,
                ((u : SpatialCoordinates d → ℝ) x -
                  (u : SpatialCoordinates d → ℝ) y) ^ 2) /
              (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
                ((d : ℝ) + 2 * (s : ℝ)))) =
        ENNReal.ofReal (s : ℝ) * (R⁻¹ * R) * (R * D⁻¹) * Iunit := by
          simp only [Iunit]
          ac_rfl
      _ = ENNReal.ofReal (s : ℝ) * (R * D⁻¹) * Iunit := by
        rw [ENNReal.inv_mul_cancel hRpos.ne' hRtop]
        simp
      _ = ENNReal.ofReal (r ^ (-2 * (s : ℝ))) *
          (ENNReal.ofReal (s : ℝ) * (1 : ℝ≥0∞)⁻¹ * Iunit) := by
            rw [hcoeff]
            simp [mul_assoc, mul_left_comm, mul_comm]
  have hsqrt :
      ENNReal.ofReal (r ^ (-2 * (s : ℝ))) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (r ^ (-(s : ℝ))) := by
    rw [← ENNReal.ofReal_rpow_of_pos hr, ← ENNReal.rpow_mul,
      ENNReal.ofReal_rpow_of_pos hr]
    congr 1
    ring
  change Bbig ^ (1 / 2 : ℝ) =
    ENNReal.ofReal (r ^ (-(s : ℝ))) * Bunit ^ (1 / 2 : ℝ)
  rw [hbase, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hsqrt]

lemma aux_inputs_Interp_interpolation_norm_scale
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : Set.Ioo (0 : ℝ) 1)
    (w : CubeFractionalL2 (k := 1) hd z r hr s)
    (u : CubeFractionalL2 (k := 1) hd (0 : SpatialCoordinates d) 1 (by norm_num) s)
    (hcomp : (u.val 0 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) : Set (SpatialCoordinates d))]
      (fun x => (w.val 0 : SpatialCoordinates d → ℝ) (cubeDilation z 0 r x)))
    (hnorm : ‖w.val 0‖ /
      Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) = ‖u.val 0‖) :
    cubeFractionalL2Norm hd z r hr s w =
      r ^ (-(s : ℝ)) *
        cubeFractionalL2Norm hd (0 : SpatialCoordinates d) 1 (by norm_num) s
          u := by
  have hwval : w.val = fun _ : Fin 1 => w.val 0 := by
    funext i
    fin_cases i
    rfl
  have huval : u.val = fun _ : Fin 1 => u.val 0 := by
    funext i
    fin_cases i
    rfl
  have hsem := aux_inputs_Interp_interpolation_seminorm_scale
    hd z r hr s (w.val 0) (u.val 0) hcomp
  have hsemReal :
      (cubeFractionalL2Seminorm hd z r hr s w.val).toReal =
        r ^ (-(s : ℝ)) *
          (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 (by norm_num) s
            u.val).toReal := by
    calc
      (cubeFractionalL2Seminorm hd z r hr s w.val).toReal =
          (cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => w.val 0)).toReal := by
            rw [hwval]
      _ = r ^ (-(s : ℝ)) *
          (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 (by norm_num) s
            (fun _ : Fin 1 => u.val 0)).toReal := by
              rw [hsem, ENNReal.toReal_mul,
                ENNReal.toReal_ofReal (Real.rpow_nonneg hr.le _)]
      _ = r ^ (-(s : ℝ)) *
          (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 (by norm_num) s
            u.val).toReal := by rw [huval]
  unfold SubdiffusiveProcess.cubeFractionalL2Norm
  rw [hsemReal]
  rw [hwval, huval]
  simp only [Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm]
  rw [SubdiffusiveProcess.centeredCube_volume_real (0 : SpatialCoordinates d) (by norm_num)]
  simp only [one_pow, Real.sqrt_one, Real.one_rpow, div_one, one_mul]
  ring

theorem inputs_Interp_interpolation (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (threeQuarters : Set.Ioo (0 : ℝ) 1) (hs : (threeQuarters : ℝ) = 3 / 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (wHalf : CubeFractionalL2 (k := 1) hd z r hr halfFractionalOrder)
        (wThree : CubeFractionalL2 (k := 1) hd z r hr threeQuarters),
        wThree.val 0 = wHalf.val 0 →
        cubeFractionalL2Norm hd z r hr halfFractionalOrder wHalf ≤
          C * (‖wHalf.val 0‖ / Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^ (1 / 3 : ℝ) *
            cubeFractionalL2Norm hd z r hr threeQuarters wThree ^ (2 / 3 : ℝ) := by
  classical
  have hts : (halfFractionalOrder : ℝ) < (threeQuarters : ℝ) := by
    rw [hs]
    norm_num [SubdiffusiveProcess.halfFractionalOrder]
  obtain ⟨K, hK, hinterp⟩ :=
    _root_.SubdiffusiveProcess.Paper.inputs_classical_e4_interpolation d hd threeQuarters halfFractionalOrder hts
  let ch : ℝ := r ^ (-(halfFractionalOrder : ℝ))
  let ct : ℝ := r ^ (-(threeQuarters : ℝ))
  let mh : ℝ := max 1 ch
  let mt : ℝ := max 1 (ct⁻¹)
  let C : ℝ := 2 * mh * K * mt ^ (2 / 3 : ℝ)
  have hch : 0 < ch := by dsimp [ch]; positivity
  have hct : 0 < ct := by dsimp [ct]; positivity
  have hC : 0 < C := by
    dsimp [C, mh, mt]
    positivity
  have hpow1 : 1 - (halfFractionalOrder : ℝ) / (threeQuarters : ℝ) = 1 / 3 := by
    rw [hs]
    norm_num [SubdiffusiveProcess.halfFractionalOrder]
  have hpow2 : (halfFractionalOrder : ℝ) / (threeQuarters : ℝ) = 2 / 3 := by
    rw [hs]
    norm_num [SubdiffusiveProcess.halfFractionalOrder]
  refine ⟨C, hC, ?_⟩
  intro wHalf wThree hEq
  by_cases hr1 : r ≤ 1
  · have htsfinite : cubeFractionalL2Seminorm hd z r hr threeQuarters
        (fun _ : Fin 1 => wThree.val 0) < ⊤ := by
      have heq : (fun _ : Fin 1 => wThree.val 0) = wThree.val := by
        funext i
        exact congrArg wThree.val (Subsingleton.elim 0 i)
      rw [heq]
      exact wThree.property
    have hI := hinterp z r hr hr1 (wThree.val 0) htsfinite
    rw [hpow1, hpow2] at hI
    let vol : ℝ := volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
    let b : ℝ := ‖wThree.val 0‖ / Real.sqrt vol
    let ah : ℝ := (cubeFractionalL2Seminorm hd z r hr halfFractionalOrder
      (fun _ : Fin 1 => wThree.val 0)).toReal
    let athree : ℝ := (cubeFractionalL2Seminorm hd z r hr threeQuarters
      (fun _ : Fin 1 => wThree.val 0)).toReal
    let Nhalf : ℝ := Real.sqrt (cubeFractionalSqNorm hd z r hr halfFractionalOrder
      (wThree.val 0))
    let Nthree : ℝ := Real.sqrt (cubeFractionalSqNorm hd z r hr threeQuarters
      (wThree.val 0))
    have hah : 0 ≤ ah := ENNReal.toReal_nonneg
    have hat : 0 ≤ athree := ENNReal.toReal_nonneg
    have hb : 0 ≤ b := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    have hvolpos : 0 < vol := by
      dsimp [vol]
      exact SubdiffusiveProcess.centeredCube_volume_pos z hr
    have hsqH : cubeFractionalSqNorm hd z r hr halfFractionalOrder
        (wThree.val 0) = ah ^ 2 + b ^ 2 := by
      dsimp [ah, b, vol]
      simp [_root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm,
        _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalVecSqNorm,
        _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalVecSeminormSq,
        SubdiffusiveProcess.cubeFractionalL2Seminorm]
      field_simp
      rw [Real.sq_sqrt (le_of_lt (SubdiffusiveProcess.centeredCube_volume_pos z hr))]
    have hsqT : cubeFractionalSqNorm hd z r hr threeQuarters
        (wThree.val 0) = athree ^ 2 + b ^ 2 := by
      dsimp [athree, b, vol]
      simp [_root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalSqNorm,
        _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalVecSqNorm,
        _root_.SubdiffusiveProcess.EllipticRegularity.cubeFractionalVecSeminormSq,
        SubdiffusiveProcess.cubeFractionalL2Seminorm]
      field_simp
      rw [Real.sq_sqrt (le_of_lt (SubdiffusiveProcess.centeredCube_volume_pos z hr))]
    have hNormH : cubeFractionalL2Norm hd z r hr halfFractionalOrder wHalf =
        ah + ch * b := by
      have hval : wHalf.val = fun _ : Fin 1 => wThree.val 0 := by
        funext i
        fin_cases i
        exact hEq.symm
      unfold SubdiffusiveProcess.cubeFractionalL2Norm
      rw [hval, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]
    have hNormT : cubeFractionalL2Norm hd z r hr threeQuarters wThree =
        athree + ct * b := by
      have hval : wThree.val = fun _ : Fin 1 => wThree.val 0 := by
        funext i
        fin_cases i
        rfl
      unfold SubdiffusiveProcess.cubeFractionalL2Norm
      rw [hval, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]
    have hIalg : Real.sqrt (ah ^ 2 + b ^ 2) ≤
        K * b ^ (1 / 3 : ℝ) * Real.sqrt (athree ^ 2 + b ^ 2) ^ (2 / 3 : ℝ) := by
      rw [← hsqH, ← hsqT]
      dsimp only [b, vol]
      exact hI.2
    have hconv := aux_inputs_Interp_interpolation_norm_conversion
      ah athree b ch ct K hah hat hb hch hct hK.le hIalg
    have hratio : ‖wHalf.val 0‖ / Real.sqrt vol = b := by
      simp [b, hEq]
    calc
      cubeFractionalL2Norm hd z r hr halfFractionalOrder wHalf = ah + ch * b := hNormH
      _ ≤ (2 * max 1 ch * K * (max 1 (ct⁻¹)) ^ (2 / 3 : ℝ)) *
          b ^ (1 / 3 : ℝ) * (athree + ct * b) ^ (2 / 3 : ℝ) := hconv
      _ = C * (‖wHalf.val 0‖ / Real.sqrt vol) ^ (1 / 3 : ℝ) *
          cubeFractionalL2Norm hd z r hr threeQuarters wThree ^ (2 / 3 : ℝ) := by
        rw [show C = 2 * max 1 ch * K * (max 1 (ct⁻¹)) ^ (2 / 3 : ℝ) by rfl,
          hratio, hNormT]
  · have hrgt1 : 1 < r := lt_of_not_ge hr1
    let h1 : (0 : ℝ) < 1 := by norm_num
    let U : Opens (SpatialCoordinates d) := centeredCube (0 : SpatialCoordinates d) 1 h1
    obtain ⟨u, hcomp, hnorm⟩ :=
      aux_inputs_Interp_interpolation_pullback_l2 z r hr (wThree.val 0)
    have hvalThree : wThree.val = fun _ : Fin 1 => wThree.val 0 := by
      funext i
      fin_cases i
      rfl
    have hvalHalf : wHalf.val = fun _ : Fin 1 => wHalf.val 0 := by
      funext i
      fin_cases i
      rfl
    have hfiniteBig : cubeFractionalL2Seminorm hd z r hr threeQuarters
        (fun _ : Fin 1 => wThree.val 0) < ⊤ := by
      rw [← hvalThree]
      exact wThree.property
    have hscaleThree := aux_inputs_Interp_interpolation_seminorm_scale
      hd z r hr threeQuarters (wThree.val 0) u hcomp
    have hfiniteUnit : cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 h1
        threeQuarters (fun _ : Fin 1 => u) < ⊤ := by
      rw [hscaleThree] at hfiniteBig
      apply ENNReal.lt_top_of_mul_ne_top_right hfiniteBig.ne
      exact ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hr _)
    have hUnitInterp := hinterp (0 : SpatialCoordinates d) 1 h1 le_rfl u hfiniteUnit
    rw [hpow1, hpow2] at hUnitInterp
    have hfiniteUnitHalf : cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 h1
        halfFractionalOrder (fun _ : Fin 1 => u) < ⊤ := by
      simpa using hUnitInterp.1
    let uHalf : CubeFractionalL2 (k := 1) hd (0 : SpatialCoordinates d) 1 h1
        halfFractionalOrder := ⟨fun _ : Fin 1 => u, hfiniteUnitHalf⟩
    let uThree : CubeFractionalL2 (k := 1) hd (0 : SpatialCoordinates d) 1 h1
        threeQuarters := ⟨fun _ : Fin 1 => u, hfiniteUnit⟩
    have hcompHalf :
        (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))]
          (fun x => (wHalf.val 0 : SpatialCoordinates d → ℝ) (cubeDilation z 0 r x)) := by
      simpa [hEq, U, h1] using hcomp
    have hnormEq : ‖wThree.val 0‖ = ‖wHalf.val 0‖ := congrArg norm hEq
    have hnormHalf : ‖wHalf.val 0‖ /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) =
          ‖uHalf.val 0‖ := by
      calc
        ‖wHalf.val 0‖ /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) =
          ‖wThree.val 0‖ /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
              rw [← hnormEq]
        _ = ‖u‖ := hnorm
        _ = ‖uHalf.val 0‖ := rfl
    have hnormThree : ‖wThree.val 0‖ /
        Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) =
          ‖uThree.val 0‖ := by
      simpa [uThree] using hnorm
    have hscaleHalfNorm := aux_inputs_Interp_interpolation_norm_scale
      hd z r hr halfFractionalOrder wHalf uHalf hcompHalf hnormHalf
    have hscaleThreeNorm := aux_inputs_Interp_interpolation_norm_scale
      hd z r hr threeQuarters wThree uThree hcomp hnormThree
    let volU : ℝ := volume.real (U : Set (SpatialCoordinates d))
    let b : ℝ := ‖u‖ / Real.sqrt volU
    let ah : ℝ := (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 h1
      halfFractionalOrder (fun _ : Fin 1 => u)).toReal
    let athree : ℝ := (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 h1
      threeQuarters (fun _ : Fin 1 => u)).toReal
    have hb : 0 ≤ b := by
      dsimp [b]
      exact div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    have hah : 0 ≤ ah := ENNReal.toReal_nonneg
    have hat : 0 ≤ athree := ENNReal.toReal_nonneg
    have hvolpos : 0 < volU := by
      dsimp [volU, U]
      exact SubdiffusiveProcess.centeredCube_volume_pos (0 : SpatialCoordinates d) h1
    have hsqH : cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 h1
        halfFractionalOrder u = ah ^ 2 + b ^ 2 := by
      change (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 h1
          halfFractionalOrder (fun _ : Fin 1 => u)).toReal ^ 2 +
        (∑ i : Fin 1, ‖(fun _ : Fin 1 => u) i‖ ^ 2) /
          volume.real (U : Set (SpatialCoordinates d)) = ah ^ 2 + b ^ 2
      dsimp [ah, b, volU]
      simp only [Fin.sum_univ_one]
      rw [div_pow, Real.sq_sqrt (le_of_lt hvolpos)]
    have hsqT : cubeFractionalSqNorm hd (0 : SpatialCoordinates d) 1 h1
        threeQuarters u = athree ^ 2 + b ^ 2 := by
      change (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 h1
          threeQuarters (fun _ : Fin 1 => u)).toReal ^ 2 +
        (∑ i : Fin 1, ‖(fun _ : Fin 1 => u) i‖ ^ 2) /
          volume.real (U : Set (SpatialCoordinates d)) = athree ^ 2 + b ^ 2
      dsimp [athree, b, volU]
      simp only [Fin.sum_univ_one]
      rw [div_pow, Real.sq_sqrt (le_of_lt hvolpos)]
    have hIalg : Real.sqrt (ah ^ 2 + b ^ 2) ≤
        K * b ^ (1 / 3 : ℝ) * Real.sqrt (athree ^ 2 + b ^ 2) ^ (2 / 3 : ℝ) := by
      rw [← hsqH, ← hsqT]
      dsimp only [b, volU]
      exact hUnitInterp.2
    have hconv := aux_inputs_Interp_interpolation_norm_conversion
      ah athree b 1 1 K hah hat hb (by norm_num) (by norm_num) hK.le hIalg
    have hNormUnitH : cubeFractionalL2Norm hd (0 : SpatialCoordinates d) 1 h1
        halfFractionalOrder uHalf = ah + b := by
      have huv : uHalf.val = fun _ : Fin 1 => u := by
        funext i
        fin_cases i
        rfl
      unfold SubdiffusiveProcess.cubeFractionalL2Norm
      rw [huv, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]
      change (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 h1
          halfFractionalOrder (fun _ : Fin 1 => u)).toReal +
        (1 : ℝ) ^ (-(halfFractionalOrder : ℝ)) *
          (‖u‖ / Real.sqrt (volume.real (U : Set (SpatialCoordinates d)))) = ah + b
      dsimp only [ah, b]
      rw [Real.one_rpow, one_mul]
    have hNormUnitT : cubeFractionalL2Norm hd (0 : SpatialCoordinates d) 1 h1
        threeQuarters uThree = athree + b := by
      have huv : uThree.val = fun _ : Fin 1 => u := by
        funext i
        fin_cases i
        rfl
      unfold SubdiffusiveProcess.cubeFractionalL2Norm
      rw [huv, Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)]
      change (cubeFractionalL2Seminorm hd (0 : SpatialCoordinates d) 1 h1
          threeQuarters (fun _ : Fin 1 => u)).toReal +
        (1 : ℝ) ^ (-(threeQuarters : ℝ)) *
          (‖u‖ / Real.sqrt (volume.real (U : Set (SpatialCoordinates d)))) = athree + b
      dsimp only [athree, b]
      rw [Real.one_rpow, one_mul]
    have hUnitBound : cubeFractionalL2Norm hd (0 : SpatialCoordinates d) 1 h1
        halfFractionalOrder uHalf ≤
          (2 * K) * b ^ (1 / 3 : ℝ) *
            cubeFractionalL2Norm hd (0 : SpatialCoordinates d) 1 h1 threeQuarters
              uThree ^ (2 / 3 : ℝ) := by
      rw [hNormUnitH, hNormUnitT]
      simpa using hconv
    have hmh1 : 1 ≤ mh := le_max_left _ _
    have hmt1 : 1 ≤ mt := le_max_left _ _
    have hmtpow : 1 ≤ mt ^ (2 / 3 : ℝ) := by
      calc
        (1 : ℝ) = 1 ^ (2 / 3 : ℝ) := by simp
        _ ≤ mt ^ (2 / 3 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) hmt1 (by norm_num)
    have hmhnonneg : 0 ≤ mh := le_trans (by norm_num) hmh1
    have hconstnonneg : 0 ≤ 2 * mh * K :=
      mul_nonneg (mul_nonneg (by norm_num) hmhnonneg) hK.le
    have hCsmall : 2 * K ≤ C := by
      dsimp [C]
      calc
        2 * K = (2 * K) * 1 := by ring
        _ ≤ (2 * K) * mh := mul_le_mul_of_nonneg_left hmh1 (by positivity)
        _ = 2 * mh * K := by ring
        _ ≤ (2 * mh * K) * mt ^ (2 / 3 : ℝ) := by
          calc
            2 * mh * K = (2 * mh * K) * 1 := by ring
            _ ≤ (2 * mh * K) * mt ^ (2 / 3 : ℝ) :=
              mul_le_mul_of_nonneg_left hmtpow hconstnonneg
        _ = 2 * mh * K * mt ^ (2 / 3 : ℝ) := by ring
    have hvolUreal : volU = 1 := by
      dsimp [volU, U]
      rw [SubdiffusiveProcess.centeredCube_volume_real]
      norm_num
    have hratio :
        ‖wHalf.val 0‖ /
          Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) = b := by
      calc
        ‖wHalf.val 0‖ /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) =
          ‖wThree.val 0‖ /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d))) := by
              rw [← hnormEq]
        _ = ‖u‖ := hnorm
        _ = b := by
          dsimp [b]
          rw [hvolUreal, Real.sqrt_one, div_one]
    have hpowScale :
        (r ^ (-(threeQuarters : ℝ))) ^ (2 / 3 : ℝ) =
          r ^ (-(halfFractionalOrder : ℝ)) := by
      have hexp : (-(threeQuarters : ℝ)) * (2 / 3 : ℝ) =
          -(halfFractionalOrder : ℝ) := by
        rw [hs]
        norm_num [SubdiffusiveProcess.halfFractionalOrder]
      calc
        (r ^ (-(threeQuarters : ℝ))) ^ (2 / 3 : ℝ) =
            r ^ ((-(threeQuarters : ℝ)) * (2 / 3 : ℝ)) :=
              (Real.rpow_mul hr.le _ _).symm
        _ = r ^ (-(halfFractionalOrder : ℝ)) := by rw [hexp]
    have hUnitNormTnonneg : 0 ≤ cubeFractionalL2Norm
        hd (0 : SpatialCoordinates d) 1 h1 threeQuarters uThree := by
      unfold SubdiffusiveProcess.cubeFractionalL2Norm
      apply add_nonneg
      · exact ENNReal.toReal_nonneg
      · apply mul_nonneg
        · exact Real.rpow_nonneg (by norm_num) _
        · exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hbigThreePow :
        cubeFractionalL2Norm hd z r hr threeQuarters wThree ^ (2 / 3 : ℝ) =
          r ^ (-(halfFractionalOrder : ℝ)) *
            cubeFractionalL2Norm hd (0 : SpatialCoordinates d) 1 h1 threeQuarters
              uThree ^ (2 / 3 : ℝ) := by
      rw [hscaleThreeNorm,
        Real.mul_rpow (Real.rpow_nonneg hr.le _) hUnitNormTnonneg, hpowScale]
    let hfactor : ℝ := b ^ (1 / 3 : ℝ) *
      (r ^ (-(halfFractionalOrder : ℝ)) *
        cubeFractionalL2Norm hd (0 : SpatialCoordinates d) 1 h1 threeQuarters
          uThree ^ (2 / 3 : ℝ))
    have hfactorNonneg : 0 ≤ hfactor := by
      dsimp only [hfactor]
      apply mul_nonneg
      · exact Real.rpow_nonneg hb _
      · apply mul_nonneg
        · exact Real.rpow_nonneg hr.le _
        · exact Real.rpow_nonneg hUnitNormTnonneg _
    calc
      cubeFractionalL2Norm hd z r hr halfFractionalOrder wHalf =
          r ^ (-(halfFractionalOrder : ℝ)) *
            cubeFractionalL2Norm hd (0 : SpatialCoordinates d) 1 h1 halfFractionalOrder
              uHalf := hscaleHalfNorm
      _ ≤ r ^ (-(halfFractionalOrder : ℝ)) *
          ((2 * K) * b ^ (1 / 3 : ℝ) *
            cubeFractionalL2Norm hd (0 : SpatialCoordinates d) 1 h1 threeQuarters
              uThree ^ (2 / 3 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hUnitBound (Real.rpow_nonneg hr.le _)
      _ = (2 * K) * b ^ (1 / 3 : ℝ) *
          (r ^ (-(halfFractionalOrder : ℝ)) *
            cubeFractionalL2Norm hd (0 : SpatialCoordinates d) 1 h1 threeQuarters
              uThree ^ (2 / 3 : ℝ)) := by ring
      _ ≤ C * b ^ (1 / 3 : ℝ) *
          (r ^ (-(halfFractionalOrder : ℝ)) *
            cubeFractionalL2Norm hd (0 : SpatialCoordinates d) 1 h1 threeQuarters
              uThree ^ (2 / 3 : ℝ)) := by
            calc
                (2 * K) * b ^ (1 / 3 : ℝ) *
                  (r ^ (-(halfFractionalOrder : ℝ)) *
                    cubeFractionalL2Norm hd (0 : SpatialCoordinates d) 1 h1 threeQuarters
                      uThree ^ (2 / 3 : ℝ)) =
                (2 * K) * hfactor := by dsimp only [hfactor]; ring
              _ ≤ C * hfactor := mul_le_mul_of_nonneg_right hCsmall hfactorNonneg
              _ = C * b ^ (1 / 3 : ℝ) *
                  (r ^ (-(halfFractionalOrder : ℝ)) *
                    cubeFractionalL2Norm hd (0 : SpatialCoordinates d) 1 h1 threeQuarters
                      uThree ^ (2 / 3 : ℝ)) := by dsimp only [hfactor]; ring
      _ = C *
          (‖wHalf.val 0‖ /
            Real.sqrt (volume.real (centeredCube z r hr : Set (SpatialCoordinates d)))) ^
              (1 / 3 : ℝ) *
          cubeFractionalL2Norm hd z r hr threeQuarters wThree ^ (2 / 3 : ℝ) := by
            rw [← hratio, ← hbigThreePow]

end SubdiffusiveProcess.Paper


