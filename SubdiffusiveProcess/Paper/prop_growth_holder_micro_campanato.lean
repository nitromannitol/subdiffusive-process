module

public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Paper.aux_coercivity_dilation_mean_zero_pullback
public import SubdiffusiveProcess.Paper.aux_coercivity_dilation_integral_scaling
public import Mathlib.Tactic
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.ResponseMoments.LocalEnergyAux
public import SubdiffusiveProcess.Sobolev.LocalEnergy
public import SubdiffusiveProcess.HolderMicroAbsorption
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import SubdiffusiveProcess.Paper.prop_growth_energy_assembly

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-! ###  `MicroPoincare` -/
/-- The square of the norm of an `L²` class on a domain is the integral of its square. -/
theorem aux_prop_growth_holder_micro_campanato_norm_sq {d : ℕ}
    {Ω : Opens (SpatialCoordinates d)} (f : DomainL2 Ω) :
    ‖f‖ ^ 2 = ∫ y in (Ω : Set (SpatialCoordinates d)), (f y) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with y
  simp only [RCLike.inner_apply, conj_trivial, sq]

/-- **Scaled mean-zero Poincaré on cubes.**  One constant, depending only on `d`, for every
centre and every side. -/
theorem aux_prop_growth_holder_micro_campanato_scaled_poincare (d : ℕ) (hd : 1 ≤ d) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (v : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        Cp * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).2 i y) ^ 2 := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨K, hK⟩ := (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    (centeredCube (0 : SpatialCoordinates d) 1 one_pos)
    (isOpenBoundedConvexDomain_centeredCube 0 one_pos)).2
  refine ⟨(K : ℝ) ^ 2, sq_nonneg _, ?_⟩
  intro c s hs v
  obtain ⟨w, hw1, hw2⟩ := aux_coercivity_dilation_mean_zero_pullback d c s hs one_pos v
  set U : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) with hU
  have hP2 : ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ^ 2 ≤
      (K : ℝ) ^ 2 * ∑ i : Fin d,
        ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).2 i‖ ^ 2 := by
    have h0 : 0 ≤ ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ :=
      norm_nonneg _
    have h := pow_le_pow_left₀ h0 (hK w) 2
    rw [mul_pow] at h
    have hg : ‖subspaceGradient
        (meanZeroSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) w‖ ^ 2 =
        ∑ i : Fin d,
          ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).2 i‖ ^ 2 :=
      sobolevGradient_norm_sq _
    rwa [hg] at h
  -- change of variables for the value
  have hval : ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
      ((v : SobolevData (centeredCube c s hs)).1 y) ^ 2 =
      s ^ d * ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ^ 2 := by
    rw [aux_coercivity_dilation_integral_scaling d c s hs one_pos
      (fun y => ((v : SobolevData (centeredCube c s hs)).1 y) ^ 2)
      ((Lp.aestronglyMeasurable _).pow 2), aux_prop_growth_holder_micro_campanato_norm_sq]
    congr 1
    apply integral_congr_ae
    filter_upwards [hw1] with x hx
    rw [hx]
  -- change of variables for each gradient coordinate
  have hgrad : ∀ i : Fin d,
      ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).2 i‖ ^ 2 =
      s ^ 2 * ∫ x in U, ((v : SobolevData (centeredCube c s hs)).2 i
        (cubeDilation c 0 s x)) ^ 2 := by
    intro i
    rw [aux_prop_growth_holder_micro_campanato_norm_sq, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hw2 i] with x hx
    rw [hx]
    ring
  have hgrad' : ∀ i : Fin d,
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
        ((v : SobolevData (centeredCube c s hs)).2 i y) ^ 2 =
      s ^ d * ∫ x in U, ((v : SobolevData (centeredCube c s hs)).2 i
        (cubeDilation c 0 s x)) ^ 2 := by
    intro i
    exact aux_coercivity_dilation_integral_scaling d c s hs one_pos
      (fun y => ((v : SobolevData (centeredCube c s hs)).2 i y) ^ 2)
      ((Lp.aestronglyMeasurable _).pow 2)
  have hsd : 0 ≤ s ^ d := pow_nonneg hs.le d
  rw [hval]
  calc s ^ d * ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).1‖ ^ 2
      ≤ s ^ d * ((K : ℝ) ^ 2 * ∑ i : Fin d,
        ‖(w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)).2 i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hP2 hsd
    _ = (K : ℝ) ^ 2 * s ^ 2 * ∑ i : Fin d, (s ^ d * ∫ x in U,
          ((v : SobolevData (centeredCube c s hs)).2 i (cubeDilation c 0 s x)) ^ 2) := by
        simp only [hgrad, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = (K : ℝ) ^ 2 * s ^ 2 * ∑ i : Fin d,
          ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
            ((v : SobolevData (centeredCube c s hs)).2 i y) ^ 2 := by
        simp only [hgrad']

/-- The centred restriction `u|_U - (u)_U` to a sub-domain, in the mean-zero graph, with the
same gradient. -/
theorem aux_prop_growth_holder_micro_campanato_centered_restrict {d : ℕ}
    {U Ω : Opens (SpatialCoordinates d)} (hle : U ≤ Ω)
    [IsFiniteMeasure (volume.restrict (U : Set (SpatialCoordinates d)))]
    (hvol : volume.real (U : Set (SpatialCoordinates d)) ≠ 0)
    (u : weakSobolevGraph Ω) :
    ∃ v : meanZeroSobolevGraph U,
      ((v : SobolevData U).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))]
        (fun y => (u : SobolevData Ω).1 y -
          setAverage (U : Set (SpatialCoordinates d)) (u : SobolevData Ω).1) ∧
      ∀ i : Fin d, ((v : SobolevData U).2 i : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))]
        ((u : SobolevData Ω).2 i : SpatialCoordinates d → ℝ) := by
  set m : ℝ := setAverage (U : Set (SpatialCoordinates d)) (u : SobolevData Ω).1 with hm
  set v0 : SobolevData U := sobolevDataRestrict hle (u : SobolevData Ω) -
    (domainConstantL2 (Ω := U) m, fun _ => (0 : DomainL2 U)) with hv0
  have hv0w : v0 ∈ weakSobolevGraph U :=
    Submodule.sub_mem _ (sobolevDataRestrict_mem_weak hle u.2) (constantSobolevData_mem_weak m)
  have hv01 : (v0.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (U : Set (SpatialCoordinates d))]
      fun y => (u : SobolevData Ω).1 y - m := by
    filter_upwards [Lp.coeFn_sub (sobolevDataRestrict hle (u : SobolevData Ω)).1
      (domainConstantL2 (Ω := U) m), domainLpRestrict_coeFn hle (u : SobolevData Ω).1,
      domainConstantL2_coeFn (Ω := U) m] with y h1 h2 h3
    change (((sobolevDataRestrict hle (u : SobolevData Ω)).1 - domainConstantL2 (Ω := U) m :
      DomainL2 U) : SpatialCoordinates d → ℝ) y = _
    rw [h1, Pi.sub_apply, h3]
    change ((domainLpRestrict hle (u : SobolevData Ω).1 : DomainL2 U) :
      SpatialCoordinates d → ℝ) y - m = _
    rw [h2]
  have hUm : MeasurableSet (U : Set (SpatialCoordinates d)) := U.isOpen.measurableSet
  have hInt : Integrable (fun y => (u : SobolevData Ω).1 y)
      (volume.restrict (U : Set (SpatialCoordinates d))) := by
    have h := (Lp.memLp (domainLpRestrict hle (u : SobolevData Ω).1)).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    exact h.congr (domainLpRestrict_coeFn hle (u : SobolevData Ω).1)
  have hIU : (∫ y in (U : Set (SpatialCoordinates d)), (u : SobolevData Ω).1 y
      ∂volume.restrict (Ω : Set (SpatialCoordinates d))) =
      ∫ y in (U : Set (SpatialCoordinates d)), (u : SobolevData Ω).1 y := by
    rw [Measure.restrict_restrict hUm, Set.inter_eq_left.mpr hle]
  refine ⟨⟨v0, ?_⟩, hv01, ?_⟩
  · rw [mem_meanZeroSobolevGraph_iff]
    refine ⟨hv0w, ?_⟩
    rw [integral_congr_ae hv01, integral_sub hInt (integrable_const m),
      MeasureTheory.setIntegral_const, smul_eq_mul, ← hIU, hm]
    unfold setAverage
    field_simp
    ring
  · intro i
    have h2 := domainLpRestrict_coeFn hle ((u : SobolevData Ω).2 i)
    change ((((sobolevDataRestrict hle (u : SobolevData Ω)).2 i - (0 : DomainL2 U)) :
      DomainL2 U) : SpatialCoordinates d → ℝ) =ᵐ[_] _
    rw [sub_zero]
    exact h2

/-- The mean minimizes the quadratic deviation. -/
theorem aux_prop_growth_holder_micro_campanato_variance_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : MemLp f 2 μ) (A m : ℝ)
    (hA : ∫ x, f x ∂μ = A * μ.real univ) :
    ∫ x, (f x - A) ^ 2 ∂μ ≤ ∫ x, (f x - m) ^ 2 ∂μ := by
  have hfA : MemLp (fun x => f x - A) 2 μ := hf.sub (memLp_const A)
  have hI1 : Integrable (fun x => (f x - A) ^ 2) μ := hfA.integrable_sq
  have hI2 : Integrable (fun x => f x - A) μ := hfA.integrable one_le_two
  have hexp : (fun x => (f x - m) ^ 2) =
      fun x => ((f x - A) ^ 2 + (2 * (A - m)) * (f x - A)) + (A - m) ^ 2 := by
    funext x; ring
  have hlin : ∫ x, (f x - A) ∂μ = 0 := by
    rw [integral_sub (hf.integrable one_le_two) (integrable_const A), hA, integral_const,
      smul_eq_mul]
    ring
  have e1 : ∫ x, ((f x - A) ^ 2 + 2 * (A - m) * (f x - A) + (A - m) ^ 2) ∂μ =
      ∫ x, ((f x - A) ^ 2 + 2 * (A - m) * (f x - A)) ∂μ + ∫ _x, (A - m) ^ 2 ∂μ :=
    integral_add (hI1.add (hI2.const_mul _)) (integrable_const _)
  have e2 : ∫ x, ((f x - A) ^ 2 + 2 * (A - m) * (f x - A)) ∂μ =
      ∫ x, (f x - A) ^ 2 ∂μ + ∫ x, 2 * (A - m) * (f x - A) ∂μ :=
    integral_add hI1 (hI2.const_mul _)
  rw [hexp, e1, e2, integral_const_mul, hlin, integral_const, smul_eq_mul]
  have h1 : 0 ≤ μ.real univ * (A - m) ^ 2 := mul_nonneg measureReal_nonneg (sq_nonneg _)
  linarith

/-! ###  `MicroGeometry` -/
/-- The centre `x` clamped, coordinatewise, into `[z - (R-h), z + (R-h)]`. -/
def aux_prop_growth_holder_micro_campanato_clamp {d : ℕ} (z x : SpatialCoordinates d)
    (R h : ℝ) : SpatialCoordinates d :=
  fun i => max (z i - (R - h)) (min (z i + (R - h)) (x i))

theorem aux_prop_growth_holder_micro_campanato_clamp_coord_z (zi xi R h : ℝ) (hhR : h ≤ R) :
    |max (zi - (R - h)) (min (zi + (R - h)) xi) - zi| ≤ R - h := by
  rw [abs_le]
  constructor
  · have := le_max_left (zi - (R - h)) (min (zi + (R - h)) xi)
    linarith
  · rcases max_cases (zi - (R - h)) (min (zi + (R - h)) xi) with h1 | h1 <;>
      rw [h1.1] <;>
      [linarith; linarith [min_le_left (zi + (R - h)) xi]]

theorem aux_prop_growth_holder_micro_campanato_clamp_coord_x (zi xi R h : ℝ) (hh : 0 < h)
    (hx : |xi - zi| < R) :
    |xi - max (zi - (R - h)) (min (zi + (R - h)) xi)| < h := by
  rw [abs_lt] at hx ⊢
  rcases max_cases (zi - (R - h)) (min (zi + (R - h)) xi) with h1 | h1 <;>
    rcases min_cases (zi + (R - h)) xi with h2 | h2 <;>
    rw [h1.1] <;> (try rw [h2.1]) <;> constructor <;> linarith [h1.2, h2.2]

theorem aux_prop_growth_holder_micro_campanato_clamp_coord_y (zi xi yi R h : ℝ)
    (hyx : |yi - xi| < h) (hyz : |yi - zi| < R) :
    |yi - max (zi - (R - h)) (min (zi + (R - h)) xi)| < h := by
  rw [abs_lt] at hyx hyz ⊢
  rcases max_cases (zi - (R - h)) (min (zi + (R - h)) xi) with h1 | h1 <;>
    rcases min_cases (zi + (R - h)) xi with h2 | h2 <;>
    rw [h1.1] <;> (try rw [h2.1]) <;> constructor <;> linarith [h1.2, h2.2]

/-- The `h`-ball about the clamped centre stays in `ball z R`. -/
theorem aux_prop_growth_holder_micro_campanato_clamp_ball_subset {d : ℕ}
    (z x : SpatialCoordinates d) {R h : ℝ} (hh : 0 < h) (hhR : h ≤ R) :
    ball (aux_prop_growth_holder_micro_campanato_clamp z x R h) h ⊆ ball z R := by
  intro y hy
  rw [mem_ball, dist_pi_lt_iff (hh.trans_le hhR)]
  rw [mem_ball, dist_pi_lt_iff hh] at hy
  intro i
  have h1 := hy i
  have h2 := aux_prop_growth_holder_micro_campanato_clamp_coord_z (z i) (x i) R h hhR
  rw [Real.dist_eq] at h1 ⊢
  change |y i - max (z i - (R - h)) (min (z i + (R - h)) (x i))| < h at h1
  calc |y i - z i| = |(y i - max (z i - (R - h)) (min (z i + (R - h)) (x i))) +
        (max (z i - (R - h)) (min (z i + (R - h)) (x i)) - z i)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ < h + (R - h) := add_lt_add_of_lt_of_le h1 h2
    _ = R := by ring

/-- The clamped centre lies in `ball z R`. -/
theorem aux_prop_growth_holder_micro_campanato_clamp_mem {d : ℕ}
    (z x : SpatialCoordinates d) {R h : ℝ} (hh : 0 < h) (hhR : h ≤ R) :
    aux_prop_growth_holder_micro_campanato_clamp z x R h ∈ ball z R :=
  aux_prop_growth_holder_micro_campanato_clamp_ball_subset z x hh hhR (mem_ball_self hh)

/-- `x` is within `h` of its clamp. -/
theorem aux_prop_growth_holder_micro_campanato_clamp_dist {d : ℕ}
    (z x : SpatialCoordinates d) {R h : ℝ} (hh : 0 < h) (hhR : h ≤ R) (hx : x ∈ ball z R) :
    dist x (aux_prop_growth_holder_micro_campanato_clamp z x R h) < h := by
  rw [dist_pi_lt_iff hh]
  rw [mem_ball, dist_pi_lt_iff (hh.trans_le hhR)] at hx
  intro i
  have h1 := hx i
  rw [Real.dist_eq] at h1 ⊢
  exact aux_prop_growth_holder_micro_campanato_clamp_coord_x (z i) (x i) R h hh h1

/-- `ball x h ∩ ball z R ⊆ ball (clamp) h`. -/
theorem aux_prop_growth_holder_micro_campanato_clamp_inter_subset {d : ℕ}
    (z x : SpatialCoordinates d) {R h : ℝ} (hh : 0 < h) (hhR : h ≤ R) :
    ball x h ∩ ball z R ⊆ ball (aux_prop_growth_holder_micro_campanato_clamp z x R h) h := by
  rintro y ⟨hyx, hyz⟩
  rw [mem_ball, dist_pi_lt_iff hh]
  rw [mem_ball, dist_pi_lt_iff hh] at hyx
  rw [mem_ball, dist_pi_lt_iff (hh.trans_le hhR)] at hyz
  intro i
  have h1 := hyx i
  have h2 := hyz i
  rw [Real.dist_eq] at h1 h2 ⊢
  exact aux_prop_growth_holder_micro_campanato_clamp_coord_y (z i) (x i) (y i) R h h1 h2

/-- **Covering cube.**  For `x ∈ ball z R`, the set `ball x rad ∩ ball z R` lies in one cube
`ball c h` contained in `ball z R`, with `c ∈ ball z R` and `h ≤ rad`. -/
theorem aux_prop_growth_holder_micro_campanato_cover {d : ℕ} (z x : SpatialCoordinates d)
    {R rad : ℝ} (hR : 0 < R) (hrad : 0 < rad) :
    ∃ (c : SpatialCoordinates d) (h : ℝ), 0 < h ∧ h ≤ rad ∧ c ∈ ball z R ∧
      ball x rad ∩ ball z R ⊆ ball c h ∧ ball c h ⊆ ball z R := by
  by_cases hle : rad ≤ R
  · exact ⟨aux_prop_growth_holder_micro_campanato_clamp z x R rad, rad, hrad, le_rfl,
      aux_prop_growth_holder_micro_campanato_clamp_mem z x hrad hle,
      aux_prop_growth_holder_micro_campanato_clamp_inter_subset z x hrad hle,
      aux_prop_growth_holder_micro_campanato_clamp_ball_subset z x hrad hle⟩
  · push Not at hle
    exact ⟨z, R, hR, hle.le, mem_ball_self hR, Set.inter_subset_right, subset_rfl⟩

/-- **Volume lower bound.**  `rad^d ≤ |ball x rad ∩ ball z R|` for `x ∈ ball z R`,
`0 < rad ≤ 2R`. -/
theorem aux_prop_growth_holder_micro_campanato_volume_ge {d : ℕ} (z x : SpatialCoordinates d)
    {R rad : ℝ} (hrad : 0 < rad) (hradR : rad ≤ 2 * R) (hx : x ∈ ball z R) :
    rad ^ d ≤ volume.real (ball x rad ∩ ball z R) := by
  have hh : 0 < rad / 2 := half_pos hrad
  have hhR : rad / 2 ≤ R := by linarith
  set c := aux_prop_growth_holder_micro_campanato_clamp z x R (rad / 2) with hc
  have hsub : ball c (rad / 2) ⊆ ball x rad ∩ ball z R := by
    intro y hy
    refine ⟨?_, aux_prop_growth_holder_micro_campanato_clamp_ball_subset z x hh hhR hy⟩
    rw [mem_ball] at hy ⊢
    have h2 := aux_prop_growth_holder_micro_campanato_clamp_dist z x hh hhR hx
    calc dist y x ≤ dist y c + dist c x := dist_triangle _ _ _
      _ < rad / 2 + rad / 2 := add_lt_add hy (by rw [dist_comm]; exact h2)
      _ = rad := by ring
  have hvol : volume.real (ball c (rad / 2)) = rad ^ d := by
    rw [measureReal_def, Real.volume_pi_ball c hh, Fintype.card_fin,
      ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [← hvol]
  exact measureReal_mono hsub ((measure_mono Set.inter_subset_left).trans_lt
    measure_ball_lt_top).ne

/-! ###  `MicroPathwise` -/
/-- The unweighted local gradient mass on a sub-cube is controlled by the coefficient floor. -/
theorem aux_prop_growth_holder_micro_campanato_floor {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (Mx : ℝ)
    (hlow : ∀ᵐ y ∂volume.restrict (Ω : Set (SpatialCoordinates d)), 1 ≤ Mx * a.val y)
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s) (w : SobolevData Ω) :
    ∑ i : Fin d, ∫ y in s, (w.2 i y) ^ 2 ∂volume.restrict (Ω : Set (SpatialCoordinates d)) ≤
      Mx * localGradientEnergy a hs (sobolevGradient w) := by
  rw [localGradientEnergy_eq_integral, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← integral_const_mul]
  have hL : Integrable (fun y => (w.2 i y) ^ 2)
      ((volume.restrict (Ω : Set (SpatialCoordinates d))).restrict s) :=
    ((Lp.memLp (w.2 i)).integrable_sq).restrict
  have hW : Integrable (fun y => a.val y * (w.2 i y) ^ 2)
      (volume.restrict (Ω : Set (SpatialCoordinates d))) := by
    have h := integrable_weighted_inner a.val (w.2 i) (w.2 i)
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [RCLike.inner_apply, conj_trivial, sq]
  refine integral_mono_ae hL (hW.restrict.const_mul Mx) ?_
  filter_upwards [ae_restrict_of_ae hlow] with y hy
  have hsq : 0 ≤ (w.2 i y) ^ 2 := sq_nonneg _
  change (w.2 i y) ^ 2 ≤ Mx * (a.val y * ((sobolevGradient w) i y) ^ 2)
  have hg : ((sobolevGradient w) i : SpatialCoordinates d → ℝ) = (w.2 i : _) := rfl
  rw [hg]
  nlinarith [mul_le_mul_of_nonneg_right hy hsq]

/-- **Deterministic pathwise estimate.** -/
theorem aux_prop_growth_holder_micro_campanato_pathwise {d : ℕ} (Cp : ℝ) (hCp0 : 0 ≤ Cp)
    (hPoinc : ∀ (c : SpatialCoordinates d) (s : ℝ) (hs : 0 < s)
      (v : meanZeroSobolevGraph (centeredCube c s hs)),
      ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).1 y) ^ 2 ≤
        Cp * s ^ 2 * ∑ i : Fin d, ∫ y in (centeredCube c s hs : Set (SpatialCoordinates d)),
          ((v : SobolevData (centeredCube c s hs)).2 i y) ^ 2)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr)) (Mx : ℝ) (hMx : 0 ≤ Mx)
    (hlow : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      1 ≤ Mx * a.val y)
    (u : weakSobolevGraph (centeredCube z r hr)) (rad Eb : ℝ) (hrad : 0 < rad)
    (hen : ∀ c ∈ centeredCube z r hr,
      localGradientEnergy a
          (s := Metric.ball c rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤ Eb)
    (x : SpatialCoordinates d) (hx : x ∈ centeredCube z r hr) :
    ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
        ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
          (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (u : SobolevData (centeredCube z r hr)).1) ^ 2
        ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
      4 * Cp * rad ^ 2 * (Mx * Eb) := by
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d))
    with hQdef
  have hQfin : IsFiniteMeasure (volume.restrict Q) := by rw [hQdef]; infer_instance
  have hQm : MeasurableSet Q := (centeredCube z r hr).isOpen.measurableSet
  obtain ⟨c, h, hh, hhrad, hcQ, hsubB, hsubQ⟩ :=
    aux_prop_growth_holder_micro_campanato_cover z x (half_pos hr) hrad
  have h2h : 0 < 2 * h := by positivity
  set Q' : Opens (SpatialCoordinates d) := centeredCube c (2 * h) h2h with hQ'def
  have hQ'set : (Q' : Set (SpatialCoordinates d)) = ball c h := by
    change ball c (2 * h / 2) = ball c h
    congr 1
    ring
  have hQ'm : MeasurableSet (Q' : Set (SpatialCoordinates d)) := Q'.isOpen.measurableSet
  have hQ'Q : (Q' : Set (SpatialCoordinates d)) ⊆ Q := by
    intro y hy
    rw [hQ'set] at hy
    exact hsubQ hy
  have hle : Q' ≤ centeredCube z r hr := hQ'Q
  have hvolQ' : volume.real (Q' : Set (SpatialCoordinates d)) ≠ 0 := by
    rw [hQ'set, measureReal_def, Real.volume_pi_ball c hh, Fintype.card_fin,
      ENNReal.toReal_ofReal (by positivity)]
    positivity
  obtain ⟨v, hv1, hv2⟩ :=
    aux_prop_growth_holder_micro_campanato_centered_restrict hle hvolQ' u
  set m' : ℝ := setAverage (Q' : Set (SpatialCoordinates d))
    (u : SobolevData (centeredCube z r hr)).1 with hm'
  set S : Set (SpatialCoordinates d) := Metric.ball x rad ∩ Q with hS
  have hSm : MeasurableSet S := isOpen_ball.measurableSet.inter hQm
  have hSQ : S ⊆ Q := Set.inter_subset_right
  have hSQ' : S ⊆ (Q' : Set (SpatialCoordinates d)) := by rw [hQ'set]; exact hsubB
  have hSpos : 0 < volume.real S := by
    have hpos : 0 < volume S :=
      (isOpen_ball.inter (centeredCube z r hr).isOpen).measure_pos volume
        ⟨x, mem_ball_self hrad, hx⟩
    have hfin : volume S ≠ ⊤ :=
      ((measure_mono Set.inter_subset_left).trans_lt measure_ball_lt_top).ne
    exact ENNReal.toReal_pos hpos.ne' hfin
  -- Step 1: the mean minimizes the deviation on `S`
  have hμS : ((volume.restrict Q).restrict S).real univ = volume.real S := by
    rw [measureReal_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Measure.restrict_apply hSm, Set.inter_eq_left.mpr hSQ, ← measureReal_def]
  have step1 : ∫ y in S, ((u : SobolevData (centeredCube z r hr)).1 y -
        setAverage S (u : SobolevData (centeredCube z r hr)).1) ^ 2 ∂volume.restrict Q ≤
      ∫ y in S, ((u : SobolevData (centeredCube z r hr)).1 y - m') ^ 2 ∂volume.restrict Q := by
    apply aux_prop_growth_holder_micro_campanato_variance_le ((volume.restrict Q).restrict S) _
      ((Lp.memLp _).restrict S)
    rw [hμS]
    unfold setAverage
    rw [inv_mul_eq_div, div_mul_cancel₀ _ hSpos.ne']
  -- Step 2: enlarge to the covering cube
  have hInt2 : Integrable (fun y => ((u : SobolevData (centeredCube z r hr)).1 y - m') ^ 2)
      (volume.restrict Q) :=
    ((Lp.memLp (u : SobolevData (centeredCube z r hr)).1).sub (memLp_const m')).integrable_sq
  have step2 : ∫ y in S, ((u : SobolevData (centeredCube z r hr)).1 y - m') ^ 2
        ∂volume.restrict Q ≤
      ∫ y in (Q' : Set (SpatialCoordinates d)),
        ((u : SobolevData (centeredCube z r hr)).1 y - m') ^ 2 ∂volume.restrict Q :=
    setIntegral_mono_set hInt2.integrableOn
      (Filter.Eventually.of_forall fun y => sq_nonneg _) hSQ'.eventuallyLE
  -- Step 3: the centred restriction
  have step3 : ∫ y in (Q' : Set (SpatialCoordinates d)),
        ((u : SobolevData (centeredCube z r hr)).1 y - m') ^ 2 ∂volume.restrict Q =
      ∫ y in (Q' : Set (SpatialCoordinates d)), ((v : SobolevData Q').1 y) ^ 2 := by
    rw [Measure.restrict_restrict hQ'm, Set.inter_eq_left.mpr hQ'Q]
    apply integral_congr_ae
    filter_upwards [hv1] with y hy
    rw [hy]
  -- Step 4: Poincaré on the covering cube
  have step4 := hPoinc c (2 * h) h2h v
  have step4b : ∑ i : Fin d, ∫ y in (Q' : Set (SpatialCoordinates d)),
        ((v : SobolevData Q').2 i y) ^ 2 =
      ∑ i : Fin d, ∫ y in (Q' : Set (SpatialCoordinates d)),
        ((u : SobolevData (centeredCube z r hr)).2 i y) ^ 2 ∂volume.restrict Q := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Measure.restrict_restrict hQ'm, Set.inter_eq_left.mpr hQ'Q]
    apply integral_congr_ae
    filter_upwards [hv2 i] with y hy
    rw [hy]
  -- Step 5: coefficient floor
  have step5 := aux_prop_growth_holder_micro_campanato_floor a Mx hlow hQ'm
    (u : SobolevData (centeredCube z r hr))
  -- Step 6: monotonicity and the ball energy bound
  have hsub6 : (Q' : Set (SpatialCoordinates d)) ⊆ Metric.ball c rad ∩ Q := by
    intro y hy
    refine ⟨?_, hQ'Q hy⟩
    rw [hQ'set] at hy
    exact ball_subset_ball hhrad hy
  have step6 := (_root_.SubdiffusiveProcess.ResponseMoments.localGradientEnergy_mono a hQ'm
    (isOpen_ball.measurableSet.inter hQm) hsub6
    (sobolevGradient (u : SobolevData (centeredCube z r hr)))).trans (hen c hcQ)
  have hE0 : 0 ≤ localGradientEnergy a hQ'm
      (sobolevGradient (u : SobolevData (centeredCube z r hr))) :=
    localGradientEnergy_nonneg _ _ _
  have hMxE : 0 ≤ Mx * Eb := mul_nonneg hMx (hE0.trans step6)
  have hCph : 0 ≤ Cp * (2 * h) ^ 2 := mul_nonneg hCp0 (sq_nonneg _)
  have hh4 : Cp * (2 * h) ^ 2 ≤ 4 * Cp * rad ^ 2 := by
    have : (2 * h) ^ 2 ≤ (2 * rad) ^ 2 := pow_le_pow_left₀ h2h.le (by linarith) 2
    nlinarith
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ = _ := step3
    _ ≤ _ := step4
    _ = Cp * (2 * h) ^ 2 * ∑ i : Fin d, ∫ y in (Q' : Set (SpatialCoordinates d)),
        ((u : SobolevData (centeredCube z r hr)).2 i y) ^ 2 ∂volume.restrict Q := by
        rw [step4b]
    _ ≤ Cp * (2 * h) ^ 2 * (Mx * localGradientEnergy a hQ'm
          (sobolevGradient (u : SobolevData (centeredCube z r hr)))) :=
        mul_le_mul_of_nonneg_left step5 hCph
    _ ≤ Cp * (2 * h) ^ 2 * (Mx * Eb) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left step6 hMx) hCph
    _ ≤ 4 * Cp * rad ^ 2 * (Mx * Eb) := mul_le_mul_of_nonneg_right hh4 hMxE

/-! ###  `MicroCampanato` -/
/-- `cutoffPositiveCoefficient` is the continuous `cutoffCoefficient` a.e. on its cube. -/
theorem aux_prop_growth_holder_micro_campanato_coeff_ae {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H omega N z hr).val x = cutoffCoefficient M H omega N x := by
  have h1 := @normalizedContinuousPositiveCoefficient_coeFn d (centeredCube z r hr)
    (closedCube z r hr) ⟨centeredCube_subset_closedCube z hr⟩
    (cutoffCoefficientCM M H omega N z hr) (cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
  filter_upwards [h1, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxm
  unfold cutoffPositiveCoefficient
  rw [hx hxm, div_one]
  rfl

/-- The final numerical step: the pathwise bound is of Campanato form. -/
theorem aux_prop_growth_holder_micro_campanato_final_alg (d : ℕ)
    (Cp Mx K S rad eps V t alpha e L : ℝ)
    (hCp : 0 ≤ Cp) (hMx : 0 ≤ Mx) (hrad : 0 < rad) (hre : rad ≤ eps) (he : 0 ≤ e)
    (hexp : 2 + t = 2 * alpha + d + e) (hV : rad ^ d ≤ V)
    (hL : L ≤ 4 * Cp * rad ^ 2 * (Mx * (K * S ^ 2 * rad ^ t))) :
    L ≤ ((1 + Cp) * (Mx + |K|) * eps ^ (e / 2) * S) ^ 2 * rad ^ (2 * alpha) * V := by
  have heps : 0 < eps := hrad.trans_le hre
  have hA : 0 ≤ rad ^ (2 * alpha) := Real.rpow_nonneg hrad.le _
  have hB : 0 ≤ rad ^ d := pow_nonneg hrad.le d
  have hC : 0 ≤ rad ^ e := Real.rpow_nonneg hrad.le _
  have hsplit : rad ^ 2 * rad ^ t = rad ^ (2 * alpha) * rad ^ d * rad ^ e := by
    have h1 : rad ^ 2 * rad ^ t = rad ^ ((2 : ℝ) + t) := by
      rw [Real.rpow_add hrad, Real.rpow_two]
    rw [h1, hexp, Real.rpow_add hrad, Real.rpow_add hrad, Real.rpow_natCast]
  have hCe : rad ^ e ≤ (eps ^ (e / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul heps.le]
    have : e / 2 * ((2 : ℕ) : ℝ) = e := by push_cast; ring
    rw [this]
    exact Real.rpow_le_rpow hrad.le hre he
  have hcoef : 4 * Cp * (Mx * K) ≤ ((1 + Cp) * (Mx + |K|)) ^ 2 := by
    have h1 : Mx * K ≤ Mx * |K| := mul_le_mul_of_nonneg_left (le_abs_self K) hMx
    have h2 : 4 * (Mx * |K|) ≤ (Mx + |K|) ^ 2 := by nlinarith [sq_nonneg (Mx - |K|)]
    have h3 : Cp ≤ (1 + Cp) ^ 2 := by nlinarith
    have h4 : 0 ≤ (Mx + |K|) ^ 2 := sq_nonneg _
    calc 4 * Cp * (Mx * K) ≤ Cp * (4 * (Mx * |K|)) := by nlinarith
      _ ≤ Cp * (Mx + |K|) ^ 2 := mul_le_mul_of_nonneg_left h2 hCp
      _ ≤ (1 + Cp) ^ 2 * (Mx + |K|) ^ 2 := mul_le_mul_of_nonneg_right h3 h4
      _ = ((1 + Cp) * (Mx + |K|)) ^ 2 := by ring
  have hS2 : 0 ≤ S ^ 2 := sq_nonneg S
  have hX0 : 0 ≤ S ^ 2 * rad ^ (2 * alpha) * rad ^ d * rad ^ e := by positivity
  have hXY : S ^ 2 * rad ^ (2 * alpha) * rad ^ d * rad ^ e ≤
      S ^ 2 * rad ^ (2 * alpha) * V * (eps ^ (e / 2)) ^ 2 := by
    have h1 : S ^ 2 * rad ^ (2 * alpha) * rad ^ d ≤ S ^ 2 * rad ^ (2 * alpha) * V :=
      mul_le_mul_of_nonneg_left hV (mul_nonneg hS2 hA)
    exact mul_le_mul h1 hCe hC (mul_nonneg (mul_nonneg hS2 hA) (hB.trans hV))
  have hB0 : 0 ≤ ((1 + Cp) * (Mx + |K|)) ^ 2 := sq_nonneg _
  calc L ≤ 4 * Cp * rad ^ 2 * (Mx * (K * S ^ 2 * rad ^ t)) := hL
    _ = 4 * Cp * (Mx * K) * (S ^ 2 * (rad ^ 2 * rad ^ t)) := by ring
    _ = 4 * Cp * (Mx * K) * (S ^ 2 * rad ^ (2 * alpha) * rad ^ d * rad ^ e) := by
        rw [hsplit]; ring
    _ ≤ ((1 + Cp) * (Mx + |K|)) ^ 2 * (S ^ 2 * rad ^ (2 * alpha) * rad ^ d * rad ^ e) :=
        mul_le_mul_of_nonneg_right hcoef hX0
    _ ≤ ((1 + Cp) * (Mx + |K|)) ^ 2 * (S ^ 2 * rad ^ (2 * alpha) * V * (eps ^ (e / 2)) ^ 2) :=
        mul_le_mul_of_nonneg_left hXY hB0
    _ = ((1 + Cp) * (Mx + |K|) * eps ^ (e / 2) * S) ^ 2 * rad ^ (2 * alpha) * V := by ring

/-- Moments of `G (Mx + |K|) g` from the moments of `Mx` (at a larger order, with
exponential growth absorbed by `g`) and of `K`. -/
theorem aux_prop_growth_holder_micro_campanato_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (p q : ℝ) (hp : 1 ≤ p) (hpq : p ≤ q)
    (Mx K : Ω → ℝ) (G g b CE CK : ℝ) (hG : 0 ≤ G) (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hgb : g * Real.exp b ≤ 1) (hCE : 0 ≤ CE)
    (hMxL : MemLp Mx (ENNReal.ofReal q) P)
    (hMxB : eLpNorm Mx (ENNReal.ofReal q) P ≤ ENNReal.ofReal (CE * Real.exp b))
    (hKL : MemLp K (ENNReal.ofReal p) P)
    (hKB : eLpNorm K (ENNReal.ofReal p) P ≤ ENNReal.ofReal CK) :
    MemLp (fun om => G * (Mx om + |K om|) * g) (ENNReal.ofReal p) P ∧
      eLpNorm (fun om => G * (Mx om + |K om|) * g) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (G * (CE + max CK 0)) := by
  have hle : ENNReal.ofReal p ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal hpq
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hMxp : MemLp Mx (ENNReal.ofReal p) P := hMxL.mono_exponent hle
  have hKa : MemLp (fun om => |K om|) (ENNReal.ofReal p) P := hKL.abs
  have hsum : MemLp (fun om => Mx om + |K om|) (ENNReal.ofReal p) P := hMxp.add hKa
  have hfun : (fun om => G * (Mx om + |K om|) * g) = fun om => (G * g) * (Mx om + |K om|) := by
    funext om; ring
  have hGg : 0 ≤ G * g := mul_nonneg hG hg
  have hsmul : (fun om => G * g * (Mx om + |K om|)) =
      (G * g) • (fun om => Mx om + |K om|) := by
    funext om; simp only [Pi.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact hsum.const_mul (G * g)
  rw [hfun, hsmul, eLpNorm_const_smul]
  have hs : eLpNorm (fun om => Mx om + |K om|) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (CE * Real.exp b) + ENNReal.ofReal (max CK 0) := by
    refine (eLpNorm_add_le hp1).trans (add_le_add ?_ ?_)
    · exact (eLpNorm_le_eLpNorm_of_exponent_le hle).trans hMxB
    · have habs : eLpNorm (fun om => |K om|) (ENNReal.ofReal p) P =
          eLpNorm K (ENNReal.ofReal p) P := by
        have : (fun om => |K om|) = fun om => ‖K om‖ := by
          funext om; rw [Real.norm_eq_abs]
        rw [this, eLpNorm_norm _ hKL.aestronglyMeasurable]
      rw [habs]
      exact hKB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hexp0 : 0 ≤ CE * Real.exp b := mul_nonneg hCE (Real.exp_pos b).le
  rw [← ENNReal.ofReal_add hexp0 (le_max_right _ _)] at hs
  rw [Real.enorm_eq_ofReal hGg]
  refine (mul_le_mul_of_nonneg_left hs bot_le).trans ?_
  rw [← ENNReal.ofReal_mul hGg]
  refine ENNReal.ofReal_le_ofReal ?_
  have hm0 : 0 ≤ max CK 0 := le_max_right _ _
  have h1 : g * (CE * Real.exp b) ≤ CE := by
    calc g * (CE * Real.exp b) = CE * (g * Real.exp b) := by ring
      _ ≤ CE * 1 := mul_le_mul_of_nonneg_left hgb hCE
      _ = CE := mul_one CE
  have h2 : g * max CK 0 ≤ max CK 0 := by nlinarith
  calc G * g * (CE * Real.exp b + max CK 0) = G * (g * (CE * Real.exp b) + g * max CK 0) := by
        ring
    _ ≤ G * (CE + max CK 0) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hG

/-- The cutoff factor `(3^{-N})^{e/2}` as an `rpow` of `3`. -/
theorem aux_prop_growth_holder_micro_campanato_factor_eq (e : ℝ) (N : ℕ) :
    ((3 : ℝ) ^ (-(N : ℤ))) ^ (e / 2) = (3 : ℝ) ^ (-(e / 2) * (N : ℝ)) := by
  rw [show ((3 : ℝ) ^ (-(N : ℤ))) = (3 : ℝ) ^ (-(N : ℝ)) by
    rw [← Real.rpow_intCast]; push_cast; ring_nf]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  ring_nf

/-- The disorder threshold makes the envelope growth rate at most `(e/2) log 3`. -/
theorem aux_prop_growth_holder_micro_campanato_rate (Cd Cpe e delta : ℝ) (hCd : 0 < Cd)
    (hCpe : 0 < Cpe) (hdelta : 0 < delta)
    (hle : delta ≤ min 1 ((e / 2) * Real.log 3 / (Cd + Cpe))) :
    Cd * delta + Cpe * delta ^ 2 ≤ (e / 2) * Real.log 3 := by
  have h1 : delta ≤ 1 := hle.trans (min_le_left _ _)
  have h2 : delta ≤ (e / 2) * Real.log 3 / (Cd + Cpe) := hle.trans (min_le_right _ _)
  have h3 : delta ^ 2 ≤ delta := by nlinarith
  have h4 : (Cd + Cpe) * delta ≤ (e / 2) * Real.log 3 := by
    rwa [le_div_iff₀ (by positivity), mul_comm] at h2
  nlinarith

/-- The cutoff factor `(3^{-N})^{e/2}` lies in `[0,1]` and absorbs `e^{bN}` for
`0 ≤ b ≤ (e/2) log 3`. -/
theorem aux_prop_growth_holder_micro_campanato_fac (e b : ℝ) (he : 0 < e)
    (hb : b ≤ (e / 2) * Real.log 3) (N : ℕ) :
    0 ≤ ((3 : ℝ) ^ (-(N : ℤ))) ^ (e / 2) ∧ ((3 : ℝ) ^ (-(N : ℤ))) ^ (e / 2) ≤ 1 ∧
      ((3 : ℝ) ^ (-(N : ℤ))) ^ (e / 2) * Real.exp (b * N) ≤ 1 := by
  rw [aux_prop_growth_holder_micro_campanato_factor_eq]
  refine ⟨Real.rpow_nonneg (by norm_num) _, ?_, ?_⟩
  · apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  · rw [mul_comm]
    have h := aux_holder_micro_absorb (e / 2) b (by positivity) hb N
    rw [neg_mul] at h ⊢; assumption

/-- The exact type of `prop_growth_energy_assembly` (copied verbatim from its header), so
that the Campanato child can be stated conditionally and its own axioms printed. -/
def aux_prop_growth_holder_micro_campanato_EnergyAssembly : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (_Cp : CampanatoInput d) (_S : SobolevFoundationalInput d hd)
    (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 →
    (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 1 ≤ K N om) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict
            (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          ∀ (x : SpatialCoordinates d) (rad : ℝ),
            x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
                (s := Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter
                  (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
              K N om * (Kf + Cphi) ^ 2 * rad ^ t

/-- **The below-wavelength Campanato child from the energy assembly.**  Exact statement of
`aux_prop_growth_holder_assembly_MicroCampanato`, conditional only on the exact type of the
Lean-closed `prop_growth_energy_assembly`. -/
theorem aux_prop_growth_holder_micro_campanato_of_energy
    (hEA : aux_prop_growth_holder_micro_campanato_EnergyAssembly) :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E) (_X : in_extension d hd E)
    (_W : SmallPerturbationInput d) (_Cp : CampanatoInput d)
    (_S : SobolevFoundationalInput d hd) (alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (Kosc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kosc N om) ∧
        (∀ i N, MemLp (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad →
            rad < (3 : ℝ) ^ (-(N : ℤ)) → rad ≤ r →
            ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
                ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
                  (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (u : SobolevData (centeredCube z r hr)).1) ^ 2
                ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
              (Kosc N om * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  intro d hd _ _ E P X W Cp S alpha k ps ha0 ha1 hps
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  -- the energy exponent `t` and the excess `e = 2 + t - 2α - d > 0`
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) + d) / 2 :=
    ⟨_, rfl⟩
  have hmax1 := le_max_left ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha)
  have hmax2 := le_max_right ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha)
  have hmaxd : max ((d : ℝ) - 1) ((d : ℝ) - 2 + 2 * alpha) < d :=
    max_lt (by linarith) (by linarith)
  have ht1 : (d : ℝ) - 1 < t := by rw [htdef]; linarith
  have htd : t < d := by rw [htdef]; linarith
  have hte : (d : ℝ) - 2 + 2 * alpha < t := by rw [htdef]; linarith
  obtain ⟨e, hedef⟩ : ∃ e : ℝ, e = 2 + t - 2 * alpha - d := ⟨_, rfl⟩
  have he : 0 < e := by rw [hedef]; linarith
  have hexp : 2 + t = 2 * alpha + d + e := by rw [hedef]; ring
  -- suppliers, all fixed before the model
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = 1 + ∑ i, ps i := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ i, ps i := Finset.sum_nonneg fun i _ => le_trans zero_le_one (hps i)
  have hq : 1 ≤ q := by rw [hqdef]; linarith
  have hpq : ∀ i, ps i ≤ q := by
    intro i
    have := Finset.single_le_sum (fun j _ => le_trans zero_le_one (hps j)) (Finset.mem_univ i)
    rw [hqdef]; linarith
  have hq0 : 0 < 2 * q := by linarith
  obtain ⟨deltaE, hdeltaE, hEA⟩ :=
    hEA d hd E P X W Cp S t alpha k ps ht1 htd ha0 ha1 hps
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
  intro M Rm Sreg It H hH hdelta z r hr hr1
  have hdE : M.delta ≤ deltaE := hdelta.trans (min_le_left _ _)
  have hdc : M.delta ≤ cd / (2 * q) :=
    hdelta.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hda : M.delta ≤ dabs := hdelta.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdpos : 0 < M.delta := M.shellPrefix.delta_pos
  -- the exponential growth rate of the coefficient envelope is absorbed
  have hrate : Cd * M.delta + Cpe * M.delta ^ 2 ≤ (e / 2) * Real.log 3 :=
    aux_prop_growth_holder_micro_campanato_rate Cd Cpe e M.delta hCd hCpe hdpos
      (hda.trans_eq hdabs)
  obtain ⟨K, CbK, hKL, hKB, -, hen⟩ := hEA M Rm Sreg It H hH hdE z r hr hr1
  obtain ⟨D, Mx, CE, hCE, hDMx0, hext, hmem, -, hMxmom⟩ := hroot M H hH hdc z r hr hr1
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
    intro N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol x hx rad hrad hradN hradr
    obtain ⟨hMxpos, hbounds, -⟩ := hext' N
    have hlow : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        1 ≤ Mx N om * (cutoffPositiveCoefficient M H om N z hr).val y := by
      filter_upwards [aux_prop_growth_holder_micro_campanato_coeff_ae M H om N z hr,
        ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with y hy hyQ
      rw [hy]
      have hlo := (hbounds y (centeredCube_subset_closedCube z hr hyQ)).1
      calc (1 : ℝ) = Mx N om * (Mx N om)⁻¹ := (mul_inv_cancel₀ hMxpos.ne').symm
        _ ≤ Mx N om * cutoffCoefficient M H om N y :=
          mul_le_mul_of_nonneg_left hlo hMxpos.le
    have hrad1 : rad ≤ 1 := hradr.trans hr1
    have hpw := aux_prop_growth_holder_micro_campanato_pathwise CP hCP0 hPoinc z hr
      (cutoffPositiveCoefficient M H om N z hr) (Mx N om) hMxpos.le hlow u rad
      (K N om * (Kf + Cphi) ^ 2 * rad ^ t) hrad
      (fun c hc => hom N F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol c rad hc hrad hrad1)
      x hx
    have hV := aux_prop_growth_holder_micro_campanato_volume_ge z x (R := r / 2) hrad
      (hradr.trans_eq (by ring)) hx
    exact aux_prop_growth_holder_micro_campanato_final_alg d CP (Mx N om) (K N om) (Kf + Cphi)
      rad ((3 : ℝ) ^ (-(N : ℤ))) _ t alpha e _ hCP0 hMxpos.le hrad hradN.le he.le hexp hV hpw


/-- **Campanato decay below the wavelength** (the below-wavelength half of the Hölder paragraph of `mfd:prop-growth`).

For `0 < rad < 3^{-N}`, `rad ≤ r`, the `L²` oscillation of the Dirichlet solution on
`B(x,rad) ∩ Q` is at most `(Kosc_N (Kf + Cphi))² rad^{2α} |B(x,rad) ∩ Q|`, with one random
constant whose listed moments are uniform in the cutoff.  Proof: the all-radii energy growth
`prop_growth_energy_assembly` at an exponent `t > d-2+2α`, the scaled mean-zero Poincaré inequality
on the covering sub-cube, the coefficient floor of `lem_extremes` (through
`aux_prop_growth_energy_assembly_root_extremes`), and absorption of its `e^{cδN}` moment growth
by the excess power `3^{-N(2+t-2α-d)/2}` for small disorder.  No premise beyond the reduction's
child statement. -/
theorem prop_growth_holder_micro_campanato :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E) (_X : in_extension d hd E)
    (_W : SmallPerturbationInput d) (_Cp : CampanatoInput d)
    (_S : SobolevFoundationalInput d hd) (alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∃ (Kosc : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ Kosc N om) ∧
        (∀ i N, MemLp (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (Kosc N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
        ∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ),
          ContDiff ℝ 2 phi →
          c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u →
          ∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad →
            rad < (3 : ℝ) ^ (-(N : ℤ)) → rad ≤ r →
            ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
                ((u : SobolevData (centeredCube z r hr)).1 y - setAverage
                  (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                  (u : SobolevData (centeredCube z r hr)).1) ^ 2
                ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
              (Kosc N om * (Kf + Cphi)) ^ 2 * rad ^ (2 * alpha) *
                volume.real (Metric.ball x rad ∩
                  (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  exact aux_prop_growth_holder_micro_campanato_of_energy prop_growth_energy_assembly

end SubdiffusiveProcess.Paper
