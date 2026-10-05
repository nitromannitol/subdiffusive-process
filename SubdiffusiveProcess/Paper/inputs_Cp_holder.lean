module

public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.MultiplicativeChaos.ChaosBasic
public import SubdiffusiveProcess.Sobolev.CampanatoRepresentative
public import SubdiffusiveProcess.EllipticRegularity.InDetCampanatoHolder

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open SubdiffusiveProcess Homogenization _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_inputs_Cp_holder_ball_inter_lower_bound {d : ℕ}
    (z x : SpatialCoordinates d) {r rad : ℝ} (hr : 0 < r)
    (hrad : 0 < rad) (hrad_r : rad ≤ r)
    (hx : x ∈ Metric.closedBall z (r / 2)) :
    ENNReal.ofReal ((1 / 2 : ℝ) ^ d * rad ^ d) ≤
      volume (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) := by
  let t : ℝ := rad / r
  let w : SpatialCoordinates d := fun i => t * z i + (1 - t) * x i
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    rw [div_le_one (by linarith : 0 < r)]
    exact hrad_r
  have htr : t * r = rad := by
    dsimp [t]
    field_simp
  have hxd : dist x z ≤ r / 2 := Metric.mem_closedBall.mp hx
  have hnorm_xz : ‖z - x‖ ≤ r / 2 := by
    simpa [dist_eq_norm, norm_sub_rev] using hxd
  have hwx_eq : w - x = t • (z - x) := by
    ext i
    simp [w]
    ring
  have hwx : dist w x ≤ rad / 2 := by
    rw [dist_eq_norm, hwx_eq, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    calc
      t * ‖z - x‖ ≤ t * (r / 2) := mul_le_mul_of_nonneg_left hnorm_xz ht0
      _ = rad / 2 := by nlinarith [htr]
  have hwz_eq : w - z = (1 - t) • (x - z) := by
    ext i
    simp [w]
    ring
  have hnorm_xz' : ‖x - z‖ ≤ r / 2 := by
    simpa [dist_eq_norm] using hxd
  have hwz : dist w z ≤ r / 2 - rad / 2 := by
    rw [dist_eq_norm, hwz_eq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht1)]
    calc
      (1 - t) * ‖x - z‖ ≤ (1 - t) * (r / 2) :=
        mul_le_mul_of_nonneg_left hnorm_xz' (sub_nonneg.mpr ht1)
      _ = r / 2 - rad / 2 := by nlinarith [htr]
  have hball : Metric.ball w (rad / 4) ⊆ Metric.ball x rad := by
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    have htri := dist_triangle y w x
    linarith
  have hcube : Metric.ball w (rad / 4) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    intro y hy
    change y ∈ Metric.ball z (r / 2)
    rw [Metric.mem_ball]
    have hyw : dist y w < rad / 4 := Metric.mem_ball.mp hy
    have htri := dist_triangle y w z
    have : dist y z < r / 2 := by linarith
    exact this
  have hsub : Metric.ball w (rad / 4) ⊆
      Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    fun y hy => ⟨hball hy, hcube hy⟩
  have hvol : volume (Metric.ball w (rad / 4)) = ENNReal.ofReal ((rad / 2) ^ d) := by
    rw [SubdiffusiveProcess.volume_ball_spatial w (by linarith : 0 < rad / 4)]
    congr 1
    congr 1
    ring
  have hmono : volume (Metric.ball w (rad / 4)) ≤
      volume (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    measure_mono hsub
  rw [hvol] at hmono
  have hreal : (1 / 2 : ℝ) ^ d * rad ^ d = (rad / 2) ^ d := by
    calc
      (1 / 2 : ℝ) ^ d * rad ^ d = rad ^ d * (1 / 2 : ℝ) ^ d := mul_comm _ _
      _ = (rad / 2) ^ d := by
        rw [div_pow, div_eq_mul_inv, ← inv_pow]
        ring
  rw [hreal]
  exact hmono

theorem aux_inputs_Cp_holder_setAverage_eq_volume {d : ℕ}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    (S : Set (SpatialCoordinates d)) (u : DomainL2 (centeredCube z r hr))
    (hS : S ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))) :
    setAverage S u = (volume.real S)⁻¹ * ∫ q in S, u q ∂volume := by
  unfold _root_.SubdiffusiveProcess.EllipticRegularity.setAverage
  change (volume.real S)⁻¹ * ∫ q, (u q) ∂((volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))).restrict S) =
    (volume.real S)⁻¹ * ∫ q, (u q) ∂(volume.restrict S)
  rw [Measure.restrict_restrict_of_subset hS]

theorem aux_inputs_Cp_holder_setIntegral_eq_volume {d : ℕ}
    {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    (S : Set (SpatialCoordinates d)) (f : SpatialCoordinates d → ℝ)
    (hS : S ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))) :
    (∫ y in S, f y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) =
      ∫ y in S, f y ∂volume := by
  rw [Measure.restrict_restrict_of_subset hS]


/-- Coordinatewise clamp onto the closed cube of side `r` about `z` (a continuous retraction). -/
def aux_inputs_Cp_holder_clamp {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) :
    SpatialCoordinates d → SpatialCoordinates d :=
  fun x i => max (z i - r / 2) (min (x i) (z i + r / 2))

theorem aux_inputs_Cp_holder_clamp_continuous {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) :
    Continuous (aux_inputs_Cp_holder_clamp z r) := by
  unfold aux_inputs_Cp_holder_clamp
  exact continuous_pi fun i => continuous_const.max ((continuous_apply i).min continuous_const)

theorem aux_inputs_Cp_holder_clamp_mem {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (x : SpatialCoordinates d) :
    aux_inputs_Cp_holder_clamp z r x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
  show dist (aux_inputs_Cp_holder_clamp z r x) z ≤ r / 2
  rw [dist_pi_le_iff (by positivity)]
  intro i
  rw [Real.dist_eq, abs_le]
  simp only [aux_inputs_Cp_holder_clamp]
  constructor
  · have := le_max_left (z i - r / 2) (min (x i) (z i + r / 2))
    linarith
  · have : max (z i - r / 2) (min (x i) (z i + r / 2)) ≤ z i + r / 2 :=
      max_le (by linarith) (min_le_right _ _)
    linarith

theorem aux_inputs_Cp_holder_clamp_of_mem {d : ℕ} (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    {x : SpatialCoordinates d} (hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d))) :
    aux_inputs_Cp_holder_clamp z r x = x := by
  funext i
  have h : dist x z ≤ r / 2 := hx
  have hi := (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ r / 2)).1 h i
  rw [Real.dist_eq, abs_le] at hi
  simp only [aux_inputs_Cp_holder_clamp]
  rw [min_eq_left (by linarith [hi.2]), max_eq_right (by linarith [hi.1])]

/-- The normalised `L²` seminorm on a window about a constant only depends on the a.e. class of the function on
a set containing the window. -/
theorem aux_inputs_Cp_holder_normalizedL2On_congr_ae {d : ℕ}
    {Q B : Set (SpatialCoordinates d)} (hBQ : B ⊆ Q) {f g : SpatialCoordinates d → ℝ}
    (hfg : f =ᵐ[volume.restrict Q] g) (c : ℝ) :
    SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On B (fun y => f y - c) =
      SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On B (fun y => g y - c) := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On Homogenization.volumeAverage
  congr 2
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hBQ hfg] with y hy
  simp only [hy]

theorem inputs_Cp_holder (d : ℕ) :
    ∀ (alpha : ℝ), 0 < alpha → alpha < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ (u : DomainL2 (centeredCube z r hr)) (K : ℝ), 0 ≤ K →
      (∀ x ∈ centeredCube z r hr, ∀ rad : ℝ, 0 < rad → rad ≤ r →
        ∫ y in Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)),
            (u y - setAverage
              (Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d))) u) ^ 2
            ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) ≤
          K ^ 2 * rad ^ (2 * alpha) *
            volume.real (Metric.ball x rad ∩
              (centeredCube z r hr : Set (SpatialCoordinates d)))) →
      ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
        ((u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U) ∧
        IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
        holderSeminorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤ C * K := by
  intro alpha ha ha1
  have halpha : alpha ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha, ha1⟩
  have hCh0 : 0 ≤ aux_in_deterministic_regularity_holderConst d alpha :=
    aux_in_deterministic_regularity_holderConst_nonneg d ha
  refine ⟨aux_in_deterministic_regularity_holderConst d alpha + 1, by linarith, ?_⟩
  intro z r hr hr1 u K hK hosc
  set Ch : ℝ := aux_in_deterministic_regularity_holderConst d alpha with hChdef
  set C : ℝ := Ch + 1 with hCdef
  have hC : 0 < C := by linarith
  let U : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d))
  have hUopen : IsOpen U := (centeredCube z r hr).isOpen
  have hclosure : closure U = (closedCube z r hr : Set (SpatialCoordinates d)) :=
    campanato_closure_centeredCube_eq_closedCube z hr
  have hoscCamp : ∀ x ∈ U, ∀ rad : ℝ, 0 < rad → rad ≤ r →
      (∫ y in Metric.ball x rad ∩ U,
        (u y - (volume.real (Metric.ball x rad ∩ U))⁻¹ *
          ∫ q in Metric.ball x rad ∩ U, u q ∂volume) ^ 2) ≤
        K ^ 2 * rad ^ (2 * alpha) * volume.real (Metric.ball x rad ∩ U) := by
    intro x hx rad hrad hrad_r
    let S : Set (SpatialCoordinates d) := Metric.ball x rad ∩ U
    have hS : S ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      intro y hy
      exact hy.2
    have havg := aux_inputs_Cp_holder_setAverage_eq_volume S u hS
    have houter := aux_inputs_Cp_holder_setIntegral_eq_volume S
      (fun y => (u y - (volume.real S)⁻¹ * ∫ q in S, u q ∂volume) ^ 2) hS
    have hlocal := hosc x hx rad hrad hrad_r
    rw [havg] at hlocal
    calc
      (∫ y in Metric.ball x rad ∩ U,
          (u y - (volume.real (Metric.ball x rad ∩ U))⁻¹ *
            ∫ q in Metric.ball x rad ∩ U, u q ∂volume) ^ 2) =
        ∫ y in Metric.ball x rad ∩ U,
          (u y - (volume.real (Metric.ball x rad ∩ U))⁻¹ *
            ∫ q in Metric.ball x rad ∩ U, u q ∂volume) ^ 2
          ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) := by
            simpa [S, U] using houter.symm
      _ ≤ K ^ 2 * rad ^ (2 * alpha) * volume.real (Metric.ball x rad ∩ U) := by
        simpa [S, U] using hlocal
  have huMem : MemLp (u : SpatialCoordinates d → ℝ) 2 (volume.restrict U) := Lp.memLp u
  have : IsFiniteMeasure (volume.restrict U) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hu1 : IntegrableOn (u : SpatialCoordinates d → ℝ) U volume :=
    huMem.integrable (by norm_num)
  have hu2 : IntegrableOn (fun y => (u : SpatialCoordinates d → ℝ) y ^ 2) U volume :=
    huMem.integrable_sq
  set K' : ℝ := K * (r / 2) ^ alpha with hK'def
  have hK' : 0 ≤ K' := mul_nonneg hK (Real.rpow_nonneg (by positivity) _)
  -- the dyadic Campanato hypothesis for `u`, from the oscillation hypothesis at radius `r * 3^(-D) / 2`
  have hcampu : ∀ (D : ℕ), ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On (campanatoWindow z hr x D)
        (fun y => (u : SpatialCoordinates d → ℝ) y -
          campanatoAvg z hr (u : SpatialCoordinates d → ℝ) x D) ≤
        K' * ((3 : ℝ) ^ (-alpha)) ^ D := by
    intro D x hx
    set rad : ℝ := r * (3 : ℝ) ^ (-(D : ℤ)) / 2 with hraddef
    have hrad : 0 < rad := campanatoWindow_rad_pos z hr D
    have hradr : rad ≤ r := by
      have := campanatoWindow_two_rad_le z hr D
      linarith
    have hxc : x ∈ Metric.closedBall z (r / 2) := Metric.ball_subset_closedBall hx
    have hlow := aux_inputs_Cp_holder_ball_inter_lower_bound z x hr hrad hradr hxc
    have hSpos : 0 < volume.real (Metric.ball x rad ∩ U) := by
      have hpos : 0 < volume (Metric.ball x rad ∩ U) := by
        refine lt_of_lt_of_le ?_ hlow
        rw [ENNReal.ofReal_pos]
        positivity
      exact ENNReal.toReal_pos hpos.ne'
        (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_ball_lt_top).ne
    have hint := hoscCamp x hx rad hrad hradr
    have hW : campanatoWindow z hr x D = Metric.ball x rad ∩ U := rfl
    have hsq : K ^ 2 * rad ^ (2 * alpha) = (K * rad ^ alpha) ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast (rad ^ alpha) 2, ← Real.rpow_mul hrad.le]
      congr 2
      push_cast
      ring
    have hkey : ((3 : ℝ) ^ (-(D : ℤ))) ^ alpha = ((3 : ℝ) ^ (-alpha)) ^ D := by
      rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]
      congr 1
      push_cast
      ring
    have hradpow : rad ^ alpha = (r / 2) ^ alpha * ((3 : ℝ) ^ (-alpha)) ^ D := by
      rw [hraddef, show r * (3 : ℝ) ^ (-(D : ℤ)) / 2 = r / 2 * (3 : ℝ) ^ (-(D : ℤ)) by ring,
        Real.mul_rpow (by positivity) (by positivity), hkey]
    have hnonneg : 0 ≤ K * rad ^ alpha := mul_nonneg hK (Real.rpow_nonneg hrad.le _)
    have hgoal : K * rad ^ alpha = K' * ((3 : ℝ) ^ (-alpha)) ^ D := by
      rw [hradpow, hK'def]
      ring
    rw [← hgoal, hW]
    unfold SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On Homogenization.volumeAverage
    have hcamAvg : campanatoAvg z hr (u : SpatialCoordinates d → ℝ) x D =
        (volume.real (Metric.ball x rad ∩ U))⁻¹ * ∫ q in Metric.ball x rad ∩ U, u q ∂volume := rfl
    rw [hcamAvg]
    calc Real.sqrt ((volume (Metric.ball x rad ∩ U)).toReal⁻¹ *
          ∫ y in Metric.ball x rad ∩ U, (u y - (volume.real (Metric.ball x rad ∩ U))⁻¹ *
            ∫ q in Metric.ball x rad ∩ U, u q ∂volume) ^ 2)
        ≤ Real.sqrt ((K * rad ^ alpha) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [← hsq]
          have hSpos' : 0 < (volume (Metric.ball x rad ∩ U)).toReal := hSpos
          rw [inv_mul_le_iff₀ hSpos']
          calc _ ≤ K ^ 2 * rad ^ (2 * alpha) * volume.real (Metric.ball x rad ∩ U) := hint
            _ = (volume (Metric.ball x rad ∩ U)).toReal * (K ^ 2 * rad ^ (2 * alpha)) := by
              rw [mul_comm]; rfl
      _ = K * rad ^ alpha := Real.sqrt_sq hnonneg
  obtain ⟨U', hU'cont, hU'ae⟩ :=
    aux_campanato_continuous_representative z hr halpha hK' hu1 hu2 hcampu
  have hU'cl : ContinuousOn U' (closure (centeredCube z r hr : Set (SpatialCoordinates d))) := by
    rw [campanato_closure_centeredCube_eq_closedCube z hr]
    exact hU'cont
  have hcampU' : ∀ (D : ℕ), ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      let B : Set (SpatialCoordinates d) :=
        Metric.ball x (r * (3 : ℝ) ^ (-(D : ℤ)) / 2) ∩
          (centeredCube z r hr : Set (SpatialCoordinates d))
      SubdiffusiveProcess.CoarseGrainingVocab.normalizedL2On B
        (fun y => U' y - (volume.real B)⁻¹ * ∫ t in B, U' t) ≤
        K' * ((3 : ℝ) ^ (-alpha)) ^ D := by
    intro D x hx B
    have hBQ : B ⊆ U := Set.inter_subset_right
    have hae : ∀ᵐ t ∂volume.restrict B, U' t = (u : SpatialCoordinates d → ℝ) t :=
      ae_restrict_of_ae_restrict_of_subset hBQ hU'ae
    have hint : ∫ t in B, U' t = ∫ t in B, (u : SpatialCoordinates d → ℝ) t :=
      integral_congr_ae hae
    rw [hint, aux_inputs_Cp_holder_normalizedL2On_congr_ae hBQ hU'ae]
    exact hcampu D x hx
  obtain ⟨-, hbound, -⟩ :=
    _root_.SubdiffusiveProcess.Paper.aux_in_deterministic_regularity_campanato_holder alpha halpha z r hr U' hU'cl K' hK'
      hcampU'
  set V : SpatialCoordinates d → ℝ := U' ∘ aux_inputs_Cp_holder_clamp z r with hVdef
  have hVcont : Continuous V :=
    hU'cont.comp_continuous (aux_inputs_Cp_holder_clamp_continuous z r)
      (aux_inputs_Cp_holder_clamp_mem z hr)
  have hVeq : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), V x = U' x := by
    intro x hx
    simp only [hVdef, Function.comp, aux_inputs_Cp_holder_clamp_of_mem z hr hx]
  have hVae : (u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict U] V := by
    filter_upwards [hU'ae, ae_restrict_mem hUopen.measurableSet] with x hx hxU
    have hxc : x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) := by
      rw [← hclosure]
      exact subset_closure hxU
    rw [hVeq x hxc, hx]
  have hVholder : ∀ x ∈ closure U, ∀ y ∈ closure U, |V x - V y| ≤ C * K * ‖x - y‖ ^ alpha := by
    intro x hx y hy
    have hx' := hx
    have hy' := hy
    rw [hclosure] at hx' hy'
    rw [hVeq x hx', hVeq y hy']
    have hb := hbound x (by rw [campanato_closure_centeredCube_eq_closedCube z hr]; exact hx') y
      (by rw [campanato_closure_centeredCube_eq_closedCube z hr]; exact hy')
    have ht : 0 ≤ ‖x - y‖ := norm_nonneg _
    have hdist : dist x y = ‖x - y‖ := dist_eq_norm x y
    rw [hdist] at hb
    have hprod : (r / 2) ^ alpha * (‖x - y‖ / r) ^ alpha = (‖x - y‖ / 2) ^ alpha := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      field_simp
    have hstep : Ch * K' * (‖x - y‖ / r) ^ alpha = Ch * K * (‖x - y‖ / 2) ^ alpha := by
      calc Ch * K' * (‖x - y‖ / r) ^ alpha = Ch * K * ((r / 2) ^ alpha * (‖x - y‖ / r) ^ alpha) := by
            rw [hK'def]; ring
        _ = Ch * K * (‖x - y‖ / 2) ^ alpha := by rw [hprod]
    have hle : (‖x - y‖ / 2) ^ alpha ≤ ‖x - y‖ ^ alpha :=
      Real.rpow_le_rpow (by positivity) (by linarith) ha.le
    have hKt : 0 ≤ K * ‖x - y‖ ^ alpha := mul_nonneg hK (Real.rpow_nonneg ht _)
    calc |U' x - U' y| ≤ Ch * K' * (‖x - y‖ / r) ^ alpha := hb
      _ = Ch * K * (‖x - y‖ / 2) ^ alpha := hstep
      _ ≤ Ch * K * ‖x - y‖ ^ alpha :=
          mul_le_mul_of_nonneg_left hle (mul_nonneg hCh0 hK)
      _ ≤ C * K * ‖x - y‖ ^ alpha := by
          rw [hCdef]
          nlinarith [hKt]
  have hCK : 0 ≤ C * K := mul_nonneg hC.le hK
  have hratioBound : ∀ q ∈ holderRatioSet alpha
      (closedCube z r hr : Set (SpatialCoordinates d)) V, q ≤ C * K := by
    intro q hq
    rcases hq with ⟨x, hx, y, hy, hxy, hqeq⟩
    rw [hqeq]
    have hx' : x ∈ closure U := by
      rw [hclosure]
      exact hx
    have hy' : y ∈ closure U := by
      rw [hclosure]
      exact hy
    have hpiEuclidean : ‖x - y‖ ≤
        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      simpa [Homogenization.euclideanNorm, Homogenization.vecNormSq,
        Homogenization.vecDot, pow_two] using Homogenization.norm_le_euclideanNorm (x - y)
    have hpow : ‖x - y‖ ^ alpha ≤
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
      Real.rpow_le_rpow (norm_nonneg _) hpiEuclidean ha.le
    have hdiffBound : |V x - V y| ≤
        C * K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
      calc
        |V x - V y| ≤ C * K * ‖x - y‖ ^ alpha := hVholder x hx' y hy'
        _ ≤ C * K * (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha :=
          mul_le_mul_of_nonneg_left hpow hCK
    have hdiff : x - y ≠ (0 : SpatialCoordinates d) := sub_ne_zero.mpr hxy
    have hEucNe : Homogenization.euclideanNorm (x - y) ≠ 0 := by
      intro hzero
      exact hdiff (Homogenization.euclideanNorm_eq_zero_iff.mp hzero)
    have hEucPos : 0 < Homogenization.euclideanNorm (x - y) :=
      lt_of_le_of_ne (Homogenization.euclideanNorm_nonneg _) (Ne.symm hEucNe)
    have heq : Homogenization.euclideanNorm (x - y) =
        Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
      simp [Homogenization.euclideanNorm, Homogenization.vecNormSq,
        Homogenization.vecDot, pow_two]
    have hdenom : 0 <
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ alpha := by
      rw [← heq]
      exact Real.rpow_pos_of_pos hEucPos alpha
    exact (div_le_iff₀ hdenom).2 hdiffBound
  have hIsHolder : IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) V :=
    ⟨C * K, hratioBound⟩
  have hseminorm : holderSeminorm alpha
      (closedCube z r hr : Set (SpatialCoordinates d)) V ≤ C * K := by
    unfold _root_.SubdiffusiveProcess.EllipticRegularity.holderSeminorm
    by_cases hn : (holderRatioSet alpha
        (closedCube z r hr : Set (SpatialCoordinates d)) V).Nonempty
    · exact csSup_le hn hratioBound
    · have hempty : holderRatioSet alpha
        (closedCube z r hr : Set (SpatialCoordinates d)) V = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hn
      simpa [hempty] using hCK
  exact ⟨V, hVcont, hVae, hIsHolder, hseminorm⟩

end SubdiffusiveProcess.Paper
