module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.MultiplicativeChaos.ChaosBasic
public import SubdiffusiveProcess.MultiplicativeChaos.TriadicGrid
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.lane4_reference_point_moments
public import SubdiffusiveProcess.Paper.lane4_reference_oscillation_moments
public import SubdiffusiveProcess.Paper.lane4_reference_mesh_envelope
public import SubdiffusiveProcess.Main.InfraredAdmissible

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

namespace SubdiffusiveProcess.Paper

lemma aux_lane4_reference_mesh_statistic_exp_compare
    (A gx gy c o : ℝ) (hA : 0 ≤ A) (ho : |gx - gy| ≤ o) :
    Real.exp (-o) * (A * Real.exp (gy - c)) ≤ A * Real.exp (gx - c) ∧
      A * Real.exp (gx - c) ≤ Real.exp o * (A * Real.exp (gy - c)) := by
  have hlo : gy - c - o ≤ gx - c := by
    have h := (abs_le.mp ho).1
    linarith
  have hhi : gx - c ≤ gy - c + o := by
    have h := (abs_le.mp ho).2
    linarith
  have hElow : Real.exp (gy - c - o) ≤ Real.exp (gx - c) :=
    Real.exp_le_exp.mpr hlo
  have hEhi : Real.exp (gx - c) ≤ Real.exp (gy - c + o) :=
    Real.exp_le_exp.mpr hhi
  constructor
  · calc
      Real.exp (-o) * (A * Real.exp (gy - c)) =
          A * Real.exp (gy - c - o) := by
            calc
              Real.exp (-o) * (A * Real.exp (gy - c)) =
                  A * (Real.exp (-o) * Real.exp (gy - c)) := by ring
              _ = A * Real.exp (gy - c - o) := by
                rw [← Real.exp_add]
                congr 1
                ring_nf
      _ ≤ A * Real.exp (gx - c) := by
        exact mul_le_mul_of_nonneg_left hElow hA
  · calc
      A * Real.exp (gx - c) ≤ A * Real.exp (gy - c + o) := by
        exact mul_le_mul_of_nonneg_left hEhi hA
      _ = Real.exp o * (A * Real.exp (gy - c)) := by
        calc
          A * Real.exp (gy - c + o) =
              A * (Real.exp (gy - c) * Real.exp o) := by
                rw [Real.exp_add]
          _ = Real.exp o * (A * Real.exp (gy - c)) := by ring

lemma aux_lane4_reference_mesh_statistic_average_bounds
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (f : SpatialCoordinates d → ℝ) (lo hi : ℝ)
    (hvol : 0 < volume.real (Metric.ball z r))
    (hfi : IntegrableOn f (Metric.ball z r) volume)
    (hlo : ∀ x ∈ Metric.ball z r, lo ≤ f x)
    (hhi : ∀ x ∈ Metric.ball z r, f x ≤ hi) :
    lo ≤ (volume.real (Metric.ball z r))⁻¹ * ∫ x in Metric.ball z r, f x ∧
      (volume.real (Metric.ball z r))⁻¹ * ∫ x in Metric.ball z r, f x ≤ hi := by
  have hvoltop : volume (Metric.ball z r) ≠ ∞ := by
    rw [SubdiffusiveProcess.volume_ball_spatial z hr]
    exact ENNReal.ofReal_ne_top
  have hlo_int : (∫ _ in Metric.ball z r, lo) ≤
      ∫ x in Metric.ball z r, f x := by
    apply setIntegral_mono_on (integrableOn_const hvoltop) hfi measurableSet_ball
    intro x hx
    exact hlo x hx
  have hhi_int : (∫ x in Metric.ball z r, f x) ≤
      ∫ _ in Metric.ball z r, hi := by
    apply setIntegral_mono_on hfi (integrableOn_const hvoltop) measurableSet_ball
    intro x hx
    exact hhi x hx
  have hconst_lo : (∫ _ in Metric.ball z r, lo) =
      volume.real (Metric.ball z r) * lo := by
    rw [setIntegral_const, smul_eq_mul]
  have hconst_hi : (∫ _ in Metric.ball z r, hi) =
      volume.real (Metric.ball z r) * hi := by
    rw [setIntegral_const, smul_eq_mul]
  have hlo' : lo ≤ (volume.real (Metric.ball z r))⁻¹ *
      ∫ x in Metric.ball z r, f x := by
    have hmul := mul_le_mul_of_nonneg_left hlo_int (inv_pos.mpr hvol).le
    calc
      lo = (volume.real (Metric.ball z r))⁻¹ *
          (volume.real (Metric.ball z r) * lo) := by field_simp
      _ = (volume.real (Metric.ball z r))⁻¹ *
          (∫ _ in Metric.ball z r, lo) := by rw [hconst_lo]
      _ ≤ (volume.real (Metric.ball z r))⁻¹ *
          ∫ x in Metric.ball z r, f x := hmul
  have hhi' : (volume.real (Metric.ball z r))⁻¹ *
      ∫ x in Metric.ball z r, f x ≤ hi := by
    have hmul := mul_le_mul_of_nonneg_left hhi_int (inv_pos.mpr hvol).le
    calc
      (volume.real (Metric.ball z r))⁻¹ *
          ∫ x in Metric.ball z r, f x ≤
          (volume.real (Metric.ball z r))⁻¹ *
            (∫ _ in Metric.ball z r, hi) := hmul
      _ = (volume.real (Metric.ball z r))⁻¹ *
          (volume.real (Metric.ball z r) * hi) := by rw [hconst_hi]
      _ = hi := by field_simp
  constructor
  · exact hlo'
  · exact hhi'

lemma aux_lane4_reference_mesh_statistic_mesh_point
    (d J k : ℕ) (_hJ : 1 ≤ J) (z : SpatialCoordinates d)
    (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1) :
    ∃ a : Fin d → Fin (3^(k + J) + 1),
      dist z (fun i => (a i : ℝ) * (3 : ℝ)^(-((k + J : ℕ) : ℤ))) ≤
        (3 : ℝ)^(-((k + J : ℕ) : ℤ)) ∧
      (∀ i, 0 ≤ (a i : ℝ) * (3 : ℝ)^(-((k + J : ℕ) : ℤ)) ∧
        (a i : ℝ) * (3 : ℝ)^(-((k + J : ℕ) : ℤ)) ≤ 1) ∧
      Metric.ball z ((3 : ℝ)^(-(k : ℤ)) / 2) ⊆
        Metric.closedBall
          (fun i => (a i : ℝ) * (3 : ℝ)^(-((k + J : ℕ) : ℤ)))
          (3 * ((3 : ℝ)^(-(k : ℤ)) / 2)) := by
  let h : ℝ := (3 : ℝ)^(-((k + J : ℕ) : ℤ))
  have hh : 0 < h := by
    dsimp [h]
    positivity
  have hscale : (3 : ℝ)^(k + J) * h = 1 := by
    dsimp [h]
    rw [← zpow_natCast]
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    rw [← zpow_zero (3 : ℝ)]
    congr 1
    push_cast
    ring
  let a : Fin d → Fin (3^(k + J) + 1) := fun i =>
    ⟨⌊z i / h⌋₊, by
      have hdiv0 : 0 ≤ z i / h := div_nonneg (hz i).1 hh.le
      have hdivle : z i / h ≤ (3 : ℝ)^(k + J) := by
        apply (div_le_iff₀ hh).2
        calc
          z i ≤ 1 := (hz i).2
          _ = (3 : ℝ)^(k + J) * h := by rw [hscale]
      have hdivle' : z i / h ≤ ((3^(k + J) : ℕ) : ℝ) := by
        simpa using hdivle
      have hfloor : ⌊z i / h⌋₊ ≤ 3^(k + J) :=
        Nat.floor_le_of_le hdivle'
      omega⟩
  have hdist : dist z (fun i => (a i : ℝ) * h) ≤ h := by
    rw [dist_pi_le_iff hh.le]
    intro i
    have hdiv0 : 0 ≤ z i / h := div_nonneg (hz i).1 hh.le
    have hfloorle : (⌊z i / h⌋₊ : ℝ) ≤ z i / h := Nat.floor_le hdiv0
    have hfloorlt : z i / h < (⌊z i / h⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hmul_le : (⌊z i / h⌋₊ : ℝ) * h ≤ z i := by
      calc
        (⌊z i / h⌋₊ : ℝ) * h ≤ (z i / h) * h :=
          mul_le_mul_of_nonneg_right hfloorle hh.le
        _ = z i := by field_simp
    have hmul_lt : z i < (⌊z i / h⌋₊ : ℝ) * h + h := by
      have h' := (div_lt_iff₀ hh).mp hfloorlt
      convert h' using 1 ; ring
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have hcoords : ∀ i, 0 ≤ (a i : ℝ) * h ∧ (a i : ℝ) * h ≤ 1 := by
    intro i
    have hfloor0 : 0 ≤ (a i : ℝ) := by positivity
    have hdiv0 : 0 ≤ z i / h := div_nonneg (hz i).1 hh.le
    have hfloorle : (⌊z i / h⌋₊ : ℝ) ≤ z i / h := Nat.floor_le hdiv0
    have hmul_le : (a i : ℝ) * h ≤ z i := by
      change (⌊z i / h⌋₊ : ℝ) * h ≤ z i
      calc
        (⌊z i / h⌋₊ : ℝ) * h ≤ (z i / h) * h :=
          mul_le_mul_of_nonneg_right hfloorle hh.le
        _ = z i := by field_simp
    exact ⟨mul_nonneg hfloor0 hh.le, hmul_le.trans (hz i).2⟩
  have hbase : h ≤ (3 : ℝ)^(-(k : ℤ)) := by
    dsimp [h]
    rw [neg_add, zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    calc
      (3 : ℝ)^(-(k : ℤ)) * (3 : ℝ)^(-(J : ℤ)) ≤
          (3 : ℝ)^(-(k : ℤ)) * 1 := by
        gcongr
        exact SubdiffusiveProcess.three_zpow_neg_le_one J
      _ = (3 : ℝ)^(-(k : ℤ)) := by ring
  refine ⟨a, ?_, ?_, ?_⟩
  · change dist z (fun i => (a i : ℝ) * h) ≤ h
    exact hdist
  · change ∀ i, 0 ≤ (a i : ℝ) * h ∧ (a i : ℝ) * h ≤ 1
    exact hcoords
  · intro x hx
    have hxy : dist x (fun i => (a i : ℝ) * h) ≤
        dist x z + dist z (fun i => (a i : ℝ) * h) := dist_triangle _ _ _
    have hxz : dist x z < (3 : ℝ)^(-(k : ℤ)) / 2 := by
      exact (Metric.mem_ball.mp hx).trans_le le_rfl
    have hsum' : dist x z + dist z (fun i => (a i : ℝ) * h) ≤
        (3 : ℝ)^(-(k : ℤ)) / 2 + h := by
      exact add_le_add (le_of_lt hxz) hdist
    have hsum : dist x (fun i => (a i : ℝ) * h) ≤
        (3 : ℝ)^(-(k : ℤ)) / 2 + h := hxy.trans hsum'
    have hle : h ≤ 2 * ((3 : ℝ)^(-(k : ℤ)) / 2) := by
      linarith
    apply Metric.mem_closedBall.mpr
    linarith

lemma aux_lane4_reference_mesh_statistic_oscillation
    {d : ℕ} (_k : ℕ) (R : ℝ) (hR : 0 < R)
    (g : C(SpatialCoordinates d, ℝ)) (y : SpatialCoordinates d) :
    let S : Set ℝ := {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R),
      ∃ x' ∈ Metric.closedBall y (3 * R), v = |g x - g x'|}
    S.Nonempty ∧ BddAbove S ∧ IsLUB S (sSup S) := by
  let T : Set (SpatialCoordinates d) := Metric.closedBall y (3 * R)
  let F : SpatialCoordinates d × SpatialCoordinates d → ℝ :=
    fun u => |g u.1 - g u.2|
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hcompact : IsCompact (F '' (T ×ˢ T)) := by
    exact ((isCompact_closedBall y (3 * R)).prod
      (isCompact_closedBall y (3 * R))).image_of_continuousOn hFcont.continuousOn
  have hset : {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R),
      ∃ x' ∈ Metric.closedBall y (3 * R), v = |g x - g x'|} =
      F '' (T ×ˢ T) := by
    ext v
    constructor
    · rintro ⟨x, hx, x', hx', rfl⟩
      exact ⟨(x, x'), ⟨hx, hx'⟩, rfl⟩
    · rintro ⟨⟨x, x'⟩, ⟨hx, hx'⟩, rfl⟩
      exact ⟨x, hx, x', hx', rfl⟩
  have hne : (F '' (T ×ˢ T)).Nonempty := by
    refine ⟨F (y, y), ⟨(y, y), ?_, rfl⟩⟩
    exact ⟨Metric.mem_closedBall_self (by positivity),
      Metric.mem_closedBall_self (by positivity)⟩
  dsimp
  rw [hset]
  exact ⟨hne, hcompact.bddAbove, hcompact.isLUB_sSup hne⟩

/-- Admissible-infrared form of `lane4_reference_mesh_statistic`: the characterized field or a finite infrared truncation. -/
theorem aux_lane4_reference_mesh_statistic_adm
    (d J : ℕ) (hd : 2 ≤ d) (hJ : 1 ≤ J)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (p q eta : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (heta : 0 < eta) :
    ∃ qref : ℝ, p ≤ qref ∧ q ≤ qref ∧ (d : ℝ) < qref * eta ∧
    ∃ delta0 Cmom Crate Cosc CV : ℝ,
      0 < delta0 ∧ 0 < Cmom ∧ 0 < Crate ∧ 0 < Cosc ∧ 0 < CV ∧
      delta0 ≤ 1 ∧
      Crate * ((2 * qref) + (2 * qref)^2) * delta0^2 <
        (eta - (d : ℝ) / qref) * Real.log 3 / 4 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredAdmissible M H → M.delta ≤ delta0 →
        let P := (chaosSampleLaw M).toMeasure
        let K : Set (SpatialCoordinates d) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let s : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun N k omega x =>
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
              Real.exp (G k omega x - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
        let root : ℕ → SpatialCoordinates d → Set (SpatialCoordinates d) :=
          fun k z => Metric.ball z (R k)
        let b : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun N k omega z => (volume.real (root k z))⁻¹ * ∫ x in root k z, s N k omega x
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k), v = |G k omega x - G k omega x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega y => sSup (oscSet k omega y)
        let Grid : ℕ → Type := fun k => Fin d → Fin (3^(k + J) + 1)
        let ygrid : (k : ℕ) → Grid k → SpatialCoordinates d :=
          fun k a i => (a i : ℝ) * (3 : ℝ)^(-((k + J : ℕ) : ℤ))
        let spacing : ℕ → ℝ := fun k => (3 : ℝ)^(-((k + J : ℕ) : ℤ))
        let Z : (N k : ℕ) → BilateralField d → Grid k → ℝ :=
          fun N k omega a => Real.exp (osc k omega (ygrid k a)) *
            (s N k omega (ygrid k a) + (s N k omega (ygrid k a))⁻¹)
        (∀ (omega : BilateralField d) (N k : ℕ), k ≤ N →
          ∀ z ∈ K, 0 < b N k omega z) ∧
        (∀ (omega : BilateralField d) (k : ℕ) (y : SpatialCoordinates d), y ∈ K →
          (oscSet k omega y).Nonempty ∧ BddAbove (oscSet k omega y) ∧
            IsLUB (oscSet k omega y) (osc k omega y)) ∧
        (∀ (k : ℕ) (z : SpatialCoordinates d), z ∈ K →
          ∃ a : Grid k, dist z (ygrid k a) ≤ spacing k ∧ ygrid k a ∈ K ∧
            root k z ⊆ Metric.closedBall (ygrid k a) (3 * R k) ∧
            ∀ (N : ℕ), k ≤ N → ∀ omega : BilateralField d,
              Real.exp (-osc k omega (ygrid k a)) * s N k omega (ygrid k a) ≤
                b N k omega z ∧
              b N k omega z ≤
                Real.exp (osc k omega (ygrid k a)) * s N k omega (ygrid k a)) ∧
        (∀ aexp : ℝ, aexp ∈ Set.Icc 1 (2 * q) →
          ∀ (N k : ℕ), k ≤ N → ∀ y ∈ K,
            Integrable (fun omega => (s N k omega y)^aexp +
              (s N k omega y)^(-aexp)) P ∧
            (∫ omega, (s N k omega y)^aexp + (s N k omega y)^(-aexp) ∂P) ≤
              Cmom * Real.exp (Crate * (aexp + aexp^2) * M.delta^2 * (k : ℝ)) ∧
            MemLp (fun omega => s N k omega y) (ENNReal.ofReal aexp) P ∧
            MemLp (fun omega => (s N k omega y)⁻¹) (ENNReal.ofReal aexp) P) ∧
        (∀ (k : ℕ) (y : SpatialCoordinates d), y ∈ K →
          MemLp (fun omega => Real.exp (osc k omega y)) (ENNReal.ofReal (2 * qref)) P ∧
          eLpNorm (fun omega => Real.exp (osc k omega y)) (ENNReal.ofReal (2 * qref)) P ≤
            ENNReal.ofReal Cosc) ∧
        (∃ V : ℕ → BilateralField d → ℝ,
          (∀ N, Measurable (V N)) ∧
          (∀ N omega, 0 ≤ V N omega) ∧
          (∀ N, MemLp (V N) (ENNReal.ofReal p) P) ∧
          (∀ N, eLpNorm (V N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal CV) ∧
          ∀ᵐ omega ∂P, ∀ N : ℕ,
            IsLUB {v : ℝ | ∃ k : ℕ, k ≤ N ∧ ∃ a : Grid k,
              v = (R k)^eta * Z N k omega a} (V N omega) ∧
            ∀ k : ℕ, k ≤ N → ∀ z ∈ K,
              b N k omega z + (b N k omega z)⁻¹ ≤ V N omega * (R k)^(-eta)) := by
  let qref : ℝ := max (max p q) ((d : ℝ) / eta + 1)
  have hpqref : p ≤ qref := by
    exact le_max_of_le_left (le_max_left p q)
  have hqqref : q ≤ qref := by
    exact le_max_of_le_left (le_max_right p q)
  have hqref_pos : 0 < qref := by
    have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
    exact hqpos.trans_le hqqref
  have hqref_one : 1 ≤ qref := hq.trans hqqref
  have hqref_gap : (d : ℝ) < qref * eta := by
    have hbase : (d : ℝ) / eta + 1 ≤ qref := le_max_right _ _
    have hmul := mul_le_mul_of_nonneg_right hbase heta.le
    have heq : ((d : ℝ) / eta + 1) * eta = (d : ℝ) + eta := by
      field_simp
    rw [heq] at hmul
    linarith
  obtain ⟨Cmom, Crate, hCmom, hCrate, hpoint⟩ :=
    lane4_reference_point_moments d hd q hq
  obtain ⟨Cosc, hCosc, hosc⟩ :=
    lane4_reference_oscillation_moments d hd qref hqref_one
  obtain ⟨deltaMesh, CV, hdeltaMesh, hCV, hdeltaMesh_le, hmesh⟩ :=
    lane4_reference_mesh_envelope d J hd hJ p qref eta hp hpqref heta hqref_gap
  let A : ℝ := Crate * ((2 * qref) + (2 * qref)^2)
  let B : ℝ := (eta - (d : ℝ) / qref) * Real.log 3 / 4
  let eps : ℝ := B / (2 * (A + 1))
  let delta0 : ℝ := min deltaMesh (min 1 eps)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hB : 0 < B := by
    dsimp [B]
    have hratio : (d : ℝ) / qref < eta := by
      exact (div_lt_iff₀ hqref_pos).2 (by simpa [mul_comm] using hqref_gap)
    have hfactor : 0 < eta - (d : ℝ) / qref := sub_pos.mpr hratio
    positivity
  have hA : 0 < A := by
    dsimp [A]
    have hqterm : 0 < (2 * qref) + (2 * qref)^2 := by positivity
    positivity
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have hdelta0 : 0 < delta0 := by
    dsimp [delta0]
    exact lt_min hdeltaMesh (lt_min zero_lt_one heps)
  have hdelta0_le_one : delta0 ≤ 1 := by
    exact (min_le_right deltaMesh (min 1 eps)).trans (min_le_left 1 eps)
  have hdelta0_le_mesh : delta0 ≤ deltaMesh := min_le_left _ _
  have hdelta0_le_eps : delta0 ≤ eps := by
    exact (min_le_right deltaMesh (min 1 eps)).trans (min_le_right 1 eps)
  have heps_bound : A * eps < B := by
    dsimp [eps]
    have hden : 0 < 2 * (A + 1) := by positivity
    rw [show A * (B / (2 * (A + 1))) = (A * B) / (2 * (A + 1)) by ring]
    apply (div_lt_iff₀ hden).2
    nlinarith
  have hdelta_sq : delta0 ^ 2 ≤ delta0 := by
    have hnonneg : 0 ≤ delta0 := hdelta0.le
    nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hdelta0_le_one)]
  have hbudget : A * delta0^2 < B := by
    calc
      A * delta0^2 ≤ A * delta0 := by
        exact mul_le_mul_of_nonneg_left hdelta_sq hA.le
      _ ≤ A * eps := by
        exact mul_le_mul_of_nonneg_left hdelta0_le_eps hA.le
      _ < B := heps_bound
  refine ⟨qref, hpqref, hqqref, hqref_gap, ?_⟩
  refine ⟨delta0, Cmom, Crate, Cosc, CV, hdelta0, hCmom, hCrate, hCosc,
    hCV, hdelta0_le_one, ?_, ?_⟩
  · simpa [A, B] using hbudget
  · intro M Rm H hH hMdelta
    dsimp
    have hpoint' := hpoint delta0 hdelta0 hdelta0_le_one M Rm H hH hMdelta
    have hosc' := hosc delta0 hdelta0 hdelta0_le_one M H hH hMdelta
    have hmesh' := hmesh M Rm H hH (le_trans hMdelta hdelta0_le_mesh)
    dsimp at hpoint' hosc' hmesh'
    let K0 : Set (SpatialCoordinates d) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
    let R0 : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
    let G0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
      fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
    let s0 : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
      fun N k omega x =>
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp (G0 k omega x - (k : ℝ) *
            _root_.SubdiffusiveProcess.Model.tauSq M.P)
    let root0 : ℕ → SpatialCoordinates d → Set (SpatialCoordinates d) :=
      fun k z => Metric.ball z (R0 k)
    let b0 : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
      fun N k omega z => (volume.real (root0 k z))⁻¹ *
        ∫ x in root0 k z, s0 N k omega x
    let oscSet0 : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
      fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R0 k),
        ∃ x' ∈ Metric.closedBall y (3 * R0 k),
          v = |G0 k omega x - G0 k omega x'|}
    let osc0 : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
      fun k omega y => sSup (oscSet0 k omega y)
    let Grid0 : ℕ → Type := fun k => Fin d → Fin (3^(k + J) + 1)
    let ygrid0 : (k : ℕ) → Grid0 k → SpatialCoordinates d :=
      fun k a i => (a i : ℝ) * (3 : ℝ)^(-((k + J : ℕ) : ℤ))
    let spacing0 : ℕ → ℝ := fun k => (3 : ℝ)^(-((k + J : ℕ) : ℤ))
    let Z0 : (N k : ℕ) → BilateralField d → Grid0 k → ℝ :=
      fun N k omega a => Real.exp (osc0 k omega (ygrid0 k a)) *
        (s0 N k omega (ygrid0 k a) +
          (s0 N k omega (ygrid0 k a))⁻¹)
    have hcomparison : ∀ (k : ℕ)
        (z : SpatialCoordinates d), z ∈ K0 →
      ∃ a : Grid0 k,
        dist z (ygrid0 k a) ≤ spacing0 k ∧ ygrid0 k a ∈ K0 ∧
        root0 k z ⊆ Metric.closedBall (ygrid0 k a) (3 * R0 k) ∧
        ∀ (N : ℕ) (omega : BilateralField d),
          Real.exp (-osc0 k omega (ygrid0 k a)) *
              s0 N k omega (ygrid0 k a) ≤ b0 N k omega z ∧
          b0 N k omega z ≤ Real.exp (osc0 k omega (ygrid0 k a)) *
              s0 N k omega (ygrid0 k a) := by
      intro k z hz
      obtain ⟨a, hadist, hay, hroot⟩ :=
        aux_lane4_reference_mesh_statistic_mesh_point d J k hJ z hz
      refine ⟨a, ?_, ?_, ?_, ?_⟩
      · simpa [spacing0, ygrid0] using hadist
      · simpa [K0, ygrid0] using hay
      · simpa [root0, R0, ygrid0] using hroot
      · intro N omega
        let y : SpatialCoordinates d := ygrid0 k a
        let g : C(SpatialCoordinates d, ℝ) :=
          H omega + ∑ j ∈ Finset.range k, omega (-(j : ℤ))
        have hR : 0 < R0 k := by
          dsimp [R0]
          positivity
        have hg : ∀ x, g x = G0 k omega x := by
          intro x
          simp [g, G0]
        have hosc_lub := aux_lane4_reference_mesh_statistic_oscillation
          k (R0 k) hR g y
        have hosc_bdd : BddAbove (oscSet0 k omega y) := by
          simpa [oscSet0, G0, g, y] using hosc_lub.2.1
        have hosc_isLUB : IsLUB (oscSet0 k omega y) (osc0 k omega y) := by
          simpa [osc0, oscSet0, G0, g, y] using hosc_lub.2.2
        let A0 : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M N
        let c0 : ℝ := (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P
        have hA0 : 0 ≤ A0 := by
          dsimp [A0]
          exact div_nonneg
            (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N - k)).le
            (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).le
        let f0 : SpatialCoordinates d → ℝ := fun x =>
          A0 * Real.exp (G0 k omega x - c0)
        have hfcont : Continuous f0 := by
          dsimp [f0, G0, c0, A0]
          fun_prop
        have hfi : IntegrableOn f0 (root0 k z) volume := by
          apply (hfcont.continuousOn.integrableOn_compact
            (isCompact_closedBall z (R0 k))).mono_set
          exact Metric.ball_subset_closedBall
        have hvol : 0 < volume.real (root0 k z) := by
          dsimp [root0]
          rw [Measure.real, SubdiffusiveProcess.volume_ball_spatial z hR,
            ENNReal.toReal_ofReal (by positivity)]
          positivity
        have hpointwise : ∀ x ∈ root0 k z,
            Real.exp (-osc0 k omega y) * f0 y ≤ f0 x ∧
              f0 x ≤ Real.exp (osc0 k omega y) * f0 y := by
          intro x hx
          have hx' : x ∈ Metric.closedBall y (3 * R0 k) := hroot hx
          have hmem : |g x - g y| ∈ oscSet0 k omega y := by
            refine ⟨x, ?_, y, Metric.mem_closedBall_self (by positivity), ?_⟩
            · simpa [g, G0, y]
            · rw [hg x, hg y]
          have hoscx : |g x - g y| ≤ osc0 k omega y := hosc_isLUB.1 hmem
          have hcomp := aux_lane4_reference_mesh_statistic_exp_compare
            A0 (G0 k omega x) (G0 k omega y) c0 (osc0 k omega y) hA0
            (by simpa [g, G0, y] using hoscx)
          simpa [f0, s0, A0, c0, g, G0, y] using hcomp
        have havg := aux_lane4_reference_mesh_statistic_average_bounds
          z (R0 k) hR f0
          (Real.exp (-osc0 k omega y) * f0 y)
          (Real.exp (osc0 k omega y) * f0 y)
          hvol hfi
          (fun x hx => (hpointwise x hx).1)
          (fun x hx => (hpointwise x hx).2)
        exact ⟨by
          simpa [b0, s0, f0, A0, c0, osc0, ygrid0, y, root0] using havg.1,
          by
            simpa [b0, s0, f0, A0, c0, osc0, ygrid0, y, root0] using havg.2⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro omega N k hk z hz
      obtain ⟨a, hadist, hay, hroot, hbounds⟩ :=
        hcomparison k z (by simpa [K0] using hz)
      have hspos : 0 < s0 N k omega (ygrid0 k a) := by
        dsimp [s0, G0]
        exact mul_pos
          (div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N - k))
            (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N))
          (Real.exp_pos _)
      have hlow := (hbounds N omega).1
      have hu : 0 < Real.exp (-osc0 k omega (ygrid0 k a)) *
          s0 N k omega (ygrid0 k a) :=
        mul_pos (Real.exp_pos _) hspos
      have hbpos : 0 < b0 N k omega z := lt_of_lt_of_le hu hlow
      simpa [b0, s0, G0, osc0, oscSet0, ygrid0, root0, R0] using hbpos
    · intro omega k y hy
      have hR : 0 < (3 : ℝ)^(-(k : ℤ)) / 2 := by positivity
      let g : C(SpatialCoordinates d, ℝ) :=
        H omega + ∑ j ∈ Finset.range k, omega (-(j : ℤ))
      have h := aux_lane4_reference_mesh_statistic_oscillation
        k ((3 : ℝ)^(-(k : ℤ)) / 2) hR g y
      simpa [G0, g, oscSet0, osc0, R0] using h
    · intro k z hz
      obtain ⟨a, hadist, hay, hroot, hbounds⟩ :=
        hcomparison k z (by simpa [K0] using hz)
      refine ⟨a, ?_, ?_, ?_, ?_⟩
      · simpa [spacing0, ygrid0] using hadist
      · simpa [K0, ygrid0] using hay
      · simpa [root0, R0, ygrid0] using hroot
      · intro N hk omega
        simpa [osc0, oscSet0, s0, G0, b0, ygrid0, root0, R0] using
          (hbounds N omega)
    · exact hpoint'
    · exact hosc'
    · rcases hmesh' with ⟨V, hVmeas, hVnonneg, hVmem, hVnorm, hVaelub⟩
      refine ⟨V, hVmeas, hVnonneg, hVmem, hVnorm, ?_⟩
      filter_upwards [hVaelub] with omega hL
      intro N
      refine ⟨hL N, ?_⟩
      intro k hk z hz
      obtain ⟨a, hadist, hay, hroot, hbounds⟩ :=
        hcomparison k z (by simpa [K0] using hz)
      have hR : 0 < R0 k := by
        dsimp [R0]
        positivity
      have hspos : 0 < s0 N k omega (ygrid0 k a) := by
        dsimp [s0, G0]
        exact mul_pos
          (div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (N - k))
            (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N))
          (Real.exp_pos _)
      have hu : 0 < Real.exp (-osc0 k omega (ygrid0 k a)) *
          s0 N k omega (ygrid0 k a) :=
        mul_pos (Real.exp_pos _) hspos
      have hbpos : 0 < b0 N k omega z :=
        lt_of_lt_of_le hu (hbounds N omega).1
      have hinv : (b0 N k omega z)⁻¹ ≤
          Real.exp (osc0 k omega (ygrid0 k a)) *
            (s0 N k omega (ygrid0 k a))⁻¹ := by
        have hlowpos : 0 < Real.exp (-osc0 k omega (ygrid0 k a)) *
            s0 N k omega (ygrid0 k a) := hu
        have hi := (inv_le_inv₀ hbpos hlowpos).2 (hbounds N omega).1
        have hi' : (b0 N k omega z)⁻¹ ≤
            (s0 N k omega (ygrid0 k a))⁻¹ *
              Real.exp (osc0 k omega (ygrid0 k a)) := by
          simpa [mul_inv_rev, Real.exp_neg] using hi
        calc
          (b0 N k omega z)⁻¹ ≤
              (s0 N k omega (ygrid0 k a))⁻¹ *
                Real.exp (osc0 k omega (ygrid0 k a)) := hi'
          _ = Real.exp (osc0 k omega (ygrid0 k a)) *
                (s0 N k omega (ygrid0 k a))⁻¹ := by ring
      have hsum : b0 N k omega z + (b0 N k omega z)⁻¹ ≤
          Real.exp (osc0 k omega (ygrid0 k a)) *
            (s0 N k omega (ygrid0 k a) +
              (s0 N k omega (ygrid0 k a))⁻¹) := by
        calc
          b0 N k omega z + (b0 N k omega z)⁻¹ ≤
              Real.exp (osc0 k omega (ygrid0 k a)) *
                s0 N k omega (ygrid0 k a) +
              Real.exp (osc0 k omega (ygrid0 k a)) *
                (s0 N k omega (ygrid0 k a))⁻¹ :=
            add_le_add (hbounds N omega).2 hinv
          _ = _ := by ring
      have hdisc : R0 k ^ eta * Z0 N k omega a ≤ V N omega := by
        have hmem := (hL N).1
          ⟨k, hk, a, by rfl⟩
        exact hmem
      have hmul : R0 k ^ eta *
          (b0 N k omega z + (b0 N k omega z)⁻¹) ≤ V N omega := by
        have hnonneg : 0 ≤ R0 k ^ eta := Real.rpow_nonneg (by positivity) _
        have hstep := mul_le_mul_of_nonneg_left hsum hnonneg
        exact hstep.trans hdisc
      have hrpow : 0 < R0 k ^ eta := Real.rpow_pos_of_pos hR _
      have hdiv : b0 N k omega z + (b0 N k omega z)⁻¹ ≤
          V N omega / (R0 k ^ eta) := by
        apply (le_div_iff₀ hrpow).2
        simpa [mul_comm] using hmul
      have htarget : b0 N k omega z + (b0 N k omega z)⁻¹ ≤
          V N omega * (R0 k)^(-eta) := by
        simpa [div_eq_mul_inv, Real.rpow_neg (le_of_lt hR) eta] using hdiv
      change b0 N k omega z + (b0 N k omega z)⁻¹ ≤
        V N omega * (R0 k)^(-eta)
      exact htarget



theorem lane4_reference_mesh_statistic
    (d J : ℕ) (hd : 2 ≤ d) (hJ : 1 ≤ J)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (p q eta : ℝ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (heta : 0 < eta) :
    ∃ qref : ℝ, p ≤ qref ∧ q ≤ qref ∧ (d : ℝ) < qref * eta ∧
    ∃ delta0 Cmom Crate Cosc CV : ℝ,
      0 < delta0 ∧ 0 < Cmom ∧ 0 < Crate ∧ 0 < Cosc ∧ 0 < CV ∧
      delta0 ≤ 1 ∧
      Crate * ((2 * qref) + (2 * qref)^2) * delta0^2 <
        (eta - (d : ℝ) / qref) * Real.log 3 / 4 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : _root_.SubdiffusiveProcess.Paper.in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        let P := (chaosSampleLaw M).toMeasure
        let K : Set (SpatialCoordinates d) := {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}
        let R : ℕ → ℝ := fun k => (3 : ℝ)^(-(k : ℤ)) / 2
        let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega x => H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
        let s : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun N k omega x =>
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
              Real.exp (G k omega x - (k : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq M.P)
        let root : ℕ → SpatialCoordinates d → Set (SpatialCoordinates d) :=
          fun k z => Metric.ball z (R k)
        let b : ℕ → ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun N k omega z => (volume.real (root k z))⁻¹ * ∫ x in root k z, s N k omega x
        let oscSet : ℕ → BilateralField d → SpatialCoordinates d → Set ℝ :=
          fun k omega y => {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
            ∃ x' ∈ Metric.closedBall y (3 * R k), v = |G k omega x - G k omega x'|}
        let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
          fun k omega y => sSup (oscSet k omega y)
        let Grid : ℕ → Type := fun k => Fin d → Fin (3^(k + J) + 1)
        let ygrid : (k : ℕ) → Grid k → SpatialCoordinates d :=
          fun k a i => (a i : ℝ) * (3 : ℝ)^(-((k + J : ℕ) : ℤ))
        let spacing : ℕ → ℝ := fun k => (3 : ℝ)^(-((k + J : ℕ) : ℤ))
        let Z : (N k : ℕ) → BilateralField d → Grid k → ℝ :=
          fun N k omega a => Real.exp (osc k omega (ygrid k a)) *
            (s N k omega (ygrid k a) + (s N k omega (ygrid k a))⁻¹)
        (∀ (omega : BilateralField d) (N k : ℕ), k ≤ N →
          ∀ z ∈ K, 0 < b N k omega z) ∧
        (∀ (omega : BilateralField d) (k : ℕ) (y : SpatialCoordinates d), y ∈ K →
          (oscSet k omega y).Nonempty ∧ BddAbove (oscSet k omega y) ∧
            IsLUB (oscSet k omega y) (osc k omega y)) ∧
        (∀ (k : ℕ) (z : SpatialCoordinates d), z ∈ K →
          ∃ a : Grid k, dist z (ygrid k a) ≤ spacing k ∧ ygrid k a ∈ K ∧
            root k z ⊆ Metric.closedBall (ygrid k a) (3 * R k) ∧
            ∀ (N : ℕ), k ≤ N → ∀ omega : BilateralField d,
              Real.exp (-osc k omega (ygrid k a)) * s N k omega (ygrid k a) ≤
                b N k omega z ∧
              b N k omega z ≤
                Real.exp (osc k omega (ygrid k a)) * s N k omega (ygrid k a)) ∧
        (∀ aexp : ℝ, aexp ∈ Set.Icc 1 (2 * q) →
          ∀ (N k : ℕ), k ≤ N → ∀ y ∈ K,
            Integrable (fun omega => (s N k omega y)^aexp +
              (s N k omega y)^(-aexp)) P ∧
            (∫ omega, (s N k omega y)^aexp + (s N k omega y)^(-aexp) ∂P) ≤
              Cmom * Real.exp (Crate * (aexp + aexp^2) * M.delta^2 * (k : ℝ)) ∧
            MemLp (fun omega => s N k omega y) (ENNReal.ofReal aexp) P ∧
            MemLp (fun omega => (s N k omega y)⁻¹) (ENNReal.ofReal aexp) P) ∧
        (∀ (k : ℕ) (y : SpatialCoordinates d), y ∈ K →
          MemLp (fun omega => Real.exp (osc k omega y)) (ENNReal.ofReal (2 * qref)) P ∧
          eLpNorm (fun omega => Real.exp (osc k omega y)) (ENNReal.ofReal (2 * qref)) P ≤
            ENNReal.ofReal Cosc) ∧
        (∃ V : ℕ → BilateralField d → ℝ,
          (∀ N, Measurable (V N)) ∧
          (∀ N omega, 0 ≤ V N omega) ∧
          (∀ N, MemLp (V N) (ENNReal.ofReal p) P) ∧
          (∀ N, eLpNorm (V N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal CV) ∧
          ∀ᵐ omega ∂P, ∀ N : ℕ,
            IsLUB {v : ℝ | ∃ k : ℕ, k ≤ N ∧ ∃ a : Grid k,
              v = (R k)^eta * Z N k omega a} (V N omega) ∧
            ∀ k : ℕ, k ≤ N → ∀ z ∈ K,
              b N k omega z + (b N k omega z)⁻¹ ≤ V N omega * (R k)^(-eta)) := by
  obtain ⟨qref, h1, h2, h3, delta0, Cmom, Crate, Cosc, CV, h4, h5, h6, h7, h8, h9, h10, hall⟩ :=
    aux_lane4_reference_mesh_statistic_adm d J hd hJ p q eta hp hq heta
  exact ⟨qref, h1, h2, h3, delta0, Cmom, Crate, Cosc, CV, h4, h5, h6, h7, h8, h9, h10,
    fun M Rm H hH hδ => hall M Rm H (InfraredAdmissible.of_char hH) hδ⟩

end SubdiffusiveProcess.Paper
