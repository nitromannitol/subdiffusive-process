module

public import SubdiffusiveProcess.Paper.whole_space_resolvent_localization
public import SubdiffusiveProcess.Paper.in_cutoff_start_continuity
public import SubdiffusiveProcess.Paper.in_crossing
public import MarkovProcess.Path.ExitTime
public import Mathlib.Order.LiminfLimsup

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory ProbabilityTheory MarkovProcess SubdiffusiveProcess Topology
open scoped ENNReal NNReal

namespace Paper

theorem aux_tight_whole_space_resolvent_limit_bound
    {d : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : Nat → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (RN : Nat → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN : ∀ N omega lam f x, RN N omega lam f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
    (lam : ℝ) (hlam : 0 < lam) :
    ∀ N omega f x, |RN N omega lam f x| ≤ ‖f‖ / lam := by
  intro N omega f x
  rw [hRN N omega lam f x]
  let μ : Measure (DiffusionPath d) := KN N (omega, x)
  letI : IsProbabilityMeasure μ := (hKN N).isProbabilityMeasure (omega, x)
  have hpoint : ∀ path : DiffusionPath d, |∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-lam * t) * f (path (Real.toNNReal t))| ≤ ‖f‖ * lam⁻¹ := by
    intro path
    have h_bound : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ‖Real.exp (-lam * t) * f (path (Real.toNNReal t))‖ ≤
          ‖f‖ * Real.exp (-lam * t) := by
      filter_upwards with t
      calc
        ‖Real.exp (-lam * t) * f (path (Real.toNNReal t))‖
            = ‖Real.exp (-lam * t)‖ * ‖f (path (Real.toNNReal t))‖ := by
                rw [norm_mul]
        _ = Real.exp (-lam * t) * ‖f (path (Real.toNNReal t))‖ := by
              rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (-lam * t) * ‖f‖ :=
              mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (Real.exp_pos _).le
        _ = ‖f‖ * Real.exp (-lam * t) := by ring
    have h_exp_int : Integrable (fun t : ℝ => Real.exp (-lam * t))
        (volume.restrict (Set.Ioi (0 : ℝ))) := exp_neg_integrableOn_Ioi 0 hlam
    have h_major_int : Integrable (fun t : ℝ => ‖f‖ * Real.exp (-lam * t))
        (volume.restrict (Set.Ioi (0 : ℝ))) := h_exp_int.const_mul ‖f‖
    have h_int := norm_integral_le_of_norm_le h_major_int h_bound
    have h_rhs : ∫ t in Set.Ioi (0 : ℝ), ‖f‖ * Real.exp (-lam * t) = ‖f‖ * lam⁻¹ := by
      rw [integral_const_mul,
        MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero hlam]
    calc
      |∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) * f (path (Real.toNNReal t))|
          = ‖∫ t in Set.Ioi (0 : ℝ),
              Real.exp (-lam * t) * f (path (Real.toNNReal t))‖ := by
                rw [Real.norm_eq_abs]
      _ ≤ ∫ t in Set.Ioi (0 : ℝ), ‖f‖ * Real.exp (-lam * t) := h_int
      _ = ‖f‖ * lam⁻¹ := h_rhs
  have h_bound : ∀ᵐ path ∂μ, ‖(∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-lam * t) * f (path (Real.toNNReal t)))‖ ≤ ‖f‖ * lam⁻¹ := by
    filter_upwards with path
    rw [Real.norm_eq_abs]
    exact hpoint path
  have h_int := norm_integral_le_of_norm_le
    (integrable_const (‖f‖ * lam⁻¹)) h_bound
  have h_outer : |∫ path, (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂μ| ≤ ‖f‖ * lam⁻¹ := by
    calc
      |∫ path, (∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂μ|
          = ‖∫ path, (∫ t in Set.Ioi (0 : ℝ),
              Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂μ‖ := by
                rw [Real.norm_eq_abs]
      _ ≤ ∫ path, ‖f‖ * lam⁻¹ ∂μ := h_int
      _ = ‖f‖ * lam⁻¹ := by simp [integral_const]
  simpa only [μ, div_eq_mul_inv] using h_outer

theorem aux_tight_whole_space_resolvent_limit_localization_bridge
    {d : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : Nat → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : Nat → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (Qc : Nat → SpatialCoordinates d) (Qr : Nat → ℝ) (hQr : ∀ m, 0 < Qr m)
    (RN : Nat → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (RNQ : Nat → Nat → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (exitP : Nat → Nat → BilateralField d → SpatialCoordinates d → ℝ → ℝ)
    (hRN : ∀ N omega lam f x, RN N omega lam f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
    (hRNQ : ∀ m N omega lam f x, RNQ m N omega lam f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator
          {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
            (centeredCube (Qc m) (Qr m) (hQr m) : Set _) path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
        ∂(KN N (omega, x)))
    (hexitP : ∀ m N omega x T, exitP m N omega x T =
      ((KN N (omega, x)) {path | ContinuousPath.exitTime
        (centeredCube (Qc m) (Qr m) (hQr m) : Set _) path ≤ ENNReal.ofReal T}).toReal)
    (N m : Nat) (omega : BilateralField d) (x : SpatialCoordinates d)
    (lam T : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (hlam : 0 < lam) (hT : 0 ≤ T)
    (hx : x ∈ (centeredCube (Qc m) (Qr m) (hQr m) : Set _)) :
    |RN N omega lam f x - RNQ m N omega lam f x| ≤
      (‖f‖ / lam) * (exitP m N omega x T + Real.exp (-lam * T)) := by
  have h := whole_space_resolvent_localization M H PN KN hKN hin N omega
    (Qc m) (Qr m) (hQr m) x hx lam hlam T hT f
    (RN N omega lam f x) (RNQ m N omega lam f x)
    (hRN N omega lam f x) (hRNQ m N omega lam f x)
  rw [hexitP m N omega x T]
  exact h

theorem aux_tight_whole_space_resolvent_limit_cauchy_event_union
    {Ω I : Type*}
    (F₁ F₂ G₁ G₂ : Ω → I → ℝ)
    {a b c eps : ℝ} (hsum : a + b + c ≤ eps) :
    ∀ omega i,
      eps ≤ |F₁ omega i - F₂ omega i| →
        (∃ i, a ≤ |F₁ omega i - G₁ omega i|) ∨
        (∃ i, b ≤ |G₁ omega i - G₂ omega i|) ∨
        (∃ i, c ≤ |G₂ omega i - F₂ omega i|) := by
  intro omega i hlarge
  by_cases h₁ : ∃ i, a ≤ |F₁ omega i - G₁ omega i|
  · exact Or.inl h₁
  by_cases h₂ : ∃ i, b ≤ |G₁ omega i - G₂ omega i|
  · exact Or.inr (Or.inl h₂)
  by_cases h₃ : ∃ i, c ≤ |G₂ omega i - F₂ omega i|
  · exact Or.inr (Or.inr h₃)
  exfalso
  have hA : |F₁ omega i - G₁ omega i| < a := by
    exact lt_of_not_ge (fun h => h₁ ⟨i, h⟩)
  have hB : |G₁ omega i - G₂ omega i| < b := by
    exact lt_of_not_ge (fun h => h₂ ⟨i, h⟩)
  have hC : |G₂ omega i - F₂ omega i| < c := by
    exact lt_of_not_ge (fun h => h₃ ⟨i, h⟩)
  have htri : |F₁ omega i - F₂ omega i| ≤
      |F₁ omega i - G₁ omega i| + |G₁ omega i - G₂ omega i| +
        |G₂ omega i - F₂ omega i| := by
    calc
      |F₁ omega i - F₂ omega i| =
          |(F₁ omega i - G₁ omega i) + (G₁ omega i - G₂ omega i) +
            (G₂ omega i - F₂ omega i)| := by ring_nf
      _ ≤ |(F₁ omega i - G₁ omega i) + (G₁ omega i - G₂ omega i)| +
          |G₂ omega i - F₂ omega i| := abs_add_le _ _
      _ ≤ |F₁ omega i - G₁ omega i| + |G₁ omega i - G₂ omega i| +
          |G₂ omega i - F₂ omega i| := by
        gcongr
        exact abs_add_le _ _
  linarith

/-- A quantitative tail choice, including the zero-function case `K = 0`. -/
theorem aux_tight_whole_space_resolvent_limit_choose_tail
    (K lam eps : ℝ) (hK : 0 ≤ K) (hlam : 0 < lam) (heps : 0 < eps) :
    ∃ T eta : ℝ, 0 ≤ T ∧ 0 < eta ∧
      K * (eta + Real.exp (-lam * T)) < eps / 4 := by
  let eta : ℝ := eps / (16 * (K + 1))
  have hK1 : 0 < K + 1 := by linarith
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hlim : Filter.Tendsto (fun T : ℝ => Real.exp (-lam * T))
      Filter.atTop (nhds (0 : ℝ)) := by
    have hneg : -lam < 0 := by linarith
    simpa only [Function.comp_apply, id_eq] using! Real.tendsto_exp_atBot.comp
      (Filter.tendsto_id.const_mul_atTop_of_neg hneg)
  have hev : ∀ᶠ T : ℝ in Filter.atTop, Real.exp (-lam * T) < eta :=
    hlim.eventually (eventually_lt_nhds heta)
  obtain ⟨T, hT, htail⟩ := ((Filter.eventually_ge_atTop (0 : ℝ)).and hev).exists
  refine ⟨T, eta, hT, heta, ?_⟩
  have hsmallK : K * (eta + eta) < eps / 4 := by
    dsimp [eta]
    apply (lt_of_le_of_lt (show K * (eps / (16 * (K + 1)) +
      eps / (16 * (K + 1))) ≤ eps / 8 by
        have hfrac : K / (K + 1) ≤ 1 := (div_le_one hK1).mpr (by linarith)
        have hpos : 0 ≤ eps / 8 := by positivity
        calc
          _ = (eps / 8) * (K / (K + 1)) := by
            field_simp
            ring
          _ ≤ (eps / 8) * 1 := mul_le_mul_of_nonneg_left hfrac hpos
          _ = _ := by ring))
    linarith
  have hmul : K * (eta + Real.exp (-lam * T)) ≤ K * (eta + eta) :=
    mul_le_mul_of_nonneg_left (by linarith) hK
  exact lt_of_le_of_lt hmul hsmallK

/-- A fixed-time Cauchy estimate with the quantifier structure of `hcontain` and
`hkilled`. The abstract `Q` is instantiated by the centered cube. -/
theorem aux_tight_whole_space_resolvent_limit_cauchy_probability
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    (μ : Measure Ω) (Q : Nat → Set X)
    (RN : Nat → Ω → X → ℝ)
    (RNQ : Nat → Nat → Ω → X → ℝ)
    (RQ : Nat → Ω → X → ℝ)
    (exitP : Nat → Nat → Ω → X → ℝ)
    (K tail : ℝ) (hK : 0 ≤ K)
    (hloc : ∀ m N omega x, x ∈ Q m →
      |RN N omega x - RNQ m N omega x| ≤ K * (exitP m N omega x + tail))
    (hkilled : ∀ m, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : Nat, ∀ N, N0 ≤ N →
        μ {omega | ∃ x ∈ closure (Q m), eps ≤ |RNQ m N omega x - RQ m omega x|} ≤
          ENNReal.ofReal rho)
    (hcontain : ∀ B : Set X, IsCompact B → ∀ T : ℝ, 0 ≤ T →
      ∀ eta : ℝ, 0 < eta → ∀ rho : ℝ, 0 < rho →
      ∃ m : Nat, B ⊆ Q m ∧ ∀ N : Nat,
        μ {omega | ∃ x ∈ B, eta ≤ exitP m N omega x} ≤ ENNReal.ofReal rho)
    (B : Set X) (hB : IsCompact B) (T eta eps rho : ℝ)
    (hT : 0 ≤ T) (heta : 0 < eta) (heps : 0 < eps) (hrho : 0 < rho)
    (hsmall : K * (eta + tail) < eps / 4) :
    ∃ N0 : Nat, ∀ N P, N0 ≤ N → N0 ≤ P →
      μ {omega | ∃ x ∈ B, eps ≤ |RN N omega x - RN P omega x|} ≤
        ENNReal.ofReal rho := by
  obtain ⟨m, hBQ, hcontain_m⟩ := hcontain B hB T hT eta heta (rho / 4) (by positivity)
  obtain ⟨Nk, hk⟩ := hkilled m (eps / 4) (by positivity) (rho / 4) (by positivity)
  refine ⟨Nk, ?_⟩
  intro N P hN hP
  let A : Set Ω := {omega | ∃ x ∈ B, eps / 4 ≤ |RN N omega x - RNQ m N omega x|}
  let D : Set Ω := {omega | ∃ x ∈ B, eps / 4 ≤ |RNQ m P omega x - RN P omega x|}
  let E : Set Ω := {omega | ∃ x ∈ B, eps / 4 ≤ |RNQ m N omega x - RQ m omega x|}
  let F : Set Ω := {omega | ∃ x ∈ B, eps / 4 ≤ |RNQ m P omega x - RQ m omega x|}
  have hAloc : A ⊆ {omega | ∃ x ∈ B, eta ≤ exitP m N omega x} := by
    intro omega ⟨x, hx, hlarge⟩
    by_contra hn
    have hexit : exitP m N omega x < eta :=
      lt_of_not_ge (fun h => hn ⟨x, hx, h⟩)
    have hbound := hloc m N omega x (hBQ hx)
    have hmul : K * (exitP m N omega x + tail) ≤ K * (eta + tail) :=
      mul_le_mul_of_nonneg_left (by linarith) hK
    linarith
  have hDloc : D ⊆ {omega | ∃ x ∈ B, eta ≤ exitP m P omega x} := by
    intro omega ⟨x, hx, hlarge⟩
    by_contra hn
    have hexit : exitP m P omega x < eta :=
      lt_of_not_ge (fun h => hn ⟨x, hx, h⟩)
    have hbound := hloc m P omega x (hBQ hx)
    have hmul : K * (exitP m P omega x + tail) ≤ K * (eta + tail) :=
      mul_le_mul_of_nonneg_left (by linarith) hK
    rw [abs_sub_comm] at hlarge
    linarith
  have hA : μ A ≤ ENNReal.ofReal (rho / 4) :=
    (measure_mono hAloc).trans (hcontain_m N)
  have hD : μ D ≤ ENNReal.ofReal (rho / 4) :=
    (measure_mono hDloc).trans (hcontain_m P)
  have hE : μ E ≤ ENNReal.ofReal (rho / 4) := by
    have hsub : E ⊆ {omega | ∃ x ∈ closure (Q m),
        eps / 4 ≤ |RNQ m N omega x - RQ m omega x|} := by
      intro omega ⟨x, hx, he⟩
      exact ⟨x, subset_closure (hBQ hx), he⟩
    exact (measure_mono hsub).trans (hk N hN)
  have hF : μ F ≤ ENNReal.ofReal (rho / 4) := by
    have hsub : F ⊆ {omega | ∃ x ∈ closure (Q m),
        eps / 4 ≤ |RNQ m P omega x - RQ m omega x|} := by
      intro omega ⟨x, hx, he⟩
      exact ⟨x, subset_closure (hBQ hx), he⟩
    exact (measure_mono hsub).trans (hk P hP)
  have hunion : {omega | ∃ x ∈ B, eps ≤ |RN N omega x - RN P omega x|} ⊆
      A ∪ (E ∪ (F ∪ D)) := by
    intro omega ⟨x, hx, hlarge⟩
    have htri := aux_tight_whole_space_resolvent_limit_cauchy_event_union
      (fun omega (x : B) => RN N omega x)
      (fun omega (x : B) => RN P omega x)
      (fun omega (x : B) => RNQ m N omega x)
      (fun omega (x : B) => RNQ m P omega x)
      (a := eps / 4) (b := eps / 4 + eps / 4) (c := eps / 4) (eps := eps)
      (by linarith) omega ⟨x, hx⟩ hlarge
    rcases htri with hleft | hmiddle | hright
    · obtain ⟨y, hy⟩ := hleft
      exact Or.inl ⟨y, y.property, hy⟩
    · obtain ⟨y, hy⟩ := hmiddle
      by_cases hfirst : eps / 4 ≤ |RNQ m N omega y - RQ m omega y|
      · exact Or.inr (Or.inl ⟨y, y.property, hfirst⟩)
      · have hlt : |RNQ m N omega y - RQ m omega y| < eps / 4 :=
          lt_of_not_ge hfirst
        have hbound : |RNQ m N omega y - RNQ m P omega y| ≤
            |RNQ m N omega y - RQ m omega y| +
              |RNQ m P omega y - RQ m omega y| := by
          calc
            _ = |(RNQ m N omega y - RQ m omega y) +
                (RQ m omega y - RNQ m P omega y)| := by ring_nf
            _ ≤ _ := by simpa only [abs_sub_comm] using
              (abs_add_le (RNQ m N omega y - RQ m omega y)
                (RQ m omega y - RNQ m P omega y))
        have hsecond : eps / 4 ≤ |RNQ m P omega y - RQ m omega y| := by
          linarith
        exact Or.inr (Or.inr (Or.inl ⟨y, y.property, hsecond⟩))
    · obtain ⟨y, hy⟩ := hright
      exact Or.inr (Or.inr (Or.inr ⟨y, y.property, hy⟩))
  calc
    μ {omega | ∃ x ∈ B, eps ≤ |RN N omega x - RN P omega x|}
        ≤ μ (A ∪ (E ∪ (F ∪ D))) := measure_mono hunion
    _ ≤ μ A + (μ E + (μ F + μ D)) := by
      calc
        _ ≤ μ A + μ (E ∪ (F ∪ D)) := measure_union_le _ _
        _ ≤ μ A + (μ E + μ (F ∪ D)) := by gcongr; exact measure_union_le _ _
        _ ≤ _ := by gcongr; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (rho / 4) + ENNReal.ofReal (rho / 4) +
          ENNReal.ofReal (rho / 4) + ENNReal.ofReal (rho / 4) := by
      calc
        _ ≤ ENNReal.ofReal (rho / 4) +
            (ENNReal.ofReal (rho / 4) +
              (ENNReal.ofReal (rho / 4) + ENNReal.ofReal (rho / 4))) :=
          add_le_add hA (add_le_add hE (add_le_add hF hD))
        _ = _ := by ac_rfl
    _ = ENNReal.ofReal rho := by
      have hq : 0 ≤ rho / 4 := by positivity
      have hhalf : 0 ≤ rho / 4 + rho / 4 := by positivity
      calc
        _ = ENNReal.ofReal (rho / 4 + rho / 4) +
            ENNReal.ofReal (rho / 4 + rho / 4) := by
          rw [ENNReal.ofReal_add hq hq]
          ac_rfl
        _ = ENNReal.ofReal ((rho / 4 + rho / 4) + (rho / 4 + rho / 4)) :=
          (ENNReal.ofReal_add hhalf hhalf).symm
        _ = ENNReal.ofReal rho := by congr 1; ring

/-- The full locally uniform Cauchy-in-probability estimate at the abstract
interface of the frozen localization and killed-resolvent hypotheses. -/
theorem aux_tight_whole_space_resolvent_limit_cauchy_in_measure
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    (μ : Measure Ω) (Q : Nat → Set X)
    (RN : Nat → Ω → X → ℝ)
    (RNQ : Nat → Nat → Ω → X → ℝ)
    (RQ : Nat → Ω → X → ℝ)
    (exitP : Nat → Nat → Ω → X → ℝ → ℝ)
    (K lam : ℝ) (hK : 0 ≤ K) (hlam : 0 < lam)
    (hloc : ∀ m N omega x T, 0 ≤ T → x ∈ Q m →
      |RN N omega x - RNQ m N omega x| ≤
        K * (exitP m N omega x T + Real.exp (-lam * T)))
    (hkilled : ∀ m, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : Nat, ∀ N, N0 ≤ N →
        μ {omega | ∃ x ∈ closure (Q m), eps ≤ |RNQ m N omega x - RQ m omega x|} ≤
          ENNReal.ofReal rho)
    (hcontain : ∀ B : Set X, IsCompact B → ∀ T : ℝ, 0 ≤ T →
      ∀ eta : ℝ, 0 < eta → ∀ rho : ℝ, 0 < rho →
      ∃ m : Nat, B ⊆ Q m ∧ ∀ N : Nat,
        μ {omega | ∃ x ∈ B, eta ≤ exitP m N omega x T} ≤ ENNReal.ofReal rho) :
    ∀ B : Set X, IsCompact B → ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : Nat, ∀ N P, N0 ≤ N → N0 ≤ P →
        μ {omega | ∃ x ∈ B, eps ≤ |RN N omega x - RN P omega x|} ≤
          ENNReal.ofReal rho := by
  intro B hB eps heps rho hrho
  obtain ⟨T, eta, hT, heta, hsmall⟩ :=
    aux_tight_whole_space_resolvent_limit_choose_tail K lam eps hK hlam heps
  exact aux_tight_whole_space_resolvent_limit_cauchy_probability
    μ Q RN RNQ RQ (fun m N omega x => exitP m N omega x T)
    K (Real.exp (-lam * T)) hK
    (fun m N omega x hx => hloc m N omega x T hT hx)
    hkilled (fun B hB _ _ eta heta rho hrho =>
      hcontain B hB T hT eta heta rho hrho)
    B hB T eta eps rho hT heta heps hrho hsmall

/-- Concrete compact-local Cauchy-in-probability for the pinned full and killed
occupation resolvents. -/
theorem aux_tight_whole_space_resolvent_limit_concrete_cauchy_in_measure
    {d : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (PN : Nat → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : Nat → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (Qc : Nat → SpatialCoordinates d) (Qr : Nat → ℝ) (hQr : ∀ m, 0 < Qr m)
    (RN : Nat → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (RNQ : Nat → Nat → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (RQ : Nat → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (exitP : Nat → Nat → BilateralField d → SpatialCoordinates d → ℝ → ℝ)
    (hRN : ∀ N omega lam f x, RN N omega lam f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
    (hRNQ : ∀ m N omega lam f x, RNQ m N omega lam f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator
          {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
            (centeredCube (Qc m) (Qr m) (hQr m) : Set _) path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
        ∂(KN N (omega, x)))
    (hexitP : ∀ m N omega x T, exitP m N omega x T =
      ((KN N (omega, x)) {path | ContinuousPath.exitTime
        (centeredCube (Qc m) (Qr m) (hQr m) : Set _) path ≤ ENNReal.ofReal T}).toReal)
    (hkilled : ∀ m lam, 0 < lam → ∀ f, ∀ eps : ℝ, 0 < eps →
      ∀ rho : ℝ, 0 < rho → ∃ N0 : Nat, ∀ N, N0 ≤ N →
        (chaosSampleLaw M).toMeasure
          {omega | ∃ x ∈ closure (centeredCube (Qc m) (Qr m) (hQr m) : Set _),
            eps ≤ |RNQ m N omega lam f x - RQ m omega lam f x|} ≤ ENNReal.ofReal rho)
    (hcontain : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ T : ℝ, 0 ≤ T → ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ m : Nat, B ⊆ (centeredCube (Qc m) (Qr m) (hQr m) : Set _) ∧
          ∀ N : Nat, (chaosSampleLaw M).toMeasure
            {omega | ∃ x ∈ B, eps ≤ exitP m N omega x T} ≤ ENNReal.ofReal rho)
    (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0 : Nat, ∀ N P, N0 ≤ N → N0 ≤ P →
          (chaosSampleLaw M).toMeasure
            {omega | ∃ x ∈ B, eps ≤ |RN N omega lam f x - RN P omega lam f x|} ≤
              ENNReal.ofReal rho := by
  let Q : Nat → Set (SpatialCoordinates d) :=
    fun m => centeredCube (Qc m) (Qr m) (hQr m)
  have hK : 0 ≤ ‖f‖ / lam := div_nonneg (norm_nonneg _) hlam.le
  exact aux_tight_whole_space_resolvent_limit_cauchy_in_measure
    (chaosSampleLaw M).toMeasure Q
    (fun N omega x => RN N omega lam f x)
    (fun m N omega x => RNQ m N omega lam f x)
    (fun m omega x => RQ m omega lam f x)
    exitP (‖f‖ / lam) lam hK hlam
    (by
      intro m N omega x T hT hx
      exact aux_tight_whole_space_resolvent_limit_localization_bridge
        M H PN KN hKN hin Qc Qr hQr RN RNQ exitP
        hRN hRNQ hexitP N m omega x lam T f hlam hT hx)
    (by
      intro m eps heps rho hrho
      exact hkilled m lam hlam f eps heps rho hrho)
    (by
      intro B hB T hT eta heta rho hrho
      exact hcontain B hB T hT eta heta rho hrho)



theorem aux_tight_whole_space_resolvent_limit_mapsTo_iff
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    (K : Set X) (hK : IsCompact K) (D : Set X) (hDK : D ⊆ K) (hKD : K ⊆ closure D)
    (U : Set Y) (hU : IsOpen U) (hUc : (Uᶜ).Nonempty) (g : C(X, Y)) :
    Set.MapsTo g K U ↔ ∃ n : ℕ, ∀ x ∈ D, (1 : ℝ) / (n + 1) ≤ Metric.infDist (g x) Uᶜ := by
  have hclosed : IsClosed Uᶜ := hU.isClosed_compl
  have hcont : Continuous fun x => Metric.infDist (g x) Uᶜ :=
    (Metric.continuous_infDist_pt _).comp g.continuous
  constructor
  · intro hmaps
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · refine ⟨0, fun x hx => ?_⟩
      exact absurd (hDK hx) (by simp [hKe])
    obtain ⟨x0, hx0K, hmin⟩ := hK.exists_isMinOn hKne hcont.continuousOn
    have hpos : 0 < Metric.infDist (g x0) Uᶜ :=
      (hclosed.notMem_iff_infDist_pos hUc).mp (fun h => h (hmaps hx0K))
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    refine ⟨n, fun x hx => ?_⟩
    exact hn.le.trans (hmin (hDK hx))
  · rintro ⟨n, hn⟩ x hxK
    have hset : IsClosed {x | (1 : ℝ) / (n + 1) ≤ Metric.infDist (g x) Uᶜ} :=
      isClosed_le continuous_const hcont
    have hsub : closure D ⊆ {x | (1 : ℝ) / (n + 1) ≤ Metric.infDist (g x) Uᶜ} :=
      closure_minimal (fun y hy => hn y hy) hset
    have hx : (1 : ℝ) / (n + 1) ≤ Metric.infDist (g x) Uᶜ := hsub (hKD hxK)
    have hpos : 0 < Metric.infDist (g x) Uᶜ :=
      lt_of_lt_of_le (by positivity) hx
    have := (hclosed.notMem_iff_infDist_pos hUc).mpr hpos
    simpa using this

/-- A map into `C(X, ℝ)` (Borel for the compact-open topology) is measurable as soon as all
its evaluations are measurable. -/
theorem aux_tight_whole_space_resolvent_limit_measurable_of_eval
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    [SecondCountableTopology C(X, ℝ)]
    [MeasurableSpace C(X, ℝ)] [BorelSpace C(X, ℝ)]
    (F : Ω → C(X, ℝ)) (hF : ∀ x, Measurable fun ω => F ω x) : Measurable F := by
  let S : Set (Set C(X, ℝ)) :=
    Set.image2 (fun K U => {f : C(X, ℝ) | Set.MapsTo f K U}) {K | IsCompact K} {t | IsOpen t}
  have hborel : (inferInstance : MeasurableSpace C(X, ℝ)) =
      MeasurableSpace.generateFrom S := by
    rw [BorelSpace.measurable_eq (α := C(X, ℝ))]
    exact borel_eq_generateFrom_of_subbasis ContinuousMap.compactOpen_eq
  have key : ∀ t ∈ S, MeasurableSet (F ⁻¹' t) := by
    rintro t ⟨K, hK, U, hU, rfl⟩
    change IsCompact K at hK
    change IsOpen U at hU
    rcases (Uᶜ).eq_empty_or_nonempty with hUe | hUc
    · have hUu : U = Set.univ := Set.compl_empty_iff.mp hUe
      subst hUu
      have : F ⁻¹' {f : C(X, ℝ) | Set.MapsTo f K Set.univ} = Set.univ := by
        ext ω; simp [Set.mapsTo_univ]
      rw [this]; exact MeasurableSet.univ
    obtain ⟨D, hDK, hDc, hKD⟩ := hK.isSeparable.exists_countable_dense_subset
    have heq : F ⁻¹' {f : C(X, ℝ) | Set.MapsTo f K U} =
        ⋃ n : ℕ, ⋂ x ∈ D, {ω | (1 : ℝ) / (n + 1) ≤ Metric.infDist (F ω x) Uᶜ} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
      exact aux_tight_whole_space_resolvent_limit_mapsTo_iff K hK D hDK hKD U hU hUc (F ω)
    rw [heq]
    refine MeasurableSet.iUnion fun n => MeasurableSet.biInter hDc fun x _ => ?_
    exact measurableSet_le measurable_const
      ((Metric.continuous_infDist_pt _).measurable.comp (hF x))
  have h := @measurable_generateFrom Ω C(X, ℝ) _ S F key
  rw [← hborel] at h
  exact h


/-- Pointwise geometric Cauchy control at one point gives the limit and a tail bound. -/
theorem aux_tight_whole_space_resolvent_limit_geometric_point
    {X : Type*} (U : Nat → Set X) (hUmono : Monotone U)
    (a : Nat → X → ℝ) (k : Nat)
    (hgood : ∀ i, k ≤ i → ∀ x ∈ U i, |a i x - a (i + 1) x| ≤ (1 / 2 : ℝ) ^ i)
    (x : X) (k1 : Nat) (hx : x ∈ U k1) :
    Tendsto (fun i => a i x) atTop (𝓝 (limUnder atTop (fun i => a i x))) ∧
      ∀ j, k ≤ j → x ∈ U j →
        |a j x - limUnder atTop (fun i => a i x)| ≤ 2 * (1 / 2 : ℝ) ^ j := by
  have hshift : ∀ j, k ≤ j → x ∈ U j → ∀ i,
      dist (a (i + j) x) (a (i + 1 + j) x) ≤ (1 / 2 : ℝ) ^ j * (1 / 2 : ℝ) ^ i := by
    intro j hj hxj i
    have hij : i + 1 + j = (i + j) + 1 := by omega
    rw [hij, Real.dist_eq, ← pow_add, add_comm j i]
    exact hgood (i + j) (by omega) x (hUmono (by omega) hxj)
  have hj0 : x ∈ U (max k k1) := hUmono (le_max_right _ _) hx
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric (1 / 2 : ℝ) ((1 / 2 : ℝ) ^ max k k1)
      (f := fun i => a (i + max k k1) x) (by norm_num)
      (hshift (max k k1) (le_max_left _ _) hj0))
  have htend : Tendsto (fun i => a i x) atTop (𝓝 L) :=
    (tendsto_add_atTop_iff_nat (max k k1)).mp hL
  have hlim : limUnder atTop (fun i => a i x) = L := htend.limUnder_eq
  rw [hlim]
  refine ⟨htend, fun j hj hxj => ?_⟩
  have htj : Tendsto (fun i => a (i + j) x) atTop (𝓝 L) :=
    (tendsto_add_atTop_iff_nat j).mpr htend
  have h := dist_le_of_le_geometric_of_tendsto (1 / 2 : ℝ) ((1 / 2 : ℝ) ^ j)
    (f := fun i => a (i + j) x) (by norm_num)
    (hshift j hj hxj) htj 0
  rw [Real.dist_eq] at h
  simp only [zero_add, pow_zero, mul_one] at h
  calc |a j x - L| ≤ (1 / 2 : ℝ) ^ j / (1 - 1 / 2) := h
    _ = 2 * (1 / 2 : ℝ) ^ j := by ring

/-- Geometric Cauchy control on an increasing open cover gives a locally uniform limit. -/
theorem aux_tight_whole_space_resolvent_limit_geometric_limit
    {X : Type*} [TopologicalSpace X] (U : Nat → Set X) (hUopen : ∀ k, IsOpen (U k))
    (hUmono : Monotone U) (hUcover : ∀ x, ∃ k, x ∈ U k)
    (a : Nat → X → ℝ) (k : Nat)
    (hgood : ∀ i, k ≤ i → ∀ x ∈ U i, |a i x - a (i + 1) x| ≤ (1 / 2 : ℝ) ^ i) :
    (∀ x, Tendsto (fun i => a i x) atTop (𝓝 (limUnder atTop (fun i => a i x)))) ∧
      (∀ j, k ≤ j → ∀ x ∈ U j,
        |a j x - limUnder atTop (fun i => a i x)| ≤ 2 * (1 / 2 : ℝ) ^ j) ∧
      ((∀ i, Continuous (a i)) → Continuous (fun x => limUnder atTop (fun i => a i x))) := by
  have hpt := fun x => (hUcover x).elim fun k1 hk1 =>
    aux_tight_whole_space_resolvent_limit_geometric_point U hUmono a k hgood x k1 hk1
  refine ⟨fun x => (hpt x).1, fun j hj x hx => (hpt x).2 j hj hx, fun hcont => ?_⟩
  have hloc : TendstoLocallyUniformly a (fun x => limUnder atTop (fun i => a i x)) atTop := by
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε x
    obtain ⟨k1, hk1⟩ := hUcover x
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨U k1, (hUopen k1).mem_nhds hk1, ?_⟩
    filter_upwards [eventually_ge_atTop (max (max k k1) M)] with n hn y hy
    have hkn : k ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hyn : y ∈ U n :=
      hUmono (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn) hy
    have hb := (hpt y).2 n hkn hyn
    have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ M :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_trans (le_max_right _ _) hn)
    rw [dist_comm, Real.dist_eq]
    linarith
  exact hloc.continuous (Frequently.of_forall hcont)


/-- Countable subadditivity along a geometric tail. -/
theorem aux_tight_whole_space_resolvent_limit_tail_measure
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Bad : Nat → Set Ω)
    (hBad : ∀ i, μ (Bad i) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ i)) (k : Nat) :
    μ (⋃ i, Bad (i + k)) ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) := by
  have hsum : Summable (fun i : Nat => (1 / 2 : ℝ) ^ (i + k)) := by
    simp_rw [pow_add]
    exact summable_geometric_two.mul_right _
  calc μ (⋃ i, Bad (i + k)) ≤ ∑' i, μ (Bad (i + k)) := measure_iUnion_le _
    _ ≤ ∑' i, ENNReal.ofReal ((1 / 2 : ℝ) ^ (i + k)) := ENNReal.tsum_le_tsum fun i => hBad _
    _ = ENNReal.ofReal (∑' i, (1 / 2 : ℝ) ^ (i + k)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum).symm
    _ = ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) := by
        congr 1
        simp_rw [pow_add]
        rw [tsum_mul_right, tsum_geometric_two]

/-- Generic completion: a compact-local Cauchy-in-probability sequence of almost surely
continuous random functions with measurable evaluations has a measurable
`C(X, ℝ)`-valued limit; the entire sequence converges to it locally uniformly in
probability, and a fixed subsequence converges almost surely pointwise. -/
theorem aux_tight_whole_space_resolvent_limit_completion
    {Ω X : Type*} [MeasurableSpace Ω] [MetricSpace X] [LocallyCompactSpace X]
    [SigmaCompactSpace X] [SecondCountableTopology X]
    [SecondCountableTopology C(X, ℝ)] [MeasurableSpace C(X, ℝ)] [BorelSpace C(X, ℝ)]
    (μ : Measure Ω) (u : Nat → Ω → X → ℝ)
    (hmeas : ∀ N x, Measurable fun ω => u N ω x)
    (hcont : ∀ᵐ ω ∂μ, ∀ N, Continuous (u N ω))
    (hcauchy : ∀ B : Set X, IsCompact B → ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : Nat, ∀ N P, N0 ≤ N → N0 ≤ P →
        μ {ω | ∃ x ∈ B, eps ≤ |u N ω x - u P ω x|} ≤ ENNReal.ofReal rho) :
    ∃ v : Ω → C(X, ℝ), ∃ φ : Nat → Nat, StrictMono φ ∧ Measurable v ∧
      (∀ᵐ ω ∂μ, ∀ x, Tendsto (fun k => u (φ k) ω x) atTop (𝓝 (v ω x))) ∧
      (∀ B : Set X, IsCompact B → ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ N0 : Nat, ∀ N, N0 ≤ N →
          μ {ω | ∃ x ∈ B, eps ≤ |u N ω x - v ω x|} ≤ ENNReal.ofReal rho) := by
  classical
  -- a measurable full-measure set on which every `u N ω` is continuous
  obtain ⟨T0, hT0sub, hT0meas, hT0null⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hcont)
  have hS0cont : ∀ ω, ω ∉ T0 → ∀ N, Continuous (u N ω) := by
    intro ω hω
    by_contra h
    exact hω (hT0sub h)
  -- an increasing open cover by interiors of a compact exhaustion
  let Kc := CompactExhaustion.choice X
  let U : Nat → Set X := fun k => interior (Kc (k + 1))
  have hUopen : ∀ k, IsOpen (U k) := fun k => isOpen_interior
  have hUmono : Monotone U := fun a b hab => interior_mono (Kc.subset (by omega))
  have hUK : ∀ k, U k ⊆ Kc (k + 1) := fun k => interior_subset
  have hKU : ∀ k, Kc k ⊆ U k := fun k => Kc.subset_interior_succ k
  have hUcover : ∀ x, ∃ k, x ∈ U k := by
    intro x
    have hx : x ∈ ⋃ n, Kc n := by rw [Kc.iUnion_eq]; trivial
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
    exact ⟨k, hKU k hk⟩
  obtain ⟨D, hDc, hDdense⟩ := TopologicalSpace.exists_countable_dense X
  -- a fast subsequence
  have hsel : ∀ k : Nat, ∃ n0 : Nat, ∀ N P, n0 ≤ N → n0 ≤ P →
      μ {ω | ∃ x ∈ Kc (k + 1), (1 / 2 : ℝ) ^ k ≤ |u N ω x - u P ω x|} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ k) :=
    fun k => hcauchy (Kc (k + 1)) (Kc.isCompact _) _ (by positivity) _ (by positivity)
  choose n hn using hsel
  let φ : Nat → Nat := fun k => k + ∑ j ∈ Finset.range (k + 1), n j
  have hφmono : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro k
    simp only [φ, Finset.sum_range_succ _ (k + 1)]
    omega
  have hnφ : ∀ k, n k ≤ φ k := fun k => by
    have : n k ≤ ∑ j ∈ Finset.range (k + 1), n j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.self_mem_range_succ k)
    simp only [φ]
    omega
  let Bad : Nat → Set Ω := fun k =>
    {ω | ∃ x ∈ Kc (k + 1), (1 / 2 : ℝ) ^ k ≤ |u (φ k) ω x - u (φ (k + 1)) ω x|}
  have hBad : ∀ k, μ (Bad k) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := fun k =>
    hn k _ _ (hnφ k) ((hnφ k).trans (hφmono.monotone (Nat.le_succ k)))
  let E : Nat → Set Ω := fun k => ⋃ i, Bad (i + k)
  have hE : ∀ k, μ (E k) ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) :=
    aux_tight_whole_space_resolvent_limit_tail_measure μ Bad hBad
  -- goodness at level `k`
  let Good : Nat → Ω → Prop := fun k ω => ∀ i, k ≤ i → ∀ x ∈ U i,
    |u (φ i) ω x - u (φ (i + 1)) ω x| ≤ (1 / 2 : ℝ) ^ i
  have hGoodE : ∀ k ω, ω ∉ E k → Good k ω := by
    intro k ω hω i hi x hx
    have hnot : ω ∉ Bad (i - k + k) := fun h => hω (Set.mem_iUnion.mpr ⟨i - k, h⟩)
    have hik : i - k + k = i := by omega
    rw [hik] at hnot
    by_contra hlt
    exact hnot ⟨x, hUK i hx, (lt_of_not_ge hlt).le⟩
  -- a measurable good set
  let G : Set Ω := T0ᶜ ∩ ⋃ k, ⋂ i, ⋂ (_ : k ≤ i), ⋂ x ∈ D ∩ U i,
    {ω | |u (φ i) ω x - u (φ (i + 1)) ω x| ≤ (1 / 2 : ℝ) ^ i}
  have hGmeas : MeasurableSet G := by
    refine hT0meas.compl.inter (MeasurableSet.iUnion fun k => MeasurableSet.iInter fun i =>
      MeasurableSet.iInter fun _ => MeasurableSet.biInter (hDc.mono Set.inter_subset_left)
        fun x _ => ?_)
    exact measurableSet_le
      (continuous_abs.measurable.comp ((hmeas _ x).sub (hmeas _ x))) measurable_const
  have hGgood : ∀ ω ∈ G, ∃ k, Good k ω := by
    rintro ω ⟨hωT, hωU⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hωU
    refine ⟨k, fun i hi x hx => ?_⟩
    have hcts := hS0cont ω hωT
    have hclosed : IsClosed {y | |u (φ i) ω y - u (φ (i + 1)) ω y| ≤ (1 / 2 : ℝ) ^ i} :=
      isClosed_le (continuous_abs.comp ((hcts _).sub (hcts _))) continuous_const
    have hsub : U i ∩ D ⊆ {y | |u (φ i) ω y - u (φ (i + 1)) ω y| ≤ (1 / 2 : ℝ) ^ i} := by
      intro y hy
      have := Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hk i) hi) y
      exact Set.mem_iInter.mp this ⟨hy.2, hy.1⟩
    exact closure_minimal hsub hclosed (hDdense.open_subset_closure_inter (hUopen i) hx)
  have hEG : ∀ k ω, ω ∉ T0 → ω ∉ E k → ω ∈ G := by
    intro k ω hωT hωE
    refine ⟨hωT, Set.mem_iUnion.mpr ⟨k, ?_⟩⟩
    simp only [Set.mem_iInter]
    intro i hi x hx
    exact hGoodE k ω hωE i hi x hx.2
  -- the limit
  have hlimG : ∀ ω ∈ G, ∃ k,
      (∀ x, Tendsto (fun i => u (φ i) ω x) atTop
        (𝓝 (limUnder atTop (fun i => u (φ i) ω x)))) ∧
      (∀ j, k ≤ j → ∀ x ∈ U j,
        |u (φ j) ω x - limUnder atTop (fun i => u (φ i) ω x)| ≤ 2 * (1 / 2 : ℝ) ^ j) ∧
      Continuous (fun x => limUnder atTop (fun i => u (φ i) ω x)) := by
    intro ω hω
    obtain ⟨k, hk⟩ := hGgood ω hω
    obtain ⟨h1, h2, h3⟩ := aux_tight_whole_space_resolvent_limit_geometric_limit U hUopen hUmono
      hUcover (fun i => u (φ i) ω) k hk
    exact ⟨k, h1, h2, h3 fun i => hS0cont ω hω.1 _⟩
  let v : Ω → C(X, ℝ) := fun ω =>
    if h : ω ∈ G then ⟨fun x => limUnder atTop (fun i => u (φ i) ω x), (hlimG ω h).choose_spec.2.2⟩
    else 0
  have hv_eval : ∀ ω x, v ω x = G.indicator (fun ω => limUnder atTop (fun i => u (φ i) ω x)) ω := by
    intro ω x
    by_cases h : ω ∈ G
    · simp [v, h]
    · simp [v, h]
  have hvG : ∀ ω ∈ G, ∀ x, v ω x = limUnder atTop (fun i => u (φ i) ω x) := by
    intro ω h x
    rw [hv_eval, Set.indicator_of_mem h]
  -- measurability
  have hvmeas : Measurable v := by
    apply aux_tight_whole_space_resolvent_limit_measurable_of_eval
    intro x
    simp_rw [hv_eval]
    refine measurable_of_tendsto_metrizable
      (f := fun i ω => G.indicator (fun ω => u (φ i) ω x) ω)
      (fun i => (hmeas (φ i) x).indicator hGmeas) ?_
    rw [tendsto_pi_nhds]
    intro ω
    by_cases h : ω ∈ G
    · simp only [Set.indicator_of_mem h]
      exact (hlimG ω h).choose_spec.1 x
    · simp only [Set.indicator_of_notMem h]
      exact tendsto_const_nhds
  -- the good set has full measure
  have hGc : μ Gᶜ = 0 := by
    have hle : ∀ k, μ Gᶜ ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) := by
      intro k
      have hsub : Gᶜ ⊆ T0 ∪ E k := by
        intro ω hω
        by_contra hc
        simp only [Set.mem_union, not_or] at hc
        exact hω (hEG k ω hc.1 hc.2)
      calc μ Gᶜ ≤ μ (T0 ∪ E k) := measure_mono hsub
        _ ≤ μ T0 + μ (E k) := measure_union_le _ _
        _ ≤ 0 + ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k) := by rw [hT0null]; gcongr; exact hE k
        _ = _ := zero_add _
    have htend : Tendsto (fun k : Nat => ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ k)) atTop (𝓝 0) := by
      have h := ENNReal.tendsto_ofReal
        ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num)).const_mul 2)
      simpa using h
    exact le_antisymm (ge_of_tendsto' htend hle) (zero_le)
  refine ⟨v, φ, hφmono, hvmeas, ?_, ?_⟩
  · have hGae : ∀ᵐ ω ∂μ, ω ∈ G := by
      rw [ae_iff]
      exact hGc
    filter_upwards [hGae] with ω hω x
    rw [hvG ω hω x]
    exact (hlimG ω hω).choose_spec.1 x
  · intro B hB eps heps rho hrho
    obtain ⟨j, hBj⟩ := Kc.exists_superset_of_isCompact hB
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < min eps rho / 4)
      (by norm_num : (1 / 2 : ℝ) < 1)
    obtain ⟨N0, hN0⟩ := hcauchy B hB (eps / 2) (by positivity) (rho / 2) (by positivity)
    refine ⟨N0, fun N hN => ?_⟩
    let k := max (max j M) N0
    have hjk : j ≤ k := le_trans (le_max_left _ _) (le_max_left _ _)
    have hMk : M ≤ k := le_trans (le_max_right _ _) (le_max_left _ _)
    have hN0k : N0 ≤ φ k := le_trans (le_max_right _ _) (hφmono.id_le k)
    have hpow : (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ M :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hMk
    have hmin1 : min eps rho ≤ eps := min_le_left _ _
    have hmin2 : min eps rho ≤ rho := min_le_right _ _
    let A : Set Ω := {ω | ∃ x ∈ B, eps / 2 ≤ |u N ω x - u (φ k) ω x|}
    have hsub : {ω | ∃ x ∈ B, eps ≤ |u N ω x - v ω x|} ⊆ A ∪ (T0 ∪ E k) := by
      rintro ω ⟨x, hxB, hx⟩
      by_cases hT : ω ∈ T0
      · exact Or.inr (Or.inl hT)
      by_cases hEk : ω ∈ E k
      · exact Or.inr (Or.inr hEk)
      left
      have hωG := hEG k ω hT hEk
      obtain ⟨k', -, -, -⟩ := hlimG ω hωG
      have hgood := hGoodE k ω hEk
      have hbound := (aux_tight_whole_space_resolvent_limit_geometric_limit U hUopen hUmono hUcover
        (fun i => u (φ i) ω) k hgood).2.1 k le_rfl x (hUmono hjk (hKU j (hBj hxB)))
      rw [← hvG ω hωG x] at hbound
      refine ⟨x, hxB, ?_⟩
      have htri : |u N ω x - v ω x| ≤ |u N ω x - u (φ k) ω x| + |u (φ k) ω x - v ω x| := by
        calc |u N ω x - v ω x| = |(u N ω x - u (φ k) ω x) + (u (φ k) ω x - v ω x)| := by
              ring_nf
          _ ≤ _ := abs_add_le _ _
      linarith
    calc μ {ω | ∃ x ∈ B, eps ≤ |u N ω x - v ω x|} ≤ μ (A ∪ (T0 ∪ E k)) := measure_mono hsub
      _ ≤ μ A + (μ T0 + μ (E k)) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ ENNReal.ofReal (rho / 2) + (0 + ENNReal.ofReal (rho / 2)) := by
          rw [hT0null]
          gcongr
          · exact hN0 N (φ k) hN hN0k
          · exact (hE k).trans (ENNReal.ofReal_le_ofReal (by linarith))
      _ = ENNReal.ofReal rho := by
          rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring


/-- The discounted occupation functional of a path is strongly measurable in the path. -/
theorem aux_tight_whole_space_resolvent_limit_occupation_stronglyMeasurable
    {d : Nat} (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ) :
    StronglyMeasurable (fun path : DiffusionPath d => ∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-lam * t) * f (path (Real.toNNReal t))) := by
  have hcont : Continuous (fun q : DiffusionPath d × ℝ =>
      Real.exp (-lam * q.2) * f (q.1 (Real.toNNReal q.2))) := by
    have heval : Continuous (fun q : DiffusionPath d × ℝ => q.1 (Real.toNNReal q.2)) :=
      continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).mul
      (f.continuous.comp heval)
  exact hcont.measurable.stronglyMeasurable.integral_prod_right'

/-- Each evaluation of the actual full cutoff resolvent is measurable in the environment. -/
theorem aux_tight_whole_space_resolvent_limit_eval_measurable
    {d : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : Nat → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (RN : Nat → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (hRN : ∀ N omega lam f x, RN N omega lam f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
    (N : Nat) (lam : ℝ) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (x : SpatialCoordinates d) :
    Measurable (fun omega => RN N omega lam f x) := by
  haveI := hKN N
  have hΦ := aux_tight_whole_space_resolvent_limit_occupation_stronglyMeasurable (d := d) lam f
  have hker : StronglyMeasurable (fun a : BilateralField d × SpatialCoordinates d =>
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(KN N a)) :=
    (hΦ.comp_measurable measurable_snd).integral_kernel_prod_right'
  have hfun : (fun omega => RN N omega lam f x) = (fun a : BilateralField d × SpatialCoordinates d =>
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(KN N a)) ∘ (fun omega => (omega, x)) := by
    funext omega
    exact hRN N omega lam f x
  rw [hfun]
  exact hker.measurable.comp measurable_prodMk_right


/-- A rate-`(1/2)^k` eventual bound gives convergence. -/
theorem aux_tight_whole_space_resolvent_limit_tendsto_of_geometric
    (g : Nat → ℝ) (L : ℝ) (h : ∀ᶠ k in atTop, |g k - L| < (1 / 2 : ℝ) ^ k) :
    Tendsto g atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨k0, hk0⟩ := eventually_atTop.mp h
  refine ⟨max k0 M, fun k hk => ?_⟩
  have hpow : (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ M :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_trans (le_max_right _ _) hk)
  rw [Real.dist_eq]
  linarith [hk0 k (le_trans (le_max_left _ _) hk)]

/-- Diagonal Borel--Cantelli: countably many sequences of (possibly non-measurable) bad
events that are small in probability have one common subsequence of a given subsequence
along which almost surely each family is eventually avoided at rate `(1/2)^k`. -/
theorem aux_tight_whole_space_resolvent_limit_diagonal_subseq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : Nat → Nat → ℝ → Set Ω)
    (hE : ∀ m, ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
      ∃ N0 : Nat, ∀ N, N0 ≤ N → μ (E m N eps) ≤ ENNReal.ofReal rho)
    (φ : Nat → Nat) (hφ : StrictMono φ) :
    ∃ ψ : Nat → Nat, StrictMono ψ ∧
      ∀ᵐ ω ∂μ, ∀ m, ∀ᶠ k in atTop, ω ∉ E m (φ (ψ k)) ((1 / 2 : ℝ) ^ k) := by
  classical
  have hsel : ∀ m k : Nat, ∃ N0 : Nat, ∀ N, N0 ≤ N →
      μ (E m N ((1 / 2 : ℝ) ^ k)) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k / (k + 1)) :=
    fun m k => hE m _ (by positivity) _ (by positivity)
  choose N0 hN0 using hsel
  let n : Nat → Nat := fun k => (Finset.range (k + 1)).sup (fun m => N0 m k)
  let ψ : Nat → Nat := fun k => k + ∑ j ∈ Finset.range (k + 1), n j
  have hψ : StrictMono ψ := by
    apply strictMono_nat_of_lt_succ
    intro k
    simp only [ψ, Finset.sum_range_succ _ (k + 1)]
    omega
  have hnψ : ∀ k, n k ≤ ψ k := fun k => by
    have : n k ≤ ∑ j ∈ Finset.range (k + 1), n j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.self_mem_range_succ k)
    simp only [ψ]
    omega
  have hN0ψ : ∀ k m, m ≤ k → N0 m k ≤ φ (ψ k) := fun k m hm =>
    (Finset.le_sup (f := fun m => N0 m k)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))).trans ((hnψ k).trans (hφ.id_le _))
  let Bad : Nat → Set Ω := fun k =>
    ⋃ m ∈ Finset.range (k + 1), E m (φ (ψ k)) ((1 / 2 : ℝ) ^ k)
  have hBad : ∀ k, μ (Bad k) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro k
    calc μ (Bad k) ≤ ∑ m ∈ Finset.range (k + 1), μ (E m (φ (ψ k)) ((1 / 2 : ℝ) ^ k)) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ m ∈ Finset.range (k + 1), ENNReal.ofReal ((1 / 2 : ℝ) ^ k / (k + 1)) :=
          Finset.sum_le_sum fun m hm =>
            hN0 m k _ (hN0ψ k m (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)))
      _ = ENNReal.ofReal (∑ m ∈ Finset.range (k + 1), (1 / 2 : ℝ) ^ k / (k + 1)) :=
          (ENNReal.ofReal_sum_of_nonneg fun m _ => by positivity).symm
      _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
          congr 1
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          field_simp
  have hsum : ∑' k, μ (Bad k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hBad)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  refine ⟨ψ, hψ, ?_⟩
  filter_upwards [ae_eventually_notMem hsum] with ω hω m
  filter_upwards [hω, eventually_ge_atTop m] with k hk hmk
  intro hE'
  exact hk (Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le hmk)) hE')

/-- Passing a localization inequality with a bounded error term to the limit along a
subsequence retains the limsup of the error term over the entire sequence. -/
theorem aux_tight_whole_space_resolvent_limit_limsup_pass
    (a b : Nat → ℝ) (A B : ℝ) (e : Nat → ℝ) (he1 : ∀ N, e N ≤ 1)
    (ψ : Nat → Nat) (hψ : StrictMono ψ) (K tail : ℝ) (hK : 0 ≤ K)
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B))
    (hloc : ∀ k, |a k - b k| ≤ K * (e (ψ k) + tail)) :
    |A - B| ≤ K * (Filter.limsup e atTop + tail) := by
  set L := Filter.limsup e atTop
  have hbdd : IsBoundedUnder (· ≤ ·) atTop e := isBoundedUnder_of ⟨1, he1⟩
  have hdiff : Tendsto (fun k => |a k - b k|) atTop (𝓝 |A - B|) :=
    (continuous_abs.tendsto _).comp (ha.sub hb)
  have heps : ∀ ε : ℝ, 0 < ε → |A - B| ≤ K * (L + ε + tail) := by
    intro ε hε
    have hev : ∀ᶠ N in atTop, e N < L + ε :=
      eventually_lt_of_limsup_lt (lt_add_of_pos_right L hε) hbdd
    have hevk : ∀ᶠ k in atTop, |a k - b k| ≤ K * (L + ε + tail) := by
      filter_upwards [hψ.tendsto_atTop.eventually hev] with k hk
      exact (hloc k).trans (mul_le_mul_of_nonneg_left (by linarith) hK)
    exact le_of_tendsto hdiff hevk
  by_contra hcon
  push_neg at hcon
  set δ := |A - B| - K * (L + tail)
  have hδ : 0 < δ := by simp only [δ]; linarith
  have h := heps (δ / (2 * (K + 1))) (by positivity)
  have hKε : K * (δ / (2 * (K + 1))) ≤ δ / 2 := by
    have hK1 : 0 < K + 1 := by linarith
    rw [show K * (δ / (2 * (K + 1))) = (δ / 2) * (K / (K + 1)) by field_simp]
    have : K / (K + 1) ≤ 1 := (div_le_one hK1).mpr (by linarith)
    nlinarith
  have hexp : K * (L + δ / (2 * (K + 1)) + tail) = K * (L + tail) + K * (δ / (2 * (K + 1))) := by
    ring
  linarith

/-- The actual exit probabilities lie in `[0, 1]`. -/
theorem aux_tight_whole_space_resolvent_limit_exitP_le_one
    {d : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (KN : Nat → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (Qc : Nat → SpatialCoordinates d) (Qr : Nat → ℝ) (hQr : ∀ m, 0 < Qr m)
    (exitP : Nat → Nat → BilateralField d → SpatialCoordinates d → ℝ → ℝ)
    (hexitP : ∀ m N omega x T, exitP m N omega x T =
      ((KN N (omega, x)) {path | ContinuousPath.exitTime
        (centeredCube (Qc m) (Qr m) (hQr m) : Set _) path ≤ ENNReal.ofReal T}).toReal)
    (m N : Nat) (omega : BilateralField d) (x : SpatialCoordinates d) (T : ℝ) :
    exitP m N omega x T ≤ 1 := by
  haveI := (hKN N).isProbabilityMeasure (omega, x)
  rw [hexitP]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)



theorem tight_whole_space_resolvent_limit
    {d : Nat}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H)
    (PN : Nat → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
    (KN : Nat → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
    (hKN : ∀ N, IsMarkovKernel (KN N))
    (hin : in_crossing M H PN KN)
    (Qc : Nat → SpatialCoordinates d) (Qr : Nat → ℝ)
    (hQr : ∀ m, 0 < Qr m)
    (RN : Nat → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (RNQ : Nat → Nat → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (RQ : Nat → BilateralField d → ℝ →
      BoundedContinuousFunction (SpatialCoordinates d) ℝ → SpatialCoordinates d → ℝ)
    (exitP : Nat → Nat → BilateralField d → SpatialCoordinates d → ℝ → ℝ)
    (hRN : ∀ N omega lam f x, RN N omega lam f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-lam * t) * f (path (Real.toNNReal t))) ∂(KN N (omega, x)))
    (hRNQ : ∀ m N omega lam f x, RNQ m N omega lam f x =
      ∫ path, (∫ t in Set.Ioi (0 : ℝ),
        Set.indicator
          {s : ℝ | ENNReal.ofReal s < ContinuousPath.exitTime
            (centeredCube (Qc m) (Qr m) (hQr m) : Set _) path}
          (fun s : ℝ => Real.exp (-lam * s) * f (path (Real.toNNReal s))) t)
        ∂(KN N (omega, x)))
    (hexitP : ∀ m N omega x T, exitP m N omega x T =
      ((KN N (omega, x)) {path | ContinuousPath.exitTime
        (centeredCube (Qc m) (Qr m) (hQr m) : Set _) path ≤ ENNReal.ofReal T}).toReal)
    (hcont : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ N lam, 0 < lam → ∀ f, Continuous (RN N omega lam f))
    (hkilled : ∀ m lam, 0 < lam → ∀ f, ∀ eps : ℝ, 0 < eps →
      ∀ rho : ℝ, 0 < rho → ∃ N0 : Nat, ∀ N, N0 ≤ N →
        (chaosSampleLaw M).toMeasure
          {omega | ∃ x ∈ closure (centeredCube (Qc m) (Qr m) (hQr m) : Set _),
            eps ≤ |RNQ m N omega lam f x - RQ m omega lam f x|} ≤ ENNReal.ofReal rho)
    (hcontain : ∀ B : Set (SpatialCoordinates d), IsCompact B →
      ∀ T : ℝ, 0 ≤ T → ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
        ∃ m : Nat, B ⊆ (centeredCube (Qc m) (Qr m) (hQr m) : Set _) ∧
          ∀ N : Nat, (chaosSampleLaw M).toMeasure
            {omega | ∃ x ∈ B, eps ≤ exitP m N omega x T} ≤ ENNReal.ofReal rho) :
    ∃ R : ℝ → BoundedContinuousFunction (SpatialCoordinates d) ℝ →
        BilateralField d → C(SpatialCoordinates d, ℝ),
      ∀ lam : ℝ, 0 < lam → ∀ f,
        Measurable (R lam f) ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ x, |R lam f omega x| ≤ ‖f‖ / lam) ∧
        (∀ B : Set (SpatialCoordinates d), IsCompact B →
          ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
            ∃ N0 : Nat, ∀ N, N0 ≤ N →
              (chaosSampleLaw M).toMeasure
                {omega | ∃ x ∈ B, eps ≤ |RN N omega lam f x - R lam f omega x|} ≤
                  ENNReal.ofReal rho) ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ m : Nat, ∀ x ∈ (centeredCube (Qc m) (Qr m) (hQr m) : Set _),
            ∀ T : ℝ, 0 ≤ T →
              |R lam f omega x - RQ m omega lam f x| ≤ (‖f‖ / lam) *
                (Filter.limsup (fun N : Nat => exitP m N omega x T) Filter.atTop +
                  Real.exp (-lam * T))) := by
  classical
  have hmain : ∀ lam : ℝ, ∀ f : BoundedContinuousFunction (SpatialCoordinates d) ℝ,
      ∃ v : BilateralField d → C(SpatialCoordinates d, ℝ), 0 < lam →
        Measurable v ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ x, |v omega x| ≤ ‖f‖ / lam) ∧
        (∀ B : Set (SpatialCoordinates d), IsCompact B →
          ∀ eps : ℝ, 0 < eps → ∀ rho : ℝ, 0 < rho →
            ∃ N0 : Nat, ∀ N, N0 ≤ N →
              (chaosSampleLaw M).toMeasure
                {omega | ∃ x ∈ B, eps ≤ |RN N omega lam f x - v omega x|} ≤
                  ENNReal.ofReal rho) ∧
        (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ m : Nat, ∀ x ∈ (centeredCube (Qc m) (Qr m) (hQr m) : Set _),
            ∀ T : ℝ, 0 ≤ T →
              |v omega x - RQ m omega lam f x| ≤ (‖f‖ / lam) *
                (Filter.limsup (fun N : Nat => exitP m N omega x T) Filter.atTop +
                  Real.exp (-lam * T))) := by
    intro lam f
    by_cases hlam : 0 < lam
    swap
    · exact ⟨0, fun h => absurd h hlam⟩
    have hK : 0 ≤ ‖f‖ / lam := div_nonneg (norm_nonneg _) hlam.le
    obtain ⟨v, φ, hφ, hvmeas, hvae, hvconv⟩ := aux_tight_whole_space_resolvent_limit_completion
      (chaosSampleLaw M).toMeasure (fun N ω x => RN N ω lam f x)
      (fun N x => aux_tight_whole_space_resolvent_limit_eval_measurable KN hKN RN hRN N lam f x)
      (by
        filter_upwards [hcont] with ω hω N
        exact hω N lam hlam f)
      (aux_tight_whole_space_resolvent_limit_concrete_cauchy_in_measure M H PN KN hKN hin Qc Qr hQr
        RN RNQ RQ exitP hRN hRNQ hexitP hkilled hcontain lam hlam f)
    obtain ⟨ψ, hψ, hψae⟩ := aux_tight_whole_space_resolvent_limit_diagonal_subseq
      (chaosSampleLaw M).toMeasure
      (fun m N eps => {ω | ∃ x ∈ closure (centeredCube (Qc m) (Qr m) (hQr m) : Set _),
        eps ≤ |RNQ m N ω lam f x - RQ m ω lam f x|})
      (fun m eps heps rho hrho => hkilled m lam hlam f eps heps rho hrho) φ hφ
    let good : BilateralField d → Prop := fun ω =>
      (∀ x, Tendsto (fun k => RN (φ (ψ k)) ω lam f x) atTop (𝓝 (v ω x))) ∧
        ∀ m, ∀ x ∈ closure (centeredCube (Qc m) (Qr m) (hQr m) : Set _),
          Tendsto (fun k => RNQ m (φ (ψ k)) ω lam f x) atTop (𝓝 (RQ m ω lam f x))
    have hgood : ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, good ω := by
      filter_upwards [hvae, hψae] with ω h1 h2
      refine ⟨fun x => (h1 x).comp hψ.tendsto_atTop, fun m x hx => ?_⟩
      apply aux_tight_whole_space_resolvent_limit_tendsto_of_geometric
      filter_upwards [h2 m] with k hk
      by_contra hlt
      exact hk ⟨x, hx, le_of_not_gt hlt⟩
    have hbound := aux_tight_whole_space_resolvent_limit_bound KN hKN RN hRN lam hlam
    refine ⟨v, fun _ => ⟨hvmeas, ?_, hvconv, ?_⟩⟩
    · filter_upwards [hvae] with ω hω x
      exact le_of_tendsto' ((continuous_abs.tendsto _).comp (hω x))
        (fun k => hbound (φ k) ω f x)
    · filter_upwards [hgood] with ω hω m x hx T hT
      exact aux_tight_whole_space_resolvent_limit_limsup_pass
        (fun k => RN (φ (ψ k)) ω lam f x) (fun k => RNQ m (φ (ψ k)) ω lam f x)
        (v ω x) (RQ m ω lam f x) (fun N => exitP m N ω x T)
        (fun N => aux_tight_whole_space_resolvent_limit_exitP_le_one KN hKN Qc Qr hQr exitP hexitP
          m N ω x T)
        (fun k => φ (ψ k)) (hφ.comp hψ) (‖f‖ / lam) (Real.exp (-lam * T)) hK
        (hω.1 x) (hω.2 m x (subset_closure hx))
        (fun k => aux_tight_whole_space_resolvent_limit_localization_bridge M H PN KN hKN hin Qc Qr hQr
          RN RNQ exitP hRN hRNQ hexitP _ m ω x lam T f hlam hT hx)
  choose R hR using hmain
  exact ⟨R, fun lam hlam f => hR lam f hlam⟩

end Paper
