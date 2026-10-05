module

public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.lem_extension
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.astar_removing_H
public import SubdiffusiveProcess.Paper.Foundations.Bank.DeepGridGeometry
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import SubdiffusiveProcess.Paper.lem_as_coarse_first_clause_assembly
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Localization
public import Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Properties
public import Homogenization.Sobolev.Fractional.PairCapture
public import Homogenization.Deterministic.MultiscaleQuantitiesBasic.Ellipticity.Descendants
public import SubdiffusiveProcess.CoarseGrainingVocab.Sensitivity
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.ScalarFieldPackaging
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Set Filter Topology SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper
/-- Uniform probability-space `Lp` bounds imply eventual exponential control. -/
theorem aux_lem_as_coarse_deep_grid_uniform_lp_eventually
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℝ) (hK : ∀ N, Measurable (K N))
    (p C ξ : ℝ) (hp : 1 ≤ p) (_hC : 0 ≤ C) (hξ : 0 < ξ)
    (hLp : ∀ N, MemLp (K N) (ENNReal.ofReal p) μ)
    (hBound : ∀ N, eLpNorm (K N) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C) :
    ∀ᵐ ω ∂μ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → K N ω ≤ (3 : ℝ) ^ (ξ * (N : ℝ)) := by
  have hgeom :
      (∑' N : ℕ, ENNReal.ofReal (C * (3 : ℝ) ^ (-ξ * (N : ℝ)))) < ⊤ := by
    have hrpos : 0 < (3 : ℝ) ^ (-ξ) := Real.rpow_pos_of_pos (by norm_num) _
    have hrlt : (3 : ℝ) ^ (-ξ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hgeom' : Summable fun N : ℕ => ((3 : ℝ) ^ (-ξ)) ^ N :=
      summable_geometric_of_lt_one hrpos.le hrlt
    have hsum : Summable fun N : ℕ => C * (3 : ℝ) ^ (-ξ * (N : ℝ)) := by
      have h' := hgeom'.mul_left C
      simpa only [Real.rpow_mul_natCast (by norm_num : 0 ≤ (3 : ℝ)) (-ξ)] using h'
    exact hsum.tsum_ofReal_lt_top
  let E : ℕ → Set Ω := fun N => {ω | (3 : ℝ) ^ (ξ * (N : ℝ)) ≤ |K N ω|}
  have hE : ∀ N, MeasurableSet (E N) := by
    intro N
    exact measurableSet_le measurable_const (hK N).abs
  have hmass : ∀ N, μ (E N) ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-ξ * (N : ℝ))) := by
    intro N
    have hnorm : eLpNorm (K N) 1 μ ≤ ENNReal.ofReal C := by
      have hpenn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
        simpa using (ENNReal.ofReal_le_ofReal hp)
      calc
        eLpNorm (K N) 1 μ ≤ eLpNorm (K N) (ENNReal.ofReal p) μ :=
          eLpNorm_le_eLpNorm_of_exponent_le hpenn
        _ ≤ ENNReal.ofReal C := hBound N
    have hth : 0 < (3 : ℝ) ^ (ξ * (N : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have htail : μ (E N) ≤ ENNReal.ofReal C / ENNReal.ofReal ((3 : ℝ) ^ (ξ * (N : ℝ))) := by
      have hmeas : AEMeasurable (fun ω => ENNReal.ofReal |K N ω|) μ :=
        (ENNReal.measurable_ofReal.comp (hK N).abs).aemeasurable
      have hmarkov := meas_ge_le_lintegral_div hmeas
        (ne_of_gt (ENNReal.ofReal_pos.mpr hth)) ENNReal.ofReal_ne_top
      have hset : E N = {ω | ENNReal.ofReal ((3 : ℝ) ^ (ξ * (N : ℝ))) ≤ ENNReal.ofReal |K N ω|} := by
        ext ω
        exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _) |>.symm
      rw [hset]
      exact hmarkov.trans (ENNReal.div_le_div_right (by simpa [eLpNorm_one_eq_lintegral_enorm (hLp N).aestronglyMeasurable, Real.enorm_eq_ofReal_abs] using hnorm) _)
    calc
      μ (E N) ≤ ENNReal.ofReal C / ENNReal.ofReal ((3 : ℝ) ^ (ξ * (N : ℝ))) := htail
      _ = ENNReal.ofReal (C * (3 : ℝ) ^ (-ξ * (N : ℝ))) := by
        rw [← ENNReal.ofReal_div_of_pos hth]
        congr 1
        rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : 0 ≤ (3 : ℝ))]
        congr 1
        ring_nf
  have hsum : (∑' N, μ (E N)) < ⊤ :=
    lt_of_le_of_lt (ENNReal.tsum_le_tsum hmass) hgeom
  have hbc : ∀ᵐ ω ∂μ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ω ∉ E N := by
    simpa [Filter.eventually_atTop] using MeasureTheory.ae_eventually_notMem hsum.ne
  filter_upwards [hbc] with ω hω
  obtain ⟨N₀, hN₀⟩ := hω
  refine ⟨N₀, fun N hN => ?_⟩
  have hlt : |K N ω| < (3 : ℝ) ^ (ξ * (N : ℝ)) := lt_of_not_ge (hN₀ N hN)
  exact le_of_lt ((le_abs_self _).trans_lt hlt)

section DeepGridHelpers
open Homogenization.Book.Ch02

/-- A supremum over a finite set is bounded by a nonnegative common bound. -/
theorem aux_lem_as_coarse_deep_grid_finsetSup_le {α : Type*} (s : Finset α) (f : α → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (h : ∀ x ∈ s, f x ≤ B) : finsetSupReal s f ≤ B := by
  unfold finsetSupReal
  apply Real.sSup_le _ hB
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

/-- Centered cubes with equal centre and side coincide (proof irrelevance). -/
theorem aux_lem_as_coarse_deep_grid_cube_congr {d : ℕ} {w w' : SpatialCoordinates d}
    {t t' : ℝ} (ht : 0 < t) (ht' : 0 < t') (hw : w = w') (htt : t = t') :
    centeredCube w t ht = centeredCube w' t' ht' := by
  subst hw; subst htt; rfl

/-- **Ancestor factorisation.**  A relative-depth-`k` descendant `R` of the unit root factors
through its relative-depth-`k - m` ancestor `P`; the offset of `R` inside `P`, rescaled to the
unit root, is a depth-`m` descendant `R'` of the unit root, and
`R.index = 3^m P.index + R'.index`. -/
theorem aux_lem_as_coarse_deep_grid_ancestor {d : ℕ} {k m : ℕ} (hmk : m ≤ k)
    {R : Homogenization.TriadicCube d}
    (hR : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (k : ℤ))) :
    ∃ P ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - ((k - m : ℕ) : ℤ)),
    ∃ R' ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
        ((Homogenization.originCube d 0).scale - (m : ℤ)),
      ∀ i, R.index i = 3 ^ m * P.index i + R'.index i := by
  have hk : (Homogenization.originCube d 0).scale - (k : ℤ) ≤
      (Homogenization.originCube d 0).scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le k)
  rw [Homogenization.mem_descendantsAtScale_iff hk] at hR
  have htn : Int.toNat ((Homogenization.originCube d 0).scale -
      ((Homogenization.originCube d 0).scale - (k : ℤ))) = (k - m) + m := by
    simp only [sub_sub_cancel, Int.toNat_natCast]
    omega
  rw [htn] at hR
  obtain ⟨P, hP, hRP⟩ := Homogenization.exists_descendant_ancestor_at_depth (k - m) m hR
  have hrange := Homogenization.Gagliardo.index_range_of_mem_descendantsAtDepth hRP
  let R' : Homogenization.TriadicCube d :=
    ⟨-(m : ℤ), fun i => R.index i - 3 ^ m * P.index i⟩
  have hR' : R' ∈ Homogenization.descendantsAtDepth (Homogenization.originCube d 0) m := by
    apply Homogenization.Gagliardo.mem_descendantsAtDepth_of_index_range
    · simp [R', Homogenization.originCube]
    · intro i
      have hi := hrange i
      simp only [R', Homogenization.originCube, Pi.zero_apply, mul_zero, zero_sub, zero_add]
      constructor <;> linarith [hi.1, hi.2]
  refine ⟨P, Homogenization.mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hP, R',
    Homogenization.mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hR', fun i => ?_⟩
  simp [R']

/-- **Chart transport, general outer cell.**  For a sub-cell `w₀ + r₀ Q₀` of the root, the
cell matrices of a depth-`n` descendant `R` in the chart of `w₀ + r₀ Q₀` are the cell matrices
of the unit root in the chart of the grid cell `w₀ + r₀ 3^{-n}(R.index + Q₀)`.  (The case
`w₀ = z, r₀ = r` is `aux_lem_as_coarse_ms_chart_transport`; the proof is the same.) -/
theorem aux_lem_as_coarse_deep_grid_transport {d : ℕ} (Jc : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (w0 : SpatialCoordinates d) (r0 : ℝ) (hr0 : 0 < r0)
    (hw0 : (centeredCube w0 r0 hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (n : ℕ) {R : Homogenization.TriadicCube d}
    (hR : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (n : ℤ))) :
    coarseBMatrixNorm R (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) w0 r0) =
        coarseBMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (aux_lem_as_coarse_ms_cellCenter w0 r0 n R.index) (r0 * (3 : ℝ) ^ (-(n : ℤ)))) ∧
      coarseSigmaStarInvMatrixNorm R
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) w0 r0) =
        coarseSigmaStarInvMatrixNorm (Homogenization.originCube d 0)
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr)
            (aux_lem_as_coarse_ms_cellCenter w0 r0 n R.index) (r0 * (3 : ℝ) ^ (-(n : ℤ)))) := by
  set w := aux_lem_as_coarse_ms_cellCenter w0 r0 n R.index with hw
  set r' : ℝ := r0 * (3 : ℝ) ^ (-(n : ℤ)) with hr'def
  have hr' : 0 < r' := by positivity
  have hscale := aux_lem_as_coarse_ms_desc_scale hR
  have hsub := (aux_lem_as_coarse_ms_cell_sub w0 r0 hr0 n hR hr').trans hw0
  let F : SpatialCoordinates d → ℝ := cutoffCoefficient M H om N
  have hFc : Continuous F := cutoffCoefficient_continuous M H om N
  have hFpos : ∀ y, 0 < F y := fun y =>
    mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
  let f : C(Homogenization.Vec d, ℝ) :=
    ⟨fun y => F (fun i => w i + r' * y i), hFc.comp (by fun_prop)⟩
  have hf : ∀ y, 0 < f y := fun y => hFpos _
  let a0 := (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) w r').coeffOn
    (Homogenization.originCube d 0)
  have ha0 : ∀ᵐ x ∂Homogenization.volumeMeasureOn
      (Homogenization.openCubeSet (Homogenization.originCube d 0)),
      a0.toCoeffField x = Homogenization.scalarMatrix (f x) :=
    aux_lem_extension_cell_moment_chart_scalar_identity Jc M H om N z r hr w r' hr' hsub
      (Homogenization.originCube d 0) subset_rfl
  obtain ⟨aQ, haQ, _, hJ⟩ := aux_lem_extension_cell_moment_reference_on_cube R f hf a0 ha0
  have hroot := aux_lem_extension_cell_moment_chart_scalar_identity Jc M H om N z r hr w0 r0
    hr0 hw0 R (aux_lem_as_coarse_ms_desc_sub hR)
  have hAE : CoeffOn.AEEq
      ((Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) w0 r0).coeffOn R) aQ := by
    unfold CoeffOn.AEEq
    filter_upwards [hroot] with x hx
    rw [hx, haQ x]
    congr 1
    change F (fun i => w0 i + r0 * x i) =
      F (fun i => w i + r' * aux_lem_extension_cell_moment_cubeNormalize R x i)
    congr 1
    exact (aux_lem_as_coarse_ms_normalize_chart w0 r0 n hscale x).symm
  have hJall : ∀ p q, responseJ (cubeDomain R)
      ((Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) w0 r0).coeffOn R) p q =
      responseJ (cubeDomain (Homogenization.originCube d 0)) a0 p q := fun p q =>
    (responseJ_eq_ofAEEq hAE p q).trans (hJ p q)
  obtain ⟨hb, hs⟩ := aux_lem_as_coarse_ms_coarse_congr hJall
  exact ⟨by unfold coarseBMatrixNorm; rw [hb], by unfold coarseSigmaStarInvMatrixNorm; rw [hs]⟩

/-- `(3^{-k})^{-η} = 3^{η k}`. -/
theorem aux_lem_as_coarse_deep_grid_pow (k : ℕ) (eta : ℝ) :
    ((3 : ℝ) ^ (-(k : ℤ))) ^ (-eta) = (3 : ℝ) ^ (eta * (k : ℝ)) := by
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  push_cast
  ring

/-- **Deterministic deep-cell bound in the root chart.**  Let the root have side
`r = 3^n 3^{-m}` (`n = j⁺`, `m = j⁻`).  Suppose the grid clause of `lem_extension` holds at
all absolute depths `≤ N` (with bound `K 3^{η·depth}`).  Then every relative-depth-`k`
descendant, `m + n ≤ k ≤ N`, of the unit root in the root chart has both cell matrices at most
`3^{2 s₀ m} K 3^{η k}`.  The relative-depth-`k` cell sits at absolute depth `k + m - n`, which
can exceed `N` when `m > 0`; it is therefore read inside its ancestor at absolute depth
`k - n ≤ N` (relative depth `k - m`) and bounded by the descendant localization of `Λ_{s₀,2}`
and `λ_{s₀,2}` over the `m` extra generations. -/
theorem aux_lem_as_coarse_deep_grid_cell {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (m n : ℕ)
    (hrmn : r = (3 : ℝ) ^ (n : ℤ) * (3 : ℝ) ^ (-(m : ℤ)))
    (s0 : ℝ) (hs0 : s0 ∈ Set.Ioc (0 : ℝ) 1) (eta KN : ℝ) (heta : 0 ≤ eta)
    (hgrid : ∀ (k : ℕ) (nidx : Fin d → ℤ), k ≤ N →
      (centeredCube (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
          ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z r hr) →
      Jc.Lam z r hr (cutoffPositiveCoefficient M H om N z hr)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ))) s0 2 +
        (Jc.lam z r hr (cutoffPositiveCoefficient M H om N z hr)
          (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
            s0 2)⁻¹ ≤
        KN * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-eta))
    (k : ℕ) (hmnk : m + n ≤ k) (hkN : k ≤ N)
    {R : Homogenization.TriadicCube d}
    (hR : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (k : ℤ))) :
    0 ≤ KN ∧
    coarseBMatrixNorm R (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) ≤
        (3 : ℝ) ^ (2 * s0 * (m : ℝ)) * (KN * (3 : ℝ) ^ (eta * (k : ℝ))) ∧
      coarseSigmaStarInvMatrixNorm R
          (Jc.chart z r hr (cutoffPositiveCoefficient M H om N z hr) z r) ≤
        (3 : ℝ) ^ (2 * s0 * (m : ℝ)) * (KN * (3 : ℝ) ^ (eta * (k : ℝ))) := by
  have : NeZero d := ⟨by omega⟩
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  obtain ⟨P, hP, R', hR', hidx⟩ :=
    aux_lem_as_coarse_deep_grid_ancestor (k := k) (m := m) (by omega) hR
  set a : ℕ := k - m with ha
  set kabs : ℕ := k - n with hkabs
  set A := cutoffPositiveCoefficient M H om N z hr with hA
  -- the ancestor cell is the grid cell of absolute depth `kabs` with index `P.index`
  have htP : r * (3 : ℝ) ^ (-(a : ℤ)) = (3 : ℝ) ^ (-(kabs : ℤ)) := by
    rw [hrmn, ← zpow_add₀ h3, ← zpow_add₀ h3]
    congr 1
    omega
  set wg : SpatialCoordinates d :=
    fun i => z i + (3 : ℝ) ^ (-(kabs : ℤ)) * (P.index i : ℝ) with hwg
  set tg : ℝ := (3 : ℝ) ^ (-(kabs : ℤ)) with htg
  have htg0 : 0 < tg := by positivity
  have hcP : aux_lem_as_coarse_ms_cellCenter z r a P.index = wg := by
    funext i
    simp only [aux_lem_as_coarse_ms_cellCenter, hwg]
    rw [htP]
  have htP0 : 0 < r * (3 : ℝ) ^ (-(a : ℤ)) := by positivity
  have hPsub0 := aux_lem_as_coarse_ms_cell_sub z r hr a hP htP0
  have hPsub : (centeredCube wg tg htg0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    rw [aux_lem_as_coarse_deep_grid_cube_congr htg0 htP0 hcP.symm htP.symm]
    exact hPsub0
  have hg := hgrid kabs P.index (by omega) hPsub
  -- positivity of the bound
  have hLpos := Jc.Lam_pos z r hr A wg tg s0 2
  have hlpos := Jc.lam_pos z r hr A wg tg s0 2
  have hpow := aux_lem_as_coarse_deep_grid_pow kabs eta
  rw [hpow] at hg
  have hKN : 0 ≤ KN := by
    have h1 : 0 < KN * (3 : ℝ) ^ (eta * (kabs : ℝ)) :=
      lt_of_lt_of_le (add_pos hLpos (inv_pos.2 hlpos)) hg
    have h2 : 0 < (3 : ℝ) ^ (eta * (kabs : ℝ)) := by positivity
    exact (pos_of_mul_pos_left h1 h2.le).le
  have hmono : KN * (3 : ℝ) ^ (eta * (kabs : ℝ)) ≤ KN * (3 : ℝ) ^ (eta * (k : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ hKN
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply mul_le_mul_of_nonneg_left _ heta
    exact_mod_cast (Nat.sub_le k n)
  -- Λ, λ of the ancestor chart are the Ch02 discounted sums
  have hq : (1 : ℝ) ≤ (2 : ℝ≥0∞).toReal := by norm_num
  have hLeq := Jc.Lam_eq z r hr A wg tg htg0 hPsub s0 hs0 2 (by norm_num)
  have hleq := Jc.lam_eq z r hr A wg tg htg0 hPsub s0 hs0 2 (by norm_num)
  rw [ite_eq_right (by norm_num)] at hLeq hleq
  -- descendant localization over `m` generations
  have hW : multiscaleDescendantWeight (Homogenization.originCube d 0)
      ((Homogenization.originCube d 0).scale - (m : ℤ)) s0 = (3 : ℝ) ^ (2 * s0 * (m : ℝ)) := by
    unfold multiscaleDescendantWeight
    simp only [sub_sub_cancel, Int.cast_natCast]
    rfl
  have hWnn : 0 ≤ (3 : ℝ) ^ (2 * s0 * (m : ℝ)) := by positivity
  have hbR' := oneCube_b_le_LambdaSq_finite R' (Jc.chart z r hr A wg tg) hs0.1 hq
  have hdR' := descendant_LambdaSq_finite_le (Jc.chart z r hr A wg tg) hR' hs0.1 hq
  have hsR' := oneCube_sigmaStarInv_le_lambdaSq_finite_inv R' (Jc.chart z r hr A wg tg) hs0.1 hq
  have hdsR' := descendant_lambdaSq_finite_inv_le (Jc.chart z r hr A wg tg) hR' hs0.1 hq
  rw [hW, ← hLeq] at hdR'
  rw [hW, ← hleq] at hdsR'
  -- transport both readings to the unit root of the same physical cell
  obtain ⟨hT1b, hT1s⟩ := aux_lem_as_coarse_deep_grid_transport Jc M H om N z r hr z r hr
    subset_rfl k hR
  obtain ⟨hT2b, hT2s⟩ := aux_lem_as_coarse_deep_grid_transport Jc M H om N z r hr wg tg htg0
    hPsub m hR'
  have e1 : (3 : ℝ) ^ (n : ℤ) * (3 : ℝ) ^ (-(m : ℤ)) * (3 : ℝ) ^ (-(k : ℤ)) =
      (3 : ℝ) ^ (-(kabs : ℤ)) * (3 : ℝ) ^ (-(m : ℤ)) := by
    rw [← zpow_add₀ h3, ← zpow_add₀ h3, ← zpow_add₀ h3]
    congr 1
    omega
  have e2 : (3 : ℝ) ^ (n : ℤ) * (3 : ℝ) ^ (-(m : ℤ)) * (3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ m =
      (3 : ℝ) ^ (-(kabs : ℤ)) := by
    rw [← zpow_natCast, ← zpow_add₀ h3, ← zpow_add₀ h3, ← zpow_add₀ h3]
    congr 1
    omega
  have hside : r * (3 : ℝ) ^ (-(k : ℤ)) = tg * (3 : ℝ) ^ (-(m : ℤ)) := by
    rw [hrmn, e1]
  have hcent : aux_lem_as_coarse_ms_cellCenter z r k R.index =
      aux_lem_as_coarse_ms_cellCenter wg tg m R'.index := by
    funext i
    have hi : ((R.index i : ℤ) : ℝ) = (3 : ℝ) ^ m * (P.index i : ℝ) + (R'.index i : ℝ) := by
      have := congrArg (fun t : ℤ => (t : ℝ)) (hidx i)
      push_cast at this
      exact this
    simp only [aux_lem_as_coarse_ms_cellCenter, hwg, htg]
    rw [hi, hrmn]
    linear_combination (P.index i : ℝ) * e2 + (R'.index i : ℝ) * e1
  rw [hcent, hside] at hT1b hT1s
  rw [← hT2b] at hT1b
  rw [← hT2s] at hT1s
  refine ⟨hKN, ?_, ?_⟩
  · rw [hT1b]
    calc coarseBMatrixNorm R' (Jc.chart z r hr A wg tg)
        ≤ (3 : ℝ) ^ (2 * s0 * (m : ℝ)) * Jc.Lam z r hr A wg tg s0 2 := hbR'.trans hdR'
      _ ≤ (3 : ℝ) ^ (2 * s0 * (m : ℝ)) * (KN * (3 : ℝ) ^ (eta * (k : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hWnn
          have := (inv_pos.2 hlpos).le
          linarith
  · rw [hT1s]
    calc coarseSigmaStarInvMatrixNorm R' (Jc.chart z r hr A wg tg)
        ≤ (3 : ℝ) ^ (2 * s0 * (m : ℝ)) * (Jc.lam z r hr A wg tg s0 2)⁻¹ := hsR'.trans hdsR'
      _ ≤ (3 : ℝ) ^ (2 * s0 * (m : ℝ)) * (KN * (3 : ℝ) ^ (eta * (k : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hWnn
          linarith

/-- `|e^t - 1| ≤ e^{|t|}`. -/
theorem aux_lem_as_coarse_deep_grid_abs_exp_sub_one (t : ℝ) :
    |Real.exp t - 1| ≤ Real.exp |t| := by
  rcases le_total 0 t with ht | ht
  · have h1 := Real.add_one_le_exp t
    rw [abs_of_nonneg (by linarith), abs_of_nonneg ht]
    linarith
  · have h1 : Real.exp t ≤ 1 := Real.exp_le_one_iff.2 ht
    have h2 := Real.exp_pos t
    have h3 := Real.one_le_exp (abs_nonneg t)
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- A pointwise ratio bound on a cube bounds the paper's `L^∞` ratio error. -/
theorem aux_lem_as_coarse_deep_grid_ratio_le {d : ℕ} (R : Homogenization.TriadicCube d)
    (a b : Homogenization.Vec d → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ Homogenization.openCubeSet R, |a x / b x - 1| ≤ c) :
    SubdiffusiveProcess.CoarseGrainingVocab.scalarRatioLInf (cubeDomain R) a b ≤ c := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.scalarRatioLInf
  apply ENNReal.toReal_le_of_le_ofReal hc
  rw [SubdiffusiveProcess.RawLp.eLpNorm_top_exponent]
  apply eLpNormEssSup_le_of_ae_bound
  exact ae_restrict_of_forall_mem (Homogenization.measurableSet_openCubeSet R)
    fun x hx => by simpa [Real.norm_eq_abs] using h x hx

/-- The two quadratic slices of the symmetric response functional. -/
theorem aux_lem_as_coarse_deep_grid_J_slices {d : ℕ} (Jc : in_J d) (U : Domain d)
    (a : CoeffOn U) (hs : CoeffOn.IsSymmetric a) (p : Homogenization.Vec d) :
    responseJ U a p 0 =
        (1 / 2 : ℝ) * Homogenization.vecDot p (Homogenization.matVecMul (sigmaCoarse U a) p) ∧
      responseJ U a 0 p = (1 / 2 : ℝ) *
        Homogenization.vecDot p (Homogenization.matVecMul (sigmaStarInvCoarse U a) p) := by
  constructor
  · rw [Jc.responseJ_split U a hs p 0]
    simp [Homogenization.vecDot, Homogenization.matVecMul]
  · rw [Jc.responseJ_split U a hs 0 p]
    simp [Homogenization.vecDot, Homogenization.matVecMul]

/-- **Removing the infrared field** costs one common bounded factor.  On a root where
`|H| ≤ h`, the cell matrices of the infrared-removed cutoff coefficient `A_N^0 = e^{-H} A_N`
are at most `2 + 6 e^{2h}` times those of `A_N`, on every triadic cell of the root chart.
This is the scalar sensitivity estimate `responseJ_sensitivity` at scale ratio `1`. -/
theorem aux_lem_as_coarse_deep_grid_ir_compare {d : ℕ} (hd : 2 ≤ d) (Jc : in_J d)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (h : ℝ)
    (hh : ∀ y ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), |Hir om y| ≤ h)
    (R : Homogenization.TriadicCube d)
    (hR : Homogenization.openCubeSet R ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    coarseBMatrixNorm R (Jc.chart z r hr (cutoffPositiveCoefficient M
        (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N z hr) z r) ≤
      (2 + 6 * Real.exp (2 * h)) *
        coarseBMatrixNorm R (Jc.chart z r hr (cutoffPositiveCoefficient M Hir om N z hr) z r) ∧
    coarseSigmaStarInvMatrixNorm R (Jc.chart z r hr (cutoffPositiveCoefficient M
        (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N z hr) z r) ≤
      (2 + 6 * Real.exp (2 * h)) *
        coarseSigmaStarInvMatrixNorm R
          (Jc.chart z r hr (cutoffPositiveCoefficient M Hir om N z hr) z r) := by
  have : NeZero d := ⟨by omega⟩
  set H0 : BilateralField d → C(SpatialCoordinates d, ℝ) :=
    fun _ => (0 : C(SpatialCoordinates d, ℝ)) with hH0
  set U : Domain d := cubeDomain R with hU
  let F1 : Homogenization.Vec d → ℝ :=
    fun x => cutoffCoefficient M Hir om N (fun i => z i + r * x i)
  let F0 : Homogenization.Vec d → ℝ :=
    fun x => cutoffCoefficient M H0 om N (fun i => z i + r * x i)
  have hF1c : Continuous F1 := (cutoffCoefficient_continuous M Hir om N).comp (by fun_prop)
  have hF0c : Continuous F0 := (cutoffCoefficient_continuous M H0 om N).comp (by fun_prop)
  have hF1p : ∀ x, 0 < F1 x := fun x =>
    mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
  have hF0p : ∀ x, 0 < F0 x := fun x =>
    mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
  let da := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos hF1c hF1p U
  let db := SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.scalarCoeffOnDataOfContinuousPos hF0c hF0p U
  have hae1 : CoeffOn.AEEq
      ((Jc.chart z r hr (cutoffPositiveCoefficient M Hir om N z hr) z r).coeffOn R)
      da.toCoeffOn := by
    have hid := aux_lem_extension_cell_moment_chart_scalar_identity Jc M Hir om N z r hr z r hr
      subset_rfl R hR
    unfold CoeffOn.AEEq
    filter_upwards [hid] with x hx
    rw [hx]
    rfl
  have hae0 : CoeffOn.AEEq
      ((Jc.chart z r hr (cutoffPositiveCoefficient M H0 om N z hr) z r).coeffOn R)
      db.toCoeffOn := by
    have hid := aux_lem_extension_cell_moment_chart_scalar_identity Jc M H0 om N z r hr z r hr
      subset_rfl R hR
    unfold CoeffOn.AEEq
    filter_upwards [hid] with x hx
    rw [hx]
    rfl
  -- the ratio of the two scalar fields is `e^{±H}`
  have hquot : ∀ x, F1 x / F0 x = Real.exp (Hir om (fun i => z i + r * x i)) := by
    intro x
    simp only [F1, F0, cutoffCoefficient, cutoffPotential, H0, ContinuousMap.zero_apply,
      zero_add]
    rw [mul_div_mul_left _ _ (inv_ne_zero (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne'),
      ← Real.exp_sub]
    congr 1
    ring
  have hquot' : ∀ x, F0 x / F1 x = Real.exp (-(Hir om (fun i => z i + r * x i))) := by
    intro x
    rw [Real.exp_neg, ← hquot x, inv_div]
  have hmem : ∀ x ∈ Homogenization.openCubeSet R,
      |Hir om (fun i => z i + r * x i)| ≤ h := fun x hx =>
    hh _ (aux_lem_as_coarse_ms_affine_mem z r hr (hR hx))
  have hε1 : SubdiffusiveProcess.CoarseGrainingVocab.scalarRatioLInf U F1 F0 ≤ Real.exp h := by
    apply aux_lem_as_coarse_deep_grid_ratio_le R _ _ (Real.exp_pos h).le
    intro x hx
    rw [hquot x]
    exact (aux_lem_as_coarse_deep_grid_abs_exp_sub_one _).trans
      (Real.exp_le_exp.2 (hmem x hx))
  have hε2 : SubdiffusiveProcess.CoarseGrainingVocab.scalarRatioLInf U F0 F1 ≤ Real.exp h := by
    apply aux_lem_as_coarse_deep_grid_ratio_le R _ _ (Real.exp_pos h).le
    intro x hx
    rw [hquot' x]
    exact (aux_lem_as_coarse_deep_grid_abs_exp_sub_one _).trans
      (Real.exp_le_exp.2 (by rw [abs_neg]; exact hmem x hx))
  set E : ℝ := SubdiffusiveProcess.CoarseGrainingVocab.scalarRatioLInf U F1 F0 ^ 2 +
      SubdiffusiveProcess.CoarseGrainingVocab.scalarRatioLInf U F0 F1 ^ 2 with hE
  have hE0 : 0 ≤ E := by positivity
  have hEh : 3 * E ≤ 6 * Real.exp (2 * h) := by
    have hsq : Real.exp h ^ 2 = Real.exp (2 * h) := by
      rw [sq, ← Real.exp_add]; ring_nf
    have h1 := pow_le_pow_left₀ (SubdiffusiveProcess.CoarseGrainingVocab.scalarRatioLInf_nonneg _ _ _) hε1 2
    have h2 := pow_le_pow_left₀ (SubdiffusiveProcess.CoarseGrainingVocab.scalarRatioLInf_nonneg _ _ _) hε2 2
    rw [hsq] at h1 h2
    linarith
  have hsens : ∀ p q : Homogenization.Vec d,
      responseJ U db.toCoeffOn p q ≤ (1 + 1) * responseJ U da.toCoeffOn p q +
        3 * E * (responseJ U da.toCoeffOn p q + Homogenization.vecDot p q) := by
    intro p q
    have := SubdiffusiveProcess.CoarseGrainingVocab.responseJ_sensitivity da db (lambda := 1) (delta := 1)
      one_pos one_pos le_rfl p q
    simpa [Real.sqrt_one, SubdiffusiveProcess.CoarseGrainingVocab.J] using this
  have hTa := responseSymmetricDirichletNeumannTheory U da.toCoeffOn da.isSymmetric
  have hTb := responseSymmetricDirichletNeumannTheory U db.toCoeffOn db.isSymmetric
  have hC3 : 2 + 3 * E ≤ 2 + 6 * Real.exp (2 * h) := by linarith
  have hC30 : 0 ≤ 2 + 3 * E := by linarith
  constructor
  · unfold coarseBMatrixNorm
    rw [bCoarse_eq_ofAEEq hae0, bCoarse_eq_ofAEEq hae1]
    refine SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.matrixNorm_le_of_forall_unit
      (bCoarse_posSemidef U db.toCoeffOn) (mul_nonneg (by positivity) (norm_nonneg _)) ?_
    intro e he
    rw [hTb.derived_matrices.2.2, hTa.derived_matrices.2.2]
    have hnn : 0 ≤ matrixNorm (sigmaCoarse U da.toCoeffOn) := norm_nonneg _
    have hJb := (aux_lem_as_coarse_deep_grid_J_slices Jc U db.toCoeffOn db.isSymmetric e).1
    have hJa := (aux_lem_as_coarse_deep_grid_J_slices Jc U da.toCoeffOn da.isSymmetric e).1
    have hs := hsens e 0
    have hv0 : Homogenization.vecDot e 0 = 0 := by simp [Homogenization.vecDot]
    rw [hv0, add_zero, hJa, hJb] at hs
    have hA := Homogenization.Book.Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq
      (sigmaCoarse U da.toCoeffOn) e
    rw [← Homogenization.Book.Ch02.matrixNorm_eq_matrixOperatorNorm, he, mul_one] at hA
    have hA' := (abs_le.mp hA).2
    calc Homogenization.vecDot e (Homogenization.matVecMul (sigmaCoarse U db.toCoeffOn) e)
        ≤ (2 + 3 * E) *
            Homogenization.vecDot e (Homogenization.matVecMul (sigmaCoarse U da.toCoeffOn) e) := by
          linarith
      _ ≤ (2 + 3 * E) * matrixNorm (sigmaCoarse U da.toCoeffOn) :=
          mul_le_mul_of_nonneg_left hA' hC30
      _ ≤ (2 + 6 * Real.exp (2 * h)) * matrixNorm (sigmaCoarse U da.toCoeffOn) :=
          mul_le_mul_of_nonneg_right hC3 hnn
  · unfold coarseSigmaStarInvMatrixNorm
    rw [sigmaStarInvCoarse_eq_ofAEEq hae0, sigmaStarInvCoarse_eq_ofAEEq hae1]
    have hnn : 0 ≤ matrixNorm (sigmaStarInvCoarse U da.toCoeffOn) := norm_nonneg _
    refine SubdiffusiveProcess.CoarseGrainingVocab.Section4Recursion.ErrorComparison.matrixNorm_le_of_forall_unit
      (sigmaStarInvCoarse_posDef U db.toCoeffOn).posSemidef
      (mul_nonneg (by positivity) hnn) ?_
    intro e he
    have hJb := (aux_lem_as_coarse_deep_grid_J_slices Jc U db.toCoeffOn db.isSymmetric e).2
    have hJa := (aux_lem_as_coarse_deep_grid_J_slices Jc U da.toCoeffOn da.isSymmetric e).2
    have hs := hsens 0 e
    have hv0 : Homogenization.vecDot 0 e = 0 := by simp [Homogenization.vecDot]
    rw [hv0, add_zero, hJa, hJb] at hs
    have hA := Homogenization.Book.Ch02.abs_vecDot_matVecMul_le_matrixOperatorNorm_mul_vecNormSq
      (sigmaStarInvCoarse U da.toCoeffOn) e
    rw [← Homogenization.Book.Ch02.matrixNorm_eq_matrixOperatorNorm, he, mul_one] at hA
    have hA' := (abs_le.mp hA).2
    calc Homogenization.vecDot e
          (Homogenization.matVecMul (sigmaStarInvCoarse U db.toCoeffOn) e)
        ≤ (2 + 3 * E) * Homogenization.vecDot e
            (Homogenization.matVecMul (sigmaStarInvCoarse U da.toCoeffOn) e) := by
          linarith
      _ ≤ (2 + 3 * E) * matrixNorm (sigmaStarInvCoarse U da.toCoeffOn) :=
          mul_le_mul_of_nonneg_left hA' hC30
      _ ≤ (2 + 6 * Real.exp (2 * h)) * matrixNorm (sigmaStarInvCoarse U da.toCoeffOn) :=
          mul_le_mul_of_nonneg_right hC3 hnn

end DeepGridHelpers

/-- The deep-grid estimate in the proof of the pathwise coarse bounds.
The disorder threshold precedes the model, and the bound concerns the cell
matrices in the root chart. The extension grid clause is the proof supplier. -/
theorem lem_as_coarse_deep_grid
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d)
    (Xc : in_extension d hd Jc)
    (Sf : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd)
    (s beta rho theta xi : ℝ)
    (_hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1)
    (hrho : 0 < rho) (_hrhos : rho < s / 4)
    (htheta : 0 < theta) (htheta1 : theta < 1)
    (hxi : 0 < xi) (_hxi_tail : xi < (s - rho) * theta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (_Rm : in_responses d M)
      (Hir : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M Hir →
      M.delta ≤ min 1 delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      (∃ j : ℤ, r = (3 : ℝ) ^ j) →
      ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∃ K_N : ℕ → ℝ, (∀ N, 0 < K_N N) ∧
        ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
          (K_N N ≤ (3 : ℝ) ^ (xi * (N : ℝ)) ∧
          ∀ withIR : Bool,
            let Hc : BilateralField d → C(SpatialCoordinates d, ℝ) :=
              if withIR then Hir else fun _ => (0 : C(SpatialCoordinates d, ℝ))
            ∀ k : ℕ, (theta * (N : ℝ) < (k : ℝ)) ∧ k ≤ N →
              Homogenization.Book.Ch02.maxDescendantBMatrixNormAtScale
                  (Homogenization.originCube d 0) (-(k : ℤ))
                  (Jc.chart z r hr
                    (cutoffPositiveCoefficient M Hc ω N z hr) z r) +
                Homogenization.Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
                  (Homogenization.originCube d 0) (-(k : ℤ))
                  (Jc.chart z r hr
                    (cutoffPositiveCoefficient M Hc ω N z hr) z r) ≤
                K_N N * (3 : ℝ) ^ (rho * (k : ℝ))) := by
  have : NeZero d := ⟨by omega⟩
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  -- the extension order `s₀ = (β - 1/2)/4` and the grid clause at `η = ρ`, `p = 1`;
  -- its disorder threshold is fixed here, before the model
  have hs0 : (beta - 1 / 2) / 4 ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor <;> linarith [hbeta.1, hbeta.2]
  obtain ⟨delta0, hdelta0, hgridAll⟩ :=
    (lem_extension d hd Jc Xc Sf).2 rho 1 hrho le_rfl beta hbeta
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Hir hIR hdelta z r hr hj
  obtain ⟨j, hrj⟩ := hj
  set m : ℕ := Int.toNat (-j) with hm
  set n : ℕ := Int.toNat j with hn
  have hrmn : r = (3 : ℝ) ^ (n : ℤ) * (3 : ℝ) ^ (-(m : ℤ)) := by
    rw [hrj, ← zpow_add₀ h3]
    congr 1
    omega
  set μ := (chaosSampleLaw M).toMeasure with hμ
  obtain ⟨K, Cb, hLp, hBd, hae⟩ :=
    hgridAll M Rm Hir hIR (hdelta.trans (min_le_right _ _)) z r hr 1 (fun _ => z)
  -- a measurable version of the grid constants, and Borel--Cantelli at rate `ξ/2`
  let Kg : ℕ → BilateralField d → ℝ := fun N => (hLp N).aestronglyMeasurable.mk (K N)
  have hKg_meas : ∀ N, Measurable (Kg N) := fun N =>
    (hLp N).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hKg_ae : ∀ N, K N =ᵐ[μ] Kg N := fun N => (hLp N).aestronglyMeasurable.ae_eq_mk
  have hKgLp : ∀ N, MemLp (Kg N) (ENNReal.ofReal 1) μ := fun N => (hLp N).ae_eq (hKg_ae N)
  have hKgBd : ∀ N, eLpNorm (Kg N) (ENNReal.ofReal 1) μ ≤ ENNReal.ofReal (max Cb 0) := by
    intro N
    rw [← eLpNorm_congr_ae (hKg_ae N)]
    exact (hBd N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hBC := aux_lem_as_coarse_deep_grid_uniform_lp_eventually μ Kg hKg_meas 1 (max Cb 0)
    (xi / 2) le_rfl (le_max_right _ _) (by linarith) hKgLp hKgBd
  have hKeq : ∀ᵐ ω ∂μ, ∀ N, K N ω = Kg N ω := ae_all_iff.2 hKg_ae
  filter_upwards [hae, hBC, hKeq] with ω hω hBCω hKeqω
  -- the infrared field is bounded on the root (continuous on the compact closed cube)
  obtain ⟨h, hh⟩ : ∃ h : ℝ, ∀ y ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      |Hir ω y| ≤ h := by
    obtain ⟨C, hC⟩ := (closedCube z r hr).isCompact.exists_bound_of_continuousOn
      (Hir ω).continuous.continuousOn
    exact ⟨C, fun y hy => by
      simpa [Real.norm_eq_abs] using hC y (centeredCube_subset_closedCube z hr hy)⟩
  set Ccmp : ℝ := 2 + 6 * Real.exp (2 * h) with hCcmp
  have hCcmp1 : 1 ≤ Ccmp := by
    have := Real.exp_pos (2 * h)
    linarith
  set W : ℝ := (3 : ℝ) ^ (2 * ((beta - 1 / 2) / 4) * (m : ℝ)) with hW
  have hW0 : 0 ≤ W := by positivity
  set C0 : ℝ := 2 * Ccmp * W with hC0
  have hC00 : 0 ≤ C0 := by positivity
  refine ⟨fun N => max 1 (C0 * Kg N ω), fun N => lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  -- eventual thresholds
  have hE1 : ∀ᶠ N : ℕ in Filter.atTop, ((m + n : ℕ) : ℝ) ≤ theta * (N : ℝ) :=
    (Filter.Tendsto.const_mul_atTop htheta tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hE2 : ∀ᶠ N : ℕ in Filter.atTop, Kg N ω ≤ (3 : ℝ) ^ (xi / 2 * (N : ℝ)) := by
    obtain ⟨N₀, hN₀⟩ := hBCω
    exact Filter.eventually_atTop.2 ⟨N₀, hN₀⟩
  have hE3 := aux_lem_as_coarse_ms_eventually_rpow_ge (c := xi / 2) (by linarith) C0
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 (hE1.and (hE2.and hE3))
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨hN1, hN2, hN3⟩ := hN0 N hN
  refine ⟨?_, ?_⟩
  · apply max_le
    · exact Real.one_le_rpow (by norm_num) (by positivity)
    · calc C0 * Kg N ω ≤ C0 * (3 : ℝ) ^ (xi / 2 * (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hN2 hC00
        _ ≤ (3 : ℝ) ^ (xi / 2 * (N : ℝ)) * (3 : ℝ) ^ (xi / 2 * (N : ℝ)) :=
            mul_le_mul_of_nonneg_right hN3 (by positivity)
        _ = (3 : ℝ) ^ (xi * (N : ℝ)) := by
            rw [← Real.rpow_add (by norm_num)]
            ring_nf
  · -- the grid clause at this sample and cutoff, in the form used by the cell lemma
    have hgrid : ∀ (k : ℕ) (nidx : Fin d → ℤ), k ≤ N →
        (centeredCube (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ))
            ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z r hr) →
        Jc.Lam z r hr (cutoffPositiveCoefficient M Hir ω N z hr)
            (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
            ((beta - 1 / 2) / 4) 2 +
          (Jc.lam z r hr (cutoffPositiveCoefficient M Hir ω N z hr)
            (fun i => z i + (3 : ℝ) ^ (-(k : ℤ)) * (nidx i : ℝ)) ((3 : ℝ) ^ (-(k : ℤ)))
              ((beta - 1 / 2) / 4) 2)⁻¹ ≤
          K N ω * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-rho) :=
      fun k nidx hk hsub => hω N k 0 nidx hk hsub
    have hcell : ∀ k : ℕ, theta * (N : ℝ) < (k : ℝ) → k ≤ N →
        ∀ R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) (-(k : ℤ)),
        0 ≤ Kg N ω ∧
        Homogenization.Book.Ch02.coarseBMatrixNorm R
            (Jc.chart z r hr (cutoffPositiveCoefficient M Hir ω N z hr) z r) ≤
          W * (Kg N ω * (3 : ℝ) ^ (rho * (k : ℝ))) ∧
        Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
            (Jc.chart z r hr (cutoffPositiveCoefficient M Hir ω N z hr) z r) ≤
          W * (Kg N ω * (3 : ℝ) ^ (rho * (k : ℝ))) ∧
        Homogenization.Book.Ch02.coarseBMatrixNorm R
            (Jc.chart z r hr (cutoffPositiveCoefficient M
              (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr) z r) ≤
          Ccmp * (W * (Kg N ω * (3 : ℝ) ^ (rho * (k : ℝ)))) ∧
        Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
            (Jc.chart z r hr (cutoffPositiveCoefficient M
              (fun _ => (0 : C(SpatialCoordinates d, ℝ))) ω N z hr) z r) ≤
          Ccmp * (W * (Kg N ω * (3 : ℝ) ^ (rho * (k : ℝ)))) := by
      intro k hk1 hk2 R hR
      have hR' : R ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0)
          ((Homogenization.originCube d 0).scale - (k : ℤ)) := by
        simpa [Homogenization.originCube] using hR
      have hmnk : m + n ≤ k := by
        have : ((m + n : ℕ) : ℝ) < (k : ℝ) := lt_of_le_of_lt hN1 hk1
        exact_mod_cast this.le
      obtain ⟨hK0, hb, hs⟩ := aux_lem_as_coarse_deep_grid_cell hd Jc M Hir ω N z r hr m n hrmn
        _ hs0 rho (K N ω) hrho.le hgrid k hmnk hk2 hR'
      rw [hKeqω N] at hK0 hb hs
      obtain ⟨hcb, hcs⟩ := aux_lem_as_coarse_deep_grid_ir_compare hd Jc M Hir ω N z r hr h hh R
        (aux_lem_as_coarse_ms_desc_sub hR')
      have hnb : 0 ≤ Homogenization.Book.Ch02.coarseBMatrixNorm R
          (Jc.chart z r hr (cutoffPositiveCoefficient M Hir ω N z hr) z r) := norm_nonneg _
      have hns : 0 ≤ Homogenization.Book.Ch02.coarseSigmaStarInvMatrixNorm R
          (Jc.chart z r hr (cutoffPositiveCoefficient M Hir ω N z hr) z r) := norm_nonneg _
      refine ⟨hK0, hb, hs, hcb.trans (mul_le_mul_of_nonneg_left hb (by positivity)),
        hcs.trans (mul_le_mul_of_nonneg_left hs (by positivity))⟩
    -- assemble the two maxima into `K_N 3^{ρk}`
    have hfinal : ∀ k : ℕ, theta * (N : ℝ) < (k : ℝ) → k ≤ N → ∀ X Y : ℝ,
        X ≤ Ccmp * (W * (Kg N ω * (3 : ℝ) ^ (rho * (k : ℝ)))) →
        Y ≤ Ccmp * (W * (Kg N ω * (3 : ℝ) ^ (rho * (k : ℝ)))) →
        X + Y ≤ max 1 (C0 * Kg N ω) * (3 : ℝ) ^ (rho * (k : ℝ)) := by
      intro k hk1 hk2 X Y hX hY
      obtain ⟨R0, hR0⟩ := Homogenization.descendantsAtScale_nonempty
        (Homogenization.originCube d 0) (k := -(k : ℤ)) (by simp [Homogenization.originCube])
      have hK0 := (hcell k hk1 hk2 R0 hR0).1
      have hpk : 0 < (3 : ℝ) ^ (rho * (k : ℝ)) := by positivity
      calc X + Y ≤ C0 * Kg N ω * (3 : ℝ) ^ (rho * (k : ℝ)) := by
            rw [hC0]
            nlinarith
        _ ≤ max 1 (C0 * Kg N ω) * (3 : ℝ) ^ (rho * (k : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hpk.le
    have hBnd : ∀ k : ℕ, theta * (N : ℝ) < (k : ℝ) → k ≤ N → 0 ≤ Kg N ω := by
      intro k hk1 hk2
      obtain ⟨R0, hR0⟩ := Homogenization.descendantsAtScale_nonempty
        (Homogenization.originCube d 0) (k := -(k : ℤ)) (by simp [Homogenization.originCube])
      exact (hcell k hk1 hk2 R0 hR0).1
    intro withIR
    cases withIR with
    | false =>
      intro Hc k hk
      obtain ⟨hk1, hk2⟩ := hk
      have hK0 := hBnd k hk1 hk2
      have hB0 : 0 ≤ Ccmp * (W * (Kg N ω * (3 : ℝ) ^ (rho * (k : ℝ)))) := by positivity
      apply hfinal k hk1 hk2
      · exact aux_lem_as_coarse_deep_grid_finsetSup_le _ _ hB0
          fun R hR => (hcell k hk1 hk2 R hR).2.2.2.1
      · exact aux_lem_as_coarse_deep_grid_finsetSup_le _ _ hB0
          fun R hR => (hcell k hk1 hk2 R hR).2.2.2.2
    | true =>
      intro Hc k hk
      obtain ⟨hk1, hk2⟩ := hk
      have hK0 := hBnd k hk1 hk2
      have hB0 : 0 ≤ W * (Kg N ω * (3 : ℝ) ^ (rho * (k : ℝ))) := by positivity
      have hup : W * (Kg N ω * (3 : ℝ) ^ (rho * (k : ℝ))) ≤
          Ccmp * (W * (Kg N ω * (3 : ℝ) ^ (rho * (k : ℝ)))) :=
        le_mul_of_one_le_left hB0 hCcmp1
      apply hfinal k hk1 hk2
      · exact (aux_lem_as_coarse_deep_grid_finsetSup_le _ _ hB0
          fun R hR => (hcell k hk1 hk2 R hR).2.1).trans hup
      · exact (aux_lem_as_coarse_deep_grid_finsetSup_le _ _ hB0
          fun R hR => (hcell k hk1 hk2 R hR).2.2.1).trans hup

end SubdiffusiveProcess.Paper
