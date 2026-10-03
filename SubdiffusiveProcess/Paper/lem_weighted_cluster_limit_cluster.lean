module

public import SubdiffusiveProcess.Paper.lem_weighted_cluster_form_bounds
public import SubdiffusiveProcess.Paper.lem_weighted_cluster_inverse_bounds
public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.lem_19
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.weighted_killed_form
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane2.NativeBridge
public import SubdiffusiveProcess.Lane2.ResponseMarkov
public import SubdiffusiveProcess.Lane4.Carriers
public import Mathlib.LinearAlgebra.Countable

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace Paper

lemma aux_lem_weighted_cluster_limit_cluster_countable_subseq
    {κ : Type} [Countable κ] (K : κ → Set ℝ)
    (hK : ∀ k, IsCompact (K k)) (u : κ → ℕ → ℝ)
    (hu : ∀ k n, u k n ∈ K k) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ k, ∃ x, Tendsto (fun n => u k (σ n)) atTop (𝓝 x) := by
  classical
  letI : ∀ k, CompactSpace (K k) := fun k =>
    isCompact_iff_compactSpace.mp (hK k)
  let v : ℕ → ∀ k, K k := fun n k => ⟨u k n, hu k n⟩
  obtain ⟨x, σ, hσ, hx⟩ := CompactSpace.tendsto_subseq v
  refine ⟨σ, hσ, fun k => ⟨x k, ?_⟩⟩
  have hcont : Continuous (fun p : (∀ k, K k) => (p k : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply k)
  have h := hcont.tendsto (x) |>.comp hx
  exact h

lemma aux_lem_weighted_cluster_limit_cluster_collective_compact
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (arho : ℕ → PositiveCoefficient (centeredCube z r hr))
    (T : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ]
      DomainL2 (centeredCube z r hr))
    (hT : ∀ n f, T n f =
      (responseSolution S (arho n)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (Kstar : ℝ) (hKstar : 0 ≤ Kstar) (lo : ℝ) (hlo : 0 < lo)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (H34sq : DomainL2 (centeredCube z r hr) → ℝ)
    (hH34def : ∀ u, H34sq u = ‖u‖ ^ 2 +
      volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => u)).toReal) ^ 2)
    (KN : ℕ → ℝ) (hKN : ∀ n, 0 ≤ KN n)
    (hKNle : ∀ n, KN n ≤ Kstar)
    (hinverse : ∀ n (f : DomainL2 (centeredCube z r hr)),
      H34sq (T n f) ≤ (KN n / lo) * inner ℝ f (T n f) ∧
      H34sq (T n f) ≤ (KN n / lo) ^ 2 * ‖f‖ ^ 2 ∧
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => T n f) < ⊤)
    :
    IsCompact (closure (⋃ n : ℕ,
      (T n) '' Metric.closedBall (0 : DomainL2 (centeredCube z r hr)) 1)) := by
  let V : ℝ := volume.real (centeredCube z r hr : Set (SpatialCoordinates d))
  have hV : 0 < V := by
    dsimp [V]
    exact centeredCube_volume_pos z hr
  have hsqrtV : 0 < Real.sqrt V := Real.sqrt_pos.2 hV
  have hsqrtV_sq : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV.le
  let B : ℝ := Kstar / lo
  have hB : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg hKstar hlo.le
  let c : ℝ := r ^ (-(Lane4.threeQuarterOrder : ℝ))
  have hc : 0 ≤ c := by
    dsimp [c]
    exact Real.rpow_nonneg hr.le _
  let M : ℝ := B / Real.sqrt V + c * (B / Real.sqrt V)
  have hnorm_bound (n : ℕ) (f : DomainL2 (centeredCube z r hr))
      (hf : ‖f‖ ≤ 1) :
      cubeFractionalL2Norm hd z r hr Lane4.threeQuarterOrder
        ⟨fun _ : Fin 1 => (T n f), (hinverse n f).2.2⟩ ≤ M := by
    have hdiv : 0 ≤ KN n / lo := div_nonneg (hKN n) hlo.le
    have hdiv_le : KN n / lo ≤ B := by
      dsimp [B]
      exact (div_le_div_of_nonneg_right (hKNle n) hlo.le)
    have hH : H34sq (T n f) ≤ B ^ 2 := by
      calc
        H34sq (T n f) ≤ (KN n / lo) ^ 2 * ‖f‖ ^ 2 := (hinverse n f).2.1
        _ ≤ B ^ 2 * 1 ^ 2 := by gcongr
        _ = B ^ 2 := by ring
    rw [hH34def (T n f)] at hH
    have hnorm : ‖T n f‖ ≤ B := by
      have hnonneg : 0 ≤ V *
          ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
            (fun _ : Fin 1 => T n f)).toReal) ^ 2 :=
        mul_nonneg hV.le (sq_nonneg _)
      nlinarith
    have hq : (cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => T n f)).toReal ≤ B / Real.sqrt V := by
      have hq0 : 0 ≤ (cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
          (fun _ : Fin 1 => T n f)).toReal := ENNReal.toReal_nonneg
      apply (le_div_iff₀ hsqrtV).2
      nlinarith
    unfold cubeFractionalL2Norm
    simp only [Fin.sum_univ_one, Real.sqrt_sq_eq_abs, abs_norm]
    change (cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => T n f)).toReal +
      c * (‖T n f‖ / Real.sqrt V) ≤ M
    dsimp [M]
    have hnorm' : ‖T n f‖ / Real.sqrt V ≤ B / Real.sqrt V :=
      div_le_div_of_nonneg_right hnorm hsqrtV.le
    gcongr
  apply isCompact_closure_of_subseq_tendsto
  intro u hu
  choose k hk using fun n => Set.mem_iUnion.mp (hu n)
  choose f hf huf using fun n => hk n
  have hfball : ∀ n, ‖f n‖ ≤ 1 := by
    intro n
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hf n)
  let w : ℕ → CubeFractionalL2 (k := 1) hd z r hr Lane4.threeQuarterOrder :=
    fun n => ⟨fun _ : Fin 1 => T (k n) (f n), (hinverse (k n) (f n)).2.2⟩
  obtain ⟨sigma, hsigma, wlim, hwlim⟩ := hInterp.compact_embedding z r hr
    Lane4.threeQuarterOrder (by rfl) w M
      (by intro n; exact hnorm_bound (k n) (f n) (hfball n))
  refine ⟨wlim, sigma, hsigma, ?_⟩
  have hwu : ∀ n, u n = (w n).val 0 := by
    intro n
    calc
      u n = T (k n) (f n) := (huf n).symm
      _ = (w n).val 0 := by rfl
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_apply, hwu] using hwlim

lemma aux_lem_weighted_cluster_limit_cluster_psd_zero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H)
    (hsym : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (hpos : ∀ x, 0 ≤ inner ℝ x (T x))
    {x : H} (hx : inner ℝ x (T x) = 0) : T x = 0 := by
  have hinner : ∀ y : H, inner ℝ (T x) y = 0 := by
    intro y
    by_contra hne
    let b : ℝ := inner ℝ x (T y)
    let c : ℝ := inner ℝ y (T y)
    have hc : 0 ≤ c := hpos y
    have hplus : ∀ t : ℝ, 0 ≤ 2 * t * b + t ^ 2 * c := by
      intro t
      have h := hpos (x + t • y)
      simp only [map_add, map_smul, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, smul_eq_mul] at h
      have hcross : inner ℝ y (T x) = inner ℝ x (T y) := by
        rw [← hsym y x, real_inner_comm]
      rw [hcross, hx] at h
      dsimp [b, c]
      nlinarith
    have hden : 0 < c + 1 := by linarith
    let ht : ℝ := -b / (c + 1)
    have hbad := hplus ht
    have hb : b ≠ 0 := by
      dsimp [b]
      intro hb
      apply hne
      rw [hsym x y, hb]
    dsimp [ht] at hbad
    field_simp [hden.ne'] at hbad
    nlinarith [sq_pos_of_ne_zero hb]
  have hzero : inner ℝ (T x) (T x) = 0 := hinner (T x)
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp hzero

lemma aux_lem_weighted_cluster_limit_cluster_inverse_lower
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (S : ResponseSpace Ω) (a b : PositiveCoefficient Ω)
    (hi : ℝ) (hhi : 0 < hi)
    (hform : ∀ u : S.space,
      responseForm S b u u ≤ hi * responseForm S a u u)
    (f : DomainL2 Ω) :
    (1 / hi) * inner ℝ f
        (responseSolution S a ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 ≤
      inner ℝ f
        (responseSolution S b ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 := by
  let L : S.space →L[ℝ] ℝ := (sobolevVolumeLoad f).comp S.space.subtypeL
  let ua : S.space := responseSolution S a L
  let ub : S.space := responseSolution S b L
  have hLa : L ua = responseForm S a ua ua := by
    symm
    exact responseSolution_spec S a L ua
  have hLb : L ub = responseForm S b ub ub := by
    symm
    exact responseSolution_spec S b L ub
  have hgreat := (inverseResponse_isGreatest S b L).2
    (show 2 * L ((1 / hi) • ua) - responseForm S b ((1 / hi) • ua) ((1 / hi) • ua) ∈
      Set.range (fun v : S.space => 2 * L v - responseForm S b v v) from
        ⟨(1 / hi) • ua, rfl⟩)
  have hupper := hform ua
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] at hgreat
  have hrecip : hi * (1 / hi) = 1 := by
    field_simp
  have hrecip2 : (1 / hi) ^ 2 * hi = 1 / hi := by
    field_simp
  have hterm : (1 / hi) ^ 2 * responseForm S b ua ua ≤
      (1 / hi) ^ 2 * (hi * responseForm S a ua ua) :=
    mul_le_mul_of_nonneg_left hupper (sq_nonneg _)
  have hterm' : (1 / hi) * ((1 / hi) * responseForm S b ua ua) ≤
      (1 / hi) * L ua := by
    calc
      (1 / hi) * ((1 / hi) * responseForm S b ua ua) ≤
          (1 / hi) ^ 2 * (hi * responseForm S a ua ua) := by
            simpa only [pow_two, mul_assoc] using hterm
      _ = (1 / hi) * L ua := by
        rw [← hLa]
        calc
          (1 / hi) ^ 2 * (hi * L ua) =
              ((1 / hi) ^ 2 * hi) * L ua := by ring
          _ = (1 / hi) * L ua := by rw [hrecip2]
  have hscaled :
      (1 / hi) * L ua ≤ inverseResponse S b L := by
    nlinarith [hgreat, hterm']
  have hInv : inverseResponse S b L = L ub := by
    rw [inverseResponse_eq_load]
  have hLa' : responseForm S a ua ua = inner ℝ f ua.val.1 := by
    rw [responseSolution_spec]
    rfl
  have hLb' : responseForm S b ub ub = inner ℝ f ub.val.1 := by
    rw [responseSolution_spec]
    rfl
  have hs : (1 / hi) * L ua ≤ L ub := by
    have hs0 := hscaled
    rw [hInv] at hs0
    exact hs0
  have hs' : (1 / hi) * responseForm S a ua ua ≤
      responseForm S b ub ub := by
    calc
      (1 / hi) * responseForm S a ua ua = (1 / hi) * L ua :=
        congrArg (fun x : ℝ => (1 / hi) * x) hLa.symm
      _ ≤ L ub := hs
      _ = responseForm S b ub ub := hLb
  change (1 / hi) * inner ℝ f ua.val.1 ≤ inner ℝ f ub.val.1
  calc
    (1 / hi) * inner ℝ f ua.val.1 =
        (1 / hi) * responseForm S a ua ua :=
      congrArg (fun x : ℝ => (1 / hi) * x) hLa'.symm
    _ ≤ responseForm S b ub ub := hs'
    _ = inner ℝ f ub.val.1 := hLb'



theorem lem_weighted_cluster_limit_cluster
    (d : ℕ) (hd : 2 ≤ d) (J : Type) [Countable J]
    (z : J → SpatialCoordinates d) (r : J → ℝ) (hr : ∀ j, 0 < r j) :
    let Q := fun j => centeredCube (z j) (r j) (hr j)
    let H := fun j => DomainL2 (Q j)
    ∀ (S : ∀ j, ResponseSpace (Q j))
    (hS : ∀ j, (S j).space = killedSobolevGraph (Q j))
    (a arho : ∀ j, ℕ → PositiveCoefficient (Q j))
    (GrhoN : ∀ j, ℕ → (H j →L[ℝ] H j))
    (hGrhoN : ∀ j n f, GrhoN j n f =
      (responseSolution (S j) (arho j n)
        ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
    (KN : J → ℕ → ℝ) (hKN : ∀ j n, 0 ≤ KN j n)
    (Kstar : J → ℝ) (hKstar : ∀ j n, KN j n ≤ Kstar j)
    (G : ∀ j, H j →L[ℝ] H j)
    (hGinj : ∀ j, Function.Injective (G j))
    (hGlim : ∀ j f, Tendsto (fun n =>
      (responseSolution (S j) (a j n)
        ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1)
      atTop (𝓝 (G j f)))
    (H34sq : ∀ j, H j → ℝ)
    (hH34def : ∀ j u, H34sq j u = ‖u‖ ^ 2 +
      volume.real (Q j : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z j) (r j) (hr j)
          Lane4.threeQuarterOrder (fun _ : Fin 1 => u)).toReal) ^ 2)
    (hfrac : ∀ j (u : (S j).space),
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j)
        Lane4.threeQuarterOrder (fun _ : Fin 1 => u.val.1) < ⊤)
    (lo hi : J → ℝ) (hlo : ∀ j, 0 < lo j)
    (hform : ∀ j n (u : (S j).space),
      lo j * responseForm (S j) (a j n) u u ≤
          responseForm (S j) (arho j n) u u ∧
      responseForm (S j) (arho j n) u u ≤
          hi j * responseForm (S j) (a j n) u u)
    (hInterp : CubeFractionalInterpolationInput d hd)
    (hinverse : ∀ j n (f : H j),
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) * inner ℝ f (GrhoN j n f) ∧
      H34sq j (GrhoN j n f) ≤ (KN j n / lo j) ^ 2 * ‖f‖ ^ 2 ∧
      cubeFractionalL2Seminorm hd (z j) (r j) (hr j)
        Lane4.threeQuarterOrder (fun _ : Fin 1 => GrhoN j n f) < ⊤),
    (∀ tau : ℕ → ℕ, StrictMono tau →
      ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
        ∃ (Grho : (∀ j : J, H j →L[ℝ] H j)),
          (∀ j : J,
            Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 (Grho j)) ∧
            IsCompactOperator (Grho j) ∧
            (∀ x y : H j, inner ℝ (Grho j x) y = inner ℝ x (Grho j y)) ∧
            (∀ x : H j, 0 ≤ inner ℝ x (Grho j x)) ∧
            Function.Injective (Grho j))) := by
  intro Q H S hS a arho GrhoN hGrhoN KN hKN Kstar hKstar G hGinj hGlim H34sq hH34def hfrac lo hi hlo hform hInterp hinverse tau htau
  classical
  have hKstar_nonneg : ∀ j, 0 ≤ Kstar j := by
    intro j
    have h := hKstar j 0
    linarith [hKN j 0]
  have hsym : ∀ (j : J) (n : ℕ) (x y : H j),
      inner ℝ (GrhoN j n x) y = inner ℝ x (GrhoN j n y) := by
    intro j n x y
    rw [hGrhoN, hGrhoN, real_inner_comm]
    exact volumeResponse_pairing_symm (S j) (arho j n) y x
  have hpos : ∀ (j : J) (n : ℕ) (x : H j),
      0 ≤ inner ℝ x (GrhoN j n x) := by
    intro j n x
    rw [hGrhoN]
    exact volumeResponse_pairing_nonneg (S j) (arho j n) x
  have hcompact : ∀ j : J,
      IsCompact (closure (⋃ n : ℕ,
        (GrhoN j n) '' Metric.closedBall (0 : H j) 1)) := by
    intro j
    exact aux_lem_weighted_cluster_limit_cluster_collective_compact
      d hd (z j) (r j) (hr j) (S j) (arho j) (GrhoN j)
      (hGrhoN j) (Kstar j) (hKstar_nonneg j) (lo j) (hlo j) hInterp
      (H34sq j) (hH34def j) (fun n => KN j n) (hKN j) (hKstar j) (hinverse j)
  have hexistsD : ∀ j : J, ∃ D : Submodule ℚ (H j),
      Countable D ∧ Dense (D : Set (H j)) := by
    intro j
    letI : IsSeparable (volume.restrict (Q j : Set (SpatialCoordinates d))) := by
      infer_instance
    letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
    letI : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
    letI : SecondCountableTopology (H j) := by
      change SecondCountableTopology
        (Lp ℝ 2 (volume.restrict (Q j : Set (SpatialCoordinates d))))
      infer_instance
    letI : SeparableSpace (H j) := by infer_instance
    letI : Nonempty (H j) := inferInstance
    let Dj : Submodule ℚ (H j) :=
      Submodule.span ℚ (Set.range (denseSeq (H j)))
    refine ⟨Dj, ?_, ?_⟩
    · exact inferInstance
    · apply Dense.mono Submodule.subset_span
      exact denseRange_denseSeq (H j)
  choose D hDcount hDdense using hexistsD
  have hDadd : ∀ j : J, ∀ x ∈ (D j : Set (H j)),
      ∀ y ∈ (D j : Set (H j)), x + y ∈ D j := by
    intro j x hx y hy
    exact (D j).add_mem hx hy
  letI : ∀ j : J, Nonempty (H j) := fun j => inferInstance
  let κ := Sigma (fun j => (D j : Type))
  let C : ∀ j : J, ℝ := fun j =>
    Classical.choose (exists_operatorNorm_bound_of_collectively_compact (hcompact j))
  have hC : ∀ j : J, 0 ≤ C j ∧
      ∀ n : ℕ, ‖GrhoN j n‖ ≤ C j := by
    intro j
    dsimp [C]
    exact Classical.choose_spec
      (exists_operatorNorm_bound_of_collectively_compact (hcompact j))
  let Kq : κ → Set ℝ := fun k =>
    Set.Icc (-(C k.1) * ‖(k.2 : H k.1)‖ ^ 2)
      (C k.1 * ‖(k.2 : H k.1)‖ ^ 2)
  have hKq : ∀ k : κ, IsCompact (Kq k) := by
    intro k
    have hC0 := (hC k.1).1
    apply isCompact_Icc
  let uq : κ → ℕ → ℝ := fun k n =>
    inner ℝ (GrhoN k.1 (tau n) (k.2 : H k.1)) (k.2 : H k.1)
  have huq : ∀ k n, uq k n ∈ Kq k := by
    intro k n
    have hCj := (hC k.1).1
    have hCb := (hC k.1).2
    have hnorm : ‖GrhoN k.1 (tau n) (k.2 : H k.1)‖ ≤
            C k.1 * ‖(k.2 : H k.1)‖ := by
      exact ((GrhoN k.1 (tau n)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hCb _) (norm_nonneg _))
    have habs : |uq k n| ≤ C k.1 * ‖(k.2 : H k.1)‖ ^ 2 := by
      dsimp [uq]
      calc
        |inner ℝ (GrhoN k.1 (tau n) (k.2 : H k.1)) (k.2 : H k.1)| ≤
            ‖GrhoN k.1 (tau n) (k.2 : H k.1)‖ * ‖(k.2 : H k.1)‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ (C k.1 * ‖(k.2 : H k.1)‖) * ‖(k.2 : H k.1)‖ :=
          mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
        _ = C k.1 * ‖(k.2 : H k.1)‖ ^ 2 := by ring
    simpa only [Kq, Set.mem_Icc, neg_mul] using (abs_le.mp habs)
  obtain ⟨sigma, hsigma, hquad⟩ :=
    aux_lem_weighted_cluster_limit_cluster_countable_subseq Kq hKq uq huq
  have hcompact_sub : ∀ j : J,
      IsCompact (closure (⋃ n : ℕ,
        (GrhoN j (tau (sigma n))) '' Metric.closedBall (0 : H j) 1)) := by
    intro j
    apply IsCompact.of_isClosed_subset (hcompact j) isClosed_closure
    apply closure_minimal
    · intro y hy
      obtain ⟨n, hy⟩ := Set.mem_iUnion.mp hy
      obtain ⟨x, hx, rfl⟩ := hy
      apply subset_closure
      exact Set.mem_iUnion.mpr ⟨tau (sigma n), x, hx, rfl⟩
    · exact (hcompact j).isClosed
  have hlimit : ∀ j : J, ∃ Gj : H j →L[ℝ] H j,
      Tendsto (fun n => GrhoN j (tau (sigma n))) atTop (𝓝 Gj) ∧
      IsCompactOperator Gj ∧
      (∀ x y : H j, inner ℝ (Gj x) y = inner ℝ x (Gj y)) ∧
      (∀ x : H j, 0 ≤ inner ℝ x (Gj x)) := by
    intro j
    obtain ⟨Gj, hGj, -⟩ := existsUnique_limit_of_collectively_compact_quadratic_responses
      (hDdense j) (hDadd j)
      (fun n x y => hsym j (tau (sigma n)) x y)
      (fun n x => hpos j (tau (sigma n)) x)
      (hcompact_sub j) (by
        intro x hx
        obtain ⟨q, hq⟩ := hquad ⟨j, ⟨x, hx⟩⟩
        have heq :
            (fun n => uq ⟨j, ⟨x, hx⟩⟩ (sigma n)) =
              (fun n => inner ℝ x ((GrhoN j (tau (sigma n))) x)) := by
          funext n
          dsimp [uq]
          exact real_inner_comm _ _
        rw [← heq]
        exact hq.cauchySeq)
    exact ⟨Gj, hGj⟩
  choose Grho hGrho using hlimit
  have hGsym : ∀ (j : J) (x y : H j),
      inner ℝ (G j x) y = inner ℝ x (G j y) := by
    intro j x y
    have hleft : Tendsto
        (fun n => inner ℝ
          (responseSolution (S j) (a j n)
            ((sobolevVolumeLoad x).comp (S j).space.subtypeL)).val.1 y) atTop
        (𝓝 (inner ℝ (G j x) y)) :=
      (hGlim j x).inner tendsto_const_nhds
    have hright : Tendsto
        (fun n => inner ℝ x
          (responseSolution (S j) (a j n)
            ((sobolevVolumeLoad y).comp (S j).space.subtypeL)).val.1) atTop
        (𝓝 (inner ℝ x (G j y))) :=
      tendsto_const_nhds.inner (hGlim j y)
    have hright' : Tendsto
        (fun n => inner ℝ
          (responseSolution (S j) (a j n)
            ((sobolevVolumeLoad x).comp (S j).space.subtypeL)).val.1 y) atTop
        (𝓝 (inner ℝ x (G j y))) := by
      apply hright.congr'
      filter_upwards [] with n
      calc
        inner ℝ x
            (responseSolution (S j) (a j n)
              ((sobolevVolumeLoad y).comp (S j).space.subtypeL)).val.1 =
            inner ℝ y
              (responseSolution (S j) (a j n)
                ((sobolevVolumeLoad x).comp (S j).space.subtypeL)).val.1 :=
          volumeResponse_pairing_symm (S j) (a j n) x y
        _ = inner ℝ
              (responseSolution (S j) (a j n)
                ((sobolevVolumeLoad x).comp (S j).space.subtypeL)).val.1 y :=
          real_inner_comm _ _
    exact tendsto_nhds_unique hleft hright'
  have hGpos : ∀ (j : J) (x : H j), 0 ≤ inner ℝ x (G j x) := by
    intro j x
    have hconv : Tendsto
        (fun n => inner ℝ x
          (responseSolution (S j) (a j n)
            ((sobolevVolumeLoad x).comp (S j).space.subtypeL)).val.1) atTop
        (𝓝 (inner ℝ x (G j x))) :=
      tendsto_const_nhds.inner (hGlim j x)
    exact isClosed_Ici.mem_of_tendsto hconv
      (Eventually.of_forall fun n => by
        exact volumeResponse_pairing_nonneg (S j) (a j n) x)
  have hhi : ∀ j : J, 0 < hi j := by
    intro j
    by_contra hnot
    have hhi0 : hi j ≤ 0 := le_of_not_gt hnot
    have hμ : volume.restrict (Q j : Set (SpatialCoordinates d)) ≠ 0 := by
      intro hzero
      have hreal : volume.real (Q j : Set (SpatialCoordinates d)) = 0 := by
        rw [← measureReal_restrict_apply_univ]
        rw [hzero]
        simp
      exact (centeredCube_volume_pos (z j) (hr j)).ne' hreal
    letI : NeZero (volume.restrict (Q j : Set (SpatialCoordinates d))) := ⟨hμ⟩
    let f0 : H j := Lp.const (2 : ℝ≥0∞)
      (volume.restrict (Q j : Set (SpatialCoordinates d))) (1 : ℝ)
    have hf0 : f0 ≠ 0 := by
      intro hf0zero
      have hnorm : ‖f0‖ = 0 := by rw [hf0zero]; simp
      dsimp [f0] at hnorm
      have hformula :
          ‖Lp.const (2 : ℝ≥0∞)
              (volume.restrict (Q j : Set (SpatialCoordinates d))) (1 : ℝ)‖ =
            ‖(1 : ℝ)‖ *
              (volume.restrict (Q j : Set (SpatialCoordinates d))).real Set.univ ^
                (1 / (2 : ℝ≥0∞).toReal) :=
        Lp.norm_const (2 : ℝ≥0∞)
          (volume.restrict (Q j : Set (SpatialCoordinates d))) (1 : ℝ) (by norm_num)
      rw [hformula] at hnorm
      norm_num at hnorm
      have hμpos : 0 <
          (volume.restrict (Q j : Set (SpatialCoordinates d))).real Set.univ := by
        rw [measureReal_restrict_apply_univ]
        exact centeredCube_volume_pos (z j) (hr j)
      have hμpos' : 0 < volume.real (Q j : Set (SpatialCoordinates d)) := by
        simpa only [measureReal_restrict_apply_univ] using hμpos
      nlinarith
    obtain ⟨f, hf⟩ : ∃ f : H j, f ≠ 0 := ⟨f0, hf0⟩
    have hGf : G j f ≠ 0 := by
      intro hzero
      apply hf
      apply hGinj j
      simpa using hzero
    obtain ⟨n, hn⟩ : ∃ n : ℕ,
        (responseSolution (S j) (a j n)
          ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1 ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      have hz : Tendsto (fun _ : ℕ => (0 : H j)) atTop (𝓝 (G j f)) := by
        apply (hGlim j f).congr'
        exact Eventually.of_forall fun m => by simpa using hnone m
      have hGzero : G j f = 0 := tendsto_nhds_unique hz tendsto_const_nhds
      exact hGf hGzero
    let u : (S j).space := responseSolution (S j) (a j n)
      ((sobolevVolumeLoad f).comp (S j).space.subtypeL)
    have hu : u ≠ 0 := by
      intro hu0
      apply hn
      simpa [u, hu0]
    have ha_pos : 0 < responseForm (S j) (a j n) u u := by
      apply lt_of_le_of_ne (responseForm_nonneg (S j) (a j n) u)
      intro hzero
      exact hu ((responseForm_self_eq_zero_iff (S j) (a j n) u).mp hzero.symm)
    have hb_le : responseForm (S j) (arho j n) u u ≤ 0 := by
      calc
        responseForm (S j) (arho j n) u u ≤
            hi j * responseForm (S j) (a j n) u u := (hform j n u).2
        _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hhi0 ha_pos.le
    have hb_zero : responseForm (S j) (arho j n) u u = 0 :=
      le_antisymm hb_le (responseForm_nonneg (S j) (arho j n) u)
    exact hu ((responseForm_self_eq_zero_iff (S j) (arho j n) u).mp hb_zero)
  have hlower : ∀ (j : J) (f : H j),
      (1 / hi j) * inner ℝ f (G j f) ≤ inner ℝ f (Grho j f) := by
    intro j f
    have hA : Tendsto
        (fun n => inner ℝ f
          (responseSolution (S j) (a j (tau (sigma n)))
            ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1) atTop
        (𝓝 (inner ℝ f (G j f))) := by
      simpa only [Function.comp_apply] using
        (tendsto_const_nhds.inner
          ((hGlim j f).comp ((htau.comp hsigma).tendsto_atTop)))
    have hT : Tendsto
        (fun n => GrhoN j (tau (sigma n)) f) atTop (𝓝 (Grho j f)) :=
      ((continuous_id.clm_apply continuous_const).tendsto (Grho j)).comp
        (hGrho j).1
    have hB : Tendsto
        (fun n => inner ℝ f (GrhoN j (tau (sigma n)) f)) atTop
        (𝓝 (inner ℝ f (Grho j f))) :=
      tendsto_const_nhds.inner hT
    have hpoint : ∀ n : ℕ,
        (1 / hi j) * inner ℝ f
            (responseSolution (S j) (a j (tau (sigma n)))
              ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1 ≤
          inner ℝ f (GrhoN j (tau (sigma n)) f) := by
      intro n
      have h := aux_lem_weighted_cluster_limit_cluster_inverse_lower
        (S j) (a j (tau (sigma n))) (arho j (tau (sigma n))) (hi j)
        (hhi j) (fun u => (hform j (tau (sigma n)) u).2) f
      simpa only [hGrhoN] using h
    have hscale : Tendsto
        (fun n => (1 / hi j) * inner ℝ f
          (responseSolution (S j) (a j (tau (sigma n)))
            ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1) atTop
        (𝓝 ((1 / hi j) * inner ℝ f (G j f))) := by
      simpa only using (tendsto_const_nhds.mul hA)
    have hdiff : Tendsto
        (fun n => inner ℝ f (GrhoN j (tau (sigma n)) f) -
          (1 / hi j) * inner ℝ f
            (responseSolution (S j) (a j (tau (sigma n)))
              ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1) atTop
        (𝓝 (inner ℝ f (Grho j f) - (1 / hi j) * inner ℝ f (G j f))) :=
      hB.sub hscale
    have hnonneg : ∀ᶠ n : ℕ in atTop,
        0 ≤ inner ℝ f (GrhoN j (tau (sigma n)) f) -
          (1 / hi j) * inner ℝ f
            (responseSolution (S j) (a j (tau (sigma n)))
              ((sobolevVolumeLoad f).comp (S j).space.subtypeL)).val.1 :=
      Eventually.of_forall fun n => sub_nonneg.mpr (hpoint n)
    have hlim_nonneg := isClosed_Ici.mem_of_tendsto hdiff hnonneg
    change 0 ≤ inner ℝ f (Grho j f) - (1 / hi j) * inner ℝ f (G j f) at hlim_nonneg
    linarith
  have hinj : ∀ j : J, Function.Injective (Grho j) := by
    intro j x y hxy
    have hv : Grho j (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hqzero : inner ℝ (x - y) (G j (x - y)) = 0 := by
      have hlow := hlower j (x - y)
      have hupper : inner ℝ (x - y) (Grho j (x - y)) = 0 := by
        rw [hv]
        exact inner_zero_right _
      have hscaled : (1 / hi j) * inner ℝ (x - y) (G j (x - y)) ≤ 0 := by
        simpa only [hupper] using hlow
      have hcoef : 0 < (1 / hi j) := one_div_pos.mpr (hhi j)
      nlinarith [hGpos j (x - y)]
    have hGzero : G j (x - y) = 0 :=
      aux_lem_weighted_cluster_limit_cluster_psd_zero (G j)
        (hGsym j) (hGpos j) hqzero
    have hGzero' : G j (x - y) = G j 0 := by
      simpa using hGzero
    exact sub_eq_zero.mp (hGinj j hGzero')
  refine ⟨sigma, hsigma, Grho, ?_⟩
  intro j
  exact ⟨(hGrho j).1, (hGrho j).2.1, (hGrho j).2.2.1,
    (hGrho j).2.2.2, hinj j⟩

end Paper

