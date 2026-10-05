module

public import SubdiffusiveProcess.Paper.gagliardo_dilation_scaling
public import SubdiffusiveProcess.Paper.weak_gradient_chain_rule
public import SubdiffusiveProcess.Paper.dilation_coefficient_transport
public import SubdiffusiveProcess.Paper.energy_dilation_scaling
public import SubdiffusiveProcess.Paper.coercivity_dilation
public import SubdiffusiveProcess.Paper.lem_extension_trace_class_transport
public import SubdiffusiveProcess.Main.OriginalGridResponseConvolution
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CubeNegativeL2Norm
public import SubdiffusiveProcess.Main.HalfFractionalOrder
public import SubdiffusiveProcess.Main.CubeFractionalL2Norm
public import SubdiffusiveProcess.Sobolev.BoundaryEnergy
public import SubdiffusiveProcess.Sobolev.FoldDiscounts
public import SubdiffusiveProcess.Sobolev.LoadApproximation
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.FractionalVectorFiniteness
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.CoarseGrainingVocab.Core
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SupportBase
public import SubdiffusiveProcess.Section6.Defs.GoodEvent
public import SubdiffusiveProcess.Section6.Defs.HolderRegularityConclusions
public import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.coefficient_physical_identity
public import SubdiffusiveProcess.Paper.lem_extension_cell_moment
public import SubdiffusiveProcess.Paper.lem_extension_grid_cardinality
public import SubdiffusiveProcess.Paper.lem_extension_grid_assembly
public import SubdiffusiveProcess.EllipticRegularity.Inputs

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess
open _root_.SubdiffusiveProcess.EllipticRegularity

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_lem_extension_choose_growth_threshold
    (d : ℕ) (eta q deltaq Cd : ℝ)
    (hq : 0 < q) (hqeta : (d : ℝ) < q * eta)
    (hdeltaq : 0 < deltaq) (hCd : 0 < Cd) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ deltaq ∧
      ∀ delta : ℝ, 0 ≤ delta → delta ≤ delta0 →
        0 ≤ Cd * (q + q ^ 2) * delta ^ 2 ∧
        Cd * (q + q ^ 2) * delta ^ 2 <
          (eta - (d : ℝ) / q) * Real.log 3 := by
  let gap : ℝ := (eta - (d : ℝ) / q) * Real.log 3
  have hgap : 0 < gap := by
    have hdiv : (d : ℝ) / q < eta := (div_lt_iff₀ hq).2 (by simpa [mul_comm] using hqeta)
    exact mul_pos (sub_pos.mpr hdiv) (Real.log_pos (by norm_num))
  let A : ℝ := Cd * (q + q ^ 2)
  have hA : 0 < A := by
    dsimp [A]
    have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
    exact mul_pos hCd (by linarith)
  let delta0 : ℝ := min deltaq (min 1 (gap / (2 * A)))
  have hdelta0 : 0 < delta0 := by
    dsimp [delta0]
    exact lt_min hdeltaq (lt_min (by norm_num) (div_pos hgap (by positivity)))
  refine ⟨delta0, hdelta0, min_le_left _ _, ?_⟩
  intro delta hnonneg hle
  have hle1 : delta ≤ 1 := le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hleA : delta ≤ gap / (2 * A) :=
    le_trans hle (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsquare : delta ^ 2 ≤ delta := by nlinarith
  have hbound : A * delta ^ 2 ≤ A * (gap / (2 * A)) := by
    apply le_trans (mul_le_mul_of_nonneg_left hsquare hA.le)
    exact mul_le_mul_of_nonneg_left hleA hA.le
  have hhalf : A * (gap / (2 * A)) = gap / 2 := by
    field_simp [ne_of_gt hA]
  constructor
  · positivity
  · change A * delta ^ 2 < gap
    rw [hhalf] at hbound
    linarith

theorem aux_lem_extension_grid_clause
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) :
  ∀ (eta p : ℝ), 0 < eta → 1 ≤ p →
    ∀ (beta : ℝ), beta ∈ Set.Ioo (1 / 2 : ℝ) 1 →
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
        ∀ (J : ℕ) (origins : Fin J → SpatialCoordinates d),
        ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : ℝ),
          (∀ N, MemLp (K N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
          (∀ N, eLpNorm (K N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal Cbound) ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
            ∀ (N k : ℕ) (index : Fin J) (nidx : Fin d → ℤ), k ≤ N →
              (centeredCube (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
                ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
              E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                  (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
                    ((3 : ℝ) ^ (-(k : ℤ))) ((beta - 1 / 2) / 4) 2 +
                (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                  (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
                    ((3 : ℝ) ^ (-(k : ℤ))) ((beta - 1 / 2) / 4) 2)⁻¹ ≤
                K N om * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-eta) := by
  intro eta p heta hp beta hbeta
  let q : ℝ := p + ((d : ℝ) + 1) / eta
  have hqpos : 0 < q := by
    dsimp [q]
    have : 0 ≤ ((d : ℝ) + 1) / eta := div_nonneg (by positivity) heta.le
    linarith
  have hpq : p ≤ q := by
    dsimp [q]
    have : 0 ≤ ((d : ℝ) + 1) / eta := div_nonneg (by positivity) heta.le
    linarith
  have hq1 : 1 ≤ q := le_trans hp hpq
  have hqeta : (d : ℝ) < q * eta := by
    dsimp [q]
    have hcancel : ((d : ℝ) + 1) / eta * eta = (d : ℝ) + 1 :=
      div_mul_cancel₀ _ (ne_of_gt heta)
    nlinarith [mul_nonneg (by linarith : 0 ≤ p) heta.le]
  obtain ⟨deltaq, Cd, hdeltaq, hCd, hcell⟩ :=
    lem_extension_cell_moment d hd E beta eta q hbeta heta hq1 hqeta
  obtain ⟨delta0, hdelta0, hsmall, hgrowth⟩ :=
    aux_lem_extension_choose_growth_threshold d eta q deltaq Cd hqpos hqeta hdeltaq hCd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm H hInfra hM z0 R hR J origins
  obtain ⟨Cq, hCq, hcellroot⟩ := hcell M Rm H hInfra (le_trans hM hsmall) z0 R hR
  obtain ⟨Cgrid, hgrid⟩ := lem_extension_grid_cardinality d hd z0 R hR J origins
  let admissible : ℕ → Fin J → (Fin d → ℤ) → Prop := fun k index nidx =>
    centeredCube (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
      ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR
  let F : ℕ → ℕ → Fin J → (Fin d → ℤ) → BilateralField d → ℝ :=
    fun N k index nidx om =>
      E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
        (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
          ((3 : ℝ) ^ (-(k : ℤ))) ((beta - 1 / 2) / 4) 2 +
      (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
        (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
          ((3 : ℝ) ^ (-(k : ℤ))) ((beta - 1 / 2) / 4) 2)⁻¹
  let growth : ℝ := Cd * (q + q ^ 2) * M.delta ^ 2
  have hMd : 0 ≤ M.delta := M.shellPrefix.delta_pos.le
  have hgrowth0 : 0 ≤ growth := (hgrowth M.delta hMd hM).1
  have hgrowth1 : growth < (eta - (d : ℝ) / q) * Real.log 3 :=
    (hgrowth M.delta hMd hM).2
  have hmeasure : ∀ (N k : ℕ) (index : Fin J) (nidx : Fin d → ℤ),
      k ≤ N → admissible k index nidx →
      AEStronglyMeasurable (F N k index nidx) (chaosSampleLaw M).toMeasure := by
    intro N k index nidx hkn had
    exact (hcellroot J origins N k index nidx hkn had).1
  have hmoment : ∀ (N k : ℕ) (index : Fin J) (nidx : Fin d → ℤ),
      k ≤ N → admissible k index nidx →
      eLpNorm (F N k index nidx) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Cq * Real.exp (growth * (k : ℝ))) := by
    intro N k index nidx hkn had
    exact (hcellroot J origins N k index nidx hkn had).2
  simpa only [F, admissible] using
    (lem_extension_grid_assembly (BilateralField d) (chaosSampleLaw M).toMeasure
      d J eta p q heta hp hpq hqeta admissible F Cgrid Cq growth hCq.le
      hgrowth0 hgrowth1 hgrid hmeasure hmoment)

private def aux_lem_extension_boundaryDilationHomeomorph {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    SpatialCoordinates d ≃ₜ SpatialCoordinates d where
  toEquiv := (cubeDilationEquiv z 0 hr.ne').toEquiv
  continuous_toFun := continuous_cubeDilation z 0 r
  continuous_invFun := continuous_cubeDilation 0 z r⁻¹

private theorem aux_lem_extension_boundaryDilation_frontier_iff {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (x : SpatialCoordinates d) :
    x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
      Set (SpatialCoordinates d)) ↔
    cubeDilation z 0 r x ∈ frontier (centeredCube z r hr :
      Set (SpatialCoordinates d)) := by
  let T := aux_lem_extension_boundaryDilationHomeomorph z r hr
  have hpre : T ⁻¹' (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) =
      frontier (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
        Set (SpatialCoordinates d)) := by
    rw [T.preimage_frontier]
    change frontier ((cubeDilation z 0 r) ⁻¹' (centeredCube z r hr :
      Set (SpatialCoordinates d))) = _
    rw [cubeDilation_preimage_centeredCube z 0 hr (by norm_num)]
  have hx := congrArg (fun S : Set (SpatialCoordinates d) => x ∈ S) hpre
  exact hx.symm.to_iff

private theorem aux_lem_extension_boundaryDilation_sqrt_pos {d : ℕ}
    (x y : SpatialCoordinates d) (hxy : x ≠ y) :
    0 < Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) := by
  have hi : ∃ i : Fin d, x i ≠ y i := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  obtain ⟨i, hi⟩ := hi
  have hsum : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
    apply Finset.sum_pos' (fun j _ => sq_nonneg _)
    exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hi)⟩
  exact Real.sqrt_pos.2 hsum

private theorem aux_lem_extension_boundaryDilation_ratio {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (beta : ℝ) (G : SpatialCoordinates d → ℝ)
    (x y : SpatialCoordinates d) (hxy : x ≠ y) :
    |G (cubeDilation z 0 r x) - G (cubeDilation z 0 r y)| /
        (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta =
      r ^ beta *
        (|G (cubeDilation z 0 r x) - G (cubeDilation z 0 r y)| /
          (Real.sqrt (∑ j : Fin d,
            (cubeDilation z 0 r x j - cubeDilation z 0 r y j) ^ 2)) ^ beta) := by
  have hDpos := aux_lem_extension_boundaryDilation_sqrt_pos x y hxy
  have hrpow : 0 < r ^ beta := Real.rpow_pos_of_pos hr _
  have hDpow : 0 < (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) ^ beta :=
    Real.rpow_pos_of_pos hDpos _
  rw [sqrt_sum_sq_cubeDilation z 0 hr x y, Real.mul_rpow hr.le hDpos.le]
  field_simp

theorem aux_lem_extension_holderRatioSet_dilation {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (beta : ℝ) (G : SpatialCoordinates d → ℝ) :
    holderRatioSet beta
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
          Set (SpatialCoordinates d))) (fun x => G (cubeDilation z 0 r x)) =
      (r ^ beta) • holderRatioSet beta
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G := by
  let T := aux_lem_extension_boundaryDilationHomeomorph z r hr
  let S0 : Set (SpatialCoordinates d) :=
    frontier (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
      Set (SpatialCoordinates d))
  let S : Set (SpatialCoordinates d) :=
    frontier (centeredCube z r hr : Set (SpatialCoordinates d))
  have hfront (x : SpatialCoordinates d) : x ∈ S0 ↔ T x ∈ S := by
    exact aux_lem_extension_boundaryDilation_frontier_iff z r hr x
  ext v
  constructor
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    have hTxy : T x ≠ T y := T.injective.ne hxy
    refine Set.mem_smul_set.mpr ⟨
      |G (T x) - G (T y)| /
        (Real.sqrt (∑ j : Fin d, (T x j - T y j) ^ 2)) ^ beta,
      ⟨T x, (hfront x).mp hx, T y, (hfront y).mp hy, hTxy, rfl⟩, ?_⟩
    change r ^ beta * _ = _
    exact (aux_lem_extension_boundaryDilation_ratio z r hr beta G x y hxy).symm
  · rintro ⟨v', ⟨x, hx, y, hy, hxy, rfl⟩, rfl⟩
    let u := T.symm x
    let w := T.symm y
    have hu : u ∈ S0 := (hfront u).mpr (by simpa [u] using hx)
    have hw : w ∈ S0 := (hfront w).mpr (by simpa [w] using hy)
    have huw : u ≠ w := T.symm.injective.ne hxy
    refine ⟨u, hu, w, hw, huw, ?_⟩
    have hux : cubeDilation z 0 r u = x := by
      change T (T.symm x) = x
      exact T.apply_symm_apply x
    have hwy : cubeDilation z 0 r w = y := by
      change T (T.symm y) = y
      exact T.apply_symm_apply y
    have hratio := (aux_lem_extension_boundaryDilation_ratio z r hr beta G u w huw).symm
    rw [hux, hwy] at hratio
    change r ^ beta * _ = _
    simpa only [hux, hwy] using hratio

theorem aux_lem_extension_holderSeminorm_dilation {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (beta : ℝ) (G : SpatialCoordinates d → ℝ) :
    holderSeminorm beta
        (frontier (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
          Set (SpatialCoordinates d))) (fun x => G (cubeDilation z 0 r x)) =
      r ^ beta * holderSeminorm beta
        (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G := by
  unfold holderSeminorm
  rw [aux_lem_extension_holderRatioSet_dilation z r hr beta G,
    Real.sSup_smul_of_nonneg (Real.rpow_nonneg hr.le _)]
  simp only [smul_eq_mul]

theorem aux_lem_extension_isHolderOn_dilation {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (beta : ℝ) (G : SpatialCoordinates d → ℝ)
    (hG : IsHolderOn beta
      (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) :
    IsHolderOn beta
      (frontier (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
        Set (SpatialCoordinates d))) (fun x => G (cubeDilation z 0 r x)) := by
  unfold IsHolderOn at hG ⊢
  rw [aux_lem_extension_holderRatioSet_dilation z r hr beta G]
  exact (bddAbove_smul_iff_of_pos (Real.rpow_pos_of_pos hr beta)).mpr hG

/-- Exact coarse-response transport for the boundary extension proof. -/
theorem aux_extension_boundary_Lam_transport
    {d : ℕ} (E : in_J d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (s : ℝ) (q : ℝ≥0∞) :
    ∃ b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)),
      E.Lam z r hr a z r s q =
        E.Lam 0 1 (by norm_num) b 0 1 s q := by
  let h1 : (0 : ℝ) < 1 := by norm_num
  obtain ⟨b, hb⟩ := dilation_coefficient_transport d z 0 r hr h1 a
  refine ⟨b, ?_⟩
  exact E.Lam_dilation z r hr a 0 h1 b hb s q

/-- Transport of a weak Sobolev competitor and its exact energy to the unit cube. -/
theorem aux_extension_boundary_energy_transport
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (u : weakSobolevGraph (centeredCube z r hr)) :
    ∃ (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)))
      (w : weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num))),
      ((w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num))).1 :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num) :
          Set (SpatialCoordinates d))]
        (fun x => ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          (cubeDilation z 0 r x)) ∧
      sobolevCoefficientForm a (u : SobolevData (centeredCube z r hr))
          (u : SobolevData (centeredCube z r hr)) =
        r ^ ((d : ℝ) - 2) *
          sobolevCoefficientForm b
            (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num)))
            (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 (by norm_num))) := by
  let h1 : (0 : ℝ) < 1 := by norm_num
  obtain ⟨b, hb⟩ := dilation_coefficient_transport d z 0 r hr h1 a
  obtain ⟨w, hw, _⟩ := aux_coercivity_dilation_weak_pullback d z r hr h1 u
  refine ⟨b, w, hw, ?_⟩
  exact energy_dilation_scaling d z 0 r hr h1 a b u w u.2 w.2 hb hw

theorem aux_extension_boundary_trace_comparison
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (b h : weakSobolevGraph (centeredCube z r hr))
    (B H : SpatialCoordinates d → ℝ)
    (hB : ContinuousOn B (closedCube z r hr))
    (hH : ContinuousOn H (closedCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] B)
    (hh : ((h : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] H)
    (hfront : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      B x = H x) :
    (b : SobolevData (centeredCube z r hr)) -
      (h : SobolevData (centeredCube z r hr)) ∈
        killedSobolevGraph (centeredCube z r hr) := by
  let u : weakSobolevGraph (centeredCube z r hr) := b - h
  have hu : ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      (fun x => B x - H x) := by
    have hsub := Lp.coeFn_sub (b : SobolevData (centeredCube z r hr)).1
      (h : SobolevData (centeredCube z r hr)).1
    exact hsub.trans (hb.sub hh)
  have hcont : ContinuousOn (fun x => B x - H x) (closedCube z r hr) := hB.sub hH
  have hz : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      B x - H x = 0 := by
    intro x hx
    rw [hfront x hx, sub_self]
  exact lem_extension_trace_class_transport hd z r hr u (fun x => B x - H x)
    hcont hu hz

/-! ### Helpers for `eq:mfd-2`: the unit-cube reduction

The paper proves `eq:mfd-2` on the unit cube and rescales.  The helpers below carry the
rescaling `x ↦ z + r x` between the unit cube about the origin and the cube of side `r`
about `z`: exact transfer of almost-everywhere statements, the frontier, the Hölder
seminorm (which scales by `r^β`), and push-forwards of weak and killed Sobolev data (the
direction opposite to the existing pullbacks).  The fractional helpers identify the vector
`H^σ` norm of a gradient with the sum of the componentwise norms supplied by the trace
right inverse, and evaluate the source seminorm of the zero source. -/

/-- Almost-everywhere statements transfer exactly between the cube of side `r` about `z`
and the unit cube about the origin along `x ↦ z + r x`. -/
theorem aux_lem_extension_ae_dilation_iff {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (h1 : (0 : ℝ) < 1) (P : SpatialCoordinates d → Prop) :
    (∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), P y) ↔
      ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)), P (cubeDilation z 0 r x) := by
  have hmap := map_cubeDilation_restrict z (0 : SpatialCoordinates d) hr h1
  have hemb : MeasurableEmbedding (cubeDilation z (0 : SpatialCoordinates d) r) :=
    (cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne').measurableEmbedding
  have hc : ENNReal.ofReal |(r ^ d)⁻¹| ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  rw [← hemb.ae_map_iff, hmap, Measure.ae_ennreal_smul_measure_eq hc]

/-- The dilation written additively. -/
theorem aux_lem_extension_cubeDilation_eq {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (x : SpatialCoordinates d) : cubeDilation z 0 r x = z + r • x := by
  funext i
  simp [cubeDilation]

/-- The inverse of the dilation, on the right. -/
theorem aux_lem_extension_cubeDilation_inv {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (y : SpatialCoordinates d) :
    cubeDilation z 0 r (r⁻¹ • (y - z)) = y := by
  rw [aux_lem_extension_cubeDilation_eq, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  abel

/-- The inverse of the dilation, on the left. -/
theorem aux_lem_extension_cubeDilation_inv' {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (x : SpatialCoordinates d) :
    r⁻¹ • (cubeDilation z 0 r x - z) = x := by
  rw [aux_lem_extension_cubeDilation_eq, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ hr.ne', one_smul]

/-- The frontier of a centred cube is its max-norm sphere. -/
theorem aux_lem_extension_mem_frontier {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (y : SpatialCoordinates d) :
    y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)) ↔ dist y z = r / 2 := by
  change y ∈ frontier (Metric.ball z (r / 2)) ↔ _
  rw [frontier_ball z (by positivity : r / 2 ≠ 0)]
  rfl

/-- The dilation carries the frontier of the unit cube onto the frontier of the cube of
side `r`. -/
theorem aux_lem_extension_frontier_dilation {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (h1 : (0 : ℝ) < 1) (x : SpatialCoordinates d) :
    cubeDilation z 0 r x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)) ↔
      x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)) := by
  rw [aux_lem_extension_mem_frontier, aux_lem_extension_mem_frontier,
    aux_lem_extension_cubeDilation_eq, dist_eq_norm, dist_eq_norm, add_sub_cancel_left,
    sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  constructor
  · intro h
    have : r * ‖x‖ = r * (1 / 2) := by rw [h]; ring
    exact mul_left_cancel₀ hr.ne' this
  · intro h
    rw [h]
    ring



theorem aux_lem_extension_isOpenBoundedConvexDomain_centeredCube {d : ℕ}
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    Homogenization.IsOpenBoundedConvexDomain
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  refine ⟨(centeredCube z r hr).isOpen, ?_, ?_⟩
  · refine Homogenization.Bornology.IsBounded.isBoundedDomain ?_
    show Bornology.IsBounded (Metric.ball z (r / 2))
    exact Metric.isBounded_ball
  · show Convex ℝ (Metric.ball z (r / 2))
    exact convex_ball z (r / 2)

/-- A Hölder seminorm is nonnegative. -/
theorem aux_lem_extension_holderSeminorm_nonneg {d : ℕ} (beta : ℝ)
    (S : Set (SpatialCoordinates d)) (G : SpatialCoordinates d → ℝ) :
    0 ≤ holderSeminorm beta S G := by
  refine Real.sSup_nonneg ?_
  rintro w ⟨x, -, y, -, -, rfl⟩
  exact div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

/-- Transport of a native `H¹` witness along an equality of carriers keeps its values. -/
theorem aux_lem_extension_h1_cast_toFun {d : ℕ} {U V : Set (SpatialCoordinates d)}
    (h : U = V) (u : Homogenization.H1Function U) : (h ▸ u).toFun = u.toFun := by
  subst h
  rfl

/-- Transport of a native `H¹₀` witness along an equality of carriers keeps its values. -/
theorem aux_lem_extension_h10_cast_toFun {d : ℕ} {U V : Set (SpatialCoordinates d)}
    (h : U = V) (u : Homogenization.H10Function U) :
    (h ▸ u).toH1Function.toFun = u.toH1Function.toFun := by
  subst h
  rfl

/-- The unit cube about the origin is `r⁻¹` times the cube of side `r` about the origin. -/
theorem aux_lem_extension_unit_eq_inv_smul {d : ℕ} {r : ℝ} (hr : 0 < r) (h1 : (0 : ℝ) < 1) :
    (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)) =
      r⁻¹ • (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) := by
  rw [(aux_coercivity_dilation_cube_geometry d 0 r hr h1).2, smul_smul,
    inv_mul_cancel₀ hr.ne', one_smul]

/-- Push-forward of weak Sobolev data from the unit cube about the origin to the cube of
side `r` about `z`, along the inverse of `x ↦ z + r x`; the direction opposite to
`aux_coercivity_dilation_weak_pullback`. -/
theorem aux_lem_extension_weak_pushforward {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (h1 : (0 : ℝ) < 1)
    (w : weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1)) :
    ∃ u : weakSobolevGraph (centeredCube z r hr),
      ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)),
        (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 x =
          (u : SobolevData (centeredCube z r hr)).1 (cubeDilation z 0 r x) := by
  classical
  have hT := (aux_coercivity_dilation_cube_geometry d z r hr h1).1
  have hU := aux_lem_extension_unit_eq_inv_smul (d := d) hr h1
  obtain ⟨u1, hu1, -⟩ := exists_nativeH1Function_of_weakSobolevGraph w
  let uS : Homogenization.H1Function
      (r⁻¹ • (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d))) :=
    hU ▸ u1
  let u0 : Homogenization.H1Function
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) :=
    Homogenization.H1Function.unscale (inv_pos.2 hr) uS
  let uT : Homogenization.H1Function (Homogenization.translateSet z
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d))) :=
    u0.translate z
  let uq : Homogenization.H1Function (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    hT.symm ▸ uT
  have huq : ∀ y, uq.toFun y =
      (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 (r⁻¹ • (y - z)) := by
    intro y
    change (hT.symm ▸ uT).toFun y = _
    rw [aux_lem_extension_h1_cast_toFun hT.symm uT]
    change u0.toFun (y - z) = _
    change uS.toFun (r⁻¹ • (y - z)) = _
    rw [aux_lem_extension_h1_cast_toFun hU u1]
    exact congrFun hu1 _
  obtain ⟨u, hu, -⟩ := exists_weakSobolevGraph_of_nativeH1 (Om := centeredCube z r hr) uq
  refine ⟨u, ?_⟩
  have hx := (aux_lem_extension_ae_dilation_iff z hr h1 _).1 hu
  filter_upwards [hx] with x hx
  rw [hx, huq, aux_lem_extension_cubeDilation_inv' z hr x]

/-- Push-forward of killed Sobolev data from the unit cube about the origin to the cube of
side `r` about `z`. -/
theorem aux_lem_extension_killed_pushforward {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (h1 : (0 : ℝ) < 1)
    (w : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1)) :
    ∃ u : killedSobolevGraph (centeredCube z r hr),
      ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
          Set (SpatialCoordinates d)),
        (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 x =
          (u : SobolevData (centeredCube z r hr)).1 (cubeDilation z 0 r x) := by
  classical
  have hT := (aux_coercivity_dilation_cube_geometry d z r hr h1).1
  have hU := aux_lem_extension_unit_eq_inv_smul (d := d) hr h1
  obtain ⟨u1, hu1, -⟩ := exists_nativeH10Function_of_killedSobolevGraph w
  let uS : Homogenization.H10Function
      (r⁻¹ • (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d))) :=
    hU ▸ u1
  let u0 : Homogenization.H10Function
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) :=
    Homogenization.H10Function.unscale (inv_pos.2 hr) uS
  let uT : Homogenization.H10Function (Homogenization.translateSet z
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d))) :=
    u0.translate z
  let uq : Homogenization.H10Function (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    hT.symm ▸ uT
  have huq : ∀ y, (uq : SpatialCoordinates d → ℝ) y =
      (w : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 (r⁻¹ • (y - z)) := by
    intro y
    change (hT.symm ▸ uT).toH1Function.toFun y = _
    rw [aux_lem_extension_h10_cast_toFun hT.symm uT]
    change u0.toH1Function.toFun (y - z) = _
    change uS.toH1Function.toFun (r⁻¹ • (y - z)) = _
    rw [aux_lem_extension_h10_cast_toFun hU u1]
    exact congrFun hu1 _
  obtain ⟨u, hu, -⟩ := exists_killedSobolevGraph_of_nativeH10 (Ω := centeredCube z r hr) uq
  refine ⟨u, ?_⟩
  have hx := (aux_lem_extension_ae_dilation_iff z hr h1 _).1 hu
  filter_upwards [hx] with x hx
  rw [hx, huq, aux_lem_extension_cubeDilation_inv' z hr x]

theorem aux_lem_extension_sqrt_sq_ennreal (t : ℝ≥0∞) : (t ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = t := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The vector Gagliardo seminorm squared is the sum of the componentwise ones. -/
theorem aux_lem_extension_vec_seminorm_sq {d k : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : Fin k → DomainL2 (centeredCube z r hr)) :
    (cubeFractionalL2Seminorm hd z r hr s f) ^ (2 : ℕ) =
      ∑ i : Fin k, (cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => f i)) ^ (2 : ℕ) := by
  unfold cubeFractionalL2Seminorm
  rw [aux_lem_extension_sqrt_sq_ennreal]
  conv_rhs => arg 2; ext i; rw [aux_lem_extension_sqrt_sq_ennreal]
  rw [← Finset.mul_sum]
  congr 1
  set μ := volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  set K : SpatialCoordinates d → SpatialCoordinates d → ℝ≥0∞ := fun x y =>
    (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ ((d : ℝ) + 2 * (s : ℝ))
    with hK
  have hKm : Measurable (Function.uncurry K) := by
    simp only [hK]
    fun_prop
  have hfm : ∀ i, Measurable (f i : SpatialCoordinates d → ℝ) := fun i =>
    (Lp.stronglyMeasurable (f i)).measurable
  have hFm : ∀ i, Measurable (Function.uncurry fun x y =>
      ENNReal.ofReal ((f i x - f i y) ^ 2) / K x y) := by
    intro i
    have h1 : Measurable fun p : SpatialCoordinates d × SpatialCoordinates d =>
        f i p.1 - f i p.2 := ((hfm i).comp measurable_fst).sub ((hfm i).comp measurable_snd)
    exact (ENNReal.measurable_ofReal.comp (h1.pow_const 2)).div hKm
  have hpt : ∀ x y, ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) / K x y =
      ∑ i : Fin k, ENNReal.ofReal ((f i x - f i y) ^ 2) / K x y := by
    intro x y
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    simp only [div_eq_mul_inv, Finset.sum_mul]
  simp only [Fin.sum_univ_one]
  change ∫⁻ x, ∫⁻ y, ENNReal.ofReal (∑ i : Fin k, (f i x - f i y) ^ 2) / K x y ∂μ ∂μ =
    ∑ i : Fin k, ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((f i x - f i y) ^ 2) / K x y ∂μ ∂μ
  simp only [hpt]
  have hinner : ∀ x, ∫⁻ y, ∑ i : Fin k, ENNReal.ofReal ((f i x - f i y) ^ 2) / K x y ∂μ =
      ∑ i : Fin k, ∫⁻ y, ENNReal.ofReal ((f i x - f i y) ^ 2) / K x y ∂μ := by
    intro x
    refine lintegral_finsetSum _ (fun i _ => ?_)
    exact (hFm i).of_uncurry_left
  simp only [hinner]
  refine lintegral_finsetSum _ (fun i _ => ?_)
  exact (hFm i).lintegral_prod_right'

/-- The zero vector field has zero Gagliardo seminorm. -/
theorem aux_lem_extension_seminorm_zero {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1) :
    cubeFractionalL2Seminorm hd z r hr s
      (fun i => (0 : HilbertGradient (centeredCube z r hr)) i) = 0 := by
  unfold cubeFractionalL2Seminorm
  set μ := volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))
  have h0 : ∀ᵐ x ∂μ,
      ((0 : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ) x = 0 :=
    Lp.coeFn_zero ℝ 2 μ
  have hI : ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (∑ i : Fin d, ((0 : HilbertGradient (centeredCube z r hr)) i x -
          (0 : HilbertGradient (centeredCube z r hr)) i y) ^ 2) /
          (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^
            ((d : ℝ) + 2 * (s : ℝ)) = 0 := by
    rw [← lintegral_zero (μ := μ)]
    refine lintegral_congr_ae ?_
    filter_upwards [h0] with x hx
    rw [← lintegral_zero (μ := μ)]
    refine lintegral_congr_ae ?_
    filter_upwards [h0] with y hy
    have hzx : ∀ i : Fin d,
        ((0 : HilbertGradient (centeredCube z r hr)) i : SpatialCoordinates d → ℝ) x = 0 :=
      fun i => by simpa using hx
    have hzy : ∀ i : Fin d,
        ((0 : HilbertGradient (centeredCube z r hr)) i : SpatialCoordinates d → ℝ) y = 0 :=
      fun i => by simpa using hy
    simp only [hzx, hzy, sub_self]
    simp
  rw [hI, mul_zero, ENNReal.zero_rpow_of_pos (by norm_num)]

/-- Componentwise finiteness gives vector finiteness, and the vector inhomogeneous norm
squared is the sum of the componentwise ones. -/
theorem aux_lem_extension_vec_sqNorm_eq {d k : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : Fin k → DomainL2 (centeredCube z r hr))
    (hfin : ∀ i, cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => f i) < ⊤) :
    cubeFractionalL2Seminorm hd z r hr s f ≠ ⊤ ∧
      cubeFractionalVecSqNorm hd z r hr s f =
        ∑ i : Fin k, cubeFractionalSqNorm hd z r hr s (f i) := by
  have hsq := aux_lem_extension_vec_seminorm_sq hd z r hr s f
  have hsum_ne : ∑ i : Fin k,
      (cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => f i)) ^ (2 : ℕ) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 (fun i _ => ENNReal.pow_ne_top (hfin i).ne)
  have hne : cubeFractionalL2Seminorm hd z r hr s f ≠ ⊤ := by
    intro htop
    rw [htop] at hsq
    apply hsum_ne
    rw [← hsq]
    simp
  refine ⟨hne, ?_⟩
  unfold cubeFractionalSqNorm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
  have hsemi : ((cubeFractionalL2Seminorm hd z r hr s f).toReal) ^ 2 =
      ∑ i : Fin k,
        ((cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => f i)).toReal) ^ 2 := by
    rw [← ENNReal.toReal_pow, hsq, ENNReal.toReal_sum
      (fun i _ => ENNReal.pow_ne_top (hfin i).ne)]
    simp only [ENNReal.toReal_pow]
  rw [hsemi, Finset.sum_add_distrib, Finset.sum_div]
  simp

/-- `in_extension` on a cube of side `3^0`, with zero source: the
energy of the harmonic extension of `h` is controlled by `C Λ_{s/2,2}^{1/2}` and `‖∇h‖_{H^s}`
(the constant `C = X.C` of the paper's `e.cg.RHS` stands on the boundary-datum term).
The side is carried as a variable equal to `3^0`, so the bound is read on the unit cube
without rewriting inside the dependent cube. -/
theorem aux_lem_extension_unit_extension {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (X : in_extension d hd E) (z : SpatialCoordinates d) (ρ : ℝ) (hρ : 0 < ρ)
    (e : ρ = (3 : ℝ) ^ (0 : ℕ))
    (a : PositiveCoefficient (centeredCube z ρ hρ)) (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hDatum v : weakSobolevGraph (centeredCube z ρ hρ))
    (hfin : cubeFractionalL2Seminorm hd z ρ hρ ⟨s, hs.1, hs.2⟩
      (fun i => sobolevGradient (hDatum : SobolevData (centeredCube z ρ hρ)) i) ≠ ⊤)
    (heuler : ∀ φ : killedSobolevGraph (centeredCube z ρ hρ),
      sobolevCoefficientForm a (v : SobolevData (centeredCube z ρ hρ))
        (φ : SobolevData (centeredCube z ρ hρ)) = 0)
    (hker : ((v : SobolevData (centeredCube z ρ hρ)) -
        (hDatum : SobolevData (centeredCube z ρ hρ))) ∈
      killedSobolevGraph (centeredCube z ρ hρ)) :
    normalizedEnergyNorm a (centeredCube z ρ hρ).isOpen.measurableSet
        (sobolevGradient (v : SobolevData (centeredCube z ρ hρ))) ≤
      X.C * s ^ (-(3 / 2) : ℝ) * (E.Lam z ρ hρ a z ρ (s / 2) 2) ^ ((1 / 2) : ℝ) *
        cubeFractionalL2Norm hd z ρ hρ ⟨s, hs.1, hs.2⟩
          ⟨fun i => sobolevGradient (hDatum : SobolevData (centeredCube z ρ hρ)) i,
            lt_top_iff_ne_top.2 hfin⟩ := by
  subst e
  have hz0 := aux_lem_extension_seminorm_zero hd z ((3 : ℝ) ^ (0 : ℕ)) hρ ⟨s, hs.1, hs.2⟩
  have hb := X.bound z 0 hρ a s hs 0 (by rw [hz0]; exact ENNReal.zero_ne_top) hDatum v hfin
    (fun φ => by rw [inner_zero_left, neg_zero]; exact heuler φ) hker
  have hz : cubeFractionalVecSeminormSq hd z ((3 : ℝ) ^ (0 : ℕ)) hρ ⟨s, hs.1, hs.2⟩
      (fun i => (0 : HilbertGradient (centeredCube z ((3 : ℝ) ^ (0 : ℕ)) hρ)) i) = 0 := by
    unfold cubeFractionalVecSeminormSq
    rw [hz0]
    simp
  rw [hz, Real.sqrt_zero, mul_zero, zero_add, Nat.cast_zero, mul_zero, Real.rpow_zero,
    mul_one] at hb
  exact hb


/-- Real arithmetic: `√V ≤ s^{-3/2} L^{1/2} √N` gives `V ≤ s^{-3} L N`. -/
theorem aux_lem_extension_sq_bound {V s L N : ℝ} (hV : 0 ≤ V) (hs : 0 < s) (hL : 0 < L)
    (hN : 0 ≤ N) (h : Real.sqrt V ≤ s ^ (-(3 / 2) : ℝ) * L ^ ((1 / 2) : ℝ) * Real.sqrt N) :
    V ≤ s ^ (-3 : ℝ) * L * N := by
  have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt hV, mul_pow, mul_pow, Real.sq_sqrt hN, ← Real.rpow_natCast,
    ← Real.rpow_natCast (L ^ ((1 / 2) : ℝ)), ← Real.rpow_mul hs.le, ← Real.rpow_mul hL.le] at h2
  rw [show (-(3 / 2) : ℝ) * ((2 : ℕ) : ℝ) = -3 by norm_num,
    show ((1 / 2) : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one] at h2
  exact h2

/-- `M`'s norm `[f] + r^{-s}‖f‖_{L̲²}` squared is at most twice the `ℓ²`-combined
`cubeFractionalVecSqNorm` (`(A+B)² ≤ 2(A²+B²)`), on the unit cube (`r = 1`, so `r^{-s}=1`
and the scale factor drops out). -/
theorem aux_lem_extension_unitNorm_sq_le {d k : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (h1 : (0 : ℝ) < 1) (s : Set.Ioo (0 : ℝ) 1) (f : CubeFractionalL2 (k := k) hd z 1 h1 s) :
    (cubeFractionalL2Norm hd z 1 h1 s f) ^ 2 ≤ 2 * cubeFractionalVecSqNorm hd z 1 h1 s f.val := by
  unfold cubeFractionalL2Norm cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
  rw [centeredCube_volume_real, one_pow, Real.sqrt_one, div_one, div_one, Real.one_rpow, one_mul]
  have hS : 0 ≤ ∑ i : Fin k, ‖f.val i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsq := Real.sq_sqrt hS
  nlinarith [sq_nonneg ((cubeFractionalL2Seminorm hd z 1 h1 s f.val).toReal -
    Real.sqrt (∑ i : Fin k, ‖f.val i‖ ^ 2))]

/-- `M`'s norm is nonnegative. -/
theorem aux_lem_extension_cubeFractionalL2Norm_nonneg {d k : ℕ} (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : CubeFractionalL2 (k := k) hd z r hr s) : 0 ≤ cubeFractionalL2Norm hd z r hr s f := by
  unfold cubeFractionalL2Norm
  exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg (Real.rpow_nonneg hr.le _)
    (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

/-- `(c² L)^{1/2} = c L^{1/2}` for `c, L ≥ 0`. -/
theorem aux_lem_extension_rpow_half_mul {c L : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L) :
    (c ^ 2 * L) ^ ((1 / 2) : ℝ) = c * L ^ ((1 / 2) : ℝ) := by
  have h : (c ^ 2) ^ ((1 / 2) : ℝ) = c := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hc]
  rw [Real.mul_rpow (sq_nonneg c) hL, h]

/-- Real arithmetic: `√V ≤ s^{-3/2} L^{1/2} N` and `N² ≤ 2B` give `V ≤ 2 s^{-3} L B`. -/
theorem aux_lem_extension_sq_bound_two {V s L N B : ℝ} (hV : 0 ≤ V) (hs : 0 < s) (hL : 0 < L)
    (hN : 0 ≤ N) (hNB : N ^ 2 ≤ 2 * B)
    (h : Real.sqrt V ≤ s ^ (-(3 / 2) : ℝ) * L ^ ((1 / 2) : ℝ) * N) :
    V ≤ 2 * s ^ (-3 : ℝ) * L * B := by
  have h1 := aux_lem_extension_sq_bound hV hs hL (sq_nonneg N) (by rwa [Real.sqrt_sq hN])
  have h0 : 0 ≤ s ^ (-3 : ℝ) * L := mul_nonneg (Real.rpow_nonneg hs.le _) hL.le
  calc V ≤ s ^ (-3 : ℝ) * L * N ^ 2 := h1
    _ ≤ s ^ (-3 : ℝ) * L * (2 * B) := mul_le_mul_of_nonneg_left hNB h0
    _ = 2 * s ^ (-3 : ℝ) * L * B := by ring

/-- On the unit cube the normalized energy norm is the square root of the energy. -/
theorem aux_lem_extension_normalizedEnergy_unit {d : ℕ} (h1 : (0 : ℝ) < 1)
    (a : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (u : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) :
    normalizedEnergyNorm a (centeredCube (0 : SpatialCoordinates d) 1 h1).isOpen.measurableSet
        (sobolevGradient u) = Real.sqrt (sobolevCoefficientForm a u u) := by
  unfold normalizedEnergyNorm
  rw [localGradientEnergy_domain_eq_sobolevCoefficientForm, centeredCube_volume_real,
    one_pow, div_one]

/-- The inhomogeneous normalized fractional norm squared is nonnegative. -/
theorem aux_lem_extension_vecSqNorm_nonneg {d k : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (f : Fin k → DomainL2 (centeredCube z r hr)) :
    0 ≤ cubeFractionalVecSqNorm hd z r hr s f := by
  unfold cubeFractionalVecSqNorm cubeFractionalVecSeminormSq
  exact add_nonneg (sq_nonneg _)
    (div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) measureReal_nonneg)

/-- The unit-cube energy estimate: the harmonic extension of a trace-extension datum `ĥ`
with `∇ĥ ∈ H^s` has energy at most `s^{-3} Λ_{s/2,2} Σ_i ‖∂_i ĥ‖²_{H^s}` (`in_extension`
with zero source, paper label `mfd:lem-extension`). -/
theorem aux_lem_extension_unit_energy {d : ℕ} (hd : 2 ≤ d) (E : in_J d)
    (X : in_extension d hd E) (h1 : (0 : ℝ) < 1)
    (hP1 : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1),
      ‖(u : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1)) u‖)
    (ah : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hh : weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (hfin : ∀ i : Fin d, cubeFractionalL2Seminorm hd 0 1 h1 ⟨s, hs.1, hs.2⟩
      (fun _ : Fin 1 => (hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i) < ⊤) :
    sobolevCoefficientForm ah
        (dirichletMinimizer (killedResponseSpace hP1) ah hh :
          SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))
        (dirichletMinimizer (killedResponseSpace hP1) ah hh :
          SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) ≤
      2 * X.C ^ 2 * s ^ (-3 : ℝ) * E.Lam 0 1 h1 ah 0 1 (s / 2) 2 *
        ∑ i : Fin d, cubeFractionalSqNorm hd 0 1 h1 ⟨s, hs.1, hs.2⟩
          ((hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i) := by
  have hker := dirichletMinimizer_mem_affine (killedResponseSpace hP1) ah hh
  have heuler : ∀ φ : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1),
      sobolevCoefficientForm ah (dirichletMinimizer (killedResponseSpace hP1) ah hh :
        SobolevData _) (φ : SobolevData _) = 0 :=
    fun φ => dirichletMinimizer_euler (killedResponseSpace hP1) ah hh φ
  obtain ⟨hvecfin, hvec⟩ := aux_lem_extension_vec_sqNorm_eq hd 0 1 h1 ⟨s, hs.1, hs.2⟩
    (fun i => (hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i) hfin
  have hE1 := aux_lem_extension_unit_extension hd E X 0 1 h1 (by norm_num) ah s hs hh
    (dirichletMinimizer (killedResponseSpace hP1) ah hh) hvecfin heuler hker
  rw [aux_lem_extension_normalizedEnergy_unit] at hE1
  rw [← hvec]
  have hN2 := aux_lem_extension_unitNorm_sq_le hd (0 : SpatialCoordinates d) h1 ⟨s, hs.1, hs.2⟩
    ⟨fun i => sobolevGradient
      (hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) i,
      lt_top_iff_ne_top.2 hvecfin⟩
  have hLpos := E.Lam_pos 0 1 h1 ah 0 1 (s / 2) 2
  have hE2 : Real.sqrt (sobolevCoefficientForm ah
      (dirichletMinimizer (killedResponseSpace hP1) ah hh :
        SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))
      (dirichletMinimizer (killedResponseSpace hP1) ah hh :
        SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))) ≤
      s ^ (-(3 / 2) : ℝ) * (X.C ^ 2 * E.Lam 0 1 h1 ah 0 1 (s / 2) 2) ^ ((1 / 2) : ℝ) *
        cubeFractionalL2Norm hd (0 : SpatialCoordinates d) 1 h1 ⟨s, hs.1, hs.2⟩
          ⟨fun i => sobolevGradient
            (hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) i,
            lt_top_iff_ne_top.2 hvecfin⟩ := by
    rw [aux_lem_extension_rpow_half_mul X.C_pos.le hLpos.le]
    exact hE1.trans (le_of_eq (by ring))
  have hN2' : (cubeFractionalL2Norm hd (0 : SpatialCoordinates d) 1 h1 ⟨s, hs.1, hs.2⟩
      ⟨fun i => sobolevGradient
        (hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) i,
        lt_top_iff_ne_top.2 hvecfin⟩) ^ 2 ≤
      2 * cubeFractionalVecSqNorm hd 0 1 h1 ⟨s, hs.1, hs.2⟩
        (fun i => (hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i) := hN2
  have hfin2 := aux_lem_extension_sq_bound_two (sobolevCoefficientForm_nonneg ah _) hs.1
    (mul_pos (pow_pos X.C_pos 2) hLpos)
    (aux_lem_extension_cubeFractionalL2Norm_nonneg hd _ _ _ _ _) hN2' hE2
  exact hfin2.trans (le_of_eq (by ring))

/-- The pushed trace extension has the boundary values of `b`: its difference with `b` is
a.e. a continuous function on the closed cube vanishing on the frontier, hence killed
(`lem_extension_trace_class_transport`). -/
theorem aux_lem_extension_datum_killed {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (h1 : (0 : ℝ) < 1) (G : SpatialCoordinates d → ℝ)
    (hGcont : ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)))
    (U : SpatialCoordinates d → ℝ) (hUc : Continuous U)
    (hUG : ∀ x ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)), U x = G (cubeDilation z 0 r x))
    (hh : weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (hhU : ((hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
        SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d))] U)
    (h b : weakSobolevGraph (centeredCube z r hr))
    (hhtie : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)),
      (hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 x =
        (h : SobolevData (centeredCube z r hr)).1 (cubeDilation z 0 r x))
    (htie : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G) :
    (h : SobolevData (centeredCube z r hr)) - (b : SobolevData (centeredCube z r hr)) ∈
      killedSobolevGraph (centeredCube z r hr) := by
  have hmem : (h : SobolevData (centeredCube z r hr)) - (b : SobolevData _) ∈
      weakSobolevGraph (centeredCube z r hr) := Submodule.sub_mem _ h.property b.property
  have hhU' : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      ((h : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) y =
        U (r⁻¹ • (y - z)) := by
    refine (aux_lem_extension_ae_dilation_iff z hr h1 _).2 ?_
    filter_upwards [hhtie, hhU] with x hx1 hx2
    rw [aux_lem_extension_cubeDilation_inv' z hr x, ← hx1, hx2]
  refine lem_extension_trace_class_transport hd z r hr ⟨_, hmem⟩
    (fun y => U (r⁻¹ • (y - z)) - G y) ?_ ?_ ?_
  · have hmap : Continuous (fun y : SpatialCoordinates d => r⁻¹ • (y - z)) := by fun_prop
    exact (hUc.comp hmap).continuousOn.sub hGcont
  · filter_upwards [Lp.coeFn_sub ((h : SobolevData (centeredCube z r hr)).1)
      ((b : SobolevData (centeredCube z r hr)).1), hhU', htie] with y hy1 hy2 hy3
    change ((h : SobolevData (centeredCube z r hr)).1 -
      (b : SobolevData (centeredCube z r hr)).1 : DomainL2 _) y = _
    rw [hy1, Pi.sub_apply, hy2, hy3]
  · intro y hy
    have hx : r⁻¹ • (y - z) ∈ frontier (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)) := by
      rw [← aux_lem_extension_frontier_dilation z hr h1, aux_lem_extension_cubeDilation_inv z hr]
      exact hy
    change U (r⁻¹ • (y - z)) - G y = 0
    rw [hUG _ hx, aux_lem_extension_cubeDilation_inv z hr, sub_self]

/-- The competitor `h + k` built from the push-forwards is admissible for the actual
Dirichlet response of `b`, and its energy is `r^{d-2}` times the unit-cube energy of the
harmonic extension (`energy_dilation_scaling`). -/
theorem aux_lem_extension_response_le {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (h1 : (0 : ℝ) < 1)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (ah : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (hah : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)), ah.val x = a.val (cubeDilation z 0 r x))
    (b h : weakSobolevGraph (centeredCube z r hr)) (k : killedSobolevGraph (centeredCube z r hr))
    (hhb : (h : SobolevData (centeredCube z r hr)) - (b : SobolevData (centeredCube z r hr)) ∈
      killedSobolevGraph (centeredCube z r hr))
    (hh vh : weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (hhtie : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)),
      (hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 x =
        (h : SobolevData (centeredCube z r hr)).1 (cubeDilation z 0 r x))
    (hktie : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
        Set (SpatialCoordinates d)),
      ((vh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) -
          (hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))).1 x =
        (k : SobolevData (centeredCube z r hr)).1 (cubeDilation z 0 r x)) :
    dirichletResponse (killedResponseSpace hP) a b ≤
      r ^ ((d : ℝ) - 2) *
        sobolevCoefficientForm ah (vh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))
          (vh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) := by
  obtain ⟨w, hw⟩ : ∃ w : killedSobolevGraph (centeredCube z r hr),
      (w : SobolevData (centeredCube z r hr)) =
        ((h : SobolevData (centeredCube z r hr)) - (b : SobolevData (centeredCube z r hr))) +
          (k : SobolevData (centeredCube z r hr)) :=
    ⟨⟨_, Submodule.add_mem _ hhb k.property⟩, rfl⟩
  have hresp : dirichletResponse (killedResponseSpace hP) a b ≤
      sobolevCoefficientForm a
        ((b : SobolevData (centeredCube z r hr)) + (w : SobolevData (centeredCube z r hr)))
        ((b : SobolevData (centeredCube z r hr)) + (w : SobolevData (centeredCube z r hr))) :=
    (dirichletResponse_isLeast (killedResponseSpace hP) a b).2 ⟨w, rfl⟩
  have hbw : (b : SobolevData (centeredCube z r hr)) + (w : SobolevData (centeredCube z r hr)) =
      (h : SobolevData (centeredCube z r hr)) + (k : SobolevData (centeredCube z r hr)) := by
    rw [hw]
    abel
  have hmemhk : (h : SobolevData (centeredCube z r hr)) + (k : SobolevData _) ∈
      weakSobolevGraph (centeredCube z r hr) :=
    Submodule.add_mem _ h.property (killedSobolevGraph_le_weakSobolevGraph k.property)
  have htie2 : ∀ᵐ x ∂volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 :
      Set (SpatialCoordinates d)),
      ((vh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 :
          SpatialCoordinates d → ℝ) x =
        (((h : SobolevData (centeredCube z r hr)) + (k : SobolevData _)).1 :
          SpatialCoordinates d → ℝ) (cubeDilation z 0 r x) := by
    have hadd := (aux_lem_extension_ae_dilation_iff z hr h1 _).1
      (Lp.coeFn_add ((h : SobolevData (centeredCube z r hr)).1)
        ((k : SobolevData (centeredCube z r hr)).1))
    filter_upwards [hadd, hhtie, hktie,
      Lp.coeFn_sub ((vh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1)
        ((hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1)]
      with x hx1 hx2 hx3 hx4
    change _ = ((h : SobolevData (centeredCube z r hr)).1 +
      (k : SobolevData (centeredCube z r hr)).1 : DomainL2 _) (cubeDilation z 0 r x)
    rw [hx1, Pi.add_apply, ← hx2]
    change (((vh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 -
      (hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1 : DomainL2 _) x) = _ at hx3
    rw [hx4, Pi.sub_apply] at hx3
    linarith
  have hscale := energy_dilation_scaling d z 0 r hr h1 a ah
    ((h : SobolevData (centeredCube z r hr)) + (k : SobolevData _)) (vh : SobolevData _)
    hmemhk vh.property hah htie2
  rw [hbw, hscale] at hresp
  exact hresp

/-- The deterministic half `eq:mfd-2` of `lem_extension` (paper label `eq:mfd-2`).

On the unit cube the trace right inverse of `SobolevFoundationalInput` extends the
rescaled boundary datum `Ĝ = G(z + r·)` to `ĥ ∈ H¹` with `∇ĥ ∈ H^σ`, `σ = (β-1/2)/2`, and
`‖∇ĥ‖²_{H^σ} ≤ C_β [Ĝ]²_{C^β}`; `in_extension` with zero source bounds the energy of the
harmonic extension `v̂` of `ĥ` by `σ^{-3} Λ_{σ/2,2} ‖∇ĥ‖²_{H^σ}`.  Pushing `ĥ` and `v̂ - ĥ`
forward to the cube of side `r` gives an admissible competitor for the actual Dirichlet
response of `b`: `ĥ`'s push-forward differs from `b` by a continuous function vanishing on
the frontier (the datum is tied to `b` a.e., continuous on the closed cube, and equals the
trace there), hence by a killed function (`lem_extension_trace_class_transport`).
Rescaling multiplies the energy by `r^{d-2}` (`energy_dilation_scaling`), leaves
`Λ` unchanged (`in_J.Lam_dilation`), and `[Ĝ]_{C^β} = r^β [G]_{C^β}`
(`aux_lem_extension_holderSeminorm_dilation`). -/
theorem aux_lem_extension_boundary_half (d : ℕ) (hd : 2 ≤ d) (E : in_J d)
    (X : in_extension d hd E) (S : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd) :
    ∀ (beta : ℝ), beta ∈ Set.Ioo (1 / 2 : ℝ) 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
      ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
          ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
            K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
        (a : PositiveCoefficient (centeredCube z r hr))
        (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
        ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
        IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
        dirichletResponse (killedResponseSpace hP) a b ≤
          C * E.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
            (r ^ beta *
              holderSeminorm beta
                (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
  intro beta hbeta
  have hσ : (beta - 1 / 2) / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hbeta.1, hbeta.2]
  refine ⟨2 * X.C ^ 2 * (((beta - 1 / 2) / 2) ^ (-3 : ℝ) * S.CTrace beta),
    mul_pos (mul_pos two_pos (pow_pos X.C_pos 2))
      (mul_pos (Real.rpow_pos_of_pos hσ.1 _) (S.CTrace_pos beta)), ?_⟩
  intro z r hr _hr1 hP a G b hGcont hGhol htie
  have h1 : (0 : ℝ) < 1 := one_pos
  have : NeZero d := ⟨by omega⟩
  -- the coefficient on the unit cube, and the dilation invariance of `Λ`
  obtain ⟨ah, hah⟩ := dilation_coefficient_transport d z 0 r hr h1 a
  have hLam : E.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 =
      E.Lam 0 1 h1 ah 0 1 ((beta - 1 / 2) / 2 / 2) 2 := by
    rw [show (beta - 1 / 2) / 4 = (beta - 1 / 2) / 2 / 2 by ring]
    exact E.Lam_dilation z r hr a 0 h1 ah hah _ 2
  -- the boundary datum on the unit cube and its trace extension
  have hGhol1 := aux_lem_extension_isHolderOn_dilation z r hr beta G hGhol
  have hGsemi1 := (aux_lem_extension_holderSeminorm_dilation z r hr beta G).le
  obtain ⟨hh, U, hUc, hhU, hUG, hfin, hsum⟩ :=
    S.traceRightInverse beta hbeta 0 1 h1 rfl _ hGhol1
  -- the harmonic extension of `ĥ` on the unit cube and its energy
  obtain ⟨hP1, -⟩ := exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain
    (centeredCube (0 : SpatialCoordinates d) 1 h1)
    (aux_lem_extension_isOpenBoundedConvexDomain_centeredCube 0 h1)
  have hEn := aux_lem_extension_unit_energy hd E X h1 hP1 ah _ hσ hh hfin
  have hker := dirichletMinimizer_mem_affine (killedResponseSpace hP1) ah hh
  -- the trace bound, rescaled
  have hNb : ∑ i : Fin d, cubeFractionalSqNorm hd 0 1 h1 ⟨_, hσ.1, hσ.2⟩
        ((hh : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).2 i) ≤
      S.CTrace beta * (r ^ beta *
        holderSeminorm beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2 := by
    refine hsum.trans ?_
    rw [Real.one_rpow, one_mul]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (aux_lem_extension_holderSeminorm_nonneg _ _ _) hGsemi1 2)
      (S.CTrace_pos beta).le
  -- push-forward of the extension and of the harmonic correction
  obtain ⟨h, hhtie⟩ := aux_lem_extension_weak_pushforward z hr h1 hh
  obtain ⟨k, hktie⟩ := aux_lem_extension_killed_pushforward z hr h1 ⟨_, hker⟩
  have hhb := aux_lem_extension_datum_killed hd z hr h1 G hGcont U hUc hUG hh hhU h b hhtie htie
  have hresp := aux_lem_extension_response_le z hr h1 hP a ah hah b h k hhb hh
    (dirichletMinimizer (killedResponseSpace hP1) ah hh) hhtie hktie
  have hrd : 0 < r ^ ((d : ℝ) - 2) := Real.rpow_pos_of_pos hr _
  have hLpos := E.Lam_pos 0 1 h1 ah 0 1 ((beta - 1 / 2) / 2 / 2) 2
  refine hresp.trans ?_
  rw [hLam]
  calc r ^ ((d : ℝ) - 2) * sobolevCoefficientForm ah _ _
      ≤ r ^ ((d : ℝ) - 2) * (2 * X.C ^ 2 * ((beta - 1 / 2) / 2) ^ (-3 : ℝ) *
          E.Lam 0 1 h1 ah 0 1 ((beta - 1 / 2) / 2 / 2) 2 * (S.CTrace beta * (r ^ beta *
            holderSeminorm beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (hEn.trans ?_) hrd.le
        exact mul_le_mul_of_nonneg_left hNb
          (mul_nonneg (mul_nonneg (mul_nonneg two_pos.le (pow_pos X.C_pos 2).le)
            (Real.rpow_nonneg hσ.1.le _)) hLpos.le)
    _ = _ := by ring





theorem lem_extension :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_X : in_extension d hd E)
    (_S : _root_.SubdiffusiveProcess.EllipticRegularity.SobolevFoundationalInput d hd),
  -- `eq:mfd-2`
  (∀ (beta : ℝ), beta ∈ Set.Ioo (1 / 2 : ℝ) 1 →
  ∃ C : ℝ, 0 < C ∧
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
      (a : PositiveCoefficient (centeredCube z r hr))
      (G : SpatialCoordinates d → ℝ) (b : weakSobolevGraph (centeredCube z r hr)),
      -- the paper's single datum `g ∈ C^β(∂q)` is the response input *and* the
      -- Hölder-norm input.  Continuity on the closed cube is what makes the a.e. tie on
      -- the open cube determine `G` on the frontier, where the seminorm is taken; without
      -- it `G` may be reset to `0` on that null set and the estimate is refutable.
      ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)) →
      -- and `g ∈ C^β(∂q)` itself: without it `holderSeminorm` is `sSup` of an unbounded
      -- set, which mathlib evaluates to the junk value `0`, and the estimate is refutable
      -- (take `G x = |x₁|^α` with `α < β`).  This is the paper's own hypothesis.
      IsHolderOn beta (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G →
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G →
      dirichletResponse (killedResponseSpace hP) a b ≤
        C * E.Lam z r hr a z r ((beta - 1 / 2) / 4) 2 * r ^ ((d : ℝ) - 2) *
          (r ^ beta *
            holderSeminorm beta
              (frontier (centeredCube z r hr : Set (SpatialCoordinates d))) G) ^ 2) ∧
  -- `eq:mfd-3`
  (∀ (eta p : ℝ), 0 < eta → 1 ≤ p →
    ∀ (beta : ℝ), beta ∈ Set.Ioo (1 / 2 : ℝ) 1 →
    ∃ delta0 : ℝ, 0 < delta0 ∧
        ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
          InfraredCharacterization M H → M.delta ≤ delta0 →
          ∀ (z0 : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
          ∀ (J : ℕ) (origins : Fin J → SpatialCoordinates d),
          ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : ℝ),
            (∀ N, MemLp (K N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
            (∀ N, eLpNorm (K N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤
              ENNReal.ofReal Cbound) ∧
            ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
              ∀ (N k : ℕ) (index : Fin J) (nidx : Fin d → ℤ), k ≤ N →
                (centeredCube (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i)
                    ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) ≤ centeredCube z0 R hR) →
                E.Lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                    (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) ((3 : ℝ) ^ (-(k : ℤ)))
                    ((beta - 1 / 2) / 4) 2 +
                  (E.lam z0 R hR (cutoffPositiveCoefficient M H om N z0 hR)
                    (fun i => origins index i + (3 : ℝ) ^ (-(k : ℤ)) * nidx i) ((3 : ℝ) ^ (-(k : ℤ)))
                    ((beta - 1 / 2) / 4) 2)⁻¹ ≤
                  K N om * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-eta)) := by
  intro d hd _ _ E X S
  exact ⟨aux_lem_extension_boundary_half d hd E X S, aux_lem_extension_grid_clause d hd E⟩

end SubdiffusiveProcess.Paper
