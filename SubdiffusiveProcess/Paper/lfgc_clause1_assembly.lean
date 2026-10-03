module

public import SubdiffusiveProcess.Paper.lem_finite_good_cell_local_holder

@[expose] public section

/-! Extraction of the finite good-event tests used by the local Holder estimate
(eq:mfd-finite-good-holder), and its assembly in the form of Clause 1 of
Lemma lem-finite-good-cell. No probability statement is made here. -/

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology
noncomputable section
namespace Paper

/-- The deterministic content of eq:mfd-finite-good-holder for fixed thresholds and constants. -/
def aux_lfgc_clause1_spec (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (alpha sigma cell eps lam Cfin delta1 : ℝ) : Prop :=
  ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), in_responses d M → M.delta ≤ delta1 →
  ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (m k : ℕ) (z : SpatialCoordinates d) (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
    (∀ (i : ℕ) (y : SpatialCoordinates d),
      eta i y = omega ((i : ℤ) - ((m + k : ℕ) : ℤ)) (((3 : ℝ) ^ (-((m + k : ℕ) : ℤ))) • y)) →
    (Tendsto (infraredPartialSum omega) atTop (nhds (H omega)) ∨ H = 0) →
  ∀ (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ)
    (goodEvt : ℕ → Vec d → Prop),
    primitive_scores d M sigma eps eta Fsc Psc Rsc Dsc Zsc goodEvt →
    (∀ (n : ℕ) (y : Vec d), Dsc n y ≠ ⊤) →
    (∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), 1 ≤ DA → k + DA ≤ m + k →
      ∑ l ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA),
          Zsc (((m + k : ℕ) : ℤ) - l).toNat
            (((3 : ℝ) ^ (m + k)) • descendantCenter 1 z ((3 : ℝ) ^ (-(k : ℤ))) DA dword) <
        lam * DA ∧
      ∑ l ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA),
          (Dsc (((m + k : ℕ) : ℤ) - l).toNat
            (((3 : ℝ) ^ (m + k)) • descendantCenter 1 z ((3 : ℝ) ^ (-(k : ℤ))) DA dword)).toReal <
        lam * DA) →
    (∀ (D : ℕ) (pword : Fin D → OddGridIndex d 1), D = m + 1 →
      (Dsc 0 (((3 : ℝ) ^ (m + k)) •
        descendantCenter 1 z (3 * (3 : ℝ) ^ (-(k : ℤ))) D pword)).toReal ≤ lam * (D : ℝ)) →
    |omega (-((k : ℤ) - 1)) z| ≤ 1 →
    (∀ h3 : 0 < 3 * (3 : ℝ) ^ (-(k : ℤ)),
      cell * aux_in_deterministic_onestep_sref M H omega (m + k) ((k : ℤ) - 1) z ≤
        I.lam z (3 * (3 : ℝ) ^ (-(k : ℤ))) h3
          (cutoffPositiveCoefficient M H omega (m + k) z h3)
          z (3 * (3 : ℝ) ^ (-(k : ℤ))) sigma 2) →
  ∀ (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R),
    Metric.closedBall z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2) ⊆
      (centeredCube zP R hR : Set (SpatialCoordinates d)) →
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), Measurable F → 0 ≤ Kf →
    (∀ x ∈ (centeredCube zP R hR : Set (SpatialCoordinates d)), |F x| ≤ Kf) →
  ∀ u : weakSobolevGraph (centeredCube zP R hR),
    (∀ psi : killedSobolevGraph (centeredCube zP R hR),
      sobolevCoefficientForm (cutoffPositiveCoefficient M H omega (m + k) zP hR) u.val psi.val =
        ∫ x in (centeredCube zP R hR : Set (SpatialCoordinates d)), F x * psi.val.1 x) →
  ∃ (U : SpatialCoordinates d → ℝ) (c : ℝ),
    ContinuousOn U (closedCube z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) :
      Set (SpatialCoordinates d)) ∧
    ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (centeredCube z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) : Set (SpatialCoordinates d))] U) ∧
    IsHolderOn alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => U (z + (3 : ℝ) ^ (-(k : ℤ)) • x) - c) ∧
    cAlphaNorm alpha (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => U (z + (3 : ℝ) ^ (-(k : ℤ)) • x) - c) ≤
      Cfin * ((3 : ℝ) ^ (-(k : ℤ))) ^ (((2 : ℝ) - (d : ℝ)) / 2) *
          (aux_in_deterministic_onestep_sref M H omega (m + k) k z) ^ (-(1 : ℝ) / 2) *
          Real.sqrt (sobolevCoefficientForm (cutoffPositiveCoefficient M H omega (m + k) zP hR)
            u.val u.val) +
        Cfin * ((3 : ℝ) ^ (-(k : ℤ))) ^ (2 : ℝ) *
          (aux_in_deterministic_onestep_sref M H omega (m + k) k z)⁻¹ * Kf



theorem aux_lfgc_clause1_spec_exists
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (Poincare : Paper.in_poincare d hd I)
    (MeyersMorrey : SmallPerturbationInput d)
    (Det : Paper.lane4_deterministic_good_scale_input d)
    (alpha sigma cell : ℝ) (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1)
    (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1) (hsigma32 : sigma ≤ 1 / 32) (hcell : 0 < cell) :
    ∃ Cfin t0 delta1 : ℝ, 0 < Cfin ∧ 0 < t0 ∧ 0 < delta1 ∧
    ∀ (eps lam lamDet : ℝ), eps ∈ Set.Ioo (0 : ℝ) 1 → eps ≤ t0 → 0 ≤ lam → lam ≤ lamDet →
      lamDet ≤ t0 → aux_lfgc_clause1_spec d I alpha sigma cell eps lam Cfin delta1 := by
  obtain ⟨Cfin, t0, delta1, hC, ht, hd1, h⟩ := lem_finite_good_cell_local_holder d hd I Poincare
    MeyersMorrey Det alpha sigma cell halpha hsigma hsigma32 hcell
  exact ⟨Cfin, t0, delta1, hC, ht, hd1, fun eps lam lamDet h1 h2 h3 h4 h5 =>
    h eps lam lamDet h1 h2 h3 h4 h5⟩

/-- The infrared choice inside the good event satisfies the infrared alternative. -/
theorem aux_lfgc_clause1_hIR {d : ℕ} (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (h : Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)))
    (b : Bool) :
    Tendsto (infraredPartialSum omega) atTop
        (𝓝 ((if b then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega)) ∨
      (if b then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) = 0 := by
  cases b
  · exact Or.inr rfl
  · exact Or.inl h

/-- The zero-offset term of the discounted field test bounds the centre value of its layer. -/
theorem aux_lfgc_clause1_Fsc_center {d : ℕ} [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s eps : ℝ) (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ) (goodEvt : ℕ → Vec d → Prop)
    (hPS : primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt) (n : ℕ) (y : Vec d) :
    ENNReal.ofReal |eta n y| ≤ Fsc n y := by
  obtain ⟨_, _, _, _, hF, -⟩ := hPS
  rw [hF n y]
  refine le_sSup_of_le ⟨0, rfl⟩ ?_
  simp only [Nat.cast_zero, mul_zero, zero_div, neg_zero, Real.rpow_zero, ENNReal.ofReal_one,
    one_mul, Nat.sub_zero, add_zero, Finset.Icc_self, Finset.sum_singleton]
  have hy : y ∈ translatedCube d ((n + 1 : ℕ) : ℤ) y := by
    rw [aux_in_deterministic_regularity_translatedCube_eq_ball]
    exact Metric.mem_ball_self (by positivity)
  refine le_sSup_of_le ⟨y, hy, rfl⟩ (ENNReal.ofReal_le_ofReal ?_)
  have hnn : 0 ≤ (3 : ℝ) ^ (n : ℝ) * euclideanNorm (shellGradient (eta n) y) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (euclideanNorm_nonneg _)
  rw [abs_of_nonneg (add_nonneg (abs_nonneg _) hnn)]
  linarith only [hnn]

/-- The padded field test bounds the single intervening layer at the cell centre. -/
theorem aux_lfgc_clause1_layer {d : ℕ} [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (s eps : ℝ) (eta : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (omega : BilateralField d)
    (m k : ℕ)
    (hEta : ∀ (i : ℕ) (x : SpatialCoordinates d),
      eta i x = omega ((i : ℤ) - ((m + k : ℕ) : ℤ)) ((3 : ℝ) ^ (-((m + k : ℕ) : ℤ)) • x))
    (Fsc Psc Rsc Dsc : ℕ → Vec d → ENNReal) (Zsc : ℕ → Vec d → ℝ) (goodEvt : ℕ → Vec d → Prop)
    (hPS : primitive_scores d M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt) (z : SpatialCoordinates d)
    (hF1 : Fsc (m + 1) ((3 : ℝ) ^ (m + k) • z) ≤ 1) :
    |omega (-((k : ℤ) - 1)) z| ≤ 1 := by
  have h := (aux_lfgc_clause1_Fsc_center M s eps eta Fsc Psc Rsc Dsc Zsc goodEvt hPS (m + 1)
    ((3 : ℝ) ^ (m + k) • z)).trans hF1
  rw [hEta] at h
  have hidx : (((m + 1 : ℕ) : ℤ) - ((m + k : ℕ) : ℤ)) = -((k : ℤ) - 1) := by push_cast; ring
  have hpt : (3 : ℝ) ^ (-((m + k : ℕ) : ℤ)) • (3 : ℝ) ^ (m + k) • z = z := by
    rw [smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity), one_smul]
  rw [hidx, hpt] at h
  exact (ENNReal.ofReal_le_one).mp h

/-- The self-root prefix test with unit buffer gives the prefix sums used by the iteration. -/
theorem aux_lfgc_clause1_pre {d : ℕ} (m k : ℕ) (lam : ℝ) (buffer k0 e0 : ℕ) (hb : buffer = 1)
    (hk0 : k0 = 1) (he0 : e0 = 0)
    (Zs : ℕ → SpatialCoordinates d → ℝ) (hZ0 : ∀ n y, 0 ≤ Zs n y)
    (Ds : ℕ → SpatialCoordinates d → ENNReal)
    (cen : ∀ DA : ℕ, (Fin DA → OddGridIndex d 1) → SpatialCoordinates d)
    (h : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k0 ≤ DA →
      (∑ j ∈ Finset.Icc ((k : ℤ) - (e0 : ℤ) - (buffer : ℤ))
          (min ((m + k : ℕ) : ℤ) ((k : ℤ) - (e0 : ℤ) + (DA : ℤ) + (buffer : ℤ))),
          (if 0 ≤ ((m + k : ℕ) : ℤ) - j then
            Zs (((m + k : ℕ) : ℤ) - j).toNat ((3 : ℝ) ^ (m + k) • cen DA dword) else 0)) <
        lam * DA ∧
      (∑ j ∈ Finset.Icc ((k : ℤ) - (e0 : ℤ) - (buffer : ℤ))
          (min ((m + k : ℕ) : ℤ) ((k : ℤ) - (e0 : ℤ) + (DA : ℤ) + (buffer : ℤ))),
          (if 0 ≤ ((m + k : ℕ) : ℤ) - j then
            (Ds (((m + k : ℕ) : ℤ) - j).toNat ((3 : ℝ) ^ (m + k) • cen DA dword)).toReal
          else 0)) < lam * DA) :
    ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), 1 ≤ DA → k + DA ≤ m + k →
      ∑ l ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA),
          Zs (((m + k : ℕ) : ℤ) - l).toNat ((3 : ℝ) ^ (m + k) • cen DA dword) < lam * DA ∧
      ∑ l ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA),
          (Ds (((m + k : ℕ) : ℤ) - l).toNat ((3 : ℝ) ^ (m + k) • cen DA dword)).toReal <
        lam * DA := by
  subst hb hk0 he0
  intro DA dword hDA hkN
  obtain ⟨hZ, hD⟩ := h DA dword hDA
  have hsub : Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA) ⊆
      Finset.Icc ((k : ℤ) - ((0 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))
        (min ((m + k : ℕ) : ℤ) ((k : ℤ) - ((0 : ℕ) : ℤ) + (DA : ℤ) + ((1 : ℕ) : ℤ))) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  have hin : ∀ l ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA),
      0 ≤ ((m + k : ℕ) : ℤ) - l := by
    intro l hl
    simp only [Finset.mem_Icc] at hl
    omega
  constructor
  · calc ∑ l ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA),
          Zs (((m + k : ℕ) : ℤ) - l).toNat ((3 : ℝ) ^ (m + k) • cen DA dword)
        = ∑ l ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA),
          (if 0 ≤ ((m + k : ℕ) : ℤ) - l then
            Zs (((m + k : ℕ) : ℤ) - l).toNat ((3 : ℝ) ^ (m + k) • cen DA dword) else 0) :=
          Finset.sum_congr rfl (fun l hl => (if_pos (hin l hl)).symm)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by
          split_ifs
          · exact hZ0 _ _
          · exact le_rfl)
      _ < lam * DA := hZ
  · calc ∑ l ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA),
          (Ds (((m + k : ℕ) : ℤ) - l).toNat ((3 : ℝ) ^ (m + k) • cen DA dword)).toReal
        = ∑ l ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ)) ((k : ℤ) + DA),
          (if 0 ≤ ((m + k : ℕ) : ℤ) - l then
            (Ds (((m + k : ℕ) : ℤ) - l).toNat ((3 : ℝ) ^ (m + k) • cen DA dword)).toReal
          else 0) :=
          Finset.sum_congr rfl (fun l hl => (if_pos (hin l hl)).symm)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by
          split_ifs
          · exact ENNReal.toReal_nonneg
          · exact le_rfl)
      _ < lam * DA := hD

/-- The padded-root prefix test reaching the cutoff bounds the wavelength score of each
padded descendant at the wavelength. -/
theorem aux_lfgc_clause1_pad {d : ℕ} (m k : ℕ) (lam : ℝ) (buffer k0 e1 : ℕ) (hb : buffer = 1)
    (hk0 : k0 = 1) (he1 : e1 = 1)
    (Ds : ℕ → SpatialCoordinates d → ENNReal)
    (cen : ∀ D : ℕ, (Fin D → OddGridIndex d 1) → SpatialCoordinates d)
    (h : ∀ (D : ℕ) (pword : Fin D → OddGridIndex d 1), k0 ≤ D →
      (∑ j ∈ Finset.Icc ((k : ℤ) - (e1 : ℤ) - (buffer : ℤ))
          (min ((m + k : ℕ) : ℤ) ((k : ℤ) - (e1 : ℤ) + (D : ℤ) + (buffer : ℤ))),
          (if 0 ≤ ((m + k : ℕ) : ℤ) - j then
            (Ds (((m + k : ℕ) : ℤ) - j).toNat ((3 : ℝ) ^ (m + k) • cen D pword)).toReal
          else 0)) < lam * D) :
    ∀ (D : ℕ) (pword : Fin D → OddGridIndex d 1), D = m + 1 →
      (Ds 0 ((3 : ℝ) ^ (m + k) • cen D pword)).toReal ≤ lam * (D : ℝ) := by
  subst hb hk0 he1
  intro D pword hD
  have hlt := h D pword (by omega)
  have hmem : ((m + k : ℕ) : ℤ) ∈ Finset.Icc ((k : ℤ) - ((1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))
      (min ((m + k : ℕ) : ℤ) ((k : ℤ) - ((1 : ℕ) : ℤ) + (D : ℤ) + ((1 : ℕ) : ℤ))) := by
    simp only [Finset.mem_Icc]
    omega
  have hle := Finset.single_le_sum (f := fun j : ℤ => if 0 ≤ ((m + k : ℕ) : ℤ) - j then
      (Ds (((m + k : ℕ) : ℤ) - j).toNat ((3 : ℝ) ^ (m + k) • cen D pword)).toReal else 0)
    (fun j _ => by
      split_ifs
      · exact ENNReal.toReal_nonneg
      · exact le_rfl) hmem
  simp only [sub_self, le_refl, if_true, Int.toNat_zero] at hle
  exact (hle.trans_lt hlt).le

/-- The padded-root coarse ellipticity test in its reference gives the padded lower bound. -/
theorem aux_lfgc_clause1_ell {d : ℕ} [NeZero d] (I : Paper.in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Hu : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N k : ℕ) (z zc : SpatialCoordinates d) (r rc : ℝ)
    (hrc : 0 < rc) (sigma cell ref : ℝ)
    (h : cell ≤ I.lam zc rc hrc (cutoffPositiveCoefficient M Hu omega N zc hrc) zc rc sigma 2 / ref)
    (hzc : zc = z) (hrc3 : rc = 3 * r)
    (href : ref = aux_in_deterministic_onestep_sref M Hu omega N ((k : ℤ) - 1) z) :
    ∀ h3 : 0 < 3 * r,
      cell * aux_in_deterministic_onestep_sref M Hu omega N ((k : ℤ) - 1) z ≤
        I.lam z (3 * r) h3 (cutoffPositiveCoefficient M Hu omega N z h3) z (3 * r) sigma 2 := by
  subst hzc hrc3 href
  intro _h3
  have hs := aux_in_deterministic_onestep_sref_pos M Hu omega N ((k : ℤ) - 1) zc
  rw [le_div_iff₀ hs] at h
  exact h

/-- The retained prefix at a nonnegative level is the partial sum of the first layers. -/
theorem aux_lfgc_clause1_retained {d : ℕ} (omega : BilateralField d) (k : ℕ)
    (z : SpatialCoordinates d) :
    (∑ i ∈ Finset.Ico (0 : ℤ) (k : ℤ), omega (-i) z) =
      ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z := by
  rw [show (Finset.Ico (0 : ℤ) (k : ℤ)) = (Finset.range k).map
      ⟨(Nat.cast : ℕ → ℤ), Nat.cast_injective⟩ by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h0, hj⟩
      exact ⟨x.toNat, by omega, by omega⟩
    · rintro ⟨y, hy, rfl⟩
      omega]
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]

/-- The cell reference written through the annealed normalization is the reference scalar. -/
theorem aux_lfgc_clause1_s_eq {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Hu : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (m k : ℕ)
    (z : SpatialCoordinates d) :
    Real.exp (((m : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M m /
      (Real.exp ((((m + k : ℕ) : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M (m + k)) *
        Real.exp ((Hu omega) z + ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z) =
      aux_in_deterministic_onestep_sref M Hu omega (m + k) k z := by
  unfold aux_in_deterministic_onestep_sref
  have hNk : ((m + k : ℕ) : ℤ) - (k : ℤ) = (m : ℤ) := by push_cast; ring
  have hkpos : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  simp only [hNk, Int.toNat_natCast, if_pos hkpos, aux_lfgc_clause1_retained]

/-- The padded-root reference at the padded level is the reference scalar one level up. -/
theorem aux_lfgc_clause1_ref_pad {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Hu : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (m k e : ℕ)
    (he : e = 1) (z : SpatialCoordinates d) :
    (let kappa := fun J : ℕ =>
        Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
     let retained := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
        if 0 ≤ j then ∑ i ∈ Finset.Ico (0 : ℤ) j, om (-i) w
        else -∑ i ∈ Finset.Ico j (0 : ℤ), om (-i) w
     kappa (((m + k : ℕ) : ℤ) - ((k : ℤ) - (e : ℤ))).toNat / kappa (m + k) *
        Real.exp (Hu omega z + retained ((k : ℤ) - (e : ℤ)) z omega)) =
      aux_in_deterministic_onestep_sref M Hu omega (m + k) ((k : ℤ) - 1) z := by
  subst he
  rfl

/-- **Clause 1 assembly.** The finite good-event tests at a cell, on the pinned carrier, give
eq:mfd-finite-good-holder for every bounded-source solution on any parent containing the
padded cell, in the form used by Lemma lem-finite-good-cell. -/
theorem lfgc_clause1_assembly
    (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d) (alpha sigma cell eps lam Cfin delta1 : ℝ)
    (hLH : aux_lfgc_clause1_spec d I alpha sigma cell eps lam Cfin delta1)
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (response : in_responses d model)
    (hdelta : model.delta ≤ delta1)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (Fs Praw Rraw Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (rawGood : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (omega : BilateralField d)
    (hC1 : ∀ (N i : ℕ) (x : SpatialCoordinates d),
      eta N omega i x = omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • x))
    (hC2 : ∀ N, primitive_scores d model sigma eps (eta N omega)
      (fun m z => Fs N m z omega) (fun m z => Praw N m z omega)
      (fun m z => Rraw N m z omega) (fun m z => Draw N m z omega)
      (fun m z => Z N m z omega) (fun m z => rawGood N m z omega))
    (hC4 : Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)))
    (hC3 : ∀ (N n : ℕ) (y : SpatialCoordinates d), Draw N n y omega ≠ ⊤)
    (en ns : ℕ) (self padRoot : Fin en) (selfShift : Fin ns) (enDepth : Fin en → ℕ)
    (shift : Fin ns → SpatialCoordinates d) (hself : enDepth self = 0)
    (hselfShift : shift selfShift = 0) (hpadDepth : enDepth padRoot = 1)
    (buffer k0 : ℕ) (hbuffer1 : buffer = 1) (hk01 : k0 = 1)
    (m k : ℕ) (z : SpatialCoordinates d) (infrared : Bool)
    (hFtest : Fs (m + k) (m + enDepth padRoot) ((3 : ℝ) ^ (m + k) •
      (z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth padRoot) • shift selfShift)) omega ≤ 1)
    (hPreSelf : ∀ (DA : ℕ) (dword : Fin DA → OddGridIndex d 1), k0 ≤ DA →
      (∑ j ∈ Finset.Icc ((k : ℤ) - (enDepth self : ℤ) - (buffer : ℤ))
          (min ((m + k : ℕ) : ℤ) ((k : ℤ) - (enDepth self : ℤ) + (DA : ℤ) + (buffer : ℤ))),
          (if 0 ≤ ((m + k : ℕ) : ℤ) - j then
            Z (m + k) (((m + k : ℕ) : ℤ) - j).toNat ((3 : ℝ) ^ (m + k) •
              descendantCenter 1
                (z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth self) • shift selfShift)
                ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth self) DA dword) omega else 0)) <
        lam * DA ∧
      (∑ j ∈ Finset.Icc ((k : ℤ) - (enDepth self : ℤ) - (buffer : ℤ))
          (min ((m + k : ℕ) : ℤ) ((k : ℤ) - (enDepth self : ℤ) + (DA : ℤ) + (buffer : ℤ))),
          (if 0 ≤ ((m + k : ℕ) : ℤ) - j then
            (Draw (m + k) (((m + k : ℕ) : ℤ) - j).toNat ((3 : ℝ) ^ (m + k) •
              descendantCenter 1
                (z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth self) • shift selfShift)
                ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth self) DA dword) omega).toReal
          else 0)) < lam * DA)
    (hPrePad : ∀ (D : ℕ) (pword : Fin D → OddGridIndex d 1), k0 ≤ D →
      (∑ j ∈ Finset.Icc ((k : ℤ) - (enDepth padRoot : ℤ) - (buffer : ℤ))
          (min ((m + k : ℕ) : ℤ) ((k : ℤ) - (enDepth padRoot : ℤ) + (D : ℤ) + (buffer : ℤ))),
          (if 0 ≤ ((m + k : ℕ) : ℤ) - j then
            (Draw (m + k) (((m + k : ℕ) : ℤ) - j).toNat ((3 : ℝ) ^ (m + k) •
              descendantCenter 1
                (z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth padRoot) • shift selfShift)
                ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth padRoot) D pword) omega).toReal
          else 0)) < lam * D)
    (zc : SpatialCoordinates d) (rc : ℝ) (hrc : 0 < rc) (ref : ℝ)
    (hEll : cell ≤ I.lam zc rc hrc (cutoffPositiveCoefficient model
        (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
        omega (m + k) zc hrc) zc rc sigma 2 / ref)
    (hzc : zc = z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth padRoot) • shift selfShift)
    (hrc3 : rc = (3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth padRoot)
    (href : ref =
      (let kappa := fun J : ℕ =>
          Real.exp (((J : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
       let retained := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
          if 0 ≤ j then ∑ i ∈ Finset.Ico (0 : ℤ) j, om (-i) w
          else -∑ i ∈ Finset.Ico j (0 : ℤ), om (-i) w
       kappa (((m + k : ℕ) : ℤ) - ((k : ℤ) - (enDepth padRoot : ℤ))).toNat / kappa (m + k) *
          Real.exp ((if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
            omega zc + retained ((k : ℤ) - (enDepth padRoot : ℤ)) zc omega)))
    (zP : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (hsub : Metric.closedBall z (3 * (3 : ℝ) ^ (-(k : ℤ)) / 2) ⊆
      (centeredCube zP R hR : Set (SpatialCoordinates d))) :
    ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), Measurable F → 0 ≤ Kf →
      (∀ x ∈ centeredCube zP R hR, |F x| ≤ Kf) →
      ∀ u : weakSobolevGraph (centeredCube zP R hR),
        (∀ psi : killedSobolevGraph (centeredCube zP R hR),
          @sobolevCoefficientForm d (centeredCube zP R hR)
            (cutoffPositiveCoefficient model
              (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
              omega (m + k) zP hR)
            (u : SobolevData (centeredCube zP R hR)) (psi : SobolevData (centeredCube zP R hR)) =
            ∫ x in (centeredCube zP R hR : Set (SpatialCoordinates d)),
              F x * (psi : SobolevData (centeredCube zP R hR)).1 x) →
        ∃ (U : SpatialCoordinates d → ℝ) (c : ℝ),
          ContinuousOn U (closedCube z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) :
            Set (SpatialCoordinates d)) ∧
          ((fun x => (u : SobolevData (centeredCube zP R hR)).1 x) =ᵐ[volume.restrict
            (centeredCube z ((3 : ℝ) ^ (-(k : ℤ))) (by positivity) :
              Set (SpatialCoordinates d))] U) ∧
          @IsHolderOn d alpha
            (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
            (fun x => U (z + (3 : ℝ) ^ (-(k : ℤ)) • x) - c) ∧
          @cAlphaNorm d alpha
            (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
            (fun x => U (z + (3 : ℝ) ^ (-(k : ℤ)) • x) - c) ≤
            Cfin * ((3 : ℝ) ^ (-(k : ℤ))) ^ (((2 : ℝ) - (d : ℝ)) / 2) *
                (Real.exp (((m : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
                    SubdiffusiveProcess.CoarseGrainingVocab.ahom model m /
                  (Real.exp ((((m + k : ℕ) : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
                    SubdiffusiveProcess.CoarseGrainingVocab.ahom model (m + k)) *
                  Real.exp (((if infrared then H else
                    (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega) z +
                    ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z)) ^ (-(1 : ℝ) / 2) *
                Real.sqrt (@sobolevCoefficientForm d (centeredCube zP R hR)
                  (cutoffPositiveCoefficient model
                    (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
                    omega (m + k) zP hR)
                  (u : SobolevData (centeredCube zP R hR))
                  (u : SobolevData (centeredCube zP R hR))) +
              Cfin * ((3 : ℝ) ^ (-(k : ℤ))) ^ (2 : ℝ) *
                (Real.exp (((m : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
                    SubdiffusiveProcess.CoarseGrainingVocab.ahom model m /
                  (Real.exp ((((m + k : ℕ) : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
                    SubdiffusiveProcess.CoarseGrainingVocab.ahom model (m + k)) *
                  Real.exp (((if infrared then H else
                    (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega) z +
                    ∑ j ∈ Finset.range k, omega (-(j : ℤ)) z))⁻¹ * Kf := by
  intro F Kf hF hKf hbound u heq
  set Hu : BilateralField d → C(SpatialCoordinates d, ℝ) :=
    if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) with hHu
  have hIR : Tendsto (infraredPartialSum omega) atTop (nhds (Hu omega)) ∨ Hu = 0 :=
    aux_lfgc_clause1_hIR H omega hC4 infrared
  have hPS := hC2 (m + k)
  have hZ0 : ∀ (n : ℕ) (y : SpatialCoordinates d), 0 ≤ Z (m + k) n y omega := by
    intro n y
    obtain ⟨_, _, _, _, _, _, _, _, _, hZ, _⟩ := hPS
    exact (hZ n y).2.1
  have hrS : (3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth self = (3 : ℝ) ^ (-(k : ℤ)) := by
    rw [hself, pow_zero, mul_one]
  have hzP : z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth padRoot) • shift selfShift = z := by
    rw [hselfShift, smul_zero, add_zero]
  have hrP : (3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth padRoot = 3 * (3 : ℝ) ^ (-(k : ℤ)) := by
    rw [hpadDepth, pow_one, mul_comm]
  have hpre0 := aux_lfgc_clause1_pre m k lam buffer k0 (enDepth self) hbuffer1 hk01 hself
    (fun n y => Z (m + k) n y omega) hZ0 (fun n y => Draw (m + k) n y omega)
    (fun DA dword => descendantCenter 1
      (z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth self) • shift selfShift)
      ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth self) DA dword) hPreSelf
  simp only [hselfShift, smul_zero, add_zero, hrS] at hpre0
  have hpad0 := aux_lfgc_clause1_pad m k lam buffer k0 (enDepth padRoot) hbuffer1 hk01 hpadDepth
    (fun n y => Draw (m + k) n y omega)
    (fun D pword => descendantCenter 1
      (z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth padRoot) • shift selfShift)
      ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth padRoot) D pword) hPrePad
  simp only [hselfShift, smul_zero, add_zero, hrP] at hpad0
  have hF1 : Fs (m + k) (m + 1) ((3 : ℝ) ^ (m + k) • z) omega ≤ 1 := by
    rw [hzP, hpadDepth] at hFtest
    exact hFtest
  have hlayer := aux_lfgc_clause1_layer model sigma eps (eta (m + k) omega) omega m k
    (hC1 (m + k)) _ _ _ _ _ _ hPS z hF1
  have hzc' : zc = z := hzc.trans hzP
  have hrc' : rc = 3 * (3 : ℝ) ^ (-(k : ℤ)) := hrc3.trans hrP
  have href' : ref = aux_in_deterministic_onestep_sref model Hu omega (m + k) ((k : ℤ) - 1) z := by
    rw [href, hzc']
    exact aux_lfgc_clause1_ref_pad model Hu omega m k (enDepth padRoot) hpadDepth z
  have hell := aux_lfgc_clause1_ell I model Hu omega (m + k) k z zc ((3 : ℝ) ^ (-(k : ℤ))) rc hrc
    sigma cell ref hEll hzc' hrc' href'
  obtain ⟨U, c, hU, htie, hHol, hnorm⟩ := hLH model response hdelta Hu omega m k z
    (eta (m + k) omega) (hC1 (m + k)) hIR _ _ _ _ _ _ hPS (fun n y => hC3 (m + k) n y)
    hpre0 hpad0 hlayer hell zP R hR hsub F Kf hF hKf hbound u heq
  refine ⟨U, c, hU, htie, hHol, ?_⟩
  rw [aux_lfgc_clause1_s_eq model Hu omega m k z]
  exact hnorm

end Paper
