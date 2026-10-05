module

public import SubdiffusiveProcess.Paper.conv_represented_catalogue_original
public import Mathlib
public import SubdiffusiveProcess.Paper.conv_represented_env_interface
public import SubdiffusiveProcess.Paper.conv_represented_estimates_transfer
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_sources
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_traces_buffered
public import SubdiffusiveProcess.Paper.conv_represented_env_interface_grids
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_coercivity_clause
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_source_clause
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_cell_clause
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_source_response
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_cell_response
public import SubdiffusiveProcess.Paper.conv_represented_catalogue_smooth_class
public import SubdiffusiveProcess.Paper.conv_represented_tight_of_bounded
public import SubdiffusiveProcess.Paper.model_triadic_cube_coercivity
public import SubdiffusiveProcess.Paper.model_cube_coarse_bank
public import SubdiffusiveProcess.Paper.model_cube_trace_bound
public import SubdiffusiveProcess.Paper.conv_represented_grid_clause_bank

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Actual finite-cutoff catalogue, preserving the given rational grid coverage. -/
theorem conv_represented_catalogue_original_grids
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Pin : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (alpha eta beta t : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (heta : 0 < eta) (hAeta : 1 + eta < 2 * alpha) (hb : 1 / 2 < beta) (hba : beta < alpha) :
    ∃ δ0 : ℝ, 0 < δ0 ∧
      ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H),
        M.delta ≤ δ0 →
      ∀ (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (Sspace : ∀ i, ResponseSpace (centeredCube (z i) (r i) (hr i)))
        (_hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
        (root : ℕ) (origin : ℕ → SpatialCoordinates d) (gridRoot : ℕ → ℕ)
        (_hunit : (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) ⊆
          (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
        (_hsub : ∀ j, (centeredCube (z j) (r j) (hr j) : Set (SpatialCoordinates d)) ⊆
          (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)))
        (_hrat : ∀ (j : ℕ) (c : Fin d), ∃ q : ℚ, z j c = (q : ℝ))
        (_htri : ∀ j, ∃ m : ℤ, r j = (3 : ℝ) ^ m)
        (_hcomp : ∀ (z' : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
          (∀ c : Fin d, ∃ q : ℚ, z' c = (q : ℝ)) → (∃ m : ℤ, r' = (3 : ℝ) ^ m) →
          (centeredCube z' r' hr' : Set (SpatialCoordinates d)) ⊆
            (centeredCube (z root) (r root) (hr root) : Set (SpatialCoordinates d)) →
          ∃ j, z j = z' ∧ r j = r')
        (_horat : ∀ (g : ℕ) (c : Fin d), ∃ q : ℚ, origin g c = (q : ℝ))
        (_hgrid : ∀ (j : ℕ) (o : SpatialCoordinates d), (∀ c : Fin d, ∃ q : ℚ, o c = (q : ℝ)) →
          ∃ g : ℕ, gridRoot g = j ∧ origin g = o)
        (NE NF : ℕ → ℕ), StrictMono NE → StrictMono NF →
      conv_represented_env_interface_grids d hd M H z r hr Sspace NE NF alpha eta E beta t := by
  classical
  have hbeta : beta ∈ Set.Ioo (1 / 2 : ℝ) 1 := ⟨hb, hba.trans ha1⟩
  obtain ⟨δ1, hδ1, hcoerc⟩ := model_triadic_cube_coercivity d hd E Pin Sob
  obtain ⟨δ2, hδ2, hsrc⟩ := conv_represented_catalogue_source_clause d hd E Pin X W Cp Sob t alpha
    ht htd ha0 ha1
  obtain ⟨δ3, hδ3, hcell⟩ := conv_represented_catalogue_cell_clause d hd E Pin X W Cp Sob t alpha
    ht htd ha0 ha1
  obtain ⟨δ4, hδ4, hcube⟩ := model_cube_coarse_bank d hd E beta 1 hbeta le_rfl
  obtain ⟨Cext, hCext, hI⟩ := model_cube_trace_bound d hd E X Sob beta hbeta
  obtain ⟨δ5, hδ5, hgridb⟩ :=
    conv_represented_grid_clause_bank d hd E X Sob eta 1 beta heta le_rfl hbeta
  refine ⟨min (min (min δ1 δ2) (min δ3 δ4)) δ5,
    lt_min (lt_min (lt_min hδ1 hδ2) (lt_min hδ3 hδ4)) hδ5, ?_⟩
  intro M Rm Sreg It H hH hδ z r hr Sspace hS root origin gridRoot hunit hsub hrat htri hcomp
    horat hgrid NE NF hNE hNF
  have hδ1' : M.delta ≤ δ1 := hδ.trans
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hδ2' : M.delta ≤ δ2 := hδ.trans
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hδ3' : M.delta ≤ δ3 := hδ.trans
    ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ4' : M.delta ≤ δ4 := hδ.trans
    ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδ5' : M.delta ≤ δ5 := hδ.trans (min_le_right _ _)
  -- deterministic catalogue: sources, traces
  choose Dcat hDc fcat hDdense hf3 hf4 using fun i =>
    conv_represented_catalogue_sources d (z i) (r i) (hr i)
  have hDcI : ∀ i, Countable (Dcat i) := hDc
  obtain ⟨theta, thetaH1, hth5, hth6, hth7, hth8, hth9, hth10⟩ :=
    conv_represented_catalogue_traces_buffered d hd beta alpha hb hba ha1 ℕ z r hr
      (fun i => ↥(Dcat i)) fcat (fun j g => (hf3 j g).1)
  -- coercivity (clause H)
  have hrad : ∀ i, r i ≤ 1 ∨ ∃ k : ℕ, 0 < k ∧ r i = (3 : ℝ) ^ k := by
    intro i
    obtain ⟨m, hm⟩ := htri i
    by_cases hm0 : m ≤ 0
    · left
      rw [hm]
      exact zpow_le_one_of_nonpos₀ (by norm_num) hm0
    · right
      refine ⟨m.toNat, by omega, ?_⟩
      rw [hm, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  obtain ⟨Kc, Cbc, hCbc, hKcm, hKcn, hKcae, hKcb, hKctight⟩ :=
    hcoerc M Rm H hH hδ1' z r hr hrad
  have hHcl := fun i => conv_represented_catalogue_coercivity_clause d hd M H (z i) (r i) (hr i)
    (Sspace i) (hS i) (Kc i) (hKcm i) (hKcn i) (hKcae i) (Cbc i)
    (fun N => by simpa only [ENNReal.ofReal_one] using hKcb i N)
  choose KH BH GH hGHm hGHnull hKHm hKHn hBH0 hKHb hKH using hHcl
  -- source and cell growth clauses
  choose Kgs Khs Cbgs Cbhs Gs hGsm hGsnull hCbgs hCbhs hKgsm hKgsn hKgsb hKhsm hKhsn hKhsb hKs
    using fun i => hsrc M Rm Sreg It H hH hδ2' (z i) (r i) (hr i) (Sspace i) (hS i)
  choose srcRepB hsrcB using fun i =>
    aux_conv_represented_catalogue_original_K M H (z i) (r i) (hr i) (Sspace i) (Dcat i)
      (fcat i) (hf3 i) t alpha (Kgs i) (Khs i) (Gs i) (hKs i)
  choose Kgc Khc Cbgc Cbhc Gc hGcm hGcnull hCbgc hCbhc hKgcm hKgcn hKgcb hKhcm hKhcn hKhcb hLc
    using fun i => hcell M Rm Sreg It H hH hδ3' (z i) (r i) (hr i)
  choose ucellB hucellB using fun i =>
    aux_conv_represented_catalogue_original_L M H (z i) (r i) (hr i) (theta i) (thetaH1 i)
      (hth5 i) t alpha (Kgc i) (Khc i) (Gc i) (hLc i)
  -- coarse constants and grid constants
  obtain ⟨CbL, hCbL0, hLamm, hlamm, hLampos, hLambank, hLamtight⟩ :=
    hcube M Rm H hH hδ4' ℕ z r hr htri
  obtain ⟨Zg, Cbg, Ggrid, hCbg0, hZgm, hZgn, hZgb, hZgt, hGgm, hGgnull, hJ⟩ :=
    hgridb M Rm H hH hδ5' ℕ z r hr ℕ origin gridRoot
  clear hcoerc hsrc hcell hcube hgridb
  obtain ⟨κ, hκ⟩ := Countable.exists_injective_nat
    (aux_conv_represented_catalogue_original_Key (fun i => ↥(Dcat i)))
  -- tightness of the coercivity constants and the killed-space form of clause H
  have hKHtight : ∀ i (Ns : ℕ → ℕ), ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      (chaosSampleLaw M).toMeasure {β | Mb < KH i (Ns n) β} ≤ ENNReal.ofReal rho := by
    intro i Ns rho hrho
    obtain ⟨Mb, hMb⟩ := aux_conv_represented_tight_of_bounded_L1_bounded
      (chaosSampleLaw M).toMeasure
      (fun n => KH i (Ns n)) (fun n => hKHm i (Ns n)) (BH i) (hBH0 i) (fun n => by
        have := (hKHb i (Ns n)).2
        rw [ENNReal.ofReal_one, eLpNorm_one_eq_lintegral_enorm (hKHm i (Ns n)).aestronglyMeasurable] at this
        exact this) rho hrho
    refine ⟨Mb, fun n => le_trans (measure_mono ?_) (hMb n)⟩
    intro β hβ
    have hβ' : Mb < KH i (Ns n) β := hβ
    exact lt_of_lt_of_le hβ' (le_abs_self _)
  have hKHc : ∀ i N, ∀ β ∈ GH i, ∀ v : (Sspace i).space,
      ‖(v : SobolevData (centeredCube (z i) (r i) (hr i))).1‖ ^ 2 ≤
        KH i N β * responseForm (Sspace i)
          (cutoffPositiveCoefficient M H β N (z i) (hr i)) v v := by
    intro i N β hβ v
    have h := (hKH i N β hβ v).2
    have hnn : 0 ≤ volume.real (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd (z i) (r i) (hr i) threeQuarterOrder
          (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 :=
      mul_nonneg measureReal_nonneg (sq_nonneg _)
    exact le_trans (le_add_of_nonneg_right hnn) h
  -- cell responses: boundary class and the absolute trace estimate
  have hcellcls : ∀ i h, ContinuousOn (thetaH1 i h).toFun
      (closure (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d))) ∧
      IsCellBoundaryClass beta (z i) (r i) (thetaH1 i h).toFun := by
    intro i h
    have h1 := hth5 i h
    rw [h1.2]
    exact ⟨h1.1.continuous.continuousOn, conv_represented_catalogue_smooth_class beta
      (by linarith) (by linarith) (z i) (r i) (theta i h) h1.1⟩
  have hcellI : ∀ i h N β, cellDirichletInfimum (cutoffCoefficient M H β N)
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) (thetaH1 i h) ≤
      (Cext * (r i) ^ ((d : ℝ) - 2) *
        (cellBoundaryQuotientNorm beta (z i) (r i) (thetaH1 i h).toFun) ^ 2) *
        E.Lam (z i) (r i) (hr i) (cutoffPositiveCoefficient M H β N (z i) (hr i))
          (z i) (r i) ((beta - 1 / 2) / 4) 2 := by
    intro i h N β
    have := hI M H β N (z i) (r i) (hr i) (thetaH1 i h) (hcellcls i h).1 (hcellcls i h).2
    calc _ ≤ _ := this
      _ = _ := by ring
  have hcellc : ∀ i h, 0 ≤ Cext * (r i) ^ ((d : ℝ) - 2) *
      (cellBoundaryQuotientNorm beta (z i) (r i) (thetaH1 i h).toFun) ^ 2 := fun i h =>
    mul_nonneg (mul_nonneg hCext.le (Real.rpow_nonneg (hr i).le _)) (sq_nonneg _)
  have hLamT : ∀ i (Ns : ℕ → ℕ), ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      (chaosSampleLaw M).toMeasure {β |
      Mb < E.Lam (z i) (r i) (hr i) (cutoffPositiveCoefficient M H β (Ns n) (z i) (hr i))
        (z i) (r i) ((beta - 1 / 2) / 4) 2} ≤ ENNReal.ofReal rho := by
    intro i Ns rho hrho
    obtain ⟨Mb, hMb⟩ := hLamtight i rho hrho
    exact ⟨Mb, fun n => (hMb (Ns n)).1⟩
  have hd0 : 0 < d := lt_of_lt_of_le two_pos hd
  -- keyed constants and responses
  obtain ⟨const0, resp0, hC0, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hR0, hR1, hconstM, hconstN,
      hconstB, hresp0M, hresp0T⟩ :=
    aux_conv_represented_catalogue_original_keyed (chaosSampleLaw M).toMeasure
    (fun i => ↥(Dcat i)) κ hκ KH
    (fun j N β => E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
      (z j) (r j) ((beta - 1 / 2) / 4) 2)
    (fun j N β => (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β N (z j) (hr j))
      (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ)))
    Kgs Khs Kgc Khc Zg
    (fun i g N β => inverseResponse (Sspace i)
      (cutoffPositiveCoefficient M H β N (z i) (hr i))
      ((sobolevVolumeLoad g.val).comp (Sspace i).space.subtypeL))
    (fun i h N β => cellDirichletInfimum (cutoffCoefficient M H β N)
      (centeredCube (z i) (r i) (hr i) : Set (SpatialCoordinates d)) (thetaH1 i h))
    ⟨hKHm, hLamm, hlamm, hKgsm, hKhsm, hKgcm, hKhcm, hZgm⟩
    ⟨hKHn, fun j N β => (hLampos j N β).1.le, fun j N β => (hLampos j N β).2.le,
      hKgsn, hKhsn, hKgcn, hKhcn, hZgn⟩
    ⟨fun j => ⟨BH j, hBH0 j, hKHb j⟩,
     fun j => ⟨CbL j, hCbL0 j, fun N => (hLambank j N 1 one_pos le_rfl).1⟩,
     fun j => ⟨CbL j, hCbL0 j, fun N => (hLambank j N 1 one_pos le_rfl).2⟩,
     fun j => ⟨Cbgs j, hCbgs j, hKgsb j⟩, fun j => ⟨Cbhs j, hCbhs j, hKhsb j⟩,
     fun j => ⟨Cbgc j, hCbgc j, hKgcb j⟩, fun j => ⟨Cbhc j, hCbhc j, hKhcb j⟩,
     fun g => ⟨Cbg g, hCbg0 g, fun N => hZgb g N 1 one_pos le_rfl⟩⟩
    (fun i g N => (conv_represented_catalogue_source_response d M H hH (z i) (r i) (hr i)
      (Sspace i) (KH i) (GH i) (hKHn i) (hKHc i) g.val (chaosSampleLaw M).toMeasure (hGHnull i)
      (fun n => n) (hKHtight i (fun n => n))).1 N)
    (fun i g Ns => (conv_represented_catalogue_source_response d M H hH (z i) (r i) (hr i)
      (Sspace i) (KH i) (GH i) (hKHn i) (hKHc i) g.val (chaosSampleLaw M).toMeasure (hGHnull i)
      Ns (hKHtight i Ns)).2.2.2)
    (fun i h N => (conv_represented_catalogue_cell_response d hd0 M H hH (z i) (r i) (hr i)
      (thetaH1 i h) (fun N β => E.Lam (z i) (r i) (hr i)
        (cutoffPositiveCoefficient M H β N (z i) (hr i)) (z i) (r i) ((beta - 1 / 2) / 4) 2)
      Set.univ _ (hcellc i h) (fun N β _ => hcellI i h N β) (chaosSampleLaw M).toMeasure
      (by simp) (fun n => n) (hLamT i (fun n => n))).1 N)
    (fun i h Ns => (conv_represented_catalogue_cell_response d hd0 M H hH (z i) (r i) (hr i)
      (thetaH1 i h) (fun N β => E.Lam (z i) (r i) (hr i)
        (cutoffPositiveCoefficient M H β N (z i) (hr i)) (z i) (r i) ((beta - 1 / 2) / 4) 2)
      Set.univ _ (hcellc i h) (fun N β _ => hcellI i h N β) (chaosSampleLaw M).toMeasure
      (by simp) Ns (hLamT i Ns)).2.2)
  -- the full-measure event
  obtain ⟨G0, hG0m, hG0null, hβGH, hβGs, hβGc, hβGg⟩ :=
    aux_conv_represented_catalogue_original_events (chaosSampleLaw M).toMeasure GH Gs Gc Ggrid
      hGHm hGsm hGcm hGgm hGHnull hGsnull hGcnull hGgnull
  -- the catalogue at the identity cutoff
  have hpin1 : ∀ (j n : ℕ) (β : BilateralField d), β ∈ G0 →
      const0 (κ (Sum.inr (Sum.inl j))) n β =
        E.Lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β n (z j) (hr j))
          (z j) (r j) ((beta - 1 / 2) / 4) 2 ∧
      const0 (κ (Sum.inr (Sum.inr (Sum.inl j)))) n β =
        (E.lam (z j) (r j) (hr j) (cutoffPositiveCoefficient M H β n (z j) (hr j))
          (z j) (r j) ((beta - 1 / 2) / 4) 2) ^ (-(1 : ℝ)) := fun j n β _ =>
    ⟨hC1 j n β, hC2 j n β⟩
  have hpin2 : ∀ (g n : ℕ) (β : BilateralField d), β ∈ G0 →
      const0 (κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl g))))))))) n β = Zg g n β := fun g n β _ => hC7 g n β
  have hJfin := hJ ℕ const0 (fun j => κ (Sum.inr (Sum.inl j)))
    (fun j => κ (Sum.inr (Sum.inr (Sum.inl j))))
    (fun g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (Sum.inl g))))))))) (fun N => N) G0 hpin1 hpin2
  have hcoreid : aux_conv_represented_estimates_transfer_core d hd M H (fun N => N) ℕ root z r hr
      Sspace Dcat fcat (fun _ => ℕ) theta thetaH1
      (fun j g N β => responseSolution (Sspace j)
        (cutoffPositiveCoefficient M H β N (z j) (hr j))
        ((sobolevVolumeLoad g.val).comp (Sspace j).space.subtypeL))
      srcRepB ucellB Cext beta alpha eta t {1} E ℕ resp0 const0 G0
      (fun j => κ (Sum.inl j)) (fun j => κ (Sum.inr (Sum.inl j)))
      (fun j => κ (Sum.inr (Sum.inr (Sum.inl j))))
      (fun i g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inl ⟨i, g⟩))))))))))
      (fun i g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩)))))
      (fun i g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩))))))
      (fun i h => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inr (i, h)))))))))))
      (fun i h => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h))))))))
      (fun i h => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h)))))))))
      ℕ origin gridRoot
      (fun g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl g)))))))))  := by
    unfold aux_conv_represented_estimates_transfer_core
    refine ⟨⟨ht, htd⟩, ⟨ha1, heta, hAeta⟩, ⟨hb, hba⟩, hCext, ?_, fun a b hab => hab, hH, hG0m,
      hG0null, hsub, hrat, htri, hcomp, horat, fun j => hgrid j (z j) (hrat j), hS, hDdense, hf3,
      hf4, hth5, hth6, hth7, hth8, hth9, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      rw [Finset.mem_singleton] at hp
      rw [hp]; norm_num
    · exact fun i N => hconstM i N
    · intro i p hp
      rw [Finset.mem_singleton] at hp
      subst hp
      exact hconstB i
    · exact fun i β _ N => hconstN i N β
    · intro j N β hβ
      refine ⟨fun g => ⟨rfl, (hsrcB j g N β (hβGs β hβ j)).1, hR0 j g N β⟩,
        fun h => ⟨?_, ?_, ?_, ?_, hR1 j h N β⟩⟩
      · exact (hucellB j h N β (hβGc β hβ j)).1
      · exact (hucellB j h N β (hβGc β hβ j)).2.1
      · exact (hucellB j h N β (hβGc β hβ j)).2.2.1
      · exact (hucellB j h N β (hβGc β hβ j)).2.2.2.1
    · exact fun j N β hβ => ⟨hC1 j N β, hC2 j N β⟩
    · intro j N β hβ v
      have := hKH j N β (hβGH β hβ j) v
      exact ⟨this.1, this.2.trans (le_of_eq (by rw [hC0 j N β]))⟩
    · intro j N β hβ e hec hcls
      have := hI M H β N (z j) (r j) (hr j) e hec hcls
      exact this.trans (le_of_eq (by rw [hC1 j N β]))
    · exact fun g n k j β hβ => hJfin g n k j β hβ (hβGg β hβ)
    · intro j g N β hβ
      obtain ⟨_, hgr, hco, hfr, hho, hno⟩ := hsrcB j g N β (hβGs β hβ j)
      refine ⟨fun x hx rr h1 h2 => (hgr x hx rr h1 h2).trans
        (ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hC3 j g N β]))), hco, hfr, hho,
        hno.trans (le_of_eq (by rw [hC4 j g N β]))⟩
    · intro j h N β hβ
      obtain ⟨_, _, _, _, hgr, hho, hno⟩ := hucellB j h N β (hβGc β hβ j)
      refine ⟨fun x hx rr h1 h2 => (hgr x hx rr h1 h2).trans
        (ENNReal.ofReal_le_ofReal (le_of_eq (by rw [hC5 j h N β]))), hho,
        hno.trans (le_of_eq (by rw [hC6 j h N β]))⟩
  refine ⟨resp0, const0, root, hunit, Dcat, hDc, fcat, theta, thetaH1,
    (fun j g n β => responseSolution (Sspace j)
      (cutoffPositiveCoefficient M H β (NE n) (z j) (hr j))
      ((sobolevVolumeLoad g.val).comp (Sspace j).space.subtypeL)),
    (fun j g n β => responseSolution (Sspace j)
      (cutoffPositiveCoefficient M H β (NF n) (z j) (hr j))
      ((sobolevVolumeLoad g.val).comp (Sspace j).space.subtypeL)),
    (fun j g n β => srcRepB j g (NE n) β), (fun j g n β => srcRepB j g (NF n) β),
    (fun j h n β => ucellB j h (NE n) β), (fun j h n β => ucellB j h (NF n) β),
    Cext, beta, t, E,
    (fun j => κ (Sum.inl j)),
    (fun j => κ (Sum.inr (Sum.inl j))),
    (fun j => κ (Sum.inr (Sum.inr (Sum.inl j)))),
    (fun i g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩)))))))))),
    (fun i g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩))))),
    (fun i g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨i, g⟩)))))),
    (fun i h => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, h))))))))))),
    (fun i h => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h)))))))),
    (fun i h => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, h))))))))),
    origin, gridRoot,
    (fun g => κ (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl g))))))))), G0, G0, ⟨rfl, rfl, rfl⟩, hgrid, ?_, ?_, ?_, ?_⟩
  · exact fun i n => ⟨hresp0M i (NE n), hresp0M i (NF n)⟩
  · intro i rho hrho
    obtain ⟨M1, hM1⟩ := hresp0T NE i rho hrho
    obtain ⟨M2, hM2⟩ := hresp0T NF i rho hrho
    refine ⟨max M1 M2, fun n => ⟨le_trans (measure_mono ?_) (hM1 n),
      le_trans (measure_mono ?_) (hM2 n)⟩⟩
    · intro β hβ
      have hβ' : max M1 M2 < |resp0 i (NE n) β| := hβ
      exact lt_of_le_of_lt (le_max_left _ _) hβ'
    · intro β hβ
      have hβ' : max M1 M2 < |resp0 i (NF n) β| := hβ
      exact lt_of_le_of_lt (le_max_right _ _) hβ'
  · exact hth10
  · let : ∀ i, Countable (Dcat i) := hDc
    exact ⟨aux_conv_represented_catalogue_original_shift d hd M H NE hNE ℕ root z r hr Sspace
      Dcat fcat (fun _ => ℕ) theta thetaH1 _ srcRepB ucellB Cext beta alpha eta t {1} E ℕ resp0
      const0 G0 _ _ _ _ _ _ _ _ _ ℕ origin gridRoot _ hcoreid,
      aux_conv_represented_catalogue_original_shift d hd M H NF hNF ℕ root z r hr Sspace
      Dcat fcat (fun _ => ℕ) theta thetaH1 _ srcRepB ucellB Cext beta alpha eta t {1} E ℕ resp0
      const0 G0 _ _ _ _ _ _ _ _ _ ℕ origin gridRoot _ hcoreid⟩

end SubdiffusiveProcess.Paper
