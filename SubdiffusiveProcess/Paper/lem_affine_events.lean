module

public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.Lane3.Forms
public import SubdiffusiveProcess.Lane3.Subdivision
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Lane4.Carriers
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.conv_represented_estimates
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.prop_growth_large_root
public import SubdiffusiveProcess.Paper.killed_continuous_boundary_zero
public import SubdiffusiveProcess.Paper.candidate_represented_source_bank
public import SubdiffusiveProcess.Paper.in_deterministic
public import SubdiffusiveProcess.Geometry.OddGrid
public import Homogenization.Book.Ch02.MultiscaleEllipticity

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper
/-- The four constants of the affine lemma can be enlarged to one common constant `≥ 1`. -/
theorem aux_lem_affine_exists_Cin (a b c e : ℝ) :
    ∃ Cin : ℝ, 1 ≤ Cin ∧ a ≤ Cin ∧ b ≤ Cin ∧ c ≤ Cin ∧ e ≤ Cin :=
  ⟨max (max (max (max 1 a) b) c) e, le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_left _ _))),
    le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (le_max_right _ _))),
    le_max_of_le_left (le_max_of_le_left (le_max_right _ _)),
    le_max_of_le_left (le_max_right _ _), le_max_right _ _⟩

/-- The Poincaré constant `Pin.C^2 * ((disc s 2 / disc 1 1) * (1/5))⁻¹` is nonnegative. -/
theorem aux_lem_affine_KP_nonneg (s Pc : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) :
    0 ≤ Pc ^ 2 * ((Homogenization.Book.Ch02.geometricDiscount s 2 /
      Homogenization.Book.Ch02.geometricDiscount 1 1) * (1 / 5 : ℝ))⁻¹ := by
  have h1 : 0 < Homogenization.Book.Ch02.geometricDiscount s 2 := by
    unfold Homogenization.Book.Ch02.geometricDiscount
    have : Real.rpow (3 : ℝ) (-s * 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [hs.1])
    linarith
  have h2 : 0 < Homogenization.Book.Ch02.geometricDiscount 1 1 := by
    unfold Homogenization.Book.Ch02.geometricDiscount
    have : Real.rpow (3 : ℝ) (-1 * 1) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    linarith
  positivity

/-- The constant zero has zero `c2Norm` on every set. -/
theorem aux_lem_affine_events_c2_zero {d : ℕ} (S : Set (SpatialCoordinates d)) :
    c2Norm S (fun _ => (0 : ℝ)) = 0 := by
  have hz : sSup {v : ℝ | ∃ x ∈ S, v = 0} = 0 := by
    apply le_antisymm
    · exact Real.sSup_le (by rintro v ⟨x, hx, rfl⟩; exact le_rfl) le_rfl
    · exact Real.sSup_nonneg (by rintro v ⟨x, hx, rfl⟩; exact le_rfl)
  simp only [c2Norm, abs_zero, fderiv_fun_const, fderiv_zero, Pi.zero_apply,
    ContinuousLinearMap.opNorm_zero, hz, add_zero]

/-- Arbitrary cube sizes are covered by the small and large radius growth estimates. -/
theorem aux_lem_affine_events_growth_input
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Poin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hb : beta ∈ Ioo (0 : ℝ) 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
        ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
        ∃ (K : ℕ → BilateralField d → ℝ) (C : ℝ),
          (∀ n, MemLp (K n) 1 (chaosSampleLaw M).toMeasure) ∧
          (∀ n, eLpNorm (K n) 1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ n, 1 ≤ K n om) ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ (n : ℕ) (f : SpatialCoordinates d → ℝ) (Kf : ℝ),
            ContDiff ℝ ∞ f → 0 ≤ Kf →
            (∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
              |f x| ≤ Kf) →
          ∀ u : killedSobolevGraph (centeredCube z r hr),
            (∀ psi : killedSobolevGraph (centeredCube z r hr),
              sobolevCoefficientForm (cutoffPositiveCoefficient M H om n z hr)
                u.val psi.val = ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
                  f x * psi.val.1 x) →
            ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
              ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
                volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U) ∧
              (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0) ∧
              IsHolderOn beta (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
              cAlphaNorm beta (closedCube z r hr : Set (SpatialCoordinates d)) U ≤ K n om * Kf := by
  obtain ⟨delta0, hd0, hG⟩ := prop_growth d hd I Poin X W Cp Sob
    ((d : ℝ) - 1 / 2) beta 1 (fun _ => 1) (by linarith) (by linarith) hb.1 hb.2
    (fun _ => le_rfl)
  obtain ⟨delta0', hd0', hG'⟩ := prop_growth_large_root d hd I Poin X W Cp Sob
    ((d : ℝ) - 1 / 2) beta 1 (fun _ => 1) (by linarith) (by linarith) hb.1 hb.2
    (fun _ => le_rfl)
  refine ⟨min delta0 delta0', lt_min hd0 hd0', ?_⟩
  intro M Rm Sreg It H hIR hdelta z r hr
  by_cases hr1 : r ≤ 1
  · obtain ⟨K, C, hmem, hnorm, hge, hsource⟩ :=
      hG M Rm Sreg It H hIR (hdelta.trans (min_le_left _ _)) z r hr hr1
    refine ⟨K, C 0, ?_, ?_, hge, ?_⟩
    · simpa only [ENNReal.ofReal_one] using hmem 0
    · simpa only [ENNReal.ofReal_one] using hnorm 0
    filter_upwards [hsource] with om hom
    intro n f Kf hf hKf hfbound u hsolve
    let uw : weakSobolevGraph (centeredCube z r hr) :=
      ⟨u.val, killedSobolevGraph_le_weakSobolevGraph u.property⟩
    have hsol : SolvesDirichlet (cutoffPositiveCoefficient M H om n z hr) f 0 uw := by
      refine ⟨?_, hsolve⟩
      simpa only [ZeroMemClass.coe_zero, sub_zero] using u.property
    have hzero : (((0 : weakSobolevGraph (centeredCube z r hr)).val.1) :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] (fun _ => 0) :=
      Lp.coeFn_zero _ _ _
    obtain ⟨U, hUc, hUrep, hUH, hUbound⟩ := (hom n f Kf hKf
      hf.continuous.measurable.aemeasurable hfbound (fun _ => 0) 0 contDiff_const
      (aux_lem_affine_events_c2_zero _).le 0 uw hzero hsol).2
    refine ⟨U, hUc, hUrep, ?_, hUH, ?_⟩
    · intro x hx
      apply killed_continuous_boundary_zero d z r hr u.val u.property U hUc hUrep x
      · have hc := frontier_subset_closure hx
        change x ∈ closure (Metric.ball z (r / 2)) at hc
        exact closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall hc
      · simpa only [(centeredCube z r hr).isOpen.interior_eq] using hx.2
    · simpa only [add_zero] using hUbound
  · push_neg at hr1
    obtain ⟨K, C, hmem, hnorm, hge, hsource⟩ :=
      hG' M Rm Sreg It H hIR (hdelta.trans (min_le_right _ _)) z r hr hr1
    refine ⟨K, C 0, ?_, ?_, hge, ?_⟩
    · simpa only [ENNReal.ofReal_one] using hmem 0
    · simpa only [ENNReal.ofReal_one] using hnorm 0
    filter_upwards [hsource] with om hom
    intro n f Kf hf hKf hfbound u hsolve
    let uw : weakSobolevGraph (centeredCube z r hr) :=
      ⟨u.val, killedSobolevGraph_le_weakSobolevGraph u.property⟩
    have hsol : SolvesDirichlet (cutoffPositiveCoefficient M H om n z hr) f 0 uw := by
      refine ⟨?_, hsolve⟩
      simpa only [ZeroMemClass.coe_zero, sub_zero] using u.property
    have hzero : (((0 : weakSobolevGraph (centeredCube z r hr)).val.1) :
        SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] (fun _ => 0) :=
      Lp.coeFn_zero _ _ _
    obtain ⟨U, hUc, hUrep, hUH, hUbound⟩ := (hom n f Kf hKf
      hf.continuous.measurable.aemeasurable hfbound (fun _ => 0) 0 contDiff_const
      (aux_lem_affine_events_c2_zero _).le 0 uw hzero hsol).2
    refine ⟨U, hUc, hUrep, ?_, hUH, ?_⟩
    · intro x hx
      apply killed_continuous_boundary_zero d z r hr u.val u.property U hUc hUrep x
      · have hc := frontier_subset_closure hx
        change x ∈ closure (Metric.ball z (r / 2)) at hc
        exact closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall hc
      · simpa only [(centeredCube z r hr).isOpen.interior_eq] using hx.2
    · simpa only [add_zero] using hUbound




/-- The disorder threshold of the growth bank (`prop_growth` for every cube size). -/
noncomputable def aux_lem_affine_events_growthDelta
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Poin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hb : beta ∈ Ioo (0 : ℝ) 1) : ℝ :=
  Classical.choose (aux_lem_affine_events_growth_input d hd I Poin X W Cp Sob beta hb)

theorem aux_lem_affine_events_growthDelta_pos
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Poin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hb : beta ∈ Ioo (0 : ℝ) 1) :
    0 < aux_lem_affine_events_growthDelta d hd I Poin X W Cp Sob beta hb :=
  (Classical.choose_spec (aux_lem_affine_events_growth_input d hd I Poin X W Cp Sob beta hb)).1



theorem lem_affine_events
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Poin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd)
    (beta : ℝ) (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
    (Sreg : in_6_16 d M) (It : in_iteration d M I Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hMH : InfraredCharacterization M H)
    (hdelta : M.delta ≤ aux_lem_affine_events_growthDelta d hd I Poin X W Cp Sob beta
      ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hbeta, hbeta1⟩)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (env : ℕ → Ω → BilateralField d)
    (hEnvMeas : ∀ n, Measurable (env n))
    (hEnvLaw : ∀ n, Measure.map (env n) P = (chaosSampleLaw M).toMeasure)
    (phi : ℕ → ℕ) (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (S : ResponseSpace (centeredCube Qcentre Qside hQside))
    (hS : S.space = killedSobolevGraph (centeredCube Qcentre Qside hQside))
    (GN : ℕ → BilateralField d →
      DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ] DomainL2 (centeredCube Qcentre Qside hQside))
    (hGN : ∀ N omega f, GN N omega f =
      (responseSolution S (Lane4.cutoffPositiveCoefficient M H omega N Qcentre hQside)
        ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (GE : Ω → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ]
      DomainL2 (centeredCube Qcentre Qside hQside))
    (hGE : ∀ᵐ omega ∂P, Tendsto (fun n => GN (phi n) (env n omega)) atTop (𝓝 (GE omega))) :
    ∀ᵐ omega ∂P, ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
      ∀ (fL2 : DomainL2 (centeredCube Qcentre Qside hQside)),
        ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f) →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
          ((GE omega fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) ∧
          (∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)),
            U x = 0) := by
  have hbeta0 : beta ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hbeta, hbeta1⟩
  let hGrowth := (Classical.choose_spec
    (aux_lem_affine_events_growth_input d hd I Poin X W Cp Sob beta hbeta0)).2 M Rm Sreg It H hMH
    hdelta Qcentre Qside hQside
  let K : ℕ → BilateralField d → ℝ := Classical.choose hGrowth
  let hGrowthC := Classical.choose_spec hGrowth
  let C : ℝ := Classical.choose hGrowthC
  obtain ⟨hKmem, hKnorm, hKge, hsource⟩ := Classical.choose_spec hGrowthC
  let Cnn : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hCboundNN : ENNReal.ofReal C ≤ (Cnn : ENNReal) := by
    have hcoe : ENNReal.ofReal (max C 0) = (Cnn : ENNReal) :=
      ENNReal.ofReal_eq_coe_nnreal (le_max_right _ _)
    rw [← hcoe]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  have hKnormNN : ∀ n, eLpNorm (K n) 1 (chaosSampleLaw M).toMeasure ≤ Cnn := by
    intro n
    exact (hKnorm n).trans hCboundNN
  have hSourceBank := candidate_represented_source_bank
    (chaosSampleLaw M).toMeasure P env hEnvMeas hEnvLaw
    phi Qcentre Qside hQside beta ⟨hbeta, hbeta1⟩ S hS
    (fun n xi => Lane4.cutoffPositiveCoefficient M H xi n Qcentre hQside)
    GN hGN GE hGE K Cnn hKmem hKnormNN hsource
  filter_upwards [hSourceBank] with omega hBank
  intro f hf fL2 hfL2
  let Q := centeredCube Qcentre Qside hQside
  let fsup := sSup {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|}
  have hfsup : 0 ≤ fsup := by
    apply Real.sSup_nonneg
    rintro v ⟨x, hx, rfl⟩
    exact abs_nonneg _
  have hfbdd : BddAbove {v : ℝ | ∃ x ∈ closure (Q : Set (SpatialCoordinates d)), v = |f x|} := by
    obtain ⟨B, hB⟩ :=
      (centeredCube_isBounded Qcentre hQside).isCompact_closure.exists_bound_of_continuousOn
        hf.continuous.continuousOn
    refine ⟨B, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    simpa only [Real.norm_eq_abs] using hB x hx
  have hfbound : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)), |f x| ≤ fsup :=
    ae_restrict_of_forall_mem Q.isOpen.measurableSet
      (fun x hx => le_csSup hfbdd ⟨x, subset_closure hx, rfl⟩)
  obtain ⟨U, ns, UN, hns, hUc, hUr, hUb, hUh, hUni, hUN⟩ :=
    hBank f fsup hf hfsup hfbound fL2 hfL2
  exact ⟨U, hUc, hUr, hUb⟩


/-- `2 m + 1 = L` for the half width `m` of the `L = 3^H1`-adic subdivision. -/
theorem aux_lem_affine_events_half_width (H1 : ℕ) :
    (2 * ((Lane3.subdivisionHalfWidth H1 : ℕ) : ℝ) + 1) = (3 : ℝ) ^ H1 := by
  have h := Lane3.two_mul_subdivisionHalfWidth_add_one H1
  exact_mod_cast h

/-- A child of the `L`-adic subdivision of the parent cell lies on the grid of mesh `r` and inside
the parent. -/
theorem aux_lem_affine_events_cell_grid {d : ℕ} (H1 : ℕ) (r L : ℝ) (hr : 0 < r)
    (hL : L = (3 : ℝ) ^ H1) (o zP z : SpatialCoordinates d) (parentIndex : Fin d → ℤ)
    (idx : OddGridIndex d (Lane3.subdivisionHalfWidth H1))
    (hzP : zP = fun i => o i + (L * r) * ((parentIndex i : ℤ) : ℝ))
    (hz : z = oddGridCenter zP (L * r) (Lane3.subdivisionHalfWidth H1) idx) :
    (∃ j : Fin d → ℤ, z = fun a => o a + r * ((j a : ℤ) : ℝ)) ∧ dist z zP < L * r / 2 := by
  have hw := aux_lem_affine_events_half_width H1
  have hLpos : 0 < L := by rw [hL]; positivity
  have hstep : L * r / (2 * ((Lane3.subdivisionHalfWidth H1 : ℕ) : ℝ) + 1) = r := by
    rw [hw, ← hL]; field_simp
  refine ⟨⟨fun a => (3 ^ H1 : ℤ) * parentIndex a + ((idx a).val : ℤ) -
      (Lane3.subdivisionHalfWidth H1 : ℤ), ?_⟩, ?_⟩
  · funext a
    rw [hz]
    simp only [oddGridCenter, hzP, hstep]
    push_cast
    rw [hL]
    ring
  · have hm : 0 < L * r / 2 := by positivity
    rw [dist_pi_lt_iff hm]
    intro a
    rw [hz]
    simp only [oddGridCenter, Real.dist_eq, hstep]
    have hidx := (idx a).isLt
    have h1 : ((idx a).val : ℝ) ≤ 2 * (Lane3.subdivisionHalfWidth H1 : ℝ) := by
      have : (idx a).val ≤ 2 * Lane3.subdivisionHalfWidth H1 := by omega
      exact_mod_cast this
    have h0 : (0 : ℝ) ≤ ((idx a).val : ℝ) := Nat.cast_nonneg _
    rw [show zP a + (((idx a).val : ℝ) - (Lane3.subdivisionHalfWidth H1 : ℝ)) * r - zP a =
      (((idx a).val : ℝ) - (Lane3.subdivisionHalfWidth H1 : ℝ)) * r by ring, abs_lt]
    have hL2 : L = 2 * (Lane3.subdivisionHalfWidth H1 : ℝ) + 1 := by rw [hL, ← hw]
    constructor <;> nlinarith [hr, h1, h0]

/-- A child at distance `≥ t` from the frontier of the parent has a full `t`-neighbourhood in the
parent, and `t < L r` (the frontier is non-empty and at most `dist z zP + L r / 2` away). -/
theorem aux_lem_affine_events_padded {d : ℕ} [NeZero d] (z zP : SpatialCoordinates d)
    (r L t : ℝ) (hr : 0 < r) (hLr : 0 < L * r) (hz : dist z zP < L * r / 2)
    (hpad : ∀ x ∈ Metric.ball z (r / 2), ∀ y ∈ frontier (Metric.ball zP (L * r / 2)), t ≤ dist x y) :
    Metric.ball z t ⊆ Metric.ball zP (L * r / 2) ∧ t < L * r := by
  have hzp : z ∈ Metric.ball zP (L * r / 2) := Metric.mem_ball.2 hz
  have hzq : z ∈ Metric.ball z (r / 2) := Metric.mem_ball_self (by positivity)
  refine ⟨?_, ?_⟩
  · intro w hw
    by_contra hwp
    have hzt : z ∈ Metric.ball z t := Metric.mem_ball_self (by
      have := Metric.mem_ball.1 hw
      linarith [dist_nonneg (x := w) (y := z)])
    have hconn : IsPreconnected (Metric.ball z t) := (convex_ball z t).isPreconnected
    have hwcl : w ∉ closure (Metric.ball zP (L * r / 2)) := by
      intro hwc
      have hwf : w ∈ frontier (Metric.ball zP (L * r / 2)) :=
        ⟨hwc, by rwa [Metric.isOpen_ball.interior_eq]⟩
      have := hpad z hzq w hwf
      have h2 := Metric.mem_ball.1 hw
      rw [dist_comm] at h2
      linarith
    have hkey := hconn (Metric.ball zP (L * r / 2)) (closure (Metric.ball zP (L * r / 2)))ᶜ
      Metric.isOpen_ball isClosed_closure.isOpen_compl
      (by
        intro x hx
        by_cases hxc : x ∈ closure (Metric.ball zP (L * r / 2))
        · left
          by_contra hxp
          have hxf : x ∈ frontier (Metric.ball zP (L * r / 2)) :=
            ⟨hxc, by rwa [Metric.isOpen_ball.interior_eq]⟩
          have := hpad z hzq x hxf
          have h2 := Metric.mem_ball.1 hx
          rw [dist_comm] at h2
          linarith
        · right; exact hxc)
      ⟨z, hzt, hzp⟩ ⟨w, hw, hwcl⟩
    obtain ⟨x, -, hx1, hx2⟩ := hkey
    exact hx2 (subset_closure hx1)
  · rw [frontier_ball zP (by positivity : L * r / 2 ≠ 0)] at hpad
    obtain ⟨y, hy⟩ := (NormedSpace.sphere_nonempty (E := SpatialCoordinates d) (x := zP)
      (r := L * r / 2)).2 (by positivity)
    have h1 := hpad z hzq y hy
    have h2 : dist z y ≤ dist z zP + dist zP y := dist_triangle _ _ _
    rw [Metric.mem_sphere, dist_comm] at hy
    linarith


/-- The side of the chosen comparison cube: `3^{-(k - H1 + b)} = 3^{-b} L r` and it is at least `9 r`. -/
theorem aux_lem_affine_events_cmp_side (H1 k b : ℕ) (hb : b + 2 ≤ H1) (S : ℝ)
    (hS : S = (3 : ℝ) ^ (-(((k : ℤ)) - (H1 : ℤ) + (b : ℤ)))) :
    S = (3 : ℝ) ^ (-(b : ℤ)) * (((3 : ℝ) ^ H1) * (3 : ℝ) ^ (-(k : ℤ))) ∧
      9 * (3 : ℝ) ^ (-(k : ℤ)) ≤ S := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hEq : S = (3 : ℝ) ^ (-(b : ℤ)) * (((3 : ℝ) ^ H1) * (3 : ℝ) ^ (-(k : ℤ))) := by
    rw [hS, show -(((k : ℤ)) - (H1 : ℤ) + (b : ℤ)) =
      (-(b : ℤ)) + ((H1 : ℤ) + (-(k : ℤ))) by ring, zpow_add₀ h3, zpow_add₀ h3, zpow_natCast]
  refine ⟨hEq, ?_⟩
  rw [hEq]
  have hk : 0 < (3 : ℝ) ^ (-(k : ℤ)) := by positivity
  have h1 : (9 : ℝ) ≤ (3 : ℝ) ^ (-(b : ℤ)) * (3 : ℝ) ^ H1 := by
    have e : (3 : ℝ) ^ (-(b : ℤ)) * (3 : ℝ) ^ H1 = (3 : ℝ) ^ (H1 - b) := by
      rw [_root_.zpow_neg, zpow_natCast, ← div_eq_inv_mul]
      exact (pow_sub₀ _ h3 (by omega)).symm
    rw [e]
    calc (9 : ℝ) = (3 : ℝ) ^ 2 := by norm_num
      _ ≤ (3 : ℝ) ^ (H1 - b) := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith only [h1, hk]

/-- Scalar geometry of the comparison window: `R = m/729 = L̃ r` with `L̃ = L / 3^(b+6)`. -/
theorem aux_lem_affine_events_Lt (L m r Cin : ℝ) (b : ℕ) (hm : m = (3 : ℝ) ^ (-(b : ℤ)) * (L * r))
    (hr : 0 < r) (hL : 0 < L) (hCin : 1 ≤ Cin) :
    (L / (3 : ℝ) ^ (b + 6)) ^ (1 : ℝ) * r ≤ m / 729 ∧
      m / 729 ≤ Cin * (L / (3 : ℝ) ^ (b + 6)) ^ (1 : ℝ) * r ∧
      L / (L / (3 : ℝ) ^ (b + 6)) = (3 : ℝ) ^ (b + 6) ∧ 0 < L / (3 : ℝ) ^ (b + 6) ∧
      L / (3 : ℝ) ^ (b + 6) ≤ L := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (b + 6) := by positivity
  have hLt : 0 < L / (3 : ℝ) ^ (b + 6) := by positivity
  have hEq : m / 729 = L / (3 : ℝ) ^ (b + 6) * r := by
    rw [hm, _root_.zpow_neg, zpow_natCast, pow_add]
    field_simp
    norm_num
  rw [Real.rpow_one]
  refine ⟨hEq.symm.le, ?_, ?_, hLt, ?_⟩
  · rw [hEq]
    have : 0 ≤ L / (3 : ℝ) ^ (b + 6) * r := by positivity
    nlinarith only [this, hCin]
  · field_simp
  · rw [div_le_iff₀ h3]
    have : (1 : ℝ) ≤ (3 : ℝ) ^ (b + 6) := one_le_pow₀ (by norm_num)
    nlinarith only [this, hL]

/-- Consequences of the padding: the wide comparison window, and containments in the parent. -/
theorem aux_lem_affine_events_cell_geometry {d : ℕ} [NeZero d] (z zP : SpatialCoordinates d)
    (r L Cd m : ℝ) (hr : 0 < r) (hL : 0 < L) (hCd : 27 ≤ Cd) (hm : 0 < m) (hm9 : 9 * r ≤ m)
    (hz : dist z zP < L * r / 2)
    (hpad : ∀ x ∈ Metric.ball z (r / 2), ∀ y ∈ frontier (Metric.ball zP (L * r / 2)),
      Cd * m ≤ dist x y) :
    27 * m ≤ L * r ∧ Metric.closedBall z (m / 2) ⊆ Metric.ball zP (L * r / 2) ∧
      Metric.ball z (3 * r / 2) ⊆ Metric.ball zP (L * r / 2) := by
  obtain ⟨hball, hlt⟩ := aux_lem_affine_events_padded z zP r L (Cd * m) hr (by positivity) hz
    (fun x hx y hy => by rw [← mul_comm m Cd] at *; exact hpad x hx y hy)
  refine ⟨by nlinarith only [hCd, hm, hlt], ?_, ?_⟩
  · exact (Metric.closedBall_subset_ball (by nlinarith only [hCd, hm])).trans hball
  · exact (Metric.ball_subset_ball (by nlinarith only [hCd, hm, hm9, hr])).trans hball


/-- The comparison cube is a subcube of the root cube and its closure lies in the parent. -/
theorem aux_lem_affine_events_cube_le {d : ℕ} (z zP c : SpatialCoordinates d) (m rho : ℝ)
    (hm : 0 < m) (Qc : SpatialCoordinates d) (Qs : ℝ) (hQs : 0 < Qs) (hc : c = z)
    (hcl : Metric.closedBall z (m / 2) ⊆ Metric.ball zP rho)
    (hsub : Metric.ball zP rho ⊆ (centeredCube Qc Qs hQs : Set (SpatialCoordinates d))) :
    centeredCube c m hm ≤ centeredCube Qc Qs hQs ∧
      closure (centeredCube c m hm : Set (SpatialCoordinates d)) ⊆ Metric.ball zP rho := by
  subst hc
  rw [centeredCube_coe_eq_ball]
  refine ⟨?_, (Metric.closure_ball_subset_closedBall).trans hcl⟩
  rw [← SetLike.coe_subset_coe, centeredCube_coe_eq_ball]
  exact Metric.ball_subset_closedBall.trans (hcl.trans hsub)

/-- Cubes with equal centre and side coincide. -/
theorem aux_lem_affine_events_cube_congr {d : ℕ} (z1 z2 : SpatialCoordinates d) (r1 r2 : ℝ)
    (h1 : 0 < r1) (h2 : 0 < r2) (hz : z1 = z2) (hr : r1 = r2) :
    (centeredCube z1 r1 h1 : Set (SpatialCoordinates d)) = centeredCube z2 r2 h2 := by
  subst hz
  subst hr
  rfl


/-- A fine base mesh makes `K r^(1-η/2)` smaller than any given target (`η < 2`). -/
theorem aux_lem_affine_events_mesh_exists (K eta target : ℝ) (hK : 0 ≤ K) (heta : eta < 2)
    (htarget : 0 < target) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 → K * r ^ (1 - eta / 2) ≤ target := by
  have he : 0 < 1 - eta / 2 := by linarith
  refine ⟨(target / (K + 1)) ^ (1 / (1 - eta / 2)), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro r hr hrle
  have h1 : r ^ (1 - eta / 2) ≤ ((target / (K + 1)) ^ (1 / (1 - eta / 2))) ^ (1 - eta / 2) :=
    Real.rpow_le_rpow hr.le hrle he.le
  rw [← Real.rpow_mul (by positivity)] at h1
  have h2 : 1 / (1 - eta / 2) * (1 - eta / 2) = 1 := by
    rw [one_div, inv_mul_cancel₀ he.ne']
  rw [h2, Real.rpow_one] at h1
  calc K * r ^ (1 - eta / 2) ≤ K * (target / (K + 1)) := mul_le_mul_of_nonneg_left h1 hK
    _ = target * (K / (K + 1)) := by ring
    _ ≤ target * 1 := by
        apply mul_le_mul_of_nonneg_left _ htarget.le
        rw [div_le_one (by positivity)]; linarith
    _ = target := mul_one _

/-- The source terms of the comparison cell are below the budget `src0 √c r sE^(-1/2)` for a fine
mesh: the pure real-number step of the affine lemma. -/
theorem aux_lem_affine_events_src (Ctotal rho0 fsup B c eta src0 r m sE sCmpInv : ℝ)
    (hCt : 0 ≤ Ctotal) (hfsup : 0 ≤ fsup) (hB : 0 ≤ B) (hc : 0 < c) (heta : eta < 2)
    (hr : 0 < r) (hsE : 0 < sE) (hm : m / 9 = rho0 * r)
    (hratio : sCmpInv ≤ 2 * sE⁻¹) (hcap : sE⁻¹ ≤ B * r ^ (-eta))
    (hmesh : (2 * Ctotal * rho0 ^ 2 + 1) * fsup * Real.sqrt B * r ^ (1 - eta / 2) ≤
      src0 * Real.sqrt c) :
    Ctotal * (m / 9) ^ 2 * sCmpInv * fsup + r ^ 2 * sE⁻¹ * fsup ≤
      src0 * Real.sqrt c * r * sE ^ (-(1 : ℝ) / 2) := by
  set X : ℝ := sE⁻¹ with hX
  have hXpos : 0 < X := inv_pos.2 hsE
  set A : ℝ := 2 * Ctotal * rho0 ^ 2 + 1 with hA
  have hA0 : 0 ≤ A := by positivity
  have hle1 : Ctotal * (m / 9) ^ 2 * sCmpInv * fsup + r ^ 2 * X * fsup ≤ A * r ^ 2 * X * fsup := by
    have h1 : Ctotal * (m / 9) ^ 2 * sCmpInv ≤ Ctotal * (m / 9) ^ 2 * (2 * X) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    have h2 : Ctotal * (m / 9) ^ 2 * sCmpInv * fsup ≤ Ctotal * (m / 9) ^ 2 * (2 * X) * fsup :=
      mul_le_mul_of_nonneg_right h1 hfsup
    rw [hm] at h2 ⊢
    calc _ ≤ Ctotal * (rho0 * r) ^ 2 * (2 * X) * fsup + r ^ 2 * X * fsup := by linarith only [h2]
      _ = A * r ^ 2 * X * fsup := by rw [hA]; ring
  have hsq : sE ^ (-(1 : ℝ) / 2) = X ^ ((1 : ℝ) / 2) := by
    rw [hX, Real.inv_rpow hsE.le, ← Real.rpow_neg hsE.le]
    congr 1; ring
  rw [hsq]
  set Y : ℝ := X ^ ((1 : ℝ) / 2) with hY
  have hYpos : 0 < Y := Real.rpow_pos_of_pos hXpos _
  have hXY : X = Y ^ 2 := by
    rw [hY, ← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]; norm_num
  have hYle : Y ≤ Real.sqrt B * r ^ (-eta / 2) := by
    have h1 : Y ≤ (B * r ^ (-eta)) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow hXpos.le hcap (by norm_num)
    rw [Real.mul_rpow hB (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le,
      ← Real.sqrt_eq_rpow] at h1
    have : -eta * (1 / 2) = -eta / 2 := by ring
    rwa [this] at h1
  have hkey : A * r * fsup * Y ≤ src0 * Real.sqrt c := by
    have h1 : A * r * fsup * Y ≤ A * r * fsup * (Real.sqrt B * r ^ (-eta / 2)) :=
      mul_le_mul_of_nonneg_left hYle (by positivity)
    have h2 : A * r * fsup * (Real.sqrt B * r ^ (-eta / 2)) =
        A * fsup * Real.sqrt B * r ^ (1 - eta / 2) := by
      have : r ^ (1 - eta / 2) = r * r ^ (-eta / 2) := by
        rw [show 1 - eta / 2 = 1 + (-eta / 2) by ring, Real.rpow_add hr, Real.rpow_one]
      rw [this]; ring
    linarith only [h1, h2, hmesh]
  calc Ctotal * (m / 9) ^ 2 * sCmpInv * fsup + r ^ 2 * X * fsup ≤ A * r ^ 2 * X * fsup := hle1
    _ = (A * r * fsup * Y) * (r * Y) := by rw [hXY]; ring
    _ ≤ (src0 * Real.sqrt c) * (r * Y) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = src0 * Real.sqrt c * r * Y := by ring


/-- The pathwise catalogue cap holds eventually along the represented cutoff sequence at a grid
cell. -/
theorem aux_lem_affine_events_hcap {d : ℕ} [NeZero d] (I : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    {Ω : Type} (phi : ℕ → ℕ) (hphi : StrictMono phi) (env : ℕ → Ω → BilateralField d)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside) (J : ℕ)
    (origins : Fin J → SpatialCoordinates d) (eta sigma K : ℝ) (om : Ω)
    (hK : ∀ (n k : ℕ) (i : Fin J) (idx : Fin d → ℤ), k ≤ phi n →
      let wc : SpatialCoordinates d := fun a => origins i a + (3 : ℝ) ^ (-(k : ℤ)) * (idx a : ℝ)
      let rc : ℝ := (3 : ℝ) ^ (-(k : ℤ))
      ∀ hc : 0 < rc,
      (centeredCube wc rc hc : Set (SpatialCoordinates d)) ⊆
        (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) →
      I.Lam wc rc hc (cutoffPositiveCoefficient M H (env n om) (phi n) wc hc)
        wc rc sigma 2 +
        (I.lam wc rc hc (cutoffPositiveCoefficient M H (env n om) (phi n) wc hc)
          wc rc sigma 2)⁻¹ ≤ K * rc ^ (-eta))
    (k : ℕ) (i : Fin J) (z : SpatialCoordinates d)
    (hz : ∃ idx : Fin d → ℤ, z = fun a => origins i a + (3 : ℝ) ^ (-(k : ℤ)) * (idx a : ℝ))
    (hr : 0 < (3 : ℝ) ^ (-(k : ℤ)))
    (hsub : (centeredCube z ((3 : ℝ) ^ (-(k : ℤ))) hr : Set (SpatialCoordinates d)) ⊆
      (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) :
    ∀ᶠ n in atTop,
      I.Lam z ((3 : ℝ) ^ (-(k : ℤ))) hr
        (cutoffPositiveCoefficient M H (env n om) (phi n) z hr)
        z ((3 : ℝ) ^ (-(k : ℤ))) sigma 2 +
        (I.lam z ((3 : ℝ) ^ (-(k : ℤ))) hr
          (cutoffPositiveCoefficient M H (env n om) (phi n) z hr)
          z ((3 : ℝ) ^ (-(k : ℤ))) sigma 2)⁻¹ ≤ K * ((3 : ℝ) ^ (-(k : ℤ))) ^ (-eta) := by
  obtain ⟨idx, hz⟩ := hz
  subst hz
  filter_upwards [hphi.tendsto_atTop.eventually_ge_atTop k] with n hn
  exact hK n k i idx hn hr hsub


/-- Transport of the root-cell quantity `Λ` along equalities of centre and side. -/
theorem aux_lem_affine_events_norm_transport {d : ℕ} [NeZero d] (I : in_J d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (phi : ℕ → ℕ) (env : ℕ → Ω → BilateralField d)
    (sN : ℕ → ℤ → SpatialCoordinates d → BilateralField d → ℝ) (sigma : ℝ) (Lim : Ω → ℝ)
    (c1 z : SpatialCoordinates d) (s1 : ℝ) (hs1 : 0 < s1) (l1 : ℤ) (k : ℕ)
    (hc : c1 = z) (hs : s1 = (3 : ℝ) ^ (-(k : ℤ))) (hl : l1 = (k : ℤ))
    (hr : 0 < (3 : ℝ) ^ (-(k : ℤ)))
    (hlim : TendstoInMeasure P (fun n om =>
      I.Lam c1 s1 hs1 (cutoffPositiveCoefficient M H (env n om) (phi n) c1 hs1) c1 s1 sigma 2 /
        sN (phi n) l1 c1 (env n om)) atTop Lim) :
    TendstoInMeasure P (fun n om =>
      I.Lam z ((3 : ℝ) ^ (-(k : ℤ))) hr
        (cutoffPositiveCoefficient M H (env n om) (phi n) z hr) z ((3 : ℝ) ^ (-(k : ℤ))) sigma 2 /
        sN (phi n) (k : ℤ) z (env n om)) atTop Lim := by
  subst hc
  subst hl
  subst hs
  exact hlim


/-- The lattice of the `L`-adic subdivision: a lattice point `k i ≥ 0` shifted by the half-width gives
a child inside the parent (used for the padded central child below). -/
theorem aux_lem_affine_events_padded_link {d : ℕ} (L r W : ℝ) (hr : 0 < r) (hL : 0 < L)
    (lo lop z zP : Fin d → ℝ) (hz : ∀ i, z i = lo i + r / 2) (hzP : ∀ i, zP i = lop i + L * r / 2)
    (hpad : ∀ i, W * r < lo i - lop i ∧ W * r < lop i + L * r - (lo i + r)) :
    ∀ x ∈ Metric.ball z (r / 2), ∀ y ∈ frontier (Metric.ball zP (L * r / 2)),
      W * r ≤ dist x y := by
  intro x hx y hy
  by_contra hlt
  push_neg at hlt
  have hρ : 0 < L * r / 2 := by positivity
  have hxi : ∀ i, dist (x i) (z i) < r / 2 := (dist_pi_lt_iff (by positivity)).1 hx
  have hxy : ∀ i, dist (x i) (y i) < W * r :=
    fun i => lt_of_le_of_lt (dist_le_pi_dist x y i) hlt
  have hyin : y ∈ Metric.ball zP (L * r / 2) := by
    rw [Metric.mem_ball, dist_pi_lt_iff hρ]
    intro i
    have h1 := hxi i
    have h2 := hxy i
    have h3 := hpad i
    rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
    rw [hz i] at h1
    rw [hzP i]
    constructor <;> nlinarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  rw [Metric.isOpen_ball.frontier_eq] at hy
  exact hy.2 hyin

/-- The non-vacuity witness: the central child is padded as soon as `Cd * 3^(-b) ≤ 1/4`. -/
theorem aux_lem_affine_events_central {d : ℕ} [NeZero d] (H1 b : ℕ) (Cd : ℝ)
    (hL2 : 2 < (3 : ℝ) ^ H1) :
    Cd * (3 : ℝ) ^ (-(b : ℤ)) ≤ 1 / 4 →
      ∀ (parentSide : ℝ), 0 < parentSide → ∀ zParent : SpatialCoordinates d,
        ∃ idx : OddGridIndex d (Lane3.subdivisionHalfWidth H1),
          oddGridCenter zParent parentSide (Lane3.subdivisionHalfWidth H1) idx = zParent ∧
          ∀ x ∈ Metric.ball zParent (parentSide / (3 : ℝ) ^ H1 / 2),
            ∀ y ∈ frontier (Metric.ball zParent ((3 : ℝ) ^ H1 * (parentSide / (3 : ℝ) ^ H1) / 2)),
              Cd * ((3 : ℝ) ^ (-(b : ℤ)) * ((3 : ℝ) ^ H1 * (parentSide / (3 : ℝ) ^ H1))) ≤
                dist x y := by
  intro hC parentSide hps zParent
  have hLpos : 0 < (3 : ℝ) ^ H1 := by linarith only [hL2]
  refine ⟨fun _ => ⟨Lane3.subdivisionHalfWidth H1, by omega⟩, ?_, ?_⟩
  · funext i; simp [oddGridCenter]
  · set r : ℝ := parentSide / (3 : ℝ) ^ H1 with hr
    have hrpos : 0 < r := by positivity
    have hLr : (3 : ℝ) ^ H1 * r = parentSide := by rw [hr]; field_simp
    have hbase := aux_lem_affine_events_padded_link (d := d) ((3 : ℝ) ^ H1) r
      (Cd * (3 : ℝ) ^ (-(b : ℤ)) * (3 : ℝ) ^ H1) hrpos hLpos
      (fun i => zParent i - (3 : ℝ) ^ H1 * r / 2 + ((3 : ℝ) ^ H1 * r / 2 - r / 2))
      (fun i => zParent i - (3 : ℝ) ^ H1 * r / 2) zParent zParent
      (fun i => by ring) (fun i => by ring) (by
        intro i
        have hb0 : 0 < (3 : ℝ) ^ (-(b : ℤ)) := by positivity
        have h1 : (Cd * (3 : ℝ) ^ (-(b : ℤ))) * (3 : ℝ) ^ H1 * r ≤ (1 / 4) * ((3 : ℝ) ^ H1 * r) := by
          have : (Cd * (3 : ℝ) ^ (-(b : ℤ))) * ((3 : ℝ) ^ H1 * r) ≤ (1 / 4) * ((3 : ℝ) ^ H1 * r) :=
            mul_le_mul_of_nonneg_right hC (by positivity)
          linarith only [this]
        have h2 : 0 < (3 : ℝ) ^ H1 * r := by positivity
        constructor <;> nlinarith only [h1, h2, hL2, hrpos])
    intro x hx y hy
    have := hbase x hx y hy
    calc Cd * ((3 : ℝ) ^ (-(b : ℤ)) * ((3 : ℝ) ^ H1 * r)) =
        Cd * (3 : ℝ) ^ (-(b : ℤ)) * (3 : ℝ) ^ H1 * r := by ring
      _ ≤ dist x y := this

/-- Large `H1` makes the comparison scale `L / 3^(b+6)` exceed the threshold `L0`. -/
theorem aux_lem_affine_events_scale (L0 : ℝ) (n0 b H1 : ℕ) (hn0 : L0 < (3 : ℝ) ^ n0)
    (hH1 : b + 6 + n0 ≤ H1) : L0 ≤ (3 : ℝ) ^ H1 / (3 : ℝ) ^ (b + 6) := by
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  rw [div_eq_mul_inv, ← pow_sub₀ _ h3 (by omega : b + 6 ≤ H1)]
  exact hn0.le.trans (pow_le_pow_right₀ (by norm_num) (by omega))

end Paper
