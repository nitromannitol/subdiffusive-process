module

public import Mathlib
public import SubdiffusiveProcess.Paper.in_joint_extraction_inprob
public import SubdiffusiveProcess.Paper.Support.RepresentedFunctionsRegular
public import SubdiffusiveProcess.Paper.conv_represented_tight_of_bounded
public import SubdiffusiveProcess.Paper.conv_represented_opNorm_tendsto
public import SubdiffusiveProcess.Lnorm.CutoffVolumeResponseMeasurability

@[expose] public section





open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped Topology ENNReal NNReal InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.WeightedLimitIdentification
open _root_.SubdiffusiveProcess.Paper

/-- The continuous-map space of the model is Polish; hence so is the bilateral field space. -/
theorem aux_conv_represented_model_operators_polish (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    PolishSpace (BilateralField d) := by
  let : TopologicalSpace.IsCompletelyMetrizableSpace C(SpatialCoordinates d, ℝ) :=
    TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
      (X := C(SpatialCoordinates d, ℝ))
  have : PolishSpace C(SpatialCoordinates d, ℝ) := inferInstance
  infer_instance


/-- **Represented cutoff-dependent operators.**  On the canonical original space (the bilateral
field with the chaos law), take the actual cutoff killed inverses `Φ i N β` of a countable
catalogue of cubes, random coercivity constants `Kc i N` that are measurable, nonnegative,
tight in `N` and satisfy the coercivity estimate almost surely, and countable dense additive
test sets `D i`.  For the two cutoff sequences `NE`, `NF` there is one strictly increasing
`seq`, a probability space with environments `env n` (each of the chaos law) and a limit
environment (also of the chaos law) such that almost surely `env n → envLim`, the coercivity
constants along the represented sequence converge (in particular are bounded), and the actual
killed inverses of the *varying* environments, `Φ i (NE (seq n)) (env n ω)` and
`Φ i (NF (seq n)) (env n ω)`, converge in operator norm.  Nothing is asserted across different
indices `n`, and no fixed-field boundedness is inferred from the moment bound. -/
theorem represented_model_operators_with_ae_descent
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (hInterp : CubeFractionalInterpolationInput d hd)
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (Sspace : (i : ℕ) → ResponseSpace (centeredCube (z i) (r i) (hr i)))
    (hS : ∀ i, (Sspace i).space = killedSobolevGraph (centeredCube (z i) (r i) (hr i)))
    (D : (i : ℕ) → Set (DomainL2 (centeredCube (z i) (r i) (hr i))))
    [hDcount : ∀ i, Countable (D i)]
    (hDdense : ∀ i, Dense (D i))
    (hDadd : ∀ i, ∀ x ∈ D i, ∀ y ∈ D i, x + y ∈ D i)
    (NE NF : ℕ → ℕ)
    (Kc : ℕ → ℕ → BilateralField d → ℝ)
    (hKcmeas : ∀ i N, Measurable (Kc i N))
    (hKcnonneg : ∀ i N β, 0 ≤ Kc i N β)
    (hcoer : ∀ i N, ∀ᵐ β ∂(chaosSampleLaw M).toMeasure,
      ∀ v : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
        cubeFractionalL2Seminorm hd (z i) (r i) (hr i) threeQuarterOrder
            (fun _ : Fin 1 => (v : SobolevData (centeredCube (z i) (r i) (hr i))).1) < ⊤ ∧
        cubeFractionalSqNorm hd (z i) (r i) (hr i) threeQuarterOrder
            (v : SobolevData (centeredCube (z i) (r i) (hr i))).1 ≤
          Kc i N β *
            sobolevCoefficientForm
              (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N (z i) (hr i))
              (v : SobolevData (centeredCube (z i) (r i) (hr i)))
              (v : SobolevData (centeredCube (z i) (r i) (hr i))))
    (htight : ∀ i, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      (chaosSampleLaw M).toMeasure {β | Mb < Kc i (NE n) β} ≤ ENNReal.ofReal rho ∧
      (chaosSampleLaw M).toMeasure {β | Mb < Kc i (NF n) β} ≤ ENNReal.ofReal rho)
    {X : Type} [Countable X] (Z : X → ℕ → BilateralField d → ℝ)
    (hZmeas : ∀ x n, Measurable (Z x (NE n)) ∧ Measurable (Z x (NF n)))
    (hZtight : ∀ x, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      (chaosSampleLaw M).toMeasure {β | Mb < |Z x (NE n) β|} ≤ ENNReal.ofReal rho ∧
      (chaosSampleLaw M).toMeasure {β | Mb < |Z x (NF n) β|} ≤ ENNReal.ofReal rho) :
    ∃ seq : ℕ → ℕ, StrictMono seq ∧
      ∃ (Ωh : Type) (_ : MeasurableSpace Ωh) (Ph : Measure Ωh) (_ : IsProbabilityMeasure Ph)
        (env : ℕ → Ωh → BilateralField d) (envLim : Ωh → BilateralField d)
        (GE GF : (i : ℕ) → Ωh →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i))),
        (∀ n, MeasurePreserving (env n) Ph (chaosSampleLaw M).toMeasure) ∧
        MeasurePreserving envLim Ph (chaosSampleLaw M).toMeasure ∧
        (∀ᵐ ω ∂Ph,
          Tendsto (fun n => env n ω) atTop (𝓝 (envLim ω)) ∧
          (∀ x, ∃ ZE ZF : ℝ,
              Tendsto (fun n => Z x (NE (seq n)) (env n ω)) atTop (𝓝 ZE) ∧
              Tendsto (fun n => Z x (NF (seq n)) (env n ω)) atTop (𝓝 ZF)) ∧
          ∀ i,
            (∃ KE KF : ℝ,
              Tendsto (fun n => Kc i (NE (seq n)) (env n ω)) atTop (𝓝 KE) ∧
              Tendsto (fun n => Kc i (NF (seq n)) (env n ω)) atTop (𝓝 KF)) ∧
            Tendsto (fun n => volumeResponseOperator (Sspace i)
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n ω) (NE (seq n)) (z i) (hr i)))
              atTop (𝓝 (GE i ω)) ∧
            Tendsto (fun n => volumeResponseOperator (Sspace i)
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n ω) (NF (seq n)) (z i) (hr i)))
              atTop (𝓝 (GF i ω))) ∧
        (∀ p : BilateralField d → Prop,
          (∀ᵐ ω ∂Ph, p (envLim ω)) → ∀ᵐ β ∂(chaosSampleLaw M).toMeasure, p β) := by
  classical
  have : PolishSpace (BilateralField d) := aux_conv_represented_model_operators_polish d
  let P0 : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
  have : IsProbabilityMeasure P0 := inferInstance
  let Φ : ∀ i : ℕ, ℕ → BilateralField d →
      DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)) :=
    fun i N β => volumeResponseOperator (Sspace i)
      (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N (z i) (hr i))
  have hΦapp : ∀ i N β f, Φ i N β f =
      (responseSolution (Sspace i)
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (id β) N (z i) (hr i))
        ((sobolevVolumeLoad f).comp (Sspace i).space.subtypeL)).val.1 :=
    fun i N β f => volumeResponseOperator_apply _ _ f
  have hΦsym : ∀ i N β (x y : DomainL2 (centeredCube (z i) (r i) (hr i))),
      ⟪Φ i N β x, y⟫_ℝ = ⟪x, Φ i N β y⟫_ℝ := by
    intro i N β x y
    rw [real_inner_comm]
    exact volumeResponseOperator_symm (Sspace i) _ y x
  have hΦmeas : ∀ i N, StronglyMeasurable (fun β => Φ i N β) := fun i N =>
    stronglyMeasurable_cutoffVolumeResponseOperator M H hH.1 N (z i) (r i) (hr i) (Sspace i)
  have hTmeas : ∀ i N (x : DomainL2 (centeredCube (z i) (r i) (hr i))),
      Measurable (fun β => ⟪x, Φ i N β x⟫_ℝ) := by
    intro i N x
    have hc : Continuous (fun T : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)) => ⟪x, T x⟫_ℝ) :=
      continuous_const.inner ((ContinuousLinearMap.apply ℝ _ x).continuous)
    exact (hc.comp_stronglyMeasurable (hΦmeas i N)).measurable
  -- the good set: coercivity for every cube and cutoff
  let good : BilateralField d → Prop := fun β => ∀ i N,
    ∀ v : killedSobolevGraph (centeredCube (z i) (r i) (hr i)),
      cubeFractionalL2Seminorm hd (z i) (r i) (hr i) threeQuarterOrder
          (fun _ : Fin 1 => (v : SobolevData (centeredCube (z i) (r i) (hr i))).1) < ⊤ ∧
      cubeFractionalSqNorm hd (z i) (r i) (hr i) threeQuarterOrder
          (v : SobolevData (centeredCube (z i) (r i) (hr i))).1 ≤
        Kc i N β *
          sobolevCoefficientForm
            (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β N (z i) (hr i))
            (v : SobolevData (centeredCube (z i) (r i) (hr i)))
            (v : SobolevData (centeredCube (z i) (r i) (hr i)))
  have hgood0 : ∀ᵐ β ∂P0, good β :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun N => hcoer i N
  -- compactness of the unit-ball images on the good set with bounded constants
  have hcompact : ∀ i (Mb : ℝ), IsCompact (closure
      {y : DomainL2 (centeredCube (z i) (r i) (hr i)) | ∃ (N : ℕ) (β : BilateralField d),
        good β ∧ Kc i N β ≤ Mb ∧ ∃ f : DomainL2 (centeredCube (z i) (r i) (hr i)),
          ‖f‖ ≤ 1 ∧ Φ i N β f = y}) := by
    intro i Mb
    exact aux_in_joint_extraction_inprob_compact d hd hInterp M H
      (id : BilateralField d → BilateralField d) (z i) (r i) (hr i) (Sspace i) (hS i)
      (fun N β => Φ i N β) (fun N β f => hΦapp i N β f) (Kc i) good
      (fun N β hg v => hg i N v) Mb
  have hbound : ∀ i (Mb : ℝ), ∃ R : ℝ, 0 ≤ R ∧ ∀ N β, good β → Kc i N β ≤ Mb →
      ‖Φ i N β‖ ≤ R := by
    intro i Mb
    obtain ⟨R0, hR0⟩ := (hcompact i Mb).isBounded.exists_norm_le
    refine ⟨max R0 0, le_max_right _ _, fun N β hg hK => ?_⟩
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun x => ?_
    by_cases hx : x = 0
    · simp [hx]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hunit : ‖(‖x‖⁻¹) • x‖ ≤ 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxpos.ne']
    have hmem : Φ i N β ((‖x‖⁻¹) • x) ∈ closure
        {y : DomainL2 (centeredCube (z i) (r i) (hr i)) | ∃ (N : ℕ) (β : BilateralField d),
          good β ∧ Kc i N β ≤ Mb ∧ ∃ f : DomainL2 (centeredCube (z i) (r i) (hr i)),
            ‖f‖ ≤ 1 ∧ Φ i N β f = y} :=
      subset_closure ⟨N, β, hg, hK, _, hunit, rfl⟩
    have h1 := hR0 _ hmem
    have h2 : Φ i N β x = ‖x‖ • Φ i N β ((‖x‖⁻¹) • x) := by
      rw [map_smul, smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
    rw [h2, norm_smul, norm_norm]
    calc ‖x‖ * ‖Φ i N β ((‖x‖⁻¹) • x)‖ ≤ ‖x‖ * max R0 0 :=
          mul_le_mul_of_nonneg_left (h1.trans (le_max_left _ _)) (norm_nonneg _)
      _ = max R0 0 * ‖x‖ := mul_comm _ _
  -- the countable coordinate family: coercivity constants and quadratic tests, both cutoff sides
  let Ns : Bool → ℕ → ℕ := fun b => cond b NE NF
  let Y : ((Bool × ℕ) ⊕ (Bool × Σ i : ℕ, D i) ⊕ (Bool × X)) → ℕ → BilateralField d → ℝ :=
    Sum.elim (fun q n β => Kc q.2 (Ns q.1 n) β)
      (Sum.elim
        (fun q n β => ⟪(q.2.2 : DomainL2 (centeredCube (z q.2.1) (r q.2.1) (hr q.2.1))),
          Φ q.2.1 (Ns q.1 n) β q.2.2⟫_ℝ)
        (fun q n β => Z q.2 (Ns q.1 n) β))
  have hY : ∀ c n, Measurable (Y c n) := by
    rintro (q | q | q) n
    · exact hKcmeas _ _
    · exact hTmeas _ _ _
    · obtain ⟨b, x⟩ := q
      cases b
      · exact (hZmeas x n).2
      · exact (hZmeas x n).1
  have hbad : P0 {β | ¬ good β} = 0 := ae_iff.1 hgood0
  have hbddY : ∀ c, ∀ rho : ℝ, 0 < rho → ∃ Mb : ℝ, ∀ n,
      P0 {β | Mb < |Y c n β|} ≤ ENNReal.ofReal rho := by
    rintro (q | q | q) rho hrho
    · obtain ⟨Mb, hMb0⟩ := htight q.2 rho hrho
      have hMb : ∀ n b, (chaosSampleLaw M).toMeasure {β | Mb < Kc q.2 (Ns b n) β} ≤
          ENNReal.ofReal rho := fun n b => by
        cases b
        · exact (hMb0 n).2
        · exact (hMb0 n).1
      refine ⟨Mb, fun n => ?_⟩
      have : {β | Mb < |Y (Sum.inl q) n β|} = {β | Mb < Kc q.2 (Ns q.1 n) β} := by
        ext β
        simp only [mem_ofPred_eq, Y, Sum.elim_inl, abs_of_nonneg (hKcnonneg _ _ _)]
      rw [this]
      exact hMb _ _
    · obtain ⟨Mb, hMb0⟩ := htight q.2.1 rho hrho
      have hMb : ∀ n b, (chaosSampleLaw M).toMeasure {β | Mb < Kc q.2.1 (Ns b n) β} ≤
          ENNReal.ofReal rho := fun n b => by
        cases b
        · exact (hMb0 n).2
        · exact (hMb0 n).1
      obtain ⟨R, hR0, hR⟩ := hbound q.2.1 Mb
      refine ⟨R * ‖(q.2.2 : DomainL2 (centeredCube (z q.2.1) (r q.2.1) (hr q.2.1)))‖ ^ 2,
        fun n => ?_⟩
      have hsub : {β | R * ‖(q.2.2 : DomainL2 (centeredCube (z q.2.1) (r q.2.1)
            (hr q.2.1)))‖ ^ 2 < |Y (Sum.inr (Sum.inl q)) n β|} ⊆
          {β | Mb < Kc q.2.1 (Ns q.1 n) β} ∪ {β | ¬ good β} := by
        intro β hβ
        by_contra hcon
        simp only [Set.mem_union, mem_ofPred_eq, not_or, not_lt, not_not] at hcon
        obtain ⟨hK, hg⟩ := hcon
        simp only [mem_ofPred_eq, Y, Sum.elim_inr, Sum.elim_inl] at hβ
        have h1 := abs_real_inner_le_norm
          (q.2.2 : DomainL2 (centeredCube (z q.2.1) (r q.2.1) (hr q.2.1)))
          (Φ q.2.1 (Ns q.1 n) β q.2.2)
        have h2 := ContinuousLinearMap.le_opNorm (Φ q.2.1 (Ns q.1 n) β) q.2.2
        have h3 := hR (Ns q.1 n) β hg hK
        have hx := norm_nonneg (q.2.2 : DomainL2 (centeredCube (z q.2.1) (r q.2.1) (hr q.2.1)))
        have h4 : ‖(q.2.2 : DomainL2 (centeredCube (z q.2.1) (r q.2.1) (hr q.2.1)))‖ *
            ‖Φ q.2.1 (Ns q.1 n) β q.2.2‖ ≤
            R * ‖(q.2.2 : DomainL2 (centeredCube (z q.2.1) (r q.2.1) (hr q.2.1)))‖ ^ 2 := by
          calc _ ≤ ‖(q.2.2 : DomainL2 (centeredCube (z q.2.1) (r q.2.1) (hr q.2.1)))‖ *
                (‖Φ q.2.1 (Ns q.1 n) β‖ *
                  ‖(q.2.2 : DomainL2 (centeredCube (z q.2.1) (r q.2.1) (hr q.2.1)))‖) :=
                mul_le_mul_of_nonneg_left h2 hx
            _ ≤ ‖(q.2.2 : DomainL2 (centeredCube (z q.2.1) (r q.2.1) (hr q.2.1)))‖ *
                (R * ‖(q.2.2 : DomainL2 (centeredCube (z q.2.1) (r q.2.1) (hr q.2.1)))‖) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hx) hx
            _ = _ := by ring
        linarith
      calc P0 _ ≤ P0 ({β | Mb < Kc q.2.1 (Ns q.1 n) β} ∪ {β | ¬ good β}) := measure_mono hsub
        _ ≤ P0 {β | Mb < Kc q.2.1 (Ns q.1 n) β} + P0 {β | ¬ good β} := measure_union_le _ _
        _ ≤ ENNReal.ofReal rho := by rw [hbad, add_zero]; exact hMb _ _
    · obtain ⟨b, x⟩ := q
      obtain ⟨Mb, hMb0⟩ := hZtight x rho hrho
      refine ⟨Mb, fun n => ?_⟩
      cases b
      · exact (hMb0 n).2
      · exact (hMb0 n).1
  have htightY := fun c => conv_represented_tight_of_bounded P0 (Y c) (hY c) (hbddY c)
  obtain ⟨seq, hseq, Ωh, mΩh, Ph, hPh, env, envLim, Ylim, hmp, hmpLim, hYlim, hconv, hdescent⟩ :=
    represented_environment_functions_with_ae_descent P0 Y hY htightY
  have hgoodΩ : ∀ᵐ ω ∂Ph, ∀ n, good (env n ω) :=
    ae_all_iff.2 fun n => (hmp n).quasiMeasurePreserving.ae hgood0
  -- pathwise: bounded constants, compactness and convergent tests give norm convergence
  have hex : ∀ ω : Ωh, (∀ n, good (env n ω)) →
      (∀ c, Tendsto (fun n => Y c (seq n) (env n ω)) atTop (𝓝 (Ylim c ω))) →
      ∀ (b : Bool) (i : ℕ), ∃ L : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)),
        Tendsto (fun n => Φ i (Ns b (seq n)) (env n ω)) atTop (𝓝 L) := by
    intro ω hg hlim b i
    obtain ⟨Mb, hMb⟩ := (hlim (Sum.inl (b, i))).bddAbove_range
    have hMb' : ∀ n, Kc i (Ns b (seq n)) (env n ω) ≤ Mb := fun n => hMb ⟨n, rfl⟩
    exact conv_represented_opNorm_tendsto (fun n => Φ i (Ns b (seq n)) (env n ω))
      (fun n x y => hΦsym i _ _ x y) _ (hcompact i Mb)
      (fun n x hx => subset_closure ⟨Ns b (seq n), env n ω, hg n, hMb' n, x, hx, rfl⟩)
      (D i) (hDdense i) (hDadd i)
      (fun h hh => ⟨Ylim (Sum.inr (Sum.inl (b, ⟨i, ⟨h, hh⟩⟩))) ω,
        hlim (Sum.inr (Sum.inl (b, ⟨i, ⟨h, hh⟩⟩)))⟩)
  let lim : (b : Bool) → (i : ℕ) → Ωh → DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
      DomainL2 (centeredCube (z i) (r i) (hr i)) := fun b i ω =>
    if h : ∃ L : DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
        DomainL2 (centeredCube (z i) (r i) (hr i)),
        Tendsto (fun n => Φ i (Ns b (seq n)) (env n ω)) atTop (𝓝 L) then h.choose else 0
  refine ⟨seq, hseq, Ωh, mΩh, Ph, hPh, env, envLim, lim true, lim false, hmp, hmpLim, ?_, hdescent⟩
  filter_upwards [hconv, hgoodΩ] with ω hω hg
  refine ⟨hω.1, fun x => ⟨Ylim (Sum.inr (Sum.inr (true, x))) ω, Ylim (Sum.inr (Sum.inr (false, x))) ω,
    hω.2 (Sum.inr (Sum.inr (true, x))), hω.2 (Sum.inr (Sum.inr (false, x)))⟩,
    fun i => ⟨⟨Ylim (Sum.inl (true, i)) ω, Ylim (Sum.inl (false, i)) ω,
    hω.2 (Sum.inl (true, i)), hω.2 (Sum.inl (false, i))⟩, ?_, ?_⟩⟩
  · have h := hex ω hg hω.2 true i
    simp only [lim, dite_eq_left h]
    exact h.choose_spec
  · have h := hex ω hg hω.2 false i
    simp only [lim, dite_eq_left h]
    exact h.choose_spec

end SubdiffusiveProcess.WeightedLimitIdentification
