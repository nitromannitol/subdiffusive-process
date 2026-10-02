import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.InfraredAdmissible
import SubdiffusiveProcess.Main.InfraredPartialSum
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.prop_folded_iteration
import SubdiffusiveProcess.Paper.lem_primitive
import SubdiffusiveProcess.Paper.rem_resolved_strata
import SubdiffusiveProcess.Paper.lane4_regularity_mesh_statistic
import SubdiffusiveProcess.Paper.lane4_reference_mesh_statistic
import SubdiffusiveProcess.Paper.lane4_two_mesh_energy_bound
import SubdiffusiveProcess.Paper.in_common_scale_coupling
import SubdiffusiveProcess.Paper.coefficient_physical_identity
import SubdiffusiveProcess.Paper.lem_infrared

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

noncomputable section
attribute [local instance] Classical.propDecidable
namespace Paper

/-! ### Carrier-uniform transport of the folded one-center package

`in_iteration` reads its `in_J` carrier only in `good_error`, and there only at admissible
arguments, where `in_J.err_eq`/`in_J.chart_eq` pin `E.err` to a carrier-independent value.  Hence an
iteration package over one carrier re-indexes to any other carrier with the same `prefixLen` and
`ref`, and the folded constant `(C, K)` of `prop_folded_iteration` can be chosen before every
carrier (paper line 1092: "all are fixed before disorder"). -/

theorem aux_rem_resolved_meshes_probe
    {d : ℕ} {A B : Homogenization.Book.Ch02.TriadicCoeffFamily d}
    {Q : Homogenization.TriadicCube d}
    (h : Homogenization.Book.Ch02.CoeffOn.AEEq (A.coeffOn Q) (B.coeffOn Q))
    (alpha : ℝ) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax Q A alpha =
      SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax Q B alpha := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbeMax
    SubdiffusiveProcess.CoarseGrainingVocab.paperScalarProbe
  apply iSup_congr
  intro e
  congr 1
  exact Homogenization.Book.Ch02.responseJ_eq_ofAEEq h _ _

theorem aux_rem_resolved_meshes_scale
    {d : ℕ} {A B : Homogenization.Book.Ch02.TriadicCoeffFamily d}
    (Q : Homogenization.TriadicCube d) (k : ℤ)
    (h : ∀ R : Homogenization.TriadicCube d,
      R ∈ Homogenization.descendantsAtScale Q k →
        Homogenization.Book.Ch02.CoeffOn.AEEq (A.coeffOn R) (B.coeffOn R))
    (p : Homogenization.Book.Ch02.MultiscaleExponent) (alpha : ℝ) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale Q k p A alpha =
      SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale Q k p B alpha := by
  cases p with
  | finite p =>
      simp only [SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro R hR
      rw [aux_rem_resolved_meshes_probe (h R hR) alpha]
  | infinity =>
      simp only [SubdiffusiveProcess.CoarseGrainingVocab.paperScaleResponseAtScale,
        SubdiffusiveProcess.CoarseGrainingVocab.paperMaxDescendantProbeAtScale]
      congr 1
      apply iSup_congr
      intro R
      exact aux_rem_resolved_meshes_probe (h R.1 R.2) alpha

theorem aux_rem_resolved_meshes_error
    {d : ℕ} {A B : Homogenization.Book.Ch02.TriadicCoeffFamily d}
    (Q : Homogenization.TriadicCube d) (n : ℤ) (s : ℝ)
    (p : Homogenization.Book.Ch02.MultiscaleExponent) (q : ℝ) (alpha : ℝ)
    (h : ∀ k : ℤ, ∀ R : Homogenization.TriadicCube d,
      R ∈ Homogenization.descendantsAtScale Q k →
        Homogenization.Book.Ch02.CoeffOn.AEEq (A.coeffOn R) (B.coeffOn R)) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite Q n s p q A alpha =
      SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite Q n s p q B alpha := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorFinite
  congr 1
  apply tsum_congr
  intro l
  rw [aux_rem_resolved_meshes_scale Q (n - (l : ℤ)) (h (n - (l : ℤ))) p alpha]

theorem aux_rem_resolved_meshes_error_infinity
    {d : ℕ} {A B : Homogenization.Book.Ch02.TriadicCoeffFamily d}
    (Q : Homogenization.TriadicCube d) (n : ℤ) (s : ℝ)
    (p : Homogenization.Book.Ch02.MultiscaleExponent) (alpha : ℝ)
    (h : ∀ k : ℤ, ∀ R : Homogenization.TriadicCube d,
      R ∈ Homogenization.descendantsAtScale Q k →
        Homogenization.Book.Ch02.CoeffOn.AEEq (A.coeffOn R) (B.coeffOn R)) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity Q n s p A alpha =
      SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity Q n s p B alpha := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperHomogenizationErrorInfinity
  apply iSup_congr
  intro l
  congr 1
  exact aux_rem_resolved_meshes_scale Q (n - (l : ℤ)) (h (n - (l : ℤ))) p alpha

/-- `in_J.err` is carrier-independent at admissible arguments (sub-cube, `s ∈ (0,1]`, `q ≥ 1`,
`a0 > 0`). -/
theorem aux_rem_resolved_meshes_inJ_err_canonical {d : ℕ} (E E' : in_J d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hsub : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (a0 s : ℝ) (q : ℝ≥0∞) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hq : 1 ≤ q) (ha0 : 0 < a0) :
    E.err z r hr a w r' a0 s q = E'.err z r hr a w r' a0 s q := by
  have hchart : ∀ (k : ℤ) (Q : Homogenization.TriadicCube d),
      Q ∈ Homogenization.descendantsAtScale (Homogenization.originCube d 0) k →
        Homogenization.Book.Ch02.CoeffOn.AEEq
          ((E.chart z r hr a w r').coeffOn Q) ((E'.chart z r hr a w r').coeffOn Q) := by
    intro k Q hQmem
    have hk : k ≤ (Homogenization.originCube d 0).scale :=
      Homogenization.descendant_scale_le_of_mem_descendantsAtScale hQmem
    have hQ : Homogenization.openCubeSet Q ⊆
        Homogenization.openCubeSet (Homogenization.originCube d 0) :=
      Homogenization.openCubeSet_subset_of_mem_descendantsAtScale
        (by simpa [Homogenization.originCube] using hk) hQmem
    have h1 := E.chart_eq z r hr a w r' hr' hsub Q hQ
    have h2 := E'.chart_eq z r hr a w r' hr' hsub Q hQ
    change ((E.chart z r hr a w r').coeffOn Q).toCoeffField =ᵐ[
      volume.restrict (Homogenization.openCubeSet Q)]
      ((E'.chart z r hr a w r').coeffOn Q).toCoeffField
    exact Filter.EventuallyEq.trans h1 (Filter.EventuallyEq.symm h2)
  by_cases hqtop : q = ⊤
  · have e1 := E.err_eq z r hr a w r' hr' hsub s hs q hq a0 ha0
    have e2 := E'.err_eq z r hr a w r' hr' hsub s hs q hq a0 ha0
    simp only [if_pos hqtop] at e1 e2
    rw [e1, e2]
    exact congrArg ENNReal.toReal
      (aux_rem_resolved_meshes_error_infinity
        (Homogenization.originCube d 0) 0 s
        Homogenization.Book.Ch02.MultiscaleExponent.infinity a0 hchart)
  · have e1 := E.err_eq z r hr a w r' hr' hsub s hs q hq a0 ha0
    have e2 := E'.err_eq z r hr a w r' hr' hsub s hs q hq a0 ha0
    simp only [if_neg hqtop] at e1 e2
    rw [e1, e2]
    exact congrArg ENNReal.toReal
      (aux_rem_resolved_meshes_error
        (Homogenization.originCube d 0) 0 s
        Homogenization.Book.Ch02.MultiscaleExponent.infinity q.toReal a0 hchart)

/-- Re-index an iteration package at another `in_J` carrier.  Only `good_error` mentions the
carrier; every other field, in particular `prefixLen` and `ref`, is copied unchanged. -/
def aux_rem_resolved_meshes_iteration_transport {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {E : in_J d} (E₀ : in_J d)
    {S : in_6_16 d M} (It : in_iteration d M E S) : in_iteration d M E₀ S :=
  { It with
    good_error := by
      intro L j z hR eps om h1 h2 h3 h4 hg hL
      have hs0 : It.s0 ∈ Set.Ioc (0 : ℝ) 1 := by
        rw [It.s0_eq]; constructor <;> norm_num
      rw [aux_rem_resolved_meshes_inJ_err_canonical E₀ E z _ hR _ z _ hR Set.Subset.rfl _ _ 2
        hs0 (by norm_num) (It.ref_pos L j z om)]
      exact It.good_error L j z hR eps om h1 h2 h3 h4 hg hL }

theorem aux_rem_resolved_meshes_iteration_transport_prefixLen {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {E : in_J d} (E₀ : in_J d)
    {S : in_6_16 d M} (It : in_iteration d M E S) :
    (aux_rem_resolved_meshes_iteration_transport E₀ It).prefixLen = It.prefixLen ∧
      (aux_rem_resolved_meshes_iteration_transport E₀ It).ref = It.ref :=
  ⟨rfl, rfl⟩

/-- Generic uniformization: a `∀ E Poinc Ext D, ∃ c, good c ∧ ∀ M Sreg It, Ψ` whose body reads
`It` only through `prefixLen` and `ref` holds with one `c` for all carriers.  If no carrier tuple
exists the carrier quantifier is empty and any `good` witness serves. -/
theorem aux_rem_resolved_meshes_uniformize (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {ι : Type} (good : ι → Prop) (hgood : ∃ c, good c)
    (Ψ : ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), in_6_16 d M →
      (SpatialCoordinates d → ℝ → ℕ → BilateralField d → ℕ) →
      (ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ) → ι → Prop)
    (h : ∀ (E : in_J d) (_ : in_poincare d hd E) (_ : in_extension d hd E)
      (_ : @lane4_deterministic_good_scale_input d
        ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩),
      ∃ c, good c ∧ ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
        (It : in_iteration d M E Sreg), Ψ M Sreg It.prefixLen It.ref c) :
    ∃ c, good c ∧ ∀ (E : in_J d) (_ : in_poincare d hd E) (_ : in_extension d hd E)
      (_ : @lane4_deterministic_good_scale_input d
        ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
      (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
      (It : in_iteration d M E Sreg), Ψ M Sreg It.prefixLen It.ref c := by
  by_cases hin : ∃ E : in_J d, Nonempty (in_poincare d hd E) ∧
      Nonempty (in_extension d hd E) ∧
      @lane4_deterministic_good_scale_input d ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  · obtain ⟨E₀, ⟨P₀⟩, ⟨X₀⟩, D₀⟩ := hin
    obtain ⟨c, hc, hΨ⟩ := h E₀ P₀ X₀ D₀
    exact ⟨c, hc, fun E P X D M Sreg It =>
      hΨ M Sreg (aux_rem_resolved_meshes_iteration_transport E₀ It)⟩
  · obtain ⟨c, hc⟩ := hgood
    exact ⟨c, hc, fun E P X D => absurd ⟨E, ⟨P⟩, ⟨X⟩, D⟩ hin⟩

/-- The body of `prop_folded_iteration` at constants `(C, K)`, as a predicate of the only two
projections of the iteration package it reads (`prefixLen`, `ref`). -/
def aux_rem_resolved_meshes_folded_core (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (pl : SpatialCoordinates d → ℝ → ℕ → BilateralField d → ℕ)
    (rf : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ) (C K : ℝ) : Prop :=
      M.delta ≤ C⁻¹ →
      ∀ (alpha : ℝ),
        alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * Real.sqrt (abs (Real.log M.delta))) →
        let alphaTight : ℝ := 1 - (1 - alpha) / K
        ∀ (L m n : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
          (om : BilateralField d) (I P : Finset (Fin d)), I.Nonempty → m ≤ L → n ≤ m →
          (n : ℤ) ≤ (m : ℤ) - pl z alphaTight m om →
          ∀ foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR),
            ((foldedCoef.val : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
              fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val (coordinateFold z I P x)) →
          ∀ (g : SpatialCoordinates d → Fin d → ℝ)
            (hgrad : HilbertGradient (centeredCube z ((3 : ℝ) ^ m) hR))
            (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)),
            SubdiffusiveProcess.CoarseGrainingVocab.MemHolder
                (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))
                (1 / 2) g →
            (∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
              =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR :
                Set (SpatialCoordinates d))] fun x => g x i) →
            (∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR),
              sobolevCoefficientForm foldedCoef
                  (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))
                  (φ : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)) =
                -inner ℝ hgrad
                  (subspaceGradient
                    (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)) φ)) →
            normalizedEnergyNorm foldedCoef
                (centeredCube z ((3 : ℝ) ^ n) (by positivity)).isOpen.measurableSet
                (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) ≤
              C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - n)) *
                (normalizedEnergyNorm foldedCoef
                    (centeredCube z ((3 : ℝ) ^ m) hR).isOpen.measurableSet
                    (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) +
                  Real.sqrt (rf L (m - 2) z om)⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) *
                    halfHolderSeminorm
                      (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g)



theorem aux_rem_resolved_meshes_folded_uniform (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ Cf Kf : ℝ, 0 < Cf ∧
      1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ Kf ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (E : in_J d)
        (_ : in_poincare d hd E) (_ : in_extension d hd E)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (_ : @lane4_deterministic_good_scale_input d
          ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩),
        aux_rem_resolved_meshes_folded_core d M Sreg It.prefixLen It.ref Cf Kf := by
  obtain ⟨⟨C, K⟩, ⟨hC, hK⟩, hU⟩ :=
    aux_rem_resolved_meshes_uniformize d hd (ι := ℝ × ℝ)
      (fun p => 0 < p.1 ∧
        1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ p.2)
      ⟨(1, 1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1)), one_pos, le_rfl⟩
      (fun M Sreg pl rf p => aux_rem_resolved_meshes_folded_core d M Sreg pl rf p.1 p.2)
      (fun E P X D => by
        obtain ⟨C, K, hC, hK, h⟩ := prop_folded_iteration d hd E P X D
        exact ⟨(C, K), ⟨hC, hK⟩, fun M Sreg It => h M Sreg It⟩)
  exact ⟨C, K, hC, hK, fun M E P X Sreg It D => hU E P X D M Sreg It⟩

/-! ### Step 1a: pulling an a.e. statement back along a dilation -/

/-- An a.e. statement on `T` pulls back along the dilation `y ↦ c • y` to an a.e. statement on
any `S` that the dilation maps into `T`. -/
theorem aux_rem_resolved_meshes_physical_cutoff_bridge_ae_smul_pullback {d : ℕ} {c : ℝ} (hc : c ≠ 0)
    {S T : Set (SpatialCoordinates d)} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hST : ∀ y ∈ S, c • y ∈ T) {p : SpatialCoordinates d → Prop}
    (h : ∀ᵐ x ∂volume.restrict T, p x) :
    ∀ᵐ y ∂volume.restrict S, p (c • y) := by
  have h' : ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)), x ∈ T → p x :=
    (ae_restrict_iff' hT).1 h
  have h'' : ∀ᵐ y ∂(volume : Measure (SpatialCoordinates d)), c • y ∈ T → p (c • y) :=
    (Measure.quasiMeasurePreserving_smul volume hc).ae h'
  exact (ae_restrict_iff' hS).2 (h''.mono fun y hy hyS => hy (hST y hyS))

/-- The dilation by `3 ^ N` maps the cube `centeredCube z r` into `centeredCube (3^N • z) R`
when `R = 3 ^ N * r`. -/
theorem aux_rem_resolved_meshes_physical_cutoff_bridge_smul_mem_cube {d : ℕ} (N : ℕ) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (R : ℝ) (hR : 0 < R) (hRr : R = (3 : ℝ) ^ (N : ℤ) * r) :
    ∀ y ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      ((3 : ℝ) ^ (N : ℤ)) • y ∈
        (centeredCube (((3 : ℝ) ^ (N : ℤ)) • z) R hR : Set (SpatialCoordinates d)) := by
  intro y hy
  change dist y z < r / 2 at hy
  change dist (((3 : ℝ) ^ (N : ℤ)) • y) (((3 : ℝ) ^ (N : ℤ)) • z) < R / 2
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (N : ℤ) := by positivity
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos h3, hRr]
  have := mul_lt_mul_of_pos_left hy h3
  linarith




/-- `cutoffPositiveCoefficient M H omega N z hr` equals the continuous `cutoffCoefficient`
almost everywhere on its cube. -/
theorem aux_rem_resolved_meshes_physical_cutoff_bridge_cutoffPositiveCoefficient_ae {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H omega N z hr).val x = cutoffCoefficient M H omega N x := by
  have h1 := @normalizedContinuousPositiveCoefficient_coeFn d (centeredCube z r hr)
    (closedCube z r hr) ⟨centeredCube_subset_closedCube z hr⟩
    (cutoffCoefficientCM M H omega N z hr) (cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
  filter_upwards [h1, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxm
  unfold cutoffPositiveCoefficient
  rw [hx hxm, div_one]
  rfl

/-! ### Step 1c: the finite relabelling identity -/

/-- Splitting the relabelled layer sum `∑_{j ≤ N+L'} ω_{j-N}` into the `N+1` physical layers
`ω_0, ω_{-1}, …, ω_{-N}` and the `L'` infrared layers `ω_1, …, ω_{L'}`. -/
theorem aux_rem_resolved_meshes_physical_cutoff_bridge_layer_sum {d : ℕ} (omega : BilateralField d) (N L' : ℕ)
    (y : SpatialCoordinates d) :
    (∑ j ∈ Finset.range (N + L' + 1), omega ((j : ℤ) - (N : ℤ)) y) =
      (∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j)) y) +
        ∑ n ∈ Finset.range L', omega (Int.ofNat (n + 1)) y := by
  rw [show N + L' + 1 = (N + 1) + L' by omega, Finset.sum_range_add]
  congr 1
  · rw [← Finset.sum_range_reflect (fun j : ℕ => omega (-(Int.ofNat j)) y) (N + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    congr 2
    simp only [Int.ofNat_eq_natCast]
    omega
  · apply Finset.sum_congr rfl
    intro n _
    congr 2
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring

/-- The truncated physical coefficient `A_N^{(L')}` (paper line 605: `H` replaced by
`H_{L'}`) is the positive constant
`c_{N,L'} = ahom_N⁻¹ e^{L'τ²} exp(-∑_{n=1}^{L'} ω_n(0))` times the stationary cutoff layer
formula at level `L = N + L'` (paper lines 607–610). -/
theorem aux_rem_resolved_meshes_physical_cutoff_bridge_truncation_identity {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (omega : BilateralField d) (N L' : ℕ)
    (y : SpatialCoordinates d) :
    cutoffCoefficient M (fun om => infraredPartialSum om L') omega N y =
      ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
          Real.exp ((L' : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P -
            ∑ n ∈ Finset.range L', omega (Int.ofNat (n + 1)) 0)) *
        Real.exp ((∑ j ∈ Finset.range (N + L' + 1), omega ((j : ℤ) - (N : ℤ)) y) -
          (((N + L' : ℕ) : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
  rw [aux_rem_resolved_meshes_physical_cutoff_bridge_layer_sum]
  unfold cutoffCoefficient cutoffPotential infraredPartialSum
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.sub_apply,
    ContinuousMap.const_apply]
  rw [mul_assoc, ← Real.exp_add, Finset.sum_sub_distrib]
  congr 2
  push_cast
  ring

/-! ### Step 2: uniform convergence of the truncated coefficients on compacts -/

/-- `cutoffCoefficient` at a fixed sample and scale, as a continuous map of the infrared field
`h ∈ C(ℝ^d, ℝ)` into `C(ℝ^d, ℝ)`: `h ↦ ahom_N⁻¹ exp(h + ∑_{j ≤ N} ω_{-j} - (N+1)τ²)`. -/
def aux_rem_resolved_meshes_physical_cutoff_bridge_coefficientMap {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (omega : BilateralField d) (N : ℕ) :
    C(SpatialCoordinates d, ℝ) → C(SpatialCoordinates d, ℝ) := fun h =>
  (⟨fun t : ℝ => (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
      Real.exp (t - (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P),
    continuous_const.mul (Real.continuous_exp.comp (continuous_id.sub continuous_const))⟩ :
      C(ℝ, ℝ)).comp
    (h + ∑ j ∈ Finset.range (N + 1), omega (-(Int.ofNat j)))

theorem aux_rem_resolved_meshes_physical_cutoff_bridge_coefficientMap_apply {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) :
    aux_rem_resolved_meshes_physical_cutoff_bridge_coefficientMap M omega N (H omega) x =
      cutoffCoefficient M H omega N x := by
  unfold aux_rem_resolved_meshes_physical_cutoff_bridge_coefficientMap cutoffCoefficient cutoffPotential
  simp [ContinuousMap.coe_sum, Finset.sum_apply]

theorem aux_rem_resolved_meshes_physical_cutoff_bridge_coefficientMap_continuous {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (omega : BilateralField d) (N : ℕ) :
    Continuous (aux_rem_resolved_meshes_physical_cutoff_bridge_coefficientMap M omega N) :=
  (ContinuousMap.continuous_postcomp _).comp (continuous_add_right _)

/-- On the infrared-convergence event, the truncated physical coefficients
`A_N^{(L')} = cutoffCoefficient M H_{L'}` converge to `A_N = cutoffCoefficient M H` uniformly
on every compact set (paper line 727: uniformly on `\overline Q`). -/
theorem aux_rem_resolved_meshes_physical_cutoff_bridge_tendstoUniformlyOn {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (hconv : Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)))
    {K : Set (SpatialCoordinates d)} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun L' y => cutoffCoefficient M (fun om => infraredPartialSum om L') omega N y)
      (cutoffCoefficient M H omega N) atTop K := by
  have h := ((aux_rem_resolved_meshes_physical_cutoff_bridge_coefficientMap_continuous M omega N).tendsto
    (H omega)).comp hconv
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn] at h
  have hK' := h K hK
  have e1 : (fun L' y => cutoffCoefficient M (fun om => infraredPartialSum om L') omega N y) =
      fun L' y => ((aux_rem_resolved_meshes_physical_cutoff_bridge_coefficientMap M omega N) ∘ infraredPartialSum omega)
        L' y := by
    funext L' y
    exact (aux_rem_resolved_meshes_physical_cutoff_bridge_coefficientMap_apply M
      (fun om => infraredPartialSum om L') omega N y).symm
  have e2 : cutoffCoefficient M H omega N =
      ⇑(aux_rem_resolved_meshes_physical_cutoff_bridge_coefficientMap M omega N (H omega)) := by
    funext y
    exact (aux_rem_resolved_meshes_physical_cutoff_bridge_coefficientMap_apply M H omega N y).symm
  rw [e1, e2]
  exact hK'




/-- **Deterministic core.** For a sample on which the infrared partial sums converge in
`C(ℝ^d, ℝ)`, the finite physical coefficients
`aFin L' := cutoffPositiveCoefficient M H_{L'} omega N z hr` (paper line 605: `A_N^{(L')}` is
`A_N` with `H` replaced by `H_{L'}`) are, almost everywhere on the cube, positive scalar
multiples of the relabelled stationary cutoff coefficient at level `N + L'` on the dilated
cube, and converge essentially uniformly to the continuous `cutoffCoefficient M H omega N`. -/
theorem aux_rem_resolved_meshes_physical_cutoff_bridge_of_tendsto {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (hconv : Tendsto (infraredPartialSum omega) atTop (𝓝 (H omega)))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ)
    (R : ℝ) (hR : 0 < R) (hRr : R = (3 : ℝ) ^ (N : ℤ) * r) :
    let relabel : ℕ → BilateralField d → BilateralField d :=
      fun N' omega' j =>
        ContinuousMap.compRightContinuousMap ℝ
          (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N' : ℤ)) • x,
            continuous_const.smul continuous_id⟩ :
            C(SpatialCoordinates d, SpatialCoordinates d))
          (omega' (j - (N' : ℤ)))
    let aFin : ℕ → PositiveCoefficient (centeredCube z r hr) :=
      fun L' => cutoffPositiveCoefficient M (fun om => infraredPartialSum om L') omega N z hr
    (∀ L' : ℕ, ∃ cFin : ℝ, 0 < cFin ∧
      ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        (aFin L').val y =
          cFin *
            (Sreg.cutoffOn (N + L') (relabel N omega)
              (((3 : ℝ) ^ (N : ℤ)) • z) R hR).val
              (((3 : ℝ) ^ (N : ℤ)) • y)) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ L₀ : ℕ, ∀ L' : ℕ, L₀ ≤ L' →
        ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
          |(aFin L').val y - cutoffCoefficient M H omega N y| < ε) := by
  intro relabel aFin
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (N : ℤ) := by positivity
  constructor
  · intro L'
    refine ⟨(SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
        Real.exp ((L' : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P -
          ∑ n ∈ Finset.range L', omega (Int.ofNat (n + 1)) 0),
      mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _), ?_⟩
    have hcut := aux_rem_resolved_meshes_physical_cutoff_bridge_ae_smul_pullback h3.ne'
      (centeredCube z r hr).isOpen.measurableSet
      (centeredCube (((3 : ℝ) ^ (N : ℤ)) • z) R hR).isOpen.measurableSet
      (aux_rem_resolved_meshes_physical_cutoff_bridge_smul_mem_cube N z r hr R hR hRr)
      (Sreg.cutoffOn_eq (N + L') (relabel N omega) (((3 : ℝ) ^ (N : ℤ)) • z) R hR)
    filter_upwards [aux_rem_resolved_meshes_physical_cutoff_bridge_cutoffPositiveCoefficient_ae M
      (fun om => infraredPartialSum om L') omega N z hr, hcut] with y hy hcy
    change (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L') omega N z hr).val y
      = _
    rw [hy, hcy, aux_rem_resolved_meshes_physical_cutoff_bridge_truncation_identity]
    congr 3
    apply Finset.sum_congr rfl
    intro j _
    change _ = (omega ((j : ℤ) - (N : ℤ)))
        ((3 : ℝ) ^ (-(N : ℤ)) • ((3 : ℝ) ^ (N : ℤ)) • y)
    rw [smul_smul, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero,
      one_smul]
  · intro ε hε
    have hU := aux_rem_resolved_meshes_physical_cutoff_bridge_tendstoUniformlyOn M H omega N hconv
      (closedCube z r hr).isCompact
    rw [Metric.tendstoUniformlyOn_iff] at hU
    obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 (hU ε hε)
    refine ⟨L₀, fun L' hL' => ?_⟩
    filter_upwards [aux_rem_resolved_meshes_physical_cutoff_bridge_cutoffPositiveCoefficient_ae M
      (fun om => infraredPartialSum om L') omega N z hr,
      ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with y hy hym
    change |(cutoffPositiveCoefficient M (fun om => infraredPartialSum om L') omega N z hr).val y
      - _| < ε
    rw [hy, ← Real.dist_eq, dist_comm]
    exact hL₀ L' hL' y (centeredCube_subset_closedCube z hr hym)



theorem aux_rem_resolved_meshes_physical_cutoff_bridge {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    let relabel : ℕ → BilateralField d → BilateralField d :=
      fun N' omega' j =>
        ContinuousMap.compRightContinuousMap ℝ
          (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N' : ℤ)) • x,
            continuous_const.smul continuous_id⟩ :
            C(SpatialCoordinates d, SpatialCoordinates d))
          (omega' (j - (N' : ℤ)))
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      ∀ (R : ℝ) (hR : 0 < R), R = (3 : ℝ) ^ (N : ℤ) * r →
      ∃ aFin : ℕ → PositiveCoefficient (centeredCube z r hr),
        (∀ L' : ℕ, ∃ cFin : ℝ, 0 < cFin ∧
          ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
            (aFin L').val y =
              cFin *
                (Sreg.cutoffOn (N + L') (relabel N omega)
                  (((3 : ℝ) ^ (N : ℤ)) • z) R hR).val
                  (((3 : ℝ) ^ (N : ℤ)) • y)) ∧
        (∀ ε : ℝ, 0 < ε →
          ∃ L₀ : ℕ, ∀ L' : ℕ, L₀ ≤ L' →
            ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
              |(aFin L').val y - cutoffCoefficient M H omega N y| < ε) := by
  intro relabel
  filter_upwards [hH.2] with omega homega
  intro N R hR hRr
  exact ⟨fun L' => cutoffPositiveCoefficient M (fun om => infraredPartialSum om L') omega N z hr,
    aux_rem_resolved_meshes_physical_cutoff_bridge_of_tendsto M Sreg H omega homega z r hr N R hR hRr⟩



theorem aux_rem_resolved_meshes_physical_cutoff_bridge_unitNeumannCube (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H) :
    let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
    let Q : Opens (SpatialCoordinates d) := unitNeumannCube d
    let relabel : ℕ → BilateralField d → BilateralField d :=
      fun N omega j =>
        ContinuousMap.compRightContinuousMap ℝ
          (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
            continuous_const.smul continuous_id⟩ :
            C(SpatialCoordinates d, SpatialCoordinates d))
          (omega (j - (N : ℤ)))
    ∀ᵐ omega ∂P, ∀ N : ℕ,
      ∃ aFin : ℕ → PositiveCoefficient Q,
        (∀ L' : ℕ, ∃ cFin : ℝ, 0 < cFin ∧
          ∀ᵐ y ∂volume.restrict (Q : Set (SpatialCoordinates d)),
            (aFin L').val y =
              cFin *
                (Sreg.cutoffOn (N + L') (relabel N omega)
                  ((3 : ℝ) ^ (N : ℤ) •
                    (fun _ : Fin d => (1 / 2 : ℝ)))
                  ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val
                  (((3 : ℝ) ^ (N : ℤ)) • y)) ∧
        (∀ ε : ℝ, 0 < ε →
          ∃ L₀ : ℕ, ∀ L' : ℕ, L₀ ≤ L' →
            ∀ᵐ y ∂volume.restrict (Q : Set (SpatialCoordinates d)),
              |(aFin L').val y - cutoffCoefficient M H omega N y| < ε) := by
  intro P Q relabel
  filter_upwards [aux_rem_resolved_meshes_physical_cutoff_bridge M Sreg H hH (fun _ : Fin d => (1 / 2 : ℝ))
    1 one_pos] with omega homega N
  exact homega N ((3 : ℝ) ^ (N : ℤ)) (by positivity) (mul_one _).symm



theorem aux_rem_resolved_meshes_physical_cutoff_bridge_macro (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
          ∀ (N : ℕ),
            let relabel : ℕ → BilateralField d → BilateralField d := fun N' omega j =>
              ContinuousMap.compRightContinuousMap ℝ
                (⟨fun x : SpatialCoordinates d =>
                    (3 : ℝ) ^ (-(N' : ℤ)) • x,
                  continuous_const.smul continuous_id⟩ :
                  C(SpatialCoordinates d, SpatialCoordinates d))
                (omega (j - (N' : ℤ)))
            ∃ aFin : ℕ → PositiveCoefficient (centeredCube z r hr),
              (∀ L' : ℕ, ∃ cFin : ℝ, 0 < cFin ∧
                ∀ᵐ y ∂volume.restrict
                    (centeredCube z r hr : Set (SpatialCoordinates d)),
                  (aFin L').val y =
                    cFin *
                      (Sreg.cutoffOn (N + L') (relabel N om)
                        ((3 : ℝ) ^ (N : ℤ) • z)
                        ((3 : ℝ) ^ (N : ℤ) * r) (by positivity)).val
                        ((3 : ℝ) ^ (N : ℤ) • y)) ∧
              (∀ ε : ℝ, 0 < ε →
                ∃ L₀ : ℕ, ∀ L' : ℕ, L₀ ≤ L' →
                  ∀ᵐ y ∂volume.restrict
                    (centeredCube z r hr : Set (SpatialCoordinates d)),
                    |(aFin L').val y -
                        cutoffCoefficient M H om N y| < ε) := by
  filter_upwards [aux_rem_resolved_meshes_physical_cutoff_bridge M Sreg H hH z r hr] with om hom N
  exact hom N ((3 : ℝ) ^ (N : ℤ) * r) (by positivity) rfl


/-! ### Assembly: folded one-step, finite-cutoff transfer and two-mesh application -/

def aux_rem_resolved_meshes_Rbound (d J : ℕ) (eta q Cstep K : ℝ) : ℝ≥0∞ :=
  (∑' n : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-eta * (n : ℝ))) *
    (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
        ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ≥0∞) ^
      (1 / (ENNReal.ofReal q).toReal)) *
    (ENNReal.ofReal (Cstep ^ (d + 1)) *
      ENNReal.ofReal (((d : ℝ) + 1) * K) ^ (d + 1 : ℝ))

/-- `lane4_regularity_mesh_statistic`, second clause, with its `L^p` bound exhibited as
`aux_rem_resolved_meshes_Rbound` (the frozen export quantifies that bound after the probability
space).  The proof is the frozen proof, using its public helpers. -/
theorem aux_rem_resolved_meshes_regularity (d J : ℕ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p q eta : ℝ) (hp : 1 ≤ p) (hpq : p ≤ q) (heta : 0 < eta) (hgap : (d : ℝ) < q * eta)
    (Cstep c K : ℝ) (hCstep : 1 ≤ Cstep) (hc : 0 ≤ c) (hK : 1 ≤ K)
    (B : (N : ℕ) → (n : ℕ) → ((Fin d → Fin (3 ^ (n + J) + 1)) ×
        ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) → Fin (d + 1) → Ω → ℝ)
    (hBnonneg : ∀ N n pi i om, 0 ≤ B N n pi i om)
    (hBmem : ∀ N n pi i, MemLp (fun om => Real.exp (c * B N n pi i om))
      (ENNReal.ofReal (((d : ℝ) + 1) * q)) P)
    (hBnorm : ∀ N n pi i, eLpNorm (fun om => Real.exp (c * B N n pi i om))
      (ENNReal.ofReal (((d : ℝ) + 1) * q)) P ≤ ENNReal.ofReal K) :
    ∃ U : ℕ → Ω → ℝ,
      (∀ N, Measurable (U N)) ∧
      (∀ N om, 0 ≤ U N om) ∧
      (∀ N, MemLp (U N) (ENNReal.ofReal p) P) ∧
      (∀ N, eLpNorm (U N) (ENNReal.ofReal p) P ≤ aux_rem_resolved_meshes_Rbound d J eta q Cstep K) ∧
      (∀ᵐ om ∂P, ∀ N,
        IsLUB {v : ℝ | ∃ n : ℕ, ∃ pi,
          v = (3 : ℝ) ^ (-eta * (n : ℝ)) *
            (Cstep ^ (d + 1) * Real.exp (c * ∑ i : Fin (d + 1), B N n pi i om))} (U N om)) ∧
      aux_rem_resolved_meshes_Rbound d J eta q Cstep K ≠ (⊤ : ℝ≥0∞) := by
  obtain ⟨Ccount, Cd, hCcount, hCd, hcard, hCdEq⟩ :=
    aux_lane4_regularity_mesh_statistic_card_bound d J
  have hp0 : 0 ≤ p := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one (hp.trans hpq)
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hpqE : ENNReal.ofReal p ≤ ENNReal.ofReal q :=
    ENNReal.ofReal_le_ofReal hpq
  have hqtop : ENNReal.ofReal q ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hqgap : (d : ℝ) < (ENNReal.ofReal q).toReal * eta := by
    simpa [ENNReal.toReal_ofReal hq0] using hgap
  let Cenv : ℝ := Ccount * (Ccount + 1) ^ (d + 1 : ℕ)
  have hCenv : 0 ≤ Cenv := by
    dsimp [Cenv]
    positivity
  have hcard_env : ∀ n : ℕ, (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
        ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ) ≤
      Cenv * ((n : ℝ) + 1) ^ (d + 1 : ℕ) *
        (3 : ℝ) ^ ((d : ℝ) * n) := by
    intro n
    calc
      _ ≤ Ccount * ((n : ℝ) + Ccount) ^ Cd *
          (3 : ℝ) ^ ((d : ℝ) * n) := hcard n
      _ ≤ Cenv * ((n : ℝ) + 1) ^ (d + 1 : ℕ) *
          (3 : ℝ) ^ ((d : ℝ) * n) := by
        have hn : (n : ℝ) + Ccount ≤ (Ccount + 1) * ((n : ℝ) + 1) := by
          nlinarith [hCcount]
        have hCd' : ((n : ℝ) + Ccount) ^ Cd =
            ((n : ℝ) + Ccount) ^ (d + 1 : ℕ) := by
          rw [hCdEq]
          exact Real.rpow_natCast _ _
        rw [hCd']
        have hpow := pow_le_pow_left₀ (by positivity) hn (d + 1)
        calc
          Ccount * ((n : ℝ) + Ccount) ^ (d + 1 : ℕ) *
              (3 : ℝ) ^ ((d : ℝ) * n) ≤
              Ccount * ((Ccount + 1) * ((n : ℝ) + 1)) ^ (d + 1 : ℕ) *
                (3 : ℝ) ^ ((d : ℝ) * n) := by
                  gcongr
          _ = Cenv * ((n : ℝ) + 1) ^ (d + 1 : ℕ) *
              (3 : ℝ) ^ ((d : ℝ) * n) := by
                dsimp [Cenv]
                rw [mul_pow]
                ring
  have hinhab : ∀ n : ℕ,
      Nonempty ((Fin d → Fin (3 ^ (n + J) + 1)) ×
        ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) := by
    intro n
    have hgrid : 0 < 3 ^ (n + J) + 1 := by positivity
    have hroot : 0 < n + J + 1 := by positivity
    exact ⟨(fun _ => ⟨0, hgrid⟩,
      (fun _ => ⟨0, hroot⟩, Equiv.refl _))⟩
  let KZ : ℝ≥0∞ := ENNReal.ofReal (Cstep ^ (d + 1)) *
    ENNReal.ofReal (((d : ℝ) + 1) * K) ^ (d + 1 : ℝ)
  have hKZtop : KZ ≠ (⊤ : ℝ≥0∞) := by
    dsimp [KZ]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by finiteness))
  have hZmem : ∀ N n pi, MemLp
      (fun om => Cstep ^ (d + 1) * Real.exp (c *
        ∑ i : Fin (d + 1), B N n pi i om)) (ENNReal.ofReal q) P := by
    intro N n pi
    have hprod := aux_lane4_regularity_mesh_statistic_product_moment P d q K c
      (by linarith) hK (fun i om => B N n pi i om)
      (fun i => by simpa using hBmem N n pi i)
      (fun i => by simpa using hBnorm N n pi i)
    exact hprod.1.const_mul (Cstep ^ (d + 1))
  have henv : ∀ N : ℕ, ∃ W : Ω → ℝ, MemLp W (ENNReal.ofReal p) P ∧
      (∀ᵐ om ∂P, 0 ≤ W om ∧ ∀ n pi,
        |(Cstep ^ (d + 1) * Real.exp (c *
          ∑ i : Fin (d + 1), B N n pi i om))| ≤
          W om * (3 : ℝ) ^ (eta * n)) ∧
      eLpNorm W (ENNReal.ofReal p) P ≤
        (∑' n : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-eta * n)) *
        (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
            ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ≥0∞) ^
              (1 / (ENNReal.ofReal q).toReal)) * KZ := by
    intro N
    have hZae : ∀ n pi, AEStronglyMeasurable
        (fun om => Cstep ^ (d + 1) * Real.exp (c *
          ∑ i : Fin (d + 1), B N n pi i om)) P := by
      intro n pi
      exact (hZmem N n pi).1
    have hZnorm : ∀ n pi, eLpNorm
        (fun om => Cstep ^ (d + 1) * Real.exp (c *
          ∑ i : Fin (d + 1), B N n pi i om)) (ENNReal.ofReal q) P ≤ KZ := by
      intro n pi
      dsimp [KZ]
      rw [show (fun om => Cstep ^ (d + 1) *
        Real.exp (c * ∑ i : Fin (d + 1), B N n pi i om)) =
          (Cstep ^ (d + 1)) •
            (fun om => Real.exp (c * ∑ i : Fin (d + 1), B N n pi i om)) by
        funext om; simp [smul_eq_mul]]
      rw [eLpNorm_const_smul]
      rw [Real.enorm_of_nonneg (by positivity)]
      exact mul_le_mul_left' (aux_lane4_regularity_mesh_statistic_product_moment P d q K c
        (by linarith) hK (fun i om => B N n pi i om)
        (fun i => by simpa using hBmem N n pi i)
        (fun i => by simpa using hBnorm N n pi i)).2 _
    have hgen := aux_lane4_regularity_mesh_statistic_envelope P
      (ι := fun n => (Fin d → Fin (3 ^ (n + J) + 1)) ×
        ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d)))
      hinhab d (d + 1) Cenv eta hCenv hpE hpqE hqtop hqgap
      (by simpa only [Nat.card_eq_fintype_card] using hcard_env)
      (fun n pi om => Cstep ^ (d + 1) * Real.exp (c *
        ∑ i : Fin (d + 1), B N n pi i om))
      hZae KZ hKZtop hZnorm
    simpa only [Nat.card_eq_fintype_card] using hgen
  choose W hW hWdom hWbound using henv
  let I : Type := Σ n : ℕ,
    (Fin d → Fin (3 ^ (n + J) + 1)) ×
      ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))
  let f : ℕ → I → Ω → ℝ := fun N z om =>
    (3 : ℝ) ^ (-(eta * (z.1 : ℝ))) *
      (Cstep ^ (d + 1) * Real.exp (c *
        ∑ i : Fin (d + 1), B N z.1 z.2 i om))
  have hfmem : ∀ N z, MemLp (f N z) (ENNReal.ofReal p) P := by
    intro N z
    rcases z with ⟨n, pi⟩
    dsimp [f]
    exact (hZmem N n pi).mono_exponent hpqE |>.const_mul
      ((3 : ℝ) ^ (-(eta * (n : ℝ))))
  have hfmeas : ∀ N z, AEMeasurable (f N z) P := by
    intro N z
    exact (hfmem N z).1.aemeasurable
  let V : ℕ → Ω → ℝ := fun N om => ⨆ z : I, f N z om
  have hVae : ∀ N, AEMeasurable (V N) P := by
    intro N
    apply AEMeasurable.iSup (hfmeas N)
  let U : ℕ → Ω → ℝ := fun N om =>
    max 0 ((hVae N).mk (V N) om)
  let Rbound : ℝ≥0∞ :=
    (∑' n : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-eta * (n : ℝ))) *
      (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
        ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ≥0∞) ^
          (1 / (ENNReal.ofReal q).toReal)) * KZ
  let Cp : ℝ := Rbound.toReal
  let z0 : I := ⟨0, Classical.choice (hinhab 0)⟩
  letI : Nonempty I := ⟨z0⟩
  have hf_nonneg : ∀ N z om, 0 ≤ f N z om := by
    intro N z om
    dsimp [f]
    positivity
  have hVmk : ∀ᵐ om ∂P, ∀ N, (hVae N).mk (V N) om = V N om := by
    rw [ae_all_iff]
    intro N
    exact (hVae N).ae_eq_mk.symm
  have hWdom_all : ∀ᵐ om ∂P, ∀ N n pi,
      |Cstep ^ (d + 1) * Real.exp (c *
        ∑ i : Fin (d + 1), B N n pi i om)| ≤
        W N om * (3 : ℝ) ^ (eta * n) := by
    rw [ae_all_iff]
    intro N
    exact (hWdom N).mono (fun om hom n pi => hom.2 n pi)
  have hWnonneg_all : ∀ᵐ om ∂P, ∀ N, 0 ≤ W N om := by
    rw [ae_all_iff]
    intro N
    exact (hWdom N).mono (fun om hom => hom.1)
  have hupper : ∀ᵐ om ∂P, ∀ N z, f N z om ≤ W N om := by
    filter_upwards [hWdom_all] with om hom N z
    rcases z with ⟨n, pi⟩
    have hz := hom N n pi
    have ha : 0 < (3 : ℝ) ^ (-(eta * (n : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hznonneg : 0 ≤ Cstep ^ (d + 1) * Real.exp
        (c * ∑ i : Fin (d + 1), B N n pi i om) := by positivity
    calc
      f N ⟨n, pi⟩ om = (3 : ℝ) ^ (-(eta * (n : ℝ))) *
          |Cstep ^ (d + 1) * Real.exp (c *
            ∑ i : Fin (d + 1), B N n pi i om)| := by
              simp [f, abs_of_nonneg hznonneg]
      _ ≤ (3 : ℝ) ^ (-(eta * (n : ℝ))) *
          (W N om * (3 : ℝ) ^ (eta * (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hz ha.le
      _ = W N om := by
        calc
          (3 : ℝ) ^ (-(eta * (n : ℝ))) *
              (W N om * (3 : ℝ) ^ (eta * (n : ℝ))) =
            W N om * ((3 : ℝ) ^ (-(eta * (n : ℝ))) *
              (3 : ℝ) ^ (eta * (n : ℝ))) := by ring
          _ = W N om := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
            simp
  have hVupper : ∀ᵐ om ∂P, ∀ N, V N om ≤ W N om := by
    filter_upwards [hupper] with om hom N
    exact ciSup_le (fun z => hom N z)
  have hV_nonneg_ae : ∀ᵐ om ∂P, ∀ N, 0 ≤ V N om := by
    filter_upwards [hupper] with om hom N
    have hBdd : BddAbove (Set.range (fun z : I => f N z om)) := by
      refine ⟨W N om, ?_⟩
      rintro _ ⟨z, rfl⟩
      exact hom N z
    exact (hf_nonneg N z0 om).trans (le_ciSup hBdd z0)
  have hUeq : ∀ᵐ om ∂P, ∀ N, U N om = V N om := by
    filter_upwards [hVmk, hV_nonneg_ae] with om hom hnonneg N
    dsimp [U]
    rw [hom N]
    exact max_eq_right (hnonneg N)
  have hUdom : ∀ᵐ om ∂P, ∀ N, ‖U N om‖ ≤ ‖W N om‖ := by
    filter_upwards [hUeq, hVupper, hWnonneg_all, hV_nonneg_ae] with
      om hEq hVup hWnonneg hVnonneg N
    rw [hEq N]
    rw [Real.norm_eq_abs, abs_of_nonneg (hVnonneg N)]
    rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg N)]
    exact hVup N
  have hrealR : Summable (fun n : ℕ =>
      (3 : ℝ) ^ (-eta * (n : ℝ)) *
        (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
          ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ) ^
          (1 / q)) :=
    aux_lane4_regularity_mesh_statistic_summable_cardinality
      (fun n => Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
        ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))))
      d (d + 1) Cenv q eta hCenv (by linarith) hgap hcard_env
  have hRbound : Rbound ≠ (⊤ : ℝ≥0∞) := by
    have hterm : ∀ n : ℕ,
        ENNReal.ofReal ((3 : ℝ) ^ (-eta * (n : ℝ))) *
            (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
              ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ≥0∞) ^
              (1 / (ENNReal.ofReal q).toReal) =
          ENNReal.ofReal ((3 : ℝ) ^ (-eta * (n : ℝ)) *
            (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
              ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ) ^
              (1 / q)) := by
      intro n
      have hpowtop :
          (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
            ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ≥0∞) ^
              (1 / (ENNReal.ofReal q).toReal) ≠ (⊤ : ℝ≥0∞) :=
        ENNReal.rpow_ne_top_of_nonneg (by positivity) (by finiteness)
      have hpowreal :
          ((Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
            ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ≥0∞) ^
              (1 / (ENNReal.ofReal q).toReal)).toReal =
            (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
              ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ) ^ (1 / q) := by
        rw [← ENNReal.toReal_rpow]
        norm_cast
        simp [ENNReal.toReal_ofReal hq0]
      rw [← ENNReal.ofReal_toReal hpowtop, hpowreal]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    dsimp [Rbound]
    rw [show (∑' n : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-eta * (n : ℝ))) *
        (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
          ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ≥0∞) ^
            (1 / (ENNReal.ofReal q).toReal)) =
        ∑' n : ℕ, ENNReal.ofReal ((3 : ℝ) ^ (-eta * (n : ℝ)) *
          (Nat.card ((Fin d → Fin (3 ^ (n + J) + 1)) ×
            ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))) : ℝ) ^
              (1 / q)) by
          apply tsum_congr
          exact hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hrealR]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKZtop

  refine ⟨U, ?_, ?_, ?_, ?_, ?_, hRbound⟩
  · intro N
    dsimp [U]
    exact Measurable.max measurable_const (hVae N).measurable_mk
  · intro N om
    dsimp [U]
    exact le_max_left _ _
  · intro N
    apply MemLp.of_le (hW N)
      ((Measurable.max measurable_const (hVae N).measurable_mk).aestronglyMeasurable)
    exact hUdom.mono (fun om hom => hom N)
  · intro N
    calc
      eLpNorm (U N) (ENNReal.ofReal p) P ≤
          eLpNorm (W N) (ENNReal.ofReal p) P :=
        eLpNorm_mono_ae (hUdom.mono (fun om hom => hom N))
      _ ≤ Rbound := hWbound N
  · filter_upwards [hUeq, hVupper, hupper] with om hEq hVup hpoint N
    have hBdd : BddAbove (Set.range (fun z : I => f N z om)) := by
      refine ⟨W N om, ?_⟩
      rintro _ ⟨z, rfl⟩
      exact hpoint N z
    have hL : IsLUB (Set.range (fun z : I => f N z om)) (V N om) :=
      isLUB_ciSup hBdd
    have hset :
        {v : ℝ | ∃ n : ℕ, ∃ pi,
          v = (3 : ℝ) ^ (-eta * (n : ℝ)) *
            (Cstep ^ (d + 1) * Real.exp (c *
              ∑ i : Fin (d + 1), B N n pi i om))} =
          Set.range (fun z : I => f N z om) := by
      ext v
      constructor
      · rintro ⟨n, pi, rfl⟩
        refine ⟨⟨n, pi⟩, ?_⟩
        dsimp [f]
        ring
      · rintro ⟨z, rfl⟩
        rcases z with ⟨n, pi⟩
        refine ⟨n, pi, ?_⟩
        dsimp [f]
        ring
    rw [hset, hEq N]
    simpa [V] using hL


/-- The relabelling of the original field at cutoff `N`: layer `j` of the relabelled field is the
original layer `j - N`, read at `3^{-N} x`. -/
def aux_rem_resolved_meshes_relabel {d : ℕ} (N : ℕ) (omega : BilateralField d) : BilateralField d :=
  fun j => ContinuousMap.compRightContinuousMap ℝ
    (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
      continuous_const.smul continuous_id⟩ :
      C(SpatialCoordinates d, SpatialCoordinates d))
    (omega (j - (N : ℤ)))

theorem aux_rem_resolved_meshes_layerScaling_comp {d : ℕ} (N : ℕ) (j : ℤ) :
    (layerScaling d (N : ℤ)).comp (layerScaling d (j - (N : ℤ))) = layerScaling d j := by
  ext g x
  simp only [layerScaling, ContinuousMap.comp_apply, ContinuousMap.compRightContinuousMap_apply,
    ContinuousMap.coe_mk]
  congr 1
  rw [smul_smul, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  congr 2
  ring

/-- The relabelling at cutoff `N` preserves the common-scale law (paper 33–37: the layer at
index `j` has the law of the root layer rescaled by `3^{-j}`, independently over `j`). -/
theorem aux_rem_resolved_meshes_relabel_mp {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    MeasurePreserving (aux_rem_resolved_meshes_relabel (d := d) N)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure := by
  set ν := chaosRootFieldLaw M
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j : Measure C(SpatialCoordinates d, ℝ))
  have hP : (chaosSampleLaw M).toMeasure = Measure.infinitePi laws := rfl
  let S : C(SpatialCoordinates d, ℝ) → C(SpatialCoordinates d, ℝ) := layerScaling d (N : ℤ)
  have hS : Measurable S := (layerScaling d (N : ℤ)).continuous.measurable
  have hshift_eq : (MeasurableEquiv.piCongrLeft (fun _ : ℤ => C(SpatialCoordinates d, ℝ))
      (Equiv.addRight (N : ℤ)) : BilateralField d → BilateralField d) =
      fun omega j => omega (j - (N : ℤ)) := by
    funext omega j
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, sub_eq_add_neg]
  have hshift_meas : Measurable (fun (omega : BilateralField d) (j : ℤ) => omega (j - (N : ℤ))) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply (j - (N : ℤ)))
  have hrel_eq : aux_rem_resolved_meshes_relabel (d := d) N =
      (fun (x : BilateralField d) (j : ℤ) => S (x j)) ∘
        (fun (omega : BilateralField d) (j : ℤ) => omega (j - (N : ℤ))) := by
    funext omega j
    rfl
  have hmeas_comp : Measurable (fun (x : BilateralField d) (j : ℤ) => S (x j)) :=
    measurable_pi_lambda _ (fun j => hS.comp (measurable_pi_apply j))
  refine ⟨hrel_eq ▸ hmeas_comp.comp hshift_meas, ?_⟩
  rw [hrel_eq, ← Measure.map_map hmeas_comp hshift_meas, hP]
  have h1 : (Measure.infinitePi laws).map (fun (omega : BilateralField d) (j : ℤ) =>
      omega (j - (N : ℤ))) = Measure.infinitePi (fun j => laws (j - (N : ℤ))) := by
    have h := Measure.infinitePi_map_piCongrLeft (fun j => laws (j - (N : ℤ)))
      (Equiv.addRight (N : ℤ))
    rw [hshift_eq] at h
    have hl : (fun a : ℤ => laws ((Equiv.addRight (N : ℤ)) a - (N : ℤ))) = laws := by
      funext a
      simp
    rw [hl] at h
    exact h
  rw [h1]
  refine (Measure.infinitePi_map_pi (μ := fun j => laws (j - (N : ℤ))) (f := fun _ => S)
    (fun _ => hS)).trans ?_
  congr 1
  funext j
  change ((scaledLayerLaw d ν (j - (N : ℤ)) : Measure C(SpatialCoordinates d, ℝ))).map
      (layerScaling d (N : ℤ)) = (scaledLayerLaw d ν j : Measure C(SpatialCoordinates d, ℝ))
  simp only [scaledLayerLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (layerScaling d (N : ℤ)).continuous.measurable
    (layerScaling d (j - (N : ℤ))).continuous.measurable]
  congr 1
  exact congrArg (fun F : C(C(SpatialCoordinates d, ℝ), C(SpatialCoordinates d, ℝ)) =>
    (F : C(SpatialCoordinates d, ℝ) → C(SpatialCoordinates d, ℝ)))
    (aux_rem_resolved_meshes_layerScaling_comp N j)

/-- A natural-valued prefix length with an exponential tail beyond a shift `A` has uniformly
bounded exponential moments once the tail rate is twice the moment rate. -/
theorem aux_rem_resolved_meshes_prefix_moment {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℕ) (hX : Measurable X)
    (A beta c r : ℝ) (hA : 0 ≤ A) (hc : 0 < c) (hr : 1 ≤ r) (hbeta : 2 * (r * c) ≤ beta)
    (htail : ∀ k' : ℕ, P {om | k' < X om} ≤
      ENNReal.ofReal (A * Real.exp (-(beta * max ((k' : ℝ) - A) 0)))) :
    MemLp (fun om => Real.exp (c * (X om : ℝ))) (ENNReal.ofReal r) P ∧
      eLpNorm (fun om => Real.exp (c * (X om : ℝ))) (ENNReal.ofReal r) P ≤
        ENNReal.ofReal (Real.exp (c * (A + 1)) * (1 + A)) := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hrc : 0 < r * c := mul_pos hr0 hc
  have hbeta0 : 0 < beta := by linarith
  let Y : Ω → ℝ := fun om => max 0 ((X om : ℝ) - (A + 1))
  have hYm : Measurable Y :=
    measurable_const.max ((measurable_from_top.comp hX).sub measurable_const)
  have hY0 : ∀ om, 0 ≤ Y om := fun om => le_max_left _ _
  have hYtail : ∀ t : ℝ, 0 ≤ t → P {om | t < Y om} ≤ ENNReal.ofReal (A * Real.exp (-beta * t)) := by
    intro t ht
    have hsub : {om | t < Y om} ⊆ {om | ⌈t + A⌉₊ < X om} := by
      intro om hom
      simp only [Set.mem_setOf_eq] at hom ⊢
      have h1 : t < (X om : ℝ) - (A + 1) := by
        rcases le_total 0 ((X om : ℝ) - (A + 1)) with h | h
        · simpa [Y, max_eq_right h] using hom
        · have : Y om = 0 := max_eq_left h
          linarith
      have h2 : (⌈t + A⌉₊ : ℝ) < t + A + 1 := Nat.ceil_lt_add_one (by linarith)
      exact_mod_cast (show (⌈t + A⌉₊ : ℝ) < X om by linarith)
    refine (measure_mono hsub).trans ((htail _).trans (ENNReal.ofReal_le_ofReal ?_))
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    have h3 : t ≤ max ((⌈t + A⌉₊ : ℝ) - A) 0 :=
      le_max_of_le_left (by linarith [Nat.le_ceil (t + A)])
    nlinarith
  obtain ⟨hmem, hnorm⟩ := aux_rem_resolved_strata_tail_moment P Y hYm hY0 A beta c r hA hc.le hr0
    (by linarith) hYtail
  have hfrac : A * (r * c) / (beta - r * c) ≤ A := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hbase : (1 + A * (r * c) / (beta - r * c)) ^ (1 / r) ≤ 1 + A := by
    have h1 : 1 ≤ 1 + A * (r * c) / (beta - r * c) := by
      have : 0 ≤ A * (r * c) / (beta - r * c) := div_nonneg (by positivity) (by linarith)
      linarith
    calc (1 + A * (r * c) / (beta - r * c)) ^ (1 / r)
        ≤ (1 + A * (r * c) / (beta - r * c)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by rw [div_le_one hr0]; exact hr)
      _ ≤ 1 + A := by rw [Real.rpow_one]; linarith
  have hpt : ∀ om, ‖Real.exp (c * (X om : ℝ))‖ ≤
      ‖Real.exp (c * (A + 1)) * Real.exp (c * Y om)‖ := by
    intro om
    rw [Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : (X om : ℝ) - (A + 1) ≤ Y om := le_max_right _ _
    nlinarith
  have hmem2 : MemLp (fun om => Real.exp (c * (A + 1)) * Real.exp (c * Y om)) (ENNReal.ofReal r) P :=
    hmem.const_mul _
  refine ⟨hmem2.mono' ?_ ?_, ?_⟩
  · exact (by fun_prop : Measurable fun om => Real.exp (c * (X om : ℝ))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun om => (hpt om).trans (le_of_eq (Real.norm_of_nonneg
      (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le))
  · calc eLpNorm (fun om => Real.exp (c * (X om : ℝ))) (ENNReal.ofReal r) P
        ≤ eLpNorm (fun om => Real.exp (c * (A + 1)) * Real.exp (c * Y om)) (ENNReal.ofReal r) P :=
          eLpNorm_mono hpt
      _ = ENNReal.ofReal (Real.exp (c * (A + 1))) *
            eLpNorm (fun om => Real.exp (c * Y om)) (ENNReal.ofReal r) P := by
          rw [show (fun om => Real.exp (c * (A + 1)) * Real.exp (c * Y om)) =
              (Real.exp (c * (A + 1))) • (fun om => Real.exp (c * Y om)) by
            funext om; simp [smul_eq_mul], eLpNorm_const_smul,
            Real.enorm_of_nonneg (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (Real.exp (c * (A + 1))) * ENNReal.ofReal (1 + A) := by
          gcongr
          exact hnorm.trans (ENNReal.ofReal_le_ofReal hbase)
      _ = ENNReal.ofReal (Real.exp (c * (A + 1)) * (1 + A)) :=
          (ENNReal.ofReal_mul (Real.exp_pos _).le).symm

/-- Exponential moments of the relabelled original prefix length, uniform in the centre, the
depth and the cutoff: `It.prefix_tail` is read through the law-preserving relabelling. -/
theorem aux_rem_resolved_meshes_prefix_relabel_moment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {E : in_J d} {Sreg : in_6_16 d M}
    (It : in_iteration d M E Sreg) (cC : ℝ) (hcC : It.C = cC) (hcC1 : 1 ≤ cC)
    (alphaT : ℝ) (hαT : alphaT ∈ It.alphaRange) (hδ : M.delta ≤ It.C⁻¹)
    (c r : ℝ) (hc : 0 < c) (hr : 1 ≤ r)
    (hrate : 2 * (r * c) ≤
      (1 - alphaT) ^ 2 / (cC * M.delta ^ 2 * |Real.log M.delta|))
    (z : SpatialCoordinates d) (m N : ℕ) :
    MemLp (fun om => Real.exp (c *
        (It.prefixLen z alphaT m (aux_rem_resolved_meshes_relabel N om) : ℝ)))
      (ENNReal.ofReal r) (chaosSampleLaw M).toMeasure ∧
    eLpNorm (fun om => Real.exp (c *
        (It.prefixLen z alphaT m (aux_rem_resolved_meshes_relabel N om) : ℝ)))
      (ENNReal.ofReal r) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.exp (c * (cC + 1)) * (1 + cC)) := by
  have hmp := aux_rem_resolved_meshes_relabel_mp M N
  have hXm : Measurable (fun om => It.prefixLen z alphaT m (aux_rem_resolved_meshes_relabel N om)) :=
    (It.prefix_measurable z alphaT m).comp hmp.measurable
  refine aux_rem_resolved_meshes_prefix_moment (chaosSampleLaw M).toMeasure _ hXm cC
    ((1 - alphaT) ^ 2 / (cC * M.delta ^ 2 * |Real.log M.delta|)) c r (by linarith) hc hr hrate ?_
  intro k'
  have hpre : {om | k' < It.prefixLen z alphaT m (aux_rem_resolved_meshes_relabel N om)} =
      aux_rem_resolved_meshes_relabel N ⁻¹' {om | k' < It.prefixLen z alphaT m om} := rfl
  have hset : MeasurableSet {om : BilateralField d | k' < It.prefixLen z alphaT m om} :=
    measurableSet_lt measurable_const (It.prefix_measurable z alphaT m)
  rw [hpre, hmp.measure_preimage hset.nullMeasurableSet]
  have ht := It.prefix_tail z alphaT hαT hδ m k'
  rw [hcC] at ht
  refine ht.trans (le_of_eq ?_)
  congr 3
  ring

/-- The allowance moment in the form consumed by the first-mesh statistic. -/
theorem aux_rem_resolved_meshes_allowance_moment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {E : in_J d} {Sreg : in_6_16 d M}
    (It : in_iteration d M E Sreg) (cC : ℝ) (hcC : It.C = cC) (hcC1 : 1 ≤ cC)
    (alphaT : ℝ) (hαT : alphaT ∈ It.alphaRange) (hδ : M.delta ≤ It.C⁻¹)
    (c r : ℝ) (hc : 0 < c) (hr : 1 ≤ r)
    (hrate : 2 * (r * c) ≤
      (1 - alphaT) ^ 2 / (cC * M.delta ^ 2 * |Real.log M.delta|))
    (J : ℕ) (z : SpatialCoordinates d) (N kk : ℕ) :
    MemLp (fun om => Real.exp (c *
        (if kk ≤ N then
          (It.prefixLen z alphaT (N - kk + J) (aux_rem_resolved_meshes_relabel N om) : ℝ) +
            (J : ℝ) + (It.k : ℝ) + 5
        else 0)))
      (ENNReal.ofReal r) (chaosSampleLaw M).toMeasure ∧
    eLpNorm (fun om => Real.exp (c *
        (if kk ≤ N then
          (It.prefixLen z alphaT (N - kk + J) (aux_rem_resolved_meshes_relabel N om) : ℝ) +
            (J : ℝ) + (It.k : ℝ) + 5
        else 0)))
      (ENNReal.ofReal r) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Real.exp (c * ((J : ℝ) + 26)) *
        (Real.exp (c * (cC + 1)) * (1 + cC))) := by
  have hK1 : 1 ≤ Real.exp (c * ((J : ℝ) + 26)) * (Real.exp (c * (cC + 1)) * (1 + cC)) := by
    have h1 : 1 ≤ Real.exp (c * ((J : ℝ) + 26)) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ Real.exp (c * (cC + 1)) := Real.one_le_exp (by positivity)
    have h3 : 1 ≤ Real.exp (c * (cC + 1)) * (1 + cC) :=
      one_le_mul_of_one_le_of_one_le h2 (by linarith)
    exact one_le_mul_of_one_le_of_one_le h1 h3
  by_cases hk : kk ≤ N
  · simp only [if_pos hk]
    obtain ⟨hmem, hnorm⟩ := aux_rem_resolved_meshes_prefix_relabel_moment It cC hcC hcC1 alphaT
      hαT hδ c r hc hr hrate z (N - kk + J) N
    have hk21 : (It.k : ℝ) = 21 := by rw [It.k_eq]; norm_num
    have heq : (fun om => Real.exp (c *
        ((It.prefixLen z alphaT (N - kk + J) (aux_rem_resolved_meshes_relabel N om) : ℝ) +
          (J : ℝ) + (It.k : ℝ) + 5))) =
        (Real.exp (c * ((J : ℝ) + 26))) • (fun om => Real.exp (c *
          (It.prefixLen z alphaT (N - kk + J) (aux_rem_resolved_meshes_relabel N om) : ℝ))) := by
      funext om
      rw [Pi.smul_apply, smul_eq_mul, ← Real.exp_add, hk21]
      congr 1
      ring
    rw [heq]
    refine ⟨hmem.const_smul _, ?_⟩
    rw [eLpNorm_const_smul, Real.enorm_of_nonneg (Real.exp_pos _).le,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    gcongr
  · simp only [if_neg hk, mul_zero, Real.exp_zero]
    refine ⟨memLp_const 1, ?_⟩
    rw [eLpNorm_const (1 : ℝ) (by simp; linarith) (IsProbabilityMeasure.ne_zero _)]
    simp only [enorm_one, measure_univ, ENNReal.one_rpow, mul_one]
    exact ENNReal.one_le_ofReal.mpr hK1

/-! ### The one-step residual and its deterministic two-mesh application -/

/-- The actual coefficient energy of `u` on `A ∩ Q`. -/
def aux_rem_resolved_meshes_energy {d : ℕ} (a : PositiveCoefficient (unitNeumannCube d))
    (u : meanZeroSobolevGraph (unitNeumannCube d)) (A : Set (SpatialCoordinates d)) : ℝ :=
  ∫ y in A ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
    a.val y * ∑ i : Fin d,
      (((sobolevGradient (u : SobolevData (unitNeumannCube d))) i :
        SpatialCoordinates d → ℝ) y) ^ 2

/-- The projection of `y` onto the faces of `Q` selected by `I`. -/
def aux_rem_resolved_meshes_center {d : ℕ} (y : SpatialCoordinates d) (I : Finset (Fin d)) :
    SpatialCoordinates d :=
  fun i => if i ∈ I then (if y i ≤ 1 / 2 then (0 : ℝ) else 1) else y i

/-- The literal original reference `b_k(z)` of the parent statement (ball average of
`s_N(k,·)`). -/
def aux_rem_resolved_meshes_bref {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N k : ℕ) (z : SpatialCoordinates d) : ℝ :=
  (volume.real (Metric.ball z ((3 : ℝ) ^ (-((k : ℤ))) / 2)))⁻¹ *
    ∫ x in Metric.ball z ((3 : ℝ) ^ (-((k : ℤ))) / 2),
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
        Real.exp ((H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
          (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)

/-- The root allowance as a function of the (projected) root centre, its active faces and its
depth, at cutoff `N`: the relabelled tightened prefix length of `in_iteration` plus the fixed
shift `J + k + 5`. -/
def aux_rem_resolved_meshes_B {d : ℕ} (pl : SpatialCoordinates d → ℕ → ℕ) (N J kIt : ℕ)
    (y : SpatialCoordinates d) (I : Finset (Fin d)) (k : ℕ) : ℝ :=
  if k ≤ N then
    (pl ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I) (N - k + J) : ℝ) +
      (J : ℝ) + (kIt : ℝ) + 5
  else 0

/-- **The one-step residual** (step 3 of the assembly).  For the actual cutoff coefficient
`A_N` on `Q`, an arbitrary essentially bounded mean-zero source and weak Neumann solution, at a
root of depth `k` with active faces `I` and projected centre `center y I`:
`E(s) ≤ Cstep e^{c ℒ} (s/R_k)^{t₀} [E(L_* R_k) + b_{k-J}^{-1} ‖f‖_∞² R_k^{d+2}]`, where `ℒ` is the
relabelled tightened prefix length of `in_iteration` at scale `N-k+J` (the root allowance).
Inputs: the finite-infrared transfer `hphysical` at `(ω, N)` and the infrared convergence at `ω`,
both almost-sure facts of the parent's premises; no mesh, moment or energy conclusion. -/
def aux_rem_resolved_meshes_onestep (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 : ℝ) (J : ℕ) (Kt Cstep c delta1 : ℝ) : Prop :=
  ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (E : in_J d)
    (_ : in_poincare d hd E) (_ : in_extension d hd E)
    (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
    (_ : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
    M.delta ≤ delta1 →
    ∀ (omega : BilateralField d),
      Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega)) →
    ∀ (N : ℕ),
      (∃ aFin : ℕ → PositiveCoefficient (unitNeumannCube d),
        (∀ L' : ℕ, ∃ cFin : ℝ, 0 < cFin ∧
          ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
            (aFin L').val y =
              cFin *
                (Sreg.cutoffOn (N + L') (aux_rem_resolved_meshes_relabel N omega)
                  ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
                  ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val
                  (((3 : ℝ) ^ (N : ℤ)) • y)) ∧
        (∀ ε : ℝ, 0 < ε →
          ∃ L₀ : ℕ, ∀ L' : ℕ, L₀ ≤ L' →
            ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
              |(aFin L').val y - cutoffCoefficient M H omega N y| < ε)) →
    ∀ f : SpatialCoordinates d → ℝ,
      AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
    ∀ Kf : ℝ, 0 ≤ Kf →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
    ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      SolvesNeumann (cutoffPositiveCoefficient M H omega N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) f u →
    ∀ (y : SpatialCoordinates d), y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
    ∀ (I : Finset (Fin d)) (s : ℝ) (k : ℕ),
      s ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) → (3 : ℝ) ^ (-(N : ℤ)) / 2 ≤ s → 0 < s →
      k ≤ N → 8 * s < (3 : ℝ) ^ (-((k : ℤ))) / 2 → (3 : ℝ) ^ (-((k : ℤ))) / 2 ≤ Rstar →
      (∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ min (y i) (1 - y i)) →
      aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) s) ≤
        Cstep * Real.exp (c * (It.prefixLen
            ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
            (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + J)
            (aux_rem_resolved_meshes_relabel N omega) : ℝ)) *
          (s / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I)
                (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M H omega N (k - J)
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))

/-- The deterministic two-mesh application at one sample, cutoff, source and solution, from the
one-step estimate with reference `b_{k-J}`, through the generic two-mesh core. -/
theorem aux_rem_resolved_meshes_energy_app (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 eta etas : ℝ)
    (hLstar : 10 ≤ Lstar) (hRstar_pos : 0 < Rstar) (hRstar_lt : Rstar < 1 / (100 * Lstar))
    (hRstar_mem : Rstar ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2))
    (ht0_low : (d : ℝ) - 1 < t0) (ht0_high : t0 < (d : ℝ))
    (heta_pos : 0 < eta) (heta_lt : eta < t0 - ((d : ℝ) - 1))
    (hetas_pos : 0 < etas) (hetas_lt : etas < (d : ℝ) + 2 - t0)
    (J : ℕ) (hJ : 1 ≤ J) (Cstep c : ℝ) (hCstep : 1 ≤ Cstep) (hc : 0 ≤ c)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ)
    (a : PositiveCoefficient (unitNeumannCube d)) (u : meanZeroSobolevGraph (unitNeumannCube d))
    (Kf : ℝ) (pl : SpatialCoordinates d → ℕ → ℕ) (kIt : ℕ)
    (hone : ∀ (y : SpatialCoordinates d), y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
      ∀ (I : Finset (Fin d)) (s : ℝ) (k : ℕ),
      s ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) → (3 : ℝ) ^ (-(N : ℤ)) / 2 ≤ s → 0 < s →
      k ≤ N → 8 * s < (3 : ℝ) ^ (-((k : ℤ))) / 2 → (3 : ℝ) ^ (-((k : ℤ))) / 2 ≤ Rstar →
      (∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ min (y i) (1 - y i)) →
      aux_rem_resolved_meshes_energy a u (Metric.ball (aux_rem_resolved_meshes_center y I) s) ≤
        Cstep * Real.exp (c * (pl ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
            (N - k + J) : ℝ)) *
          (s / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy a u
              (Metric.ball (aux_rem_resolved_meshes_center y I)
                (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M H omega N (k - J)
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)))
    (U : ℝ)
    (hU : ∀ (n : ℕ) (g : Fin d → Fin (3 ^ (n + J) + 1))
        (dep : Fin (d + 1) → Fin (n + J + 1)) (σ : Equiv.Perm (Fin d)),
        (3 : ℝ) ^ (-eta * (n : ℝ)) * (Cstep ^ (d + 1) * Real.exp (c * ∑ j : Fin (d + 1),
          aux_rem_resolved_meshes_B pl N J kIt
            (fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + J : ℕ) : ℤ))))
            (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val)) (dep j).val)) ≤ U)
    (V : ℝ)
    (hV : ∀ k : ℕ, k ≤ N → ∀ z : SpatialCoordinates d, (∀ i, 0 ≤ z i ∧ z i ≤ 1) →
        aux_rem_resolved_meshes_bref M H omega N k z +
          (aux_rem_resolved_meshes_bref M H omega N k z)⁻¹ ≤
          V * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ (-etas))
    (x : SpatialCoordinates d) (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (r : ℝ) (hr : (3 : ℝ) ^ (-(N : ℤ)) ≤ r) :
    aux_rem_resolved_meshes_energy a u {y | ∀ i : Fin d, |y i - x i| < r / 2} ≤
      (2 ^ d + (36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 * 3 ^ eta * 2 ^ t0 *
        (Rstar ^ (-t0) + (d : ℝ) + 1)) * U * r ^ (t0 - eta) *
        (aux_rem_resolved_meshes_energy a u (unitNeumannCube d : Set (SpatialCoordinates d)) +
          V * Kf ^ 2) := by
  have hd1 : 1 ≤ d := by omega
  let uw : weakSobolevGraph (unitNeumannCube d) := ⟨u.1, u.2.1⟩
  have hmono : ∀ A A' : Set (SpatialCoordinates d), A ⊆ A' →
      aux_rem_resolved_meshes_energy a u A ≤ aux_rem_resolved_meshes_energy a u A' :=
    fun A A' h => aux_rem_resolved_strata_energy_mono a uw h
  have hnn : ∀ A, 0 ≤ aux_rem_resolved_meshes_energy a u A :=
    fun A => aux_rem_resolved_strata_energy_nonneg a uw A
  have hbpos : ∀ k z, 0 < aux_rem_resolved_meshes_bref M H omega N (k - J) z :=
    fun k z => aux_lane4_two_mesh_energy_bound_bpos M H omega N (k - J) z
  have hB : ∀ y I k, 0 ≤ aux_rem_resolved_meshes_B pl N J kIt y I k := by
    intro y I k
    unfold aux_rem_resolved_meshes_B
    split_ifs <;> positivity
  have hstep : ∀ (y : SpatialCoordinates d),
      y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
      ∀ (I : Finset (Fin d)) (s : ℝ) (k : ℕ),
      s ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) → (3 : ℝ) ^ (-(N : ℤ)) / 2 ≤ s → 0 < s →
      k ≤ N → 8 * s < (3 : ℝ) ^ (-((k : ℤ))) / 2 → (3 : ℝ) ^ (-((k : ℤ))) / 2 ≤ Rstar →
      (∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ min (y i) (1 - y i)) →
      ∀ C : SpatialCoordinates d, (∀ i, C i = aux_rem_resolved_meshes_center y I i) →
      aux_rem_resolved_meshes_energy a u (Metric.ball C s) ≤
        Cstep * Real.exp (c * aux_rem_resolved_meshes_B pl N J kIt y I k) *
          (s / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy a u (Metric.ball C (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M H omega N (k - J) C)⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by
    intro y hy I s k hs hs1 hs0 hk h8 hR hI C hC
    have hCe : C = aux_rem_resolved_meshes_center y I := funext hC
    subst hCe
    refine (hone y hy I s k hs hs1 hs0 hk h8 hR hI).trans ?_
    have hbr : 0 ≤ aux_rem_resolved_meshes_energy a u
          (Metric.ball (aux_rem_resolved_meshes_center y I)
            (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
        (aux_rem_resolved_meshes_bref M H omega N (k - J)
          (aux_rem_resolved_meshes_center y I))⁻¹ *
          Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2) := by
      have := hbpos k (aux_rem_resolved_meshes_center y I)
      have := hnn (Metric.ball (aux_rem_resolved_meshes_center y I)
            (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2)))
      positivity
    have hsR : 0 ≤ (s / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 := by positivity
    have hexp : Real.exp (c * (pl ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
          (N - k + J) : ℝ)) ≤ Real.exp (c * aux_rem_resolved_meshes_B pl N J kIt y I k) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hc
      unfold aux_rem_resolved_meshes_B
      rw [if_pos hk]
      have : (0 : ℝ) ≤ (J : ℝ) + (kIt : ℝ) + 5 := by positivity
      linarith
    gcongr
  have hV' : ∀ k : ℕ, k ≤ N → ∀ z : SpatialCoordinates d, (∀ i, 0 ≤ z i ∧ z i ≤ 1) →
      aux_rem_resolved_meshes_bref M H omega N (k - J) z +
        (aux_rem_resolved_meshes_bref M H omega N (k - J) z)⁻¹ ≤
        V * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ (-etas) := by
    intro k hk z hz
    have h := hV (k - J) (by omega) z hz
    refine h.trans ?_
    have hV0 : 0 ≤ V := by
      have hb := hbpos k z
      have hR0 : 0 < ((3 : ℝ) ^ (-(((k - J : ℕ) : ℤ))) / 2) ^ (-etas) := by positivity
      by_contra hneg
      push_neg at hneg
      have : V * ((3 : ℝ) ^ (-(((k - J : ℕ) : ℤ))) / 2) ^ (-etas) < 0 :=
        mul_neg_of_neg_of_pos hneg hR0
      have hb' : 0 < aux_rem_resolved_meshes_bref M H omega N (k - J) z +
          (aux_rem_resolved_meshes_bref M H omega N (k - J) z)⁻¹ := by positivity
      linarith
    apply mul_le_mul_of_nonneg_left _ hV0
    have hRle : (3 : ℝ) ^ (-((k : ℤ))) / 2 ≤ (3 : ℝ) ^ (-(((k - J : ℕ) : ℤ))) / 2 := by
      have : (3 : ℝ) ^ (-((k : ℤ))) ≤ (3 : ℝ) ^ (-(((k - J : ℕ) : ℤ))) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      linarith
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hRle (by linarith)
  have hcore := aux_lane4_two_mesh_energy_bound_core d hd Lstar Rstar t0 eta etas hLstar
    hRstar_pos hRstar_lt hRstar_mem ht0_low ht0_high heta_pos heta_lt hetas_lt J hJ Cstep c
    hCstep hc N Kf (aux_rem_resolved_meshes_energy a u) hmono hnn
    (fun k z => aux_rem_resolved_meshes_bref M H omega N (k - J) z) hbpos
    (aux_rem_resolved_meshes_B pl N J kIt) hB
    (fun y hy I s k hs hs1 hs0 hk h8 hR hI => hstep y hy I s k hs hs1 hs0 hk h8 hR hI _
      (fun i => by simp only [aux_rem_resolved_meshes_center]))
    U hU V hV' x hx r hr
  have hball : Metric.ball x (r / 2) = {y | ∀ i : Fin d, |y i - x i| < r / 2} :=
    aux_lane4_two_mesh_energy_bound_ball_eq hd1 x (r / 2)
  have huniv : aux_rem_resolved_meshes_energy a u Set.univ =
      aux_rem_resolved_meshes_energy a u (unitNeumannCube d : Set (SpatialCoordinates d)) := by
    unfold aux_rem_resolved_meshes_energy
    rw [Set.univ_inter, Set.inter_self]
  rw [← hball, ← huniv]
  exact hcore

theorem aux_rem_resolved_meshes_abs_log_le {δ : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1) :
    |Real.log δ| ≤ δ⁻¹ := by
  have hle : Real.log δ ≤ 0 := Real.log_nonpos h0.le h1
  rw [abs_of_nonpos hle]
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h0)
  rw [Real.log_inv] at h
  linarith

/-- The small-disorder threshold for the allowance moments: below it the carrier's guard, the
tightened Hölder range and the tail rate `≥ 2 r c` all hold. -/
theorem aux_rem_resolved_meshes_delta_facts (cC aT r c : ℝ) (hcC : 1 ≤ cC) (haT : aT < 1)
    (hr : 0 < r) (hc : 0 < c) :
    0 < min (1 / 2) (min (1 / cC) (min (((1 - aT) / cC) ^ 2) ((1 - aT) ^ 2 / (2 * r * c * cC)))) ∧
    ∀ δ : ℝ, 0 < δ →
      δ ≤ min (1 / 2) (min (1 / cC) (min (((1 - aT) / cC) ^ 2) ((1 - aT) ^ 2 / (2 * r * c * cC)))) →
      δ ≤ cC⁻¹ ∧ aT ≤ 1 - cC * δ * Real.sqrt |Real.log δ| ∧
        2 * (r * c) ≤ (1 - aT) ^ 2 / (cC * δ ^ 2 * |Real.log δ|) := by
  have h1a : 0 < 1 - aT := by linarith
  have hcC0 : 0 < cC := by linarith
  refine ⟨by positivity, ?_⟩
  intro δ hδ hle
  have hδh : δ ≤ 1 / 2 := hle.trans (min_le_left _ _)
  have hδc : δ ≤ 1 / cC := hle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδs : δ ≤ ((1 - aT) / cC) ^ 2 :=
    hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδr : δ ≤ (1 - aT) ^ 2 / (2 * r * c * cC) :=
    hle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hlog := aux_rem_resolved_meshes_abs_log_le hδ (by linarith)
  have hlogpos : 0 < |Real.log δ| := by
    rw [abs_pos]
    exact (Real.log_neg hδ (by linarith)).ne
  refine ⟨by rwa [one_div] at hδc, ?_, ?_⟩
  · -- δ √|log δ| ≤ √δ ≤ (1 - aT)/cC
    have hsq : δ * Real.sqrt |Real.log δ| ≤ Real.sqrt δ := by
      have : δ * Real.sqrt |Real.log δ| = Real.sqrt (δ ^ 2 * |Real.log δ|) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hδ.le]
      rw [this]
      apply Real.sqrt_le_sqrt
      calc δ ^ 2 * |Real.log δ| ≤ δ ^ 2 * δ⁻¹ := by gcongr
        _ = δ := by field_simp
    have hsd : Real.sqrt δ ≤ (1 - aT) / cC := by
      rw [show (1 - aT) / cC = Real.sqrt (((1 - aT) / cC) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hδs
    have : cC * (δ * Real.sqrt |Real.log δ|) ≤ 1 - aT := by
      calc cC * (δ * Real.sqrt |Real.log δ|) ≤ cC * ((1 - aT) / cC) := by
            gcongr; exact hsq.trans hsd
        _ = 1 - aT := by field_simp
    nlinarith
  · have hden : cC * δ ^ 2 * |Real.log δ| ≤ cC * δ := by
      calc cC * δ ^ 2 * |Real.log δ| ≤ cC * δ ^ 2 * δ⁻¹ := by gcongr
        _ = cC * δ := by field_simp
    have hpos : 0 < cC * δ ^ 2 * |Real.log δ| := by positivity
    rw [le_div_iff₀ hpos]
    calc 2 * (r * c) * (cC * δ ^ 2 * |Real.log δ|) ≤ 2 * (r * c) * (cC * δ) := by gcongr
      _ = (2 * r * c * cC) * δ := by ring
      _ ≤ (2 * r * c * cC) * ((1 - aT) ^ 2 / (2 * r * c * cC)) := by gcongr
      _ = (1 - aT) ^ 2 := by field_simp

theorem aux_rem_resolved_meshes_center_filter {d : ℕ} (y : SpatialCoordinates d)
    (σ : Equiv.Perm (Fin d)) (j : ℕ) :
    aux_rem_resolved_meshes_center y (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j)) =
      fun a => if a ∈ {a : Fin d | (σ.symm a).val < j} then
        (if y a ≤ 1 / 2 then (0 : ℝ) else 1) else y a := by
  funext a
  simp only [aux_rem_resolved_meshes_center, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.mem_setOf_eq]

theorem aux_rem_resolved_meshes_closure_subset (d : ℕ) :
    closure (unitNeumannCube d : Set (SpatialCoordinates d)) ⊆
      {x : SpatialCoordinates d | ∀ i, 0 ≤ x i ∧ x i ≤ 1} := by
  have hset : {x : SpatialCoordinates d | ∀ i, 0 ≤ x i ∧ x i ≤ 1} =
      Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ_pi, Set.mem_Icc]
  apply closure_minimal
  · intro x hx
    have hx' : x ∈ ((centeredCube (fun _ => (1 / 2 : ℝ)) 1 one_pos : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)) := hx
    rw [centeredCube_eq_pi (fun _ => (1 / 2 : ℝ)) one_pos] at hx'
    intro i
    have hi := hx' i (Set.mem_univ i)
    simp only [Set.mem_Ioo] at hi
    constructor <;> linarith [hi.1, hi.2]
  · rw [hset]
    exact isClosed_set_pi (fun _ _ => isClosed_Icc)


/-! ### Stage 1: from the finite infrared coefficients to the actual one -/




theorem aux_rem_resolved_meshes_unit_convex (d : ℕ) :
    Homogenization.IsOpenBoundedConvexDomain
      (unitNeumannCube d : Set (SpatialCoordinates d)) := by
  unfold unitNeumannCube
  refine ⟨(centeredCube _ _ _).isOpen,
    Homogenization.Bornology.IsBounded.isBoundedDomain (centeredCube_isBounded _ one_pos), ?_⟩
  change Convex ℝ (Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2))
  exact convex_ball _ _

theorem aux_rem_resolved_meshes_domainConstantL2_zero {d : ℕ} (Ω : Opens (SpatialCoordinates d))
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))] :
    domainConstantL2 (Ω := Ω) 0 = 0 := by
  apply Lp.ext
  filter_upwards [domainConstantL2_coeFn (Ω := Ω) 0,
    Lp.coeFn_zero ℝ 2 (volume.restrict (Ω : Set (SpatialCoordinates d)))] with x h1 h2
  rw [h1, h2]
  rfl

/-- Existence of a mean-zero weak Neumann solution for any positive bounded coefficient on `Q`
and any essentially bounded mean-zero source (Lax–Milgram on the mean-zero graph with the
mean-zero Poincaré inequality of the convex cube; the constant part of a test is removed with
`∫ f = 0`). -/
theorem aux_rem_resolved_meshes_neumann_exists {d : ℕ} (hd : 2 ≤ d)
    (a : PositiveCoefficient (unitNeumannCube d)) (f : SpatialCoordinates d → ℝ)
    (hf : AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (Kf : ℝ) (hfb : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      |f y| ≤ Kf)
    (hf0 : (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0) :
    ∃ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨K, hK⟩ := (exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain (unitNeumannCube d)
    (aux_rem_resolved_meshes_unit_convex d)).2
  have hmem : MemLp f 2 (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
    MemLp.of_bound hf.aestronglyMeasurable Kf (hfb.mono fun y hy => by rwa [Real.norm_eq_abs])
  obtain ⟨c, hc, ha⟩ := a.property
  obtain ⟨u, hu, -⟩ := existsUnique_meanZero_source_solution K hK a.val hc ha (hmem.toLp f)
  refine ⟨u, ?_⟩
  intro ψ
  have hQb : Bornology.IsBounded (unitNeumannCube d : Set (SpatialCoordinates d)) :=
    centeredCube_isBounded _ one_pos
  set μ : ℝ := (volume.real (unitNeumannCube d : Set (SpatialCoordinates d)))⁻¹ *
    ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), (ψ : SobolevData (unitNeumannCube d)).1 x
  let cst : SobolevData (unitNeumannCube d) := affineSobolevData hQb 0 μ
  have hcst_mem : cst ∈ weakSobolevGraph (unitNeumannCube d) := affineSobolevData_mem hQb 0 μ
  have hcst_fst : (cst.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (unitNeumannCube d : Set (SpatialCoordinates d))] fun _ => μ := by
    change ((affineL2 hQb (0 : Fin d → ℝ) μ : DomainL2 (unitNeumannCube d)) :
      SpatialCoordinates d → ℝ) =ᵐ[_] _
    filter_upwards [affineL2_coeFn hQb (0 : Fin d → ℝ) μ] with x hx
    rw [hx]
    simp [affineSlope_apply]
  have hcst_grad : sobolevGradient cst = 0 := by
    have h0 : cst.2 = 0 := by
      funext i
      exact aux_rem_resolved_meshes_domainConstantL2_zero (unitNeumannCube d)
    change (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => DomainL2 (unitNeumannCube d))).symm cst.2 = 0
    rw [h0, map_zero]
  have hvol : volume.real (unitNeumannCube d : Set (SpatialCoordinates d)) ≠ 0 := by
    have : volume (unitNeumannCube d : Set (SpatialCoordinates d)) ≠ 0 :=
      (Metric.measure_ball_pos volume _ (by norm_num)).ne'
    exact (ENNReal.toReal_pos this measure_ball_lt_top.ne).ne'
  have hψint : Integrable (ψ : SobolevData (unitNeumannCube d)).1 (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
    (Lp.memLp _).integrable one_le_two
  have hcint : Integrable (cst.1 : SpatialCoordinates d → ℝ)
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
    (Lp.memLp _).integrable one_le_two
  have hψ0 : ((ψ : SobolevData (unitNeumannCube d)) - cst) ∈ meanZeroSobolevGraph (unitNeumannCube d) := by
    rw [mem_meanZeroSobolevGraph_iff]
    refine ⟨(weakSobolevGraph (unitNeumannCube d)).sub_mem ψ.2 hcst_mem, ?_⟩
    have hsub : ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), ((ψ : SobolevData (unitNeumannCube d)) - cst).1 x =
        (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), (ψ : SobolevData (unitNeumannCube d)).1 x) -
          ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), cst.1 x := by
      rw [← integral_sub hψint hcint]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (ψ : SobolevData (unitNeumannCube d)).1 cst.1] with x hx
      simpa using hx
    rw [hsub, integral_congr_ae hcst_fst, integral_const]
    simp only [smul_eq_mul, measureReal_restrict_apply_univ]
    rw [show volume.real (unitNeumannCube d : Set (SpatialCoordinates d)) * μ =
      ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), (ψ : SobolevData (unitNeumannCube d)).1 x by
        simp only [μ]; field_simp]
    ring
  have heq := hu ⟨_, hψ0⟩
  -- left side
  have hL : sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d)) (ψ : SobolevData (unitNeumannCube d)) =
      weightedGradientForm a.val (sobolevGradient (u : SobolevData (unitNeumannCube d)))
        (sobolevGradient (((ψ : SobolevData (unitNeumannCube d)) - cst))) := by
    rw [map_sub, hcst_grad, sub_zero]
    rfl
  rw [hL, heq]
  -- right side
  have hfψ : Integrable (fun x => f x * (ψ : SobolevData (unitNeumannCube d)).1 x)
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
    hmem.integrable_mul (Lp.memLp _)
  calc (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
        (hmem.toLp f) x * (((ψ : SobolevData (unitNeumannCube d)) - cst) : SobolevData (unitNeumannCube d)).1 x)
      = ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), (f x * (ψ : SobolevData (unitNeumannCube d)).1 x - μ * f x) := by
        apply integral_congr_ae
        filter_upwards [hmem.coeFn_toLp, Lp.coeFn_sub (ψ : SobolevData (unitNeumannCube d)).1 cst.1, hcst_fst]
          with x h1 h2 h3
        change (hmem.toLp f) x * ((ψ : SobolevData (unitNeumannCube d)).1 - cst.1) x = _
        rw [h1, h2, Pi.sub_apply, h3]
        ring
    _ = (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x * (ψ : SobolevData (unitNeumannCube d)).1 x) -
          μ * ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x := by
        rw [integral_sub hfψ ((hmem.integrable one_le_two).const_mul μ), integral_const_mul]
    _ = ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x * (ψ : SobolevData (unitNeumannCube d)).1 x := by
        rw [hf0, mul_zero, sub_zero]




theorem aux_rem_resolved_meshes_energy_eq_local {d : ℕ}
    (a : PositiveCoefficient (unitNeumannCube d)) (g : HilbertGradient (unitNeumannCube d))
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A) :
    (∫ y in A ∩ (unitNeumannCube d : Set (SpatialCoordinates d)),
        a.val y * ∑ i : Fin d, ((g i : SpatialCoordinates d → ℝ) y) ^ 2) =
      localGradientEnergy a hA g := by
  rw [localGradientEnergy_eq_integral, ← Measure.restrict_restrict hA]
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum]
  intro i _
  have := integrable_weighted_inner a.val (g i) (g i)
  exact (by simpa only [RCLike.inner_apply, conj_trivial, pow_two, mul_comm] using this :
    Integrable (fun y => a.val y * ((g i : SpatialCoordinates d → ℝ) y) ^ 2)
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)))).restrict

/-- **Weak-solution stability.** Two mean-zero Neumann solutions with the same source and
relatively close coefficients (`|b - a| ≤ δ a`, `δ ≤ 1/4`) have gradients within
`E_a(∇(v-u)) ≤ 2 δ² E_a(∇u)`. -/
theorem aux_rem_resolved_meshes_stability {d : ℕ}
    (a b : PositiveCoefficient (unitNeumannCube d)) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4)
    (hab : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      |b.val x - a.val x| ≤ δ * a.val x)
    (f : SpatialCoordinates d → ℝ) (u v : meanZeroSobolevGraph (unitNeumannCube d))
    (hu : SolvesNeumann a f u) (hv : SolvesNeumann b f v) :
    weightedGradientForm a.val
        (sobolevGradient ((v : SobolevData (unitNeumannCube d)) - u))
        (sobolevGradient ((v : SobolevData (unitNeumannCube d)) - u)) ≤
      2 * δ ^ 2 * weightedGradientForm a.val (sobolevGradient (u : SobolevData (unitNeumannCube d)))
        (sobolevGradient (u : SobolevData (unitNeumannCube d))) := by
  set W : SobolevData (unitNeumannCube d) := (v : SobolevData (unitNeumannCube d)) - u with hWdef
  have hW : W ∈ weakSobolevGraph (unitNeumannCube d) :=
    (weakSobolevGraph (unitNeumannCube d)).sub_mem v.2.1 u.2.1
  have hv' := hv ⟨W, hW⟩
  have hu' := hu ⟨W, hW⟩
  set gu := sobolevGradient (u : SobolevData (unitNeumannCube d))
  set gw := sobolevGradient W
  have hsupp : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      x ∉ (Set.univ : Set (SpatialCoordinates d)) → b.val x = a.val x :=
    Filter.Eventually.of_forall fun x hx => absurd (Set.mem_univ x) hx
  -- `E_b(w,w) = E_a(u,w) - E_b(u,w)`
  have hid : weightedGradientForm b.val gw gw =
      weightedGradientForm a.val gu gw - weightedGradientForm b.val gu gw := by
    have h1 : sobolevCoefficientForm b W W =
        sobolevCoefficientForm b (v : SobolevData (unitNeumannCube d)) W -
          sobolevCoefficientForm b (u : SobolevData (unitNeumannCube d)) W :=
      (sobolevCoefficientForm b).map_sub₂ _ _ W
    have h2 : sobolevCoefficientForm b (v : SobolevData (unitNeumannCube d)) W =
        sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d)) W := by
      rw [hv', hu']
    change sobolevCoefficientForm b W W =
      sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d)) W -
        sobolevCoefficientForm b (u : SobolevData (unitNeumannCube d)) W
    rw [h1, h2]
  have hy := weightedGradientForm_difference_young_local a b MeasurableSet.univ
    (δ := δ) (c := 1) one_pos hab hsupp gu gw
  have hself := weightedGradientForm_difference_self_le_local a b MeasurableSet.univ
    (δ := δ) hab hsupp gw
  have hlu := localGradientEnergy_le a MeasurableSet.univ gu
  have hlw := localGradientEnergy_le a MeasurableSet.univ gw
  have hlw0 := localGradientEnergy_nonneg a MeasurableSet.univ gw
  have hEw0 : 0 ≤ weightedGradientForm a.val gw gw := hlw0.trans hlw
  have hA1 := (abs_le.mp hself).1
  have hA2 : δ * localGradientEnergy a MeasurableSet.univ gw ≤
      δ * weightedGradientForm a.val gw gw := mul_le_mul_of_nonneg_left hlw hδ0
  have hB1 := (abs_le.mp hy).1
  have hB2 : δ ^ 2 / (2 * 1) * localGradientEnergy a MeasurableSet.univ gu ≤
      δ ^ 2 / (2 * 1) * weightedGradientForm a.val gu gu :=
    mul_le_mul_of_nonneg_left hlu (by positivity)
  have hC : 0 ≤ (1 / 2 - δ - 1 / 4) * weightedGradientForm a.val gw gw :=
    mul_nonneg (by linarith) hEw0
  have hD : δ ^ 2 / (2 * 1) = δ ^ 2 / 2 := by norm_num
  rw [hD] at hB1 hB2
  have hE : δ * weightedGradientForm a.val gw gw ≤ 1 / 4 * weightedGradientForm a.val gw gw +
      (1 / 2 - δ - 1 / 4) * weightedGradientForm a.val gw gw + δ * weightedGradientForm a.val gw gw -
        (1 / 2 - δ - 1 / 4) * weightedGradientForm a.val gw gw - 1 / 4 * weightedGradientForm a.val gw gw := by
    ring_nf; exact le_rfl
  linarith

/-- Relative coefficient closeness transfers local energies in both directions. -/
theorem aux_rem_resolved_meshes_local_cmp {d : ℕ}
    (a b : PositiveCoefficient (unitNeumannCube d)) (δ : ℝ) (hδ : δ < 1)
    (hab : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      |b.val x - a.val x| ≤ δ * a.val x)
    {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s)
    (g : HilbertGradient (unitNeumannCube d)) :
    localGradientEnergy b hs g ≤ (1 + δ) * localGradientEnergy a hs g ∧
      (1 - δ) * localGradientEnergy a hs g ≤ localGradientEnergy b hs g := by
  have ha0 := positiveCoefficient_ae_nonneg a
  constructor
  · apply localGradientEnergy_le_mul b a (1 + δ)
    filter_upwards [hab] with x hx
    have := (abs_le.mp hx).2
    linarith
  · have h1 : 0 < 1 - δ := by linarith
    have h := localGradientEnergy_le_mul a b (1 - δ)⁻¹ (by
      filter_upwards [hab] with x hx
      have := (abs_le.mp hx).1
      rw [inv_mul_eq_div, le_div_iff₀ h1]
      nlinarith) hs g
    calc (1 - δ) * localGradientEnergy a hs g ≤ (1 - δ) * ((1 - δ)⁻¹ * localGradientEnergy b hs g) :=
          mul_le_mul_of_nonneg_left h h1.le
      _ = localGradientEnergy b hs g := by field_simp


/-! #### Reference convergence -/

theorem aux_rem_resolved_meshes_sum_shift {d : ℕ} (omega : BilateralField d) (N L : ℕ)
    (x : SpatialCoordinates d) :
    (∑ j ∈ Finset.range (N + L + 1), (omega ((j : ℤ) - (N : ℤ))) x) =
      (∑ j ∈ Finset.range (N + 1), (omega (-(j : ℤ))) x) +
        ∑ n ∈ Finset.range L, (omega (((n + 1 : ℕ) : ℤ))) x := by
  rw [show N + L + 1 = (N + 1) + L by ring, Finset.sum_range_add]
  congr 1
  · rw [← Finset.sum_range_reflect (fun j : ℕ => (omega (-(j : ℤ))) x) (N + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    congr 2
    rw [show N + 1 - 1 - j = N - j by omega, Nat.cast_sub hj']
    ring
  · apply Finset.sum_congr rfl
    intro n _
    congr 2
    push_cast
    ring

theorem aux_rem_resolved_meshes_sum_window {d : ℕ} (omega : BilateralField d) (N k L : ℕ)
    (hk1 : 1 ≤ k) (hkN : k ≤ N) (x : SpatialCoordinates d) :
    (∑ j ∈ Finset.range (N + L + 1), (omega ((j : ℤ) - (N : ℤ))) x) -
        (∑ j ∈ Finset.range (N - k + 1 + 1), (omega ((j : ℤ) - (N : ℤ))) x) =
      (∑ j ∈ Finset.range (k - 1), (omega (-(j : ℤ))) x) +
        ∑ n ∈ Finset.range L, (omega (((n + 1 : ℕ) : ℤ))) x := by
  have hsplit : (∑ j ∈ Finset.range (N + 1), (omega ((j : ℤ) - (N : ℤ))) x) =
      (∑ j ∈ Finset.range (N - k + 1 + 1), (omega ((j : ℤ) - (N : ℤ))) x) +
        ∑ j ∈ Finset.range (k - 1), (omega (-(j : ℤ))) x := by
    rw [show N + 1 = (N - k + 1 + 1) + (k - 1) by omega, Finset.sum_range_add]
    congr 1
    rw [← Finset.sum_range_reflect (fun j : ℕ => (omega (-(j : ℤ))) x) (k - 1)]
    apply Finset.sum_congr rfl
    intro t ht
    have ht' : t < k - 1 := Finset.mem_range.mp ht
    congr 2
    rw [show k - 1 - 1 - t = k - 2 - t by omega]
    push_cast [show t ≤ k - 2 by omega, show 2 ≤ k by omega, hkN, hk1,
      Nat.cast_sub (show k ≤ N by omega), Nat.cast_sub (show 2 + t ≤ k by omega)]
    ring
  have h0 := aux_rem_resolved_meshes_sum_shift omega N L x
  have h1 := aux_rem_resolved_meshes_sum_shift omega N 0 x
  simp only [Finset.range_zero, Finset.sum_empty, add_zero] at h1
  rw [h0, ← h1, hsplit]
  ring

/-- Almost-everywhere statements transfer along a dilation onto a region. -/
theorem aux_rem_resolved_meshes_ae_smul {d : ℕ} {T S : Set (SpatialCoordinates d)}
    (hT : MeasurableSet T) (hS : MeasurableSet S) {c : ℝ} (hc : c ≠ 0)
    (hmaps : ∀ y ∈ S, c • y ∈ T) {P : SpatialCoordinates d → Prop}
    (hP : ∀ᵐ x ∂volume.restrict T, P x) : ∀ᵐ y ∂volume.restrict S, P (c • y) := by
  rw [ae_restrict_iff' hT] at hP
  rw [ae_restrict_iff' hS]
  have hnull : volume {x : SpatialCoordinates d | ¬ (x ∈ T → P x)} = 0 := by
    rwa [ae_iff] at hP
  have hpre : volume ((fun y : SpatialCoordinates d => c • y) ⁻¹'
      {x : SpatialCoordinates d | ¬ (x ∈ T → P x)}) = 0 := by
    rw [Measure.addHaar_preimage_smul volume hc, hnull, mul_zero]
  rw [ae_iff]
  refine measure_mono_null ?_ hpre
  intro y hy
  simp only [Set.mem_setOf_eq, Classical.not_imp] at hy ⊢
  exact ⟨hmaps y hy.1, hy.2⟩

open scoped Pointwise in
/-- Averages are invariant under dilation: `∫_{c • S} F = c^d ∫_S F(c ·)`. -/
theorem aux_rem_resolved_meshes_setIntegral_smul {d : ℕ} (S : Set (SpatialCoordinates d))
    (hS : MeasurableSet S) {c : ℝ} (hc : 0 < c) (F : SpatialCoordinates d → ℝ) :
    (∫ x in c • S, F x) = c ^ d * ∫ x in S, F (c • x) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hind : (fun x : SpatialCoordinates d => (c • S).indicator F (c • x)) =
      S.indicator (fun x => F (c • x)) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem (Set.smul_mem_smul_set hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
      rwa [Set.smul_mem_smul_set_iff₀ hc0]
  have h := Measure.integral_comp_smul (volume : Measure (SpatialCoordinates d))
    ((c • S).indicator F) c
  rw [hind, integral_indicator hS] at h
  rw [← integral_indicator (hS.const_smul₀ c), h]
  simp only [Module.finrank_fin_fun, smul_eq_mul]
  rw [abs_of_pos (inv_pos.mpr (pow_pos hc d))]
  field_simp

open scoped Pointwise in
theorem aux_rem_resolved_meshes_volume_smul {d : ℕ} (S : Set (SpatialCoordinates d))
    {c : ℝ} (hc : 0 < c) :
    volume.real (c • S) = c ^ d * volume.real S := by
  simp only [measureReal_def, Measure.addHaar_smul, Module.finrank_fin_fun]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (pow_pos hc d)]


theorem aux_rem_resolved_meshes_log_small {t ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (h : |Real.exp t - 1| < ε) : |t| < 2 * ε := by
  have h1 := (abs_lt.mp h).1
  have h2 := (abs_lt.mp h).2
  have hpos : 0 < 1 - ε := by linarith
  have hup : t < ε := by
    have : Real.exp t < Real.exp ε := by
      have := Real.add_one_le_exp ε
      linarith
    exact Real.exp_lt_exp.mp this
  have hlo : -(2 * ε) < t := by
    have hlog := Real.one_sub_inv_le_log_of_pos hpos
    have hinv : (1 - ε)⁻¹ ≤ 1 + 2 * ε := by
      rw [inv_le_iff_one_le_mul₀ hpos]
      nlinarith
    have hl : -(2 * ε) ≤ Real.log (1 - ε) := by linarith
    have hlt : Real.log (1 - ε) < t := by
      rw [← Real.log_exp t]
      exact Real.log_lt_log hpos (by linarith)
    linarith
  rw [abs_lt]
  constructor <;> linarith

/-- Uniform convergence `exp(β_L + D_L) → 1` on `K` from uniform `D_L → 0` on `K ∪ {y₀}` and
convergence at the single point `y₀`. -/
theorem aux_rem_resolved_meshes_rho_uniform {X : Type*} (β : ℕ → ℝ) (D : ℕ → X → ℝ)
    (K : Set X) (y₀ : X)
    (hD : ∀ ε > 0, ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ y, (y = y₀ ∨ y ∈ K) → |D L y| < ε)
    (hρ0 : ∀ ε > 0, ∃ L₀ : ℕ, ∀ L ≥ L₀, |Real.exp (β L + D L y₀) - 1| < ε) :
    ∀ ε > 0, ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ y ∈ K, |Real.exp (β L + D L y) - 1| < ε := by
  intro ε hε
  set η : ℝ := min (1 / 8) (ε / 16) with hη
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1 : η ≤ 1 / 8 := min_le_left _ _
  have hηε : η ≤ ε / 16 := min_le_right _ _
  obtain ⟨L1, hL1⟩ := hD η hη0
  obtain ⟨L2, hL2⟩ := hρ0 η hη0
  refine ⟨max L1 L2, fun L hL y hy => ?_⟩
  have ha := aux_rem_resolved_meshes_log_small hη0 (by linarith) (hL2 L (le_of_max_le_right hL))
  have hb := hL1 L (le_of_max_le_left hL) y₀ (Or.inl rfl)
  have hc := hL1 L (le_of_max_le_left hL) y (Or.inr hy)
  have hβ : |β L| < 3 * η := by
    have : β L = (β L + D L y₀) - D L y₀ := by ring
    rw [this]
    calc |(β L + D L y₀) - D L y₀| ≤ |β L + D L y₀| + |D L y₀| := abs_sub _ _
      _ < 2 * η + η := add_lt_add ha hb
      _ = 3 * η := by ring
  have ht : |β L + D L y| < 4 * η := by
    calc |β L + D L y| ≤ |β L| + |D L y| := abs_add_le _ _
      _ < 3 * η + η := add_lt_add hβ hc
      _ = 4 * η := by ring
  have ht1 : |β L + D L y| ≤ 1 := by linarith
  calc |Real.exp (β L + D L y) - 1| ≤ 2 * |β L + D L y| := Real.abs_exp_sub_one_le ht1
    _ < 2 * (4 * η) := by linarith
    _ ≤ ε := by linarith


/-- The relabelling at cutoff `N` read at `3^N y`: layer `j` becomes the original layer `j - N`
at `y`. -/
theorem aux_rem_resolved_meshes_relabel_apply {d : ℕ} (N : ℕ) (omega : BilateralField d)
    (j : ℤ) (y : SpatialCoordinates d) :
    (ContinuousMap.compRightContinuousMap ℝ
      (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
        continuous_const.smul continuous_id⟩ : C(SpatialCoordinates d, SpatialCoordinates d))
      (omega (j - (N : ℤ)))) (((3 : ℝ) ^ (N : ℤ)) • y) = (omega (j - (N : ℤ))) y := by
  simp only [ContinuousMap.compRightContinuousMap_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, smul_smul]
  rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero, one_smul]

theorem aux_rem_resolved_meshes_smul_mem_cube {d : ℕ} (N : ℕ) (y : SpatialCoordinates d)
    (hy : y ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) :
    ((3 : ℝ) ^ (N : ℤ)) • y ∈ (centeredCube ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
      ((3 : ℝ) ^ (N : ℤ)) (by positivity) : Set (SpatialCoordinates d)) := by
  have hy' : dist y (fun _ : Fin d => (1 / 2 : ℝ)) < 1 / 2 := hy
  change dist (((3 : ℝ) ^ (N : ℤ)) • y) ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ))) <
    (3 : ℝ) ^ (N : ℤ) / 2
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (zpow_pos (by norm_num) _)]
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (N : ℤ) := zpow_pos (by norm_num) _
  nlinarith

/-- The finite cutoff coefficient of `hphysical`, read on `Q`. -/
theorem aux_rem_resolved_meshes_cutoffOn_scaled {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M) (omega : BilateralField d)
    (N L : ℕ) :
    ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (Sreg.cutoffOn (N + L) (aux_rem_resolved_meshes_relabel N omega)
          ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
          ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val (((3 : ℝ) ^ (N : ℤ)) • y) =
        Real.exp ((∑ j ∈ Finset.range (N + L + 1), (omega ((j : ℤ) - (N : ℤ))) y) -
          ((N + L : ℕ) + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
  have h := Sreg.cutoffOn_eq (N + L) (aux_rem_resolved_meshes_relabel N omega)
    ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ))) ((3 : ℝ) ^ (N : ℤ)) (by positivity)
  have h2 := aux_rem_resolved_meshes_ae_smul (c := (3 : ℝ) ^ (N : ℤ))
    (centeredCube _ _ _).isOpen.measurableSet (unitNeumannCube d).isOpen.measurableSet
    (zpow_pos (by norm_num : (0 : ℝ) < 3) _).ne'
    (fun y hy => aux_rem_resolved_meshes_smul_mem_cube N y hy) h
  filter_upwards [h2] with y hy
  rw [hy]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  exact aux_rem_resolved_meshes_relabel_apply N omega (j : ℤ) y

/-- The infrared correction `ρ_L = aFin_L / A_N` in closed form. -/
def aux_rem_resolved_meshes_rho {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (cF : ℝ) (L : ℕ) (y : SpatialCoordinates d) : ℝ :=
  cF * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
    Real.exp ((∑ n ∈ Finset.range L, (omega (((n + 1 : ℕ) : ℤ))) y) -
      (L : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P - H omega y)

theorem aux_rem_resolved_meshes_rho_mul {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (cF : ℝ) (L : ℕ) (y : SpatialCoordinates d) :
    aux_rem_resolved_meshes_rho M H omega N cF L y * cutoffCoefficient M H omega N y =
      cF * Real.exp ((∑ j ∈ Finset.range (N + L + 1), (omega ((j : ℤ) - (N : ℤ))) y) -
          ((N + L : ℕ) + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
  have hA : SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≠ 0 := (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne'
  unfold aux_rem_resolved_meshes_rho cutoffCoefficient cutoffPotential
  rw [aux_rem_resolved_meshes_sum_shift omega N L y]
  have hs : (∑ j ∈ Finset.range (N + 1), (omega (-(Int.ofNat j))) y) =
      ∑ j ∈ Finset.range (N + 1), (omega (-(j : ℤ))) y := rfl
  rw [hs]
  have e : Real.exp ((∑ n ∈ Finset.range L, (omega (((n + 1 : ℕ) : ℤ))) y) -
        (L : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P - H omega y) *
      Real.exp (H omega y + ∑ j ∈ Finset.range (N + 1), (omega (-(j : ℤ))) y -
        ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
      Real.exp ((∑ j ∈ Finset.range (N + 1), (omega (-(j : ℤ))) y) +
          (∑ n ∈ Finset.range L, (omega (((n + 1 : ℕ) : ℤ))) y) -
        ((N + L : ℕ) + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  calc cF * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
        Real.exp ((∑ n ∈ Finset.range L, (omega (((n + 1 : ℕ) : ℤ))) y) -
          (L : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P - H omega y) *
      ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
        Real.exp (H omega y + ∑ j ∈ Finset.range (N + 1), (omega (-(j : ℤ))) y -
          ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
      = cF * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹) *
          (Real.exp ((∑ n ∈ Finset.range L, (omega (((n + 1 : ℕ) : ℤ))) y) -
            (L : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P - H omega y) *
          Real.exp (H omega y + ∑ j ∈ Finset.range (N + 1), (omega (-(j : ℤ))) y -
            ((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hA, mul_one, e]

theorem aux_rem_resolved_meshes_cutoffCoefficient_continuous {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) : Continuous (cutoffCoefficient M H omega N) := by
  refine continuous_const.mul (Real.continuous_exp.comp ?_)
  exact Continuous.sub
    (Continuous.add (H omega).continuous
      (continuous_finset_sum _ fun j _ => (omega (-(Int.ofNat j))).continuous))
    continuous_const

/-- `ρ_L → 1` uniformly (a.e.) on `Q`, from `hphysical`. -/
theorem aux_rem_resolved_meshes_rho_conv_Q {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d) (N : ℕ)
    (aFin : ℕ → PositiveCoefficient (unitNeumannCube d)) (cF : ℕ → ℝ)
    (hA : ∀ L : ℕ, ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (aFin L).val y = cF L *
        (Sreg.cutoffOn (N + L) (aux_rem_resolved_meshes_relabel N omega)
          ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
          ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val (((3 : ℝ) ^ (N : ℤ)) • y))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        |(aFin L).val y - cutoffCoefficient M H omega N y| < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        |aux_rem_resolved_meshes_rho M H omega N (cF L) L y - 1| < ε := by
  -- a positive lower bound of `A_N` on the closed unit cube
  have hK : IsCompact (Metric.closedBall (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)) :=
    isCompact_closedBall _ _
  obtain ⟨y1, -, hy1⟩ := hK.exists_isMinOn
    ⟨(fun _ : Fin d => (1 / 2 : ℝ)), Metric.mem_closedBall_self (by norm_num)⟩
    (aux_rem_resolved_meshes_cutoffCoefficient_continuous M H omega N).continuousOn
  set m0 := cutoffCoefficient M H omega N y1
  have hm0 : 0 < m0 :=
    mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _)
  intro ε hε
  obtain ⟨L₀, hL₀⟩ := hconv (ε * m0) (mul_pos hε hm0)
  refine ⟨L₀, fun L hL => ?_⟩
  filter_upwards [hL₀ L hL, hA L, aux_rem_resolved_meshes_cutoffOn_scaled Sreg omega N L,
    ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet] with y h1 h2 h3 hyQ
  have hy1' : m0 ≤ cutoffCoefficient M H omega N y :=
    hy1 (Metric.ball_subset_closedBall hyQ)
  have hrho := aux_rem_resolved_meshes_rho_mul M H omega N (cF L) L y
  rw [h2, h3, ← hrho] at h1
  have hpos : 0 < cutoffCoefficient M H omega N y := lt_of_lt_of_le hm0 hy1'
  have : |aux_rem_resolved_meshes_rho M H omega N (cF L) L y - 1| *
      cutoffCoefficient M H omega N y < ε * m0 := by
    have e : |aux_rem_resolved_meshes_rho M H omega N (cF L) L y *
        cutoffCoefficient M H omega N y - cutoffCoefficient M H omega N y| =
        |aux_rem_resolved_meshes_rho M H omega N (cF L) L y - 1| *
          cutoffCoefficient M H omega N y := by
      rw [show aux_rem_resolved_meshes_rho M H omega N (cF L) L y *
          cutoffCoefficient M H omega N y - cutoffCoefficient M H omega N y =
          (aux_rem_resolved_meshes_rho M H omega N (cF L) L y - 1) *
            cutoffCoefficient M H omega N y by ring, abs_mul, abs_of_pos hpos]
    rw [← e]
    exact h1
  by_contra hcon
  push_neg at hcon
  have : ε * m0 ≤ |aux_rem_resolved_meshes_rho M H omega N (cF L) L y - 1| *
      cutoffCoefficient M H omega N y :=
    mul_le_mul hcon hy1' hm0.le (abs_nonneg _)
  linarith


theorem aux_rem_resolved_meshes_ips_apply {d : ℕ} (omega : BilateralField d) (L : ℕ)
    (y : SpatialCoordinates d) :
    (infraredPartialSum omega L) y =
      (∑ n ∈ Finset.range L, (omega (((n + 1 : ℕ) : ℤ))) y) -
        ∑ n ∈ Finset.range L, (omega (((n + 1 : ℕ) : ℤ))) 0 := by
  unfold infraredPartialSum
  rw [ContinuousMap.coe_sum, Finset.sum_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply]
  rfl

theorem aux_rem_resolved_meshes_rho_exp {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (cF : ℝ) (hcF : 0 < cF) (L : ℕ)
    (y : SpatialCoordinates d) :
    aux_rem_resolved_meshes_rho M H omega N cF L y =
      Real.exp ((Real.log (cF * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) +
          (∑ n ∈ Finset.range L, (omega (((n + 1 : ℕ) : ℤ))) 0) -
            (L : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) +
        ((infraredPartialSum omega L) y - H omega y)) := by
  have hpos : 0 < cF * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N :=
    mul_pos hcF (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
  unfold aux_rem_resolved_meshes_rho
  rw [aux_rem_resolved_meshes_ips_apply]
  rw [show Real.log (cF * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) +
      (∑ n ∈ Finset.range L, (omega (((n + 1 : ℕ) : ℤ))) 0) -
        (L : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P +
      ((∑ n ∈ Finset.range L, (omega (((n + 1 : ℕ) : ℤ))) y) -
        (∑ n ∈ Finset.range L, (omega (((n + 1 : ℕ) : ℤ))) 0) - H omega y) =
      Real.log (cF * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) +
        ((∑ n ∈ Finset.range L, (omega (((n + 1 : ℕ) : ℤ))) y) -
          (L : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P - H omega y) by ring,
    Real.exp_add, Real.exp_log hpos]

/-- `ρ_L → 1` uniformly on every compact set: uniform convergence of the infrared partial sums
on compacts (`hIR`) plus convergence at one good point of `Q`. -/
theorem aux_rem_resolved_meshes_rho_conv_compact {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega))) (N : ℕ)
    (aFin : ℕ → PositiveCoefficient (unitNeumannCube d)) (cF : ℕ → ℝ) (hcF : ∀ L, 0 < cF L)
    (hA : ∀ L : ℕ, ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (aFin L).val y = cF L *
        (Sreg.cutoffOn (N + L) (aux_rem_resolved_meshes_relabel N omega)
          ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
          ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val (((3 : ℝ) ^ (N : ℤ)) • y))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        |(aFin L).val y - cutoffCoefficient M H omega N y| < ε)
    (K : Set (SpatialCoordinates d)) (hK : IsCompact K) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ∀ y ∈ K,
      |aux_rem_resolved_meshes_rho M H omega N (cF L) L y - 1| < ε := by
  have hQ := aux_rem_resolved_meshes_rho_conv_Q Sreg H omega N aFin cF hA hconv
  choose L₀ hL₀ using fun n : ℕ => hQ (1 / ((n : ℝ) + 1)) (by positivity)
  have hall : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∀ n L : ℕ, L₀ n ≤ L →
        |aux_rem_resolved_meshes_rho M H omega N (cF L) L y - 1| < 1 / ((n : ℝ) + 1) := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro L
    by_cases h : L₀ n ≤ L
    · exact (hL₀ n L h).mono fun y hy _ => hy
    · exact Filter.Eventually.of_forall fun y h' => absurd h' h
  have hne : (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact (Metric.measure_ball_pos volume _ (by norm_num)).ne'
  haveI : (ae (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)))).NeBot :=
    ae_neBot.mpr hne
  obtain ⟨y₀, hy₀⟩ := hall.exists
  have hρ0 : ∀ ε > 0, ∃ L₁ : ℕ, ∀ L ≥ L₁,
      |aux_rem_resolved_meshes_rho M H omega N (cF L) L y₀ - 1| < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact ⟨L₀ n, fun L hL => (hy₀ n L hL).trans hn⟩
  -- uniform convergence of the infrared partial sums on `insert y₀ K`
  have hunif := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hIR)
    (insert y₀ K) (hK.insert y₀)
  have hD : ∀ ε > 0, ∃ L₁ : ℕ, ∀ L ≥ L₁, ∀ y, (y = y₀ ∨ y ∈ K) →
      |(infraredPartialSum omega L) y - H omega y| < ε := by
    intro ε hε
    have := (Metric.tendstoUniformlyOn_iff.mp hunif) ε hε
    rw [Filter.eventually_atTop] at this
    obtain ⟨L₁, hL₁⟩ := this
    refine ⟨L₁, fun L hL y hy => ?_⟩
    have hmem : y ∈ insert y₀ K := by
      rcases hy with h | h
      · rw [h]; exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ h
    have h := hL₁ L hL y hmem
    rw [Real.dist_eq, abs_sub_comm] at h
    exact h
  have key := aux_rem_resolved_meshes_rho_uniform
    (fun L => Real.log (cF L * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) +
      (∑ n ∈ Finset.range L, (omega (((n + 1 : ℕ) : ℤ))) 0) -
        (L : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
    (fun L y => (infraredPartialSum omega L) y - H omega y) K y₀ hD
    (fun ε hε => by
      obtain ⟨L₁, hL₁⟩ := hρ0 ε hε
      refine ⟨L₁, fun L hL => ?_⟩
      rw [← aux_rem_resolved_meshes_rho_exp M H omega N (cF L) (hcF L) L y₀]
      exact hL₁ L hL)
  intro ε hε
  obtain ⟨L₁, hL₁⟩ := key ε hε
  refine ⟨L₁, fun L hL y hy => ?_⟩
  rw [aux_rem_resolved_meshes_rho_exp M H omega N (cF L) (hcF L) L y]
  exact hL₁ L hL y hy


theorem aux_rem_resolved_meshes_avg_algebra (cF c vB I I' : ℝ) (hc : c ≠ 0) (hv : vB ≠ 0)
    (h : cF * I = I') : cF * ((c * vB)⁻¹ * (c * I)) = vB⁻¹ * I' := by
  rw [← h]
  field_simp

open scoped Pointwise in
theorem aux_rem_resolved_meshes_cube_eq_smul_ball {d : ℕ} (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (c : SpatialCoordinates d) (hR : (0 : ℝ) < (3 : ℝ) ^ (N - k + 1)) :
    (centeredCube ((3 : ℝ) ^ (N : ℤ) • c) ((3 : ℝ) ^ (N - k + 1)) hR : Set (SpatialCoordinates d)) =
      ((3 : ℝ) ^ (N : ℤ)) • Metric.ball c ((3 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) / 2) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (N : ℤ) := zpow_pos (by norm_num) _
  rw [_root_.smul_ball h3.ne', Real.norm_eq_abs, abs_of_pos h3]
  change Metric.ball ((3 : ℝ) ^ (N : ℤ) • c) ((3 : ℝ) ^ (N - k + 1) / 2) = _
  congr 1
  have e : (3 : ℝ) ^ (N - k + 1) = (3 : ℝ) ^ (N : ℤ) * (3 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    push_cast [Nat.cast_sub hkN, Nat.cast_sub hk1]
    ring
  rw [e]
  ring

/-- The finite root reference of the folded one-center estimate, multiplied by the transfer
constant, is the ball average of `ρ_L · s_N(k-1,·)` at the original scale. -/
theorem aux_rem_resolved_meshes_ref_avg {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {E : in_J d} {Sreg : in_6_16 d M}
    (It : in_iteration d M E Sreg) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N k L : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (hm2 : 2 ≤ N - k + 1)
    (cF : ℝ) (c : SpatialCoordinates d) :
    cF * It.ref (N + L) (N - k + 1 - 2) ((3 : ℝ) ^ (N : ℤ) • c)
        (aux_rem_resolved_meshes_relabel N omega) =
      (volume.real (Metric.ball c ((3 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) / 2)))⁻¹ *
        ∫ x in Metric.ball c ((3 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) / 2),
          aux_rem_resolved_meshes_rho M H omega N cF L x *
            (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - (k - 1)) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
              Real.exp ((H omega x + ∑ j ∈ Finset.range (k - 1), (omega (-(j : ℤ))) x) -
                ((k - 1 : ℕ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (N : ℤ) := zpow_pos (by norm_num) _
  have hR : (0 : ℝ) < (3 : ℝ) ^ (N - k + 1) := by positivity
  rw [It.ref_eq, show N - k + 1 - 2 + 2 = N - k + 1 by omega, Sreg.refAvg_eq _ _ _ _ hR,
    min_eq_left (show N - k + 1 ≤ N + L by omega),
    min_eq_left (show ((N - k + 1 : ℕ) : ℝ) ≤ ((N + L : ℕ) : ℝ) by exact_mod_cast (by omega)),
    aux_rem_resolved_meshes_cube_eq_smul_ball N k hk1 hkN c hR,
    aux_rem_resolved_meshes_setIntegral_smul _ measurableSet_ball h3,
    aux_rem_resolved_meshes_volume_smul _ h3]
  have hpt : ∀ x : SpatialCoordinates d,
      cF * (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k + 1) *
        Real.exp ((∑ j ∈ Finset.range (N + L + 1),
            (aux_rem_resolved_meshes_relabel N omega (j : ℤ)) (((3 : ℝ) ^ (N : ℤ)) • x)) -
          (∑ j ∈ Finset.range (N - k + 1 + 1),
            (aux_rem_resolved_meshes_relabel N omega (j : ℤ)) (((3 : ℝ) ^ (N : ℤ)) • x)) -
          (((N + L : ℕ) : ℝ) - ((N - k + 1 : ℕ) : ℝ)) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) =
      aux_rem_resolved_meshes_rho M H omega N cF L x *
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - (k - 1)) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
          Real.exp ((H omega x + ∑ j ∈ Finset.range (k - 1), (omega (-(j : ℤ))) x) -
            ((k - 1 : ℕ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
    intro x
    have hrel : ∀ j : ℕ, (aux_rem_resolved_meshes_relabel N omega (j : ℤ))
        (((3 : ℝ) ^ (N : ℤ)) • x) = (omega ((j : ℤ) - (N : ℤ))) x :=
      fun j => aux_rem_resolved_meshes_relabel_apply N omega (j : ℤ) x
    simp only [hrel]
    rw [aux_rem_resolved_meshes_sum_window omega N k L hk1 hkN x]
    have hA : SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≠ 0 := (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne'
    have hNk : N - (k - 1) = N - k + 1 := by omega
    rw [hNk]
    unfold aux_rem_resolved_meshes_rho
    have e1 : (((N + L : ℕ) : ℝ) - ((N - k + 1 : ℕ) : ℝ)) = (L : ℝ) + ((k - 1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hkN, Nat.cast_sub hk1]
      ring
    rw [e1]
    field_simp
    rw [mul_assoc (cF * SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k + 1)), ← Real.exp_add]
    congr 2
    ring
  have hvol : 0 < volume.real (Metric.ball c ((3 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) / 2)) := by
    have : volume (Metric.ball c ((3 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) / 2)) ≠ 0 :=
      (Metric.measure_ball_pos volume _ (by positivity)).ne'
    exact ENNReal.toReal_pos this measure_ball_lt_top.ne
  have h3d : (0 : ℝ) < ((3 : ℝ) ^ (N : ℤ)) ^ d := pow_pos h3 d
  refine aux_rem_resolved_meshes_avg_algebra _ _ _ _ _ h3d.ne' hvol.ne' ?_
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)


theorem aux_rem_resolved_meshes_rho_continuous {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) (cF : ℝ) (L : ℕ) :
    Continuous (aux_rem_resolved_meshes_rho M H omega N cF L) := by
  unfold aux_rem_resolved_meshes_rho
  refine continuous_const.mul (Real.continuous_exp.comp ?_)
  exact ((continuous_finset_sum _ fun n _ => (omega (((n + 1 : ℕ) : ℤ))).continuous).sub
    continuous_const).sub (H omega).continuous

theorem aux_rem_resolved_meshes_spoint_continuous {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N k : ℕ) :
    Continuous (fun x => SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
      Real.exp ((H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x) -
        (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
  refine continuous_const.mul (Real.continuous_exp.comp ?_)
  exact ((H omega).continuous.add
    (continuous_finset_sum (Finset.range k) fun (j : ℕ) _ =>
      (omega (-((j : ℕ) : ℤ))).continuous)).sub continuous_const

/-- **Reference convergence.**  The transfer constant times the finite root reference of the
folded estimate converges to the literal original reference `b_{k-1}` of the parent. -/
theorem aux_rem_resolved_meshes_ref_tendsto {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {E : in_J d} {Sreg : in_6_16 d M}
    (It : in_iteration d M E Sreg)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega))) (N : ℕ)
    (aFin : ℕ → PositiveCoefficient (unitNeumannCube d)) (cF : ℕ → ℝ) (hcF : ∀ L, 0 < cF L)
    (hA : ∀ L : ℕ, ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (aFin L).val y = cF L *
        (Sreg.cutoffOn (N + L) (aux_rem_resolved_meshes_relabel N omega)
          ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
          ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val (((3 : ℝ) ^ (N : ℤ)) • y))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        |(aFin L).val y - cutoffCoefficient M H omega N y| < ε)
    (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (hm2 : 2 ≤ N - k + 1) (c : SpatialCoordinates d) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      |cF L * It.ref (N + L) (N - k + 1 - 2) ((3 : ℝ) ^ (N : ℤ) • c)
          (aux_rem_resolved_meshes_relabel N omega) -
        aux_rem_resolved_meshes_bref M H omega N (k - 1) c| < ε := by
  set B : Set (SpatialCoordinates d) := Metric.ball c ((3 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) / 2)
  set sp : SpatialCoordinates d → ℝ := fun x =>
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - (k - 1)) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
      Real.exp ((H omega x + ∑ j ∈ Finset.range (k - 1), (omega (-(j : ℤ))) x) -
        ((k - 1 : ℕ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
  have hsp_cont : Continuous sp := aux_rem_resolved_meshes_spoint_continuous M H omega N (k - 1)
  have hsp_pos : ∀ x, 0 < sp x := fun x =>
    mul_pos (div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _))
      (Real.exp_pos _)
  have hKc : IsCompact (Metric.closedBall c ((3 : ℝ) ^ (-((k - 1 : ℕ) : ℤ)) / 2)) :=
    isCompact_closedBall _ _
  have hint : ∀ g : SpatialCoordinates d → ℝ, Continuous g → IntegrableOn g B volume := fun g hg =>
    (hg.continuousOn.integrableOn_compact hKc).mono_set Metric.ball_subset_closedBall
  have hbref : aux_rem_resolved_meshes_bref M H omega N (k - 1) c =
      (volume.real B)⁻¹ * ∫ x in B, sp x := rfl
  have hvol : 0 < volume.real B := by
    have : volume B ≠ 0 := (Metric.measure_ball_pos volume _ (by positivity)).ne'
    exact ENNReal.toReal_pos this measure_ball_lt_top.ne
  have hI0 : 0 < ∫ x in B, sp x := by
    haveI : NeZero (volume.restrict B) :=
      ⟨by rw [Ne, Measure.restrict_eq_zero]; exact (Metric.measure_ball_pos volume _ (by positivity)).ne'⟩
    have hexp_int : Integrable (fun x => Real.exp ((H omega x + ∑ j ∈ Finset.range (k - 1),
        (omega (-(j : ℤ))) x) - ((k - 1 : ℕ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P))
        (volume.restrict B) := by
      refine hint _ (Real.continuous_exp.comp ?_)
      exact ((H omega).continuous.add
        (continuous_finset_sum (Finset.range (k - 1)) fun (j : ℕ) _ =>
          (omega (-((j : ℕ) : ℤ))).continuous)).sub continuous_const
    have hpos := integral_exp_pos (μ := volume.restrict B) hexp_int
    change 0 < ∫ x in B, SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - (k - 1)) /
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N * Real.exp ((H omega x + ∑ j ∈ Finset.range (k - 1),
        (omega (-(j : ℤ))) x) - ((k - 1 : ℕ) : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
    rw [integral_const_mul]
    exact mul_pos (div_pos (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _)
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _)) hpos
  intro ε hε
  set bv := aux_rem_resolved_meshes_bref M H omega N (k - 1) c
  have hbv : 0 < bv := by rw [hbref]; exact mul_pos (inv_pos.mpr hvol) hI0
  obtain ⟨L₀, hL₀⟩ := aux_rem_resolved_meshes_rho_conv_compact Sreg H omega hIR N aFin cF hcF hA
    hconv _ hKc (ε / (2 * bv)) (by positivity)
  refine ⟨L₀, fun L hL => ?_⟩
  rw [aux_rem_resolved_meshes_ref_avg It H omega N k L hk1 hkN hm2 (cF L) c, hbref]
  rw [← mul_sub, ← integral_sub (hint _ ((aux_rem_resolved_meshes_rho_continuous M H omega N
    (cF L) L).mul hsp_cont)) (hint sp hsp_cont)]
  have hbound : |∫ x in B, (aux_rem_resolved_meshes_rho M H omega N (cF L) L x * sp x - sp x)| ≤
      ε / (2 * bv) * ∫ x in B, sp x := by
    rw [← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans ?_
    apply setIntegral_mono_on
    · exact ((hint _ ((aux_rem_resolved_meshes_rho_continuous M H omega N (cF L) L).mul
        hsp_cont)).sub (hint sp hsp_cont)).abs
    · exact (hint sp hsp_cont).const_mul _
    · exact measurableSet_ball
    · intro x hx
      have hr := hL₀ L hL x (Metric.ball_subset_closedBall hx)
      rw [show aux_rem_resolved_meshes_rho M H omega N (cF L) L x * sp x - sp x =
        (aux_rem_resolved_meshes_rho M H omega N (cF L) L x - 1) * sp x by ring, abs_mul,
        abs_of_pos (hsp_pos x)]
      exact mul_le_mul_of_nonneg_right hr.le (hsp_pos x).le
  rw [abs_mul, abs_of_pos (inv_pos.mpr hvol)]
  calc (volume.real B)⁻¹ *
        |∫ x in B, (aux_rem_resolved_meshes_rho M H omega N (cF L) L x * sp x - sp x)|
      ≤ (volume.real B)⁻¹ * (ε / (2 * bv) * ∫ x in B, sp x) :=
        mul_le_mul_of_nonneg_left hbound (inv_pos.mpr hvol).le
    _ = ε / (2 * bv) * bv := by rw [hbref]; ring
    _ < ε := by field_simp; linarith


/-! #### The finite-cutoff residual and the passage to the actual coefficient -/

theorem aux_rem_resolved_meshes_cutoff_coeFn {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) :
    ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val x =
        cutoffCoefficient M H omega N x := by
  haveI hΩ : Fact (((centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
      Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) ⊆
      closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) :=
    ⟨centeredCube_subset_closedCube (fun _ : Fin d => (1 / 2 : ℝ)) one_pos⟩
  filter_upwards [
    expPotentialCoefficient_coeFn (compactPotentialToLp
      (Ω := centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)
      (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)
      (continuousPositiveLog (cutoffCoefficientCM M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
        (cutoffCoefficientCM_pos M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) -
        ContinuousMap.const (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) (Real.log 1))),
    compactPotentialToLp_on_domain (Ω := centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)
      (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)
      (continuousPositiveLog (cutoffCoefficientCM M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
        (cutoffCoefficientCM_pos M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) -
        ContinuousMap.const (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos) (Real.log 1)),
    ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet] with x hexp hroot hxQ
  change (normalizedContinuousPositiveCoefficient
    (Ω := centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)
    (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos)
    (cutoffCoefficientCM M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
    (cutoffCoefficientCM_pos M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) 1 one_pos).val x = _
  unfold normalizedContinuousPositiveCoefficient
  rw [hexp, hroot hxQ]
  change Real.exp (Real.log ((cutoffCoefficientCM M H omega N (fun _ : Fin d => (1 / 2 : ℝ))
    one_pos) ⟨x, hΩ.out hxQ⟩) - Real.log 1) = _
  rw [Real.log_one, sub_zero, Real.exp_log
    (cutoffCoefficientCM_pos M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos _)]
  rfl


/-- **The finite-cutoff one-step residual** (`R2`).  For a finite infrared coefficient
`a = c_F · a_{N+L}(3^N ·)` on `Q` (the relabelled cutoff coefficient of `in_6_16`), an arbitrary
essentially bounded mean-zero source and weak Neumann solution, and a root of depth `k` with
active faces `I`, at every target depth `n` inside the tightened prefix window
(`n + ℒ ≤ N-k+1`), the folded one-center estimate transported to `Q`:
`E(3^{n-N}/2) ≤ C₁ (s/R_k)^{t₀} [E(3R_k) + (c_F · ref)^{-1} ‖f‖_∞² R_k^{d+2}]` with the root
reference `ref = It.ref (N+L) (N-k+1-2) (3^N·centre) (relabel N ω)`. -/
def aux_rem_resolved_meshes_finite_onestep (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 : ℝ) (Kt C1 delta1 : ℝ) : Prop :=
  ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (E : in_J d)
    (_ : in_poincare d hd E) (_ : in_extension d hd E)
    (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
    (_ : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩),
    M.delta ≤ delta1 →
    ∀ (omega : BilateralField d) (N L : ℕ) (cF : ℝ), 0 < cF →
    ∀ a : PositiveCoefficient (unitNeumannCube d),
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        a.val y = cF * (Sreg.cutoffOn (N + L) (aux_rem_resolved_meshes_relabel N omega)
          ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
          ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val (((3 : ℝ) ^ (N : ℤ)) • y)) →
    ∀ f : SpatialCoordinates d → ℝ,
      AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
    ∀ Kf : ℝ, 0 ≤ Kf →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
    ∀ u : meanZeroSobolevGraph (unitNeumannCube d), SolvesNeumann a f u →
    ∀ (y : SpatialCoordinates d), y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
    ∀ (I : Finset (Fin d)) (n k : ℕ),
      1 ≤ k → k ≤ N → (3 : ℝ) ^ (-((k : ℤ))) / 2 ≤ Rstar →
      8 * ((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) < (3 : ℝ) ^ (-((k : ℤ))) / 2 →
      (∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ min (y i) (1 - y i)) →
      n + It.prefixLen ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
          (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1)
          (aux_rem_resolved_meshes_relabel N omega) ≤ N - k + 1 →
      aux_rem_resolved_meshes_energy a u
          (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2)) ≤
        C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy a u
              (Metric.ball (aux_rem_resolved_meshes_center y I)
                (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (cF * It.ref (N + L) (N - k + 1 - 2) ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
              (aux_rem_resolved_meshes_relabel N omega))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))

/-- Arithmetic of the stability chain. -/
theorem aux_rem_resolved_meshes_chain_arith (es Ps esL e3L P3 e3 W srcL K δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) (hK : 0 ≤ K) (hPs : 0 ≤ Ps) (hP3 : 0 ≤ P3) (hsrc : 0 ≤ srcL)
    (h1 : es ≤ 2 * Ps + 2 * W) (h2 : (1 - δ) * Ps ≤ esL) (h3 : esL ≤ K * (e3L + srcL))
    (h4 : e3L ≤ (1 + δ) * P3) (h5 : P3 ≤ 2 * e3 + 2 * W) :
    es ≤ 20 / 3 * (K * e3) + 8 / 3 * (K * srcL) + (20 / 3 * (K * W) + 2 * W) := by
  have a1 : 3 / 4 * Ps ≤ (1 - δ) * Ps := mul_le_mul_of_nonneg_right (by linarith) hPs
  have a2 : (1 + δ) * P3 ≤ 5 / 4 * P3 := mul_le_mul_of_nonneg_right (by linarith) hP3
  have a3 : K * e3L ≤ K * (5 / 4 * (2 * e3 + 2 * W)) :=
    mul_le_mul_of_nonneg_left (h4.trans (a2.trans (by linarith))) hK
  have a4 : K * (5 / 4 * (2 * e3 + 2 * W)) = 5 / 2 * (K * e3) + 5 / 2 * (K * W) := by ring
  have a5 : K * (e3L + srcL) = K * e3L + K * srcL := by ring
  linarith


theorem aux_rem_resolved_meshes_cutoff_lower {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (N : ℕ) :
    ∃ m0 : ℝ, 0 < m0 ∧ ∀ y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
      m0 ≤ cutoffCoefficient M H omega N y := by
  have hK : IsCompact (Metric.closedBall (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)) :=
    isCompact_closedBall _ _
  obtain ⟨y1, -, hy1⟩ := hK.exists_isMinOn
    ⟨(fun _ : Fin d => (1 / 2 : ℝ)), Metric.mem_closedBall_self (by norm_num)⟩
    (aux_rem_resolved_meshes_cutoffCoefficient_continuous M H omega N).continuousOn
  exact ⟨cutoffCoefficient M H omega N y1,
    mul_pos (inv_pos.mpr (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _),
    fun y hy => hy1 (Metric.ball_subset_closedBall hy)⟩

theorem aux_rem_resolved_meshes_form_neg {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) (g h : HilbertGradient Ω) :
    weightedGradientForm a.val (g - h) (g - h) = weightedGradientForm a.val (h - g) (h - g) := by
  rw [show g - h = -(h - g) by abel]
  simp only [map_neg, ContinuousLinearMap.neg_apply, neg_neg]


/-- The local-energy half of the stability chain. -/
theorem aux_rem_resolved_meshes_local_chain {d : ℕ}
    (a b : PositiveCoefficient (unitNeumannCube d)) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ4 : δ ≤ 1 / 4)
    (hclose : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      |b.val x - a.val x| ≤ δ * a.val x)
    (gu gL : HilbertGradient (unitNeumannCube d)) {Bs B3 : Set (SpatialCoordinates d)}
    (hBs : MeasurableSet Bs) (hB3 : MeasurableSet B3) (K srcL : ℝ) (hK : 0 ≤ K)
    (hsrc : 0 ≤ srcL)
    (hF : localGradientEnergy b hBs gL ≤ K * (localGradientEnergy b hB3 gL + srcL)) :
    localGradientEnergy a hBs gu ≤ 20 / 3 * (K * localGradientEnergy a hB3 gu) +
      8 / 3 * (K * srcL) +
      (20 / 3 * (K * weightedGradientForm a.val (gL - gu) (gL - gu)) +
        2 * weightedGradientForm a.val (gL - gu) (gL - gu)) := by
  have hδ1 : δ < 1 := by linarith
  have hcmp_s := aux_rem_resolved_meshes_local_cmp a b δ hδ1 hclose hBs gL
  have hcmp_3 := aux_rem_resolved_meshes_local_cmp a b δ hδ1 hclose hB3 gL
  have h1 : localGradientEnergy a hBs gu ≤ 2 * localGradientEnergy a hBs gL +
      2 * weightedGradientForm a.val (gL - gu) (gL - gu) := by
    have hsub := localGradientEnergy_sub_le a hBs gu gL
    have hle := localGradientEnergy_le a hBs (gu - gL)
    rw [aux_rem_resolved_meshes_form_neg] at hle
    linarith
  have h5 : localGradientEnergy a hB3 gL ≤ 2 * localGradientEnergy a hB3 gu +
      2 * weightedGradientForm a.val (gL - gu) (gL - gu) := by
    have hsub := localGradientEnergy_sub_le a hB3 gL gu
    have hle := localGradientEnergy_le a hB3 (gL - gu)
    linarith
  exact aux_rem_resolved_meshes_chain_arith _ _ _ _ _ _ _ srcL K δ hδ0 hδ4 hK
    (localGradientEnergy_nonneg a hBs gL) (localGradientEnergy_nonneg a hB3 gL) hsrc h1 hcmp_s.2 hF
    hcmp_3.1 h5

theorem aux_rem_resolved_meshes_err_delta (K Eu ε W δ : ℝ) (hK : 0 ≤ K) (hEu : 0 ≤ Eu)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδε : δ ≤ ε / (2 * ((20 / 3 * K + 2) * 2 * (Eu + 1) + 1)))
    (hW : W ≤ 2 * δ ^ 2 * Eu) : 20 / 3 * (K * W) + 2 * W ≤ ε / 2 := by
  set T : ℝ := (20 / 3 * K + 2) * 2 * (Eu + 1) with hT_def
  have hT : 0 < T := by positivity
  have hc : 0 ≤ 20 / 3 * K + 2 := by positivity
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have e : 20 / 3 * (K * W) + 2 * W = (20 / 3 * K + 2) * W := by ring
  rw [e]
  have hA1 : (20 / 3 * K + 2) * W ≤ (20 / 3 * K + 2) * (2 * δ ^ 2 * Eu) :=
    mul_le_mul_of_nonneg_left hW hc
  have hA2 : (20 / 3 * K + 2) * (2 * δ ^ 2 * Eu) ≤ δ * T := by
    have e2 : (20 / 3 * K + 2) * (2 * δ ^ 2 * Eu) = δ ^ 2 * ((20 / 3 * K + 2) * 2 * Eu) := by ring
    rw [e2]
    have hq : 0 ≤ (20 / 3 * K + 2) * 2 * Eu := by positivity
    have hq2 : (20 / 3 * K + 2) * 2 * Eu ≤ T := by
      rw [hT_def]
      have : (20 / 3 * K + 2) * 2 * Eu ≤ (20 / 3 * K + 2) * 2 * (Eu + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      exact this
    calc δ ^ 2 * ((20 / 3 * K + 2) * 2 * Eu) ≤ δ * ((20 / 3 * K + 2) * 2 * Eu) :=
          mul_le_mul_of_nonneg_right hδ2 hq
      _ ≤ δ * T := mul_le_mul_of_nonneg_left hq2 hδ0.le
  have hA3 : δ * T ≤ ε / 2 := by
    have h1 : δ * T ≤ ε / (2 * (T + 1)) * T := mul_le_mul_of_nonneg_right hδε hT.le
    have h2 : ε / (2 * (T + 1)) * T ≤ ε / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  linarith

theorem aux_rem_resolved_meshes_err_inv (K Z bv x ε η : ℝ) (hK : 0 ≤ K) (hZ : 0 ≤ Z)
    (hbv : 0 < bv) (hε : 0 < ε) (hη : η ≤ bv / 2)
    (hη2 : η ≤ ε * bv ^ 2 / (11 * (K * Z + 1))) (hx : |x - bv| < η) :
    8 / 3 * (K * (x⁻¹ * Z)) ≤ 8 / 3 * (K * (bv⁻¹ * Z)) + ε / 2 := by
  have hx1 := (abs_lt.mp hx).1
  have hx0 : bv / 2 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hKZ : 0 ≤ K * Z := mul_nonneg hK hZ
  have hdiff : x⁻¹ - bv⁻¹ ≤ 2 * η / bv ^ 2 := by
    rw [inv_sub_inv hxpos.ne' hbv.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : bv - x < η := by linarith
    have h2 : bv / 2 * bv ≤ x * bv := mul_le_mul_of_nonneg_right hx0.le hbv.le
    have h3 : 0 ≤ η := by linarith [abs_nonneg (x - bv)]
    nlinarith
  have e : 8 / 3 * (K * (x⁻¹ * Z)) - 8 / 3 * (K * (bv⁻¹ * Z)) = 8 / 3 * (K * Z) * (x⁻¹ - bv⁻¹) := by
    ring
  have h4 : 8 / 3 * (K * Z) * (x⁻¹ - bv⁻¹) ≤ 8 / 3 * (K * Z) * (2 * η / bv ^ 2) :=
    mul_le_mul_of_nonneg_left hdiff (by positivity)
  have h5 : 8 / 3 * (K * Z) * (2 * η / bv ^ 2) ≤ ε / 2 := by
    have hη0 : 0 ≤ η := by linarith [abs_nonneg (x - bv)]
    have h6 : 8 / 3 * (K * Z) * (2 * η / bv ^ 2) ≤
        8 / 3 * (K * Z) * (2 * (ε * bv ^ 2 / (11 * (K * Z + 1))) / bv ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h7 : 8 / 3 * (K * Z) * (2 * (ε * bv ^ 2 / (11 * (K * Z + 1))) / bv ^ 2) =
        16 / 33 * ε * (K * Z / (K * Z + 1)) := by
      field_simp
      ring
    have h8 : K * Z / (K * Z + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h9 : 16 / 33 * ε * (K * Z / (K * Z + 1)) ≤ 16 / 33 * ε * 1 :=
      mul_le_mul_of_nonneg_left h8 (by positivity)
    linarith
  linarith


theorem aux_rem_resolved_meshes_energy_local {d : ℕ}
    (a : PositiveCoefficient (unitNeumannCube d)) (u : meanZeroSobolevGraph (unitNeumannCube d))
    (A : Set (SpatialCoordinates d)) (hA : MeasurableSet A) :
    aux_rem_resolved_meshes_energy a u A =
      localGradientEnergy a hA (sobolevGradient (u : SobolevData (unitNeumannCube d))) :=
  aux_rem_resolved_meshes_energy_eq_local a _ A hA

theorem aux_rem_resolved_meshes_pos_of_close {x bv η : ℝ} (hbv : 0 < bv) (hη : η ≤ bv / 2)
    (hx : |x - bv| < η) : 0 < x := by
  have := (abs_lt.mp hx).1
  linarith

/-- The limit step in the abstract: if for every `ε` there is a finite level at which the bound
holds up to `ε`, the bound holds. -/
theorem aux_rem_resolved_meshes_good_final (es e3 bv Z K : ℝ) (hK : 0 ≤ K) (he3 : 0 ≤ e3)
    (hbv : 0 < bv) (hZ : 0 ≤ Z)
    (h : ∀ ε : ℝ, 0 < ε → es ≤ 20 / 3 * (K * e3) + 8 / 3 * (K * (bv⁻¹ * Z)) + ε) :
    es ≤ 7 * K * (e3 + bv⁻¹ * Z) := by
  have hlim : es ≤ 20 / 3 * (K * e3) + 8 / 3 * (K * (bv⁻¹ * Z)) :=
    le_of_forall_pos_le_add fun ε hε => h ε hε
  have h1 : 0 ≤ K * e3 := mul_nonneg hK he3
  have h2 : 0 ≤ K * (bv⁻¹ * Z) := mul_nonneg hK (mul_nonneg (inv_pos.mpr hbv).le hZ)
  have e : 7 * K * (e3 + bv⁻¹ * Z) = 7 * (K * e3) + 7 * (K * (bv⁻¹ * Z)) := by ring
  rw [e]
  linarith

/-- **Good branch, passage to the actual coefficient.**  The finite-cutoff residual at every
large infrared level, weak-solution stability and the reference convergence give the one-step
estimate for the actual coefficient `A_N` with the literal reference `b_{k-1}`. -/
theorem aux_rem_resolved_meshes_good_limit (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 Kt C1 delta1 : ℝ) (hC1 : 0 ≤ C1)
    (hfin : aux_rem_resolved_meshes_finite_onestep d hd Lstar Rstar t0 Kt C1 delta1)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (E : in_J d)
    (Poinc : in_poincare d hd E) (Ext : in_extension d hd E)
    (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
    (hdet : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hδ : M.delta ≤ delta1)
    (omega : BilateralField d)
    (hIR : Filter.Tendsto (infraredPartialSum omega) Filter.atTop (nhds (H omega))) (N : ℕ)
    (aFin : ℕ → PositiveCoefficient (unitNeumannCube d)) (cF : ℕ → ℝ) (hcF : ∀ L, 0 < cF L)
    (hA : ∀ L : ℕ, ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (aFin L).val y = cF L *
        (Sreg.cutoffOn (N + L) (aux_rem_resolved_meshes_relabel N omega)
          ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
          ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val (((3 : ℝ) ^ (N : ℤ)) • y))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        |(aFin L).val y - cutoffCoefficient M H omega N y| < ε)
    (f : SpatialCoordinates d → ℝ)
    (hf : AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hfb : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf)
    (hf0 : (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0)
    (u : meanZeroSobolevGraph (unitNeumannCube d))
    (hu : SolvesNeumann (cutoffPositiveCoefficient M H omega N
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) f u)
    (y : SpatialCoordinates d) (hy : y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (I : Finset (Fin d)) (n k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (hR : (3 : ℝ) ^ (-((k : ℤ))) / 2 ≤ Rstar)
    (h8 : 8 * ((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) < (3 : ℝ) ^ (-((k : ℤ))) / 2)
    (hI : ∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ min (y i) (1 - y i))
    (hgood : n + It.prefixLen ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
          (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1)
          (aux_rem_resolved_meshes_relabel N omega) ≤ N - k + 1) :
    aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
        (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2)) ≤
      7 * (C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0) *
        (aux_rem_resolved_meshes_energy
            (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
            (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
          (aux_rem_resolved_meshes_bref M H omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
            (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))) := by
  have hm2 : 2 ≤ N - k + 1 := by
    have := It.prefix_lower ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
      (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1) (aux_rem_resolved_meshes_relabel N omega)
    rw [It.k_eq] at this
    omega
  have hσ : 0 ≤ (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 := by
    positivity
  have hK : 0 ≤ C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 :=
    mul_nonneg hC1 hσ
  have hZ : 0 ≤ Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2) := by positivity
  have hbv : 0 < aux_rem_resolved_meshes_bref M H omega N (k - 1)
      (aux_rem_resolved_meshes_center y I) :=
    aux_lane4_two_mesh_energy_bound_bpos M H omega N (k - 1) (aux_rem_resolved_meshes_center y I)
  have hBs : MeasurableSet (Metric.ball (aux_rem_resolved_meshes_center y I)
    ((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2)) := measurableSet_ball
  have hB3 : MeasurableSet (Metric.ball (aux_rem_resolved_meshes_center y I)
    (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) := measurableSet_ball
  rw [aux_rem_resolved_meshes_energy_local _ _ _ hBs, aux_rem_resolved_meshes_energy_local _ _ _ hB3]
  refine aux_rem_resolved_meshes_good_final _ _ _ _ _ hK (localGradientEnergy_nonneg _ _ _) hbv hZ ?_
  intro ε hε
  have hEu := (localGradientEnergy_nonneg
    (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
    MeasurableSet.univ (sobolevGradient (u : SobolevData (unitNeumannCube d)))).trans
    (localGradientEnergy_le _ MeasurableSet.univ _)
  -- tolerances
  obtain ⟨m0, hm0, hm0Q⟩ := aux_rem_resolved_meshes_cutoff_lower M H omega N
  have hδ0 : 0 < min (1 / 4) (ε / (2 * ((20 / 3 * (C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) /
      ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0) + 2) * 2 *
      (weightedGradientForm
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val
        (sobolevGradient (u : SobolevData (unitNeumannCube d)))
        (sobolevGradient (u : SobolevData (unitNeumannCube d))) + 1) + 1))) :=
    lt_min (by norm_num) (by positivity)
  obtain ⟨L₁, hL₁⟩ := hconv _ (mul_pos hδ0 hm0)
  have hη0 : 0 < min (aux_rem_resolved_meshes_bref M H omega N (k - 1)
      (aux_rem_resolved_meshes_center y I) / 2)
      (ε * aux_rem_resolved_meshes_bref M H omega N (k - 1) (aux_rem_resolved_meshes_center y I) ^ 2 /
        (11 * (C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) + 1))) :=
    lt_min (by positivity) (by positivity)
  obtain ⟨L₂, hL₂⟩ := aux_rem_resolved_meshes_ref_tendsto It H omega hIR N aFin cF hcF hA hconv
    k hk1 hkN hm2 (aux_rem_resolved_meshes_center y I) _ hη0
  have hex := aux_rem_resolved_meshes_neumann_exists hd (aFin (max L₁ L₂)) f hf Kf hfb hf0
  rcases hex with ⟨uL, huL⟩
  have hclose : ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      |(aFin (max L₁ L₂)).val x -
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val x| ≤
        min (1 / 4) (ε / (2 * ((20 / 3 * (C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) /
          ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0) + 2) * 2 *
          (weightedGradientForm
            (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val
            (sobolevGradient (u : SobolevData (unitNeumannCube d)))
            (sobolevGradient (u : SobolevData (unitNeumannCube d))) + 1) + 1))) *
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val x := by
    filter_upwards [hL₁ (max L₁ L₂) (le_max_left _ _), aux_rem_resolved_meshes_cutoff_coeFn M H omega N,
      ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet] with x h1 h2 h3
    rw [h2]
    have h4 := mul_le_mul_of_nonneg_left (hm0Q x h3) hδ0.le
    linarith
  have hF := hfin M E Poinc Ext Sreg It hdet hδ omega N (max L₁ L₂) (cF (max L₁ L₂))
    (hcF (max L₁ L₂)) (aFin (max L₁ L₂)) (hA (max L₁ L₂)) f hf Kf hKf hfb hf0 uL huL y hy I n k
    hk1 hkN hR h8 hI hgood
  rw [aux_rem_resolved_meshes_energy_local _ _ _ hBs,
    aux_rem_resolved_meshes_energy_local _ _ _ hB3] at hF
  have hW := aux_rem_resolved_meshes_stability
    (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
    (aFin (max L₁ L₂)) _ hδ0.le (min_le_left _ _) hclose f u uL hu huL
  rw [map_sub] at hW
  have hrefL := hL₂ (max L₁ L₂) (le_max_right _ _)
  have hxpos := aux_rem_resolved_meshes_pos_of_close hbv (min_le_left _ _) hrefL
  have hchain := aux_rem_resolved_meshes_local_chain
    (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
    (aFin (max L₁ L₂)) _ hδ0.le (min_le_left _ _) hclose
    (sobolevGradient (u : SobolevData (unitNeumannCube d)))
    (sobolevGradient (uL : SobolevData (unitNeumannCube d))) hBs hB3 _ _ hK
    (mul_nonneg (inv_pos.mpr hxpos).le hZ)
    (by
      refine hF.trans (le_of_eq ?_)
      ring)
  have herr1 := aux_rem_resolved_meshes_err_delta _ _ ε _ _ hK hEu hε hδ0
    ((min_le_left _ _).trans (by norm_num)) (min_le_right _ _) hW
  have herr2 := aux_rem_resolved_meshes_err_inv _ _ _ _ ε _ hK hZ hbv hε (min_le_left _ _)
    (min_le_right _ _) hrefL
  linarith

/-- The bad-prefix branch: the target radius lies within the prefix window of the root, so the
trivial bound `E(s) ≤ E(L_* R)` is paid by the allowance `e^{c ℒ}` with `c ≥ t₀ log 3`. -/
theorem aux_rem_resolved_meshes_bad_factor (t0 c : ℝ) (ht0 : 0 < t0) (hc : t0 * Real.log 3 ≤ c)
    (j : ℤ) (k pl : ℕ) (hjk : 0 ≤ j + (k : ℤ) + (pl : ℤ)) :
    1 ≤ Real.exp (c * (pl : ℝ)) * (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hsR : ((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2) = (3 : ℝ) ^ (j + (k : ℤ)) := by
    rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0), ← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  rw [hsR, Real.rpow_def_of_pos (zpow_pos (by norm_num) _), Real.log_zpow, ← Real.exp_add]
  apply Real.one_le_exp
  push_cast
  have h1 : t0 * Real.log 3 * (pl : ℝ) ≤ c * (pl : ℝ) :=
    mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
  have h2 : (0 : ℝ) ≤ ((j + (k : ℤ) + (pl : ℤ) : ℤ) : ℝ) := by exact_mod_cast hjk
  push_cast at h2
  have h3 : 0 ≤ t0 * Real.log 3 * ((j : ℝ) + (k : ℝ) + (pl : ℝ)) := by positivity
  have e1 : t0 * Real.log 3 * ((j : ℝ) + (k : ℝ) + (pl : ℝ)) =
      t0 * Real.log 3 * (pl : ℝ) + ((j : ℝ) + (k : ℝ)) * Real.log 3 * t0 := by ring
  linarith

/-- **Stage 1.**  The one-step residual for the actual coefficient follows from the finite-cutoff
residual: the bad-prefix branch is paid by the allowance, and the good branch passes to the limit
along the finite infrared levels of `hphysical`. -/
theorem aux_rem_resolved_meshes_onestep_of_finite (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 : ℝ) (hLstar : 10 ≤ Lstar) (hRstar_lt : Rstar < 1 / (100 * Lstar))
    (ht0 : 0 < t0) (Kt C1 delta1 : ℝ) (hC1 : 0 ≤ C1)
    (hfin : aux_rem_resolved_meshes_finite_onestep d hd Lstar Rstar t0 Kt C1 delta1) :
    aux_rem_resolved_meshes_onestep d hd Lstar Rstar t0 1 Kt (max 1 (7 * C1))
      (t0 * Real.log 3 + 1) delta1 := by
  intro M E Poinc Ext Sreg It hdet H hδ omega hIR N hphys f hf Kf hKf hfb hf0 u hu y hy I s k
    hs hs1 hs0 hk h8 hR hI
  obtain ⟨aFin, hA, hconv⟩ := hphys
  choose cF hcF hAc using hA
  obtain ⟨j, rfl⟩ := hs
  dsimp only at hs1 hs0 h8 ⊢
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hc0 : 0 ≤ t0 * Real.log 3 + 1 := by positivity
  -- the target depth
  have hjN : -(N : ℤ) ≤ j := by
    have h1 : (3 : ℝ) ^ (-(N : ℤ)) ≤ (3 : ℝ) ^ j := by linarith
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp h1
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    subst hk0
    have : (1 : ℝ) / 2 ≤ Rstar := by simpa using hR
    have h100 : 0 < 100 * Lstar := by linarith
    have : 1 / (100 * Lstar) ≤ 1 / 1000 := by
      rw [div_le_div_iff₀ h100 (by norm_num)]; linarith
    linarith
  set n : ℕ := (j + (N : ℤ)).toNat with hn_def
  have hn : ((n : ℕ) : ℤ) = j + (N : ℤ) := Int.toNat_of_nonneg (by omega)
  have hjn : j = (n : ℤ) - (N : ℤ) := by omega
  set pl := It.prefixLen ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
    (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1) (aux_rem_resolved_meshes_relabel N omega)
    with hpl
  have hmono : ∀ {A A' : Set (SpatialCoordinates d)}, A ⊆ A' →
      aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u A ≤
      aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u A' :=
    fun h => aux_rem_resolved_strata_energy_mono
      (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
      ⟨u.1, u.2.1⟩ h
  have hnn : ∀ A : Set (SpatialCoordinates d), 0 ≤ aux_rem_resolved_meshes_energy
      (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u A :=
    fun A => aux_rem_resolved_strata_energy_nonneg
      (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) ⟨u.1, u.2.1⟩ A
  have hRk : 0 < (3 : ℝ) ^ (-((k : ℤ))) / 2 := by positivity
  have hbv : 0 < aux_rem_resolved_meshes_bref M H omega N (k - 1)
      (aux_rem_resolved_meshes_center y I) :=
    aux_lane4_two_mesh_energy_bound_bpos M H omega N (k - 1) (aux_rem_resolved_meshes_center y I)
  have hsrc : 0 ≤ (aux_rem_resolved_meshes_bref M H omega N (k - 1)
      (aux_rem_resolved_meshes_center y I))⁻¹ * Kf ^ 2 *
      ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2) := by positivity
  have hLR : aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
        (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ j / 2)) ≤
      aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
        (Metric.ball (aux_rem_resolved_meshes_center y I) (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) :=
    hmono (Metric.ball_subset_ball (by nlinarith))
  have hσ : 0 ≤ (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 := by positivity
  have hexp1 : 1 ≤ Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) :=
    Real.one_le_exp (mul_nonneg hc0 (Nat.cast_nonneg _))
  by_cases hgood : n + pl ≤ N - k + 1
  · -- good branch
    have hG := aux_rem_resolved_meshes_good_limit d hd Lstar Rstar t0 Kt C1 delta1 hC1 hfin M E
      Poinc Ext Sreg It hdet H hδ omega hIR N aFin cF hcF hAc hconv f hf Kf hKf hfb hf0 u hu y hy I
      n k hk1 hk hR (by rw [← hjn]; exact h8) hI hgood
    rw [← hjn] at hG
    have h3L := hmono (Metric.ball_subset_ball (x := aux_rem_resolved_meshes_center y I)
      (show 3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) by nlinarith))
    refine hG.trans ?_
    have hC : 7 * C1 ≤ max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) := by
      have := le_max_right 1 (7 * C1)
      have h1 : 0 ≤ max 1 (7 * C1) := le_trans zero_le_one (le_max_left _ _)
      nlinarith
    have hB : 0 ≤ aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
        (aux_rem_resolved_meshes_bref M H omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
          (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by
      have := hnn (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2)))
      positivity
    calc 7 * (C1 * (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0) *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M H omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)))
        = (7 * C1) * (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M H omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))) := by ring
      _ ≤ (max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ))) *
            (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M H omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))) := by
          gcongr
      _ ≤ max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) *
            (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I)
                (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M H omega N (1 - 1 + (k - 1))
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by
          rw [show 1 - 1 + (k - 1) = k - 1 by omega]
          have hK0 : 0 ≤ max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) *
              (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 := by positivity
          apply mul_le_mul_of_nonneg_left _ hK0
          have e : (aux_rem_resolved_meshes_bref M H omega N (k - 1)
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) =
            (aux_rem_resolved_meshes_bref M H omega N (k - 1)
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2) := by ring
          rw [e]
          linarith
      _ = _ := by rw [show 1 - 1 + (k - 1) = k - 1 by omega]
  · -- bad branch
    have hjk : 0 ≤ j + (k : ℤ) + (pl : ℤ) := by
      push_neg at hgood
      have : (N : ℤ) - k + 1 < (n : ℤ) + pl := by
        have : N - k + 1 < n + pl := hgood
        omega
      omega
    have hfac := aux_rem_resolved_meshes_bad_factor t0 (t0 * Real.log 3 + 1) ht0 (by linarith) j k
      pl hjk
    have hE0 := hnn (Metric.ball (aux_rem_resolved_meshes_center y I)
      (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2)))
    calc aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ j / 2))
        ≤ 1 * (aux_rem_resolved_meshes_energy
            (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
            (Metric.ball (aux_rem_resolved_meshes_center y I)
              (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
          (aux_rem_resolved_meshes_bref M H omega N (k - 1)
            (aux_rem_resolved_meshes_center y I))⁻¹ *
            Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by linarith
      _ ≤ (max 1 (7 * C1) * (Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) *
            (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0)) *
          (aux_rem_resolved_meshes_energy
            (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
            (Metric.ball (aux_rem_resolved_meshes_center y I)
              (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
          (aux_rem_resolved_meshes_bref M H omega N (k - 1)
            (aux_rem_resolved_meshes_center y I))⁻¹ *
            Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          have := le_max_left 1 (7 * C1)
          nlinarith
      _ = _ := by ring



/-! ### The folded one-center package for every face set, including `I = ∅`

`prop_folded_iteration` is stated for `I.Nonempty`; its proof uses that hypothesis only in the
good-scale fold localization.  For `I = ∅` the fold is the identity and the folded coefficient is
the cutoff coefficient itself, so the localization is `E.err ≤ √(·) E.err`.  The proof text below
is `prop_folded_iteration`'s own (constants and chain unchanged), with that single step extended. -/

section FoldedAllLocalization
theorem aux_rem_resolved_meshes_fold_localization_all :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)],
  ∀ (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
    ∀ (alpha : ℝ), alpha ∈ It.alphaRange → M.delta ≤ It.C⁻¹ →
    let s0 : ℝ := It.s0
    let eps : ℝ := It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)
    64 * M.delta ^ 2 ≤ s0 → s0⁻¹ * M.delta ^ 2 ≤ eps → eps ≤ 1 →
    ∀ (L m : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
      (om : BilateralField d) (I P : Finset (Fin d)),
      ∀ foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR),
        ((foldedCoef.val : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
          fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val
            (coordinateFold z I P x)) →
        ∀ j : ℕ, j + 2 ≤ L → j + 2 ≤ m → It.good (j + 2) z eps s0 om →
          E.err z ((3 : ℝ) ^ m) hR foldedCoef z ((3 : ℝ) ^ (j + 2))
              (It.ref L j z om) s0 2 ≤
            Real.sqrt (1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * s0) - 1)) *
              E.err z ((3 : ℝ) ^ m) hR (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR) z
                ((3 : ℝ) ^ (j + 2)) (It.ref L j z om) s0 2 := by
  intro d hd hms hbs E M Sreg It alpha halpha hdelta
  dsimp only
  intro h64 hse heps L m z hR om I P foldedCoef hfolded j hjL hjm hgood
  by_cases hI : I.Nonempty
  · exact lem_repair_err_fold_localization d hd E M Sreg It alpha halpha hdelta h64 hse heps
      L m z hR om I P hI foldedCoef hfolded j hjL hjm hgood
  · have hI0 : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    have hfc : foldedCoef = Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR := by
      apply Subtype.ext
      apply Lp.ext
      refine hfolded.trans (Filter.Eventually.of_forall fun x => ?_)
      have hx : coordinateFold z I P x = x := by
        funext i
        simp [coordinateFold, hI0]
      simp only [hx]
    rw [hfc]
    have hs : 0 < 1 - 2 * It.s0 := by rw [It.s0_eq]; norm_num
    have h3 : (1 : ℝ) < (3 : ℝ) ^ (1 - 2 * It.s0) := Real.one_lt_rpow (by norm_num) hs
    have hfrac : 0 ≤ 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * It.s0) - 1) :=
      div_nonneg (by positivity) (by linarith)
    have h1 : 1 ≤ Real.sqrt (1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * It.s0) - 1)) :=
      Real.one_le_sqrt.mpr (by linarith)
    exact le_mul_of_one_le_left (E.err_nonneg _ _ _ _ _ _ _ _ _) h1

end FoldedAllLocalization

section FoldedAllGSE
open SubdiffusiveProcess.CoarseGrainingVocab
def aux_rem_resolved_meshes_gse_all_prop (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cg : ℝ) : Prop :=
      ∀ (E : in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
      ∀ (alpha : ℝ), alpha ∈ It.alphaRange → M.delta ≤ It.C⁻¹ →
      64 * M.delta ^ 2 ≤ It.s0 →
      It.s0⁻¹ * M.delta ^ 2 ≤ It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ) →
      It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ) ≤ 1 →
      ∀ (L m : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
        (om : BilateralField d) (I P : Finset (Fin d)),
      ∀ foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR),
        ((foldedCoef.val : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
          fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val (coordinateFold z I P x)) →
      ∀ j : ℕ, j + 2 ≤ L → j + 2 ≤ m →
        It.good (j + 2) z (It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) It.s0 om →
      ∀ (a' : SpatialCoordinates d → ℝ),
        (∀ᵐ y ∂volume.restrict
            (Homogenization.openCubeSet (Homogenization.originCube d ((j : ℤ) + 2))),
          a' y = (foldedCoef.val : SpatialCoordinates d → ℝ) (fun i => z i + y i)) →
      ∀ data : ScalarTriadicCoeffData (fun y => a' (y + 0)),
        paperHomogenizationError
            (Homogenization.originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2) (1 / 32)
            Homogenization.Book.Ch02.MultiscaleExponent.infinity
            (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
            data.toTriadicCoeffFamily (It.ref L j z om) ≤
          ENNReal.ofReal (Cg * min (It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ))
            (M.delta ^ 2 + (It.C2⁻¹ * (1 - alpha) ^ (1 / 2 : ℝ)) ^ 8 +
              It.score (j + 2) z It.s0 om))

/-- The good-scale error for every face set `I`, including the unfolded `I = ∅`. -/
theorem aux_rem_resolved_meshes_gse_all_min (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ Cg : ℝ, 0 < Cg ∧ aux_rem_resolved_meshes_gse_all_prop d Cg := by
  obtain ⟨Cg, hCg, hT⟩ := lem_repair_err_good_scale_transport d hd
  refine ⟨Cg, hCg, ?_⟩
  intro E M Sreg It alpha halpha hdel h64 heps1 heps2 L m z hR om I P foldedCoef hfold j hjL
    hjm hgood a' ha' data
  have hloc := aux_rem_resolved_meshes_fold_localization_all d hd E M Sreg It alpha halpha hdel
    h64 heps1 heps2 L m z hR om I P foldedCoef hfold j hjL hjm hgood
  have htr := hT E M Sreg It alpha halpha hdel h64 heps1 heps2 L m j z hR om hjL hjm hgood
  have hs0 : It.s0 ∈ Set.Ioc (0 : ℝ) 1 := by
    rw [It.s0_eq]; constructor <;> norm_num
  obtain ⟨hEq, hfin⟩ := aux_prop_folded_iteration_err_physical E z m j hR hjm foldedCoef a' ha'
    data (It.ref L j z om) (It.ref_pos L j z om) It.s0 hs0
  rw [show (1 / 32 : ℝ) = It.s0 from It.s0_eq.symm]
  rw [← ENNReal.ofReal_toReal hfin, ← hEq]
  exact ENNReal.ofReal_le_ofReal (hloc.trans htr)

end FoldedAllGSE

section FoldedAllRooted
open Filter SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book

theorem aux_rem_resolved_meshes_rooted_all (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (Cg CH CI Cc CP cC c1 c2 eta K C : ℝ) (h : ℕ)
    (hCg : 0 < Cg) (hCH : 0 < CH) (hCI : 0 < CI) (hCc : 0 < Cc) (hCP : 0 < CP)
    (hcC : 1 ≤ cC) (hc1 : 2 ≤ c1) (hc12 : c1 ≤ c2)
    (hGSE : aux_rem_resolved_meshes_gse_all_prop d Cg)
    (hchain : aux_prop_folded_iteration_chain_prop d Cg CH CI Cc CP)
    (hconst : ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
      (It : in_iteration d M E Sreg), It.C = cC ∧ It.C1 = c1 ∧ It.C2 = c2)
    (hh : 0 < h) (hth : ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h < 3 / 5)
    (heta0 : 0 < eta) (heta1 : eta ≤ 1)
    (hthr : CH * ((3 : ℝ) ^ (-(h : ℝ) / 2) +
        (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * eta) ≤
      ((3 : ℝ) ^ (-(1 / 4 : ℝ))) ^ h)
    (hK1 : 1 ≤ K)
    (hKGam : (d : ℝ) * Real.log 3 + (CI * (h + 1) + 3 * (CH * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) *
        (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * Cg) * CI) + 2 * cC ≤ K)
    (hKeta : 1 / (2 * eta ^ 2) ≤ K)
    (hC46 : 46 ≤ C) (hKcC : K * cC ≤ C) (hKc2 : 1024 * c2 ^ 2 * K ≤ C) (hKc1 : K * c1 ≤ C)
    (hCfin : Real.exp (7 * (d : ℝ) / 2 * Real.log 3 + CI * (h + 1) * (h + 2)) * cC ^ 2 *
        (Cc * (CP + (5 / 2 : ℝ) * (CH * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h)) * Section6ExcessDecay.fractionalHolderConst d *
            Real.sqrt (1 / 4) +
          Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 8))) ≤ C) :
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
      M.delta ≤ C⁻¹ →
      ∀ (alpha : ℝ),
        alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * Real.sqrt (abs (Real.log M.delta))) →
        let alphaTight : ℝ := 1 - (1 - alpha) / K
        ∀ (L m n : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
          (om : BilateralField d) (I P : Finset (Fin d)), m ≤ L → n ≤ m →
          (n : ℤ) ≤ (m : ℤ) - It.prefixLen z alphaTight m om →
          ∀ foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR),
            ((foldedCoef.val : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
              fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val (coordinateFold z I P x)) →
          ∀ (g : SpatialCoordinates d → Fin d → ℝ)
            (hgrad : HilbertGradient (centeredCube z ((3 : ℝ) ^ m) hR))
            (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)),
            SubdiffusiveProcess.CoarseGrainingVocab.MemHolder
                (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))
                (1 / 2) g →
            (∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
              =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR :
                Set (SpatialCoordinates d))] fun x => g x i) →
            (∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR),
              sobolevCoefficientForm foldedCoef
                  (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))
                  (φ : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)) =
                -inner ℝ hgrad
                  (subspaceGradient
                    (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)) φ)) →
            normalizedEnergyNorm foldedCoef
                (centeredCube z ((3 : ℝ) ^ n) (by positivity)).isOpen.measurableSet
                (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) ≤
              C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - n)) *
                (normalizedEnergyNorm foldedCoef
                    (centeredCube z ((3 : ℝ) ^ m) hR).isOpen.measurableSet
                    (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) +
                  Real.sqrt (It.ref L (m - 2) z om)⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) *
                    halfHolderSeminorm
                      (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g) := by
  intro M Sreg It hdel alpha halpha aT L m n z hR om I P hmL hnm hpre foldedCoef hfold g hgrad
    u hgH hg hweak
  obtain ⟨hCeq, hC1eq, hC2eq⟩ := hconst M Sreg It
  have hdel0 : 0 < M.delta := M.shellPrefix.delta_pos
  have h18 : c1 * c2 ^ (-8 : ℝ) ≤ 1 := by rw [← hC1eq, ← hC2eq]; exact It.C1_C2_le_one
  obtain ⟨haT, hdelC, h64, hs0eps, hepseta, heps0, hlam0, hlamhalf, hbase, hlameq⟩ :=
    aux_prop_folded_iteration_parameters (delta := M.delta) (alpha := alpha) (K := K) (C := C)
      (cC := cC) (c1 := c1) (c2 := c2) (eta := eta) hdel0 hdel hK1 hC46 hcC hKcC hKc2 hKc1
      hc1 hc12 h18 heta0 hKeta halpha
  have hαT : aT ∈ It.alphaRange := by rw [It.alphaRange_eq, hCeq]; exact haT
  have hdelIt : M.delta ≤ It.C⁻¹ := by rw [hCeq]; exact hdelC
  have h64It : 64 * M.delta ^ 2 ≤ It.s0 := by rw [It.s0_eq]; exact h64
  have hsIt : It.s0⁻¹ * M.delta ^ 2 ≤ It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ) := by
    rw [It.s0_eq, hC2eq]; exact hs0eps
  have hepseta' : It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ) ≤ eta := by rw [hC2eq]; exact hepseta
  have hepsIt1 : It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ) ≤ 1 := hepseta'.trans heta1
  have hlamhalf' : It.C1⁻¹ * (1 - aT) ≤ 1 / 2 := by rw [hC1eq]; exact hlamhalf
  have hbase' : M.delta ^ 2 + (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) ^ 8 ≤
      2 * (It.C1⁻¹ * (1 - aT)) := by rw [hC2eq, hC1eq]; exact hbase
  have hlam0' : 0 ≤ It.C1⁻¹ * (1 - aT) := by rw [hC1eq]; exact hlam0
  have heps0' : 0 ≤ It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ) := by rw [hC2eq]; exact heps0
  have hlameq' : It.C1⁻¹ * (1 - aT) = (1 - alpha) / (K * c1) := by rw [hC1eq]; exact hlameq
  obtain ⟨hscore, hcount⟩ := It.good_scale_sums z aT hαT hdelIt (It.C1⁻¹ * (1 - aT))
    (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) rfl rfl n m om hpre
  have hpl := It.prefix_lower z aT m om
  rw [It.k_eq] at hpl
  have h26 : n + 26 ≤ m := by omega
  have hcount' : ((@Finset.filter ℕ
      (fun j => ¬ It.good j z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om)
      (Classical.decPred _) (Finset.Icc n m)).card : ℝ) <
      1 + It.C1⁻¹ * (1 - aT) * ((m : ℝ) - n) := by
    convert hcount using 3
    ext j
    simp
  obtain ⟨k, k', hnk, hkk', hk'm, hgk, hgk', hdk, hdk'⟩ :=
    aux_prop_folded_iteration_good_pair
      (fun j => It.good j z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om) n m h26
      (It.C1⁻¹ * (1 - aT)) hlamhalf' hcount'
  obtain ⟨a', -, ha'pos, ha'm, ⟨data⟩⟩ :=
    aux_prop_folded_iteration_folded_representative d Sreg L m z hR om I P foldedCoef hfold
  obtain ⟨u', -, hu'2, hu'w⟩ :=
    aux_prop_folded_iteration_weak_transfer m z hR foldedCoef a' ha'm g hgrad u hg hweak
  -- per-scale error at good scales
  have hsc : ∀ j : ℕ, j + 2 ≤ m → It.good (j + 2) z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om →
      paperHomogenizationError (Homogenization.originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2)
          (1 / 32) Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily (It.ref L j z om) ≤
        ENNReal.ofReal (Cg * min (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ))
          (M.delta ^ 2 + (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) ^ 8 +
            It.score (j + 2) z It.s0 om)) := by
    intro j hjm hgj
    exact hGSE E M Sreg It aT hαT hdelIt h64It hsIt hepsIt1 L m z hR om I P foldedCoef hfold j
      (by omega) hjm hgj a' (ae_restrict_of_ae_restrict_of_subset
        (aux_prop_folded_iteration_originCube_subset (by omega)) ha'm) data
  have hsc_eta : ∀ j : ℕ, j + 2 ≤ m →
      It.good (j + 2) z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om →
      paperHomogenizationError (Homogenization.originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2)
          (1 / 32) Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily (It.ref L j z om) ≤ ENNReal.ofReal (Cg * eta) :=
    fun j hjm hgj => (hsc j hjm hgj).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hepseta') hCg.le))
  have hsc_one : ∀ j : ℕ, j + 2 ≤ m →
      It.good (j + 2) z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om →
      paperHomogenizationError (Homogenization.originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2)
          (1 / 32) Homogenization.Book.Ch02.MultiscaleExponent.infinity
          (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
          data.toTriadicCoeffFamily (It.ref L j z om) ≤ ENNReal.ofReal Cg :=
    fun j hjm hgj => (hsc_eta j hjm hgj).trans (ENNReal.ofReal_le_ofReal
      (mul_le_of_le_one_right hCg.le heta1))
  -- the iteration's bad set
  obtain ⟨bad, hbaddef⟩ : ∃ bad : Finset ℤ, bad = ((Finset.Icc (k + 2) (k' + 2)).filter
      (fun j => j < h ∨ ¬ It.good (j + 2) z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om)).image
      (fun j : ℕ => (j : ℤ)) := ⟨_, rfl⟩
  have hbadsub : bad ⊆ Finset.Icc ((k + 2 : ℕ) : ℤ) ((k' + 2 : ℕ) : ℤ) := by
    intro j hj
    rw [hbaddef] at hj
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hj
    obtain ⟨i, ⟨⟨h1, h2⟩, _⟩, rfl⟩ := hj
    simp only [Finset.mem_Icc]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hnotbad : ∀ j : ℕ, k + 2 ≤ j → j ≤ k' + 2 → (j : ℤ) ∉ bad →
      h ≤ j ∧ It.good (j + 2) z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om := by
    intro j h1 h2 hj
    by_contra hcon
    apply hj
    rw [hbaddef]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨j, ⟨⟨h1, h2⟩, ?_⟩, rfl⟩
    by_contra hc2
    push_neg at hc2
    exact hcon hc2
  have hbadcard : (bad.card : ℝ) ≤ h + (@Finset.filter ℕ
      (fun j => ¬ It.good j z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om)
      (Classical.decPred _) (Finset.Icc n m)).card := by
    have h1 := aux_prop_folded_iteration_bad_card
      (fun j => It.good j z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om) n m k k' h hnk hk'm
    have h2 : bad.card ≤ (@Finset.filter ℕ
        (fun j => j < h ∨ ¬ It.good (j + 2) z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om)
        (Classical.decPred _) (Finset.Icc (k + 2) (k' + 2))).card := by
      rw [hbaddef]
      refine Finset.card_image_le.trans (le_of_eq ?_)
      congr 1
      ext j
      simp
    exact_mod_cast h2.trans h1
  -- reference ratios
  have hR0 : 0 < It.ref L (m - 2) z om := It.ref_pos L (m - 2) z om
  have hrat : ∀ j : ℕ, n ≤ j → j + 5 ≤ m →
      (It.C * Real.exp (It.C * (It.C1⁻¹ * (1 - aT)) * ((m : ℝ) - n)))⁻¹ *
          It.ref L (m - 2) z om ≤ It.ref L j z om ∧
        It.ref L j z om ≤ It.C * Real.exp (It.C * (It.C1⁻¹ * (1 - aT)) * ((m : ℝ) - n)) *
          It.ref L (m - 2) z om ∧
        (It.ref L j z om)⁻¹ ≤ It.C * Real.exp (It.C * (It.C1⁻¹ * (1 - aT)) * ((m : ℝ) - n)) *
          (It.ref L (m - 2) z om)⁻¹ := fun j hnj hj5 =>
    aux_prop_folded_iteration_ratio It.C_pos hR0
      (It.ref_ratio L z aT hαT hdelIt _ rfl n m j om hpre hmL hnj hj5)
  -- the translated chain
  have hW := hchain h hh hth eta heta0.le heta1 hthr m k k' hkk' hk'm z hR g hgH a' ha'pos data
    u' hu'w (fun j => It.ref L j z om) (fun j => It.ref_pos L j z om)
    (It.C * Real.exp (It.C * (It.C1⁻¹ * (1 - aT)) * ((m : ℝ) - n)) * (It.ref L (m - 2) z om)⁻¹)
    (fun j h1 h2 => (hrat j (by omega) (by omega)).2.2) bad hbadsub
    (fun j h1 h2 hj => ⟨(hnotbad j h1 h2 hj).1,
      hsc_eta j (by omega) (hnotbad j h1 h2 hj).2⟩)
    (hsc_one k (by omega) hgk) (hsc_one k' (by omega) hgk')
  dsimp only at hW
  -- energies on the root chart
  have hRn : (0 : ℝ) < 3 ^ n := by positivity
  have hRk : (0 : ℝ) < 3 ^ k := by positivity
  have hRt : (0 : ℝ) < 3 ^ (k' + 2) := by positivity
  have hsubc : ∀ (a b : ℕ), a ≤ b → ∀ (ha : (0 : ℝ) < 3 ^ a) (hb : (0 : ℝ) < 3 ^ b),
      (centeredCube z ((3 : ℝ) ^ a) ha : Set (SpatialCoordinates d)) ⊆
        centeredCube z ((3 : ℝ) ^ b) hb := by
    intro a b hab ha hb
    change Metric.ball z ((3 : ℝ) ^ a / 2) ⊆ Metric.ball z ((3 : ℝ) ^ b / 2)
    refine Metric.ball_subset_ball ?_
    have : (3 : ℝ) ^ a ≤ (3 : ℝ) ^ b := pow_le_pow_right₀ (by norm_num) hab
    linarith only [this]
  have hEk := aux_prop_folded_iteration_energy_bridge m k (by omega) z hR foldedCoef a'
    (fun y => (ha'pos y).le) ha'm (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)) u' hu'2 hRk
  have hEt := aux_prop_folded_iteration_energy_bridge m (k' + 2) (by omega) z hR foldedCoef a'
    (fun y => (ha'pos y).le) ha'm (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)) u' hu'2 hRt
  have hcast : ((k' + 2 : ℕ) : ℤ) = (k' : ℤ) + 2 := by push_cast; ring
  rw [hcast] at hEt
  have hEn := normalizedEnergyNorm_le_sqrt_volume_ratio foldedCoef
    (centeredCube z ((3 : ℝ) ^ n) hRn).isOpen.measurableSet
    (centeredCube z ((3 : ℝ) ^ k) hRk).isOpen.measurableSet (hsubc n k hnk hRn hRk)
    (by rw [centeredCube_volume_real]; positivity) (by rw [centeredCube_volume_real]; positivity)
    (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)))
  rw [centeredCube_volume_real, centeredCube_volume_real, hEk] at hEn
  have hEtm := normalizedEnergyNorm_le_sqrt_volume_ratio foldedCoef
    (centeredCube z ((3 : ℝ) ^ (k' + 2)) hRt).isOpen.measurableSet
    (centeredCube z ((3 : ℝ) ^ m) hR).isOpen.measurableSet (hsubc (k' + 2) m (by omega) hRt hR)
    (by rw [centeredCube_volume_real]; positivity) (by rw [centeredCube_volume_real]; positivity)
    (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)))
  rw [centeredCube_volume_real, centeredCube_volume_real, hEt] at hEtm
  -- counting in reals
  obtain ⟨nb, hnb⟩ : ∃ nb : ℕ, nb = (@Finset.filter ℕ
      (fun j => ¬ It.good j z (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) It.s0 om)
      (Classical.decPred _) (Finset.Icc n m)).card := ⟨_, rfl⟩
  rw [← hnb] at hdk hdk' hcount' hbadcard
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast (by omega : n ≤ m)
  have hN0 : (0 : ℝ) ≤ (m : ℝ) - n := by linarith only [hnm']
  have hLam0 : 0 ≤ It.C1⁻¹ * (1 - aT) * ((m : ℝ) - n) := mul_nonneg hlam0' hN0
  have hkn : (k : ℝ) - n ≤ 1 + It.C1⁻¹ * (1 - aT) * ((m : ℝ) - n) := by
    have h1 : ((k - n : ℕ) : ℝ) ≤ (nb : ℝ) := by exact_mod_cast hdk
    rw [Nat.cast_sub hnk] at h1
    linarith only [h1, hcount']
  have hmt : (m : ℝ) - ((k' + 2 : ℕ) : ℝ) ≤ 6 + It.C1⁻¹ * (1 - aT) * ((m : ℝ) - n) := by
    have h1 : ((m - 7 - k' : ℕ) : ℝ) ≤ (nb : ℝ) := by exact_mod_cast hdk'
    have h2 : ((m - 7 - k' : ℕ) : ℝ) = (m : ℝ) - 7 - k' := by
      rw [Nat.cast_sub (by omega : k' ≤ m - 7), Nat.cast_sub (by omega : 7 ≤ m)]
      push_cast
      ring
    rw [h2] at h1
    push_cast
    linarith only [h1, hcount']
  have hPkb := aux_prop_folded_iteration_vol_factor d n k _ hkn
  have hPtb := aux_prop_folded_iteration_vol_factor d (k' + 2) m _ hmt
  have hPt1 : 1 ≤ Real.sqrt (((3 : ℝ) ^ m) ^ d / ((3 : ℝ) ^ (k' + 2)) ^ d) := by
    rw [Real.one_le_sqrt, one_le_div (by positivity)]
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega)) d
  -- the error sum and the iteration exponent
  have hcE0 : 0 ≤ CH * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg hCH.le (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _)
  obtain ⟨heA1, heAb⟩ := aux_prop_folded_iteration_eA_bound (k + 2) (k' + 2) n m h (by omega)
    (by omega) (by omega) bad
    (fun j => (paperHomogenizationError (Homogenization.originCube d ((j : ℤ) + 2)) ((j : ℤ) + 2)
      (1 / 4 / 8) Homogenization.Book.Ch02.MultiscaleExponent.infinity
      (Homogenization.Book.Ch02.MultiscaleExponent.finite 2)
      data.toTriadicCoeffFamily (It.ref L j z om)).toReal)
    (fun i => It.score i z It.s0 om)
    (CH * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) * (1 / 4 : ℝ) ^ (-3 / 2 : ℝ)) Cg CI
    (M.delta ^ 2 + (It.C2⁻¹ * (1 - aT) ^ (1 / 2 : ℝ)) ^ 8) (It.C1⁻¹ * (1 - aT)) nb
    hcE0 hCg.le hCI.le (by positivity) (fun i => It.score_nonneg i z It.s0 om)
    (fun j => ENNReal.toReal_nonneg)
    (fun j h1 h2 hj => by
      have hgj := (hnotbad j h1 h2 hj).2
      have h3 := hsc j (by omega) hgj
      rw [show (1 / 4 / 8 : ℝ) = 1 / 32 by norm_num]
      exact ENNReal.toReal_le_of_le_ofReal
        (mul_nonneg hCg.le (add_nonneg (by positivity) (It.score_nonneg _ _ _ _)))
        (h3.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (min_le_right _ _) hCg.le))))
    hbase' hscore hbadcard hcount'
  -- final collapse
  have hrk := hrat k hnk (by omega)
  have hrk' := hrat k' (by omega) (by omega)
  have hw : 0 ≤ 1 - alpha := by
    have : 0 ≤ C * M.delta * Real.sqrt |Real.log M.delta| :=
      mul_nonneg (mul_nonneg (by linarith only [hC46]) hdel0.le) (Real.sqrt_nonneg _)
    linarith only [halpha.2, this]
  have hT0 : 0 ≤ (3 : ℝ) ^ ((m : ℝ) / 2) *
      halfHolderSeminorm (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g :=
    mul_nonneg (by positivity) (aux_prop_folded_iteration_halfHolder_nonneg _ _)
  have hfin := aux_prop_folded_iteration_final_arith (dd := (d : ℝ)) (c1 := c1) (C := C)
    (K := K) (w := 1 - alpha) (N := (m : ℝ) - n) (cC := cC)
    (Lam := It.C1⁻¹ * (1 - aT) * ((m : ℝ) - n))
    hR0 hcC (by exact heA1) hPt1 (Real.sqrt_nonneg _)
    hCc.le hCP.le
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hCH.le
      (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg (by norm_num) _)))
      (Section6ExcessDecay.fractionalHolderConst_nonneg d)) (Real.sqrt_nonneg _))
    (mul_nonneg (Section6ExcessDecay.fractionalHolderConst_nonneg d) (Real.sqrt_nonneg _))
    hT0 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hrk.1 hrk.2.1 hrk'.1 hEn hW hEtm
    (Nat.cast_nonneg d) hc1 hKGam (lt_of_lt_of_le one_pos hK1) (by positivity) hw hN0
    (by rw [hlameq']; ring) hLam0 hPkb hPtb
    (by exact heAb)
    (by rw [hCeq, mul_assoc cC]) hCfin
  exact aux_prop_folded_iteration_final_shape hfin



end FoldedAllRooted

theorem aux_rem_resolved_meshes_folded_iteration_all :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d)
    (Poinc : in_poincare d hd E)
    (Ext : in_extension d hd E)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩),
  ∃ C K : ℝ, 0 < C ∧
    1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ K ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
      M.delta ≤ C⁻¹ →
      ∀ (alpha : ℝ),
        alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * Real.sqrt (abs (Real.log M.delta))) →
        let alphaTight : ℝ := 1 - (1 - alpha) / K
        ∀ (L m n : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
          (om : BilateralField d) (I P : Finset (Fin d)), m ≤ L → n ≤ m →
          (n : ℤ) ≤ (m : ℤ) - It.prefixLen z alphaTight m om →
          ∀ foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR),
            ((foldedCoef.val : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
              fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val (coordinateFold z I P x)) →
          ∀ (g : SpatialCoordinates d → Fin d → ℝ)
            (hgrad : HilbertGradient (centeredCube z ((3 : ℝ) ^ m) hR))
            (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)),
            SubdiffusiveProcess.CoarseGrainingVocab.MemHolder
                (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))
                (1 / 2) g →
            (∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
              =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR :
                Set (SpatialCoordinates d))] fun x => g x i) →
            (∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR),
              sobolevCoefficientForm foldedCoef
                  (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))
                  (φ : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)) =
                -inner ℝ hgrad
                  (subspaceGradient
                    (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)) φ)) →
            normalizedEnergyNorm foldedCoef
                (centeredCube z ((3 : ℝ) ^ n) (by positivity)).isOpen.measurableSet
                (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) ≤
              C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - n)) *
                (normalizedEnergyNorm foldedCoef
                    (centeredCube z ((3 : ℝ) ^ m) hR).isOpen.measurableSet
                    (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) +
                  Real.sqrt (It.ref L (m - 2) z om)⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) *
                    halfHolderSeminorm
                      (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g) := by
  intro d hd _ _ E Poinc Ext D
  obtain ⟨Cg, hCg, hGSE⟩ := aux_rem_resolved_meshes_gse_all_min d hd
  obtain ⟨CH, CI, Cc, CP, hCH, hCI, hCc, hCP, hchain⟩ :=
    aux_prop_folded_iteration_translated_chain d hd D Cg hCg
  obtain ⟨cC, c1, c2, hcC, hc1, hc12, hconst⟩ := aux_prop_folded_iteration_carrier_constants d hd
  obtain ⟨h, hh, hth, hstep⟩ := aux_prop_folded_iteration_step_choice CH
  obtain ⟨eta, heta0, heta1, hthr⟩ := aux_prop_folded_iteration_eta_exists d CH h hCH hstep
  obtain ⟨K, C, hK1, hKGam, hKeta, hKd2, hC46, hKcC, hKc2, hKc1, hCfin⟩ :=
    aux_prop_folded_iteration_choose_KC
      ((d : ℝ) * Real.log 3 + (CI * (h + 1) + 3 * (CH * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h) *
        (1 / 4 : ℝ) ^ (-3 / 2 : ℝ) * Cg) * CI) + 2 * cC)
      (1 / (2 * eta ^ 2))
      (1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1))
      cC c1 c2
      (Real.exp (7 * (d : ℝ) / 2 * Real.log 3 + CI * (h + 1) * (h + 2)) * cC ^ 2 *
        (Cc * (CP + (5 / 2 : ℝ) * (CH * (1 / 4 : ℝ) ^ (-15 / 2 : ℝ) *
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * h)) * SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.fractionalHolderConst d *
            Real.sqrt (1 / 4) +
          SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.fractionalHolderConst d * Real.sqrt (1 / 8))))
  exact ⟨C, K, lt_of_lt_of_le (by norm_num) hC46, hKd2,
    aux_rem_resolved_meshes_rooted_all d E Cg CH CI Cc CP cC c1 c2 eta K C h hCg hCH hCI hCc hCP
      hcC hc1 hc12 hGSE hchain (hconst E) hh hth heta0 heta1 hthr hK1 hKGam hKeta hC46 hKcC
      hKc2 hKc1 hCfin⟩

/-- The all-face-set body (including `I = ∅`) at constants `(C, K)`, as a predicate of the only two
projections of the iteration package it reads (`prefixLen`, `ref`). -/
def aux_rem_resolved_meshes_folded_core_all (d : ℕ)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (pl : SpatialCoordinates d → ℝ → ℕ → BilateralField d → ℕ)
    (rf : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ) (C K : ℝ) : Prop :=
      M.delta ≤ C⁻¹ →
      ∀ (alpha : ℝ),
        alpha ∈ Set.Icc (1 / 2 : ℝ)
          (1 - C * M.delta * Real.sqrt (abs (Real.log M.delta))) →
        let alphaTight : ℝ := 1 - (1 - alpha) / K
        ∀ (L m n : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ m)
          (om : BilateralField d) (I P : Finset (Fin d)), m ≤ L → n ≤ m →
          (n : ℤ) ≤ (m : ℤ) - pl z alphaTight m om →
          ∀ foldedCoef : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ m) hR),
            ((foldedCoef.val : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))]
              fun x => (Sreg.cutoffOn L om z ((3 : ℝ) ^ m) hR).val (coordinateFold z I P x)) →
          ∀ (g : SpatialCoordinates d → Fin d → ℝ)
            (hgrad : HilbertGradient (centeredCube z ((3 : ℝ) ^ m) hR))
            (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)),
            SubdiffusiveProcess.CoarseGrainingVocab.MemHolder
                (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d))
                (1 / 2) g →
            (∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
              =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ m) hR :
                Set (SpatialCoordinates d))] fun x => g x i) →
            (∀ φ : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR),
              sobolevCoefficientForm foldedCoef
                  (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))
                  (φ : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR)) =
                -inner ℝ hgrad
                  (subspaceGradient
                    (killedSobolevGraph (centeredCube z ((3 : ℝ) ^ m) hR)) φ)) →
            normalizedEnergyNorm foldedCoef
                (centeredCube z ((3 : ℝ) ^ n) (by positivity)).isOpen.measurableSet
                (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) ≤
              C * (3 : ℝ) ^ ((1 - alpha) * ((m : ℝ) - n)) *
                (normalizedEnergyNorm foldedCoef
                    (centeredCube z ((3 : ℝ) ^ m) hR).isOpen.measurableSet
                    (sobolevGradient (u : SobolevData (centeredCube z ((3 : ℝ) ^ m) hR))) +
                  Real.sqrt (rf L (m - 2) z om)⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) *
                    halfHolderSeminorm
                      (centeredCube z ((3 : ℝ) ^ m) hR : Set (SpatialCoordinates d)) g)



theorem aux_rem_resolved_meshes_folded_uniform_all (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ Cf Kf : ℝ, 0 < Cf ∧
      1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ Kf ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (E : in_J d)
        (_ : in_poincare d hd E) (_ : in_extension d hd E)
        (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (_ : @lane4_deterministic_good_scale_input d
          ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩),
        aux_rem_resolved_meshes_folded_core_all d M Sreg It.prefixLen It.ref Cf Kf := by
  obtain ⟨⟨C, K⟩, ⟨hC, hK⟩, hU⟩ :=
    aux_rem_resolved_meshes_uniformize d hd (ι := ℝ × ℝ)
      (fun p => 0 < p.1 ∧
        1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ p.2)
      ⟨(1, 1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1)), one_pos, le_rfl⟩
      (fun M Sreg pl rf p => aux_rem_resolved_meshes_folded_core_all d M Sreg pl rf p.1 p.2)
      (fun E P X D => by
        obtain ⟨C, K, hC, hK, h⟩ := aux_rem_resolved_meshes_folded_iteration_all d hd E P X D
        exact ⟨(C, K), ⟨hC, hK⟩, fun M Sreg It => h M Sreg It⟩)
  exact ⟨C, K, hC, hK, fun M E P X Sreg It D => hU E P X D M Sreg It⟩





theorem aux_rem_resolved_meshes_dilate_algebra {d : ℕ} (cF l X Y : ℝ) (hcF : cF ≠ 0) (hl : l ≠ 0)
    (heq : cF * X = l⁻¹ * Y) : l ^ d * X = l ^ d * ((cF * l)⁻¹ * Y) := by
  have hX : X = cF⁻¹ * (l⁻¹ * Y) := by
    rw [← heq]; field_simp
  rw [hX, mul_inv]
  ring

open scoped Pointwise in
/-- **Neumann dilation.**  A weak Neumann solution on `Ω` for `a = c_F · A(λ ·)` becomes, after
the dilation `v = λ u(·/λ)`, a weak Neumann solution on `λΩ` for `A` with source
`(c_F λ)^{-1} f(·/λ)`. -/
theorem aux_rem_resolved_meshes_neumann_dilate {d : ℕ} {Ω Ωl : Opens (SpatialCoordinates d)}
    {l : ℝ} (hl : 0 < l) (hset : (Ωl : Set (SpatialCoordinates d)) = l • (Ω : Set (SpatialCoordinates d)))
    (a : PositiveCoefficient Ω) (A : PositiveCoefficient Ωl) (cF : ℝ) (hcF : 0 < cF)
    (hA : ∀ᵐ y ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val y = cF * A.val (l • y))
    (f : SpatialCoordinates d → ℝ) (u : weakSobolevGraph Ω)
    (hu : ∀ ψ : weakSobolevGraph Ω, sobolevCoefficientForm a (u : SobolevData Ω) (ψ : SobolevData Ω) =
      ∫ x in (Ω : Set (SpatialCoordinates d)), f x * (ψ : SobolevData Ω).1 x) :
    ∃ v : weakSobolevGraph Ωl,
      (∀ᵐ x ∂volume.restrict (Ωl : Set (SpatialCoordinates d)),
        (v : SobolevData Ωl).1 x = l * (u : SobolevData Ω).1 (l⁻¹ • x)) ∧
      (∀ i : Fin d, ∀ᵐ x ∂volume.restrict (Ωl : Set (SpatialCoordinates d)),
        (v : SobolevData Ωl).2 i x = (u : SobolevData Ω).2 i (l⁻¹ • x)) ∧
      ∀ ψ : weakSobolevGraph Ωl,
        sobolevCoefficientForm A (v : SobolevData Ωl) (ψ : SobolevData Ωl) =
          ∫ x in (Ωl : Set (SpatialCoordinates d)),
            ((cF * l)⁻¹ * f (l⁻¹ • x)) * (ψ : SobolevData Ωl).1 x := by
  obtain ⟨u', hu'1, hu'2⟩ := exists_nativeH1Function_of_weakSobolevGraph u
  obtain ⟨v, hv1, hv2⟩ := SubdiffusiveProcess.Lane4.exists_weakSobolevGraph_of_nativeH1
    (Om := Ωl) (u'.dilateSet hl hset)
  have hll : ∀ y : SpatialCoordinates d, l⁻¹ • (l • y) = y := fun y => by
    rw [smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
  refine ⟨v, ?_, ?_, ?_⟩
  · filter_upwards [hv1] with x hx
    rw [hx, Homogenization.H1Function.dilateSet_toFun]
    exact congrArg (fun t => l * t) (congrFun hu'1 _)
  · intro i
    filter_upwards [hv2 i] with x hx
    rw [hx, Homogenization.H1Function.dilateSet_grad]
    exact congrFun (congrFun hu'2 _) i
  · intro ψ
    obtain ⟨ψ', hψ'1, hψ'2⟩ := exists_nativeH1Function_of_weakSobolevGraph ψ
    obtain ⟨ψ0, h01, h02⟩ := SubdiffusiveProcess.Lane4.exists_weakSobolevGraph_of_nativeH1
      (Om := Ω) (ψ'.undilateSet hl hset)
    have heq := hu ψ0
    have hΩm : MeasurableSet (Ω : Set (SpatialCoordinates d)) := Ω.isOpen.measurableSet
    have hld : (0 : ℝ) < l ^ d := pow_pos hl d
    have key : ∀ F : SpatialCoordinates d → ℝ, (∫ x in (Ωl : Set (SpatialCoordinates d)), F x) =
        l ^ d * ∫ y in (Ω : Set (SpatialCoordinates d)), F (l • y) := fun F => by
      rw [hset]; exact aux_rem_resolved_meshes_setIntegral_smul _ hΩm hl F
    -- the left side of the dilated equation, pulled back to `Ω`
    have hL : sobolevCoefficientForm A (v : SobolevData Ωl) (ψ : SobolevData Ωl) =
        l ^ d * ∑ i : Fin d, ∫ y in (Ω : Set (SpatialCoordinates d)),
          A.val (l • y) * ((u : SobolevData Ω).2 i y * (ψ : SobolevData Ωl).2 i (l • y)) := by
      rw [sobolevCoefficientForm_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      calc (∫ x in (Ωl : Set (SpatialCoordinates d)),
            A.val x * ((v : SobolevData Ωl).2 i x * (ψ : SobolevData Ωl).2 i x))
          = ∫ x in (Ωl : Set (SpatialCoordinates d)),
            A.val x * ((u : SobolevData Ω).2 i (l⁻¹ • x) * (ψ : SobolevData Ωl).2 i x) := by
            apply integral_congr_ae
            filter_upwards [hv2 i] with x hx
            rw [hx, Homogenization.H1Function.dilateSet_grad]
            congr 2
            exact congrFun (congrFun hu'2 _) i
        _ = l ^ d * ∫ y in (Ω : Set (SpatialCoordinates d)),
            A.val (l • y) * ((u : SobolevData Ω).2 i y * (ψ : SobolevData Ωl).2 i (l • y)) := by
            rw [key]
            congr 1
            apply integral_congr_ae
            filter_upwards with y
            rw [hll]
    -- the left side of the original equation at the pulled-back test
    have hR : sobolevCoefficientForm a (u : SobolevData Ω) (ψ0 : SobolevData Ω) =
        cF * ∑ i : Fin d, ∫ y in (Ω : Set (SpatialCoordinates d)),
          A.val (l • y) * ((u : SobolevData Ω).2 i y * (ψ : SobolevData Ωl).2 i (l • y)) := by
      rw [sobolevCoefficientForm_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hA, h02 i] with y hy hy2
      rw [hy, hy2, Homogenization.H1Function.undilateSet_grad]
      have : ψ'.grad (l • y) i = (ψ : SobolevData Ωl).2 i (l • y) :=
        congrFun (congrFun hψ'2 _) i
      rw [this]
      ring
    -- the right sides
    have hS1 : (∫ x in (Ω : Set (SpatialCoordinates d)), f x * (ψ0 : SobolevData Ω).1 x) =
        l⁻¹ * ∫ y in (Ω : Set (SpatialCoordinates d)), f y * (ψ : SobolevData Ωl).1 (l • y) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [h01] with y hy
      rw [hy, Homogenization.H1Function.undilateSet_toFun]
      have : ψ'.toFun (l • y) = (ψ : SobolevData Ωl).1 (l • y) := congrFun hψ'1 _
      rw [this]
      ring
    have hS2 : (∫ x in (Ωl : Set (SpatialCoordinates d)),
          ((cF * l)⁻¹ * f (l⁻¹ • x)) * (ψ : SobolevData Ωl).1 x) =
        l ^ d * ((cF * l)⁻¹ *
          ∫ y in (Ω : Set (SpatialCoordinates d)), f y * (ψ : SobolevData Ωl).1 (l • y)) := by
      rw [key]
      congr 1
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      rw [hll]
      ring
    rw [hL, hS2]
    rw [hR, hS1] at heq
    exact aux_rem_resolved_meshes_dilate_algebra _ _ _ _ hcF.ne' hl.ne' heq


/-- Local energy on a subset of a subdomain only sees the restricted coefficient and gradient. -/
theorem aux_rem_resolved_meshes_localEnergy_restrict {d : ℕ} {V U : Opens (SpatialCoordinates d)}
    (hle : V ≤ U) (a : PositiveCoefficient U) (vf : SobolevData U)
    {B : Set (SpatialCoordinates d)} (hB : MeasurableSet B) (hBV : B ⊆ (V : Set (SpatialCoordinates d))) :
    localGradientEnergy (positiveCoefficientRestrict hle a) hB
        (sobolevGradient (sobolevDataRestrict hle vf)) =
      localGradientEnergy a hB (sobolevGradient vf) := by
  rw [localGradientEnergy_eq_integral, localGradientEnergy_eq_integral]
  apply Finset.sum_congr rfl
  intro i _
  have hBU : B ⊆ (U : Set (SpatialCoordinates d)) := hBV.trans hle
  rw [Measure.restrict_restrict hB, Measure.restrict_restrict hB, Set.inter_eq_left.mpr hBV,
    Set.inter_eq_left.mpr hBU]
  apply integral_congr_ae
  have h1 := ae_restrict_of_ae_restrict_of_subset hBV (positiveCoefficientRestrict_coeFn hle a)
  have h2 := ae_restrict_of_ae_restrict_of_subset hBV (domainLpRestrict_coeFn hle (vf.2 i))
  filter_upwards [h1, h2] with x hx1 hx2
  change (positiveCoefficientRestrict hle a).val x * ((domainLpRestrict hle (vf.2 i)) x) ^ 2 =
    a.val x * (vf.2 i x) ^ 2
  rw [hx1, hx2]

/-- **Fold and restrict.**  `lem_even` on the Neumann cube, restricted to a root cube inside the
folded cube: the folded coefficient, the killed-test equation with the folded source, and the
energy doubling identity on fold-symmetric subsets. -/
theorem aux_rem_resolved_meshes_fold_restrict {d : ℕ} (w : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (I P : Finset (Fin d)) (A : PositiveCoefficient (centeredCube w r hr))
    (F : SpatialCoordinates d → ℝ) (MF : ℝ) (hMF : 0 ≤ MF)
    (hFm : AEMeasurable F (volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube w r hr : Set (SpatialCoordinates d)), |F x| ≤ MF)
    (hF0 : (∫ x in (centeredCube w r hr : Set (SpatialCoordinates d)), F x) = 0)
    (v : weakSobolevGraph (centeredCube w r hr))
    (hv : ∀ ψ : weakSobolevGraph (centeredCube w r hr),
      sobolevCoefficientForm A (v : SobolevData (centeredCube w r hr))
          (ψ : SobolevData (centeredCube w r hr)) =
        ∫ x in (centeredCube w r hr : Set (SpatialCoordinates d)),
          F x * (ψ : SobolevData (centeredCube w r hr)).1 x)
    (z : SpatialCoordinates d) (ρ : ℝ) (hρ : 0 < ρ)
    (hsub : (centeredCube z ρ hρ : Set (SpatialCoordinates d)) ⊆ foldedCube w r hr I P) :
    ∃ (fc : PositiveCoefficient (centeredCube z ρ hρ))
      (ut : weakSobolevGraph (centeredCube z ρ hρ)),
      ((fc.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z ρ hρ : Set (SpatialCoordinates d))]
        fun x => A.val (coordinateFold (foldedCubeCenter w r I P) I P x)) ∧
      (∀ φ : killedSobolevGraph (centeredCube z ρ hρ),
        sobolevCoefficientForm fc (ut : SobolevData (centeredCube z ρ hρ))
            (φ : SobolevData (centeredCube z ρ hρ)) =
          ∫ x in (centeredCube z ρ hρ : Set (SpatialCoordinates d)),
            F (coordinateFold (foldedCubeCenter w r I P) I P x) *
              (φ : SobolevData (centeredCube z ρ hρ)).1 x) ∧
      (∀ (B : Set (SpatialCoordinates d)) (hB : MeasurableSet B),
        B ⊆ (centeredCube z ρ hρ : Set (SpatialCoordinates d)) →
        (∀ J : Finset (Fin d), J ⊆ I →
          coordinateReflection (foldedCubeCenter w r I P) J ⁻¹' B = B) →
        localGradientEnergy fc hB (sobolevGradient (ut : SobolevData (centeredCube z ρ hρ))) =
          2 ^ I.card *
            localGradientEnergy A (hB.inter (centeredCube w r hr).isOpen.measurableSet)
              (sobolevGradient (v : SobolevData (centeredCube w r hr)))) := by
  obtain ⟨af, vf, haf, -, hweq, hE⟩ := lem_even d w r hr I P A F MF hMF hFm hFb hF0 v hv
  have hle : centeredCube z ρ hρ ≤ foldedCube w r hr I P := hsub
  refine ⟨positiveCoefficientRestrict hle af,
    ⟨sobolevDataRestrict hle (vf : SobolevData (foldedCube w r hr I P)),
      sobolevDataRestrict_mem_weak hle vf.2⟩, ?_, ?_, ?_⟩
  · filter_upwards [positiveCoefficientRestrict_coeFn hle af,
      ae_restrict_of_ae_restrict_of_subset hsub haf] with x h1 h2
    rw [h1, h2]
  · intro φ
    have hψ := lane2_zeroExtensionSobolevData_mem_weak_of_killed hle φ.2
    have h := hweq ⟨_, hψ⟩
    have hab : ((af.val : SpatialCoordinates d → ℝ)) =ᵐ[volume.restrict
        (centeredCube z ρ hρ : Set (SpatialCoordinates d))]
        (positiveCoefficientRestrict hle af).val :=
      (positiveCoefficientRestrict_coeFn hle af).symm
    have hz := sobolevCoefficientForm_zeroExtension hle af (positiveCoefficientRestrict hle af) hab
      (φ : SobolevData (centeredCube z ρ hρ)) (vf : SobolevData (foldedCube w r hr I P))
    rw [sobolevCoefficientForm_symm, ← hz, sobolevCoefficientForm_symm]
    rw [h]
    exact integral_mul_zeroExtensionLp hle _ _
  · intro B hB hBC hsym
    rw [aux_rem_resolved_meshes_localEnergy_restrict hle af _ hB hBC]
    exact hE B hB hsym


theorem aux_rem_resolved_meshes_fold_center_congr {d : ℕ} (Z z : SpatialCoordinates d)
    (I P : Finset (Fin d)) (hZ : ∀ i ∈ I, Z i = z i) :
    coordinateFold Z I P = coordinateFold z I P := by
  funext x i
  by_cases hi : i ∈ I
  · simp only [coordinateFold, hi, if_true, hZ i hi]
  · simp only [coordinateFold, hi, if_false]

/-- **Coefficient identification.**  The folded coefficient read through the big cutoff cube is,
almost everywhere on the root cube, the root-cube cutoff coefficient composed with the fold:
both are pinned to the same layer formula, and the fold is quasi-measure-preserving. -/
theorem aux_rem_resolved_meshes_coef_ident {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M) (L : ℕ) (om : BilateralField d)
    (W : SpatialCoordinates d) (l : ℝ) (hl : 0 < l) (z : SpatialCoordinates d) (ρ : ℝ)
    (hρ : 0 < ρ) (I P : Finset (Fin d)) (Z : SpatialCoordinates d) (hZ : ∀ i ∈ I, Z i = z i)
    (hmaps : ∀ x ∈ (centeredCube z ρ hρ : Set (SpatialCoordinates d)), (∀ i : Fin d, x i ≠ z i) →
      coordinateFold z I P x ∈ (centeredCube W l hl : Set (SpatialCoordinates d)))
    (fc : PositiveCoefficient (centeredCube z ρ hρ))
    (hfc : (fc.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z ρ hρ : Set (SpatialCoordinates d))]
      fun x => (Sreg.cutoffOn L om W l hl).val (coordinateFold Z I P x)) :
    (fc.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z ρ hρ : Set (SpatialCoordinates d))]
      fun x => (Sreg.cutoffOn L om z ρ hρ).val (coordinateFold z I P x) := by
  have hqmp := aux_lem_repair_err_fold_carrier_bridge_fold_qmp z I P
  have h1 := (ae_restrict_iff' (centeredCube W l hl).isOpen.measurableSet).mp
    (Sreg.cutoffOn_eq L om W l hl)
  have h2 := (ae_restrict_iff' (centeredCube z ρ hρ).isOpen.measurableSet).mp
    (Sreg.cutoffOn_eq L om z ρ hρ)
  have h1' := hqmp.ae h1
  have h2' := hqmp.ae h2
  have hplane : ∀ᵐ x ∂(volume : Measure (SpatialCoordinates d)), ∀ i : Fin d, x i ≠ z i := by
    rw [ae_all_iff]
    intro i
    exact Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i (z i)
  rw [aux_rem_resolved_meshes_fold_center_congr Z z I P hZ] at hfc
  filter_upwards [hfc, ae_restrict_of_ae h1', ae_restrict_of_ae h2', ae_restrict_of_ae hplane,
    ae_restrict_mem (centeredCube z ρ hρ).isOpen.measurableSet] with x hx h1x h2x hpx hxC
  have hfold_mem : coordinateFold z I P x ∈ (centeredCube z ρ hρ : Set (SpatialCoordinates d)) := by
    change dist (coordinateFold z I P x) z < ρ / 2
    rw [coordinateFold_dist_center]
    exact hxC
  rw [hx, h1x (hmaps x hxC hpx), h2x hfold_mem]

open scoped Pointwise in
/-- **Energy under the dilation.**  The local energy of the dilated solution on `l • S` is
`l^d c_F^{-1}` times the original local energy on `S`. -/
theorem aux_rem_resolved_meshes_energy_dilate {d : ℕ} {Ω Ωl : Opens (SpatialCoordinates d)}
    {l : ℝ} (hl : 0 < l) (hset : (Ωl : Set (SpatialCoordinates d)) = l • (Ω : Set (SpatialCoordinates d)))
    (a : PositiveCoefficient Ω) (A : PositiveCoefficient Ωl) (cF : ℝ) (hcF : 0 < cF)
    (hA : ∀ᵐ y ∂volume.restrict (Ω : Set (SpatialCoordinates d)), a.val y = cF * A.val (l • y))
    (u : weakSobolevGraph Ω) (v : weakSobolevGraph Ωl)
    (hv2 : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict (Ωl : Set (SpatialCoordinates d)),
      (v : SobolevData Ωl).2 i x = (u : SobolevData Ω).2 i (l⁻¹ • x))
    (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S)
    (hB : MeasurableSet ((l • S) ∩ (Ωl : Set (SpatialCoordinates d)))) :
    localGradientEnergy A hB (sobolevGradient (v : SobolevData Ωl)) =
      l ^ d * cF⁻¹ * localGradientEnergy a hS (sobolevGradient (u : SobolevData Ω)) := by
  rw [localGradientEnergy_eq_integral, localGradientEnergy_eq_integral, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hll : ∀ y : SpatialCoordinates d, l⁻¹ • (l • y) = y := fun y => by
    rw [smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
  have hΩm : MeasurableSet (Ω : Set (SpatialCoordinates d)) := Ω.isOpen.measurableSet
  have hinter : (l • S) ∩ (Ωl : Set (SpatialCoordinates d)) = l • (S ∩ (Ω : Set (SpatialCoordinates d))) := by
    rw [hset, Set.smul_set_inter₀ hl.ne']
  rw [Measure.restrict_restrict hB, Measure.restrict_restrict hS]
  rw [Set.inter_assoc, Set.inter_self]
  calc (∫ x in (l • S) ∩ (Ωl : Set (SpatialCoordinates d)),
        A.val x * ((sobolevGradient (v : SobolevData Ωl)) i x) ^ 2)
      = ∫ x in (l • S) ∩ (Ωl : Set (SpatialCoordinates d)),
          A.val x * ((u : SobolevData Ω).2 i (l⁻¹ • x)) ^ 2 := by
        apply integral_congr_ae
        have := ae_restrict_of_ae_restrict_of_subset
          (Set.inter_subset_right (s := l • S) (t := (Ωl : Set (SpatialCoordinates d)))) (hv2 i)
        filter_upwards [this] with x hx
        change A.val x * ((v : SobolevData Ωl).2 i x) ^ 2 = _
        rw [hx]
    _ = l ^ d * ∫ y in S ∩ (Ω : Set (SpatialCoordinates d)),
          A.val (l • y) * ((u : SobolevData Ω).2 i y) ^ 2 := by
        rw [hinter, aux_rem_resolved_meshes_setIntegral_smul _ (hS.inter hΩm) hl]
        congr 1
        apply integral_congr_ae
        filter_upwards with y
        rw [hll]
    _ = l ^ d * cF⁻¹ * ∫ y in S ∩ (Ω : Set (SpatialCoordinates d)),
          a.val y * ((sobolevGradient (u : SobolevData Ω)) i y) ^ 2 := by
        rw [mul_assoc]
        congr 1
        rw [← integral_const_mul]
        apply integral_congr_ae
        have := ae_restrict_of_ae_restrict_of_subset
          (Set.inter_subset_right (s := S) (t := (Ω : Set (SpatialCoordinates d)))) hA
        filter_upwards [this] with y hy
        change A.val (l • y) * ((u : SobolevData Ω).2 i y) ^ 2 =
          cF⁻¹ * (a.val y * ((u : SobolevData Ω).2 i y) ^ 2)
        rw [hy]
        field_simp


/-! #### The Hölder divergence-form source -/

theorem aux_rem_resolved_meshes_cont_of_holder {d : ℕ} (G : SpatialCoordinates d → ℝ) (K R : ℝ)
    (hR : 0 < R)
    (h : ∀ x y : SpatialCoordinates d, Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
      |G x - G y| ≤ K * Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) :
    Continuous G := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hc : Continuous (fun y : SpatialCoordinates d => Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_finset_sum _ fun j _ =>
      ((continuous_apply j).sub continuous_const).pow 2)
  have h0 : Real.sqrt (∑ j : Fin d, (x j - x j) ^ 2) = 0 := by simp
  have hE : Filter.Tendsto (fun y : SpatialCoordinates d =>
      K * Real.sqrt (Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2))) (nhds x) (nhds 0) := by
    have hc2 := ((continuous_const : Continuous (fun _ : SpatialCoordinates d => K)).mul
      (Real.continuous_sqrt.comp hc)).tendsto x
    simpa [h0] using hc2
  have hev : ∀ᶠ y in nhds x, Real.sqrt (∑ j : Fin d, (y j - x j) ^ 2) ≤ R := by
    have := hc.tendsto x
    rw [h0] at this
    exact this.eventually (ge_mem_nhds hR)
  refine squeeze_zero' (Filter.Eventually.of_forall fun y => dist_nonneg) ?_ hE
  filter_upwards [hev] with y hy
  rw [Real.dist_eq]
  exact h y x hy


/-- `lem_primitive` with its explicit kernel abstracted: a divergence-form representative with the
smooth weak identity and the pointwise half-Hölder bound at scale `R`. -/
theorem aux_rem_resolved_meshes_primitive (d : ℕ) (hd : 2 ≤ d) :
    ∃ Ch : ℝ, 0 < Ch ∧ ∀ (R : ℝ) (hR : 0 < R) (z : SpatialCoordinates d)
      (f : SpatialCoordinates d → ℝ), MemLp f (⊤ : ENNReal) volume →
      (∀ᵐ x ∂volume, x ∉ (closedCube z R hR : Set (SpatialCoordinates d)) → f x = 0) →
      ∃ g : SpatialCoordinates d → Fin d → ℝ,
        (∀ φ : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          (∑ i : Fin d, ∫ x, g x i * fderiv ℝ φ x (Pi.single i 1)) = -∫ x, f x * φ x) ∧
        (∀ x y : SpatialCoordinates d, Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
          Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
            Ch * Real.sqrt R * (eLpNormEssSup f volume).toReal *
              Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) := by
  obtain ⟨C_log, C_holder, C_cube, -, hChol, -, hprim⟩ := lem_primitive d hd
  refine ⟨C_holder, hChol, fun R hR z f hf hs => ?_⟩
  have hP := hprim R hR z f hf hs
  exact ⟨_, hP.1, fun x y h => (hP.2.1 x y h).trans (hP.2.2.1 x y h)⟩

theorem aux_rem_resolved_meshes_cube_dist {d : ℕ} (z : SpatialCoordinates d) (ρ : ℝ) (hρ : 0 < ρ)
    (x y : SpatialCoordinates d) (hx : x ∈ (centeredCube z ρ hρ : Set (SpatialCoordinates d)))
    (hy : y ∈ (centeredCube z ρ hρ : Set (SpatialCoordinates d))) :
    Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ d * ρ := by
  have hx' : dist x z < ρ / 2 := hx
  have hy' : dist y z < ρ / 2 := hy
  have hxy : dist x y < ρ := by
    calc dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
      _ < ρ / 2 + ρ / 2 := by rw [dist_comm z y]; exact add_lt_add hx' hy'
      _ = ρ := by ring
  have hj : ∀ j : Fin d, (x j - y j) ^ 2 ≤ ρ ^ 2 := by
    intro j
    have := (dist_le_pi_dist x y j).trans hxy.le
    rw [Real.dist_eq] at this
    calc (x j - y j) ^ 2 = |x j - y j| ^ 2 := (sq_abs _).symm
      _ ≤ ρ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  by_cases hd0 : d = 0
  · subst hd0; simp
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd0
  have hsum : ∑ j : Fin d, (x j - y j) ^ 2 ≤ (d * ρ) ^ 2 := by
    calc ∑ j : Fin d, (x j - y j) ^ 2 ≤ ∑ _j : Fin d, ρ ^ 2 := Finset.sum_le_sum fun j _ => hj j
      _ = d * ρ ^ 2 := by simp
      _ ≤ (d * ρ) ^ 2 := by nlinarith
  calc Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ Real.sqrt ((d * ρ) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = d * ρ := Real.sqrt_sq (by positivity)

theorem aux_rem_resolved_meshes_coord_le {d : ℕ} (g : SpatialCoordinates d → Fin d → ℝ)
    (x y : SpatialCoordinates d) (i : Fin d) :
    |g x i - g y i| ≤ Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (f := fun i => (g x i - g y i) ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

/-- Consequences of a pointwise half-Hölder bound at a scale covering the root cube. -/
theorem aux_rem_resolved_meshes_holder_facts {d : ℕ} (z : SpatialCoordinates d) (ρ : ℝ)
    (hρ : 0 < ρ) (R : ℝ) (hR : 0 < R) (hRρ : (d : ℝ) * ρ ≤ R) (g : SpatialCoordinates d → Fin d → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hpt : ∀ x y : SpatialCoordinates d, Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R →
      Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) ≤
        K * Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) :
    (∀ i : Fin d, MemLp (fun x => g x i) 2
      (volume.restrict (centeredCube z ρ hρ : Set (SpatialCoordinates d)))) ∧
    SubdiffusiveProcess.CoarseGrainingVocab.MemHolder (centeredCube z ρ hρ : Set (SpatialCoordinates d)) (1 / 2) g ∧
    halfHolderSeminorm (centeredCube z ρ hρ : Set (SpatialCoordinates d)) g ≤ K := by
  have hdist : ∀ x ∈ (centeredCube z ρ hρ : Set (SpatialCoordinates d)),
      ∀ y ∈ (centeredCube z ρ hρ : Set (SpatialCoordinates d)),
      Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2) ≤ R :=
    fun x hx y hy => (aux_rem_resolved_meshes_cube_dist z ρ hρ x y hx hy).trans hRρ
  have hcont : ∀ i : Fin d, Continuous (fun x => g x i) := fun i =>
    aux_rem_resolved_meshes_cont_of_holder _ K R hR fun x y h =>
      (aux_rem_resolved_meshes_coord_le g x y i).trans (hpt x y h)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hzC : z ∈ (centeredCube z ρ hρ : Set (SpatialCoordinates d)) :=
      Metric.mem_ball_self (by positivity)
    refine MemLp.of_bound (hcont i).aestronglyMeasurable (|g z i| + K * Real.sqrt R) ?_
    filter_upwards [ae_restrict_mem (centeredCube z ρ hρ).isOpen.measurableSet] with x hx
    have hxz := hdist x hx z hzC
    have h1 := (aux_rem_resolved_meshes_coord_le g x z i).trans (hpt x z hxz)
    have h3 : Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - z j) ^ 2)) ≤ Real.sqrt R :=
      Real.sqrt_le_sqrt hxz
    have h4 : K * Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - z j) ^ 2)) ≤
        K * Real.sqrt R := mul_le_mul_of_nonneg_left h3 hK
    rw [Real.norm_eq_abs]
    have : |g x i| ≤ |g z i| + |g x i - g z i| := by
      have := abs_sub_abs_le_abs_sub (g x i) (g z i)
      linarith
    linarith
  · refine ⟨K, hK, ?_⟩
    intro x hx y hy
    have e1 : Homogenization.euclideanNorm (g x - g y) =
        Real.sqrt (∑ i : Fin d, (g x i - g y i) ^ 2) := by
      simp only [Homogenization.euclideanNorm, Homogenization.vecNormSq, Homogenization.vecDot,
        Pi.sub_apply, sq]
    have e2 : Homogenization.euclideanNorm (x - y) ^ (1 / 2 : ℝ) =
        Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) := by
      rw [← Real.sqrt_eq_rpow]
      simp only [Homogenization.euclideanNorm, Homogenization.vecNormSq, Homogenization.vecDot,
        Pi.sub_apply, sq]
    rw [e1, e2]
    exact hpt x y (hdist x hx y hy)
  · refine Real.sSup_le ?_ hK
    rintro v ⟨x, hx, y, hy, hxy, rfl⟩
    have hpos : 0 < Real.sqrt (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2)) := by
      apply Real.sqrt_pos.mpr
      apply Real.sqrt_pos.mpr
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
        by_contra hne
        push_neg at hne
        exact hxy (funext hne)
      have : 0 < (x j - y j) ^ 2 := by
        have : x j - y j ≠ 0 := sub_ne_zero.mpr hj
        positivity
      exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun j => (x j - y j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ j))
    rw [div_le_iff₀ hpos]
    exact hpt x y (hdist x hx y hy)


open scoped Distributions in
/-- The divergence-form identity passes from smooth compactly supported tests to the whole killed
space by continuity (killed data are the closure of smooth data). -/
theorem aux_rem_resolved_meshes_killed_identity {d : ℕ} (Ω : Opens (SpatialCoordinates d))
    (g : SpatialCoordinates d → Fin d → ℝ)
    (hgmem : ∀ i : Fin d, MemLp (fun x => g x i) 2 (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (Fr : SpatialCoordinates d → ℝ)
    (hFrmem : MemLp Fr 2 (volume.restrict (Ω : Set (SpatialCoordinates d))))
    (hweak : ∀ ψ : 𝓓(Ω, ℝ), (∑ i : Fin d, ∫ x, g x i * fderiv ℝ ψ x (Pi.single i 1)) =
      -∫ x, (Ω : Set (SpatialCoordinates d)).indicator Fr x * ψ x) :
    ∃ hgrad : HilbertGradient Ω,
      (∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
        =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fun x => g x i) ∧
      ∀ φ : killedSobolevGraph Ω,
        (∫ x in (Ω : Set (SpatialCoordinates d)), Fr x * (φ : SobolevData Ω).1 x) =
          -inner ℝ hgrad (subspaceGradient (killedSobolevGraph Ω) φ) := by
  have hΩm : MeasurableSet (Ω : Set (SpatialCoordinates d)) := Ω.isOpen.measurableSet
  let hgrad : HilbertGradient Ω :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => DomainL2 Ω)).symm
      (fun i => (hgmem i).toLp (fun x => g x i))
  have hgrad_apply : ∀ i, hgrad i = (hgmem i).toLp (fun x => g x i) := fun i => rfl
  refine ⟨hgrad, fun i => by rw [hgrad_apply]; exact MemLp.coeFn_toLp _, ?_⟩
  intro φ
  let T : SobolevData Ω →L[ℝ] ℝ :=
    (innerSL ℝ hgrad).comp (sobolevGradient) +
      (innerSL ℝ (hFrmem.toLp Fr)).comp (ContinuousLinearMap.fst ℝ (DomainL2 Ω) (Fin d → DomainL2 Ω))
  have hL2 : ∀ w : DomainL2 Ω, inner ℝ (hFrmem.toLp Fr) w =
      ∫ x in (Ω : Set (SpatialCoordinates d)), Fr x * w x := by
    intro w
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hFrmem.coeFn_toLp] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hinner : ∀ w : SobolevData Ω, inner ℝ hgrad (sobolevGradient w) =
      ∑ i : Fin d, ∫ x in (Ω : Set (SpatialCoordinates d)), g x i * w.2 i x := by
    intro w
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hgmem i).coeFn_toLp] with x hx
    change inner ℝ ((hgmem i).toLp (fun x => g x i) x) (w.2 i x) = _
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hTapply : ∀ w : SobolevData Ω, T w = inner ℝ hgrad (sobolevGradient w) +
      ∫ x in (Ω : Set (SpatialCoordinates d)), Fr x * w.1 x := by
    intro w
    change inner ℝ hgrad (sobolevGradient w) + inner ℝ (hFrmem.toLp Fr) w.1 = _
    rw [hL2]
  have hsmooth : ∀ ψ : 𝓓(Ω, ℝ), T (smoothSobolevData ψ) = 0 := by
    intro ψ
    rw [hTapply, hinner]
    have e1 : ∀ i : Fin d, (∫ x in (Ω : Set (SpatialCoordinates d)),
        g x i * (smoothSobolevData ψ).2 i x) = ∫ x, g x i * fderiv ℝ ψ x (Pi.single i 1) := by
      intro i
      calc (∫ x in (Ω : Set (SpatialCoordinates d)), g x i * (smoothSobolevData ψ).2 i x)
          = ∫ x in (Ω : Set (SpatialCoordinates d)), g x i * fderiv ℝ ψ x (Pi.single i 1) := by
            apply integral_congr_ae
            filter_upwards [testPartialL2_coeFn ψ i] with x hx
            change g x i * testPartialL2 ψ i x = _
            rw [hx]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
            rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (ψ.tsupport_subset h)),
              ContinuousLinearMap.zero_apply, mul_zero]
    have e2 : (∫ x in (Ω : Set (SpatialCoordinates d)), Fr x * (smoothSobolevData ψ).1 x) =
        ∫ x, (Ω : Set (SpatialCoordinates d)).indicator Fr x * ψ x := by
      calc (∫ x in (Ω : Set (SpatialCoordinates d)), Fr x * (smoothSobolevData ψ).1 x)
          = ∫ x in (Ω : Set (SpatialCoordinates d)), Fr x * ψ x := by
            apply integral_congr_ae
            filter_upwards [testL2_coeFn ψ] with x hx
            change Fr x * testL2 ψ x = _
            rw [hx]
        _ = ∫ x, (Ω : Set (SpatialCoordinates d)).indicator (fun x => Fr x * ψ x) x :=
            (integral_indicator hΩm).symm
        _ = _ := by
            congr 1
            funext x
            by_cases hxC : x ∈ (Ω : Set (SpatialCoordinates d))
            · simp only [Set.indicator_of_mem hxC]
            · simp only [Set.indicator_of_notMem hxC, zero_mul]
    rw [Finset.sum_congr rfl (fun i _ => e1 i), e2, hweak ψ]
    ring
  have hker : killedSobolevGraph Ω ≤ LinearMap.ker (T : SobolevData Ω →ₗ[ℝ] ℝ) := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨ψ, rfl⟩
      exact hsmooth ψ
    · exact ContinuousLinearMap.isClosed_ker T
  have hT0 := hker φ.2
  rw [LinearMap.mem_ker] at hT0
  change T (φ : SobolevData Ω) = 0 at hT0
  rw [hTapply] at hT0
  change _ = -inner ℝ hgrad (sobolevGradient (φ : SobolevData Ω))
  linarith


/-! #### Root-cube geometry -/

/-- The active faces of `I` on which the projected centre is the upper face `x_j = 1`. -/
def aux_rem_resolved_meshes_faceSet {d : ℕ} (y : SpatialCoordinates d) (I : Finset (Fin d)) :
    Finset (Fin d) :=
  I.filter (fun j => ¬ (y j ≤ 1 / 2))

theorem aux_rem_resolved_meshes_foldCenter_eq {d : ℕ} (y : SpatialCoordinates d)
    (I : Finset (Fin d)) (l : ℝ) (j : Fin d) (hj : j ∈ I) :
    foldedCubeCenter (l • (fun _ : Fin d => (1 / 2 : ℝ))) l I
        (aux_rem_resolved_meshes_faceSet y I) j =
      (l • aux_rem_resolved_meshes_center y I) j := by
  simp only [foldedCubeCenter, aux_rem_resolved_meshes_faceSet, aux_rem_resolved_meshes_center,
    Finset.mem_filter, hj, true_and, if_true, Pi.smul_apply, smul_eq_mul]
  by_cases hy : y j ≤ 1 / 2
  · simp only [hy, not_true_eq_false, if_false, if_true]; ring
  · simp only [hy, not_false_eq_true, if_true, if_false]; ring

theorem aux_rem_resolved_meshes_mem_centeredCube_iff {d : ℕ} (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (x : SpatialCoordinates d) :
    x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)) ↔ ∀ j, |x j - z j| < r / 2 := by
  rw [centeredCube_eq_pi, Set.mem_univ_pi]
  simp only [Set.mem_Ioo, abs_sub_lt_iff]
  constructor
  · intro h j; exact ⟨by linarith [(h j).2], by linarith [(h j).1]⟩
  · intro h j; exact ⟨by linarith [(h j).2], by linarith [(h j).1]⟩

/-- The root cube around the projected centre lies in the folded cube of `lem_even`. -/
theorem aux_rem_resolved_meshes_root_sub_folded {d : ℕ} (y : SpatialCoordinates d)
    (hy : y ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) (I : Finset (Fin d))
    (Lstar Rk : ℝ) (hLstar : 10 ≤ Lstar) (hRk : 0 < Rk) (hRk1 : 3 * Rk < 1)
    (hI : ∀ i, i ∉ I → 4 * Lstar * Rk ≤ min (y i) (1 - y i))
    (l : ℝ) (hl : 0 < l) (ρ : ℝ) (hρ : 0 < ρ) (hρeq : ρ / 2 = l * (3 * Rk)) :
    (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ : Set (SpatialCoordinates d)) ⊆
      foldedCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl I (aux_rem_resolved_meshes_faceSet y I) := by
  intro x hx
  rw [aux_rem_resolved_meshes_mem_centeredCube_iff] at hx
  have hyQ : ∀ j, 0 < y j ∧ y j < 1 := by
    intro j
    have := (aux_rem_resolved_meshes_mem_centeredCube_iff (fun _ : Fin d => (1 / 2 : ℝ))
      one_pos y).mp hy j
    rw [abs_lt] at this
    constructor <;> linarith [this.1, this.2]
  change x ∈ Set.pi Set.univ _
  rw [Set.mem_univ_pi]
  intro j
  have hxj := hx j
  rw [abs_lt, hρeq] at hxj
  simp only [Pi.smul_apply, smul_eq_mul, aux_rem_resolved_meshes_center] at hxj ⊢
  have h3l : l * (3 * Rk) < l := by nlinarith
  by_cases hj : j ∈ I
  · simp only [hj, if_true, aux_rem_resolved_meshes_faceSet, Finset.mem_filter, true_and] at hxj ⊢
    by_cases hyj : y j ≤ 1 / 2
    · simp only [hyj, if_true, not_true_eq_false, if_false, Set.mem_Ioo] at hxj ⊢
      constructor <;> nlinarith [hxj.1, hxj.2]
    · simp only [hyj, if_false, not_false_eq_true, if_true, Set.mem_Ioo] at hxj ⊢
      constructor <;> nlinarith [hxj.1, hxj.2]
  · simp only [hj, if_false, Set.mem_Ioo] at hxj ⊢
    have hmin := hI j hj
    have h1 : 3 * Rk ≤ y j := by
      have := min_le_left (y j) (1 - y j); nlinarith
    have h2 : 3 * Rk ≤ 1 - y j := by
      have := min_le_right (y j) (1 - y j); nlinarith
    constructor <;> nlinarith [hxj.1, hxj.2]

/-- Off the active planes, the fold sends the root cube into the Neumann cube `λQ`. -/
theorem aux_rem_resolved_meshes_fold_maps {d : ℕ} (y : SpatialCoordinates d)
    (hy : y ∈ (unitNeumannCube d : Set (SpatialCoordinates d))) (I : Finset (Fin d))
    (Lstar Rk : ℝ) (hLstar : 10 ≤ Lstar) (hRk : 0 < Rk) (hRk1 : 3 * Rk < 1)
    (hI : ∀ i, i ∉ I → 4 * Lstar * Rk ≤ min (y i) (1 - y i))
    (l : ℝ) (hl : 0 < l) (ρ : ℝ) (hρ : 0 < ρ) (hρeq : ρ / 2 = l * (3 * Rk))
    (x : SpatialCoordinates d)
    (hx : x ∈ (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ : Set (SpatialCoordinates d)))
    (hne : ∀ i : Fin d, x i ≠ (l • aux_rem_resolved_meshes_center y I) i) :
    coordinateFold (l • aux_rem_resolved_meshes_center y I) I (aux_rem_resolved_meshes_faceSet y I) x ∈
      (centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl : Set (SpatialCoordinates d)) := by
  rw [aux_rem_resolved_meshes_mem_centeredCube_iff] at hx ⊢
  have hyQ : ∀ j, 0 < y j ∧ y j < 1 := by
    intro j
    have := (aux_rem_resolved_meshes_mem_centeredCube_iff (fun _ : Fin d => (1 / 2 : ℝ))
      one_pos y).mp hy j
    rw [abs_lt] at this
    constructor <;> linarith [this.1, this.2]
  intro j
  have hxj := hx j
  have hnej := hne j
  rw [hρeq] at hxj
  simp only [Pi.smul_apply, smul_eq_mul, aux_rem_resolved_meshes_center, coordinateFold,
    coordinateReflectionSign] at hxj hnej ⊢
  have h3l : l * (3 * Rk) < l := by nlinarith
  rw [abs_lt]
  by_cases hj : j ∈ I
  · simp only [hj, if_true, aux_rem_resolved_meshes_faceSet, Finset.mem_filter, true_and] at hxj hnej ⊢
    by_cases hyj : y j ≤ 1 / 2
    · simp only [hyj, if_true, not_true_eq_false, if_false, mul_zero] at hxj hnej ⊢
      have hpos : 0 < |x j - 0| := abs_pos.mpr (sub_ne_zero.mpr hnej)
      constructor <;> nlinarith [abs_lt.mp hxj]
    · simp only [hyj, if_false, not_false_eq_true, if_true, mul_one] at hxj hnej ⊢
      have hpos : 0 < |x j - l| := abs_pos.mpr (sub_ne_zero.mpr hnej)
      constructor <;> nlinarith [abs_lt.mp hxj]
  · simp only [hj, if_false] at hxj ⊢
    have hmin := hI j hj
    have h1 : 3 * Rk ≤ y j := by
      have := min_le_left (y j) (1 - y j); nlinarith
    have h2 : 3 * Rk ≤ 1 - y j := by
      have := min_le_right (y j) (1 - y j); nlinarith
    constructor <;> nlinarith [abs_lt.mp hxj]

/-- A cube around the fold centre is invariant under the reflections of the fold. -/
theorem aux_rem_resolved_meshes_cube_symm {d : ℕ} (W z : SpatialCoordinates d) (I : Finset (Fin d))
    (hWz : ∀ i ∈ I, W i = z i) {r : ℝ} (hr : 0 < r) (J : Finset (Fin d)) (hJ : J ⊆ I) :
    coordinateReflection W J ⁻¹' (centeredCube z r hr : Set (SpatialCoordinates d)) =
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
  ext x
  simp only [Set.mem_preimage, aux_rem_resolved_meshes_mem_centeredCube_iff, coordinateReflection]
  apply forall_congr'
  intro j
  by_cases hj : j ∈ J
  · rw [if_pos hj, hWz j (hJ hj)]
    rw [show 2 * z j - x j - z j = -(x j - z j) by ring, abs_neg]
  · rw [if_neg hj]

open scoped Pointwise in
theorem aux_rem_resolved_meshes_cube_eq_smul {d : ℕ} (c : SpatialCoordinates d) {l r : ℝ}
    (hl : 0 < l) (hr : 0 < r) :
    (centeredCube (l • c) r hr : Set (SpatialCoordinates d)) = l • Metric.ball c (r / (2 * l)) := by
  rw [_root_.smul_ball hl.ne', Real.norm_eq_abs, abs_of_pos hl]
  change Metric.ball (l • c) (r / 2) = _
  congr 1
  field_simp



theorem aux_rem_resolved_meshes_e3r (x : ℝ) : (3 : ℝ) ^ x = Real.exp (Real.log 3 * x) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]

theorem aux_rem_resolved_meshes_e3n (j : ℕ) : (3 : ℝ) ^ j = Real.exp (Real.log 3 * j) := by
  rw [← Real.rpow_natCast, aux_rem_resolved_meshes_e3r]

theorem aux_rem_resolved_meshes_e3z (j : ℤ) : (3 : ℝ) ^ j = Real.exp (Real.log 3 * j) := by
  rw [← Real.rpow_intCast, aux_rem_resolved_meshes_e3r]

theorem aux_rem_resolved_meshes_arith_X (d : ℕ) (α t0 : ℝ) (hα : 2 * (1 - α) = (d : ℝ) - t0)
    (n m : ℕ) :
    ((3 : ℝ) ^ ((1 - α) * ((m : ℝ) - n))) ^ 2 * ((3 : ℝ) ^ n) ^ d / ((3 : ℝ) ^ m) ^ d =
      Real.exp (Real.log 3 * (-t0 * ((m : ℝ) - n))) := by
  rw [aux_rem_resolved_meshes_e3r, aux_rem_resolved_meshes_e3n, aux_rem_resolved_meshes_e3n,
    ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_sub]
  congr 1
  push_cast
  have : (1 - α) = ((d : ℝ) - t0) / 2 := by linarith
  rw [this]
  ring

theorem aux_rem_resolved_meshes_arith_sigma (t0 : ℝ) (n N k m : ℕ) (hm : (m : ℝ) = N - k + 1) :
    (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 =
      Real.exp (Real.log 3 * (t0 * ((n : ℝ) - m + 1))) := by
  rw [div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0), aux_rem_resolved_meshes_e3z,
    aux_rem_resolved_meshes_e3z, ← Real.exp_sub, Real.rpow_def_of_pos (Real.exp_pos _),
    Real.log_exp]
  congr 1
  push_cast
  rw [hm]
  ring

theorem aux_rem_resolved_meshes_arith_src (d : ℕ) (α t0 : ℝ) (hα : 2 * (1 - α) = (d : ℝ) - t0)
    (n m N k : ℕ) (hm : (m : ℝ) = N - k + 1) :
    ((3 : ℝ) ^ ((1 - α) * ((m : ℝ) - n))) ^ 2 * ((3 : ℝ) ^ n) ^ d *
        ((3 : ℝ) ^ ((m : ℝ) / 2)) ^ 2 * (3 : ℝ) ^ m *
        (((3 : ℝ) ^ (N : ℤ)) ^ d)⁻¹ * (((3 : ℝ) ^ (N : ℤ)) ^ 2)⁻¹ =
      6 ^ (d + 2) * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2) *
        Real.exp (Real.log 3 * (-t0 * ((m : ℝ) - n))) := by
  have h6 : (6 : ℝ) ^ (d + 2) = Real.exp (Real.log 6 * ((d : ℝ) + 2)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 6)]
    push_cast; ring_nf
  have hR : ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2) =
      Real.exp (Real.log ((3 : ℝ) ^ (-((k : ℤ))) / 2) * ((d : ℝ) + 2)) :=
    Real.rpow_def_of_pos (by positivity) _
  have hlogR : Real.log ((3 : ℝ) ^ (-((k : ℤ))) / 2) = -(k : ℝ) * Real.log 3 - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_zpow]
    push_cast; ring
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [h6, hR, hlogR, hlog6, aux_rem_resolved_meshes_e3r, aux_rem_resolved_meshes_e3r,
    aux_rem_resolved_meshes_e3n, aux_rem_resolved_meshes_e3n, aux_rem_resolved_meshes_e3z]
  simp only [← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  push_cast
  have : (1 - α) = ((d : ℝ) - t0) / 2 := by linarith
  rw [this, hm]
  ring


theorem aux_rem_resolved_meshes_arith_sq (κ vn vm X Y G Cf rf es e3 : ℝ) (hκ : 0 < κ)
    (hvn : 0 < vn) (hvm : 0 < vm) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hG : 0 ≤ G) (hCf : 0 ≤ Cf)
    (hrf : 0 < rf) (hes : 0 ≤ es) (he3 : 0 ≤ e3)
    (hcore : Real.sqrt (κ * es / vn) ≤
      Cf * X * (Real.sqrt (κ * e3 / vm) + Real.sqrt rf⁻¹ * Y * G)) :
    es ≤ 2 * Cf ^ 2 * (X ^ 2 * vn / vm) * e3 + 2 * Cf ^ 2 * (vn / κ * X ^ 2 * rf⁻¹ * Y ^ 2) * G ^ 2 := by
  set A := Real.sqrt (κ * e3 / vm)
  set B := Real.sqrt rf⁻¹ * Y * G
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hY) hG
  have h0 : 0 ≤ κ * es / vn := div_nonneg (mul_nonneg hκ.le hes) hvn.le
  have hr2 : κ * es / vn ≤ (Cf * X * (A + B)) ^ 2 := by
    have h1 := mul_self_le_mul_self (Real.sqrt_nonneg _) hcore
    rw [Real.mul_self_sqrt h0] at h1
    rw [sq]; exact h1
  have hAB : (A + B) ^ 2 ≤ 2 * (A ^ 2 + B ^ 2) := by
    have := sq_nonneg (A - B)
    have e1 : (A + B) ^ 2 = A ^ 2 + 2 * (A * B) + B ^ 2 := by ring
    have e2 : (A - B) ^ 2 = A ^ 2 - 2 * (A * B) + B ^ 2 := by ring
    linarith
  have hA2 : A ^ 2 = κ * e3 / vm := Real.sq_sqrt (div_nonneg (mul_nonneg hκ.le he3) hvm.le)
  have hB2 : B ^ 2 = rf⁻¹ * Y ^ 2 * G ^ 2 := by
    simp only [B]
    rw [mul_pow, mul_pow, Real.sq_sqrt (inv_pos.mpr hrf).le]
  have hsq : κ * es / vn ≤ 2 * Cf ^ 2 * X ^ 2 * (κ * e3 / vm + rf⁻¹ * Y ^ 2 * G ^ 2) := by
    have hCX : 0 ≤ (Cf * X) ^ 2 := sq_nonneg _
    calc κ * es / vn ≤ (Cf * X * (A + B)) ^ 2 := hr2
      _ = (Cf * X) ^ 2 * (A + B) ^ 2 := by ring
      _ ≤ (Cf * X) ^ 2 * (2 * (A ^ 2 + B ^ 2)) := mul_le_mul_of_nonneg_left hAB hCX
      _ = 2 * Cf ^ 2 * X ^ 2 * (κ * e3 / vm + rf⁻¹ * Y ^ 2 * G ^ 2) := by rw [hA2, hB2]; ring
  have hk : 0 ≤ vn / κ := div_nonneg hvn.le hκ.le
  have h1 := mul_le_mul_of_nonneg_left hsq hk
  have e3' : vn / κ * (κ * es / vn) = es := by field_simp
  have e4 : vn / κ * (2 * Cf ^ 2 * X ^ 2 * (κ * e3 / vm + rf⁻¹ * Y ^ 2 * G ^ 2)) =
      2 * Cf ^ 2 * (X ^ 2 * vn / vm) * e3 + 2 * Cf ^ 2 * (vn / κ * X ^ 2 * rf⁻¹ * Y ^ 2) * G ^ 2 := by
    field_simp
  rw [e3', e4] at h1
  exact h1

theorem aux_rem_resolved_meshes_arith_combine (Cf Ch cF rf Kf es e3 G σ ω0 Rk D6 P1 P2 L1 : ℝ)
    (hCf : 0 ≤ Cf) (hcF : 0 < cF) (hrf : 0 < rf) (hKf : 0 ≤ Kf) (he3 : 0 ≤ e3) (hRk : 0 ≤ Rk)
    (hω0 : 0 ≤ ω0) (hωσ : ω0 ≤ σ) (hD6 : 0 ≤ D6) (hL1 : 0 ≤ L1) (hL1' : L1 ≤ 1)
    (h1 : es ≤ 2 * Cf ^ 2 * P1 * e3 + 2 * Cf ^ 2 * P2 * G ^ 2)
    (hP1 : P1 = ω0) (hP2 : 0 ≤ P2)
    (hG2 : P2 * G ^ 2 ≤ L1 * D6 * ω0 * ((cF * rf)⁻¹ * Kf ^ 2 * Rk)) :
    es ≤ 2 * Cf ^ 2 * max 1 D6 * σ * (e3 + (cF * rf)⁻¹ * Kf ^ 2 * Rk) := by
  have hM1 : 1 ≤ max 1 D6 := le_max_left _ _
  have hM2 : D6 ≤ max 1 D6 := le_max_right _ _
  have hσ0 : 0 ≤ σ := hω0.trans hωσ
  have hCf2 : 0 ≤ 2 * Cf ^ 2 := by positivity
  have hsrc : 0 ≤ (cF * rf)⁻¹ * Kf ^ 2 * Rk := by positivity
  have hωM : ω0 ≤ max 1 D6 * σ :=
    calc ω0 ≤ σ := hωσ
      _ = 1 * σ := by ring
      _ ≤ max 1 D6 * σ := mul_le_mul_of_nonneg_right hM1 hσ0
  have hLD : L1 * D6 * ω0 ≤ max 1 D6 * σ := by
    have hLD1 : L1 * D6 ≤ max 1 D6 :=
      calc L1 * D6 ≤ 1 * D6 := mul_le_mul_of_nonneg_right hL1' hD6
        _ = D6 := one_mul _
        _ ≤ max 1 D6 := hM2
    calc L1 * D6 * ω0 ≤ max 1 D6 * ω0 := mul_le_mul_of_nonneg_right hLD1 hω0
      _ ≤ max 1 D6 * σ := mul_le_mul_of_nonneg_left hωσ (le_trans zero_le_one hM1)
  have t1 : 2 * Cf ^ 2 * P1 * e3 ≤ 2 * Cf ^ 2 * max 1 D6 * σ * e3 := by
    rw [hP1]
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hωM hCf2) he3
    calc 2 * Cf ^ 2 * ω0 * e3 ≤ 2 * Cf ^ 2 * (max 1 D6 * σ) * e3 := this
      _ = 2 * Cf ^ 2 * max 1 D6 * σ * e3 := by ring
  have t2 : 2 * Cf ^ 2 * P2 * G ^ 2 ≤ 2 * Cf ^ 2 * max 1 D6 * σ * ((cF * rf)⁻¹ * Kf ^ 2 * Rk) := by
    have a1 : P2 * G ^ 2 ≤ max 1 D6 * σ * ((cF * rf)⁻¹ * Kf ^ 2 * Rk) :=
      hG2.trans (mul_le_mul_of_nonneg_right hLD hsrc)
    have := mul_le_mul_of_nonneg_left a1 hCf2
    calc 2 * Cf ^ 2 * P2 * G ^ 2 = 2 * Cf ^ 2 * (P2 * G ^ 2) := by ring
      _ ≤ 2 * Cf ^ 2 * (max 1 D6 * σ * ((cF * rf)⁻¹ * Kf ^ 2 * Rk)) := this
      _ = _ := by ring
  calc es ≤ 2 * Cf ^ 2 * P1 * e3 + 2 * Cf ^ 2 * P2 * G ^ 2 := h1
    _ ≤ 2 * Cf ^ 2 * max 1 D6 * σ * e3 + 2 * Cf ^ 2 * max 1 D6 * σ * ((cF * rf)⁻¹ * Kf ^ 2 * Rk) :=
        add_le_add t1 t2
    _ = _ := by ring


theorem aux_rem_resolved_meshes_arith_alg (d card : ℕ) (vn l X Y rf Ch dd m3 cF Kf : ℝ)
    (hl : 0 < l) (hcF : 0 < cF) (hrf : 0 < rf) :
    vn / (2 ^ card * l ^ d * cF⁻¹) * X ^ 2 * rf⁻¹ * Y ^ 2 *
        (Ch ^ 2 * (dd * m3) * ((cF * l)⁻¹ * Kf) ^ 2) =
      (2 ^ card : ℝ)⁻¹ * (Ch ^ 2 * dd) * ((cF * rf)⁻¹ * Kf ^ 2) *
        (X ^ 2 * vn * Y ^ 2 * m3 * (l ^ d)⁻¹ * (l ^ 2)⁻¹) := by
  field_simp

/-- **Exponent arithmetic of the transported folded estimate.** -/
theorem aux_rem_resolved_meshes_final_arith (d : ℕ) (t0 α : ℝ) (hα : 2 * (1 - α) = (d : ℝ) - t0)
    (ht0 : 0 ≤ t0) (n m N k card : ℕ) (hm : (m : ℝ) = N - k + 1)
    (Cf Ch cF rf Kf es e3 G : ℝ) (hCf : 0 ≤ Cf) (hCh : 0 ≤ Ch) (hcF : 0 < cF) (hrf : 0 < rf)
    (hKf : 0 ≤ Kf) (hes : 0 ≤ es) (he3 : 0 ≤ e3) (hG0 : 0 ≤ G)
    (hcore : Real.sqrt ((2 ^ card * ((3 : ℝ) ^ (N : ℤ)) ^ d * cF⁻¹ * es) / ((3 : ℝ) ^ n) ^ d) ≤
      Cf * (3 : ℝ) ^ ((1 - α) * ((m : ℝ) - n)) *
        (Real.sqrt ((2 ^ card * ((3 : ℝ) ^ (N : ℤ)) ^ d * cF⁻¹ * e3) / ((3 : ℝ) ^ m) ^ d) +
          Real.sqrt rf⁻¹ * (3 : ℝ) ^ ((m : ℝ) / 2) * G))
    (hG : G ≤ Ch * Real.sqrt ((d : ℝ) * (3 : ℝ) ^ m) * ((cF * (3 : ℝ) ^ (N : ℤ))⁻¹ * Kf)) :
    es ≤ 2 * Cf ^ 2 * max 1 (Ch ^ 2 * d * 6 ^ (d + 2)) *
      (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
      (e3 + (cF * rf)⁻¹ * Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by
  have hl : 0 < (3 : ℝ) ^ (N : ℤ) := zpow_pos (by norm_num) _
  have hκ : 0 < 2 ^ card * ((3 : ℝ) ^ (N : ℤ)) ^ d * cF⁻¹ := by positivity
  have h1 := aux_rem_resolved_meshes_arith_sq (2 ^ card * ((3 : ℝ) ^ (N : ℤ)) ^ d * cF⁻¹)
    (((3 : ℝ) ^ n) ^ d) (((3 : ℝ) ^ m) ^ d) ((3 : ℝ) ^ ((1 - α) * ((m : ℝ) - n)))
    ((3 : ℝ) ^ ((m : ℝ) / 2)) G Cf rf es e3 hκ (by positivity) (by positivity)
    (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _) hG0 hCf hrf hes he3 hcore
  have iX := aux_rem_resolved_meshes_arith_X d α t0 hα n m
  have iσ := aux_rem_resolved_meshes_arith_sigma t0 n N k m hm
  have iS := aux_rem_resolved_meshes_arith_src d α t0 hα n m N k hm
  have hωσ : Real.exp (Real.log 3 * (-t0 * ((m : ℝ) - n))) ≤
      (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 := by
    rw [iσ]
    apply Real.exp_le_exp.mpr
    have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have e : Real.log 3 * (t0 * ((n : ℝ) - m + 1)) - Real.log 3 * (-t0 * ((m : ℝ) - n)) =
        Real.log 3 * t0 := by ring
    have := mul_nonneg hl3.le ht0
    linarith
  have hG2 : G ^ 2 ≤ Ch ^ 2 * ((d : ℝ) * (3 : ℝ) ^ m) * ((cF * (3 : ℝ) ^ (N : ℤ))⁻¹ * Kf) ^ 2 := by
    have h := pow_le_pow_left₀ hG0 hG 2
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)] at h
    exact h
  have hP2 : 0 ≤ ((3 : ℝ) ^ n) ^ d / (2 ^ card * ((3 : ℝ) ^ (N : ℤ)) ^ d * cF⁻¹) *
      ((3 : ℝ) ^ ((1 - α) * ((m : ℝ) - n))) ^ 2 * rf⁻¹ * ((3 : ℝ) ^ ((m : ℝ) / 2)) ^ 2 := by
    positivity
  refine aux_rem_resolved_meshes_arith_combine Cf Ch cF rf Kf es e3 G _ _ _ (Ch ^ 2 * d * 6 ^ (d + 2)) _ _
    (2 ^ card : ℝ)⁻¹ hCf hcF hrf hKf he3 (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
    hωσ (by positivity) (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))) h1 iX hP2 ?_
  calc ((3 : ℝ) ^ n) ^ d / (2 ^ card * ((3 : ℝ) ^ (N : ℤ)) ^ d * cF⁻¹) *
        ((3 : ℝ) ^ ((1 - α) * ((m : ℝ) - n))) ^ 2 * rf⁻¹ * ((3 : ℝ) ^ ((m : ℝ) / 2)) ^ 2 * G ^ 2
      ≤ ((3 : ℝ) ^ n) ^ d / (2 ^ card * ((3 : ℝ) ^ (N : ℤ)) ^ d * cF⁻¹) *
        ((3 : ℝ) ^ ((1 - α) * ((m : ℝ) - n))) ^ 2 * rf⁻¹ * ((3 : ℝ) ^ ((m : ℝ) / 2)) ^ 2 *
          (Ch ^ 2 * ((d : ℝ) * (3 : ℝ) ^ m) * ((cF * (3 : ℝ) ^ (N : ℤ))⁻¹ * Kf) ^ 2) :=
        mul_le_mul_of_nonneg_left hG2 hP2
    _ = (2 ^ card : ℝ)⁻¹ * (Ch ^ 2 * d) * ((cF * rf)⁻¹ * Kf ^ 2) *
          (((3 : ℝ) ^ ((1 - α) * ((m : ℝ) - n))) ^ 2 * ((3 : ℝ) ^ n) ^ d *
            ((3 : ℝ) ^ ((m : ℝ) / 2)) ^ 2 * (3 : ℝ) ^ m *
            (((3 : ℝ) ^ (N : ℤ)) ^ d)⁻¹ * (((3 : ℝ) ^ (N : ℤ)) ^ 2)⁻¹) :=
        aux_rem_resolved_meshes_arith_alg d card _ _ _ _ rf Ch d _ cF Kf hl hcF hrf
    _ = _ := by rw [iS]; ring


/-! ### Stage 2: the finite-cutoff residual from the all-face-set folded package -/

theorem aux_rem_resolved_meshes_localE_congr {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) {s t : Set (SpatialCoordinates d)} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : s = t) (g : HilbertGradient Ω) :
    localGradientEnergy a hs g = localGradientEnergy a ht g := by
  subst hst; rfl

/-- A measurable, everywhere-bounded representative of an essentially bounded source. -/
theorem aux_rem_resolved_meshes_clamp {d : ℕ} (f : SpatialCoordinates d → ℝ)
    (hf : AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (Kf : ℝ) (hK : 0 ≤ Kf)
    (hfb : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) :
    ∃ f' : SpatialCoordinates d → ℝ, Measurable f' ∧ (∀ y, |f' y| ≤ Kf) ∧
      f =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] f' := by
  refine ⟨fun y => max (-Kf) (min Kf (hf.mk f y)), ?_, ?_, ?_⟩
  · exact measurable_const.max (measurable_const.min hf.measurable_mk)
  · intro y
    rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  · filter_upwards [hf.ae_eq_mk, hfb] with y hy hb
    rw [← hy]
    have := abs_le.mp hb
    rw [min_eq_right this.2, max_eq_right this.1]

/-- The α-range guard of the folded package below a disorder threshold. -/
theorem aux_rem_resolved_meshes_alpha_range (Cf α : ℝ) (hCf : 0 < Cf) (hα : α < 1) (hα2 : 1 / 2 ≤ α)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ min (1 / 2) (((1 - α) / Cf) ^ 2)) :
    α ∈ Set.Icc (1 / 2 : ℝ) (1 - Cf * δ * Real.sqrt |Real.log δ|) := by
  refine ⟨hα2, ?_⟩
  have h1 : δ ≤ 1 / 2 := hδ.trans (min_le_left _ _)
  have h2 : δ ≤ ((1 - α) / Cf) ^ 2 := hδ.trans (min_le_right _ _)
  have hlog := aux_rem_resolved_meshes_abs_log_le hδ0 (by linarith)
  have hsq : δ * Real.sqrt |Real.log δ| ≤ Real.sqrt δ := by
    have : δ * Real.sqrt |Real.log δ| = Real.sqrt (δ ^ 2 * |Real.log δ|) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hδ0.le]
    rw [this]
    apply Real.sqrt_le_sqrt
    calc δ ^ 2 * |Real.log δ| ≤ δ ^ 2 * δ⁻¹ := by gcongr
      _ = δ := by field_simp
  have hsd : Real.sqrt δ ≤ (1 - α) / Cf := by
    rw [show (1 - α) / Cf = Real.sqrt (((1 - α) / Cf) ^ 2) from
      (Real.sqrt_sq (div_nonneg (by linarith) hCf.le)).symm]
    exact Real.sqrt_le_sqrt h2
  have : Cf * (δ * Real.sqrt |Real.log δ|) ≤ 1 - α := by
    calc Cf * (δ * Real.sqrt |Real.log δ|) ≤ Cf * ((1 - α) / Cf) := by
          gcongr; exact hsq.trans hsd
      _ = 1 - α := by field_simp
  nlinarith

open scoped Pointwise in
/-- The folded root-cube energy of a sub-cube around the fold centre, in terms of the original
energy on the corresponding ball. -/
theorem aux_rem_resolved_meshes_root_energy {d : ℕ} (l : ℝ) (hl : 0 < l)
    (hset : ((centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)) = l • (unitNeumannCube d : Set (SpatialCoordinates d)))
    (a : PositiveCoefficient (unitNeumannCube d))
    (A : PositiveCoefficient (centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl))
    (cF : ℝ) (hcF : 0 < cF)
    (hA : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      a.val y = cF * A.val (l • y))
    (u : meanZeroSobolevGraph (unitNeumannCube d))
    (v : weakSobolevGraph (centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl))
    (hv2 : ∀ i : Fin d, ∀ᵐ x ∂volume.restrict ((centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl :
        Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
      (v : SobolevData (centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl)).2 i x = (u : SobolevData (unitNeumannCube d)).2 i (l⁻¹ • x))
    (c : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hB : MeasurableSet (centeredCube (l • c) r hr : Set (SpatialCoordinates d))) :
    localGradientEnergy A (hB.inter (centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl).isOpen.measurableSet)
        (sobolevGradient (v : SobolevData (centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl))) =
      l ^ d * cF⁻¹ *
        aux_rem_resolved_meshes_energy a u (Metric.ball c (r / (2 * l))) := by
  have hS : MeasurableSet (Metric.ball c (r / (2 * l))) := measurableSet_ball
  have hB' : MeasurableSet ((l • Metric.ball c (r / (2 * l))) ∩
      ((centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))) :=
    (hS.const_smul₀ l).inter (centeredCube _ _ _).isOpen.measurableSet
  rw [aux_rem_resolved_meshes_localE_congr A _ hB'
    (by rw [aux_rem_resolved_meshes_cube_eq_smul c hl hr])]
  rw [aux_rem_resolved_meshes_energy_dilate hl hset a A cF hcF hA ⟨u.1, u.2.1⟩ v hv2 _ hS hB',
    aux_rem_resolved_meshes_energy_local a u _ hS]

open scoped Pointwise in
/-- **Q1a.**  Dilation, `lem_even`, restriction, coefficient identification and the root-cube
energy formula. -/
theorem aux_rem_resolved_meshes_root_package {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M) (Lv : ℕ) (om : BilateralField d)
    (l : ℝ) (hl : 0 < l) (cF : ℝ) (hcF : 0 < cF)
    (a : PositiveCoefficient (unitNeumannCube d))
    (ha : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        a.val y = cF * (Sreg.cutoffOn Lv om (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl).val (l • y))
    (f2 : SpatialCoordinates d → ℝ) (hf2m : Measurable f2) (Kf' : ℝ) (hKf' : 0 ≤ Kf')
    (hf2b : ∀ y, |f2 y| ≤ Kf')
    (hf20 : (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f2 y) = 0)
    (u : meanZeroSobolevGraph (unitNeumannCube d))
    (hu2 : ∀ ψ : weakSobolevGraph (unitNeumannCube d),
      sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d)) ψ =
        ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
          f2 x * (ψ : SobolevData (unitNeumannCube d)).1 x)
    (y : SpatialCoordinates d) (hy : y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (I : Finset (Fin d)) (Lstar Rk : ℝ) (hLstar : 10 ≤ Lstar) (hRk : 0 < Rk) (hRk3 : 3 * Rk < 1)
    (hI : ∀ i, i ∉ I → 4 * Lstar * Rk ≤ min (y i) (1 - y i))
    (ρ : ℝ) (hρ : 0 < ρ) (hρeq : ρ / 2 = l * (3 * Rk)) :
    ∃ (fc : PositiveCoefficient (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ))
      (ut : weakSobolevGraph (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ)),
      ((fc.val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ :
            Set (SpatialCoordinates d))]
        fun x => (Sreg.cutoffOn Lv om (l • aux_rem_resolved_meshes_center y I) ρ hρ).val
          (coordinateFold (l • aux_rem_resolved_meshes_center y I) I
            (aux_rem_resolved_meshes_faceSet y I) x)) ∧
      (∀ φ : killedSobolevGraph (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ),
        sobolevCoefficientForm fc (ut : SobolevData (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ)) (φ : SobolevData (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ)) =
          ∫ x in (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ : Set (SpatialCoordinates d)),
            ((cF * l)⁻¹ * f2 (l⁻¹ • coordinateFold (l • aux_rem_resolved_meshes_center y I) I
              (aux_rem_resolved_meshes_faceSet y I) x)) * (φ : SobolevData (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ)).1 x) ∧
      (∀ (r : ℝ) (hr : 0 < r), r ≤ ρ →
        localGradientEnergy fc (centeredCube (l • aux_rem_resolved_meshes_center y I) r hr).isOpen.measurableSet
            (sobolevGradient (ut : SobolevData (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ))) =
          2 ^ I.card * (l ^ d * cF⁻¹ *
            aux_rem_resolved_meshes_energy a u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (r / (2 * l))))) := by
  have hset : ((centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)) = l • (unitNeumannCube d : Set (SpatialCoordinates d)) := by
    rw [aux_rem_resolved_meshes_cube_eq_smul _ hl hl]
    change l • Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (l / (2 * l)) =
      l • Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)
    congr 2
    field_simp
  obtain ⟨v, -, hv2, hveq⟩ := aux_rem_resolved_meshes_neumann_dilate hl hset a
    (Sreg.cutoffOn Lv om (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl) cF hcF ha f2 ⟨u.1, u.2.1⟩ hu2
  have hFm : Measurable (fun x : SpatialCoordinates d => (cF * l)⁻¹ * f2 (l⁻¹ • x)) :=
    measurable_const.mul (hf2m.comp (measurable_const_smul _))
  have hMF : 0 ≤ (cF * l)⁻¹ * Kf' := by positivity
  have hFb : ∀ x : SpatialCoordinates d, |(cF * l)⁻¹ * f2 (l⁻¹ • x)| ≤ (cF * l)⁻¹ * Kf' := by
    intro x
    rw [abs_mul, abs_of_pos (inv_pos.mpr (mul_pos hcF hl))]
    exact mul_le_mul_of_nonneg_left (hf2b _) (by positivity)
  have hF0 : (∫ x in (centeredCube (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl : Set (SpatialCoordinates d)),
      (cF * l)⁻¹ * f2 (l⁻¹ • x)) = 0 := by
    rw [hset, aux_rem_resolved_meshes_setIntegral_smul _ (unitNeumannCube d).isOpen.measurableSet hl]
    have : ∀ y : SpatialCoordinates d, (cF * l)⁻¹ * f2 (l⁻¹ • (l • y)) = (cF * l)⁻¹ * f2 y :=
      fun y => by rw [smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
    simp only [this]
    rw [integral_const_mul, hf20]; ring
  have hsub := aux_rem_resolved_meshes_root_sub_folded y hy I Lstar Rk hLstar hRk hRk3 hI l hl ρ hρ hρeq
  obtain ⟨fc, ut, hfc, hueq, hE⟩ := aux_rem_resolved_meshes_fold_restrict
    (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl I (aux_rem_resolved_meshes_faceSet y I)
    (Sreg.cutoffOn Lv om (l • (fun _ : Fin d => (1 / 2 : ℝ))) l hl) _
    ((cF * l)⁻¹ * Kf') hMF hFm.aemeasurable (Filter.Eventually.of_forall hFb) hF0 v hveq
    (l • aux_rem_resolved_meshes_center y I) ρ hρ hsub
  have hZ : ∀ i ∈ I, foldedCubeCenter (l • (fun _ : Fin d => (1 / 2 : ℝ))) l I
      (aux_rem_resolved_meshes_faceSet y I) i = (l • aux_rem_resolved_meshes_center y I) i :=
    fun i hi => aux_rem_resolved_meshes_foldCenter_eq y I l i hi
  have hfold := aux_rem_resolved_meshes_fold_center_congr _ _ I (aux_rem_resolved_meshes_faceSet y I) hZ
  refine ⟨fc, ut, ?_, ?_, ?_⟩
  · exact aux_rem_resolved_meshes_coef_ident Sreg Lv om _ l hl _ ρ hρ I _ _ hZ
      (fun x hx hne => aux_rem_resolved_meshes_fold_maps y hy I Lstar Rk hLstar hRk hRk3 hI l hl ρ hρ
        hρeq x hx hne) fc hfc
  · intro φ
    rw [hueq φ, hfold]
  · intro r hr hrρ
    have hsubr : (centeredCube (l • aux_rem_resolved_meshes_center y I) r hr : Set (SpatialCoordinates d)) ⊆
        (centeredCube (l • aux_rem_resolved_meshes_center y I) ρ hρ : Set (SpatialCoordinates d)) :=
      Metric.ball_subset_ball (by linarith)
    rw [hE _ _ hsubr (fun J hJ => aux_rem_resolved_meshes_cube_symm _ _ I hZ hr J hJ)]
    rw [aux_rem_resolved_meshes_root_energy l hl hset a _ cF hcF ha u v hv2 _ r hr
      (centeredCube (l • aux_rem_resolved_meshes_center y I) r hr).isOpen.measurableSet]

/-! ### Finite infrared truncations: exact window identity and exact reference

For `H = H_{L0} = ∑_{n ≤ L0}` (infrared layers up to `L0`, `H_0 = 0`) the actual coefficient is,
almost everywhere on `Q`, the constant multiple `c_{N,L0} · a_{N+L0}(3^N ·)` of the relabelled
stationary cutoff coefficient (no limit `L' → ∞`), and the infrared correction `ρ` is identically
`1`, so the finite root reference is the literal reference `b_{k-1}`. -/

theorem aux_rem_resolved_meshes_window_trunc {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M) (omega : BilateralField d)
    (L0 N : ℕ) :
    ∃ cFin : ℝ, 0 < cFin ∧
      ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N
            (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val y =
          cFin * (Sreg.cutoffOn (N + L0) (aux_rem_resolved_meshes_relabel N omega)
            ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
            ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val (((3 : ℝ) ^ (N : ℤ)) • y) := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (N : ℤ) := by positivity
  refine ⟨(SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
      Real.exp ((L0 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P -
        ∑ n ∈ Finset.range L0, omega (Int.ofNat (n + 1)) 0),
    mul_pos (inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)) (Real.exp_pos _), ?_⟩
  have hcut := aux_rem_resolved_meshes_physical_cutoff_bridge_ae_smul_pullback h3.ne'
    (unitNeumannCube d).isOpen.measurableSet
    (centeredCube (((3 : ℝ) ^ (N : ℤ)) • (fun _ : Fin d => (1 / 2 : ℝ))) ((3 : ℝ) ^ (N : ℤ))
      (by positivity)).isOpen.measurableSet
    (fun y hy => aux_rem_resolved_meshes_smul_mem_cube N y hy)
    (Sreg.cutoffOn_eq (N + L0) (aux_rem_resolved_meshes_relabel N omega)
      (((3 : ℝ) ^ (N : ℤ)) • (fun _ : Fin d => (1 / 2 : ℝ))) ((3 : ℝ) ^ (N : ℤ)) (by positivity))
  filter_upwards [aux_rem_resolved_meshes_physical_cutoff_bridge_cutoffPositiveCoefficient_ae M
    (fun om => infraredPartialSum om L0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos, hcut]
    with y hy hcy
  rw [hy, hcy, aux_rem_resolved_meshes_physical_cutoff_bridge_truncation_identity]
  congr 3
  apply Finset.sum_congr rfl
  intro j _
  change _ = (omega ((j : ℤ) - (N : ℤ)))
      ((3 : ℝ) ^ (-(N : ℤ)) • ((3 : ℝ) ^ (N : ℤ)) • y)
  rw [smul_smul, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero, one_smul]

theorem aux_rem_resolved_meshes_rho_eq_one {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M) (omega : BilateralField d)
    (L0 N : ℕ) (cF : ℝ) (hcF : 0 < cF)
    (hwin : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N
          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val y =
        cF * (Sreg.cutoffOn (N + L0) (aux_rem_resolved_meshes_relabel N omega)
          ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
          ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val (((3 : ℝ) ^ (N : ℤ)) • y)) :
    ∀ x : SpatialCoordinates d,
      aux_rem_resolved_meshes_rho M (fun om => infraredPartialSum om L0) omega N cF L0 x = 1 := by
  have hconst : ∀ x : SpatialCoordinates d,
      aux_rem_resolved_meshes_rho M (fun om => infraredPartialSum om L0) omega N cF L0 x =
        aux_rem_resolved_meshes_rho M (fun om => infraredPartialSum om L0) omega N cF L0 0 := by
    intro x
    rw [aux_rem_resolved_meshes_rho_exp M _ omega N cF hcF L0 x,
      aux_rem_resolved_meshes_rho_exp M _ omega N cF hcF L0 0]
    simp only [sub_self, add_zero]
  haveI : NeZero (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
    ⟨by
      rw [Ne, Measure.restrict_eq_zero]
      change volume (Metric.ball (fun _ : Fin d => (1 / 2 : ℝ)) (1 / 2)) ≠ 0
      exact (Metric.measure_ball_pos volume _ (by norm_num)).ne'⟩
  have hex : ∃ y : SpatialCoordinates d,
      (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N
          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val y =
        cF * (Sreg.cutoffOn (N + L0) (aux_rem_resolved_meshes_relabel N omega)
          ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
          ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val (((3 : ℝ) ^ (N : ℤ)) • y) ∧
      (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N
          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val y =
        cutoffCoefficient M (fun om => infraredPartialSum om L0) omega N y ∧
      (Sreg.cutoffOn (N + L0) (aux_rem_resolved_meshes_relabel N omega)
          ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
          ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val (((3 : ℝ) ^ (N : ℤ)) • y) =
        Real.exp ((∑ j ∈ Finset.range (N + L0 + 1), (omega ((j : ℤ) - (N : ℤ))) y) -
          ((N + L0 : ℕ) + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) :=
    (hwin.and ((aux_rem_resolved_meshes_cutoff_coeFn M _ omega N).and
      (aux_rem_resolved_meshes_cutoffOn_scaled Sreg omega N L0))).exists
  obtain ⟨y, h1, h2, h3⟩ := hex
  have hpos := cutoffCoefficient_pos M (fun om => infraredPartialSum om L0) omega N y
  have hrho := aux_rem_resolved_meshes_rho_mul M (fun om => infraredPartialSum om L0) omega N cF L0 y
  have hy : aux_rem_resolved_meshes_rho M (fun om => infraredPartialSum om L0) omega N cF L0 y = 1 := by
    have e : aux_rem_resolved_meshes_rho M (fun om => infraredPartialSum om L0) omega N cF L0 y *
        cutoffCoefficient M (fun om => infraredPartialSum om L0) omega N y =
        1 * cutoffCoefficient M (fun om => infraredPartialSum om L0) omega N y := by
      rw [hrho, one_mul, ← h2, h1, h3]
    exact mul_right_cancel₀ hpos.ne' e
  intro x
  rw [hconst x, ← hconst y, hy]

/-- **Good branch at a finite truncation, no limit.**  The finite-cutoff residual applied to the
actual coefficient `A_N^{(L0)} = c · a_{N+L0}(3^N ·)`, whose root reference `c · ref` is exactly
the literal reference `b_{k-1}` (`ρ ≡ 1`). -/
theorem aux_rem_resolved_meshes_good_finite (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 Kt C1 delta1 : ℝ) (hC1 : 0 ≤ C1)
    (hfin : aux_rem_resolved_meshes_finite_onestep d hd Lstar Rstar t0 Kt C1 delta1)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (E : in_J d)
    (Poinc : in_poincare d hd E) (Ext : in_extension d hd E)
    (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
    (hdet : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (L0 : ℕ) (hδ : M.delta ≤ delta1)
    (omega : BilateralField d) (N : ℕ) (cF : ℝ) (hcF : 0 < cF)
    (hwin : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N
          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos).val y =
        cF * (Sreg.cutoffOn (N + L0) (aux_rem_resolved_meshes_relabel N omega)
          ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
          ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val (((3 : ℝ) ^ (N : ℤ)) • y))
    (f : SpatialCoordinates d → ℝ)
    (hf : AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hfb : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf)
    (hf0 : (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0)
    (u : meanZeroSobolevGraph (unitNeumannCube d))
    (hu : SolvesNeumann (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) f u)
    (y : SpatialCoordinates d) (hy : y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (I : Finset (Fin d)) (n k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (hR : (3 : ℝ) ^ (-((k : ℤ))) / 2 ≤ Rstar)
    (h8 : 8 * ((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) < (3 : ℝ) ^ (-((k : ℤ))) / 2)
    (hI : ∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ min (y i) (1 - y i))
    (hgood : n + It.prefixLen ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
          (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1)
          (aux_rem_resolved_meshes_relabel N omega) ≤ N - k + 1) :
    aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N
          (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
        (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2)) ≤
      7 * (C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0) *
        (aux_rem_resolved_meshes_energy
            (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N
              (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
            (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
          (aux_rem_resolved_meshes_bref M (fun om => infraredPartialSum om L0) omega N (k - 1)
            (aux_rem_resolved_meshes_center y I))⁻¹ *
            (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))) := by
  have hm2 : 2 ≤ N - k + 1 := by
    have := It.prefix_lower ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
      (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1) (aux_rem_resolved_meshes_relabel N omega)
    rw [It.k_eq] at this
    omega
  have hF := hfin M E Poinc Ext Sreg It hdet hδ omega N L0 cF hcF
    (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) hwin f hf Kf hKf hfb hf0 u hu y hy I n k
    hk1 hkN hR h8 hI hgood
  have href : cF * It.ref (N + L0) (N - k + 1 - 2) ((3 : ℝ) ^ (N : ℤ) •
      aux_rem_resolved_meshes_center y I) (aux_rem_resolved_meshes_relabel N omega) =
      aux_rem_resolved_meshes_bref M (fun om => infraredPartialSum om L0) omega N (k - 1)
        (aux_rem_resolved_meshes_center y I) := by
    rw [aux_rem_resolved_meshes_ref_avg It (fun om => infraredPartialSum om L0) omega N k L0 hk1
      hkN hm2 cF (aux_rem_resolved_meshes_center y I)]
    have hrho := aux_rem_resolved_meshes_rho_eq_one M Sreg omega L0 N cF hcF hwin
    simp only [hrho, one_mul]
    rfl
  rw [href] at hF
  have hσ : 0 ≤ (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 := by
    positivity
  have hK : 0 ≤ C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 :=
    mul_nonneg hC1 hσ
  have hbv : 0 < aux_rem_resolved_meshes_bref M (fun om => infraredPartialSum om L0) omega N (k - 1)
      (aux_rem_resolved_meshes_center y I) :=
    aux_lane4_two_mesh_energy_bound_bpos M (fun om => infraredPartialSum om L0) omega N (k - 1)
      (aux_rem_resolved_meshes_center y I)
  have hE3 : 0 ≤ aux_rem_resolved_meshes_energy
      (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
      (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) := by
    rw [aux_rem_resolved_meshes_energy_local _ _ _ measurableSet_ball]
    exact localGradientEnergy_nonneg _ _ _
  have hZ : 0 ≤ Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2) := by positivity
  have hB : 0 ≤ aux_rem_resolved_meshes_energy
      (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
      (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
      (aux_rem_resolved_meshes_bref M (fun om => infraredPartialSum om L0) omega N (k - 1)
        (aux_rem_resolved_meshes_center y I))⁻¹ *
        (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) :=
    add_nonneg hE3 (mul_nonneg (inv_pos.mpr hbv).le hZ)
  refine hF.trans ?_
  have e : C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
      (aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N
            (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
        (aux_rem_resolved_meshes_bref M (fun om => infraredPartialSum om L0) omega N (k - 1)
          (aux_rem_resolved_meshes_center y I))⁻¹ * Kf ^ 2 *
          ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) =
      C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
        (aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N
            (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
        (aux_rem_resolved_meshes_bref M (fun om => infraredPartialSum om L0) omega N (k - 1)
          (aux_rem_resolved_meshes_center y I))⁻¹ *
          (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))) := by ring
  rw [e]
  nlinarith [mul_nonneg hK hB]

def aux_rem_resolved_meshes_onestep_trunc (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 : ℝ) (J : ℕ) (Kt Cstep c delta1 : ℝ) : Prop :=
  ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (E : in_J d)
    (_ : in_poincare d hd E) (_ : in_extension d hd E)
    (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
    (_ : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (L0 : ℕ),
    M.delta ≤ delta1 →
    ∀ (omega : BilateralField d) (N : ℕ),
    ∀ f : SpatialCoordinates d → ℝ,
      AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
    ∀ Kf : ℝ, 0 ≤ Kf →
      (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
      (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
    ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      SolvesNeumann (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) f u →
    ∀ (y : SpatialCoordinates d), y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
    ∀ (I : Finset (Fin d)) (s : ℝ) (k : ℕ),
      s ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) → (3 : ℝ) ^ (-(N : ℤ)) / 2 ≤ s → 0 < s →
      k ≤ N → 8 * s < (3 : ℝ) ^ (-((k : ℤ))) / 2 → (3 : ℝ) ^ (-((k : ℤ))) / 2 ≤ Rstar →
      (∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ min (y i) (1 - y i)) →
      aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) s) ≤
        Cstep * Real.exp (c * (It.prefixLen
            ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
            (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + J)
            (aux_rem_resolved_meshes_relabel N omega) : ℝ)) *
          (s / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M (fun om => infraredPartialSum om L0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I)
                (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M (fun om => infraredPartialSum om L0) omega N (k - J)
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))


/-- **Stage 1 at a finite truncation.**  The one-step residual for `A_N^{(L0)}` follows from the
finite-cutoff residual: the bad-prefix branch is paid by the allowance, the good branch is the
finite estimate itself (`good_finite`), with no limit. -/
theorem aux_rem_resolved_meshes_onestep_trunc_of_finite (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 : ℝ) (hLstar : 10 ≤ Lstar) (hRstar_lt : Rstar < 1 / (100 * Lstar))
    (ht0 : 0 < t0) (Kt C1 delta1 : ℝ) (hC1 : 0 ≤ C1)
    (hfin : aux_rem_resolved_meshes_finite_onestep d hd Lstar Rstar t0 Kt C1 delta1) :
    aux_rem_resolved_meshes_onestep_trunc d hd Lstar Rstar t0 1 Kt (max 1 (7 * C1))
      (t0 * Real.log 3 + 1) delta1 := by
  intro M E Poinc Ext Sreg It hdet L0 hδ omega N f hf Kf hKf hfb hf0 u hu y hy I s k
    hs hs1 hs0 hk h8 hR hI
  obtain ⟨cF0, hcF0, hwin⟩ := aux_rem_resolved_meshes_window_trunc M Sreg omega L0 N
  set H : BilateralField d → C(SpatialCoordinates d, ℝ) := fun om => infraredPartialSum om L0
    with hHdef
  obtain ⟨j, rfl⟩ := hs
  dsimp only at hs1 hs0 h8 ⊢
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hc0 : 0 ≤ t0 * Real.log 3 + 1 := by positivity
  -- the target depth
  have hjN : -(N : ℤ) ≤ j := by
    have h1 : (3 : ℝ) ^ (-(N : ℤ)) ≤ (3 : ℝ) ^ j := by linarith
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp h1
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    subst hk0
    have : (1 : ℝ) / 2 ≤ Rstar := by simpa using hR
    have h100 : 0 < 100 * Lstar := by linarith
    have : 1 / (100 * Lstar) ≤ 1 / 1000 := by
      rw [div_le_div_iff₀ h100 (by norm_num)]; linarith
    linarith
  set n : ℕ := (j + (N : ℤ)).toNat with hn_def
  have hn : ((n : ℕ) : ℤ) = j + (N : ℤ) := Int.toNat_of_nonneg (by omega)
  have hjn : j = (n : ℤ) - (N : ℤ) := by omega
  set pl := It.prefixLen ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
    (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1) (aux_rem_resolved_meshes_relabel N omega)
    with hpl
  have hmono : ∀ {A A' : Set (SpatialCoordinates d)}, A ⊆ A' →
      aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u A ≤
      aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u A' :=
    fun h => aux_rem_resolved_strata_energy_mono
      (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
      ⟨u.1, u.2.1⟩ h
  have hnn : ∀ A : Set (SpatialCoordinates d), 0 ≤ aux_rem_resolved_meshes_energy
      (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u A :=
    fun A => aux_rem_resolved_strata_energy_nonneg
      (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) ⟨u.1, u.2.1⟩ A
  have hRk : 0 < (3 : ℝ) ^ (-((k : ℤ))) / 2 := by positivity
  have hbv : 0 < aux_rem_resolved_meshes_bref M H omega N (k - 1)
      (aux_rem_resolved_meshes_center y I) :=
    aux_lane4_two_mesh_energy_bound_bpos M H omega N (k - 1) (aux_rem_resolved_meshes_center y I)
  have hsrc : 0 ≤ (aux_rem_resolved_meshes_bref M H omega N (k - 1)
      (aux_rem_resolved_meshes_center y I))⁻¹ * Kf ^ 2 *
      ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2) := by positivity
  have hLR : aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
        (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ j / 2)) ≤
      aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
        (Metric.ball (aux_rem_resolved_meshes_center y I) (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) :=
    hmono (Metric.ball_subset_ball (by nlinarith))
  have hσ : 0 ≤ (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 := by positivity
  have hexp1 : 1 ≤ Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) :=
    Real.one_le_exp (mul_nonneg hc0 (Nat.cast_nonneg _))
  by_cases hgood : n + pl ≤ N - k + 1
  · -- good branch
    have hG := aux_rem_resolved_meshes_good_finite d hd Lstar Rstar t0 Kt C1 delta1 hC1 hfin M E
      Poinc Ext Sreg It hdet L0 hδ omega N cF0 hcF0 hwin f hf Kf hKf hfb hf0 u hu y hy I
      n k hk1 hk hR (by rw [← hjn]; exact h8) hI hgood
    rw [← hjn] at hG
    have h3L := hmono (Metric.ball_subset_ball (x := aux_rem_resolved_meshes_center y I)
      (show 3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) by nlinarith))
    refine hG.trans ?_
    have hC : 7 * C1 ≤ max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) := by
      have := le_max_right 1 (7 * C1)
      have h1 : 0 ≤ max 1 (7 * C1) := le_trans zero_le_one (le_max_left _ _)
      nlinarith
    have hB : 0 ≤ aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
        (aux_rem_resolved_meshes_bref M H omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
          (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by
      have := hnn (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2)))
      positivity
    calc 7 * (C1 * (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0) *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M H omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)))
        = (7 * C1) * (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M H omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))) := by ring
      _ ≤ (max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ))) *
            (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M H omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))) := by
          gcongr
      _ ≤ max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) *
            (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I)
                (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M H omega N (1 - 1 + (k - 1))
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by
          rw [show 1 - 1 + (k - 1) = k - 1 by omega]
          have hK0 : 0 ≤ max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) *
              (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 := by positivity
          apply mul_le_mul_of_nonneg_left _ hK0
          have e : (aux_rem_resolved_meshes_bref M H omega N (k - 1)
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) =
            (aux_rem_resolved_meshes_bref M H omega N (k - 1)
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2) := by ring
          rw [e]
          linarith
      _ = _ := by rw [show 1 - 1 + (k - 1) = k - 1 by omega]
  · -- bad branch
    have hjk : 0 ≤ j + (k : ℤ) + (pl : ℤ) := by
      push_neg at hgood
      have : (N : ℤ) - k + 1 < (n : ℤ) + pl := by
        have : N - k + 1 < n + pl := hgood
        omega
      omega
    have hfac := aux_rem_resolved_meshes_bad_factor t0 (t0 * Real.log 3 + 1) ht0 (by linarith) j k
      pl hjk
    have hE0 := hnn (Metric.ball (aux_rem_resolved_meshes_center y I)
      (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2)))
    calc aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ j / 2))
        ≤ 1 * (aux_rem_resolved_meshes_energy
            (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
            (Metric.ball (aux_rem_resolved_meshes_center y I)
              (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
          (aux_rem_resolved_meshes_bref M H omega N (k - 1)
            (aux_rem_resolved_meshes_center y I))⁻¹ *
            Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by linarith
      _ ≤ (max 1 (7 * C1) * (Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) *
            (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0)) *
          (aux_rem_resolved_meshes_energy
            (cutoffPositiveCoefficient M H omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
            (Metric.ball (aux_rem_resolved_meshes_center y I)
              (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
          (aux_rem_resolved_meshes_bref M H omega N (k - 1)
            (aux_rem_resolved_meshes_center y I))⁻¹ *
            Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          have := le_max_left 1 (7 * C1)
          nlinarith
      _ = _ := by ring



theorem aux_rem_resolved_meshes_onestep_exists (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 : ℝ) (hLstar : 10 ≤ Lstar) (hRstar_lt : Rstar < 1 / (100 * Lstar))
    (ht0 : 0 < t0)
    (hfin : ∃ Kt C1 delta1 : ℝ,
      1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ Kt ∧ 0 ≤ C1 ∧ 0 < delta1 ∧
        aux_rem_resolved_meshes_finite_onestep d hd Lstar Rstar t0 Kt C1 delta1) :
    ∃ Kt Cstep c delta1 : ℝ,
      1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ Kt ∧ 1 ≤ Cstep ∧ 0 < c ∧
        0 < delta1 ∧ aux_rem_resolved_meshes_onestep d hd Lstar Rstar t0 1 Kt Cstep c delta1 ∧
        aux_rem_resolved_meshes_onestep_trunc d hd Lstar Rstar t0 1 Kt Cstep c delta1 := by
  obtain ⟨Kt, C1, delta1, hKt, hC1, hdelta1, hF⟩ := hfin
  exact ⟨Kt, max 1 (7 * C1), t0 * Real.log 3 + 1, delta1, hKt, le_max_left _ _,
    by have := Real.log_pos (by norm_num : (1 : ℝ) < 3); positivity, hdelta1,
    aux_rem_resolved_meshes_onestep_of_finite d hd Lstar Rstar t0 hLstar hRstar_lt ht0 Kt C1
      delta1 hC1 hF,
    aux_rem_resolved_meshes_onestep_trunc_of_finite d hd Lstar Rstar t0 hLstar hRstar_lt ht0 Kt C1
      delta1 hC1 hF⟩

theorem aux_rem_resolved_meshes_of_onestep
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 eta etas p q : ℝ)
    (hLstar : 10 ≤ Lstar)
    (hRstar_pos : 0 < Rstar)
    (hRstar_lt : Rstar < 1 / (100 * Lstar))
    (hRstar_mem : Rstar ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2))
    (ht0_low : (d : ℝ) - 1 < t0)
    (ht0_high : t0 < (d : ℝ))
    (heta_pos : 0 < eta)
    (heta_lt : eta < t0 - ((d : ℝ) - 1))
    (hetas_pos : 0 < etas)
    (hetas_lt : etas < (d : ℝ) + 2 - t0)
    (hp : 1 ≤ p)
    (hpq : p ≤ q)
    (hdq_eta : (d : ℝ) < q * eta)
    (hres : ∃ Kt Cstep c delta1 : ℝ,
      1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ Kt ∧ 1 ≤ Cstep ∧ 0 < c ∧
        0 < delta1 ∧ aux_rem_resolved_meshes_onestep d hd Lstar Rstar t0 1 Kt Cstep c delta1 ∧
        aux_rem_resolved_meshes_onestep_trunc d hd Lstar Rstar t0 1 Kt Cstep c delta1) :
    ∃ J : ℕ, 1 ≤ J ∧
      ∃ Cstep c C delta0 Cp Kt : ℝ,
        1 ≤ Cstep ∧ 0 < c ∧ 0 < C ∧ 0 < delta0 ∧ 0 < Cp ∧
        1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ Kt ∧
        ∃ Ccount Cd : ℝ, 0 < Ccount ∧ 0 < Cd ∧
          (let Cat : ℕ → Type :=
            fun n =>
              (Fin d → Fin (3 ^ (n + J) + 1)) ×
                ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))
           ∀ n : ℕ, (Nat.card (Cat n) : ℝ) ≤
              Ccount * ((n : ℝ) + Ccount) ^ Cd *
                (3 : ℝ) ^ ((d : ℝ) * n)) ∧
        ∃ Cmom Crate : ℝ, 0 < Cmom ∧ 0 < Crate ∧
          ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
          (E : in_J d)
          (Poinc : in_poincare d hd E)
          (Ext : in_extension d hd E)
          (Rm : in_responses d M)
          (Sreg : in_6_16 d M)
          (It : in_iteration d M E Sreg)
          (hdet : @lane4_deterministic_good_scale_input d
            ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
          InfraredAdmissible M H → M.delta ≤ delta0 →
          let alpha : ℝ := (t0 + 2 - (d : ℝ)) / 2
          let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
          let Q : Opens (SpatialCoordinates d) := unitNeumannCube d
          let K : Set (SpatialCoordinates d) := closure (Q : Set (SpatialCoordinates d))
          let R : ℕ → ℝ := fun k => (3 : ℝ) ^ (-(k : ℤ)) / 2
          let relabel : ℕ → BilateralField d → BilateralField d :=
            fun N omega j =>
              ContinuousMap.compRightContinuousMap ℝ
                (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
                  continuous_const.smul continuous_id⟩ :
                  C(SpatialCoordinates d, SpatialCoordinates d))
                (omega (j - (N : ℤ)))
          let Grid : ℕ → Type :=
            fun n => Fin d → Fin (3 ^ (n + J) + 1)
          let Cat : ℕ → Type :=
            fun n =>
              (Fin d → Fin (3 ^ (n + J) + 1)) ×
                ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))
          let ygrid : (n : ℕ) → Grid n → SpatialCoordinates d :=
            fun n a i => (a i : ℝ) * (3 : ℝ) ^ (-(((n + J : ℕ) : ℤ)))
          let active : (n : ℕ) → Cat n → Fin (d + 1) → Set (Fin d) :=
            fun n pi i => {a : Fin d | (pi.2.2.symm a).val < i.val}
          let center : SpatialCoordinates d → Set (Fin d) → SpatialCoordinates d :=
            fun y I a => if a ∈ I then (if y a ≤ 1 / 2 then 0 else 1) else y a
          let k : (n : ℕ) → Cat n → Fin (d + 1) → ℕ :=
            fun n pi i => (pi.2.1 i).val
          let allowance : (N n : ℕ) → Cat n → Fin (d + 1) → BilateralField d → ℝ :=
            fun N n pi i omega =>
              if k n pi i ≤ N then
                (It.prefixLen
                    ((3 : ℝ) ^ (N : ℤ) • center (ygrid n pi.1) (active n pi i))
                    (1 - (1 - alpha) / Kt) (N - k n pi i + J) (relabel N omega) : ℝ) +
                  (J : ℝ) + (It.k : ℝ) + 5
              else 0
          let Z : (N n : ℕ) → Cat n → BilateralField d → ℝ :=
            fun N n pi omega =>
              Cstep ^ (d + 1) *
                Real.exp (c * ∑ i : Fin (d + 1), allowance N n pi i omega)
          let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
            fun k omega x =>
              H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
          let spoint : (N k : ℕ) → BilateralField d → SpatialCoordinates d → ℝ :=
            fun N k omega x =>
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
                Real.exp (G k omega x - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
          let b : (N k : ℕ) → BilateralField d → SpatialCoordinates d → ℝ :=
            fun N k omega z =>
              (volume.real (Metric.ball z (R k)))⁻¹ *
                ∫ x in Metric.ball z (R k), spoint N k omega x
          let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
            fun k omega y =>
              sSup {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
                ∃ x' ∈ Metric.closedBall y (3 * R k),
                  v = |G k omega x - G k omega x'|}
          let Vstat : (N k : ℕ) → BilateralField d → Grid k → ℝ :=
            fun N k omega a =>
              Real.exp (osc k omega (ygrid k a)) *
                (spoint N k omega (ygrid k a) +
                  (spoint N k omega (ygrid k a))⁻¹)
          (∀ (N k : ℕ), k ≤ N → ∀ y ∈ K,
            Integrable (fun omega => (spoint N k omega y)^q +
              (spoint N k omega y)^(-q)) P ∧
            (∫ omega, (spoint N k omega y)^q +
              (spoint N k omega y)^(-q) ∂P) ≤
              Cmom * Real.exp (Crate * (q + q^2) * M.delta^2 * (k : ℝ)) ∧
            MemLp (fun omega => spoint N k omega y) (ENNReal.ofReal q) P ∧
            MemLp (fun omega => (spoint N k omega y)⁻¹)
              (ENNReal.ofReal q) P) ∧
          ∃ U V : ℕ → BilateralField d → ℝ,
              (∀ N, Measurable (U N)) ∧
              (∀ N, Measurable (V N)) ∧
              (∀ N omega, 0 ≤ U N omega) ∧
              (∀ N omega, 0 ≤ V N omega) ∧
              (∀ N, MemLp (U N) (ENNReal.ofReal p) P) ∧
              (∀ N, MemLp (V N) (ENNReal.ofReal p) P) ∧
              (∀ N, eLpNorm (U N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cp) ∧
              (∀ N, eLpNorm (V N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cp) ∧
              ∀ᵐ omega ∂P, ∀ N : ℕ,
                IsLUB {v : ℝ | ∃ n : ℕ, ∃ pi : Cat n,
                  v = (3 : ℝ) ^ (-eta * (n : ℝ)) * Z N n pi omega} (U N omega) ∧
                IsLUB {v : ℝ | ∃ k : ℕ, k ≤ N ∧ ∃ a : Grid k,
                  v = (R k) ^ etas * Vstat N k omega a} (V N omega) ∧
                (∀ k : ℕ, k ≤ N → ∀ z ∈ K,
                  b N k omega z + (b N k omega z)⁻¹ ≤
                    V N omega * (R k) ^ (-etas)) ∧
                (∀ k : ℕ, k ≤ N → ∀ z ∈ K,
                  ∃ a : Grid k,
                    dist z (ygrid k a) ≤ R k ∧
                    Real.exp (-osc k omega (ygrid k a)) *
                        spoint N k omega (ygrid k a) ≤ b N k omega z ∧
                    b N k omega z ≤
                      Real.exp (osc k omega (ygrid k a)) *
                        spoint N k omega (ygrid k a)) ∧
                let a : PositiveCoefficient Q :=
                  cutoffPositiveCoefficient M H omega N
                    (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
                ∀ f : SpatialCoordinates d → ℝ,
                  AEMeasurable f (volume.restrict (Q : Set (SpatialCoordinates d))) →
                  ∀ Kf : ℝ, 0 ≤ Kf →
                    (∀ᵐ y ∂volume.restrict (Q : Set (SpatialCoordinates d)),
                      |f y| ≤ Kf) →
                    (∫ y in (Q : Set (SpatialCoordinates d)), f y) = 0 →
                    ∀ u : meanZeroSobolevGraph Q, SolvesNeumann a f u →
                      let cube : SpatialCoordinates d → ℝ → Set (SpatialCoordinates d) :=
                        fun x r => {y | ∀ i : Fin d, |y i - x i| < r / 2}
                      let energy : Set (SpatialCoordinates d) → ℝ :=
                        fun A =>
                          ∫ y in A ∩ (Q : Set (SpatialCoordinates d)),
                            a.val y * ∑ i : Fin d,
                              (((sobolevGradient (u : SobolevData Q)) i :
                                SpatialCoordinates d → ℝ) y) ^ 2
                      ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
                        ∀ r : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ r →
                          energy (cube x r) ≤
                            C * U N omega * r ^ (t0 - eta) *
                              (energy (Q : Set (SpatialCoordinates d)) +
                                V N omega * Kf ^ 2)
      := by
  obtain ⟨Kt, Cstep, c, delta1, hKt, hCstep, hc, hdelta1, hone, hone_t⟩ := hres
  have hq1 : 1 ≤ q := hp.trans hpq
  have href0 := aux_lane4_reference_mesh_statistic_adm d 1 hd le_rfl p q etas hp hq1 hetas_pos
  obtain ⟨qref, hpqref, hqqref, hgapref, dref, Cmom, Crate, Cosc, CV, hdref, hCmom, hCrate,
    hCosc, hCV, hdref1, hbudget, href⟩ := href0
  obtain ⟨cC, c1, c2, hcC1, -, -, hconst⟩ := aux_prop_folded_iteration_carrier_constants d hd
  have hreg := lane4_regularity_mesh_statistic d 1 le_rfl
  obtain ⟨Ccount, Cd, hCcount, hCd, hcard, -⟩ := hreg
  have hKt1 : 1 ≤ Kt := by
    have h3 : (1 : ℝ) < (3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) :=
      Real.one_lt_rpow (by norm_num) (by norm_num)
    have : 0 ≤ 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) :=
      div_nonneg (by positivity) (by linarith)
    linarith
  have hα1 : 0 < 1 - (t0 + 2 - (d : ℝ)) / 2 := by linarith
  have haT : 1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt < 1 := by
    have : 0 < (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt := div_pos hα1 (by linarith)
    linarith
  have haThalf : 1 / 2 ≤ 1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt := by
    have h1 : (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt ≤ 1 - (t0 + 2 - (d : ℝ)) / 2 :=
      div_le_self hα1.le hKt1
    linarith
  have hr1 : 1 ≤ ((d : ℝ) + 1) * q := by
    have : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    nlinarith
  have hr0 : 0 < ((d : ℝ) + 1) * q := by linarith
  have hδfacts := aux_rem_resolved_meshes_delta_facts cC
    (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (((d : ℝ) + 1) * q) c hcC1 haT hr0 hc
  rcases hδfacts with ⟨hδm, hδall⟩
  have hK1 : 1 ≤ Real.exp (c * (((1 : ℕ) : ℝ) + 26)) *
      (Real.exp (c * (cC + 1)) * (1 + cC)) := by
    have h1 : 1 ≤ Real.exp (c * (((1 : ℕ) : ℝ) + 26)) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ Real.exp (c * (cC + 1)) := Real.one_le_exp (by positivity)
    have h3 : 1 ≤ Real.exp (c * (cC + 1)) * (1 + cC) :=
      one_le_mul_of_one_le_of_one_le h2 (by linarith)
    exact one_le_mul_of_one_le_of_one_le h1 h3
  refine ⟨1, le_rfl, Cstep, c,
    2 ^ d + (36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 * 3 ^ eta * 2 ^ t0 *
      (Rstar ^ (-t0) + (d : ℝ) + 1),
    min dref (min delta1 (min (1 / 2) (min (1 / cC)
      (min (((1 - (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt)) / cC) ^ 2)
        ((1 - (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt)) ^ 2 /
          (2 * (((d : ℝ) + 1) * q) * c * cC)))))),
    max 1 (max (aux_rem_resolved_meshes_Rbound d 1 eta q Cstep
      (Real.exp (c * (((1 : ℕ) : ℝ) + 26)) * (Real.exp (c * (cC + 1)) * (1 + cC)))).toReal CV),
    Kt, hCstep, hc, aux_lane4_two_mesh_energy_bound_Cpos d Lstar Rstar t0 eta hLstar hRstar_pos,
    lt_min hdref (lt_min hdelta1 hδm), lt_of_lt_of_le one_pos (le_max_left _ _), hKt,
    Ccount, Cd, by linarith, hCd, hcard, Cmom, Crate, hCmom, hCrate, ?_⟩
  intro M E Poinc Ext Rm Sreg It hdet H hH hδ
  intro alpha P Q K R relabel Grid Cat ygrid active center k allowance Z G spoint b osc Vstat
  have hδref : M.delta ≤ dref := hδ.trans (min_le_left _ _)
  have hδ1 : M.delta ≤ delta1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδm' := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδf := hδall M.delta hδpos hδm'
  rcases hδf with ⟨hdC, haTr, hrate⟩
  have hCeq : It.C = cC := (hconst E M Sreg It).1
  have hαT : (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) ∈ It.alphaRange := by
    rw [It.alphaRange_eq, hCeq]
    exact ⟨haThalf, haTr⟩
  have hδIt : M.delta ≤ It.C⁻¹ := by rw [hCeq]; exact hdC
  have hR := href M Rm H hH hδref
  rcases hR with ⟨-, -, hmesh, hmom, -, V, hVm, hV0, hVmem, hVnorm, hVae⟩
  have hKsub : K ⊆ {x : SpatialCoordinates d | ∀ i, 0 ≤ x i ∧ x i ≤ 1} :=
    aux_rem_resolved_meshes_closure_subset d
  have hBmom : ∀ (N n : ℕ) (pi : Cat n) (i : Fin (d + 1)),
      MemLp (fun om => Real.exp (c * allowance N n pi i om))
        (ENNReal.ofReal (((d : ℝ) + 1) * q)) P ∧
      eLpNorm (fun om => Real.exp (c * allowance N n pi i om))
        (ENNReal.ofReal (((d : ℝ) + 1) * q)) P ≤
        ENNReal.ofReal (Real.exp (c * (((1 : ℕ) : ℝ) + 26)) *
          (Real.exp (c * (cC + 1)) * (1 + cC))) :=
    fun N n pi i => aux_rem_resolved_meshes_allowance_moment It cC hCeq hcC1 _ hαT hδIt c
      (((d : ℝ) + 1) * q) hc hr1 hrate 1
      ((3 : ℝ) ^ (N : ℤ) • center (ygrid n pi.1) (active n pi i)) N (k n pi i)
  have hB0 : ∀ (N n : ℕ) (pi : Cat n) (i : Fin (d + 1)) (om : BilateralField d),
      0 ≤ allowance N n pi i om := by
    intro N n pi i om
    simp only [allowance]
    split_ifs <;> positivity
  have hU := aux_rem_resolved_meshes_regularity d 1 P p q eta hp hpq heta_pos hdq_eta Cstep c
    (Real.exp (c * (((1 : ℕ) : ℝ) + 26)) * (Real.exp (c * (cC + 1)) * (1 + cC)))
    hCstep hc.le hK1 (fun N n pi i om => allowance N n pi i om) hB0
    (fun N n pi i => (hBmom N n pi i).1) (fun N n pi i => (hBmom N n pi i).2)
  rcases hU with ⟨U, hUm, hU0, hUmem, hUnorm, hUae, hRb⟩
  refine ⟨fun N k' hk y hy => hmom q ⟨hq1, by linarith⟩ N k' hk y (hKsub hy),
    U, V, hUm, hVm, hU0, hV0, hUmem, hVmem, ?_, ?_, ?_⟩
  · intro N
    refine (hUnorm N).trans (le_trans (le_of_eq (ENNReal.ofReal_toReal hRb).symm) ?_)
    exact ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_right _ _))
  · intro N
    exact (hVnorm N).trans (ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans (le_max_right _ _)))
  rcases hH with hH | ⟨L0, rfl⟩
  · filter_upwards [aux_rem_resolved_meshes_physical_cutoff_bridge_unitNeumannCube d M Sreg H hH, hUae, hVae, hH.2] with om hphys hUlub hVlub hIR
    intro N
    refine ⟨hUlub N, (hVlub N).1, fun k' hk z hz => (hVlub N).2 k' hk z (hKsub hz), ?_, ?_⟩
    · intro k' hk z hz
      rcases hmesh k' z (hKsub hz) with ⟨a, hdist, -, -, hcmp⟩
      refine ⟨a, hdist.trans ?_, hcmp N hk om⟩
      have h3 : (3 : ℝ) ^ (-(((k' + 1 : ℕ) : ℤ))) = (3 : ℝ) ^ (-(k' : ℤ)) / 3 := by
        rw [show (-(((k' + 1 : ℕ) : ℤ))) = -(k' : ℤ) - 1 by push_cast; ring,
          zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
      change (3 : ℝ) ^ (-(((k' + 1 : ℕ) : ℤ))) ≤ (3 : ℝ) ^ (-(k' : ℤ)) / 2
      rw [h3]
      have : (0 : ℝ) < (3 : ℝ) ^ (-(k' : ℤ)) := zpow_pos (by norm_num) _
      linarith
    · intro a f hf Kf hKf hfb hf0 u hu cube energy x hx r hr
      have hsum : ∀ (n : ℕ) (g : Fin d → Fin (3 ^ (n + 1) + 1))
          (dep : Fin (d + 1) → Fin (n + 1 + 1)) (σ : Equiv.Perm (Fin d)),
          (∑ j : Fin (d + 1), aux_rem_resolved_meshes_B
            (fun z m => It.prefixLen z (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) m
              (aux_rem_resolved_meshes_relabel N om)) N 1 It.k
            (fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))))
            (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val)) (dep j).val) =
          ∑ j : Fin (d + 1), allowance N n (g, (dep, σ)) j om := by
        intro n g dep σ
        apply Finset.sum_congr rfl
        intro j _
        simp only [aux_rem_resolved_meshes_B, allowance, k, center, ygrid, active, relabel, alpha,
          aux_rem_resolved_meshes_center_filter]
        rfl
      have hUcore : ∀ (n : ℕ) (g : Fin d → Fin (3 ^ (n + 1) + 1))
          (dep : Fin (d + 1) → Fin (n + 1 + 1)) (σ : Equiv.Perm (Fin d)),
          (3 : ℝ) ^ (-eta * (n : ℝ)) * (Cstep ^ (d + 1) * Real.exp (c * ∑ j : Fin (d + 1),
            aux_rem_resolved_meshes_B
              (fun z m => It.prefixLen z (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) m
                (aux_rem_resolved_meshes_relabel N om)) N 1 It.k
              (fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))))
              (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val)) (dep j).val)) ≤
            U N om := by
        intro n g dep σ
        rw [hsum n g dep σ]
        exact (hUlub N).1 ⟨n, (g, (dep, σ)), rfl⟩
      exact aux_rem_resolved_meshes_energy_app d hd Lstar Rstar t0 eta etas hLstar hRstar_pos
        hRstar_lt hRstar_mem ht0_low ht0_high heta_pos heta_lt hetas_pos hetas_lt 1 le_rfl Cstep c
        hCstep hc.le M H om N a u Kf
        (fun z m => It.prefixLen z (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) m
          (aux_rem_resolved_meshes_relabel N om)) It.k
        (hone M E Poinc Ext Sreg It hdet H hδ1 om hIR N (hphys N) f hf Kf hKf hfb hf0 u hu)
        (U N om) hUcore (V N om) (fun k' hk z hz => (hVlub N).2 k' hk z hz) x hx r hr
  · filter_upwards [hUae, hVae] with om hUlub hVlub
    intro N
    refine ⟨hUlub N, (hVlub N).1, fun k' hk z hz => (hVlub N).2 k' hk z (hKsub hz), ?_, ?_⟩
    · intro k' hk z hz
      rcases hmesh k' z (hKsub hz) with ⟨a, hdist, -, -, hcmp⟩
      refine ⟨a, hdist.trans ?_, hcmp N hk om⟩
      have h3 : (3 : ℝ) ^ (-(((k' + 1 : ℕ) : ℤ))) = (3 : ℝ) ^ (-(k' : ℤ)) / 3 := by
        rw [show (-(((k' + 1 : ℕ) : ℤ))) = -(k' : ℤ) - 1 by push_cast; ring,
          zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
      change (3 : ℝ) ^ (-(((k' + 1 : ℕ) : ℤ))) ≤ (3 : ℝ) ^ (-(k' : ℤ)) / 2
      rw [h3]
      have : (0 : ℝ) < (3 : ℝ) ^ (-(k' : ℤ)) := zpow_pos (by norm_num) _
      linarith
    · intro a f hf Kf hKf hfb hf0 u hu cube energy x hx r hr
      have hsum : ∀ (n : ℕ) (g : Fin d → Fin (3 ^ (n + 1) + 1))
          (dep : Fin (d + 1) → Fin (n + 1 + 1)) (σ : Equiv.Perm (Fin d)),
          (∑ j : Fin (d + 1), aux_rem_resolved_meshes_B
            (fun z m => It.prefixLen z (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) m
              (aux_rem_resolved_meshes_relabel N om)) N 1 It.k
            (fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))))
            (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val)) (dep j).val) =
          ∑ j : Fin (d + 1), allowance N n (g, (dep, σ)) j om := by
        intro n g dep σ
        apply Finset.sum_congr rfl
        intro j _
        simp only [aux_rem_resolved_meshes_B, allowance, k, center, ygrid, active, relabel, alpha,
          aux_rem_resolved_meshes_center_filter]
        rfl
      have hUcore : ∀ (n : ℕ) (g : Fin d → Fin (3 ^ (n + 1) + 1))
          (dep : Fin (d + 1) → Fin (n + 1 + 1)) (σ : Equiv.Perm (Fin d)),
          (3 : ℝ) ^ (-eta * (n : ℝ)) * (Cstep ^ (d + 1) * Real.exp (c * ∑ j : Fin (d + 1),
            aux_rem_resolved_meshes_B
              (fun z m => It.prefixLen z (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) m
                (aux_rem_resolved_meshes_relabel N om)) N 1 It.k
              (fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))))
              (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val)) (dep j).val)) ≤
            U N om := by
        intro n g dep σ
        rw [hsum n g dep σ]
        exact (hUlub N).1 ⟨n, (g, (dep, σ)), rfl⟩
      exact aux_rem_resolved_meshes_energy_app d hd Lstar Rstar t0 eta etas hLstar hRstar_pos
        hRstar_lt hRstar_mem ht0_low ht0_high heta_pos heta_lt hetas_pos hetas_lt 1 le_rfl Cstep c
        hCstep hc.le M (fun om => infraredPartialSum om L0) om N a u Kf
        (fun z m => It.prefixLen z (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) m
          (aux_rem_resolved_meshes_relabel N om)) It.k
        (hone_t M E Poinc Ext Sreg It hdet L0 hδ1 om N f hf Kf hKf hfb hf0 u hu)
        (U N om) hUcore (V N om) (fun k' hk z hz => (hVlub N).2 k' hk z hz) x hx r hr

open scoped Distributions in
/-- **The divergence-form source on a root cube.**  A measurable bounded source `Fr` on the root
cube `Q_ρ(z)` is written, on killed tests, as `-⟨G, ∇φ⟩` for a half-Hölder field `G` (from
`lem_primitive` at scale `dρ`, applied to `1_{Q_ρ(z)} Fr`), with `[G]_{1/2} ≤ Ch (dρ)^{1/2} sup|Fr|`.
The constant `Ch` is dimensional and chosen before the cube. -/
theorem aux_rem_resolved_meshes_fin_source (d : ℕ) (hd : 2 ≤ d) :
    ∃ Ch : ℝ, 0 ≤ Ch ∧ ∀ (z : SpatialCoordinates d) (ρ : ℝ) (hρ : 0 < ρ)
      (Fr : SpatialCoordinates d → ℝ), Measurable Fr → ∀ MF : ℝ, 0 ≤ MF →
      (∀ x, |Fr x| ≤ MF) →
      ∃ (g : SpatialCoordinates d → Fin d → ℝ) (hgrad : HilbertGradient (centeredCube z ρ hρ)),
        SubdiffusiveProcess.CoarseGrainingVocab.MemHolder
          (centeredCube z ρ hρ : Set (SpatialCoordinates d)) (1 / 2) g ∧
        (∀ i : Fin d, ((hgrad i : SpatialCoordinates d → ℝ))
          =ᵐ[volume.restrict (centeredCube z ρ hρ : Set (SpatialCoordinates d))]
            fun x => g x i) ∧
        (∀ φ : killedSobolevGraph (centeredCube z ρ hρ),
          (∫ x in (centeredCube z ρ hρ : Set (SpatialCoordinates d)),
              Fr x * (φ : SobolevData (centeredCube z ρ hρ)).1 x) =
            -inner ℝ hgrad (subspaceGradient (killedSobolevGraph (centeredCube z ρ hρ)) φ)) ∧
        halfHolderSeminorm (centeredCube z ρ hρ : Set (SpatialCoordinates d)) g ≤
          Ch * Real.sqrt ((d : ℝ) * ρ) * MF := by
  obtain ⟨Ch, hCh, hprim⟩ := aux_rem_resolved_meshes_primitive d hd
  refine ⟨Ch, hCh.le, fun z ρ hρ Fr hFr MF hMF hFb => ?_⟩
  have hΩm : MeasurableSet (centeredCube z ρ hρ : Set (SpatialCoordinates d)) :=
    (centeredCube z ρ hρ).isOpen.measurableSet
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hR : 0 < (d : ℝ) * ρ := by positivity
  have hfm : Measurable ((centeredCube z ρ hρ : Set (SpatialCoordinates d)).indicator Fr) :=
    hFr.indicator hΩm
  have hfb : ∀ x, ‖(centeredCube z ρ hρ : Set (SpatialCoordinates d)).indicator Fr x‖ ≤ MF := by
    intro x
    rw [Real.norm_eq_abs]
    by_cases hx : x ∈ (centeredCube z ρ hρ : Set (SpatialCoordinates d))
    · rw [Set.indicator_of_mem hx]; exact hFb x
    · rw [Set.indicator_of_notMem hx, abs_zero]; exact hMF
  have hfLp : MemLp ((centeredCube z ρ hρ : Set (SpatialCoordinates d)).indicator Fr)
      (⊤ : ENNReal) volume :=
    memLp_top_of_bound hfm.aestronglyMeasurable MF (Filter.Eventually.of_forall hfb)
  have hsupp : ∀ᵐ x ∂volume, x ∉ (closedCube z ((d : ℝ) * ρ) hR : Set (SpatialCoordinates d)) →
      (centeredCube z ρ hρ : Set (SpatialCoordinates d)).indicator Fr x = 0 := by
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hxΩ : x ∉ (centeredCube z ρ hρ : Set (SpatialCoordinates d)) := by
      intro hxΩ
      apply hx
      have h1 : dist x z < ρ / 2 := hxΩ
      change dist x z ≤ (d : ℝ) * ρ / 2
      nlinarith
    rw [Set.indicator_of_notMem hxΩ]
  obtain ⟨g, hgweak, hgpt⟩ := hprim ((d : ℝ) * ρ) hR z _ hfLp hsupp
  have hess : (eLpNormEssSup ((centeredCube z ρ hρ : Set (SpatialCoordinates d)).indicator Fr)
      volume).toReal ≤ MF :=
    ENNReal.toReal_le_of_le_ofReal hMF
      (eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall hfb))
  have hK0 : 0 ≤ Ch * Real.sqrt ((d : ℝ) * ρ) *
      (eLpNormEssSup ((centeredCube z ρ hρ : Set (SpatialCoordinates d)).indicator Fr)
        volume).toReal :=
    mul_nonneg (mul_nonneg hCh.le (Real.sqrt_nonneg _)) ENNReal.toReal_nonneg
  obtain ⟨hgmem, hHol, hsemi⟩ := aux_rem_resolved_meshes_holder_facts z ρ hρ ((d : ℝ) * ρ) hR
    le_rfl g _ hK0 hgpt
  have hFrmem : MemLp Fr 2 (volume.restrict (centeredCube z ρ hρ : Set (SpatialCoordinates d))) := by
    refine MemLp.of_bound hFr.aestronglyMeasurable MF (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact hFb x
  obtain ⟨hgrad, hgae, hid⟩ := aux_rem_resolved_meshes_killed_identity (centeredCube z ρ hρ) g
    hgmem Fr hFrmem (fun ψ => hgweak ψ ψ.contDiff ψ.hasCompactSupport)
  refine ⟨g, hgrad, hHol, hgae, hid, hsemi.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hess (mul_nonneg hCh.le (Real.sqrt_nonneg _))

/-- Scale identities of the root cube at depth `k ≤ N`, side `3^{N-k+1}`. -/
theorem aux_rem_resolved_meshes_fin_scales (N k : ℕ) (hkN : k ≤ N) :
    (3 : ℝ) ^ (N - k + 1) = (3 : ℝ) ^ (N : ℤ) * (3 * (3 : ℝ) ^ (-((k : ℤ)))) := by
  rw [← zpow_natCast, show (((N - k + 1 : ℕ)) : ℤ) = (N : ℤ) + (1 + -(k : ℤ)) by omega,
    zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]

theorem aux_rem_resolved_meshes_fin_Rk (k : ℕ) (hk1 : 1 ≤ k) :
    3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) < 1 := by
  have h : (3 : ℝ) ^ (-((k : ℤ))) ≤ (3 : ℝ) ^ (-1 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
  rw [zpow_neg_one] at h
  linarith

/-- **The finite-cutoff one-step residual, proved.**  For `t₀ ∈ (d-1,d)`, the folded one-center
package (`prop_folded_iteration`, carrier-uniform), transported to `Q` by the Neumann dilation,
`lem_even` and the root-cube restriction, with the divergence-form source of `lem_primitive`, gives
`aux_rem_resolved_meshes_finite_onestep` with `Kt` the folded allowance factor. -/
theorem aux_rem_resolved_meshes_finite_onestep_holds (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 : ℝ) (hLstar : 10 ≤ Lstar) (ht0_low : (d : ℝ) - 1 < t0)
    (ht0_high : t0 < (d : ℝ)) :
    ∃ Kt C1 delta1 : ℝ,
      1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ Kt ∧ 0 ≤ C1 ∧ 0 < delta1 ∧
        aux_rem_resolved_meshes_finite_onestep d hd Lstar Rstar t0 Kt C1 delta1 := by
  obtain ⟨Cf, Kf, hCf, hKf, hfold⟩ := aux_rem_resolved_meshes_folded_uniform_all d hd
  obtain ⟨Ch, hCh, hsrc⟩ := aux_rem_resolved_meshes_fin_source d hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hα1 : (t0 + 2 - (d : ℝ)) / 2 < 1 := by linarith
  have hα2 : 1 / 2 ≤ (t0 + 2 - (d : ℝ)) / 2 := by linarith
  have hαeq : 2 * (1 - (t0 + 2 - (d : ℝ)) / 2) = (d : ℝ) - t0 := by ring
  have ht0 : 0 ≤ t0 := by linarith
  have h1α : 0 < 1 - (t0 + 2 - (d : ℝ)) / 2 := by linarith
  refine ⟨Kf, 2 * Cf ^ 2 * max 1 (Ch ^ 2 * d * 6 ^ (d + 2)),
    min (min (1 / 2) (((1 - (t0 + 2 - (d : ℝ)) / 2) / Cf) ^ 2)) Cf⁻¹, hKf,
    mul_nonneg (by positivity) (le_trans zero_le_one (le_max_left _ _)),
    lt_min (lt_min (by norm_num) (by positivity)) (inv_pos.mpr hCf), ?_⟩
  intro M E Poinc Ext Sreg It hdet hδ omega N L cF hcF a ha f hf Kf0 hKf0 hfb hf0 u hu y hy I n k
    hk1 hkN _hRkR _hn8 hI hwin
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδC : M.delta ≤ Cf⁻¹ := hδ.trans (min_le_right _ _)
  have hαr := aux_rem_resolved_meshes_alpha_range Cf ((t0 + 2 - (d : ℝ)) / 2) hCf hα1 hα2
    M.delta hδpos (hδ.trans (min_le_left _ _))
  -- the source: a measurable everywhere-bounded representative, same weak equation
  obtain ⟨f2, hf2m, hf2b, hff2⟩ := aux_rem_resolved_meshes_clamp f hf Kf0 hKf0 hfb
  have hf20 : (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f2 y) = 0 := by
    rw [← hf0]; exact integral_congr_ae hff2.symm
  have hu2 : ∀ ψ : weakSobolevGraph (unitNeumannCube d),
      sobolevCoefficientForm a (u : SobolevData (unitNeumannCube d)) ψ =
        ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
          f2 x * (ψ : SobolevData (unitNeumannCube d)).1 x := by
    intro ψ
    rw [hu ψ]
    apply integral_congr_ae
    filter_upwards [hff2] with x hx
    rw [hx]
  -- scales
  have hl : (0 : ℝ) < (3 : ℝ) ^ (N : ℤ) := zpow_pos (by norm_num) _
  have hR : (0 : ℝ) < (3 : ℝ) ^ (N - k + 1) := by positivity
  have hRk : (0 : ℝ) < (3 : ℝ) ^ (-((k : ℤ))) / 2 := by positivity
  have h3m := aux_rem_resolved_meshes_fin_scales N k hkN
  have hρeq : (3 : ℝ) ^ (N - k + 1) / 2 =
      (3 : ℝ) ^ (N : ℤ) * (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2)) := by
    rw [h3m]; ring
  obtain ⟨fc, ut, hfc, hueq, hE⟩ := aux_rem_resolved_meshes_root_package Sreg (N + L)
    (aux_rem_resolved_meshes_relabel N omega) ((3 : ℝ) ^ (N : ℤ)) hl cF hcF a ha f2 hf2m Kf0
    hKf0 hf2b hf20 u hu2 y hy I Lstar ((3 : ℝ) ^ (-((k : ℤ))) / 2) hLstar hRk
    (aux_rem_resolved_meshes_fin_Rk k hk1) hI ((3 : ℝ) ^ (N - k + 1)) hR hρeq
  -- the divergence-form source on the root cube
  have hFrm : Measurable (fun x : SpatialCoordinates d => ((cF * (3 : ℝ) ^ (N : ℤ))⁻¹ *
      f2 (((3 : ℝ) ^ (N : ℤ))⁻¹ • coordinateFold ((3 : ℝ) ^ (N : ℤ) •
        aux_rem_resolved_meshes_center y I) I (aux_rem_resolved_meshes_faceSet y I) x))) :=
    measurable_const.mul (hf2m.comp ((continuous_const_smul _).comp
      (coordinateFold_continuous _ _ _)).measurable)
  have hMF : 0 ≤ (cF * (3 : ℝ) ^ (N : ℤ))⁻¹ * Kf0 := by positivity
  have hFrb : ∀ x : SpatialCoordinates d, |(cF * (3 : ℝ) ^ (N : ℤ))⁻¹ *
      f2 (((3 : ℝ) ^ (N : ℤ))⁻¹ • coordinateFold ((3 : ℝ) ^ (N : ℤ) •
        aux_rem_resolved_meshes_center y I) I (aux_rem_resolved_meshes_faceSet y I) x)| ≤
      (cF * (3 : ℝ) ^ (N : ℤ))⁻¹ * Kf0 := by
    intro x
    rw [abs_mul, abs_of_pos (inv_pos.mpr (mul_pos hcF hl))]
    exact mul_le_mul_of_nonneg_left (hf2b _) (by positivity)
  obtain ⟨g, hgrad, hHol, hgae, hid, hGb⟩ := hsrc ((3 : ℝ) ^ (N : ℤ) •
    aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ (N - k + 1)) hR _ hFrm _ hMF hFrb
  have hweq : ∀ φ : killedSobolevGraph (centeredCube ((3 : ℝ) ^ (N : ℤ) •
      aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ (N - k + 1)) hR),
      sobolevCoefficientForm fc (ut : SobolevData (centeredCube ((3 : ℝ) ^ (N : ℤ) •
          aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ (N - k + 1)) hR))
        (φ : SobolevData (centeredCube ((3 : ℝ) ^ (N : ℤ) •
          aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ (N - k + 1)) hR)) =
      -inner ℝ hgrad (subspaceGradient (killedSobolevGraph (centeredCube ((3 : ℝ) ^ (N : ℤ) •
          aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ (N - k + 1)) hR)) φ) :=
    fun φ => (hueq φ).trans (hid φ)
  -- the prefix window
  have hmL : N - k + 1 ≤ N + L := by omega
  have hnm : n ≤ N - k + 1 := by omega
  have hnz : (n : ℤ) ≤ ((N - k + 1 : ℕ) : ℤ) - (It.prefixLen ((3 : ℝ) ^ (N : ℤ) •
      aux_rem_resolved_meshes_center y I) (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kf) (N - k + 1)
      (aux_rem_resolved_meshes_relabel N omega) : ℤ) := by
    have h := hwin
    omega
  have hcore := hfold M E Poinc Ext Sreg It hdet hδC ((t0 + 2 - (d : ℝ)) / 2) hαr (N + L)
    (N - k + 1) n ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I) hR
    (aux_rem_resolved_meshes_relabel N omega) I (aux_rem_resolved_meshes_faceSet y I) hmL hnm hnz
    fc hfc g hgrad ut hHol hgae hweq
  -- unfold the normalized norms through the root-cube energy identity
  have hn3 : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hnρ : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ (N - k + 1) := pow_le_pow_right₀ (by norm_num) hnm
  have hEs := hE ((3 : ℝ) ^ n) hn3 hnρ
  have hE3 := hE ((3 : ℝ) ^ (N - k + 1)) hR le_rfl
  have hvol : ∀ (r : ℝ) (hr : 0 < r), volume.real (centeredCube ((3 : ℝ) ^ (N : ℤ) •
      aux_rem_resolved_meshes_center y I) r hr : Set (SpatialCoordinates d)) = r ^ d := by
    intro r hr
    rw [measureReal_def, centeredCube_volume, ENNReal.toReal_ofReal (by positivity)]
  simp only [normalizedEnergyNorm] at hcore
  rw [hEs, hE3, hvol, hvol] at hcore
  have hrad_s : (3 : ℝ) ^ n / (2 * (3 : ℝ) ^ (N : ℤ)) = (3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2 := by
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]; simp only [zpow_natCast]; ring
  have hrad_3 : (3 : ℝ) ^ (N - k + 1) / (2 * (3 : ℝ) ^ (N : ℤ)) =
      3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) := by
    rw [h3m]; field_simp
  rw [hrad_s, hrad_3] at hcore
  have hEnn : ∀ A : Set (SpatialCoordinates d), MeasurableSet A →
      0 ≤ aux_rem_resolved_meshes_energy a u A := fun A hA => by
    rw [aux_rem_resolved_meshes_energy_local a u A hA]; exact localGradientEnergy_nonneg _ _ _
  have hm : ((N - k + 1 : ℕ) : ℝ) = (N : ℝ) - k + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hkN, Nat.cast_one]
  have hG0 : 0 ≤ halfHolderSeminorm (centeredCube ((3 : ℝ) ^ (N : ℤ) •
      aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ (N - k + 1)) hR : Set (SpatialCoordinates d)) g :=
    Real.sSup_nonneg (fun v hv => by
      obtain ⟨x, -, y', -, -, rfl⟩ := hv
      positivity)
  exact aux_rem_resolved_meshes_final_arith d t0 ((t0 + 2 - (d : ℝ)) / 2) hαeq ht0 n (N - k + 1) N k
    I.card hm Cf Ch cF _ Kf0 _ _ _ hCf.le hCh hcF (It.ref_pos _ _ _ _) hKf0
    (hEnn _ measurableSet_ball) (hEnn _ measurableSet_ball) hG0
    (by simpa only [mul_assoc] using hcore) hGb

theorem aux_rem_resolved_meshes_adm
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 eta etas p q : ℝ)
    (hLstar : 10 ≤ Lstar)
    (hRstar_pos : 0 < Rstar)
    (hRstar_lt : Rstar < 1 / (100 * Lstar))
    (hRstar_mem : Rstar ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2))
    (ht0_low : (d : ℝ) - 1 < t0)
    (ht0_high : t0 < (d : ℝ))
    (heta_pos : 0 < eta)
    (heta_lt : eta < t0 - ((d : ℝ) - 1))
    (hetas_pos : 0 < etas)
    (hetas_lt : etas < (d : ℝ) + 2 - t0)
    (hp : 1 ≤ p)
    (hpq : p ≤ q)
    (hdq_eta : (d : ℝ) < q * eta) :
    ∃ J : ℕ, 1 ≤ J ∧
      ∃ Cstep c C delta0 Cp Kt : ℝ,
        1 ≤ Cstep ∧ 0 < c ∧ 0 < C ∧ 0 < delta0 ∧ 0 < Cp ∧
        1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ Kt ∧
        ∃ Ccount Cd : ℝ, 0 < Ccount ∧ 0 < Cd ∧
          (let Cat : ℕ → Type :=
            fun n =>
              (Fin d → Fin (3 ^ (n + J) + 1)) ×
                ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))
           ∀ n : ℕ, (Nat.card (Cat n) : ℝ) ≤
              Ccount * ((n : ℝ) + Ccount) ^ Cd *
                (3 : ℝ) ^ ((d : ℝ) * n)) ∧
        ∃ Cmom Crate : ℝ, 0 < Cmom ∧ 0 < Crate ∧
          ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
          (E : in_J d)
          (Poinc : in_poincare d hd E)
          (Ext : in_extension d hd E)
          (Rm : in_responses d M)
          (Sreg : in_6_16 d M)
          (It : in_iteration d M E Sreg)
          (hdet : @lane4_deterministic_good_scale_input d
            ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
          InfraredAdmissible M H → M.delta ≤ delta0 →
          let alpha : ℝ := (t0 + 2 - (d : ℝ)) / 2
          let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
          let Q : Opens (SpatialCoordinates d) := unitNeumannCube d
          let K : Set (SpatialCoordinates d) := closure (Q : Set (SpatialCoordinates d))
          let R : ℕ → ℝ := fun k => (3 : ℝ) ^ (-(k : ℤ)) / 2
          let relabel : ℕ → BilateralField d → BilateralField d :=
            fun N omega j =>
              ContinuousMap.compRightContinuousMap ℝ
                (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
                  continuous_const.smul continuous_id⟩ :
                  C(SpatialCoordinates d, SpatialCoordinates d))
                (omega (j - (N : ℤ)))
          let Grid : ℕ → Type :=
            fun n => Fin d → Fin (3 ^ (n + J) + 1)
          let Cat : ℕ → Type :=
            fun n =>
              (Fin d → Fin (3 ^ (n + J) + 1)) ×
                ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))
          let ygrid : (n : ℕ) → Grid n → SpatialCoordinates d :=
            fun n a i => (a i : ℝ) * (3 : ℝ) ^ (-(((n + J : ℕ) : ℤ)))
          let active : (n : ℕ) → Cat n → Fin (d + 1) → Set (Fin d) :=
            fun n pi i => {a : Fin d | (pi.2.2.symm a).val < i.val}
          let center : SpatialCoordinates d → Set (Fin d) → SpatialCoordinates d :=
            fun y I a => if a ∈ I then (if y a ≤ 1 / 2 then 0 else 1) else y a
          let k : (n : ℕ) → Cat n → Fin (d + 1) → ℕ :=
            fun n pi i => (pi.2.1 i).val
          let allowance : (N n : ℕ) → Cat n → Fin (d + 1) → BilateralField d → ℝ :=
            fun N n pi i omega =>
              if k n pi i ≤ N then
                (It.prefixLen
                    ((3 : ℝ) ^ (N : ℤ) • center (ygrid n pi.1) (active n pi i))
                    (1 - (1 - alpha) / Kt) (N - k n pi i + J) (relabel N omega) : ℝ) +
                  (J : ℝ) + (It.k : ℝ) + 5
              else 0
          let Z : (N n : ℕ) → Cat n → BilateralField d → ℝ :=
            fun N n pi omega =>
              Cstep ^ (d + 1) *
                Real.exp (c * ∑ i : Fin (d + 1), allowance N n pi i omega)
          let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
            fun k omega x =>
              H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
          let spoint : (N k : ℕ) → BilateralField d → SpatialCoordinates d → ℝ :=
            fun N k omega x =>
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
                Real.exp (G k omega x - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
          let b : (N k : ℕ) → BilateralField d → SpatialCoordinates d → ℝ :=
            fun N k omega z =>
              (volume.real (Metric.ball z (R k)))⁻¹ *
                ∫ x in Metric.ball z (R k), spoint N k omega x
          let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
            fun k omega y =>
              sSup {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
                ∃ x' ∈ Metric.closedBall y (3 * R k),
                  v = |G k omega x - G k omega x'|}
          let Vstat : (N k : ℕ) → BilateralField d → Grid k → ℝ :=
            fun N k omega a =>
              Real.exp (osc k omega (ygrid k a)) *
                (spoint N k omega (ygrid k a) +
                  (spoint N k omega (ygrid k a))⁻¹)
          (∀ (N k : ℕ), k ≤ N → ∀ y ∈ K,
            Integrable (fun omega => (spoint N k omega y)^q +
              (spoint N k omega y)^(-q)) P ∧
            (∫ omega, (spoint N k omega y)^q +
              (spoint N k omega y)^(-q) ∂P) ≤
              Cmom * Real.exp (Crate * (q + q^2) * M.delta^2 * (k : ℝ)) ∧
            MemLp (fun omega => spoint N k omega y) (ENNReal.ofReal q) P ∧
            MemLp (fun omega => (spoint N k omega y)⁻¹)
              (ENNReal.ofReal q) P) ∧
          ∃ U V : ℕ → BilateralField d → ℝ,
              (∀ N, Measurable (U N)) ∧
              (∀ N, Measurable (V N)) ∧
              (∀ N omega, 0 ≤ U N omega) ∧
              (∀ N omega, 0 ≤ V N omega) ∧
              (∀ N, MemLp (U N) (ENNReal.ofReal p) P) ∧
              (∀ N, MemLp (V N) (ENNReal.ofReal p) P) ∧
              (∀ N, eLpNorm (U N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cp) ∧
              (∀ N, eLpNorm (V N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cp) ∧
              ∀ᵐ omega ∂P, ∀ N : ℕ,
                IsLUB {v : ℝ | ∃ n : ℕ, ∃ pi : Cat n,
                  v = (3 : ℝ) ^ (-eta * (n : ℝ)) * Z N n pi omega} (U N omega) ∧
                IsLUB {v : ℝ | ∃ k : ℕ, k ≤ N ∧ ∃ a : Grid k,
                  v = (R k) ^ etas * Vstat N k omega a} (V N omega) ∧
                (∀ k : ℕ, k ≤ N → ∀ z ∈ K,
                  b N k omega z + (b N k omega z)⁻¹ ≤
                    V N omega * (R k) ^ (-etas)) ∧
                (∀ k : ℕ, k ≤ N → ∀ z ∈ K,
                  ∃ a : Grid k,
                    dist z (ygrid k a) ≤ R k ∧
                    Real.exp (-osc k omega (ygrid k a)) *
                        spoint N k omega (ygrid k a) ≤ b N k omega z ∧
                    b N k omega z ≤
                      Real.exp (osc k omega (ygrid k a)) *
                        spoint N k omega (ygrid k a)) ∧
                let a : PositiveCoefficient Q :=
                  cutoffPositiveCoefficient M H omega N
                    (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
                ∀ f : SpatialCoordinates d → ℝ,
                  AEMeasurable f (volume.restrict (Q : Set (SpatialCoordinates d))) →
                  ∀ Kf : ℝ, 0 ≤ Kf →
                    (∀ᵐ y ∂volume.restrict (Q : Set (SpatialCoordinates d)),
                      |f y| ≤ Kf) →
                    (∫ y in (Q : Set (SpatialCoordinates d)), f y) = 0 →
                    ∀ u : meanZeroSobolevGraph Q, SolvesNeumann a f u →
                      let cube : SpatialCoordinates d → ℝ → Set (SpatialCoordinates d) :=
                        fun x r => {y | ∀ i : Fin d, |y i - x i| < r / 2}
                      let energy : Set (SpatialCoordinates d) → ℝ :=
                        fun A =>
                          ∫ y in A ∩ (Q : Set (SpatialCoordinates d)),
                            a.val y * ∑ i : Fin d,
                              (((sobolevGradient (u : SobolevData Q)) i :
                                SpatialCoordinates d → ℝ) y) ^ 2
                      ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
                        ∀ r : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ r →
                          energy (cube x r) ≤
                            C * U N omega * r ^ (t0 - eta) *
                              (energy (Q : Set (SpatialCoordinates d)) +
                                V N omega * Kf ^ 2)
      := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  exact aux_rem_resolved_meshes_of_onestep d hd Lstar Rstar t0 eta etas p q hLstar hRstar_pos
    hRstar_lt hRstar_mem ht0_low ht0_high heta_pos heta_lt hetas_pos hetas_lt hp hpq hdq_eta
    (aux_rem_resolved_meshes_onestep_exists d hd Lstar Rstar t0 hLstar hRstar_lt (by linarith)
      (aux_rem_resolved_meshes_finite_onestep_holds d hd Lstar Rstar t0 hLstar ht0_low ht0_high))



theorem rem_resolved_meshes
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 eta etas p q : ℝ)
    (hLstar : 10 ≤ Lstar)
    (hRstar_pos : 0 < Rstar)
    (hRstar_lt : Rstar < 1 / (100 * Lstar))
    (hRstar_mem : Rstar ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2))
    (ht0_low : (d : ℝ) - 1 < t0)
    (ht0_high : t0 < (d : ℝ))
    (heta_pos : 0 < eta)
    (heta_lt : eta < t0 - ((d : ℝ) - 1))
    (hetas_pos : 0 < etas)
    (hetas_lt : etas < (d : ℝ) + 2 - t0)
    (hp : 1 ≤ p)
    (hpq : p ≤ q)
    (hdq_eta : (d : ℝ) < q * eta) :
    ∃ J : ℕ, 1 ≤ J ∧
      ∃ Cstep c C delta0 Cp Kt : ℝ,
        1 ≤ Cstep ∧ 0 < c ∧ 0 < C ∧ 0 < delta0 ∧ 0 < Cp ∧
        1 + 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) ≤ Kt ∧
        ∃ Ccount Cd : ℝ, 0 < Ccount ∧ 0 < Cd ∧
          (let Cat : ℕ → Type :=
            fun n =>
              (Fin d → Fin (3 ^ (n + J) + 1)) ×
                ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))
           ∀ n : ℕ, (Nat.card (Cat n) : ℝ) ≤
              Ccount * ((n : ℝ) + Ccount) ^ Cd *
                (3 : ℝ) ^ ((d : ℝ) * n)) ∧
        ∃ Cmom Crate : ℝ, 0 < Cmom ∧ 0 < Crate ∧
          ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
          (E : in_J d)
          (Poinc : in_poincare d hd E)
          (Ext : in_extension d hd E)
          (Rm : in_responses d M)
          (Sreg : in_6_16 d M)
          (It : in_iteration d M E Sreg)
          (hdet : @lane4_deterministic_good_scale_input d
            ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
          (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
          InfraredCharacterization M H → M.delta ≤ delta0 →
          let alpha : ℝ := (t0 + 2 - (d : ℝ)) / 2
          let P : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
          let Q : Opens (SpatialCoordinates d) := unitNeumannCube d
          let K : Set (SpatialCoordinates d) := closure (Q : Set (SpatialCoordinates d))
          let R : ℕ → ℝ := fun k => (3 : ℝ) ^ (-(k : ℤ)) / 2
          let relabel : ℕ → BilateralField d → BilateralField d :=
            fun N omega j =>
              ContinuousMap.compRightContinuousMap ℝ
                (⟨fun x : SpatialCoordinates d => (3 : ℝ) ^ (-(N : ℤ)) • x,
                  continuous_const.smul continuous_id⟩ :
                  C(SpatialCoordinates d, SpatialCoordinates d))
                (omega (j - (N : ℤ)))
          let Grid : ℕ → Type :=
            fun n => Fin d → Fin (3 ^ (n + J) + 1)
          let Cat : ℕ → Type :=
            fun n =>
              (Fin d → Fin (3 ^ (n + J) + 1)) ×
                ((Fin (d + 1) → Fin (n + J + 1)) × Equiv.Perm (Fin d))
          let ygrid : (n : ℕ) → Grid n → SpatialCoordinates d :=
            fun n a i => (a i : ℝ) * (3 : ℝ) ^ (-(((n + J : ℕ) : ℤ)))
          let active : (n : ℕ) → Cat n → Fin (d + 1) → Set (Fin d) :=
            fun n pi i => {a : Fin d | (pi.2.2.symm a).val < i.val}
          let center : SpatialCoordinates d → Set (Fin d) → SpatialCoordinates d :=
            fun y I a => if a ∈ I then (if y a ≤ 1 / 2 then 0 else 1) else y a
          let k : (n : ℕ) → Cat n → Fin (d + 1) → ℕ :=
            fun n pi i => (pi.2.1 i).val
          let allowance : (N n : ℕ) → Cat n → Fin (d + 1) → BilateralField d → ℝ :=
            fun N n pi i omega =>
              if k n pi i ≤ N then
                (It.prefixLen
                    ((3 : ℝ) ^ (N : ℤ) • center (ygrid n pi.1) (active n pi i))
                    (1 - (1 - alpha) / Kt) (N - k n pi i + J) (relabel N omega) : ℝ) +
                  (J : ℝ) + (It.k : ℝ) + 5
              else 0
          let Z : (N n : ℕ) → Cat n → BilateralField d → ℝ :=
            fun N n pi omega =>
              Cstep ^ (d + 1) *
                Real.exp (c * ∑ i : Fin (d + 1), allowance N n pi i omega)
          let G : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
            fun k omega x =>
              H omega x + ∑ j ∈ Finset.range k, (omega (-(j : ℤ))) x
          let spoint : (N k : ℕ) → BilateralField d → SpatialCoordinates d → ℝ :=
            fun N k omega x =>
              SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) /
                  SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
                Real.exp (G k omega x - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
          let b : (N k : ℕ) → BilateralField d → SpatialCoordinates d → ℝ :=
            fun N k omega z =>
              (volume.real (Metric.ball z (R k)))⁻¹ *
                ∫ x in Metric.ball z (R k), spoint N k omega x
          let osc : ℕ → BilateralField d → SpatialCoordinates d → ℝ :=
            fun k omega y =>
              sSup {v : ℝ | ∃ x ∈ Metric.closedBall y (3 * R k),
                ∃ x' ∈ Metric.closedBall y (3 * R k),
                  v = |G k omega x - G k omega x'|}
          let Vstat : (N k : ℕ) → BilateralField d → Grid k → ℝ :=
            fun N k omega a =>
              Real.exp (osc k omega (ygrid k a)) *
                (spoint N k omega (ygrid k a) +
                  (spoint N k omega (ygrid k a))⁻¹)
          (∀ (N k : ℕ), k ≤ N → ∀ y ∈ K,
            Integrable (fun omega => (spoint N k omega y)^q +
              (spoint N k omega y)^(-q)) P ∧
            (∫ omega, (spoint N k omega y)^q +
              (spoint N k omega y)^(-q) ∂P) ≤
              Cmom * Real.exp (Crate * (q + q^2) * M.delta^2 * (k : ℝ)) ∧
            MemLp (fun omega => spoint N k omega y) (ENNReal.ofReal q) P ∧
            MemLp (fun omega => (spoint N k omega y)⁻¹)
              (ENNReal.ofReal q) P) ∧
          ∃ U V : ℕ → BilateralField d → ℝ,
              (∀ N, Measurable (U N)) ∧
              (∀ N, Measurable (V N)) ∧
              (∀ N omega, 0 ≤ U N omega) ∧
              (∀ N omega, 0 ≤ V N omega) ∧
              (∀ N, MemLp (U N) (ENNReal.ofReal p) P) ∧
              (∀ N, MemLp (V N) (ENNReal.ofReal p) P) ∧
              (∀ N, eLpNorm (U N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cp) ∧
              (∀ N, eLpNorm (V N) (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cp) ∧
              ∀ᵐ omega ∂P, ∀ N : ℕ,
                IsLUB {v : ℝ | ∃ n : ℕ, ∃ pi : Cat n,
                  v = (3 : ℝ) ^ (-eta * (n : ℝ)) * Z N n pi omega} (U N omega) ∧
                IsLUB {v : ℝ | ∃ k : ℕ, k ≤ N ∧ ∃ a : Grid k,
                  v = (R k) ^ etas * Vstat N k omega a} (V N omega) ∧
                (∀ k : ℕ, k ≤ N → ∀ z ∈ K,
                  b N k omega z + (b N k omega z)⁻¹ ≤
                    V N omega * (R k) ^ (-etas)) ∧
                (∀ k : ℕ, k ≤ N → ∀ z ∈ K,
                  ∃ a : Grid k,
                    dist z (ygrid k a) ≤ R k ∧
                    Real.exp (-osc k omega (ygrid k a)) *
                        spoint N k omega (ygrid k a) ≤ b N k omega z ∧
                    b N k omega z ≤
                      Real.exp (osc k omega (ygrid k a)) *
                        spoint N k omega (ygrid k a)) ∧
                let a : PositiveCoefficient Q :=
                  cutoffPositiveCoefficient M H omega N
                    (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
                ∀ f : SpatialCoordinates d → ℝ,
                  AEMeasurable f (volume.restrict (Q : Set (SpatialCoordinates d))) →
                  ∀ Kf : ℝ, 0 ≤ Kf →
                    (∀ᵐ y ∂volume.restrict (Q : Set (SpatialCoordinates d)),
                      |f y| ≤ Kf) →
                    (∫ y in (Q : Set (SpatialCoordinates d)), f y) = 0 →
                    ∀ u : meanZeroSobolevGraph Q, SolvesNeumann a f u →
                      let cube : SpatialCoordinates d → ℝ → Set (SpatialCoordinates d) :=
                        fun x r => {y | ∀ i : Fin d, |y i - x i| < r / 2}
                      let energy : Set (SpatialCoordinates d) → ℝ :=
                        fun A =>
                          ∫ y in A ∩ (Q : Set (SpatialCoordinates d)),
                            a.val y * ∑ i : Fin d,
                              (((sobolevGradient (u : SobolevData Q)) i :
                                SpatialCoordinates d → ℝ) y) ^ 2
                      ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
                        ∀ r : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ r →
                          energy (cube x r) ≤
                            C * U N omega * r ^ (t0 - eta) *
                              (energy (Q : Set (SpatialCoordinates d)) +
                                V N omega * Kf ^ 2)
      := by
  obtain ⟨J, hJ, Cstep, c, C, delta0, Cp, Kt, h1, h2, h3, h4, h5, h6, Ccount, Cd, hC1, hC2, hcount,
    Cmom, Crate, hM1, hM2, hmesh⟩ :=
    aux_rem_resolved_meshes_adm d hd Lstar Rstar t0 eta etas p q hLstar hRstar_pos hRstar_lt
      hRstar_mem ht0_low ht0_high heta_pos heta_lt hetas_pos hetas_lt hp hpq hdq_eta
  exact ⟨J, hJ, Cstep, c, C, delta0, Cp, Kt, h1, h2, h3, h4, h5, h6, Ccount, Cd, hC1, hC2, hcount,
    Cmom, Crate, hM1, hM2, fun M E Poinc Ext Rm Sreg It hdet H hH hδ =>
      hmesh M E Poinc Ext Rm Sreg It hdet H (InfraredAdmissible.of_char hH) hδ⟩

end Paper
