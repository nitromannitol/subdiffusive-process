import SubdiffusiveProcess.Paper.prop_conc_setup
import SubdiffusiveProcess.Paper.prop_conc_affine_order
import SubdiffusiveProcess.Paper.prop_conc_layer_step
import SubdiffusiveProcess.Paper.in_joint_extracted_candidates
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Probability.ResamplingSum
import SubdiffusiveProcess.Probability.ConditionalPullback
import SubdiffusiveProcess.Lane3.RelativeResponseSlopes
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Lane3.Interfaces
import SubdiffusiveProcess.Lane2.ExternalInputs
import SubdiffusiveProcess.Sobolev.AffineResponses
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.ScaledLayerLaw
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Probability
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators Topology

namespace Paper
noncomputable section

theorem aux_prop_conc_assembly_nat_tail (q : ℝ≥0∞) (H : ℕ) :
    (∑' n : ℕ, if H ≤ n then q ^ n else 0) = q ^ H * (1 - q)⁻¹ := by
  have hzero : (∑ n ∈ Finset.range H, if H ≤ n then q ^ n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [if_neg (not_le.mpr (Finset.mem_range.mp hn))]
  have ht := ((ENNReal.summable : Summable
    (fun n : ℕ => if H ≤ n + H then q ^ (n + H) else 0)).hasSum.sum_range_add
      (f := fun n : ℕ => if H ≤ n then q ^ n else 0) (k := H)).tsum_eq
  rw [hzero, zero_add] at ht
  rw [ht]
  simp only [Nat.le_add_left, if_true, pow_add]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, mul_comm]

/-- The resampling increments summed over the indices outside a set at distance at least `H` from
the shifted origin `-k` are bounded by a geometric tail (each distance occurs at most twice). -/
theorem aux_prop_conc_assembly_int_tail (q A : ℝ≥0∞) (k : ℤ) (H : ℕ) (S : Set ℤ)
    (hS : ∀ j ∈ S, H ≤ (j + k).natAbs) :
    (∑' j : ↥S, A * q ^ (j + k : ℤ).natAbs) ≤
      A * (q ^ H * (1 - q)⁻¹ + q ^ H * (1 - q)⁻¹) := by
  classical
  let g : ℕ → ℝ≥0∞ := fun n => if H ≤ n then q ^ n else 0
  have hnat : ∑' n, g n = q ^ H * (1 - q)⁻¹ :=
    aux_prop_conc_assembly_nat_tail q H
  have hneg : (∑' n : ℕ, g (n + 1)) ≤ ∑' n : ℕ, g n :=
    ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective g
  have hint : (∑' j : ℤ, g j.natAbs) ≤
      q ^ H * (1 - q)⁻¹ + q ^ H * (1 - q)⁻¹ := by
    have habs (n : ℕ) : ((n : ℤ) + 1).natAbs = n + 1 := by
      change (((n + 1 : ℕ) : ℤ)).natAbs = n + 1
      exact Int.natAbs_natCast _
    rw [tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable]
    simp only [Int.natAbs_natCast, Int.natAbs_neg, habs]
    exact (add_le_add le_rfl hneg).trans_eq (by rw [hnat])
  calc
    (∑' j : ↥S, A * q ^ (j + k : ℤ).natAbs) = ∑' j : ℤ, S.indicator
        (fun j : ℤ => A * q ^ (j + k).natAbs) j := tsum_subtype S (fun j : ℤ => A * q ^ (j + k).natAbs)
    _ ≤ ∑' j : ℤ, A * g (j + k).natAbs := by
      refine ENNReal.tsum_le_tsum fun j => ?_
      by_cases hj : j ∈ S
      · rw [Set.indicator_of_mem hj]
        simp only [g, if_pos (hS j hj)]
        exact le_rfl
      · rw [Set.indicator_of_notMem hj]
        exact zero_le _
    _ = A * ∑' j : ℤ, g (j + k).natAbs := by rw [ENNReal.tsum_mul_left]
    _ = A * ∑' j : ℤ, g j.natAbs := by
      congr 1
      exact (Equiv.addRight k).tsum_eq (fun j : ℤ => g j.natAbs)
    _ ≤ _ := mul_le_mul_right hint A

/-- Centered and band-error norms pull back along the actual field law, including an arbitrary
almost-everywhere representative `R` on the original probability space. -/
theorem aux_prop_conc_assembly_pullback
    {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (laws : ℤ → Measure X) [∀ j, IsProbabilityMeasure (laws j)]
    (field : Ω → ℤ → X) (hfield : MeasurePreserving field P (Measure.infinitePi laws))
    (f : (ℤ → X) → ℝ) (hfi : Integrable f (Measure.infinitePi laws))
    (R : Ω → ℝ) (hR : R =ᵐ[P] f ∘ field) (p : ℝ≥0∞) (J : Set ℤ) :
    eLpNorm (fun om => R om - (P[R | ⨆ j ∈ J, (inferInstance : MeasurableSpace X).comap
        (fun om : Ω => field om j)]) om) p P =
      eLpNorm (f - (Measure.infinitePi laws)[f | coordinateSigma (fun _ : ℤ => X) J]) p
        (Measure.infinitePi laws) := by
  have hce := condExp_comp_measurePreserving hfield
    (coordinateSigma_le (fun _ : ℤ => X) J) hfi
  have hband : (coordinateSigma (fun _ : ℤ => X) J).comap field =
      ⨆ j ∈ J, (inferInstance : MeasurableSpace X).comap (fun om : Ω => field om j) := by
    rw [coordinateSigma_eq_iSup]
    simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    rfl
  rw [hband] at hce
  have hceR := (condExp_congr_ae (m := ⨆ j ∈ J, (inferInstance : MeasurableSpace X).comap
    (fun om : Ω => field om j)) hR).trans hce
  have hae : (fun om => R om - (P[R | ⨆ j ∈ J, (inferInstance : MeasurableSpace X).comap
      (fun om : Ω => field om j)]) om) =ᵐ[P]
      (f - (Measure.infinitePi laws)[f | coordinateSigma (fun _ : ℤ => X) J]) ∘ field := by
    filter_upwards [hR, hceR] with om hom hcond
    simp only [Function.comp_apply, Pi.sub_apply] at hom hcond ⊢
    rw [hom, hcond]
  rw [eLpNorm_congr_ae hae]
  exact eLpNorm_comp_measurePreserving
    (hfi.aestronglyMeasurable.sub integrable_condExp.aestronglyMeasurable) hfield

/-- The scalar centered and shifted-band estimates from single-layer influences, by the resampling
sum and two geometric series. The constant is explicit and independent of the represented space,
observation level and tail width. -/
theorem aux_prop_conc_assembly_scalar
    {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (laws : ℤ → Measure X) [∀ j, IsProbabilityMeasure (laws j)]
    (field : Ω → ℤ → X) (hfield : MeasurePreserving field P (Measure.infinitePi laws))
    (f : (ℤ → X) → ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤)
    (hf : MemLp f p (Measure.infinitePi laws))
    (R : Ω → ℝ) (hR : R =ᵐ[P] f ∘ field)
    (a A : ℝ) (ha : 0 < a) (hA : 0 ≤ A) (k : ℕ)
    (hstep : ∀ j : ℤ, eLpNorm (fun q : (ℤ → X) × (ℤ → X) =>
        f q.1 - f (Function.update q.1 j (q.2 j))) p
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤
          ENNReal.ofReal (A * (3 : ℝ) ^ (-a * ((j + (k : ℤ)).natAbs : ℝ)))) :
    eLpNorm (fun om => R om - ∫ om', R om' ∂P) p P ≤
        ENNReal.ofReal (2 * A / (1 - (3 : ℝ) ^ (-a))) ∧
      ∀ H : ℕ,
        eLpNorm (fun om => R om - (P[R | ⨆ (j : ℤ) (_h : |j + (k : ℤ)| ≤ (H : ℤ)),
            (inferInstance : MeasurableSpace X).comap (fun om : Ω => field om j)]) om) p P ≤
          ENNReal.ofReal (2 * A / (1 - (3 : ℝ) ^ (-a)) * (3 : ℝ) ^ (-a * (H : ℝ))) := by
  classical
  let b : ℝ := (3 : ℝ) ^ (-a)
  let q : ℝ≥0∞ := ENNReal.ofReal b
  have hb0 : 0 ≤ b := by positivity
  have hb1 : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpow (H : ℕ) : ENNReal.ofReal ((3 : ℝ) ^ (-a * (H : ℝ))) = q ^ H := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast, ENNReal.ofReal_pow hb0]
  have hden : (1 - q)⁻¹ = ENNReal.ofReal ((1 - b)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (sub_pos.mpr hb1), ENNReal.ofReal_sub 1 hb0,
      ENNReal.ofReal_one]
  have hcoef (H : ℕ) : ENNReal.ofReal A *
      (q ^ H * (1 - q)⁻¹ + q ^ H * (1 - q)⁻¹) =
        ENNReal.ofReal (2 * A / (1 - b) * (3 : ℝ) ^ (-a * (H : ℝ))) := by
    have ht0 : 0 ≤ (3 : ℝ) ^ (-a * (H : ℝ)) * (1 - b)⁻¹ :=
      mul_nonneg (by positivity) (inv_nonneg.mpr (sub_nonneg.mpr hb1.le))
    rw [← hpow H, hden, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add ht0 ht0, ← ENNReal.ofReal_mul hA]
    congr 1
    ring
  have hstep' (j : ℤ) : eLpNorm (fun q : (ℤ → X) × (ℤ → X) =>
        f q.1 - f (Function.update q.1 j (q.2 j))) p
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤
          ENNReal.ofReal A * q ^ (j + (k : ℤ)).natAbs := by
    have h := hstep j
    rwa [ENNReal.ofReal_mul hA, hpow] at h
  have hfi : Integrable f (Measure.infinitePi laws) := hf.integrable hp
  have hbound (J : Set ℤ) (H : ℕ) (hJ : ∀ j ∈ Jᶜ, H ≤ (j + (k : ℤ)).natAbs) :
      eLpNorm (fun om => R om - (P[R | ⨆ j ∈ J, (inferInstance : MeasurableSpace X).comap
        (fun om : Ω => field om j)]) om) p P ≤
          ENNReal.ofReal (2 * A / (1 - b) * (3 : ℝ) ^ (-a * (H : ℝ))) := by
    rw [aux_prop_conc_assembly_pullback P laws field hfield f hfi R hR p J, ← hcoef H]
    refine (eLpNorm_sub_condExp_le_tsum_resample (E := fun _ : ℤ => X) laws hp hpt f hf J).trans ?_
    refine (ENNReal.tsum_le_tsum (fun j : ↥Jᶜ => hstep' (j : ℤ))).trans ?_
    exact aux_prop_conc_assembly_int_tail q (ENNReal.ofReal A) k H Jᶜ hJ
  constructor
  · have h0 := hbound ∅ 0 (fun j _ => Nat.zero_le _)
    have hbot : (⨆ j ∈ (∅ : Set ℤ), (inferInstance : MeasurableSpace X).comap
        (fun om : Ω => field om j)) = ⊥ := by simp
    rw [hbot] at h0
    have hcond : (P[R | (⊥ : MeasurableSpace Ω)]) = fun _ => ∫ om', R om' ∂P := condExp_bot R
    simp only [hcond, Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one] at h0
    exact h0
  · intro H
    have h := hbound {j : ℤ | |j + (k : ℤ)| ≤ (H : ℤ)} H (by
      intro j hj
      have h : (H : ℤ) < |j + (k : ℤ)| := lt_of_not_ge hj
      rw [← Int.natCast_natAbs] at h
      exact_mod_cast h.le)
    exact h

/-- Assembly of `(31)` per slope, single level `k`: from the per-layer bound (`prop_conc_layer_step`), the resampling
sum with no layers retained and with the band `B_{k,H}` retained, two geometric sums, and Hölder for `p < 2`. -/
theorem prop_conc_assembly
    (d : ℕ) (hd : 2 ≤ d)
    (I : Paper.in_J d) (_X : Paper.in_extension d hd I)
    (_Sob : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd)
    (_MeyersMorrey : SubdiffusiveProcess.Lane4.SmallPerturbationInput d)
    (Pin : Paper.in_poincare d hd I)
    (Ccamp : SubdiffusiveProcess.Lane4.CampanatoInput d)
    (Interp : CubeFractionalInterpolationInput d hd)
    (hES : SubdiffusiveProcess.Lane3.EfronSteinMomentInequality) :
    ∃ aexp : ℝ, 0 < aexp ∧
      ∀ (C0 : ℝ) (hC0 : 1 ≤ C0),
      ∀ (p : ℝ) (hp : 0 < p),
      ∃ delta0 C : ℝ, 0 < delta0 ∧ 0 < C ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (Rm : Paper.in_responses d model) (Sreg : Paper.in_6_16 d model)
        (It : Paper.in_iteration d model I Sreg),
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
        (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace
          (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ) (m M : ℝ)
        (zcell : SpatialCoordinates d) (k : ℕ) (cellIdx paddedIdx : ℕ)
        (hPk : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph
            (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _)),
          ‖(u : SobolevData
              (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))).1‖ ≤
            K * ‖subspaceGradient
              (killedSobolevGraph
                (centeredCube zcell ((3 : ℝ) ^ (-(k : ℝ))) (Real.rpow_pos_of_pos zero_lt_three _))) u‖)
        (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
        (hyps : prop_conc_setup d model H Ω P field z r hr Sspace GN GE GF NE NF C0 m M
          zcell k cellIdx paddedIdx hPk AE AF),
      ∀ c ∈ Icc m M, ∀ (pvec : Fin d → ℝ),
        ((∃ i : Fin d, pvec = (Pi.single i (1 : ℝ) : Fin d → ℝ)) ∨
          (∃ i j : Fin d, pvec = (Pi.single i (1 : ℝ) : Fin d → ℝ) +
            (Pi.single j (1 : ℝ) : Fin d → ℝ))) →
      let R : Ω → ℝ := fun omega =>
        (pvec ⬝ᵥ (AF omega).mulVec pvec - c * (pvec ⬝ᵥ (AE omega).mulVec pvec)) /
          Matrix.trace (AE omega)
      let Band : ℕ → MeasurableSpace Ω := fun Hb =>
        ⨆ (j : ℤ) (_h : |j + (k : ℤ)| ≤ (Hb : ℤ)),
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
            (fun omega : Ω => field omega j)
      (eLpNorm (fun omega => R omega - ∫ omega', R omega' ∂P) (ENNReal.ofReal p) P ≤
          ENNReal.ofReal (C * model.delta * (M - m))) ∧
        (∀ Hb : ℕ,
          eLpNorm (fun omega => R omega - (P[R | Band Hb]) omega) (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (C * model.delta * (M - m) * (3 : ℝ) ^ (-aexp * (Hb : ℝ)))) := by
  obtain ⟨aexp, ha, hstep⟩ :=
    prop_conc_layer_step d hd I _X _Sob _MeyersMorrey Pin Ccamp Interp hES
  refine ⟨aexp, ha, ?_⟩
  intro C0 hC0 p hp
  obtain ⟨d1, C1, hd1, hC1, hs⟩ := hstep C0 hC0 (max p 2) (le_max_right _ _)
  obtain ⟨d2, hd2, hord⟩ :=
    prop_conc_affine_order d hd I _X _Sob _MeyersMorrey Pin Ccamp Interp hES C0 hC0
  have hb1 : (3 : ℝ) ^ (-aexp) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨min d1 d2, 2 * C1 / (1 - (3 : ℝ) ^ (-aexp)), lt_min hd1 hd2,
    div_pos (by positivity) (sub_pos.mpr hb1), ?_⟩
  intro _ _ model hdelta Rm Sreg It H Ω _ P field z r hr Sspace GN GE GF NE NF m M
    zcell k cellIdx paddedIdx hPk AE AF hyps c hc pvec hpvec
  have hdpos : (0 : ℝ) < model.delta := model.shellPrefix.delta_pos
  have hd1' : model.delta ≤ d1 := hdelta.trans (min_le_left _ _)
  have hd2' : model.delta ≤ d2 := hdelta.trans (min_le_right _ _)
  obtain ⟨-, -, hpsd, hordAE⟩ := hord model hd2' Rm Sreg It H Ω P field z r hr Sspace GN GE GF
    NE NF m M zcell k cellIdx paddedIdx hPk AE AF hyps
  obtain ⟨f, hfm, hRf, hbound⟩ := hs model hd1' Rm Sreg It H Ω P field z r hr Sspace GN GE GF
    NE NF m M zcell k cellIdx paddedIdx hPk AE AF hyps c hc pvec hpvec
  obtain ⟨hJoint, ⟨hm, hmM, hM⟩, horder, hcell, hpadded, hsymAE, hsymAF, hAE, hAF⟩ := hyps
  haveI : IsProbabilityMeasure P := hJoint.1
  have hfield : MeasurePreserving field P (chaosSampleLaw model).toMeasure :=
    ⟨hJoint.2.1, hJoint.2.2.1⟩
  have hm0 : 0 ≤ m := (inv_nonneg.mpr (zero_le_one.trans hC0)).trans hm
  have hRb : ∀ᵐ ω ∂P, ‖(fun omega => (pvec ⬝ᵥ (AF omega).mulVec pvec -
      c * (pvec ⬝ᵥ (AE omega).mulVec pvec)) / Matrix.trace (AE omega)) ω‖ ≤ 4 * M := by
    filter_upwards [hpsd, hordAE] with ω hp' ho
    rw [Real.norm_eq_abs]
    exact SubdiffusiveProcess.Lane3.RelSlopes.relativeResponse_abs_le (AE ω) (AF ω)
      (hsymAE ω) hp' m M c hm0 (hm0.trans hc.1) hc.2 ho.1 ho.2 pvec hpvec
  have hRmeas : AEStronglyMeasurable (fun omega => (pvec ⬝ᵥ (AF omega).mulVec pvec -
      c * (pvec ⬝ᵥ (AE omega).mulVec pvec)) / Matrix.trace (AE omega)) P :=
    (hfm.comp hfield.measurable).aestronglyMeasurable.congr hRf.symm
  have hRint : Integrable (fun omega => (pvec ⬝ᵥ (AF omega).mulVec pvec -
      c * (pvec ⬝ᵥ (AE omega).mulVec pvec)) / Matrix.trace (AE omega)) P :=
    Integrable.of_bound hRmeas (4 * M) hRb
  have hfb : ∀ᵐ x ∂(chaosSampleLaw model).toMeasure, ‖f x‖ ≤ 4 * M := by
    rw [← hfield.map_eq]
    refine (ae_map_iff hfield.measurable.aemeasurable
      (measurableSet_le hfm.norm measurable_const)).2 ?_
    filter_upwards [hRf, hRb] with ω h1 h2
    exact (congrArg norm h1).symm.trans_le h2
  have hMemLp : MemLp f (ENNReal.ofReal (max p 2)) (chaosSampleLaw model).toMeasure :=
    MemLp.of_bound hfm.aestronglyMeasurable (4 * M) hfb
  have hp2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max p 2) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [le_max_right p 2])
  have hAnn : 0 ≤ C1 * model.delta * (M - m) :=
    mul_nonneg (mul_nonneg hC1.le hdpos.le) (sub_nonneg.mpr hmM)
  obtain ⟨hc1, hc2⟩ := aux_prop_conc_assembly_scalar (X := C(SpatialCoordinates d, ℝ)) P
    (fun j : ℤ => (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure) field hfield f hp2
    ENNReal.ofReal_ne_top hMemLp _ hRf aexp (C1 * model.delta * (M - m)) ha hAnn k hbound
  have hpq : ENNReal.ofReal p ≤ ENNReal.ofReal (max p 2) :=
    ENNReal.ofReal_le_ofReal (le_max_left p 2)
  have hcst : 2 * C1 / (1 - (3 : ℝ) ^ (-aexp)) * model.delta * (M - m) =
      2 * (C1 * model.delta * (M - m)) / (1 - (3 : ℝ) ^ (-aexp)) := by ring
  refine ⟨?_, fun Hb => ?_⟩
  · refine ((eLpNorm_le_eLpNorm_of_exponent_le hpq
      (hRmeas.sub aestronglyMeasurable_const)).trans hc1).trans ?_
    rw [hcst]
  · have hcst2 : 2 * C1 / (1 - (3 : ℝ) ^ (-aexp)) * model.delta * (M - m) *
        (3 : ℝ) ^ (-aexp * (Hb : ℝ)) = 2 * (C1 * model.delta * (M - m)) /
          (1 - (3 : ℝ) ^ (-aexp)) * (3 : ℝ) ^ (-aexp * (Hb : ℝ)) := by ring
    refine ((eLpNorm_le_eLpNorm_of_exponent_le hpq
      (hRmeas.sub integrable_condExp.aestronglyMeasurable)).trans (hc2 Hb)).trans ?_
    rw [hcst2]

end
end Paper
