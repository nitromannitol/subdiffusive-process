import Mathlib.Tactic
import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Lane3.DeterministicEndpoints
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Geometry.Cube

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

namespace Paper

lemma aux_lem_endpoints_resample_preserving
    {Y : ℤ → Type} [∀ j, MeasurableSpace (Y j)]
    (laws : (j : ℤ) → Measure (Y j)) [∀ j, IsProbabilityMeasure (laws j)]
    (S : Finset ℤ) :
    MeasurePreserving
      (fun z : ((j : ℤ) → Y j) × ((j : ℤ) → Y j) =>
        fun j => if j ∈ S then z.2 j else z.1 j)
      ((Measure.infinitePi laws).prod (Measure.infinitePi laws))
      (Measure.infinitePi laws) := by
  classical
  let P : Measure ((j : ℤ) → Y j) := Measure.infinitePi laws
  let A : Type := (j : {j : ℤ // j ∉ S}) → Y j
  let B : Type := (j : {j : ℤ // ¬ (j ∉ S)}) → Y j
  let PA : Measure A := Measure.infinitePi (fun i : {j : ℤ // j ∉ S} => laws i.1)
  let PB : Measure B := Measure.infinitePi (fun i : {j : ℤ // ¬ (j ∉ S)} => laws i.1)
  let e : ((j : ℤ) → Y j) ≃ᵐ A × B :=
    MeasurableEquiv.piEquivPiSubtypeProd Y (fun j => j ∉ S)
  have he : MeasurePreserving e P (PA.prod PB) := by
    dsimp only [e, P, A, B, PA, PB]
    exact measurePreserving_infinitePi_split laws (fun j => j ∉ S)
  have hfst : MeasurePreserving Prod.fst (PA.prod PB) PA :=
    measurePreserving_fst
  have hsnd : MeasurePreserving Prod.snd (PA.prod PB) PB :=
    measurePreserving_snd
  have hmix : MeasurePreserving
      (fun q : (A × B) × (A × B) => (q.1.1, q.2.2))
      ((PA.prod PB).prod (PA.prod PB)) (PA.prod PB) := by
    convert hfst.skew_product (g := fun _ q : A × B => q.2)
      (by fun_prop) (ae_of_all _ (fun _ => hsnd.map_eq)) using 1
  have hprod : MeasurePreserving (Prod.map e e)
      (P.prod P) ((PA.prod PB).prod (PA.prod PB)) := he.prod he
  have hes : MeasurePreserving e.symm (PA.prod PB) P := by
    refine ⟨e.symm.measurable, ?_⟩
    rw [← he.map_eq]
    rw [Measure.map_map e.symm.measurable e.measurable]
    simp only [Function.comp_def, e.symm_apply_apply]
    change Measure.map id P = P
    exact Measure.map_id
  have hcomp := hes.comp (hmix.comp hprod)
  refine ⟨?_, ?_⟩
  · apply measurable_pi_iff.mpr
    intro j
    by_cases hj : j ∈ S
    · simpa only [if_pos hj] using
        (measurable_pi_apply j).comp measurable_snd
    · simpa only [if_neg hj] using
        (measurable_pi_apply j).comp measurable_fst
  · have hmap := hcomp.map_eq
    change Measure.map
      (fun z : ((j : ℤ) → Y j) × ((j : ℤ) → Y j) =>
        fun j => if j ∈ S then z.2 j else z.1 j) (P.prod P) = P
    calc
      Measure.map
          (fun z : ((j : ℤ) → Y j) × ((j : ℤ) → Y j) =>
            fun j => if j ∈ S then z.2 j else z.1 j) (P.prod P) =
          Measure.map
            (e.symm ∘ (fun q : (A × B) × (A × B) => (q.1.1, q.2.2)) ∘
              Prod.map e e) (P.prod P) := by
        apply Measure.map_congr
        filter_upwards [] with z
        funext j
        change (if j ∈ S then z.2 j else z.1 j) =
          (if _h : j ∉ S then z.1 j else z.2 j)
        by_cases hj : j ∈ S <;> simp [hj]
      _ = P := hmap

lemma aux_lem_endpoints_ae_invariant
    {Y : ℤ → Type} [∀ j, MeasurableSpace (Y j)]
    (laws : (j : ℤ) → Measure (Y j)) [∀ j, IsProbabilityMeasure (laws j)]
    (f : ((j : ℤ) → Y j) → ℝ)
    (hf : AEMeasurable f (Measure.infinitePi laws))
    (C : ℝ) (hbound : ∀ᵐ x ∂(Measure.infinitePi laws), |f x| ≤ C)
    (hinv : ∀ S : Finset ℤ,
      ∀ᵐ z ∂((Measure.infinitePi laws).prod (Measure.infinitePi laws)),
        f z.1 = f (fun j => if j ∈ S then z.2 j else z.1 j)) :
    ∃ c : ℝ, ∀ᵐ x ∂(Measure.infinitePi laws), f x = c := by
  classical
  let P : Measure ((j : ℤ) → Y j) := Measure.infinitePi laws
  have hC : 0 ≤ C := by
    obtain ⟨x, hx⟩ := hbound.exists
    exact (abs_nonneg (f x)).trans hx
  have hbound' : ∀ᵐ x ∂P, f x ∈ {y : ℝ | |y| ≤ C} := by
    simpa only [P, Set.mem_setOf_eq] using hbound
  obtain ⟨g, hg, hgrange, hfg⟩ := hf.exists_ae_eq_range_subset hbound'
    ⟨0, by simpa only [Set.mem_setOf_eq, abs_zero] using hC⟩
  have hgbound : ∀ x, |g x| ≤ C := by
    intro x
    exact hgrange (Set.mem_range_self x)
  have hginv : ∀ S : Finset ℤ,
      ∀ᵐ z ∂(P.prod P),
        g z.1 = g (fun j => if j ∈ S then z.2 j else z.1 j) := by
    intro S
    have hR := aux_lem_endpoints_resample_preserving laws S
    have hleft := (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae_eq_comp hfg
    have hright := hR.quasiMeasurePreserving.ae_eq_comp hfg
    filter_upwards [hleft.symm, hinv S, hright] with z hzleft hzmid hzright
    exact hzleft.trans (hzmid.trans hzright)
  obtain ⟨c, hgc⟩ := SubdiffusiveProcess.Lane3.deterministic_endpoints
    (Y := Y) laws g hg C hgbound hginv
  exact ⟨c, hfg.trans hgc⟩



theorem lem_endpoints_zero_one
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), model.delta ≤ delta0 →
      let μ : Measure (BilateralField d) := (chaosSampleLaw model).toMeasure
      ∀ (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
        (GE GF : (i : ℕ) → BilateralField d →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i))),
      let lower : BilateralField d → ℝ := fun omega =>
        sSup {a : ℝ | ∀ i : ℕ, ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
          u ∈ limitFormDomain (GE i omega) →
            a * (limitFormEnergy (GE i omega) u).toReal ≤
              (limitFormEnergy (GF i omega) u).toReal}
      let upper : BilateralField d → ℝ := fun omega =>
        sInf {a : ℝ | ∀ i : ℕ, ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
          u ∈ limitFormDomain (GE i omega) →
            (limitFormEnergy (GF i omega) u).toReal ≤
              a * (limitFormEnergy (GE i omega) u).toReal}
      (hLowerMeas : AEMeasurable lower μ) →
      (hUpperMeas : AEMeasurable upper μ) →
      (Cb : ℝ) →
      (hLowerBound : ∀ᵐ omega ∂μ, |lower omega| ≤ Cb) →
      (hUpperBound : ∀ᵐ omega ∂μ, |upper omega| ≤ Cb) →
      (hLowerInv : ∀ S : Finset ℤ,
        ∀ᵐ zz ∂(μ.prod μ),
          lower zz.1 = lower (fun j => if j ∈ S then zz.2 j else zz.1 j)) →
      (hUpperInv : ∀ S : Finset ℤ,
        ∀ᵐ zz ∂(μ.prod μ),
          upper zz.1 = upper (fun j => if j ∈ S then zz.2 j else zz.1 j)) →
      ∃ cLower cUpper : ℝ, ∀ᵐ omega ∂μ,
        lower omega = cLower ∧ upper omega = cUpper := by
  refine ⟨1, by norm_num, ?_⟩
  intro _ _ model _
  dsimp only
  intro z r hr GE GF
  intro hLowerMeas hUpperMeas Cb hLowerBound hUpperBound hLowerInv hUpperInv
  let laws : (j : ℤ) → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d (chaosRootFieldLaw model) j).toMeasure
  let lower : BilateralField d → ℝ := fun omega =>
    sSup {a : ℝ | ∀ i : ℕ, ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
      u ∈ limitFormDomain (GE i omega) →
        a * (limitFormEnergy (GE i omega) u).toReal ≤
          (limitFormEnergy (GF i omega) u).toReal}
  let upper : BilateralField d → ℝ := fun omega =>
    sInf {a : ℝ | ∀ i : ℕ, ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
      u ∈ limitFormDomain (GE i omega) →
        (limitFormEnergy (GF i omega) u).toReal ≤
          a * (limitFormEnergy (GE i omega) u).toReal}
  have hLowerMeas' : AEMeasurable lower (Measure.infinitePi laws) := by
    simpa only [lower, laws, chaosSampleLaw, commonScaleLaw] using hLowerMeas
  have hUpperMeas' : AEMeasurable upper (Measure.infinitePi laws) := by
    simpa only [upper, laws, chaosSampleLaw, commonScaleLaw] using hUpperMeas
  have hLowerBound' : ∀ᵐ omega ∂(Measure.infinitePi laws), |lower omega| ≤ Cb := by
    simpa only [lower, laws, chaosSampleLaw, commonScaleLaw] using hLowerBound
  have hUpperBound' : ∀ᵐ omega ∂(Measure.infinitePi laws), |upper omega| ≤ Cb := by
    simpa only [upper, laws, chaosSampleLaw, commonScaleLaw] using hUpperBound
  have hLowerInv' : ∀ S : Finset ℤ,
      ∀ᵐ zz ∂((Measure.infinitePi laws).prod (Measure.infinitePi laws)),
        lower zz.1 = lower (fun j => if j ∈ S then zz.2 j else zz.1 j) := by
    intro S
    simpa only [lower, laws, chaosSampleLaw, commonScaleLaw] using hLowerInv S
  have hUpperInv' : ∀ S : Finset ℤ,
      ∀ᵐ zz ∂((Measure.infinitePi laws).prod (Measure.infinitePi laws)),
        upper zz.1 = upper (fun j => if j ∈ S then zz.2 j else zz.1 j) := by
    intro S
    simpa only [upper, laws, chaosSampleLaw, commonScaleLaw] using hUpperInv S
  obtain ⟨cLower, hcLower⟩ := aux_lem_endpoints_ae_invariant
    laws lower hLowerMeas' Cb hLowerBound' hLowerInv'
  obtain ⟨cUpper, hcUpper⟩ := aux_lem_endpoints_ae_invariant
    laws upper hUpperMeas' Cb hUpperBound' hUpperInv'
  refine ⟨cLower, cUpper, ?_⟩
  simpa only [lower, upper, laws, chaosSampleLaw, commonScaleLaw] using
    (hcLower.and hcUpper)

end Paper
