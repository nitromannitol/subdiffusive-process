import SubdiffusiveProcess.Paper.lem_band
import SubdiffusiveProcess.Main.BilateralField
import Mathlib.Data.Fin.Fin2
import Mathlib.Tactic

open MeasureTheory Filter Set SubdiffusiveProcess
open scoped ENNReal BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_neg_restrict_le_ambient
    {E : Type*} [MeasurableSpace E]
    (s : Set ℤ) :
    MeasurableSpace.comap
        (fun omega : ℤ → E =>
          fun j : s => omega (-(j : Int)))
        (inferInstance : MeasurableSpace (s → E)) ≤
      (inferInstance : MeasurableSpace (ℤ → E)) := by
  have hrestriction :
      Measurable
        (fun omega : ℤ → E =>
          fun j : s => omega (-(j : Int))) := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply (-(j : Int))
  exact hrestriction.comap_le

theorem aux_neg_restrict_mono
    {E : Type*} [MeasurableSpace E]
    {s t : Set ℤ} (hst : s ⊆ t) :
    MeasurableSpace.comap
        (fun omega : ℤ → E =>
          fun j : s => omega (-(j : Int)))
        (inferInstance : MeasurableSpace (s → E)) ≤
      MeasurableSpace.comap
        (fun omega : ℤ → E =>
          fun j : t => omega (-(j : Int)))
        (inferInstance : MeasurableSpace (t → E)) := by
  let inc : s → t := fun j => ⟨j.1, hst j.2⟩
  let project : (t → E) → (s → E) :=
    fun x j => x (inc j)
  have hproject : Measurable project := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply (inc j)
  have hfactor :
      (fun omega : ℤ → E =>
        fun j : s => omega (-(j : Int))) =
      project ∘
        (fun omega : ℤ → E =>
          fun j : t => omega (-(j : Int))) := by
    rfl
  rw [hfactor, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hproject.comap_le

/--
Band measurability transfer for the finite prefix sums in the proof of
`mfd:lem-witness` (paper lines 2897--2903).

Tick list:

* `hBsig` pins every band sigma-field to the original-layer coordinate comap;
* the input representatives are the actual `Xb` and `Tb` families appearing
  in `lem_witness`, with their source band radii;
* the output enlarges a band by the buffer, the prefix length, and the
  approximant radius, so every summand is measurable in one common witness
  band;
* the ambient a.e. measurability of both representative families is also
  concluded for the common-version child;
* no prefix sum, limit, or witness event is assumed; finite-sum measurability
  is the conclusion of this proof step;
* this fine child refines `lem_witness` and retains a single `by sorry` body.
-/
theorem lem_witness_prefix_band_measurability
    (d : ℕ) (hd : 1 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (P : Measure (BilateralField d)) [IsProbabilityMeasure P]
    (Bsig : ℤ → ℤ → MeasurableSpace (BilateralField d))
    (hBsig : ∀ lo hi : ℤ,
      Bsig lo hi = MeasurableSpace.comap
        (fun omega : BilateralField d =>
          fun j : Set.Icc lo hi => omega (-(j : Int)))
        (inferInstance : MeasurableSpace
          ((i : Set.Icc lo hi) → C(SpatialCoordinates d, ℝ))))
    (Cband c0 J : ℕ)
    (Xb : Fin2 2 → ℤ → ℕ → SpatialCoordinates d →
      BilateralField d → ℝ)
    (Tb : ℤ → Fin J → ℕ → BilateralField d → ℝ)
    (hXb : ∀ q m H z,
      StronglyMeasurable[
        Bsig (m - ((Cband * (H + 1) : ℕ) : ℤ))
          (m + ((Cband * (H + 1) : ℕ) : ℤ))]
        (Xb q m H z))
    (hTb : ∀ n i H,
      StronglyMeasurable[
        Bsig (n - ((Cband * (H + 1) : ℕ) : ℤ))
          (n + ((Cband * (H + 1) : ℕ) : ℤ))]
        (Tb n i H)) :
    (∀ q m H z, AEStronglyMeasurable (Xb q m H z) P) ∧
    (∀ n i H, AEStronglyMeasurable (Tb n i H) P) ∧
    (∀ (n : ℤ) (D H : ℕ) (s : ℤ) (q : Fin2 2)
        (z : SpatialCoordinates d),
      D ≤ H → n - (c0 : ℤ) ≤ s → s ≤ n + (c0 : ℤ) →
        let R : ℕ := Cband * (H + 1) + c0 + D
        StronglyMeasurable[
          Bsig (n - (R : ℤ)) (n + 2 * (R : ℤ))]
          (fun om =>
            ∑ j ∈ Finset.range D,
              Xb q (s + (j : ℤ)) H z om)) := by
  have hle :
      ∀ lo hi : ℤ,
        Bsig lo hi ≤
          (inferInstance : MeasurableSpace (BilateralField d)) := by
    intro lo hi
    rw [hBsig lo hi]
    exact aux_neg_restrict_le_ambient
      (E := C(SpatialCoordinates d, ℝ)) (Set.Icc lo hi)
  have hmono :
      ∀ lo hi lo' hi' : ℤ,
        Set.Icc lo hi ⊆ Set.Icc lo' hi' →
          Bsig lo hi ≤ Bsig lo' hi' := by
    intro lo hi lo' hi' hI
    rw [hBsig lo hi, hBsig lo' hi']
    exact aux_neg_restrict_mono
      (E := C(SpatialCoordinates d, ℝ)) hI
  refine ⟨?_, ?_, ?_⟩
  · intro q m H z
    have hstrong : StronglyMeasurable (Xb q m H z) :=
      (hXb q m H z).mono (hle _ _)
    exact hstrong.aestronglyMeasurable
  · intro n i H
    have hstrong : StronglyMeasurable (Tb n i H) :=
      (hTb n i H).mono (hle _ _)
    exact hstrong.aestronglyMeasurable
  · intro n D H s q z _hDH hslo hshi
    let A : ℕ := Cband * (H + 1)
    let R : ℕ := A + c0 + D
    change StronglyMeasurable[
      Bsig (n - (R : ℤ)) (n + 2 * (R : ℤ))]
      (fun om =>
        ∑ j ∈ Finset.range D,
          Xb q (s + (j : ℤ)) H z om)
    have hR :
        (R : ℤ) = (A : ℤ) + (c0 : ℤ) + (D : ℤ) := by
      simp only [R, Nat.cast_add]
    have hDnonneg : (0 : ℤ) ≤ (D : ℤ) :=
      Int.natCast_nonneg D
    have hRnonneg : (0 : ℤ) ≤ (R : ℤ) :=
      Int.natCast_nonneg R
    refine Finset.stronglyMeasurable_fun_sum
      (m := Bsig (n - (R : ℤ)) (n + 2 * (R : ℤ)))
      (Finset.range D) ?_
    intro j hj
    have hjnonneg : (0 : ℤ) ≤ (j : ℤ) :=
      Int.natCast_nonneg j
    have hjD : (j : ℤ) < (D : ℤ) :=
      Int.ofNat_lt.mpr (Finset.mem_range.mp hj)
    have hlo :
        n - (R : ℤ) ≤ s + (j : ℤ) - (A : ℤ) := by
      linarith only [hR, hslo, hjnonneg, hDnonneg]
    have hhi :
        s + (j : ℤ) + (A : ℤ) ≤ n + 2 * (R : ℤ) := by
      linarith only [hR, hshi, hjD, hRnonneg]
    have hsubset :
        Set.Icc
            (s + (j : ℤ) - (A : ℤ))
            (s + (j : ℤ) + (A : ℤ)) ⊆
          Set.Icc (n - (R : ℤ)) (n + 2 * (R : ℤ)) := by
      intro k hk
      exact ⟨hlo.trans hk.1, hk.2.trans hhi⟩
    have hband :
        Bsig
            (s + (j : ℤ) - (A : ℤ))
            (s + (j : ℤ) + (A : ℤ)) ≤
          Bsig (n - (R : ℤ)) (n + 2 * (R : ℤ)) :=
      hmono _ _ _ _ hsubset
    exact (hXb q (s + (j : ℤ)) H z).mono hband

end Paper
