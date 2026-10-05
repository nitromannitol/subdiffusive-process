module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.ReflectedGlue

@[expose] public section

/-!
# Zero extension and slab measure for boundary cells

This module turns an ambient `H1_0` datum into an `H1Function` on an arbitrary
comparison box, and records the translation-cover estimate which supplies a
positive-volume exterior slab.


-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder
open scoped ENNReal

noncomputable section

variable {d : ℕ}

theorem fderiv_apply_eq_zero_of_notMem_tsupport {phi : Vec d → ℝ} {x : Vec d}
    (hx : x ∉ tsupport phi) (i : Fin d) : (fderiv ℝ phi x) (basisVec i) = 0 := by
  have hzero : phi =ᶠ[nhds x] 0 :=
    ((isClosed_tsupport (f := phi)).isOpen_compl.eventually_mem hx).mono
      fun z hz => image_eq_zero_of_notMem_tsupport hz
  rw [hzero.fderiv_eq]
  simp only [fderiv_zero, Pi.zero_apply, zero_apply]

theorem hasWeakGradientOn_of_univ {V : Set (Vec d)} {u : Vec d → ℝ}
    {Du : Vec d → Vec d} (h : HasWeakGradientOn Set.univ u Du) :
    HasWeakGradientOn V u Du := by
  intro i phi hphi hphic hphiV
  have h1 := h i phi hphi hphic (by simp)
  rw [Measure.restrict_univ] at h1
  have hzero1 : ∀ x ∉ V, u x * (fderiv ℝ phi x) (basisVec i) = 0 := by
    intro x hx
    rw [fderiv_apply_eq_zero_of_notMem_tsupport (fun hmem => hx (hphiV hmem)) i,
      mul_zero]
  have hzero2 : ∀ x ∉ V, Du x i * phi x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hmem => hx (hphiV hmem)), mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero1,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero2]
  exact h1

/-- Literal zero extension of an `H1_0(V)` datum, read as an `H1Function` on
an arbitrary set. -/
def zeroExtendH1 {V : Set (Vec d)} (hV : MeasurableSet V) (u : H10Function V)
    (A : Set (Vec d)) : H1Function A where
  toFun := zeroExtend V u.toFun
  grad := zeroExtendGrad V u.grad
  memL2 := (memL2_zeroExtend hV u).restrict A
  gradMemL2 := by
    intro i
    have h := gradMemL2_zeroExtendGrad hV u i
    rw [MemLpOn, Measure.restrict_univ] at h
    exact h.restrict A
  hasWeakGradient := hasWeakGradientOn_of_univ (hasWeakGradientOn_univ_zeroExtend hV u)

@[simp] theorem zeroExtendH1_toFun {V : Set (Vec d)} (hV : MeasurableSet V)
    (u : H10Function V) (A : Set (Vec d)) :
    (zeroExtendH1 hV u A).toFun = zeroExtend V u.toFun := rfl

@[simp] theorem zeroExtendH1_grad {V : Set (Vec d)} (hV : MeasurableSet V)
    (u : H10Function V) (A : Set (Vec d)) :
    (zeroExtendH1 hV u A).grad = zeroExtendGrad V u.grad := rfl

theorem zeroExtendH1_eq_zero_of_notMem {V : Set (Vec d)} (hV : MeasurableSet V)
    (u : H10Function V) (A : Set (Vec d)) {y : Vec d} (hy : y ∉ V) :
    (zeroExtendH1 hV u A).toFun y = 0 :=
  zeroExtend_of_notMem _ hy

theorem eLpNorm_zeroExtend_eq {V : Set (Vec d)} (hV : MeasurableSet V)
    (f : Vec d → ℝ) (A : Set (Vec d)) :
    eLpNorm (zeroExtend V f) 2 (volume.restrict A) =
      eLpNorm f 2 (volume.restrict (A ∩ V)) := by
  rw [zeroExtend, eLpNorm_indicator_eq_eLpNorm_restrict hV,
    Measure.restrict_restrict hV, Set.inter_comm V A]

theorem eLpNorm_zeroExtendGrad_eq {V : Set (Vec d)} (hV : MeasurableSet V)
    (G : Vec d → Vec d) (A : Set (Vec d)) (i : Fin d) :
    eLpNorm (fun y => zeroExtendGrad V G y i) 2 (volume.restrict A) =
      eLpNorm (fun y => G y i) 2 (volume.restrict (A ∩ V)) := by
  rw [zeroExtendGrad_apply_coord, eLpNorm_indicator_eq_eLpNorm_restrict hV,
    Measure.restrict_restrict hV, Set.inter_comm V A]

/-- Three translates of the upper slab cover the box. -/
theorem volume_le_three_mul_slab {A : Set (Vec d)} {g : Vec d → ℝ} {e : Vec d}
    {lo hi a : ℝ} (hg : ∀ (y : Vec d) (s : ℝ), g (y + s • e) = g y + s)
    (hrange : ∀ y ∈ A, lo < g y ∧ g y < hi)
    (hshift : ∀ y ∈ A, ∀ s : ℝ, lo < g y + s → g y + s < hi → y + s • e ∈ A)
    (hah : a < hi) (halo : a - 2 * (hi - a) ≤ lo) :
    volume A ≤ 3 * volume (A ∩ {y | a ≤ g y}) := by
  classical
  let S : Set (Vec d) := A ∩ {y | a ≤ g y}
  let t : ℝ := hi - a
  have ht : 0 < t := by dsimp [t]; linarith only [hah]
  have hcover : A ⊆ ((fun y : Vec d => y + (0 : ℝ) • e) ⁻¹' S) ∪
      ((fun y : Vec d => y + t • e) ⁻¹' S) ∪
      ((fun y : Vec d => y + (2 * t) • e) ⁻¹' S) := by
    intro y hy
    obtain ⟨hlo, hhi⟩ := hrange y hy
    by_cases h0 : a ≤ g y
    · refine Or.inl (Or.inl ?_)
      simp only [Set.mem_preimage, S, Set.mem_inter_iff, Set.mem_ofPred_eq,
        zero_smul, add_zero]
      exact ⟨hy, h0⟩
    · push Not at h0
      by_cases h1 : a - t ≤ g y
      · refine Or.inl (Or.inr ?_)
        have hmemA : y + t • e ∈ A := by
          refine hshift y hy t ?_ ?_
          · linarith only [hlo, ht]
          · dsimp [t]; linarith only [h0]
        simp only [Set.mem_preimage, S, Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨hmemA, by rw [hg y t]; linarith only [h1]⟩
      · push Not at h1
        refine Or.inr ?_
        have hmemA : y + (2 * t) • e ∈ A := by
          refine hshift y hy (2 * t) ?_ ?_
          · linarith only [hlo, ht]
          · dsimp [t]; linarith only [h1]
        simp only [Set.mem_preimage, S, Set.mem_inter_iff, Set.mem_ofPred_eq]
        refine ⟨hmemA, ?_⟩
        rw [hg y (2 * t)]
        have h : a - 2 * t ≤ lo := by dsimp [t]; linarith only [halo]
        linarith only [hlo, h]
  have htrans : ∀ c : ℝ, volume ((fun y : Vec d => y + c • e) ⁻¹' S) = volume S :=
    fun c => measure_preimage_add_right volume (c • e) S
  calc
    volume A ≤ volume (((fun y : Vec d => y + (0 : ℝ) • e) ⁻¹' S) ∪
        ((fun y : Vec d => y + t • e) ⁻¹' S) ∪
        ((fun y : Vec d => y + (2 * t) • e) ⁻¹' S)) := measure_mono hcover
    _ ≤ volume (((fun y : Vec d => y + (0 : ℝ) • e) ⁻¹' S) ∪
          ((fun y : Vec d => y + t • e) ⁻¹' S)) +
        volume ((fun y : Vec d => y + (2 * t) • e) ⁻¹' S) := measure_union_le _ _
    _ ≤ (volume ((fun y : Vec d => y + (0 : ℝ) • e) ⁻¹' S) +
          volume ((fun y : Vec d => y + t • e) ⁻¹' S)) +
        volume ((fun y : Vec d => y + (2 * t) • e) ⁻¹' S) :=
      add_le_add (measure_union_le _ _) le_rfl
    _ = 3 * volume S := by
      rw [htrans 0, htrans t, htrans (2 * t)]
      ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
