import Mathlib

/-!
# Layer-window σ-algebras on bilateral layer sequences

For a family of layers `ω : ℤ → E` and a set of indices `s`, the window σ-algebra is the
pullback of the product σ-algebra under the restriction `ω ↦ ω|_s`.  This file proves:
monotonicity in the index set, that a coordinate inside the window is window-measurable,
and the factorisation criterion: a measurable function that depends only on the window
coordinates is window-measurable.  It does not assume any probability law.
-/

open MeasureTheory

namespace SubdiffusiveProcess.Lfgc
variable {E : Type*} [MeasurableSpace E]

/-- The window σ-algebra of the index set `s`: pullback of the product σ-algebra under restriction. -/
def layerWindow (E : Type*) [MeasurableSpace E] (s : Set ℤ) : MeasurableSpace (ℤ → E) :=
  MeasurableSpace.comap s.restrict (inferInstance : MeasurableSpace (s → E))

theorem layerWindow_mono {s t : Set ℤ} (hst : s ⊆ t) :
    layerWindow E s ≤ layerWindow E t := by
  unfold layerWindow
  have hfac : (s.restrict : (ℤ → E) → (s → E)) =
      (fun x : t → E => fun j : s => x ⟨j.1, hst j.2⟩) ∘ t.restrict := by
    funext ω j; rfl
  rw [hfac, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono
    (measurable_pi_iff.mpr fun j => measurable_pi_apply _).comap_le

theorem layerWindow_le_pi (s : Set ℤ) :
    layerWindow E s ≤ (inferInstance : MeasurableSpace (ℤ → E)) := by
  unfold layerWindow
  exact (measurable_pi_iff.mpr fun j : s =>
    measurable_pi_apply (X := fun _ : ℤ => E) (j : ℤ)).comap_le

theorem measurable_coord_layerWindow {s : Set ℤ} {i : ℤ} (hi : i ∈ s) :
    Measurable[layerWindow E s] (fun ω : ℤ → E => ω i) := by
  have h : (fun ω : ℤ → E => ω i) = (fun x : s → E => x ⟨i, hi⟩) ∘ s.restrict := by
    funext ω; rfl
  rw [h]
  exact (measurable_pi_apply _).comp (comap_measurable _)

section Extend

variable [Zero E]

open Classical in
/-- Zero extension of a window configuration to all indices. -/
noncomputable def windowExtend (s : Set ℤ) (x : s → E) : ℤ → E :=
  fun i => if hi : i ∈ s then x ⟨i, hi⟩ else 0

theorem measurable_windowExtend (s : Set ℤ) :
    Measurable (windowExtend (E := E) s) := by
  classical
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases hi : i ∈ s
  · simp only [windowExtend, hi, dif_pos]
    exact measurable_pi_apply _
  · simp only [windowExtend, hi, dif_neg, not_false_eq_true]
    exact measurable_const

omit [MeasurableSpace E] in
theorem windowExtend_restrict_eq {s : Set ℤ} (ω : ℤ → E) {i : ℤ} (hi : i ∈ s) :
    windowExtend s (s.restrict ω) i = ω i := by
  classical
  simp [windowExtend, hi]

/-- A measurable function depending only on the window coordinates is window-measurable. -/
theorem measurable_layerWindow_of_depends {β : Type*} [MeasurableSpace β]
    {s : Set ℤ} {f : (ℤ → E) → β} (hf : Measurable f)
    (hdep : ∀ ω ω' : ℤ → E, (∀ i ∈ s, ω i = ω' i) → f ω = f ω') :
    Measurable[layerWindow E s] f := by
  have hfac : f = (f ∘ windowExtend s) ∘ s.restrict := by
    funext ω
    exact hdep ω _ (fun i hi => (windowExtend_restrict_eq ω hi).symm)
  rw [hfac]
  exact (hf.comp (measurable_windowExtend s)).comp (comap_measurable _)

/-- Set version of `measurable_layerWindow_of_depends`. -/
theorem measurableSet_layerWindow_of_depends {s : Set ℤ} {A : Set (ℤ → E)}
    (hA : MeasurableSet A)
    (hdep : ∀ ω ω' : ℤ → E, (∀ i ∈ s, ω i = ω' i) → (ω ∈ A ↔ ω' ∈ A)) :
    MeasurableSet[layerWindow E s] A := by
  have h := measurable_layerWindow_of_depends (s := s) (f := A.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hA) (fun ω ω' h => by
      by_cases hω : ω ∈ A
      · have hω' : ω' ∈ A := (hdep ω ω' h).1 hω
        simp [hω, hω']
      · have hω' : ω' ∉ A := fun h' => hω ((hdep ω ω' h).2 h')
        simp [hω, hω'])
  have hpre : A = A.indicator (fun _ => (1 : ℝ)) ⁻¹' {1} := by
    ext ω; by_cases hω : ω ∈ A <;> simp [hω]
  rw [hpre]
  exact h (measurableSet_singleton 1)

end Extend

end SubdiffusiveProcess.Lfgc
