module

public import SubdiffusiveProcess.Paper.Support.B7cReplacementTools

@[expose] public section





set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper
variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}

theorem aux_mfd_prop_gluing_construct_replacement
    (hd : 2 ≤ d)
    (hQcube : ∃ z : SpatialCoordinates d, ∃ R : ℝ, 0 < R ∧
      (Q : Set (SpatialCoordinates d)) = Metric.ball z (R / 2))
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Γ : DirichletForm.EnergyMeasure E)
    (alpha : ℝ) (halpha : 1 / 2 < alpha) (halpha1 : alpha < 1)
    (m : ℕ) (cent : Fin m → SpatialCoordinates d) (rad : Fin m → ℝ)
    (hrad : ∀ i : Fin m, 0 < rad i)
    (hcellQ : ∀ i : Fin m,
      closure (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)))
    (henlarge : ∀ i : Fin m,
      Metric.ball (cent i) (3 * rad i / 2) ⊆ (Q : Set (SpatialCoordinates d)))
    (hdisj : Pairwise fun i j : Fin m =>
      Disjoint (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))
        (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (hcent : ∀ (i : Fin m) (j : Fin d), ∃ s : ℚ, cent i j = (s : ℝ))
    (htri : ∀ i : Fin m, ∃ k : ℤ, rad i = (3 : ℝ) ^ k)
    (Dq : Fin m → Submodule ℝ (DomainL2 Q))
    (hDq : ∀ i : Fin m, DirichletForm.IsKilledDomain E
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (Dq i))
    (V : DomainL2 Q) (hV : V ∈ E.domain)
    (Vc : SpatialCoordinates d → ℝ)
    (hVcont : ContinuousOn Vc (closure (Q : Set (SpatialCoordinates d))))
    (hVrep : (V : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] Vc)
    (hVholder : ∀ i : Fin m, Lane4.IsHolderOn alpha
      (frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))) Vc)
    (Ui : Fin m → SpatialCoordinates d → ℝ)
    (UiL2 : Fin m → DomainL2 Q)
    (hUiDomain : ∀ i : Fin m, UiL2 i ∈ E.domain)
    (hUiRep : ∀ i : Fin m, (UiL2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] Ui i)
    (hUicont : ∀ i : Fin m, ContinuousOn (Ui i)
      (closure (Q : Set (SpatialCoordinates d))))
    (hUibdry : ∀ i : Fin m,
      ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), Ui i x = Vc x)
    (hZeroTrace : ∀ i : Fin m, ∀ (w : DomainL2 Q), w ∈ E.domain →
      ∀ (wc : SpatialCoordinates d → ℝ),
      ContinuousOn wc (closure (Q : Set (SpatialCoordinates d))) →
      ((w : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] wc) →
      (∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), wc x = 0) →
      ∀ (wq : DomainL2 Q),
      ((wq : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          Set.indicator (closure (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))) wc) →
      wq ∈ Dq i ∧ E.form wq wq = (Γ.measure w
        (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))).toReal)
 :
    ∃ V' : DomainL2 Q,
      let V'c := fun x => Vc x + ∑ i : Fin m,
        (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)).indicator
          (fun y => Ui i y - Vc y) x
      (V' : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V'c ∧
      (∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
        x ∉ ⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) →
          V'c x = Vc x) ∧
      (∀ i : Fin m, ∀ x ∈ (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)),
        V'c x = Ui i x) ∧
      V' ∈ E.domain ∧ ContinuousOn V'c (closure (Q : Set (SpatialCoordinates d))) := by
  classical
  let cells : Fin m → Set (SpatialCoordinates d) := fun i =>
    (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
  let corr : Fin m → DomainL2 Q := fun i =>
    localizeL2 (centeredCube (cent i) (rad i) (hrad i)).isOpen.measurableSet (UiL2 i - V)
  let V' : DomainL2 Q := V + ∑ i : Fin m, corr i
  let V'c := fun x => Vc x + ∑ i : Fin m, (cells i).indicator (fun y => Ui i y - Vc y) x
  have hcorr : ∀ i : Fin m, (corr i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        (cells i).indicator (fun y => Ui i y - Vc y) := by
    intro i
    filter_upwards [localizeL2_coeFn (centeredCube (cent i) (rad i) (hrad i)).isOpen.measurableSet
      (UiL2 i - V), Lp.coeFn_sub (UiL2 i) V, hUiRep i, hVrep] with x hx hs hu hv
    rw [hx]
    by_cases hxi : x ∈ cells i
    · rw [Set.indicator_of_mem hxi, Set.indicator_of_mem hxi, hs, Pi.sub_apply, hu, hv]
    · rw [Set.indicator_of_notMem hxi, Set.indicator_of_notMem hxi]
  have hsum : ((∑ i : Fin m, corr i : DomainL2 Q) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        (fun x => ∑ i : Fin m, (cells i).indicator (fun y => Ui i y - Vc y) x) := by
    filter_upwards [lane2_Lp_coeFn_sum corr Finset.univ, ae_all_iff.2 hcorr] with x hx hc
    rw [hx]
    exact Finset.sum_congr rfl (fun i _ => hc i)
  have hrep : (V' : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V'c := by
    filter_upwards [Lp.coeFn_add V (∑ i : Fin m, corr i), hsum, hVrep] with x hx hs hv
    rw [hx]
    change V x + (∑ i : Fin m, corr i) x = _
    rw [hv, hs]
  have hout : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      x ∉ ⋃ i : Fin m, cells i → V'c x = Vc x := by
    intro x _ hx
    have hzero : ∀ i : Fin m, (cells i).indicator (fun y => Ui i y - Vc y) x = 0 := by
      intro i
      exact Set.indicator_of_notMem (fun hi => hx (Set.mem_iUnion.mpr ⟨i, hi⟩)) _
    change Vc x + ∑ i : Fin m, (cells i).indicator (fun y => Ui i y - Vc y) x = Vc x
    rw [Finset.sum_eq_zero (fun i _ => hzero i), add_zero]
  have hin : ∀ i : Fin m, ∀ x ∈ cells i, V'c x = Ui i x := by
    intro i x hx
    have hsum : (∑ j : Fin m, (cells j).indicator (fun y => Ui j y - Vc y) x) =
        (cells i).indicator (fun y => Ui i y - Vc y) x := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        apply Set.indicator_of_notMem
        intro hxj
        exact Set.disjoint_left.mp (hdisj (Ne.symm hji)) hx hxj
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    change Vc x + ∑ j : Fin m, (cells j).indicator (fun y => Ui j y - Vc y) x = Ui i x
    rw [hsum, Set.indicator_of_mem hx]
    ring
  have hpatch := prop_gluing_replacement_patch hd hQcube E Γ alpha halpha halpha1
    m cent rad hrad hcellQ henlarge hdisj hcent htri Dq hDq V hV Vc hVcont hVrep hVholder
    Ui UiL2 hUiDomain hUiRep hUicont hUibdry hZeroTrace V' V'c hrep hout hin
  exact ⟨V', hrep, hout, hin, hpatch.1, hpatch.2⟩

end Paper
