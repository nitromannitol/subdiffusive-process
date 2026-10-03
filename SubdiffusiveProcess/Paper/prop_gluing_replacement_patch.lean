module

public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Lane2.BoundaryPackaging
public import SubdiffusiveProcess.Lane2.NativeBridge
public import SubdiffusiveProcess.Lane2.ResponseMarkov
public import SubdiffusiveProcess.Lane2.BoundaryResponse
public import SubdiffusiveProcess.Lane2.MeshError
public import SubdiffusiveProcess.Lane2.ExternalInputs
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.Lane4.Carriers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Paper.prop_killed_consistency
public import SubdiffusiveProcess.Paper.lem_truncation
public import SubdiffusiveProcess.Variational.LocalizedL2

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_prop_gluing_replacement_patch_finite_closed_union
    {α β ι : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : α → β) (s : Finset ι) (t : ι → Set α)
    (htclosed : ∀ i ∈ s, IsClosed (t i))
    (htcont : ∀ i ∈ s, ContinuousOn f (t i)) :
    ContinuousOn f (⋃ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.set_biUnion_insert]
      exact (htcont a (by simp)).union_of_isClosed
        (ih (fun i hi => htclosed i (by simp [hi]))
          (fun i hi => htcont i (by simp [hi])))
        (htclosed a (by simp))
        (isClosed_biUnion_finset (fun i hi => htclosed i (by simp [hi])))

variable {d : ℕ} {Q : Opens (SpatialCoordinates d)}



theorem prop_gluing_replacement_patch
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
    (V' : DomainL2 Q) (V'c : SpatialCoordinates d → ℝ)
    (hV'rep : (V' : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V'c)
    (hV'out : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      x ∉ ⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) → V'c x = Vc x)
    (hV'in : ∀ i : Fin m,
      ∀ x ∈ (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), V'c x = Ui i x) :
    V' ∈ E.domain ∧
      ContinuousOn V'c (closure (Q : Set (SpatialCoordinates d))) := by
  classical
  let corr : Fin m → DomainL2 Q := fun i =>
    localizeL2
      ((isClosed_closure : IsClosed (closure (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)))).measurableSet)
      (UiL2 i - V)
  have hdiff : ∀ i : Fin m,
      ((UiL2 i - V : DomainL2 Q) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          (fun x => Ui i x - Vc x) := by
    intro i
    filter_upwards [Lp.coeFn_sub (UiL2 i) V, hUiRep i, hVrep] with x hsub hui hv
    calc
      ((UiL2 i - V : DomainL2 Q) : SpatialCoordinates d → ℝ) x =
          ((UiL2 i : DomainL2 Q) : SpatialCoordinates d → ℝ) x -
            ((V : DomainL2 Q) : SpatialCoordinates d → ℝ) x := hsub
      _ = Ui i x - Vc x := by rw [hui, hv]
  have hcorr_rep : ∀ i : Fin m,
      ((corr i : DomainL2 Q) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          Set.indicator
            (closure (centeredCube (cent i) (rad i) (hrad i) :
              Set (SpatialCoordinates d)))
            (fun x => Ui i x - Vc x) := by
    intro i
    let hs : MeasurableSet (closure (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))) :=
      (isClosed_closure : IsClosed (closure (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)))).measurableSet
    change localizeL2 hs (UiL2 i - V) =ᵐ[_] _
    filter_upwards [localizeL2_coeFn hs (UiL2 i - V), hdiff i] with x hx hxi
    rw [hx]
    by_cases hsx : x ∈ closure (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))
    · simp only [Set.indicator_of_mem hsx]
      exact hxi
    · simp only [Set.indicator_of_notMem hsx]
  have hcorr_killed : ∀ i : Fin m, corr i ∈ Dq i := by
    intro i
    have hzero := hZeroTrace i (UiL2 i - V)
      (E.domain.sub_mem (hUiDomain i) hV)
      (fun x => Ui i x - Vc x)
      ((hUicont i).sub hVcont)
      (hdiff i)
      (by
        intro x hx
        change Ui i x - Vc x = 0
        rw [hUibdry i x hx]
        ring)
      (corr i)
      (hcorr_rep i)
    exact hzero.1
  have hcorr_domain : ∀ i : Fin m, corr i ∈ E.domain := by
    intro i
    exact (hDq i).le_domain (hcorr_killed i)
  let W : DomainL2 Q := V + ∑ i : Fin m, corr i
  have hWdomain : W ∈ E.domain := by
    dsimp [W]
    exact E.domain.add_mem hV
      (Submodule.sum_mem E.domain (fun i _ => hcorr_domain i))
  have hcellopen : ∀ i : Fin m,
      IsOpen (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) := by
    intro i
    exact (centeredCube (cent i) (rad i) (hrad i)).isOpen
  have hcellrep : ∀ (i : Fin m) (x : SpatialCoordinates d),
      x ∈ closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) →
        V'c x = Ui i x := by
    intro i x hx
    by_cases hxin : x ∈ (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
    · exact hV'in i x hxin
    · have hfront : x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)) := by
        rw [(hcellopen i).frontier_eq]
        exact ⟨hx, hxin⟩
      have hnotunion : x ∉ ⋃ j : Fin m,
          (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)) := by
        intro hxu
        obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxu
        by_cases hji : j = i
        · exact hxin (hji ▸ hxj)
        · exact (Set.disjoint_left.mp
            ((hdisj (Ne.symm hji)).frontier_left (hcellopen j))) hfront hxj
      have hxQ : x ∈ closure (Q : Set (SpatialCoordinates d)) :=
        subset_closure (hcellQ i hx)
      exact (hV'out x hxQ hnotunion).trans (hUibdry i x hfront).symm
  let Uall : Set (SpatialCoordinates d) := ⋃ i : Fin m,
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
  let T : Set (SpatialCoordinates d) := closure (Q : Set (SpatialCoordinates d)) \ Uall
  have hTclosed : IsClosed T := by
    dsimp [T, Uall]
    exact isClosed_closure.sdiff (isOpen_iUnion hcellopen)
  have hTcont : ContinuousOn V'c T := by
    apply (hVcont.mono (by
      intro x hx
      exact hx.1)).congr
    intro x hx
    exact hV'out x hx.1 hx.2
  have hcellcont : ∀ i : Fin m,
      ContinuousOn V'c (closure (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))) := by
    intro i
    apply ((hUicont i).mono (hcellQ i |>.trans subset_closure)).congr
    intro x hx
    exact hcellrep i x hx
  have hclosedUnion : IsClosed (⋃ i : Fin m,
      closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))) :=
    isClosed_iUnion_of_finite (fun i => isClosed_closure)
  have hunioncont : ContinuousOn V'c (⋃ i : Fin m,
      closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))) := by
    simpa using
      (aux_prop_gluing_replacement_patch_finite_closed_union V'c (Finset.univ)
        (fun i : Fin m => closure (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d)))
        (fun i _ => isClosed_closure)
        (fun i _ => hcellcont i))
  have hcover : T ∪ ⋃ i : Fin m,
      closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) =
        closure (Q : Set (SpatialCoordinates d)) := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx.1
      · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
        exact subset_closure (hcellQ i hxi)
    · intro hx
      by_cases hxu : x ∈ Uall
      · right
        obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxu
        exact Set.mem_iUnion.mpr ⟨i, subset_closure hxi⟩
      · left
        exact ⟨hx, hxu⟩
  have hV'cont : ContinuousOn V'c (closure (Q : Set (SpatialCoordinates d))) := by
    rw [← hcover]
    exact hTcont.union_of_isClosed hunioncont hTclosed hclosedUnion
  have hsumrep :
      ((∑ i : Fin m, corr i : DomainL2 Q) : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          (fun x => ∑ i : Fin m,
            Set.indicator
              (closure (centeredCube (cent i) (rad i) (hrad i) :
                Set (SpatialCoordinates d)))
              (fun y => Ui i y - Vc y) x) := by
    have hsum := lane2_Lp_coeFn_sum corr (Finset.univ)
    have hall := (ae_all_iff.2 (fun i => hcorr_rep i))
    filter_upwards [hsum, hall] with x hx hxi
    rw [hx]
    apply Finset.sum_congr rfl
    intro i hi
    exact hxi i
  have hWrep :
      (W : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
          (fun x => Vc x + ∑ i : Fin m,
            Set.indicator
              (closure (centeredCube (cent i) (rad i) (hrad i) :
                Set (SpatialCoordinates d)))
              (fun y => Ui i y - Vc y) x) := by
    have hadd := Lp.coeFn_add V (∑ i : Fin m, corr i)
    filter_upwards [hadd, hsumrep, hVrep] with x hx hsum hv
    rw [hx]
    simp only [Pi.add_apply]
    rw [hv, hsum]
  have hpoint : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      Vc x + ∑ i : Fin m,
        Set.indicator
          (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
          (fun y => Ui i y - Vc y) x = V'c x := by
    intro x hxQ
    by_cases hxu : x ∈ Uall
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxu
      have hsum0 : (∑ j : Fin m,
          Set.indicator
            (closure (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
            (fun y => Ui j y - Vc y) x) =
          Set.indicator
            (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
            (fun y => Ui i y - Vc y) x := by
        refine (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin m)))
          (f := fun j : Fin m =>
            Set.indicator
              (closure (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
              (fun y => Ui j y - Vc y) x) i) ?_ ?_
        · intro j hj hji
          rw [Set.indicator_of_notMem]
          intro hxj
          exact (Set.disjoint_left.mp
            ((hdisj (Ne.symm hji)).closure_right (hcellopen i))) hxi hxj
        · simp
      have hsum : (∑ j : Fin m,
          Set.indicator
            (closure (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
            (fun y => Ui j y - Vc y) x) = Ui i x - Vc x := by
        rw [hsum0, Set.indicator_of_mem (subset_closure hxi)]
      rw [hsum, hV'in i x hxi]
      ring
    · have hzero : ∀ i : Fin m,
          Set.indicator
              (closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)))
              (fun y => Ui i y - Vc y) x = 0 := by
        intro i
        by_cases hci : x ∈ closure (centeredCube (cent i) (rad i) (hrad i) :
            Set (SpatialCoordinates d))
        · have hni : x ∉ (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) := by
            intro hxi
            exact hxu (Set.mem_iUnion.mpr ⟨i, hxi⟩)
          have hfront : x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
              Set (SpatialCoordinates d)) := by
            rw [(hcellopen i).frontier_eq]
            exact ⟨hci, hni⟩
          rw [Set.indicator_of_mem hci, sub_eq_zero.mpr (hUibdry i x hfront)]
        · exact Set.indicator_of_notMem hci _
      rw [Finset.sum_eq_zero (fun i _ => hzero i), add_zero, hV'out x hxQ hxu]
  have hWV' : W = V' := by
    apply Lp.ext
    filter_upwards [hWrep, hV'rep,
      ae_restrict_mem (Q.isOpen.measurableSet)] with x hx hxp hxQ
    rw [hx, hxp]
    exact hpoint x (subset_closure hxQ)
  constructor
  · rw [← hWV']
    exact hWdomain
  · exact hV'cont

end Paper

