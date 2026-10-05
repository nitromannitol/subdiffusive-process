module

public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.MeshError
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

lemma aux_prop_gluing_face_mass_residual_subset_frontier
    {d m : ℕ} (Q : Set (SpatialCoordinates d)) (C : Fin m → Set (SpatialCoordinates d))
    (hQopen : IsOpen Q) (hCopen : ∀ i, IsOpen (C i))
    (hcover : (⋃ i : Fin m, C i) =ᵐ[(volume : Measure (SpatialCoordinates d))] Q) :
    Q \ (⋃ i : Fin m, C i) ⊆ ⋃ i : Fin m, frontier (C i) := by
  intro x hx
  by_contra hnot
  have hxcl : x ∉ ⋃ i : Fin m, closure (C i) := by
    intro hxi
    rcases Set.mem_iUnion.mp hxi with ⟨i, hxi⟩
    apply hnot
    apply Set.mem_iUnion.mpr
    refine ⟨i, ?_⟩
    rw [hCopen i |>.frontier_eq]
    exact ⟨hxi, fun hxc => hx.2 (Set.mem_iUnion.mpr ⟨i, hxc⟩)⟩
  have hclosed : IsClosed (⋃ i : Fin m, closure (C i)) :=
    isClosed_iUnion_of_finite (fun i => isClosed_closure)
  have hopen : IsOpen (Q \ ⋃ i : Fin m, closure (C i)) := by
    rw [Set.sdiff_eq]
    exact hQopen.inter hclosed.isOpen_compl
  have hsub : (Q \ ⋃ i : Fin m, closure (C i)) ⊆ Q \ ⋃ i : Fin m, C i := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    intro hyC
    rcases Set.mem_iUnion.mp hyC with ⟨i, hyC⟩
    exact hy.2 (Set.mem_iUnion.mpr ⟨i, subset_closure hyC⟩)
  have hzero : volume (Q \ ⋃ i : Fin m, C i) = 0 := (ae_eq_set.mp hcover).2
  have hopen_zero : volume (Q \ ⋃ i : Fin m, closure (C i)) = 0 :=
    measure_mono_null hsub hzero
  exact (ne_of_gt (hopen.measure_pos volume ⟨x, hx.1, hxcl⟩)) hopen_zero



theorem prop_gluing_face_mass
    (d : ℕ)
    (_hd : 2 ≤ d)
    (Q : Opens (SpatialCoordinates d))
    (_hQcube : ∃ z : SpatialCoordinates d, ∃ R : ℝ, 0 < R ∧
      (Q : Set (SpatialCoordinates d)) = Metric.ball z (R / 2))
    (E : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (Γ : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E)
    (beta alpha : ℝ)
    (_hbeta : 1 / 2 < beta)
    (_hba : beta < alpha)
    (_halpha1 : alpha < 1)
    (m : ℕ)
    (cent : Fin m → SpatialCoordinates d)
    (rad : Fin m → ℝ)
    (hrad : ∀ i : Fin m, 0 < rad i)
    (_hcent : ∀ (i : Fin m) (j : Fin d), ∃ s : ℚ, cent i j = (s : ℝ))
    (_htri : ∀ i : Fin m, ∃ k : ℤ, rad i = (3 : ℝ) ^ k)
    (_hcellQ : ∀ i : Fin m,
      closure (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) ⊆ (Q : Set (SpatialCoordinates d)))
    (_henlarge : ∀ i : Fin m,
      Metric.ball (cent i) (3 * rad i / 2) ⊆ (Q : Set (SpatialCoordinates d)))
    (hdisj : Pairwise fun i j : Fin m =>
      Disjoint (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))
        (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d)))
    (V : DomainL2 Q)
    (_hV : V ∈ E.domain)
    (Vc : SpatialCoordinates d → ℝ)
    (_hVcont : ContinuousOn Vc (closure (Q : Set (SpatialCoordinates d))))
    (_hVrep : (V : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] Vc)
    (_hVholder : ∀ i : Fin m, _root_.SubdiffusiveProcess.EllipticRegularity.IsHolderOn alpha
      (frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))) Vc)
    (Lam : Fin m → ℝ)
    (UiL2 : Fin m → DomainL2 Q)
    (Uic : Fin m → SpatialCoordinates d → ℝ)
    (hUiDomain : ∀ i : Fin m, UiL2 i ∈ E.domain)
    (_hUiRep : ∀ i : Fin m, (UiL2 i : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] Uic i)
    (_hUiCont : ∀ i : Fin m, ContinuousOn (Uic i)
      (closure (Q : Set (SpatialCoordinates d))))
    (_hUiBoundary : ∀ i : Fin m,
      ∀ x ∈ frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), Uic i x = Vc x)
    (hUiEnergy : ∀ i : Fin m, (Γ.measure (UiL2 i)
      (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))).toReal = Lam i)
    (_hUiFace : ∀ i : Fin m, Γ.measure (UiL2 i)
      (frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))) = 0)
    (Dq : Fin m → Submodule ℝ (DomainL2 Q))
    (_hDq : ∀ i : Fin m, _root_.SubdiffusiveProcess.DirichletForm.IsKilledDomain E
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) (Dq i))
    (_hUiOrth : ∀ i : Fin m, ∀ φ : DomainL2 Q, φ ∈ Dq i →
      E.form (UiL2 i) φ = 0)
    (V' : DomainL2 Q)
    (V'c : SpatialCoordinates d → ℝ)
    (_hV'rep : (V' : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V'c)
    (_hV'out : ∀ x ∈ closure (Q : Set (SpatialCoordinates d)),
      x ∉ ⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) → V'c x = Vc x)
    (_hV'in : ∀ i : Fin m,
      ∀ x ∈ (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)), V'c x = Uic i x)
    (_hV'dom : V' ∈ E.domain)
    (_hV'cont : ContinuousOn V'c (closure (Q : Set (SpatialCoordinates d))))
    (hCellMeasure : ∀ i : Fin m, ∀ B : Set (SpatialCoordinates d),
      MeasurableSet B →
      B ⊆ (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)) →
      Γ.measure V' B = Γ.measure (UiL2 i) B)
    (hOutsideMeasure : ∀ B : Set (SpatialCoordinates d), MeasurableSet B →
      B ⊆ (Q : Set (SpatialCoordinates d)) \
        (⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
          Set (SpatialCoordinates d))) →
      Γ.measure V' B = Γ.measure V B)
    (hface : ∀ i : Fin m,
      Γ.measure V (frontier (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d))) = 0)
    (Q' : Opens (SpatialCoordinates d))
    (_hQ'cube : ∃ z : SpatialCoordinates d, ∃ R : ℝ, 0 < R ∧
      (Q' : Set (SpatialCoordinates d)) = Metric.ball z (R / 2))
    (hQ'sub : (Q' : Set (SpatialCoordinates d)) ⊆
      (Q : Set (SpatialCoordinates d)))
    (hcellsub : ∀ i : Fin m,
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ⊆
        (Q' : Set (SpatialCoordinates d)))
    (hcover : (⋃ i : Fin m, (centeredCube (cent i) (rad i) (hrad i) :
        Set (SpatialCoordinates d)))
      =ᵐ[(volume : Measure (SpatialCoordinates d))]
        (Q' : Set (SpatialCoordinates d))) :
    (Γ.measure V' (Q' : Set (SpatialCoordinates d))).toReal
      = ∑ i : Fin m, Lam i := by
  let C : Fin m → Set (SpatialCoordinates d) := fun i =>
    (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
  let U : Set (SpatialCoordinates d) := ⋃ i : Fin m, C i
  have hCopen : ∀ i : Fin m, IsOpen (C i) := by
    intro i
    exact (centeredCube (cent i) (rad i) (hrad i)).isOpen
  have hCdisj : Pairwise (Function.onFun Disjoint C) := by
    intro i j hij
    simpa [C] using hdisj hij
  have hcoverC : U =ᵐ[(volume : Measure (SpatialCoordinates d))]
      (Q' : Set (SpatialCoordinates d)) := by
    simpa [U, C] using hcover
  have hresidual_frontier :
      (Q' : Set (SpatialCoordinates d)) \ U ⊆
        ⋃ i : Fin m, frontier (C i) := by
    exact aux_prop_gluing_face_mass_residual_subset_frontier
      (Q' : Set (SpatialCoordinates d)) C Q'.isOpen hCopen hcoverC
  have hfrontier_zero :
      Γ.measure V (⋃ i : Fin m, frontier (C i)) = 0 := by
    apply measure_iUnion_null
    intro i
    simpa [C] using hface i
  have hresidual_zero :
      Γ.measure V ((Q' : Set (SpatialCoordinates d)) \ U) = 0 := by
    apply measure_mono_null hresidual_frontier
    exact hfrontier_zero
  have hresidual_meas :
      MeasurableSet ((Q' : Set (SpatialCoordinates d)) \ U) := by
    apply Q'.isOpen.measurableSet.diff
    exact (isOpen_iUnion hCopen).measurableSet
  have hresidual_sub :
      ((Q' : Set (SpatialCoordinates d)) \ U) ⊆
        (Q : Set (SpatialCoordinates d)) \ U := by
    intro x hx
    exact ⟨hQ'sub hx.1, hx.2⟩
  have hresidual_zero' :
      Γ.measure V' ((Q' : Set (SpatialCoordinates d)) \ U) = 0 := by
    rw [hOutsideMeasure ((Q' : Set (SpatialCoordinates d)) \ U) hresidual_meas
      hresidual_sub]
    exact hresidual_zero
  have hQ'union :
      (Q' : Set (SpatialCoordinates d)) = U ∪
        ((Q' : Set (SpatialCoordinates d)) \ U) := by
    ext x
    by_cases hx : x ∈ U
    · rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
      constructor
      · intro
        exact Or.inl hx
      · intro
        exact hcellsub i hxi
    · simp [hx]
  have hQ'measure :
      Γ.measure V' (Q' : Set (SpatialCoordinates d)) =
        Γ.measure V' U +
          Γ.measure V' ((Q' : Set (SpatialCoordinates d)) \ U) := by
    calc
      Γ.measure V' (Q' : Set (SpatialCoordinates d)) =
          Γ.measure V' (U ∪ ((Q' : Set (SpatialCoordinates d)) \ U)) :=
        congrArg (Γ.measure V') hQ'union
      _ = Γ.measure V' U +
          Γ.measure V' ((Q' : Set (SpatialCoordinates d)) \ U) :=
        measure_union disjoint_sdiff_right hresidual_meas
  have hQ'measure' :
      Γ.measure V' (Q' : Set (SpatialCoordinates d)) = Γ.measure V' U := by
    rw [hQ'measure, hresidual_zero', add_zero]
  have hUmeasure :
      Γ.measure V' U = ∑ i : Fin m, Γ.measure (UiL2 i) (C i) := by
    rw [show U = ⋃ i : Fin m, C i by rfl]
    rw [measure_iUnion hCdisj (fun i => (hCopen i).measurableSet)]
    rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro i hi
    exact hCellMeasure i (C i) (hCopen i).measurableSet (by rfl)
  have hmass :
      Γ.measure V' (Q' : Set (SpatialCoordinates d)) =
        ∑ i : Fin m, Γ.measure (UiL2 i) (C i) := by
    rw [hQ'measure', hUmeasure]
  calc
    (Γ.measure V' (Q' : Set (SpatialCoordinates d))).toReal =
        (∑ i : Fin m, Γ.measure (UiL2 i) (C i)).toReal :=
      congrArg ENNReal.toReal hmass
    _ = ∑ i : Fin m, (Γ.measure (UiL2 i) (C i)).toReal := by
      exact ENNReal.toReal_sum (fun i _ => Γ.measure_ne_top (hUiDomain i) (C i))
    _ = ∑ i : Fin m, Lam i := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa [C] using hUiEnergy i

end SubdiffusiveProcess.Paper
