import SubdiffusiveProcess.Lane4.Carriers
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Constructions.Pi
import SubdiffusiveProcess.Paper.lane4_neumann_boundary_identity_face_trace
import SubdiffusiveProcess.Paper.lane4_neumann_boundary_identity_frontier_hn_decomposition
import SubdiffusiveProcess.Paper.lane4_neumann_boundary_identity_weak_ftc

open MeasureTheory TopologicalSpace Set
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section
namespace Paper

lemma aux_lane4_neumann_boundary_identity_boundary_assembly_insertNth_measurableEmbedding
    {n : ℕ} (i : Fin (n + 1)) (c : ℝ) :
    MeasurableEmbedding (fun y : SpatialCoordinates n =>
      @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i c y) := by
  let e : SpatialCoordinates n → SpatialCoordinates (n + 1) := fun y =>
    @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i c y
  have he : Measurable e := by
    refine measurable_pi_iff.2 (fun j => ?_)
    classical
    by_cases hji : j = i
    · subst hji
      simp [e]
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
      subst hk
      simpa [e] using (measurable_pi_apply k)
  have hrange : Set.range e = {x | x i = c} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      simp [e]
    · intro hx
      refine ⟨Fin.removeNth i x, ?_⟩
      apply Fin.insertNth_eq_iff.2
      constructor
      · exact hx.symm
      · rfl
  have hri : MeasurableSet (Set.range e) := by
    rw [hrange]
    exact measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  change MeasurableEmbedding e
  let g : Set.range e → SpatialCoordinates n := fun x j => x.1 (i.succAbove j)
  have hg : Measurable g := measurable_pi_iff.2 (fun j =>
    (measurable_pi_apply (i.succAbove j)).comp measurable_subtype_coe)
  have hleft : Function.LeftInverse g (Set.rangeFactorization e) := by
    intro y
    funext j
    simp [g, e]
  exact MeasurableEmbedding.of_measurable_inverse_on_range he hri hg hleft

lemma aux_lane4_neumann_boundary_identity_boundary_assembly_face_intersection_ae
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≠ j) (c d : ℝ) :
    ∀ᵐ y : SpatialCoordinates n ∂(volume.restrict
      (unitNeumannCube n : Set (SpatialCoordinates n))),
      (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i c y) j ≠ d := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
  have hz : volume ({y : SpatialCoordinates n | y k = d}) = 0 := by
    simpa using (Measure.pi_hyperplane (μ := fun _ : Fin n => (volume : Measure ℝ)) k d)
  rw [ae_iff]
  simp only [not_ne_iff]
  have hz' : (volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n)))
      {y : SpatialCoordinates n | y k = d} = 0 := by
    rw [Measure.restrict_apply (measurableSet_eq_fun (measurable_pi_apply k) measurable_const)]
    exact measure_mono_null inter_subset_left hz
  have hsub : {y : SpatialCoordinates n |
      (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i c y) j = d} ⊆
      {y : SpatialCoordinates n | y k = d} := by
    intro y hy
    change (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i c y) j = d at hy
    rw [← hk, Fin.insertNth_apply_succAbove] at hy
    exact hy
  exact measure_mono_null hsub hz'

/-- Statement-only fine child: integrability and exact assembly of the
coordinate face flux into the boundary integral. It consumes the face and
frontier constructions through its statement-only proof interface. -/
theorem lane4_neumann_boundary_identity_boundary_assembly
    (n : ℕ) (hn : 1 ≤ n) :
    let Q : Opens (SpatialCoordinates (n + 1)) := unitNeumannCube (n + 1)
    let Qface : Opens (SpatialCoordinates n) := unitNeumannCube n
    let μface : Measure (SpatialCoordinates n) :=
      volume.restrict (Qface : Set (SpatialCoordinates n))
    let muBoundary : Measure (SpatialCoordinates (n + 1)) :=
      (MeasureTheory.Measure.hausdorffMeasure (n : ℝ)).restrict
        (frontier (Q : Set (SpatialCoordinates (n + 1))))
    let normal : SpatialCoordinates (n + 1) → SpatialCoordinates (n + 1) :=
      fun x i => if x i = 1 then 1 else if x i = 0 then -1 else 0
    ∀ (Tr : (i : Fin (n + 1)) → (side : Bool) →
        weakSobolevGraph Q →L[ℝ] DomainL2 Qface) (Ct : ℝ),
      0 < Ct →
      (∀ (i : Fin (n + 1)) (side : Bool) (v : weakSobolevGraph Q),
        ‖Tr i side v‖ ≤ Ct * ‖v‖) →
      (∀ (φ : SpatialCoordinates (n + 1) → ℝ),
        ContDiff ℝ 1 φ →
          ∀ (v : weakSobolevGraph Q),
            ((v : SobolevData Q).1 : SpatialCoordinates (n + 1) → ℝ) =ᵐ[
              volume.restrict (Q : Set (SpatialCoordinates (n + 1)))] φ →
              ∀ (i : Fin (n + 1)) (side : Bool),
                ((Tr i side v : DomainL2 Qface) : SpatialCoordinates n → ℝ) =ᵐ[μface]
                  (fun y => φ (Fin.insertNth i (if side then 1 else 0) y))) →
      muBoundary =
        ∑ i : Fin (n + 1),
          (Measure.map (fun y : SpatialCoordinates n =>
              @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (1 : ℝ) y) μface +
            Measure.map (fun y : SpatialCoordinates n =>
              @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (0 : ℝ) y) μface) →
      (let traceBoundary : weakSobolevGraph Q → SpatialCoordinates (n + 1) → ℝ :=
          fun v x =>
            ∑ i : Fin (n + 1),
              if x i = 1 then
                ((Tr i true v : DomainL2 Qface) : SpatialCoordinates n → ℝ)
                  (fun j : Fin n => x (i.succAbove j))
              else if x i = 0 then
                ((Tr i false v : DomainL2 Qface) : SpatialCoordinates n → ℝ)
                  (fun j : Fin n => x (i.succAbove j))
              else 0
        ∀ (v : weakSobolevGraph Q) (p : SpatialCoordinates (n + 1)),
          Integrable
              (fun x =>
                (∑ i : Fin (n + 1), p i * normal x i) * traceBoundary v x)
              muBoundary ∧
            (∫ x, (∑ i : Fin (n + 1), p i * normal x i) * traceBoundary v x ∂muBoundary) =
              ∑ i : Fin (n + 1),
                p i * ∫ x in (Q : Set (SpatialCoordinates (n + 1))),
                  (sobolevGradient (v : SobolevData Q) i) x) := by
  dsimp
  intros Tr Ct hCt hbound htrace hdecomp v p
  let F : SpatialCoordinates (n + 1) → ℝ := fun x =>
    (∑ i : Fin (n + 1), p i * (if x i = 1 then 1 else if x i = 0 then -1 else 0)) *
      (∑ i : Fin (n + 1),
        if x i = 1 then
          ((Tr i true v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ)
            (fun j : Fin n => x (i.succAbove j))
        else if x i = 0 then
          ((Tr i false v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ)
            (fun j : Fin n => x (i.succAbove j))
        else 0)
  change Integrable F ((MeasureTheory.Measure.hausdorffMeasure (n : ℝ)).restrict
      (frontier (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1)))) ) ∧
    (∫ x, F x ∂((MeasureTheory.Measure.hausdorffMeasure (n : ℝ)).restrict
      (frontier (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))))) =
      ∑ i : Fin (n + 1), p i * ∫ x in (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))),
        (sobolevGradient (v : SobolevData (unitNeumannCube (n + 1))) i) x)
  have hcross : ∀ (i : Fin (n + 1)) (c : ℝ), ∀ᵐ y : SpatialCoordinates n ∂(volume.restrict
      (unitNeumannCube n : Set (SpatialCoordinates n))),
      ∀ j : Fin (n + 1), j ≠ i →
        (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i c y) j ≠ 1 ∧
          (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i c y) j ≠ 0 := by
    intro i
    intro c
    rw [ae_all_iff]
    intro j
    by_cases hji : j = i
    · simp [hji]
    · have hij : i ≠ j := fun h => hji h.symm
      exact ((aux_lane4_neumann_boundary_identity_boundary_assembly_face_intersection_ae
        i j hij c 1).and
        (aux_lane4_neumann_boundary_identity_boundary_assembly_face_intersection_ae
          i j hij c 0)).mono (fun y h _ => h)
  have hfront : ∀ i : Fin (n + 1), ∀ᵐ y : SpatialCoordinates n ∂(volume.restrict
      (unitNeumannCube n : Set (SpatialCoordinates n))),
      F (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 1 y) =
        p i * ((Tr i true v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ) y := by
    intro i
    filter_upwards [hcross i 1] with y hy
    have hnormal :
        (∑ k : Fin (n + 1), p k *
          (if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 1 y) k = 1 then 1
           else if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 1 y) k = 0 then -1 else 0)) =
          p i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b hb hbi
        have h := hy b hbi
        simp [h.1, h.2]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    have htrace :
        (∑ k : Fin (n + 1),
          if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 1 y) k = 1 then
            ((Tr k true v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ)
              (fun j : Fin n => (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 1 y)
                (k.succAbove j))
          else if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 1 y) k = 0 then
            ((Tr k false v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ)
              (fun j : Fin n => (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 1 y)
                (k.succAbove j))
          else 0) =
          ((Tr i true v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ) y := by
      rw [Finset.sum_eq_single i]
      · simp [Fin.insertNth_apply_succAbove]
      · intro b hb hbi
        have h := hy b hbi
        simp [h.1, h.2]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    change
      (∑ k : Fin (n + 1), p k *
          (if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 1 y) k = 1 then 1
           else if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 1 y) k = 0 then -1 else 0)) *
        (∑ k : Fin (n + 1),
          if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 1 y) k = 1 then
            ((Tr k true v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ)
              (fun j : Fin n => (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 1 y)
                (k.succAbove j))
          else if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 1 y) k = 0 then
            ((Tr k false v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ)
              (fun j : Fin n => (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 1 y)
                (k.succAbove j))
          else 0) =
        p i * ((Tr i true v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ) y
    simpa only [hnormal, htrace]
  have hback : ∀ i : Fin (n + 1), ∀ᵐ y : SpatialCoordinates n ∂(volume.restrict
      (unitNeumannCube n : Set (SpatialCoordinates n))),
      F (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 0 y) =
        -p i * ((Tr i false v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ) y := by
    intro i
    filter_upwards [hcross i 0] with y hy
    have hnormal :
        (∑ k : Fin (n + 1), p k *
          (if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 0 y) k = 1 then 1
           else if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 0 y) k = 0 then -1 else 0)) =
          -p i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b hb hbi
        have h := hy b hbi
        simp [h.1, h.2]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    have htrace :
        (∑ k : Fin (n + 1),
          if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 0 y) k = 1 then
            ((Tr k true v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ)
              (fun j : Fin n => (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 0 y)
                (k.succAbove j))
          else if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 0 y) k = 0 then
            ((Tr k false v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ)
              (fun j : Fin n => (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 0 y)
                (k.succAbove j))
          else 0) =
          ((Tr i false v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ) y := by
      rw [Finset.sum_eq_single i]
      · simp [Fin.insertNth_apply_succAbove]
      · intro b hb hbi
        have h := hy b hbi
        simp [h.1, h.2]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    change
      (∑ k : Fin (n + 1), p k *
          (if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 0 y) k = 1 then 1
           else if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 0 y) k = 0 then -1 else 0)) *
        (∑ k : Fin (n + 1),
          if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 0 y) k = 1 then
            ((Tr k true v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ)
              (fun j : Fin n => (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 0 y)
                (k.succAbove j))
          else if (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 0 y) k = 0 then
            ((Tr k false v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ)
              (fun j : Fin n => (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 0 y)
                (k.succAbove j))
          else 0) =
        -p i * ((Tr i false v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ) y
    simpa only [hnormal, htrace]
  have htrInt : ∀ (i : Fin (n + 1)) (side : Bool),
      Integrable ((Tr i side v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ)
        (volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n))) := by
    intro i side
    exact (Lp.memLp (Tr i side v)).integrable (by norm_num)
  have hFfront : ∀ i : Fin (n + 1),
      Integrable F (Measure.map (fun y : SpatialCoordinates n =>
        @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (1 : ℝ) y)
        (volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n)))) := by
    intro i
    apply (aux_lane4_neumann_boundary_identity_boundary_assembly_insertNth_measurableEmbedding
      i 1).integrable_map_iff.mpr
    refine (htrInt i true).const_mul (p i) |>.congr ?_
    filter_upwards [hfront i] with y hy
    exact hy.symm
  have hFback : ∀ i : Fin (n + 1),
      Integrable F (Measure.map (fun y : SpatialCoordinates n =>
        @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (0 : ℝ) y)
        (volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n)))) := by
    intro i
    apply (aux_lane4_neumann_boundary_identity_boundary_assembly_insertNth_measurableEmbedding
      i 0).integrable_map_iff.mpr
    refine (htrInt i false).const_mul (-p i) |>.congr ?_
    filter_upwards [hback i] with y hy
    exact hy.symm
  have hFsum : Integrable F
      (∑ i : Fin (n + 1),
        (Measure.map (fun y : SpatialCoordinates n =>
          @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (1 : ℝ) y)
            (volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n))) +
         Measure.map (fun y : SpatialCoordinates n =>
          @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (0 : ℝ) y)
            (volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n))))) := by
    refine integrable_finset_sum_measure.2 ?_
    intro i hi
    exact (hFfront i).add_measure (hFback i)
  let μB : Measure (SpatialCoordinates (n + 1)) :=
    (MeasureTheory.Measure.hausdorffMeasure (n : ℝ)).restrict
      (frontier (unitNeumannCube (n + 1) : Set (SpatialCoordinates (n + 1))))
  let μi : Fin (n + 1) → Measure (SpatialCoordinates (n + 1)) := fun i =>
    Measure.map (fun y : SpatialCoordinates n =>
      @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (1 : ℝ) y)
        (volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n))) +
    Measure.map (fun y : SpatialCoordinates n =>
      @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (0 : ℝ) y)
        (volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n)))
  have hdecomp' : μB = ∑ i : Fin (n + 1), μi i := by
    simpa [μB, μi] using hdecomp
  have hFsum' : Integrable F (∑ i : Fin (n + 1), μi i) := by
    simpa [μi] using hFsum
  have hFi : ∀ i : Fin (n + 1), Integrable F (μi i) := by
    intro i
    simpa [μi] using (hFfront i).add_measure (hFback i)
  have hFboundary : Integrable F μB := by
    rw [hdecomp']
    exact hFsum'
  have hIntegralBoundary :
      (∫ x, F x ∂μB) = ∑ i : Fin (n + 1), ∫ x, F x ∂μi i := by
    calc
      (∫ x, F x ∂μB) = ∫ x, F x ∂(∑ i : Fin (n + 1), μi i) := by rw [hdecomp']
      _ = ∑ i : Fin (n + 1), ∫ x, F x ∂μi i := by
        simpa using (integral_finset_sum_measure (s := Finset.univ)
          (fun i _ => hFi i))
  have hfrontInt : ∀ i : Fin (n + 1),
      (∫ x, F x ∂(Measure.map (fun y : SpatialCoordinates n =>
        @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (1 : ℝ) y)
          (volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n)))) =
        p i * ∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
          ((Tr i true v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ) y) := by
    intro i
    calc
      (∫ x, F x ∂(Measure.map (fun y : SpatialCoordinates n =>
          @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (1 : ℝ) y)
            (volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n)))) =
          ∫ y, F (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 1 y)
            ∂(volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n)))) :=
        (aux_lane4_neumann_boundary_identity_boundary_assembly_insertNth_measurableEmbedding
          i 1).integral_map F
      _ = ∫ y, p i *
          ((Tr i true v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ) y
            ∂(volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n))) :=
        integral_congr_ae (hfront i)
      _ = _ := by
        rw [integral_const_mul]
  have hbackInt : ∀ i : Fin (n + 1),
      (∫ x, F x ∂(Measure.map (fun y : SpatialCoordinates n =>
        @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (0 : ℝ) y)
          (volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n)))) =
        -p i * ∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
          ((Tr i false v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ) y) := by
    intro i
    calc
      (∫ x, F x ∂(Measure.map (fun y : SpatialCoordinates n =>
          @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (0 : ℝ) y)
            (volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n)))) =
          ∫ y, F (@Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i 0 y)
            ∂(volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n)))) :=
        (aux_lane4_neumann_boundary_identity_boundary_assembly_insertNth_measurableEmbedding
          i 0).integral_map F
      _ = ∫ y, -p i *
          ((Tr i false v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ) y
            ∂(volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n))) :=
        integral_congr_ae (hback i)
      _ = _ := by
        rw [integral_const_mul]
  have hBoundaryFace :
      (∫ x, F x ∂μB) = ∑ i : Fin (n + 1), p i *
        ((∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
          ((Tr i true v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ) y) -
         (∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
          ((Tr i false v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ) y)) := by
    calc
      (∫ x, F x ∂μB) = ∑ i : Fin (n + 1), ∫ x, F x ∂μi i := hIntegralBoundary
      _ = ∑ i : Fin (n + 1),
          (∫ x, F x ∂(Measure.map (fun y : SpatialCoordinates n =>
            @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (1 : ℝ) y)
              (volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n)))) +
           ∫ x, F x ∂(Measure.map (fun y : SpatialCoordinates n =>
            @Fin.insertNth n (fun _ : Fin (n + 1) => ℝ) i (0 : ℝ) y)
              (volume.restrict (unitNeumannCube n : Set (SpatialCoordinates n))))) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [μi]
        exact integral_add_measure (hFfront i) (hFback i)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = p i * (∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
                ((Tr i true v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ) y) +
              (-p i * (∫ y in (unitNeumannCube n : Set (SpatialCoordinates n)),
                ((Tr i false v : DomainL2 (unitNeumannCube n)) : SpatialCoordinates n → ℝ) y)) :=
            congrArg₂ (· + ·) (hfrontInt i) (hbackInt i)
          _ = _ := by ring
  have hFTC := lane4_neumann_boundary_identity_weak_ftc n hn Tr htrace v p
  constructor
  · exact hFboundary
  · simpa [μB] using hBoundaryFace.trans hFTC.symm

end Paper
