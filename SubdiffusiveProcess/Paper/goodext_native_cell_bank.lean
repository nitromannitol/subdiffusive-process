module

public import SubdiffusiveProcess.Paper.inputs_classical_h1_mesh_gluing
public import SubdiffusiveProcess.Sobolev.NativeRepresentativeData
public import SubdiffusiveProcess.Sobolev.ContinuousNativeRepresentative

@[expose] public section

/-! Glue continuous weak Sobolev cell data while retaining their exact gradients.
The shared trace and outer zero trace are explicit; this module asserts
neither coefficient estimates nor convergence.
-/
open MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Compatible continuous weak cell data assemble into a killed parent datum with their exact restricted Sobolev data. -/
theorem goodext_native_cell_bank
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (J : ℕ)
    (g : SpatialCoordinates d → ℝ)
    (hg0 : ∀ x ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)), g x = 0)
    (u : ∀ k : OddGridIndex d (triadicHalf J),
      weakSobolevGraph (oddGridCell z R hR (triadicHalf J) k))
    (U : OddGridIndex d (triadicHalf J) → SpatialCoordinates d → ℝ)
    (hcont : ∀ k, ContinuousOn (U k)
      (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))))
    (hrep : ∀ k, ((u k).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))] U k)
    (htrace : ∀ k, ∀ x ∈ frontier
      (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)), U k x = g x) :
    ∃ w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      ContinuousOn w.toH1Function.toFun (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      ∀ k, EqOn w.toH1Function.toFun (U k)
          (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))) ∧
        sobolevDataOfH1 (w.toH1Function.restrict
          (oddGridCell z R hR (triadicHalf J) k).isOpen
          (oddGridCell_subset z hR (triadicHalf J) k)) = (u k).val := by
  classical
  choose v hv hdata using fun k => exists_nativeH1Function_of_ae_representative (u k) (U k) (hrep k)
  have hvc : ∀ k, ContinuousOn (v k).toFun
      (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))) := by
    intro k
    rw [hv k]
    exact hcont k
  have hvt : ∀ k, ∀ x ∈ frontier (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d)),
      (v k).toFun x = g x := by
    intro k x hx
    rw [hv k]
    exact htrace k x hx
  obtain ⟨w, hwc, hwcell, _⟩ := inputs_classical_h1_mesh_gluing z R hR J g hg0 v hvc hvt
  refine ⟨w, hwc, ?_⟩
  intro k
  have heq : EqOn w.toH1Function.toFun (U k)
      (closure (oddGridCell z R hR (triadicHalf J) k : Set (SpatialCoordinates d))) := by
    rw [← hv k]
    exact hwcell k
  refine ⟨heq, ?_⟩
  let wk := w.toH1Function.restrict (oddGridCell z R hR (triadicHalf J) k).isOpen
    (oddGridCell_subset z hR (triadicHalf J) k)
  have hval : (sobolevDataOfH1 wk).1 = (u k).val.1 := by
    apply Lp.ext
    filter_upwards [sobolevDataOfH1_fst_coeFn wk, hrep k,
      self_mem_ae_restrict (oddGridCell z R hR (triadicHalf J) k).isOpen.measurableSet]
      with x hx hy hxQ
    exact hx.trans ((heq (subset_closure hxQ)).trans hy.symm)
  apply Prod.ext hval
  apply weakSobolevGraph_gradient_unique (u := (u k).val.1)
  · rw [← hval]
    exact sobolevDataOfH1_mem_weak wk
  · exact (u k).property

end SubdiffusiveProcess.Paper
