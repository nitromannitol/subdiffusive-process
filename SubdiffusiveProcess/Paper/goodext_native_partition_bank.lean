import SubdiffusiveProcess.Paper.inputs_classical_h1_partition_gluing
import SubdiffusiveProcess.Sobolev.NativeRepresentativeData
import SubdiffusiveProcess.Sobolev.ContinuousNativeRepresentative
import SubdiffusiveProcess.Compactness.FiniteUniformCover
import SubdiffusiveProcess.Sobolev.UniformCubeLimit

/-! Compatible continuous weak Sobolev data on a supplied finite cubical partition
assemble into a killed parent datum with exact restrictions. This file makes no
coefficient or limiting estimate. -/
open Filter MeasureTheory Set TopologicalSpace Homogenization SubdiffusiveProcess
open scoped Topology ENNReal NNReal
noncomputable section
namespace Paper

/-- Compatible continuous weak cell data glue with their exact restricted Sobolev data on a finite cubical partition. -/
theorem goodext_native_partition_bank
    {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (cent : Fin m → SpatialCoordinates d) (rad : Fin m → ℝ) (hrad : ∀ i, 0 < rad i)
    (hsub : ∀ i, (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d)) ⊆
      (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hdisj : Pairwise (fun i j => Disjoint
      (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))
      (centeredCube (cent j) (rad j) (hrad j) : Set (SpatialCoordinates d))))
    (hcover : (⋃ i, closure (centeredCube (cent i) (rad i) (hrad i) : Set (SpatialCoordinates d))) =
      closure (centeredCube z R hR : Set (SpatialCoordinates d)))
    (g : SpatialCoordinates d → ℝ)
    (hg0 : ∀ x ∈ frontier (centeredCube z R hR : Set (SpatialCoordinates d)), g x = 0)
    (u : ∀ k : Fin m,
      weakSobolevGraph (centeredCube (cent k) (rad k) (hrad k)))
    (U : Fin m → SpatialCoordinates d → ℝ)
    (hcont : ∀ k, ContinuousOn (U k)
      (closure (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d))))
    (hrep : ∀ k, ((u k).val.1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d))] U k)
    (htrace : ∀ k, ∀ x ∈ frontier
      (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d)), U k x = g x) :
    ∃ w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      ContinuousOn w.toH1Function.toFun (closure (centeredCube z R hR : Set (SpatialCoordinates d))) ∧
      ∀ k, EqOn w.toH1Function.toFun (U k)
          (closure (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d))) ∧
        sobolevDataOfH1 (w.toH1Function.restrict
          (centeredCube (cent k) (rad k) (hrad k)).isOpen
          (hsub k)) = (u k).val := by
  classical
  choose v hv hdata using fun k => exists_nativeH1Function_of_ae_representative (u k) (U k) (hrep k)
  have hvc : ∀ k, ContinuousOn (v k).toFun
      (closure (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d))) := by
    intro k
    rw [hv k]
    exact hcont k
  have hvt : ∀ k, ∀ x ∈ frontier
      (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d)), (v k).toFun x = g x := by
    intro k x hx
    rw [hv k]
    exact htrace k x hx
  obtain ⟨w, hwc, hwcell, _⟩ :=
    inputs_classical_h1_partition_gluing z R hR m cent rad hrad hsub hdisj hcover g hg0 v hvc hvt
  refine ⟨w, hwc, ?_⟩
  intro k
  have heq : EqOn w.toH1Function.toFun (U k)
      (closure (centeredCube (cent k) (rad k) (hrad k) : Set (SpatialCoordinates d))) := by
    rw [← hv k]
    exact hwcell k
  refine ⟨heq, ?_⟩
  let wk := w.toH1Function.restrict (centeredCube (cent k) (rad k) (hrad k)).isOpen (hsub k)
  have hval : (sobolevDataOfH1 wk).1 = (u k).val.1 := by
    apply Lp.ext
    filter_upwards [sobolevDataOfH1_fst_coeFn wk, hrep k,
      self_mem_ae_restrict (centeredCube (cent k) (rad k) (hrad k)).isOpen.measurableSet]
      with x hx hy hxQ
    exact hx.trans ((heq (subset_closure hxQ)).trans hy.symm)
  apply Prod.ext hval
  apply weakSobolevGraph_gradient_unique (u := (u k).val.1)
  · rw [← hval]
    exact sobolevDataOfH1_mem_weak wk
  · exact (u k).property

end Paper
