module

public import SubdiffusiveProcess.Sobolev.NativeH10
public import SubdiffusiveProcess.Sobolev.EvenReflectionGraph
public import SubdiffusiveProcess.Lane4.Bridge

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open Homogenization
open scoped ENNReal NNReal Topology Distributions ContDiff

noncomputable section

namespace SubdiffusiveProcess

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}



def sobolevDataOfH1 (u : H1Function (Ω : Set (SpatialCoordinates d))) :
    SobolevData Ω :=
  (MemLp.toLp u.toFun u.memL2,
    fun i => MemLp.toLp (fun x => u.grad x i) (u.gradMemL2 i))

theorem sobolevDataOfH1_fst_coeFn (u : H1Function (Ω : Set (SpatialCoordinates d))) :
    ((sobolevDataOfH1 u).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] u.toFun :=
  MemLp.coeFn_toLp u.memL2

theorem sobolevDataOfH1_snd_coeFn (u : H1Function (Ω : Set (SpatialCoordinates d)))
    (i : Fin d) :
    (((sobolevDataOfH1 u).2 i : DomainL2 Ω) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))] fun x => u.grad x i :=
  MemLp.coeFn_toLp (u.gradMemL2 i)

theorem sobolevDataOfH1_mem_weak (u : H1Function (Ω : Set (SpatialCoordinates d))) :
    sobolevDataOfH1 u ∈ weakSobolevGraph Ω := by
  rw [mem_weakSobolevGraph_iff]
  intro φ i
  have h1 : (∫ x in (Ω : Set (SpatialCoordinates d)),
      φ x * ((sobolevDataOfH1 u).2 i) x) =
      ∫ x in (Ω : Set (SpatialCoordinates d)), φ x * u.grad x i := by
    refine integral_congr_ae ?_
    filter_upwards [sobolevDataOfH1_snd_coeFn u i] with x hx
    rw [hx]
  have h2 : (∫ x in (Ω : Set (SpatialCoordinates d)),
      fderiv ℝ φ x (Pi.single i 1) * ((sobolevDataOfH1 u).1) x) =
      ∫ x in (Ω : Set (SpatialCoordinates d)),
        fderiv ℝ φ x (Pi.single i 1) * u.toFun x := by
    refine integral_congr_ae ?_
    filter_upwards [sobolevDataOfH1_fst_coeFn u] with x hx
    rw [hx]
  rw [h1, h2]
  have hw := u.hasWeakGradient i (φ : SpatialCoordinates d → ℝ) φ.contDiff
    φ.hasCompactSupport φ.tsupport_subset
  have hwl : (∫ x in (Ω : Set (SpatialCoordinates d)),
      fderiv ℝ φ x (Pi.single i 1) * u.toFun x) =
      ∫ x in (Ω : Set (SpatialCoordinates d)),
        u.toFun x * (fderiv ℝ (φ : SpatialCoordinates d → ℝ) x) (basisVec i) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [basisVec]
    ring
  have hwr : (∫ x in (Ω : Set (SpatialCoordinates d)), φ x * u.grad x i) =
      ∫ x in (Ω : Set (SpatialCoordinates d)), u.grad x i * φ x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hwl, hwr, hw]
  ring

/-- **Adapter B, killed tests.**  The data of an upstream `H¹₀` function lie in
the killed space, so the project's weak equation may be tested against exactly
the class `IsDivFormWeakSolutionOn` quantifies over. -/
theorem sobolevDataOfH1_mem_killed
    (u : H10Function (Ω : Set (SpatialCoordinates d))) :
    sobolevDataOfH1 u.toH1Function ∈ killedSobolevGraph Ω := by
  obtain ⟨w, hval, hgrad⟩ := Lane4.exists_killedSobolevGraph_of_nativeH10 u
  have hEq : sobolevDataOfH1 u.toH1Function = (w : SobolevData Ω) := by
    refine Prod.ext ?_ ?_
    · exact Lp.ext ((MemLp.coeFn_toLp u.toH1Function.memL2).trans hval.symm)
    · funext i
      exact Lp.ext
        ((MemLp.coeFn_toLp (u.toH1Function.gradMemL2 i)).trans (hgrad i).symm)
  rw [hEq]
  exact w.property

end SubdiffusiveProcess
