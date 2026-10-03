module

public import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy
public import SubdiffusiveProcess.Sobolev.AffineData
public import SubdiffusiveProcess.Lane4.Bridge
public import Homogenization.Sobolev.H1.BasicLemmas

@[expose] public section

/-! Continuous-boundary variational infima agree with Sobolev Dirichlet responses
when zero continuous trace characterizes the killed space. No stochastic limits are asserted. -/

open MeasureTheory Filter Set TopologicalSpace Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff Distributions

noncomputable section
namespace SubdiffusiveProcess
variable {d : ℕ}

/-- The energies of continuous Sobolev competitors with prescribed boundary values. -/
def continuousBoundaryEnergies {d : ℕ} (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) : Set ℝ :=
  {e : ℝ | ∃ (u : weakSobolevGraph (centeredCube z r hr))
      (U : SpatialCoordinates d → ℝ),
    ContinuousOn U (closedCube z r hr : Set (SpatialCoordinates d)) ∧
    ((u.val).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
    (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = g x) ∧
    e = sobolevCoefficientForm a u.val u.val}

/-- Every continuous-boundary competitor has nonnegative energy. -/
theorem continuousBoundaryEnergies_nonneg (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) :
    ∀ e ∈ continuousBoundaryEnergies z r hr a g, 0 ≤ e := by
  rintro e ⟨u, U, -, -, -, rfl⟩
  exact sobolevCoefficientForm_nonneg a u.val

/-- The continuous-boundary infimum is nonnegative. -/
theorem continuousBoundaryInfimum_nonneg (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) :
    0 ≤ sInf (continuousBoundaryEnergies z r hr a g) :=
  Real.sInf_nonneg (continuousBoundaryEnergies_nonneg z r hr a g)

/-- Continuous-boundary competitor energies are bounded below by zero. -/
theorem continuousBoundaryEnergies_bddBelow (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) :
    BddBelow (continuousBoundaryEnergies z r hr a g) :=
  ⟨0, continuousBoundaryEnergies_nonneg z r hr a g⟩

/-- Adding a compactly supported smooth test preserves the prescribed boundary values. -/
theorem continuousBoundaryEnergies_smooth_competitor
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (g G : SpatialCoordinates d → ℝ)
    (hGc : ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G)
    (hGg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), G x = g x)
    (ψ : 𝓓(centeredCube z r hr, ℝ)) :
    sobolevCoefficientForm a (b.val + smoothSobolevData ψ) (b.val + smoothSobolevData ψ) ∈
      continuousBoundaryEnergies z r hr a g := by
  let u : weakSobolevGraph (centeredCube z r hr) :=
    ⟨b.val + smoothSobolevData ψ,
      (weakSobolevGraph (centeredCube z r hr)).add_mem b.property (smoothSobolevData_mem ψ)⟩
  refine ⟨u, fun x => G x + ψ x, ?_, ?_, ?_, rfl⟩
  · exact hGc.add ψ.contDiff.continuous.continuousOn
  · filter_upwards [Lp.coeFn_add b.val.1 (testL2 ψ), hb, testL2_coeFn ψ] with x hadd hbx hψx
    change ((b.val.1 + testL2 ψ : DomainL2 (centeredCube z r hr)) :
      SpatialCoordinates d → ℝ) x = G x + ψ x
    rw [hadd, Pi.add_apply, hbx, hψx]
  · intro x hx
    have hxnot : x ∉ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      have hopen : IsOpen (centeredCube z r hr : Set (SpatialCoordinates d)) :=
        (centeredCube z r hr).isOpen
      rw [hopen.frontier_eq] at hx
      exact hx.2
    have hψ0 : ψ x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hxnot (ψ.tsupport_subset h))
    simp only [hψ0, add_zero, hGg x hx]

/-- Smooth approximation of the killed minimizer bounds the boundary infimum by its response. -/
theorem continuousBoundaryInfimum_le_response
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0,
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (g G : SpatialCoordinates d → ℝ)
    (hGc : ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G)
    (hGg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), G x = g x) :
    sInf (continuousBoundaryEnergies z r hr a g) ≤
      dirichletResponse (killedResponseSpace hP) a b := by
  have hmem : (dirichletMinimizer (killedResponseSpace hP) a b).val - b.val ∈
      killedSobolevGraph (centeredCube z r hr) :=
    dirichletMinimizer_mem_affine (killedResponseSpace hP) a b
  have hcl : (dirichletMinimizer (killedResponseSpace hP) a b).val - b.val ∈ closure
      ((LinearMap.range (smoothSobolevDataLinear (Ω := centeredCube z r hr)) :
        Submodule ℝ (SobolevData (centeredCube z r hr))) :
          Set (SobolevData (centeredCube z r hr))) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hmem
  obtain ⟨x, hxmem, hxlim⟩ := mem_closure_iff_seq_limit.mp hcl
  choose ψ hψ using hxmem
  have hψ' : ∀ n, smoothSobolevData (ψ n) = x n := hψ
  have hconv : Tendsto (fun n => b.val + smoothSobolevData (ψ n)) atTop
      (𝓝 (dirichletMinimizer (killedResponseSpace hP) a b).val) := by
    have h1 : Tendsto (fun n => b.val + x n) atTop
        (𝓝 (b.val + ((dirichletMinimizer (killedResponseSpace hP) a b).val - b.val))) :=
      tendsto_const_nhds.add hxlim
    rw [add_sub_cancel] at h1
    simpa only [hψ'] using h1
  have hform : Continuous (fun u : SobolevData (centeredCube z r hr) =>
      sobolevCoefficientForm a u u) :=
    (sobolevCoefficientForm a).continuous₂.comp (continuous_id.prodMk continuous_id)
  have hlim : Tendsto (fun n => sobolevCoefficientForm a (b.val + smoothSobolevData (ψ n))
      (b.val + smoothSobolevData (ψ n))) atTop
      (𝓝 (dirichletResponse (killedResponseSpace hP) a b)) := (hform.tendsto _).comp hconv
  refine ge_of_tendsto' hlim (fun n => ?_)
  exact csInf_le (continuousBoundaryEnergies_bddBelow z r hr a g)
    (continuousBoundaryEnergies_smooth_competitor z r hr a b g G hGc hb hGg (ψ n))

/-- The zero-trace characterization makes every continuous competitor admissible for the response. -/
theorem response_le_continuousBoundaryInfimum
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hTrace : ∀ (u : weakSobolevGraph (centeredCube z r hr))
      (U : SpatialCoordinates d → ℝ), ContinuousOn U (closedCube z r hr) →
      ((u.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U) →
      (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0) →
      u.val ∈ killedSobolevGraph (centeredCube z r hr))
    (hP : ∃ K : ℝ≥0,
      ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient
            (killedSobolevGraph (centeredCube z r hr)) w‖)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : weakSobolevGraph (centeredCube z r hr))
    (g G : SpatialCoordinates d → ℝ)
    (hGc : ContinuousOn G (closedCube z r hr : Set (SpatialCoordinates d)))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] G)
    (hGg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), G x = g x) :
    dirichletResponse (killedResponseSpace hP) a b ≤
      sInf (continuousBoundaryEnergies z r hr a g) := by
  have hne : (continuousBoundaryEnergies z r hr a g).Nonempty := by
    exact ⟨sobolevCoefficientForm a b.val b.val, ⟨b, G, hGc, hb, hGg, rfl⟩⟩
  apply le_csInf hne
  rintro e ⟨u, U, hUc, huU, hUb, rfl⟩
  let v : weakSobolevGraph (centeredCube z r hr) :=
    ⟨u.val - b.val, (weakSobolevGraph (centeredCube z r hr)).sub_mem u.property b.property⟩
  have hvrep : ((v : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] (U - G) := by
    filter_upwards [Lp.coeFn_sub u.val.1 b.val.1, huU, hb] with x hsub hxu hbx
    change ((u.val.1 - b.val.1 : DomainL2 (centeredCube z r hr)) :
      SpatialCoordinates d → ℝ) x = U x - G x
    rw [hsub, Pi.sub_apply, hxu, hbx]
  have hvzero : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      (U - G) x = 0 := by
    intro x hx
    simp only [Pi.sub_apply, hUb x hx, hGg x hx, sub_self]
  have hvk : (v : SobolevData (centeredCube z r hr)) ∈
      killedSobolevGraph (centeredCube z r hr) :=
    hTrace v (U - G) (hUc.sub hGc) hvrep hvzero
  let w : (killedResponseSpace hP).space := ⟨v.val, hvk⟩
  have hsum : b.val + w.val = u.val := by
    change b.val + (u.val - b.val) = u.val
    abel
  have hleast := dirichletResponse_isLeast (killedResponseSpace hP) a b
  have hle := hleast.2 ⟨w, rfl⟩
  change dirichletResponse (killedResponseSpace hP) a b ≤
    sobolevCoefficientForm a (b.val + w.val) (b.val + w.val) at hle
  rw [hsum] at hle
  exact hle

/-- An affine constant has zero energy pairing against every Sobolev datum. -/
theorem sobolevCoefficientForm_affine_constant_right (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (a : PositiveCoefficient (centeredCube z r hr))
    (v : SobolevData (centeredCube z r hr)) (c : ℝ) :
    sobolevCoefficientForm a v (affineSobolevData (centeredCube_isBounded z hr) 0 c) = 0 := by
  rw [sobolevCoefficientForm_apply]
  apply Finset.sum_eq_zero
  intro i _
  have h : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      a.val x * (v.2 i x * (affineSobolevData (centeredCube_isBounded z hr) 0 c).2 i x) = 0 := by
    filter_upwards [domainConstantL2_coeFn (Ω := centeredCube z r hr) ((0 : Fin d → ℝ) i)]
      with x hx
    change a.val x * (v.2 i x * (domainConstantL2 (Ω := centeredCube z r hr)
      ((0 : Fin d → ℝ) i)) x) = 0
    rw [hx, Pi.zero_apply, mul_zero, mul_zero]
  rw [integral_congr_ae h, integral_zero]

/-- A smooth function on a cube has a weak Sobolev representative. -/
theorem smooth_cube_weakSobolev_representative
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (g : SpatialCoordinates d → ℝ) (hg : ContDiff ℝ ∞ g) :
    ∃ b : weakSobolevGraph (centeredCube z r hr),
      ((b.val.1 : SpatialCoordinates d → ℝ) =ᵐ[
        volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] g) := by
  have hdom : Homogenization.IsOpenBoundedConvexDomain
      (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    ⟨(centeredCube z r hr).isOpen, (centeredCube_isBounded z hr).isBoundedDomain,
      convex_ball z (r / 2)⟩
  let v := Homogenization.H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    hdom (hg.of_le (by norm_num))
  obtain ⟨b, hb, _⟩ := exists_weakSobolevGraph_of_nativeH1 v
  exact ⟨b, hb⟩

/-- A constant prescribed trace has zero continuous-boundary infimum. -/
theorem continuousBoundaryInfimum_eq_zero_of_constant_trace
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (g : SpatialCoordinates d → ℝ) (c : ℝ)
    (hg : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), g x = c) :
    sInf (continuousBoundaryEnergies z r hr a g) = 0 := by
  have hz : 0 ∈ continuousBoundaryEnergies z r hr a g := by
    refine ⟨affineSobolev (centeredCube_isBounded z hr) 0 c, fun _ => c,
      continuousOn_const, ?_, fun x hx => (hg x hx).symm, ?_⟩
    · filter_upwards [affineL2_coeFn (centeredCube_isBounded z hr) (0 : Fin d → ℝ) c]
        with x hx
      change (affineL2 (centeredCube_isBounded z hr) (0 : Fin d → ℝ) c) x = c
      simpa only [affineSlope_apply, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
        zero_add] using hx
    · exact (sobolevCoefficientForm_affine_constant_right z r hr a
        (affineSobolevData (centeredCube_isBounded z hr) 0 c) c).symm
  exact le_antisymm
    (csInf_le (continuousBoundaryEnergies_bddBelow z r hr a g) hz)
    (continuousBoundaryInfimum_nonneg z r hr a g)

end SubdiffusiveProcess
