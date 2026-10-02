import SubdiffusiveProcess.FractionalSup.Upper
import SubdiffusiveProcess.Sobolev.HarmonicMaxPrincipleClosure

/-!
# The two-sided Stampacchia bound on the closed cube
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.FractionalSup

variable {d : ℕ}

open SubdiffusiveProcess SubdiffusiveProcess.Lane4

/-- The Dirichlet problem is odd in `(F, b, u)`. -/
theorem solvesDirichlet_neg {Ω : Opens (SpatialCoordinates d)} {a : PositiveCoefficient Ω}
    {F : SpatialCoordinates d → ℝ} {b u : weakSobolevGraph Ω} (h : SolvesDirichlet a F b u) :
    SolvesDirichlet a (fun x => -F x) (-b) (-u) := by
  refine ⟨?_, fun ψ => ?_⟩
  · have := (killedSobolevGraph Ω).neg_mem h.1
    change (-(u : SobolevData Ω)) - (-(b : SobolevData Ω)) ∈ killedSobolevGraph Ω
    convert this using 1
    abel
  · have := h.2 ψ
    have e1 : sobolevCoefficientForm a ((-u : weakSobolevGraph Ω) : SobolevData Ω) (ψ : SobolevData Ω)
        = -sobolevCoefficientForm a (u : SobolevData Ω) (ψ : SobolevData Ω) := by
      change sobolevCoefficientForm a (-(u : SobolevData Ω)) (ψ : SobolevData Ω) = _
      rw [map_neg, ContinuousLinearMap.neg_apply]
    rw [e1, this, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring

/-- **Two-sided Stampacchia bound.** -/
theorem fractionalSup_bound [NeZero d] (hd : 2 ≤ d) (s : Set.Ioo (0 : ℝ) 1)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) {CS : ℝ} (hCS : 0 < CS)
    (hemb : ∀ v : DomainL2 (centeredCube z r hr),
      cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => v) < ⊤ →
      MemLp (v : SpatialCoordinates d → ℝ) (ENNReal.ofReal (critExp d s))
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            |v x| ^ (critExp d s)) ^ (((d : ℝ) - 2 * (s : ℝ)) / (d : ℝ)) ≤
          CS * cubeFractionalSqNorm hd z r hr s v)
    (hfin : ∀ Ψ : SobolevData (centeredCube z r hr), Ψ ∈ killedSobolevGraph (centeredCube z r hr) →
      cubeFractionalL2Seminorm hd z r hr s (fun _ : Fin 1 => Ψ.1) < ⊤)
    (a : PositiveCoefficient (centeredCube z r hr)) {K : ℝ} (hK : 0 < K)
    (hcoer : ∀ v : killedSobolevGraph (centeredCube z r hr),
      cubeFractionalSqNorm hd z r hr s (v : SobolevData (centeredCube z r hr)).1 ≤
        K * sobolevCoefficientForm a (v : SobolevData (centeredCube z r hr))
          (v : SobolevData (centeredCube z r hr)))
    (F : SpatialCoordinates d → ℝ) {Kf : ℝ} (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (phi : SpatialCoordinates d → ℝ) {Bphi : ℝ}
    (hphi : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)), |phi x| ≤ Bphi)
    (b u : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (hsol : SolvesDirichlet a F b u) (U : SpatialCoordinates d → ℝ) (hU : Continuous U)
    (hu : ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ) =ᵐ[
      volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U)
    (x : SpatialCoordinates d) (hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d))) :
    |U x| ≤ Bphi + (CS * (r ^ d) ^ ((critExp d s - 2) / critExp d s) *
      (2 : ℝ) ^ ((critExp d s - 1) / (critExp d s - 2))) * K * Kf := by
  classical
  have hQmeas : MeasurableSet (centeredCube z r hr : Set (SpatialCoordinates d)) :=
    (centeredCube z r hr).isOpen.measurableSet
  have hbM : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      |(b : SobolevData (centeredCube z r hr)).1 y| ≤ Bphi := by
    filter_upwards [hb, ae_restrict_mem hQmeas] with y h1 h2
    rw [h1]
    exact hphi y (centeredCube_subset_closedCube z hr h2)
  set δ0 : ℝ := (CS * K * Kf) * (r ^ d) ^ ((critExp d s - 2) / critExp d s) *
    (2 : ℝ) ^ ((critExp d s - 1) / (critExp d s - 2)) with hδ0
  have hclosure : ∀ δ : ℝ, 0 < δ → δ0 ≤ δ → |U x| ≤ Bphi + δ := by
    intro δ hδ hδδ
    have hup := fractionalSup_upper hd s z r hr hCS hemb hfin a hK hcoer F hKf hFm hFb b u
      (M := Bphi) (hbM.mono fun y hy => (le_abs_self _).trans hy) hsol hδ hδδ
    have hsol' := solvesDirichlet_neg hsol
    have hFb' : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        |(fun x => -F x) y| ≤ Kf := hFb.mono fun y hy => by simpa using hy
    have hFm' : AEMeasurable (fun x => -F x)
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) := hFm.neg
    have hbM' : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        ((-b : weakSobolevGraph (centeredCube z r hr)) : SobolevData (centeredCube z r hr)).1 y ≤ Bphi := by
      filter_upwards [hbM, Lp.coeFn_neg (b : SobolevData (centeredCube z r hr)).1] with y h1 h2
      have : ((-b : weakSobolevGraph (centeredCube z r hr)) : SobolevData (centeredCube z r hr)).1 y =
          -(b : SobolevData (centeredCube z r hr)).1 y := by
        change (-(b : SobolevData (centeredCube z r hr)) : SobolevData (centeredCube z r hr)).1 y = _
        exact h2
      rw [this]
      linarith [(abs_le.1 h1).1]
    have hlow := fractionalSup_upper hd s z r hr hCS hemb hfin a hK hcoer (fun x => -F x) hKf hFm' hFb'
      (-b) (-u) (M := Bphi) hbM' hsol' hδ hδδ
    have hae : ∀ᵐ y ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        |U y| ≤ Bphi + δ := by
      filter_upwards [hup, hlow, hu, Lp.coeFn_neg (u : SobolevData (centeredCube z r hr)).1]
        with y h1 h2 h3 h4
      have h5 : ((-u : weakSobolevGraph (centeredCube z r hr)) : SobolevData (centeredCube z r hr)).1 y =
          -(u : SobolevData (centeredCube z r hr)).1 y := by
        change (-(u : SobolevData (centeredCube z r hr)) : SobolevData (centeredCube z r hr)).1 y = _
        exact h4
      rw [h5] at h2
      rw [abs_le]
      constructor <;> linarith
    have hin := abs_le_of_ae_abs_le_of_continuousOn_open (centeredCube z r hr).isOpen U
      hU.continuousOn (Bphi + δ) hae
    -- pass to the closed cube
    have hclos : (closedCube z r hr : Set (SpatialCoordinates d)) ⊆
        closure (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      change Metric.closedBall z (r / 2) ⊆ closure (centeredCube z r hr : Set (SpatialCoordinates d))
      rw [centeredCube_coe_eq_ball, closure_ball z (by positivity)]
    have hsub : closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
        {y | |U y| ≤ Bphi + δ} :=
      closure_minimal (fun y hy => hin y hy)
        (isClosed_le (continuous_abs.comp hU) continuous_const)
    exact hsub (hclos hx)
  by_cases h0 : 0 < δ0
  · have := hclosure δ0 h0 le_rfl
    rw [hδ0] at this
    calc |U x| ≤ Bphi + (CS * K * Kf) * (r ^ d) ^ ((critExp d s - 2) / critExp d s) *
        (2 : ℝ) ^ ((critExp d s - 1) / (critExp d s - 2)) := this
      _ = _ := by ring
  · have hz : δ0 ≤ 0 := not_lt.1 h0
    have hδnn : 0 ≤ δ0 := by
      rw [hδ0]
      have := critExp_gt_two hd s.2.1 s.2.2
      positivity
    have hzero : δ0 = 0 := le_antisymm hz hδnn
    have : |U x| ≤ Bphi := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have := hclosure ε hε (by rw [hzero]; exact hε.le)
      linarith
    calc |U x| ≤ Bphi := this
      _ = Bphi + δ0 := by rw [hzero]; ring
      _ = _ := by rw [hδ0]; ring

end SubdiffusiveProcess.FractionalSup
