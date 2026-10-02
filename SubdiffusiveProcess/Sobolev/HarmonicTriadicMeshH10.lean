import SubdiffusiveProcess.Sobolev.HarmonicCellMinimum
import SubdiffusiveProcess.Sobolev.OddGridEnergy
import SubdiffusiveProcess.Geometry.TriadicResidual
import SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.HarmonicExtensionSelection
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.MeshGluing
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteDirichletConvergence
import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.SmallContrastScalarBridge

open MeasureTheory Set TopologicalSpace
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ContDiff

noncomputable section

namespace SubdiffusiveProcess

/-- Internal partial mesh construction for `eq:mfd-18`: all Sobolev, harmonic,
trace, minimality, and exact energy-assembly clauses, excluding only boundary
continuity and the pointwise maximum-principle error estimate. -/
theorem exists_harmonicTriadicMeshH10_energy
    {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R) (J : ℕ)
    (a : SpatialCoordinates d → ℝ) (lam Lam : ℝ)
    (hlam : 0 < lam)
    (ha : Continuous a)
    (haBounds : ∀ x ∈ (centeredCube z R hR : Set (SpatialCoordinates d)),
      lam ≤ a x ∧ a x ≤ Lam)
    (φ : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)))
    (hφsmooth : ContDiff ℝ ∞ φ.toFun)
    (hφcompact : HasCompactSupport φ.toFun)
    (hφsupport : tsupport φ.toFun ⊆
      (centeredCube z R hR : Set (SpatialCoordinates d))) :
    ∃ w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)),
      (∀ k : OddGridIndex d (triadicHalf J),
        let W := oddGridCell z R hR (triadicHalf J) k
        let hW : (W : Set (SpatialCoordinates d)) ⊆
            (centeredCube z R hR : Set (SpatialCoordinates d)) :=
          oddGridCell_subset z hR (triadicHalf J) k
        let wk : H1Function (W : Set (SpatialCoordinates d)) :=
          w.toH1Function.restrict W.isOpen hW
        let φk : H1Function (W : Set (SpatialCoordinates d)) :=
          φ.restrict W.isOpen hW
        IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) wk ∧
        HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) wk φk ∧
        energy a (W : Set (SpatialCoordinates d)) wk =
          sInf {e : ℝ | ∃ u : H1Function (W : Set (SpatialCoordinates d)),
            HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u φk ∧
            e = energy a (W : Set (SpatialCoordinates d)) u}) ∧
      energy a (centeredCube z R hR : Set (SpatialCoordinates d))
          w.toH1Function =
        (∑ k : OddGridIndex d (triadicHalf J),
          let W := oddGridCell z R hR (triadicHalf J) k
          let hW : (W : Set (SpatialCoordinates d)) ⊆
              (centeredCube z R hR : Set (SpatialCoordinates d)) :=
            oddGridCell_subset z hR (triadicHalf J) k
          let φk : H1Function (W : Set (SpatialCoordinates d)) :=
            φ.restrict W.isOpen hW
          sInf {e : ℝ | ∃ u : H1Function (W : Set (SpatialCoordinates d)),
            HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) u φk ∧
            e = energy a (W : Set (SpatialCoordinates d)) u}) := by
  have hUopen : IsOpen (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    (centeredCube z R hR).isOpen
  have hUdom : IsOpenBoundedConvexDomain
      (centeredCube z R hR : Set (SpatialCoordinates d)) := by
    refine ⟨hUopen, (centeredCube_isBounded z hR).isBoundedDomain, ?_⟩
    change Convex ℝ (Metric.ball z (R / 2))
    exact convex_ball z (R / 2)
  have hUell : IsEllipticFieldOn lam Lam
      (centeredCube z R hR : Set (SpatialCoordinates d))
      (scalarCoeffField a) := by
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundedMultiplier.isEllipticFieldOn_scalarCoeffField_of_continuousOn
      hUopen.measurableSet ha.continuousOn hlam haBounds
  let m : ℕ := triadicHalf J
  have hcellDom (k : OddGridIndex d m) :
      IsOpenBoundedConvexDomain (oddGridCell z R hR m k : Set (SpatialCoordinates d)) := by
    have hopen := (oddGridCell z R hR m k).isOpen
    refine ⟨hopen, (centeredCube_isBounded _ (div_pos hR (by positivity))).isBoundedDomain, ?_⟩
    change Convex ℝ (Metric.ball (oddGridCenter z R m k)
      ((R / (2 * (m : ℝ) + 1)) / 2))
    exact convex_ball _ _
  have hcellne (k : OddGridIndex d m) :
      (oddGridCell z R hR m k : Set (SpatialCoordinates d)).Nonempty := by
    exact ⟨oddGridCenter z R m k,
      Metric.mem_ball_self (half_pos (div_pos hR (by positivity)))⟩
  have hcellEll (k : OddGridIndex d m) :
      IsEllipticFieldOn lam Lam (oddGridCell z R hR m k : Set (SpatialCoordinates d))
        (scalarCoeffField a) :=
    hUell.mono (oddGridCell z R hR m k).isOpen.measurableSet
      (oddGridCell_subset z hR m k)
  let datum : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)) := φ
  let localDatum (k : OddGridIndex d m) :
      H1Function (oddGridCell z R hR m k : Set (SpatialCoordinates d)) :=
    datum.restrict (oddGridCell z R hR m k).isOpen (oddGridCell_subset z hR m k)
  let localSol (k : OddGridIndex d m) :
      H1Function (oddGridCell z R hR m k : Set (SpatialCoordinates d)) :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.weakHarmonicDirichletExtension
      (hcellDom k) (hcellne k) (hcellEll k) (localDatum k)
  have localSolHarm (k : OddGridIndex d m) :
      IsWeaklyHarmonicOn a (oddGridCell z R hR m k : Set (SpatialCoordinates d))
        (localSol k) := by
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.isWeaklyHarmonicOn_weakHarmonicDirichletExtension
      (hcellDom k) (hcellne k) (hcellEll k) (localDatum k)
  have localSolTrace (k : OddGridIndex d m) :
      HasZeroTraceDifferenceOn (oddGridCell z R hR m k : Set (SpatialCoordinates d))
        (localSol k) (localDatum k) := by
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.hasZeroTraceDifferenceOn_weakHarmonicDirichletExtension
      (hcellDom k) (hcellne k) (hcellEll k) (localDatum k)
  have localSelfTrace (k : OddGridIndex d m) :
      HasZeroTraceDifferenceOn (oddGridCell z R hR m k : Set (SpatialCoordinates d))
        (localDatum k) (localDatum k) := by
    refine ⟨0, ?_, ?_⟩
    · intro x
      change (localDatum k).toFun x = (localDatum k).toFun x + 0
      simp
    · intro x
      change (localDatum k).grad x = (localDatum k).grad x + 0
      simp
  choose rho hrhoVal hrhoGrad using fun k ↦
    SubdiffusiveProcess.CoarseGrainingVocab.Section6Dirichlet.exists_h10Function_solutionDifference_sub_boundaryDifference
      (localSolTrace k) (localSelfTrace k)
  have hrhoVal' (k : OddGridIndex d m) (x : SpatialCoordinates d) :
      (rho k).toH1Function.toFun x = (localSol k).toFun x - (localDatum k).toFun x := by
    simpa [sub_self, sub_zero] using hrhoVal k x
  have hrhoGrad' (k : OddGridIndex d m) (x : SpatialCoordinates d) :
      (rho k).toH1Function.grad x = (localSol k).grad x - (localDatum k).grad x := by
    simpa [sub_self, sub_zero] using hrhoGrad k x
  have glue : ∀ S : Finset (OddGridIndex d m), ∃ G : H10Function
      (centeredCube z R hR : Set (SpatialCoordinates d)),
      (∀ x, G.toH1Function.toFun x =
        ∑ k ∈ S, Set.indicator (oddGridCell z R hR m k : Set (SpatialCoordinates d))
          (fun y => (rho k).toH1Function.toFun y) x) ∧
      (∀ x, G.toH1Function.grad x =
        ∑ k ∈ S, Set.indicator (oddGridCell z R hR m k : Set (SpatialCoordinates d))
          (fun y => (rho k).toH1Function.grad y) x) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
    refine ⟨0, ?_, ?_⟩
    · intro x
      change (0 : SpatialCoordinates d → ℝ) x = 0
      rfl
    · intro x
      change (0 : SpatialCoordinates d → SpatialCoordinates d) x = 0
      rfl
    | @insert k S hk ih =>
        obtain ⟨G, hGval, hGgrad⟩ := ih
        let E : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)) :=
          (rho k).extendByZeroToOpenSuperset
            (oddGridCell z R hR m k).isOpen.measurableSet hUopen
            (oddGridCell_subset z hR m k)
        refine ⟨G + E, ?_, ?_⟩
        · intro x
          change G.toH1Function.toFun x + E.toH1Function.toFun x = _
          rw [hGval, H10Function.extendByZeroToOpenSuperset_toFun]
          simp [E, H10Function.zeroExtension, Finset.sum_insert, hk,
            H1Function.add_toFun]
          rw [add_comm]
        · intro x
          change G.toH1Function.grad x + E.toH1Function.grad x = _
          rw [hGgrad, H10Function.extendByZeroToOpenSuperset_grad]
          simp [E, H10Function.zeroExtensionGrad, Finset.sum_insert, hk,
            H1Function.add_grad]
          rw [add_comm]
  obtain ⟨G, hGval, hGgrad⟩ := glue Finset.univ
  have hLibraryGlue :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.exists_h10Function_grad_eq_sum_indicator
      hUopen (Finset.univ : Finset (OddGridIndex d m))
      (V := fun k => (oddGridCell z R hR m k : Set (SpatialCoordinates d)))
      (fun k => (oddGridCell z R hR m k).isOpen.measurableSet)
      (fun k => oddGridCell_subset z hR m k) rho
  let smoothDatum : H1Function (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    H1Function.ofContDiff hUopen (hφsmooth.of_le (by simp)) hφcompact
  have hDatumGradAe : smoothDatum.grad =ᵐ[volume.restrict
      (centeredCube z R hR : Set (SpatialCoordinates d))] φ.grad := by
    exact SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.H1Function.grad_ae_eq_of_toFun_eq
      hUopen (u := smoothDatum) (v := φ) (by rfl)
  let base : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    { toH1Function := φ
      approx := fun _ => φ.toFun
      approx_smooth := fun _ => hφsmooth.of_le (by simp)
      approx_hasCompactSupport := fun _ => hφcompact
      approx_support_subset := fun _ => hφsupport
      tendsto_approx := by simp
      tendsto_approx_grad := by
        intro i
        have hi :
            (fun x => (fderiv ℝ φ.toFun x) (basisVec i) - φ.grad x i) =ᵐ[
              volume.restrict (centeredCube z R hR : Set (SpatialCoordinates d))] 0 := by
          filter_upwards [hDatumGradAe] with x hx
          change (fderiv ℝ φ.toFun x) (basisVec i) - φ.grad x i = 0
          have hx' := congr_fun hx i
          change (fderiv ℝ φ.toFun x) (basisVec i) = φ.grad x i at hx'
          linarith
        rw [eLpNorm_congr_ae hi]
        simp }
  let w : H10Function (centeredCube z R hR : Set (SpatialCoordinates d)) := base + G
  have hsum_toFun (k : OddGridIndex d m) (x : SpatialCoordinates d)
      (hx : x ∈ (oddGridCell z R hR m k : Set (SpatialCoordinates d))) :
      (∑ l : OddGridIndex d m, Set.indicator
          (oddGridCell z R hR m l : Set (SpatialCoordinates d))
          (fun y => (rho l).toH1Function.toFun y) x) =
        (rho k).toH1Function.toFun x := by
    rw [Finset.sum_eq_single k]
    · exact Set.indicator_of_mem hx _
    · intro l hl hlk
      apply Set.indicator_of_notMem
      intro hxl
      exact Set.disjoint_left.mp
        (oddGridCell_pairwiseDisjoint z hR m hlk) hxl hx
    · simp
  have hsum_grad (k : OddGridIndex d m) (x : SpatialCoordinates d)
      (hx : x ∈ (oddGridCell z R hR m k : Set (SpatialCoordinates d))) :
      (∑ l : OddGridIndex d m, Set.indicator
          (oddGridCell z R hR m l : Set (SpatialCoordinates d))
          (fun y => (rho l).toH1Function.grad y) x) =
        (rho k).toH1Function.grad x := by
    rw [Finset.sum_eq_single k]
    · exact Set.indicator_of_mem hx _
    · intro l hl hlk
      apply Set.indicator_of_notMem
      intro hxl
      exact Set.disjoint_left.mp
        (oddGridCell_pairwiseDisjoint z hR m hlk) hxl hx
    · simp
  have hw_val_on (k : OddGridIndex d m) (x : SpatialCoordinates d)
      (hx : x ∈ (oddGridCell z R hR m k : Set (SpatialCoordinates d))) :
      (w.toH1Function.restrict (oddGridCell z R hR m k).isOpen
        (oddGridCell_subset z hR m k)).toFun x = (localSol k).toFun x := by
    change base.toH1Function.toFun x + G.toH1Function.toFun x = _
    rw [hGval x, hsum_toFun k x hx]
    rw [hrhoVal' k x]
    dsimp [base, localDatum, datum]
    change φ.toFun x + ((localSol k).toFun x - φ.toFun x) = (localSol k).toFun x
    ring
  have hw_grad_on (k : OddGridIndex d m) (x : SpatialCoordinates d)
      (hx : x ∈ (oddGridCell z R hR m k : Set (SpatialCoordinates d))) :
      (w.toH1Function.restrict (oddGridCell z R hR m k).isOpen
        (oddGridCell_subset z hR m k)).grad x = (localSol k).grad x := by
    change base.toH1Function.grad x + G.toH1Function.grad x = _
    rw [hGgrad x, hsum_grad k x hx]
    rw [hrhoGrad' k x]
    dsimp [base, localDatum, datum]
    change φ.grad x + ((localSol k).grad x - φ.grad x) = (localSol k).grad x
    ext i
    change φ.grad x i + ((localSol k).grad x i - φ.grad x i) = (localSol k).grad x i
    ring
  have hcellResult (k : OddGridIndex d m) :
      IsWeaklyHarmonicOn a (oddGridCell z R hR m k : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (oddGridCell z R hR m k).isOpen
            (oddGridCell_subset z hR m k)) ∧
        HasZeroTraceDifferenceOn (oddGridCell z R hR m k : Set (SpatialCoordinates d))
          (w.toH1Function.restrict (oddGridCell z R hR m k).isOpen
            (oddGridCell_subset z hR m k))
          (φ.restrict (oddGridCell z R hR m k).isOpen
            (oddGridCell_subset z hR m k)) ∧
        energy a (oddGridCell z R hR m k : Set (SpatialCoordinates d))
            (w.toH1Function.restrict (oddGridCell z R hR m k).isOpen
              (oddGridCell_subset z hR m k)) =
          sInf {e : ℝ | ∃ u : H1Function (oddGridCell z R hR m k : Set (SpatialCoordinates d)),
            HasZeroTraceDifferenceOn (oddGridCell z R hR m k : Set (SpatialCoordinates d)) u
              (φ.restrict (oddGridCell z R hR m k).isOpen
                (oddGridCell_subset z hR m k)) ∧
            e = energy a (oddGridCell z R hR m k : Set (SpatialCoordinates d)) u} := by
    let W := oddGridCell z R hR m k
    let hW : (W : Set (SpatialCoordinates d)) ⊆
        (centeredCube z R hR : Set (SpatialCoordinates d)) :=
      oddGridCell_subset z hR m k
    let wk : H1Function (W : Set (SpatialCoordinates d)) :=
      w.toH1Function.restrict W.isOpen hW
    let φk : H1Function (W : Set (SpatialCoordinates d)) :=
      φ.restrict W.isOpen hW
    have hwkVal : wk.toFun =ᵐ[volume.restrict (W : Set (SpatialCoordinates d))]
        (localSol k).toFun := by
      filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with x hx
      exact hw_val_on k x hx
    have hwkGrad : wk.grad =ᵐ[volume.restrict (W : Set (SpatialCoordinates d))]
        (localSol k).grad := by
      filter_upwards [ae_restrict_mem W.isOpen.measurableSet] with x hx
      exact hw_grad_on k x hx
    have hharm : IsWeaklyHarmonicOn a (W : Set (SpatialCoordinates d)) wk := by
      intro ψ
      have hcongr :
          (fun x => vecDot (a x • wk.grad x) (ψ.toH1Function.grad x)) =ᵐ[
            volume.restrict (W : Set (SpatialCoordinates d))]
          (fun x => vecDot (a x • (localSol k).grad x)
            (ψ.toH1Function.grad x)) := by
        filter_upwards [hwkGrad] with x hx
        rw [hx]
      rw [MeasureTheory.integral_congr_ae hcongr]
      exact localSolHarm k ψ
    have htrace : HasZeroTraceDifferenceOn (W : Set (SpatialCoordinates d)) wk φk := by
      let diffH1 : H1Function (W : Set (SpatialCoordinates d)) := wk - φk
      have hdiffVal : diffH1.toFun =ᵐ[volume.restrict (W : Set (SpatialCoordinates d))]
          (rho k).toH1Function.toFun := by
        filter_upwards [hwkVal, ae_restrict_mem W.isOpen.measurableSet] with x hxw hxW
        rw [H1Function.sub_toFun]
        change wk.toFun x - φk.toFun x = _
        rw [hxw]
        rw [hrhoVal' k x]
      have hdiffGrad : diffH1.grad =ᵐ[volume.restrict (W : Set (SpatialCoordinates d))]
          (rho k).toH1Function.grad := by
        filter_upwards [hwkGrad, ae_restrict_mem W.isOpen.measurableSet] with x hxw hxW
        rw [H1Function.sub_grad]
        change wk.grad x - φk.grad x = _
        rw [hxw]
        rw [hrhoGrad' k x]
      refine ⟨
        { toH1Function := diffH1
          approx := (rho k).approx
          approx_smooth := (rho k).approx_smooth
          approx_hasCompactSupport := (rho k).approx_hasCompactSupport
          approx_support_subset := (rho k).approx_support_subset
          tendsto_approx := ?_
          tendsto_approx_grad := ?_ }, ?_, ?_⟩
      · have hEq :
            (fun n => eLpNorm (fun x => (rho k).approx n x - diffH1.toFun x) 2
              (volume.restrict (W : Set (SpatialCoordinates d)))) =
            (fun n => eLpNorm
              (fun x => (rho k).approx n x - (rho k).toH1Function.toFun x) 2
              (volume.restrict (W : Set (SpatialCoordinates d)))) := by
          funext n
          apply eLpNorm_congr_ae
          filter_upwards [hdiffVal] with x hx
          rw [hx]
        rw [hEq]
        exact (rho k).tendsto_approx
      · intro i
        have hEq :
            (fun n => eLpNorm
              (fun x => (fderiv ℝ ((rho k).approx n) x) (basisVec i) - diffH1.grad x i) 2
              (volume.restrict (W : Set (SpatialCoordinates d)))) =
            (fun n => eLpNorm
              (fun x => (fderiv ℝ ((rho k).approx n) x) (basisVec i) -
                (rho k).toH1Function.grad x i) 2
              (volume.restrict (W : Set (SpatialCoordinates d)))) := by
          funext n
          apply eLpNorm_congr_ae
          filter_upwards [hdiffGrad] with x hx
          rw [congr_fun hx i]
        rw [hEq]
        exact (rho k).tendsto_approx_grad i
      · intro x
        rw [H1Function.sub_toFun]
        change wk.toFun x = φk.toFun x + (wk.toFun x - φk.toFun x)
        ring
      · intro x
        rw [H1Function.sub_grad]
        change wk.grad x = φk.grad x + (wk.grad x - φk.grad x)
        ext i
        change wk.grad x i = φk.grad x i + (wk.grad x i - φk.grad x i)
        ring
    have hmin := energy_eq_sInf_sameTrace_of_isWeaklyHarmonicOn
      (hcellDom k) (hcellne k) (hcellEll k) hharm htrace
    exact ⟨hharm, htrace, hmin⟩
  refine ⟨w, ?_, ?_⟩
  · intro k
    exact hcellResult k
  · have hint : IntegrableOn
        (fun x => a x * vecDot (w.toH1Function.grad x) (w.toH1Function.grad x))
        (centeredCube z R hR : Set (SpatialCoordinates d)) volume := by
      apply SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.integrableOn_mul_of_integrableOn_vecNormSq
        hUopen.measurableSet ha.measurable
        (C := Lam)
      · intro x hx
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact (haBounds x hx).2
        · exact hlam.le.trans (haBounds x hx).1
      · simpa [vecNormSq] using
          (integrableOn_vecNormSq_h1Grad w.toH1Function)
    rw [energy_eq_sum_oddGridCell_restrict z hR m a w.toH1Function hint]
    apply Finset.sum_congr rfl
    intro k hk
    exact (hcellResult k).2.2

end SubdiffusiveProcess
