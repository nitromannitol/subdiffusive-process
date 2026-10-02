import Mathlib
import SubdiffusiveProcess.Paper.conv_represented_catalogue_source_clause
import SubdiffusiveProcess.Paper.prop_growth
import SubdiffusiveProcess.Paper.prop_growth_large_root
import SubdiffusiveProcess.Sobolev.BoundaryGrowthEnergy
import SubdiffusiveProcess.Lane4.CutoffCoefficientRepresentative
import SubdiffusiveProcess.Sobolev.NativeGrowthOnLargeCubes
import SubdiffusiveProcess.Sobolev.NativeBoundaryMinimizer
import SubdiffusiveProcess.Sobolev.NativeH10
import SubdiffusiveProcess.Sobolev.HarmonicDiffMaxPrinciple
import SubdiffusiveProcess.Sobolev.NativeBoundaryResponse
import SubdiffusiveProcess.Lane4.Bridge

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess SubdiffusiveProcess.Lane4
open Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped Topology ENNReal NNReal InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- A Dirichlet solution with a continuous representative is the value function of a native
`H¹` function with zero-trace difference from the datum, that vanishes-difference on the frontier. -/
theorem aux_conv_represented_cell_clause_construct
    {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (thetaH1 : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)))
    (hthc : Continuous thetaH1.toFun)
    (udata : weakSobolevGraph (centeredCube z r hr))
    (hkill : (udata : SobolevData (centeredCube z r hr)) - sobolevDataOfH1 thetaH1 ∈
      killedSobolevGraph (centeredCube z r hr))
    (U : SpatialCoordinates d → ℝ) (hUc : Continuous U)
    (hUae : (((udata : SobolevData (centeredCube z r hr)).1 : DomainL2 (centeredCube z r hr)) :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube z r hr : Set (SpatialCoordinates d))] U) :
    ∃ ucell : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
      HasZeroTraceDifferenceOn (centeredCube z r hr : Set (SpatialCoordinates d)) ucell thetaH1 ∧
      ucell.toFun = U ∧
      sobolevDataOfH1 ucell = (udata : SobolevData (centeredCube z r hr)) ∧
      ∀ x ∈ frontier ((centeredCube z r hr : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)), U x = thetaH1.toFun x := by
  classical
  let Q := centeredCube z r hr
  let wk : killedSobolevGraph Q := ⟨(udata : SobolevData Q) - sobolevDataOfH1 thetaH1, hkill⟩
  obtain ⟨v, hvfun, hvgrad⟩ := exists_nativeH10Function_of_killedSobolevGraph wk
  let V : SpatialCoordinates d → ℝ := fun x => U x - thetaH1.toFun x
  have hVc : Continuous V := hUc.sub hthc
  have hwk1 : ((wk.val.1 : DomainL2 Q) : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (Q : Set (SpatialCoordinates d))] V := by
    have h1 := Lp.coeFn_sub ((udata : SobolevData Q).1) ((sobolevDataOfH1 thetaH1).1)
    have h2 := sobolevDataOfH1_fst_coeFn thetaH1
    filter_upwards [h1, h2, hUae] with x hx1 hx2 hx3
    change ((udata : SobolevData Q).1 - (sobolevDataOfH1 thetaH1).1 : DomainL2 Q) x = _
    rw [hx1, Pi.sub_apply, hx2, hx3]
  have hvV : V =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] v.toH1Function.toFun := by
    have : v.toH1Function.toFun = fun x => wk.val.1 x := hvfun
    rw [this]
    exact hwk1.symm
  let v' : H10Function (Q : Set (SpatialCoordinates d)) := H10Function.ofAEEq v V hvV
  refine ⟨thetaH1 + v'.toH1Function, ⟨v', fun x => rfl, fun x => rfl⟩, ?_, ?_, ?_⟩
  · funext x
    change thetaH1.toFun x + V x = U x
    simp only [V]; ring
  · -- Sobolev data of the glued function
    rw [sobolevDataOfH1_add]
    have hv'data : sobolevDataOfH1 v'.toH1Function = wk.val := by
      have hfun' : v'.toH1Function.toFun = V := rfl
      apply Prod.ext
      · apply Lp.ext
        filter_upwards [sobolevDataOfH1_fst_coeFn v'.toH1Function, hwk1] with x hx hy
        rw [hx, hfun', ← hy]
      · funext i
        apply Lp.ext
        filter_upwards [sobolevDataOfH1_snd_coeFn v'.toH1Function i] with x hx
        rw [hx]
        have : v'.toH1Function.grad = v.toH1Function.grad := rfl
        rw [this, hvgrad]
    rw [hv'data]
    change sobolevDataOfH1 thetaH1 + ((udata : SobolevData Q) - sobolevDataOfH1 thetaH1) = _
    abel
  · intro x hx
    have hV0 := aux_conv_represented_source_clause_frontier z r hr wk.val wk.2 V hVc hwk1 x hx
    simp only [V] at hV0
    linarith


/-- A Dirichlet solution with zero source represented by a native function is weakly
harmonic for any representative of its coefficient. -/
theorem aux_conv_represented_cell_clause_harmonic
    {d : ℕ} {Q : Opens (SpatialCoordinates d)} (a : PositiveCoefficient Q)
    (c : SpatialCoordinates d → ℝ)
    (hc : (fun x => a.val x) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] c)
    (thetaH1 : H1Function (Q : Set (SpatialCoordinates d))) (udata : weakSobolevGraph Q)
    (hsolve : SolvesDirichlet a (fun _ => 0)
      ⟨sobolevDataOfH1 thetaH1, sobolevDataOfH1_mem_weak thetaH1⟩ udata)
    (ucell : H1Function (Q : Set (SpatialCoordinates d)))
    (hdata : sobolevDataOfH1 ucell = (udata : SobolevData Q)) :
    IsWeaklyHarmonicOn c (Q : Set (SpatialCoordinates d)) ucell := by
  intro φ
  have hkφ := sobolevDataOfH1_mem_killed φ
  have h0 := hsolve.2 ⟨sobolevDataOfH1 φ.toH1Function, hkφ⟩
  simp only [zero_mul, integral_zero] at h0
  rw [← hdata, Lane4.sobolevCoefficientForm_eq_upstream_integral a c hc] at h0
  have hae : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))),
      vecDot (matVecMul (scalarCoeffField c x) (fun i => (sobolevDataOfH1 ucell).2 i x))
        (fun i => (sobolevDataOfH1 φ.toH1Function).2 i x) =
      vecDot (c x • ucell.grad x) (φ.toH1Function.grad x) := by
    filter_upwards [ae_all_iff.2 (fun i => sobolevDataOfH1_snd_coeFn ucell i),
      ae_all_iff.2 (fun i => sobolevDataOfH1_snd_coeFn φ.toH1Function i)] with x hu hφ'
    have e1 : (fun i => (sobolevDataOfH1 ucell).2 i x) = ucell.grad x := funext hu
    have e2 : (fun i => (sobolevDataOfH1 φ.toH1Function).2 i x) = φ.toH1Function.grad x :=
      funext hφ'
    rw [e1, e2, Lane4.vecDot_matVecMul_scalarCoeffField, Homogenization.vecDot_smul_left]
    rfl
  rw [integral_congr_ae hae] at h0
  exact h0

/-- Pointwise part of the cell clause: for one cutoff and one environment, the cell solution with
the given `C²` trace exists with the stated properties, given the interior-centre bounds of the
actual growth theorem. The geometric factor `A` depends only on the cube. -/
theorem aux_conv_represented_cell_clause_pointwise
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (N : ℕ) (β : BilateralField d) (t alpha K Kh : ℝ),
      0 ≤ t → 0 ≤ K → K ≤ Kh → 0 ≤ Kh →
      (∀ (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ), ContDiff ℝ 2 phi →
        c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi →
        ∀ (b u : weakSobolevGraph (centeredCube z r hr)),
          ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
          SolvesDirichlet (Lane4.cutoffPositiveCoefficient M H β N z hr) (fun _ => (0 : ℝ)) b u →
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ centeredCube z r hr →
            0 < rad → rad ≤ 1 →
            localGradientEnergy (Lane4.cutoffPositiveCoefficient M H β N z hr)
                (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
                (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
                (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
              K * (0 + Cphi) ^ 2 * rad ^ t) ∧
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            ((u : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
              =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
            IsHolderOn alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ∧
            cAlphaNorm alpha (closedCube z r hr : Set (SpatialCoordinates d)) U ≤
              K * (0 + Cphi))) →
      ∀ (theta : SpatialCoordinates d → ℝ)
        (thetaH1 : H1Function (centeredCube z r hr : Set (SpatialCoordinates d))),
        ContDiff ℝ 2 theta → thetaH1.toFun = theta →
        ∃ ucell : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
          IsWeaklyHarmonicOn (cutoffCoefficient M H β N)
            (centeredCube z r hr : Set (SpatialCoordinates d)) ucell ∧
          HasZeroTraceDifferenceOn (centeredCube z r hr : Set (SpatialCoordinates d))
            ucell thetaH1 ∧
          ContinuousOn ucell.toFun
            (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
            ucell.toFun x = theta x) ∧
          (∀ (x : SpatialCoordinates d) (rr : ℝ), 0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal
                ((Lane4.cutoffPositiveCoefficient M H β N z hr).val y *
                  ∑ i : Fin d, (((sobolevDataOfH1 ucell).2 i) y) ^ 2)))
              (Metric.ball x rr) ≤
            ENNReal.ofReal (((2 ^ t * A) * Kh) *
              (c2Norm (closure (centeredCube z r hr : Set (SpatialCoordinates d))) theta) ^ 2 *
                rr ^ t)) ∧
          IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
            ucell.toFun ∧
          cAlphaNorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
            ucell.toFun ≤
            Kh * c2Norm (closure (centeredCube z r hr : Set (SpatialCoordinates d))) theta := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨A, hA1, hAgeom⟩ := native_energy_and_measure_growth_all_cubes z hr
  refine ⟨A, hA1, ?_⟩
  intro N β t alpha K Kh ht0 hK0 hKK hKh0 hprop theta thetaH1 hθ2 hθ
  have hcl := aux_conv_represented_source_clause_closure z r hr
  set a := Lane4.cutoffPositiveCoefficient M H β N z hr with ha_def
  have hP := centeredCube_killedPoincare z hr
  let bdata : weakSobolevGraph (centeredCube z r hr) :=
    ⟨sobolevDataOfH1 thetaH1, sobolevDataOfH1_mem_weak thetaH1⟩
  let udata := dirichletMinimizer (killedResponseSpace hP) a bdata
  have hsolve : SolvesDirichlet a (fun _ => (0 : ℝ)) bdata udata :=
    dirichletMinimizer_solves_zero hP a bdata
  have hb : ((bdata : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] theta := by
    have := sobolevDataOfH1_fst_coeFn thetaH1
    rw [hθ] at this
    exact this
  obtain ⟨hgrowth, U, hUc, hUae, hUh, hUn⟩ := hprop theta
    (c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) theta) hθ2 le_rfl bdata udata hb hsolve
  have hthc : Continuous thetaH1.toFun := by rw [hθ]; exact hθ2.continuous
  obtain ⟨ucell, hzt, hfun, hdata, hfront⟩ :=
    aux_conv_represented_cell_clause_construct z r hr thetaH1 hthc udata hsolve.1 U hUc hUae
  have hc : (fun x => a.val x) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      cutoffCoefficient M H β N :=
    (cutoffPositiveCoefficient_representative M H β N z hr).2.2.2
  refine ⟨ucell, aux_conv_represented_cell_clause_harmonic a _ hc thetaH1 udata hsolve ucell hdata,
    hzt, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfun]; exact hUc.continuousOn
  · intro x hx
    rw [hfun, hfront x hx, hθ]
  · -- growth at every centre
    have hCphi := aux_prop_growth_c2Norm_nonneg (closedCube z r hr : Set (SpatialCoordinates d)) theta
    have hB : 0 ≤ K * (0 + c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) theta) ^ 2 :=
      mul_nonneg hK0 (sq_nonneg _)
    have hg : ∀ x ∈ ((centeredCube z r hr : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)), ∀ rad : ℝ, 0 < rad → rad ≤ 1 →
        localGradientEnergy a
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (Metric.isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (sobolevDataOfH1 ucell)) ≤
          (K * (0 + c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) theta) ^ 2) * rad ^ t := by
      intro x hx rad hrad hrad1
      rw [hdata]
      exact hgrowth x rad hx hrad hrad1
    obtain ⟨-, hmeas⟩ := hAgeom a (fun y => a.val y) (Filter.EventuallyEq.refl _ _) ucell
      (K * (0 + c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) theta) ^ 2) t hB ht0 hg
    intro x rr hrr hrr1
    have hcongr : (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal (a.val y * ∑ i : Fin d, (ucell.grad y i) ^ 2)) =
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
        (fun y => ENNReal.ofReal
          (a.val y * ∑ i : Fin d, (((sobolevDataOfH1 ucell).2 i) y) ^ 2)) := by
      apply withDensity_congr_ae
      filter_upwards [ae_all_iff.2 (fun i => sobolevDataOfH1_snd_coeFn ucell i)] with y hy
      simp only [hy]
    rw [← hcongr, hcl]
    refine (hmeas x rr hrr hrr1).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : K * (0 + c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) theta) ^ 2 ≤
        Kh * c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) theta ^ 2 := by
      rw [zero_add]
      exact mul_le_mul_of_nonneg_right hKK (sq_nonneg _)
    have h2 : 0 ≤ 2 ^ t * A := mul_nonneg (Real.rpow_nonneg (by norm_num) t) (by linarith)
    have hpow : 0 ≤ rr ^ t := Real.rpow_nonneg hrr.le t
    calc 2 ^ t * (A * (K * (0 + c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) theta) ^ 2))
          * rr ^ t
        = (2 ^ t * A) * (K * (0 + c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) theta) ^ 2)
          * rr ^ t := by ring
      _ ≤ (2 ^ t * A) * (Kh * c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) theta ^ 2)
          * rr ^ t := by gcongr
      _ = ((2 ^ t * A) * Kh) * c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) theta ^ 2
          * rr ^ t := by ring
  · rw [hfun, hcl]; exact hUh
  · rw [hfun, hcl]
    refine hUn.trans ?_
    have hCphi := aux_prop_growth_c2Norm_nonneg (closedCube z r hr : Set (SpatialCoordinates d)) theta
    calc K * (0 + c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) theta)
        = K * c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) theta := by ring
      _ ≤ Kh * c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) theta :=
        mul_le_mul_of_nonneg_right hKK hCphi

/-- **Catalogue clause L (cell solutions) from the actual growth theorem.**
For every `C²` boundary datum `theta` with an `H¹` packaging `thetaH1`, on one measurable full-measure
event and for every cutoff `N`, the `A_N`-harmonic cell solution with that trace exists as a native `H¹`
function that is continuous on the closed cube, has boundary values `theta` on the frontier, and satisfies
the energy-measure growth bound at every centre with constant `Kg N β · ‖theta‖²_{C²} · rr^t` and the
`C^α`-norm bound `Kh N β · ‖theta‖_{C²}`. The constants are measurable, nonnegative, first-moment banked. -/
theorem conv_represented_catalogue_cell_clause
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (Pin : in_poincare d hd I) (X : in_extension d hd I)
    (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Sob : SobolevFoundationalInput d hd) (t alpha : ℝ)
    (ht : (d : ℝ) - 1 < t) (htd : t < d) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M I Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
      ∃ (Kg Kh : ℕ → BilateralField d → ℝ) (Cbg Cbh : ℝ) (G : Set (BilateralField d)),
        MeasurableSet G ∧ (chaosSampleLaw M).toMeasure Gᶜ = 0 ∧ 0 ≤ Cbg ∧ 0 ≤ Cbh ∧
        (∀ N, Measurable (Kg N)) ∧ (∀ N β, 0 ≤ Kg N β) ∧
        (∀ N, MemLp (Kg N) (ENNReal.ofReal 1) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (Kg N) (ENNReal.ofReal 1) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal Cbg) ∧
        (∀ N, Measurable (Kh N)) ∧ (∀ N β, 0 ≤ Kh N β) ∧
        (∀ N, MemLp (Kh N) (ENNReal.ofReal 1) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (Kh N) (ENNReal.ofReal 1) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal Cbh) ∧
        ∀ (N : ℕ), ∀ β ∈ G, ∀ (theta : SpatialCoordinates d → ℝ)
          (thetaH1 : H1Function (centeredCube z r hr : Set (SpatialCoordinates d))),
          ContDiff ℝ 2 theta → thetaH1.toFun = theta →
          ∃ ucell : H1Function (centeredCube z r hr : Set (SpatialCoordinates d)),
            IsWeaklyHarmonicOn (cutoffCoefficient M H β N)
              (centeredCube z r hr : Set (SpatialCoordinates d)) ucell ∧
            HasZeroTraceDifferenceOn (centeredCube z r hr : Set (SpatialCoordinates d))
              ucell thetaH1 ∧
            ContinuousOn ucell.toFun
              (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
            (∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
              ucell.toFun x = theta x) ∧
            (∀ (x : SpatialCoordinates d) (rr : ℝ), 0 < rr → rr ≤ 1 →
              ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
                (fun y => ENNReal.ofReal
                  ((Lane4.cutoffPositiveCoefficient M H β N z hr).val y *
                    ∑ i : Fin d, (((sobolevDataOfH1 ucell).2 i) y) ^ 2)))
                (Metric.ball x rr) ≤
              ENNReal.ofReal (Kg N β *
                (c2Norm (closure (centeredCube z r hr : Set (SpatialCoordinates d))) theta) ^ 2 *
                  rr ^ t)) ∧
            IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
              ucell.toFun ∧
            cAlphaNorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
              ucell.toFun ≤
              Kh N β * c2Norm (closure (centeredCube z r hr : Set (SpatialCoordinates d))) theta := by
  classical
  obtain ⟨δE, hδE, hE⟩ := prop_growth d hd I Pin X W Cp Sob t alpha 1 (fun _ => (1 : ℝ))
    ht htd ha ha1 (fun _ => le_rfl)
  obtain ⟨δL, hδL, hL⟩ := prop_growth_large_root d hd I Pin X W Cp Sob t alpha 1 (fun _ => (1 : ℝ))
    ht htd ha ha1 (fun _ => le_rfl)
  refine ⟨min δE δL, lt_min hδE hδL, ?_⟩
  intro M Rm Sreg It H hIR hδ z r hr
  set P0 : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure with hP0
  obtain ⟨K, Cbound, hmem, hnorm, hge, hprop⟩ := (dite (r ≤ 1)
    (fun hr1 => hE M Rm Sreg It H hIR (hδ.trans (min_le_left _ _)) z r hr hr1)
    (fun hr1 => hL M Rm Sreg It H hIR (hδ.trans (min_le_right _ _)) z r hr
      (lt_of_not_ge hr1)))
  have ht0 : 0 ≤ t := by
    have : (1 : ℝ) < t := by
      have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    linarith
  obtain ⟨Kh, hKhm, hKhnn, hKle, hKhbank⟩ :=
    aux_conv_represented_source_clause_pos_majorant (μ := P0) K (fun N => hmem 0 N)
      (Cbound 0) (fun N => hnorm 0 N)
  obtain ⟨A, hA1, hpw⟩ := aux_conv_represented_cell_clause_pointwise hd M H z r hr
  have hAnn : 0 ≤ 2 ^ t * A := mul_nonneg (Real.rpow_nonneg (by norm_num) t) (by linarith)
  have hev := (ae_all_iff.2 hKle).and (hge.and hprop)
  obtain ⟨G, hGm, hGnull, hGP⟩ := aux_conv_represented_source_clause_event hev
  refine ⟨fun N β => (2 ^ t * A) * Kh N β, Kh, (2 ^ t * A) * max (Cbound 0) 0, max (Cbound 0) 0, G,
    hGm, hGnull, mul_nonneg hAnn (le_max_right _ _), le_max_right _ _,
    fun N => (hKhm N).const_mul _, fun N β => mul_nonneg hAnn (hKhnn N β), fun N => ?_,
    hKhm, hKhnn, hKhbank, ?_⟩
  · refine ⟨(hKhbank N).1.const_mul _, ?_⟩
    calc eLpNorm (fun β => (2 ^ t * A) * Kh N β) (ENNReal.ofReal 1) P0
        ≤ ‖(2 ^ t * A : ℝ)‖ₑ * eLpNorm (Kh N) (ENNReal.ofReal 1) P0 := by
          simpa [Pi.smul_apply, smul_eq_mul] using
            (eLpNorm_const_smul_le (c := (2 ^ t * A : ℝ)) (f := Kh N) (p := ENNReal.ofReal 1)
              (μ := P0))
      _ ≤ ‖(2 ^ t * A : ℝ)‖ₑ * ENNReal.ofReal (max (Cbound 0) 0) :=
          mul_le_mul_right (hKhbank N).2 _
      _ = ENNReal.ofReal ((2 ^ t * A) * max (Cbound 0) 0) := by
          rw [Real.enorm_eq_ofReal hAnn]
          exact (ENNReal.ofReal_mul hAnn).symm
  · intro N β hβ theta thetaH1 hθ2 hθ
    obtain ⟨hKleβ, hgeβ, hmainβ⟩ := hGP β hβ
    exact hpw N β t alpha (K N β) (Kh N β) ht0 (by linarith [hgeβ N]) (hKleβ N) (hKhnn N β)
      (fun phi Cphi hphi hCphi b u hb hsolve =>
        hmainβ N (fun _ => (0 : ℝ)) 0 le_rfl aemeasurable_const
          (Filter.Eventually.of_forall fun _ => by norm_num) phi Cphi hphi hCphi b u hb hsolve)
      theta thetaH1 hθ2 hθ

end Paper
