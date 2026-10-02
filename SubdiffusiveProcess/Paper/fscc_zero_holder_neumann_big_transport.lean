import SubdiffusiveProcess.Paper.fscc_holder_predicates
import SubdiffusiveProcess.Paper.fscc_char_holder_neumann
import SubdiffusiveProcess.Paper.calib3_HT
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Paper.lane4_deterministic_good_scale_input
import SubdiffusiveProcess.Paper.lem_as_regularity_affine_transport
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.ChaosRootFieldLaw
import SubdiffusiveProcess.Main.ScaledLayerLaw
import SubdiffusiveProcess.Main.LayerScaling
import SubdiffusiveProcess.Main.CommonScaleLaw
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.CutoffPotential
import SubdiffusiveProcess.Main.InfraredPartialSum
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Main.InfraredAdmissible
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient
import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
import SubdiffusiveProcess.Main.BilateralField
import SubdiffusiveProcess.Lane4.CubeDilation
import SubdiffusiveProcess.Sobolev.DirichletResponse
import SubdiffusiveProcess.Sobolev.MeanZero
import SubdiffusiveProcess.Sobolev.CoefficientRestriction
import SubdiffusiveProcess.Sobolev.ResponseComparison
import SubdiffusiveProcess.Probability.GMCFieldLaws
import SubdiffusiveProcess.Lane4.Bridge
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic




set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology Metric ProbabilityTheory
open SubdiffusiveProcess SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace Paper

/-- **Big-root potential transport** (exact): for `m = -j'`, `j' ≥ 1`, the layer sum of the
infrared-free field at `w + 3^{-m}y` and depth `N` is the layer sum of the shifted field up to depth
`N + j'` with the top `j'` layers removed (`calib3_HT`). -/
theorem aux_fscc_zeroBig_potential {d : ℕ} (jn : ℕ) (hjn : 0 < jn) (w : SpatialCoordinates d) (N : ℕ)
    (om : BilateralField d) (y : SpatialCoordinates d) :
    cutoffPotential (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om N (w + (3 : ℝ) ^ (-(-(jn : ℤ))) • y) =
      cutoffPotential (calib3_HT d jn) (aux_transport_S (-(jn : ℤ)) w om) (N + jn) y := by
  set m : ℤ := -(jn : ℤ) with hm
  set x := w + (3 : ℝ) ^ (-m) • y with hx
  have hSk : ∀ k : ℕ, (aux_transport_S m w om) (-(Int.ofNat k)) y = om (-(Int.ofNat k) - m) x := by
    intro k; exact aux_transport_S_apply m w om (-(Int.ofNat k)) y
  have hshift := aux_transport_potential_sum (fun j => om j x) N m (by omega)
  simp only at hshift
  have hret : aux_transport_ret m (fun j => om j x) = aux_transport_retained m x om := rfl
  rw [hret] at hshift
  have hK : ((N : ℤ) - m).toNat = N + jn := by omega
  rw [hK] at hshift
  rw [aux_fscc_holNeuH_retained_eq_neg m (by omega) x om] at hshift
  have hnm : (-m).toNat = jn := by omega
  have hS1 : ∑ k ∈ Finset.range (N + jn + 1), (aux_transport_S m w om) (-(Int.ofNat k)) y =
      ∑ k ∈ Finset.range (N + jn + 1), om (-(Int.ofNat k) - m) x :=
    Finset.sum_congr rfl (fun k _ => hSk k)
  have hS2 : ∑ i ∈ Finset.range jn, (aux_transport_S m w om) (-(Int.ofNat i)) y =
      ∑ k ∈ Finset.range jn, om (-m - (k : ℤ)) x := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hSk k]
    have hk : (-(Int.ofNat k) - m) = (-m - (k : ℤ)) := by rw [Int.ofNat_eq_natCast]; ring
    rw [hk]
  rw [hnm] at hshift
  unfold cutoffPotential calib3_HT
  simp only [Pi.zero_apply, ContinuousMap.zero_apply, ContinuousMap.neg_apply,
    ContinuousMap.coe_sum, Finset.sum_apply, zero_add]
  rw [hS1, hS2]
  linarith [hshift]

/-- Coefficient transport with a deterministic reference: if the two potentials agree, the coefficients
differ by the factor `κ_K/κ_N`. -/
theorem aux_fscc_zeroBig_coefficient {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℤ) (w : SpatialCoordinates d)
    (H1 H2 : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N K : ℕ) (om : BilateralField d) (y : SpatialCoordinates d)
    (hpot : cutoffPotential H1 om N (w + (3 : ℝ) ^ (-m) • y) =
      cutoffPotential H2 (aux_transport_S m w om) K y) :
    cutoffCoefficient M H1 om N (w + (3 : ℝ) ^ (-m) • y) =
      aux_transport_kappa M K / aux_transport_kappa M N *
        cutoffCoefficient M H2 (aux_transport_S m w om) K y := by
  have hposK : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M K := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M K
  have hposN : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hne1 : SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≠ 0 := hposN.ne'
  have hne2 : SubdiffusiveProcess.CoarseGrainingVocab.ahom M K ≠ 0 := hposK.ne'
  have hL1 : cutoffCoefficient M H1 om N (w + (3 : ℝ) ^ (-m) • y) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
      Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
      Real.exp (cutoffPotential H1 om N (w + (3 : ℝ) ^ (-m) • y)) := by
    unfold cutoffCoefficient
    rw [Real.exp_sub]
    field_simp
  have hR1 : cutoffCoefficient M H2 (aux_transport_S m w om) K y *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M K *
      Real.exp (((K : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
      Real.exp (cutoffPotential H2 (aux_transport_S m w om) K y) := by
    unfold cutoffCoefficient
    rw [Real.exp_sub]
    field_simp
  have hexppot : Real.exp (cutoffPotential H1 om N (w + (3 : ℝ) ^ (-m) • y)) =
      Real.exp (cutoffPotential H2 (aux_transport_S m w om) K y) := by
    rw [hpot]
  have hcombine : cutoffCoefficient M H1 om N (w + (3 : ℝ) ^ (-m) • y) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
      Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) =
      (cutoffCoefficient M H2 (aux_transport_S m w om) K y *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M K *
          Real.exp (((K : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) := by
    rw [hL1, hR1, hexppot]
  unfold aux_transport_kappa
  have hexpN : Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≠ 0 :=
    (Real.exp_pos _).ne'
  have hexpK : Real.exp (((K : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) ≠ 0 :=
    (Real.exp_pos _).ne'
  rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hexpN hne1)]
  linear_combination hcombine


theorem aux_fscc_zeroBig_coeff_ident {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H1 H2 : BilateralField d → C(SpatialCoordinates d, ℝ))
    (m : ℤ) (w : SpatialCoordinates d) (N : ℕ) (z0 : SpatialCoordinates d)
    (omega : BilateralField d)
    (ref : ℝ) (hrefpos : 0 < ref) (K : ℕ)
    (hcoeff : ∀ y : SpatialCoordinates d,
      cutoffCoefficient model H1 omega N (w + (3 : ℝ) ^ (-m) • y) =
        ref * cutoffCoefficient model H2 (aux_transport_S m w omega) K y) :
    ∀ a1 : PositiveCoefficient (centeredCube z0 1 one_pos),
      (∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        (a1.val : SpatialCoordinates d → ℝ) x =
          cutoffCoefficient model H1 omega N (w + (3 : ℝ) ^ (-m) • x)) →
      a1 = scalePositiveCoefficient ref hrefpos
        (cutoffPositiveCoefficient model H2 (aux_transport_S m w omega) K z0 one_pos) := by
  intro a1 ha1
  have hA2 := aux_fscc_holNeuH_cutoffPos_val model H2 (aux_transport_S m w omega)
    K z0 one_pos
  have hval : ∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      (a1.val : SpatialCoordinates d → ℝ) x =
        (scalePositiveCoefficient ref hrefpos
          (cutoffPositiveCoefficient model H2 (aux_transport_S m w omega) K z0 one_pos)).val x := by
    filter_upwards [ha1, hA2,
      scalePositiveCoefficient_coeFn ref hrefpos
        (cutoffPositiveCoefficient model H2 (aux_transport_S m w omega) K z0 one_pos)] with x hx1 hx2 hx3
    rw [hx1, hx3, hx2, hcoeff x]
  exact Subtype.ext (Lp.ext hval)

/-- **Core per-`(J, omega)` content of the big-root transport**: given the coefficient identification
`hcoeff` (the root-cube coefficient is the constant `ref` times the level-`K` coefficient of the shifted
field on the unit cube) and the unit-cube Hölder bound `hcorS` for that level-`K` coefficient with
constant `Kc`, produce the `holNeu` fact on the root cube `(z, r)`. -/
theorem aux_fscc_zeroBig_core {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H1 H2 : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z z0 w : SpatialCoordinates d) (m : ℤ) (r : ℝ) (hr : 0 < r) (alpha : ℝ) (halpha : 0 < alpha)
    (hz0 : z0 = fun _ : Fin d => (1 / 2 : ℝ))
    (hTeq : ∀ x : SpatialCoordinates d, cubeDilation z z0 r x = w + (3 : ℝ) ^ (-m) • x)
    (hinjQ : ∀ x : SpatialCoordinates d, cubeDilation z0 z r⁻¹ (cubeDilation z z0 r x) = x)
    (ref : ℝ) (hrefpos : 0 < ref) (K : ℕ) (Kc : ℝ) (J : ℕ) (omega : BilateralField d)
    (hcoeff : ∀ a1 : PositiveCoefficient (centeredCube z0 1 one_pos),
      (∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        (a1.val : SpatialCoordinates d → ℝ) x =
          cutoffCoefficient model H1 omega J (w + (3 : ℝ) ^ (-m) • x)) →
      a1 = scalePositiveCoefficient ref hrefpos
        (cutoffPositiveCoefficient model H2 (aux_transport_S m w omega) K z0 one_pos))
    (hcorS : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
      AEMeasurable F (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        |F x| ≤ Kf) →
      (∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ v : meanZeroSobolevGraph (centeredCube z0 1 one_pos),
        SolvesNeumann
          (cutoffPositiveCoefficient model H2 (aux_transport_S m w omega) K z0 one_pos) F v →
        ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
          IsHolderOn alpha (closedCube z0 1 one_pos : Set (SpatialCoordinates d)) U ∧
          ((v : SobolevData (centeredCube z0 1 one_pos)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))] U ∧
          cAlphaNorm alpha (closedCube z0 1 one_pos : Set (SpatialCoordinates d)) U ≤
            Kc * Kf)
    (hq : Measure.QuasiMeasurePreserving (cubeDilation z z0 r)
      (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    aux_fscc_holder_predicates_holNeu d z r hr
      (cutoffPositiveCoefficient model H1 omega J z hr) alpha
      (Real.sqrt d ^ alpha * Kc * r ^ (2 - alpha) / ref) := by
  subst hz0
  intro F Kf hKf hF hFb hFint u hsol
  obtain ⟨a1, ha1, -, hNeumannPart⟩ :=
    lem_as_regularity_affine_transport d model H1 omega J z r hr
  obtain ⟨F1, v1, hF1def, hF1meas, hF1b, hF1z, hsolve1, hv1val, hv1grad, -⟩ :=
    hNeumannPart F Kf hKf hF.aemeasurable
      (ae_restrict_of_forall_mem (centeredCube z r hr).isOpen.measurableSet hFb) hFint u hsol
  unfold unitNeumannCube at hF1meas hF1b hF1z hv1val
  have ha1' : ∀ᵐ x ∂ volume.restrict (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
      (a1.val : SpatialCoordinates d → ℝ) x =
        cutoffCoefficient model H1 omega J (w + (3 : ℝ) ^ (-m) • x) := by
    filter_upwards [ha1, hq.ae (aux_fscc_holNeuH_cutoffPos_val model H1 omega J z hr)]
      with x hx1 hx2
    rw [hx1, hx2, hTeq]
  clear ha1 hNeumannPart hsol hF hFb hFint hF1def
  have hident := hcoeff a1 ha1'
  have hsolve2 := aux_fscc_holNeuH_solvesNeumann_unscale ref hrefpos a1
    (cutoffPositiveCoefficient model H2 (aux_transport_S m w omega) K (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) hident
    F1 v1 hsolve1
  have hF1'meas : AEMeasurable (fun x => F1 x / ref)
      (volume.restrict (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d))) :=
    hF1meas.div_const ref
  have hF1'b : ∀ᵐ x ∂ volume.restrict (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
      |F1 x / ref| ≤ r ^ 2 * Kf / ref := by
    filter_upwards [hF1b] with x hx
    rw [abs_div, abs_of_pos hrefpos]
    exact div_le_div_of_nonneg_right hx hrefpos.le
  have hF1'z : (∫ x in (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)), F1 x / ref) =
      0 := by
    rw [show (fun x => F1 x / ref) = fun x => ref⁻¹ * F1 x from by
        funext x; ring, integral_const_mul, hF1z, mul_zero]
  have hKfref0 : 0 ≤ r ^ 2 * Kf / ref := div_nonneg (by positivity) hrefpos.le
  obtain ⟨U, hUcont, hUhol, hUeq, hUcalpha⟩ :=
    hcorS (fun x => F1 x / ref) (r ^ 2 * Kf / ref) hKfref0 hF1'meas hF1'b hF1'z v1 hsolve2
  have hsemi0 : holderSeminorm alpha
      (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) U ≤
        Kc * (r ^ 2 * Kf / ref) :=
    (aux_fscc_holder_predicates_holderSeminorm_le _ _ U).trans hUcalpha
  obtain ⟨hUcO, hUholQ, hsemiQ⟩ :=
    aux_fscc_holNeuH_holder_transport z (fun _ : Fin d => (1 / 2 : ℝ)) hr halpha.le U
      hUcont.continuousOn hUhol
  set Ufinal : SpatialCoordinates d → ℝ := fun y => U (cubeDilation (fun _ : Fin d => (1 / 2 : ℝ)) z r⁻¹ y) with hUfd
  have hsemiQ' : holderSeminorm alpha
      (closedCube z r hr : Set (SpatialCoordinates d)) Ufinal ≤
      r ^ (-alpha) * (Kc * (r ^ 2 * Kf / ref)) :=
    hsemiQ.trans (mul_le_mul_of_nonneg_left hsemi0 (Real.rpow_nonneg hr.le _))
  have hdiff := aux_fscc_holNeuH_holder_dist_of_seminorm
    (closedCube z r hr : Set (SpatialCoordinates d)) Ufinal alpha
    (r ^ (-alpha) * (Kc * (r ^ 2 * Kf / ref)))
    halpha hUholQ hsemiQ'
  have hUv : ∀ᵐ x ∂ volume.restrict (centeredCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)),
      (u : SobolevData (centeredCube z r hr)).1 (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x) = U x := by
    filter_upwards [hUeq, hv1val] with x hx1 hx2
    rw [← hx1, hx2]
  have hUfinalCont : Continuous Ufinal := hUcont.comp (continuous_cubeDilation (fun _ : Fin d => (1 / 2 : ℝ)) z r⁻¹)
  have hp : MeasurableSet {y : SpatialCoordinates d |
      (u : SobolevData (centeredCube z r hr)).1 y = Ufinal y} :=
    measurableSet_eq_fun
      (Lp.stronglyMeasurable (u : SobolevData (centeredCube z r hr)).1).measurable
      hUfinalCont.measurable
  refine ⟨Ufinal, hUcO, ?_, ?_⟩
  · refine (aux_fscc_holNeuH_ae_iff z (fun _ : Fin d => (1 / 2 : ℝ)) hr hp).mpr ?_
    filter_upwards [hUv] with x hx
    show (u : SobolevData (centeredCube z r hr)).1 (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x) =
      Ufinal (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x)
    rw [hUfd]
    show (u : SobolevData (centeredCube z r hr)).1 (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x) =
      U (cubeDilation (fun _ : Fin d => (1 / 2 : ℝ)) z r⁻¹
        (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x))
    rw [hinjQ x]
    exact hx
  · intro x hx y hy
    have hb := hdiff x hx y hy
    have hpow : r ^ (-alpha) * r ^ 2 = r ^ (2 - alpha) := by
      have h2 : (r : ℝ) ^ (2 : ℕ) = r ^ (2 : ℝ) := (Real.rpow_natCast r 2).symm
      rw [h2, ← Real.rpow_add hr]
      congr 1; ring
    calc |Ufinal x - Ufinal y| ≤
          Real.sqrt d ^ alpha *
            (r ^ (-alpha) * (Kc * (r ^ 2 * Kf / ref))) *
            dist x y ^ alpha := hb
      _ = Real.sqrt d ^ alpha * Kc *
            (r ^ (-alpha) * r ^ 2) * Kf / ref * dist x y ^ alpha := by ring
      _ = Real.sqrt d ^ alpha * Kc * r ^ (2 - alpha) /
            ref * Kf * dist x y ^ alpha := by rw [hpow]; ring


/-- First moment of the transported random constant: pushing `Kc J` through the measure-preserving scale
shift and multiplying by a deterministic constant. -/
theorem aux_fscc_zeroBig_moment {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℤ) (w : SpatialCoordinates d)
    (Kc : ℕ → BilateralField d → ℝ) (Cb : ℝ)
    (hmem : ∀ N, MemLp (Kc N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure)
    (hnorm : ∀ N, eLpNorm (Kc N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal Cb)
    (c : ℝ) (hc : 0 ≤ c) (J : ℕ) :
    MemLp (fun omega => c * Kc J (aux_transport_S m w omega)) (ENNReal.ofReal 1)
        (chaosSampleLaw model).toMeasure ∧
      eLpNorm (fun omega => c * Kc J (aux_transport_S m w omega)) (ENNReal.ofReal 1)
        (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal (c * Cb) := by
  have hSmp := aux_transport_S_measurePreserving model m w
  have hf : MemLp (fun omega => Kc J (aux_transport_S m w omega)) (ENNReal.ofReal 1)
      (chaosSampleLaw model).toMeasure := (hmem J).comp_measurePreserving hSmp
  have heq : eLpNorm (fun omega => Kc J (aux_transport_S m w omega)) (ENNReal.ofReal 1)
      (chaosSampleLaw model).toMeasure =
      eLpNorm (Kc J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure := by
    simpa [Function.comp_def] using
      eLpNorm_comp_measurePreserving (p := ENNReal.ofReal 1)
        (hmem J).aestronglyMeasurable hSmp
  refine ⟨hf.const_mul c, ?_⟩
  calc eLpNorm (fun omega => c * Kc J (aux_transport_S m w omega)) (ENNReal.ofReal 1)
        (chaosSampleLaw model).toMeasure
      ≤ ‖c‖ₑ * eLpNorm (fun omega => Kc J (aux_transport_S m w omega)) (ENNReal.ofReal 1)
          (chaosSampleLaw model).toMeasure := by
        simpa [smul_eq_mul] using
          (eLpNorm_const_smul_le (c := c)
            (f := fun omega => Kc J (aux_transport_S m w omega)) (p := ENNReal.ofReal 1)
            (μ := (chaosSampleLaw model).toMeasure))
    _ ≤ ‖c‖ₑ * ENNReal.ofReal Cb := by
        rw [heq]; exact mul_le_mul_left' (hnorm J) _
    _ = ENNReal.ofReal (c * Cb) := by
        rw [Real.enorm_eq_ofReal hc, ← ENNReal.ofReal_mul hc]

/-- **Big-root transport.**  If the unit-cube Neumann Hölder bound `hUnit` holds for the top-block-removed
coefficient `A^{HT_j}_{N+j}` (one threshold `delta0` before the model and `j`; the random constant and its
first-moment bound may depend on `j`), then the zero-infrared Neumann Hölder branch holds on every triadic
root `3^j`, `j ≥ 1`, with the same threshold, for every cutoff `J ≥ 0`. -/
theorem fscc_zero_holder_neumann_big_transport
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (hUnit : ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d model)
        (Sreg : in_6_16 d model) (_It : in_iteration d model E Sreg),
        model.delta ≤ delta0 → ∀ j : ℕ, 0 < j →
        ∃ (Kcor : ℕ → BilateralField d → ℝ) (Cbcor : ℝ),
          (∀ N, MemLp (Kcor N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure) ∧
          (∀ N, eLpNorm (Kcor N) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
            ENNReal.ofReal Cbcor) ∧
          ∀ᵐ om ∂(chaosSampleLaw model).toMeasure,
            ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
              AEMeasurable F
                (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
              (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
                |F x| ≤ Kf) →
              (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
              ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
                SolvesNeumann (cutoffPositiveCoefficient model (calib3_HT d j) om (N + j)
                  (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) F v →
                ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
                  IsHolderOn alpha
                    (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)) U ∧
                  ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                    =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
                  cAlphaNorm alpha
                    (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                      Set (SpatialCoordinates d)) U ≤ Kcor N om * Kf) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d model)
        (Sreg : in_6_16 d model) (_It : in_iteration d model E Sreg),
        model.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (j : ℤ) (r : ℝ) (hr : 0 < r), r = (3 : ℝ) ^ j → 0 < j →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbank : ℝ),
        (∀ J, MemLp (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure) ∧
        (∀ J, eLpNorm (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal Cbank) ∧
        ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ J : ℕ, -j ≤ (J : ℤ) →
          aux_fscc_holder_predicates_holNeu d z r hr
            (cutoffPositiveCoefficient model
              (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega J z hr)
            alpha (K J omega) := by
  obtain ⟨delta0, hdelta0, hCor⟩ := hUnit
  refine ⟨delta0, hdelta0, ?_⟩
  intro model Rm Sreg It hdelta z j r hr hj hj0
  obtain ⟨jn, hjn⟩ : ∃ jn : ℕ, j = (jn : ℤ) := ⟨j.toNat, (Int.toNat_of_nonneg hj0.le).symm⟩
  have hjnpos : 0 < jn := by omega
  obtain ⟨Kcor, Cbcor, hmemcor, hnormcor, haecor⟩ := hCor model Rm Sreg It hdelta jn hjnpos
  set z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ) with hz0def
  set m : ℤ := -(jn : ℤ) with hmdef
  have hrm : r = (3 : ℝ) ^ (-m) := by rw [hmdef, neg_neg, hj, hjn]
  set w : SpatialCoordinates d := fun i => z i - r * z0 i with hwdef
  have hTeq : ∀ x : SpatialCoordinates d, cubeDilation z z0 r x = w + (3 : ℝ) ^ (-m) • x := by
    intro x
    funext i
    simp only [cubeDilation_apply, hwdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hrm]
    ring
  have hinjQ : ∀ x : SpatialCoordinates d, cubeDilation z0 z r⁻¹ (cubeDilation z z0 r x) = x := by
    intro x
    have hrne : r ≠ 0 := hr.ne'
    funext i
    simp only [cubeDilation_apply]
    field_simp
    ring
  have hq := lane4_dilation_quasi_measure_preserving d z z0 r hr one_pos
  -- the deterministic reference `κ_{J+j}/κ_J`
  have hκpos : ∀ N : ℕ, 0 < aux_transport_kappa model N := by
    intro N
    unfold aux_transport_kappa
    exact mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model N)
  set ref : ℕ → ℝ := fun J => aux_transport_kappa model (J + jn) / aux_transport_kappa model J
    with hrefdef
  have hrefpos : ∀ J : ℕ, 0 < ref J := fun J => div_pos (hκpos _) (hκpos _)
  have hcoeffJ : ∀ (J : ℕ) (omega : BilateralField d) (y : SpatialCoordinates d),
      cutoffCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega J (w + (3 : ℝ) ^ (-m) • y) =
        ref J * cutoffCoefficient model (calib3_HT d jn) (aux_transport_S m w omega) (J + jn) y := by
    intro J omega y
    exact aux_fscc_zeroBig_coefficient model m w (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) (calib3_HT d jn) J (J + jn) omega y
      (aux_fscc_zeroBig_potential jn hjnpos w J omega y)
  have hCoreJ : ∀ J : ℕ, ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
      aux_fscc_holder_predicates_holNeu d z r hr
        (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega J z hr) alpha
        (Real.sqrt d ^ alpha * Kcor J (aux_transport_S m w omega) * r ^ (2 - alpha) / ref J) := by
    intro J
    filter_upwards [(aux_transport_S_measurePreserving model m w).quasiMeasurePreserving.ae haecor]
      with omega hcorSraw
    have hcoeff := aux_fscc_zeroBig_coeff_ident model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) (calib3_HT d jn) m w J z0 omega
      (ref J) (hrefpos J) (J + jn) (hcoeffJ J omega)
    exact aux_fscc_zeroBig_core model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) (calib3_HT d jn) z z0 w m r hr alpha ha0 hz0def hTeq
      hinjQ (ref J) (hrefpos J) (J + jn) (Kcor J (aux_transport_S m w omega)) J omega hcoeff
      (fun F Kf hKf hF hFb hFint v hsol => hcorSraw J F Kf hKf hF hFb hFint v hsol) hq
  -- moments: `1/ref J ≤ exp (j τ²)`
  have hrefinv : ∀ J : ℕ, (ref J)⁻¹ ≤ Real.exp ((jn : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) := by
    intro J
    obtain ⟨hlo, -⟩ := aux_fscc_holNeuH_kappa_ratio_bound model m J (by omega)
    have hK : ((J : ℤ) - m).toNat = J + jn := by omega
    have hab : m.natAbs = jn := by omega
    rw [hK, hab] at hlo
    have h1 : Real.exp (-((jn : ℝ)) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) ≤ ref J := hlo
    have h2 := inv_anti₀ (Real.exp_pos _) h1
    rwa [← Real.exp_neg, neg_mul, neg_neg] at h2
  set cstar : ℝ := Real.sqrt d ^ alpha * r ^ (2 - alpha) *
    Real.exp ((jn : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) with hcstardef
  have hcJ : ∀ J : ℕ, Real.sqrt d ^ alpha * r ^ (2 - alpha) / ref J ≤ cstar := by
    intro J
    rw [hcstardef, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (hrefinv J) (by positivity)
  refine ⟨fun J omega => Real.sqrt d ^ alpha * Kcor J (aux_transport_S m w omega) *
      r ^ (2 - alpha) / ref J, cstar * |Cbcor|, ?_, ?_, ?_⟩
  · intro J
    beta_reduce
    have hfun : (fun omega => Real.sqrt d ^ alpha * Kcor J (aux_transport_S m w omega) *
        r ^ (2 - alpha) / ref J) = fun omega => (Real.sqrt d ^ alpha * r ^ (2 - alpha) / ref J) *
        Kcor J (aux_transport_S m w omega) := by
      funext omega; ring
    rw [hfun]
    exact (aux_fscc_zeroBig_moment model m w Kcor |Cbcor| hmemcor
      (fun N => (hnormcor N).trans (ENNReal.ofReal_le_ofReal (le_abs_self Cbcor)))
      _ (by have := hrefpos J; positivity) J).1
  · intro J
    beta_reduce
    have hfun : (fun omega => Real.sqrt d ^ alpha * Kcor J (aux_transport_S m w omega) *
        r ^ (2 - alpha) / ref J) = fun omega => (Real.sqrt d ^ alpha * r ^ (2 - alpha) / ref J) *
        Kcor J (aux_transport_S m w omega) := by
      funext omega; ring
    rw [hfun]
    refine (aux_fscc_zeroBig_moment model m w Kcor |Cbcor| hmemcor
      (fun N => (hnormcor N).trans (ENNReal.ofReal_le_ofReal (le_abs_self Cbcor)))
      _ (by have := hrefpos J; positivity) J).2.trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hcJ J) (abs_nonneg _))
  · rw [ae_all_iff]
    intro J
    filter_upwards [hCoreJ J] with omega hom _
    exact hom

end Paper
