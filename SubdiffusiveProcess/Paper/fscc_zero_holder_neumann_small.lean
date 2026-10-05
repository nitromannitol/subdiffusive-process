module

public import SubdiffusiveProcess.Paper.fscc_holder_predicates
public import SubdiffusiveProcess.Paper.fscc_char_holder_neumann
public import SubdiffusiveProcess.Paper.cor_neumann_source
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.lem_as_regularity_affine_transport
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.ChaosRootFieldLaw
public import SubdiffusiveProcess.Main.ScaledLayerLaw
public import SubdiffusiveProcess.Main.LayerScaling
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.CutoffPotential
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Main.InfraredAdmissible
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.EllipticRegularity.CubeDilation
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.MeanZero
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.Sobolev.ResponseComparison
public import SubdiffusiveProcess.Probability.GMCFieldLaws
public import SubdiffusiveProcess.EllipticRegularity.Bridge
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

/-!
# The mean-zero Neumann Hölder branch for the infrared-free coefficient, small roots `j ≤ 0`

Paper `mfd:lem-finite-source-comparison` (last paragraph of its proof), Neumann half, on every
triadic root cube `Q(z, 3^j)`, `j ≤ 0`, and every cutoff `J ≥ -j`, for the coefficient without its
infrared factor (`H = 0`).  The scale shift `S_{m,w}`, `m = -j ≥ 0`, transports the coefficient
*exactly* (no limit) to a constant multiple of the unit-cube coefficient with the finite infrared
truncation `H_m = ∑_{n<m}` of the shifted field, at cutoff `J - m`; the unit-cube bound is
`aux_cor_neumann_source_adm` at `H_m` (threshold independent of the truncation level), and the
reference scalar has the moments of the char pipeline (`fscc_char_holder_neumann`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology Metric ProbabilityTheory
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- **Zero-infrared potential transport** (exact, no limit), `0 ≤ m ≤ N`: the layer sum over
`j ≤ N` of the field at `w + 3^{-m}y` is the layer sum of the shifted field up to depth `N - m`, plus the
retained top layers; the retained layers at `y` are the finite infrared truncation `H_m` of the
shifted field, up to their value at `w`. -/
theorem aux_fscc_zeroNeu_potential {d : ℕ} (m : ℤ) (hm0 : 0 ≤ m) (w : SpatialCoordinates d) (N : ℕ)
    (hm : m ≤ (N : ℤ)) (om : BilateralField d) (y : SpatialCoordinates d) :
    cutoffPotential (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om N (w + (3 : ℝ) ^ (-m) • y) =
      cutoffPotential (fun om' => infraredPartialSum om' m.toNat) (aux_transport_S m w om)
        (((N : ℤ) - m).toNat) y + (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) om w + aux_transport_retained m w om := by
  set x := w + (3 : ℝ) ^ (-m) • y with hx
  have hSk : ∀ k : ℕ, (aux_transport_S m w om) (-(Int.ofNat k)) y = om (-(Int.ofNat k) - m) x := by
    intro k; exact aux_transport_S_apply m w om (-(Int.ofNat k)) y
  have hshift := aux_transport_potential_sum (fun j => om j x) N m hm
  have hret : aux_transport_ret m (fun j => om j x) = aux_transport_retained m x om := rfl
  rw [hret] at hshift
  have hpsum : ∑ k ∈ Finset.range (((N : ℤ) - m).toNat + 1), (aux_transport_S m w om)
      (-(Int.ofNat k)) y =
      ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x - aux_transport_retained m x om := by
    rw [show (∑ k ∈ Finset.range (((N : ℤ) - m).toNat + 1), (aux_transport_S m w om)
        (-(Int.ofNat k)) y) =
        ∑ k ∈ Finset.range (((N : ℤ) - m).toNat + 1), om (-(Int.ofNat k) - m) x from
      Finset.sum_congr rfl (fun k _ => hSk k)]
    linarith [hshift]
  have hL : m ≤ ((m.toNat : ℕ) : ℤ) := by omega
  have hIR := aux_transport_infraredPartialSum_S m w om m.toNat hL y
  have h0 : (((m.toNat : ℕ) : ℤ) - m).toNat = 0 := by omega
  rw [h0] at hIR
  have hzero : ∀ (om' : BilateralField d) (z : SpatialCoordinates d),
      infraredPartialSum om' 0 z = 0 := by
    intro om' z; simp [infraredPartialSum]
  rw [hzero, hzero] at hIR
  simp only [cutoffPotential, Pi.zero_apply, ContinuousMap.zero_apply]
  rw [hpsum]
  linarith [hIR]

/-- Coefficient transport (pointwise form of `aux_transport_coefficient`). -/
theorem aux_fscc_zeroNeu_coefficient {d : ℕ}
    (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℤ) (w : SpatialCoordinates d)
    (H1 H2 : BilateralField d → C(SpatialCoordinates d, ℝ))
    (N : ℕ) (hm : m ≤ (N : ℤ)) (om : BilateralField d) (y : SpatialCoordinates d)
    (hpot : cutoffPotential H1 om N (w + (3 : ℝ) ^ (-m) • y) =
      cutoffPotential H2 (aux_transport_S m w om) (((N : ℤ) - m).toNat) y +
        H1 om w + aux_transport_retained m w om) :
    cutoffCoefficient M H1 om N (w + (3 : ℝ) ^ (-m) • y) =
      aux_transport_reference M H1 N m w om *
        cutoffCoefficient M H2 (aux_transport_S m w om) (((N : ℤ) - m).toNat) y := by
  set K := ((N : ℤ) - m).toNat with hKdef
  have hNsub : (K : ℝ) = (N : ℝ) - (m : ℝ) := by
    have hnn : (0 : ℤ) ≤ (N : ℤ) - m := by omega
    have hKZ : (K : ℤ) = (N : ℤ) - m := by rw [hKdef]; exact Int.toNat_of_nonneg hnn
    exact_mod_cast hKZ
  have hposK : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M K := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M K
  have hposN : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom M N := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have hne1 : SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≠ 0 := hposN.ne'
  have hne2 : SubdiffusiveProcess.CoarseGrainingVocab.ahom M K ≠ 0 := hposK.ne'
  have hL1 : cutoffCoefficient M H1 om N (w + (3 : ℝ) ^ (-m) • y) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
      Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) =
      Real.exp (cutoffPotential H1 om N (w + (3 : ℝ) ^ (-m) • y)) := by
    unfold cutoffCoefficient
    rw [Real.exp_sub]
    field_simp
  have hR1 : cutoffCoefficient M H2 (aux_transport_S m w om) K y *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M K *
      Real.exp (((K : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) =
      Real.exp (cutoffPotential H2 (aux_transport_S m w om) K y) := by
    unfold cutoffCoefficient
    rw [Real.exp_sub]
    field_simp
  have hexppot : Real.exp (cutoffPotential H1 om N (w + (3 : ℝ) ^ (-m) • y)) =
      Real.exp (cutoffPotential H2 (aux_transport_S m w om) K y) *
        Real.exp (H1 om w + aux_transport_retained m w om) := by
    rw [hpot, ← Real.exp_add]
    congr 1
    ring
  have hcombine : cutoffCoefficient M H1 om N (w + (3 : ℝ) ^ (-m) • y) *
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
      Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) =
      (cutoffCoefficient M H2 (aux_transport_S m w om) K y *
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M K *
          Real.exp (((K : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P)) *
        Real.exp (H1 om w + aux_transport_retained m w om) := by
    rw [hL1, hR1, hexppot]
  unfold aux_transport_reference aux_transport_kappa
  have hexpN : Real.exp (((N : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) ≠ 0 :=
    (Real.exp_pos _).ne'
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hexpN hne1)]
  linear_combination hcombine


theorem aux_fscc_zeroNeu_coeff_ident {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H1 H2 : BilateralField d → C(SpatialCoordinates d, ℝ))
    (m : ℤ) (w : SpatialCoordinates d) (N : ℕ) (z0 : SpatialCoordinates d)
    (omega : BilateralField d)
    (hcoeff : ∀ y : SpatialCoordinates d,
      cutoffCoefficient model H1 omega N (w + (3 : ℝ) ^ (-m) • y) =
        aux_transport_reference model H1 N m w omega *
          cutoffCoefficient model H2 (aux_transport_S m w omega) (((N : ℤ) - m).toNat) y) :
    ∀ a1 : PositiveCoefficient (centeredCube z0 1 one_pos),
      (∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        (a1.val : SpatialCoordinates d → ℝ) x =
          cutoffCoefficient model H1 omega N (w + (3 : ℝ) ^ (-m) • x)) →
      a1 = scalePositiveCoefficient (aux_transport_reference model H1 N m w omega)
        (aux_transport_reference_pos model H1 N m w omega)
        (cutoffPositiveCoefficient model H2 (aux_transport_S m w omega) ((N : ℤ) - m).toNat
          z0 one_pos) := by
  intro a1 ha1
  have hA2 := aux_fscc_holNeuH_cutoffPos_val model H2 (aux_transport_S m w omega)
    ((N : ℤ) - m).toNat z0 one_pos
  have hval : ∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
      (a1.val : SpatialCoordinates d → ℝ) x =
        (scalePositiveCoefficient (aux_transport_reference model H1 N m w omega)
          (aux_transport_reference_pos model H1 N m w omega)
          (cutoffPositiveCoefficient model H2 (aux_transport_S m w omega) ((N : ℤ) - m).toNat
            z0 one_pos)).val x := by
    filter_upwards [ha1, hA2,
      scalePositiveCoefficient_coeFn (aux_transport_reference model H1 N m w omega)
        (aux_transport_reference_pos model H1 N m w omega)
        (cutoffPositiveCoefficient model H2 (aux_transport_S m w omega) ((N : ℤ) - m).toNat
          z0 one_pos)] with x hx1 hx2 hx3
    rw [hx1, hx3, hx2, hcoeff x]
  exact Subtype.ext (Lp.ext hval)

/-- **Core per-`(J, omega)` content of the zero-infrared Neumann transport** (`aux_fscc_holNeuH_core` with the
coefficient on the root cube built from `H1` and the transported unit-cube coefficient from `H2`), isolated into its own declaration (elaborating
the whole chain inside one big accumulated tactic block times out at 200000 heartbeats): given
the coefficient identification at this `omega` (`hcoeff`) and the pulled-back
`cor_neumann_source` Hölder fact at this `omega` (`hcorS`, at cutoff `N` for the shifted field
`S_{m,w} omega`), produce the actual `holNeu` fact on the general cube `(z, r)`, `r = 3^{-m}`,
`m ≤ J`. -/
theorem aux_fscc_zeroNeu_core {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H1 H2 : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z z0 w : SpatialCoordinates d) (m : ℤ) (r : ℝ) (hr : 0 < r) (alpha : ℝ) (halpha : 0 < alpha)
    (hz0 : z0 = fun _ : Fin d => (1 / 2 : ℝ))
    (hTeq : ∀ x : SpatialCoordinates d, cubeDilation z z0 r x = w + (3 : ℝ) ^ (-m) • x)
    (hinjQ : ∀ x : SpatialCoordinates d, cubeDilation z0 z r⁻¹ (cubeDilation z z0 r x) = x)
    (Kcor : ℕ → BilateralField d → ℝ) (J : ℕ) (omega : BilateralField d)
    (hcoeff : ∀ a1 : PositiveCoefficient (centeredCube z0 1 one_pos),
      (∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        (a1.val : SpatialCoordinates d → ℝ) x =
          cutoffCoefficient model H1 omega J (w + (3 : ℝ) ^ (-m) • x)) →
      a1 = scalePositiveCoefficient (aux_transport_reference model H1 J m w omega)
        (aux_transport_reference_pos model H1 J m w omega)
        (cutoffPositiveCoefficient model H2 (aux_transport_S m w omega) ((J : ℤ) - m).toNat
          z0 one_pos))
    (hcorS : ∀ (N : ℕ) (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf →
      AEMeasurable F (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))) →
      (∀ᵐ x ∂volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)),
        |F x| ≤ Kf) →
      (∫ x in (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ v : meanZeroSobolevGraph (centeredCube z0 1 one_pos),
        SolvesNeumann
          (cutoffPositiveCoefficient model H2 (aux_transport_S m w omega) N z0 one_pos) F v →
        ∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
          IsHolderOn alpha (closedCube z0 1 one_pos : Set (SpatialCoordinates d)) U ∧
          ((v : SobolevData (centeredCube z0 1 one_pos)).1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d))] U ∧
          cAlphaNorm alpha (closedCube z0 1 one_pos : Set (SpatialCoordinates d)) U ≤
            Kcor N (aux_transport_S m w omega) * Kf)
    (hq : Measure.QuasiMeasurePreserving (cubeDilation z z0 r)
      (volume.restrict (centeredCube z0 1 one_pos : Set (SpatialCoordinates d)))
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) :
    aux_fscc_holder_predicates_holNeu d z r hr
      (cutoffPositiveCoefficient model H1 omega J z hr) alpha
      (Real.sqrt d ^ alpha * Kcor ((J : ℤ) - m).toNat (aux_transport_S m w omega) *
        r ^ (2 - alpha) / aux_transport_reference model H1 J m w omega) := by
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
  set K : ℕ := ((J : ℤ) - m).toNat with hKdef
  set ref := aux_transport_reference model H1 J m w omega with hrefdef
  have hrefpos := aux_transport_reference_pos model H1 J m w omega
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
    hcorS K (fun x => F1 x / ref) (r ^ 2 * Kf / ref) hKfref0 hF1'meas hF1'b hF1'z v1 hsolve2
  have hsemi0 : holderSeminorm alpha
      (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos : Set (SpatialCoordinates d)) U ≤
        Kcor K (aux_transport_S m w omega) * (r ^ 2 * Kf / ref) :=
    (aux_fscc_holder_predicates_holderSeminorm_le _ _ U).trans hUcalpha
  obtain ⟨hUcO, hUholQ, hsemiQ⟩ :=
    aux_fscc_holNeuH_holder_transport z (fun _ : Fin d => (1 / 2 : ℝ)) hr halpha.le U
      hUcont.continuousOn hUhol
  set Ufinal : SpatialCoordinates d → ℝ := fun y => U (cubeDilation (fun _ : Fin d => (1 / 2 : ℝ)) z r⁻¹ y) with hUfd
  have hsemiQ' : holderSeminorm alpha
      (closedCube z r hr : Set (SpatialCoordinates d)) Ufinal ≤
      r ^ (-alpha) * (Kcor K (aux_transport_S m w omega) * (r ^ 2 * Kf / ref)) :=
    hsemiQ.trans (mul_le_mul_of_nonneg_left hsemi0 (Real.rpow_nonneg hr.le _))
  have hdiff := aux_fscc_holNeuH_holder_dist_of_seminorm
    (closedCube z r hr : Set (SpatialCoordinates d)) Ufinal alpha
    (r ^ (-alpha) * (Kcor K (aux_transport_S m w omega) * (r ^ 2 * Kf / ref)))
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
            (r ^ (-alpha) * (Kcor K (aux_transport_S m w omega) * (r ^ 2 * Kf / ref))) *
            dist x y ^ alpha := hb
      _ = Real.sqrt d ^ alpha * Kcor K (aux_transport_S m w omega) *
            (r ^ (-alpha) * r ^ 2) * Kf / ref * dist x y ^ alpha := by ring
      _ = Real.sqrt d ^ alpha * Kcor K (aux_transport_S m w omega) * r ^ (2 - alpha) /
            ref * Kf * dist x y ^ alpha := by rw [hpow]; ring


theorem aux_fscc_zeroNeu_ref_inv_moment
    (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (w : SpatialCoordinates d) (m : ℤ) (hHw : ∀ om : BilateralField d, H om w = 0) :
    ∃ Cref : ℝ, 0 ≤ Cref ∧
      ∀ J : ℕ, m ≤ (J : ℤ) →
        MemLp (fun om => (aux_transport_reference model H J m w om)⁻¹)
          (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure ∧
        eLpNorm (fun om => (aux_transport_reference model H J m w om)⁻¹)
          (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal Cref := by
  have hHmeas : Measurable (fun om : BilateralField d => H om w) := by
    have h0 : (fun om : BilateralField d => H om w) = fun _ => 0 := funext hHw
    rw [h0]; exact measurable_const
  obtain ⟨CHw, hCHw0, hHint, hHbound⟩ :
      ∃ CHw : ℝ, 0 ≤ CHw ∧
        Integrable (fun om => Real.exp (-4 * H om w)) (chaosSampleLaw model).toMeasure ∧
        (∫ om, Real.exp (-4 * H om w) ∂(chaosSampleLaw model).toMeasure) ≤ CHw := by
    refine ⟨1, zero_le_one, ?_, ?_⟩
    · simp only [hHw, mul_zero, Real.exp_zero]; exact integrable_const _
    · simp only [hHw, mul_zero, Real.exp_zero]; simp
  obtain ⟨Bret, hBret0, hRetInt, hRetBound⟩ :
      ∃ Bret : ℝ, 0 ≤ Bret ∧
        Integrable (fun om => Real.exp (-4 * aux_transport_retained m w om))
          (chaosSampleLaw model).toMeasure ∧
        (∫ om, Real.exp (-4 * aux_transport_retained m w om)
          ∂(chaosSampleLaw model).toMeasure) ≤ Bret := by
    rcases le_or_gt 0 m with hm | hm
    · exact aux_fscc_holNeuH_retained_moment_pos model m hm w
    · exact aux_fscc_holNeuH_retained_moment_neg model m hm w
  have hRetMeas := aux_fscc_holNeuH_retained_measurable (d := d) m w
  set Msup : ℝ := Real.exp (2 * (m.natAbs : ℝ) *
    _root_.SubdiffusiveProcess.Model.tauSq model.P) * ((CHw + Bret) / 2) with hMsupdef
  have hMsup0 : 0 ≤ Msup := by rw [hMsupdef]; positivity
  set Cref : ℝ := Msup ^ (1 / 2 : ℝ) with hCrefdef
  refine ⟨Cref, Real.rpow_nonneg hMsup0 _, ?_⟩
  intro J hmJ
  have hpt : ∀ om : BilateralField d,
      Real.exp (-2 * H om w) * Real.exp (-2 * aux_transport_retained m w om) ≤
        (Real.exp (-4 * H om w) + Real.exp (-4 * aux_transport_retained m w om)) / 2 := by
    intro om
    have hx2 : Real.exp (-2 * H om w) ^ 2 = Real.exp (-4 * H om w) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have hy2 : Real.exp (-2 * aux_transport_retained m w om) ^ 2 =
        Real.exp (-4 * aux_transport_retained m w om) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    nlinarith [sq_nonneg (Real.exp (-2 * H om w) - Real.exp (-2 * aux_transport_retained m w om)),
      hx2, hy2]
  have hSumInt : Integrable (fun om => Real.exp (-4 * H om w) +
      Real.exp (-4 * aux_transport_retained m w om)) (chaosSampleLaw model).toMeasure :=
    hHint.add hRetInt
  have hProdMeas : Measurable (fun om : BilateralField d =>
      Real.exp (-2 * H om w) * Real.exp (-2 * aux_transport_retained m w om)) := by
    have h1 : Measurable (fun om : BilateralField d => Real.exp (-2 * H om w)) :=
      (measurable_const.mul hHmeas).exp
    have h2 : Measurable (fun om : BilateralField d =>
        Real.exp (-2 * aux_transport_retained m w om)) :=
      (measurable_const.mul hRetMeas).exp
    exact h1.mul h2
  have hProdInt : Integrable (fun om : BilateralField d =>
      Real.exp (-2 * H om w) * Real.exp (-2 * aux_transport_retained m w om))
      (chaosSampleLaw model).toMeasure := by
    refine hSumInt.mono' hProdMeas.aestronglyMeasurable ?_
    filter_upwards [] with om
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
    have h0 : (0:ℝ) ≤ Real.exp (-4 * H om w) + Real.exp (-4 * aux_transport_retained m w om) :=
      by positivity
    linarith [hpt om]
  have hProdBound : (∫ om, Real.exp (-2 * H om w) *
      Real.exp (-2 * aux_transport_retained m w om) ∂(chaosSampleLaw model).toMeasure) ≤
      (CHw + Bret) / 2 := by
    calc (∫ om, Real.exp (-2 * H om w) * Real.exp (-2 * aux_transport_retained m w om)
        ∂(chaosSampleLaw model).toMeasure) ≤
        ∫ om, (Real.exp (-4 * H om w) + Real.exp (-4 * aux_transport_retained m w om)) / 2
          ∂(chaosSampleLaw model).toMeasure :=
        integral_mono hProdInt (hSumInt.div_const 2) hpt
      _ = (∫ om, Real.exp (-4 * H om w) + Real.exp (-4 * aux_transport_retained m w om)
          ∂(chaosSampleLaw model).toMeasure) / 2 := by
        rw [integral_div]
      _ ≤ (CHw + Bret) / 2 := by
        have := integral_add hHint hRetInt
        have hle : (∫ om, Real.exp (-4 * H om w) + Real.exp (-4 * aux_transport_retained m w om)
            ∂(chaosSampleLaw model).toMeasure) ≤ CHw + Bret := by
          rw [this]
          linarith [hHbound, hRetBound]
        linarith
  obtain ⟨hκlo, hκhi⟩ := aux_fscc_holNeuH_kappa_ratio_bound model m J hmJ
  have hκpos : 0 < aux_transport_kappa model ((J : ℤ) - m).toNat / aux_transport_kappa model J := by
    unfold aux_transport_kappa
    have h1 : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom model ((J : ℤ) - m).toNat :=
      SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model _
    have h2 : 0 < SubdiffusiveProcess.CoarseGrainingVocab.ahom model J := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos model J
    positivity
  have hinv_le : ∀ a b : ℝ, 0 < a → a ≤ b → b⁻¹ ≤ a⁻¹ := by
    intro a b ha hab
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le ha hab
  have hκlo' : Real.exp (-((m.natAbs : ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P)) ≤
      aux_transport_kappa model ((J : ℤ) - m).toNat / aux_transport_kappa model J := by
    rw [← neg_mul]; exact hκlo
  have hκinv_bound : (aux_transport_kappa model ((J : ℤ) - m).toNat /
      aux_transport_kappa model J)⁻¹ ≤ Real.exp ((m.natAbs : ℝ) *
      _root_.SubdiffusiveProcess.Model.tauSq model.P) := by
    have hstep := hinv_le _ _ (Real.exp_pos _) hκlo'
    rwa [← Real.exp_neg, neg_neg] at hstep
  set κratio : ℝ := aux_transport_kappa model ((J : ℤ) - m).toNat / aux_transport_kappa model J
    with hκratiodef
  have hrefeq : ∀ om : BilateralField d,
      aux_transport_reference model H J m w om =
        κratio * Real.exp (H om w + aux_transport_retained m w om) := fun _ => rfl
  have hrefpos : ∀ om : BilateralField d, 0 < aux_transport_reference model H J m w om := by
    intro om
    rw [hrefeq om]
    exact mul_pos hκpos (Real.exp_pos _)
  have hsqeq : ∀ om : BilateralField d,
      ((aux_transport_reference model H J m w om)⁻¹) ^ (2 : ℝ) =
        κratio⁻¹ ^ (2 : ℝ) *
          (Real.exp (-2 * H om w) * Real.exp (-2 * aux_transport_retained m w om)) := by
    intro om
    rw [hrefeq om, mul_inv, ← Real.exp_neg,
      Real.mul_rpow (by positivity) (Real.exp_pos _).le]
    congr 1
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
    congr 1
    ring
  have hrefMeas : Measurable (fun om : BilateralField d =>
      aux_transport_reference model H J m w om) := by
    have heq : (fun om : BilateralField d => aux_transport_reference model H J m w om) =
        fun om => κratio * Real.exp (H om w + aux_transport_retained m w om) := funext hrefeq
    rw [heq]
    exact measurable_const.mul
      (hHmeas.add hRetMeas).exp
  have hFm : Measurable (fun om : BilateralField d =>
      (aux_transport_reference model H J m w om)⁻¹) := hrefMeas.inv
  have hFnonneg : ∀ om : BilateralField d, 0 ≤ (aux_transport_reference model H J m w om)⁻¹ :=
    fun om => inv_nonneg.mpr (hrefpos om).le
  have hFa : Integrable (fun om : BilateralField d =>
      ((aux_transport_reference model H J m w om)⁻¹) ^ (2 : ℝ))
      (chaosSampleLaw model).toMeasure := by
    have heq : (fun om : BilateralField d => ((aux_transport_reference model H J m w om)⁻¹) ^ (2 : ℝ)) =
        fun om => κratio⁻¹ ^ (2 : ℝ) *
          (Real.exp (-2 * H om w) * Real.exp (-2 * aux_transport_retained m w om)) :=
      funext hsqeq
    rw [heq]
    exact hProdInt.const_mul _
  set M : ℝ := κratio⁻¹ ^ (2 : ℝ) * ((CHw + Bret) / 2) with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have : (0:ℝ) ≤ κratio⁻¹ ^ (2:ℝ) := Real.rpow_nonneg (inv_nonneg.mpr hκpos.le) _
    positivity
  have hMbound : (∫ om, ((aux_transport_reference model H J m w om)⁻¹) ^ (2 : ℝ)
      ∂(chaosSampleLaw model).toMeasure) ≤ M := by
    have heq : (∫ om, ((aux_transport_reference model H J m w om)⁻¹) ^ (2 : ℝ)
        ∂(chaosSampleLaw model).toMeasure) =
        κratio⁻¹ ^ (2 : ℝ) * (∫ om, Real.exp (-2 * H om w) *
          Real.exp (-2 * aux_transport_retained m w om) ∂(chaosSampleLaw model).toMeasure) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall hsqeq)
    rw [heq, hMdef]
    have hκnn : (0:ℝ) ≤ κratio⁻¹ ^ (2:ℝ) := Real.rpow_nonneg (inv_nonneg.mpr hκpos.le) _
    exact mul_le_mul_of_nonneg_left hProdBound hκnn
  have hEL := aux_fscc_holNeuH_eLpNorm_of_integral_rpow (chaosSampleLaw model).toMeasure
    (fun om => (aux_transport_reference model H J m w om)⁻¹) hFm hFnonneg 2 (by norm_num)
    hFa M hM0 hMbound
  have hMMsup : M ≤ Msup := by
    rw [hMdef, hMsupdef]
    have hκnn : (0:ℝ) ≤ κratio⁻¹ ^ (2:ℝ) := Real.rpow_nonneg (inv_nonneg.mpr hκpos.le) _
    have hκsq_le : κratio⁻¹ ^ (2:ℝ) ≤
        Real.exp (2 * (m.natAbs:ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P) := by
      have h1 : κratio⁻¹ ^ (2:ℝ) ≤ (Real.exp ((m.natAbs:ℝ) *
          _root_.SubdiffusiveProcess.Model.tauSq model.P)) ^ (2:ℝ) :=
        Real.rpow_le_rpow (inv_nonneg.mpr hκpos.le) hκinv_bound (by norm_num)
      rwa [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
        show (m.natAbs:ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P * 2 =
          2 * (m.natAbs:ℝ) * _root_.SubdiffusiveProcess.Model.tauSq model.P by ring] at h1
    exact mul_le_mul_of_nonneg_right hκsq_le (by positivity)
  have hMhalf_le : M ^ (1 / 2 : ℝ) ≤ Cref := by
    rw [hCrefdef]
    exact Real.rpow_le_rpow hM0 hMMsup (by norm_num)
  refine ⟨?_, ?_⟩
  · exact lt_of_le_of_lt (hEL.trans (ENNReal.ofReal_le_ofReal hMhalf_le)) ENNReal.ofReal_lt_top
  · exact hEL.trans (ENNReal.ofReal_le_ofReal hMhalf_le)


/-- **H1 close**, zero-infrared reference: combines the cutoff-uniform `p = 2` moment of `Kcor` (pushed through
`S_{m,w}` by measure-preservation) with the `p = 2` moment of `reference⁻¹`
(`aux_fscc_holNeuH_ref_inv_moment`) via Cauchy--Schwarz (`ENNReal.HolderTriple 2 2 1`) into the
cutoff-uniform `p = 1` moment of the product, scaled by the deterministic constants
`sqrt d ^ (1/2)` and `r ^ (3/2)`. -/
theorem aux_fscc_zeroNeu_hRefMoment
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (m : ℤ)
    (Kcor : ℕ → BilateralField d → ℝ) (Cb2 : ℝ) (hCb0 : 0 ≤ Cb2)
    (hmemK2 : ∀ N, MemLp (Kcor N) (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure)
    (hnormK2 : ∀ N, eLpNorm (Kcor N) (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal Cb2)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (w : SpatialCoordinates d) (hHw : ∀ om : BilateralField d, H om w = 0) (r : ℝ) (hr : 0 < r) (alpha : ℝ) :
    ∃ Cref : ℝ, 0 ≤ Cref ∧
      ∀ J : ℕ, m ≤ (J : ℤ) →
        MemLp (fun omega => Real.sqrt d ^ alpha *
              Kcor ((J : ℤ) - m).toNat (aux_transport_S m w omega) * r ^ (2 - alpha) /
              aux_transport_reference model H J m w omega)
            (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ∧
          eLpNorm (fun omega => Real.sqrt d ^ alpha *
              Kcor ((J : ℤ) - m).toNat (aux_transport_S m w omega) * r ^ (2 - alpha) /
              aux_transport_reference model H J m w omega)
            (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal Cref := by
  obtain ⟨CrefG, hCrefG0, hRef⟩ := aux_fscc_zeroNeu_ref_inv_moment d hd model H w m hHw
  set c : ℝ := Real.sqrt d ^ alpha * r ^ (2 - alpha) with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  refine ⟨c * (Cb2 * CrefG), by positivity, ?_⟩
  intro J hmJ
  set N : ℕ := ((J : ℤ) - m).toNat with hNdef
  have hSmp := aux_transport_S_measurePreserving model m w
  have hf2 : MemLp (fun omega => Kcor N (aux_transport_S m w omega))
      (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure :=
    (hmemK2 N).comp_measurePreserving hSmp
  have hf2norm : eLpNorm (fun omega => Kcor N (aux_transport_S m w omega))
      (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure ≤ ENNReal.ofReal Cb2 := by
    have heq : eLpNorm (fun omega => Kcor N (aux_transport_S m w omega)) (ENNReal.ofReal 2)
        (chaosSampleLaw model).toMeasure =
        eLpNorm (Kcor N) (ENNReal.ofReal 2) (chaosSampleLaw model).toMeasure := by
      simpa [Function.comp_def] using
        eLpNorm_comp_measurePreserving (p := ENNReal.ofReal 2)
          (hmemK2 N).aestronglyMeasurable hSmp
    rw [heq]
    exact hnormK2 N
  obtain ⟨hg2, hg2norm⟩ := hRef J hmJ
  have hp2 : (ENNReal.ofReal (2 : ℝ)) = (2 : ℝ≥0∞) := by norm_num
  have hp1 : (ENNReal.ofReal (1 : ℝ)) = (1 : ℝ≥0∞) := ENNReal.ofReal_one
  rw [hp2] at hf2 hf2norm hg2 hg2norm
  have hmul : MemLp (fun omega => Kcor N (aux_transport_S m w omega) *
      (aux_transport_reference model H J m w omega)⁻¹)
      (1 : ℝ≥0∞) (chaosSampleLaw model).toMeasure := by
    have hraw := MemLp.fun_mul (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (f := fun omega => (aux_transport_reference model H J m w omega)⁻¹)
      (φ := fun omega => Kcor N (aux_transport_S m w omega)) hf2 hg2
    simpa using hraw
  have hmulnorm : eLpNorm (fun omega => Kcor N (aux_transport_S m w omega) *
      (aux_transport_reference model H J m w omega)⁻¹)
      (1 : ℝ≥0∞) (chaosSampleLaw model).toMeasure ≤
      ENNReal.ofReal Cb2 * ENNReal.ofReal CrefG := by
    have hle := eLpNorm_smul_le_mul_eLpNorm (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (f := fun omega => (aux_transport_reference model H J m w omega)⁻¹)
      (φ := fun omega => Kcor N (aux_transport_S m w omega)) hf2.aestronglyMeasurable hg2.aestronglyMeasurable
    simp only [smul_eq_mul] at hle
    calc eLpNorm (fun omega => Kcor N (aux_transport_S m w omega) *
          (aux_transport_reference model H J m w omega)⁻¹) (1 : ℝ≥0∞)
          (chaosSampleLaw model).toMeasure
        ≤ eLpNorm (fun omega => Kcor N (aux_transport_S m w omega)) (2 : ℝ≥0∞)
            (chaosSampleLaw model).toMeasure *
          eLpNorm (fun omega => (aux_transport_reference model H J m w omega)⁻¹) (2 : ℝ≥0∞)
            (chaosSampleLaw model).toMeasure := hle
      _ ≤ ENNReal.ofReal Cb2 * ENNReal.ofReal CrefG := mul_le_mul' hf2norm hg2norm
  have hgoalfun : (fun omega => Real.sqrt d ^ alpha *
        Kcor N (aux_transport_S m w omega) * r ^ (2 - alpha) /
        aux_transport_reference model H J m w omega) =
      fun omega => c * (Kcor N (aux_transport_S m w omega) *
        (aux_transport_reference model H J m w omega)⁻¹) := by
    funext omega
    rw [hcdef, div_eq_mul_inv]
    ring
  rw [hgoalfun, hp1]
  refine ⟨hmul.const_mul c, ?_⟩
  calc eLpNorm (fun omega => c * (Kcor N (aux_transport_S m w omega) *
        (aux_transport_reference model H J m w omega)⁻¹)) (1 : ℝ≥0∞)
        (chaosSampleLaw model).toMeasure
      ≤ ‖c‖ₑ * eLpNorm (fun omega => Kcor N (aux_transport_S m w omega) *
          (aux_transport_reference model H J m w omega)⁻¹) (1 : ℝ≥0∞)
          (chaosSampleLaw model).toMeasure := by
        simpa [smul_eq_mul] using!
          (eLpNorm_const_smul_le (c := c)
            (f := fun omega => Kcor N (aux_transport_S m w omega) *
              (aux_transport_reference model H J m w omega)⁻¹) (p := (1 : ℝ≥0∞))
            (μ := (chaosSampleLaw model).toMeasure))
    _ ≤ ‖c‖ₑ * (ENNReal.ofReal Cb2 * ENNReal.ofReal CrefG) := mul_le_mul_right hmulnorm _
    _ = ENNReal.ofReal (c * (Cb2 * CrefG)) := by
        rw [Real.enorm_eq_ofReal hc0, ← ENNReal.ofReal_mul hCb0, ← ENNReal.ofReal_mul hc0]



/-- **The mean-zero Neumann Hölder branch for the infrared-free coefficient, cubes of side `3^j ≤ 1`
(`j ≤ 0`), every cutoff `J ≥ -j`, every exponent `α ∈ (0,1)`.**  One threshold `delta0` for the
exponent, before the model, the root and the cutoff; one random constant `K J` with first moment
bounded uniformly in `J`, serving every source and solution on one full-measure event. -/
theorem fscc_zero_holder_neumann_small
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (_Sf : SobolevFoundationalInput d hd)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d model)
        (Sreg : in_6_16 d model) (_It : in_iteration d model E Sreg),
        model.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (j : ℤ) (r : ℝ) (hr : 0 < r), r = (3 : ℝ) ^ j → j ≤ 0 →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbank : ℝ),
        (∀ J, MemLp (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure) ∧
        (∀ J, eLpNorm (K J) (ENNReal.ofReal 1) (chaosSampleLaw model).toMeasure ≤
          ENNReal.ofReal Cbank) ∧
        ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure, ∀ J : ℕ, -j ≤ (J : ℤ) →
          aux_fscc_holder_predicates_holNeu d z r hr
            (cutoffPositiveCoefficient model
              (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega J z hr)
            alpha (K J omega) := by
  have ht1 : (d : ℝ) - 1 < (d : ℝ) - 1 / 2 := by linarith
  have ht2 : (d : ℝ) - 1 / 2 < d := by linarith
  obtain ⟨delta0, hdelta0, hCor⟩ :=
    aux_cor_neumann_source_adm d hd E P X W D Cp ((d : ℝ) - 1 / 2) alpha 2 ![1, 2] ht1 ht2
      ha0 ha1 (fun i => by fin_cases i <;> norm_num)
  refine ⟨delta0, hdelta0, ?_⟩
  intro model Rm Sreg It hdelta z j r hr hj hj0
  set m : ℤ := -j with hmdef
  have hm0 : 0 ≤ m := by omega
  obtain ⟨Kcor, Cbcor, hmemcor, hnormcor, haecor⟩ :=
    hCor model Rm Sreg It (fun om => infraredPartialSum om m.toNat)
      (InfraredAdmissible.of_trunc model m.toNat) hdelta
  set z0 : SpatialCoordinates d := fun _ => (1 / 2 : ℝ) with hz0def
  have hrm : r = (3 : ℝ) ^ (-m) := by rw [hmdef, neg_neg, hj]
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
  have hq := dilation_quasi_measure_preserving d z z0 r hr one_pos
  have hCoreJ : ∀ J : ℕ, m ≤ (J : ℤ) →
      ∀ᵐ omega ∂(chaosSampleLaw model).toMeasure,
        aux_fscc_holder_predicates_holNeu d z r hr
          (cutoffPositiveCoefficient model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) omega J z hr) alpha
          (Real.sqrt d ^ alpha * Kcor ((J : ℤ) - m).toNat (aux_transport_S m w omega) *
            r ^ (2 - alpha) / aux_transport_reference model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) J m w omega) := by
    intro J hmJ
    filter_upwards [(aux_transport_S_measurePreserving model m w).quasiMeasurePreserving.ae haecor]
      with omega hcorSraw
    have hcoeff := aux_fscc_zeroNeu_coeff_ident model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) (fun om => infraredPartialSum om m.toNat)
      m w J z0 omega (fun y => aux_fscc_zeroNeu_coefficient model m w (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
        (fun om => infraredPartialSum om m.toNat) J hmJ omega y
        (aux_fscc_zeroNeu_potential m hm0 w J hmJ omega y))
    exact aux_fscc_zeroNeu_core model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) (fun om => infraredPartialSum om m.toNat) z z0 w m r hr
      alpha ha0 hz0def hTeq hinjQ Kcor J omega hcoeff
      (fun N F Kf hKf hF hFb hFint v hsol => (hcorSraw N F Kf hKf hF hFb hFint v hsol).1) hq
  obtain ⟨Cref, hCref0, hRef⟩ := aux_fscc_zeroNeu_hRefMoment hd model m Kcor |Cbcor 1|
    (abs_nonneg _) (fun N => hmemcor 1 N)
    (fun N => (hnormcor 1 N).trans (ENNReal.ofReal_le_ofReal (le_abs_self _))) 0 w (fun _ => rfl) r hr alpha
  refine ⟨fun J omega => if m ≤ (J : ℤ) then
      Real.sqrt d ^ alpha * Kcor ((J : ℤ) - m).toNat (aux_transport_S m w omega) *
        r ^ (2 - alpha) / aux_transport_reference model (0 : BilateralField d → C(SpatialCoordinates d, ℝ)) J m w omega
    else 0, Cref, ?_, ?_, ?_⟩
  · intro J
    by_cases hmJ : m ≤ (J : ℤ)
    · simp only [ite_eq_left hmJ]; exact (hRef J hmJ).1
    · simp only [ite_eq_right hmJ]; exact memLp_const 0
  · intro J
    by_cases hmJ : m ≤ (J : ℤ)
    · simp only [ite_eq_left hmJ]; exact (hRef J hmJ).2
    · simp only [ite_eq_right hmJ]
      rw [show (fun _ : BilateralField d => (0 : ℝ)) = 0 from rfl, eLpNorm_zero]
      exact bot_le
  · rw [ae_all_iff]
    intro J
    by_cases hmJ : m ≤ (J : ℤ)
    · filter_upwards [hCoreJ J hmJ] with omega hom _
      simpa only [ite_eq_left hmJ] using hom
    · exact Filter.Eventually.of_forall (fun _ hcon => absurd hcon hmJ)

end SubdiffusiveProcess.Paper
