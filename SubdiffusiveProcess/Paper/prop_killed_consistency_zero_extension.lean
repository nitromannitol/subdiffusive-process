module

public import SubdiffusiveProcess.Paper.prop_killed_inverse
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.lem_19
public import SubdiffusiveProcess.Paper.conv_represented_sequence
public import SubdiffusiveProcess.Paper.prop_locality_recovery
public import SubdiffusiveProcess.Paper.catalog_cutoff_existence
public import SubdiffusiveProcess.Paper.conv_catalog_cutoffs
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.VariationalResponses.BoundaryPackaging
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.VariationalResponses.NativeBridge
public import SubdiffusiveProcess.VariationalResponses.ResponseMarkov
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.VariationalResponses.MeshError
public import SubdiffusiveProcess.VariationalResponses.ExternalInputs
public import SubdiffusiveProcess.Main.MeasureTrace
public import SubdiffusiveProcess.DirichletForm.All
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import SubdiffusiveProcess.Sobolev.EvenReflectionGraph

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Fine proof step for `mfd:prop-killed-consistency`, paper label `mfd:prop-killed-consistency`.

Inputs:
- The two native killed graphs, coefficient sequences, and coefficient
  identification are the concrete small/large-cube data of the parent.
- The small-cube recovery clause is supplied by `prop_killed_inverse`.
- Fractional coercivity, trace/interpolation, represented-sequence bounds,
  and the catalog cutoff convention are supplied by the cited predecessor
  nodes; no limiting energy equality is assumed.
- CONCLUDED HERE: zero-extension of the recovery sequence, its finite
  energy identity, convergence to the zero extension, and the large-cube
  lower-bound inequality.
 -/
theorem aux_prop_killed_consistency_zero_extension_restrict
    {d : ℕ} {V U : Opens (SpatialCoordinates d)} (hV : V ≤ U)
    (v : SobolevData V) :
    sobolevDataRestrict hV (zeroExtensionSobolevData hV v) = v := by
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [domainLpRestrict_coeFn hV (zeroExtensionLp hV v.1),
      ae_restrict_of_ae_restrict_of_subset hV (zeroExtensionLp_coeFn hV v.1),
      ae_restrict_mem V.isOpen.measurableSet] with x h1 h2 hx
    change (domainLpRestrict hV (zeroExtensionLp hV v.1) :
      SpatialCoordinates d → ℝ) x = v.1 x
    rw [h1, h2, Set.indicator_of_mem hx]
  · funext i
    apply Lp.ext
    filter_upwards [domainLpRestrict_coeFn hV (zeroExtensionLp hV (v.2 i)),
      ae_restrict_of_ae_restrict_of_subset hV
        (zeroExtensionLp_coeFn hV (v.2 i)),
      ae_restrict_mem V.isOpen.measurableSet] with x h1 h2 hx
    change (domainLpRestrict hV (zeroExtensionLp hV (v.2 i)) :
      SpatialCoordinates d → ℝ) x = (v.2 i) x
    rw [h1, h2, Set.indicator_of_mem hx]

theorem aux_prop_killed_consistency_zero_extension_response
    {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (S : ResponseSpace Ω)
    (a : PositiveCoefficient Ω) (x y : S.space) :
    responseForm S a x y = sobolevCoefficientForm a x.val y.val := by
  rw [responseForm_apply, sobolevCoefficientForm_apply]

theorem prop_killed_consistency_zero_extension
    (d : ℕ) (_hd : 2 ≤ d)
    (zQ zq : SpatialCoordinates d) (R r : ℝ) (hR0 : 0 < R) (hr0 : 0 < r)
    (hqQ : (centeredCube zq r hr0 : Set (SpatialCoordinates d)) ⊆
      (centeredCube zQ R hR0 : Set (SpatialCoordinates d)))
    (SQ : ResponseSpace (centeredCube zQ R hR0))
    (Sq : ResponseSpace (centeredCube zq r hr0))
    (hSQ : SQ.space = killedSobolevGraph (centeredCube zQ R hR0))
    (hSq : Sq.space = killedSobolevGraph (centeredCube zq r hr0))
    (aQ : ℕ → PositiveCoefficient (centeredCube zQ R hR0))
    (aq : ℕ → PositiveCoefficient (centeredCube zq r hr0))
    (hcoeff : ∀ n, ((aQ n).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))]
        ((aq n).val : SpatialCoordinates d → ℝ))
    (EQ : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube zQ R hR0 : Set (SpatialCoordinates d))))
    (Eq : _root_.SubdiffusiveProcess.DirichletForm.ClosedForm
      (volume.restrict (centeredCube zq r hr0 : Set (SpatialCoordinates d))))
    (hQlower : ∀ (vN : ℕ → SQ.space) (v : DomainL2 (centeredCube zQ R hR0)),
      (∀ f : DomainL2 (centeredCube zQ R hR0),
        Tendsto (fun n => inner ℝ f (vN n).val.1) atTop
          (𝓝 (inner ℝ f v))) →
      (EQ.energy v : EReal) ≤
        liminf (fun n => (responseForm SQ (aQ n) (vN n) (vN n) : EReal)) atTop)
    (hqrecovery : ∀ v ∈ Eq.domain, ∃ vN : ℕ → Sq.space,
      Tendsto (fun n => ((vN n).val.1,
        (responseForm Sq (aq n) (vN n) (vN n) : EReal))) atTop
        (𝓝 (v, (Eq.energy v : EReal))))
    (u : DomainL2 (centeredCube zq r hr0)) (hu : u ∈ Eq.domain) :
    ∃ uNQ : ℕ → SQ.space,
      (∀ n, (uNQ n).val.1 = zeroExtensionLp hqQ ((Classical.choose (hqrecovery u hu) n).val.1)) ∧
      (∀ n, responseForm SQ (aQ n) (uNQ n) (uNQ n) =
        responseForm Sq (aq n) (Classical.choose (hqrecovery u hu) n)
          (Classical.choose (hqrecovery u hu) n)) ∧
      Tendsto (fun n => ((uNQ n).val.1,
        (responseForm SQ (aQ n) (uNQ n) (uNQ n) : EReal))) atTop
        (𝓝 (zeroExtensionLp hqQ u, (Eq.energy u : EReal))) ∧
      (EQ.energy (zeroExtensionLp hqQ u) : EReal) ≤ (Eq.energy u : EReal) := by
  have hmemQ : ∀ n : ℕ,
      zeroExtensionSobolevData hqQ ((Classical.choose (hqrecovery u hu) n).val)
        ∈ SQ.space := by
    intro n
    rw [hSQ]
    apply lane2_zeroExtensionSobolevData_mem_killed hqQ
    rw [← hSq]
    exact (Classical.choose (hqrecovery u hu) n).property
  let uNQ : ℕ → SQ.space := fun n =>
    ⟨zeroExtensionSobolevData hqQ ((Classical.choose (hqrecovery u hu) n).val),
      hmemQ n⟩
  have henergy : ∀ n : ℕ,
      responseForm SQ (aQ n) (uNQ n) (uNQ n) =
        responseForm Sq (aq n) (Classical.choose (hqrecovery u hu) n)
          (Classical.choose (hqrecovery u hu) n) := by
    intro n
    calc
      responseForm SQ (aQ n) (uNQ n) (uNQ n) =
          sobolevCoefficientForm (aQ n) (uNQ n).val (uNQ n).val :=
        aux_prop_killed_consistency_zero_extension_response SQ (aQ n)
          (uNQ n) (uNQ n)
      _ = sobolevCoefficientForm (aQ n)
          (zeroExtensionSobolevData hqQ
            ((Classical.choose (hqrecovery u hu) n).val))
          (zeroExtensionSobolevData hqQ
            ((Classical.choose (hqrecovery u hu) n).val)) := by
        rfl
      _ = sobolevCoefficientForm (aq n)
          (Classical.choose (hqrecovery u hu) n).val
          (Classical.choose (hqrecovery u hu) n).val := by
        have hrestrict :=
          aux_prop_killed_consistency_zero_extension_restrict hqQ
            ((Classical.choose (hqrecovery u hu) n).val)
        exact (sobolevCoefficientForm_zeroExtension hqQ (aQ n) (aq n)
          (hcoeff n) _ _).trans
          (congrArg (fun w => sobolevCoefficientForm (aq n)
            (Classical.choose (hqrecovery u hu) n).val w) hrestrict)
      _ = responseForm Sq (aq n) (Classical.choose (hqrecovery u hu) n)
          (Classical.choose (hqrecovery u hu) n) := by
        exact (aux_prop_killed_consistency_zero_extension_response Sq (aq n)
          (Classical.choose (hqrecovery u hu) n)
          (Classical.choose (hqrecovery u hu) n)).symm
  have hrec := Classical.choose_spec (hqrecovery u hu)
  have hrec' : Tendsto
      (fun n => ((Classical.choose (hqrecovery u hu) n).val.1,
        (responseForm Sq (aq n) (Classical.choose (hqrecovery u hu) n)
          (Classical.choose (hqrecovery u hu) n) : EReal))) atTop
      (𝓝 u ×ˢ 𝓝 (Eq.energy u : EReal)) := by
    simpa only [nhds_prod_eq] using hrec
  have hfirst : Tendsto
      (fun n => ((Classical.choose (hqrecovery u hu) n).val.1)) atTop
      (𝓝 u) := hrec'.fst
  have hzero : Tendsto
      (fun n => zeroExtensionLp hqQ
        ((Classical.choose (hqrecovery u hu) n).val.1)) atTop
      (𝓝 (zeroExtensionLp hqQ u)) :=
    (lane2_continuous_zeroExtensionLp hqQ).tendsto u |>.comp hfirst
  have hzeroN : Tendsto (fun n => (uNQ n).val.1) atTop
      (𝓝 (zeroExtensionLp hqQ u)) := by
    simpa only [uNQ, zeroExtensionSobolevData] using hzero
  have henergyT : Tendsto
      (fun n => (responseForm Sq (aq n)
        (Classical.choose (hqrecovery u hu) n)
        (Classical.choose (hqrecovery u hu) n) : EReal)) atTop
      (𝓝 (Eq.energy u : EReal)) := hrec'.snd
  have henergyQ : Tendsto
      (fun n => (responseForm SQ (aQ n) (uNQ n) (uNQ n) : EReal)) atTop
      (𝓝 (Eq.energy u : EReal)) := by
    apply henergyT.congr'
    filter_upwards [Filter.Eventually.of_forall henergy] with n hn
    exact congrArg (fun x : ℝ => (x : EReal)) hn.symm
  have hpair : Tendsto
      (fun n => ((uNQ n).val.1,
        (responseForm SQ (aQ n) (uNQ n) (uNQ n) : EReal))) atTop
      (𝓝 (zeroExtensionLp hqQ u, (Eq.energy u : EReal))) := by
    simpa only [nhds_prod_eq] using hzeroN.prodMk henergyQ
  have hweak : ∀ f : DomainL2 (centeredCube zQ R hR0),
      Tendsto (fun n => inner ℝ f (uNQ n).val.1) atTop
        (𝓝 (inner ℝ f (zeroExtensionLp hqQ u))) := by
    intro f
    simpa only [Function.comp_apply, id_eq] using!
      ((continuous_const.inner continuous_id).tendsto
        (zeroExtensionLp hqQ u)).comp hzeroN
  have hlow := hQlower uNQ (zeroExtensionLp hqQ u) hweak
  have hfinal : (EQ.energy (zeroExtensionLp hqQ u) : EReal) ≤
      (Eq.energy u : EReal) := by
    calc
      (EQ.energy (zeroExtensionLp hqQ u) : EReal) ≤
          liminf (fun n =>
            (responseForm SQ (aQ n) (uNQ n) (uNQ n) : EReal)) atTop := hlow
      _ = (Eq.energy u : EReal) := henergyQ.liminf_eq
  exact ⟨uNQ, (by
    intro n
    rfl), henergy, hpair, hfinal⟩

end SubdiffusiveProcess.Paper
