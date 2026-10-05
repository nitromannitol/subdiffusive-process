module

public import Mathlib.Tactic
public import SubdiffusiveProcess.Compactness.OperatorNormCluster
public import SubdiffusiveProcess.Compactness.SequentialCompactness
public import SubdiffusiveProcess.DirichletForm.FOTProduct
public import SubdiffusiveProcess.VariationalResponses.LimitForm
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import SubdiffusiveProcess.Sobolev.CompactResponses
public import SubdiffusiveProcess.Paper.killed_inverse_mosco
public import SubdiffusiveProcess.Paper.lem_weighted_cluster
public import SubdiffusiveProcess.Paper.prop_killed_inverse

@[expose] public section

/-! Deterministic prop conc controlled forms data extracted upstream of process convergence.
This module does not assert concentration or invoke the process-convergence theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators ContDiff
namespace SubdiffusiveProcess.Paper
noncomputable section

/-- Extracted response cluster argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_forms_response_cluster
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (hInterp : CubeFractionalInterpolationInput d hd)
    (K : ℝ) (hK : 0 < K)
    (hCoercive : ∀ n (v : S.space),
      cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => v.val.1) < ⊤ ∧
      ‖v.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
          (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤ K * responseForm S (a n) v v)
    (D : Submodule ℚ (DomainL2 (centeredCube z r hr)))
    (hDcount : (D : Set (DomainL2 (centeredCube z r hr))).Countable)
    (hDense : Dense (D : Set (DomainL2 (centeredCube z r hr)))) :
    ∃ (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
      (sigma : ℕ → ℕ)
      (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)),
      (∀ n f, GN n f =
        (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1) ∧
      StrictMono sigma ∧ Tendsto (fun n => GN (sigma n)) atTop (𝓝 G) ∧
      IsCompactOperator G ∧
      (∀ x y, inner ℝ (G x) y = inner ℝ x (G y)) ∧
      (∀ x, 0 ≤ inner ℝ x (G x)) := by
  choose GN hGN using fun n => (existsUnique_volumeResponseOperator S (a n)).exists
  have hCompact := aux_killed_inverse_mosco_compact d hd z r hr S a GN hGN
    hInterp K hK hCoercive
  have hSym : ∀ n x y, inner ℝ (GN n x) y = inner ℝ x (GN n y) := by
    intro n x y
    rw [hGN, hGN, real_inner_comm]
    exact volumeResponse_pairing_symm S (a n) y x
  have hPos : ∀ n x, 0 ≤ inner ℝ x (GN n x) := by
    intro n x
    rw [hGN]
    exact volumeResponse_pairing_nonneg S (a n) x
  obtain ⟨sigma, G, hsigma, hG⟩ := SubdiffusiveProcess.OperatorCompactness.exists_norm_cluster_of_collectively_compact GN D hDcount hDense
    hSym hPos hCompact
  exact ⟨GN, sigma, G, hGN, hsigma, hG⟩

/-- Extracted analytic controls argument from the pre-convergence deterministic proof. -/
structure aux_prop_conc_controlled_forms_analytic_controls
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr)) where
  K : ℝ
  K_pos : 0 < K
  coercive : ∀ n (v : S.space),
    cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
      (fun _ : Fin 1 => v.val.1) < ⊤ ∧
    ‖v.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
      ((cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
        (fun _ : Fin 1 => v.val.1)).toReal) ^ 2 ≤ K * responseForm S (a n) v v
  interpolation : CubeFractionalInterpolationInput d hd
  sources : Submodule ℚ (DomainL2 (centeredCube z r hr))
  sources_countable : (sources : Set (DomainL2 (centeredCube z r hr))).Countable
  sources_dense : Dense (sources : Set (DomainL2 (centeredCube z r hr)))
  sources_smooth : ∀ f : sources,
    ∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
      tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (f.val : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc
  mesh : ∀ phi : DomainL2 (centeredCube z r hr),
    (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
      tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (phi : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
    ∀ eps : ℝ, 0 < eps → ∃ w : ℕ → S.space, ∃ C : ℝ,
      (∀ n, responseForm S (a n) (w n) (w n) ≤ C) ∧
      (∀ n, ‖(w n).val.1 - phi‖ ≤ eps)
  t : ℝ
  t_lower : (d : ℝ) - 1 < t
  t_upper : t < (d : ℝ)
  cutoffs : ∀ (K O : Set (SpatialCoordinates d)),
      IsCompact K → IsOpen O → K ⊆ O → closure O ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∃ (V : Set (SpatialCoordinates d)) (chi : ℕ → S.space)
        (chic : ℕ → SpatialCoordinates d → ℝ) (B : ℝ),
        IsOpen V ∧ K ⊆ V ∧ V ⊆ O ∧ 0 ≤ B ∧ ∀ n,
          ContinuousOn (chic n) (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ((chi n).val.1 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] chic n ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), 0 ≤ chic n x ∧ chic n x ≤ 1) ∧
          (∀ x ∈ V, chic n x = 1) ∧
          (∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), x ∉ O → chic n x = 0) ∧
          responseForm S (a n) (chi n) (chi n) ≤ B ∧
          (∀ x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)), ∀ rr : ℝ, 0 < rr → rr ≤ 1 →
            ((volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))).withDensity
              (fun y => ENNReal.ofReal ((a n).val y * ∑ i : Fin d, ((chi n).val.2 i y) ^ 2)))
              (Metric.ball x rr) ≤ ENNReal.ofReal (B * rr ^ t))

/-- Extracted analytic controls reindex weight argument from the pre-convergence deterministic proof. -/
noncomputable def aux_prop_conc_controlled_forms_analytic_controls_reindex_weight
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (b : ℕ → PositiveCoefficient (centeredCube z r hr)) (iota : ℕ → ℕ)
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hLower : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      lo * (a (iota n)).val x ≤ (b n).val x)
    (hUpper : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (b n).val x ≤ hi * (a (iota n)).val x) :
    _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S b where
  K := A.K / lo
  K_pos := div_pos A.K_pos hlo
  coercive := by
    intro n v
    refine ⟨(A.coercive (iota n) v).1, ?_⟩
    exact aux_lem_weighted_cluster_weighted_coercive S (a (iota n)) (b n) lo A.K
      hlo A.K_pos.le (fun u => ‖u‖ ^ 2 +
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
          ((cubeFractionalL2Seminorm hd z r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder
            (fun _ : Fin 1 => u)).toReal) ^ 2) v
      (A.coercive (iota n) v).2
      (weightedGradientForm_mul_le _ _ hlo (hLower n) (subspaceGradient S.space v))
  interpolation := A.interpolation
  sources := A.sources
  sources_countable := A.sources_countable
  sources_dense := A.sources_dense
  sources_smooth := A.sources_smooth
  mesh := by
    intro phi hphi eps heps
    obtain ⟨w, C, hEnergy, hClose⟩ := A.mesh phi hphi eps heps
    refine ⟨fun n => w (iota n), hi * C, ?_, fun n => hClose (iota n)⟩
    intro n
    exact (aux_lem_weighted_cluster_responseForm_le_mul S (b n) (a (iota n)) hi
      (hUpper n) (w (iota n))).trans
        (mul_le_mul_of_nonneg_left (hEnergy (iota n)) hhi)
  t := A.t
  t_lower := A.t_lower
  t_upper := A.t_upper
  cutoffs := aux_lem_weighted_cluster_weighted_cutoffs z r hr A.t S a b iota hi hhi
    hUpper A.cutoffs

/-- Extracted form cluster argument from the pre-convergence deterministic proof. -/
structure aux_prop_conc_controlled_forms_form_cluster
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q) where
  operatorN : ℕ → DomainL2 Q →L[ℝ] DomainL2 Q
  operatorN_eq : ∀ n f, operatorN n f =
    (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1
  sigma : ℕ → ℕ
  sigma_strict : StrictMono sigma
  operator : DomainL2 Q →L[ℝ] DomainL2 Q
  operator_tendsto : Tendsto (fun n => operatorN (sigma n)) atTop (𝓝 operator)
  symmetric : ∀ x y, inner ℝ (operator x) y = inner ℝ x (operator y)
  positive : ∀ x, 0 ≤ inner ℝ x (operator x)
  form : _root_.SubdiffusiveProcess.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d)))
  energy_eq : ∀ u, form.energy u = limitFormEnergy operator u
  lower : ∀ (uN : ℕ → S.space) (u : DomainL2 Q),
    (∀ f, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
    limitFormEnergy operator u ≤
      liminf (fun n => (responseForm S (a (sigma n)) (uN n) (uN n) : EReal)) atTop
  recovery : ∀ u ∈ limitFormDomain operator, ∃ w : ℕ → S.space,
    Tendsto (fun n => ((w n).val.1,
      (responseForm S (a (sigma n)) (w n) (w n) : EReal))) atTop
      (𝓝 (u, limitFormEnergy operator u))

/-- Extracted form cluster exists argument from the pre-convergence deterministic proof. -/
theorem aux_prop_conc_controlled_forms_form_cluster_exists
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (hcontract : ∀ n (T : ℝ → ℝ), _root_.SubdiffusiveProcess.DirichletForm.IsNormalContraction T →
      ∀ u : S.space, ∃ v : S.space,
        ((v.val.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
            (fun x => T (u.val.1 x))) ∧ responseForm S (a n) v v ≤ responseForm S (a n) u u) :
    Nonempty (_root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_form_cluster (centeredCube z r hr) S a) := by
  obtain ⟨GN, sigma, G, hGN, hsigma, hConv, _hComp, hSym, hPos⟩ :=
    _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_response_cluster d hd z r hr S a A.interpolation A.K A.K_pos A.coercive
      A.sources A.sources_countable A.sources_dense
  let EN : ℕ → DomainL2 (centeredCube z r hr) → EReal := fun n u =>
    sInf {e : EReal | ∃ w : S.space, w.val.1 = u ∧
      e = (responseForm S (a (sigma n)) w w : EReal)}
  have hmesh : ∀ phi : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (phi : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∀ eps : ℝ, 0 < eps → ∃ w : ℕ → S.space, ∃ C : ℝ,
        (∀ n, responseForm S (a (sigma n)) (w n) (w n) ≤ C) ∧
        (∀ n, ‖(w n).val.1 - phi‖ ≤ eps) := by
    intro phi hphi eps heps
    obtain ⟨w, C, hE, hClose⟩ := A.mesh phi hphi eps heps
    exact ⟨fun n => w (sigma n), C, fun n => hE (sigma n), fun n => hClose (sigma n)⟩
  have hResult := prop_killed_inverse d hd z r hr S hS (fun n => a (sigma n))
    (fun n => hcontract (sigma n)) (fun n => GN (sigma n)) (fun n => hGN (sigma n))
    A.interpolation A.K A.K_pos (fun n => A.coercive (sigma n))
    A.sources A.sources_countable A.sources_dense A.sources_smooth
    (fun f => SubdiffusiveProcess.OperatorCompactness.quadratic_response_cauchy_of_tendsto _ G hConv f.val) EN (fun _ _ => rfl) hmesh
  have hG := SubdiffusiveProcess.OperatorCompactness.property_of_unique_limit (fun n => GN (sigma n)) G hConv _
    (fun _ h => h.1.1) hResult
  obtain ⟨E, hE, _hNC⟩ := hG.2.2.1
  exact ⟨{
    operatorN := GN, operatorN_eq := hGN, sigma := sigma, sigma_strict := hsigma
    operator := G, operator_tendsto := hConv, symmetric := hSym, positive := hPos
    form := E, energy_eq := hE
    lower := aux_prop_killed_inverse_moscoS S (fun n => a (sigma n)) G EN
      (fun _ _ => rfl) hG.2.2.2.1.1
    recovery := hG.2.2.2.1.2 }⟩

/-- Extracted mosco data argument from the pre-convergence deterministic proof. -/
structure aux_prop_conc_controlled_forms_mosco_data
    {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (S : ResponseSpace Q) (a : ℕ → PositiveCoefficient Q)
    (G : DomainL2 Q →L[ℝ] DomainL2 Q) : Prop where
  symmetric : ∀ x y, inner ℝ (G x) y = inner ℝ x (G y)
  lower : ∀ (wN : ℕ → S.space) (w : DomainL2 Q),
    (∀ f, Tendsto (fun n => inner ℝ f (wN n).val.1) atTop (𝓝 (inner ℝ f w))) →
    limitFormEnergy G w ≤
      liminf (fun n => (responseForm S (a n) (wN n) (wN n) : EReal)) atTop
  recovery : ∀ u ∈ limitFormDomain G, ∃ w : ℕ → S.space,
    Tendsto (fun n => ((w n).val.1,
      (responseForm S (a n) (w n) (w n) : EReal))) atTop
      (𝓝 (u, limitFormEnergy G u))

/-- Extracted controlled mosco argument from the pre-convergence deterministic proof. -/
theorem prop_conc_controlled_forms
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G)) :
    _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_mosco_data (centeredCube z r hr) S a G := by
  let EN : ℕ → DomainL2 (centeredCube z r hr) → EReal := fun n u =>
    sInf {e : EReal | ∃ w : S.space, w.val.1 = u ∧ e = (responseForm S (a n) w w : EReal)}
  have hResult := killed_inverse_mosco d hd z r hr S hS a GN hGN A.interpolation
    A.K A.K_pos A.coercive A.sources A.sources_countable A.sources_dense A.sources_smooth
    (fun f => SubdiffusiveProcess.OperatorCompactness.quadratic_response_cauchy_of_tendsto GN G hConv f.val) EN (fun _ _ => rfl)
  have hG := SubdiffusiveProcess.OperatorCompactness.property_of_unique_limit GN G hConv _ (fun _ h => h.1.1) hResult
  exact ⟨hG.1.2.2.1, aux_prop_killed_inverse_moscoS S a G EN (fun _ _ => rfl) hG.2.1,
    hG.2.2⟩

/-- Extracted controls reindex argument from the pre-convergence deterministic proof. -/
noncomputable def aux_prop_conc_controlled_forms_controls_reindex
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a) (sigma : ℕ → ℕ) :
    _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S (fun n => a (sigma n)) :=
  _root_.SubdiffusiveProcess.Paper.aux_prop_conc_controlled_forms_analytic_controls_reindex_weight A _ sigma 1 1 zero_lt_one zero_le_one
    (fun _ => Eventually.of_forall fun _ => by rw [one_mul])
    (fun _ => Eventually.of_forall fun _ => by rw [one_mul])

end
end SubdiffusiveProcess.Paper
