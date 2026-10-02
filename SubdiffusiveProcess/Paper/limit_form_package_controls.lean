import SubdiffusiveProcess.Lane2.LimitForm
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.DirichletForm.All
import SubdiffusiveProcess.Lane4.Carriers
import SubdiffusiveProcess.Sobolev.ReflectionResponses
import Mathlib.Tactic
import SubdiffusiveProcess.Paper.limit_form_package_side
import SubdiffusiveProcess.Paper.killed_inverse_mosco
import SubdiffusiveProcess.Paper.lem_weighted_cluster
import SubdiffusiveProcess.Paper.prop_killed_inverse

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal NNReal Topology ContDiff BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

/-- A countable diagonal extraction of actual quadratic responses supplies an
operator-norm cluster for a collectively compact symmetric positive sequence. -/
theorem aux_limit_form_package_operator_cluster
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [Module ℚ V]
    (T : ℕ → V →L[ℝ] V) (D : Submodule ℚ V)
    (hDcount : (D : Set V).Countable) (hDense : Dense (D : Set V))
    (hSym : ∀ n x y, inner ℝ (T n x) y = inner ℝ x (T n y))
    (hPos : ∀ n x, 0 ≤ inner ℝ x (T n x))
    (hCompact : IsCompact (closure (⋃ n : ℕ, (T n) '' Metric.closedBall (0 : V) 1))) :
    ∃ (sigma : ℕ → ℕ) (G : V →L[ℝ] V), StrictMono sigma ∧
      Tendsto (fun n => T (sigma n)) atTop (𝓝 G) ∧ IsCompactOperator G ∧
      (∀ x y, inner ℝ (G x) y = inner ℝ x (G y)) ∧
      (∀ x, 0 ≤ inner ℝ x (G x)) := by
  classical
  letI : Countable D := Set.countable_coe_iff.mpr hDcount
  obtain ⟨C, hC, hBound⟩ := exists_operatorNorm_bound_of_collectively_compact hCompact
  let q : ℕ → D → ℝ := fun n f => inner ℝ f.val (T n f.val)
  have hqbound (n : ℕ) (f : D) : q n f ∈ Icc (0 : ℝ) (C * ‖f.val‖ ^ 2) := by
    refine ⟨hPos n f.val, ?_⟩
    calc
      q n f ≤ |inner ℝ f.val (T n f.val)| := le_abs_self _
      _ ≤ ‖f.val‖ * ‖T n f.val‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖f.val‖ * (C * ‖f.val‖) :=
        mul_le_mul_of_nonneg_left
          ((T n).le_opNorm f.val |>.trans
            (mul_le_mul_of_nonneg_right (hBound n) (norm_nonneg _))) (norm_nonneg _)
      _ = C * ‖f.val‖ ^ 2 := by ring
  have hProd : IsCompact {p : D → ℝ | ∀ f, p f ∈ Icc (0 : ℝ) (C * ‖f.val‖ ^ 2)} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  obtain ⟨qlim, _hqlim, sigma, hsigma, hq⟩ := hProd.tendsto_subseq hqbound
  have hqCauchy : ∀ f ∈ (D : Set V),
      CauchySeq (fun n => inner ℝ f (T (sigma n) f)) := by
    intro f hf
    exact (((continuous_apply (⟨f, hf⟩ : D)).tendsto qlim).comp hq).cauchySeq
  have hsub : closure (⋃ n : ℕ, (T (sigma n)) '' Metric.closedBall (0 : V) 1) ⊆
      closure (⋃ n : ℕ, (T n) '' Metric.closedBall (0 : V) 1) := by
    apply closure_mono
    intro y hy
    obtain ⟨n, hn⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨sigma n, hn⟩
  obtain ⟨G, hG, _hUnique⟩ := existsUnique_limit_of_collectively_compact_quadratic_responses
    hDense (fun x hx y hy => D.add_mem hx hy)
    (fun n => hSym (sigma n)) (fun n => hPos (sigma n))
    (hCompact.of_isClosed_subset isClosed_closure hsub) hqCauchy
  exact ⟨sigma, G, hsigma, hG⟩

/-- Coercivity and the dense source catalogue produce an actual operator cluster;
no convergence or Cauchy premise is imposed on the new weighted responses. -/
theorem aux_limit_form_package_response_cluster
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (hInterp : CubeFractionalInterpolationInput d hd)
    (K : ℝ) (hK : 0 < K)
    (hCoercive : ∀ n (v : S.space),
      cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
        (fun _ : Fin 1 => v.val.1) < ⊤ ∧
      ‖v.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
        ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
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
  obtain ⟨sigma, G, hsigma, hG⟩ := aux_limit_form_package_operator_cluster GN D hDcount hDense
    hSym hPos hCompact
  exact ⟨GN, sigma, G, hGN, hsigma, hG⟩

/-- The concrete compactness, cutoff and mesh data stable under bounded positive
changes of the coefficient. These are extracted from the represented bounds. -/
structure aux_limit_form_package_analytic_controls
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr)) where
  K : ℝ
  K_pos : 0 < K
  coercive : ∀ n (v : S.space),
    cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
      (fun _ : Fin 1 => v.val.1) < ⊤ ∧
    ‖v.val.1‖ ^ 2 + volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
      ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
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

/-- Actual represented bounds supply the analytic package without strengthening
its exponent or adding a regularity premise. -/
theorem aux_limit_form_package_controls_of_bounds
    {d : ℕ} (hd : 2 ≤ d)


    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (hBounds : in_represented_bounds_seq d hd z r hr S a G) :
    Nonempty (aux_limit_form_package_analytic_controls d hd z r hr S
      (fun n => a n)) := by
  obtain ⟨K, hK, hCoerc, D, hDcount, hDense, hSmooth, hInterp⟩ :=
    limit_form_package_regularity_supply hd z r hr S G a hBounds
  have hmesh := aux_limit_form_package_endpoint_invariance_hmesh_of_bounds_side hd z r hr
    S G a hBounds
  obtain ⟨_KN, _hKN, _Kstar, _hKstar, _hfrac, _hcoer, _hInterp, t, ht, htd,
    hCutoffs, _⟩ := hBounds
  exact ⟨{
    K := K, K_pos := hK, coercive := hCoerc, interpolation := hInterp
    sources := D, sources_countable := hDcount, sources_dense := hDense
    sources_smooth := hSmooth
    mesh := hmesh
    t := t, t_lower := ht, t_upper := htd, cutoffs := hCutoffs }⟩

/-- Positive two-sided coefficient comparison transports every analytic
control, including its source-independent cutoff growth and finite meshes. -/
noncomputable def aux_limit_form_package_analytic_controls_reindex_weight
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a)
    (b : ℕ → PositiveCoefficient (centeredCube z r hr)) (iota : ℕ → ℕ)
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hLower : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      lo * (a (iota n)).val x ≤ (b n).val x)
    (hUpper : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      (b n).val x ≤ hi * (a (iota n)).val x) :
    aux_limit_form_package_analytic_controls d hd z r hr S b where
  K := A.K / lo
  K_pos := div_pos A.K_pos hlo
  coercive := by
    intro n v
    refine ⟨(A.coercive (iota n) v).1, ?_⟩
    exact aux_lem_weighted_cluster_weighted_coercive S (a (iota n)) (b n) lo A.K
      hlo A.K_pos.le (fun u => ‖u‖ ^ 2 +
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) *
          ((cubeFractionalL2Seminorm hd z r hr Lane4.threeQuarterOrder
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

/-- Data supplied by the actual norm limit of a coefficient sequence. -/
structure aux_limit_form_package_form_cluster
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
  form : _root_.DirichletForm (volume.restrict (Q : Set (SpatialCoordinates d)))
  energy_eq : ∀ u, form.energy u = limitFormEnergy operator u
  lower : ∀ (uN : ℕ → S.space) (u : DomainL2 Q),
    (∀ f, Tendsto (fun n => inner ℝ f (uN n).val.1) atTop (𝓝 (inner ℝ f u))) →
    limitFormEnergy operator u ≤
      liminf (fun n => (responseForm S (a (sigma n)) (uN n) (uN n) : EReal)) atTop
  recovery : ∀ u ∈ limitFormDomain operator, ∃ w : ℕ → S.space,
    Tendsto (fun n => ((w n).val.1,
      (responseForm S (a (sigma n)) (w n) (w n) : EReal))) atTop
      (𝓝 (u, limitFormEnergy operator u))

/-- Compactness, meshes and the approved contraction rule construct a genuine
Dirichlet cluster with the weak lower bound and recovery sequences. -/
theorem aux_limit_form_package_form_cluster_exists
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a)
    (hcontract : ∀ n (T : ℝ → ℝ), DirichletForm.IsNormalContraction T →
      ∀ u : S.space, ∃ v : S.space,
        ((v.val.1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
            (fun x => T (u.val.1 x))) ∧ responseForm S (a n) v v ≤ responseForm S (a n) u u) :
    Nonempty (aux_limit_form_package_form_cluster (centeredCube z r hr) S a) := by
  obtain ⟨GN, sigma, G, hGN, hsigma, hConv, _hComp, hSym, hPos⟩ :=
    aux_limit_form_package_response_cluster d hd z r hr S a A.interpolation A.K A.K_pos A.coercive
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
    (fun f => aux_limit_form_package_response_cauchy _ G hConv f.val) EN (fun _ _ => rfl) hmesh
  have hG := aux_limit_form_package_property_of_limit (fun n => GN (sigma n)) G hConv _
    (fun _ h => h.1.1) hResult
  obtain ⟨E, hE, _hNC⟩ := hG.2.2.1
  exact ⟨{
    operatorN := GN, operatorN_eq := hGN, sigma := sigma, sigma_strict := hsigma
    operator := G, operator_tendsto := hConv, symmetric := hSym, positive := hPos
    form := E, energy_eq := hE
    lower := aux_prop_killed_inverse_moscoS S (fun n => a (sigma n)) G EN
      (fun _ _ => rfl) hG.2.2.2.1.1
    recovery := hG.2.2.2.1.2 }⟩

/-- The three variational facts needed for local coefficient comparison. -/
structure aux_limit_form_package_mosco_data
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

/-- The established killed-inverse theorem applies to each weighted norm limit. -/
theorem limit_form_package_controls
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G)) :
    aux_limit_form_package_mosco_data (centeredCube z r hr) S a G := by
  let EN : ℕ → DomainL2 (centeredCube z r hr) → EReal := fun n u =>
    sInf {e : EReal | ∃ w : S.space, w.val.1 = u ∧ e = (responseForm S (a n) w w : EReal)}
  have hResult := killed_inverse_mosco d hd z r hr S hS a GN hGN A.interpolation
    A.K A.K_pos A.coercive A.sources A.sources_countable A.sources_dense A.sources_smooth
    (fun f => aux_limit_form_package_response_cauchy GN G hConv f.val) EN (fun _ _ => rfl)
  have hG := aux_limit_form_package_property_of_limit GN G hConv _ (fun _ h => h.1.1) hResult
  exact ⟨hG.1.2.2.1, aux_prop_killed_inverse_moscoS S a G EN (fun _ _ => rfl) hG.2.1,
    hG.2.2⟩

/-- Reindexing preserves all controls before any compactness extraction. -/
noncomputable def aux_limit_form_package_controls_reindex
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a) (sigma : ℕ → ℕ) :
    aux_limit_form_package_analytic_controls d hd z r hr S (fun n => a (sigma n)) :=
  aux_limit_form_package_analytic_controls_reindex_weight A _ sigma 1 1 zero_lt_one zero_le_one
    (fun _ => Eventually.of_forall fun _ => by rw [one_mul])
    (fun _ => Eventually.of_forall fun _ => by rw [one_mul])

/-- Local recovery passes a coefficient inequality only where the core
representative is supported. Both coefficients may be weighted. -/
theorem aux_limit_form_package_controlled_local_form_le
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a b : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a)
    {G F : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : aux_limit_form_package_mosco_data (centeredCube z r hr) S a G)
    (hB : aux_limit_form_package_mosco_data (centeredCube z r hr) S b F)
    (E EF : DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hF : ∀ u, EF.energy u = limitFormEnergy F u)
    (q : Set (SpatialCoordinates d)) (hq : IsOpen q)
    (hqQ : q ⊆ (centeredCube z r hr : Set (SpatialCoordinates d))) (K : ℝ)
    (hCoeff : ∀ n, ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
      x ∈ q → (b n).val x ≤ K * (a n).val x) :
    ∀ u, E.MemCoreOn q u → u ∈ EF.domain ∧ EF.form u u ≤ K * E.form u u := by
  intro u hu
  have huG : u ∈ limitFormDomain G :=
    (aux_limit_form_package_domain_eq_of_energy E G hE) ▸ hu.mem_domain
  obtain ⟨_huE, uc, huc, hucs, hucq, huae⟩ := hu
  obtain ⟨Y, hY, hYgrad⟩ := aux_limit_form_package_localized_recovery_base d hd z r hr S hS a G
    hA.lower hA.recovery (fun _ => A.K) (fun _ => A.K_pos.le) A.K (fun _ => le_rfl)
    (fun w => (A.coercive 0 w).1) (fun n w => (A.coercive n w).2)
    A.interpolation A.t A.t_lower A.t_upper A.cutoffs q hq hqQ u huG uc huc hucs hucq huae
  rw [aux_limit_form_package_energy_coe G u huG] at hY
  have hle := aux_limit_form_package_energy_order_of_recovery S a b F hB.lower u
    (limitFormEnergy G u).toReal K Y hY (Eventually.of_forall fun n =>
      aux_limit_form_package_responseForm_le_local S (a n) (b n) K q (Y n) (hCoeff n) (hYgrad n))
  have huF : u ∈ EF.domain := EF.mem_domain_of_energy_lt_top (by
    rw [hF]
    exact hle.trans_lt (EReal.coe_lt_top _))
  refine ⟨huF, ?_⟩
  rw [← hF, EF.energy_of_mem huF,
    ← aux_limit_form_package_form_eq_toReal_energy E G hE u _huE] at hle
  exact EReal.coe_le_coe_iff.mp hle

/-- The actual cutoff argument proves the cube-relative core locality of a
controlled limit, which is the antecedent consumed by approved BD/BDQ. -/
theorem aux_limit_form_package_controlled_core_locality
    {d : ℕ} {hd : 2 ≤ d} {z : SpatialCoordinates d} {r : ℝ} {hr : 0 < r}
    {S : ResponseSpace (centeredCube z r hr)}
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    {a : ℕ → PositiveCoefficient (centeredCube z r hr)}
    (A : aux_limit_form_package_analytic_controls d hd z r hr S a)
    {G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr)}
    (hA : aux_limit_form_package_mosco_data (centeredCube z r hr) S a G)
    (E : DirichletForm.ClosedForm
      (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u) :
    ∀ u v : DomainL2 (centeredCube z r hr),
      E.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) u →
      E.MemCoreOn (centeredCube z r hr : Set (SpatialCoordinates d)) v →
      ∀ uc vc : SpatialCoordinates d → ℝ,
        (u : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] uc →
        (v : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] vc →
        Continuous uc → Continuous vc → HasCompactSupport uc → HasCompactSupport vc →
        tsupport uc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        tsupport vc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
        ∀ (c : ℝ) (W : Set (SpatialCoordinates d)), IsOpen W → tsupport vc ⊆ W →
          (∀ x ∈ W, uc x = c) → E.form u v = 0 := by
  have hSym : ∀ f g, inner ℝ f (G g) = inner ℝ g (G f) := by
    intro f g
    rw [← hA.symmetric, real_inner_comm]
  exact aux_lem_weighted_cluster_strongly_local d hd z r hr S hS a G hSym
    hA.lower hA.recovery (fun _ => A.K) (fun _ => A.K_pos.le) A.K (fun _ => le_rfl)
    (fun w => (A.coercive 0 w).1) (fun n w => (A.coercive n w).2)
    A.interpolation A.t A.t_lower A.t_upper A.cutoffs E hE

end Paper
