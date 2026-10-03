module

public import SubdiffusiveProcess.Paper.primitive_scores_finite
public import SubdiffusiveProcess.Paper.prop_response_compact
public import SubdiffusiveProcess.Sobolev.CompactPotential
public import SubdiffusiveProcess.Sobolev.DiagonalDefect
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.Lane2.CellDirichlet
public import SubdiffusiveProcess.Geometry.CoordinateFold
public import SubdiffusiveProcess.Sobolev.AffineUpperBounds
public import SubdiffusiveProcess.Sobolev.PotentialResponses
public import SubdiffusiveProcess.Probability.ResponseContinuity
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import SubdiffusiveProcess.Probability.LayerProductBlocks
public import SubdiffusiveProcess.Probability.CopyLayerBlock
public import SubdiffusiveProcess.Lane3.BandFiltration
public import SubdiffusiveProcess.Paper.lem_as_coarse_shallow_grid_descendant_rechart
public import SubdiffusiveProcess.Lane4.ResponseJBridge
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualJMoment
public import SubdiffusiveProcess.Paper.Foundations.PrefixActualJMeas
public import SubdiffusiveProcess.Paper.Foundations.PrefixFieldTransport
public import SubdiffusiveProcess.Paper.lem_15
public import SubdiffusiveProcess.Paper.lem_neumann_15
public import SubdiffusiveProcess.Paper.prop_growth_energy_assembly
public import SubdiffusiveProcess.Paper.prop_growth_macro_energy
public import SubdiffusiveProcess.Paper.finite_negative_layer_log_lipschitz_majorant
public import SubdiffusiveProcess.Paper.rem_resolved
public import SubdiffusiveProcess.Paper.lane4_reference_mesh_statistic
public import SubdiffusiveProcess.Probability.InfraredCharacterizationExistence
public import SubdiffusiveProcess.Probability.InfraredCharacterizationCompactExponentialMoment
public import SubdiffusiveProcess.Paper.lem_as_regularity_affine_transport
public import SubdiffusiveProcess.Paper.lane4_dilation_quasi_measure_preserving
public import SubdiffusiveProcess.Paper.lem_coercivity
public import SubdiffusiveProcess.Paper.rem_bank
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import SubdiffusiveProcess.Probability.GMCFieldLaws

@[expose] public section




set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

section PaeDefs

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

variable {d : ℕ}

/-- The literal zero-infrared response atom read by the raw prefix scores: the matched
response supremum `J_{l+N}` at the rescaled point `3^N y`, set to `0` below the cutoff. -/
def aux_lem_prefix_limit_atom_extraction_atom
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (N : ℕ) (l : ℤ) (y : Vec d) (omega : BilateralField d) : ℝ :=
  if 0 ≤ l + (N : ℤ) then
    (aux_psf_Jval M (l + (N : ℤ)).toNat (eta N omega) ((3 : ℝ) ^ N • y)).toReal
  else 0

/-- The affine map `x ↦ y + 3^l x`. -/
def aux_lem_prefix_limit_atom_extraction_affine (l : ℤ) (y : SpatialCoordinates d) :
    C(SpatialCoordinates d, SpatialCoordinates d) :=
  ⟨fun x => y + (3 : ℝ) ^ l • x, (by fun_prop)⟩

/-- The scale-and-translation relabelling of the bilateral field: coordinate `c` of the image
is the layer `c + l` read at `y + 3^l x`. -/
def aux_lem_prefix_limit_atom_extraction_shift (l : ℤ) (y : SpatialCoordinates d)
    (omega : BilateralField d) : BilateralField d :=
  fun c => (omega (c + l)).comp (aux_lem_prefix_limit_atom_extraction_affine l y)

/-- The deterministic normalization `κ_N = e^{(N+1)τ²} ahom_N`. -/
def aux_lem_prefix_limit_atom_extraction_kappa (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) : ℝ :=
  Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * ahom M N

/-- The unit observation cube `Q₀ = centeredCube 0 1`. -/
abbrev aux_lem_prefix_limit_atom_extraction_Q0 (d : ℕ) : Opens (SpatialCoordinates d) :=
  centeredCube (0 : SpatialCoordinates d) 1 one_pos

/-- The unit-cube zero-infrared potential `Σ_{j ≤ N} ω_{-j} - log κ_N`, as a bounded potential
on `Q₀`. -/
def aux_lem_prefix_limit_atom_extraction_pot (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (omega : BilateralField d) :
    Lp ℝ ∞ (volume.restrict
      ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))) :=
  compactPotentialLp (closedCube (0 : SpatialCoordinates d) 1 one_pos)
    ((∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ))).restrict
        (closedCube (0 : SpatialCoordinates d) 1 one_pos) -
      ContinuousMap.const _ (Real.log (aux_lem_prefix_limit_atom_extraction_kappa M N)))

/-- Killed and mean-zero Poincaré on the unit cube. -/
theorem aux_lem_prefix_limit_atom_extraction_poincare [NeZero d] :
    (∃ K : ℝ≥0, ∀ u : killedSobolevGraph (aux_lem_prefix_limit_atom_extraction_Q0 d),
      ‖(u : SobolevData (aux_lem_prefix_limit_atom_extraction_Q0 d)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (aux_lem_prefix_limit_atom_extraction_Q0 d)) u‖) ∧
    (∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (aux_lem_prefix_limit_atom_extraction_Q0 d),
      ‖(u : SobolevData (aux_lem_prefix_limit_atom_extraction_Q0 d)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (aux_lem_prefix_limit_atom_extraction_Q0 d)) u‖) :=
  exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain _
    (lane2_isOpenBoundedConvexDomain_centeredCube (0 : SpatialCoordinates d) one_pos)

/-- The affine Dirichlet response on `Q₀` of the coefficient `a` at slope `e`. -/
def aux_lem_prefix_limit_atom_extraction_D [NeZero d]
    (a : PositiveCoefficient (aux_lem_prefix_limit_atom_extraction_Q0 d)) (e : Fin d → ℝ) : ℝ :=
  affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
    aux_lem_prefix_limit_atom_extraction_poincare.1 a e

/-- The affine inverse-Neumann response on `Q₀` of the coefficient `a` at slope `e`. -/
def aux_lem_prefix_limit_atom_extraction_N [NeZero d]
    (a : PositiveCoefficient (aux_lem_prefix_limit_atom_extraction_Q0 d)) (e : Fin d → ℝ) : ℝ :=
  affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincare.2 a e

/-- `J_e + |e|² = (D_e + N_e)/(2|Q₀|)` for the coefficient `a`. -/
def aux_lem_prefix_limit_atom_extraction_W [NeZero d]
    (a : PositiveCoefficient (aux_lem_prefix_limit_atom_extraction_Q0 d)) (e : Fin d → ℝ) : ℝ :=
  (aux_lem_prefix_limit_atom_extraction_D a e + aux_lem_prefix_limit_atom_extraction_N a e) /
    (2 * volume.real ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)))

/-- The response evaluation `sup_{|e|=1} (D_e + N_e)/(2|Q₀|)` at the coefficient `e^g`. -/
def aux_lem_prefix_limit_atom_extraction_eval [NeZero d]
    (g : Lp ℝ ∞ (volume.restrict
      ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)))) : ℝ :=
  ⨆ e : {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1},
    aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g) (e : Fin d → ℝ)

/-- The unit-cube zero-infrared response `J_sup + 1` at cutoff `N`. -/
def aux_lem_prefix_limit_atom_extraction_Rf [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (omega : BilateralField d) : ℝ :=
  aux_lem_prefix_limit_atom_extraction_eval (aux_lem_prefix_limit_atom_extraction_pot M N omega)

end PaeDefs

section PaeEval

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

variable {d : ℕ}

/-- Two-sided pointwise bounds of the exponential coefficient of a bounded potential. -/
theorem aux_lem_prefix_limit_atom_extraction_exp_bounds {Ω : Opens (SpatialCoordinates d)}
    (g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d)))) :
    (∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      Real.exp (-‖g‖) ≤ (expPotentialCoefficient g).val x) ∧
    (∀ᵐ x ∂volume.restrict (Ω : Set (SpatialCoordinates d)),
      (expPotentialCoefficient g).val x ≤ Real.exp ‖g‖) := by
  constructor
  · filter_upwards [expPotentialCoefficient_coeFn g, boundedPotential_ae_bound g] with x he hx
    rw [he]
    exact Real.exp_le_exp.mpr (by linarith [neg_abs_le (g x)])
  · filter_upwards [expPotentialCoefficient_coeFn g, boundedPotential_ae_bound g] with x he hx
    rw [he]
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) hx)

variable [NeZero d]

omit [NeZero d] in
theorem aux_lem_prefix_limit_atom_extraction_vol_pos :
    0 < volume.real ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)) :=
  centeredCube_volume_pos (0 : SpatialCoordinates d) one_pos

theorem aux_lem_prefix_limit_atom_extraction_D_nonneg
    (a : PositiveCoefficient (aux_lem_prefix_limit_atom_extraction_Q0 d)) (e : Fin d → ℝ) :
    0 ≤ aux_lem_prefix_limit_atom_extraction_D a e :=
  dirichletResponse_nonneg _ _ _

theorem aux_lem_prefix_limit_atom_extraction_N_nonneg
    (a : PositiveCoefficient (aux_lem_prefix_limit_atom_extraction_Q0 d)) (e : Fin d → ℝ) :
    0 ≤ aux_lem_prefix_limit_atom_extraction_N a e :=
  inverseResponse_nonneg _ _ _

theorem aux_lem_prefix_limit_atom_extraction_W_nonneg
    (a : PositiveCoefficient (aux_lem_prefix_limit_atom_extraction_Q0 d)) (e : Fin d → ℝ) :
    0 ≤ aux_lem_prefix_limit_atom_extraction_W a e :=
  div_nonneg (add_nonneg (aux_lem_prefix_limit_atom_extraction_D_nonneg a e)
    (aux_lem_prefix_limit_atom_extraction_N_nonneg a e))
    (mul_nonneg zero_le_two aux_lem_prefix_limit_atom_extraction_vol_pos.le)

/-- `W_e ≤ |e|² e^{‖g‖}` for the coefficient `e^g`. -/
theorem aux_lem_prefix_limit_atom_extraction_W_le
    (g : Lp ℝ ∞ (volume.restrict
      ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)))) (e : Fin d → ℝ) :
    aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g) e ≤
      (∑ i : Fin d, (e i) ^ 2) * Real.exp ‖g‖ := by
  obtain ⟨hlo, hhi⟩ := aux_lem_prefix_limit_atom_extraction_exp_bounds g
  set V := volume.real ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)) with hV
  have hVpos : 0 < V := aux_lem_prefix_limit_atom_extraction_vol_pos
  have hD : aux_lem_prefix_limit_atom_extraction_D (expPotentialCoefficient g) e ≤
      (∑ i : Fin d, (e i) ^ 2) * (V * Real.exp ‖g‖) :=
    affineDirichletResponse_le_upper_bound _ _ _ _ hhi
  have hN : aux_lem_prefix_limit_atom_extraction_N (expPotentialCoefficient g) e ≤
      (∑ i : Fin d, (e i) ^ 2) * (V * (Real.exp (-‖g‖))⁻¹) :=
    affineInverseNeumannResponse_le_lower_bound _ _ _ (Real.exp_pos _) hlo
  rw [Real.exp_neg, inv_inv] at hN
  unfold aux_lem_prefix_limit_atom_extraction_W
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hD, hN]

/-- `W_e` of `e^g` is at most `e^{‖g-h‖}` times `W_e` of `e^h`. -/
theorem aux_lem_prefix_limit_atom_extraction_W_cmp
    (g h : Lp ℝ ∞ (volume.restrict
      ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)))) (e : Fin d → ℝ) :
    aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g) e ≤
      Real.exp ‖g - h‖ * aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient h) e := by
  have hn : ‖h - g‖ = ‖g - h‖ := norm_sub_rev h g
  have hD : aux_lem_prefix_limit_atom_extraction_D (expPotentialCoefficient g) e ≤
      Real.exp ‖g - h‖ * aux_lem_prefix_limit_atom_extraction_D (expPotentialCoefficient h) e := by
    unfold aux_lem_prefix_limit_atom_extraction_D affineDirichletResponse
    rw [← hn]
    exact (dirichletResponse_potential_comparison _ _ h g).2
  have hN : aux_lem_prefix_limit_atom_extraction_N (expPotentialCoefficient g) e ≤
      Real.exp ‖g - h‖ * aux_lem_prefix_limit_atom_extraction_N (expPotentialCoefficient h) e := by
    unfold aux_lem_prefix_limit_atom_extraction_N affineInverseNeumannResponse
    rw [← hn]
    exact (inverseResponse_potential_comparison _ _ h g).2
  unfold aux_lem_prefix_limit_atom_extraction_W
  rw [mul_div_assoc']
  apply div_le_div_of_nonneg_right _ (mul_nonneg zero_le_two
    aux_lem_prefix_limit_atom_extraction_vol_pos.le)
  rw [mul_add]
  exact add_le_add hD hN

/-- The unit sphere of slopes is nonempty. -/
instance aux_lem_prefix_limit_atom_extraction_sphere_nonempty :
    Nonempty {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1} :=
  ⟨⟨Pi.single 0 1, by
    rw [Finset.sum_eq_single (0 : Fin d)]
    · simp
    · intro b _ hb
      simp [hb]
    · simp⟩⟩

theorem aux_lem_prefix_limit_atom_extraction_bdd
    (g : Lp ℝ ∞ (volume.restrict
      ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)))) :
    BddAbove (Set.range fun e : {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1} =>
      aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g) (e : Fin d → ℝ)) := by
  refine ⟨Real.exp ‖g‖, ?_⟩
  rintro _ ⟨e, rfl⟩
  have h := aux_lem_prefix_limit_atom_extraction_W_le g (e : Fin d → ℝ)
  rwa [e.2, one_mul] at h

theorem aux_lem_prefix_limit_atom_extraction_W_le_eval
    (g : Lp ℝ ∞ (volume.restrict
      ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))))
    (e : {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1}) :
    aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g) (e : Fin d → ℝ) ≤
      aux_lem_prefix_limit_atom_extraction_eval g :=
  le_ciSup (aux_lem_prefix_limit_atom_extraction_bdd g) e

theorem aux_lem_prefix_limit_atom_extraction_eval_nonneg
    (g : Lp ℝ ∞ (volume.restrict
      ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)))) :
    0 ≤ aux_lem_prefix_limit_atom_extraction_eval g := by
  obtain ⟨e⟩ := (inferInstance : Nonempty {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1})
  exact (aux_lem_prefix_limit_atom_extraction_W_nonneg _ _).trans
    (aux_lem_prefix_limit_atom_extraction_W_le_eval g e)

theorem aux_lem_prefix_limit_atom_extraction_eval_le
    (g : Lp ℝ ∞ (volume.restrict
      ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)))) :
    aux_lem_prefix_limit_atom_extraction_eval g ≤ Real.exp ‖g‖ :=
  ciSup_le fun e => by
    have h := aux_lem_prefix_limit_atom_extraction_W_le g (e : Fin d → ℝ)
    rwa [e.2, one_mul] at h

/-- The multiplicative comparison `eq:mfd-mult` for the response evaluation. -/
theorem aux_lem_prefix_limit_atom_extraction_eval_cmp
    (g h : Lp ℝ ∞ (volume.restrict
      ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)))) :
    aux_lem_prefix_limit_atom_extraction_eval g ≤
      Real.exp ‖g - h‖ * aux_lem_prefix_limit_atom_extraction_eval h :=
  ciSup_le fun e => (aux_lem_prefix_limit_atom_extraction_W_cmp g h (e : Fin d → ℝ)).trans
    (mul_le_mul_of_nonneg_left (aux_lem_prefix_limit_atom_extraction_W_le_eval h e)
      (Real.exp_pos _).le)

theorem aux_lem_prefix_limit_atom_extraction_eval_continuous :
    Continuous (aux_lem_prefix_limit_atom_extraction_eval (d := d)) := by
  have he := equicontinuous_of_exp_comparison
    (f := fun _ : Unit => aux_lem_prefix_limit_atom_extraction_eval (d := d))
    (C := 1) (by norm_num)
    (fun _ g => aux_lem_prefix_limit_atom_extraction_eval_nonneg g) (fun _ g h => ?_)
    (fun g => ⟨aux_lem_prefix_limit_atom_extraction_eval g, fun _ => le_rfl⟩)
  · exact he.continuous ()
  · rw [one_mul, dist_eq_norm]
    exact aux_lem_prefix_limit_atom_extraction_eval_cmp g h

theorem aux_lem_prefix_limit_atom_extraction_real_perturb (x E Y : ℝ) (hx : 0 ≤ x)
    (hY : 0 ≤ Y) (hup : E ≤ Real.exp x * Y) (hlo : Y ≤ Real.exp x * E) :
    |E - Y| ≤ 2 * x * Real.exp (4 * x) * Y := by
  have h1 : Real.exp x - 1 ≤ x * Real.exp x := by
    have := Real.add_one_le_exp (-x)
    have hex : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos x]
  have h2 : x * Real.exp x ≤ 2 * x * Real.exp (4 * x) := by
    have : Real.exp x ≤ Real.exp (4 * x) := Real.exp_le_exp.mpr (by linarith)
    nlinarith [Real.exp_pos x]
  have hEnn : 0 ≤ E := by
    by_contra hE
    push_neg at hE
    have : Real.exp x * E < 0 := mul_neg_of_pos_of_neg (Real.exp_pos x) hE
    linarith
  have hlo' : Real.exp (-x) * Y ≤ E := by
    have hex : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    calc Real.exp (-x) * Y ≤ Real.exp (-x) * (Real.exp x * E) :=
          mul_le_mul_of_nonneg_left hlo (Real.exp_pos _).le
      _ = E := by rw [← mul_assoc, hex, one_mul]
  have h3 : 1 - Real.exp (-x) ≤ x := by linarith [Real.add_one_le_exp (-x)]
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right h3 hY, mul_le_mul_of_nonneg_right h2 hY,
      mul_le_mul_of_nonneg_right h1 hY, mul_nonneg hx (Real.exp_pos x).le]
  · nlinarith [mul_le_mul_of_nonneg_right h1 hY, mul_le_mul_of_nonneg_right h2 hY]

/-- The trivial-mass response of the unit-cube evaluation: every `Response` field follows from
the multiplicative comparison. -/
def aux_lem_prefix_limit_atom_extraction_response :
    Response (aux_lem_prefix_limit_atom_extraction_Q0 d) where
  eval := aux_lem_prefix_limit_atom_extraction_eval
  mass g _ := aux_lem_prefix_limit_atom_extraction_eval g
  eval_nonneg := aux_lem_prefix_limit_atom_extraction_eval_nonneg
  mass_nonneg g _ := aux_lem_prefix_limit_atom_extraction_eval_nonneg g
  mass_mono _ _ _ _ _ _ := le_rfl
  mass_univ _ := rfl
  exp_comparison := aux_lem_prefix_limit_atom_extraction_eval_cmp
  response_perturbation h g _ _ _ := by
    apply aux_lem_prefix_limit_atom_extraction_real_perturb ‖g‖ _ _ (norm_nonneg g)
      (aux_lem_prefix_limit_atom_extraction_eval_nonneg h)
    · have := aux_lem_prefix_limit_atom_extraction_eval_cmp (h + g) h
      rwa [add_sub_cancel_left] at this
    · have := aux_lem_prefix_limit_atom_extraction_eval_cmp h (h + g)
      rwa [sub_add_cancel_left, norm_neg] at this
  mass_perturbation h g _ _ _ := by
    have hc := aux_lem_prefix_limit_atom_extraction_eval_cmp (h + g) h
    rw [add_sub_cancel_left] at hc
    have hn := aux_lem_prefix_limit_atom_extraction_eval_nonneg h
    have h1 : 1 ≤ 2 * (1 + ‖g‖ ^ 2 * Real.exp (4 * ‖g‖)) := by
      nlinarith [sq_nonneg ‖g‖, Real.exp_pos (4 * ‖g‖), mul_nonneg (sq_nonneg ‖g‖)
        (Real.exp_pos (4 * ‖g‖)).le]
    calc aux_lem_prefix_limit_atom_extraction_eval (h + g)
        ≤ Real.exp ‖g‖ * aux_lem_prefix_limit_atom_extraction_eval h := hc
      _ ≤ 2 * Real.exp ‖g‖ * (1 + ‖g‖ ^ 2 * Real.exp (4 * ‖g‖)) *
            aux_lem_prefix_limit_atom_extraction_eval h := by
          have hE := Real.exp_pos ‖g‖
          nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hE.le hn)]

/-- The restriction-and-embedding `C(K₀, ℝ) → L∞(Q₀)` is `1`-Lipschitz. -/
theorem aux_lem_prefix_limit_atom_extraction_cp_lipschitz :
    LipschitzWith 1 (compactPotentialLp
      (Ω := aux_lem_prefix_limit_atom_extraction_Q0 d)
      (closedCube (0 : SpatialCoordinates d) 1 one_pos)) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have hsub : compactPotentialLp (Ω := aux_lem_prefix_limit_atom_extraction_Q0 d)
      (closedCube (0 : SpatialCoordinates d) 1 one_pos) (f - g) =
      compactPotentialLp (closedCube (0 : SpatialCoordinates d) 1 one_pos) f -
        compactPotentialLp (closedCube (0 : SpatialCoordinates d) 1 one_pos) g := by
    have hfg : f - g = f + (-1 : ℝ) • g := by rw [neg_one_smul, sub_eq_add_neg]
    rw [hfg, compactPotentialLp_add, compactPotentialLp_smul, neg_one_smul, ← sub_eq_add_neg]
  rw [← hsub]
  exact compactPotentialLp_norm_le _ _

/-- The unit-cube potential depends continuously on the bilateral field (product topology). -/
theorem aux_lem_prefix_limit_atom_extraction_pot_continuous
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Continuous (aux_lem_prefix_limit_atom_extraction_pot M N) := by
  unfold aux_lem_prefix_limit_atom_extraction_pot
  refine aux_lem_prefix_limit_atom_extraction_cp_lipschitz.continuous.comp ?_
  refine Continuous.sub ?_ continuous_const
  refine (ContinuousMap.continuous_restrict _).comp ?_
  exact continuous_finset_sum _ fun j _ => continuous_apply _

theorem aux_lem_prefix_limit_atom_extraction_Rf_continuous
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Continuous (aux_lem_prefix_limit_atom_extraction_Rf M N) :=
  aux_lem_prefix_limit_atom_extraction_eval_continuous.comp
    (aux_lem_prefix_limit_atom_extraction_pot_continuous M N)

theorem aux_lem_prefix_limit_atom_extraction_Rf_measurable
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Measurable (aux_lem_prefix_limit_atom_extraction_Rf M N) :=
  (aux_lem_prefix_limit_atom_extraction_Rf_continuous M N).measurable

end PaeEval

section PaeQuadGen

open scoped BigOperators

variable {d : ℕ}

/-! ## Generic finite-dimensional part -/

/-- The basis vector `ε_i`. -/
abbrev aux_lem_prefix_limit_atom_extraction_eps (i : Fin d) : Fin d → ℝ := Pi.single i 1

theorem aux_lem_prefix_limit_atom_extraction_decomp (e : Fin d → ℝ) :
    e = ∑ i : Fin d, e i • aux_lem_prefix_limit_atom_extraction_eps i := by
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

/-- A bilinear form composed with a linear map of the slope is the quadratic form of its
values on the basis. -/
theorem aux_lem_prefix_limit_atom_extraction_quad_expand {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (v : (Fin d → ℝ) →ₗ[ℝ] E) (e : Fin d → ℝ) :
    B (v e) (v e) = ∑ i : Fin d, ∑ j : Fin d, e i * e j *
      B (v (aux_lem_prefix_limit_atom_extraction_eps i))
        (v (aux_lem_prefix_limit_atom_extraction_eps j)) := by
  conv_lhs => rw [aux_lem_prefix_limit_atom_extraction_decomp e]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The quadratic form of a coefficient matrix. -/
def aux_lem_prefix_limit_atom_extraction_qf (P : Fin d → Fin d → ℝ) (e : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, e i * e j * P i j

/-- Polarization from the values `z_{kl} = F(ε_k + ε_l)`. -/
def aux_lem_prefix_limit_atom_extraction_polOf (z : Fin d → Fin d → ℝ) (i j : Fin d) : ℝ :=
  (z i j - z i i / 4 - z j j / 4) / 2

/-- The bilinear form of a coefficient matrix. -/
def aux_lem_prefix_limit_atom_extraction_bf (P : Fin d → Fin d → ℝ) (u v : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, u i * v j * P i j

theorem aux_lem_prefix_limit_atom_extraction_bf_single (P : Fin d → Fin d → ℝ) (k l : Fin d) :
    aux_lem_prefix_limit_atom_extraction_bf P (aux_lem_prefix_limit_atom_extraction_eps k)
      (aux_lem_prefix_limit_atom_extraction_eps l) = P k l := by
  classical
  unfold aux_lem_prefix_limit_atom_extraction_bf
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single l]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro c _
    simp [Pi.single_apply, hb]
  · simp

theorem aux_lem_prefix_limit_atom_extraction_qf_add (P : Fin d → Fin d → ℝ) (u v : Fin d → ℝ) :
    aux_lem_prefix_limit_atom_extraction_qf P (u + v) =
      aux_lem_prefix_limit_atom_extraction_qf P u + aux_lem_prefix_limit_atom_extraction_qf P v +
        aux_lem_prefix_limit_atom_extraction_bf P u v +
          aux_lem_prefix_limit_atom_extraction_bf P v u := by
  unfold aux_lem_prefix_limit_atom_extraction_qf aux_lem_prefix_limit_atom_extraction_bf
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem aux_lem_prefix_limit_atom_extraction_qf_basis (P : Fin d → Fin d → ℝ)
    (hP : ∀ i j, P i j = P j i) (k l : Fin d) :
    aux_lem_prefix_limit_atom_extraction_qf P
        (aux_lem_prefix_limit_atom_extraction_eps k + aux_lem_prefix_limit_atom_extraction_eps l) =
      P k k + P l l + 2 * P k l := by
  rw [aux_lem_prefix_limit_atom_extraction_qf_add]
  have h1 : aux_lem_prefix_limit_atom_extraction_qf P (aux_lem_prefix_limit_atom_extraction_eps k) =
      P k k := aux_lem_prefix_limit_atom_extraction_bf_single P k k
  have h2 : aux_lem_prefix_limit_atom_extraction_qf P (aux_lem_prefix_limit_atom_extraction_eps l) =
      P l l := aux_lem_prefix_limit_atom_extraction_bf_single P l l
  rw [h1, h2, aux_lem_prefix_limit_atom_extraction_bf_single,
    aux_lem_prefix_limit_atom_extraction_bf_single, hP l k]
  ring

theorem aux_lem_prefix_limit_atom_extraction_polOf_eq (P : Fin d → Fin d → ℝ)
    (hP : ∀ i j, P i j = P j i) :
    aux_lem_prefix_limit_atom_extraction_polOf
        (fun k l => aux_lem_prefix_limit_atom_extraction_qf P
          (aux_lem_prefix_limit_atom_extraction_eps k +
            aux_lem_prefix_limit_atom_extraction_eps l)) = P := by
  funext i j
  simp only [aux_lem_prefix_limit_atom_extraction_polOf,
    aux_lem_prefix_limit_atom_extraction_qf_basis P hP]
  ring

/-- The unit-sphere supremum of the quadratic form with coefficients `P`. -/
def aux_lem_prefix_limit_atom_extraction_qsup (P : Fin d → Fin d → ℝ) : ℝ :=
  ⨆ e : {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1},
    aux_lem_prefix_limit_atom_extraction_qf P (e : Fin d → ℝ)

/-- The reconstruction map from the values `z_{kl} = F(ε_k + ε_l)`. -/
def aux_lem_prefix_limit_atom_extraction_Phi (z : Fin d → Fin d → ℝ) : ℝ :=
  aux_lem_prefix_limit_atom_extraction_qsup (aux_lem_prefix_limit_atom_extraction_polOf z)

theorem aux_lem_prefix_limit_atom_extraction_abs_coord_le
    (e : {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1}) (i : Fin d) :
    |(e : Fin d → ℝ) i| ≤ 1 := by
  have h : ((e : Fin d → ℝ) i) ^ 2 ≤ 1 := by
    calc ((e : Fin d → ℝ) i) ^ 2 ≤ ∑ k : Fin d, ((e : Fin d → ℝ) k) ^ 2 :=
          Finset.single_le_sum (fun k _ => sq_nonneg ((e : Fin d → ℝ) k)) (Finset.mem_univ i)
      _ = 1 := e.2
  exact (sq_le_one_iff_abs_le_one _).mp h

theorem aux_lem_prefix_limit_atom_extraction_qf_diff_le (P P' : Fin d → Fin d → ℝ)
    (e : {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1}) :
    |aux_lem_prefix_limit_atom_extraction_qf P (e : Fin d → ℝ) -
        aux_lem_prefix_limit_atom_extraction_qf P' (e : Fin d → ℝ)| ≤
      ∑ i : Fin d, ∑ j : Fin d, |P i j - P' i j| := by
  unfold aux_lem_prefix_limit_atom_extraction_qf
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← mul_sub, abs_mul, abs_mul]
  have hi := aux_lem_prefix_limit_atom_extraction_abs_coord_le e i
  have hj := aux_lem_prefix_limit_atom_extraction_abs_coord_le e j
  have h1 : |(e : Fin d → ℝ) i| * |(e : Fin d → ℝ) j| ≤ 1 := by
    nlinarith [abs_nonneg ((e : Fin d → ℝ) i), abs_nonneg ((e : Fin d → ℝ) j)]
  nlinarith [abs_nonneg (P i j - P' i j), mul_nonneg (abs_nonneg ((e : Fin d → ℝ) i))
    (abs_nonneg ((e : Fin d → ℝ) j))]

theorem aux_lem_prefix_limit_atom_extraction_qf_bdd (P : Fin d → Fin d → ℝ) :
    BddAbove (Set.range fun e : {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1} =>
      aux_lem_prefix_limit_atom_extraction_qf P (e : Fin d → ℝ)) := by
  refine ⟨∑ i : Fin d, ∑ j : Fin d, |P i j|, ?_⟩
  rintro _ ⟨e, rfl⟩
  have h := aux_lem_prefix_limit_atom_extraction_qf_diff_le P 0 e
  have h0 : aux_lem_prefix_limit_atom_extraction_qf (0 : Fin d → Fin d → ℝ) (e : Fin d → ℝ) = 0 := by
    simp [aux_lem_prefix_limit_atom_extraction_qf]
  rw [h0, sub_zero] at h
  simpa using (le_abs_self _).trans h

variable [NeZero d]

/-- The unit sphere of slopes is nonempty. -/
instance aux_lem_prefix_limit_atom_extraction_sphere_nonempty_gen :
    Nonempty {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1} :=
  ⟨⟨Pi.single 0 1, by
    rw [Finset.sum_eq_single (0 : Fin d)]
    · simp
    · intro b _ hb
      simp [hb]
    · simp⟩⟩

theorem aux_lem_prefix_limit_atom_extraction_qsup_lipschitz (P P' : Fin d → Fin d → ℝ) :
    |aux_lem_prefix_limit_atom_extraction_qsup P - aux_lem_prefix_limit_atom_extraction_qsup P'| ≤
      ∑ i : Fin d, ∑ j : Fin d, |P i j - P' i j| := by
  set S := ∑ i : Fin d, ∑ j : Fin d, |P i j - P' i j|
  have h1 : aux_lem_prefix_limit_atom_extraction_qsup P ≤
      aux_lem_prefix_limit_atom_extraction_qsup P' + S := by
    refine ciSup_le fun e => ?_
    have := aux_lem_prefix_limit_atom_extraction_qf_diff_le P P' e
    have h2 : aux_lem_prefix_limit_atom_extraction_qf P' (e : Fin d → ℝ) ≤
        aux_lem_prefix_limit_atom_extraction_qsup P' :=
      le_ciSup (aux_lem_prefix_limit_atom_extraction_qf_bdd P') e
    linarith [le_abs_self (aux_lem_prefix_limit_atom_extraction_qf P (e : Fin d → ℝ) -
      aux_lem_prefix_limit_atom_extraction_qf P' (e : Fin d → ℝ))]
  have h1' : aux_lem_prefix_limit_atom_extraction_qsup P' ≤
      aux_lem_prefix_limit_atom_extraction_qsup P + S := by
    refine ciSup_le fun e => ?_
    have := aux_lem_prefix_limit_atom_extraction_qf_diff_le P P' e
    have h2 : aux_lem_prefix_limit_atom_extraction_qf P (e : Fin d → ℝ) ≤
        aux_lem_prefix_limit_atom_extraction_qsup P :=
      le_ciSup (aux_lem_prefix_limit_atom_extraction_qf_bdd P) e
    linarith [neg_abs_le (aux_lem_prefix_limit_atom_extraction_qf P (e : Fin d → ℝ) -
      aux_lem_prefix_limit_atom_extraction_qf P' (e : Fin d → ℝ))]
  rw [abs_le]
  constructor <;> linarith

theorem aux_lem_prefix_limit_atom_extraction_polOf_diff_le (z z' : Fin d → Fin d → ℝ) :
    ∑ i : Fin d, ∑ j : Fin d, |aux_lem_prefix_limit_atom_extraction_polOf z i j -
        aux_lem_prefix_limit_atom_extraction_polOf z' i j| ≤
      (2 * (d : ℝ) ^ 2 + 1) * ∑ k : Fin d, ∑ l : Fin d, |z k l - z' k l| := by
  set S := ∑ k : Fin d, ∑ l : Fin d, |z k l - z' k l| with hS
  have hle : ∀ k l : Fin d, |z k l - z' k l| ≤ S := by
    intro k l
    calc |z k l - z' k l| ≤ ∑ l' : Fin d, |z k l' - z' k l'| :=
          Finset.single_le_sum (fun l' _ => abs_nonneg (z k l' - z' k l')) (Finset.mem_univ l)
      _ ≤ S := Finset.single_le_sum (f := fun k' => ∑ l' : Fin d, |z k' l' - z' k' l'|)
          (fun k' _ => Finset.sum_nonneg fun l' _ => abs_nonneg _) (Finset.mem_univ k)
  have hpt : ∀ i j : Fin d, |aux_lem_prefix_limit_atom_extraction_polOf z i j -
      aux_lem_prefix_limit_atom_extraction_polOf z' i j| ≤ |z i j - z' i j| + 2 * S := by
    intro i j
    unfold aux_lem_prefix_limit_atom_extraction_polOf
    have heq : (z i j - z i i / 4 - z j j / 4) / 2 - (z' i j - z' i i / 4 - z' j j / 4) / 2 =
        (z i j - z' i j) / 2 - (z i i - z' i i) / 8 - (z j j - z' j j) / 8 := by ring
    rw [heq, abs_le]
    have h1 := hle i i
    have h2 := hle j j
    constructor <;>
      linarith [le_abs_self (z i j - z' i j), neg_abs_le (z i j - z' i j),
        le_abs_self (z i i - z' i i), neg_abs_le (z i i - z' i i),
        le_abs_self (z j j - z' j j), neg_abs_le (z j j - z' j j), abs_nonneg (z i j - z' i j)]
  calc ∑ i : Fin d, ∑ j : Fin d, |aux_lem_prefix_limit_atom_extraction_polOf z i j -
        aux_lem_prefix_limit_atom_extraction_polOf z' i j|
      ≤ ∑ i : Fin d, ∑ j : Fin d, (|z i j - z' i j| + 2 * S) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
    _ = S + (d : ℝ) * ((d : ℝ) * (2 * S)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        rw [hS]
    _ = (2 * (d : ℝ) ^ 2 + 1) * S := by ring

/-- `Φ` is Lipschitz for the `ℓ¹` distance of the values. -/
theorem aux_lem_prefix_limit_atom_extraction_Phi_lipschitz (z z' : Fin d → Fin d → ℝ) :
    |aux_lem_prefix_limit_atom_extraction_Phi z - aux_lem_prefix_limit_atom_extraction_Phi z'| ≤
      (2 * (d : ℝ) ^ 2 + 1) * ∑ k : Fin d, ∑ l : Fin d, |z k l - z' k l| :=
  (aux_lem_prefix_limit_atom_extraction_qsup_lipschitz _ _).trans
    (aux_lem_prefix_limit_atom_extraction_polOf_diff_le z z')

theorem aux_lem_prefix_limit_atom_extraction_Phi_continuous :
    Continuous (aux_lem_prefix_limit_atom_extraction_Phi (d := d)) := by
  rw [Metric.continuous_iff]
  intro z ε hε
  have hC : (0 : ℝ) < (2 * (d : ℝ) ^ 2 + 1) * (d : ℝ) ^ 2 + 1 := by positivity
  refine ⟨ε / ((2 * (d : ℝ) ^ 2 + 1) * (d : ℝ) ^ 2 + 1), div_pos hε hC, fun z' hz' => ?_⟩
  rw [Real.dist_eq]
  have hcoord : ∀ k l, |z' k l - z k l| ≤ dist z' z := fun k l => by
    rw [← Real.dist_eq]
    exact (dist_le_pi_dist (z' k) (z k) l).trans (dist_le_pi_dist z' z k)
  have hsum : ∑ k : Fin d, ∑ l : Fin d, |z' k l - z k l| ≤ (d : ℝ) ^ 2 * dist z' z := by
    calc ∑ k : Fin d, ∑ l : Fin d, |z' k l - z k l|
        ≤ ∑ k : Fin d, ∑ l : Fin d, dist z' z :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hcoord k l
      _ = (d : ℝ) ^ 2 * dist z' z := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hL := aux_lem_prefix_limit_atom_extraction_Phi_lipschitz z' z
  have hd0 : (0 : ℝ) ≤ 2 * (d : ℝ) ^ 2 + 1 := by positivity
  calc |aux_lem_prefix_limit_atom_extraction_Phi z' - aux_lem_prefix_limit_atom_extraction_Phi z|
      ≤ (2 * (d : ℝ) ^ 2 + 1) * ((d : ℝ) ^ 2 * dist z' z) :=
        hL.trans (mul_le_mul_of_nonneg_left hsum hd0)
    _ ≤ ((2 * (d : ℝ) ^ 2 + 1) * (d : ℝ) ^ 2 + 1) * dist z' z := by
        nlinarith [dist_nonneg (x := z') (y := z)]
    _ < ε := by
        rw [← lt_div_iff₀' hC]
        exact hz'

omit [NeZero d] in
/-- For a symmetric quadratic form, `Φ` of its values is its unit-sphere supremum. -/
theorem aux_lem_prefix_limit_atom_extraction_Phi_eq (P : Fin d → Fin d → ℝ)
    (hP : ∀ i j, P i j = P j i) :
    aux_lem_prefix_limit_atom_extraction_Phi
        (fun k l => aux_lem_prefix_limit_atom_extraction_qf P
          (aux_lem_prefix_limit_atom_extraction_eps k +
            aux_lem_prefix_limit_atom_extraction_eps l)) =
      aux_lem_prefix_limit_atom_extraction_qsup P := by
  unfold aux_lem_prefix_limit_atom_extraction_Phi
  rw [aux_lem_prefix_limit_atom_extraction_polOf_eq P hP]

end PaeQuadGen

section PaeProb

open MeasureTheory Filter
open scoped ENNReal BigOperators

section Generic

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}

theorem aux_lem_prefix_limit_atom_extraction_condExp_best [IsFiniteMeasure μ] (hm : m ≤ m0)
    {X Z : Ω → ℝ} (hX : Integrable X μ) (hZ : Integrable Z μ) (hZm : StronglyMeasurable[m] Z) :
    eLpNorm (fun ω => X ω - μ[X|m] ω) 1 μ ≤ 2 * eLpNorm (fun ω => X ω - Z ω) 1 μ := by
  have hce := condExp_sub hX hZ m
  have hZZ : μ[Z|m] = Z := condExp_of_stronglyMeasurable hm hZm hZ
  have heq : (fun ω => X ω - μ[X|m] ω) =ᵐ[μ] (X - Z) - μ[X - Z|m] := by
    filter_upwards [hce] with ω h
    simp only [Pi.sub_apply] at h ⊢
    rw [h, hZZ]
    ring
  rw [eLpNorm_congr_ae heq]
  calc eLpNorm ((X - Z) - μ[X - Z|m]) 1 μ
      ≤ eLpNorm (X - Z) 1 μ + eLpNorm (μ[X - Z|m]) 1 μ :=
        eLpNorm_sub_le le_rfl
    _ ≤ eLpNorm (X - Z) 1 μ + eLpNorm (X - Z) 1 μ := by
        gcongr
        exact eLpNorm_one_condExp_le_eLpNorm _
    _ = 2 * eLpNorm (fun ω => X ω - Z ω) 1 μ := by rw [two_mul]; rfl

theorem aux_lem_prefix_limit_atom_extraction_band_add_div [IsFiniteMeasure μ]
    {D N : Ω → ℝ} (hD : Integrable D μ) (hN : Integrable N μ) (c : ℝ) :
    eLpNorm (fun ω => (D ω + N ω) / c - μ[fun ω => (D ω + N ω) / c|m] ω) 1 μ ≤
      ‖c⁻¹‖ₑ * (eLpNorm (fun ω => D ω - μ[D|m] ω) 1 μ +
        eLpNorm (fun ω => N ω - μ[N|m] ω) 1 μ) := by
  have hfun : (fun ω => (D ω + N ω) / c) = c⁻¹ • (D + N) := by
    funext ω
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hce : μ[fun ω => (D ω + N ω) / c|m] =ᵐ[μ] c⁻¹ • (μ[D|m] + μ[N|m]) := by
    rw [hfun]
    exact (condExp_smul c⁻¹ (D + N) m).trans ((condExp_add hD hN m).const_smul c⁻¹)
  have heq : (fun ω => (D ω + N ω) / c - μ[fun ω => (D ω + N ω) / c|m] ω) =ᵐ[μ]
      c⁻¹ • ((D - μ[D|m]) + (N - μ[N|m])) := by
    filter_upwards [hce] with ω h
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul] at h ⊢
    rw [h]
    ring
  rw [eLpNorm_congr_ae heq, eLpNorm_const_smul]
  gcongr
  exact eLpNorm_add_le le_rfl

end Generic

section PhiBand

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {d : ℕ} [NeZero d]

theorem aux_lem_prefix_limit_atom_extraction_Phi_zero :
    aux_lem_prefix_limit_atom_extraction_Phi (0 : Fin d → Fin d → ℝ) = 0 := by
  unfold aux_lem_prefix_limit_atom_extraction_Phi aux_lem_prefix_limit_atom_extraction_qsup
  have h : ∀ e : {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1},
      aux_lem_prefix_limit_atom_extraction_qf
        (aux_lem_prefix_limit_atom_extraction_polOf 0) (e : Fin d → ℝ) = 0 := by
    intro e
    simp [aux_lem_prefix_limit_atom_extraction_qf, aux_lem_prefix_limit_atom_extraction_polOf]
  simp only [h, ciSup_const]

theorem aux_lem_prefix_limit_atom_extraction_Phi_abs_le (w : Fin d → Fin d → ℝ) :
    |aux_lem_prefix_limit_atom_extraction_Phi w| ≤
      (2 * (d : ℝ) ^ 2 + 1) * ∑ k : Fin d, ∑ l : Fin d, |w k l| := by
  have h := aux_lem_prefix_limit_atom_extraction_Phi_lipschitz w 0
  simpa [aux_lem_prefix_limit_atom_extraction_Phi_zero] using h

theorem aux_lem_prefix_limit_atom_extraction_band_Phi [IsFiniteMeasure μ] (hm : m ≤ m0)
    (z : Fin d → Fin d → Ω → ℝ) (hzm : ∀ k l, Measurable (z k l))
    (hz : ∀ k l, Integrable (z k l) μ) :
    eLpNorm (fun ω => aux_lem_prefix_limit_atom_extraction_Phi (fun k l => z k l ω) -
        μ[fun ω => aux_lem_prefix_limit_atom_extraction_Phi (fun k l => z k l ω)|m] ω) 1 μ ≤
      2 * (ENNReal.ofReal (2 * (d : ℝ) ^ 2 + 1) *
        ∑ k : Fin d, ∑ l : Fin d, eLpNorm (fun ω => z k l ω - μ[z k l|m] ω) 1 μ) := by
  set C : ℝ := 2 * (d : ℝ) ^ 2 + 1 with hC
  have hC0 : 0 ≤ C := by positivity
  let X : Ω → ℝ := fun ω => aux_lem_prefix_limit_atom_extraction_Phi (fun k l => z k l ω)
  let zh : Fin d → Fin d → Ω → ℝ := fun k l => μ[z k l|m]
  let Z : Ω → ℝ := fun ω => aux_lem_prefix_limit_atom_extraction_Phi (fun k l => zh k l ω)
  have hXm : Measurable X :=
    aux_lem_prefix_limit_atom_extraction_Phi_continuous.measurable.comp
      (measurable_pi_lambda fun k => measurable_pi_lambda fun l => hzm k l)
  have hzhm : ∀ k l, Measurable[m] (zh k l) := fun k l =>
    (stronglyMeasurable_condExp (m := m) (μ := μ) (f := z k l)).measurable
  have htuple : Measurable[m] (fun ω => fun k l => zh k l ω) := by
    refine @measurable_pi_lambda Ω (Fin d) (fun _ => Fin d → ℝ) m _ _ (fun k => ?_)
    exact @measurable_pi_lambda Ω (Fin d) (fun _ => ℝ) m _ _ (fun l => hzhm k l)
  have hZmeas : Measurable[m] Z :=
    aux_lem_prefix_limit_atom_extraction_Phi_continuous.measurable.comp htuple
  have hZm : StronglyMeasurable[m] Z := hZmeas.stronglyMeasurable
  have hbdX : Integrable (fun ω => C * ∑ k : Fin d, ∑ l : Fin d, |z k l ω|) μ :=
    (integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => (hz k l).abs).const_mul C
  have hbdZ : Integrable (fun ω => C * ∑ k : Fin d, ∑ l : Fin d, |zh k l ω|) μ :=
    (integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ =>
      (integrable_condExp (f := z k l)).abs).const_mul C
  have hX : Integrable X μ := Integrable.mono' hbdX hXm.aestronglyMeasurable
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact aux_lem_prefix_limit_atom_extraction_Phi_abs_le _)
  have hZ : Integrable Z μ := Integrable.mono' hbdZ
    ((hZm.mono hm).aestronglyMeasurable)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact aux_lem_prefix_limit_atom_extraction_Phi_abs_le _)
  refine (aux_lem_prefix_limit_atom_extraction_condExp_best hm hX hZ hZm).trans ?_
  gcongr
  have hmeasD : ∀ k l, AEMeasurable (fun ω => ‖z k l ω - zh k l ω‖ₑ) μ := fun k l =>
    ((hzm k l).sub ((stronglyMeasurable_condExp (m := m) (μ := μ)
      (f := z k l)).measurable.mono hm le_rfl)).enorm.aemeasurable
  have hXZ : AEStronglyMeasurable (fun ω => X ω - Z ω) μ := by
    simpa only [Pi.sub_apply] using! (hX.sub hZ).aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm hXZ]
  calc ∫⁻ ω, ‖X ω - Z ω‖ₑ ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal C * ∑ k : Fin d, ∑ l : Fin d, ‖z k l ω - zh k l ω‖ₑ ∂μ := by
        refine lintegral_mono fun ω => ?_
        have hpt := aux_lem_prefix_limit_atom_extraction_Phi_lipschitz
          (fun k l => z k l ω) (fun k l => zh k l ω)
        rw [Real.enorm_eq_ofReal_abs]
        calc ENNReal.ofReal |X ω - Z ω|
            ≤ ENNReal.ofReal (C * ∑ k : Fin d, ∑ l : Fin d, |z k l ω - zh k l ω|) :=
              ENNReal.ofReal_le_ofReal hpt
          _ = ENNReal.ofReal C * ∑ k : Fin d, ∑ l : Fin d, ‖z k l ω - zh k l ω‖ₑ := by
              rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_sum_of_nonneg
                (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg _)]
              congr 1
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => abs_nonneg _)]
              refine Finset.sum_congr rfl fun l _ => ?_
              rw [Real.enorm_eq_ofReal_abs]
    _ = ENNReal.ofReal C * ∑ k : Fin d, ∑ l : Fin d, ∫⁻ ω, ‖z k l ω - zh k l ω‖ₑ ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        rw [lintegral_finset_sum' (f := fun k ω => ∑ l : Fin d, ‖z k l ω - zh k l ω‖ₑ)
          Finset.univ (fun k _ => Finset.aemeasurable_fun_sum _ fun l _ => hmeasD k l)]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact lintegral_finset_sum' (f := fun l ω => ‖z k l ω - zh k l ω‖ₑ) Finset.univ
          (fun l _ => hmeasD k l)
    _ = ENNReal.ofReal C *
          ∑ k : Fin d, ∑ l : Fin d, eLpNorm (fun ω => z k l ω - μ[z k l|m] ω) 1 μ := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        exact (eLpNorm_one_eq_lintegral_enorm
          ((hz k l).sub (integrable_condExp (f := z k l))).aestronglyMeasurable).symm

end PhiBand

end PaeProb

section PaeTele

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators
open SubdiffusiveProcess SubdiffusiveProcess.Lane3

/-- Exchanging the first components of two independent product samples preserves the
joint product law. -/
theorem aux_lem_prefix_limit_atom_extraction_tele_swap4 {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasurePreserving (fun x : (A × B) × (A × B) => ((x.2.1, x.1.2), (x.1.1, x.2.2)))
      ((μ.prod ν).prod (μ.prod ν)) ((μ.prod ν).prod (μ.prod ν)) := by
  have f1 := measurePreserving_prodAssoc μ ν (μ.prod ν)
  have f2 : MeasurePreserving (Prod.map id Prod.swap)
      (μ.prod (ν.prod (μ.prod ν))) (μ.prod ((μ.prod ν).prod ν)) :=
    (MeasurePreserving.id μ).prod Measure.measurePreserving_swap
  have f3 : MeasurePreserving (Prod.map id MeasurableEquiv.prodAssoc)
      (μ.prod ((μ.prod ν).prod ν)) (μ.prod (μ.prod (ν.prod ν))) :=
    (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc μ ν ν)
  have f4 := (measurePreserving_prodAssoc μ μ (ν.prod ν)).symm
  have f5 : MeasurePreserving (Prod.map Prod.swap Prod.swap)
      ((μ.prod μ).prod (ν.prod ν)) ((μ.prod μ).prod (ν.prod ν)) :=
    Measure.measurePreserving_swap.prod Measure.measurePreserving_swap
  have g1 := measurePreserving_prodAssoc μ μ (ν.prod ν)
  have g2 : MeasurePreserving (Prod.map id MeasurableEquiv.prodAssoc.symm)
      (μ.prod (μ.prod (ν.prod ν))) (μ.prod ((μ.prod ν).prod ν)) :=
    (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc μ ν ν).symm
  have g3 : MeasurePreserving (Prod.map id (Prod.map Prod.swap id))
      (μ.prod ((μ.prod ν).prod ν)) (μ.prod ((ν.prod μ).prod ν)) :=
    (MeasurePreserving.id μ).prod
      (Measure.measurePreserving_swap.prod (MeasurePreserving.id ν))
  have g4 : MeasurePreserving (Prod.map id MeasurableEquiv.prodAssoc)
      (μ.prod ((ν.prod μ).prod ν)) (μ.prod (ν.prod (μ.prod ν))) :=
    (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ν μ ν)
  have g5 := (measurePreserving_prodAssoc μ ν (μ.prod ν)).symm
  have h := g5.comp (g4.comp (g3.comp (g2.comp (g1.comp
    (f5.comp (f4.comp (f3.comp (f2.comp f1))))))))
  convert h using 1
  rfl

/-- Exchanging an arbitrary block of coordinates between two independent samples of an
infinite product preserves the joint law. -/
theorem aux_lem_prefix_limit_atom_extraction_tele_block_swap {I : Type*} {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S : Set I) [DecidablePred (fun i => i ∈ S)] :
    MeasurePreserving
      (fun z : ((i : I) → X i) × ((i : I) → X i) =>
        ((fun i : I => if i ∈ S then z.2 i else z.1 i),
          (fun i : I => if i ∈ S then z.1 i else z.2 i)))
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ))
      ((Measure.infinitePi μ).prod (Measure.infinitePi μ)) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd X (fun i => i ∈ S)
  let νS := Measure.infinitePi (fun i : S => μ i)
  let νC := Measure.infinitePi (fun i : {i // i ∉ S} => μ i)
  have hsplit : MeasurePreserving e (Measure.infinitePi μ) (νS.prod νC) :=
    measurePreserving_infinitePi_split μ (fun i => i ∈ S)
  have h := ((MeasurePreserving.symm e hsplit).prod (MeasurePreserving.symm e hsplit)).comp
    ((aux_lem_prefix_limit_atom_extraction_tele_swap4 νS νC).comp (hsplit.prod hsplit))
  convert h using 1
  funext z
  apply Prod.ext <;> funext i <;> by_cases hi : i ∈ S <;> simp [e, hi]

/-- Replacing one coordinate by the same coordinate of an independent copy preserves the law. -/
theorem aux_lem_prefix_limit_atom_extraction_tele_update_mp {I : Type*} [DecidableEq I] {X : Type*}
    [MeasurableSpace X] (μs : I → Measure X) [∀ i, IsProbabilityMeasure (μs i)] (k0 : I) :
    MeasurePreserving (fun p : (I → X) × (I → X) => Function.update p.1 k0 (p.2 k0))
      ((Measure.infinitePi μs).prod (Measure.infinitePi μs)) (Measure.infinitePi μs) := by
  classical
  have h := SubdiffusiveProcess.measurePreserving_copy_infinitePi_block
    (X := fun _ : I => X) μs ({k0} : Set I)
  convert h using 1
  funext p i
  by_cases hi : i = k0
  · subst hi; simp
  · simp [Function.update, hi]

/-- Conditional Jensen through an independent resampling of the discarded block. -/
theorem aux_lem_prefix_limit_atom_extraction_tele_resample_jensen {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] {ξ : Measure Ω} [IsProbabilityMeasure ξ] {μ : Measure A}
    {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (e : Ω ≃ᵐ A × B) (he : MeasurePreserving e ξ (μ.prod ν))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤) {f : Ω → ℝ} (hf : Integrable f ξ) :
    eLpNorm (f - ξ[f | (inferInstance : MeasurableSpace A).comap (fun x => (e x).1)]) p ξ ≤
      eLpNorm (fun q : Ω × Ω => f q.1 - f (e.symm ((e q.1).1, (e q.2).2))) p
        (ξ.prod ξ) := by
  have hce := condExp_equiv_fst_integral e he hf
  have h1 : MeasurePreserving (Prod.map (fun x => (e x).1) id) (ξ.prod ν) (μ.prod ν) :=
    (measurePreserving_fst.comp he).prod (MeasurePreserving.id ν)
  have hΘ : MeasurePreserving (fun xb : Ω × B => e.symm ((e xb.1).1, xb.2)) (ξ.prod ν) ξ :=
    (he.symm e).comp h1
  have hg : Integrable (fun xb : Ω × B => f (e.symm ((e xb.1).1, xb.2))) (ξ.prod ν) :=
    hΘ.integrable_comp_of_integrable hf
  let F : Ω × B → ℝ := fun xb => f xb.1 - f (e.symm ((e xb.1).1, xb.2))
  have hF : Integrable F (ξ.prod ν) := (hf.comp_fst ν).sub hg
  have hae : (f - ξ[f | (inferInstance : MeasurableSpace A).comap (fun x => (e x).1)])
      =ᵐ[ξ] fun x => ∫ b, F (x, b) ∂ν := by
    filter_upwards [hce, hg.prod_right_ae] with x hx hxint
    simp only [Pi.sub_apply, hx, F]
    rw [integral_sub (integrable_const _) hxint, integral_const]
    simp
  rw [eLpNorm_congr_ae hae]
  have hfst : MeasurePreserving (Prod.fst : Ω × B → Ω) (ξ.prod ν) ξ := measurePreserving_fst
  rw [← eLpNorm_comp_measurePreserving hF.integral_prod_left.aestronglyMeasurable hfst]
  refine (eLpNorm_prod_integral_le hp hp_top hF.aestronglyMeasurable).trans (le_of_eq ?_)
  have hT : MeasurePreserving (Prod.map id (fun x => (e x).2)) (ξ.prod ξ) (ξ.prod ν) :=
    (MeasurePreserving.id ξ).prod (measurePreserving_snd.comp he)
  rw [← eLpNorm_comp_measurePreserving hF.aestronglyMeasurable hT]
  rfl

/-- The retained block of the three-block decomposition generates the band σ-field. -/
theorem aux_lem_prefix_limit_atom_extraction_tele_band_sigma_eq {X : Type} [MeasurableSpace X] (h : ℕ) :
    bandSigma (fun _ : ℤ => X) h =
      middleSigma.comap (threeBlockEquiv (X := fun _ : ℤ => X)
        (fun j : ℤ => j ≤ (h : ℤ)) (fun j => j < -(h : ℤ))) := by
  classical
  set e := threeBlockEquiv (X := fun _ : ℤ => X) (fun j : ℤ => j ≤ (h : ℤ))
    (fun j => j < -(h : ℤ))
  have hmid : middleSigma.comap e =
      (inferInstance : MeasurableSpace
        ((i : {i : {j : ℤ // j ≤ (h : ℤ)} // ¬ i.1 < -(h : ℤ)}) → X)).comap
        (fun om => (e om).1.2) := by
    rw [middleSigma, MeasurableSpace.comap_comp]
    rfl
  rw [hmid]
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    have hj1 : j ≤ (h : ℤ) := hj.2
    have hj2 : ¬ j < -(h : ℤ) := not_lt.mpr hj.1
    have hfun : (fun om : ℤ → X => om j) =
        (fun b : ((i : {i : {j : ℤ // j ≤ (h : ℤ)} // ¬ i.1 < -(h : ℤ)}) → X) =>
          b ⟨⟨j, hj1⟩, hj2⟩) ∘ (fun om => (e om).1.2) := rfl
    rw [hfun, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  · show MeasurableSpace.comap (fun om => (e om).1.2) MeasurableSpace.pi ≤ _
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    refine iSup_le fun i => ?_
    have hi : i.1.1 ∈ Set.Icc (-(h : ℤ)) (h : ℤ) := ⟨not_lt.mp i.2, i.1.2⟩
    exact le_iSup₂ (f := fun (k : ℤ) (_ : k ∈ Set.Icc (-(h : ℤ)) (h : ℤ)) =>
        (inferInstance : MeasurableSpace X).comap (fun om : ℤ → X => om k)) i.1.1 hi

theorem aux_lem_prefix_limit_atom_extraction_tele_coarse_symm {X : Type} [MeasurableSpace X] (h : ℕ)
    (q : (ℤ → X) × (ℤ → X)) :
    let e := threeBlockEquiv (X := fun _ : ℤ => X) (fun j : ℤ => j ≤ (h : ℤ))
      (fun j => j < -(h : ℤ))
    e.symm ((e q.1).1, (e q.2).2) = fun j => if (h : ℤ) < j then q.2 j else q.1 j := by
  intro e
  apply e.injective
  rw [MeasurableEquiv.apply_symm_apply]
  refine Prod.ext ?_ ?_
  · have hfun : (fun i : {j : ℤ // j ≤ (h : ℤ)} => q.1 i) =
        (fun i : {j : ℤ // j ≤ (h : ℤ)} => if (h : ℤ) < (i : ℤ) then q.2 i else q.1 i) :=
      funext fun i => (if_neg (not_lt.mpr i.2)).symm
    exact congrArg (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : {j : ℤ // j ≤ (h : ℤ)} => X)
      (fun i => (i : ℤ) < -(h : ℤ))) hfun
  · funext i
    show q.2 i = if (h : ℤ) < (i : ℤ) then q.2 i else q.1 i
    rw [if_pos (lt_of_not_ge i.2)]

theorem aux_lem_prefix_limit_atom_extraction_tele_fine_symm {X : Type} [MeasurableSpace X] (h : ℕ)
    (q : (ℤ → X) × (ℤ → X)) :
    let e := threeBlockEquiv (X := fun _ : ℤ => X) (fun j : ℤ => j ≤ (h : ℤ))
      (fun j => j < -(h : ℤ))
    let e2 := e.trans (MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodComm)
    e2.symm ((e2 q.1).1, (e2 q.2).2) = fun j => if j < -(h : ℤ) then q.2 j else q.1 j := by
  intro e e2
  apply e2.injective
  rw [MeasurableEquiv.apply_symm_apply]
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext i
    show q.1 i.1 = if (i.1 : ℤ) < -(h : ℤ) then q.2 i.1 else q.1 i.1
    rw [if_neg i.2]
  · funext i
    show q.1 i = if (i : ℤ) < -(h : ℤ) then q.2 i else q.1 i
    have : ¬ (i : ℤ) < -(h : ℤ) := by have := i.2; omega
    rw [if_neg this]
  · funext i
    show q.2 i.1 = if (i.1 : ℤ) < -(h : ℤ) then q.2 i.1 else q.1 i.1
    rw [if_pos i.2]

/-- **Band split.** The band error is bounded by the coarse-copy and fine-copy increments. -/
theorem aux_lem_prefix_limit_atom_extraction_tele_band_split {X : Type} [MeasurableSpace X]
    (laws : ℤ → Measure X) [∀ j, IsProbabilityMeasure (laws j)] (h : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    {f : (ℤ → X) → ℝ} (hf : Integrable f (Measure.infinitePi laws)) :
    eLpNorm (fun om => f om - (Measure.infinitePi laws)[f | bandSigma (fun _ : ℤ => X) h] om) p
        (Measure.infinitePi laws) ≤
      eLpNorm (fun q : (ℤ → X) × (ℤ → X) =>
          f q.1 - f (fun j => if (h : ℤ) < j then q.2 j else q.1 j)) p
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) +
      eLpNorm (fun q : (ℤ → X) × (ℤ → X) =>
          f q.1 - f (fun j => if j < -(h : ℤ) then q.2 j else q.1 j)) p
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) := by
  have hmain := infinitePi_integer_band_error_le laws h hp hp_top hf
  simp only at hmain
  set e := threeBlockEquiv (X := fun _ : ℤ => X) (fun j : ℤ => j ≤ (h : ℤ))
    (fun j => j < -(h : ℤ)) with he_def
  rw [← aux_lem_prefix_limit_atom_extraction_tele_band_sigma_eq] at hmain
  have he := measurePreserving_infinitePi_threeBlock laws (fun j : ℤ => j ≤ (h : ℤ))
    (fun j => j < -(h : ℤ))
  refine hmain.trans (add_le_add ?_ ?_)
  · have hlm : leftMiddleSigma.comap e =
        (inferInstance : MeasurableSpace _).comap (fun x => (e x).1) := by
      rw [leftMiddleSigma, MeasurableSpace.comap_comp]
      rfl
    rw [hlm]
    refine (aux_lem_prefix_limit_atom_extraction_tele_resample_jensen e he hp hp_top hf).trans (le_of_eq ?_)
    congr 1
    funext q
    rw [aux_lem_prefix_limit_atom_extraction_tele_coarse_symm h q]
  · let e2 := e.trans (MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodComm)
    have he2 : MeasurePreserving e2 (Measure.infinitePi laws) _ :=
      (Measure.measurePreserving_swap.comp (measurePreserving_prodAssoc _ _ _)).comp he
    have hmr : middleRightSigma.comap e =
        (inferInstance : MeasurableSpace _).comap (fun x => (e2 x).1) := by
      rw [middleRightSigma, MeasurableSpace.comap_comp]
      rfl
    rw [hmr]
    refine (aux_lem_prefix_limit_atom_extraction_tele_resample_jensen e2 he2 hp hp_top hf).trans (le_of_eq ?_)
    congr 1
    funext q
    rw [aux_lem_prefix_limit_atom_extraction_tele_fine_symm h q]

/-- **Fine telescoping.** If `f` is determined by the coordinates `≥ -N` on a full-measure
set, the fine-copy increment is bounded by the one-coordinate replacement increments of the
layers strictly between the band and the cutoff. -/
theorem aux_lem_prefix_limit_atom_extraction_tele_fine_telescope {X : Type} [MeasurableSpace X]
    (laws : ℤ → Measure X) [∀ j, IsProbabilityMeasure (laws j)]
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : (ℤ → X) → ℝ) (hf : AEStronglyMeasurable f (Measure.infinitePi laws))
    (G : Set (ℤ → X)) (hG : ∀ᵐ om ∂(Measure.infinitePi laws), om ∈ G)
    (h N : ℕ)
    (hdet : ∀ ω₁ ∈ G, ∀ ω₂ ∈ G, (∀ j : ℤ, -(N : ℤ) ≤ j → ω₁ j = ω₂ j) → f ω₁ = f ω₂)
    (c : ℕ → ℝ≥0∞)
    (hstep : ∀ k : ℕ, h < k → k ≤ N →
      eLpNorm (fun q : (ℤ → X) × (ℤ → X) =>
          f q.1 - f (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))) p
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤ c k) :
    eLpNorm (fun q : (ℤ → X) × (ℤ → X) =>
        f q.1 - f (fun j => if j < -(h : ℤ) then q.2 j else q.1 j)) p
      ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤
      ∑ k ∈ Finset.Ioc h N, c k := by
  classical
  set P := Measure.infinitePi laws with hP
  let W : ℕ → (ℤ → X) × (ℤ → X) → (ℤ → X) := fun k q j =>
    if -(k : ℤ) ≤ j ∧ j < -(h : ℤ) then q.2 j else q.1 j
  have hWmp : ∀ k, MeasurePreserving (W k) (P.prod P) P := fun k =>
    measurePreserving_copy_infinitePi_block laws {j : ℤ | -(k : ℤ) ≤ j ∧ j < -(h : ℤ)}
  let Sw : ℕ → (ℤ → X) × (ℤ → X) → (ℤ → X) × (ℤ → X) := fun k q =>
    (W k q, fun j => if -(k : ℤ) ≤ j ∧ j < -(h : ℤ) then q.1 j else q.2 j)
  have hSwmp : ∀ k, MeasurePreserving (Sw k) (P.prod P) (P.prod P) := fun k =>
    aux_lem_prefix_limit_atom_extraction_tele_block_swap laws {j : ℤ | -(k : ℤ) ≤ j ∧ j < -(h : ℤ)}
  have hfW : ∀ k, AEStronglyMeasurable (fun q => f (W k q)) (P.prod P) := fun k =>
    hf.comp_measurePreserving (hWmp k)
  have hf1 : AEStronglyMeasurable (fun q : (ℤ → X) × (ℤ → X) => f q.1) (P.prod P) :=
    hf.comp_measurePreserving measurePreserving_fst
  -- one step
  have hstep' : ∀ k : ℕ, h ≤ k → k + 1 ≤ N →
      eLpNorm (fun q => f (W k q) - f (W (k + 1) q)) p (P.prod P) ≤ c (k + 1) := by
    intro k hk hkN
    let Gk : (ℤ → X) × (ℤ → X) → ℝ := fun q =>
      f q.1 - f (Function.update q.1 (-((k + 1 : ℕ) : ℤ)) (q.2 (-((k + 1 : ℕ) : ℤ))))
    have hGk : AEStronglyMeasurable Gk (P.prod P) :=
      hf1.sub (hf.comp_measurePreserving (aux_lem_prefix_limit_atom_extraction_tele_update_mp laws _))
    have hcomp : (fun q => f (W k q) - f (W (k + 1) q)) = Gk ∘ Sw k := by
      funext q
      simp only [Gk, Sw, Function.comp_apply]
      congr 2
      funext j
      by_cases hj : j = -((k + 1 : ℕ) : ℤ)
      · subst hj
        simp only [Function.update_self, W]
        have h1 : -((k + 1 : ℕ) : ℤ) ≤ -((k + 1 : ℕ) : ℤ) ∧ -((k + 1 : ℕ) : ℤ) < -(h : ℤ) :=
          ⟨le_rfl, by push_cast; omega⟩
        have h2 : ¬ (-(k : ℤ) ≤ -((k + 1 : ℕ) : ℤ) ∧ -((k + 1 : ℕ) : ℤ) < -(h : ℤ)) := by
          push_cast; omega
        rw [if_pos (by exact_mod_cast h1), if_neg h2]
      · rw [Function.update_of_ne hj]
        simp only [W]
        have hiff : (-((k + 1 : ℕ) : ℤ) ≤ j ∧ j < -(h : ℤ)) ↔ (-(k : ℤ) ≤ j ∧ j < -(h : ℤ)) := by
          push_cast at hj ⊢; omega
        by_cases hc : -(k : ℤ) ≤ j ∧ j < -(h : ℤ)
        · rw [if_pos hc, if_pos (hiff.mpr hc)]
        · rw [if_neg hc, if_neg (fun h' => hc (hiff.mp h'))]
    rw [hcomp, eLpNorm_comp_measurePreserving hGk (hSwmp k)]
    exact hstep (k + 1) (by omega) hkN
  -- the telescoping sum
  have hW0 : ∀ q, W h q = q.1 := by
    intro q
    funext j
    simp only [W]
    rw [if_neg (by omega)]
  have htel : ∀ m : ℕ, h + m ≤ N →
      eLpNorm (fun q => f q.1 - f (W (h + m) q)) p (P.prod P) ≤
        ∑ k ∈ Finset.Ioc h (h + m), c k := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [Nat.add_zero, hW0, sub_self]
      simp
    | succ m ih =>
      intro hm
      have hsplit : (fun q => f q.1 - f (W (h + (m + 1)) q)) =
          (fun q => f q.1 - f (W (h + m) q)) + (fun q => f (W (h + m) q) - f (W (h + m + 1) q)) := by
        funext q
        simp only [Pi.add_apply]
        rw [show h + (m + 1) = h + m + 1 by omega]
        ring
      rw [hsplit, show h + (m + 1) = h + m + 1 by omega, Finset.sum_Ioc_succ_top (by omega)]
      refine (eLpNorm_add_le hp).trans ?_
      exact add_le_add (ih (by omega)) (hstep' (h + m) (by omega) (by omega))
  -- determination by coordinates `≥ -N`
  let FC : (ℤ → X) × (ℤ → X) → (ℤ → X) := fun q j => if j < -(h : ℤ) then q.2 j else q.1 j
  have hFCmp : MeasurePreserving FC (P.prod P) P :=
    measurePreserving_copy_infinitePi_block laws {j : ℤ | j < -(h : ℤ)}
  have hGFC : ∀ᵐ q ∂(P.prod P), FC q ∈ G := hFCmp.quasiMeasurePreserving.ae hG
  have hG1 : ∀ᵐ q ∂(P.prod P), q.1 ∈ G :=
    (measurePreserving_fst : MeasurePreserving Prod.fst (P.prod P) P).quasiMeasurePreserving.ae hG
  by_cases hNh : N ≤ h
  · have hzero : (fun q : (ℤ → X) × (ℤ → X) => f q.1 - f (FC q)) =ᵐ[P.prod P] 0 := by
      filter_upwards [hGFC, hG1] with q hq1 hq2
      rw [hdet (FC q) hq1 q.1 hq2 (fun j hj => by
        simp only [FC]; rw [if_neg (by omega)])]
      simp
    change eLpNorm (fun q : (ℤ → X) × (ℤ → X) => f q.1 - f (FC q)) p (P.prod P) ≤ _
    rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
    exact zero_le
  · push_neg at hNh
    have hGW : ∀ᵐ q ∂(P.prod P), W N q ∈ G := (hWmp N).quasiMeasurePreserving.ae hG
    have heq : (fun q : (ℤ → X) × (ℤ → X) => f q.1 - f (FC q)) =ᵐ[P.prod P]
        (fun q => f q.1 - f (W (h + (N - h)) q)) := by
      filter_upwards [hGFC, hGW] with q hq1 hq2
      rw [show h + (N - h) = N by omega]
      rw [hdet (FC q) hq1 (W N q) hq2 (fun j hj => by
        simp only [FC, W]
        by_cases hj2 : j < -(h : ℤ)
        · rw [if_pos hj2, if_pos ⟨hj, hj2⟩]
        · rw [if_neg hj2, if_neg (fun h' => hj2 h'.2)])]
    change eLpNorm (fun q : (ℤ → X) × (ℤ → X) => f q.1 - f (FC q)) p (P.prod P) ≤ _
    rw [eLpNorm_congr_ae heq]
    have := htel (N - h) (by omega)
    rwa [show h + (N - h) = N by omega] at this ⊢

end PaeTele

section PaeSplit

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

variable {d : ℕ}

open Classical in
/-- The band coordinate `ω_{-j}` of a band sample (zero when `-j` is outside the band). -/
def aux_lem_prefix_limit_atom_extraction_bandCoord (H : ℕ)
    (b : (j : bandSet H) → (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) j.1) (j : ℕ) :
    C(SpatialCoordinates d, ℝ) :=
  if h : (-(j : ℤ)) ∈ bandSet H then b ⟨-(j : ℤ), h⟩ else 0

open Classical in
/-- The non-band coordinate `ω_{-j}` of a non-band sample (zero when `-j` is in the band). -/
def aux_lem_prefix_limit_atom_extraction_tailCoord (H : ℕ)
    (t : (j : {j : ℤ // j ∉ bandSet H}) → (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) j.1)
    (j : ℕ) : C(SpatialCoordinates d, ℝ) :=
  if h : (-(j : ℤ)) ∉ bandSet H then t ⟨-(j : ℤ), h⟩ else 0

theorem aux_lem_prefix_limit_atom_extraction_bandCoord_apply (H : ℕ)
    (ω : ℤ → C(SpatialCoordinates d, ℝ)) (j : ℕ) (hj : j ≤ H) :
    aux_lem_prefix_limit_atom_extraction_bandCoord H (fun i => ω i.1) j = ω (-(j : ℤ)) := by
  have h : (-(j : ℤ)) ∈ bandSet H := by
    rw [bandSet, Set.mem_Icc]
    constructor <;> omega
  rw [aux_lem_prefix_limit_atom_extraction_bandCoord, dif_pos h]

theorem aux_lem_prefix_limit_atom_extraction_tailCoord_apply (H : ℕ)
    (ω : ℤ → C(SpatialCoordinates d, ℝ)) (j : ℕ) (hj : H < j) :
    aux_lem_prefix_limit_atom_extraction_tailCoord H (fun i => ω i.1) j = ω (-(j : ℤ)) := by
  have h : (-(j : ℤ)) ∉ bandSet H := by
    rw [bandSet, Set.mem_Icc]
    omega
  rw [aux_lem_prefix_limit_atom_extraction_tailCoord, dif_pos h]

theorem aux_lem_prefix_limit_atom_extraction_bandCoord_continuous (H j : ℕ) :
    Continuous (fun b : (j : bandSet H) → (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) j.1 =>
      aux_lem_prefix_limit_atom_extraction_bandCoord H b j) := by
  unfold aux_lem_prefix_limit_atom_extraction_bandCoord
  split_ifs with h
  · exact continuous_apply _
  · exact continuous_const

theorem aux_lem_prefix_limit_atom_extraction_tailCoord_continuous (H j : ℕ) :
    Continuous (fun t : (j : {j : ℤ // j ∉ bandSet H}) →
        (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) j.1 =>
      aux_lem_prefix_limit_atom_extraction_tailCoord H t j) := by
  unfold aux_lem_prefix_limit_atom_extraction_tailCoord
  by_cases h : (-(j : ℤ)) ∉ bandSet H
  · simp only [dif_pos h]
    exact continuous_apply (⟨-(j : ℤ), h⟩ : {j : ℤ // j ∉ bandSet H})
  · simp only [dif_neg h]
    exact continuous_const

/-- The band potential, restricted to the compact root `K₀`. -/
def aux_lem_prefix_limit_atom_extraction_V (H : ℕ)
    (b : (j : bandSet H) → (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) j.1) :
    C(closedCube (0 : SpatialCoordinates d) 1 one_pos, ℝ) :=
  (∑ j ∈ Finset.range (H + 1), aux_lem_prefix_limit_atom_extraction_bandCoord H b j).restrict
    (closedCube (0 : SpatialCoordinates d) 1 one_pos)

/-- The fine tail potential at cutoff `N`, including the deterministic normalization. -/
def aux_lem_prefix_limit_atom_extraction_tail (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H N : ℕ)
    (t : (j : {j : ℤ // j ∉ bandSet H}) → (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) j.1) :
    Lp ℝ ∞ (volume.restrict
      ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))) :=
  compactPotentialLp (closedCube (0 : SpatialCoordinates d) 1 one_pos)
    ((∑ j ∈ Finset.Ico (H + 1) (N + 1), aux_lem_prefix_limit_atom_extraction_tailCoord H t j).restrict
        (closedCube (0 : SpatialCoordinates d) 1 one_pos) -
      ContinuousMap.const _ (Real.log (aux_lem_prefix_limit_atom_extraction_kappa M N)))

theorem aux_lem_prefix_limit_atom_extraction_V_continuous (H : ℕ) :
    Continuous (aux_lem_prefix_limit_atom_extraction_V (d := d) H) := by
  unfold aux_lem_prefix_limit_atom_extraction_V
  refine (ContinuousMap.continuous_restrict _).comp ?_
  exact continuous_finset_sum _ fun j _ =>
    aux_lem_prefix_limit_atom_extraction_bandCoord_continuous H j

theorem aux_lem_prefix_limit_atom_extraction_tail_continuous [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H N : ℕ) :
    Continuous (aux_lem_prefix_limit_atom_extraction_tail M H N) := by
  unfold aux_lem_prefix_limit_atom_extraction_tail
  refine aux_lem_prefix_limit_atom_extraction_cp_lipschitz.continuous.comp ?_
  refine Continuous.sub ?_ continuous_const
  refine (ContinuousMap.continuous_restrict _).comp ?_
  exact continuous_finset_sum _ fun j _ =>
    aux_lem_prefix_limit_atom_extraction_tailCoord_continuous H j

/-- The pointwise split of the unit-cube potential. -/
theorem aux_lem_prefix_limit_atom_extraction_pot_split
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H N : ℕ) (hHN : H ≤ N)
    (ω : ℤ → C(SpatialCoordinates d, ℝ)) :
    aux_lem_prefix_limit_atom_extraction_pot M N ω =
      compactPotentialLp (closedCube (0 : SpatialCoordinates d) 1 one_pos)
          (aux_lem_prefix_limit_atom_extraction_V H (fun j => ω j.1)) +
        aux_lem_prefix_limit_atom_extraction_tail M H N (fun j => ω j.1) := by
  unfold aux_lem_prefix_limit_atom_extraction_pot aux_lem_prefix_limit_atom_extraction_V
    aux_lem_prefix_limit_atom_extraction_tail
  rw [← compactPotentialLp_add]
  congr 1
  have hband : (∑ j ∈ Finset.range (H + 1),
      aux_lem_prefix_limit_atom_extraction_bandCoord H (fun i => ω i.1) j) =
      ∑ j ∈ Finset.range (H + 1), ω (-(j : ℤ)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    exact aux_lem_prefix_limit_atom_extraction_bandCoord_apply H ω j
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  have htail : (∑ j ∈ Finset.Ico (H + 1) (N + 1),
      aux_lem_prefix_limit_atom_extraction_tailCoord H (fun i => ω i.1) j) =
      ∑ j ∈ Finset.Ico (H + 1) (N + 1), ω (-(j : ℤ)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    exact aux_lem_prefix_limit_atom_extraction_tailCoord_apply H ω j
      (Nat.succ_le_iff.mp (Finset.mem_Ico.mp hj).1)
  rw [hband, htail]
  have hsum : (∑ j ∈ Finset.range (N + 1), ω (-(j : ℤ))) =
      (∑ j ∈ Finset.range (H + 1), ω (-(j : ℤ))) +
        ∑ j ∈ Finset.Ico (H + 1) (N + 1), ω (-(j : ℤ)) := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)).symm
  rw [hsum]
  ext x
  change (∑ j ∈ Finset.range (H + 1), ω (-(j : ℤ)) +
      ∑ j ∈ Finset.Ico (H + 1) (N + 1), ω (-(j : ℤ))) x.1 -
        Real.log (aux_lem_prefix_limit_atom_extraction_kappa M N) =
    (∑ j ∈ Finset.range (H + 1), ω (-(j : ℤ))) x.1 +
      ((∑ j ∈ Finset.Ico (H + 1) (N + 1), ω (-(j : ℤ))) x.1 -
        Real.log (aux_lem_prefix_limit_atom_extraction_kappa M N))
  rw [ContinuousMap.add_apply]
  ring

/-- **H3b.** The structural split required by `prop_response_compact`. -/
theorem aux_lem_prefix_limit_atom_extraction_split (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : ℕ) :
    ∃ (X : Type) (_ : MetricSpace X)
      (_ : TopologicalSpace.SeparableSpace X) (_ : MeasurableSpace X)
      (_ : BorelSpace X) (Q : Opens (SpatialCoordinates d))
      (R : Response Q)
      (V : ((j : bandSet H) → (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) j.1) → X)
      (psi : X → Potential Q)
      (tail : ℕ → ((j : {j : ℤ // j ∉ bandSet H}) →
        (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) j.1) → Potential Q),
      Measurable V ∧
      LipschitzWith 1 psi ∧
      (∀ N : ℕ, H ≤ N →
        Measurable
          (fun z : X × ((j : {j : ℤ // j ∉ bandSet H}) →
              (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) j.1) =>
            R.eval (psi z.1 + tail N z.2))) ∧
      (∀ N : ℕ, H ≤ N →
        ∀ ω : (j : ℤ) → (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) j,
          aux_lem_prefix_limit_atom_extraction_Rf M N ω =
            R.eval
              (psi (V (fun j => ω j.1)) +
                tail N (fun j => ω j.1))) := by
  let K := closedCube (0 : SpatialCoordinates d) 1 one_pos
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp K.isCompact
  letI mX : MeasurableSpace C(K, ℝ) := borel _
  haveI bX : BorelSpace C(K, ℝ) := ⟨rfl⟩
  refine ⟨C(K, ℝ), inferInstance, inferInstance, mX, bX,
    aux_lem_prefix_limit_atom_extraction_Q0 d, aux_lem_prefix_limit_atom_extraction_response,
    aux_lem_prefix_limit_atom_extraction_V H, compactPotentialLp K,
    fun N => aux_lem_prefix_limit_atom_extraction_tail M H N,
    (aux_lem_prefix_limit_atom_extraction_V_continuous H).measurable,
    aux_lem_prefix_limit_atom_extraction_cp_lipschitz, ?_, ?_⟩
  · intro N _
    refine Continuous.measurable ?_
    exact aux_lem_prefix_limit_atom_extraction_eval_continuous.comp
      ((aux_lem_prefix_limit_atom_extraction_cp_lipschitz.continuous.comp continuous_fst).add
        ((aux_lem_prefix_limit_atom_extraction_tail_continuous M H N).comp continuous_snd))
  · intro N hHN ω
    change aux_lem_prefix_limit_atom_extraction_eval
        (aux_lem_prefix_limit_atom_extraction_pot M N ω) = _
    rw [aux_lem_prefix_limit_atom_extraction_pot_split M H N hHN ω]
    rfl

end PaeSplit

section PaeQuad

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

section Linearity

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
  [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

theorem aux_lem_prefix_limit_atom_extraction_dc_add (a b : ℝ) :
    domainConstantL2 (Ω := Ω) (a + b) = domainConstantL2 a + domainConstantL2 b := by
  apply Lp.ext
  filter_upwards [domainConstantL2_coeFn (Ω := Ω) (a + b), domainConstantL2_coeFn (Ω := Ω) a,
    domainConstantL2_coeFn (Ω := Ω) b,
    Lp.coeFn_add (domainConstantL2 (Ω := Ω) a) (domainConstantL2 b)] with x h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3]

theorem aux_lem_prefix_limit_atom_extraction_dc_smul (c a : ℝ) :
    domainConstantL2 (Ω := Ω) (c * a) = c • domainConstantL2 a := by
  apply Lp.ext
  filter_upwards [domainConstantL2_coeFn (Ω := Ω) (c * a), domainConstantL2_coeFn (Ω := Ω) a,
    Lp.coeFn_smul c (domainConstantL2 (Ω := Ω) a)] with x h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2, smul_eq_mul]

theorem aux_lem_prefix_limit_atom_extraction_affineL2_add
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d))) (p q : Fin d → ℝ) :
    affineL2 hΩ (p + q) 0 = affineL2 hΩ p 0 + affineL2 hΩ q 0 := by
  apply Lp.ext
  filter_upwards [affineL2_coeFn hΩ (p + q) 0, affineL2_coeFn hΩ p 0, affineL2_coeFn hΩ q 0,
    Lp.coeFn_add (affineL2 hΩ p 0) (affineL2 hΩ q 0)] with x h1 h2 h3 h4
  rw [h1, h4, Pi.add_apply, h2, h3]
  simp [affineSlope_apply, Finset.sum_add_distrib, add_mul]

theorem aux_lem_prefix_limit_atom_extraction_affineL2_smul
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d))) (c : ℝ) (p : Fin d → ℝ) :
    affineL2 hΩ (c • p) 0 = c • affineL2 hΩ p 0 := by
  apply Lp.ext
  filter_upwards [affineL2_coeFn hΩ (c • p) 0, affineL2_coeFn hΩ p 0,
    Lp.coeFn_smul c (affineL2 hΩ p 0)] with x h1 h2 h3
  rw [h1, h3, Pi.smul_apply, h2]
  simp [affineSlope_apply, Finset.mul_sum, mul_assoc]

theorem aux_lem_prefix_limit_atom_extraction_affineSobolev_add
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d))) (p q : Fin d → ℝ) :
    affineSobolev hΩ (p + q) 0 = affineSobolev hΩ p 0 + affineSobolev hΩ q 0 := by
  apply Subtype.ext
  change affineSobolevData hΩ (p + q) 0 = affineSobolevData hΩ p 0 + affineSobolevData hΩ q 0
  unfold affineSobolevData
  refine Prod.ext (aux_lem_prefix_limit_atom_extraction_affineL2_add hΩ p q) ?_
  funext i
  exact aux_lem_prefix_limit_atom_extraction_dc_add (p i) (q i)

theorem aux_lem_prefix_limit_atom_extraction_affineSobolev_smul
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d))) (c : ℝ) (p : Fin d → ℝ) :
    affineSobolev hΩ (c • p) 0 = c • affineSobolev hΩ p 0 := by
  apply Subtype.ext
  change affineSobolevData hΩ (c • p) 0 = c • affineSobolevData hΩ p 0
  unfold affineSobolevData
  refine Prod.ext (aux_lem_prefix_limit_atom_extraction_affineL2_smul hΩ c p) ?_
  funext i
  exact aux_lem_prefix_limit_atom_extraction_dc_smul c (p i)

theorem aux_lem_prefix_limit_atom_extraction_neumannLoad_add (p q : Fin d → ℝ) :
    affineNeumannLoad (Ω := Ω) (p + q) = affineNeumannLoad p + affineNeumannLoad q := by
  ext g
  simp only [affineNeumannLoad, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, Pi.add_apply,
    aux_lem_prefix_limit_atom_extraction_dc_add, inner_add_left, Finset.sum_add_distrib]

theorem aux_lem_prefix_limit_atom_extraction_neumannLoad_smul (c : ℝ) (p : Fin d → ℝ) :
    affineNeumannLoad (Ω := Ω) (c • p) = c • affineNeumannLoad p := by
  ext g
  simp only [affineNeumannLoad, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, Pi.smul_apply, smul_eq_mul,
    aux_lem_prefix_limit_atom_extraction_dc_smul, real_inner_smul_left, Finset.mul_sum]

/-- The affine Dirichlet minimizer as a linear map of the slope (generic domain). -/
def aux_lem_prefix_limit_atom_extraction_vDg
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) : (Fin d → ℝ) →ₗ[ℝ] SobolevData Ω where
  toFun e := (dirichletMinimizer (killedResponseSpace hP) a (affineSobolev hΩ e 0)).val
  map_add' p q := by
    rw [aux_lem_prefix_limit_atom_extraction_affineSobolev_add, dirichletMinimizer_add]
    rfl
  map_smul' c p := by
    rw [aux_lem_prefix_limit_atom_extraction_affineSobolev_smul, dirichletMinimizer_smul]
    rfl

/-- The affine Neumann load as a linear map of the slope (generic domain). -/
def aux_lem_prefix_limit_atom_extraction_loadg
    (hP : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖) :
    (Fin d → ℝ) →ₗ[ℝ] ((meanZeroResponseSpace hP).space →L[ℝ] ℝ) where
  toFun e := (affineNeumannLoad e).comp (subspaceGradient (meanZeroSobolevGraph Ω))
  map_add' p q := by
    simp only [aux_lem_prefix_limit_atom_extraction_neumannLoad_add, ContinuousLinearMap.add_comp]
    ext v
    rfl
  map_smul' c p := by
    simp only [aux_lem_prefix_limit_atom_extraction_neumannLoad_smul,
      ContinuousLinearMap.smul_comp, RingHom.id_apply]
    ext v
    rfl

/-- The affine inverse-Neumann solution as a linear map of the slope (generic domain). -/
def aux_lem_prefix_limit_atom_extraction_vNg
    (hP : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) : (Fin d → ℝ) →ₗ[ℝ] (meanZeroResponseSpace hP).space :=
  (responseSolutionLinear (meanZeroResponseSpace hP) a).comp
    (aux_lem_prefix_limit_atom_extraction_loadg hP)

omit [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))] in
theorem aux_lem_prefix_limit_atom_extraction_qf_add_div (A B : Fin d → Fin d → ℝ) (V : ℝ)
    (e : Fin d → ℝ) :
    ((∑ i : Fin d, ∑ j : Fin d, e i * e j * A i j) +
        ∑ i : Fin d, ∑ j : Fin d, e i * e j * B i j) / V =
      aux_lem_prefix_limit_atom_extraction_qf (fun i j => (A i j + B i j) / V) e := by
  unfold aux_lem_prefix_limit_atom_extraction_qf
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- `(D_e + N_e)/(2V)` is the quadratic form of the matrix of polarized responses. -/
theorem aux_lem_prefix_limit_atom_extraction_Wg_qf
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hD : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (hN : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (V : ℝ) (e : Fin d → ℝ) :
    (affineDirichletResponse hΩ hD a e + affineInverseNeumannResponse hN a e) / V =
      aux_lem_prefix_limit_atom_extraction_qf (fun i j =>
        (sobolevCoefficientForm a (aux_lem_prefix_limit_atom_extraction_vDg hΩ hD a
            (aux_lem_prefix_limit_atom_extraction_eps i))
            (aux_lem_prefix_limit_atom_extraction_vDg hΩ hD a
              (aux_lem_prefix_limit_atom_extraction_eps j)) +
          responseForm (meanZeroResponseSpace hN) a
            (aux_lem_prefix_limit_atom_extraction_vNg hN a
              (aux_lem_prefix_limit_atom_extraction_eps i))
            (aux_lem_prefix_limit_atom_extraction_vNg hN a
              (aux_lem_prefix_limit_atom_extraction_eps j))) / V) e := by
  have hDe : affineDirichletResponse hΩ hD a e =
      sobolevCoefficientForm a (aux_lem_prefix_limit_atom_extraction_vDg hΩ hD a e)
        (aux_lem_prefix_limit_atom_extraction_vDg hΩ hD a e) := rfl
  have hNe : affineInverseNeumannResponse hN a e =
      responseForm (meanZeroResponseSpace hN) a (aux_lem_prefix_limit_atom_extraction_vNg hN a e)
        (aux_lem_prefix_limit_atom_extraction_vNg hN a e) := rfl
  have hDx : sobolevCoefficientForm a (aux_lem_prefix_limit_atom_extraction_vDg hΩ hD a e)
      (aux_lem_prefix_limit_atom_extraction_vDg hΩ hD a e) =
      ∑ i : Fin d, ∑ j : Fin d, e i * e j *
        sobolevCoefficientForm a (aux_lem_prefix_limit_atom_extraction_vDg hΩ hD a
          (aux_lem_prefix_limit_atom_extraction_eps i))
          (aux_lem_prefix_limit_atom_extraction_vDg hΩ hD a
            (aux_lem_prefix_limit_atom_extraction_eps j)) := by
    conv_lhs => rw [aux_lem_prefix_limit_atom_extraction_decomp e]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hNx : responseForm (meanZeroResponseSpace hN) a
      (aux_lem_prefix_limit_atom_extraction_vNg hN a e)
      (aux_lem_prefix_limit_atom_extraction_vNg hN a e) =
      ∑ i : Fin d, ∑ j : Fin d, e i * e j *
        responseForm (meanZeroResponseSpace hN) a
          (aux_lem_prefix_limit_atom_extraction_vNg hN a
            (aux_lem_prefix_limit_atom_extraction_eps i))
          (aux_lem_prefix_limit_atom_extraction_vNg hN a
            (aux_lem_prefix_limit_atom_extraction_eps j)) := by
    conv_lhs => rw [aux_lem_prefix_limit_atom_extraction_decomp e]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  exact (congrArg (fun t => t / V) (congrArg₂ (· + ·) (hDe.trans hDx) (hNe.trans hNx))).trans
    (aux_lem_prefix_limit_atom_extraction_qf_add_div
      (fun i j => sobolevCoefficientForm a (aux_lem_prefix_limit_atom_extraction_vDg hΩ hD a
          (aux_lem_prefix_limit_atom_extraction_eps i))
          (aux_lem_prefix_limit_atom_extraction_vDg hΩ hD a
            (aux_lem_prefix_limit_atom_extraction_eps j)))
      (fun i j => responseForm (meanZeroResponseSpace hN) a
          (aux_lem_prefix_limit_atom_extraction_vNg hN a
            (aux_lem_prefix_limit_atom_extraction_eps i))
          (aux_lem_prefix_limit_atom_extraction_vNg hN a
            (aux_lem_prefix_limit_atom_extraction_eps j))) V e)

end Linearity

variable {d : ℕ} [NeZero d]

/-- The symmetric coefficient matrix of `W`. -/
def aux_lem_prefix_limit_atom_extraction_Wpol
    (a : PositiveCoefficient (aux_lem_prefix_limit_atom_extraction_Q0 d)) (i j : Fin d) : ℝ :=
  (sobolevCoefficientForm a (aux_lem_prefix_limit_atom_extraction_vDg
      (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
      aux_lem_prefix_limit_atom_extraction_poincare.1 a
      (aux_lem_prefix_limit_atom_extraction_eps i))
      (aux_lem_prefix_limit_atom_extraction_vDg
        (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
        aux_lem_prefix_limit_atom_extraction_poincare.1 a
        (aux_lem_prefix_limit_atom_extraction_eps j)) +
    responseForm (meanZeroResponseSpace aux_lem_prefix_limit_atom_extraction_poincare.2) a
      (aux_lem_prefix_limit_atom_extraction_vNg aux_lem_prefix_limit_atom_extraction_poincare.2 a
        (aux_lem_prefix_limit_atom_extraction_eps i))
      (aux_lem_prefix_limit_atom_extraction_vNg aux_lem_prefix_limit_atom_extraction_poincare.2 a
        (aux_lem_prefix_limit_atom_extraction_eps j))) /
    (2 * volume.real ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)))

theorem aux_lem_prefix_limit_atom_extraction_Wpol_symm
    (a : PositiveCoefficient (aux_lem_prefix_limit_atom_extraction_Q0 d)) (i j : Fin d) :
    aux_lem_prefix_limit_atom_extraction_Wpol a i j =
      aux_lem_prefix_limit_atom_extraction_Wpol a j i := by
  unfold aux_lem_prefix_limit_atom_extraction_Wpol
  rw [sobolevCoefficientForm_symm, responseForm_symm]

/-- `W_e` is the quadratic form of `Wpol`. -/
theorem aux_lem_prefix_limit_atom_extraction_W_qf
    (a : PositiveCoefficient (aux_lem_prefix_limit_atom_extraction_Q0 d)) (e : Fin d → ℝ) :
    aux_lem_prefix_limit_atom_extraction_W a e =
      aux_lem_prefix_limit_atom_extraction_qf (aux_lem_prefix_limit_atom_extraction_Wpol a) e :=
  aux_lem_prefix_limit_atom_extraction_Wg_qf _ _ _ a _ e

/-- The response evaluation is `Φ` of the values `W_{ε_k + ε_l}`. -/
theorem aux_lem_prefix_limit_atom_extraction_eval_eq_Phi
    (g : Lp ℝ ∞ (volume.restrict
      ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)))) :
    aux_lem_prefix_limit_atom_extraction_eval g =
      aux_lem_prefix_limit_atom_extraction_Phi (fun k l =>
        aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g)
          (aux_lem_prefix_limit_atom_extraction_eps k +
            aux_lem_prefix_limit_atom_extraction_eps l)) := by
  simp only [aux_lem_prefix_limit_atom_extraction_W_qf]
  rw [aux_lem_prefix_limit_atom_extraction_Phi_eq _
    (aux_lem_prefix_limit_atom_extraction_Wpol_symm _)]
  unfold aux_lem_prefix_limit_atom_extraction_eval aux_lem_prefix_limit_atom_extraction_qsup
  simp only [aux_lem_prefix_limit_atom_extraction_W_qf]

omit [NeZero d] in
theorem aux_lem_prefix_limit_atom_extraction_qf_smul (P : Fin d → Fin d → ℝ) (c : ℝ)
    (e : Fin d → ℝ) :
    aux_lem_prefix_limit_atom_extraction_qf P (c • e) =
      c ^ 2 * aux_lem_prefix_limit_atom_extraction_qf P e := by
  unfold aux_lem_prefix_limit_atom_extraction_qf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- `W_u ≤ |u|² · eval`. -/
theorem aux_lem_prefix_limit_atom_extraction_W_le_sq_eval
    (g : Lp ℝ ∞ (volume.restrict
      ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)))) (u : Fin d → ℝ) :
    aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g) u ≤
      (∑ i : Fin d, (u i) ^ 2) * aux_lem_prefix_limit_atom_extraction_eval g := by
  set s := ∑ i : Fin d, (u i) ^ 2 with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => sq_nonneg (u i)
  rcases hs0.lt_or_eq with hpos | hzero
  · set r := Real.sqrt s with hr
    have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
    have hr2 : r ^ 2 = s := Real.sq_sqrt hs0
    let ehat : Fin d → ℝ := r⁻¹ • u
    have hehat : ∑ i : Fin d, (ehat i) ^ 2 = 1 := by
      simp only [ehat, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      rw [← hs, inv_pow, hr2, inv_mul_cancel₀ hpos.ne']
    have hu : u = r • ehat := by
      simp only [ehat, smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
    rw [aux_lem_prefix_limit_atom_extraction_W_qf, hu,
      aux_lem_prefix_limit_atom_extraction_qf_smul, hr2,
      ← aux_lem_prefix_limit_atom_extraction_W_qf]
    exact mul_le_mul_of_nonneg_left
      (aux_lem_prefix_limit_atom_extraction_W_le_eval g ⟨ehat, hehat⟩) hs0
  · have hu : u = 0 := by
      funext i
      have h := Finset.single_le_sum (fun k _ => sq_nonneg (u k)) (Finset.mem_univ i)
      rw [← hs, ← hzero] at h
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h (sq_nonneg _))
    rw [hu, aux_lem_prefix_limit_atom_extraction_W_qf]
    simp only [aux_lem_prefix_limit_atom_extraction_qf, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero]
    exact mul_nonneg hs0 (aux_lem_prefix_limit_atom_extraction_eval_nonneg g)

end PaeQuad

section PaeCarrier

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

variable {d : ℕ}

/-- The dilated-translated sample: layer `i` is `η_i(3^n x + x₀)`. -/
def aux_lem_prefix_limit_atom_extraction_dil (n : ℕ) (x0 : Vec d)
    (η : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d :=
  fun i => SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale ((3 : ℝ) ^ n)
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate x0 (η i))

theorem aux_lem_prefix_limit_atom_extraction_aCutoff_dil
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (x0 : Vec d)
    (η : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (x : Vec d) :
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (aux_lem_prefix_limit_atom_extraction_dil n x0 η) x =
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample x0 η) ((3 : ℝ) ^ n • x) := by
  simp only [SubdiffusiveProcess.Frozen.Assumptions.aCutoff, aux_lem_prefix_limit_atom_extraction_dil,
    translatePotentialSample, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply,
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply]

/-- Step 1: the eta-cube response equals the unit-cube response of the dilated sample. -/
theorem aux_lem_prefix_limit_atom_extraction_J_rechart
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ) (x0 : Vec d)
    (η : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d) (p q : Vec d) :
    Homogenization.Book.Ch02.responseJ
        (Homogenization.Book.Ch02.cubeDomain (originCube d (n : ℤ)))
        ((aCutoffFamily M n (translatePotentialSample x0 η)).coeffOn (originCube d (n : ℤ))) p q =
      Homogenization.Book.Ch02.responseJ
        (Homogenization.Book.Ch02.cubeDomain (originCube d 0))
        ((aCutoffCoeffOnData M n (aux_lem_prefix_limit_atom_extraction_dil n x0 η)
          (Homogenization.Book.Ch02.cubeDomain (originCube d 0))).toCoeffOn) p q := by
  refine aux_rechart_responseJ_eq _ _
    (scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample x0 η)))
    (Filter.EventuallyEq.refl _ _) ?_ p q
  refine Eventually.of_forall fun x => ?_
  have hc : cubeCenter (originCube d (n : ℤ)) = 0 := by
    funext i
    simp [cubeCenter, originCube]
  change scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n
      (aux_lem_prefix_limit_atom_extraction_dil n x0 η)) x =
    scalarCoeffField (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n (translatePotentialSample x0 η))
      (cubeCenter (originCube d (n : ℤ)) + cubeScaleFactor (originCube d (n : ℤ)) • x)
  rw [hc, zero_add, cubeScaleFactor_originCube, zpow_natCast]
  simp only [scalarCoeffField, aux_lem_prefix_limit_atom_extraction_aCutoff_dil]

theorem aux_lem_prefix_limit_atom_extraction_Q0_eq :
    ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)) =
      ((Homogenization.Book.Ch02.cubeDomain (originCube d 0) :
        Homogenization.Book.Ch02.Domain d) : Set (Homogenization.Vec d)) := by
  rw [Homogenization.Book.Ch02.cubeDomain_coe, centeredCube_eq_pi]
  ext x
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Ioo, forall_const,
    Homogenization.mem_openCubeSet_originCube_iff, zpow_zero, mul_one, Pi.zero_apply,
    zero_sub, zero_add]

/-- Step 2: on the unit cube the normalized response is `W_e - 1`. -/
theorem aux_lem_prefix_limit_atom_extraction_J_eq_W [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (n : ℕ)
    (dil : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (g : Lp ℝ ∞ (volume.restrict
      ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d))))
    (hg : ∀ᵐ x ∂volume.restrict
      ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)),
      Real.exp (g x) = SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n dil x / ahom M n)
    (e : Homogenization.Vec d) (he : Homogenization.vecNormSq e = 1) :
    Homogenization.Book.Ch02.responseJ
        (Homogenization.Book.Ch02.cubeDomain (originCube d 0))
        ((aCutoffCoeffOnData M n dil (Homogenization.Book.Ch02.cubeDomain (originCube d 0))).toCoeffOn)
        ((Real.sqrt (ahom M n))⁻¹ • e) (Real.sqrt (ahom M n) • e) =
      aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g) e - 1 := by
  have haQ : (((expPotentialCoefficient g).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict ((aux_lem_prefix_limit_atom_extraction_Q0 d :
        Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))]
        fun x => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n dil x / ahom M n) := by
    filter_upwards [expPotentialCoefficient_coeFn g, hg] with x h1 h2
    rw [h1, h2]
  rw [responseJ_eq_affineDiagonalDefect (Homogenization.Book.Ch02.cubeDomain (originCube d 0))
    (aux_lem_prefix_limit_atom_extraction_Q0 d) aux_lem_prefix_limit_atom_extraction_Q0_eq
    (ahom_pos M n) (aCutoffCoeffOnData M n dil _)
    (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
    (centeredCube_volume_pos (0 : SpatialCoordinates d) one_pos)
    aux_lem_prefix_limit_atom_extraction_poincare.1 aux_lem_prefix_limit_atom_extraction_poincare.2
    (expPotentialCoefficient g) haQ e he]
  have hsq : ∑ i : Fin d, (e i) ^ 2 = 1 := by
    rw [← he, Homogenization.vecNormSq, Homogenization.vecDot]
    exact Finset.sum_congr rfl fun i _ => sq (e i)
  unfold affineDiagonalDefect
  rw [hsq]
  rfl

/-- `log κ_n = (n+1)τ² + log ahom_n`. -/
theorem aux_lem_prefix_limit_atom_extraction_log_kappa (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n : ℕ) :
    Real.log (aux_lem_prefix_limit_atom_extraction_kappa M n) =
      ((n : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P + Real.log (ahom M n) := by
  unfold aux_lem_prefix_limit_atom_extraction_kappa
  rw [Real.log_mul (Real.exp_pos _).ne' (ahom_pos M n).ne', Real.log_exp]

/-- The unit-cube potential is the restricted continuous potential, a.e. on `Q₀`. -/
theorem aux_lem_prefix_limit_atom_extraction_pot_ae (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n : ℕ) (ω' : BilateralField d) :
    ∀ᵐ x ∂volume.restrict ((aux_lem_prefix_limit_atom_extraction_Q0 d :
        Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
      aux_lem_prefix_limit_atom_extraction_pot M n ω' x =
        (∑ j ∈ Finset.range (n + 1), ω' (-(j : ℤ)) x) -
          Real.log (aux_lem_prefix_limit_atom_extraction_kappa M n) := by
  have h := compactPotentialLp_on_domain (Ω := aux_lem_prefix_limit_atom_extraction_Q0 d)
    (closedCube (0 : SpatialCoordinates d) 1 one_pos)
    (centeredCube_subset_closedCube (0 : SpatialCoordinates d) one_pos)
    ((∑ j ∈ Finset.range (n + 1), ω' (-(j : ℤ))).restrict
        (closedCube (0 : SpatialCoordinates d) 1 one_pos) -
      ContinuousMap.const _ (Real.log (aux_lem_prefix_limit_atom_extraction_kappa M n)))
  filter_upwards [h, ae_restrict_mem (aux_lem_prefix_limit_atom_extraction_Q0 d).isOpen.measurableSet]
    with x hx hmem
  unfold aux_lem_prefix_limit_atom_extraction_pot
  rw [hx hmem]
  show (∑ j ∈ Finset.range (n + 1), ω' (-(j : ℤ))) x -
      Real.log (aux_lem_prefix_limit_atom_extraction_kappa M n) = _
  rw [ContinuousMap.sum_apply]

/-- Step 3, pointwise: on the `hEta` event the dilated layers are the relabelled layers. -/
theorem aux_lem_prefix_limit_atom_extraction_layer_eq
    (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (ω : BilateralField d)
    (hω : ∀ (N i : ℕ) (y : Vec d), eta N ω i y = ω ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (l : ℤ) (y : Vec d) (N n : ℕ) (hn : (n : ℤ) = l + N) (x : Vec d) (i : ℕ) :
    aux_lem_prefix_limit_atom_extraction_dil n ((3 : ℝ) ^ N • y) (eta N ω) i x =
      aux_lem_prefix_limit_atom_extraction_shift l y ω ((i : ℤ) - n) x := by
  simp only [aux_lem_prefix_limit_atom_extraction_dil,
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply,
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.translate_apply, hω,
    aux_lem_prefix_limit_atom_extraction_shift, aux_lem_prefix_limit_atom_extraction_affine,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  have hidx : (i : ℤ) - (N : ℤ) = (i : ℤ) - (n : ℤ) + l := by omega
  rw [hidx]
  congr 1
  have h3 : (3 : ℝ) ≠ 0 := by norm_num
  have hl : (l : ℤ) = (n : ℤ) - N := by omega
  have e1 : (3 : ℝ) ^ (-(N : ℤ)) * (3 : ℝ) ^ n = (3 : ℝ) ^ l := by
    rw [← zpow_natCast, ← zpow_add₀ h3, hl]
    congr 1
    ring
  have e2 : (3 : ℝ) ^ (-(N : ℤ)) * (3 : ℝ) ^ N = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ h3]
    simp
  ext k
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [mul_add, ← mul_assoc, ← mul_assoc, e1, e2, one_mul, add_comm]

/-- Step 4: `ENNReal` supremum versus real supremum. -/
theorem aux_lem_prefix_limit_atom_extraction_sSup_toReal [NeZero d]
    (F : Homogenization.Vec d → ℝ)
    (hF0 : ∀ e, Homogenization.vecNormSq e = 1 → 0 ≤ F e)
    (hbdd : BddAbove (Set.range fun e : {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1} =>
      F (e : Fin d → ℝ))) :
    (sSup {v : ℝ≥0∞ | ∃ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 ∧
        v = ENNReal.ofReal (F e)}).toReal =
      ⨆ e : {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1}, F (e : Fin d → ℝ) := by
  have hiff : ∀ e : Homogenization.Vec d,
      Homogenization.vecNormSq e = 1 ↔ ∑ i : Fin d, (e i) ^ 2 = 1 := by
    intro e
    rw [Homogenization.vecNormSq, Homogenization.vecDot]
    simp only [sq]
  set S := ⨆ e : {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1}, F (e : Fin d → ℝ) with hS
  obtain ⟨e0⟩ := (inferInstance : Nonempty {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1})
  have hS0 : 0 ≤ S := (hF0 _ ((hiff _).mpr e0.2)).trans (le_ciSup hbdd e0)
  have hle : sSup {v : ℝ≥0∞ | ∃ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 ∧
      v = ENNReal.ofReal (F e)} ≤ ENNReal.ofReal S := by
    apply sSup_le
    rintro v ⟨e, he, rfl⟩
    exact ENNReal.ofReal_le_ofReal (le_ciSup hbdd ⟨e, (hiff e).mp he⟩)
  have hne : sSup {v : ℝ≥0∞ | ∃ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 ∧
      v = ENNReal.ofReal (F e)} ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  apply le_antisymm
  · exact (ENNReal.toReal_le_toReal hne ENNReal.ofReal_ne_top).mpr hle |>.trans
      (by rw [ENNReal.toReal_ofReal hS0])
  · apply ciSup_le
    intro e
    have h1 : ENNReal.ofReal (F (e : Fin d → ℝ)) ≤ sSup {v : ℝ≥0∞ | ∃ e : Homogenization.Vec d,
        Homogenization.vecNormSq e = 1 ∧ v = ENNReal.ofReal (F e)} :=
      le_sSup ⟨e, (hiff _).mpr e.2, rfl⟩
    have h2 := ENNReal.toReal_mono hne h1
    rwa [ENNReal.toReal_ofReal (hF0 _ ((hiff _).mpr e.2))] at h2

/-- **H1.** Pathwise carrier identity: on the `hEta` event the literal atom is the unit-cube
zero-infrared response of the relabelled field, minus one. -/
theorem aux_lem_prefix_limit_atom_extraction_carrier [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d)
    (hEta : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y))
    (l : ℤ) (y : Vec d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, 0 ≤ l + (N : ℤ) →
      aux_lem_prefix_limit_atom_extraction_atom M eta N l y omega =
        aux_lem_prefix_limit_atom_extraction_Rf M (l + (N : ℤ)).toNat
          (aux_lem_prefix_limit_atom_extraction_shift l y omega) - 1 := by
  filter_upwards [hEta] with ω hω
  intro N hN
  set n : ℕ := (l + (N : ℤ)).toNat with hn_def
  have hn : (n : ℤ) = l + N := Int.toNat_of_nonneg hN
  set ω' := aux_lem_prefix_limit_atom_extraction_shift l y ω with hω'
  set g := aux_lem_prefix_limit_atom_extraction_pot M n ω' with hg_def
  set x0 : Vec d := (3 : ℝ) ^ N • y with hx0
  set dil := aux_lem_prefix_limit_atom_extraction_dil n x0 (eta N ω) with hdil
  -- the normalized coefficient identity on `Q₀`
  have hsum : ∀ x : Vec d, ∑ i ∈ Finset.range (n + 1), dil i x =
      ∑ j ∈ Finset.range (n + 1), ω' (-(j : ℤ)) x := by
    intro x
    rw [← Finset.sum_range_reflect (fun j => ω' (-(j : ℤ)) x) (n + 1)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hidx : ((i : ℤ) - (n : ℤ)) = -(((n + 1 - 1 - i : ℕ)) : ℤ) := by omega
    rw [hdil, aux_lem_prefix_limit_atom_extraction_layer_eq eta ω hω l y N n hn x i, hidx]
  have hg : ∀ᵐ x ∂volume.restrict ((aux_lem_prefix_limit_atom_extraction_Q0 d :
      Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
      Real.exp (g x) = SubdiffusiveProcess.Frozen.Assumptions.aCutoff M n dil x / ahom M n := by
    filter_upwards [aux_lem_prefix_limit_atom_extraction_pot_ae M n ω'] with x hx
    rw [hx, aux_lem_prefix_limit_atom_extraction_log_kappa, SubdiffusiveProcess.Frozen.Assumptions.aCutoff,
      Finset.sum_sub_distrib, hsum x, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Real.exp_sub, Real.exp_add, Real.exp_log (ahom_pos M n), Real.exp_sub]
    push_cast
    have hα := (ahom_pos M n).ne'
    have hE := (Real.exp_pos (((n : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)).ne'
    field_simp
  -- the per-direction identity
  have hJ : ∀ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 →
      section6Response M n n (eta N ω) x0 e =
        aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g) e - 1 := by
    intro e he
    unfold section6Response paperScalarProbe J
    rw [aux_lem_prefix_limit_atom_extraction_J_rechart M n x0 (eta N ω)]
    exact aux_lem_prefix_limit_atom_extraction_J_eq_W M n dil g hg e he
  -- unfold the atom
  have hatom : aux_lem_prefix_limit_atom_extraction_atom M eta N l y ω =
      (aux_psf_Jval M n (eta N ω) x0).toReal := by
    simp only [aux_lem_prefix_limit_atom_extraction_atom, if_pos hN]
    rfl
  rw [hatom]
  have hset : {v : ℝ≥0∞ | ∃ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 ∧
      v = ENNReal.ofReal (section6Response M n n (eta N ω) x0 e)} =
      {v : ℝ≥0∞ | ∃ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 ∧
        v = ENNReal.ofReal (aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g) e -
          1)} := by
    ext v
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, by rw [hJ e he]⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨e, he, by rw [hJ e he]⟩
  have hdef : aux_psf_Jval M n (eta N ω) x0 = sSup {v : ℝ≥0∞ | ∃ e : Homogenization.Vec d,
      Homogenization.vecNormSq e = 1 ∧
        v = ENNReal.ofReal (section6Response M n n (eta N ω) x0 e)} := rfl
  have hiff : ∀ e : Homogenization.Vec d,
      Homogenization.vecNormSq e = 1 ↔ ∑ i : Fin d, (e i) ^ 2 = 1 := by
    intro e
    rw [Homogenization.vecNormSq, Homogenization.vecDot]
    simp only [sq]
  have hF0 : ∀ e : Homogenization.Vec d, Homogenization.vecNormSq e = 1 →
      0 ≤ aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g) e - 1 := by
    intro e he
    have h := affineDiagonalDefect_nonneg
      (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos)
      (centeredCube_volume_pos (0 : SpatialCoordinates d) one_pos)
      aux_lem_prefix_limit_atom_extraction_poincare.1 aux_lem_prefix_limit_atom_extraction_poincare.2
      (expPotentialCoefficient g) e
    unfold affineDiagonalDefect at h
    rw [(hiff e).mp he] at h
    exact h
  have hbdd : BddAbove (Set.range fun e : {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1} =>
      aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g) (e : Fin d → ℝ) - 1) := by
    obtain ⟨B, hB⟩ := aux_lem_prefix_limit_atom_extraction_bdd g
    exact ⟨B - 1, by rintro _ ⟨e, rfl⟩; linarith [hB ⟨e, rfl⟩]⟩
  rw [hdef, hset, aux_lem_prefix_limit_atom_extraction_sSup_toReal _ hF0 hbdd]
  -- `⨆ (W_e - 1) = eval - 1`
  change _ = aux_lem_prefix_limit_atom_extraction_eval g - 1
  apply le_antisymm
  · apply ciSup_le
    intro e
    linarith [aux_lem_prefix_limit_atom_extraction_W_le_eval g e]
  · have h : aux_lem_prefix_limit_atom_extraction_eval g ≤
        (⨆ e : {e : Fin d → ℝ // ∑ i : Fin d, (e i) ^ 2 = 1},
          (aux_lem_prefix_limit_atom_extraction_W (expPotentialCoefficient g) (e : Fin d → ℝ) - 1)) +
          1 := by
      apply ciSup_le
      intro e
      linarith [le_ciSup hbdd e]
    linarith

end PaeCarrier

section PaeMoments

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

/-- **H3a (typed hole).** Uniform `L²` bound of the unit-cube responses. -/
theorem aux_lem_prefix_limit_atom_extraction_moments (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    ∃ delta1 : ℝ, 0 < delta1 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta1 →
    ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
    (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      ∃ B : ℝ≥0∞, B ≠ ∞ ∧ ∀ N : ℕ,
        MemLp (aux_lem_prefix_limit_atom_extraction_Rf M N) 2 (chaosSampleLaw M).toMeasure ∧
        eLpNorm (aux_lem_prefix_limit_atom_extraction_Rf M N) 2
          (chaosSampleLaw M).toMeasure ≤ B := by
  obtain ⟨c, C, _hc, _hC, hbank⟩ := aux_psf_exists_Jval_spatial_moment_small_disorder d
  obtain ⟨δ0, hδ0, hδ⟩ := hbank 2 (by norm_num)
  refine ⟨δ0, hδ0, ?_⟩
  intro M hM eta hEta
  have hMpos : 0 < M.delta := M.shellPrefix.delta_pos
  set P := (chaosSampleLaw M).toMeasure with hP
  set B0 : ℝ≥0∞ := ENNReal.ofReal (C * 2 * Real.log (2 + 2) * M.delta ^ 2) with hB0
  have hone_fin : eLpNorm (fun _ : BilateralField d => (1 : ℝ)) 2 P < ∞ :=
    (memLp_const (1 : ℝ)).eLpNorm_lt_top
  refine ⟨B0 + eLpNorm (fun _ : BilateralField d => (1 : ℝ)) 2 P,
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hone_fin.ne⟩, ?_⟩
  intro N
  have hshift0 : ∀ ω : BilateralField d, aux_lem_prefix_limit_atom_extraction_shift 0 0 ω = ω := by
    intro ω
    funext c
    ext x
    simp [aux_lem_prefix_limit_atom_extraction_shift, aux_lem_prefix_limit_atom_extraction_affine]
  have hcar := aux_lem_prefix_limit_atom_extraction_carrier M eta hEta 0 0
  have hatom : ∀ ω, aux_lem_prefix_limit_atom_extraction_atom M eta N 0 0 ω =
      (aux_psf_Jval M N (eta N ω) 0).toReal := by
    intro ω
    simp [aux_lem_prefix_limit_atom_extraction_atom]
  have hae : aux_lem_prefix_limit_atom_extraction_Rf M N =ᵐ[P]
      fun ω => (aux_psf_Jval M N (eta N ω) 0).toReal + 1 := by
    filter_upwards [hcar] with ω h
    have h' := h N (by simp)
    rw [hshift0, hatom] at h'
    simp only [zero_add, Int.toNat_natCast] at h'
    linarith
  have hlaw : Measure.map (eta N) P = M.P.toMeasure := prefix_eta_law M eta hEta N
  have hetam : AEMeasurable (eta N) P := prefix_eta_aemeasurable M eta hEta N
  have hfm : Measurable (fun η : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      (aux_psf_Jval M N η 0).toReal) :=
    (aux_lem_prefix_limit_actual_J_meas M N 0).ennreal_toReal
  have hA : eLpNorm (fun ω => (aux_psf_Jval M N (eta N ω) 0).toReal) 2 P ≤ B0 := by
    have heq : (fun ω => (aux_psf_Jval M N (eta N ω) 0).toReal) =
        (fun η : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => (aux_psf_Jval M N η 0).toReal) ∘
          eta N := rfl
    rw [heq, ← eLpNorm_map_measure (hlaw ▸ hfm.aestronglyMeasurable) hetam, hlaw]
    have h := hδ M hMpos hM N 0
    have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
    rw [h2] at h
    exact h
  have hAm : AEStronglyMeasurable (fun ω => (aux_psf_Jval M N (eta N ω) 0).toReal) P :=
    (hfm.comp_aemeasurable hetam).aestronglyMeasurable
  have hbound : eLpNorm (aux_lem_prefix_limit_atom_extraction_Rf M N) 2 P ≤
      B0 + eLpNorm (fun _ : BilateralField d => (1 : ℝ)) 2 P := by
    rw [eLpNorm_congr_ae hae]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    gcongr
  refine ⟨hbound.trans_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hone_fin⟩), hbound⟩

end PaeMoments

section PaeCanon

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

variable {d : ℕ}

/-- The canonical cutoff samples of the common scale coupling. -/
def aux_lem_prefix_limit_atom_extraction_etaC
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (N : ℕ) (ω : BilateralField d) :
    SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d :=
  fun i => aux_lem_crossing_unforget
    (SubdiffusiveProcess.layerScaling d (N : ℤ) (ω ((i : ℤ) - (N : ℤ))))

theorem aux_lem_prefix_limit_atom_extraction_layerScaling_forget (c : ℤ)
    (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    SubdiffusiveProcess.layerScaling d c (aux_lem_crossing_forget g) =
      aux_lem_crossing_forget
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale ((3 : ℝ) ^ (-c)) g) := by
  apply ContinuousMap.ext
  intro x
  rfl

/-- Almost surely every coordinate of the chaos sample is a potential field. -/
theorem aux_lem_prefix_limit_atom_extraction_range_forget_ae
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∀ᵐ ω ∂(chaosSampleLaw M).toMeasure, ∀ c : ℤ,
      ω c ∈ Set.range (aux_lem_crossing_forget (d := d)) := by
  rw [ae_all_iff]
  intro c
  set ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) := chaosRootFieldLaw M
  have hrange : MeasurableSet (Set.range (aux_lem_crossing_forget (d := d))) :=
    aux_lem_crossing_measurableEmbedding_forget.measurableSet_range
  have hmeas : MeasurableSet {ω : BilateralField d |
      ω c ∈ Set.range (aux_lem_crossing_forget (d := d))} :=
    (measurable_pi_apply c) hrange
  rw [ae_iff, ← Set.compl_setOf, prob_compl_eq_zero_iff hmeas]
  change (Measure.infinitePi (fun j : ℤ =>
      (scaledLayerLaw d ν j : Measure C(SpatialCoordinates d, ℝ))))
    ((fun ω : BilateralField d => ω c) ⁻¹' Set.range aux_lem_crossing_forget) = 1
  rw [← Measure.map_apply (measurable_pi_apply c) hrange, Measure.infinitePi_map_eval]
  change (Measure.map (SubdiffusiveProcess.layerScaling d c)
      (Measure.map aux_lem_crossing_forget
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)) _ = 1
  rw [Measure.map_map (SubdiffusiveProcess.layerScaling d c).continuous.measurable
      aux_lem_crossing_measurable_forget,
    Measure.map_apply ((SubdiffusiveProcess.layerScaling d c).continuous.measurable.comp
      aux_lem_crossing_measurable_forget) hrange]
  have : (SubdiffusiveProcess.layerScaling d c ∘ aux_lem_crossing_forget) ⁻¹'
      Set.range aux_lem_crossing_forget = Set.univ := by
    ext g
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨_, (aux_lem_prefix_limit_atom_extraction_layerScaling_forget c g).symm⟩
  rw [this, measure_univ]

/-- The canonical cutoff samples satisfy the coupling identity almost surely. -/
theorem aux_lem_prefix_limit_atom_extraction_etaC_spec
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), aux_lem_prefix_limit_atom_extraction_etaC N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y) := by
  filter_upwards [aux_lem_prefix_limit_atom_extraction_range_forget_ae M] with ω hω
  intro N i y
  obtain ⟨g, hg⟩ := hω ((i : ℤ) - (N : ℤ))
  have h := aux_lem_prefix_limit_atom_extraction_layerScaling_forget (N : ℤ) g
  simp only [aux_lem_prefix_limit_atom_extraction_etaC, ← hg, h,
    aux_lem_crossing_unforget_forget]
  rfl

/-- Uniform `L^q` bounds of the unit-cube responses, for every `q ≥ 1`. -/
theorem aux_lem_prefix_limit_atom_extraction_moments_q (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta1 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
        MemLp (aux_lem_prefix_limit_atom_extraction_Rf M N) (ENNReal.ofReal q)
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (aux_lem_prefix_limit_atom_extraction_Rf M N) (ENNReal.ofReal q)
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B := by
  obtain ⟨c, C, _hc, _hC, hbank⟩ := aux_psf_exists_Jval_spatial_moment_small_disorder d
  obtain ⟨δ0, hδ0, hδ⟩ := hbank q hq
  refine ⟨δ0, hδ0, ?_⟩
  intro M hM
  have hMpos : 0 < M.delta := M.shellPrefix.delta_pos
  set P := (chaosSampleLaw M).toMeasure with hP
  set eta := aux_lem_prefix_limit_atom_extraction_etaC (d := d) with heta
  have hEta := aux_lem_prefix_limit_atom_extraction_etaC_spec M
  have hq0 : ENNReal.ofReal q ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    linarith
  set B1 : ℝ := C * q * Real.log (2 + q) * M.delta ^ 2 with hB1
  set E1 : ℝ≥0∞ := eLpNorm (fun _ : BilateralField d => (1 : ℝ)) (ENNReal.ofReal q) P with hE1
  have hE1fin : E1 < ∞ := (memLp_const (1 : ℝ)).eLpNorm_lt_top
  refine ⟨max B1 0 + E1.toReal, add_nonneg (le_max_right _ _) ENNReal.toReal_nonneg, ?_⟩
  intro N
  have hshift0 : ∀ ω : BilateralField d, aux_lem_prefix_limit_atom_extraction_shift 0 0 ω = ω := by
    intro ω
    funext c
    ext x
    simp [aux_lem_prefix_limit_atom_extraction_shift, aux_lem_prefix_limit_atom_extraction_affine]
  have hcar := aux_lem_prefix_limit_atom_extraction_carrier M eta hEta 0 0
  have hatom : ∀ ω, aux_lem_prefix_limit_atom_extraction_atom M eta N 0 0 ω =
      (aux_psf_Jval M N (eta N ω) 0).toReal := by
    intro ω
    simp [aux_lem_prefix_limit_atom_extraction_atom]
  have hae : aux_lem_prefix_limit_atom_extraction_Rf M N =ᵐ[P]
      fun ω => (aux_psf_Jval M N (eta N ω) 0).toReal + 1 := by
    filter_upwards [hcar] with ω h
    have h' := h N (by simp)
    rw [hshift0, hatom] at h'
    simp only [zero_add, Int.toNat_natCast] at h'
    linarith
  have hlaw : Measure.map (eta N) P = M.P.toMeasure := prefix_eta_law M eta hEta N
  have hetam : AEMeasurable (eta N) P := prefix_eta_aemeasurable M eta hEta N
  have hfm : Measurable (fun η : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d =>
      (aux_psf_Jval M N η 0).toReal) :=
    (aux_lem_prefix_limit_actual_J_meas M N 0).ennreal_toReal
  have hA : eLpNorm (fun ω => (aux_psf_Jval M N (eta N ω) 0).toReal) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal B1 := by
    have heq : (fun ω => (aux_psf_Jval M N (eta N ω) 0).toReal) =
        (fun η : SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d => (aux_psf_Jval M N η 0).toReal) ∘
          eta N := rfl
    rw [heq, ← eLpNorm_map_measure (hlaw ▸ hfm.aestronglyMeasurable) hetam, hlaw]
    exact hδ M hMpos hM N 0
  have hAm : AEStronglyMeasurable (fun ω => (aux_psf_Jval M N (eta N ω) 0).toReal) P :=
    (hfm.comp_aemeasurable hetam).aestronglyMeasurable
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hq
  have hbound : eLpNorm (aux_lem_prefix_limit_atom_extraction_Rf M N) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal (max B1 0 + E1.toReal) := by
    rw [eLpNorm_congr_ae hae]
    refine (eLpNorm_add_le hq1).trans ?_
    rw [ENNReal.ofReal_add (le_max_right _ _) ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hE1fin.ne]
    gcongr
    exact hA.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  exact ⟨hbound.trans_lt ENNReal.ofReal_lt_top, hbound⟩

end PaeCanon

section PaeCrux

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

/-- **Band error by single-layer increments.** A variable read only from the coordinates
`-N, …, 0` has band error at `H ≤ N` at most the sum of its single-layer increments over
`H < k ≤ N`. -/
theorem aux_lem_prefix_limit_atom_extraction_band_le_sum {X : Type} [MeasurableSpace X]
    (laws : ℤ → Measure X) [∀ j, IsProbabilityMeasure (laws j)]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (f : (ℤ → X) → ℝ) (hf : Integrable f (Measure.infinitePi laws)) (H N : ℕ)
    (hdet : ∀ ω₁ ω₂ : ℤ → X, (∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ 0 → ω₁ j = ω₂ j) → f ω₁ = f ω₂)
    (c : ℕ → ℝ≥0∞)
    (hstep : ∀ k : ℕ, H < k → k ≤ N →
      eLpNorm (fun q : (ℤ → X) × (ℤ → X) =>
          f q.1 - f (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))) p
        ((Measure.infinitePi laws).prod (Measure.infinitePi laws)) ≤ c k) :
    eLpNorm (fun ω => f ω - (Measure.infinitePi laws)[f | bandSigma (fun _ : ℤ => X) H] ω) p
        (Measure.infinitePi laws) ≤ ∑ k ∈ Finset.Ioc H N, c k := by
  refine (aux_lem_prefix_limit_atom_extraction_tele_band_split laws H hp hp_top hf).trans ?_
  have hcoarse : (fun q : (ℤ → X) × (ℤ → X) =>
      f q.1 - f (fun j => if (H : ℤ) < j then q.2 j else q.1 j)) = 0 := by
    funext q
    rw [hdet q.1 (fun j => if (H : ℤ) < j then q.2 j else q.1 j) (fun j _ hj0 => by
      show q.1 j = if (H : ℤ) < j then q.2 j else q.1 j
      rw [if_neg (by omega)])]
    simp
  rw [hcoarse, eLpNorm_zero, zero_add]
  exact aux_lem_prefix_limit_atom_extraction_tele_fine_telescope laws hp f hf.aestronglyMeasurable
    Set.univ (ae_of_all _ fun _ => Set.mem_univ _) H N
    (fun ω₁ _ ω₂ _ h => hdet ω₁ ω₂ fun j hj _ => h j hj) c hstep

/-- The geometric tail `Σ_{H < k ≤ N} 3^{-ak} ≤ (1 - 3^{-a})⁻¹ 3^{-aH}`. -/
theorem aux_lem_prefix_limit_atom_extraction_geom (a : ℝ) (ha : 0 < a) (H N : ℕ) :
    ∑ k ∈ Finset.Ioc H N, (3 : ℝ) ^ (-(a * (k : ℝ))) ≤
      (1 - (3 : ℝ) ^ (-a))⁻¹ * (3 : ℝ) ^ (-(a * (H : ℝ))) := by
  set r : ℝ := (3 : ℝ) ^ (-a) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpow : ∀ k : ℕ, (3 : ℝ) ^ (-(a * (k : ℝ))) = r ^ k := by
    intro k
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    ring_nf
  simp only [hpow]
  have hIoc : Finset.Ioc H N = Finset.Ico (H + 1) (N + 1) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hIoc]
  calc ∑ k ∈ Finset.Ico (H + 1) (N + 1), r ^ k ≤ r ^ (H + 1) / (1 - r) :=
        geom_sum_Ico_le_of_lt_one hr0 hr1
    _ ≤ r ^ H / (1 - r) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hr0 _) hr1.le
    _ = (1 - r)⁻¹ * r ^ H := by rw [div_eq_inv_mul]

section Continuity

variable {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
  [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]

theorem aux_lem_prefix_limit_atom_extraction_affineD_continuous
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d)))
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (u : Fin d → ℝ) :
    Continuous (fun g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) =>
      affineDirichletResponse hΩ hP (expPotentialCoefficient g) u) :=
  continuous_dirichletResponse_potential _ _

theorem aux_lem_prefix_limit_atom_extraction_affineN_continuous
    (hP : ∃ K : ℝ≥0, ∀ z : meanZeroSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (meanZeroSobolevGraph Ω) z‖)
    (u : Fin d → ℝ) :
    Continuous (fun g : Lp ℝ ∞ (volume.restrict (Ω : Set (SpatialCoordinates d))) =>
      affineInverseNeumannResponse hP (expPotentialCoefficient g) u) :=
  continuous_inverseResponse_potential _ _

end Continuity

variable {d : ℕ} [NeZero d]

/-- The unit-cube affine Dirichlet response of the zero-infrared coefficient at slope `u`. -/
def aux_lem_prefix_limit_atom_extraction_Dz (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (u : Fin d → ℝ) (N : ℕ) (omega : BilateralField d) : ℝ :=
  aux_lem_prefix_limit_atom_extraction_D
    (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N omega)) u

/-- The unit-cube affine inverse-Neumann response of the zero-infrared coefficient at slope `u`. -/
def aux_lem_prefix_limit_atom_extraction_Nz (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (u : Fin d → ℝ) (N : ℕ) (omega : BilateralField d) : ℝ :=
  aux_lem_prefix_limit_atom_extraction_N
    (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N omega)) u

omit [NeZero d] in
/-- The unit-cube potential at cutoff `N` reads only the coordinates `-N, …, 0`. -/
theorem aux_lem_prefix_limit_atom_extraction_pot_det (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (ω₁ ω₂ : BilateralField d)
    (h : ∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ 0 → ω₁ j = ω₂ j) :
    aux_lem_prefix_limit_atom_extraction_pot M N ω₁ =
      aux_lem_prefix_limit_atom_extraction_pot M N ω₂ := by
  unfold aux_lem_prefix_limit_atom_extraction_pot
  congr 3
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact h _ (by omega) (by omega)

theorem aux_lem_prefix_limit_atom_extraction_Dz_continuous
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (u : Fin d → ℝ) (N : ℕ) :
    Continuous (aux_lem_prefix_limit_atom_extraction_Dz M u N) :=
  (aux_lem_prefix_limit_atom_extraction_affineD_continuous _ _ u).comp
    (aux_lem_prefix_limit_atom_extraction_pot_continuous M N)

theorem aux_lem_prefix_limit_atom_extraction_Nz_continuous
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (u : Fin d → ℝ) (N : ℕ) :
    Continuous (aux_lem_prefix_limit_atom_extraction_Nz M u N) :=
  (aux_lem_prefix_limit_atom_extraction_affineN_continuous _ u).comp
    (aux_lem_prefix_limit_atom_extraction_pot_continuous M N)

end PaeCrux

section PaeLem15

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology Pointwise

section UniformFourTerm
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology Pointwise

theorem aux_lem_prefix_limit_atom_extraction_l15_env
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (dir : Bool)
    (bd : weakSobolevGraph (centeredCube z r hr)) (L : S.space →L[ℝ] ℝ)
    (Qt : Set (SpatialCoordinates d)) (hQt : IsCompact Qt)
    (hQQt : ((centeredCube z r hr : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) ⊆ Qt)
    (t : ℝ) (delta : ℝ) (hdelta : 0 < delta) (hdelta_le : delta ≤ 1)
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (hG1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
    (hG2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHmeas : Measurable H)
    (hHupd : ∀ j : ℕ, ∀ᵐ pair ∂(((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure).prod
        ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure)),
      H pair.1 = H (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ)))))
    (kappa : ℕ → ℝ)
    (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr))
    (haN : ∀ N omega,
      (aN N omega).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N))))
    (K : ℕ → BilateralField d → ℝ)
    (hK : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure),
      ∀ N, 0 ≤ K N omega)
    (hgrowth : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure),
      ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          localGradientEnergy (aN N omega)
            (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
            (aux_lem_15_u_grad S dir bd L (aN N omega)) ≤ K N omega * rho ^ t)
    (N j : ℕ) (hjN : j ≤ N) :
    let μs : ℤ → Measure C(SpatialCoordinates d, ℝ) := fun i =>
      (scaledLayerLaw d ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ)))) i :
        Measure C(SpatialCoordinates d, ℝ))
    let base := aux_lem_15_u_base H N j (Real.log (kappa N))
    Measurable base ∧
    (∀ᵐ q ∂((Measure.infinitePi μs).prod (Measure.infinitePi μs)),
      base (Function.update q.1 (-(j : ℤ)) (q.2 (-(j : ℤ)))) = base q.1) ∧
    (∀ omega, aN N omega = expPotentialCoefficient
      (aux_lem_15_u_embU Qt hQt hQQt (base omega + omega (-(j : ℤ))))) ∧
    (∀ᵐ omega ∂(Measure.infinitePi μs), 0 ≤ K N omega ∧
      aux_lem_15_u_Growth S dir bd L t
        (aux_lem_15_u_embU Qt hQt hQQt (base omega + omega (-(j : ℤ)))) (K N omega)) := by
  intro μs base
  have hcoef : ∀ omega, aN N omega = expPotentialCoefficient
      (aux_lem_15_u_embU Qt hQt hQQt (base omega + omega (-(j : ℤ)))) :=
    fun omega => aux_lem_15_u_coeff_eq Qt hQt hQQt H N j hjN (kappa N) omega (aN N omega)
      (haN N omega)
  refine ⟨aux_lem_15_u_base_measurable H hHmeas N j _, ?_, hcoef, ?_⟩
  · have hHinv := hHupd j
    filter_upwards [hHinv] with q hq
    exact aux_lem_15_u_base_update H N j _ q.1 (q.2 (-(j : ℤ))) hq.symm
  · have hK' : ∀ᵐ omega ∂(Measure.infinitePi μs), ∀ N, 0 ≤ K N omega := hK
    have hg' : ∀ᵐ omega ∂(Measure.infinitePi μs), ∀ N, ∀ x ∈ (centeredCube z r hr : Set _),
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          localGradientEnergy (aN N omega) (s := Metric.ball x rho)
            Metric.isOpen_ball.measurableSet
            (aux_lem_15_u_grad S dir bd L (aN N omega)) ≤ K N omega * rho ^ t := hgrowth
    filter_upwards [hK', hg'] with omega h1 h2
    refine ⟨h1 N, ?_⟩
    intro x hx rho hrho hrho1
    have h := h2 N x hx rho hrho hrho1
    rw [hcoef omega] at h
    exact h


theorem aux_lem_prefix_limit_atom_extraction_l15_mask_case
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (dir : Bool)
    (bd : weakSobolevGraph (centeredCube z r hr)) (L : S.space →L[ℝ] ℝ)
    (t p B : ℝ) (hp : 2 ≤ p) (hB : 0 ≤ B)
    (Cd : ℝ) (hCd : 0 < Cd) (hbpos : 0 < t * (t - (d : ℝ) + 1) / (t + 1))
    (Cp : ℝ) (hCp : 0 < Cp)
    (hCpall : ∀ (m : ℕ) (mu : Fin m → Measure C(SpatialCoordinates d, ℝ))
      [∀ i, IsProbabilityMeasure (mu i)], aux_lem_15_u_ESProp mu p Cp)
    (Cexp Cdel Ca Cb Cc Ce : ℝ) (hCdel : 0 ≤ Cdel) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb)
    (hCc : 0 ≤ Cc) (hCe : 0 ≤ Ce)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta_le : delta ≤ 1)
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (hG1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
    (hG2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHmeas : Measurable H)
    (hHupd : ∀ j : ℕ, ∀ᵐ pair ∂(((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure).prod
        ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure)),
      H pair.1 = H (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ)))))
    (kappa : ℕ → ℝ)
    (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr))
    (haN : ∀ N omega,
      (aN N omega).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N))))
    (K : ℕ → BilateralField d → ℝ)
    (hKm : ∀ N, AEStronglyMeasurable (K N) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure))
    (hK : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure),
      ∀ N, 0 ≤ K N omega)
    (hgrowth : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure),
      ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          localGradientEnergy (aN N omega)
            (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
            (aux_lem_15_u_grad S dir bd L (aN N omega)) ≤ K N omega * rho ^ t)
    (N j : ℕ) (hjN : j ≤ N)
    (hmomK : eLpNorm (K N) (ENNReal.ofReal (3 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure) ≤
      ENNReal.ofReal B)
    (hmomR : eLpNorm (fun omega => aux_lem_15_u_resp S dir bd L (aN N omega))
      (ENNReal.ofReal (3 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure) ≤
      ENNReal.ofReal B)
    (rs : ℝ) (hrsdef : rs = (3 : ℝ) ^ (-(j : ℝ)))
    (hgeom : (0 < rs ^ ((t - (d : ℝ) + 1) / (t + 1)) ∧ rs ^ ((t - (d : ℝ) + 1) / (t + 1)) ≤ 1 ∧
        (2 * Real.sqrt d) * rs < rs ^ ((t - (d : ℝ) + 1) / (t + 1))) ∧
      aux_lem_15_u_StripBound (centeredCube z r hr) t 0
        (rs ^ ((t - (d : ℝ) + 1) / (t + 1))) ((2 * Real.sqrt d) * rs)
        (Cd * (max 1 r) ^ d * rs ^ (t * (t - (d : ℝ) + 1) / (t + 1)))
        (Cd * rs ^ (t * (t - (d : ℝ) + 1) / (t + 1))))
    (hMexp : eLpNorm (fun ω : BilateralField d => Real.exp (2 * aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ)))))
      (ENNReal.ofReal p) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure) ≤
      ENNReal.ofReal Cexp)
    (hMdel : eLpNorm (fun ω : BilateralField d => aux_lem_15_u_supn (aux_lem_15_u_Qt z r)
        (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ))) * Real.exp (4 * aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ)))))
      (ENNReal.ofReal (2 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure) ≤
      ENNReal.ofReal (Cdel * delta * rs ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 12))))
    (hMa : eLpNorm (fun ω : BilateralField d => Real.exp (7 * aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ)))))
      (ENNReal.ofReal (2 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure) ≤
      ENNReal.ofReal (Ca * rs ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 12))))
    (hMb : eLpNorm (fun ω : BilateralField d => aux_lem_15_u_supn (aux_lem_15_u_Qt z r)
        (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ))) * Real.exp (7 * aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ)))))
      (ENNReal.ofReal (2 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure) ≤
      ENNReal.ofReal (Cb * delta * rs ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 12))))
    (hMc : eLpNorm (fun ω : BilateralField d => Real.exp (8 * aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ))))) 1
      ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure) ≤
      ENNReal.ofReal (Cc * rs ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 12))))
    (hMe : eLpNorm (fun ω : BilateralField d => aux_lem_15_u_supn (aux_lem_15_u_Qt z r)
        (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ))) ^ 2 * Real.exp (8 * aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (ω (-(j : ℤ))))) 1
      ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure) ≤
      ENNReal.ofReal (Ce * delta ^ 2 * rs ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / 12)))) :
    eLpNorm (fun pair : BilateralField d × BilateralField d =>
        aux_lem_15_u_resp S dir bd L (aN N pair.1) -
          aux_lem_15_u_resp S dir bd L
            (aN N (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ))))))
      (ENNReal.ofReal p)
      (((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure).prod
      ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure)) ≤
    ENNReal.ofReal ((4 * Cd * (max 1 r) ^ d * Cdel * B +
      4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
        (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) *
      delta * rs ^ (3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8)) := by
  -- environment
  set bexp := t * (t - (d : ℝ) + 1) / (t + 1) with hbexp
  set ell := rs ^ ((t - (d : ℝ) + 1) / (t + 1)) with hell_def
  set w := (2 * Real.sqrt d) * rs with hw_def
  have hrs : 0 < rs := by rw [hrsdef]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hrs1 : rs ≤ 1 := by
    rw [hrsdef]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith)
  obtain ⟨⟨hell, hell1, hwl⟩, hSB⟩ := hgeom
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d by omega))
  have hw : 0 < w := by rw [hw_def]; positivity
  have henv := aux_lem_prefix_limit_atom_extraction_l15_env d hd z r hr S dir bd L (aux_lem_15_u_Qt z r)
    (aux_lem_15_u_Qt_compact z r) (aux_lem_15_u_Qt_sub z hr) t delta hdelta hdelta_le Praw hG1
    hG2 H hHmeas hHupd kappa aN haN K hK hgrowth N j hjN
  simp only at henv
  obtain ⟨hbase, hinv, hcoef, hgr⟩ := henv
  -- index set of the grid
  set I := aux_lem_15_u_index 0 z r ell with hI
  set idx : Fin I.card → (Fin d → ℤ) := fun k => (I.equivFin.symm k).1 with hidx
  have hinj : Function.Injective idx := by
    intro k k' h
    exact I.equivFin.symm.injective (Subtype.ext h)
  have hcover : ∀ x ∈ ((centeredCube z r hr : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)), x ∉ aux_lem_15_u_stripSet 0 ell w →
      ∃ k, x ∈ aux_lem_15_u_core 0 ell w (idx k) := by
    intro x hx hxs
    have hmem := aux_lem_15_u_floorIdx_mem_index 0 z (s := r) hell hx
    refine ⟨I.equivFin ⟨_, hmem⟩, ?_⟩
    have : idx (I.equivFin ⟨_, hmem⟩) = aux_lem_15_u_floorIdx 0 ell x := by
      simp [hidx]
    rw [this]
    exact aux_lem_15_u_mem_core_of_not_strip 0 hell hxs
  have hkbox : ∀ k, aux_lem_15_u_kbox 0 ell w (idx k) ⊆ aux_lem_15_u_Qt z r := fun k =>
    aux_lem_15_u_kbox_subset 0 z hr.le hell hell1 hw.le (I.equivFin.symm k).2
  -- independence of the pieces
  have hsep : Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (-(-(j : ℤ))) * (w / 2) := by
    have h3 : (3 : ℝ) ^ (-(-(j : ℤ))) * rs = 1 := by
      rw [neg_neg, zpow_natCast, hrsdef, Real.rpow_neg (by norm_num), Real.rpow_natCast,
        mul_inv_cancel₀ (by positivity)]
    have : (3 : ℝ) ^ (-(-(j : ℤ))) * (w / 2) = Real.sqrt d * ((3 : ℝ) ^ (-(-(j : ℤ))) * rs) := by
      rw [hw_def]; ring
    rw [this, h3, mul_one]
  have hπ := aux_lem_15_u_key_law hd Praw hG1 j 0 hell.le hw hwl.le hsep idx hinj
  haveI : IsProbabilityMeasure ((Measure.infinitePi (fun i => (scaledLayerLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ)))) i :
        Measure C(SpatialCoordinates d, ℝ)))).map (fun ω : BilateralField d => ω (-(j : ℤ)))) :=
    inferInstance
  haveI hprobk : ∀ k, IsProbabilityMeasure (aux_lem_15_u_muk (fun i => (scaledLayerLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ)))) i :
        Measure C(SpatialCoordinates d, ℝ))) (-(j : ℤ)) 0 ell w idx k) := fun k => by
    unfold aux_lem_15_u_muk
    exact inferInstance
  have hES := hCpall I.card (aux_lem_15_u_muk (fun i => (scaledLayerLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ)))) i :
        Measure C(SpatialCoordinates d, ℝ))) (-(j : ℤ)) 0 ell w idx)
  have hRN : ∀ ω, aux_lem_15_u_resp S dir bd L (aN N ω) = aux_lem_15_u_R S dir bd L
      (aux_lem_15_u_embU (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
        (aux_lem_15_u_Qt_sub z hr) (aux_lem_15_u_base H N j (Real.log (kappa N)) ω +
          ω (-(j : ℤ)))) := by
    intro ω; rw [hcoef ω]; rfl
  have hmain := aux_lem_15_u_masking S dir bd L (aux_lem_15_u_Qt z r)
    (aux_lem_15_u_Qt_compact z r) (aux_lem_15_u_Qt_sub z hr) _ (-(j : ℤ)) _ hbase hinv
    (fun ω => aux_lem_15_u_resp S dir bd L (aN N ω)) (K N) hRN (hKm N) t hgr p B
    (by linarith) hB hmomK hmomR 0 ell w hell hw hwl.le idx hinj hcover hkbox _ _ hSB
    (by positivity) (by positivity) hπ Cp hCp.le hES Cexp
    (Cdel * delta * rs ^ (-(bexp / 12))) (Ca * rs ^ (-(bexp / 12)))
    (Cb * delta * rs ^ (-(bexp / 12))) (Cc * rs ^ (-(bexp / 12)))
    (Ce * delta ^ 2 * rs ^ (-(bexp / 12)))
    (by have := Real.rpow_pos_of_pos hrs (-(bexp / 12)); positivity)
    (by have := Real.rpow_pos_of_pos hrs (-(bexp / 12)); positivity)
    (by have := Real.rpow_pos_of_pos hrs (-(bexp / 12)); positivity)
    (by have := Real.rpow_pos_of_pos hrs (-(bexp / 12)); positivity)
    (by have := Real.rpow_pos_of_pos hrs (-(bexp / 12)); positivity)
    hMexp hMdel hMa hMb hMc hMe
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  -- numerical bookkeeping
  obtain ⟨e1, e2, e3, hvu⟩ := aux_lem_15_u_rpow_facts rs bexp hrs hrs1 hbpos
  have hγ : -(t * (t - (d : ℝ) + 1) / (t + 1) / 12) = -(bexp / 12) := by rw [hbexp]
  rw [hγ, e1, e2, e3]
  exact aux_lem_15_u_mask_numeric delta B Cd ((max 1 r) ^ d) Cdel Ca Cb Cc Ce Cp
    (rs ^ (bexp / 2)) (rs ^ (-(bexp / 12) / 2)) hdelta.le hB hCd.le (by positivity) hCdel
    hCc hCe (Real.rpow_pos_of_pos hrs _).le (Real.rpow_pos_of_pos hrs _).le hvu



theorem aux_lem_prefix_limit_atom_extraction_l15_init_case
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr)) (dir : Bool)
    (bd : weakSobolevGraph (centeredCube z r hr)) (L : S.space →L[ℝ] ℝ)
    (t p B : ℝ) (hp : 2 ≤ p)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta_le : delta ≤ 1)
    (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
    (hG1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
    (hG2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hHmeas : Measurable H)
    (hHupd : ∀ j : ℕ, ∀ᵐ pair ∂(((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure).prod
        ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure)),
      H pair.1 = H (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ)))))
    (kappa : ℕ → ℝ)
    (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr))
    (haN : ∀ N omega,
      (aN N omega).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
        (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N))))
    (K : ℕ → BilateralField d → ℝ)
    (hK : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure),
      ∀ N, 0 ≤ K N omega)
    (hgrowth : ∀ᵐ omega ∂((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure),
      ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          localGradientEnergy (aN N omega)
            (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
            (aux_lem_15_u_grad S dir bd L (aN N omega)) ≤ K N omega * rho ^ t)
    (N j : ℕ) (hjN : j ≤ N)
    (hmomR : eLpNorm (fun omega => aux_lem_15_u_resp S dir bd L (aN N omega))
      (ENNReal.ofReal (3 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure) ≤
      ENNReal.ofReal B)
    (N1 N0 : ℝ) (hN1 : 0 ≤ N1) (hN0 : 0 ≤ N0)
    (hm1 : eLpNorm (fun om : BilateralField d => aux_lem_15_u_supn (aux_lem_15_u_Qt z r)
        (aux_lem_15_u_Qt_compact z r) (om (-(j : ℤ))) * Real.exp (aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (om (-(j : ℤ)))))
      (ENNReal.ofReal (4 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure) ≤
      ENNReal.ofReal N1)
    (hm0 : eLpNorm (fun om : BilateralField d => Real.exp (aux_lem_15_u_supn
        (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r) (om (-(j : ℤ)))))
      (ENNReal.ofReal (4 * p)) ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure) ≤
      ENNReal.ofReal N0) :
    eLpNorm (fun pair : BilateralField d × BilateralField d =>
        aux_lem_15_u_resp S dir bd L (aN N pair.1) -
          aux_lem_15_u_resp S dir bd L
            (aN N (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ))))))
      (ENNReal.ofReal p)
      (((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure).prod
      ((commonScaleLaw d
      ((SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
        (⟨fun g => g.1.1, continuous_subtype_val.fst⟩ :
          C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
            C(SpatialCoordinates d, ℝ))))).toMeasure)) ≤
    ENNReal.ofReal (2 * (N1 * N0) * B) := by
  have henv := aux_lem_prefix_limit_atom_extraction_l15_env d hd z r hr S dir bd L (aux_lem_15_u_Qt z r)
    (aux_lem_15_u_Qt_compact z r) (aux_lem_15_u_Qt_sub z hr) t delta hdelta hdelta_le Praw hG1
    hG2 H hHmeas hHupd kappa aN haN K hK hgrowth N j hjN
  simp only at henv
  obtain ⟨hbase, hinv, hcoef, _⟩ := henv
  have hRN : ∀ om, aux_lem_15_u_resp S dir bd L (aN N om) = aux_lem_15_u_R S dir bd L
      (aux_lem_15_u_embU (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
        (aux_lem_15_u_Qt_sub z hr) (aux_lem_15_u_base H N j (Real.log (kappa N)) om +
          om (-(j : ℤ)))) := by
    intro om; rw [hcoef om]; rfl
  exact aux_lem_15_u_initial S dir bd L (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    (aux_lem_15_u_Qt_sub z hr) _ (-(j : ℤ)) _ hbase hinv
    (fun om => aux_lem_15_u_resp S dir bd L (aN N om)) hRN p B (by linarith) hmomR N1 N0 hN1 hN0
    hm1 hm0


open scoped ContDiff in
theorem aux_lem_prefix_limit_atom_extraction_l15_main
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (phi : SpatialCoordinates d → ℝ) (_hphi : ContDiff ℝ ∞ phi)
    (_hnonconst : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), phi x ≠ phi y)
    (b : weakSobolevGraph (centeredCube z r hr))
    (_hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (f : SpatialCoordinates d → ℝ) (_hf : ContDiff ℝ ∞ f)
    (_hfc : HasCompactSupport f)
    (_hfsupp : tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (_hf0 : ∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0)
    (fL2 : DomainL2 (centeredCube z r hr))
    (_hfL2 : (fL2 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f)
    (t p B : ℝ) (ht_lower : (d : ℝ) - 1 < t) (_ht_upper : t < (d : ℝ))
    (hp : 2 ≤ p) (hB : 0 ≤ B) (dirichlet : Bool) :
    let S := killedResponseSpace hP
    let L := (sobolevVolumeLoad fL2).comp S.space.subtypeL
    ∃ C : ℝ, 0 < C ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
          (_G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
          (_G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw),
          let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
            forget
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ j : ℕ, ∀ᵐ pair ∂(P.prod P),
              H pair.1 = H (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ))))) →
          ∀ (kappa : ℕ → ℝ), (∀ N, 0 < kappa N) →
          ∀ (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr)),
            (∀ N omega,
              (aN N omega).val =ᵐ[volume.restrict
                (centeredCube z r hr : Set (SpatialCoordinates d))]
                (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) →
          let RN : ℕ → BilateralField d → ℝ :=
            fun N omega =>
              if dirichlet then
                dirichletResponse S (aN N omega) b
              else
                inverseResponse S (aN N omega) L
          let gN : ℕ → BilateralField d → HilbertGradient (centeredCube z r hr) :=
            fun N omega =>
              if dirichlet then
                sobolevGradient (dirichletMinimizer S (aN N omega) b).val
              else
                subspaceGradient S.space (responseSolution S (aN N omega) L)
          ∀ (K : ℕ → BilateralField d → ℝ),
            ((∀ N, AEStronglyMeasurable (K N) P) ∧
            (∀ᵐ omega ∂P, ∀ N, 0 ≤ K N omega)) →
            (∀ᵐ omega ∂P, ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
                localGradientEnergy (aN N omega)
                  (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
                  (gN N omega) ≤ K N omega * rho ^ t) →
            (∀ N,
              MemLp (K N) (ENNReal.ofReal (3 * p)) P ∧
              MemLp (RN N) (ENNReal.ofReal (3 * p)) P ∧
              eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B ∧
              eLpNorm (RN N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B) →
            ∀ (N j : ℕ), j ≤ N →
              eLpNorm
                (fun pair : BilateralField d × BilateralField d =>
                  RN N pair.1 -
                    RN N
                      (Function.update pair.1 (-(j : ℤ))
                        (pair.2 (-(j : ℤ)))))
                (ENNReal.ofReal p) (P.prod P) ≤
              ENNReal.ofReal
                (C * delta *
                  (3 : ℝ) ^
                  (-(t * (t - (d : ℝ) + 1) / (t + 1) /
                      (8 * Real.log 3)) * (j : ℝ)))
    := by
  intro S L
  have hd1 : 1 ≤ d := by omega
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d by omega))
  have hgeo := aux_lem_15_u_geom d hd1 (2 * Real.sqrt d) (by positivity)
  obtain ⟨Cd, hCd, hgeo⟩ := hgeo
  have hgeo2 := hgeo t ht_lower
  obtain ⟨hbpos, r0, hr0, _, hgeoR⟩ := hgeo2
  have hp0 : 0 < p := by linarith
  have hgam : 0 < t * (t - (d : ℝ) + 1) / (t + 1) / 12 := by positivity
  have hQne := aux_lem_15_u_Qt_nonempty z hr
  have hRt : 0 ≤ ‖z‖ + (r / 2 + 1) := by positivity
  have hQR := aux_lem_15_u_Qt_bound z r
  -- the uniform layer-moment bank
  have hLexp := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR p ((0 : ℕ) : ℝ) 2 _ hp0 (by norm_num) (by norm_num) hgam
  obtain ⟨Cexp, _, hLexp⟩ := hLexp
  have hLdel := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (2 * p) ((1 : ℕ) : ℝ) 4 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨Cdel, hCdel, hLdel⟩ := hLdel
  have hLa := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (2 * p) ((0 : ℕ) : ℝ) 7 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨Ca, hCa, hLa⟩ := hLa
  have hLb := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (2 * p) ((1 : ℕ) : ℝ) 7 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨Cb, hCb, hLb⟩ := hLb
  have hLc := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR 1 ((0 : ℕ) : ℝ) 8 _ (by norm_num) (by norm_num) (by norm_num) hgam
  obtain ⟨Cc, hCc, hLc⟩ := hLc
  have hLe := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR 1 ((2 : ℕ) : ℝ) 8 _ (by norm_num) (by norm_num) (by norm_num) hgam
  obtain ⟨Ce, hCe, hLe⟩ := hLe
  have hL7 := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (4 * p) ((1 : ℕ) : ℝ) 1 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨C7, hC7, hL7⟩ := hL7
  have hL8 := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (4 * p) ((0 : ℕ) : ℝ) 1 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨C8, hC8, hL8⟩ := hL8
  -- the Efron–Stein constant (BBLM, proved in `aux_lem_15_bblm`)
  have hIES := in_efron_stein aux_lem_15_bblm p hp
  obtain ⟨Cp, hCp, hCpall⟩ := hIES
  have hCpall' : ∀ (m : ℕ) (mu : Fin m → Measure C(SpatialCoordinates d, ℝ))
      [∀ i, IsProbabilityMeasure (mu i)], aux_lem_15_u_ESProp mu p Cp := by
    intro m mu _
    exact (hCpall m (fun _ => C(SpatialCoordinates d, ℝ)) mu).1
  -- the initial scales
  have hj0 := exists_pow_lt_of_lt_one hr0 (by norm_num : (1 / 3 : ℝ) < 1)
  obtain ⟨j0, hj0⟩ := hj0
  refine ⟨(4 * Cd * (max 1 r) ^ d * Cdel * B +
      4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
        (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) +
      2 * (C7 * C8) * B * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) * j0) + 1,
    by positivity, ?_⟩
  intro delta hdelta hdelta1 Praw hG1 hG2 forget nu P H hHmeas hHupd kappa _ aN haN RN gN K
    hKmn hgrowth hmom N j hjN
  obtain ⟨hKm, hKnn⟩ := hKmn
  have hmomN := hmom N
  obtain ⟨_, _, hmomK, hmomR⟩ := hmomN
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha0 : 0 ≤ t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) := by positivity
  have hrs : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hY0 : 0 ≤ (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  by_cases hj : j0 ≤ j
  · -- masking case
    have hrsr0 : (3 : ℝ) ^ (-(j : ℝ)) ≤ r0 := by
      have h1 : (3 : ℝ) ^ (-(j : ℝ)) = (1 / 3 : ℝ) ^ j := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
      rw [h1]
      exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj).trans hj0.le
    have hgeom := hgeoR z r hr _ hrs hrsr0
    have hM1 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hLexp delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM2 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hLdel delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM3 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hLa delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM4 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hLb delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM5 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hLc delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM6 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 2
      (hLe delta hdelta hdelta1 Praw hG1 hG2 j)
    simp only [pow_zero, one_mul, pow_one, Real.rpow_natCast, ENNReal.ofReal_one,
      mul_one] at hM1 hM2 hM3 hM4 hM5 hM6
    have hmask := aux_lem_prefix_limit_atom_extraction_l15_mask_case d hd z r hr S dirichlet b L t p B hp hB Cd hCd hbpos
      Cp hCp hCpall' _ Cdel Ca Cb Cc Ce hCdel.le hCa.le hCb.le hCc.le hCe.le delta hdelta
      hdelta1 Praw hG1 hG2 H hHmeas hHupd kappa aN haN K hKm hKnn hgrowth N j hjN hmomK
      hmomR _ rfl hgeom hM1 hM2 hM3 hM4 hM5 hM6
    refine hmask.trans (ENNReal.ofReal_le_ofReal ?_)
    have hexp := aux_lem_15_u_exponent (t * (t - (d : ℝ) + 1) / (t + 1)) hbpos.le j
    have hrw : ((3 : ℝ) ^ (-(j : ℝ))) ^ (3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) =
        (3 : ℝ) ^ (-(3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
    rw [hrw]
    have hK0 : 0 ≤ 4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B := by positivity
    have hKi : 0 ≤ 2 * (C7 * C8) * B * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) * j0) := by positivity
    calc (4 * Cd * (max 1 r) ^ d * Cdel * B +
          4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
            (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) * delta *
          (3 : ℝ) ^ (-(3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ))
        ≤ (4 * Cd * (max 1 r) ^ d * Cdel * B +
          4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
            (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) * delta *
          (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ)) := by
          gcongr
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hdelta.le) hY0
          linarith
  · -- initial scales
    push_neg at hj
    have hM7 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hL7 delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM8 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hL8 delta hdelta hdelta1 Praw hG1 hG2 j)
    simp only [pow_zero, one_mul, pow_one, Real.rpow_natCast, mul_one] at hM7 hM8
    have hinit := aux_lem_prefix_limit_atom_extraction_l15_init_case d hd z r hr S dirichlet b L t p B hp delta hdelta
      hdelta1 Praw hG1 hG2 H hHmeas hHupd kappa aN haN K hKnn hgrowth N j hjN hmomR _ _
      (by positivity) (by positivity) hM7 hM8
    refine hinit.trans (ENNReal.ofReal_le_ofReal ?_)
    have hnum := aux_lem_15_u_init_numeric C7 C8 B delta
      (t * (t - (d : ℝ) + 1) / (t + 1) / 12)
      (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) j j0 hj.le hC7.le hC8.le hB
      hdelta.le hgam.le ha0
    have hK0 : 0 ≤ 4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B := by positivity
    have hd0 : 0 ≤ delta := hdelta.le
    refine hnum.trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hd0) hY0
    linarith



end UniformFourTerm

end PaeLem15

section PaeNeu15

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open Filter
open scoped Topology

section NeumannUniform
open Filter
open scoped Topology

theorem aux_lem_prefix_limit_atom_extraction_n15_uniform
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (t p : ℝ) (ht_lower : (d : ℝ) - 1 < t) (hp : 2 ≤ p) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (B : ℝ), 0 ≤ B →
      ∀ (S : ResponseSpace (centeredCube z r hr)) (dir : Bool)
        (bd : weakSobolevGraph (centeredCube z r hr)) (L : S.space →L[ℝ] ℝ)
        (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
          (_G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
          (_G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw),
          let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
            forget
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ j : ℕ, ∀ᵐ pair ∂(P.prod P),
              H pair.1 = H (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ))))) →
          ∀ (kappa : ℕ → ℝ)
            (aN : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr)),
            (∀ N omega,
              (aN N omega).val =ᵐ[volume.restrict
                (centeredCube z r hr : Set (SpatialCoordinates d))]
                (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) →
          ∀ (K : ℕ → BilateralField d → ℝ),
            (∀ N, AEStronglyMeasurable (K N) P) →
            (∀ᵐ omega ∂P, ∀ N, 0 ≤ K N omega) →
            (∀ᵐ omega ∂P, ∀ N, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
              ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
                localGradientEnergy (aN N omega)
                  (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
                  (aux_lem_15_u_grad S dir bd L (aN N omega)) ≤ K N omega * rho ^ t) →
            ∀ (N j : ℕ), j ≤ N →
            eLpNorm (K N) (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B →
            eLpNorm (fun omega => aux_lem_15_u_resp S dir bd L (aN N omega))
              (ENNReal.ofReal (3 * p)) P ≤ ENNReal.ofReal B →
              eLpNorm
                (fun pair : BilateralField d × BilateralField d =>
                  aux_lem_15_u_resp S dir bd L (aN N pair.1) -
                    aux_lem_15_u_resp S dir bd L (aN N
                      (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ))))))
                (ENNReal.ofReal p) (P.prod P) ≤
              ENNReal.ofReal
                (A * B * delta *
                  (3 : ℝ) ^
                  (-(t * (t - (d : ℝ) + 1) / (t + 1) /
                      (8 * Real.log 3)) * (j : ℝ))) := by
  have hd1 : 1 ≤ d := by omega
  have hsd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d by omega))
  have hgeo := aux_lem_15_u_geom d hd1 (2 * Real.sqrt d) (by positivity)
  obtain ⟨Cd, hCd, hgeo⟩ := hgeo
  have hgeo2 := hgeo t ht_lower
  obtain ⟨hbpos, r0, hr0, _, hgeoR⟩ := hgeo2
  have hp0 : 0 < p := by linarith
  have hgam : 0 < t * (t - (d : ℝ) + 1) / (t + 1) / 12 := by positivity
  have hQne := aux_lem_15_u_Qt_nonempty z hr
  have hRt : 0 ≤ ‖z‖ + (r / 2 + 1) := by positivity
  have hQR := aux_lem_15_u_Qt_bound z r
  -- the uniform layer-moment bank
  have hLexp := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR p ((0 : ℕ) : ℝ) 2 _ hp0 (by norm_num) (by norm_num) hgam
  obtain ⟨Cexp, _, hLexp⟩ := hLexp
  have hLdel := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (2 * p) ((1 : ℕ) : ℝ) 4 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨Cdel, hCdel, hLdel⟩ := hLdel
  have hLa := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (2 * p) ((0 : ℕ) : ℝ) 7 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨Ca, hCa, hLa⟩ := hLa
  have hLb := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (2 * p) ((1 : ℕ) : ℝ) 7 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨Cb, hCb, hLb⟩ := hLb
  have hLc := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR 1 ((0 : ℕ) : ℝ) 8 _ (by norm_num) (by norm_num) (by norm_num) hgam
  obtain ⟨Cc, hCc, hLc⟩ := hLc
  have hLe := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR 1 ((2 : ℕ) : ℝ) 8 _ (by norm_num) (by norm_num) (by norm_num) hgam
  obtain ⟨Ce, hCe, hLe⟩ := hLe
  have hL7 := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (4 * p) ((1 : ℕ) : ℝ) 1 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨C7, hC7, hL7⟩ := hL7
  have hL8 := aux_lem_15_u_layer_moment d hd (aux_lem_15_u_Qt z r) (aux_lem_15_u_Qt_compact z r)
    hQne _ hRt hQR (4 * p) ((0 : ℕ) : ℝ) 1 _ (by positivity) (by norm_num) (by norm_num) hgam
  obtain ⟨C8, hC8, hL8⟩ := hL8
  -- the Efron–Stein constant (BBLM, proved in `aux_lem_15_bblm`)
  have hIES := in_efron_stein aux_lem_15_bblm p hp
  obtain ⟨Cp, hCp, hCpall⟩ := hIES
  have hCpall' : ∀ (m : ℕ) (mu : Fin m → Measure C(SpatialCoordinates d, ℝ))
      [∀ i, IsProbabilityMeasure (mu i)], aux_lem_15_u_ESProp mu p Cp := by
    intro m mu _
    exact (hCpall m (fun _ => C(SpatialCoordinates d, ℝ)) mu).1
  -- the initial scales
  have hj0 := exists_pow_lt_of_lt_one hr0 (by norm_num : (1 / 3 : ℝ) < 1)
  obtain ⟨j0, hj0⟩ := hj0
  refine ⟨(4 * Cd * (max 1 r) ^ d * Cdel +
      4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
        (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb)) +
      2 * (C7 * C8) * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) * j0),
    by positivity, ?_⟩
  intro B hB S dir bd L delta hdelta hdelta1 Praw hG1 hG2 forget nu P H hHmeas hHupd kappa aN
    haN K hKm hKnn hgrowth N j hjN hmomK hmomR
  have hAB : ((4 * Cd * (max 1 r) ^ d * Cdel +
      4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
        (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb)) +
      2 * (C7 * C8) * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) * j0)) * B =
      (4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) +
      2 * (C7 * C8) * B * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) * j0) := by ring
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have ha0 : 0 ≤ t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) := by positivity
  have hrs : (0 : ℝ) < (3 : ℝ) ^ (-(j : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hY0 : 0 ≤ (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ)) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  by_cases hj : j0 ≤ j
  · -- masking case
    have hrsr0 : (3 : ℝ) ^ (-(j : ℝ)) ≤ r0 := by
      have h1 : (3 : ℝ) ^ (-(j : ℝ)) = (1 / 3 : ℝ) ^ j := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]
      rw [h1]
      exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hj).trans hj0.le
    have hgeom := hgeoR z r hr _ hrs hrsr0
    have hM1 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hLexp delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM2 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hLdel delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM3 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hLa delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM4 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hLb delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM5 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hLc delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM6 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 2
      (hLe delta hdelta hdelta1 Praw hG1 hG2 j)
    simp only [pow_zero, one_mul, pow_one, Real.rpow_natCast, ENNReal.ofReal_one,
      mul_one] at hM1 hM2 hM3 hM4 hM5 hM6
    have hmask := aux_lem_prefix_limit_atom_extraction_l15_mask_case d hd z r hr S dir bd L t p B hp hB Cd hCd hbpos
      Cp hCp hCpall' _ Cdel Ca Cb Cc Ce hCdel.le hCa.le hCb.le hCc.le hCe.le delta hdelta
      hdelta1 Praw hG1 hG2 H hHmeas hHupd kappa aN haN K hKm hKnn hgrowth N j hjN hmomK
      hmomR _ rfl hgeom hM1 hM2 hM3 hM4 hM5 hM6
    refine hmask.trans (ENNReal.ofReal_le_ofReal ?_)
    have hexp := aux_lem_15_u_exponent (t * (t - (d : ℝ) + 1) / (t + 1)) hbpos.le j
    have hrw : ((3 : ℝ) ^ (-(j : ℝ))) ^ (3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) =
        (3 : ℝ) ^ (-(3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num)]; congr 1; ring
    rw [hrw]
    have hK0 : 0 ≤ 4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B := by positivity
    have hKi : 0 ≤ 2 * (C7 * C8) * B * (3 : ℝ) ^ (2 * (t * (t - (d : ℝ) + 1) / (t + 1) / 12) * j0) *
        (3 : ℝ) ^ (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) * j0) := by positivity
    calc (4 * Cd * (max 1 r) ^ d * Cdel * B +
          4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
            (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) * delta *
          (3 : ℝ) ^ (-(3 * (t * (t - (d : ℝ) + 1) / (t + 1)) / 8) * (j : ℝ))
        ≤ (4 * Cd * (max 1 r) ^ d * Cdel * B +
          4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
            (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B) * delta *
          (3 : ℝ) ^ (-(t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) * (j : ℝ)) := by
          gcongr
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hdelta.le) hY0
          rw [hAB]; linarith
  · -- initial scales
    push_neg at hj
    have hM7 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 1
      (hL7 delta hdelta hdelta1 Praw hG1 hG2 j)
    have hM8 := aux_lem_15_u_moment_supn _ (aux_lem_15_u_Qt_compact z r) _ j _ _ _ 0
      (hL8 delta hdelta hdelta1 Praw hG1 hG2 j)
    simp only [pow_zero, one_mul, pow_one, Real.rpow_natCast, mul_one] at hM7 hM8
    have hinit := aux_lem_prefix_limit_atom_extraction_l15_init_case d hd z r hr S dir bd L t p B hp delta hdelta
      hdelta1 Praw hG1 hG2 H hHmeas hHupd kappa aN haN K hKnn hgrowth N j hjN hmomR _ _
      (by positivity) (by positivity) hM7 hM8
    refine hinit.trans (ENNReal.ofReal_le_ofReal ?_)
    have hnum := aux_lem_15_u_init_numeric C7 C8 B delta
      (t * (t - (d : ℝ) + 1) / (t + 1) / 12)
      (t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3)) j j0 hj.le hC7.le hC8.le hB
      hdelta.le hgam.le ha0
    have hK0 : 0 ≤ 4 * Cd * (max 1 r) ^ d * Cdel * B +
        4 * Cp * Real.sqrt (8 * Cd * (2 + 4 * (max 1 r) ^ d)) *
          (Real.sqrt Ce * Ca + Real.sqrt Cc * Cb) * B := by positivity
    have hd0 : 0 ≤ delta := hdelta.le
    refine hnum.trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hd0) hY0
    rw [hAB]; linarith


end NeumannUniform

end PaeNeu15

section PaeBandN

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

section Generic

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Band error of `X` is at most twice its `L¹` distance to `Y` plus the band error of `Y`. -/
theorem aux_lem_prefix_limit_atom_extraction_band_triangle [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ) :
    eLpNorm (fun ω => X ω - μ[X|m] ω) 1 μ ≤
      2 * eLpNorm (fun ω => X ω - Y ω) 1 μ + eLpNorm (fun ω => Y ω - μ[Y|m] ω) 1 μ := by
  have hce := condExp_sub hX hY m
  have heq : (fun ω => X ω - μ[X|m] ω) =ᵐ[μ]
      ((X - Y) - μ[X - Y|m]) + (Y - μ[Y|m]) := by
    filter_upwards [hce] with ω h
    simp only [Pi.sub_apply, Pi.add_apply] at h ⊢
    rw [h]
    ring
  rw [eLpNorm_congr_ae heq]
  have hXY : Integrable (X - Y) μ := hX.sub hY
  calc eLpNorm (((X - Y) - μ[X - Y|m]) + (Y - μ[Y|m])) 1 μ
      ≤ eLpNorm ((X - Y) - μ[X - Y|m]) 1 μ + eLpNorm (Y - μ[Y|m]) 1 μ :=
        eLpNorm_add_le le_rfl
    _ ≤ (eLpNorm (X - Y) 1 μ + eLpNorm (μ[X - Y|m]) 1 μ) + eLpNorm (Y - μ[Y|m]) 1 μ := by
        gcongr
        exact eLpNorm_sub_le le_rfl
    _ ≤ (eLpNorm (X - Y) 1 μ + eLpNorm (X - Y) 1 μ) + eLpNorm (Y - μ[Y|m]) 1 μ := by
        gcongr
        exact eLpNorm_one_condExp_le_eLpNorm _
    _ = 2 * eLpNorm (fun ω => X ω - Y ω) 1 μ + eLpNorm (fun ω => Y ω - μ[Y|m] ω) 1 μ := by
        rw [← two_mul]
        rfl

end Generic

/-- Real bookkeeping for the smoothing width `ε = 3^{-aH/8}/16`. -/
theorem aux_lem_prefix_limit_atom_extraction_eps_facts (a : ℝ) (ha : 0 < a) (H : ℕ) :
    let ε : ℝ := (1 / 16) * (3 : ℝ) ^ (-(a * (H : ℝ) / 8))
    0 < ε ∧ ε < 1 / 8 ∧ ε ≤ 1 ∧ ε ^ (1 / 4 : ℝ) ≤ (3 : ℝ) ^ (-(a / 32 * (H : ℝ))) ∧
      ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-(a * (H : ℝ))) ≤ 256 * (3 : ℝ) ^ (-(a / 32 * (H : ℝ))) := by
  intro ε
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (-(a * (H : ℝ) / 8)) := Real.rpow_pos_of_pos (by norm_num) _
  have h3le : (3 : ℝ) ^ (-(a * (H : ℝ) / 8)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith)
  have hε0 : 0 < ε := by positivity
  have hε16 : ε ≤ 1 / 16 := by
    change (1 / 16) * (3 : ℝ) ^ (-(a * (H : ℝ) / 8)) ≤ 1 / 16
    nlinarith
  refine ⟨hε0, by linarith, by linarith, ?_, ?_⟩
  · change ((1 / 16) * (3 : ℝ) ^ (-(a * (H : ℝ) / 8))) ^ (1 / 4 : ℝ) ≤ _
    rw [Real.mul_rpow (by norm_num) h3.le, ← Real.rpow_mul (by norm_num)]
    have h1 : (1 / 16 : ℝ) ^ (1 / 4 : ℝ) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)
    have heq : -(a * (H : ℝ) / 8) * (1 / 4) = -(a / 32 * (H : ℝ)) := by ring
    rw [heq]
    have hp : (0 : ℝ) < (3 : ℝ) ^ (-(a / 32 * (H : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith
  · change ((1 / 16) * (3 : ℝ) ^ (-(a * (H : ℝ) / 8))) ^ (-2 : ℝ) * _ ≤ _
    rw [Real.mul_rpow (by norm_num) h3.le, ← Real.rpow_mul (by norm_num)]
    have h16 : (1 / 16 : ℝ) ^ (-2 : ℝ) = 256 := by
      rw [Real.rpow_neg (by norm_num), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    rw [h16, mul_assoc, ← Real.rpow_add (by norm_num)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith

end PaeBandN

section PaeG0Core

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

variable {d : ℕ}

/-- The empty infrared partial sum. -/
theorem aux_lem_prefix_limit_atom_extraction_ips_zero :
    (fun om : BilateralField d => infraredPartialSum om 0) = fun _ => 0 := by
  funext om
  simp [infraredPartialSum]

/-- The exact finite identity at `L' = 0`: the zero-infrared coefficient is a positive constant
times the stationary cutoff coefficient `a_N` at physical scale. -/
theorem aux_lem_prefix_limit_atom_extraction_zero_identity
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M) (om : BilateralField d)
    (N : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ N) :
    ∃ cFin : ℝ, 0 < cFin ∧
      ∀ᵐ y ∂volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d)),
        (cutoffPositiveCoefficient M (fun _ => 0) om N z one_pos).val y =
          cFin * (Sreg.cutoffOn (N + 0) (aux_aux_macro_energy_recurrence_relabel N om)
            ((3 : ℝ) ^ N • z) (3 ^ N) hR).val ((3 : ℝ) ^ N • y) := by
  obtain ⟨cFin, hcF, hae⟩ := aux_prop_growth_macro_energy_finite_identity Sreg om N 0 z
    one_pos (by positivity)
  refine ⟨cFin, hcF, ?_⟩
  rw [aux_lem_prefix_limit_atom_extraction_ips_zero] at hae
  filter_upwards [hae] with y hy
  rw [hy]
  congr 1
  exact aux_aux_macro_energy_recurrence_cutoffOn_congr Sreg (N + 0) rfl
    (by rw [zpow_natCast]) (by rw [zpow_natCast, mul_one]) _ _ (by rw [zpow_natCast])

/-- **The one-centre estimate for the zero-infrared coefficient** (exact, `L' = 0`). -/
theorem aux_lem_prefix_limit_atom_extraction_core0 (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (hchild : aux_aux_macro_energy_recurrence_DensityChild Sreg) (alpha : ℝ)
    (hδ : M.delta ≤ Sreg.C⁻¹) (hα : alpha ∈ Sreg.alphaRange)
    (om : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) (hR : (0 : ℝ) < 3 ^ N)
    (P0 : ℕ) (hpre : Sreg.prefixLen N alpha N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_energy_recurrence_relabel N om) ≤ P0)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hCφ : c2Norm (closedCube z 1 one_pos : Set (SpatialCoordinates d)) φ ≤ Cφ)
    (b u : weakSobolevGraph (centeredCube z 1 one_pos))
    (hb : ((b : SobolevData (centeredCube z 1 one_pos)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))] φ)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M (fun _ => 0) om N z one_pos) F b u)
    (x : SpatialCoordinates d) (hx : x ∈ (centeredCube z 1 one_pos : Set (SpatialCoordinates d)))
    (n : ℕ) (hn : (n : ℤ) ≤ (N : ℤ) - P0) :
    localGradientEnergy (cutoffPositiveCoefficient M (fun _ => 0) om N z one_pos)
        (isOpen_ball.measurableSet.inter (centeredCube z 1 one_pos).isOpen.measurableSet :
          MeasurableSet (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
            (centeredCube z 1 one_pos : Set (SpatialCoordinates d))))
        (sobolevGradient (u : SobolevData (centeredCube z 1 one_pos))) ≤
      16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n *
          sobolevCoefficientForm (cutoffPositiveCoefficient M (fun _ => 0) om N z one_pos)
            (u : SobolevData _) (u : SobolevData _) +
        8 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n * 1 *
          (Cp ^ 2 * Kf ^ 2 + (d : ℝ) ^ 2 * Cφ ^ 2) := by
  obtain ⟨lam, Λ, hlam, hlamA, hΛA⟩ :=
    aux_aux_macro_energy_recurrence_cutoffCoefficient_bounds M (fun _ => 0) om N z one_pos
  have hΛ0 : 0 ≤ Λ := by
    have := (hlamA z (Metric.mem_closedBall_self (by norm_num))).trans
      (hΛA z (Metric.mem_closedBall_self (by norm_num)))
    linarith
  have hKr : ∀ x ∈ (closedCube z 1 one_pos : Set (SpatialCoordinates d)),
      Real.exp |(fun _ : BilateralField d => (0 : C(SpatialCoordinates d, ℝ))) om x| ≤ 1 := by
    intro x _
    simp
  obtain ⟨cFin, hcF, hcoef⟩ := aux_lem_prefix_limit_atom_extraction_zero_identity Sreg om N z hR
  have hn' : (n : ℤ) ≤ (N : ℤ) - Sreg.prefixLen (N + 0) alpha N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_energy_recurrence_relabel N om) := by
    have : (Sreg.prefixLen (N + 0) alpha N ((3 : ℝ) ^ N • z)
        (aux_aux_macro_energy_recurrence_relabel N om) : ℤ) ≤ (P0 : ℤ) := by
      exact_mod_cast hpre
    linarith
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc =
      (16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n + 2) * Λ *
      (4 / lam ^ 2 * aux_aux_macro_energy_recurrence_gradSq
        (u : SobolevData (centeredCube z 1 one_pos))) := ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by
    rw [hKc]
    have := aux_aux_macro_energy_recurrence_P_nonneg (d := d) Sreg.C alpha N n
    have := aux_aux_macro_energy_recurrence_gradSq_nonneg
      (u : SobolevData (centeredCube z 1 one_pos))
    positivity
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (lam / 2) (Real.sqrt (ε / (Kc + 1))) := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hηdef]
    exact lt_min (half_pos hlam) (Real.sqrt_pos.2 (div_pos hε (by linarith)))
  have hηl : η ≤ lam / 2 := by rw [hηdef]; exact min_le_left _ _
  have hηsq : Kc * η ^ 2 ≤ ε := by
    have h1' : η ^ 2 ≤ ε / (Kc + 1) := by
      have : η ≤ Real.sqrt (ε / (Kc + 1)) := by rw [hηdef]; exact min_le_right _ _
      calc η ^ 2 ≤ (Real.sqrt (ε / (Kc + 1))) ^ 2 := pow_le_pow_left₀ hη0.le this 2
        _ = ε / (Kc + 1) := Real.sq_sqrt (div_nonneg hε.le (by linarith))
    calc Kc * η ^ 2 ≤ Kc * (ε / (Kc + 1)) := mul_le_mul_of_nonneg_left h1' hKc0
      _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith
  have hηae : ∀ᵐ y ∂volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d)),
      |(cutoffPositiveCoefficient M (fun _ => 0) om N z one_pos).val y -
        cutoffCoefficient M (fun _ => 0) om N y| < η := by
    filter_upwards [aux_aux_macro_energy_recurrence_coeff_ae M (fun _ => 0) om N z one_pos]
      with y hy
    rw [hy, sub_self, abs_zero]
    exact hη0
  have hstep := aux_aux_macro_energy_recurrence_core_step hd Cp hFE M Sreg hchild alpha hδ hα
    (fun _ => 0) om N z one_pos hR lam Λ 1 hlam hlamA hΛA hKr F Kf hKf hFm hFb φ Cφ hφ hCφ b u hb
    hu x hx n 0 (cutoffPositiveCoefficient M (fun _ => 0) om N z one_pos) cFin hcF hcoef η hηl
    hηae hn'
  have heq : (16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C alpha N n + 2) * Λ *
      (4 * η ^ 2 / lam ^ 2 * aux_aux_macro_energy_recurrence_gradSq
        (u : SobolevData (centeredCube z 1 one_pos))) = Kc * η ^ 2 := by
    rw [hKc]; ring
  rw [heq] at hstep
  linarith

/-- **The macro range for the zero-infrared coefficient** at one sample: for
`3^{-N} ≤ ρ ≤ 1`, `Γ(B_ρ ∩ Q) ≤ Z ρ^{t₁} K (K_f + C_φ)²`, from the exact one-centre estimate
(`L' = 0`) above the prefix and the global energy below it. -/
theorem aux_lem_prefix_limit_atom_extraction_macro0 (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (t1 : ℝ) (ht1 : (d : ℝ) - 1 < t1) (ht1' : t1 < d)
    (hδ : M.delta ≤ Sreg.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg.alphaRange)
    (om : BilateralField d) (N : ℕ) (z : SpatialCoordinates d)
    (P0 : ℕ) (hpre : Sreg.prefixLen N (1 - ((d : ℝ) - t1) / 4) N ((3 : ℝ) ^ N • z)
      (aux_aux_macro_energy_recurrence_relabel N om) ≤ P0)
    (Kmac : ℝ) (hKref : (3 : ℝ) ^ (t1 * (P0 : ℝ)) ≤ Kmac)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d)), |F x| ≤ Kf)
    (φ : SpatialCoordinates d → ℝ) (Cφ : ℝ) (hφ : ContDiff ℝ 2 φ)
    (hCφ : c2Norm (closedCube z 1 one_pos : Set (SpatialCoordinates d)) φ ≤ Cφ)
    (b u : weakSobolevGraph (centeredCube z 1 one_pos))
    (hb : ((b : SobolevData (centeredCube z 1 one_pos)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))] φ)
    (hu : SolvesDirichlet (cutoffPositiveCoefficient M (fun _ => 0) om N z one_pos) F b u)
    (hKsrc : (3 : ℝ) ^ (t1 * (P0 : ℝ)) *
      sobolevCoefficientForm (cutoffPositiveCoefficient M (fun _ => 0) om N z one_pos)
        (u : SobolevData (centeredCube z 1 one_pos)) (u : SobolevData (centeredCube z 1 one_pos)) ≤
      Kmac * (Kf + Cφ) ^ 2)
    (x : SpatialCoordinates d) (ρ : ℝ)
    (hx : x ∈ (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hρN : (3 : ℝ) ^ (-(N : ℤ)) ≤ ρ) :
    localGradientEnergy (cutoffPositiveCoefficient M (fun _ => 0) om N z one_pos)
        (s := Metric.ball x ρ ∩ (centeredCube z 1 one_pos : Set (SpatialCoordinates d)))
        (isOpen_ball.measurableSet.inter (centeredCube z 1 one_pos).isOpen.measurableSet)
        (sobolevGradient (u : SobolevData (centeredCube z 1 one_pos))) ≤
      aux_aux_macro_energy_recurrence_Z Sreg.C Cp t1 d * (ρ ^ t1 * (Kmac * (Kf + Cφ) ^ 2)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht10 : 0 < t1 := lt_of_le_of_lt (by linarith only [hdR] : (0 : ℝ) ≤ (d : ℝ) - 1) ht1
  have h3P : 1 ≤ (3 : ℝ) ^ (t1 * (P0 : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg ht10.le (Nat.cast_nonneg _))
  have hfA0 := sobolevCoefficientForm_nonneg
    (cutoffPositiveCoefficient M (fun _ => 0) om N z one_pos)
    (u : SobolevData (centeredCube z 1 one_pos))
  have hfA : sobolevCoefficientForm (cutoffPositiveCoefficient M (fun _ => 0) om N z one_pos)
      (u : SobolevData (centeredCube z 1 one_pos)) (u : SobolevData (centeredCube z 1 one_pos)) ≤
      Kmac * (Kf + Cφ) ^ 2 := (le_mul_of_one_le_left hfA0 h3P).trans hKsrc
  have hCφ0 : 0 ≤ Cφ := (aux_aux_macro_energy_recurrence_c2Norm_nonneg _ φ).trans hCφ
  have hX0 : 0 ≤ Kmac * (Kf + Cφ) ^ 2 := hfA0.trans hfA
  have hρt : 0 ≤ ρ ^ t1 := Real.rpow_nonneg hρ.le _
  have hR : (0 : ℝ) < 3 ^ N := by positivity
  by_cases hcase : ((3 : ℝ) ^ P0)⁻¹ / 2 ≤ ρ
  · refine aux_aux_macro_energy_recurrence_initial_close d Sreg.C Cp t1 ρ (Kmac * (Kf + Cφ) ^ 2)
      _ _ P0 ht10 hρ hcase hX0 ?_ hKsrc
    exact localGradientEnergy_le _ _ _
  · push_neg at hcase
    obtain ⟨n, hnP, hρn, h6⟩ := aux_aux_macro_energy_recurrence_select_n N P0 ρ hρN hcase
    have hcore := aux_lem_prefix_limit_atom_extraction_core0 hd Cp hFE M Sreg Sreg.energy_density
      (1 - ((d : ℝ) - t1) / 4) hδ hα om N z hR P0 hpre F Kf hKf hFm hFb φ Cφ hφ hCφ b u hb hu
      x hx n hnP
    have hmono := aux_aux_macro_energy_recurrence_localEnergy_mono
      (cutoffPositiveCoefficient M (fun _ => 0) om N z one_pos)
      (isOpen_ball.measurableSet.inter (centeredCube z 1 one_pos).isOpen.measurableSet :
        MeasurableSet (Metric.ball x ρ ∩ (centeredCube z 1 one_pos : Set (SpatialCoordinates d))))
      (isOpen_ball.measurableSet.inter (centeredCube z 1 one_pos).isOpen.measurableSet :
        MeasurableSet (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
          (centeredCube z 1 one_pos : Set (SpatialCoordinates d))))
      (Set.inter_subset_inter_left _ (Metric.ball_subset_ball hρn))
      (sobolevGradient (u : SobolevData (centeredCube z 1 one_pos)))
    have hK0 : 0 ≤ Kmac := (zero_le_one.trans h3P).trans hKref
    have hcore' : localGradientEnergy (cutoffPositiveCoefficient M (fun _ => 0) om N z one_pos)
        (isOpen_ball.measurableSet.inter (centeredCube z 1 one_pos).isOpen.measurableSet :
          MeasurableSet (Metric.ball x (((3 : ℝ) ^ N)⁻¹ * ((3 : ℝ) ^ n / 2)) ∩
            (centeredCube z 1 one_pos : Set (SpatialCoordinates d))))
        (sobolevGradient (u : SobolevData (centeredCube z 1 one_pos))) ≤
        16 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C (1 - ((d : ℝ) - t1) / 4) N n *
          sobolevCoefficientForm (cutoffPositiveCoefficient M (fun _ => 0) om N z one_pos)
            (u : SobolevData _) (u : SobolevData _) +
        8 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C (1 - ((d : ℝ) - t1) / 4) N n *
          Kmac * (Cp ^ 2 * Kf ^ 2 + (d : ℝ) ^ 2 * Cφ ^ 2) := by
      refine hcore.trans ?_
      have hP0 := aux_aux_macro_energy_recurrence_P_nonneg (d := d) Sreg.C
        (1 - ((d : ℝ) - t1) / 4) N n
      have hK1 : (1 : ℝ) ≤ Kmac := h3P.trans hKref
      have hS0 : 0 ≤ Cp ^ 2 * Kf ^ 2 + (d : ℝ) ^ 2 * Cφ ^ 2 := by positivity
      have : 8 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C (1 - ((d : ℝ) - t1) / 4) N n
          * 1 * (Cp ^ 2 * Kf ^ 2 + (d : ℝ) ^ 2 * Cφ ^ 2) ≤
          8 * aux_aux_macro_energy_recurrence_P (d := d) Sreg.C (1 - ((d : ℝ) - t1) / 4) N n *
          Kmac * (Cp ^ 2 * Kf ^ 2 + (d : ℝ) ^ 2 * Cφ ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hS0
        exact mul_le_mul_of_nonneg_left hK1 (by positivity)
      linarith
    exact aux_aux_macro_energy_recurrence_onecentre_close d Sreg.C Cp t1 ρ Kf Cφ Kmac _ _ _
      (aux_aux_macro_energy_recurrence_P_nonneg (d := d) Sreg.C (1 - ((d : ℝ) - t1) / 4) N n)
      (aux_aux_macro_energy_recurrence_P_le (d := d) Sreg.C t1 ρ N n hdR ht1 ht1' hρ hρ1 h6)
      hKf hCφ0 hK0 hρt hfA (hmono.trans hcore')

end PaeG0Core

section PaeG0Ext

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

variable {d : ℕ}

/-- `A_N^0 = A_N e^{-H}` pointwise. -/
theorem aux_lem_prefix_limit_atom_extraction_cutoff_zero_eq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) :
    cutoffCoefficient M (fun _ => 0) om N x =
      cutoffCoefficient M H om N x * Real.exp (-(H om x)) := by
  unfold cutoffCoefficient cutoffPotential
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  simp only [ContinuousMap.zero_apply]
  ring

/-- `log A_N^0` is the negative-layer sum minus a deterministic constant. -/
theorem aux_lem_prefix_limit_atom_extraction_log_cutoff_zero (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (om : BilateralField d) (N : ℕ) (x y : SpatialCoordinates d) :
    Real.log (cutoffCoefficient M (fun _ => 0) om N x) -
        Real.log (cutoffCoefficient M (fun _ => 0) om N y) =
      (∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) x) -
        ∑ j ∈ Finset.range (N + 1), om (-(Int.ofNat j)) y := by
  unfold cutoffCoefficient cutoffPotential
  have ha : 0 < (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ := inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
  rw [Real.log_mul ha.ne' (Real.exp_pos _).ne', Real.log_mul ha.ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_exp]
  simp only [ContinuousMap.zero_apply, zero_add]
  ring

/-- The envelope transfer at one sample. -/
theorem aux_lem_prefix_limit_atom_extraction_env_zero (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (K : Set (SpatialCoordinates d))
    (om : BilateralField d) (N : ℕ) (S mlow mhigh : ℝ) (hS : ∀ x ∈ K, |H om x| ≤ S)
    (hlo : 0 < mlow)
    (hbd : ∀ x ∈ K, mlow ≤ cutoffCoefficient M H om N x ∧ cutoffCoefficient M H om N x ≤ mhigh)
    (hne : K.Nonempty) :
    0 < Real.exp S * |mhigh + mlow⁻¹| ∧
    ∀ x ∈ K, (Real.exp S * |mhigh + mlow⁻¹|)⁻¹ ≤ cutoffCoefficient M (fun _ => 0) om N x ∧
      cutoffCoefficient M (fun _ => 0) om N x ≤ Real.exp S * |mhigh + mlow⁻¹| := by
  obtain ⟨x0, hx0⟩ := hne
  have hhigh : 0 < mhigh := hlo.trans_le ((hbd x0 hx0).1.trans (hbd x0 hx0).2)
  have hY : 0 < mhigh + mlow⁻¹ := add_pos hhigh (inv_pos.mpr hlo)
  rw [abs_of_pos hY]
  refine ⟨mul_pos (Real.exp_pos _) hY, fun x hx => ?_⟩
  have hb := hbd x hx
  have hSx := hS x hx
  rw [aux_lem_prefix_limit_atom_extraction_cutoff_zero_eq M H om N x]
  constructor
  · rw [mul_inv]
    have e1 : (Real.exp S)⁻¹ ≤ Real.exp (-(H om x)) := by
      rw [← Real.exp_neg]
      exact Real.exp_le_exp.mpr (by linarith [le_abs_self (H om x)])
    have e2 : (mhigh + mlow⁻¹)⁻¹ ≤ cutoffCoefficient M H om N x := by
      calc (mhigh + mlow⁻¹)⁻¹ ≤ (mlow⁻¹)⁻¹ :=
            inv_anti₀ (inv_pos.mpr hlo) (le_add_of_nonneg_left hhigh.le)
        _ = mlow := inv_inv _
        _ ≤ _ := hb.1
    calc (Real.exp S)⁻¹ * (mhigh + mlow⁻¹)⁻¹
        ≤ Real.exp (-(H om x)) * cutoffCoefficient M H om N x :=
          mul_le_mul e1 e2 (by positivity) (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  · have e1 : Real.exp (-(H om x)) ≤ Real.exp S :=
      Real.exp_le_exp.mpr (by linarith [neg_abs_le (H om x)])
    have e2 : cutoffCoefficient M H om N x ≤ mhigh + mlow⁻¹ :=
      hb.2.trans (le_add_of_nonneg_right (inv_pos.mpr hlo).le)
    calc cutoffCoefficient M H om N x * Real.exp (-(H om x))
        ≤ (mhigh + mlow⁻¹) * Real.exp S := mul_le_mul e2 e1 (Real.exp_pos _).le hY.le
      _ = _ := mul_comm _ _

/-- The compact sup of the infrared field bounds it pointwise. -/
theorem aux_lem_prefix_limit_atom_extraction_restrict_bound
    (h : C(SpatialCoordinates d, ℝ)) (K : Compacts (SpatialCoordinates d)) :
    ∀ x ∈ (K : Set (SpatialCoordinates d)), |h x| ≤ ‖h.restrict (K : Set (SpatialCoordinates d))‖ := by
  intro x hx
  have := ContinuousMap.norm_coe_le_norm (h.restrict (K : Set (SpatialCoordinates d))) ⟨x, hx⟩
  rw [Real.norm_eq_abs] at this
  exact this

/-- `e^{‖H‖_{C(K)}}` has all moments. -/
theorem aux_lem_prefix_limit_atom_extraction_expSup_memLp (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (K : Compacts (SpatialCoordinates d)) (q : ℝ)
    (hq : 0 < q) :
    MemLp (fun om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
      (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure := by
  have hint := exists_compactExponentialMoment_of_infraredCharacterization hd M H hH K q hq.le
  have hmeasR : Measurable fun om => ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ :=
    (ContinuousMap.continuous_restrict (K : Set (SpatialCoordinates d))).norm.measurable.comp hH.1
  have hmeas : AEStronglyMeasurable
      (fun om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
      (chaosSampleLaw M).toMeasure :=
    (Real.measurable_exp.comp hmeasR).aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hmeas (by simp [hq]) ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal hq.le]
  refine hint.congr (Filter.Eventually.of_forall fun om => ?_)
  simp only
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_mul, mul_comm]

/-- **Extremes of `A_N^0` on `closedCube z 1`** with the moment shape of `lem_extremes`. -/
theorem aux_lem_prefix_limit_atom_extraction_extremes0 (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ Cp Cd cd : ℝ, 0 < Cp ∧ 0 < Cd ∧ 0 < cd ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ cd / (2 * q) →
        ∃ (D Mx : ℕ → BilateralField d → ℝ) (CE : ℝ), 0 ≤ CE ∧
          (∀ N om, 0 ≤ D N om ∧ 0 ≤ Mx N om) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
            0 < Mx N om ∧
            (∀ x ∈ (closedCube z 1 one_pos : Set (SpatialCoordinates d)),
              (Mx N om)⁻¹ ≤ cutoffCoefficient M (fun _ => 0) om N x ∧
                cutoffCoefficient M (fun _ => 0) om N x ≤ Mx N om) ∧
            (∀ x y, x ∈ (closedCube z 1 one_pos : Set (SpatialCoordinates d)) →
              y ∈ (closedCube z 1 one_pos : Set (SpatialCoordinates d)) →
              |Real.log (cutoffCoefficient M (fun _ => 0) om N x) -
                  Real.log (cutoffCoefficient M (fun _ => 0) om N y)| ≤
                D N om * (3 : ℝ) ^ N * dist x y)) ∧
          (∀ N, MemLp (D N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
            MemLp (Mx N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure) ∧
          (∀ N, eLpNorm (D N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cp * Real.sqrt (1 + (N : ℝ)))) ∧
          (∀ N, eLpNorm (Mx N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (CE * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N))) := by
  obtain ⟨CpE, Cd, cdE, hCpE, hCd, hcdE, hext⟩ :=
    aux_lem_extremes_compat d hd z 1 one_pos (2 * q) (by linarith)
  obtain ⟨CU, cU, hCU, hcU, hU⟩ :=
    finite_negative_layer_log_lipschitz_majorant d hd z 1 one_pos q hq
  refine ⟨max CpE CU, Cd, min cdE (2 * cU), lt_max_of_lt_left hCpE, hCd,
    lt_min hcdE (by positivity), ?_⟩
  intro M hδ
  have hq0 : 0 < q := by linarith
  have h2q : 0 < 2 * q := by linarith
  have hδE : M.delta ≤ cdE / (2 * q) :=
    hδ.trans (div_le_div_of_nonneg_right (min_le_left _ _) h2q.le)
  have hδU : M.delta ≤ cU / q := by
    have := hδ.trans (div_le_div_of_nonneg_right (min_le_right _ _) h2q.le)
    rw [show 2 * cU / (2 * q) = cU / q by field_simp] at this
    exact this
  have hδ0 : 0 < M.delta := M.shellPrefix.delta_pos
  have hδ1 : M.delta ≤ 1 := M.shellPrefix.delta_le_half.trans (by norm_num)
  obtain ⟨H, hH⟩ := exists_infraredCharacterization hd M
  obtain ⟨D0, mlow, mhigh, _hD0, hae0, _hD0mem, hYmem, _hD0mom, hYmom⟩ := hext M H hH hδE
  obtain ⟨U, hU0, haeU, hUmem, hUmom⟩ := hU M hδU
  set K : Compacts (SpatialCoordinates d) := closedCube z 1 one_pos with hK
  have hEmem := aux_lem_prefix_limit_atom_extraction_expSup_memLp hd M H hH K (2 * q) h2q
  set CE0 := (eLpNorm (fun om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
    (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure).toReal with hCE0def
  have hCE0 : eLpNorm (fun om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖)
      (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure = ENNReal.ofReal CE0 :=
    (ENNReal.ofReal_toReal hEmem.eLpNorm_lt_top.ne).symm
  have hYabs : ∀ N, MemLp (fun om => |mhigh N om + (mlow N om)⁻¹|) (ENNReal.ofReal (2 * q))
      (chaosSampleLaw M).toMeasure := by
    intro N
    simpa only [Real.norm_eq_abs] using (hYmem N).norm
  refine ⟨U, fun N om => Real.exp ‖(H om).restrict (K : Set (SpatialCoordinates d))‖ *
      |mhigh N om + (mlow N om)⁻¹|, CE0 * CpE, mul_nonneg ENNReal.toReal_nonneg hCpE.le,
    fun N om => ⟨hU0 N om, mul_nonneg (Real.exp_pos _).le (abs_nonneg _)⟩, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hae0, haeU] with om h1 h2
    intro N
    obtain ⟨-, hlo, hbd⟩ := h1 N
    have henv := aux_lem_prefix_limit_atom_extraction_env_zero M H (K : Set (SpatialCoordinates d))
      om N _ (mlow N om) (mhigh N om)
      (aux_lem_prefix_limit_atom_extraction_restrict_bound (H om) K) hlo hbd
      ⟨z, Metric.mem_closedBall_self (by norm_num)⟩
    refine ⟨henv.1, henv.2, fun x y hx hy => ?_⟩
    rw [aux_lem_prefix_limit_atom_extraction_log_cutoff_zero M om N x y]
    exact h2 N x y hx hy
  · intro N
    refine ⟨hUmem N, ?_⟩
    have hb := aux_rem_resolved_microscopic_product_lq_bound (chaosSampleLaw M).toMeasure q
      (2 * q) hq0 le_rfl _ _ hEmem (hYabs N)
    exact lt_of_le_of_lt hb (ENNReal.mul_lt_top hEmem.eLpNorm_lt_top (hYabs N).eLpNorm_lt_top)
  · intro N
    refine (hUmom N).trans (ENNReal.ofReal_le_ofReal ?_)
    have hs : 0 ≤ Real.sqrt (1 + (N : ℝ)) := Real.sqrt_nonneg _
    calc CU * M.delta * Real.sqrt (1 + (N : ℝ)) ≤ CU * 1 * Real.sqrt (1 + (N : ℝ)) := by
          gcongr
      _ ≤ max CpE CU * Real.sqrt (1 + (N : ℝ)) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) hs
  · intro N
    have hb := aux_rem_resolved_microscopic_product_lq_bound (chaosSampleLaw M).toMeasure q
      (2 * q) hq0 le_rfl _ _ hEmem (hYabs N)
    have hYn : eLpNorm (fun om => |mhigh N om + (mlow N om)⁻¹|) (ENNReal.ofReal (2 * q))
        (chaosSampleLaw M).toMeasure =
        eLpNorm (fun om => mhigh N om + (mlow N om)⁻¹) (ENNReal.ofReal (2 * q))
          (chaosSampleLaw M).toMeasure := by
      have hn : (fun om => |mhigh N om + (mlow N om)⁻¹|) =
          fun om => ‖mhigh N om + (mlow N om)⁻¹‖ := by
        funext om
        rw [Real.norm_eq_abs]
      rw [hn, eLpNorm_norm]
      simpa using! (hYmem N).aestronglyMeasurable
    have hrate : Real.exp ((Cd * M.delta + CpE * M.delta ^ 2) * N) ≤
        Real.exp ((Cd * M.delta + max CpE CU * M.delta ^ 2) * N) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
      have := mul_le_mul_of_nonneg_right (le_max_left CpE CU) (sq_nonneg M.delta)
      linarith
    calc _ ≤ _ := hb
      _ = ENNReal.ofReal CE0 * eLpNorm (fun om => mhigh N om + (mlow N om)⁻¹)
            (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure := by rw [hCE0, hYn]
      _ ≤ ENNReal.ofReal CE0 *
            ENNReal.ofReal (CpE * Real.exp ((Cd * M.delta + CpE * M.delta ^ 2) * N)) := by
          gcongr; exact hYmom N
      _ = ENNReal.ofReal (CE0 * CpE * Real.exp ((Cd * M.delta + CpE * M.delta ^ 2) * N)) := by
          rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_assoc]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_left hrate (mul_nonneg ENNReal.toReal_nonneg hCpE.le)

end PaeG0Ext

section PaeG0Dir

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

variable {d : ℕ}

/-- The unit-cube potential coefficient is the zero-infrared cutoff coefficient. -/
theorem aux_lem_prefix_limit_atom_extraction_coef_eq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (om : BilateralField d) :
    expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N om) =
      cutoffPositiveCoefficient M (fun _ => 0) om N 0 one_pos := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [expPotentialCoefficient_coeFn (aux_lem_prefix_limit_atom_extraction_pot M N om),
    aux_lem_prefix_limit_atom_extraction_pot_ae M N om,
    aux_aux_macro_energy_recurrence_coeff_ae M (fun _ => 0) om N 0 one_pos] with x h1 h2 h3
  rw [h1, h2, h3, aux_lem_prefix_limit_atom_extraction_log_kappa]
  unfold cutoffCoefficient cutoffPotential
  simp only [ContinuousMap.zero_apply, zero_add, Int.ofNat_eq_natCast]
  have ha := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  rw [show ∀ S A B : ℝ, S - (A + B) = (S - A) + -B from fun S A B => by ring,
    Real.exp_add, Real.exp_neg, Real.exp_log ha, mul_comm]

/-- The constructed affine minimizer solves the Dirichlet problem without source. -/
theorem aux_lem_prefix_limit_atom_extraction_solves_min {Ω : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ z : killedSobolevGraph Ω,
      ‖(z : SobolevData Ω).1‖ ≤ K * ‖subspaceGradient (killedSobolevGraph Ω) z‖)
    (a : PositiveCoefficient Ω) (b : weakSobolevGraph Ω) :
    SolvesDirichlet a 0 b (dirichletMinimizer (killedResponseSpace hP) a b) := by
  refine ⟨dirichletMinimizer_mem_affine (killedResponseSpace hP) a b, fun ψ => ?_⟩
  simp only [Pi.zero_apply, zero_mul, integral_zero]
  exact dirichletMinimizer_euler (killedResponseSpace hP) a b ψ

theorem aux_lem_prefix_limit_atom_extraction_physical0 {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t t1 C : ℝ) (ht0 : 0 ≤ t) (htt1 : t < t1) (ht1d : t1 < (d : ℝ)) (hC : 0 < C)
    (hmic : aux_prop_growth_energy_assembly_MicroLocal d t t1 C)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1)
    (Kmacv Dv Mxv : ℝ) (hK0 : 0 ≤ Kmacv) (hD0 : 0 ≤ Dv) (hMx : 0 < Mxv)
    (henv : ∀ x ∈ (closedCube z r hr : Set (SpatialCoordinates d)),
      Mxv⁻¹ ≤ cutoffCoefficient M H om N x ∧ cutoffCoefficient M H om N x ≤ Mxv)
    (hlip : ∀ x y, x ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      y ∈ (closedCube z r hr : Set (SpatialCoordinates d)) →
      |Real.log (cutoffCoefficient M H om N x) - Real.log (cutoffCoefficient M H om N y)| ≤
        Dv * (3 : ℝ) ^ N * dist x y)
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hFm : AEMeasurable F (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hFb : ∀ᵐ x ∂(volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))), |F x| ≤ Kf)
    (phi : SpatialCoordinates d → ℝ) (Cphi : ℝ) (hphi : ContDiff ℝ 2 phi)
    (hCphi : c2Norm (closedCube z r hr : Set (SpatialCoordinates d)) phi ≤ Cphi)
    (b u : weakSobolevGraph (centeredCube z r hr))
    (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi)
    (hsol : SolvesDirichlet (cutoffPositiveCoefficient M H om N z hr) F b u)
    (hmacro1 : ∀ (x : SpatialCoordinates d) (rad : ℝ),
      x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 → (3 : ℝ) ^ (-(N : ℤ)) ≤ rad →
      localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
          (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
          (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
        Kmacv * (Kf + Cphi) ^ 2 * rad ^ t1) :
    ∀ (x : SpatialCoordinates d) (rad : ℝ),
        x ∈ centeredCube z r hr → 0 < rad → rad ≤ 1 →
        localGradientEnergy (cutoffPositiveCoefficient M H om N z hr)
            (s := Metric.ball x rad ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet)
            (sobolevGradient (u : SobolevData (centeredCube z r hr))) ≤
          ((2 / r) ^ t * Kmacv + aux_prop_growth_energy_assembly_Cr d r t t1 C *
            ((1 + Dv) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * Kmacv +
              Mxv * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t) +
              Mxv * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) * (1 + Dv) ^ t)) *
            (Kf + Cphi) ^ 2 * rad ^ t := by
  intro x rad hx hrad0 hrad1
  have hCphi0 : 0 ≤ Cphi :=
    (aux_prop_growth_energy_assembly_c2Norm_nonneg _ _).trans hCphi
  have hE0 : 0 ≤ (Kf + Cphi) ^ 2 := sq_nonneg _
  have ht1 : 0 ≤ t1 := by linarith
  set w : ℝ := (3 : ℝ) ^ (-(N : ℝ)) with hwdef
  have hw0 : 0 < w := by positivity
  have hw1 : w ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)
  have hwz : (3 : ℝ) ^ (-(N : ℤ)) = w := aux_prop_growth_energy_assembly_zpow_eq_rpow N
  have hw3 : (3 : ℝ) ^ N * w = 1 := by
    rw [hwdef, Real.rpow_neg (by norm_num), Real.rpow_natCast]
    exact mul_inv_cancel₀ (by positivity)
  -- the local energy as a function of the radius
  set a := cutoffPositiveCoefficient M H om N z hr with ha
  set g := sobolevGradient (u : SobolevData (centeredCube z r hr)) with hg
  let L : ℝ → ℝ := fun ρ => localGradientEnergy a
    (s := Metric.ball x ρ ∩ (centeredCube z r hr : Set (SpatialCoordinates d)))
    (isOpen_ball.measurableSet.inter (centeredCube z r hr).isOpen.measurableSet) g
  have hLmono : ∀ r1 r2 : ℝ, 0 < r1 → r1 ≤ r2 → L r1 ≤ L r2 := by
    intro r1 r2 _ h12
    exact SubdiffusiveProcess.Lane3.localGradientEnergy_mono a _ _
      (Set.inter_subset_inter_left _ (Metric.ball_subset_ball h12)) g
  have hLsat : ∀ ρ : ℝ, 1 ≤ ρ → L ρ ≤ L 1 := by
    intro ρ _
    refine SubdiffusiveProcess.Lane3.localGradientEnergy_mono a _ _ ?_ g
    intro y hy
    refine ⟨?_, hy.2⟩
    have hyz : dist y z < r / 2 := hy.2
    have hxz : dist x z < r / 2 := hx
    change dist y x < 1
    calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
      _ < r / 2 + r / 2 := by rw [dist_comm z x]; linarith
      _ ≤ 1 := by linarith
  have hLmac : ∀ ρ : ℝ, w ≤ ρ → ρ ≤ 1 → L ρ ≤ Kmacv * (Kf + Cphi) ^ 2 * ρ ^ t1 := by
    intro ρ hwρ hρ1
    exact hmacro1 x ρ hx
      (lt_of_lt_of_le hw0 hwρ) hρ1 (by rw [hwz]; exact hwρ)
  have hKE : 0 ≤ Kmacv * (Kf + Cphi) ^ 2 := mul_nonneg hK0 hE0
  have hLall := aux_prop_growth_energy_assembly_lmac L w (Kmacv * (Kf + Cphi) ^ 2) t1 hw1 hKE
    ht1 hLmono hLsat hLmac
  -- the two nonnegative pieces of the constant
  set Zs := (1 + Dv) ^ t * w ^ (t1 - t) * Kmacv + Mxv * w ^ ((d : ℝ) + 2 - t) +
    Mxv * w ^ ((d : ℝ) - t) * (1 + Dv) ^ t with hZs
  have hZs0 : 0 ≤ Zs := by
    have h1 : 0 ≤ (1 + Dv) ^ t := Real.rpow_nonneg (by linarith) _
    have h2 : 0 ≤ w ^ (t1 - t) := Real.rpow_nonneg hw0.le _
    have h3 : 0 ≤ w ^ ((d : ℝ) + 2 - t) := Real.rpow_nonneg hw0.le _
    have h4 : 0 ≤ w ^ ((d : ℝ) - t) := Real.rpow_nonneg hw0.le _
    have := hMx.le
    positivity
  have hCr0 := aux_prop_growth_energy_assembly_Cr_nonneg d r t t1 C hr hC.le
  have hradt : 0 ≤ rad ^ t := Real.rpow_nonneg hrad0.le _
  have h2r : 0 ≤ (2 / r) ^ t := Real.rpow_nonneg (by positivity) _
  have hA0 : 0 ≤ (2 / r) ^ t * Kmacv * (Kf + Cphi) ^ 2 * rad ^ t := by positivity
  have hB0 : 0 ≤ aux_prop_growth_energy_assembly_Cr d r t t1 C * Zs * (Kf + Cphi) ^ 2 *
      rad ^ t := by positivity
  have hsplit : ((2 / r) ^ t * Kmacv + aux_prop_growth_energy_assembly_Cr d r t t1 C * Zs) *
      (Kf + Cphi) ^ 2 * rad ^ t =
      (2 / r) ^ t * Kmacv * (Kf + Cphi) ^ 2 * rad ^ t +
        aux_prop_growth_energy_assembly_Cr d r t t1 C * Zs * (Kf + Cphi) ^ 2 * rad ^ t := by
    ring
  change L rad ≤ _
  rw [hsplit]
  by_cases hcase : w ≤ 2 * rad ∨ r ≤ 2 * rad
  · -- macro range
    have h1 := hLall rad hrad0
    have h2 := aux_prop_growth_energy_assembly_case_macro w r rad t t1
      (Kmacv * (Kf + Cphi) ^ 2) hw1 hr hr1 hrad0 hrad1 ht0 htt1.le hKE hcase
    have h3 : (2 / r) ^ t * (Kmacv * (Kf + Cphi) ^ 2) * rad ^ t =
        (2 / r) ^ t * Kmacv * (Kf + Cphi) ^ 2 * rad ^ t := by ring
    linarith
  · -- microscopic range, through the unit cube
    push_neg at hcase
    obtain ⟨hcw, hcr⟩ := hcase
    exact le_add_of_nonneg_of_le hA0
      (aux_prop_growth_energy_assembly_micro_branch t t1 C ht0 htt1 ht1d hC hmic M H om N z r hr hr1
        Kmacv Dv Mxv hK0 hD0 hMx henv hlip F Kf hKf hFm hFb phi Cphi hphi hCphi b u hb hsol
        x rad hx hrad0 w hw0 hw1 hw3 hcw hcr hLall)

/-- Local energy only sees the part of the set inside the domain. -/
theorem aux_lem_prefix_limit_atom_extraction_lge_inter {Ω : Opens (SpatialCoordinates d)}
    (a : PositiveCoefficient Ω) {s : Set (SpatialCoordinates d)} (hs : MeasurableSet s)
    (hsΩ : MeasurableSet (s ∩ (Ω : Set (SpatialCoordinates d)))) (g : HilbertGradient Ω) :
    localGradientEnergy a hsΩ g = localGradientEnergy a hs g := by
  rw [localGradientEnergy_eq_integral, localGradientEnergy_eq_integral]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.restrict_restrict hsΩ, Measure.restrict_restrict hs, Set.inter_assoc,
    Set.inter_self]

/-- The prefix length used at cutoff `N` (exact finite depth `L' = 0`, root `0`). -/
def aux_lem_prefix_limit_atom_extraction_P0
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M) (alpha : ℝ) (z : SpatialCoordinates d)
    (N : ℕ) (om : BilateralField d) : ℕ :=
  Sreg.prefixLen N alpha N ((3 : ℝ) ^ N • z) (aux_aux_macro_energy_recurrence_relabel N om)

/-- The macro constant: prefix factor times the affine Dirichlet response. -/
def aux_lem_prefix_limit_atom_extraction_Kmac0 [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M) (t1 : ℝ) (u : Fin d → ℝ)
    (N : ℕ) (om : BilateralField d) : ℝ :=
  (3 : ℝ) ^ (t1 * (aux_lem_prefix_limit_atom_extraction_P0 Sreg (1 - ((d : ℝ) - t1) / 4) 0 N om : ℝ)) *
    (1 + aux_lem_prefix_limit_atom_extraction_Dz M u N om)

/-- **Per-sample all-radii bound** for the affine Dirichlet minimizer of `A_N^0` on `Q₀`. -/
theorem aux_lem_prefix_limit_atom_extraction_dir_sample [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (t t1 C : ℝ) (ht0 : 0 ≤ t) (htt1 : t < t1) (ht1 : (d : ℝ) - 1 < t1) (ht1d : t1 < (d : ℝ))
    (hC : 0 < C) (hmic : aux_prop_growth_energy_assembly_MicroLocal d t t1 C)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (hδC : M.delta ≤ Sreg.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg.alphaRange)
    (u : Fin d → ℝ) (Cφ : ℝ)
    (hCφ : c2Norm (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun z => affineSlope u z + 0) ≤ Cφ) (hCφ1 : 1 ≤ Cφ)
    (om : BilateralField d) (N : ℕ) (Dv Mxv : ℝ) (hD0 : 0 ≤ Dv) (hMx : 0 < Mxv)
    (henv : ∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
      Mxv⁻¹ ≤ cutoffCoefficient M (fun _ => 0) om N x ∧
        cutoffCoefficient M (fun _ => 0) om N x ≤ Mxv)
    (hlip : ∀ x y, x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) →
      y ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) →
      |Real.log (cutoffCoefficient M (fun _ => 0) om N x) -
        Real.log (cutoffCoefficient M (fun _ => 0) om N y)| ≤ Dv * (3 : ℝ) ^ N * dist x y)
    (x : SpatialCoordinates d)
    (hx : x ∈ ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
      Set (SpatialCoordinates d)))
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    localGradientEnergy
        (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N om))
        (s := Metric.ball x ρ) Metric.isOpen_ball.measurableSet
        (sobolevGradient (dirichletMinimizer
          (killedResponseSpace aux_lem_prefix_limit_atom_extraction_poincare.1)
          (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N om))
          (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0)).val) ≤
      ((2 / 1) ^ t * (aux_aux_macro_energy_recurrence_Z Sreg.C Cp t1 d *
          aux_lem_prefix_limit_atom_extraction_Kmac0 M Sreg t1 u N om) +
        aux_prop_growth_energy_assembly_Cr d 1 t t1 C *
          ((1 + Dv) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) *
              (aux_aux_macro_energy_recurrence_Z Sreg.C Cp t1 d *
                aux_lem_prefix_limit_atom_extraction_Kmac0 M Sreg t1 u N om) +
            Mxv * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t) +
            Mxv * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) - t) * (1 + Dv) ^ t)) *
        (0 + Cφ) ^ 2 * ρ ^ t := by
  have hDz : aux_lem_prefix_limit_atom_extraction_Dz M u N om =
      sobolevCoefficientForm (cutoffPositiveCoefficient M (fun _ => 0) om N 0 one_pos)
        (dirichletMinimizer (killedResponseSpace aux_lem_prefix_limit_atom_extraction_poincare.1)
          (cutoffPositiveCoefficient M (fun _ => 0) om N 0 one_pos)
          (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0)).val
        (dirichletMinimizer (killedResponseSpace aux_lem_prefix_limit_atom_extraction_poincare.1)
          (cutoffPositiveCoefficient M (fun _ => 0) om N 0 one_pos)
          (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0)).val := by
    unfold aux_lem_prefix_limit_atom_extraction_Dz aux_lem_prefix_limit_atom_extraction_D
      affineDirichletResponse dirichletResponse
    rw [aux_lem_prefix_limit_atom_extraction_coef_eq]
  have hDz0 : 0 ≤ aux_lem_prefix_limit_atom_extraction_Dz M u N om :=
    aux_lem_prefix_limit_atom_extraction_D_nonneg _ _
  rw [aux_lem_prefix_limit_atom_extraction_coef_eq M N om]
  obtain ⟨a, ha⟩ : ∃ a : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      a = cutoffPositiveCoefficient M (fun _ => 0) om N 0 one_pos := ⟨_, rfl⟩
  obtain ⟨umin, humin⟩ : ∃ umin : weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 one_pos),
      umin = dirichletMinimizer (killedResponseSpace aux_lem_prefix_limit_atom_extraction_poincare.1)
        (cutoffPositiveCoefficient M (fun _ => 0) om N 0 one_pos)
        (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0) := ⟨_, rfl⟩
  rw [← humin] at hDz ⊢
  have hsol : SolvesDirichlet (cutoffPositiveCoefficient M (fun _ => 0) om N 0 one_pos) 0
      (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0) umin := by
    rw [humin]; exact aux_lem_prefix_limit_atom_extraction_solves_min _ _ _
  have hb := affineL2_coeFn (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0
  have hφ : ContDiff ℝ 2 (fun z : SpatialCoordinates d => affineSlope u z + 0) :=
    (affineSlope u).contDiff.add contDiff_const
  have hFm : AEMeasurable (0 : SpatialCoordinates d → ℝ)
      (volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))) :=
    aemeasurable_const
  have hFb : ∀ᵐ x ∂(volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))),
      |(0 : SpatialCoordinates d → ℝ) x| ≤ 0 := Filter.Eventually.of_forall fun _ => by simp
  have h3P : 1 ≤ (3 : ℝ) ^ (t1 * (aux_lem_prefix_limit_atom_extraction_P0 Sreg
      (1 - ((d : ℝ) - t1) / 4) 0 N om : ℝ)) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (by linarith [(show (1 : ℝ) ≤ d by
      exact_mod_cast (show 1 ≤ d by omega))]) (Nat.cast_nonneg _))
  have hKref : (3 : ℝ) ^ (t1 * (aux_lem_prefix_limit_atom_extraction_P0 Sreg
      (1 - ((d : ℝ) - t1) / 4) 0 N om : ℝ)) ≤ aux_lem_prefix_limit_atom_extraction_Kmac0 M Sreg t1 u N om := by
    unfold aux_lem_prefix_limit_atom_extraction_Kmac0
    exact le_mul_of_one_le_right (by linarith) (by linarith)
  have hKsrc : (3 : ℝ) ^ (t1 * (aux_lem_prefix_limit_atom_extraction_P0 Sreg
      (1 - ((d : ℝ) - t1) / 4) 0 N om : ℝ)) *
      sobolevCoefficientForm (cutoffPositiveCoefficient M (fun _ => 0) om N 0 one_pos)
        (umin : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))
        (umin : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos)) ≤
      aux_lem_prefix_limit_atom_extraction_Kmac0 M Sreg t1 u N om * (0 + Cφ) ^ 2 := by
    rw [← hDz]
    unfold aux_lem_prefix_limit_atom_extraction_Kmac0
    have hC2 : 1 ≤ (0 + Cφ) ^ 2 := by rw [zero_add]; nlinarith
    have h0 : 0 ≤ (3 : ℝ) ^ (t1 * (aux_lem_prefix_limit_atom_extraction_P0 Sreg
      (1 - ((d : ℝ) - t1) / 4) 0 N om : ℝ)) := by linarith
    calc (3 : ℝ) ^ (t1 * (aux_lem_prefix_limit_atom_extraction_P0 Sreg
          (1 - ((d : ℝ) - t1) / 4) 0 N om : ℝ)) * aux_lem_prefix_limit_atom_extraction_Dz M u N om
        ≤ (3 : ℝ) ^ (t1 * (aux_lem_prefix_limit_atom_extraction_P0 Sreg
          (1 - ((d : ℝ) - t1) / 4) 0 N om : ℝ)) * (1 + aux_lem_prefix_limit_atom_extraction_Dz M u N om) :=
          mul_le_mul_of_nonneg_left (by linarith) h0
      _ ≤ _ := le_mul_of_one_le_right (mul_nonneg h0 (by linarith)) hC2
  have hmacro1 : ∀ (x : SpatialCoordinates d) (rad : ℝ),
      x ∈ centeredCube (0 : SpatialCoordinates d) 1 one_pos → 0 < rad → rad ≤ 1 →
      (3 : ℝ) ^ (-(N : ℤ)) ≤ rad →
      localGradientEnergy (cutoffPositiveCoefficient M (fun _ => 0) om N 0 one_pos)
          (s := Metric.ball x rad ∩
            (centeredCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)))
          (isOpen_ball.measurableSet.inter
            (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet)
          (sobolevGradient (umin : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 one_pos))) ≤
        (aux_aux_macro_energy_recurrence_Z Sreg.C Cp t1 d *
          aux_lem_prefix_limit_atom_extraction_Kmac0 M Sreg t1 u N om) * (0 + Cφ) ^ 2 * rad ^ t1 := by
    intro x' rad hx' hrad0 hrad1 hradN
    have h := aux_lem_prefix_limit_atom_extraction_macro0 hd Cp hFE M Sreg t1 ht1 ht1d hδC hα om N 0
      (aux_lem_prefix_limit_atom_extraction_P0 Sreg (1 - ((d : ℝ) - t1) / 4) 0 N om) le_rfl
      (aux_lem_prefix_limit_atom_extraction_Kmac0 M Sreg t1 u N om) hKref 0 0 le_rfl hFm hFb
      (fun z => affineSlope u z + 0) Cφ hφ hCφ
      (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0) umin hb hsol
      hKsrc x' rad hx' hrad0 hrad1 hradN
    calc _ ≤ _ := h
      _ = _ := by ring
  have hZ0 := aux_aux_macro_energy_recurrence_Z_nonneg Sreg.C Cp t1 d
  have hK0 : 0 ≤ aux_aux_macro_energy_recurrence_Z Sreg.C Cp t1 d *
      aux_lem_prefix_limit_atom_extraction_Kmac0 M Sreg t1 u N om :=
    mul_nonneg hZ0 ((zero_le_one.trans h3P).trans hKref)
  have hphys := aux_lem_prefix_limit_atom_extraction_physical0 t t1 C ht0 htt1 ht1d hC hmic M
    (fun _ => 0) om N 0 1 one_pos le_rfl _ Dv Mxv hK0 hD0 hMx henv hlip 0 0 le_rfl hFm hFb
    (fun z => affineSlope u z + 0) Cφ hφ hCφ
    (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0) umin hb hsol
    hmacro1 x ρ hx hρ hρ1
  rw [← aux_lem_prefix_limit_atom_extraction_lge_inter _ Metric.isOpen_ball.measurableSet
    (isOpen_ball.measurableSet.inter
      (centeredCube (0 : SpatialCoordinates d) 1 one_pos).isOpen.measurableSet)]
  exact hphys

/-- `D_u ≤ |Q₀|·2·W_u ≤ 2|Q₀| |u|² (J_sup + 1)`. -/
theorem aux_lem_prefix_limit_atom_extraction_Dz_le [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (u : Fin d → ℝ) (N : ℕ) (om : BilateralField d) :
    aux_lem_prefix_limit_atom_extraction_Dz M u N om ≤
      (2 * volume.real ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)) * ∑ i : Fin d, (u i) ^ 2) *
        aux_lem_prefix_limit_atom_extraction_Rf M N om := by
  set V := 2 * volume.real ((aux_lem_prefix_limit_atom_extraction_Q0 d :
    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) with hV
  have hVpos : 0 < V := mul_pos two_pos aux_lem_prefix_limit_atom_extraction_vol_pos
  set a := expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N om)
  have hW := aux_lem_prefix_limit_atom_extraction_W_le_sq_eval
    (aux_lem_prefix_limit_atom_extraction_pot M N om) u
  have hN0 := aux_lem_prefix_limit_atom_extraction_N_nonneg a u
  have hDW : aux_lem_prefix_limit_atom_extraction_D a u ≤ V *
      aux_lem_prefix_limit_atom_extraction_W a u := by
    unfold aux_lem_prefix_limit_atom_extraction_W
    rw [← hV, mul_div_cancel₀ _ hVpos.ne']
    linarith
  change aux_lem_prefix_limit_atom_extraction_D a u ≤ _
  calc aux_lem_prefix_limit_atom_extraction_D a u ≤ V * aux_lem_prefix_limit_atom_extraction_W a u :=
        hDW
    _ ≤ V * ((∑ i : Fin d, (u i) ^ 2) * aux_lem_prefix_limit_atom_extraction_eval
          (aux_lem_prefix_limit_atom_extraction_pot M N om)) :=
        mul_le_mul_of_nonneg_left hW hVpos.le
    _ = _ := by
        change _ = (V * _) * aux_lem_prefix_limit_atom_extraction_eval
          (aux_lem_prefix_limit_atom_extraction_pot M N om)
        rw [hV]
        ring


/-- **Moments of the macro constant** `3^{t₁ P₀} (1 + D_u)`, uniformly in the cutoff. -/
theorem aux_lem_prefix_limit_atom_extraction_Kmac0_moment [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M) (t1 qq : ℝ) (ht10 : 0 < t1)
    (hqq : 1 ≤ qq) (hδC : M.delta ≤ Sreg.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg.alphaRange)
    (hκ' : 2 * qq * t1 * Real.log 3 <
      (1 - (1 - ((d : ℝ) - t1) / 4)) ^ 2 / (Sreg.C * M.delta ^ 2 * |Real.log M.delta|))
    (u : Fin d → ℝ) (BR : ℝ) (hBR : 0 ≤ BR)
    (hR : ∀ N, MemLp (aux_lem_prefix_limit_atom_extraction_Rf M N) (ENNReal.ofReal (2 * qq))
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (aux_lem_prefix_limit_atom_extraction_Rf M N) (ENNReal.ofReal (2 * qq))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal BR) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∀ N,
      MemLp (aux_lem_prefix_limit_atom_extraction_Kmac0 M Sreg t1 u N) (ENNReal.ofReal qq)
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (aux_lem_prefix_limit_atom_extraction_Kmac0 M Sreg t1 u N) (ENNReal.ofReal qq)
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CK := by
  set μ := (chaosSampleLaw M).toMeasure with hμ
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (1 - (1 - ((d : ℝ) - t1) / 4)) ^ 2 /
      (Sreg.C * M.delta ^ 2 * |Real.log M.delta|) := ⟨_, rfl⟩
  rw [← hκ] at hκ'
  have hlam : 0 ≤ 2 * qq * t1 * Real.log 3 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
    have : (0 : ℝ) ≤ qq := by linarith
    positivity
  have hκ0 : 0 < κ := lt_of_le_of_lt hlam hκ'
  have hA1 : 1 ≤ Sreg.C * Real.exp (κ * Sreg.C) := by
    have h1 : 1 ≤ Sreg.C := Sreg.C_ge_one
    have h2 : 1 ≤ Real.exp (κ * Sreg.C) := Real.one_le_exp (by have := Sreg.C_pos; positivity)
    nlinarith
  set P0 : ℕ → BilateralField d → ℕ := fun N om =>
    aux_lem_prefix_limit_atom_extraction_P0 Sreg (1 - ((d : ℝ) - t1) / 4) 0 N om with hP0
  have hPm : ∀ N, Measurable (P0 N) := fun N =>
    (Sreg.prefix_measurable _ _ _ _).comp
      (aux_aux_macro_moment_bank_relabel_measurePreserving M N).measurable
  have htail : ∀ N k, μ {om | k < P0 N om} ≤
      ENNReal.ofReal (Sreg.C * Real.exp (κ * Sreg.C) * Real.exp (-κ * k)) := by
    intro N k
    have hpres := aux_aux_macro_moment_bank_relabel_measurePreserving M N
    have hset : {om | k < P0 N om} = aux_aux_macro_moment_bank_relabel N ⁻¹'
        {om | k < Sreg.prefixLen N (1 - ((d : ℝ) - t1) / 4) N ((3 : ℝ) ^ N • (0 : SpatialCoordinates d)) om} :=
      rfl
    rw [hset, hpres.measure_preimage
      (measurableSet_lt measurable_const (Sreg.prefix_measurable _ _ _ _)).nullMeasurableSet]
    exact aux_aux_macro_moment_bank_tail_geometric M Sreg _ κ hδC hα hκ hκ0.le _ _ _ k
  obtain ⟨BX, hBX⟩ : ∃ BX : ℝ, BX = (Sreg.C * Real.exp (κ * Sreg.C) * Real.exp κ *
      (1 - Real.exp (-(κ - 2 * qq * t1 * Real.log 3)))⁻¹) ^ (1 / (2 * qq)) := ⟨_, rfl⟩
  have hX : ∀ N, eLpNorm (fun om => (3 : ℝ) ^ (t1 * (P0 N om : ℝ))) (ENNReal.ofReal (2 * qq)) μ ≤
      ENNReal.ofReal BX := by
    intro N
    have h := aux_aux_macro_moment_bank_eLpNorm_rpow_three_le μ (P0 N) t1 (2 * qq) (by linarith) _
      (aux_aux_macro_moment_bank_lintegral_exp_le μ (P0 N) (hPm N) _ κ _ hA1 hlam hκ' (htail N))
    have hXm : AEStronglyMeasurable (fun om => (3 : ℝ) ^ (t1 * (P0 N om : ℝ))) μ := by
      simpa only [Function.comp_def] using!
        ((measurable_from_nat (f := fun n : ℕ => (3 : ℝ) ^ (t1 * (n : ℝ)))).comp
          (hPm N)).aestronglyMeasurable
    rw [SubdiffusiveProcess.RawLp.eLpNorm_eq_guarded hXm] at h
    refine h.trans (le_of_eq ?_)
    rw [hBX, ENNReal.ofReal_rpow_of_nonneg (by
      have : 0 < 1 - Real.exp (-(κ - 2 * qq * t1 * Real.log 3)) := by
        rw [sub_pos]; exact Real.exp_lt_one_iff.2 (by linarith)
      have := Sreg.C_pos
      positivity) (by positivity)]
  have hXm : ∀ N, MemLp (fun om => (3 : ℝ) ^ (t1 * (P0 N om : ℝ))) (ENNReal.ofReal (2 * qq)) μ :=
    fun N => lt_of_le_of_lt (hX N) ENNReal.ofReal_lt_top
  set cu : ℝ := 2 * volume.real ((aux_lem_prefix_limit_atom_extraction_Q0 d :
      Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) * ∑ i : Fin d, (u i) ^ 2 with hcu
  have hcu0 : 0 ≤ cu := mul_nonneg (mul_nonneg zero_le_two
    aux_lem_prefix_limit_atom_extraction_vol_pos.le) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hY : ∀ N, MemLp (fun om => 1 + aux_lem_prefix_limit_atom_extraction_Dz M u N om)
      (ENNReal.ofReal (2 * qq)) μ ∧
      eLpNorm (fun om => 1 + aux_lem_prefix_limit_atom_extraction_Dz M u N om)
        (ENNReal.ofReal (2 * qq)) μ ≤ ENNReal.ofReal (1 + cu * BR) := by
    intro N
    have hDm : AEStronglyMeasurable (aux_lem_prefix_limit_atom_extraction_Dz M u N) μ :=
      (aux_lem_prefix_limit_atom_extraction_Dz_continuous M u N).measurable.aestronglyMeasurable
    have hDle : ∀ om, ‖aux_lem_prefix_limit_atom_extraction_Dz M u N om‖ ≤
        ‖cu * aux_lem_prefix_limit_atom_extraction_Rf M N om‖ := by
      intro om
      have hD0 : 0 ≤ aux_lem_prefix_limit_atom_extraction_Dz M u N om :=
        aux_lem_prefix_limit_atom_extraction_D_nonneg _ _
      have hRf0 : 0 ≤ aux_lem_prefix_limit_atom_extraction_Rf M N om :=
        aux_lem_prefix_limit_atom_extraction_eval_nonneg _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hD0,
        abs_of_nonneg (mul_nonneg hcu0 hRf0)]
      exact aux_lem_prefix_limit_atom_extraction_Dz_le M u N om
    have hDmem : MemLp (aux_lem_prefix_limit_atom_extraction_Dz M u N) (ENNReal.ofReal (2 * qq)) μ :=
      ((hR N).1.const_mul cu).of_le hDm (Filter.Eventually.of_forall hDle)
    have hDn : eLpNorm (aux_lem_prefix_limit_atom_extraction_Dz M u N) (ENNReal.ofReal (2 * qq)) μ ≤
        ENNReal.ofReal (cu * BR) := by
      calc eLpNorm (aux_lem_prefix_limit_atom_extraction_Dz M u N) (ENNReal.ofReal (2 * qq)) μ
          ≤ eLpNorm (fun om => cu * aux_lem_prefix_limit_atom_extraction_Rf M N om)
              (ENNReal.ofReal (2 * qq)) μ := eLpNorm_mono hDm hDle
        _ = ENNReal.ofReal cu * eLpNorm (aux_lem_prefix_limit_atom_extraction_Rf M N)
              (ENNReal.ofReal (2 * qq)) μ := by
            rw [show (fun om => cu * aux_lem_prefix_limit_atom_extraction_Rf M N om) =
              cu • aux_lem_prefix_limit_atom_extraction_Rf M N from rfl, eLpNorm_const_smul,
              Real.enorm_eq_ofReal hcu0]
        _ ≤ ENNReal.ofReal cu * ENNReal.ofReal BR := by gcongr; exact (hR N).2
        _ = ENNReal.ofReal (cu * BR) := (ENNReal.ofReal_mul hcu0).symm
    have h1m : MemLp (fun _ : BilateralField d => (1 : ℝ)) (ENNReal.ofReal (2 * qq)) μ :=
      memLp_const 1
    refine ⟨h1m.add hDmem, ?_⟩
    have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * qq) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
    calc eLpNorm (fun om => 1 + aux_lem_prefix_limit_atom_extraction_Dz M u N om)
          (ENNReal.ofReal (2 * qq)) μ
        ≤ eLpNorm (fun _ : BilateralField d => (1 : ℝ)) (ENNReal.ofReal (2 * qq)) μ +
            eLpNorm (aux_lem_prefix_limit_atom_extraction_Dz M u N) (ENNReal.ofReal (2 * qq)) μ :=
          eLpNorm_add_le hq1
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (cu * BR) := by
          gcongr
          have h := eLpNorm_le_of_ae_bound (μ := μ) (p := ENNReal.ofReal (2 * qq))
            (f := fun _ : BilateralField d => (1 : ℝ)) (C := 1) aestronglyMeasurable_const
            (Filter.Eventually.of_forall fun _ => by simp)
          simpa [measure_univ] using h
      _ = ENNReal.ofReal (1 + cu * BR) := (ENNReal.ofReal_add zero_le_one (mul_nonneg hcu0 hBR)).symm
  have hBX0 : 0 ≤ BX := by
    have hpos : 0 < 1 - Real.exp (-(κ - 2 * qq * t1 * Real.log 3)) := by
      rw [sub_pos]; exact Real.exp_lt_one_iff.2 (by linarith)
    rw [hBX]
    apply Real.rpow_nonneg
    have := Sreg.C_pos
    exact mul_nonneg (by positivity) (inv_nonneg.2 hpos.le)
  refine ⟨BX * (1 + cu * BR), mul_nonneg hBX0 (by positivity), fun N => ?_⟩
  have hq0 : 0 < qq := by linarith
  have hprod := aux_rem_resolved_microscopic_product_lq_bound μ qq (2 * qq) hq0 le_rfl _ _
    (hXm N) (hY N).1
  have hfun : aux_lem_prefix_limit_atom_extraction_Kmac0 M Sreg t1 u N =
      fun om => (3 : ℝ) ^ (t1 * (P0 N om : ℝ)) *
        (1 + aux_lem_prefix_limit_atom_extraction_Dz M u N om) := rfl
  rw [hfun]
  refine ⟨lt_of_le_of_lt hprod
    (ENNReal.mul_lt_top (hXm N).eLpNorm_lt_top (hY N).1.eLpNorm_lt_top), hprod.trans ?_⟩
  calc eLpNorm (fun om => (3 : ℝ) ^ (t1 * (P0 N om : ℝ))) (ENNReal.ofReal (2 * qq)) μ *
        eLpNorm (fun om => 1 + aux_lem_prefix_limit_atom_extraction_Dz M u N om)
          (ENNReal.ofReal (2 * qq)) μ
      ≤ ENNReal.ofReal BX * ENNReal.ofReal (1 + cu * BR) := by gcongr; exacts [hX N, (hY N).2]
    _ = ENNReal.ofReal (BX * (1 + cu * BR)) := by
        rw [← ENNReal.ofReal_mul hBX0]

/-- The growth conclusion for one model, from the per-model inputs (all thresholds already
applied). -/
theorem aux_lem_prefix_limit_atom_extraction_growth_D_model [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Cp : ℝ) (hFE : aux_aux_macro_energy_recurrence_FE (d := d) Cp)
    (t t1 C q : ℝ) (ht0 : 0 ≤ t) (htt1 : t < t1) (ht1 : (d : ℝ) - 1 < t1) (ht1d : t1 < (d : ℝ))
    (hC : 0 < C) (hq : 1 ≤ q) (hmic : aux_prop_growth_energy_assembly_MicroLocal d t t1 C)
    (hmom : aux_prop_growth_energy_assembly_MomentClause d t t1)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Sreg : in_6_16 d M)
    (hδC : M.delta ≤ Sreg.C⁻¹) (hα : 1 - ((d : ℝ) - t1) / 4 ∈ Sreg.alphaRange)
    (u : Fin d → ℝ) (CK : ℝ) (hCK : 0 ≤ CK)
    (hKm : ∀ N, MemLp (aux_lem_prefix_limit_atom_extraction_Kmac0 M Sreg t1 u N)
        (ENNReal.ofReal (2 * q * max 1 t)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (aux_lem_prefix_limit_atom_extraction_Kmac0 M Sreg t1 u N)
        (ENNReal.ofReal (2 * q * max 1 t)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal CK)
    (D Mx : ℕ → BilateralField d → ℝ) (Cpe CE aRate : ℝ) (hCpe : 0 < Cpe) (hCE : 0 ≤ CE)
    (haR0 : 0 ≤ aRate)
    (haR : aRate < min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3)
    (hDMx0 : ∀ N om, 0 ≤ D N om ∧ 0 ≤ Mx N om)
    (hae : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
      0 < Mx N om ∧
      (∀ x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)),
        (Mx N om)⁻¹ ≤ cutoffCoefficient M (fun _ => 0) om N x ∧
          cutoffCoefficient M (fun _ => 0) om N x ≤ Mx N om) ∧
      (∀ x y, x ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) →
        y ∈ (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d)) →
        |Real.log (cutoffCoefficient M (fun _ => 0) om N x) -
            Real.log (cutoffCoefficient M (fun _ => 0) om N y)| ≤
          D N om * (3 : ℝ) ^ N * dist x y))
    (hmem : ∀ N, MemLp (D N) (ENNReal.ofReal (2 * q * max 1 t)) (chaosSampleLaw M).toMeasure ∧
      MemLp (Mx N) (ENNReal.ofReal (2 * q * max 1 t)) (chaosSampleLaw M).toMeasure)
    (hDmom : ∀ N, eLpNorm (D N) (ENNReal.ofReal (2 * q * max 1 t)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Cpe * Real.sqrt (1 + (N : ℝ))))
    (hMxmom : ∀ N, eLpNorm (Mx N) (ENNReal.ofReal (2 * q * max 1 t)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (CE * Real.exp (aRate * N))) :
    ∃ (K : ℕ → BilateralField d → ℝ) (B : ℝ), 0 ≤ B ∧
      ((∀ N, AEStronglyMeasurable (K N) (chaosSampleLaw M).toMeasure) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 0 ≤ K N om)) ∧
      (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
        ∀ x ∈ ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
          Set (SpatialCoordinates d)),
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          localGradientEnergy
            (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N om))
            (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
            (sobolevGradient (dirichletMinimizer
              (killedResponseSpace aux_lem_prefix_limit_atom_extraction_poincare.1)
              (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N om))
              (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0)).val) ≤
            K N om * rho ^ t) ∧
      (∀ N, MemLp (K N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
        eLpNorm (K N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B) := by
  let P := (chaosSampleLaw M).toMeasure
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = aux_aux_macro_energy_recurrence_Z Sreg.C Cp t1 d := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by rw [hZ]; exact aux_aux_macro_energy_recurrence_Z_nonneg _ _ _ _
  have hmax1 : (1 : ℝ) ≤ max 1 t := le_max_left _ _
  have hqq1 : 1 ≤ 2 * q * max 1 t := by nlinarith
  have hqqq : q ≤ 2 * q * max 1 t := by nlinarith
  have hle : ENNReal.ofReal q ≤ ENNReal.ofReal (2 * q * max 1 t) := ENNReal.ofReal_le_ofReal hqqq
  -- the macro constant with the recurrence factor
  obtain ⟨Km, hKmdef⟩ : ∃ Km : ℕ → BilateralField d → ℝ,
      Km = fun N om => Z * aux_lem_prefix_limit_atom_extraction_Kmac0 M Sreg t1 u N om := ⟨_, rfl⟩
  have hKm0 : ∀ N om, 0 ≤ Km N om := by
    intro N om
    rw [hKmdef]
    refine mul_nonneg hZ0 (mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_)
    have := aux_lem_prefix_limit_atom_extraction_D_nonneg
      (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N om)) u
    change 0 ≤ 1 + aux_lem_prefix_limit_atom_extraction_D _ u
    linarith
  have hKmmem : ∀ N, MemLp (Km N) (ENNReal.ofReal (2 * q * max 1 t)) P ∧
      eLpNorm (Km N) (ENNReal.ofReal (2 * q * max 1 t)) P ≤ ENNReal.ofReal (Z * CK) := by
    intro N
    have h := hKm N
    have hfun : Km N = Z • aux_lem_prefix_limit_atom_extraction_Kmac0 M Sreg t1 u N := by
      rw [hKmdef]; rfl
    rw [hfun]
    refine ⟨h.1.const_smul Z, ?_⟩
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hZ0, ENNReal.ofReal_mul hZ0]
    gcongr
    exact h.2
  have hMxN : ∀ N : ℕ, eLpNorm (fun o => Mx N o + Mx N o)
      (ENNReal.ofReal (2 * q * max 1 t)) P ≤ ENNReal.ofReal (2 * CE * Real.exp (aRate * (N : ℝ))) := by
    intro N
    have h1 := aux_prop_growth_energy_assembly_double P (Mx N) (2 * q * max 1 t)
      (2 * q * max 1 t) (CE * Real.exp (aRate * N)) hqq1 le_rfl (hmem N).2.aestronglyMeasurable (by positivity)
      (hMxmom N)
    refine h1.trans (le_of_eq ?_)
    ring_nf
  have hB0 := hmom (BilateralField d) P q hq D Mx Mx Km Cpe (2 * CE) (Z * CK) aRate hCpe.le
    (by positivity) (mul_nonneg hZ0 hCK) haR0 haR
    (fun N o => ⟨(hDMx0 N o).1, (hDMx0 N o).2, (hDMx0 N o).2, hKm0 N o⟩)
    (fun N => ⟨(hmem N).1, (hmem N).2, (hmem N).2, (hKmmem N).1⟩) hDmom hMxN
    (fun N => (hKmmem N).2)
  obtain ⟨B, hB0', hBN⟩ := hB0
  have h2r : (0 : ℝ) ≤ (2 / 1) ^ t := Real.rpow_nonneg (by norm_num) _
  have hCr0 := aux_prop_growth_energy_assembly_Cr_nonneg d 1 t t1 C one_pos hC.le
  obtain ⟨Kf, Cb, hKfmem, hKfnorm, hK1, hKdom⟩ :=
    aux_prop_growth_energy_assembly_final P 1 (fun _ => q) (fun _ => hq) t t1 (d : ℝ)
      ((2 / 1) ^ t) (aux_prop_growth_energy_assembly_Cr d 1 t t1 C) (Z * CK) h2r hCr0
      (mul_nonneg hZ0 hCK) Km D Mx (fun N => (hKmmem N).1.aestronglyMeasurable) (fun N => (hmem N).1.aestronglyMeasurable)
      (fun N => (hmem N).2.aestronglyMeasurable)
      (fun _ N => (eLpNorm_le_eLpNorm_of_exponent_le hle).trans (hKmmem N).2)
      (fun _ => ⟨B, hB0', hBN⟩)
  obtain ⟨Cφ, hCφdef⟩ : ∃ Cφ : ℝ, Cφ = max 1 (c2Norm
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun z => affineSlope u z + 0)) := ⟨_, rfl⟩
  have hCφ1 : 1 ≤ Cφ := by rw [hCφdef]; exact le_max_left _ _
  have hCφ : c2Norm (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun z => affineSlope u z + 0) ≤ Cφ := by rw [hCφdef]; exact le_max_right _ _
  have hE0 : 0 ≤ (0 + Cφ) ^ 2 := sq_nonneg _
  refine ⟨fun N om => Kf N om * (0 + Cφ) ^ 2, Cb 0 * (0 + Cφ) ^ 2, ?_, ⟨fun N => ?_, ?_⟩, ?_,
    fun N => ⟨?_, ?_⟩⟩
  · have := hKfnorm 0 0
    have hCb : 0 ≤ Cb 0 := by
      by_contra hneg
      push_neg at hneg
      have h1 : ENNReal.ofReal (Cb 0) = 0 := ENNReal.ofReal_of_nonpos hneg.le
      rw [h1, nonpos_iff_eq_zero, eLpNorm_eq_zero_iff (by simp; linarith)] at this
      have hae1 : ∀ᵐ o ∂P, Kf 0 o = 0 := this
      obtain ⟨o, ho⟩ := hae1.exists
      have := hK1 0 o
      linarith
    exact mul_nonneg hCb hE0
  · exact ((hKfmem 0 N).aestronglyMeasurable).mul_const _
  · exact Filter.Eventually.of_forall fun om N =>
      mul_nonneg (le_trans zero_le_one (hK1 N om)) hE0
  · filter_upwards [hae] with om hom
    intro N x hx rho hrho0 hrho1
    obtain ⟨hMxpos, henvN, hlipN⟩ := hom N
    have hs := aux_lem_prefix_limit_atom_extraction_dir_sample hd Cp hFE t t1 C ht0 htt1 ht1 ht1d
      hC hmic M Sreg hδC hα u Cφ hCφ hCφ1 om N (D N om) (Mx N om) (hDMx0 N om).1 hMxpos henvN
      hlipN x hx rho hrho0 hrho1
    refine hs.trans ?_
    have hdom := hKdom N om
    rw [hKmdef] at hdom
    simp only at hdom
    rw [← hZ] at hs ⊢
    have hradt : 0 ≤ rho ^ t := Real.rpow_nonneg hrho0.le _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdom hE0) hradt
  · exact (hKfmem 0 N).mul_const _
  · have hfun : (fun N om => Kf N om * (0 + Cφ) ^ 2) N = ((0 + Cφ) ^ 2) • Kf N := by
      funext om; simp [mul_comm]
    rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal hE0, mul_comm (Cb 0),
      ENNReal.ofReal_mul hE0]
    gcongr
    exact hKfnorm 0 N

/-- **Growth input** (paper `eq:mfd-4`, Proposition `mfd:prop-growth` with `L' = 0`) for the
affine Dirichlet minimizers of `A_N^0` on the unit cube, with the carried small-perturbation input
`W` (below-wavelength step). The regularity input is the natively constructed `in_6_16`. -/
theorem aux_lem_prefix_limit_atom_extraction_growth_D (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (W : SmallPerturbationInput d)
    (u : Fin d → ℝ) (t q : ℝ) (ht1 : (d : ℝ) - 1 < t) (ht2 : t < (d : ℝ)) (hq : 1 ≤ q) :
    ∃ delta : ℝ, 0 < delta ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta →
      ∃ (K : ℕ → BilateralField d → ℝ) (B : ℝ), 0 ≤ B ∧
        ((∀ N, AEStronglyMeasurable (K N) (chaosSampleLaw M).toMeasure) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 0 ≤ K N om)) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
          ∀ x ∈ ((aux_lem_prefix_limit_atom_extraction_Q0 d : Opens (SpatialCoordinates d)) :
            Set (SpatialCoordinates d)),
          ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
            localGradientEnergy
              (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N om))
              (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
              (sobolevGradient (dirichletMinimizer
                (killedResponseSpace aux_lem_prefix_limit_atom_extraction_poincare.1)
                (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N om))
                (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0)).val) ≤
              K N om * rho ^ t) ∧
        (∀ N, MemLp (K N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (K N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B) := by
  by_cases hd : 2 ≤ d
  swap
  · exact ⟨1, one_pos, fun M _ => absurd M.shellPrefix.dimension hd⟩
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht0 : 0 ≤ t := by linarith
  have hG1 := aux_prop_growth_energy_assembly_p1_choice d hd t ht2
  obtain ⟨p1, hp1, hp1t⟩ := hG1
  obtain ⟨t1, ht1def⟩ : ∃ s : ℝ, s = (t + d) / 2 := ⟨_, rfl⟩
  have htt1 : t < t1 := by rw [ht1def]; linarith
  have ht1d : t1 < d := by rw [ht1def]; linarith
  have ht1' : (d : ℝ) - 1 < t1 := by linarith
  have ht10 : 0 < t1 := by linarith
  have hmax1 : (1 : ℝ) ≤ max 1 t := le_max_left _ _
  have hqq1 : 1 ≤ 2 * q * max 1 t := by nlinarith
  have hqq2 : 1 ≤ 2 * (2 * q * max 1 t) := by linarith
  have hqq0 : 0 < 2 * (2 * q * max 1 t) := by linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨rmax, hrmaxdef⟩ : ∃ rmax : ℝ,
      rmax = min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 := ⟨_, rfl⟩
  have hrmax : 0 < rmax := by
    rw [hrmaxdef]
    exact mul_pos (lt_min (by linarith) (lt_min (by linarith) (by linarith))) hlog3
  have hG2 := aux_prop_growth_energy_assembly_micro_local d hd W p1 t t1 hp1 ht1 htt1 ht1d hp1t
  obtain ⟨C, hC, hmic, hmom⟩ := hG2
  have hG3 := aux_lem_prefix_limit_atom_extraction_extremes0 d hd 0 (2 * q * max 1 t) hqq1
  obtain ⟨Cpe, Cd, cd, hCpe, hCd, hcd, hext⟩ := hG3
  have hG4 := aux_aux_macro_moment_bank_threshold (d := d) t1 (2 * q * max 1 t) ht1' ht1d ht10.le hqq1
  obtain ⟨dA, hdA, hthr⟩ := hG4
  have hG5 := aux_lem_prefix_limit_atom_extraction_moments_q d (2 * (2 * q * max 1 t)) hqq2
  obtain ⟨δR, hδR, hRm⟩ := hG5
  have hG6 := aux_aux_macro_energy_recurrence_finite_estimate (d := d) hd
  obtain ⟨Cp, -, hFE⟩ := hG6
  have hcdq : 0 < cd / (2 * (2 * q * max 1 t)) := div_pos hcd hqq0
  have hG7 := aux_prop_growth_energy_assembly_threshold Cd Cpe rmax (min dA δR) (cd / (2 * (2 * q * max 1 t))) hCd hCpe hrmax (lt_min hdA hδR) hcdq
  obtain ⟨delta0, aRate, hδ0, hδM, hδc, haR0, haR, hmono⟩ := hG7
  rw [hrmaxdef] at haR
  refine ⟨delta0, hδ0, ?_⟩
  intro M hδ
  have hδA : M.delta ≤ dA := hδ.trans (hδM.trans (min_le_left _ _))
  have hδRM : M.delta ≤ δR := hδ.trans (hδM.trans (min_le_right _ _))
  have hG8 := hthr M (aux_prop_growth_macro_energy_nativeSreg M) hδA
  obtain ⟨hδC, hα, hκ'⟩ := hG8
  have hG9 := hRm M hδRM
  obtain ⟨BR, hBR, hR⟩ := hG9
  have hG10 := aux_lem_prefix_limit_atom_extraction_Kmac0_moment M (aux_prop_growth_macro_energy_nativeSreg M) t1 (2 * q * max 1 t) ht10 hqq1 hδC hα hκ' u BR hBR hR
  obtain ⟨CK, hCK, hKm⟩ := hG10
  have hG11 := hext M (hδ.trans hδc)
  obtain ⟨D, Mx, CE, hCE, hDMx0, hae, hmem, hDmom, hMxmom⟩ := hG11
  have hrate : Cd * M.delta + Cpe * M.delta ^ 2 ≤ aRate :=
    hmono _ M.shellPrefix.delta_pos.le hδ
  have hMxmom' : ∀ N, eLpNorm (Mx N) (ENNReal.ofReal (2 * q * max 1 t))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (CE * Real.exp (aRate * N)) := by
    intro N
    refine (hMxmom N).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg N))) hCE
  exact aux_lem_prefix_limit_atom_extraction_growth_D_model hd Cp hFE t t1 C q ht0 htt1 ht1' ht1d hC
    hq hmic hmom M (aux_prop_growth_macro_energy_nativeSreg M) hδC hα u CK hCK hKm D Mx Cpe CE aRate
    hCpe hCE haR0 haR hDMx0 hae hmem hDmom hMxmom'

end PaeG0Dir

section PaeN0Step

open MeasureTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

variable {d : ℕ}

/-- `ρ_0 = 1` for the zero infrared field and the transfer constant `ahom_N^{-1}`. -/
theorem aux_lem_prefix_limit_atom_extraction_rho0
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (omega : BilateralField d) (N : ℕ)
    (y : SpatialCoordinates d) :
    aux_rem_resolved_meshes_rho M (fun _ => 0) omega N (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ 0 y
      = 1 := by
  unfold aux_rem_resolved_meshes_rho
  have hA : SubdiffusiveProcess.CoarseGrainingVocab.ahom M N ≠ 0 := (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne'
  simp [hA]

/-- The exact finite identity on the unit Neumann cube at `L' = 0`. -/
theorem aux_lem_prefix_limit_atom_extraction_neumann_identity0
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} (Sreg : in_6_16 d M) (omega : BilateralField d)
    (N : ℕ) :
    ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ))
          one_pos).val y =
        (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
          (Sreg.cutoffOn (N + 0) (aux_rem_resolved_meshes_relabel N omega)
            ((3 : ℝ) ^ (N : ℤ) • (fun _ : Fin d => (1 / 2 : ℝ)))
            ((3 : ℝ) ^ (N : ℤ)) (by positivity)).val (((3 : ℝ) ^ (N : ℤ)) • y) := by
  filter_upwards [aux_rem_resolved_meshes_cutoff_coeFn M (fun _ => 0) omega N,
    aux_rem_resolved_meshes_cutoffOn_scaled Sreg omega N 0] with y h1 h2
  rw [h1, h2]
  have h := aux_rem_resolved_meshes_rho_mul M (fun _ => 0) omega N
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ 0 y
  rw [aux_lem_prefix_limit_atom_extraction_rho0, one_mul] at h
  rw [h]

/-- **The good branch at `L' = 0`** (the analogue of `aux_rem_resolved_meshes_good_limit`, with
no infrared limit). -/
theorem aux_lem_prefix_limit_atom_extraction_good0 (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 Kt C1 delta1 : ℝ) (hC1 : 0 ≤ C1)
    (hfin : aux_rem_resolved_meshes_finite_onestep d hd Lstar Rstar t0 Kt C1 delta1)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (E : in_J d)
    (Poinc : in_poincare d hd E) (Ext : in_extension d hd E)
    (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
    (hdet : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hδ : M.delta ≤ delta1) (omega : BilateralField d) (N : ℕ)
    (f : SpatialCoordinates d → ℝ)
    (hf : AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hfb : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf)
    (hf0 : (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0)
    (u : meanZeroSobolevGraph (unitNeumannCube d))
    (hu : SolvesNeumann (cutoffPositiveCoefficient M (fun _ => 0) omega N
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) f u)
    (y : SpatialCoordinates d) (hy : y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (I : Finset (Fin d)) (n k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (hR : (3 : ℝ) ^ (-((k : ℤ))) / 2 ≤ Rstar)
    (h8 : 8 * ((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) < (3 : ℝ) ^ (-((k : ℤ))) / 2)
    (hI : ∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ min (y i) (1 - y i))
    (hgood : n + It.prefixLen ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
          (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1)
          (aux_rem_resolved_meshes_relabel N omega) ≤ N - k + 1) :
    aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
        (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2)) ≤
      7 * (C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0) *
        (aux_rem_resolved_meshes_energy
            (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
            (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
          (aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1)
            (aux_rem_resolved_meshes_center y I))⁻¹ *
            (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))) := by
  have hm2 : 2 ≤ N - k + 1 := by
    have := It.prefix_lower ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
      (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1) (aux_rem_resolved_meshes_relabel N omega)
    rw [It.k_eq] at this
    omega
  have hcF : 0 < (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ :=
    inv_pos.2 (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)
  have hF := hfin M E Poinc Ext Sreg It hdet hδ omega N 0 (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹
    hcF _ (aux_lem_prefix_limit_atom_extraction_neumann_identity0 Sreg omega N) f hf Kf hKf hfb
    hf0 u hu y hy I n k hk1 hkN hR h8 hI hgood
  have href := aux_rem_resolved_meshes_ref_avg It (fun _ => 0) omega N k 0 hk1 hkN hm2
    (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ (aux_rem_resolved_meshes_center y I)
  simp only [aux_lem_prefix_limit_atom_extraction_rho0, one_mul] at href
  have hbref : (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
      It.ref (N + 0) (N - k + 1 - 2) ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
        (aux_rem_resolved_meshes_relabel N omega) =
      aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1)
        (aux_rem_resolved_meshes_center y I) := by
    rw [href]
    rfl
  rw [hbref] at hF
  have hσ : 0 ≤ (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 := by
    positivity
  have hbv : 0 < aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1)
      (aux_rem_resolved_meshes_center y I) :=
    aux_lane4_two_mesh_energy_bound_bpos M (fun _ => 0) omega N (k - 1)
      (aux_rem_resolved_meshes_center y I)
  have hE3 : 0 ≤ aux_rem_resolved_meshes_energy
      (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
      (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) :=
    aux_rem_resolved_strata_energy_nonneg _ ⟨u.1, u.2.1⟩ _
  have hZ : 0 ≤ (aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1)
      (aux_rem_resolved_meshes_center y I))⁻¹ *
      (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by positivity
  refine hF.trans ?_
  have hK : 0 ≤ C1 * (((3 : ℝ) ^ ((n : ℤ) - (N : ℤ)) / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 :=
    mul_nonneg hC1 hσ
  have heq : (aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1)
      (aux_rem_resolved_meshes_center y I))⁻¹ * Kf ^ 2 *
      ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2) =
      (aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1)
        (aux_rem_resolved_meshes_center y I))⁻¹ *
        (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by ring
  rw [heq]
  nlinarith [mul_nonneg hK (add_nonneg hE3 hZ)]

theorem aux_lem_prefix_limit_atom_extraction_onestep0 (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 : ℝ) (hLstar : 10 ≤ Lstar) (hRstar_lt : Rstar < 1 / (100 * Lstar))
    (ht0 : 0 < t0) (Kt C1 delta1 : ℝ) (hC1 : 0 ≤ C1)
    (hfin : aux_rem_resolved_meshes_finite_onestep d hd Lstar Rstar t0 Kt C1 delta1)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (E : in_J d)
    (Poinc : in_poincare d hd E) (Ext : in_extension d hd E)
    (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
    (hdet : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hδ : M.delta ≤ delta1) (omega : BilateralField d) (N : ℕ)
    (f : SpatialCoordinates d → ℝ)
    (hf : AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))))
    (Kf : ℝ) (hKf : 0 ≤ Kf)
    (hfb : ∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf)
    (hf0 : (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0)
    (u : meanZeroSobolevGraph (unitNeumannCube d))
    (hu : SolvesNeumann (cutoffPositiveCoefficient M (fun _ => 0) omega N
      (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) f u) :
    ∀ (y : SpatialCoordinates d), y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
    ∀ (I : Finset (Fin d)) (s : ℝ) (k : ℕ),
      s ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) → (3 : ℝ) ^ (-(N : ℤ)) / 2 ≤ s → 0 < s →
      k ≤ N → 8 * s < (3 : ℝ) ^ (-((k : ℤ))) / 2 → (3 : ℝ) ^ (-((k : ℤ))) / 2 ≤ Rstar →
      (∀ i, i ∉ I → 4 * Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ min (y i) (1 - y i)) →
      aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) s) ≤
        max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (It.prefixLen
            ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
            (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1)
            (aux_rem_resolved_meshes_relabel N omega) : ℝ)) *
          (s / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I)
                (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1)
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by
  intro y hy I s k hs hs1 hs0 hk h8 hR hI
  obtain ⟨j, rfl⟩ := hs
  dsimp only at hs1 hs0 h8 ⊢
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hc0 : 0 ≤ t0 * Real.log 3 + 1 := by positivity
  -- the target depth
  have hjN : -(N : ℤ) ≤ j := by
    have h1 : (3 : ℝ) ^ (-(N : ℤ)) ≤ (3 : ℝ) ^ j := by linarith
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp h1
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    subst hk0
    have : (1 : ℝ) / 2 ≤ Rstar := by simpa using hR
    have h100 : 0 < 100 * Lstar := by linarith
    have : 1 / (100 * Lstar) ≤ 1 / 1000 := by
      rw [div_le_div_iff₀ h100 (by norm_num)]; linarith
    linarith
  set n : ℕ := (j + (N : ℤ)).toNat with hn_def
  have hn : ((n : ℕ) : ℤ) = j + (N : ℤ) := Int.toNat_of_nonneg (by omega)
  have hjn : j = (n : ℤ) - (N : ℤ) := by omega
  set pl := It.prefixLen ((3 : ℝ) ^ (N : ℤ) • aux_rem_resolved_meshes_center y I)
    (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (N - k + 1) (aux_rem_resolved_meshes_relabel N omega)
    with hpl
  have hmono : ∀ {A A' : Set (SpatialCoordinates d)}, A ⊆ A' →
      aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u A ≤
      aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u A' :=
    fun h => aux_rem_resolved_strata_energy_mono
      (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
      ⟨u.1, u.2.1⟩ h
  have hnn : ∀ A : Set (SpatialCoordinates d), 0 ≤ aux_rem_resolved_meshes_energy
      (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u A :=
    fun A => aux_rem_resolved_strata_energy_nonneg
      (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) ⟨u.1, u.2.1⟩ A
  have hRk : 0 < (3 : ℝ) ^ (-((k : ℤ))) / 2 := by positivity
  have hbv : 0 < aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1)
      (aux_rem_resolved_meshes_center y I) :=
    aux_lane4_two_mesh_energy_bound_bpos M (fun _ => 0) omega N (k - 1) (aux_rem_resolved_meshes_center y I)
  have hsrc : 0 ≤ (aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1)
      (aux_rem_resolved_meshes_center y I))⁻¹ * Kf ^ 2 *
      ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2) := by positivity
  have hLR : aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
        (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ j / 2)) ≤
      aux_rem_resolved_meshes_energy
        (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
        (Metric.ball (aux_rem_resolved_meshes_center y I) (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) :=
    hmono (Metric.ball_subset_ball (by nlinarith))
  have hσ : 0 ≤ (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 := by positivity
  have hexp1 : 1 ≤ Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) :=
    Real.one_le_exp (mul_nonneg hc0 (Nat.cast_nonneg _))
  by_cases hgood : n + pl ≤ N - k + 1
  · -- good branch
    have hG := aux_lem_prefix_limit_atom_extraction_good0 d hd Lstar Rstar t0 Kt C1 delta1 hC1 hfin
      M E Poinc Ext Sreg It hdet hδ omega N f hf Kf hKf hfb hf0 u hu y hy I n k hk1 hk hR
      (by rw [← hjn]; exact h8) hI hgood
    rw [← hjn] at hG
    have h3L := hmono (Metric.ball_subset_ball (x := aux_rem_resolved_meshes_center y I)
      (show 3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ≤ Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2) by nlinarith))
    refine hG.trans ?_
    have hC : 7 * C1 ≤ max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) := by
      have := le_max_right 1 (7 * C1)
      have h1 : 0 ≤ max 1 (7 * C1) := le_trans zero_le_one (le_max_left _ _)
      nlinarith
    have hB : 0 ≤ aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
        (aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
          (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by
      have := hnn (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2)))
      positivity
    calc 7 * (C1 * (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0) *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)))
        = (7 * C1) * (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))) := by ring
      _ ≤ (max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ))) *
            (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I) (3 * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1) (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2))) := by
          gcongr
      _ ≤ max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) *
            (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 *
          (aux_rem_resolved_meshes_energy
              (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
              (Metric.ball (aux_rem_resolved_meshes_center y I)
                (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
            (aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (1 - 1 + (k - 1))
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by
          rw [show 1 - 1 + (k - 1) = k - 1 by omega]
          have hK0 : 0 ≤ max 1 (7 * C1) * Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) *
              (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0 := by positivity
          apply mul_le_mul_of_nonneg_left _ hK0
          have e : (aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1)
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              (Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) =
            (aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1)
              (aux_rem_resolved_meshes_center y I))⁻¹ *
              Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2) := by ring
          rw [e]
          linarith
      _ = _ := by rw [show 1 - 1 + (k - 1) = k - 1 by omega]
  · -- bad branch
    have hjk : 0 ≤ j + (k : ℤ) + (pl : ℤ) := by
      push_neg at hgood
      have : (N : ℤ) - k + 1 < (n : ℤ) + pl := by
        have : N - k + 1 < n + pl := hgood
        omega
      omega
    have hfac := aux_rem_resolved_meshes_bad_factor t0 (t0 * Real.log 3 + 1) ht0 (by linarith) j k
      pl hjk
    have hE0 := hnn (Metric.ball (aux_rem_resolved_meshes_center y I)
      (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2)))
    calc aux_rem_resolved_meshes_energy
          (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
          (Metric.ball (aux_rem_resolved_meshes_center y I) ((3 : ℝ) ^ j / 2))
        ≤ 1 * (aux_rem_resolved_meshes_energy
            (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
            (Metric.ball (aux_rem_resolved_meshes_center y I)
              (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
          (aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1)
            (aux_rem_resolved_meshes_center y I))⁻¹ *
            Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by linarith
      _ ≤ (max 1 (7 * C1) * (Real.exp ((t0 * Real.log 3 + 1) * (pl : ℝ)) *
            (((3 : ℝ) ^ j / 2) / ((3 : ℝ) ^ (-((k : ℤ))) / 2)) ^ t0)) *
          (aux_rem_resolved_meshes_energy
            (cutoffPositiveCoefficient M (fun _ => 0) omega N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
            (Metric.ball (aux_rem_resolved_meshes_center y I)
              (Lstar * ((3 : ℝ) ^ (-((k : ℤ))) / 2))) +
          (aux_rem_resolved_meshes_bref M (fun _ => 0) omega N (k - 1)
            (aux_rem_resolved_meshes_center y I))⁻¹ *
            Kf ^ 2 * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ ((d : ℝ) + 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          have := le_max_left 1 (7 * C1)
          nlinarith
      _ = _ := by ring

end PaeN0Step

section PaeN0Mesh

open MeasureTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

variable {d : ℕ}

/-- The zero-infrared reference is within `e^{±S}` of the original one. -/
theorem aux_lem_prefix_limit_atom_extraction_bref_cmp
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N k : ℕ)
    (z : SpatialCoordinates d) (S : ℝ)
    (hS : ∀ x ∈ Metric.ball z ((3 : ℝ) ^ (-((k : ℤ))) / 2), |H om x| ≤ S) :
    aux_rem_resolved_meshes_bref M (fun _ => 0) om N k z ≤
        Real.exp S * aux_rem_resolved_meshes_bref M H om N k z ∧
      (aux_rem_resolved_meshes_bref M (fun _ => 0) om N k z)⁻¹ ≤
        Real.exp S * (aux_rem_resolved_meshes_bref M H om N k z)⁻¹ := by
  set B : Set (SpatialCoordinates d) := Metric.ball z ((3 : ℝ) ^ (-((k : ℤ))) / 2) with hB
  set g0 : SpatialCoordinates d → ℝ := fun x =>
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
      Real.exp (((fun _ : BilateralField d => (0 : C(SpatialCoordinates d, ℝ))) om x +
        ∑ j ∈ Finset.range k, (om (-(j : ℤ))) x) - (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)
    with hg0
  set gH : SpatialCoordinates d → ℝ := fun x =>
    SubdiffusiveProcess.CoarseGrainingVocab.ahom M (N - k) / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N *
      Real.exp ((H om x + ∑ j ∈ Finset.range k, (om (-(j : ℤ))) x) -
        (k : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) with hgH
  have hc0 := aux_rem_resolved_meshes_spoint_continuous M (fun _ => 0) om N k
  have hcH := aux_rem_resolved_meshes_spoint_continuous M H om N k
  have hKc : IsCompact (Metric.closedBall z ((3 : ℝ) ^ (-((k : ℤ))) / 2)) := isCompact_closedBall _ _
  have hint : ∀ g : SpatialCoordinates d → ℝ, Continuous g → IntegrableOn g B volume := fun g hg =>
    (hg.continuousOn.integrableOn_compact hKc).mono_set Metric.ball_subset_closedBall
  have hS0 : 0 ≤ S := by
    have hz : z ∈ B := Metric.mem_ball_self (by positivity)
    exact (abs_nonneg _).trans (hS z hz)
  have hpt0 : ∀ x ∈ B, g0 x = gH x * Real.exp (-(H om x)) := by
    intro x _
    simp only [hg0, hgH, ContinuousMap.zero_apply, zero_add]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hgpos : ∀ x, 0 ≤ gH x := fun x =>
    mul_nonneg (div_nonneg (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _).le
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M _).le) (Real.exp_pos _).le
  have hup : ∀ x ∈ B, g0 x ≤ Real.exp S * gH x := by
    intro x hx
    have h1 := neg_abs_le (H om x)
    have h2 := hS x hx
    have h3 : Real.exp (-(H om x)) ≤ Real.exp S := Real.exp_le_exp.mpr (by linarith)
    rw [hpt0 x hx, mul_comm (Real.exp S)]
    exact mul_le_mul_of_nonneg_left h3 (hgpos x)
  have hlo : ∀ x ∈ B, Real.exp (-S) * gH x ≤ g0 x := by
    intro x hx
    have h1 := le_abs_self (H om x)
    have h2 := hS x hx
    have h3 : Real.exp (-S) ≤ Real.exp (-(H om x)) := Real.exp_le_exp.mpr (by linarith)
    rw [hpt0 x hx, mul_comm (Real.exp (-S))]
    exact mul_le_mul_of_nonneg_left h3 (hgpos x)
  have hvol : 0 < volume.real B := by
    have : volume B ≠ 0 := (Metric.measure_ball_pos volume _ (by positivity)).ne'
    exact ENNReal.toReal_pos this measure_ball_lt_top.ne
  have hI_up : ∫ x in B, g0 x ≤ Real.exp S * ∫ x in B, gH x := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hint g0 hc0) ((hint gH hcH).const_mul _) measurableSet_ball hup
  have hI_lo : Real.exp (-S) * ∫ x in B, gH x ≤ ∫ x in B, g0 x := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on ((hint gH hcH).const_mul _) (hint g0 hc0) measurableSet_ball hlo
  have hb0 : aux_rem_resolved_meshes_bref M (fun _ => 0) om N k z = (volume.real B)⁻¹ * ∫ x in B, g0 x :=
    rfl
  have hbH : aux_rem_resolved_meshes_bref M H om N k z = (volume.real B)⁻¹ * ∫ x in B, gH x := rfl
  have hbHpos : 0 < aux_rem_resolved_meshes_bref M H om N k z :=
    aux_lane4_two_mesh_energy_bound_bpos M H om N k z
  have hb0pos : 0 < aux_rem_resolved_meshes_bref M (fun _ => 0) om N k z :=
    aux_lane4_two_mesh_energy_bound_bpos M (fun _ => 0) om N k z
  have hvi : 0 < (volume.real B)⁻¹ := inv_pos.2 hvol
  constructor
  · rw [hb0, hbH]
    calc (volume.real B)⁻¹ * ∫ x in B, g0 x ≤ (volume.real B)⁻¹ * (Real.exp S * ∫ x in B, gH x) :=
          mul_le_mul_of_nonneg_left hI_up hvi.le
      _ = Real.exp S * ((volume.real B)⁻¹ * ∫ x in B, gH x) := by ring
  · have hlow : Real.exp (-S) * aux_rem_resolved_meshes_bref M H om N k z ≤
        aux_rem_resolved_meshes_bref M (fun _ => 0) om N k z := by
      rw [hb0, hbH]
      calc Real.exp (-S) * ((volume.real B)⁻¹ * ∫ x in B, gH x)
          = (volume.real B)⁻¹ * (Real.exp (-S) * ∫ x in B, gH x) := by ring
        _ ≤ (volume.real B)⁻¹ * ∫ x in B, g0 x := mul_le_mul_of_nonneg_left hI_lo hvi.le
    have h1 : (aux_rem_resolved_meshes_bref M (fun _ => 0) om N k z)⁻¹ ≤
        (Real.exp (-S) * aux_rem_resolved_meshes_bref M H om N k z)⁻¹ :=
      inv_anti₀ (mul_pos (Real.exp_pos _) hbHpos) hlow
    rw [mul_inv, Real.exp_neg, inv_inv] at h1
    exact h1

/-- The balls of the reference mesh around points of `[0,1]^d` stay in `closedCube c 2`. -/
theorem aux_lem_prefix_limit_atom_extraction_ball_sub_Q2 (k : ℕ) (z : SpatialCoordinates d)
    (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1) :
    Metric.ball z ((3 : ℝ) ^ (-((k : ℤ))) / 2) ⊆
      (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 2 two_pos : Set (SpatialCoordinates d)) := by
  intro x hx
  have h3 : (3 : ℝ) ^ (-((k : ℤ))) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by omega)
  have hzc : dist z (fun _ : Fin d => (1 / 2 : ℝ)) ≤ 1 / 2 := by
    rw [dist_pi_le_iff (by norm_num)]
    intro i
    rw [Real.dist_eq]
    have := hz i
    rw [abs_le]
    constructor <;> linarith
  change dist x (fun _ : Fin d => (1 / 2 : ℝ)) ≤ 2 / 2
  have hxz : dist x z < (3 : ℝ) ^ (-((k : ℤ))) / 2 := hx
  linarith [dist_triangle x z (fun _ : Fin d => (1 / 2 : ℝ))]

/-- The prefix allowance of the root `(n, π, i)` at cutoff `N` (as in `rem_resolved_meshes`). -/
def aux_lem_prefix_limit_atom_extraction_allow
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    {M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d} {E : in_J d} {Sreg : in_6_16 d M}
    (It : in_iteration d M E Sreg) (αT : ℝ) (N n : ℕ)
    (pi : (Fin d → Fin (3 ^ (n + 1) + 1)) × ((Fin (d + 1) → Fin (n + 1 + 1)) × Equiv.Perm (Fin d)))
    (i : Fin (d + 1)) (om : BilateralField d) : ℝ :=
  aux_rem_resolved_meshes_B (fun z m => It.prefixLen z αT m (aux_rem_resolved_meshes_relabel N om))
    N 1 It.k (fun a => ((pi.1 a : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))))
    (Finset.univ.filter (fun a : Fin d => (pi.2.2.symm a).val < i.val)) (pi.2.1 i).val

/-- **The two-mesh macro bound for the zero-infrared Neumann problem** on the unit cube, with the
carried deterministic good-scale input `D` (through `prop_folded_iteration` inside the finite
one-step estimate). -/
theorem aux_lem_prefix_limit_atom_extraction_meshes0
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Lstar Rstar t0 eta etas p q : ℝ)
    (hLstar : 10 ≤ Lstar) (hRstar_pos : 0 < Rstar) (hRstar_lt : Rstar < 1 / (100 * Lstar))
    (hRstar_mem : Rstar ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2))
    (ht0_low : (d : ℝ) - 1 < t0) (ht0_high : t0 < (d : ℝ))
    (heta_pos : 0 < eta) (heta_lt : eta < t0 - ((d : ℝ) - 1))
    (hetas_pos : 0 < etas) (hetas_lt : etas < (d : ℝ) + 2 - t0)
    (hp : 1 ≤ p) (hpq : p ≤ q) (hdq_eta : (d : ℝ) < q * eta) :
    ∃ Cm delta0 : ℝ, 0 < Cm ∧ 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (E : in_J d)
        (Poinc : in_poincare d hd E) (Ext : in_extension d hd E)
        (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg)
        (hdet : @lane4_deterministic_good_scale_input d
          ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩),
        M.delta ≤ delta0 →
      ∃ (U V : ℕ → BilateralField d → ℝ) (Cp : ℝ), 0 ≤ Cp ∧
        (∀ N om, 0 ≤ U N om) ∧ (∀ N om, 0 ≤ V N om) ∧
        (∀ N, MemLp (U N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ N, MemLp (V N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
        (∀ N, eLpNorm (U N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cp) ∧
        (∀ N, eLpNorm (V N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cp) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
          ∀ f : SpatialCoordinates d → ℝ,
            AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          ∀ Kf : ℝ, 0 ≤ Kf →
            (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)), |f y| ≤ Kf) →
            (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
          ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
            SolvesNeumann (cutoffPositiveCoefficient M (fun _ => 0) om N
              (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) f u →
          ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
          ∀ r : ℝ, (3 : ℝ) ^ (-(N : ℤ)) ≤ r →
            aux_rem_resolved_meshes_energy
                (cutoffPositiveCoefficient M (fun _ => 0) om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) u
                {y | ∀ i : Fin d, |y i - x i| < r / 2} ≤
              Cm * U N om * r ^ (t0 - eta) *
                (aux_rem_resolved_meshes_energy
                    (cutoffPositiveCoefficient M (fun _ => 0) om N (fun _ : Fin d => (1 / 2 : ℝ))
                      one_pos) u (unitNeumannCube d : Set (SpatialCoordinates d)) +
                  V N om * Kf ^ 2) := by
  have hfin := aux_rem_resolved_meshes_finite_onestep_holds d hd Lstar Rstar t0 hLstar ht0_low
    ht0_high
  obtain ⟨Kt, C1, delta1, hKt, hC1, hdelta1, hF⟩ := hfin
  have ht0 : 0 < t0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = t0 * Real.log 3 + 1 := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  obtain ⟨Cstep, hCstepdef⟩ : ∃ Cs : ℝ, Cs = max 1 (7 * C1) := ⟨_, rfl⟩
  have hCstep : 1 ≤ Cstep := by rw [hCstepdef]; exact le_max_left _ _
  have hq1 : 1 ≤ q := hp.trans hpq
  have h2p : 1 ≤ 2 * p := by linarith
  have href0 := lane4_reference_mesh_statistic d 1 hd le_rfl (2 * p) (2 * p) etas h2p h2p hetas_pos
  obtain ⟨qref, hpqref, hqqref, hgapref, dref, Cmom, Crate, Cosc, CV, hdref, hCmom, hCrate,
    hCosc, hCV, hdref1, hbudget, href⟩ := href0
  obtain ⟨cC, c1, c2, hcC1, -, -, hconst⟩ := aux_prop_folded_iteration_carrier_constants d hd
  have hKt1 : 1 ≤ Kt := by
    have h3 : (1 : ℝ) < (3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) :=
      Real.one_lt_rpow (by norm_num) (by norm_num)
    have : 0 ≤ 3 * (d : ℝ) / ((3 : ℝ) ^ (1 - 2 * (1 / 32 : ℝ)) - 1) :=
      div_nonneg (by positivity) (by linarith)
    linarith
  have hα1 : 0 < 1 - (t0 + 2 - (d : ℝ)) / 2 := by linarith
  have haT : 1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt < 1 := by
    have : 0 < (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt := div_pos hα1 (by linarith)
    linarith
  have haThalf : 1 / 2 ≤ 1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt := by
    have h1 : (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt ≤ 1 - (t0 + 2 - (d : ℝ)) / 2 :=
      div_le_self hα1.le hKt1
    linarith
  have hr1 : 1 ≤ ((d : ℝ) + 1) * q := by
    have : (1 : ℝ) ≤ (d : ℝ) + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    nlinarith
  have hr0 : 0 < ((d : ℝ) + 1) * q := by linarith
  have hδfacts := aux_rem_resolved_meshes_delta_facts cC
    (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) (((d : ℝ) + 1) * q) c hcC1 haT hr0 hc
  rcases hδfacts with ⟨hδm, hδall⟩
  have hK1 : 1 ≤ Real.exp (c * (((1 : ℕ) : ℝ) + 26)) *
      (Real.exp (c * (cC + 1)) * (1 + cC)) := by
    have h1 : 1 ≤ Real.exp (c * (((1 : ℕ) : ℝ) + 26)) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ Real.exp (c * (cC + 1)) := Real.one_le_exp (by positivity)
    have h3 : 1 ≤ Real.exp (c * (cC + 1)) * (1 + cC) :=
      one_le_mul_of_one_le_of_one_le h2 (by linarith)
    exact one_le_mul_of_one_le_of_one_le h1 h3
  refine ⟨2 ^ d + (36 * (3 * (1 + 100 * Lstar)) ^ d) ^ t0 * 3 ^ eta * 2 ^ t0 *
      (Rstar ^ (-t0) + (d : ℝ) + 1),
    min dref (min delta1 (min (1 / 2) (min (1 / cC)
      (min (((1 - (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt)) / cC) ^ 2)
        ((1 - (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt)) ^ 2 /
          (2 * (((d : ℝ) + 1) * q) * c * cC)))))),
    aux_lane4_two_mesh_energy_bound_Cpos d Lstar Rstar t0 eta hLstar hRstar_pos,
    lt_min hdref (lt_min hdelta1 hδm), ?_⟩
  intro M E Poinc Ext Rm Sreg It hdet hδ
  have hδref : M.delta ≤ dref := hδ.trans (min_le_left _ _)
  have hδ1 : M.delta ≤ delta1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδm' := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδf := hδall M.delta hδpos hδm'
  rcases hδf with ⟨hdC, haTr, hrate⟩
  have hCeq : It.C = cC := (hconst E M Sreg It).1
  have hαT : (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) ∈ It.alphaRange := by
    rw [It.alphaRange_eq, hCeq]
    exact ⟨haThalf, haTr⟩
  have hδIt : M.delta ≤ It.C⁻¹ := by rw [hCeq]; exact hdC
  obtain ⟨H, hH⟩ := exists_infraredCharacterization hd M
  have hR := href M Rm H hH hδref
  rcases hR with ⟨-, -, -, -, -, VH, -, hVH0, hVHmem, hVHnorm, hVHae⟩
  -- the prefix majorant
  have hBmom : ∀ (N n : ℕ)
      (pi : (Fin d → Fin (3 ^ (n + 1) + 1)) × ((Fin (d + 1) → Fin (n + 1 + 1)) × Equiv.Perm (Fin d)))
      (i : Fin (d + 1)),
      MemLp (fun om => Real.exp (c * aux_lem_prefix_limit_atom_extraction_allow It
          (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) N n pi i om))
        (ENNReal.ofReal (((d : ℝ) + 1) * q)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => Real.exp (c * aux_lem_prefix_limit_atom_extraction_allow It
          (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) N n pi i om))
        (ENNReal.ofReal (((d : ℝ) + 1) * q)) (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (Real.exp (c * (((1 : ℕ) : ℝ) + 26)) *
          (Real.exp (c * (cC + 1)) * (1 + cC))) :=
    fun N n pi i => aux_rem_resolved_meshes_allowance_moment It cC hCeq hcC1 _ hαT hδIt c
      (((d : ℝ) + 1) * q) hc hr1 hrate 1 _ N (pi.2.1 i).val
  have hB0 : ∀ (N n : ℕ)
      (pi : (Fin d → Fin (3 ^ (n + 1) + 1)) × ((Fin (d + 1) → Fin (n + 1 + 1)) × Equiv.Perm (Fin d)))
      (i : Fin (d + 1)) (om : BilateralField d),
      0 ≤ aux_lem_prefix_limit_atom_extraction_allow It
        (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) N n pi i om := by
    intro N n pi i om
    unfold aux_lem_prefix_limit_atom_extraction_allow aux_rem_resolved_meshes_B
    split_ifs <;> positivity
  have hU := aux_rem_resolved_meshes_regularity d 1 (chaosSampleLaw M).toMeasure p q eta hp hpq
    heta_pos hdq_eta Cstep c
    (Real.exp (c * (((1 : ℕ) : ℝ) + 26)) * (Real.exp (c * (cC + 1)) * (1 + cC)))
    hCstep hc.le hK1 (fun N n pi i om => aux_lem_prefix_limit_atom_extraction_allow It
      (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) N n pi i om) hB0
    (fun N n pi i => (hBmom N n pi i).1) (fun N n pi i => (hBmom N n pi i).2)
  rcases hU with ⟨U, -, hU0, hUmem, hUnorm, hUae, hRb⟩
  -- the reference majorant for the zero infrared field
  set K2 : Compacts (SpatialCoordinates d) := closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 2 two_pos
  obtain ⟨Sx, hSx⟩ : ∃ Sx : BilateralField d → ℝ,
      Sx = fun om => ‖(H om).restrict (K2 : Set (SpatialCoordinates d))‖ := ⟨_, rfl⟩
  have hEmem : MemLp (fun om => Real.exp (Sx om)) (ENNReal.ofReal (2 * p))
      (chaosSampleLaw M).toMeasure := by
    rw [hSx]
    exact aux_lem_prefix_limit_atom_extraction_expSup_memLp hd M H hH K2 (2 * p) (by linarith)
  obtain ⟨CE0, hCE0⟩ : ∃ CE0 : ℝ, CE0 = (eLpNorm (fun om => Real.exp (Sx om))
      (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure).toReal := ⟨_, rfl⟩
  have hp0 : 0 < p := by linarith
  have hV0mom : ∀ N, MemLp (fun om => Real.exp (Sx om) * VH N om) (ENNReal.ofReal p)
      (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => Real.exp (Sx om) * VH N om) (ENNReal.ofReal p)
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (CE0 * CV) := by
    intro N
    have hb := aux_rem_resolved_microscopic_product_lq_bound (chaosSampleLaw M).toMeasure p
      (2 * p) hp0 le_rfl _ _ hEmem (hVHmem N)
    refine ⟨lt_of_le_of_lt hb (ENNReal.mul_lt_top hEmem.eLpNorm_lt_top
      (hVHmem N).eLpNorm_lt_top), hb.trans ?_⟩
    have hCE0nn : 0 ≤ CE0 := by rw [hCE0]; exact ENNReal.toReal_nonneg
    rw [ENNReal.ofReal_mul hCE0nn]
    gcongr
    · rw [hCE0, ENNReal.ofReal_toReal hEmem.eLpNorm_lt_top.ne]
    · exact hVHnorm N
  refine ⟨U, fun N om => Real.exp (Sx om) * VH N om,
    max (aux_rem_resolved_meshes_Rbound d 1 eta q Cstep
      (Real.exp (c * (((1 : ℕ) : ℝ) + 26)) * (Real.exp (c * (cC + 1)) * (1 + cC)))).toReal
      (CE0 * CV), le_max_of_le_left ENNReal.toReal_nonneg, hU0,
    fun N om => mul_nonneg (Real.exp_pos _).le (hVH0 N om), hUmem,
    fun N => (hV0mom N).1, fun N => ?_, fun N => ?_, ?_⟩
  · refine (hUnorm N).trans (le_trans (le_of_eq (ENNReal.ofReal_toReal hRb).symm) ?_)
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  · exact (hV0mom N).2.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  filter_upwards [hUae, hVHae] with om hUlub hVlub
  intro N f hf Kf hKf hfb hf0 u hu x hx r hr
  have hUcore : ∀ (n : ℕ) (g : Fin d → Fin (3 ^ (n + 1) + 1))
      (dep : Fin (d + 1) → Fin (n + 1 + 1)) (σ : Equiv.Perm (Fin d)),
      (3 : ℝ) ^ (-eta * (n : ℝ)) * (Cstep ^ (d + 1) * Real.exp (c * ∑ j : Fin (d + 1),
        aux_rem_resolved_meshes_B
          (fun z m => It.prefixLen z (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) m
            (aux_rem_resolved_meshes_relabel N om)) N 1 It.k
          (fun i => ((g i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((n + 1 : ℕ) : ℤ))))
          (Finset.univ.filter (fun i : Fin d => (σ.symm i).val < j.val)) (dep j).val)) ≤
        U N om := by
    intro n g dep σ
    exact (hUlub N).1 ⟨n, (g, (dep, σ)), rfl⟩
  have hV0' : ∀ k : ℕ, k ≤ N → ∀ z : SpatialCoordinates d, (∀ i, 0 ≤ z i ∧ z i ≤ 1) →
      aux_rem_resolved_meshes_bref M (fun _ => 0) om N k z +
        (aux_rem_resolved_meshes_bref M (fun _ => 0) om N k z)⁻¹ ≤
        (Real.exp (Sx om) * VH N om) * ((3 : ℝ) ^ (-((k : ℤ))) / 2) ^ (-etas) := by
    intro k hk z hz
    have hS : ∀ y ∈ Metric.ball z ((3 : ℝ) ^ (-((k : ℤ))) / 2), |H om y| ≤ Sx om := by
      intro y hy
      rw [hSx]
      exact aux_lem_prefix_limit_atom_extraction_restrict_bound (H om) K2 y
        (aux_lem_prefix_limit_atom_extraction_ball_sub_Q2 k z hz hy)
    obtain ⟨h1, h2⟩ := aux_lem_prefix_limit_atom_extraction_bref_cmp M H om N k z (Sx om) hS
    have hH := (hVlub N).2 k hk z hz
    have hsum : aux_rem_resolved_meshes_bref M (fun _ => 0) om N k z +
        (aux_rem_resolved_meshes_bref M (fun _ => 0) om N k z)⁻¹ ≤
        Real.exp (Sx om) * (aux_rem_resolved_meshes_bref M H om N k z +
          (aux_rem_resolved_meshes_bref M H om N k z)⁻¹) := by
      rw [mul_add]; exact add_le_add h1 h2
    refine hsum.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hH (Real.exp_pos _).le
  have hone := aux_lem_prefix_limit_atom_extraction_onestep0 d hd Lstar Rstar t0 hLstar hRstar_lt
    ht0 Kt C1 delta1 hC1 hF M E Poinc Ext Sreg It hdet hδ1 om N f hf Kf hKf hfb hf0 u hu
  rw [← hCstepdef, ← hcdef] at hone
  exact aux_rem_resolved_meshes_energy_app d hd Lstar Rstar t0 eta etas hLstar hRstar_pos
    hRstar_lt hRstar_mem ht0_low ht0_high heta_pos heta_lt hetas_pos hetas_lt 1 le_rfl Cstep c
    hCstep hc.le M (fun _ => 0) om N _ u Kf
    (fun z m => It.prefixLen z (1 - (1 - (t0 + 2 - (d : ℝ)) / 2) / Kt) m
      (aux_rem_resolved_meshes_relabel N om)) It.k hone (U N om) hUcore _ hV0' x hx r hr

end PaeN0Mesh

section PaeN0Ext

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

theorem aux_lem_prefix_limit_atom_extraction_extremes0_lh (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (z : SpatialCoordinates d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ Cp Cd cd : ℝ, 0 < Cp ∧ 0 < Cd ∧ 0 < cd ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ cd / (2 * q) →
        ∃ (D mlow mhigh : ℕ → BilateralField d → ℝ) (CE : ℝ), 0 ≤ CE ∧
          (∀ N om, 0 ≤ D N om) ∧
          (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N,
            (∀ x y, x ∈ (closedCube z 1 one_pos : Set (SpatialCoordinates d)) →
                y ∈ (closedCube z 1 one_pos : Set (SpatialCoordinates d)) →
                |Real.log (cutoffCoefficient M (fun _ => 0) om N x) -
                    Real.log (cutoffCoefficient M (fun _ => 0) om N y)| ≤
                  D N om * (3 : ℝ) ^ N * dist x y) ∧
            (0 < mlow N om ∧
              ∀ x ∈ (closedCube z 1 one_pos : Set (SpatialCoordinates d)),
                mlow N om ≤ cutoffCoefficient M (fun _ => 0) om N x ∧
                  cutoffCoefficient M (fun _ => 0) om N x ≤ mhigh N om)) ∧
          (∀ N, MemLp (D N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure) ∧
          (∀ N, MemLp (fun omega => mhigh N omega + (mlow N omega)⁻¹)
            (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure) ∧
          (∀ N, eLpNorm (D N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cp * Real.sqrt (1 + (N : ℝ)))) ∧
          (∀ N, eLpNorm (fun om => mhigh N om + (mlow N om)⁻¹) (ENNReal.ofReal q)
              (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (CE * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N))) := by
  obtain ⟨Cp, Cd, cd, hCp, hCd, hcd, hext⟩ :=
    aux_lem_prefix_limit_atom_extraction_extremes0 d hd z q hq
  refine ⟨Cp, Cd, cd, hCp, hCd, hcd, fun M hδ => ?_⟩
  obtain ⟨D, Mx, CE, hCE, hDMx0, hae, hmem, hDmom, hMxmom⟩ := hext M hδ
  have hmm : ∀ N om, Mx N om + ((Mx N om)⁻¹)⁻¹ = 2 * Mx N om := by
    intro N om; rw [inv_inv]; ring
  refine ⟨D, fun N om => (Mx N om)⁻¹, Mx, 2 * CE, mul_nonneg zero_le_two hCE,
    fun N om => (hDMx0 N om).1, ?_, fun N => (hmem N).1, fun N => ?_, hDmom, fun N => ?_⟩
  · filter_upwards [hae] with om hom
    intro N
    obtain ⟨h1, h2, h3⟩ := hom N
    exact ⟨h3, inv_pos.2 h1, h2⟩
  · simp only [hmm]
    exact (hmem N).2.const_mul 2
  · simp only [hmm]
    calc eLpNorm (fun om => 2 * Mx N om) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure
        = ENNReal.ofReal 2 * eLpNorm (Mx N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure := by
          rw [show (fun om => 2 * Mx N om) = (2 : ℝ) • Mx N from rfl, eLpNorm_const_smul,
            Real.enorm_eq_ofReal (by norm_num)]
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (CE * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N)) := by
          gcongr; exact hMxmom N
      _ = ENNReal.ofReal (2 * CE * Real.exp ((Cd * M.delta + Cp * M.delta ^ 2) * N)) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring

end PaeN0Ext

section PaeN0Res

open MeasureTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

theorem aux_lem_prefix_limit_atom_extraction_resolved0 :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (t : ℝ) (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < (d : ℝ) →
    (∀ i : Fin k, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (_Rm : in_responses d M) (Sreg : in_6_16 d M)
      (_It : in_iteration d M E Sreg), M.delta ≤ delta0 →
    let Q : Opens (SpatialCoordinates d) := unitNeumannCube d
    let a : ℕ → BilateralField d → PositiveCoefficient Q :=
      fun N omega => cutoffPositiveCoefficient M (fun _ => 0) omega N
        (fun _ : Fin d => (1 / 2 : ℝ)) one_pos
    ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
      (∀ N omega, 0 ≤ K N omega) ∧
      (∀ i N,
        MemLp (K N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure) ∧
      (∀ i N,
        eLpNorm (K N) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cbound i)) ∧
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        (∀ N : ℕ,
          ∀ f : SpatialCoordinates d → ℝ,
            AEMeasurable f (volume.restrict (Q : Set (SpatialCoordinates d))) →
          ∀ Kf : ℝ, 0 ≤ Kf →
            (∀ᵐ y ∂volume.restrict (Q : Set (SpatialCoordinates d)),
              |f y| ≤ Kf) →
            (∫ y in (Q : Set (SpatialCoordinates d)), f y) = 0 →
          ∀ u : meanZeroSobolevGraph Q,
            SolvesNeumann (a N omega) f u →
          ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            localGradientEnergy (a N omega)
              (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
              (sobolevGradient (u : SobolevData Q)) ≤
                K N omega *
                  (sobolevCoefficientForm (a N omega)
                    (u : SobolevData Q) (u : SobolevData Q) + Kf ^ 2) * r ^ t) ∧
        (∀ N : ℕ,
          ∀ rho : ℝ → ℝ, ContDiff ℝ ∞ rho →
            (∀ tau : ℝ, 0 ≤ rho tau) →
            (∀ tau : ℝ, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
            (∫ tau, rho tau) = 1 →
          ∀ pvec : Fin d → ℝ, (∑ i : Fin d, (pvec i) ^ 2) = 1 →
          ∀ Cρ : ℝ, 0 ≤ Cρ →
            (∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
              ∀ y : SpatialCoordinates d, y ∈ (Q : Set (SpatialCoordinates d)) →
                |faceBump rho pvec eps y| ≤ Cρ * eps⁻¹) →
          ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
          ∀ v : meanZeroSobolevGraph Q,
            SolvesNeumann (a N omega) (faceBump rho pvec eps) v →
          ∀ x : SpatialCoordinates d, x ∈ (Q : Set (SpatialCoordinates d)) →
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            localGradientEnergy (a N omega)
              (s := Metric.ball x r ∩ (Q : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter Q.isOpen.measurableSet)
              (sobolevGradient (v : SobolevData Q)) ≤
                K N omega *
                  (sobolevCoefficientForm (a N omega)
                    (v : SobolevData Q) (v : SobolevData Q) +
                    Cρ ^ 2 * eps ^ (-2 : ℝ)) * r ^ t) := by
  intro d hd _ _ E _P _X _W D t k ps ht_low ht_high hps
  have hdt : 0 < (d : ℝ) - t := by linarith
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ht_nn : 0 ≤ t := by linarith
  -- exponents: t < t1 < t0 < d, eta = t0 - t1, all fixed before disorder
  have hex1 : ∃ t1 : ℝ, t1 = t + ((d : ℝ) - t) / 3 := ⟨_, rfl⟩
  obtain ⟨t1, ht1⟩ := hex1
  have hex0 : ∃ t0 : ℝ, t0 = t + 2 * ((d : ℝ) - t) / 3 := ⟨_, rfl⟩
  obtain ⟨t0, ht0⟩ := hex0
  have htt1 : t < t1 := by rw [ht1]; linarith
  have ht1d : t1 < (d : ℝ) := by rw [ht1]; linarith
  have ht0_low : (d : ℝ) - 1 < t0 := by rw [ht0]; linarith
  have ht0_high : t0 < (d : ℝ) := by rw [ht0]; linarith
  have heta_pos : 0 < t0 - t1 := by rw [ht0, ht1]; linarith
  have heta_lt : t0 - t1 < t0 - ((d : ℝ) - 1) := by rw [ht0, ht1]; linarith
  have hetas_pos : 0 < ((d : ℝ) + 2 - t0) / 2 := by linarith
  have hetas_lt : ((d : ℝ) + 2 - t0) / 2 < (d : ℝ) + 2 - t0 := by linarith
  -- one moment order covering the finite list
  have hexp : ∃ pmax : ℝ, pmax = 1 + ∑ i : Fin k, |ps i| := ⟨_, rfl⟩
  obtain ⟨pmax, hpmax_def⟩ := hexp
  have hsum_nn : 0 ≤ ∑ i : Fin k, |ps i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hpmax : 1 ≤ pmax := by rw [hpmax_def]; linarith
  have hps_le : ∀ i : Fin k, ps i ≤ pmax := by
    intro i
    have h1 : ps i ≤ |ps i| := le_abs_self _
    have h2 : |ps i| ≤ ∑ j : Fin k, |ps j| :=
      Finset.single_le_sum (f := fun j => |ps j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [hpmax_def]; linarith
  have hmax1 : (1 : ℝ) ≤ max 1 t := le_max_left _ _
  have hq1 : 1 ≤ 2 * pmax * max 1 t := by nlinarith
  have hpq : pmax ≤ 2 * pmax * max 1 t := by nlinarith
  have hqmesh_p : 1 ≤ 2 * (2 * pmax * max 1 t) := by linarith
  have hqmesh_q : 2 * (2 * pmax * max 1 t) ≤
      max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) := le_max_left _ _
  have hqmesh_eta : (d : ℝ) <
      max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) * (t0 - t1) := by
    have h1 : ((d : ℝ) + 1) / (t0 - t1) * (t0 - t1) = (d : ℝ) + 1 := by
      field_simp
    have h2 : ((d : ℝ) + 1) / (t0 - t1) * (t0 - t1) ≤
        max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1)) * (t0 - t1) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) heta_pos.le
    linarith
  -- geometric root radius
  have hRpos : (0 : ℝ) < (3 : ℝ) ^ (-7 : ℤ) / 2 := by positivity
  have hRlt : (3 : ℝ) ^ (-7 : ℤ) / 2 < 1 / (100 * 10) := by norm_num
  have hRmem : (3 : ℝ) ^ (-7 : ℤ) / 2 ∈ Set.range (fun k : ℤ => (3 : ℝ) ^ k / 2) := ⟨-7, rfl⟩
  -- the large-scale common package
  have hM := aux_lem_prefix_limit_atom_extraction_meshes0 d hd 10 ((3 : ℝ) ^ (-7 : ℤ) / 2) t0 (t0 - t1)
    (((d : ℝ) + 2 - t0) / 2) (2 * (2 * pmax * max 1 t))
    (max (2 * (2 * pmax * max 1 t)) (((d : ℝ) + 1) / (t0 - t1))) (by norm_num) hRpos hRlt hRmem
    ht0_low ht0_high heta_pos heta_lt hetas_pos hetas_lt hqmesh_p hqmesh_q hqmesh_eta
  rcases hM with ⟨Cm, delta0m, hCm, hdelta0m, hmesh⟩
  -- the microscopic matched range
  have hp1 : (2 : ℝ) ≤ 2 + 4 * (d : ℝ) / ((d : ℝ) - t) := by
    have : 0 ≤ 4 * (d : ℝ) / ((d : ℝ) - t) := by positivity
    linarith
  have htp : t < (d : ℝ) - 2 * (d : ℝ) / (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) := by
    have hp1pos : 0 < 2 + 4 * (d : ℝ) / ((d : ℝ) - t) := by linarith
    have hkey : 2 * (d : ℝ) / (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) < ((d : ℝ) - t) / 2 := by
      rw [div_lt_iff₀ hp1pos]
      have h4 : ((d : ℝ) - t) * (4 * (d : ℝ) / ((d : ℝ) - t)) = 4 * (d : ℝ) := by
        field_simp
      nlinarith
    linarith
  have hml := aux_rem_resolved_micro_local d hd _W (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) t t1 hp1
    ht_low htt1 ht1d htp
  rcases hml with ⟨Cmic, hCmic, hmicL⟩
  have hms := rem_resolved_microscopic d hd _W (2 + 4 * (d : ℝ) / ((d : ℝ) - t)) t t1 hp1
    ht_low htt1 ht1d htp
  rcases hms with ⟨_, _, _, _, _, _, hstat⟩
  -- extremes of the actual cutoff coefficient on the closed unit cube
  have hX := aux_lem_prefix_limit_atom_extraction_extremes0_lh d hd (fun _ => (1 / 2 : ℝ))
    (2 * pmax * max 1 t) hq1
  rcases hX with ⟨Cpe, Cde, cde, hCpe, hCde, hcde, hextM⟩
  -- rate budget
  have hexr : ∃ rmax : ℝ,
      rmax = min (t1 - t) (min ((d : ℝ) + 2 - t) ((d : ℝ) - t)) * Real.log 3 := ⟨_, rfl⟩
  obtain ⟨rmax, hrmax_def⟩ := hexr
  have hrmax : 0 < rmax := by
    rw [hrmax_def]
    refine mul_pos (lt_min (by linarith) (lt_min (by linarith) hdt)) ?_
    exact Real.log_pos (by norm_num)
  have hqpos : 0 < 2 * pmax * max 1 t := by linarith
  refine ⟨min (min delta0m (cde / (2 * (2 * pmax * max 1 t))))
    (min 1 (rmax / (2 * (Cde + Cpe)))), ?_, ?_⟩
  · refine lt_min (lt_min hdelta0m (div_pos hcde (mul_pos two_pos hqpos))) (lt_min one_pos ?_)
    exact div_pos hrmax (by positivity)
  intro M _Rm Sreg _It hδ Q a
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hδm : M.delta ≤ delta0m := hδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδe : M.delta ≤ cde / (2 * (2 * pmax * max 1 t)) :=
    hδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ1 : M.delta ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδr : M.delta ≤ rmax / (2 * (Cde + Cpe)) :=
    hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrate := aux_rem_resolved_rate Cde Cpe rmax M.delta hCde hCpe hrmax hδpos hδ1 hδr
  rw [hrmax_def] at hrate
  -- instantiate the large-scale package and the extremes on the same sample law
  have hmM := hmesh M E _P _X _Rm Sreg _It D hδm
  rcases hmM with ⟨U, V, Cp, hCp, hU0, hV0, hULp, hVLp, hUb, hVb, hae⟩
  have heM := hextM M hδe
  rcases heM with ⟨De, mlow, mhigh, CE, hCE, hDe0, heae, hDeLp, hmLp, hDeb, hmb⟩
  have hW : ∀ N : ℕ,
      MemLp (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
        (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => U N om * (1 + V N om)) (ENNReal.ofReal (2 * pmax * max 1 t))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp * (1 + Cp)) := fun N =>
    aux_rem_resolved_UV_moment (chaosSampleLaw M).toMeasure (2 * pmax * max 1 t) Cp hq1 hCp
      (U N) (V N) (hULp N) (hVLp N) (hUb N) (hVb N)
  have hSb : ∀ N : ℕ,
      eLpNorm (fun om => ‖mhigh N om + (mlow N om)⁻¹‖ + ‖mhigh N om + (mlow N om)⁻¹‖)
        (ENNReal.ofReal (2 * pmax * max 1 t)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * CE *
        Real.exp ((Cde * M.delta + Cpe * M.delta ^ 2) * (N : ℝ))) := by
    intro N
    have h2 : (fun om => ‖mhigh N om + (mlow N om)⁻¹‖ + ‖mhigh N om + (mlow N om)⁻¹‖) =
        fun om => 2 * ‖mhigh N om + (mlow N om)⁻¹‖ := by
      funext om; ring
    have hm := hmb N
    calc _ = ENNReal.ofReal 2 * eLpNorm (fun om => mhigh N om + (mlow N om)⁻¹)
            (ENNReal.ofReal (2 * pmax * max 1 t)) (chaosSampleLaw M).toMeasure := by
          rw [h2, aux_rem_resolved_microscopic_nonneg_scalar_eLpNorm _ _ 2 (by norm_num),
            eLpNorm_norm]
          simpa using! (hmLp N).aestronglyMeasurable
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal
            (CE * Real.exp ((Cde * M.delta + Cpe * M.delta ^ 2) * (N : ℝ))) := by
          gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  have hstatM := hstat (BilateralField d) (chaosSampleLaw M).toMeasure pmax hpmax De
    (fun N om => ‖mhigh N om + (mlow N om)⁻¹‖) (fun N om => ‖mhigh N om + (mlow N om)⁻¹‖)
    (fun N om => U N om * (1 + V N om)) Cpe (2 * CE) (Cp * (1 + Cp))
    (Cde * M.delta + Cpe * M.delta ^ 2) hCpe.le (mul_nonneg zero_le_two hCE)
    (mul_nonneg hCp (add_nonneg zero_le_one hCp)) hrate.1 hrate.2
    (fun N om => ⟨hDe0 N om, norm_nonneg _, norm_nonneg _,
      mul_nonneg (hU0 N om) (by linarith [hV0 N om])⟩)
    (fun N => ⟨hDeLp N, (hmLp N).norm, (hmLp N).norm, (hW N).1⟩)
    hDeb hSb (fun N => (hW N).2)
  rcases hstatM with ⟨B, hB0, hBN⟩
  have hA1 : 0 ≤ Cm * 2 ^ t1 := mul_nonneg hCm.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA3 : 0 ≤ Cmic * 2 ^ t := mul_nonneg hCmic.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA2 : 0 ≤ Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1) :=
    mul_nonneg hA3 (mul_nonneg hCm.le
      (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _).le)
  have hmom : ∀ (i : Fin k) (N : ℕ),
      MemLp (fun om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ∧
      eLpNorm (fun om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)))
        (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((Cm * 2 ^ t1) * (Cp * (1 + Cp)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) * B + (Cmic * 2 ^ t) * B) := by
    intro i N
    have hBNN := hBN N
    beta_reduce at hBNN
    have hWm := (hW N).1.aestronglyMeasurable
    have hDt := (aux_rem_resolved_microscopic_one_add_power_memLp (chaosSampleLaw M).toMeasure
      pmax t hpmax ht_nn (De N) (hDe0 N) (hDeLp N)).aestronglyMeasurable
    have hT1m : AEStronglyMeasurable (fun om =>
        (1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om)))
        (chaosSampleLaw M).toMeasure :=
      (hDt.mul aestronglyMeasurable_const).mul hWm
    have hT2m : AEStronglyMeasurable (fun om =>
        ‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t))
        (chaosSampleLaw M).toMeasure :=
      (hmLp N).norm.aestronglyMeasurable.mul aestronglyMeasurable_const
    have hWb : eLpNorm (fun om => U N om * (1 + V N om)) (ENNReal.ofReal pmax)
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Cp * (1 + Cp)) :=
      (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq)).trans (hW N).2
    exact aux_rem_resolved_three_term_moment (chaosSampleLaw M).toMeasure pmax _ _ _
      (Cp * (1 + Cp)) B hpmax hA1 hA2 hA3 (by positivity) hB0 _ _ _ hWm hT1m hT2m hWb
      hBNN.1 hBNN.2.1 (ps i) (hps_le i)
  refine ⟨fun N om => (Cm * 2 ^ t1) * (U N om * (1 + V N om)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) *
          ((1 + De N om) ^ t * ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) * (U N om * (1 + V N om))) +
        (Cmic * 2 ^ t) *
          (‖mhigh N om + (mlow N om)⁻¹‖ * ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t)),
    fun _ => (Cm * 2 ^ t1) * (Cp * (1 + Cp)) +
        (Cmic * 2 ^ t * (Cm * (max Cmic 1) ^ t1)) * B + (Cmic * 2 ^ t) * B, ?_,
    fun i N => (hmom i N).1, fun i N => (hmom i N).2, ?_⟩
  · intro N om
    have h1 : 0 ≤ U N om * (1 + V N om) := mul_nonneg (hU0 N om) (by linarith [hV0 N om])
    have h2 : 0 ≤ (1 + De N om) ^ t := (Real.rpow_pos_of_pos (by linarith [hDe0 N om]) _).le
    have h3 : 0 ≤ ((3 : ℝ) ^ (-(N : ℝ))) ^ (t1 - t) :=
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _).le
    have h4 : 0 ≤ ((3 : ℝ) ^ (-(N : ℝ))) ^ ((d : ℝ) + 2 - t) :=
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _) _).le
    have h5 := norm_nonneg (mhigh N om + (mlow N om)⁻¹)
    exact add_nonneg (add_nonneg (mul_nonneg hA1 h1) (mul_nonneg hA2 (mul_nonneg (mul_nonneg h2 h3) h1)))
      (mul_nonneg hA3 (mul_nonneg h5 h4))
  · filter_upwards [hae, heae] with om hω1 hω2
    have hfirst := fun N : ℕ => aux_rem_resolved_sample d M (fun _ => 0) om N t t1 t0 Cm Cmic
      (U N om) (V N om) (De N om) (mlow N om) (mhigh N om) (le_of_lt htt1) hCm.le hCmic
      (hU0 N om) (hV0 N om) (hDe0 N om) (hω2 N).2.1 (hω2 N).2.2 (hω2 N).1
      (hmicL ((3 : ℝ) ^ (-(N : ℝ))) (Real.rpow_pos_of_pos (by norm_num) _)
        (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)))
      (hω1 N)
    exact ⟨hfirst, fun N => aux_rem_resolved_second (a N om) _ t (hfirst N)⟩

end PaeN0Res

section PaeN0Tr

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

variable {d : ℕ}

/-- The centre of the unit Neumann cube. -/
abbrev aux_lem_prefix_limit_atom_extraction_cN (d : ℕ) : SpatialCoordinates d :=
  fun _ : Fin d => (1 / 2 : ℝ)

/-- The layerwise translation by `-c`: `(τ ω)_j(x) = ω_j(x - c)`. -/
def aux_lem_prefix_limit_atom_extraction_tau (om : BilateralField d) : BilateralField d :=
  aux_prop_growth_energy_assembly_shift d (-(aux_lem_prefix_limit_atom_extraction_cN d)) om

theorem aux_lem_prefix_limit_atom_extraction_tau_apply (om : BilateralField d) (j : ℤ)
    (x : SpatialCoordinates d) :
    aux_lem_prefix_limit_atom_extraction_tau om j x =
      om j (-(aux_lem_prefix_limit_atom_extraction_cN d) + x) :=
  aux_prop_growth_energy_assembly_shift_apply d _ om j x

theorem aux_lem_prefix_limit_atom_extraction_tau_measurable
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)] :
    Measurable (aux_lem_prefix_limit_atom_extraction_tau (d := d)) := by
  refine measurable_pi_lambda fun j => ?_
  exact (ContinuousMap.continuous_precomp
    (⟨cubeDilation (-(aux_lem_prefix_limit_atom_extraction_cN d)) 0 1,
      continuous_cubeDilation _ 0 1⟩ : C(SpatialCoordinates d, SpatialCoordinates d))).measurable.comp
    (measurable_pi_apply j)

theorem aux_lem_prefix_limit_atom_extraction_tau_mp
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    MeasurePreserving (aux_lem_prefix_limit_atom_extraction_tau (d := d))
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure :=
  ⟨aux_lem_prefix_limit_atom_extraction_tau_measurable,
    aux_prop_growth_energy_assembly_shift_map M _⟩

/-- `τ` commutes with a coordinate update. -/
theorem aux_lem_prefix_limit_atom_extraction_tau_update (om om' : BilateralField d) (j : ℤ) :
    aux_lem_prefix_limit_atom_extraction_tau (Function.update om j (om' j)) =
      Function.update (aux_lem_prefix_limit_atom_extraction_tau om) j
        (aux_lem_prefix_limit_atom_extraction_tau om' j) := by
  funext i
  by_cases h : i = j
  · subst h
    unfold aux_lem_prefix_limit_atom_extraction_tau aux_prop_growth_energy_assembly_shift
    simp only [Function.update_self]
  · simp only [Function.update_of_ne h]
    unfold aux_lem_prefix_limit_atom_extraction_tau aux_prop_growth_energy_assembly_shift
    rw [Function.update_of_ne h]

/-- `τ × τ` preserves the product law. -/
theorem aux_lem_prefix_limit_atom_extraction_tau_prod_mp
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    MeasurePreserving (fun q : BilateralField d × BilateralField d =>
        (aux_lem_prefix_limit_atom_extraction_tau q.1, aux_lem_prefix_limit_atom_extraction_tau q.2))
      ((chaosSampleLaw M).toMeasure.prod (chaosSampleLaw M).toMeasure)
      ((chaosSampleLaw M).toMeasure.prod (chaosSampleLaw M).toMeasure) :=
  (aux_lem_prefix_limit_atom_extraction_tau_mp M).prod (aux_lem_prefix_limit_atom_extraction_tau_mp M)

/-- **Translation monotonicity** of the inverse affine Neumann response (unit side). -/
theorem aux_lem_prefix_limit_atom_extraction_N_translate_le (z z' : SpatialCoordinates d)
    (hP1 : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (centeredCube z 1 one_pos),
      ‖(w : SobolevData (centeredCube z 1 one_pos)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z 1 one_pos)) w‖)
    (hP2 : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (centeredCube z' 1 one_pos),
      ‖(w : SobolevData (centeredCube z' 1 one_pos)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (centeredCube z' 1 one_pos)) w‖)
    (a1 : PositiveCoefficient (centeredCube z 1 one_pos))
    (a2 : PositiveCoefficient (centeredCube z' 1 one_pos))
    (ha : ∀ᵐ x ∂volume.restrict (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)),
      a2.val x = a1.val (cubeDilation z z' 1 x))
    (p : Fin d → ℝ) :
    affineInverseNeumannResponse hP1 a1 p ≤ affineInverseNeumannResponse hP2 a2 p := by
  obtain ⟨⟨v, hv⟩, -⟩ := affineInverseNeumannResponse_isGreatest hP1 a1 p
  obtain ⟨w, hw1, hw2⟩ := aux_lem_as_regularity_affine_transport_meanzero_pullback d z z' 1
    one_pos one_pos v
  have hmax := (affineInverseNeumannResponse_isGreatest hP2 a2 p).2 ⟨w, rfl⟩
  refine le_trans (le_of_eq ?_) hmax
  rw [← hv]
  have hsc : ∀ f : SpatialCoordinates d → ℝ,
      AEMeasurable f (volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) →
      (∫ x in (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)), f (cubeDilation z z' 1 x)) =
        ∫ y in (centeredCube z 1 one_pos : Set (SpatialCoordinates d)), f y := by
    intro f hf
    rw [aux_lem_as_regularity_affine_transport_integral_scaling d z z' 1 one_pos one_pos f hf,
      one_pow, inv_one, one_mul]
  have hg : ∀ i : Fin d, AEMeasurable (((v : SobolevData (centeredCube z 1 one_pos)).2 i :
      SpatialCoordinates d → ℝ)) (volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) :=
    fun i => (Lp.aestronglyMeasurable _).aemeasurable
  have ha1 : AEMeasurable ((a1.val : SpatialCoordinates d → ℝ))
      (volume.restrict (centeredCube z 1 one_pos : Set (SpatialCoordinates d))) :=
    (Lp.aestronglyMeasurable _).aemeasurable
  have h1 : ∀ i : Fin d,
      (∫ x in (centeredCube z 1 one_pos : Set (SpatialCoordinates d)),
          p i * (v : SobolevData (centeredCube z 1 one_pos)).2 i x) =
        ∫ x in (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)),
          p i * (w : SobolevData (centeredCube z' 1 one_pos)).2 i x := by
    intro i
    rw [← hsc _ ((hg i).const_mul (p i))]
    refine integral_congr_ae ?_
    filter_upwards [hw2 i] with x hx
    rw [hx, one_mul]
  have h2 : ∀ i : Fin d,
      (∫ x in (centeredCube z 1 one_pos : Set (SpatialCoordinates d)),
          a1.val x * ((v : SobolevData (centeredCube z 1 one_pos)).2 i x *
            (v : SobolevData (centeredCube z 1 one_pos)).2 i x)) =
        ∫ x in (centeredCube z' 1 one_pos : Set (SpatialCoordinates d)),
          a2.val x * ((w : SobolevData (centeredCube z' 1 one_pos)).2 i x *
            (w : SobolevData (centeredCube z' 1 one_pos)).2 i x) := by
    intro i
    refine (hsc (fun x => a1.val x *
      ((v : SobolevData (centeredCube z 1 one_pos)).2 i x *
        (v : SobolevData (centeredCube z 1 one_pos)).2 i x))
      (ha1.mul ((hg i).mul (hg i)))).symm.trans ?_
    refine integral_congr_ae ?_
    filter_upwards [hw2 i, ha] with x hx hax
    rw [hx, hax, one_mul]
  simp only [h1, h2]

/-- Killed and mean-zero Poincaré on the unit Neumann cube. -/
theorem aux_lem_prefix_limit_atom_extraction_poincareN [NeZero d] :
    (∃ K : ℝ≥0, ∀ u : killedSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (unitNeumannCube d)) u‖) ∧
    (∃ K : ℝ≥0, ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(u : SobolevData (unitNeumannCube d)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) u‖) :=
  exists_killed_meanZero_poincare_of_isOpenBoundedConvexDomain _
    (lane2_isOpenBoundedConvexDomain_centeredCube (aux_lem_prefix_limit_atom_extraction_cN d) one_pos)

/-- The unit-Neumann-cube affine inverse-Neumann response of the zero-infrared coefficient. -/
def aux_lem_prefix_limit_atom_extraction_NzN [NeZero d] [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (u : Fin d → ℝ) (N : ℕ) (om : BilateralField d) : ℝ :=
  affineInverseNeumannResponse aux_lem_prefix_limit_atom_extraction_poincareN.2
    (cutoffPositiveCoefficient M (fun _ => 0) om N (aux_lem_prefix_limit_atom_extraction_cN d)
      one_pos) u

theorem aux_lem_prefix_limit_atom_extraction_cutoff_tau (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (om : BilateralField d) (N : ℕ) (x : SpatialCoordinates d) :
    cutoffCoefficient M (fun _ => 0) (aux_lem_prefix_limit_atom_extraction_tau om) N x =
      cutoffCoefficient M (fun _ => 0) om N (-(aux_lem_prefix_limit_atom_extraction_cN d) + x) := by
  unfold cutoffCoefficient cutoffPotential
  simp only [aux_lem_prefix_limit_atom_extraction_tau_apply, ContinuousMap.zero_apply]

/-- **The translation identity** `N_u(Q₀; A_N^0(ω)) = N_u((0,1)^d; A_N^0(τ ω))`. -/
theorem aux_lem_prefix_limit_atom_extraction_Nz_tau [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (u : Fin d → ℝ) (N : ℕ) (om : BilateralField d) :
    aux_lem_prefix_limit_atom_extraction_Nz M u N om =
      aux_lem_prefix_limit_atom_extraction_NzN M u N (aux_lem_prefix_limit_atom_extraction_tau om) := by
  unfold aux_lem_prefix_limit_atom_extraction_Nz aux_lem_prefix_limit_atom_extraction_N
    aux_lem_prefix_limit_atom_extraction_NzN
  rw [aux_lem_prefix_limit_atom_extraction_coef_eq]
  have hcd : ∀ x : SpatialCoordinates d,
      cubeDilation 0 (aux_lem_prefix_limit_atom_extraction_cN d) 1 x =
        -(aux_lem_prefix_limit_atom_extraction_cN d) + x := by
    intro x; funext i; simp only [cubeDilation_apply, Pi.add_apply, Pi.neg_apply, Pi.zero_apply]; ring
  have hcd' : ∀ y : SpatialCoordinates d,
      -(aux_lem_prefix_limit_atom_extraction_cN d) +
        cubeDilation (aux_lem_prefix_limit_atom_extraction_cN d) 0 1 y = y := by
    intro y; funext i; simp only [cubeDilation_apply, Pi.add_apply, Pi.neg_apply, Pi.zero_apply]; ring
  apply le_antisymm
  · apply aux_lem_prefix_limit_atom_extraction_N_translate_le 0
      (aux_lem_prefix_limit_atom_extraction_cN d)
    have hq := lane4_dilation_quasi_measure_preserving d 0
      (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos one_pos
    filter_upwards [aux_aux_macro_energy_recurrence_coeff_ae M (fun _ => 0)
      (aux_lem_prefix_limit_atom_extraction_tau om) N (aux_lem_prefix_limit_atom_extraction_cN d)
      one_pos, hq.ae (aux_aux_macro_energy_recurrence_coeff_ae M (fun _ => 0) om N 0 one_pos)]
      with x h1 h2
    rw [h1, h2, aux_lem_prefix_limit_atom_extraction_cutoff_tau, hcd]
  · apply aux_lem_prefix_limit_atom_extraction_N_translate_le
      (aux_lem_prefix_limit_atom_extraction_cN d) 0
    have hq := lane4_dilation_quasi_measure_preserving d
      (aux_lem_prefix_limit_atom_extraction_cN d) 0 1 one_pos one_pos
    filter_upwards [aux_aux_macro_energy_recurrence_coeff_ae M (fun _ => 0) om N 0 one_pos,
      hq.ae (aux_aux_macro_energy_recurrence_coeff_ae M (fun _ => 0)
        (aux_lem_prefix_limit_atom_extraction_tau om) N (aux_lem_prefix_limit_atom_extraction_cN d)
        one_pos)] with x h1 h2
    rw [h1, h2, aux_lem_prefix_limit_atom_extraction_cutoff_tau, hcd']

end PaeN0Tr

section PaeN0Inp

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

variable {d : ℕ}

/-- The unit-Neumann-cube zero-infrared potential `Σ_{j ≤ N} ω_{-j} - log κ_N`. -/
def aux_lem_prefix_limit_atom_extraction_potN (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (omega : BilateralField d) :
    Lp ℝ ∞ (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
  compactPotentialLp (closedCube (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos)
    ((∑ j ∈ Finset.range (N + 1), omega (-(j : ℤ))).restrict
        (closedCube (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos) -
      ContinuousMap.const _ (Real.log (aux_lem_prefix_limit_atom_extraction_kappa M N)))

theorem aux_lem_prefix_limit_atom_extraction_cpN_lipschitz :
    LipschitzWith 1 (compactPotentialLp
      (Ω := unitNeumannCube d) (closedCube (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos)) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have hsub : compactPotentialLp (Ω := unitNeumannCube d)
      (closedCube (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos) (f - g) =
      compactPotentialLp (closedCube (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos) f -
        compactPotentialLp (closedCube (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos) g := by
    have hfg : f - g = f + (-1 : ℝ) • g := by rw [neg_one_smul, sub_eq_add_neg]
    rw [hfg, compactPotentialLp_add, compactPotentialLp_smul, neg_one_smul, ← sub_eq_add_neg]
  rw [← hsub]
  exact compactPotentialLp_norm_le _ _

theorem aux_lem_prefix_limit_atom_extraction_potN_continuous
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Continuous (aux_lem_prefix_limit_atom_extraction_potN M N) := by
  unfold aux_lem_prefix_limit_atom_extraction_potN
  refine aux_lem_prefix_limit_atom_extraction_cpN_lipschitz.continuous.comp ?_
  refine Continuous.sub ?_ continuous_const
  refine (ContinuousMap.continuous_restrict _).comp ?_
  exact continuous_finset_sum _ fun j _ => continuous_apply _

theorem aux_lem_prefix_limit_atom_extraction_potN_ae (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (n : ℕ) (om : BilateralField d) :
    ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      aux_lem_prefix_limit_atom_extraction_potN M n om x =
        (∑ j ∈ Finset.range (n + 1), om (-(j : ℤ)) x) -
          Real.log (aux_lem_prefix_limit_atom_extraction_kappa M n) := by
  have h := compactPotentialLp_on_domain (Ω := unitNeumannCube d)
    (closedCube (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos)
    (centeredCube_subset_closedCube (aux_lem_prefix_limit_atom_extraction_cN d) one_pos)
    ((∑ j ∈ Finset.range (n + 1), om (-(j : ℤ))).restrict
        (closedCube (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos) -
      ContinuousMap.const _ (Real.log (aux_lem_prefix_limit_atom_extraction_kappa M n)))
  filter_upwards [h, ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet] with x hx hmem
  unfold aux_lem_prefix_limit_atom_extraction_potN
  rw [hx hmem]
  show (∑ j ∈ Finset.range (n + 1), om (-(j : ℤ))) x -
      Real.log (aux_lem_prefix_limit_atom_extraction_kappa M n) = _
  rw [ContinuousMap.sum_apply]

/-- `e^{potN} = A_N^0` on the unit Neumann cube. -/
theorem aux_lem_prefix_limit_atom_extraction_coefN_eq (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (om : BilateralField d) :
    expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N om) =
      cutoffPositiveCoefficient M (fun _ => 0) om N (aux_lem_prefix_limit_atom_extraction_cN d)
        one_pos := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [expPotentialCoefficient_coeFn (aux_lem_prefix_limit_atom_extraction_potN M N om),
    aux_lem_prefix_limit_atom_extraction_potN_ae M N om,
    aux_aux_macro_energy_recurrence_coeff_ae M (fun _ => 0) om N
      (aux_lem_prefix_limit_atom_extraction_cN d) one_pos] with x h1 h2 h3
  have hraw : Real.exp (∑ j ∈ Finset.range (N + 1), (om (-(j : ℤ))) x -
      Real.log (aux_lem_prefix_limit_atom_extraction_kappa M N)) =
      cutoffCoefficient M (fun _ => 0) om N x := by
    rw [aux_lem_prefix_limit_atom_extraction_log_kappa]
    unfold cutoffCoefficient cutoffPotential
    simp only [ContinuousMap.zero_apply, zero_add, Int.ofNat_eq_natCast]
    have ha := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
    rw [show ∀ S A B : ℝ, S - (A + B) = (S - A) + -B from fun S A B => by ring,
      Real.exp_add, Real.exp_neg, Real.exp_log ha, mul_comm]
  simpa only [Int.ofNat_eq_natCast] using!
    h1.trans ((congrArg Real.exp h2).trans (hraw.trans h3.symm))

/-- A smooth unit-mass bump supported in `(1,2)`. -/
theorem aux_lem_prefix_limit_atom_extraction_bump :
    ∃ rho : ℝ → ℝ, ContDiff ℝ ∞ rho ∧ (∀ tau, 0 ≤ rho tau) ∧
      (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) ∧ (∫ tau, rho tau) = 1 ∧
      Continuous rho ∧ ∃ Mρ : ℝ, 0 ≤ Mρ ∧ ∀ tau, |rho tau| ≤ Mρ := by
  let f : ContDiffBump (3 / 2 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let rho : ℝ → ℝ := f.normed volume
  have hcont : Continuous rho := f.continuous_normed
  have hsupp : ∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0 := by
    intro tau htau
    have hball : Metric.ball (3 / 2 : ℝ) f.rOut = Set.Ioo 1 2 := by
      rw [Real.ball_eq_Ioo]
      norm_num [f]
    by_contra hne
    have hmem : tau ∈ Function.support rho := hne
    rw [show Function.support rho = Metric.ball (3 / 2 : ℝ) f.rOut from
      f.support_normed_eq, hball] at hmem
    exact htau hmem
  have hcs : HasCompactSupport rho := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) ?_
    intro tau htau
    exact hsupp tau (fun h => htau ⟨h.1.le, h.2.le⟩)
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hcs
  refine ⟨rho, f.contDiff_normed (n := ⊤), fun tau => f.nonneg_normed tau, hsupp,
    f.integral_normed, hcont, max M 0, le_max_right _ _, fun tau => ?_⟩
  rw [← Real.norm_eq_abs]
  exact (hM tau).trans (le_max_left _ _)

/-- The coefficient form against a weak test equals the form against its mean-zero part. -/
theorem aux_lem_prefix_limit_atom_extraction_form_meanZeroRep
    (hP : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖)
    (hΩ : Bornology.IsBounded (unitNeumannCube d : Set (SpatialCoordinates d)))
    (hvol : volume.real (unitNeumannCube d : Set (SpatialCoordinates d)) ≠ 0)
    (a : PositiveCoefficient (unitNeumannCube d)) (v : (meanZeroResponseSpace hP).space)
    (ψ : weakSobolevGraph (unitNeumannCube d)) :
    sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
        (ψ : SobolevData (unitNeumannCube d)) =
      responseForm (meanZeroResponseSpace hP) a v (meanZeroSobolevRepresentative hΩ hvol ψ) := by
  have hgrad := meanZeroSobolevRepresentative_gradient hΩ hvol ψ
  have h1 : sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
      (ψ : SobolevData (unitNeumannCube d)) =
      weightedGradientForm a.val (sobolevGradient (v : SobolevData (unitNeumannCube d)))
        (sobolevGradient (ψ : SobolevData (unitNeumannCube d))) := rfl
  have h2 : responseForm (meanZeroResponseSpace hP) a v (meanZeroSobolevRepresentative hΩ hvol ψ) =
      weightedGradientForm a.val (sobolevGradient (v : SobolevData (unitNeumannCube d)))
        (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d))
          (meanZeroSobolevRepresentative hΩ hvol ψ)) := rfl
  rw [h1, h2, hgrad]

/-- The volume load against the mean-zero part of a test, for a mean-zero source. -/
theorem aux_lem_prefix_limit_atom_extraction_load_meanZeroRep
    (hΩ : Bornology.IsBounded (unitNeumannCube d : Set (SpatialCoordinates d)))
    (hvol : volume.real (unitNeumannCube d : Set (SpatialCoordinates d)) ≠ 0)
    (f : SpatialCoordinates d → ℝ) (fL2 : DomainL2 (unitNeumannCube d))
    (hf : ((fL2 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] f))
    (hf0 : (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x) = 0)
    (ψ : weakSobolevGraph (unitNeumannCube d)) :
    sobolevVolumeLoad fL2 ((meanZeroSobolevRepresentative hΩ hvol ψ :
        meanZeroSobolevGraph (unitNeumannCube d)) : SobolevData (unitNeumannCube d)) =
      ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x * (ψ : SobolevData (unitNeumannCube d)).1 x := by
  rw [sobolevVolumeLoad_apply]
  have hc := meanZeroSobolevRepresentative_coeFn hΩ hvol ψ
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)),
      ψ.val.1 y) / volume.real (unitNeumannCube d : Set (SpatialCoordinates d)) := ⟨_, rfl⟩
  rw [← hcdef] at hc
  have hfint : Integrable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) :=
    ((Lp.memLp fL2).integrable (by norm_num)).congr hf
  have hprod : Integrable (fun x => f x * ψ.val.1 x)
      (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) := by
    have h := (L2.integrable_inner (𝕜 := ℝ) fL2 ψ.val.1)
    refine h.congr ?_
    filter_upwards [hf] with x hx
    rw [real_inner_eq_re_inner, RCLike.re_to_real, real_inner_comm, hx]
    simp
  calc (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)),
        fL2 x * ((meanZeroSobolevRepresentative hΩ hvol ψ :
          meanZeroSobolevGraph (unitNeumannCube d)) : SobolevData (unitNeumannCube d)).1 x)
      = ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x * ψ.val.1 x - c * f x := by
        refine integral_congr_ae ?_
        filter_upwards [hf, hc] with x h1 h2
        rw [h1, h2]; ring
    _ = (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x * ψ.val.1 x) -
          c * ∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x := by
        rw [integral_sub hprod (hfint.const_mul c), integral_const_mul]
    _ = _ := by rw [hf0, mul_zero, sub_zero]

/-- The mean-zero solution of a mean-zero volume load solves the weak Neumann problem. -/
theorem aux_lem_prefix_limit_atom_extraction_solvesN
    (hP : ∃ K : ℝ≥0, ∀ w : meanZeroSobolevGraph (unitNeumannCube d),
      ‖(w : SobolevData (unitNeumannCube d)).1‖ ≤
        K * ‖subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)) w‖)
    (a : PositiveCoefficient (unitNeumannCube d)) (f : SpatialCoordinates d → ℝ)
    (fL2 : DomainL2 (unitNeumannCube d))
    (hf : ((fL2 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] f))
    (hf0 : (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), f x) = 0) :
    SolvesNeumann a f (responseSolution (meanZeroResponseSpace hP) a
      ((sobolevVolumeLoad fL2).comp (meanZeroResponseSpace hP).space.subtypeL)) := by
  intro ψ
  have hΩ : Bornology.IsBounded (unitNeumannCube d : Set (SpatialCoordinates d)) := by
    unfold unitNeumannCube; exact centeredCube_isBounded _ one_pos
  have hvol : volume.real (unitNeumannCube d : Set (SpatialCoordinates d)) ≠ 0 := by
    unfold unitNeumannCube; exact (centeredCube_volume_pos _ one_pos).ne'
  let S := meanZeroResponseSpace hP
  let L := (sobolevVolumeLoad fL2).comp S.space.subtypeL
  have hrep := aux_lem_prefix_limit_atom_extraction_form_meanZeroRep hP hΩ hvol a
    (responseSolution S a L) ψ
  have hspec := responseSolution_spec S a L (meanZeroSobolevRepresentative hΩ hvol ψ)
  have hload := aux_lem_prefix_limit_atom_extraction_load_meanZeroRep hΩ hvol f fL2 hf hf0 ψ
  simpa only [S, L] using! hrep.trans (hspec.trans hload)

/-- `A_N ≤ e^{S} A_N^0` on the closed Neumann cube when `|H| ≤ S` there. -/
theorem aux_lem_prefix_limit_atom_extraction_cutoff_H_le
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om : BilateralField d) (N : ℕ) (S : ℝ)
    (hS : ∀ x ∈ (closedCube (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos :
      Set (SpatialCoordinates d)), |H om x| ≤ S) :
    ∀ᵐ x ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
      (cutoffPositiveCoefficient M H om N (aux_lem_prefix_limit_atom_extraction_cN d) one_pos).val x ≤
        Real.exp S * (cutoffPositiveCoefficient M (fun _ => 0) om N
          (aux_lem_prefix_limit_atom_extraction_cN d) one_pos).val x := by
  filter_upwards [aux_aux_macro_energy_recurrence_coeff_ae M H om N
      (aux_lem_prefix_limit_atom_extraction_cN d) one_pos,
    aux_aux_macro_energy_recurrence_coeff_ae M (fun _ => 0) om N
      (aux_lem_prefix_limit_atom_extraction_cN d) one_pos,
    ae_restrict_mem (unitNeumannCube d).isOpen.measurableSet] with x h1 h2 hx
  rw [h1, h2, aux_lem_prefix_limit_atom_extraction_cutoff_zero_eq M H om N x, mul_comm (Real.exp S),
    mul_assoc]
  have hpos := cutoffCoefficient_pos M H om N x
  refine le_mul_of_one_le_right hpos.le ?_
  rw [← Real.exp_add]
  apply Real.one_le_exp
  have := hS x (centeredCube_subset_closedCube _ one_pos hx)
  linarith [le_abs_self (H om x)]

/-- **Coarse coercivity of `A_N^0`** on the unit Neumann cube, pointwise in the sample, with
moments uniform in the cutoff (from `lem_coercivity` for an infrared field and `A_N ≤ e^{S} A_N^0`). -/
theorem aux_lem_prefix_limit_atom_extraction_coerc0N (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (Sf : SobolevFoundationalInput d hd) :
    ∃ delta0 : ℝ → ℝ, (∀ p : ℝ, 1 ≤ p → 0 < delta0 p) ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (_Rm : in_responses d M),
        ∃ Kc : ℕ → BilateralField d → ℝ, (∀ N om, 0 ≤ Kc N om) ∧
          (∀ N om, ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
            cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
                (v : SobolevData (unitNeumannCube d)).1 ≤
              Kc N om * sobolevCoefficientForm
                (cutoffPositiveCoefficient M (fun _ => 0) om N
                  (aux_lem_prefix_limit_atom_extraction_cN d) one_pos)
                (v : SobolevData (unitNeumannCube d)) (v : SobolevData (unitNeumannCube d))) ∧
          (∀ p : ℝ, 1 ≤ p → M.delta ≤ delta0 p → ∃ C : ℝ, 0 ≤ C ∧ ∀ N,
            MemLp (Kc N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ∧
            eLpNorm (Kc N) (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal C) := by
  have hco := aux_lem_coercivity_compat d hd E P Sf
  obtain ⟨dc, hdc, hcoe⟩ := hco
  refine ⟨fun p => dc (2 * p), fun p hp => hdc (2 * p) (by linarith), ?_⟩
  intro M Rm
  obtain ⟨H, hH⟩ := exists_infraredCharacterization hd M
  have hK := hcoe M Rm H hH (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos le_rfl
  obtain ⟨K, hKco, hKmom⟩ := hK
  set K1 : Compacts (SpatialCoordinates d) :=
    closedCube (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos
  obtain ⟨Sx, hSx⟩ : ∃ Sx : BilateralField d → ℝ,
      Sx = fun om => ‖(H om).restrict (K1 : Set (SpatialCoordinates d))‖ := ⟨_, rfl⟩
  refine ⟨fun N om => Real.exp (Sx om) * max (K N om) 0,
    fun N om => mul_nonneg (Real.exp_pos _).le (le_max_right _ _), ?_, ?_⟩
  · intro N om v
    have h1 := ((hKco N om).2 v).2
    have hform0 := sobolevCoefficientForm_nonneg
      (cutoffPositiveCoefficient M H om N (aux_lem_prefix_limit_atom_extraction_cN d) one_pos)
      (v : SobolevData (unitNeumannCube d))
    have hle := weightedGradientForm_le_mul
      (cutoffPositiveCoefficient M H om N (aux_lem_prefix_limit_atom_extraction_cN d) one_pos)
      (cutoffPositiveCoefficient M (fun _ => 0) om N (aux_lem_prefix_limit_atom_extraction_cN d)
        one_pos) (Real.exp (Sx om))
      (aux_lem_prefix_limit_atom_extraction_cutoff_H_le M H om N (Sx om) (by
        intro x hx
        rw [hSx]
        exact aux_lem_prefix_limit_atom_extraction_restrict_bound (H om) K1 x hx))
      (sobolevGradient (v : SobolevData (unitNeumannCube d)))
    show _ ≤ (Real.exp (Sx om) * max (K N om) 0) * weightedGradientForm _ _ _
    change _ ≤ _ * weightedGradientForm _ _ _ at h1
    change weightedGradientForm _ _ _ ≤ _ * weightedGradientForm _ _ _ at hle
    change 0 ≤ weightedGradientForm _ _ _ at hform0
    calc _ ≤ K N om * _ := h1
      _ ≤ max (K N om) 0 * _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hform0
      _ ≤ max (K N om) 0 * (Real.exp (Sx om) * _) :=
          mul_le_mul_of_nonneg_left hle (le_max_right _ _)
      _ = _ := by ring_nf; try rfl
  · intro p hp hδ
    obtain ⟨Cb, hCbmem, hCbnorm⟩ := hKmom (2 * p) (by linarith) hδ
    have hEmem : MemLp (fun om => Real.exp (Sx om)) (ENNReal.ofReal (2 * p))
        (chaosSampleLaw M).toMeasure := by
      rw [hSx]
      exact aux_lem_prefix_limit_atom_extraction_expSup_memLp hd M H hH K1 (2 * p) (by linarith)
    have hmaxmem : ∀ N, MemLp (fun om => max (K N om) 0) (ENNReal.ofReal (2 * p))
        (chaosSampleLaw M).toMeasure := fun N => (hCbmem N).pos_part
    have hmaxle : ∀ N, eLpNorm (fun om => max (K N om) 0) (ENNReal.ofReal (2 * p))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Cb := by
      intro N
      refine le_trans (eLpNorm_mono (hmaxmem N).aestronglyMeasurable fun om => ?_) (hCbnorm N)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _)
    obtain ⟨CE0, hCE0⟩ : ∃ CE0 : ℝ, CE0 = (eLpNorm (fun om => Real.exp (Sx om))
        (ENNReal.ofReal (2 * p)) (chaosSampleLaw M).toMeasure).toReal := ⟨_, rfl⟩
    have hCE0nn : 0 ≤ CE0 := by rw [hCE0]; exact ENNReal.toReal_nonneg
    have hCb0 : 0 ≤ max Cb 0 := le_max_right _ _
    refine ⟨CE0 * max Cb 0, mul_nonneg hCE0nn hCb0, fun N => ?_⟩
    have hp0 : 0 < p := by linarith
    have hb := aux_rem_resolved_microscopic_product_lq_bound (chaosSampleLaw M).toMeasure p
      (2 * p) hp0 le_rfl _ _ hEmem (hmaxmem N)
    refine ⟨lt_of_le_of_lt hb (ENNReal.mul_lt_top hEmem.eLpNorm_lt_top
      (hmaxmem N).eLpNorm_lt_top), hb.trans ?_⟩
    rw [ENNReal.ofReal_mul hCE0nn]
    gcongr
    · rw [hCE0, ENNReal.ofReal_toReal hEmem.eLpNorm_lt_top.ne]
    · exact (hmaxle N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))

end PaeN0Inp

section PaeN0Main

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
open SubdiffusiveProcess.Lane4

variable {d : ℕ}

/-- The smoothed Neumann response of `A_N^0` on the unit Neumann cube for the load `L`. -/
def aux_lem_prefix_limit_atom_extraction_YN [NeZero d] (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space
      →L[ℝ] ℝ) (N : ℕ) (om : BilateralField d) : ℝ :=
  inverseResponse (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2)
    (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N om)) L

theorem aux_lem_prefix_limit_atom_extraction_YN_continuous [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space
      →L[ℝ] ℝ) (N : ℕ) :
    Continuous (aux_lem_prefix_limit_atom_extraction_YN M L N) :=
  (continuous_inverseResponse_potential _ _).comp
    (aux_lem_prefix_limit_atom_extraction_potN_continuous M N)

theorem aux_lem_prefix_limit_atom_extraction_NzN_eq [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (u : Fin d → ℝ) (N : ℕ) (om : BilateralField d) :
    aux_lem_prefix_limit_atom_extraction_NzN M u N om =
      aux_lem_prefix_limit_atom_extraction_YN M
        ((affineNeumannLoad u).comp (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d))))
        N om := by
  unfold aux_lem_prefix_limit_atom_extraction_NzN aux_lem_prefix_limit_atom_extraction_YN
    affineInverseNeumannResponse
  rw [aux_lem_prefix_limit_atom_extraction_coefN_eq]

theorem aux_lem_prefix_limit_atom_extraction_NzN_continuous [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (u : Fin d → ℝ) (N : ℕ) :
    Continuous (aux_lem_prefix_limit_atom_extraction_NzN M u N) := by
  have h : aux_lem_prefix_limit_atom_extraction_NzN M u N =
      aux_lem_prefix_limit_atom_extraction_YN M
        ((affineNeumannLoad u).comp (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d))))
        N := funext fun om => aux_lem_prefix_limit_atom_extraction_NzN_eq M u N om
  rw [h]
  exact aux_lem_prefix_limit_atom_extraction_YN_continuous M _ N

/-- The face-bump loads on the mean-zero space of the unit Neumann cube. -/
def aux_lem_prefix_limit_atom_extraction_Lf [NeZero d] (fL2 : ℝ → DomainL2 (unitNeumannCube d))
    (eps : ℝ) :
    (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space
      →L[ℝ] ℝ :=
  (sobolevVolumeLoad (fL2 eps)).comp
    (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space.subtypeL

theorem aux_lem_prefix_limit_atom_extraction_growth_arith (K Yv F Cr e2 R : ℝ) (hK : 0 ≤ K)
    (hF : F ≤ Yv) (hF0 : 0 ≤ F) (he2 : 1 ≤ e2) (hR : 0 ≤ R) (hC : 0 ≤ Cr) :
    K * (F + Cr * e2) * R ≤ K * (Yv + Cr) * e2 * R := by
  have hY0 : 0 ≤ Yv := hF0.trans hF
  have h1 : F + Cr * e2 ≤ (Yv + Cr) * e2 := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 hK
  have h3 := mul_le_mul_of_nonneg_right h2 hR
  calc K * (F + Cr * e2) * R ≤ K * ((Yv + Cr) * e2) * R := h3
    _ = K * (Yv + Cr) * e2 * R := by ring

/-- The growth clause at one sample (from the face-bump clause of `resolved0`). -/
theorem aux_lem_prefix_limit_atom_extraction_neumann_growth_sample [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (om : BilateralField d) (N : ℕ)
    (a : PositiveCoefficient (unitNeumannCube d))
    (ha : a = cutoffPositiveCoefficient M (fun _ => 0) om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
    (p : Fin d → ℝ) (hp : ∑ i : Fin d, (p i) ^ 2 = 1) (t : ℝ)
    (rho : ℝ → ℝ) (Cρ : ℝ)
    (fL2 : ℝ → DomainL2 (unitNeumannCube d))
    (hfL2 : ∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ((fL2 eps : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] faceBump rho p eps))
    (hmean : ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
      (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), faceBump rho p eps x) = 0)
    (Kr Y : ℝ) (hKr : 0 ≤ Kr) (hC : 0 ≤ Cρ)
    (eps : ℝ) (heps : 0 < eps) (heps8 : eps < 1 / 8)
    (hY : inverseResponse (meanZeroResponseSpace
        (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2) a
        (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps) ≤ Y)
    (hres : ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
        SolvesNeumann a (faceBump rho p eps) v →
        ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
        ∀ r : ℝ, 0 < r → r ≤ 1 →
          localGradientEnergy a
            (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
            (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
            (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
            Kr * (sobolevCoefficientForm a
              (v : SobolevData (unitNeumannCube d)) (v : SobolevData (unitNeumannCube d)) +
              Cρ ^ 2 * eps ^ (-2 : ℝ)) * r ^ t)
    (x : SpatialCoordinates d) (hx : x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)))
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    localGradientEnergy a (s := Metric.ball x r) Metric.isOpen_ball.measurableSet
        (subspaceGradient (meanZeroResponseSpace
            (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space
          (responseSolution (meanZeroResponseSpace
            (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2) a
            (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps))) ≤
      Kr * (Y + Cρ ^ 2) * eps ^ (-2 : ℝ) * r ^ t := by
  have hsol := aux_lem_prefix_limit_atom_extraction_solvesN
    (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2 a
    (faceBump rho p eps) (fL2 eps) (hfL2 eps heps heps8) (hmean eps heps heps8)
  have h := hres _ hsol x hx r hr hr1
  rw [← aux_lem_prefix_limit_atom_extraction_lge_inter _ Metric.isOpen_ball.measurableSet
    (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)]
  refine h.trans ?_
  have he1 : eps ≤ 1 := le_of_lt (lt_trans heps8 (by norm_num))
  have he2 : 1 ≤ eps ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos heps he1 (by norm_num)
  exact aux_lem_prefix_limit_atom_extraction_growth_arith Kr Y _ (Cρ ^ 2)
    (eps ^ (-2 : ℝ)) (r ^ t) hKr hY (sobolevCoefficientForm_nonneg _ _) he2
    (Real.rpow_nonneg hr.le _) (sq_nonneg _)

theorem aux_lem_prefix_limit_atom_extraction_YN_eq [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space
      →L[ℝ] ℝ) (N : ℕ) (om : BilateralField d) :
    aux_lem_prefix_limit_atom_extraction_YN M L N om =
      inverseResponse (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2)
        (cutoffPositiveCoefficient M (fun _ => 0) om N (aux_lem_prefix_limit_atom_extraction_cN d)
          one_pos) L := by
  unfold aux_lem_prefix_limit_atom_extraction_YN
  rw [aux_lem_prefix_limit_atom_extraction_coefN_eq]

/-- A nonnegative function dominated by `c` times an `L^r` function is in `L^r` with the
scaled bound. -/
theorem aux_lem_prefix_limit_atom_extraction_dom_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f g : Ω → ℝ) (c r B : ℝ) (hc : 0 ≤ c)
    (hfm : AEStronglyMeasurable f P) (hf0 : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ c * g x)
    (hg : MemLp g (ENNReal.ofReal r) P) (hgB : eLpNorm g (ENNReal.ofReal r) P ≤ ENNReal.ofReal B) :
    MemLp f (ENNReal.ofReal r) P ∧ eLpNorm f (ENNReal.ofReal r) P ≤ ENNReal.ofReal (c * B) := by
  have hle : ∀ x, ‖f x‖ ≤ ‖c * g x‖ := by
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf0 x),
      abs_of_nonneg ((hf0 x).trans (hfg x))]
    exact hfg x
  refine ⟨(hg.const_mul c).of_le hfm (Filter.Eventually.of_forall hle), ?_⟩
  calc eLpNorm f (ENNReal.ofReal r) P ≤ eLpNorm (fun x => c * g x) (ENNReal.ofReal r) P :=
        eLpNorm_mono hfm hle
    _ = ENNReal.ofReal c * eLpNorm g (ENNReal.ofReal r) P := by
        rw [show (fun x => c * g x) = c • g from rfl, eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal B := by gcongr
    _ = ENNReal.ofReal (c * B) := (ENNReal.ofReal_mul hc).symm

/-- **Smoothing error and smoothed-response moments** (paper `eq:mfd-9`) for `A_N^0` on the unit
Neumann cube, from the pointwise coercivity constant `K^c`. -/
theorem aux_lem_prefix_limit_atom_extraction_neumann_smoothing [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (p : Fin d → ℝ) (hp : ∑ i : Fin d, (p i) ^ 2 = 1)
    (q : ℝ) (hq : 1 ≤ q)
    (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho) (hrho0 : ∀ tau, 0 ≤ rho tau)
    (hsupp : ∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) (hint : (∫ tau, rho tau) = 1)
    (fL2 : ℝ → DomainL2 (unitNeumannCube d))
    (hfL2 : ∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ((fL2 eps : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] faceBump rho p eps))
    (Cload : ℝ) (hCload : 0 < Cload) (hLB : aux_lem_neumann_error_load_type d hd Cload)
    (Cy : ℝ) (hCy0 : 0 ≤ Cy)
    (hCy : ∀ (a : PositiveCoefficient (unitNeumannCube d)) (K : ℝ), 0 ≤ K →
      (∀ v : meanZeroSobolevGraph (unitNeumannCube d),
        cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
            (v : SobolevData (unitNeumannCube d)).1 ≤
          K * sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
            (v : SobolevData (unitNeumannCube d))) →
      inverseResponse (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2) a
          ((affineNeumannLoad p).comp
            (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) ≤ Cy * K ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ∀ f0 : DomainL2 (unitNeumannCube d),
        ((f0 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
            faceBump rho p eps) →
        inverseResponse (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2) a
          ((sobolevVolumeLoad f0).comp
            (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space.subtypeL) ≤
            Cy * K)
    (Kc : ℕ → BilateralField d → ℝ) (hKc0 : ∀ N om, 0 ≤ Kc N om)
    (hKcCo : ∀ N om, ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
      cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
          (v : SobolevData (unitNeumannCube d)).1 ≤
        Kc N om * sobolevCoefficientForm
          (cutoffPositiveCoefficient M (fun _ => 0) om N
            (aux_lem_prefix_limit_atom_extraction_cN d) one_pos)
          (v : SobolevData (unitNeumannCube d)) (v : SobolevData (unitNeumannCube d)))
    (Cc : ℝ) (hCc : 0 ≤ Cc)
    (hKcMem : ∀ N, MemLp (Kc N) (ENNReal.ofReal (4 * q)) (chaosSampleLaw M).toMeasure)
    (hKcBd : ∀ N, eLpNorm (Kc N) (ENNReal.ofReal (4 * q)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal Cc) :
    ∃ Bs : ℝ, 0 ≤ Bs ∧ ∀ (N : ℕ) (eps : ℝ), 0 < eps → eps < 1 / 8 →
      (MemLp (aux_lem_prefix_limit_atom_extraction_YN M
          (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps) N) (ENNReal.ofReal q)
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (aux_lem_prefix_limit_atom_extraction_YN M
          (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps) N) (ENNReal.ofReal q)
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Bs) ∧
      eLpNorm (fun om => aux_lem_prefix_limit_atom_extraction_NzN M p N om -
          aux_lem_prefix_limit_atom_extraction_YN M
            (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps) N om) 1
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Bs * eps ^ (1 / 4 : ℝ)) := by
  have hq0 : 0 < q := by linarith
  have hass := lem_neumann_error_moment_assembly q Cc (Cy * Cc) (8 * Cload) hq hCc
    (mul_nonneg hCy0 hCc) (by positivity)
  obtain ⟨Cerr, Cunif, hCerr, hCunif, hA⟩ := hass
  refine ⟨max Cerr Cunif, le_max_of_le_left hCerr.le, ?_⟩
  intro N eps heps heps8
  let P := (chaosSampleLaw M).toMeasure
  -- the pointwise facts
  have hN_eq : ∀ om, aux_lem_prefix_limit_atom_extraction_NzN M p N om =
      inverseResponse (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2)
        (cutoffPositiveCoefficient M (fun _ => 0) om N (aux_lem_prefix_limit_atom_extraction_cN d) one_pos)
        ((affineNeumannLoad p).comp (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) :=
    fun om => rfl
  have hpt : ∀ om, _ := fun om => aux_lem_neumann_error_pointwise hd
    (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2
    (cutoffPositiveCoefficient M (fun _ => 0) om N (aux_lem_prefix_limit_atom_extraction_cN d) one_pos)
    (Kc N om) Cload eps
    ((affineNeumannLoad p).comp (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d))))
    (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps) hCload heps heps8 (hKcCo N om)
    (fun z => hLB rho hrho hrho0 hsupp hint p hp eps heps heps8 (fun _ _ => fL2 eps)
      (fun _ _ => hfL2 eps heps heps8) 0 (fun _ => 0) z)
  have hNle : ∀ om, aux_lem_prefix_limit_atom_extraction_NzN M p N om ≤ Cy * Kc N om := fun om =>
    (hCy _ (Kc N om) (hKc0 N om) (hKcCo N om)).1
  have hN0 : ∀ om, 0 ≤ aux_lem_prefix_limit_atom_extraction_NzN M p N om := fun om =>
    inverseResponse_nonneg _ _ _
  have hY0 : ∀ om, 0 ≤ aux_lem_prefix_limit_atom_extraction_YN M
      (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps) N om := fun om => inverseResponse_nonneg _ _ _
  have hNm : AEStronglyMeasurable (aux_lem_prefix_limit_atom_extraction_NzN M p N) P :=
    (aux_lem_prefix_limit_atom_extraction_NzN_continuous M p N).measurable.aestronglyMeasurable
  have hYm : AEStronglyMeasurable (aux_lem_prefix_limit_atom_extraction_YN M
      (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps) N) P :=
    (aux_lem_prefix_limit_atom_extraction_YN_continuous M _ N).measurable.aestronglyMeasurable
  obtain ⟨hNmem, hNbd⟩ := aux_lem_prefix_limit_atom_extraction_dom_moment P _ (Kc N) Cy (4 * q) Cc
    hCy0 hNm hN0 hNle (hKcMem N) (hKcBd N)
  have hD : ∀ om, |aux_lem_prefix_limit_atom_extraction_NzN M p N om -
      aux_lem_prefix_limit_atom_extraction_YN M (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps) N om| ≤
      (8 * Cload) * eps ^ (1 / 4 : ℝ) * Real.sqrt (Kc N om) *
          Real.sqrt (aux_lem_prefix_limit_atom_extraction_NzN M p N om) +
        (8 * Cload) ^ 2 * eps ^ (1 / 2 : ℝ) * Kc N om := by
    intro om
    rw [aux_lem_prefix_limit_atom_extraction_YN_eq, hN_eq]
    exact (hpt om).2.2.1
  have hV : ∀ om, aux_lem_prefix_limit_atom_extraction_YN M
      (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps) N om ≤
      2 * aux_lem_prefix_limit_atom_extraction_NzN M p N om +
        2 * (8 * Cload) ^ 2 * eps ^ (1 / 2 : ℝ) * Kc N om := by
    intro om
    rw [aux_lem_prefix_limit_atom_extraction_YN_eq, hN_eq]
    exact (hpt om).2.2.2
  have hres := hA (BilateralField d) P eps heps heps8 (Kc N) (aux_lem_prefix_limit_atom_extraction_NzN M p N)
    (aux_lem_prefix_limit_atom_extraction_YN M (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps) N)
    (fun om => aux_lem_prefix_limit_atom_extraction_NzN M p N om -
      aux_lem_prefix_limit_atom_extraction_YN M (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps) N om)
    (hKc0 N) hN0 hY0 hD hV (hNm.sub hYm) hYm (hKcMem N) (hKcBd N) hNmem hNbd
  obtain ⟨hDq, hVq⟩ := hres
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
  refine ⟨⟨lt_of_le_of_lt hVq ENNReal.ofReal_lt_top,
    hVq.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩, ?_⟩
  refine (eLpNorm_le_eLpNorm_of_exponent_le hq1).trans (hDq.trans ?_)
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg heps.le _))


theorem aux_lem_prefix_limit_atom_extraction_growth_mono (K V e R : ℝ) (hK : 0 ≤ K) (he : 0 ≤ e)
    (hR : 0 ≤ R) : K * V * e * R ≤ K * (1 + V) * e * R := by
  have h1 : K * V ≤ K * (1 + V) := mul_le_mul_of_nonneg_left (by linarith) hK
  have h2 := mul_le_mul_of_nonneg_right h1 he
  exact mul_le_mul_of_nonneg_right h2 hR

/-- Moments of the Neumann growth constant `K^{res}(1 + C_y K^c + C_ρ²)`. -/
theorem aux_lem_prefix_limit_atom_extraction_neumann_Kmom {Ω : Type*} [MeasurableSpace Ω]
    (Pm : Measure Ω) [IsProbabilityMeasure Pm] (q Cr Cc Cy Cρ : ℝ) (hq : 1 ≤ q) (hCc : 0 ≤ Cc)
    (hCy0 : 0 ≤ Cy) (Kres Kc : ℕ → Ω → ℝ)
    (hKmem : ∀ N, MemLp (Kres N) (ENNReal.ofReal (2 * q)) Pm)
    (hKbd : ∀ N, eLpNorm (Kres N) (ENNReal.ofReal (2 * q)) Pm ≤ ENNReal.ofReal Cr)
    (hKcMem : ∀ N, MemLp (Kc N) (ENNReal.ofReal (4 * q)) Pm)
    (hKcBd : ∀ N, eLpNorm (Kc N) (ENNReal.ofReal (4 * q)) Pm ≤ ENNReal.ofReal Cc) :
    ∃ Bk : ℝ, 0 ≤ Bk ∧ ∀ N,
      MemLp (fun om => Kres N om * (1 + (Cy * Kc N om + Cρ ^ 2))) (ENNReal.ofReal q) Pm ∧
      eLpNorm (fun om => Kres N om * (1 + (Cy * Kc N om + Cρ ^ 2))) (ENNReal.ofReal q) Pm ≤
        ENNReal.ofReal Bk := by
  have hex : ∃ Cp : ℝ, Cp = max Cr (Cy * Cc + Cρ ^ 2) := ⟨_, rfl⟩
  obtain ⟨Cp, hCpdef⟩ := hex
  have hsq : 0 ≤ Cρ ^ 2 := sq_nonneg _
  have hCyCc : 0 ≤ Cy * Cc := mul_nonneg hCy0 hCc
  have hCp0 : 0 ≤ Cp := by rw [hCpdef]; exact le_max_of_le_right (add_nonneg hCyCc hsq)
  have hq2 : 2 * q ≤ 4 * q := by linarith
  have hle2 : ENNReal.ofReal (2 * q) ≤ ENNReal.ofReal (4 * q) := ENNReal.ofReal_le_ofReal hq2
  have hVmem : ∀ N, MemLp (fun om => Cy * Kc N om + Cρ ^ 2) (ENNReal.ofReal (2 * q)) Pm := fun N =>
    (((hKcMem N).mono_exponent hle2).const_mul Cy).add (memLp_const _)
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * q) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hVbd : ∀ N, eLpNorm (fun om => Cy * Kc N om + Cρ ^ 2) (ENNReal.ofReal (2 * q)) Pm ≤
      ENNReal.ofReal Cp := by
    intro N
    have hKc2 : eLpNorm (Kc N) (ENNReal.ofReal (2 * q)) Pm ≤ ENNReal.ofReal Cc :=
      (eLpNorm_le_eLpNorm_of_exponent_le hle2).trans (hKcBd N)
    have hfun : (fun om => Cy * Kc N om + Cρ ^ 2) =
        (fun om => Cy * Kc N om) + (fun _ : Ω => Cρ ^ 2) := rfl
    calc eLpNorm (fun om => Cy * Kc N om + Cρ ^ 2) (ENNReal.ofReal (2 * q)) Pm
        ≤ eLpNorm (fun om => Cy * Kc N om) (ENNReal.ofReal (2 * q)) Pm +
            eLpNorm (fun _ : Ω => Cρ ^ 2) (ENNReal.ofReal (2 * q)) Pm := by
          rw [hfun]
          exact eLpNorm_add_le (f := fun om => Cy * Kc N om) (g := fun _ : Ω => Cρ ^ 2)
            h1
      _ ≤ ENNReal.ofReal (Cy * Cc) + ENNReal.ofReal (Cρ ^ 2) := by
          gcongr
          · rw [show (fun om => Cy * Kc N om) = Cy • Kc N from rfl, eLpNorm_const_smul,
              Real.enorm_eq_ofReal hCy0, ENNReal.ofReal_mul hCy0]
            gcongr
          · have h := eLpNorm_le_of_ae_bound (μ := Pm) (p := ENNReal.ofReal (2 * q))
              (f := fun _ : Ω => Cρ ^ 2) (C := Cρ ^ 2) aestronglyMeasurable_const
              (Filter.Eventually.of_forall fun _ => by rw [Real.norm_eq_abs, abs_of_nonneg hsq])
            simpa [measure_univ] using h
      _ = ENNReal.ofReal (Cy * Cc + Cρ ^ 2) := (ENNReal.ofReal_add hCyCc hsq).symm
      _ ≤ ENNReal.ofReal Cp := ENNReal.ofReal_le_ofReal (by rw [hCpdef]; exact le_max_right _ _)
  have hUbd : ∀ N, eLpNorm (Kres N) (ENNReal.ofReal (2 * q)) Pm ≤ ENNReal.ofReal Cp := fun N =>
    (hKbd N).trans (ENNReal.ofReal_le_ofReal (by rw [hCpdef]; exact le_max_left _ _))
  refine ⟨Cp * (1 + Cp), mul_nonneg hCp0 (add_nonneg zero_le_one hCp0), fun N => ?_⟩
  exact aux_rem_resolved_UV_moment Pm q Cp hq hCp0 (Kres N)
    (fun om => Cy * Kc N om + Cρ ^ 2) (hKmem N) (hVmem N) (hUbd N) (hVbd N)

theorem aux_lem_prefix_limit_atom_extraction_lge_resp_congr [NeZero d]
    {a b : PositiveCoefficient (unitNeumannCube d)} (h : a = b) (x : SpatialCoordinates d) (r : ℝ)
    (L : (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space
      →L[ℝ] ℝ) :
    localGradientEnergy a (s := Metric.ball x r) Metric.isOpen_ball.measurableSet
        (subspaceGradient (meanZeroResponseSpace
            (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space
          (responseSolution (meanZeroResponseSpace
            (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2) a L)) =
      localGradientEnergy b (s := Metric.ball x r) Metric.isOpen_ball.measurableSet
        (subspaceGradient (meanZeroResponseSpace
            (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space
          (responseSolution (meanZeroResponseSpace
            (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2) b L)) := by
  subst h; rfl

/-- The almost-sure growth clause for one model. -/
theorem aux_lem_prefix_limit_atom_extraction_neumann_growth_ae [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (p : Fin d → ℝ) (hp : ∑ i : Fin d, (p i) ^ 2 = 1)
    (t : ℝ)
    (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho) (hrho0 : ∀ tau, 0 ≤ rho tau)
    (hsupp : ∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) (hint : (∫ tau, rho tau) = 1)
    (Cρ : ℝ) (hCρ : 0 ≤ Cρ)
    (hface : ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
      ∀ y : SpatialCoordinates d, y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
        |faceBump rho p eps y| ≤ Cρ * eps⁻¹)
    (hmean : ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
      (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), faceBump rho p eps x) = 0)
    (fL2 : ℝ → DomainL2 (unitNeumannCube d))
    (hfL2 : ∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ((fL2 eps : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] faceBump rho p eps))
    (Cy : ℝ) (Kres Kc : ℕ → BilateralField d → ℝ) (hK0 : ∀ N om, 0 ≤ Kres N om)
    (hKc0 : ∀ N om, 0 ≤ Kc N om)
    (hY : ∀ N om (eps : ℝ), 0 < eps → eps < 1 / 8 →
      inverseResponse (meanZeroResponseSpace
        (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2)
        (cutoffPositiveCoefficient M (fun _ => 0) om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
        (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps) ≤ Cy * Kc N om)
    (hae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (∀ N : ℕ,
          ∀ f : SpatialCoordinates d → ℝ,
            AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          ∀ Kf : ℝ, 0 ≤ Kf →
            (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
              |f y| ≤ Kf) →
            (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
          ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
            SolvesNeumann (cutoffPositiveCoefficient M (fun _ => 0) omega N
              (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) f u →
          ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M (fun _ => 0) omega N
              (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
              (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
                Kres N omega *
                  (sobolevCoefficientForm (cutoffPositiveCoefficient M (fun _ => 0) omega N
                    (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
                    (u : SobolevData (unitNeumannCube d)) (u : SobolevData (unitNeumannCube d)) +
                    Kf ^ 2) * r ^ t) ∧
        (∀ N : ℕ,
          ∀ rho : ℝ → ℝ, ContDiff ℝ ∞ rho →
            (∀ tau : ℝ, 0 ≤ rho tau) →
            (∀ tau : ℝ, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
            (∫ tau, rho tau) = 1 →
          ∀ pvec : Fin d → ℝ, (∑ i : Fin d, (pvec i) ^ 2) = 1 →
          ∀ Cρ : ℝ, 0 ≤ Cρ →
            (∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
              ∀ y : SpatialCoordinates d, y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
                |faceBump rho pvec eps y| ≤ Cρ * eps⁻¹) →
          ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
          ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
            SolvesNeumann (cutoffPositiveCoefficient M (fun _ => 0) omega N
              (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) (faceBump rho pvec eps) v →
          ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M (fun _ => 0) omega N
              (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
              (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
              (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
                Kres N omega *
                  (sobolevCoefficientForm (cutoffPositiveCoefficient M (fun _ => 0) omega N
                    (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
                    (v : SobolevData (unitNeumannCube d)) (v : SobolevData (unitNeumannCube d)) +
                    Cρ ^ 2 * eps ^ (-2 : ℝ)) * r ^ t))
 :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 8 →
      ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        localGradientEnergy
          (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N om))
          (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
          (subspaceGradient (meanZeroResponseSpace
              (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space
            (responseSolution (meanZeroResponseSpace
              (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2)
              (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N om))
              (aux_lem_prefix_limit_atom_extraction_Lf fL2 ε))) ≤
          Kres N om * (1 + (Cy * Kc N om + Cρ ^ 2)) * ε ^ (-2 : ℝ) * rho ^ t := by
  filter_upwards [hae] with om hom
  intro N eps heps heps8 x hx r hr hr1
  have hsec := hom.2 N rho hrho hrho0 hsupp hint p hp Cρ hCρ hface eps heps heps8
  have hg := aux_lem_prefix_limit_atom_extraction_neumann_growth_sample hd M om N
    (cutoffPositiveCoefficient M (fun _ => 0) om N (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) rfl
    p hp t rho Cρ fL2 hfL2 hmean (Kres N om) (Cy * Kc N om) (hK0 N om) hCρ eps heps heps8
    (hY N om eps heps heps8) hsec x hx r hr hr1
  rw [aux_lem_prefix_limit_atom_extraction_lge_resp_congr
    (aux_lem_prefix_limit_atom_extraction_coefN_eq M N om)]
  refine hg.trans ?_
  exact aux_lem_prefix_limit_atom_extraction_growth_mono (Kres N om) (Cy * Kc N om + Cρ ^ 2)
    (eps ^ (-2 : ℝ)) (r ^ t) (hK0 N om) (Real.rpow_nonneg heps.le _) (Real.rpow_nonneg hr.le _)

/-- Assembly of the Neumann inputs for one model. -/
theorem aux_lem_prefix_limit_atom_extraction_neumann_final [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (p : Fin d → ℝ) (hp : ∑ i : Fin d, (p i) ^ 2 = 1)
    (t q : ℝ) (hq : 1 ≤ q)
    (rho : ℝ → ℝ) (hrho : ContDiff ℝ ∞ rho) (hrho0 : ∀ tau, 0 ≤ rho tau)
    (hsupp : ∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) (hint : (∫ tau, rho tau) = 1)
    (Cρ : ℝ) (hCρ : 0 ≤ Cρ)
    (hface : ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
      ∀ y : SpatialCoordinates d, y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
        |faceBump rho p eps y| ≤ Cρ * eps⁻¹)
    (hmean : ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
      (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), faceBump rho p eps x) = 0)
    (fL2 : ℝ → DomainL2 (unitNeumannCube d))
    (hfL2 : ∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ((fL2 eps : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] faceBump rho p eps))
    (Cy : ℝ) (hCy0 : 0 ≤ Cy)
    (hCy : ∀ (a : PositiveCoefficient (unitNeumannCube d)) (K : ℝ), 0 ≤ K →
      (∀ v : meanZeroSobolevGraph (unitNeumannCube d),
        cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
            (v : SobolevData (unitNeumannCube d)).1 ≤
          K * sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
            (v : SobolevData (unitNeumannCube d))) →
      inverseResponse (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2) a
          ((affineNeumannLoad p).comp
            (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) ≤ Cy * K ∧
      ∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ∀ f0 : DomainL2 (unitNeumannCube d),
        ((f0 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
            faceBump rho p eps) →
        inverseResponse (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2) a
          ((sobolevVolumeLoad f0).comp
            (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space.subtypeL) ≤
            Cy * K)
    (Kres : ℕ → BilateralField d → ℝ) (Cr : ℝ) (hK0 : ∀ N om, 0 ≤ Kres N om)
    (hKmem : ∀ N, MemLp (Kres N) (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure)
    (hKbd : ∀ N, eLpNorm (Kres N) (ENNReal.ofReal (2 * q)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal Cr)
    (hae : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      (∀ N : ℕ,
          ∀ f : SpatialCoordinates d → ℝ,
            AEMeasurable f (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          ∀ Kf : ℝ, 0 ≤ Kf →
            (∀ᵐ y ∂volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d)),
              |f y| ≤ Kf) →
            (∫ y in (unitNeumannCube d : Set (SpatialCoordinates d)), f y) = 0 →
          ∀ u : meanZeroSobolevGraph (unitNeumannCube d),
            SolvesNeumann (cutoffPositiveCoefficient M (fun _ => 0) omega N
              (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) f u →
          ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M (fun _ => 0) omega N
              (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
              (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
              (sobolevGradient (u : SobolevData (unitNeumannCube d))) ≤
                Kres N omega *
                  (sobolevCoefficientForm (cutoffPositiveCoefficient M (fun _ => 0) omega N
                    (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
                    (u : SobolevData (unitNeumannCube d)) (u : SobolevData (unitNeumannCube d)) +
                    Kf ^ 2) * r ^ t) ∧
        (∀ N : ℕ,
          ∀ rho : ℝ → ℝ, ContDiff ℝ ∞ rho →
            (∀ tau : ℝ, 0 ≤ rho tau) →
            (∀ tau : ℝ, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) →
            (∫ tau, rho tau) = 1 →
          ∀ pvec : Fin d → ℝ, (∑ i : Fin d, (pvec i) ^ 2) = 1 →
          ∀ Cρ : ℝ, 0 ≤ Cρ →
            (∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
              ∀ y : SpatialCoordinates d, y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
                |faceBump rho pvec eps y| ≤ Cρ * eps⁻¹) →
          ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
          ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
            SolvesNeumann (cutoffPositiveCoefficient M (fun _ => 0) omega N
              (fun _ : Fin d => (1 / 2 : ℝ)) one_pos) (faceBump rho pvec eps) v →
          ∀ x : SpatialCoordinates d, x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
          ∀ r : ℝ, 0 < r → r ≤ 1 →
            localGradientEnergy (cutoffPositiveCoefficient M (fun _ => 0) omega N
              (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
              (s := Metric.ball x r ∩ (unitNeumannCube d : Set (SpatialCoordinates d)))
              (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
              (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
                Kres N omega *
                  (sobolevCoefficientForm (cutoffPositiveCoefficient M (fun _ => 0) omega N
                    (fun _ : Fin d => (1 / 2 : ℝ)) one_pos)
                    (v : SobolevData (unitNeumannCube d)) (v : SobolevData (unitNeumannCube d)) +
                    Cρ ^ 2 * eps ^ (-2 : ℝ)) * r ^ t))
    (Kc : ℕ → BilateralField d → ℝ) (hKc0 : ∀ N om, 0 ≤ Kc N om)
    (hKcCo : ∀ N om, ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
      cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
          (v : SobolevData (unitNeumannCube d)).1 ≤
        Kc N om * sobolevCoefficientForm
          (cutoffPositiveCoefficient M (fun _ => 0) om N
            (aux_lem_prefix_limit_atom_extraction_cN d) one_pos)
          (v : SobolevData (unitNeumannCube d)) (v : SobolevData (unitNeumannCube d)))
    (Cc : ℝ) (hCc : 0 ≤ Cc)
    (hKcMem : ∀ N, MemLp (Kc N) (ENNReal.ofReal (4 * q)) (chaosSampleLaw M).toMeasure)
    (hKcBd : ∀ N, eLpNorm (Kc N) (ENNReal.ofReal (4 * q)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal Cc)
    (Bs : ℝ) (hBs : 0 ≤ Bs)
    (hsm : ∀ (N : ℕ) (eps : ℝ), 0 < eps → eps < 1 / 8 →
      (MemLp (aux_lem_prefix_limit_atom_extraction_YN M
          (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps) N) (ENNReal.ofReal q)
          (chaosSampleLaw M).toMeasure ∧
        eLpNorm (aux_lem_prefix_limit_atom_extraction_YN M
          (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps) N) (ENNReal.ofReal q)
          (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal Bs) ∧
      eLpNorm (fun om => aux_lem_prefix_limit_atom_extraction_NzN M p N om -
          aux_lem_prefix_limit_atom_extraction_YN M
            (aux_lem_prefix_limit_atom_extraction_Lf fL2 eps) N om) 1
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (Bs * eps ^ (1 / 4 : ℝ))) :
    ∃ (L : ℝ → (meanZeroResponseSpace
          (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space →L[ℝ] ℝ)
        (K : ℕ → BilateralField d → ℝ) (B : ℝ), 0 ≤ B ∧
        (∀ N, AEStronglyMeasurable (K N) (chaosSampleLaw M).toMeasure) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 0 ≤ K N om) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 8 →
          ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
          ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
            localGradientEnergy
              (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N om))
              (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
              (subspaceGradient (meanZeroResponseSpace
                  (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space
                (responseSolution (meanZeroResponseSpace
                  (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2)
                  (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N om))
                  (L ε))) ≤
              K N om * ε ^ (-2 : ℝ) * rho ^ t) ∧
        (∀ N, MemLp (K N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (K N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B) ∧
        (∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 8 →
          MemLp (aux_lem_prefix_limit_atom_extraction_YN M (L ε) N) (ENNReal.ofReal q)
            (chaosSampleLaw M).toMeasure ∧
          eLpNorm (aux_lem_prefix_limit_atom_extraction_YN M (L ε) N) (ENNReal.ofReal q)
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B) ∧
        (∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 8 →
          eLpNorm (fun om => aux_lem_prefix_limit_atom_extraction_NzN M p N om -
              aux_lem_prefix_limit_atom_extraction_YN M (L ε) N om) 1
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (B * ε ^ (1 / 4 : ℝ))) := by
  have hKm := aux_lem_prefix_limit_atom_extraction_neumann_Kmom (chaosSampleLaw M).toMeasure q Cr Cc
    Cy Cρ hq hCc hCy0 Kres Kc hKmem hKbd hKcMem hKcBd
  obtain ⟨Bk, hBk, hKmom⟩ := hKm
  have hgr := aux_lem_prefix_limit_atom_extraction_neumann_growth_ae hd M p hp t rho hrho hrho0
    hsupp hint Cρ hCρ hface hmean fL2 hfL2 Cy Kres Kc hK0 hKc0
    (fun N om eps heps heps8 => (hCy _ (Kc N om) (hKc0 N om) (hKcCo N om)).2 eps heps heps8
      (fL2 eps) (hfL2 eps heps heps8)) hae
  have hmax1 : Bk ≤ max Bk Bs := le_max_left _ _
  have hmax2 : Bs ≤ max Bk Bs := le_max_right _ _
  refine ⟨aux_lem_prefix_limit_atom_extraction_Lf fL2,
    fun N om => Kres N om * (1 + (Cy * Kc N om + Cρ ^ 2)),
    max Bk Bs, le_max_of_le_right hBs, fun N => (hKmom N).1.aestronglyMeasurable,
    Filter.Eventually.of_forall fun om N => mul_nonneg (hK0 N om)
      (add_nonneg zero_le_one (add_nonneg (mul_nonneg hCy0 (hKc0 N om)) (sq_nonneg _))), hgr,
    fun N => ⟨(hKmom N).1, (hKmom N).2.trans (ENNReal.ofReal_le_ofReal hmax1)⟩,
    fun N eps heps heps8 => ⟨(hsm N eps heps heps8).1.1,
      (hsm N eps heps heps8).1.2.trans (ENNReal.ofReal_le_ofReal hmax2)⟩,
    fun N eps heps heps8 => (hsm N eps heps heps8).2.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hmax2 (Real.rpow_nonneg heps.le _)))⟩



/-- The face-bump data at a unit slope: bump, amplitude, `L²` representatives, load and response
constants. -/
theorem aux_lem_prefix_limit_atom_extraction_neumann_data (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Sf : SobolevFoundationalInput d hd) (p : Fin d → ℝ) (hp : ∑ i : Fin d, (p i) ^ 2 = 1) :
    ∃ (rho : ℝ → ℝ) (Cρ : ℝ) (fL2 : ℝ → DomainL2 (unitNeumannCube d)) (Cload Cy : ℝ),
      ContDiff ℝ ∞ rho ∧ (∀ tau, 0 ≤ rho tau) ∧
      (∀ tau, tau ∉ Set.Ioo (1 : ℝ) 2 → rho tau = 0) ∧ (∫ tau, rho tau) = 1 ∧ 0 ≤ Cρ ∧
      (∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
        ∀ y : SpatialCoordinates d, y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
          |faceBump rho p eps y| ≤ Cρ * eps⁻¹) ∧
      (∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
        (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), faceBump rho p eps x) = 0) ∧
      (∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ((fL2 eps : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] faceBump rho p eps)) ∧
      0 < Cload ∧ aux_lem_neumann_error_load_type d hd Cload ∧ 0 ≤ Cy ∧
      (∀ (a : PositiveCoefficient (unitNeumannCube d)) (K : ℝ), 0 ≤ K →
        (∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          cubeFractionalSqNorm hd (fun _ => (1 / 2 : ℝ)) 1 one_pos threeQuarterOrder
              (v : SobolevData (unitNeumannCube d)).1 ≤
            K * sobolevCoefficientForm a (v : SobolevData (unitNeumannCube d))
              (v : SobolevData (unitNeumannCube d))) →
        inverseResponse (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2) a
            ((affineNeumannLoad p).comp
              (subspaceGradient (meanZeroSobolevGraph (unitNeumannCube d)))) ≤ Cy * K ∧
        ∀ eps : ℝ, 0 < eps → eps < 1 / 8 → ∀ f0 : DomainL2 (unitNeumannCube d),
          ((f0 : SpatialCoordinates d → ℝ)
            =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))]
              faceBump rho p eps) →
          inverseResponse (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2) a
            ((sobolevVolumeLoad f0).comp
              (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space.subtypeL) ≤
              Cy * K) := by
  classical
  have hbump := aux_lem_prefix_limit_atom_extraction_bump
  obtain ⟨rho, hrho, hrho0, hsupp, hint, hcont, Mρ, hMρ0, hMρ⟩ := hbump
  have hCρ : 0 ≤ (∑ i : Fin d, |p i|) * (2 * Mρ) :=
    mul_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (by linarith)
  have hface : ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
      ∀ y : SpatialCoordinates d, y ∈ (unitNeumannCube d : Set (SpatialCoordinates d)) →
        |faceBump rho p eps y| ≤ ((∑ i : Fin d, |p i|) * (2 * Mρ)) * eps⁻¹ := by
    intro eps heps heps8 y _
    simpa only [faceBump, lane4_smoothed_neumann_load] using
      (lane4_smoothed_load_properties d rho hrho hsupp Mρ hMρ p eps heps heps8).2.1 y
  have hmean : ∀ eps : ℝ, 0 < eps → eps < 1 / 8 →
      (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), faceBump rho p eps x) = 0 := by
    intro eps heps heps8
    simpa only [faceBump, lane4_smoothed_neumann_load] using
      (lane4_smoothed_load_properties d rho hrho hsupp Mρ hMρ p eps heps heps8).2.2.2
  choose fL2 hfL2 using fun eps : ℝ => aux_rem_bank_faceBump_rep rho hcont p eps
  have hload := lem_neumann_error_load_bound d hd Sf
  obtain ⟨Cload, hCload, hLB⟩ := hload
  have hcy := aux_rem_bank_unit_neumann_response_le_coerc d hd Sf rho hrho hrho0 hsupp hint p hp
  obtain ⟨Cy, hCy0, hCy⟩ := hcy
  exact ⟨rho, _, fL2, Cload, Cy, hrho, hrho0, hsupp, hint, hCρ, hface, hmean,
    fun eps _ _ => hfL2 eps, hCload, hLB, hCy0,
    hCy (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2⟩

/-- **Neumann inputs** for `A_N^0` on the unit Neumann cube at a unit slope (paper `eq:mfd-9`,
`eq:mfd-13`), with the carried inputs `E, P, X, W, S, D` and per-model `Rm, Sreg, It`. -/
theorem aux_lem_prefix_limit_atom_extraction_neumann_inputsN (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (p : Fin d → ℝ) (hp : ∑ i : Fin d, (p i) ^ 2 = 1) (t q : ℝ) (ht1 : (d : ℝ) - 1 < t)
    (ht2 : t < (d : ℝ)) (hq : 1 ≤ q) :
    ∃ delta : ℝ, 0 < delta ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M) (Sreg : in_6_16 d M)
      (It : in_iteration d M E Sreg), M.delta ≤ delta →
      ∃ (L : ℝ → (meanZeroResponseSpace
          (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space →L[ℝ] ℝ)
        (K : ℕ → BilateralField d → ℝ) (B : ℝ), 0 ≤ B ∧
        (∀ N, AEStronglyMeasurable (K N) (chaosSampleLaw M).toMeasure) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 0 ≤ K N om) ∧
        (∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 8 →
          ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
          ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
            localGradientEnergy
              (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N om))
              (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
              (subspaceGradient (meanZeroResponseSpace
                  (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space
                (responseSolution (meanZeroResponseSpace
                  (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2)
                  (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N om))
                  (L ε))) ≤
              K N om * ε ^ (-2 : ℝ) * rho ^ t) ∧
        (∀ N, MemLp (K N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (K N) (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B) ∧
        (∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 8 →
          MemLp (aux_lem_prefix_limit_atom_extraction_YN M (L ε) N) (ENNReal.ofReal q)
            (chaosSampleLaw M).toMeasure ∧
          eLpNorm (aux_lem_prefix_limit_atom_extraction_YN M (L ε) N) (ENNReal.ofReal q)
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B) ∧
        (∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 8 →
          eLpNorm (fun om => aux_lem_prefix_limit_atom_extraction_NzN M p N om -
              aux_lem_prefix_limit_atom_extraction_YN M (L ε) N om) 1
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (B * ε ^ (1 / 4 : ℝ))) := by
  have hdat := aux_lem_prefix_limit_atom_extraction_neumann_data d hd Sf p hp
  obtain ⟨rho, Cρ, fL2, Cload, Cy, hrho, hrho0, hsupp, hint, hCρ, hface, hmean, hfL2, hCload, hLB,
    hCy0, hCy⟩ := hdat
  have hres := aux_lem_prefix_limit_atom_extraction_resolved0 d hd E P X W D t 1 (fun _ => 2 * q)
    ht1 ht2 (fun _ => by linarith)
  obtain ⟨δres, hδres, hresM⟩ := hres
  have hco := aux_lem_prefix_limit_atom_extraction_coerc0N d hd E P Sf
  obtain ⟨dc, hdc, hcoM⟩ := hco
  have h4q : (1 : ℝ) ≤ 4 * q := by linarith
  refine ⟨min δres (dc (4 * q)), lt_min hδres (hdc (4 * q) h4q), ?_⟩
  intro M Rm Sreg It hδ
  have hRM := hresM M Rm Sreg It (hδ.trans (min_le_left _ _))
  obtain ⟨Kres, Cb, hK0, hKmem, hKbd, hae⟩ := hRM
  have hCM := hcoM M Rm
  obtain ⟨Kc, hKc0, hKcCo, hKcmom⟩ := hCM
  have hKcm := hKcmom (4 * q) h4q (hδ.trans (min_le_right _ _))
  obtain ⟨Cc, hCc, hKc⟩ := hKcm
  have hsmo := aux_lem_prefix_limit_atom_extraction_neumann_smoothing hd M p hp q hq rho hrho hrho0
    hsupp hint fL2 hfL2 Cload hCload hLB Cy hCy0 hCy Kc hKc0 hKcCo Cc hCc
    (fun N => (hKc N).1) (fun N => (hKc N).2)
  obtain ⟨Bs, hBs, hsm⟩ := hsmo
  exact aux_lem_prefix_limit_atom_extraction_neumann_final hd M p hp t q hq rho hrho hrho0 hsupp
    hint Cρ hCρ hface hmean fL2 hfL2 Cy hCy0 hCy Kres (Cb 0) hK0
    (fun N => hKmem 0 N) (fun N => hKbd 0 N) hae Kc hKc0 hKcCo Cc hCc (fun N => (hKc N).1)
    (fun N => (hKc N).2) Bs hBs hsm

end PaeN0Main

section PaeN0Band

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

variable {d : ℕ}

theorem aux_lem_prefix_limit_atom_extraction_band_generic
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (X : ℕ → BilateralField d → ℝ) (Y : ℝ → ℕ → BilateralField d → ℝ) (A B δ a0 : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (ha0 : 0 < a0)
    (hYint : ∀ (ε : ℝ), 0 < ε → ε < 1 / 8 → ∀ N, Integrable (Y ε N) (chaosSampleLaw M).toMeasure)
    (hYdet : ∀ (ε : ℝ) (N : ℕ) (ω₁ ω₂ : BilateralField d),
      (∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ 0 → ω₁ j = ω₂ j) → Y ε N ω₁ = Y ε N ω₂)
    (hsm : ∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 8 →
      eLpNorm (fun ω => X N ω - Y ε N ω) 1 (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (B * ε ^ (1 / 4 : ℝ)))
    (hstep : ∀ (ε : ℝ), 0 < ε → ε < 1 / 8 → ∀ N k : ℕ, k ≤ N →
      eLpNorm (fun q : BilateralField d × BilateralField d =>
          Y ε N q.1 - Y ε N (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))) 1
        ((chaosSampleLaw M).toMeasure.prod (chaosSampleLaw M).toMeasure) ≤
      ENNReal.ofReal (A * (B * ε ^ (-2 : ℝ)) * δ * (3 : ℝ) ^ (-(a0 * (k : ℝ))))) :
    ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧ ∀ H N : ℕ, H ≤ N →
      Integrable (X N) (chaosSampleLaw M).toMeasure →
      eLpNorm (fun ω => X N ω - ((chaosSampleLaw M).toMeasure[X N |
          bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H]) ω)
        1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
  classical
  let P := (chaosSampleLaw M).toMeasure
  have hr1 : (3 : ℝ) ^ (-a0) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨rg, hrg⟩ : ∃ rg : ℝ, rg = (1 - (3 : ℝ) ^ (-a0))⁻¹ := ⟨_, rfl⟩
  have hrg0 : 0 ≤ rg := by rw [hrg]; exact inv_nonneg.mpr (by linarith)
  refine ⟨2 * B + 256 * (A * B * δ * rg), a0 / 32, by positivity, by positivity, ?_⟩
  intro H N hHN hint
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (1 / 16) * (3 : ℝ) ^ (-(a0 * (H : ℝ) / 8)) := ⟨_, rfl⟩
  have hfacts := aux_lem_prefix_limit_atom_extraction_eps_facts a0 ha0 H
  simp only at hfacts
  rw [← hε] at hfacts
  obtain ⟨hε0, hε8, hε1, hε14, hεm2⟩ := hfacts
  have hεm2ge : 1 ≤ ε ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 hε1 (by norm_num)
  have hBε : 0 ≤ B * ε ^ (-2 : ℝ) := mul_nonneg hB (by linarith)
  have hYi : Integrable (Y ε N) P := hYint ε hε0 hε8 N
  have htri := aux_lem_prefix_limit_atom_extraction_band_triangle
    (m := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H) hint hYi
  have hband := aux_lem_prefix_limit_atom_extraction_band_le_sum
    (fun j : ℤ => (scaledLayerLaw d (chaosRootFieldLaw M) j : Measure C(SpatialCoordinates d, ℝ)))
    (p := 1) le_rfl ENNReal.one_ne_top (Y ε N) hYi H N (hYdet ε N)
    (fun k => ENNReal.ofReal (A * (B * ε ^ (-2 : ℝ)) * δ * (3 : ℝ) ^ (-(a0 * (k : ℝ)))))
    (fun k _ hk => hstep ε hε0 hε8 N k hk)
  have hc0 : 0 ≤ A * (B * ε ^ (-2 : ℝ)) * δ := mul_nonneg (mul_nonneg hA hBε) hδ
  have hnn : ∀ k : ℕ, 0 ≤ A * (B * ε ^ (-2 : ℝ)) * δ * (3 : ℝ) ^ (-(a0 * (k : ℝ))) :=
    fun k => mul_nonneg hc0 (Real.rpow_nonneg (by norm_num) _)
  have hgeomsum : ∑ k ∈ Finset.Ioc H N,
      ENNReal.ofReal (A * (B * ε ^ (-2 : ℝ)) * δ * (3 : ℝ) ^ (-(a0 * (k : ℝ)))) ≤
      ENNReal.ofReal (A * B * δ * rg * (256 * (3 : ℝ) ^ (-(a0 / 32 * (H : ℝ))))) := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hnn k]
    apply ENNReal.ofReal_le_ofReal
    rw [← Finset.mul_sum]
    have hg := aux_lem_prefix_limit_atom_extraction_geom a0 ha0 H N
    rw [← hrg] at hg
    calc A * (B * ε ^ (-2 : ℝ)) * δ * ∑ k ∈ Finset.Ioc H N, (3 : ℝ) ^ (-(a0 * (k : ℝ)))
        ≤ A * (B * ε ^ (-2 : ℝ)) * δ * (rg * (3 : ℝ) ^ (-(a0 * (H : ℝ)))) :=
          mul_le_mul_of_nonneg_left hg hc0
      _ = A * B * δ * rg * (ε ^ (-2 : ℝ) * (3 : ℝ) ^ (-(a0 * (H : ℝ)))) := by ring
      _ ≤ A * B * δ * rg * (256 * (3 : ℝ) ^ (-(a0 / 32 * (H : ℝ)))) :=
          mul_le_mul_of_nonneg_left hεm2 (by positivity)
  have hsm' : eLpNorm (fun ω => X N ω - Y ε N ω) 1 P ≤
      ENNReal.ofReal (B * (3 : ℝ) ^ (-(a0 / 32 * (H : ℝ)))) :=
    (hsm N ε hε0 hε8).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hε14 hB))
  refine htri.trans ?_
  have h3 : 0 ≤ (3 : ℝ) ^ (-(a0 / 32 * (H : ℝ))) := Real.rpow_nonneg (by norm_num) _
  calc 2 * eLpNorm (fun ω => X N ω - Y ε N ω) 1 P +
      eLpNorm (fun ω => Y ε N ω -
        P[Y ε N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H] ω) 1 P
      ≤ 2 * ENNReal.ofReal (B * (3 : ℝ) ^ (-(a0 / 32 * (H : ℝ)))) +
          ENNReal.ofReal (A * B * δ * rg * (256 * (3 : ℝ) ^ (-(a0 / 32 * (H : ℝ))))) := by
        gcongr
        exact hband.trans hgeomsum
    _ = ENNReal.ofReal ((2 * B + 256 * (A * B * δ * rg)) *
          (3 : ℝ) ^ (-(a0 / 32 * (H : ℝ)))) := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end PaeN0Band

section PaeN0BandN

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

variable {d : ℕ}

/-- The Neumann-cube potential at cutoff `N` reads only the coordinates `-N, …, 0`. -/
theorem aux_lem_prefix_limit_atom_extraction_potN_det (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (N : ℕ) (ω₁ ω₂ : BilateralField d)
    (h : ∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ 0 → ω₁ j = ω₂ j) :
    aux_lem_prefix_limit_atom_extraction_potN M N ω₁ =
      aux_lem_prefix_limit_atom_extraction_potN M N ω₂ := by
  unfold aux_lem_prefix_limit_atom_extraction_potN
  congr 3
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  exact h _ (by omega) (by omega)

theorem aux_lem_prefix_limit_atom_extraction_YN_tau_det [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (L : (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space
      →L[ℝ] ℝ) (N : ℕ) (ω₁ ω₂ : BilateralField d)
    (h : ∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ 0 → ω₁ j = ω₂ j) :
    aux_lem_prefix_limit_atom_extraction_YN M L N (aux_lem_prefix_limit_atom_extraction_tau ω₁) =
      aux_lem_prefix_limit_atom_extraction_YN M L N (aux_lem_prefix_limit_atom_extraction_tau ω₂) := by
  have h' : aux_lem_prefix_limit_atom_extraction_potN M N (aux_lem_prefix_limit_atom_extraction_tau ω₁) =
      aux_lem_prefix_limit_atom_extraction_potN M N (aux_lem_prefix_limit_atom_extraction_tau ω₂) := by
    refine aux_lem_prefix_limit_atom_extraction_potN_det M N _ _ fun j h1 h2 => ?_
    unfold aux_lem_prefix_limit_atom_extraction_tau aux_prop_growth_energy_assembly_shift
    rw [h j h1 h2]
  unfold aux_lem_prefix_limit_atom_extraction_YN
  rw [h']

/-- Single-layer influences are invariant under `τ`. -/
theorem aux_lem_prefix_limit_atom_extraction_step_tau
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (F : BilateralField d → ℝ) (hF : Continuous F)
    (k : ℕ) (p : ℝ≥0∞) :
    eLpNorm (fun q : BilateralField d × BilateralField d =>
        F (aux_lem_prefix_limit_atom_extraction_tau q.1) -
          F (aux_lem_prefix_limit_atom_extraction_tau
            (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ)))))) p
      ((chaosSampleLaw M).toMeasure.prod (chaosSampleLaw M).toMeasure) =
    eLpNorm (fun q : BilateralField d × BilateralField d =>
        F q.1 - F (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))) p
      ((chaosSampleLaw M).toMeasure.prod (chaosSampleLaw M).toMeasure) := by
  have hT := aux_lem_prefix_limit_atom_extraction_tau_prod_mp M
  have hG : Continuous (fun q : BilateralField d × BilateralField d =>
      F q.1 - F (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))) := by
    have hup : Continuous (fun q : BilateralField d × BilateralField d =>
        Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ)))) := by
      refine continuous_pi fun j => ?_
      by_cases hj : j = -(k : ℤ)
      · rw [hj]
        have e : (fun q : BilateralField d × BilateralField d =>
            Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))) (-(k : ℤ))) =
            fun q => q.2 (-(k : ℤ)) := by
          funext q
          exact Function.update_self _ _ _
        rw [e]
        exact (continuous_apply (-(k : ℤ))).comp continuous_snd
      · have e : (fun q : BilateralField d × BilateralField d =>
            Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))) j) = fun q => q.1 j := by
          funext q
          exact Function.update_of_ne hj _ _
        rw [e]
        exact (continuous_apply j).comp continuous_fst
    exact (hF.comp continuous_fst).sub (hF.comp hup)
  have h := eLpNorm_comp_measurePreserving (p := p) hG.measurable.aestronglyMeasurable hT
  rw [← h]
  congr 1
  funext q
  simp only [Function.comp_apply]
  rw [aux_lem_prefix_limit_atom_extraction_tau_update]

/-- The Neumann-cube coefficient as an exponential of the zero-infrared cutoff potential. -/
theorem aux_lem_prefix_limit_atom_extraction_haN (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (om : BilateralField d) :
    (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N om)).val
      =ᵐ[volume.restrict ((centeredCube (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos :
        Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))]
      (fun x => Real.exp (cutoffPotential (fun _ => 0) om N x -
        Real.log (aux_lem_prefix_limit_atom_extraction_kappa M N))) := by
  filter_upwards [expPotentialCoefficient_coeFn (aux_lem_prefix_limit_atom_extraction_potN M N om),
    aux_lem_prefix_limit_atom_extraction_potN_ae M N om] with x h1 h2
  rw [h1, h2]
  congr 1
  simp [cutoffPotential]

/-- The single-layer influence of the smoothed Neumann responses on the unit Neumann cube, read
at `τω`, from the `H := 0` port of `lem_neumann_15`. -/
theorem aux_lem_prefix_limit_atom_extraction_hstepN [NeZero d] (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (t A : ℝ)
    (hn : ∀ (B : ℝ), 0 ≤ B →
      ∀ (S : ResponseSpace (centeredCube (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos))
        (dir : Bool)
        (bd : weakSobolevGraph (centeredCube (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos))
        (L : S.space →L[ℝ] ℝ)
        (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (Praw : ProbabilityMeasure (SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d))
          (_G1 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG1 d Praw)
          (_G2 : SubdiffusiveProcess.Frozen.Assumptions.ShellLawG2 d delta Praw),
          let forget : C(SubdiffusiveProcess.Frozen.Assumptions.PotentialField d,
              C(SpatialCoordinates d, ℝ)) :=
            ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
          let nu := (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw Praw).map
            forget
          let P := (commonScaleLaw d nu).toMeasure
          ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
            Measurable H →
            (∀ j : ℕ, ∀ᵐ pair ∂(P.prod P),
              H pair.1 = H (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ))))) →
          ∀ (kappa : ℕ → ℝ)
            (aN : ℕ → BilateralField d → PositiveCoefficient
              (centeredCube (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos)),
            (∀ N omega,
              (aN N omega).val =ᵐ[volume.restrict
                (centeredCube (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos :
                  Set (SpatialCoordinates d))]
                (fun x => Real.exp (cutoffPotential H omega N x - Real.log (kappa N)))) →
          ∀ (K : ℕ → BilateralField d → ℝ),
            (∀ N, AEStronglyMeasurable (K N) P) →
            (∀ᵐ omega ∂P, ∀ N, 0 ≤ K N omega) →
            (∀ᵐ omega ∂P, ∀ N, ∀ x ∈ (centeredCube (aux_lem_prefix_limit_atom_extraction_cN d) 1
                one_pos : Set (SpatialCoordinates d)),
              ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
                localGradientEnergy (aN N omega)
                  (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
                  (aux_lem_15_u_grad S dir bd L (aN N omega)) ≤ K N omega * rho ^ t) →
            ∀ (N j : ℕ), j ≤ N →
            eLpNorm (K N) (ENNReal.ofReal (3 * 2)) P ≤ ENNReal.ofReal B →
            eLpNorm (fun omega => aux_lem_15_u_resp S dir bd L (aN N omega))
              (ENNReal.ofReal (3 * 2)) P ≤ ENNReal.ofReal B →
              eLpNorm
                (fun pair : BilateralField d × BilateralField d =>
                  aux_lem_15_u_resp S dir bd L (aN N pair.1) -
                    aux_lem_15_u_resp S dir bd L (aN N
                      (Function.update pair.1 (-(j : ℤ)) (pair.2 (-(j : ℤ))))))
                (ENNReal.ofReal 2) (P.prod P) ≤
              ENNReal.ofReal
                (A * B * delta *
                  (3 : ℝ) ^
                  (-(t * (t - (d : ℝ) + 1) / (t + 1) /
                      (8 * Real.log 3)) * (j : ℝ))))
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (hMpos : 0 < M.delta) (hM1 : M.delta ≤ 1)
    (L : ℝ → (meanZeroResponseSpace
          (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space →L[ℝ] ℝ)
    (K : ℕ → BilateralField d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hKm : ∀ N, AEStronglyMeasurable (K N) (chaosSampleLaw M).toMeasure)
    (hK0 : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N, 0 ≤ K N om)
    (hgrowth : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 8 →
          ∀ x ∈ (unitNeumannCube d : Set (SpatialCoordinates d)),
          ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
            localGradientEnergy
              (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N om))
              (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
              (subspaceGradient (meanZeroResponseSpace
                  (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2).space
                (responseSolution (meanZeroResponseSpace
                  (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2)
                  (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N om))
                  (L ε))) ≤
              K N om * ε ^ (-2 : ℝ) * rho ^ t)
    (hKmom : ∀ N, MemLp (K N) (ENNReal.ofReal (3 * 2)) (chaosSampleLaw M).toMeasure ∧
          eLpNorm (K N) (ENNReal.ofReal (3 * 2)) (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B)
    (hYmom : ∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 8 →
          MemLp (aux_lem_prefix_limit_atom_extraction_YN M (L ε) N) (ENNReal.ofReal (3 * 2))
            (chaosSampleLaw M).toMeasure ∧
          eLpNorm (aux_lem_prefix_limit_atom_extraction_YN M (L ε) N) (ENNReal.ofReal (3 * 2))
            (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal B)
    (a0 : ℝ) (ha0 : a0 = t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3))
    (ε : ℝ) (hε : 0 < ε) (hε8 : ε < 1 / 8) (N k : ℕ) (hk : k ≤ N) :
    eLpNorm (fun q : BilateralField d × BilateralField d =>
        aux_lem_prefix_limit_atom_extraction_YN M (L ε) N (aux_lem_prefix_limit_atom_extraction_tau q.1) -
          aux_lem_prefix_limit_atom_extraction_YN M (L ε) N (aux_lem_prefix_limit_atom_extraction_tau
            (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ)))))) 1
      ((chaosSampleLaw M).toMeasure.prod (chaosSampleLaw M).toMeasure) ≤
    ENNReal.ofReal (A * (B * ε ^ (-2 : ℝ)) * M.delta * (3 : ℝ) ^ (-(a0 * (k : ℝ)))) := by
  let Pm := (chaosSampleLaw M).toMeasure
  have hε1 : ε ≤ 1 := le_of_lt (lt_trans hε8 (by norm_num))
  have hεm2ge : 1 ≤ ε ^ (-2 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by norm_num)
  have hε2nn : 0 ≤ ε ^ (-2 : ℝ) := zero_le_one.trans hεm2ge
  have hBε : 0 ≤ B * ε ^ (-2 : ℝ) := mul_nonneg hB hε2nn
  have hresp : ∀ (N : ℕ) (ω : BilateralField d),
      aux_lem_15_u_resp (meanZeroResponseSpace
          (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2) false 0 (L ε)
          (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N ω)) =
        aux_lem_prefix_limit_atom_extraction_YN M (L ε) N ω := by
    intro N ω
    simp only [aux_lem_15_u_resp, Bool.false_eq_true, ↓reduceIte,
      aux_lem_prefix_limit_atom_extraction_YN]
  have hKm' : ∀ N, AEStronglyMeasurable (fun ω => K N ω * ε ^ (-2 : ℝ)) Pm := fun N =>
    (hKm N).mul_const _
  have hK0' : ∀ᵐ ω ∂Pm, ∀ N, 0 ≤ K N ω * ε ^ (-2 : ℝ) := by
    filter_upwards [hK0] with ω hω
    intro N
    exact mul_nonneg (hω N) hε2nn
  have hgrowth' : ∀ᵐ ω ∂Pm, ∀ N, ∀ x ∈ ((centeredCube (aux_lem_prefix_limit_atom_extraction_cN d) 1
      one_pos : Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        localGradientEnergy
          (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N ω))
          (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
          (aux_lem_15_u_grad (meanZeroResponseSpace
              (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2) false 0 (L ε)
            (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N ω))) ≤
          K N ω * ε ^ (-2 : ℝ) * rho ^ t := by
    filter_upwards [hgrowth] with ω hω
    intro N x hx rho h1 h2
    simp only [aux_lem_15_u_grad, Bool.false_eq_true, ↓reduceIte]
    exact hω N ε hε hε8 x hx rho h1 h2
  have hn1 := hn (B * ε ^ (-2 : ℝ)) hBε
    (meanZeroResponseSpace (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2) false 0
    (L ε) M.delta hMpos hM1 M.P M.G1 M.G2 (fun _ => (0 : C(SpatialCoordinates d, ℝ)))
    measurable_const (fun j => ae_of_all _ fun _ => rfl)
    (aux_lem_prefix_limit_atom_extraction_kappa M)
    (fun N ω => expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N ω))
    (aux_lem_prefix_limit_atom_extraction_haN M)
    (fun N ω => K N ω * ε ^ (-2 : ℝ)) hKm' hK0' hgrowth'
  have hKk : eLpNorm (fun ω => K N ω * ε ^ (-2 : ℝ)) (ENNReal.ofReal (3 * 2)) Pm ≤
      ENNReal.ofReal (B * ε ^ (-2 : ℝ)) := by
    rw [show (fun ω => K N ω * ε ^ (-2 : ℝ)) = (ε ^ (-2 : ℝ)) • K N by
      funext ω; simp [mul_comm], eLpNorm_const_smul,
      Real.enorm_eq_ofReal hε2nn, mul_comm B, ENNReal.ofReal_mul hε2nn]
    gcongr
    exact (hKmom N).2
  have hYk : eLpNorm (fun ω => aux_lem_15_u_resp (meanZeroResponseSpace
        (aux_lem_prefix_limit_atom_extraction_poincareN (d := d)).2) false 0 (L ε)
        (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_potN M N ω)))
      (ENNReal.ofReal (3 * 2)) Pm ≤ ENNReal.ofReal (B * ε ^ (-2 : ℝ)) := by
    simp only [hresp]
    exact ((hYmom N ε hε hε8).2).trans (ENNReal.ofReal_le_ofReal
      (le_mul_of_one_le_right hB hεm2ge))
  have h := hn1 N k hk hKk hYk
  rw [aux_lem_prefix_limit_atom_extraction_step_tau M _
    (aux_lem_prefix_limit_atom_extraction_YN_continuous M (L ε) N) k 1]
  have hmeas : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
      aux_lem_prefix_limit_atom_extraction_YN M (L ε) N q.1 -
        aux_lem_prefix_limit_atom_extraction_YN M (L ε) N
          (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))) (Pm.prod Pm) := by
    have hc := aux_lem_prefix_limit_atom_extraction_YN_continuous M (L ε) N
    have hup : Continuous (fun q : BilateralField d × BilateralField d =>
        Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ)))) := by
      refine continuous_pi fun j => ?_
      by_cases hj : j = -(k : ℤ)
      · rw [hj]
        have e : (fun q : BilateralField d × BilateralField d =>
            Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))) (-(k : ℤ))) =
            fun q => q.2 (-(k : ℤ)) := by
          funext q
          exact Function.update_self _ _ _
        rw [e]
        exact (continuous_apply (-(k : ℤ))).comp continuous_snd
      · have e : (fun q : BilateralField d × BilateralField d =>
            Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))) j) = fun q => q.1 j := by
          funext q
          exact Function.update_of_ne hj _ _
        rw [e]
        exact (continuous_apply j).comp continuous_fst
    exact ((hc.comp continuous_fst).sub (hc.comp hup)).measurable.aestronglyMeasurable
  calc eLpNorm (fun q : BilateralField d × BilateralField d =>
        aux_lem_prefix_limit_atom_extraction_YN M (L ε) N q.1 -
          aux_lem_prefix_limit_atom_extraction_YN M (L ε) N
            (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))) 1 (Pm.prod Pm)
      ≤ eLpNorm (fun q : BilateralField d × BilateralField d =>
        aux_lem_prefix_limit_atom_extraction_YN M (L ε) N q.1 -
          aux_lem_prefix_limit_atom_extraction_YN M (L ε) N
            (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))) (ENNReal.ofReal 2) (Pm.prod Pm) :=
        eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    _ ≤ _ := h
    _ = ENNReal.ofReal (A * (B * ε ^ (-2 : ℝ)) * M.delta * (3 : ℝ) ^ (-(a0 * (k : ℝ)))) := by
        rw [ha0, neg_mul]

/-- **Neumann band estimate at a unit slope** for the affine inverse-Neumann response of `A_N^0`
on `Q₀` (paper `eq:mfd-16`, Neumann clause, fine block). -/
theorem aux_lem_prefix_limit_atom_extraction_band_N_unit (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (p : Fin d → ℝ) (hp : ∑ i : Fin d, (p i) ^ 2 = 1) :
    ∃ delta : ℝ, 0 < delta ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta →
    ∀ (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
      ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧ ∀ H N : ℕ, H ≤ N →
        Integrable (aux_lem_prefix_limit_atom_extraction_Nz M p N) (chaosSampleLaw M).toMeasure →
        eLpNorm (fun ω => aux_lem_prefix_limit_atom_extraction_Nz M p N ω -
            ((chaosSampleLaw M).toMeasure[aux_lem_prefix_limit_atom_extraction_Nz M p N |
              bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H]) ω)
          1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
  classical
  have hex : ∃ t : ℝ, t = (d : ℝ) - 1 / 2 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ := hex
  have ht1 : (d : ℝ) - 1 < t := by rw [ht]; linarith
  have ht2 : t < (d : ℝ) := by rw [ht]; linarith
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have htpos : 0 < t := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith
  have h2 : 0 < t - (d : ℝ) + 1 := by linarith
  have hexa : ∃ a0 : ℝ, a0 = t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) := ⟨_, rfl⟩
  obtain ⟨a0, ha0⟩ := hexa
  have ha0pos : 0 < a0 := by rw [ha0]; positivity
  have hI := aux_lem_prefix_limit_atom_extraction_neumann_inputsN d hd E P X W Sf D p hp t (3 * 2)
    ht1 ht2 (by norm_num)
  obtain ⟨δI, hδI, hI⟩ := hI
  have hN15 := aux_lem_prefix_limit_atom_extraction_n15_uniform d hd
    (aux_lem_prefix_limit_atom_extraction_cN d) 1 one_pos t 2 ht1 le_rfl
  obtain ⟨A, hA, hn⟩ := hN15
  refine ⟨δI, hδI, ?_⟩
  intro M hM Rm Sreg It
  have hMpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hM1 : M.delta ≤ 1 := M.shellPrefix.delta_le_half.trans (by norm_num)
  have hIM := hI M Rm Sreg It hM
  obtain ⟨L, K, B, hB, hKm, hK0, hgrowth, hKmom, hYmom, hsmooth⟩ := hIM
  have hmp := aux_lem_prefix_limit_atom_extraction_tau_mp M
  refine aux_lem_prefix_limit_atom_extraction_band_generic M (aux_lem_prefix_limit_atom_extraction_Nz M p)
    (fun ε N ω => aux_lem_prefix_limit_atom_extraction_YN M (L ε) N
      (aux_lem_prefix_limit_atom_extraction_tau ω)) A B M.delta a0 hA hB hMpos.le ha0pos
    ?_ ?_ ?_ ?_
  · intro ε hε hε8 N
    have h := ((hYmom N ε hε hε8).1.comp_measurePreserving hmp)
    exact h.integrable (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num))
  · intro ε N ω₁ ω₂ h
    exact aux_lem_prefix_limit_atom_extraction_YN_tau_det M (L ε) N ω₁ ω₂ h
  · intro N ε hε hε8
    have hfun : (fun ω => aux_lem_prefix_limit_atom_extraction_Nz M p N ω -
        aux_lem_prefix_limit_atom_extraction_YN M (L ε) N (aux_lem_prefix_limit_atom_extraction_tau ω)) =
        (fun ω' => aux_lem_prefix_limit_atom_extraction_NzN M p N ω' -
          aux_lem_prefix_limit_atom_extraction_YN M (L ε) N ω') ∘
          aux_lem_prefix_limit_atom_extraction_tau := by
      funext ω
      simp only [Function.comp_apply]
      rw [aux_lem_prefix_limit_atom_extraction_Nz_tau]
    have hdiff : AEStronglyMeasurable
        (fun ω' => aux_lem_prefix_limit_atom_extraction_NzN M p N ω' -
          aux_lem_prefix_limit_atom_extraction_YN M (L ε) N ω')
        (chaosSampleLaw M).toMeasure := by
      simpa only [Pi.sub_apply] using!
        ((aux_lem_prefix_limit_atom_extraction_NzN_continuous M p N).sub
          (aux_lem_prefix_limit_atom_extraction_YN_continuous M (L ε) N)).measurable.aestronglyMeasurable
    rw [hfun, eLpNorm_comp_measurePreserving hdiff hmp]
    exact hsmooth N ε hε hε8
  · intro ε hε hε8 N k hk
    exact aux_lem_prefix_limit_atom_extraction_hstepN hd t A hn M hMpos hM1 L K B hB hKm hK0
      hgrowth hKmom hYmom a0 ha0 ε hε hε8 N k hk

/-- Homogeneity: `N_{s p} = s² N_p`. -/
theorem aux_lem_prefix_limit_atom_extraction_Nz_smul [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (s : ℝ) (hs : s ≠ 0) (q : Fin d → ℝ) (N : ℕ)
    (om : BilateralField d) :
    aux_lem_prefix_limit_atom_extraction_Nz M (s • q) N om =
      s ^ 2 * aux_lem_prefix_limit_atom_extraction_Nz M q N om := by
  unfold aux_lem_prefix_limit_atom_extraction_Nz aux_lem_prefix_limit_atom_extraction_N
  exact affineInverseNeumannResponse_smulSlope _ hs _ _

theorem aux_lem_prefix_limit_atom_extraction_Nz_zero [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) (om : BilateralField d) :
    aux_lem_prefix_limit_atom_extraction_Nz M 0 N om = 0 := by
  have h := aux_lem_prefix_limit_atom_extraction_Nz_smul M 2 two_ne_zero 0 N om
  rw [smul_zero] at h
  linarith

/-- The band error scales by the modulus of a constant factor. -/
theorem aux_lem_prefix_limit_atom_extraction_band_scale {Ω : Type*} {m m0 : MeasurableSpace Ω}
    {μ : Measure Ω} (X : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    eLpNorm (fun ω => c * X ω - μ[fun ω => c * X ω|m] ω) 1 μ =
      ENNReal.ofReal c * eLpNorm (fun ω => X ω - μ[X|m] ω) 1 μ := by
  have hce := condExp_smul (μ := μ) c X m
  have heq : (fun ω => c * X ω - μ[fun ω => c * X ω|m] ω) =ᵐ[μ]
      c • (fun ω => X ω - μ[X|m] ω) := by
    have h1 : (fun ω => c * X ω) = c • X := rfl
    rw [h1]
    filter_upwards [hce] with ω hω
    simp only [Pi.smul_apply, smul_eq_mul] at hω ⊢
    rw [hω]
    ring
  rw [eLpNorm_congr_ae heq, eLpNorm_const_smul, Real.enorm_eq_ofReal hc]

/-- **Neumann band estimate** for every slope. -/
theorem aux_lem_prefix_limit_atom_extraction_band_N0 (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (u : Fin d → ℝ) :
    ∃ delta : ℝ, 0 < delta ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta →
    ∀ (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
      ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧ ∀ H N : ℕ, H ≤ N →
        Integrable (aux_lem_prefix_limit_atom_extraction_Nz M u N) (chaosSampleLaw M).toMeasure →
        eLpNorm (fun ω => aux_lem_prefix_limit_atom_extraction_Nz M u N ω -
            ((chaosSampleLaw M).toMeasure[aux_lem_prefix_limit_atom_extraction_Nz M u N |
              bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H]) ω)
          1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
  by_cases hu : u = 0
  · subst hu
    refine ⟨1, one_pos, fun M _ _ _ _ => ⟨0, 1, le_rfl, one_pos, fun H N _ _ => ?_⟩⟩
    have h0 : aux_lem_prefix_limit_atom_extraction_Nz M 0 N = fun _ => 0 :=
      funext fun om => aux_lem_prefix_limit_atom_extraction_Nz_zero M N om
    rw [h0, show (fun _ : BilateralField d => (0 : ℝ)) = 0 from rfl, condExp_zero]
    simp
  have hsq : 0 < ∑ i : Fin d, (u i) ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
    exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi)))
      (Finset.single_le_sum (f := fun i => (u i) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  have hex : ∃ s : ℝ, s = Real.sqrt (∑ i : Fin d, (u i) ^ 2) := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ := hex
  have hs : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.2 hsq
  have hs2 : s ^ 2 = ∑ i : Fin d, (u i) ^ 2 := by rw [hsdef]; exact Real.sq_sqrt hsq.le
  have hp : ∑ i : Fin d, ((s⁻¹ • u) i) ^ 2 = 1 := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, ← hs2]
    field_simp
  have hu' : u = s • (s⁻¹ • u) := by rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hunit := aux_lem_prefix_limit_atom_extraction_band_N_unit d hd E P X W Sf D (s⁻¹ • u) hp
  obtain ⟨δ, hδ, hb⟩ := hunit
  refine ⟨δ, hδ, fun M hM Rm Sreg It => ?_⟩
  obtain ⟨C, a, hC, ha, hCa⟩ := hb M hM Rm Sreg It
  refine ⟨s ^ 2 * C, a, mul_nonneg (sq_nonneg _) hC, ha, fun H N hHN hint => ?_⟩
  have hfun : aux_lem_prefix_limit_atom_extraction_Nz M u N =
      fun om => s ^ 2 * aux_lem_prefix_limit_atom_extraction_Nz M (s⁻¹ • u) N om := by
    funext om
    conv_lhs => rw [hu']
    exact aux_lem_prefix_limit_atom_extraction_Nz_smul M s hs.ne' _ N om
  have hint' : Integrable (aux_lem_prefix_limit_atom_extraction_Nz M (s⁻¹ • u) N)
      (chaosSampleLaw M).toMeasure := by
    have h := hint.const_mul (s ^ 2)⁻¹
    refine h.congr (Filter.Eventually.of_forall fun om => ?_)
    rw [hfun]
    simp only
    field_simp
  rw [hfun, aux_lem_prefix_limit_atom_extraction_band_scale _ _ (sq_nonneg s)]
  calc ENNReal.ofReal (s ^ 2) * eLpNorm (fun ω => aux_lem_prefix_limit_atom_extraction_Nz M (s⁻¹ • u) N ω -
        ((chaosSampleLaw M).toMeasure[aux_lem_prefix_limit_atom_extraction_Nz M (s⁻¹ • u) N |
          bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H]) ω) 1 (chaosSampleLaw M).toMeasure
      ≤ ENNReal.ofReal (s ^ 2) * ENNReal.ofReal (C * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
        gcongr; exact hCa H N hHN hint'
    _ = ENNReal.ofReal (s ^ 2 * C * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg s), mul_assoc]

end PaeN0BandN

section PaeSLD

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The affine datum `x ↦ u·x` is nonconstant on the frontier of the unit cube when `u ≠ 0`. -/
theorem aux_lem_prefix_limit_atom_extraction_affine_nonconst (u : Fin d → ℝ) (hu : u ≠ 0) :
    ∃ x ∈ frontier ((centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
      ∃ y ∈ frontier ((centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
        (fun z => affineSlope u z + 0) x ≠ (fun z => affineSlope u z + 0) y := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
  have hfr : frontier ((centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) =
      Metric.sphere 0 (1 / 2) := by
    change frontier (Metric.ball (0 : SpatialCoordinates d) (1 / 2)) = _
    exact frontier_ball 0 (by norm_num)
  have hmem : ∀ s : ℝ, |s| = 1 / 2 → (Pi.single i s : SpatialCoordinates d) ∈
      Metric.sphere (0 : SpatialCoordinates d) (1 / 2) := by
    intro s hs
    rw [mem_sphere_zero_iff_norm, Pi.norm_single, Real.norm_eq_abs, hs]
  refine ⟨Pi.single i (1 / 2), hfr ▸ hmem _ (by norm_num), Pi.single i (-(1 / 2)),
    hfr ▸ hmem _ (by norm_num), ?_⟩
  simp only [affineSlope_apply, add_zero]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp),
    Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
  simp only [Pi.single_eq_same, Pi.zero_apply]
  intro h
  apply hi
  simp only [Pi.zero_apply]
  linarith

/-- **Single-layer influence** (paper `eq:mfd-15`) for the affine Dirichlet response of `A_N^0`. -/
theorem aux_lem_prefix_limit_atom_extraction_single_layer_D (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (W : Lane4.SmallPerturbationInput d) (u : Fin d → ℝ) :
    ∃ delta : ℝ, 0 < delta ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta →
      ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧ ∀ N k : ℕ, k ≤ N →
        eLpNorm (fun q : BilateralField d × BilateralField d =>
            aux_lem_prefix_limit_atom_extraction_Dz M u N q.1 -
              aux_lem_prefix_limit_atom_extraction_Dz M u N
                (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ)))))
          1 ((chaosSampleLaw M).toMeasure.prod (chaosSampleLaw M).toMeasure) ≤
        ENNReal.ofReal (C * (3 : ℝ) ^ (-(a * (k : ℝ)))) := by
  classical
  by_cases hu : u = 0
  · -- the zero datum has zero response
    refine ⟨1, one_pos, fun M _ => ⟨0, 1, le_rfl, one_pos, fun N k _ => ?_⟩⟩
    have h0 : ∀ ω, aux_lem_prefix_limit_atom_extraction_Dz M u N ω = 0 := by
      intro ω
      subst hu
      have h := aux_lem_prefix_limit_atom_extraction_W_qf
        (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N ω)) 0
      have hD0 := aux_lem_prefix_limit_atom_extraction_D_nonneg
        (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N ω)) 0
      have hN0 := aux_lem_prefix_limit_atom_extraction_N_nonneg
        (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N ω)) 0
      have hq0 : aux_lem_prefix_limit_atom_extraction_qf
          (aux_lem_prefix_limit_atom_extraction_Wpol
            (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N ω))) 0 = 0 := by
        simp [aux_lem_prefix_limit_atom_extraction_qf]
      rw [hq0] at h
      unfold aux_lem_prefix_limit_atom_extraction_W at h
      have hV := mul_pos two_pos (aux_lem_prefix_limit_atom_extraction_vol_pos (d := d))
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · change aux_lem_prefix_limit_atom_extraction_D _ 0 = 0
        linarith
      · linarith
    simp only [h0, sub_self]
    rw [show (fun _ : BilateralField d × BilateralField d => (0 : ℝ)) = 0 from rfl, eLpNorm_zero]
    exact zero_le
  -- the nontrivial datum
  set t : ℝ := (d : ℝ) - 1 / 2 with ht
  have ht1 : (d : ℝ) - 1 < t := by rw [ht]; linarith
  have ht2 : t < (d : ℝ) := by rw [ht]; linarith
  obtain ⟨δG, hδG, hG⟩ := aux_lem_prefix_limit_atom_extraction_growth_D d W u t (3 * 2) ht1 ht2
    (by norm_num)
  obtain ⟨δR, hδR, hR⟩ := aux_lem_prefix_limit_atom_extraction_moments_q d (3 * 2) (by norm_num)
  refine ⟨min δG δR, lt_min hδG hδR, ?_⟩
  intro M hM
  have hd : 2 ≤ d := M.shellPrefix.dimension
  have hMpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hM1 : M.delta ≤ 1 := M.shellPrefix.delta_le_half.trans (by norm_num)
  obtain ⟨K, BK, hBK, hKm, hgrowth, hKmom⟩ := hG M (hM.trans (min_le_left _ _))
  obtain ⟨BR, hBR, hRmom⟩ := hR M (hM.trans (min_le_right _ _))
  set P := (chaosSampleLaw M).toMeasure with hP
  set cu : ℝ := 2 * volume.real ((aux_lem_prefix_limit_atom_extraction_Q0 d :
      Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) * ∑ i : Fin d, (u i) ^ 2
    with hcu
  have hcu0 : 0 ≤ cu := mul_nonneg (mul_nonneg zero_le_two
    aux_lem_prefix_limit_atom_extraction_vol_pos.le) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  set B : ℝ := max BK (cu * BR) with hB
  have hB0 : 0 ≤ B := le_max_of_le_left hBK
  -- the source bump for the (unused) killed branch
  let bump : ContDiffBump (0 : SpatialCoordinates d) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  have hbsupp : tsupport (bump : SpatialCoordinates d → ℝ) ⊆
      ((centeredCube (0 : SpatialCoordinates d) 1 one_pos : Opens (SpatialCoordinates d)) :
        Set (SpatialCoordinates d)) := by
    rw [bump.tsupport_eq]
    exact Metric.closedBall_subset_ball (by norm_num)
  have hb0 : ∃ x ∈ ((centeredCube (0 : SpatialCoordinates d) 1 one_pos :
      Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)),
      (bump : SpatialCoordinates d → ℝ) x ≠ 0 := by
    refine ⟨0, Metric.mem_ball_self (by norm_num), ?_⟩
    rw [bump.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))]
    norm_num
  have hbL2 : MemLp (bump : SpatialCoordinates d → ℝ) 2
      (volume.restrict ((centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))) :=
    MemLp.of_bound bump.continuous.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (bump.nonneg' x)]
        exact bump.le_one)
  obtain ⟨C, hC, hmain⟩ := aux_lem_prefix_limit_atom_extraction_l15_main d hd 0 1 one_pos
    aux_lem_prefix_limit_atom_extraction_poincare.1 (fun z => affineSlope u z + 0)
    ((affineSlope u).contDiff.add contDiff_const)
    (aux_lem_prefix_limit_atom_extraction_affine_nonconst u hu)
    (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0)
    (affineL2_coeFn (centeredCube_isBounded (0 : SpatialCoordinates d) one_pos) u 0)
    (bump : SpatialCoordinates d → ℝ) bump.contDiff bump.hasCompactSupport
    hbsupp hb0 (hbL2.toLp _) hbL2.coeFn_toLp t 2 B ht1 ht2 le_rfl hB0 true
  have hkappa : ∀ N, 0 < aux_lem_prefix_limit_atom_extraction_kappa M N := fun N =>
    mul_pos (Real.exp_pos _) (ahom_pos M N)
  have haN : ∀ N ω, (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N ω)).val
      =ᵐ[volume.restrict ((centeredCube (0 : SpatialCoordinates d) 1 one_pos :
        Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d))]
      (fun x => Real.exp (cutoffPotential (fun _ => 0) ω N x -
        Real.log (aux_lem_prefix_limit_atom_extraction_kappa M N))) := by
    intro N ω
    filter_upwards [expPotentialCoefficient_coeFn (aux_lem_prefix_limit_atom_extraction_pot M N ω),
      aux_lem_prefix_limit_atom_extraction_pot_ae M N ω] with x h1 h2
    rw [h1, h2]
    congr 1
    simp [cutoffPotential]
  have hmom : ∀ N,
      MemLp (K N) (ENNReal.ofReal (3 * 2)) P ∧
      MemLp (aux_lem_prefix_limit_atom_extraction_Dz M u N) (ENNReal.ofReal (3 * 2)) P ∧
      eLpNorm (K N) (ENNReal.ofReal (3 * 2)) P ≤ ENNReal.ofReal B ∧
      eLpNorm (aux_lem_prefix_limit_atom_extraction_Dz M u N) (ENNReal.ofReal (3 * 2)) P ≤
        ENNReal.ofReal B := by
    intro N
    obtain ⟨hKN, hKNb⟩ := hKmom N
    obtain ⟨hRN, hRNb⟩ := hRmom N
    have hDm : AEStronglyMeasurable (aux_lem_prefix_limit_atom_extraction_Dz M u N) P :=
      (aux_lem_prefix_limit_atom_extraction_Dz_continuous M u N).measurable.aestronglyMeasurable
    have hDle : ∀ ω, ‖aux_lem_prefix_limit_atom_extraction_Dz M u N ω‖ ≤
        ‖cu * aux_lem_prefix_limit_atom_extraction_Rf M N ω‖ := by
      intro ω
      have hD0 : 0 ≤ aux_lem_prefix_limit_atom_extraction_Dz M u N ω :=
        aux_lem_prefix_limit_atom_extraction_D_nonneg _ _
      have hRf0 : 0 ≤ aux_lem_prefix_limit_atom_extraction_Rf M N ω :=
        aux_lem_prefix_limit_atom_extraction_eval_nonneg _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hD0,
        abs_of_nonneg (mul_nonneg hcu0 hRf0)]
      exact aux_lem_prefix_limit_atom_extraction_Dz_le M u N ω
    refine ⟨hKN, hRN.const_mul cu |>.of_le hDm (Eventually.of_forall hDle),
      hKNb.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)), ?_⟩
    calc eLpNorm (aux_lem_prefix_limit_atom_extraction_Dz M u N) (ENNReal.ofReal (3 * 2)) P
        ≤ eLpNorm (fun ω => cu * aux_lem_prefix_limit_atom_extraction_Rf M N ω)
            (ENNReal.ofReal (3 * 2)) P := eLpNorm_mono hDm hDle
      _ = ENNReal.ofReal cu * eLpNorm (aux_lem_prefix_limit_atom_extraction_Rf M N)
            (ENNReal.ofReal (3 * 2)) P := by
          rw [show (fun ω => cu * aux_lem_prefix_limit_atom_extraction_Rf M N ω) =
            cu • aux_lem_prefix_limit_atom_extraction_Rf M N from rfl, eLpNorm_const_smul,
            Real.enorm_eq_ofReal hcu0]
      _ ≤ ENNReal.ofReal cu * ENNReal.ofReal BR := by gcongr
      _ = ENNReal.ofReal (cu * BR) := (ENNReal.ofReal_mul hcu0).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (le_max_right _ _)
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℝ, a0 = t * (t - (d : ℝ) + 1) / (t + 1) / (8 * Real.log 3) :=
    ⟨_, rfl⟩
  have ha0pos : 0 < a0 := by
    have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have htpos : 0 < t := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
      linarith
    have h2 : 0 < t - (d : ℝ) + 1 := by linarith
    rw [ha0]
    positivity
  refine ⟨C * M.delta, a0, (mul_pos hC hMpos).le, ha0pos, ?_⟩
  have hmain1 := hmain M.delta hMpos hM1 M.P M.G1 M.G2
    (fun _ => (0 : C(SpatialCoordinates d, ℝ))) measurable_const
    (fun j => ae_of_all _ fun _ => rfl) (aux_lem_prefix_limit_atom_extraction_kappa M) hkappa
    (fun N ω => expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N ω)) haN
  simp only [↓reduceIte] at hmain1
  have hmain2 := hmain1 K hKm hgrowth hmom
  intro N k hk
  have h := hmain2 N k hk
  have hmeas : AEStronglyMeasurable (fun q : BilateralField d × BilateralField d =>
      aux_lem_prefix_limit_atom_extraction_Dz M u N q.1 -
        aux_lem_prefix_limit_atom_extraction_Dz M u N
          (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))) (P.prod P) := by
    have hc := aux_lem_prefix_limit_atom_extraction_Dz_continuous M u N
    have hup : Continuous (fun q : BilateralField d × BilateralField d =>
        Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ)))) := by
      refine continuous_pi fun j => ?_
      by_cases hj : j = -(k : ℤ)
      · rw [hj]
        have e : (fun q : BilateralField d × BilateralField d =>
            Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))) (-(k : ℤ))) =
            fun q => q.2 (-(k : ℤ)) := by
          funext q
          exact Function.update_self _ _ _
        rw [e]
        exact (continuous_apply (-(k : ℤ))).comp continuous_snd
      · have e : (fun q : BilateralField d × BilateralField d =>
            Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))) j) = fun q => q.1 j := by
          funext q
          exact Function.update_of_ne hj _ _
        rw [e]
        exact (continuous_apply j).comp continuous_fst
    exact ((hc.comp continuous_fst).sub (hc.comp hup)).measurable.aestronglyMeasurable
  calc eLpNorm (fun q : BilateralField d × BilateralField d =>
        aux_lem_prefix_limit_atom_extraction_Dz M u N q.1 -
          aux_lem_prefix_limit_atom_extraction_Dz M u N
            (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))) 1 (P.prod P)
      ≤ eLpNorm (fun q : BilateralField d × BilateralField d =>
        aux_lem_prefix_limit_atom_extraction_Dz M u N q.1 -
          aux_lem_prefix_limit_atom_extraction_Dz M u N
            (Function.update q.1 (-(k : ℤ)) (q.2 (-(k : ℤ))))) (ENNReal.ofReal 2) (P.prod P) :=
        eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    _ ≤ ENNReal.ofReal (C * M.delta * (3 : ℝ) ^ (-a0 * (k : ℝ))) := by rw [ha0]; exact h
    _ = ENNReal.ofReal (C * M.delta * (3 : ℝ) ^ (-(a0 * (k : ℝ)))) := by rw [neg_mul]

/-- **Band estimate, Dirichlet half.** Paper `eq:mfd-16` (fine block only) for the affine Dirichlet
response of `A_N^0`, from the single-layer bound. -/
theorem aux_lem_prefix_limit_atom_extraction_band_D (d : ℕ) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (W : Lane4.SmallPerturbationInput d) (u : Fin d → ℝ) :
    ∃ delta : ℝ, 0 < delta ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta →
      ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧ ∀ H N : ℕ, H ≤ N →
        Integrable (aux_lem_prefix_limit_atom_extraction_Dz M u N) (chaosSampleLaw M).toMeasure →
        eLpNorm (fun ω => aux_lem_prefix_limit_atom_extraction_Dz M u N ω -
            ((chaosSampleLaw M).toMeasure[aux_lem_prefix_limit_atom_extraction_Dz M u N |
              bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H]) ω)
          1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
  obtain ⟨δ, hδ, hSL⟩ := aux_lem_prefix_limit_atom_extraction_single_layer_D d W u
  refine ⟨δ, hδ, ?_⟩
  intro M hM
  obtain ⟨C, a, hC, ha, hstep⟩ := hSL M hM
  have hr1 : (3 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hinv : 0 ≤ (1 - (3 : ℝ) ^ (-a))⁻¹ := inv_nonneg.mpr (by linarith)
  refine ⟨C * (1 - (3 : ℝ) ^ (-a))⁻¹, a, mul_nonneg hC hinv, ha, ?_⟩
  intro H N _hHN hint
  have hsum := aux_lem_prefix_limit_atom_extraction_band_le_sum
    (fun j : ℤ => (scaledLayerLaw d (chaosRootFieldLaw M) j : Measure C(SpatialCoordinates d, ℝ)))
    (p := 1) le_rfl ENNReal.one_ne_top (aux_lem_prefix_limit_atom_extraction_Dz M u N) hint H N
    (fun ω₁ ω₂ h => by
      unfold aux_lem_prefix_limit_atom_extraction_Dz
      rw [aux_lem_prefix_limit_atom_extraction_pot_det M N ω₁ ω₂ h])
    (fun k => ENNReal.ofReal (C * (3 : ℝ) ^ (-(a * (k : ℝ)))))
    (fun k _ hk => hstep N k hk)
  refine hsum.trans ?_
  have hnn : ∀ k : ℕ, 0 ≤ C * (3 : ℝ) ^ (-(a * (k : ℝ))) := fun k =>
    mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => hnn k]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum, mul_assoc]
  exact mul_le_mul_of_nonneg_left (aux_lem_prefix_limit_atom_extraction_geom a ha H N) hC

/-- **The crux**, from its two halves: per-direction band estimates of the affine Dirichlet and
inverse-Neumann responses of `A_N^0` on the unit cube. -/
theorem aux_lem_prefix_limit_atom_extraction_crux (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (D : lane4_deterministic_good_scale_input d) (u : Fin d → ℝ) :
    ∃ delta3 : ℝ, 0 < delta3 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta3 →
    ∀ (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
      ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧ ∀ H N : ℕ, H ≤ N →
        Integrable (aux_lem_prefix_limit_atom_extraction_Dz M u N) (chaosSampleLaw M).toMeasure →
        Integrable (aux_lem_prefix_limit_atom_extraction_Nz M u N) (chaosSampleLaw M).toMeasure →
        eLpNorm (fun ω => aux_lem_prefix_limit_atom_extraction_Dz M u N ω -
            ((chaosSampleLaw M).toMeasure[aux_lem_prefix_limit_atom_extraction_Dz M u N |
              bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H]) ω)
          1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-(a * (H : ℝ)))) ∧
        eLpNorm (fun ω => aux_lem_prefix_limit_atom_extraction_Nz M u N ω -
            ((chaosSampleLaw M).toMeasure[aux_lem_prefix_limit_atom_extraction_Nz M u N |
              bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H]) ω)
          1 (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
  obtain ⟨δD, hδD, hD⟩ := aux_lem_prefix_limit_atom_extraction_band_D d W u
  obtain ⟨δN, hδN, hN⟩ := aux_lem_prefix_limit_atom_extraction_band_N0 d hd E P X W Sf D u
  refine ⟨min δD δN, lt_min hδD hδN, ?_⟩
  intro M hM Rm Sreg It
  obtain ⟨CD, aD, hCD, haD, hbD⟩ := hD M (hM.trans (min_le_left _ _))
  obtain ⟨CN, aN, hCN, haN, hbN⟩ := hN M (hM.trans (min_le_right _ _)) Rm Sreg It
  refine ⟨CD + CN, min aD aN, add_nonneg hCD hCN, lt_min haD haN, ?_⟩
  intro H N hHN hiD hiN
  have hmono : ∀ b : ℝ, min aD aN ≤ b →
      (3 : ℝ) ^ (-(b * (H : ℝ))) ≤ (3 : ℝ) ^ (-(min aD aN * (H : ℝ))) := fun b hb =>
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by nlinarith [(Nat.cast_nonneg H : (0 : ℝ) ≤ H)])
  have h3 : ∀ b : ℝ, 0 ≤ (3 : ℝ) ^ (-(b * (H : ℝ))) := fun b =>
    Real.rpow_nonneg (by norm_num) _
  constructor
  · refine (hbD H N hHN hiD).trans (ENNReal.ofReal_le_ofReal ?_)
    have := mul_le_mul_of_nonneg_left (hmono aD (min_le_left _ _)) hCD
    nlinarith [mul_nonneg hCN (h3 (min aD aN))]
  · refine (hbN H N hHN hiN).trans (ENNReal.ofReal_le_ofReal ?_)
    have := mul_le_mul_of_nonneg_left (hmono aN (min_le_right _ _)) hCN
    nlinarith [mul_nonneg hCD (h3 (min aD aN))]

end PaeSLD

section PaeBand

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

variable {d : ℕ} [NeZero d]

/-- **H3c.** The fine-block band estimate for the unit-cube responses `Rf N = J_sup + 1`. -/
theorem aux_lem_prefix_limit_atom_extraction_band (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (D : lane4_deterministic_good_scale_input d) :
    ∃ delta2 : ℝ, 0 < delta2 ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta2 →
    ∀ (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
    ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
    (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧ ∀ H N : ℕ, H ≤ N →
        eLpNorm
          (fun ω => aux_lem_prefix_limit_atom_extraction_Rf M N ω -
            ((chaosSampleLaw M).toMeasure[aux_lem_prefix_limit_atom_extraction_Rf M N |
              bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H]) ω)
          1 (chaosSampleLaw M).toMeasure ≤
        ENNReal.ofReal (C * 1 * (3 : ℝ) ^ (-(a * (H : ℝ)))) := by
  classical
  obtain ⟨δ1, hδ1, hmom⟩ := aux_lem_prefix_limit_atom_extraction_moments d
  have hc := fun kl : Fin d × Fin d => aux_lem_prefix_limit_atom_extraction_crux d hd E P X W Sf D
    (aux_lem_prefix_limit_atom_extraction_eps kl.1 + aux_lem_prefix_limit_atom_extraction_eps kl.2)
  choose δ3 hδ3 hcr using hc
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty := Finset.univ_nonempty
  set δm := Finset.univ.inf' hne δ3 with hδm_def
  have hδm : 0 < δm := (Finset.lt_inf'_iff hne).mpr fun kl _ => hδ3 kl
  refine ⟨min δ1 δm, lt_min hδ1 hδm, ?_⟩
  intro M hM Rm Sreg It eta hEta
  obtain ⟨B, _hBtop, hB⟩ := hmom M (hM.trans (min_le_left _ _)) eta hEta
  have hM3 : ∀ kl, M.delta ≤ δ3 kl := fun kl =>
    (hM.trans (min_le_right _ _)).trans (Finset.inf'_le _ (Finset.mem_univ kl))
  choose C a hC ha hCa using fun kl => hcr kl M (hM3 kl) Rm Sreg It
  set amin := Finset.univ.inf' hne a with hamin_def
  have hamin : 0 < amin := (Finset.lt_inf'_iff hne).mpr fun kl _ => ha kl
  have hamin_le : ∀ kl, amin ≤ a kl := fun kl => Finset.inf'_le _ (Finset.mem_univ kl)
  set V : ℝ := 2 * volume.real ((aux_lem_prefix_limit_atom_extraction_Q0 d :
    Opens (SpatialCoordinates d)) : Set (SpatialCoordinates d)) with hV
  have hVpos : 0 < V := mul_pos two_pos aux_lem_prefix_limit_atom_extraction_vol_pos
  set K1 : ℝ := 2 * (d : ℝ) ^ 2 + 1 with hK1
  have hK1 : 0 ≤ K1 := by positivity
  set Csum : ℝ := ∑ kl : Fin d × Fin d, C kl with hCsum
  have hCsum0 : 0 ≤ Csum := Finset.sum_nonneg fun kl _ => hC kl
  refine ⟨2 * K1 * (V⁻¹ * (2 * Csum)), amin, by positivity, hamin, ?_⟩
  intro H N hHN
  set P := (chaosSampleLaw M).toMeasure with hP
  have hm : bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H ≤
      (MeasurableSpace.pi : MeasurableSpace (BilateralField d)) := bandSigma_le H
  -- integrability of `Rf`
  have hRf : Integrable (aux_lem_prefix_limit_atom_extraction_Rf M N) P :=
    (hB N).1.integrable (by norm_num)
  have hRf0 : ∀ ω, 0 ≤ aux_lem_prefix_limit_atom_extraction_Rf M N ω := fun ω =>
    aux_lem_prefix_limit_atom_extraction_eval_nonneg _
  -- the values `W_{ε_k + ε_l}` and their two halves
  let u : Fin d → Fin d → Fin d → ℝ := fun k l =>
    aux_lem_prefix_limit_atom_extraction_eps k + aux_lem_prefix_limit_atom_extraction_eps l
  let Dk : Fin d → Fin d → BilateralField d → ℝ := fun k l =>
    aux_lem_prefix_limit_atom_extraction_Dz M (u k l) N
  let Nk : Fin d → Fin d → BilateralField d → ℝ := fun k l =>
    aux_lem_prefix_limit_atom_extraction_Nz M (u k l) N
  let z : Fin d → Fin d → BilateralField d → ℝ := fun k l ω => (Dk k l ω + Nk k l ω) / V
  have hzW : ∀ k l ω, z k l ω = aux_lem_prefix_limit_atom_extraction_W
      (expPotentialCoefficient (aux_lem_prefix_limit_atom_extraction_pot M N ω)) (u k l) :=
    fun k l ω => rfl
  have hDm : ∀ k l, Measurable (Dk k l) := fun k l =>
    (aux_lem_prefix_limit_atom_extraction_Dz_continuous M (u k l) N).measurable
  have hNm : ∀ k l, Measurable (Nk k l) := fun k l =>
    (aux_lem_prefix_limit_atom_extraction_Nz_continuous M (u k l) N).measurable
  have hzm : ∀ k l, Measurable (z k l) := fun k l =>
    ((hDm k l).add (hNm k l)).div_const V
  have hcoef : ∀ k l, 0 ≤ ∑ i : Fin d, (u k l i) ^ 2 := fun k l =>
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hzle : ∀ k l ω, z k l ω ≤ (∑ i : Fin d, (u k l i) ^ 2) *
      aux_lem_prefix_limit_atom_extraction_Rf M N ω := fun k l ω => by
    rw [hzW]
    exact aux_lem_prefix_limit_atom_extraction_W_le_sq_eval _ _
  have hz0 : ∀ k l ω, 0 ≤ z k l ω := fun k l ω => by
    rw [hzW]
    exact aux_lem_prefix_limit_atom_extraction_W_nonneg _ _
  have hzi : ∀ k l, Integrable (z k l) P := fun k l =>
    Integrable.mono' (hRf.const_mul _) (hzm k l).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hz0 k l ω)]
        exact hzle k l ω)
  have hD0 : ∀ k l ω, 0 ≤ Dk k l ω := fun k l ω =>
    aux_lem_prefix_limit_atom_extraction_D_nonneg _ _
  have hN0 : ∀ k l ω, 0 ≤ Nk k l ω := fun k l ω =>
    aux_lem_prefix_limit_atom_extraction_N_nonneg _ _
  have hDle : ∀ k l ω, Dk k l ω ≤ V * z k l ω := fun k l ω => by
    simp only [z]
    rw [mul_div_cancel₀ _ hVpos.ne']
    linarith [hN0 k l ω]
  have hNle : ∀ k l ω, Nk k l ω ≤ V * z k l ω := fun k l ω => by
    simp only [z]
    rw [mul_div_cancel₀ _ hVpos.ne']
    linarith [hD0 k l ω]
  have hDi : ∀ k l, Integrable (Dk k l) P := fun k l =>
    Integrable.mono' ((hzi k l).const_mul V) (hDm k l).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hD0 k l ω)]
        exact hDle k l ω)
  have hNi : ∀ k l, Integrable (Nk k l) P := fun k l =>
    Integrable.mono' ((hzi k l).const_mul V) (hNm k l).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hN0 k l ω)]
        exact hNle k l ω)
  -- `Rf = Φ(z)`
  have hRfPhi : aux_lem_prefix_limit_atom_extraction_Rf M N =
      fun ω => aux_lem_prefix_limit_atom_extraction_Phi (fun k l => z k l ω) := by
    funext ω
    exact aux_lem_prefix_limit_atom_extraction_eval_eq_Phi _
  -- per-direction bounds
  have hpow : ∀ kl : Fin d × Fin d,
      (3 : ℝ) ^ (-(a kl * (H : ℝ))) ≤ (3 : ℝ) ^ (-(amin * (H : ℝ))) := fun kl =>
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (by nlinarith [hamin_le kl, (Nat.cast_nonneg H : (0 : ℝ) ≤ H)])
  have hzband : ∀ k l, eLpNorm (fun ω => z k l ω - P[z k l|bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H] ω) 1 P ≤
      ENNReal.ofReal (V⁻¹ * (2 * (C (k, l) * (3 : ℝ) ^ (-(amin * (H : ℝ)))))) := by
    intro k l
    have h := aux_lem_prefix_limit_atom_extraction_band_add_div (m := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H) (μ := P)
      (hDi k l) (hNi k l) V
    obtain ⟨hcD, hcN⟩ := hCa (k, l) H N hHN (hDi k l) (hNi k l)
    have hc0 : 0 ≤ C (k, l) * (3 : ℝ) ^ (-(a (k, l) * (H : ℝ))) :=
      mul_nonneg (hC _) (Real.rpow_nonneg (by norm_num) _)
    calc eLpNorm (fun ω => z k l ω - P[z k l|bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H] ω) 1 P
        ≤ ‖V⁻¹‖ₑ * (eLpNorm (fun ω => Dk k l ω - P[Dk k l|bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H] ω) 1 P +
            eLpNorm (fun ω => Nk k l ω - P[Nk k l|bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H] ω) 1 P) := h
      _ ≤ ENNReal.ofReal V⁻¹ * (ENNReal.ofReal (C (k, l) * (3 : ℝ) ^ (-(a (k, l) * (H : ℝ)))) +
            ENNReal.ofReal (C (k, l) * (3 : ℝ) ^ (-(a (k, l) * (H : ℝ))))) := by
          rw [Real.enorm_eq_ofReal (inv_nonneg.mpr hVpos.le)]
          exact mul_le_mul_right (add_le_add hcD hcN) _
      _ ≤ ENNReal.ofReal (V⁻¹ * (2 * (C (k, l) * (3 : ℝ) ^ (-(amin * (H : ℝ)))))) := by
          rw [← ENNReal.ofReal_add hc0 hc0, ← ENNReal.ofReal_mul (inv_nonneg.mpr hVpos.le)]
          apply ENNReal.ofReal_le_ofReal
          have := mul_le_mul_of_nonneg_left (hpow (k, l)) (hC (k, l))
          have hVi : 0 ≤ V⁻¹ := inv_nonneg.mpr hVpos.le
          nlinarith [mul_le_mul_of_nonneg_left this hVi]
  have hΦ := aux_lem_prefix_limit_atom_extraction_band_Phi (m := bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H) (μ := P) hm z hzm hzi
  refine le_trans (le_of_eq ?_) (hΦ.trans ?_)
  · rw [hRfPhi]
  have hsum : ∑ k : Fin d, ∑ l : Fin d, eLpNorm (fun ω => z k l ω - P[z k l|bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H] ω) 1 P ≤
      ENNReal.ofReal (V⁻¹ * (2 * (Csum * (3 : ℝ) ^ (-(amin * (H : ℝ)))))) := by
    calc ∑ k : Fin d, ∑ l : Fin d, eLpNorm (fun ω => z k l ω - P[z k l|bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H] ω) 1 P
        ≤ ∑ k : Fin d, ∑ l : Fin d,
            ENNReal.ofReal (V⁻¹ * (2 * (C (k, l) * (3 : ℝ) ^ (-(amin * (H : ℝ)))))) :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hzband k l
      _ = ENNReal.ofReal (∑ k : Fin d, ∑ l : Fin d,
            V⁻¹ * (2 * (C (k, l) * (3 : ℝ) ^ (-(amin * (H : ℝ)))))) := by
          have hnn : ∀ k l : Fin d,
              0 ≤ V⁻¹ * (2 * (C (k, l) * (3 : ℝ) ^ (-(amin * (H : ℝ))))) := fun k l => by
            have := hC (k, l)
            have := Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) (-(amin * (H : ℝ)))
            have := inv_nonneg.mpr hVpos.le
            positivity
          rw [ENNReal.ofReal_sum_of_nonneg fun k _ => Finset.sum_nonneg fun l _ => hnn k l]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ENNReal.ofReal_sum_of_nonneg fun l _ => hnn k l]
      _ = ENNReal.ofReal (V⁻¹ * (2 * (Csum * (3 : ℝ) ^ (-(amin * (H : ℝ)))))) := by
          congr 1
          rw [hCsum, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  calc 2 * (ENNReal.ofReal K1 *
        ∑ k : Fin d, ∑ l : Fin d, eLpNorm (fun ω => z k l ω - P[z k l|bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) H] ω) 1 P)
      ≤ 2 * (ENNReal.ofReal K1 *
          ENNReal.ofReal (V⁻¹ * (2 * (Csum * (3 : ℝ) ^ (-(amin * (H : ℝ))))))) := by
        gcongr
    _ = ENNReal.ofReal (2 * K1 * (V⁻¹ * (2 * Csum)) * 1 * (3 : ℝ) ^ (-(amin * (H : ℝ)))) := by
        have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
        have hVi : 0 ≤ V⁻¹ := inv_nonneg.mpr hVpos.le
        have h3 : 0 ≤ (3 : ℝ) ^ (-(amin * (H : ℝ))) := Real.rpow_nonneg (by norm_num) _
        rw [h2, ← ENNReal.ofReal_mul hK1, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

end PaeBand

section PaeUnit

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

variable {d : ℕ}

/-- The chaos sample law is the product of the scaled layer laws. -/
theorem aux_lem_prefix_limit_atom_extraction_law_eq
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    (chaosSampleLaw M).toMeasure =
      Measure.infinitePi (fun j : ℤ =>
        (scaledLayerLaw d (chaosRootFieldLaw M) j : Measure C(SpatialCoordinates d, ℝ))) :=
  rfl

/-- **H3.** `L¹` relative compactness of the unit-cube zero-infrared responses. -/
theorem aux_lem_prefix_limit_atom_extraction_unit_compact (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (D : lane4_deterministic_good_scale_input d) :
    ∃ deltaA : ℝ, 0 < deltaA ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ deltaA →
    ∀ (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
    ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
    (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
      ∃ hmem : ∀ N, MemLp (aux_lem_prefix_limit_atom_extraction_Rf M N) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range fun N =>
          (hmem N).toLp (aux_lem_prefix_limit_atom_extraction_Rf M N))) := by
  obtain ⟨delta1, hd1, hmom⟩ := aux_lem_prefix_limit_atom_extraction_moments d
  obtain ⟨delta2, hd2, hband⟩ := aux_lem_prefix_limit_atom_extraction_band d hd E P X W Sf D
  refine ⟨min delta1 delta2, lt_min hd1 hd2, ?_⟩
  intro M hM Rm Sreg It eta hEta
  obtain ⟨B, hBtop, hB⟩ := hmom M (hM.trans (min_le_left _ _)) eta hEta
  obtain ⟨C, a, hC, ha, hCband⟩ := hband M (hM.trans (min_le_right _ _)) Rm Sreg It eta hEta
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) := fun j =>
    (scaledLayerLaw d (chaosRootFieldLaw M) j : Measure C(SpatialCoordinates d, ℝ))
  have hlaw : (chaosSampleLaw M).toMeasure = Measure.infinitePi laws := rfl
  haveI : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  have hmem2 : ∀ (i : Unit) (N : ℕ), MemLp (fun ω => aux_lem_prefix_limit_atom_extraction_Rf M N ω)
      2 (Measure.infinitePi laws) := fun _ N => (hB N).1
  have hRes := prop_response_compact d (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) laws Unit Empty
    (fun _ N ω => aux_lem_prefix_limit_atom_extraction_Rf M N ω) (fun w => Empty.elim w)
    1 2 (by norm_num) (by norm_num) a 1 ha one_pos (fun _ => C) (fun _ => hC) (fun _ => B)
    (fun _ => hBtop) hmem2 (fun _ N => (hB N).2)
    (fun _ H N hHN => hCband H N hHN) (fun _ H => aux_lem_prefix_limit_atom_extraction_split d M H)
    (fun w => Empty.elim w) (fun w => Empty.elim w) (fun w => Empty.elim w)
  obtain ⟨hcomp, -⟩ := hRes
  exact ⟨fun N => ((hmem2 () N).mono_exponent (by norm_num)), hcomp ()⟩

end PaeUnit

section PaeG5

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology

variable {d : ℕ}

theorem aux_lem_prefix_limit_atom_extraction_shift_measurable
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (l : ℤ) (y : SpatialCoordinates d) :
    Measurable (aux_lem_prefix_limit_atom_extraction_shift (d := d) l y) := by
  have hc : Measurable fun f : C(SpatialCoordinates d, ℝ) =>
      f.comp (aux_lem_prefix_limit_atom_extraction_affine l y) := by fun_prop
  exact measurable_pi_lambda fun j => hc.comp (measurable_pi_apply (j + l))

/-- **H2.** The scale-and-translation relabelling preserves the chaos sample law, for every
integer depth `l` and centre `y` (root stationarity and independence of the layers).
PROVENANCE: port of `lem_as_coarse_shallow_grid_scale_shift` (depth `k : ℕ`, `l = -k`). -/
theorem aux_lem_prefix_limit_atom_extraction_shift_mp
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (l : ℤ) (y : SpatialCoordinates d) :
    MeasurePreserving (aux_lem_prefix_limit_atom_extraction_shift l y)
      (chaosSampleLaw model).toMeasure (chaosSampleLaw model).toMeasure := by
  set D := aux_lem_prefix_limit_atom_extraction_affine (d := d) l y with hD
  set ν := chaosRootFieldLaw model with hν
  let laws : ℤ → Measure C(SpatialCoordinates d, ℝ) :=
    fun j => (scaledLayerLaw d ν j).toMeasure
  have hroot : ∀ z : SpatialCoordinates d, MeasurePreserving
      (fun f : C(SpatialCoordinates d, ℝ) =>
        f.comp (⟨fun x => x + z, continuous_id.add continuous_const⟩ :
          C(SpatialCoordinates d, SpatialCoordinates d)))
      ν.toMeasure ν.toMeasure := by
    intro z
    simpa [hν, chaosRootFieldLaw] using (gmc_zero_field_law_stationary model z)
  have hcompD : Measurable fun f : C(SpatialCoordinates d, ℝ) => f.comp D := by fun_prop
  have hlayer : ∀ j : ℤ,
      Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp D) (laws (j + l)) =
        laws j := by
    intro j
    let z : SpatialCoordinates d := (3 : ℝ) ^ (-(j + l)) • y
    let translateZ : C(SpatialCoordinates d, SpatialCoordinates d) :=
      ⟨fun x => x + z, continuous_id.add continuous_const⟩
    have hpow : (3 : ℝ) ^ (-(j + l)) * (3 : ℝ) ^ l = (3 : ℝ) ^ (-j) := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      ring
    have hcomm :
        (fun f : C(SpatialCoordinates d, ℝ) => f.comp D) ∘ (layerScaling d (j + l)) =
          (layerScaling d j) ∘
            (fun f : C(SpatialCoordinates d, ℝ) => f.comp translateZ) := by
      funext f
      ext x
      dsimp [ContinuousMap.compRightContinuousMap, layerScaling, ContinuousMap.comp,
        hD, aux_lem_prefix_limit_atom_extraction_affine, translateZ, z]
      congr 1
      ext i
      rw [hD]
      simp only [aux_lem_prefix_limit_atom_extraction_affine, ContinuousMap.coe_mk,
        Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      rw [mul_add, ← mul_assoc, hpow]
      ring
    change Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp D)
        (Measure.map (layerScaling d (j + l)) ν.toMeasure) =
      Measure.map (layerScaling d j) ν.toMeasure
    calc
      Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp D)
          (Measure.map (layerScaling d (j + l)) ν.toMeasure) =
          Measure.map ((fun f : C(SpatialCoordinates d, ℝ) => f.comp D) ∘
            layerScaling d (j + l)) ν.toMeasure :=
        Measure.map_map hcompD (layerScaling d (j + l)).continuous.measurable
      _ = Measure.map ((layerScaling d j) ∘
            (fun f : C(SpatialCoordinates d, ℝ) => f.comp translateZ)) ν.toMeasure := by
        rw [hcomm]
      _ = Measure.map (layerScaling d j)
          (Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp translateZ)
            ν.toMeasure) :=
        (Measure.map_map (layerScaling d j).continuous.measurable (by fun_prop)).symm
      _ = Measure.map (layerScaling d j) ν.toMeasure := by
        rw [(hroot z).map_eq]
  have hre : Measure.map (fun (ω : ℤ → C(SpatialCoordinates d, ℝ)) (j : ℤ) => ω (j + l))
      (Measure.infinitePi laws) = Measure.infinitePi (fun j => laws (j + l)) := by
    have h := Measure.infinitePi_map_piCongrLeft (fun j : ℤ => laws (j + l))
      (Equiv.addRight (-l))
    have e1 : (fun a : ℤ => (fun j : ℤ => laws (j + l)) (Equiv.addRight (-l) a)) =
        laws := by
      funext a
      simp
    have e2 : ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℤ => C(SpatialCoordinates d, ℝ))
        (Equiv.addRight (-l))) =
        fun (ω : ℤ → C(SpatialCoordinates d, ℝ)) (j : ℤ) => ω (j + l) := by
      funext ω j
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      rw [← heq_iff_eq, eqRec_heq_iff]
      simp
    rw [e1, e2] at h
    exact h
  have hco := Measure.infinitePi_map_pi (μ := fun j => laws (j + l))
    (f := fun _ : ℤ => fun f : C(SpatialCoordinates d, ℝ) => f.comp D) (fun _ => hcompD)
  refine ⟨aux_lem_prefix_limit_atom_extraction_shift_measurable l y, ?_⟩
  have hsplit : aux_lem_prefix_limit_atom_extraction_shift (d := d) l y =
      (fun (x : ℤ → C(SpatialCoordinates d, ℝ)) (i : ℤ) => (x i).comp D) ∘
        (fun (ω : ℤ → C(SpatialCoordinates d, ℝ)) (j : ℤ) => ω (j + l)) := rfl
  change Measure.map (aux_lem_prefix_limit_atom_extraction_shift l y)
      (Measure.infinitePi laws) = Measure.infinitePi laws
  have hg : Measurable (fun (x : ℤ → C(SpatialCoordinates d, ℝ)) (i : ℤ) => (x i).comp D) :=
    measurable_pi_lambda fun i => hcompD.comp (measurable_pi_apply i)
  have hf : Measurable (fun (ω : ℤ → C(SpatialCoordinates d, ℝ)) (j : ℤ) => ω (j + l)) :=
    measurable_pi_lambda fun j => measurable_pi_apply (j + l)
  have hco' : Measure.map (fun (x : ℤ → C(SpatialCoordinates d, ℝ)) (i : ℤ) => (x i).comp D)
      (Measure.infinitePi fun j => laws (j + l)) =
      Measure.infinitePi fun i => Measure.map (fun f : C(SpatialCoordinates d, ℝ) => f.comp D)
        (laws (i + l)) := hco
  rw [hsplit, ← Measure.map_map hg hf, hre, hco']
  congr 1
  funext j
  exact hlayer j

/-- **Transfer.** `L¹` relative compactness passes from a family `G` to any family that agrees
a.e. with `G ∘ T - 1` along the index shift `N ↦ l + N` (and vanishes before it), when `T` is
measure preserving. -/
theorem aux_lem_prefix_limit_atom_extraction_transfer
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (G : ℕ → Ω → ℝ) (hG : ∀ n, MemLp (G n) 1 μ)
    (hGc : IsCompact (closure (Set.range fun n => (hG n).toLp (G n))))
    (l : ℤ) (f : ℕ → Ω → ℝ)
    (hf : ∀ N : ℕ, 0 ≤ l + (N : ℤ) →
      f N =ᵐ[μ] fun ω => G (l + (N : ℤ)).toNat (T ω) - 1)
    (hf0 : ∀ N : ℕ, ¬ 0 ≤ l + (N : ℤ) → f N = 0) :
    ∃ hmem : ∀ N, MemLp (f N) 1 μ,
      IsCompact (closure (Set.range fun N => (hmem N).toLp (f N))) := by
  classical
  have hone : MemLp (fun _ : Ω => (1 : ℝ)) 1 μ := memLp_const 1
  have hGT : ∀ n, MemLp (fun ω => G n (T ω) - 1) 1 μ := fun n =>
    ((hG n).comp_measurePreserving hT).sub hone
  have hmem : ∀ N, MemLp (f N) 1 μ := by
    intro N
    by_cases hN : 0 ≤ l + (N : ℤ)
    · exact (hGT _).ae_eq (hf N hN).symm
    · rw [hf0 N hN]
      exact MemLp.zero
  refine ⟨hmem, ?_⟩
  let c : Lp ℝ 1 μ := hone.toLp _
  let Φ : Lp ℝ 1 μ → Lp ℝ 1 μ := fun g => Lp.compMeasurePreserving T hT g - c
  have hΦ : Continuous Φ :=
    (Lp.isometry_compMeasurePreserving hT).continuous.sub continuous_const
  let K : Set (Lp ℝ 1 μ) := Φ '' closure (Set.range fun n => (hG n).toLp (G n)) ∪ {0}
  have hK : IsCompact K := (hGc.image hΦ).union isCompact_singleton
  have hsub : Set.range (fun N => (hmem N).toLp (f N)) ⊆ K := by
    rintro _ ⟨N, rfl⟩
    by_cases hN : 0 ≤ l + (N : ℤ)
    · left
      refine ⟨(hG _).toLp (G (l + (N : ℤ)).toNat), subset_closure ⟨_, rfl⟩, ?_⟩
      simp only [Φ, c]
      rw [Lp.toLp_compMeasurePreserving, ← MemLp.toLp_sub]
      exact MemLp.toLp_congr _ _ (hf N hN).symm
    · right
      rw [Set.mem_singleton_iff]
      have h0 : f N =ᵐ[μ] (0 : Ω → ℝ) := by rw [hf0 N hN]
      show (hmem N).toLp (f N) = 0
      rw [MemLp.toLp_congr (hmem N) MemLp.zero h0]
      exact MemLp.toLp_zero _
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hK.isClosed)

/-- **G5.** Per-atom `L¹` relative compactness of the zero-infrared atoms. -/
theorem aux_lem_prefix_limit_atom_extraction_compact (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : Lane4.SmallPerturbationInput d) (Sf : Lane4.SobolevFoundationalInput d hd)
    (D : lane4_deterministic_good_scale_input d) :
    ∃ deltaA : ℝ, 0 < deltaA ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ deltaA →
    ∀ (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M E Sreg),
    ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
    (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
    ∀ (l : ℤ) (y : Vec d),
      ∃ hmem : ∀ N, MemLp (aux_lem_prefix_limit_atom_extraction_atom M eta N l y) 1
          (chaosSampleLaw M).toMeasure,
        IsCompact (closure (Set.range fun N =>
          (hmem N).toLp (aux_lem_prefix_limit_atom_extraction_atom M eta N l y))) := by
  obtain ⟨deltaA, hdA, hunit⟩ :=
    aux_lem_prefix_limit_atom_extraction_unit_compact d hd E P X W Sf D
  refine ⟨deltaA, hdA, ?_⟩
  intro M hM Rm Sreg It eta hEta l y
  obtain ⟨hG, hGc⟩ := hunit M hM Rm Sreg It eta hEta
  have hcar := aux_lem_prefix_limit_atom_extraction_carrier M eta hEta l y
  refine aux_lem_prefix_limit_atom_extraction_transfer
    (aux_lem_prefix_limit_atom_extraction_shift l y)
    (aux_lem_prefix_limit_atom_extraction_shift_mp M l y)
    (aux_lem_prefix_limit_atom_extraction_Rf M) hG hGc l
    (fun N => aux_lem_prefix_limit_atom_extraction_atom M eta N l y) ?_ ?_
  · intro N hN
    filter_upwards [hcar] with omega homega
    exact homega N hN
  · intro N hN
    funext omega
    simp [aux_lem_prefix_limit_atom_extraction_atom, hN]

/-- **G4.** Joint extraction inside a prescribed subsequence from per-index `L¹` relative
compactness, for countably many indices. -/
theorem aux_lem_prefix_limit_atom_extraction_subseq
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {κ : Type} [Countable κ] (X : κ → ℕ → Ω → ℝ)
    (hcomp : ∀ k, ∃ hmem : ∀ N, MemLp (X k N) 1 μ,
      IsCompact (closure (Set.range fun N => (hmem N).toLp (X k N))))
    (phi : ℕ → ℕ) :
    ∃ psi : ℕ → ℕ, StrictMono psi ∧
      ∀ k, ∃ lim : Ω → ℝ, TendstoInMeasure μ (fun i => X k (phi (psi i))) atTop lim := by
  classical
  choose hmem hK using hcomp
  obtain ⟨psi, hpsi, hlim⟩ := aux_countable_compact_subseq
    (fun k => closure (Set.range fun N => (hmem k N).toLp (X k N))) hK
    (fun k n => (hmem k (phi n)).toLp (X k (phi n)))
    (fun k n => subset_closure ⟨phi n, rfl⟩)
  refine ⟨psi, hpsi, fun k => ?_⟩
  obtain ⟨g, hg⟩ := hlim k
  refine ⟨(g : Ω → ℝ), ?_⟩
  have h := aux_raw_tendsto_of_lp (p := 1) (f := fun i => X k (phi (psi i)))
    (fun i => hmem k (phi (psi i))) hg
  exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero h

/-- Joint extraction, inside every prescribed cutoff subsequence, of the zero-infrared
response atoms read by the raw prefix scores (paper 1699--1725 as used at 2749--2751). -/
theorem lem_prefix_limit_atom_extraction
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : Paper.in_J d)
    (_Poincare : Paper.in_poincare d hd I)
    (_Extension : Paper.in_extension d hd I)
    (_Perturbation : Lane4.SmallPerturbationInput d)
    (_Sobolev : Lane4.SobolevFoundationalInput d hd)
    (D : Paper.lane4_deterministic_good_scale_input d) :
    ∃ deltaA : ℝ, 0 < deltaA ∧
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ deltaA →
    ∀ (Rm : Paper.in_responses d M) (Sreg : Paper.in_6_16 d M)
      (It : Paper.in_iteration d M I Sreg),
    ∀ (eta : ℕ → BilateralField d → SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d),
    (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      ∀ (N i : ℕ) (y : Vec d), eta N omega i y =
        omega ((i : ℤ) - (N : ℤ)) ((3 : ℝ) ^ (-(N : ℤ)) • y)) →
    ∀ (Pos : Type) [Countable Pos] (centre : Pos → SpatialCoordinates d)
      (phi : ℕ → ℕ), StrictMono phi →
    ∃ psi : ℕ → ℕ, StrictMono psi ∧
      ∀ (pos : Pos) (l : ℤ) (k : Fin d → ℤ), ∃ lim : BilateralField d → ℝ,
        TendstoInMeasure (chaosSampleLaw M).toMeasure
          (fun i omega =>
            if 0 ≤ l + ((phi (psi i) : ℕ) : ℤ) then
              (aux_psf_Jval M (l + ((phi (psi i) : ℕ) : ℤ)).toNat (eta (phi (psi i)) omega)
                ((3 : ℝ) ^ (phi (psi i)) •
                  (centre pos + (3 : ℝ) ^ l • (fun c => ((k c : ℤ) : ℝ))))).toReal
            else 0) atTop lim := by
  obtain ⟨deltaA, hdA, hcomp⟩ := aux_lem_prefix_limit_atom_extraction_compact d hd I _Poincare
    _Extension _Perturbation _Sobolev D
  refine ⟨deltaA, hdA, ?_⟩
  intro M hM Rm Sreg It eta hEta Pos _ centre phi _hphi
  obtain ⟨psi, hpsi, hlim⟩ := aux_lem_prefix_limit_atom_extraction_subseq
    (μ := (chaosSampleLaw M).toMeasure) (κ := Pos × ℤ × (Fin d → ℤ))
    (fun kk N => aux_lem_prefix_limit_atom_extraction_atom M eta N kk.2.1
      (centre kk.1 + (3 : ℝ) ^ kk.2.1 • (fun c => ((kk.2.2 c : ℤ) : ℝ))))
    (fun kk => hcomp M hM Rm Sreg It eta hEta kk.2.1 _) phi
  exact ⟨psi, hpsi, fun pos l k => hlim (pos, l, k)⟩

end PaeG5

end Paper
