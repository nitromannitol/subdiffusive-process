module

public import SubdiffusiveProcess.Lane2.LimitForm
public import SubdiffusiveProcess.Geometry.Cube
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredPartialSum
public import SubdiffusiveProcess.Main.CutoffCoefficient
public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn
public import Mathlib.Tactic
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.TestSubmodule
public import SubdiffusiveProcess.Lane4.Inputs
public import Mathlib.Analysis.Matrix.Normed
public import SubdiffusiveProcess.Lane3.RelativeConcentration
public import SubdiffusiveProcess.Sobolev.CompactResponses
public import SubdiffusiveProcess.Main.CommonScaleLaw
public import Mathlib.Probability.ProductMeasure
public import SubdiffusiveProcess.Sobolev.ReflectionResponses
public import SubdiffusiveProcess.Lane4.Scaling
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletMatrixBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DirichletInfimumCovariance
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.CellSymmetry.AffineQuadratic
public import SubdiffusiveProcess.CellSymmetry.Invariance

@[expose] public section




open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology BigOperators Pointwise ContDiff Distributions

noncomputable section
namespace SubdiffusiveProcess
namespace CellSymmetry


/-- Factor an actual matrix limit through the canonical field. This needs
neither a completed probability space nor a catalogue outside the cell. -/
theorem cs_matrix_limit_factor
    {d : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (μ : Measure Ξ) (field : Ω → Ξ)
    (hfield : Measurable field) (hlaw : P.map field = μ)
    (A : ℕ → Ξ → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ n, Measurable (A n)) (L : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hlim : ∀ᵐ om ∂P, Tendsto (fun n => A n (field om)) atTop (𝓝 (L om))) :
    ∃ g : Ξ → Matrix (Fin d) (Fin d) ℝ, Measurable g ∧
      (∀ᵐ om ∂P, g (field om) = L om) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => A n x) atTop (𝓝 (g x)) := by
  letI : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))
  letI : TopologicalSpace.IsCompletelyMetrizableSpace (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyMetrizableSpace (Fin d → Fin d → ℝ))
  letI : SecondCountableTopology (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  let g : Ξ → Matrix (Fin d) (Fin d) ℝ :=
    fun x => limUnder atTop (fun n => A n x)
  have hg : Measurable g :=
    (StronglyMeasurable.limUnder (fun n => (hA n).stronglyMeasurable)).measurable
  have heq : ∀ᵐ om ∂P, g (field om) = L om :=
    hlim.mono fun _ h => h.limUnder_eq
  refine ⟨g, hg, heq, ?_⟩
  rw [← hlaw, ae_map_iff hfield.aemeasurable (measurableSet_tendsto_fun hA hg)]
  filter_upwards [hlim, heq] with om h he
  rwa [he]

/-- A common infrared gauge cancels after passing a cell's matrix responses
to their genuine limits. The normalization is only required to be measurable;
no continuity at singular matrices and no off-event equivariance is assumed. -/
theorem cs_matrix_pair_law
    {d : ℕ} {Ω Ξ Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Y]
    (P : Measure Ω) (μ : Measure Ξ) (field : Ω → Ξ)
    (hfield : Measurable field) (hlaw : P.map field = μ)
    (T : Ξ → Ξ) (hT : MeasurePreserving T μ μ)
    (A B : ℕ → Ξ → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hAE : ∀ᵐ om ∂P, Tendsto (fun n => A n (field om)) atTop (𝓝 (AE om)))
    (hAF : ∀ᵐ om ∂P, Tendsto (fun n => B n (field om)) atTop (𝓝 (AF om)))
    (L : Matrix (Fin d) (Fin d) ℝ →L[ℝ] Matrix (Fin d) (Fin d) ℝ)
    (c : Ξ → ℝ)
    (hcov : ∀ᵐ x ∂μ, c x ≠ 0 ∧ ∀ n,
      A n (T x) = c x • L (A n x) ∧ B n (T x) = c x • L (B n x))
    (N : (Matrix (Fin d) (Fin d) ℝ × Matrix (Fin d) (Fin d) ℝ) → Y)
    (hN : Measurable N) (S : Y → Y) (hS : Measurable S)
    (hscale : ∀ (a b : Matrix (Fin d) (Fin d) ℝ) (t : ℝ), t ≠ 0 →
      N (t • a, t • b) = N (a, b))
    (htransform : ∀ a b, N (L a, L b) = S (N (a, b))) :
    P.map (fun om => N (AE om, AF om)) =
      P.map (fun om => S (N (AE om, AF om))) := by
  obtain ⟨gE, hmE, heE, hlE⟩ :=
    cs_matrix_limit_factor P μ field hfield hlaw A hA AE hAE
  obtain ⟨gF, hmF, heF, hlF⟩ :=
    cs_matrix_limit_factor P μ field hfield hlaw B hB AF hAF
  have hequiv : ∀ᵐ x ∂μ, N (gE (T x), gF (T x)) = S (N (gE x, gF x)) := by
    filter_upwards [hlE, hlF, hT.quasiMeasurePreserving.ae hlE,
      hT.quasiMeasurePreserving.ae hlF, hcov] with x hE hF hET hFT hc
    have hgE : gE (T x) = c x • L (gE x) :=
      tendsto_nhds_unique hET
        (((L.continuous.tendsto _).comp hE).const_smul (c x) |>.congr
          fun n => (hc.2 n).1.symm)
    have hgF : gF (T x) = c x • L (gF x) :=
      tendsto_nhds_unique hFT
        (((L.continuous.tendsto _).comp hF).const_smul (c x) |>.congr
          fun n => (hc.2 n).2.symm)
    rw [hgE, hgF, hscale _ _ _ hc.1, htransform]
  have hm : Measurable (fun x => N (gE x, gF x)) := hN.comp (hmE.prodMk hmF)
  have hmS : Measurable (fun x => S (N (gE x, gF x))) := hS.comp hm
  have heq : (fun om => N (AE om, AF om)) =ᵐ[P]
      (fun x => N (gE x, gF x)) ∘ field := by
    filter_upwards [heE, heF] with om hE hF
    simp only [Function.comp_apply, hE, hF]
  have heqS : (fun om => S (N (AE om, AF om))) =ᵐ[P]
      (fun x => S (N (gE x, gF x))) ∘ field := by
    filter_upwards [heq] with om h
    exact congrArg S h
  rw [Measure.map_congr heq, Measure.map_congr heqS,
    ← Measure.map_map hm hfield, ← Measure.map_map hmS hfield, hlaw]
  calc
    μ.map (fun x => N (gE x, gF x)) =
        μ.map ((fun x => N (gE x, gF x)) ∘ T) := by
      rw [← Measure.map_map hm hT.measurable, hT.map_eq]
    _ = μ.map (fun x => S (N (gE x, gF x))) := Measure.map_congr hequiv

/-- The polarization matrix of a scalar quadratic response. -/
def cs_polar_matrix {d : ℕ} (R : (Fin d → ℝ) → ℝ) :
    Matrix (Fin d) (Fin d) ℝ := fun i j =>
  (R (Pi.single i 1 + Pi.single j 1) - R (Pi.single i 1) - R (Pi.single j 1)) / 2

theorem cs_polar_matrix_symmetric {d : ℕ} (R : (Fin d → ℝ) → ℝ) :
    (cs_polar_matrix R).transpose = cs_polar_matrix R := by
  ext i j
  change (R (Pi.single j 1 + Pi.single i 1) - R (Pi.single j 1) - R (Pi.single i 1)) / 2 = _
  rw [add_comm (Pi.single j (1 : ℝ) : Fin d → ℝ) (Pi.single i 1)]
  unfold cs_polar_matrix
  ring

theorem cs_polar_matrix_of_quadratic {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.transpose = A) :
    cs_polar_matrix (fun p => p ⬝ᵥ A.mulVec p) = A := by
  ext i j
  unfold cs_polar_matrix
  simp only [cs_matrix_quadratic_eq]
  exact cs_matrix_polarization A
    (fun a b => (congrFun (congrFun hA a) b).symm) i j

theorem cs_symmetric_matrix_ext {d : ℕ}
    {A B : Matrix (Fin d) (Fin d) ℝ} (hA : A.transpose = A) (hB : B.transpose = B)
    (h : ∀ p : Fin d → ℝ, p ⬝ᵥ A.mulVec p = p ⬝ᵥ B.mulVec p) : A = B := by
  rw [← cs_polar_matrix_of_quadratic A hA,
    ← cs_polar_matrix_of_quadratic B hB]
  exact congrArg cs_polar_matrix (funext h)

theorem cs_polar_matrix_measurable {d : ℕ}
    {Ξ : Type*} [MeasurableSpace Ξ] (R : Ξ → (Fin d → ℝ) → ℝ)
    (hR : ∀ p, Measurable (fun x => R x p)) :
    Measurable (fun x => cs_polar_matrix (R x)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (((hR (Pi.single i 1 + Pi.single j 1)).sub (hR (Pi.single i 1))).sub
    (hR (Pi.single j 1))).div_const 2

theorem cs_polar_matrix_limit {d : ℕ}
    (R : ℕ → (Fin d → ℝ) → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A)
    (hR : ∀ p, Tendsto (fun n => R n p) atTop (𝓝 (p ⬝ᵥ A.mulVec p))) :
    Tendsto (fun n => cs_polar_matrix (R n)) atTop (𝓝 A) := by
  rw [← cs_polar_matrix_of_quadratic A hA]
  exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j =>
    (((hR (Pi.single i 1 + Pi.single j 1)).sub (hR (Pi.single i 1))).sub
      (hR (Pi.single j 1))).div_const 2

/-- The literal volume-normalized finite-cutoff matrix at one physical cell. -/
def cs_cutoff_affine_matrix {d : ℕ}
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (N : ℕ) (om : BilateralField d) : Matrix (Fin d) (Fin d) ℝ :=
  cs_polar_matrix fun p =>
    affineDirichletResponse (centeredCube_isBounded z hr) hP
      (Lane4.cutoffPositiveCoefficient model H om N z hr) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal

theorem cs_cutoff_affine_matrix_measurable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : Measurable H)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (N : ℕ) :
    Measurable (cs_cutoff_affine_matrix model H z hr hP N) :=
  cs_polar_matrix_measurable _ fun p =>
    (cs_affine_response_measurable model H hH N z hr hP p).div_const _

theorem cs_cutoff_affine_matrix_quadratic {d : ℕ}
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (N : ℕ) (om : BilateralField d) (p : Fin d → ℝ) :
    p ⬝ᵥ (cs_cutoff_affine_matrix model H z hr hP N om).mulVec p =
      affineDirichletResponse (centeredCube_isBounded z hr) hP
        (Lane4.cutoffPositiveCoefficient model H om N z hr) p /
          (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal := by
  obtain ⟨A, hsym, hquad⟩ := cs_dirichlet_quadratic
    (centeredCube_isBounded z hr) hP (Lane4.cutoffPositiveCoefficient model H om N z hr)
  let v : ℝ := (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal
  let B : Matrix (Fin d) (Fin d) ℝ := fun i j => A i j / v
  have hB : B.transpose = B := by
    ext i j
    exact congrArg (fun x => x / v) (hsym j i)
  have hR : ∀ q : Fin d → ℝ,
      affineDirichletResponse (centeredCube_isBounded z hr) hP
          (Lane4.cutoffPositiveCoefficient model H om N z hr) q / v = q ⬝ᵥ B.mulVec q := by
    intro q
    rw [hquad, cs_matrix_quadratic_eq]
    simp only [Finset.sum_div, B, div_mul_eq_mul_div]
  have hmatrix : cs_cutoff_affine_matrix model H z hr hP N om = B := by
    change cs_polar_matrix
      (fun q => affineDirichletResponse (centeredCube_isBounded z hr) hP
        (Lane4.cutoffPositiveCoefficient model H om N z hr) q / v) = B
    rw [funext hR, cs_polar_matrix_of_quadratic B hB]
  rw [hmatrix]
  exact (hR p).symm

/-- Sign of the reflection in coordinate `i`. -/
def cs_lc_sign {d : ℕ} (i j : Fin d) : ℝ := if j = i then -(1 : ℝ) else 1

/-- The trace-normalized pair `(A_E/tr A_E, A_F/tr A_E)`, as plain arrays. -/
def cs_lc_normpair {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ) :
    (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) :=
  (fun j l => A j l / Matrix.trace A, fun j l => B j l / Matrix.trace A)

/-- Conjugation of a pair of arrays by the reflection in coordinate `i`. -/
def cs_lc_reflpair {d : ℕ} (i : Fin d)
    (XY : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) :
    (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) :=
  (fun j l => cs_lc_sign i j * cs_lc_sign i l * XY.1 j l,
    fun j l => cs_lc_sign i j * cs_lc_sign i l * XY.2 j l)

/-- Conjugation of a pair of arrays by a coordinate permutation. -/
def cs_lc_permpair {d : ℕ} (σ : Equiv.Perm (Fin d))
    (XY : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) :
    (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) :=
  (fun j l => XY.1 (σ j) (σ l), fun j l => XY.2 (σ j) (σ l))

section
variable {Ω : Type} [MeasurableSpace Ω]

/-- Hyperoctahedral invariance of the law of the normalized pair forces the mean of
the centred matrix to vanish (paper lines 3466-3474). -/
theorem cs_lc_mean_zero {d : ℕ} (hd : 0 < d) (P : Measure Ω)
    [IsProbabilityMeasure P]
    (AE AF : Ω → Matrix (Fin d) (Fin d) ℝ) (ck : ℝ)
    (hmeasE : ∀ j l, AEStronglyMeasurable (fun omega => AE omega j l) P)
    (hmeasF : ∀ j l, AEStronglyMeasurable (fun omega => AF omega j l) P)
    (hint : ∀ j l, Integrable (fun omega => ((Matrix.trace (AE omega))⁻¹ • (AF omega - ck • AE omega)) j l) P)
    (htrace : ∫ omega, Matrix.trace ((Matrix.trace (AE omega))⁻¹ • (AF omega - ck • AE omega)) ∂P = 0)
    (hrefl : ∀ i : Fin d,
      Measure.map (fun omega => cs_lc_normpair (AE omega) (AF omega)) P =
        Measure.map (fun omega => cs_lc_reflpair i
          (cs_lc_normpair (AE omega) (AF omega))) P)
    (hperm : ∀ σ : Equiv.Perm (Fin d),
      Measure.map (fun omega => cs_lc_normpair (AE omega) (AF omega)) P =
        Measure.map (fun omega => cs_lc_permpair σ
          (cs_lc_normpair (AE omega) (AF omega))) P) :
    ∀ j l, ∫ omega, ((Matrix.trace (AE omega))⁻¹ • (AF omega - ck • AE omega)) j l ∂P = 0 := by
  set NP : Ω → (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) :=
    fun omega => cs_lc_normpair (AE omega) (AF omega) with hNP
  have htrm : AEStronglyMeasurable (fun omega => Matrix.trace (AE omega)) P := by
    have : (fun omega => Matrix.trace (AE omega)) = ∑ j : Fin d, (fun omega => AE omega j j) := by
      funext omega; simp [Matrix.trace, Matrix.diag]
    rw [this]
    exact Finset.aestronglyMeasurable_sum _ fun j _ => hmeasE j j
  have hNPm : AEMeasurable NP P := by
    refine AEMeasurable.prodMk ?_ ?_
    · refine AEMeasurable.of_eval fun j => AEMeasurable.of_eval fun l => ?_
      exact (hmeasE j l).aemeasurable.div htrm.aemeasurable
    · refine AEMeasurable.of_eval fun j => AEMeasurable.of_eval fun l => ?_
      exact (hmeasF j l).aemeasurable.div htrm.aemeasurable
  let g : Fin d → Fin d → (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) → ℝ :=
    fun j l XY => XY.2 j l - ck * XY.1 j l
  have hgc : ∀ j l, Continuous (g j l) := by
    intro j l
    have h1 : Continuous fun XY : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) => XY.1 j l :=
      (continuous_apply l).comp ((continuous_apply j).comp continuous_fst)
    have h2 : Continuous fun XY : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) => XY.2 j l :=
      (continuous_apply l).comp ((continuous_apply j).comp continuous_snd)
    exact h2.sub (continuous_const.mul h1)
  have hB : ∀ j l omega, ((Matrix.trace (AE omega))⁻¹ • (AF omega - ck • AE omega)) j l = g j l (NP omega) := by
    intro j l omega
    simp only [g, hNP, cs_lc_normpair, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul]
    ring
  -- transport of integrals along equal laws
  have htrans : ∀ (Φ : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ) →
      (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)), Continuous Φ →
      Measure.map NP P = Measure.map (fun omega => Φ (NP omega)) P →
      ∀ j l, ∫ omega, g j l (NP omega) ∂P = ∫ omega, g j l (Φ (NP omega)) ∂P := by
    intro Φ hΦ hlaw j l
    have hΦm : AEMeasurable (fun omega => Φ (NP omega)) P := hΦ.measurable.comp_aemeasurable hNPm
    rw [← integral_map hNPm (hgc j l).aestronglyMeasurable, hlaw,
      integral_map hΦm (hgc j l).aestronglyMeasurable]
  let EB : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun j l => ∫ omega, g j l (NP omega) ∂P
  have hrefl' : ∀ (i j k : Fin d),
      EB j k = (if j = i then -(1 : ℝ) else 1) * (if k = i then -(1 : ℝ) else 1) * EB j k := by
    intro i j k
    have hc : Continuous (cs_lc_reflpair (d := d) i) := by
      refine Continuous.prodMk ?_ ?_
      · refine continuous_pi fun a => continuous_pi fun b => ?_
        exact continuous_const.mul
          ((continuous_apply b).comp ((continuous_apply a).comp continuous_fst))
      · refine continuous_pi fun a => continuous_pi fun b => ?_
        exact continuous_const.mul
          ((continuous_apply b).comp ((continuous_apply a).comp continuous_snd))
    have h := htrans _ hc (hrefl i) j k
    have hpt : ∀ omega, g j k (cs_lc_reflpair i (NP omega)) =
        (if j = i then -(1 : ℝ) else 1) * (if k = i then -(1 : ℝ) else 1) * g j k (NP omega) := by
      intro omega
      simp only [g, cs_lc_reflpair, cs_lc_sign]
      ring
    show ∫ omega, g j k (NP omega) ∂P = _ * _ * ∫ omega, g j k (NP omega) ∂P
    conv_lhs => rw [h]
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul]
  have hperm' : ∀ (σ : Equiv.Perm (Fin d)) (j k : Fin d), EB (σ j) (σ k) = EB j k := by
    intro σ j k
    have hc : Continuous (cs_lc_permpair (d := d) σ) := by
      refine Continuous.prodMk ?_ ?_
      · exact continuous_pi fun a => continuous_pi fun b =>
          (continuous_apply (σ b)).comp ((continuous_apply (σ a)).comp continuous_fst)
      · exact continuous_pi fun a => continuous_pi fun b =>
          (continuous_apply (σ b)).comp ((continuous_apply (σ a)).comp continuous_snd)
    have h := htrans _ hc (hperm σ) j k
    simp only [EB, Matrix.of_apply]
    rw [h]
    rfl
  have htr0 : Matrix.trace EB = 0 := by
    have hsum : Matrix.trace EB = ∑ j : Fin d, ∫ omega, g j j (NP omega) ∂P := by
      simp only [Matrix.trace, Matrix.diag, EB, Matrix.of_apply]
    have hint' : ∀ j, Integrable (fun omega => g j j (NP omega)) P := fun j =>
      (hint j j).congr (Eventually.of_forall fun omega => hB j j omega)
    have hswap := integral_finset_sum (μ := P) Finset.univ (fun j _ => hint' j)
    rw [hsum, ← hswap, ← htrace]
    refine integral_congr_ae (Eventually.of_forall fun omega => ?_)
    show ∑ j ∈ Finset.univ, g j j (NP omega) =
      ∑ j, Matrix.diag ((Matrix.trace (AE omega))⁻¹ • (AF omega - ck • AE omega)) j
    exact Finset.sum_congr rfl fun j _ => (hB j j omega).symm
  have hzero := SubdiffusiveProcess.Lane3.relative_concentration_mean_matrix_eq_zero
    d hd EB hrefl' hperm' htr0
  intro j l
  have h := congrFun (congrFun hzero j) l
  simp only [EB, Matrix.of_apply, Matrix.zero_apply] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun omega => ?_)
  simp only
  rw [hB]

end
end CellSymmetry
end SubdiffusiveProcess
