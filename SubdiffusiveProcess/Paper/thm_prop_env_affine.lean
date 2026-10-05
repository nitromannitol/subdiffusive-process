module

public import SubdiffusiveProcess.Paper.conv_represented_affine_counted_actual_e
public import SubdiffusiveProcess.Paper.thm_prop_base
public import SubdiffusiveProcess.Paper.thm_prop_env_measure
public import SubdiffusiveProcess.Paper.thm_prop_affine_ellipticity_env_core
public import SubdiffusiveProcess.Paper.represented_same_law_in_measure
public import SubdiffusiveProcess.EllipticRegularity.GoodCellCatalogue
public import SubdiffusiveProcess.Paper.thm_prop_env_select
public import SubdiffusiveProcess.Paper.thm_prop_env_prepared
public import SubdiffusiveProcess.Paper.thm_prop_env_orig_limits
public import SubdiffusiveProcess.Paper.thm_prop_env_cell_arrays

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SubdiffusiveProcess.Paper

section Part0
open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

/-- The catalogue block for one enumeration `e` (verbatim from the output of
`conv_represented_affine_counted_actual`). -/
def aux_thm_prop_env_Kblock1
    (d : ℕ) (_hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ωh : Type) [MeasurableSpace Ωh] (Ph : Measure Ωh)
    (field : Ωh → BilateralField d)
    (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
    (_Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
    (GE GF : (i : ℕ) → Ωh →
      DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ] DomainL2 (centeredCube (Z i) (R i) (hR i)))
    (seq NE NF : ℕ → ℕ)
    (_alpha gamma _zeta : ℝ)
    (e : ℕ → ℕ) (g : aux_thm_prop_selection_geometry d) (eps epshom lambdaLim cdet : ℝ) : Prop :=
(let z := Z ∘ e
       let r := R ∘ e
       let hr := fun j => hR (e j)
       let N : Fin 2 → ℕ → ℕ := ![(fun n => NE (seq n)), (fun n => NF (seq n))]
       let GE : Fin 2 → ∀ j, Ωh → DomainL2 (centeredCube (z j) (r j) (hr j)) →L[ℝ]
          DomainL2 (centeredCube (z j) (r j) (hr j)) :=
         (fun a j => (![GE, GF] a) (e j))
      ∃ (eta : ℕ → BilateralField d → _root_.SubdiffusiveProcess.Model.PotentialSample d)
        (F Praw Rraw Draw : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ENNReal)
        (Z : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → ℝ)
        (rawGood : ℕ → ℕ → (Fin d → ℝ) → BilateralField d → Prop),
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ (N i : ℕ) (y : Fin d → ℝ),
        eta N omega i y = omega ((i : ℤ) - (N : ℤ)) (((3 : ℝ) ^ (-(N : ℤ))) • y)) ∧
      (∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
        primitive_scores d M (1 / 64) eps (eta N omega)
          (fun m y => F N m y omega) (fun m y => Praw N m y omega)
          (fun m y => Rraw N m y omega) (fun m y => Draw N m y omega)
          (fun m y => Z N m y omega) (fun m y => rawGood N m y omega)) ∧
      ∃ psi : ℕ → ℕ, StrictMono psi ∧ ∃ eRef : Fin 2 → ℕ → ℝ,
      (∀ a k, 0 < eRef a k) ∧
      (∀ a (k : ℕ), Tendsto (fun n =>
        (let kappa : ℕ → ℝ := fun J =>
          Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq M.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom M J
         kappa (((N a (psi n) : ℤ) - (k : ℤ)).toNat) / kappa (N a (psi n))))
        atTop (𝓝 (eRef a k))) ∧
      ∃ (ZLim DLim : Fin 2 → (ℕ × ℕ) → ∀ (U : Fin 3 × (Fin d → Fin 3)) (D : ℕ),
            ((Fin D → OddGridIndex d 1) ⊕ (Fin 3 × (Fin d → Fin 3))) → BilateralField d → ℝ)
        (loLim hiLim : Fin 2 → (ℕ × ℕ) → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → ℝ)
        (AELim : Fin 2 → (ℕ × ℕ) → (Fin 3 × (Fin d → Fin 3)) → BilateralField d → Matrix (Fin d) (Fin d) ℝ)
        (errLim ratioLim : Fin 2 → (ℕ × ℕ) → Unit → BilateralField d → ℝ),
      (∀ a c,
        (∀ U D code, Measurable (ZLim a c U D code) ∧ Measurable (DLim a c U D code)) ∧
        (∀ U, Measurable (loLim a c U) ∧ Measurable (hiLim a c U) ∧
          ∀ i j, Measurable (fun omega => AELim a c U omega i j)) ∧
        Measurable (errLim a c ()) ∧ Measurable (ratioLim a c ()) ∧
        aux_affine_source_cells_env_cellArrays I M H (1 / 64) (((127 / 128 : ℝ) - 1 / 2) / 4) (Nat.floor (gamma * (g.H1 : ℝ)) + 4) 4 Z Draw
          (fun n => N a (psi n)) (g.H1 * c.2) (z c.1)
          (ZLim a c) (DLim a c) (loLim a c) (hiLim a c) (AELim a c)
          (errLim a c) (ratioLim a c)) ∧
      (let Good : ℕ → SpatialCoordinates d → Set (BilateralField d) := fun n zc =>
        {omega | aux_thm_prop_cell_available z r zc (aux_thm_prop_mass_side g.H1 n) →
        ∀ a : Fin 2, omega ∈ gcat_good 1 lambdaLim (1 / 2) epshom cdet
          (ZLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
          (DLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
          (loLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
          (hiLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
          (errLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))
          (ratioLim a ((aux_thm_prop_cell_index z r zc (aux_thm_prop_mass_side g.H1 n)).1, n))}
      (∀ n zc, MeasurableSet (Good n zc)) ∧
      (∀ z0 : SpatialCoordinates d,
        ∃ B : Ωh → ℝ, Measurable B ∧ (∀ omega, 0 ≤ B omega) ∧
          ∀ᵐ omega ∂Ph, ∀ (J : ℕ) (pi : Fin J → OddGridIndex d (_root_.SubdiffusiveProcess.ResponseMoments.subdivisionHalfWidth g.H1)),
            (Nat.card {j : Fin J // field omega ∉ Good (j.val + 1)
              (_root_.SubdiffusiveProcess.ResponseMoments.descendantCenter (_root_.SubdiffusiveProcess.ResponseMoments.subdivisionHalfWidth g.H1) z0 1 (j.val + 1)
                (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩))} : ℝ) ≤
              ((1 / 32 : ℝ) / 2) * (J : ℝ) + B omega) ∧
      aux_thm_prop_mass_good_counts Ph z r hr g (fun n zc => field ⁻¹' Good n zc) ∧
      ∀ᵐ omega ∂Ph, ∀ a : Fin 2, ∀ jQ : ℕ,
      ∀ (E' : _root_.SubdiffusiveProcess.DirichletForm
          (volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))))
        (Gam' : _root_.SubdiffusiveProcess.DirichletForm.EnergyMeasure E'.toClosedForm),
      (∀ u, E'.toClosedForm.energy u = limitFormEnergy (GE a jQ omega) u) →
      (∃ C, _root_.SubdiffusiveProcess.DirichletForm.IsCoreOn E'.toClosedForm
        (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) C) →
      ∀ f ∈ aux_thm_prop_smoothSources (centeredCube (z jQ) (r jQ) (hr jQ)),
      ∀ hu : GE a jQ omega f ∈ E'.toClosedForm.domain, ∀ c : ℝ, 0 < c →
      ∃ baseMesh : ℝ, 0 < baseMesh ∧
        ∀ (n : ℕ), 1 ≤ n → aux_thm_prop_mass_side g.H1 n ≤ baseMesh →
        ∀ (sigma : Fin d → Fin g.Mm) (k : Fin d → ℤ),
        field omega ∈ Good n (aux_thm_prop_mass_center g.H1 g.Mm sigma n k) →
        aux_thm_prop_mass_padded g.H1 g.Mm g.width g.gamma sigma n k →
        closure (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k) ⊆
          (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d)) →
        let mu := Gam'.measure (GE a jQ omega f) + ENNReal.ofReal c •
          volume.restrict (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))
        (mu (aux_thm_prop_mass_parent g.H1 g.Mm sigma n k)).toReal ≤
          ((3 : ℝ) ^ g.H1) ^ ((d : ℝ) + g.zeta) *
            (mu (aux_thm_prop_mass_cell g.H1 g.Mm sigma n k)).toReal →
        ∃ U : SpatialCoordinates d → ℝ,
          ContinuousOn U (closure (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))) ∧
          (⇑(GE a jQ omega f) =ᵐ[volume.restrict
            (centeredCube (z jQ) (r jQ) (hr jQ) : Set (SpatialCoordinates d))] U) ∧
          aux_thm_prop_affine_error (centeredCube (z jQ) (r jQ) (hr jQ))
            E'.toClosedForm Gam' (GE a jQ omega f) U c
            (centeredCube (aux_thm_prop_mass_center g.H1 g.Mm sigma n k)
              (aux_thm_prop_mass_side g.H1 n) (aux_thm_prop_grid_side_pos g.H1 n) :
                Set (SpatialCoordinates d))))

/-- The catalogue block (`∀ K, ...`) of the output of `conv_represented_affine_counted_actual`. -/
def aux_thm_prop_env_Kblock
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ωh : Type) [MeasurableSpace Ωh] (Ph : Measure Ωh) [IsProbabilityMeasure Ph]
    (field : Ωh → BilateralField d) (env : ℕ → Ωh → BilateralField d)
    (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
    (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
    (GE GF : (i : ℕ) → Ωh →
      DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ] DomainL2 (centeredCube (Z i) (R i) (hR i)))
    (seq NE NF : ℕ → ℕ)
    (alpha gamma zeta : ℝ)
    (g : aux_thm_prop_selection_geometry d) (eps epshom lambdaLim cdet : ℝ) : Prop :=
  ∀ K : ℕ, ∃ e : ℕ → ℕ, (∀ i ≤ K, ∃ j, e j = i) ∧
    conv_represented_catalogue_grids d hd M H Ωh Ph env env (Z ∘ e) (R ∘ e)
      (fun j => hR (e j)) (fun j => Sspace (e j)) (fun n => NE (seq n)) (fun n => NF (seq n))
      alpha (1 / 128) I (127 / 128) ((d : ℝ) - 1 / 2) ∧
    aux_thm_prop_env_Kblock1 d hd I M H Ωh Ph field Z R hR Sspace GE GF seq NE NF alpha gamma zeta e g eps epshom lambdaLim cdet

end Part0

section Part1
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology BigOperators

/-- Trace ellipticity of the limiting affine matrix of a cell on the represented space, from the
convergence in measure of its normalized lower and upper coefficient arrays on the original space. -/
theorem aux_thm_prop_env_cell_ellipticity {d : ℕ} (hd : 0 < d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : _root_.SubdiffusiveProcess.Paper.in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (field : Ω → BilateralField d) (env : ℕ → Ω → BilateralField d)
    (hMP : ∀ n, MeasurePreserving (env n) P (chaosSampleLaw M).toMeasure)
    (hfield : MeasurePreserving field P (chaosSampleLaw M).toMeasure)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => env n ω) atTop (𝓝 (field ω)))
    (sigma : ℝ) (hsigma : sigma ∈ Set.Ioc (0 : ℝ) 1)
    (Ncut : ℕ → ℕ) (psi : ℕ → ℕ) (hpsi : StrictMono psi)
    (k : ℕ) (z : SpatialCoordinates d) (loLim hiLim : BilateralField d → ℝ)
    (hlo : Measurable loLim) (hhi : Measurable hiLim)
    (r : ℝ) (hr : 0 < r)
    (hlam : TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n β => I.lam z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (Ncut (psi n)) z hr) z r sigma 2 /
        SubdiffusiveProcess.gcat_sN M H (Ncut (psi n)) (k : ℤ) z β) atTop loLim)
    (hLam : TendstoInMeasure (chaosSampleLaw M).toMeasure
      (fun n β => I.Lam z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (Ncut (psi n)) z hr) z r sigma 2 /
        SubdiffusiveProcess.gcat_sN M H (Ncut (psi n)) (k : ℤ) z β) atTop hiLim)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (A : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ᵐ ω ∂P, ∀ p : Fin d → ℝ, Tendsto (fun n =>
      affineDirichletResponse (centeredCube_isBounded z hr) hP
        (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n ω) (Ncut n) z hr) p /
        (volume (centeredCube z r hr : Set (SpatialCoordinates d))).toReal)
      atTop (𝓝 (p ⬝ᵥ (A ω).mulVec p))) :
    ∀ᵐ ω ∂P, (1 / 2 : ℝ) ≤ loLim (field ω) → hiLim (field ω) ≤ 2 →
      ∀ p : Fin d → ℝ, ((1 / 2 : ℝ) ^ 2 / (d : ℝ)) * Matrix.trace (A ω) * (p ⬝ᵥ p) ≤
        p ⬝ᵥ (A ω).mulVec p := by
  have hY : ∀ n, MeasurePreserving (env (psi n)) P (chaosSampleLaw M).toMeasure :=
    fun n => hMP (psi n)
  have hconv' : ∀ᵐ ω ∂P, Tendsto (fun n => env (psi n) ω) atTop (𝓝 (field ω)) :=
    hconv.mono fun ω hω => hω.comp hpsi.tendsto_atTop
  let X : Bool → ℕ → BilateralField d → ℝ := fun b n β =>
    cond b
      (I.lam z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (Ncut (psi n)) z hr) z r sigma 2 /
        SubdiffusiveProcess.gcat_sN M H (Ncut (psi n)) (k : ℤ) z β)
      (I.Lam z r hr (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H β (Ncut (psi n)) z hr) z r sigma 2 /
        SubdiffusiveProcess.gcat_sN M H (Ncut (psi n)) (k : ℤ) z β)
  let V : Bool → BilateralField d → ℝ := fun b => cond b loLim hiLim
  have hV : ∀ b, AEStronglyMeasurable (V b) (chaosSampleLaw M).toMeasure := by
    intro b
    cases b with
    | true => simpa [V] using hlo.aestronglyMeasurable
    | false => simpa [V] using hhi.aestronglyMeasurable
  have hXV : ∀ b, TendstoInMeasure (chaosSampleLaw M).toMeasure (X b) atTop (V b) := by
    intro b
    cases b with
    | true => simpa [X, V] using hlam
    | false => simpa [X, V] using hLam
  obtain ⟨φ, hφmono, hae⟩ := aux_env_ae_subseq_transfer (ι := Bool) (S := BilateralField d)
    (P := P) (μ := (chaosSampleLaw M).toMeasure) (Y := fun n => env (psi n)) (Y0 := field)
    hY hfield hconv' X V hV hXV
  filter_upwards [hae, hA] with ω hω hAω
  intro hlo1 hhi1 p
  refine thm_prop_affine_ellipticity_env_core hd I M H (fun m => env (psi (φ m)) ω) z r hr hP
    (fun m => Ncut (psi (φ m))) (A ω) ?_ sigma hsigma
    (fun m => SubdiffusiveProcess.gcat_sN M H (Ncut (psi (φ m))) (k : ℤ) z (env (psi (φ m)) ω))
    (1 / 2) (loLim (field ω)) (hiLim (field ω)) (by norm_num) ?_ ?_ hlo1 ?_ p
  · intro p
    exact (hAω p).comp (hpsi.comp hφmono).tendsto_atTop
  · simpa [X, V] using hω true
  · simpa [X, V] using hω false
  · simpa using hhi1

end Part1

section Part2
open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff InnerProductSpace

/-- **The affine data of the environment form, from the catalogue block of the constructor.** -/
theorem thm_prop_env_affine
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (M : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (_hH : InfraredCharacterization M H)
    (Ωh : Type) [MeasurableSpace Ωh] (Ph : Measure Ωh) [IsProbabilityMeasure Ph]
    (field : Ωh → BilateralField d) (env : ℕ → Ωh → BilateralField d)
    (Z : ℕ → SpatialCoordinates d) (R : ℕ → ℝ) (hR : ∀ i, 0 < R i)
    (Sspace : ∀ i, ResponseSpace (centeredCube (Z i) (R i) (hR i)))
    (GE GF : (i : ℕ) → Ωh →
      DomainL2 (centeredCube (Z i) (R i) (hR i)) →L[ℝ] DomainL2 (centeredCube (Z i) (R i) (hR i)))
    (seq NE NF : ℕ → ℕ) (_hseq : StrictMono seq)
    (alpha gamma zeta : ℝ) (e : ℕ → ℕ) (g : aux_thm_prop_selection_geometry d)
    (eps epshom lambdaLim cdet : ℝ)
    (hK1 : aux_thm_prop_env_Kblock1 d hd I M H Ωh Ph field Z R hR Sspace GE GF seq NE NF alpha gamma
      zeta e g eps epshom lambdaLim cdet)
    (hfield : MeasurePreserving field Ph (chaosSampleLaw M).toMeasure)
    (hmpenv : ∀ n, MeasurePreserving (env n) Ph (chaosSampleLaw M).toMeasure)
    (hconvenv : ∀ᵐ om ∂Ph, Tendsto (fun n => env n om) atTop (𝓝 (field om)))
    (AE AF : ℕ → Ωh → Matrix (Fin d) (Fin d) ℝ)
    (hconv : ∀ᵐ om ∂Ph, ∀ j,
      (∀ p : Fin d → ℝ, Tendsto (fun n =>
        affineDirichletResponse (centeredCube_isBounded ((Z ∘ e) j) (hR (e j)))
          (aux_thm_prop_env_hP (Z ∘ e) (R ∘ e) (fun j => hR (e j)) j)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (NE (seq n)) ((Z ∘ e) j) (hR (e j))) p /
          (volume (centeredCube ((Z ∘ e) j) ((R ∘ e) j) (hR (e j)) :
            Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ (AE j om).mulVec p))) ∧
      (∀ p : Fin d → ℝ, Tendsto (fun n =>
        affineDirichletResponse (centeredCube_isBounded ((Z ∘ e) j) (hR (e j)))
          (aux_thm_prop_env_hP (Z ∘ e) (R ∘ e) (fun j => hR (e j)) j)
          (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (NF (seq n)) ((Z ∘ e) j) (hR (e j))) p /
          (volume (centeredCube ((Z ∘ e) j) ((R ∘ e) j) (hR (e j)) :
            Set (SpatialCoordinates d))).toReal)
        atTop (𝓝 (p ⬝ᵥ (AF j om).mulVec p))))
    (hpos : ∀ᵐ om ∂Ph, ∀ j, 0 < Matrix.trace (AE j om) ∧ 0 < Matrix.trace (AF j om))
    (m M' : ℝ)
    (prepared : aux_thm_prop_env_selection_data d hd Ωh Ph (Z ∘ e) (R ∘ e) (fun j => hR (e j))
      (fun j => Sspace (e j)) (fun j => GE (e j)) (fun j => GF (e j))
      (fun i om n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (NE (seq n)) (Z (e i)) (hR (e i)))
      (fun i om n => _root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient M H (env n om) (NF (seq n)) (Z (e i)) (hR (e i)))
      m M')
    (hpAE : prepared.AE = AE) :
    Nonempty (aux_thm_prop_env_local_affine_data prepared g (((1 / 2 : ℝ) ^ 2) / (d : ℝ))) := by
  classical
  obtain ⟨eta, F, Praw, Rraw, Draw, Zs, rawGood, hEta, hScores, psi, hpsi, eRef, heRefpos, hkappa,
    ZLim, DLim, loLim, hiLim, AELim, errLim, ratioLim, harr, hGoodBlock⟩ := hK1
  obtain ⟨hGm, hchain, hcounts, happrox⟩ := hGoodBlock
  let U0 : Fin 3 × (Fin d → Fin 3) := (0, fun _ => 1)
  let GoodK : ℕ → SpatialCoordinates d → Set (BilateralField d) := fun n zc =>
    {omega | aux_thm_prop_cell_available (Z ∘ e) (R ∘ e) zc (aux_thm_prop_mass_side g.H1 n) →
      ∀ a : Fin 2, omega ∈ gcat_good 1 lambdaLim (1 / 2) epshom cdet
        (ZLim a ((aux_thm_prop_cell_index (Z ∘ e) (R ∘ e) zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (DLim a ((aux_thm_prop_cell_index (Z ∘ e) (R ∘ e) zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (loLim a ((aux_thm_prop_cell_index (Z ∘ e) (R ∘ e) zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (hiLim a ((aux_thm_prop_cell_index (Z ∘ e) (R ∘ e) zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (errLim a ((aux_thm_prop_cell_index (Z ∘ e) (R ∘ e) zc (aux_thm_prop_mass_side g.H1 n)).1, n))
        (ratioLim a ((aux_thm_prop_cell_index (Z ∘ e) (R ∘ e) zc (aux_thm_prop_mass_side g.H1 n)).1, n))}
  have hGm' : ∀ n zc, MeasurableSet (GoodK n zc) := hGm
  refine ⟨{
    Good := fun n zc => field ⁻¹' GoodK n zc
    measurable := fun n zc => hfield.measurable (hGm' n zc)
    chain := fun sigma k => ?_
    ellipticity := ?_
    approximationE := ?_
    approximationF := ?_ }⟩
  · obtain ⟨B, hBm, hB0, hBae⟩ := hchain (aux_thm_prop_mass_center g.H1 g.Mm sigma 0 k)
    exact ⟨B, hBm, hB0, hBae.mono fun om h J _ pi => h J pi⟩
  · have hell : ∀ (j n : ℕ), ∀ᵐ om ∂Ph, R (e j) = aux_thm_prop_mass_side g.H1 n →
        (1 / 2 : ℝ) ≤ loLim 0 (j, n) U0 (field om) → hiLim 0 (j, n) U0 (field om) ≤ 2 →
        ∀ p : Fin d → ℝ, (((1 / 2 : ℝ) ^ 2) / (d : ℝ)) * Matrix.trace (AE j om) * (p ⬝ᵥ p) ≤
          p ⬝ᵥ (AE j om).mulVec p := by
      intro j n
      by_cases hmass : R (e j) = aux_thm_prop_mass_side g.H1 n
      · have hrk : R (e j) = (3 : ℝ) ^ (-((g.H1 * n : ℕ) : ℤ)) :=
          hmass.trans (aux_thm_prop_mass_side_zpow g.H1 n)
        have h1 := aux_thm_prop_env_root_self_arrays I M H (1 / 64) (((127 / 128 : ℝ) - 1 / 2) / 4)
          (⌊gamma * (g.H1 : ℝ)⌋₊ + 4) 4 Zs Draw
          (fun n' => ![fun n => NE (seq n), fun n => NF (seq n)] 0 (psi n')) (g.H1 * n) ((Z ∘ e) j)
          (ZLim 0 (j, n)) (DLim 0 (j, n)) (loLim 0 (j, n)) (hiLim 0 (j, n)) (AELim 0 (j, n))
          (errLim 0 (j, n)) (ratioLim 0 (j, n)) (harr 0 (j, n)).2.2.2.2 (R (e j)) (hR (e j)) hrk
        have hcellE := aux_thm_prop_env_cell_ellipticity (Nat.pos_of_ne_zero (NeZero.ne d)) I M H
          Ωh Ph field env hmpenv hfield hconvenv (((127 / 128 : ℝ) - 1 / 2) / 4)
          ⟨by norm_num, by norm_num⟩ (fun n' => NE (seq n')) psi hpsi (g.H1 * n) ((Z ∘ e) j)
          (loLim 0 (j, n) U0) (hiLim 0 (j, n) U0) ((harr 0 (j, n)).2.1 U0).1
          ((harr 0 (j, n)).2.1 U0).2.1 (R (e j)) (hR (e j)) h1.1 h1.2
          (aux_thm_prop_env_hP (Z ∘ e) (R ∘ e) (fun j => hR (e j)) j) (AE j)
          (hconv.mono fun om h p => (h j).1 p)
        filter_upwards [hcellE] with om h _ h1' h2' p
        exact h h1' h2' p
      · exact Filter.Eventually.of_forall fun om h => absurd h hmass
    have hall : ∀ᵐ om ∂Ph, ∀ j n : ℕ, R (e j) = aux_thm_prop_mass_side g.H1 n →
        (1 / 2 : ℝ) ≤ loLim 0 (j, n) U0 (field om) → hiLim 0 (j, n) U0 (field om) ≤ 2 →
        ∀ p : Fin d → ℝ, (((1 / 2 : ℝ) ^ 2) / (d : ℝ)) * Matrix.trace (AE j om) * (p ⬝ᵥ p) ≤
          p ⬝ᵥ (AE j om).mulVec p :=
      ae_all_iff.2 fun j => ae_all_iff.2 fun n => hell j n
    filter_upwards [hall, hpos] with om h hp n zc hav hgood
    obtain ⟨hzC, hrC, hzP, hrP⟩ := aux_thm_prop_cell_index_spec (Z ∘ e) (R ∘ e) zc
      (aux_thm_prop_mass_side g.H1 n) hav
    obtain ⟨_, hlohi, _, _⟩ := hgood hav 0
    have hlohi' := hlohi U0
    show 0 < Matrix.trace (prepared.AE _ om) ∧ _
    rw [hpAE]
    refine ⟨(hp _).1, h _ n hrC hlohi'.1 ?_⟩
    have := hlohi'.2
    norm_num at this ⊢
    linarith
  · filter_upwards [happrox] with om h jQ E f hf hu c hc
    exact h 0 jQ E.form E.gamma E.energy_eq E.core f hf hu c hc
  · filter_upwards [happrox] with om h jQ E f hf hu c hc
    exact h 1 jQ E.form E.gamma E.energy_eq E.core f hf hu c hc

end Part2

end SubdiffusiveProcess.Paper
end
