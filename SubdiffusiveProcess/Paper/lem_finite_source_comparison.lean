module

public import SubdiffusiveProcess.Paper.lem_finite_stopping
public import SubdiffusiveProcess.Paper.lem_finite_source_comparison_cells
public import SubdiffusiveProcess.Paper.lem_finite_source_comparison_trial
public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.MeanZero
public import Mathlib.Tactic
public import SubdiffusiveProcess.Paper.cor_neumann_source
public import SubdiffusiveProcess.Paper.lem_finite_good_cell
public import SubdiffusiveProcess.Paper.prop_growth
public import SubdiffusiveProcess.Paper.lem_infrared
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.EllipticRegularity.Inputs

public import SubdiffusiveProcess.Main.NormalizedContinuousPositiveCoefficient_coeFn

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- The actual harmonic extension solves the Dirichlet problem with zero load. -/
lemma aux_lem_finite_source_comparison_minimizer_solves_zero
    {d : ℕ} {Q : Opens (SpatialCoordinates d)}
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖)
    (a : PositiveCoefficient Q) (b : weakSobolevGraph Q) :
    SolvesDirichlet a (fun _ => (0 : ℝ)) b
      (@dirichletMinimizer d Q (@killedResponseSpace d Q hP) a b) := by
  refine ⟨dirichletMinimizer_mem_affine (killedResponseSpace hP) a b, fun ψ => ?_⟩
  have h := dirichletMinimizer_euler (killedResponseSpace hP) a b ψ
  simp only [zero_mul, integral_zero]
  exact h



lemma aux_lem_finite_source_comparison_stopping_of_cells_dir
    (d : ℕ) {Q : Opens (SpatialCoordinates d)} (closedQ : Set (SpatialCoordinates d))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (hQ : Q = centeredCube z r hr)
    (N : ℕ) (aTarget aSource : PositiveCoefficient Q) (err factor : ℝ)
    (hDir : ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
      0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
      ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
      ∀ b u : weakSobolevGraph Q,
        ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
        SolvesDirichlet aSource F b u →
        ∃ ncell : ℕ, ∃ centers : Fin ncell → SpatialCoordinates d,
          ∃ sides : Fin ncell → ℝ, ∃ hside : ∀ i, 0 < sides i,
          let cell := fun i => centeredCube (centers i) (sides i) (hside i)
          ∃ hle : ∀ i, cell i ≤ Q,
            (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
              (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
            Pairwise (fun i j =>
              Disjoint (cell i : Set (SpatialCoordinates d))
                (cell j : Set (SpatialCoordinates d))) ∧
            ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
              (Q : Set (SpatialCoordinates d))) ∧
            ∃ hPcell : ∀ i, ∃ K : ℝ≥0,
              ∀ v : killedSobolevGraph (cell i),
                ‖(v : SobolevData (cell i)).1‖ ≤
                  K * ‖@subspaceGradient d (cell i)
                    (killedSobolevGraph (cell i)) v‖,
              ∃ U : SpatialCoordinates d → ℝ,
                ContinuousOn U closedQ ∧
                (((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                  =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U) ∧
                (∀ i, ∀ x ∈ closure (cell i : Set (SpatialCoordinates d)),
                  ∀ y ∈ closure (cell i : Set (SpatialCoordinates d)),
                    |U x - U y| ≤ (err / 4) * (Kf + c2Norm closedQ phi)) ∧
            (∑ i : Fin ncell,
                @dirichletResponse d (cell i)
                  (@killedResponseSpace d (cell i) (hPcell i))
                  (positiveCoefficientRestrict (hle i) aTarget)
                  ⟨sobolevDataRestrict (hle i) u.val,
                    sobolevDataRestrict_mem_weak (hle i) u.property⟩) ≤
                factor * sobolevCoefficientForm aSource u.val u.val +
                  err * (Kf + c2Norm closedQ phi) ^ 2)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖)
    (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (b : weakSobolevGraph Q)
    (hb : ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi) :
    @dirichletResponse d Q (@killedResponseSpace d Q hP) aTarget b ≤
      factor * @dirichletResponse d Q (@killedResponseSpace d Q hP) aSource b +
        err * (c2Norm closedQ phi) ^ 2 := by
  subst hQ
  let u := @dirichletMinimizer d _ (@killedResponseSpace d _ hP) aSource b
  have hsol : SolvesDirichlet aSource (fun _ => (0 : ℝ)) b u :=
    aux_lem_finite_source_comparison_minimizer_solves_zero hP aSource b
  have hphi2 : ContDiff ℝ 2 phi := hphi.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  obtain ⟨ncell, centers, sides, hside, hle, _, hpair, hcover, hPcell, _U, _, _, _, hsum⟩ :=
    hDir (fun _ => (0 : ℝ)) 0 le_rfl measurable_const (by simp) phi hphi2 b u hb hsol
  have hu : u.val - b.val ∈ killedSobolevGraph (centeredCube z r hr) :=
    dirichletMinimizer_mem_affine (killedResponseSpace hP) aSource b
  have hglue := aux_lem_finite_stopping_glue d z r hr hP ncell centers sides hside hle
    hpair hcover hPcell aTarget b u hu
  have hE : sobolevCoefficientForm aSource u.val u.val =
      @dirichletResponse d _ (@killedResponseSpace d _ hP) aSource b := rfl
  rw [hE, zero_add] at hsum
  exact hglue.trans hsum



theorem lem_finite_source_comparison
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Step : @cutoff_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Dbase : @sum_errors_baseline_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ _ _)
    (theta : ℝ) (htheta : 0 < theta) :
    ∃ (H1 : ℕ) (Dgeom Cgeom delta0 : ℝ),
      0 < H1 ∧ 0 < Dgeom ∧ 0 < Cgeom ∧ 0 < delta0 ∧
      (let L : ℝ := (3 : ℝ) ^ H1
       ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
         (Rm : in_responses d model) (Sreg : in_6_16 d model)
         (It : in_iteration d model E Sreg)
         (H : BilateralField d → C(SpatialCoordinates d, ℝ))
         (hH : InfraredCharacterization model H) (hsmall : model.delta ≤ delta0)
         (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
         (htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
       let Q := centeredCube z r hr
       let closedQ := closedCube z r hr
       ∀ (eta : ℝ), 0 < eta →
       ∃ (Ceta gamma : ℝ) (N0 : ℕ), 0 < Ceta ∧ 0 < gamma ∧
       ∀ (N M : ℕ), N0 ≤ N → N ≤ M →
       ∀ (c : ℝ), 0 < c → c ≤ 2 →
       ∀ (S : ℕ → Prop),
         theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
           (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) →
       let kappa := fun J : ℕ =>
         Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
           SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
       ((∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
           (kappa (N - H1 * n) / kappa N) / (kappa (M - H1 * n) / kappa M) ≤ c) →
         ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
           ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖,
         ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
         ∀ b : weakSobolevGraph Q,
           ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
             =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
         ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
           (chaosSampleLaw model).toMeasure Bad ≤
             ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
           ∀ omega ∉ Bad,
           let aN := cutoffPositiveCoefficient model H omega N z hr
           let aM := cutoffPositiveCoefficient model H omega M z hr
           @dirichletResponse d Q (@killedResponseSpace d Q hP) aN b ≤
             c * (1 + Cgeom * eta * L ^ Dgeom) *
               @dirichletResponse d Q (@killedResponseSpace d Q hP) aM b +
             Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm closedQ phi) ^ 2) ∧
       ((∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
           (kappa (M - H1 * n) / kappa M) / (kappa (N - H1 * n) / kappa N) ≤ c) →
         ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
           ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖,
         ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
         ∀ b : weakSobolevGraph Q,
           ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
             =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
         ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
           (chaosSampleLaw model).toMeasure Bad ≤
             ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
           ∀ omega ∉ Bad,
           let aN := cutoffPositiveCoefficient model H omega N z hr
           let aM := cutoffPositiveCoefficient model H omega M z hr
           @dirichletResponse d Q (@killedResponseSpace d Q hP) aM b ≤
             c * (1 + Cgeom * eta * L ^ Dgeom) *
               @dirichletResponse d Q (@killedResponseSpace d Q hP) aN b +
             Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm closedQ phi) ^ 2))
      ∧
      (let L : ℝ := (3 : ℝ) ^ H1
       ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
         (Rm : in_responses d model) (Sreg : in_6_16 d model)
         (It : in_iteration d model E Sreg)
         (H : BilateralField d → C(SpatialCoordinates d, ℝ))
         (hH : InfraredCharacterization model H) (hsmall : model.delta ≤ delta0)
         (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
         (htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
       let Q := centeredCube z r hr
       let closedQ := closedCube z r hr
       ∀ (eta : ℝ), 0 < eta →
       ∃ (Ceta gamma : ℝ) (N0 : ℕ), 0 < Ceta ∧ 0 < gamma ∧
       ∀ (N M : ℕ), N0 ≤ N → N ≤ M →
       ∀ (c : ℝ), 0 < c → c ≤ 2 →
       ∀ (S : ℕ → Prop),
       theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
           (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) →
       ∀ reverse : Bool,
       let Nt : ℕ := if reverse then M else N
       let Ns : ℕ := if reverse then N else M
       let kappa := fun J : ℕ =>
         Real.exp (((J : ℝ) + 1) * _root_.SubdiffusiveProcess.Model.tauSq model.P) *
           SubdiffusiveProcess.CoarseGrainingVocab.ahom model J
       (∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
         (kappa (Nt - H1 * n) / kappa Nt) / (kappa (Ns - H1 * n) / kappa Ns) ≤ c) →
       ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
         (chaosSampleLaw model).toMeasure Bad ≤
           ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
         ∀ omega ∉ Bad, ∀ infrared : Bool,
         let Hused := if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))
         let aTarget := cutoffPositiveCoefficient model Hused omega Nt z hr
         let aSource := cutoffPositiveCoefficient model Hused omega Ns z hr
         let err := Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))
         let factor := c * (1 + Cgeom * eta * L ^ Dgeom)
         let energy := fun (a : PositiveCoefficient Q) (v : SobolevData Q) =>
           sobolevCoefficientForm a v v
         (∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
           0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
             ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
           ∀ b u : weakSobolevGraph Q,
             ((b : SobolevData Q).1 : SpatialCoordinates d → ℝ)
               =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] phi →
             SolvesDirichlet aSource F b u →
             ∃ (v : weakSobolevGraph Q) (U V : SpatialCoordinates d → ℝ),
               (v : SobolevData Q) - (b : SobolevData Q) ∈ killedSobolevGraph Q ∧
               ContinuousOn U closedQ ∧ ContinuousOn V closedQ ∧
               ((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U ∧
               ((v : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V ∧
               (∀ x ∈ closedQ, |V x - U x| ≤ err * (Kf + c2Norm closedQ phi)) ∧
               energy aTarget (v : SobolevData Q) ≤ factor * energy aSource (u : SobolevData Q) +
                 err * (Kf + c2Norm closedQ phi) ^ 2) ∧
         (∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
           0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
           (∫ x in (Q : Set (SpatialCoordinates d)), F x) = 0 →
           ∀ u : meanZeroSobolevGraph Q, SolvesNeumann aSource F u →
             ∃ (v : meanZeroSobolevGraph Q) (U V : SpatialCoordinates d → ℝ),
               ContinuousOn U closedQ ∧ ContinuousOn V closedQ ∧
               ((u : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] U ∧
               ((v : SobolevData Q).1 : SpatialCoordinates d → ℝ)
                 =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))] V ∧
               (∀ x ∈ closedQ, |V x - U x| ≤ err * Kf) ∧
               energy aTarget (v : SobolevData Q) ≤ factor * energy aSource (u : SobolevData Q) +
                 err * Kf ^ 2)) := by
  have hcells := lem_finite_source_comparison_cells d hd E P X W Cp Sf D hES Step Dbase theta htheta
  rcases hcells with ⟨H1, Dgeom, Cgeom, delta0, hH1, hDgeom, hCgeom, hdelta0, hbody⟩
  refine ⟨H1, Dgeom, Cgeom, delta0, hH1, hDgeom, hCgeom, hdelta0, ?_, ?_⟩
  · dsimp only
    intro model Rm Sreg It H hH hsmall z r hr htriadic eta heta
    have hmodel := hbody model Rm Sreg It H hH hsmall z r hr htriadic eta heta
    rcases hmodel with ⟨Ceta, gamma, N0, hCeta, hgamma, hrest⟩
    refine ⟨Ceta, gamma, N0, hCeta, hgamma, ?_⟩
    intro N M hN0 hNM c hc hc2 S hS
    constructor
    · intro hratio hP phi hphi b hb
      have h1 := hrest N M hN0 hNM c hc hc2 S hS
      have h2 := h1 false
      have h3 := h2 hratio
      rcases h3 with ⟨Bad, hBadMeas, hBadLe, hBadRest⟩
      refine ⟨Bad, hBadMeas, hBadLe, ?_⟩
      intro omega homega
      exact aux_lem_finite_source_comparison_stopping_of_cells_dir d (closedCube z r hr : Set (SpatialCoordinates d))
        z r hr rfl N
        (cutoffPositiveCoefficient model H omega N z hr)
        (cutoffPositiveCoefficient model H omega M z hr)
        (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)))
        (c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom))
        (hBadRest omega homega true).1 hP phi hphi b hb
    · intro hratio hP phi hphi b hb
      have h1 := hrest N M hN0 hNM c hc hc2 S hS
      have h2 := h1 true
      have h3 := h2 hratio
      rcases h3 with ⟨Bad, hBadMeas, hBadLe, hBadRest⟩
      refine ⟨Bad, hBadMeas, hBadLe, ?_⟩
      intro omega homega
      exact aux_lem_finite_source_comparison_stopping_of_cells_dir d (closedCube z r hr : Set (SpatialCoordinates d))
        z r hr rfl N
        (cutoffPositiveCoefficient model H omega M z hr)
        (cutoffPositiveCoefficient model H omega N z hr)
        (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)))
        (c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom))
        (hBadRest omega homega true).1 hP phi hphi b hb
  · intro L model Rm Sreg It H hH hsmall z r hr htriadic Q closedQ eta heta
    have hmodel := hbody model Rm Sreg It H hH hsmall z r hr htriadic eta heta
    rcases hmodel with ⟨Ceta, gamma, N0, hCeta, hgamma, hrest⟩
    refine ⟨Ceta, gamma, N0, hCeta, hgamma, ?_⟩
    intro N M hN0 hNM c hc hc2 S hS reverse Nt Ns kappa hratio
    have h1 := hrest N M hN0 hNM c hc hc2 S hS
    have h2 := h1 reverse
    have h3 := h2 hratio
    rcases h3 with ⟨Bad, hBadMeas, hBadLe, hBadRest⟩
    refine ⟨Bad, hBadMeas, hBadLe, ?_⟩
    intro omega homega infrared
    classical
    have hcoef : ∃ A : SpatialCoordinates d → ℝ,
        ContinuousOn A (closedCube z r hr : Set (SpatialCoordinates d)) ∧
        (((cutoffPositiveCoefficient model (if infrared then H else 0) omega
            (if reverse then M else N) z hr).val : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] A) := by
      let a := cutoffCoefficientCM model (if infrared then H else 0) omega
        (if reverse then M else N) z hr
      have hfact : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
          (closedCube z r hr : Set (SpatialCoordinates d))) :=
        ⟨centeredCube_subset_closedCube z hr⟩
      refine ⟨fun x => if hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d))
        then a ⟨x, hx⟩ / 1 else 0, ?_, ?_⟩
      · rw [continuousOn_iff_continuous_domRestrict]
        have hres : (closedCube z r hr : Set (SpatialCoordinates d)).domRestrict
            (fun x => if hx : x ∈ (closedCube z r hr : Set (SpatialCoordinates d))
              then a ⟨x, hx⟩ / 1 else 0) = fun x => a x / 1 := by
          funext x
          simp only [Set.domRestrict_apply, Subtype.coe_prop, dite_eq_left]
          rfl
        rw [hres]
        exact a.continuous.div_const 1
      · have hco := normalizedContinuousPositiveCoefficient_coeFn
          (Ω := centeredCube z r hr) (closedCube z r hr) a
          (cutoffCoefficientCM_pos model (if infrared then H else 0) omega
            (if reverse then M else N) z hr) 1 one_pos
        filter_upwards [hco, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet]
          with x h1 h2
        have e : ((cutoffPositiveCoefficient model (if infrared then H else 0) omega
            (if reverse then M else N) z hr).val : SpatialCoordinates d → ℝ) x =
            a ⟨x, hfact.out h2⟩ / 1 := h1 h2
        rw [e, dite_eq_left (hfact.out h2)]
    exact lem_finite_source_comparison_trial d hd (closedCube z r hr) z r hr rfl
      (by
        show (closedCube z r hr : Set (SpatialCoordinates d)) =
          closure (centeredCube z r hr : Set (SpatialCoordinates d))
        rw [show (closedCube z r hr : Set (SpatialCoordinates d)) =
              Metric.closedBall z (r / 2) from rfl,
            show ((centeredCube z r hr : Opens (SpatialCoordinates d)) :
              Set (SpatialCoordinates d)) = Metric.ball z (r / 2) from rfl,
            closure_ball z (ne_of_gt (half_pos hr))])
      N
      (cutoffPositiveCoefficient model (if infrared then H else 0) omega
        (if reverse then M else N) z hr)
      (cutoffPositiveCoefficient model (if infrared then H else 0) omega
        (if reverse then N else M) z hr)
      hcoef
      (Ceta * 3 ^ (-gamma * (N : ℝ)))
      (c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom))
      (hBadRest omega homega infrared).1 (hBadRest omega homega infrared).2


end SubdiffusiveProcess.Paper
