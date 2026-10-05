module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Paper.lem_finite_stopping_partition
public import SubdiffusiveProcess.Paper.lem_finite_stopping_gluing
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Paper.cutoff_good_scale_input
public import SubdiffusiveProcess.Paper.deterministic_good_scale_input
public import SubdiffusiveProcess.Paper.sum_errors_baseline_input
public import SubdiffusiveProcess.ResponseMoments.Interfaces

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

lemma aux_lem_finite_stopping_glue
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    let Q := centeredCube z r hr
    ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph Q,
      ‖(u : SobolevData Q).1‖ ≤ K * ‖@subspaceGradient d Q (killedSobolevGraph Q) u‖,
    ∀ (ncell : ℕ) (centers : Fin ncell → SpatialCoordinates d)
      (sides : Fin ncell → ℝ) (hside : ∀ i, 0 < sides i),
    let cell := fun i => centeredCube (centers i) (sides i) (hside i)
    ∀ (hle : ∀ i, cell i ≤ Q)
      (_hdisjoint : ∀ ⦃i j : Fin ncell⦄, i ≠ j →
        Disjoint (cell i : Set (SpatialCoordinates d)) (cell j : Set (SpatialCoordinates d)))
      (_hcover : (⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
        (Q : Set (SpatialCoordinates d)))
      (hPcell : ∀ i, ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (cell i),
        ‖(v : SobolevData (cell i)).1‖ ≤
          K * ‖@subspaceGradient d (cell i) (killedSobolevGraph (cell i)) v‖)
      (a : PositiveCoefficient Q) (b u : weakSobolevGraph Q)
      (_hu : u.val - b.val ∈ killedSobolevGraph Q),
    @dirichletResponse d Q (@killedResponseSpace d Q hP) a b ≤
      ∑ i : Fin ncell,
        @dirichletResponse d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
          (positiveCoefficientRestrict (hle i) a)
          ⟨sobolevDataRestrict (hle i) u.val,
            sobolevDataRestrict_mem_weak (hle i) u.property⟩ := by
  intro Q hP ncell centers sides hside cell hle hdisjoint hcover hPcell a b u hu
  obtain ⟨v, hvb, hvcell, hvenergy, hresponse⟩ :=
    lem_finite_stopping_gluing d z r hr hP ncell centers sides hside
      hle hdisjoint hcover hPcell a b u hu
  exact hresponse

lemma aux_lem_finite_stopping_from_cell
    (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖@subspaceGradient d (centeredCube z r hr)
          (killedSobolevGraph (centeredCube z r hr)) u‖)
    (N : ℕ) (aTarget : PositiveCoefficient (centeredCube z r hr))
    (b u : weakSobolevGraph (centeredCube z r hr))
    (hu : u.val - b.val ∈ killedSobolevGraph (centeredCube z r hr)) {R : ℝ}
    (hcell : ∃ (ncell : ℕ) (centers : Fin ncell → SpatialCoordinates d)
      (sides : Fin ncell → ℝ) (hside : ∀ i, 0 < sides i),
      ∃ hle : ∀ i, centeredCube (centers i) (sides i) (hside i) ≤ centeredCube z r hr,
        (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
          (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
        Pairwise (fun i j =>
          Disjoint (centeredCube (centers i) (sides i) (hside i) : Set (SpatialCoordinates d))
            (centeredCube (centers j) (sides j) (hside j) : Set (SpatialCoordinates d))) ∧
        ((⋃ i, (centeredCube (centers i) (sides i) (hside i) : Set (SpatialCoordinates d)))
          =ᵐ[volume] (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        ∃ hPcell : ∀ i, ∃ K : ℝ≥0, ∀ v : killedSobolevGraph
            (centeredCube (centers i) (sides i) (hside i)),
          ‖(v : SobolevData (centeredCube (centers i) (sides i) (hside i))).1‖ ≤
            K * ‖@subspaceGradient d (centeredCube (centers i) (sides i) (hside i))
              (killedSobolevGraph (centeredCube (centers i) (sides i) (hside i))) v‖,
        let bcell : ∀ i, weakSobolevGraph (centeredCube (centers i) (sides i) (hside i)) :=
          fun i => ⟨sobolevDataRestrict (hle i) u.val,
            sobolevDataRestrict_mem_weak (hle i) u.property⟩
        (∑ i : Fin ncell,
          @dirichletResponse d (centeredCube (centers i) (sides i) (hside i))
            (@killedResponseSpace d (centeredCube (centers i) (sides i) (hside i)) (hPcell i))
            (positiveCoefficientRestrict (hle i) aTarget) (bcell i)) ≤ R) :
    @dirichletResponse d (centeredCube z r hr)
      (@killedResponseSpace d (centeredCube z r hr) hP) aTarget b ≤ R := by
  obtain ⟨ncell, centers, sides, hside, hle, hgeom, hdisjoint, hcover,
    hPcell, henergy⟩ := hcell
  dsimp only at henergy
  have hresponse := aux_lem_finite_stopping_glue d z r hr hP ncell centers sides hside
    hle hdisjoint hcover hPcell aTarget b u hu
  exact hresponse.trans henergy

lemma aux_lem_finite_stopping_target_cell
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (omega : BilateralField d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (Nfloor target source : ℕ)
    (hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖@subspaceGradient d (centeredCube z r hr)
          (killedSobolevGraph (centeredCube z r hr)) u‖)
    (b : weakSobolevGraph (centeredCube z r hr)) {R : ℝ}
    (hcell :
      let aTarget := cutoffPositiveCoefficient model H omega target z hr
      let aSource := cutoffPositiveCoefficient model H omega source z hr
      let u := @dirichletMinimizer d (centeredCube z r hr)
        (@killedResponseSpace d (centeredCube z r hr) hP) aSource b
      ∃ (ncell : ℕ) (centers : Fin ncell → SpatialCoordinates d)
        (sides : Fin ncell → ℝ) (hside : ∀ i, 0 < sides i),
        let cell := fun i => centeredCube (centers i) (sides i) (hside i)
        ∃ hle : ∀ i, cell i ≤ centeredCube z r hr,
        (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
          (3 : ℝ) ^ (-(Nfloor : ℤ)) ≤ sides i) ∧
        Pairwise (fun i j => Disjoint (cell i : Set (SpatialCoordinates d))
          (cell j : Set (SpatialCoordinates d))) ∧
        ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
          (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        ∃ hPcell : ∀ i, ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (cell i),
          ‖(v : SobolevData (cell i)).1‖ ≤
            K * ‖@subspaceGradient d (cell i) (killedSobolevGraph (cell i)) v‖,
        let bcell : ∀ i, weakSobolevGraph (cell i) := fun i =>
          ⟨sobolevDataRestrict (hle i) u.val,
            sobolevDataRestrict_mem_weak (hle i) u.property⟩
        (∑ i : Fin ncell,
          @dirichletResponse d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
            (positiveCoefficientRestrict (hle i) aTarget) (bcell i)) ≤ R) :
    let aTarget := cutoffPositiveCoefficient model H omega target z hr
    @dirichletResponse d (centeredCube z r hr)
      (@killedResponseSpace d (centeredCube z r hr) hP) aTarget b ≤ R := by
  dsimp only at hcell ⊢
  let aTarget := cutoffPositiveCoefficient model H omega target z hr
  let aSource := cutoffPositiveCoefficient model H omega source z hr
  let u : weakSobolevGraph (centeredCube z r hr) :=
    @dirichletMinimizer d (centeredCube z r hr)
      (@killedResponseSpace d (centeredCube z r hr) hP) aSource b
  have hu : u.val - b.val ∈ killedSobolevGraph (centeredCube z r hr) := by
    simpa [u] using!
      (dirichletMinimizer_mem_affine
        (@killedResponseSpace d (centeredCube z r hr) hP) aSource b)
  exact aux_lem_finite_stopping_from_cell d z r hr hP Nfloor aTarget b u hu hcell

lemma aux_lem_finite_stopping_forward_result
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (H1 : ℕ) (Dgeom Cgeom eta Ceta gamma : ℝ) (N M : ℕ) (c : ℝ) (Nfloor : ℕ)
    (hpartition :
      ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
        ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖@subspaceGradient d (centeredCube z r hr)
            (killedSobolevGraph (centeredCube z r hr)) u‖,
      ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
      ∀ b : weakSobolevGraph (centeredCube z r hr),
        ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
      ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
        (chaosSampleLaw model).toMeasure Bad ≤
          ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (Nfloor : ℝ))) ∧
        ∀ omega ∉ Bad,
        let aTarget := cutoffPositiveCoefficient model H omega N z hr
        let aSource := cutoffPositiveCoefficient model H omega M z hr
        let u := @dirichletMinimizer d (centeredCube z r hr)
          (@killedResponseSpace d (centeredCube z r hr) hP) aSource b
        ∃ (ncell : ℕ) (centers : Fin ncell → SpatialCoordinates d)
          (sides : Fin ncell → ℝ) (hside : ∀ i, 0 < sides i),
          let cell := fun i => centeredCube (centers i) (sides i) (hside i)
          ∃ hle : ∀ i, cell i ≤ centeredCube z r hr,
          (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
            (3 : ℝ) ^ (-(Nfloor : ℤ)) ≤ sides i) ∧
          Pairwise (fun i j => Disjoint (cell i : Set (SpatialCoordinates d))
            (cell j : Set (SpatialCoordinates d))) ∧
          ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
            (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
          ∃ hPcell : ∀ i, ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (cell i),
            ‖(v : SobolevData (cell i)).1‖ ≤
              K * ‖@subspaceGradient d (cell i) (killedSobolevGraph (cell i)) v‖,
          let bcell : ∀ i, weakSobolevGraph (cell i) := fun i =>
            ⟨sobolevDataRestrict (hle i) u.val,
              sobolevDataRestrict_mem_weak (hle i) u.property⟩
          (∑ i : Fin ncell,
            @dirichletResponse d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
              (positiveCoefficientRestrict (hle i) aTarget) (bcell i)) ≤
            c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom) *
              @dirichletResponse d (centeredCube z r hr)
                (@killedResponseSpace d (centeredCube z r hr) hP) aSource b +
            Ceta * (3 : ℝ) ^ (-gamma * (Nfloor : ℝ)) *
              (c2Norm (closedCube z r hr) phi) ^ 2) :
    ∀ hP : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖@subspaceGradient d (centeredCube z r hr)
          (killedSobolevGraph (centeredCube z r hr)) u‖,
    ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ phi →
    ∀ b : weakSobolevGraph (centeredCube z r hr),
      ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi →
    ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
      (chaosSampleLaw model).toMeasure Bad ≤
        ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (Nfloor : ℝ))) ∧
      ∀ omega ∉ Bad,
      let aN := cutoffPositiveCoefficient model H omega N z hr
      let aM := cutoffPositiveCoefficient model H omega M z hr
      @dirichletResponse d (centeredCube z r hr)
        (@killedResponseSpace d (centeredCube z r hr) hP) aN b ≤
        c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom) *
          @dirichletResponse d (centeredCube z r hr)
            (@killedResponseSpace d (centeredCube z r hr) hP) aM b +
        Ceta * (3 : ℝ) ^ (-gamma * (Nfloor : ℝ)) *
          (c2Norm (closedCube z r hr) phi) ^ 2 := by
  intro hP phi hphi b hb
  obtain ⟨Bad, hBad, hBadProb, hcell⟩ := hpartition hP phi hphi b hb
  refine ⟨Bad, hBad, hBadProb, ?_⟩
  intro omega hnot
  exact aux_lem_finite_stopping_target_cell d model H omega z r hr Nfloor N M hP b
    (hcell omega hnot)

lemma aux_lem_finite_stopping_inner
    (d : ℕ) [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (Jc : in_J d)
    (theta : ℝ) (H1 : ℕ) (Dgeom Cgeom delta0 : ℝ)
    (hpart :
      let L : ℝ := (3 : ℝ) ^ H1
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (_Rm : in_responses d model) (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (_hH : InfraredCharacterization model H) (_hsmall : model.delta ≤ delta0)
        (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (_htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
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
      ∀ reverse : Bool,
      let target := if reverse then M else N
      let source := if reverse then N else M
      (∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
        (kappa (target - H1 * n) / kappa target) /
            (kappa (source - H1 * n) / kappa source) ≤ c) →
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
        let aTarget := cutoffPositiveCoefficient model H omega target z hr
        let aSource := cutoffPositiveCoefficient model H omega source z hr
        let u := @dirichletMinimizer d Q (@killedResponseSpace d Q hP) aSource b
        ∃ (ncell : ℕ) (centers : Fin ncell → SpatialCoordinates d)
          (sides : Fin ncell → ℝ) (hside : ∀ i, 0 < sides i),
        let cell := fun i => centeredCube (centers i) (sides i) (hside i)
        ∃ hle : ∀ i, cell i ≤ Q,
        (∀ i, (∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
          (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧
        Pairwise (fun i j => Disjoint (cell i : Set (SpatialCoordinates d))
          (cell j : Set (SpatialCoordinates d))) ∧
        ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
          (Q : Set (SpatialCoordinates d))) ∧
        ∃ hPcell : ∀ i, ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (cell i),
          ‖(v : SobolevData (cell i)).1‖ ≤
            K * ‖@subspaceGradient d (cell i) (killedSobolevGraph (cell i)) v‖,
        let bcell : ∀ i, weakSobolevGraph (cell i) := fun i =>
          ⟨sobolevDataRestrict (hle i) u.val,
            sobolevDataRestrict_mem_weak (hle i) u.property⟩
        (∑ i : Fin ncell,
          @dirichletResponse d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
            (positiveCoefficientRestrict (hle i) aTarget) (bcell i)) ≤
          c * (1 + Cgeom * eta * L ^ Dgeom) *
            @dirichletResponse d Q (@killedResponseSpace d Q hP) aSource b +
          Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm closedQ phi) ^ 2) :
    let L : ℝ := (3 : ℝ) ^ H1
    ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
      (_Rm : in_responses d model) (Sreg : in_6_16 d model) (_It : in_iteration d model Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (_hH : InfraredCharacterization model H) (_hsmall : model.delta ≤ delta0)
      (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (_htriadic : ∃ j : ℤ, r = (3 : ℝ) ^ j),
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
          Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm closedQ phi) ^ 2) := by
  dsimp only
  intro model Rm Sreg It H hH hsmall z r hr htriadic eta heta
  obtain ⟨Ceta, gamma, N0, hCeta, hgamma, hpart⟩ :=
    hpart model Rm Sreg It H hH hsmall z r hr htriadic eta heta
  refine ⟨Ceta, gamma, N0, hCeta, hgamma, ?_⟩
  intro N M hN hNM c hc hc2 S hS
  have hpartNM := hpart N M hN hNM c hc hc2 S hS
  constructor
  · intro hratio
    simpa only [Bool.false_eq_true, ↓reduceIte] using
      (aux_lem_finite_stopping_forward_result d model H z r hr H1 Dgeom Cgeom eta Ceta gamma
        N M c N (hpartNM false hratio))
  · intro hratio
    simpa only [Bool.true_eq_false, ↓reduceIte] using
      (aux_lem_finite_stopping_forward_result d model H z r hr H1 Dgeom Cgeom eta Ceta gamma
        M N c N (hpartNM true hratio))



theorem lem_finite_stopping
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : SobolevFoundationalInput d hd) (W : SmallPerturbationInput d) (Cp : CampanatoInput d)
    (Step : @cutoff_good_scale_input d ⟨by omega⟩)
    (D : @deterministic_good_scale_input d ⟨by omega⟩)
    (hES : _root_.SubdiffusiveProcess.ResponseMoments.EfronSteinMomentInequality)
    (Dbase : @sum_errors_baseline_input d ⟨by omega⟩ _ _)
    (theta : ℝ) (htheta : 0 < theta) :
    ∃ (H1 : ℕ) (Dgeom Cgeom delta0 : ℝ),
      0 < H1 ∧ 0 < Dgeom ∧ 0 < Cgeom ∧ 0 < delta0 ∧
      let L : ℝ := (3 : ℝ) ^ H1
      ∀ (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
        (Rm : in_responses d model) (Sreg : in_6_16 d model) (It : in_iteration d model Jc Sreg)
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
      Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)) * (c2Norm closedQ phi) ^ 2) := by
  obtain ⟨H1, Dgeom, Cgeom, delta0, hH1, hDgeom, hCgeom, hdelta0, hpart⟩ :=
    lem_finite_stopping_partition d hd Jc Pc Xc Sf W Cp Step D hES Dbase theta htheta
  refine ⟨H1, Dgeom, Cgeom, delta0, hH1, hDgeom, hCgeom, hdelta0, ?_⟩
  exact aux_lem_finite_stopping_inner d Jc theta H1 Dgeom Cgeom delta0 hpart

end SubdiffusiveProcess.Paper
