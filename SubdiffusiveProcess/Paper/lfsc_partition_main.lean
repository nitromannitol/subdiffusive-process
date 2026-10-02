import SubdiffusiveProcess.Paper.lfsc_partition_assembly
import SubdiffusiveProcess.Paper.lfsc_partition_main_sample
import SubdiffusiveProcess.Paper.lfsc_good_steps_src_constants
import SubdiffusiveProcess.Paper.lfsc_childB_src_dir
import SubdiffusiveProcess.Paper.lfsc_childB_src_neu
import SubdiffusiveProcess.Paper.inputs_step_witness
import SubdiffusiveProcess.Paper.inputs_hES_witness
import SubdiffusiveProcess.Paper.inputs_baseline_witness

/-!
# `lfsc_partition_main` — the sourced stopping partition (statement of `aux_lem_finite_source_comparison_cells_partition`)

Paper `\label{mfd:lem-finite-source-comparison}` (proof, first two paragraphs and last paragraph), on top of the
construction of `\label{mfd:lem-finite-stopping}`: "we use the partition of the proof of Lemma `mfd:lem-finite-stopping`,
now with `λ = Γ_M(u_M) + 3^{-ζN} B² dx`".  The definitions `partDir`/`partNeu` are the verbatim bodies of the FSCC ones
(the FSCC statement unfolds to this one by `exact`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace Topology Metric ProbabilityTheory
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open SubdiffusiveProcess.FiniteStopping
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace Paper

/-- Sourced partition, Dirichlet branch, one sample (paper 4310--4329, 4331): every Dirichlet
source solution has an actual covering triadic partition, sides in `[3^{-N}, smax]`, with the
target-cell energy bound.  No representative, oscillation or Hölder datum. -/
def aux_lfsc_partition_main_partDir (d : ℕ) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (N : ℕ) (smax : ℝ) (aTarget aSource : PositiveCoefficient (centeredCube z r hr))
    (err factor : ℝ) : Prop :=
  let Q := centeredCube z r hr
  let closedQ := closedCube z r hr
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
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
          (∀ i, ((∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
            (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧ sides i ≤ smax) ∧
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
            (∑ i : Fin ncell,
              @dirichletResponse d (cell i)
                (@killedResponseSpace d (cell i) (hPcell i))
                (positiveCoefficientRestrict (hle i) aTarget)
                ⟨sobolevDataRestrict (hle i) u.val,
                  sobolevDataRestrict_mem_weak (hle i) u.property⟩) ≤
              factor * sobolevCoefficientForm aSource u.val u.val +
                err * (Kf + c2Norm closedQ phi) ^ 2

/-- Sourced partition, mean-zero Neumann branch, one sample. -/
def aux_lfsc_partition_main_partNeu (d : ℕ) (z : SpatialCoordinates d) (r : ℝ)
    (hr : 0 < r) (N : ℕ) (smax : ℝ) (aTarget aSource : PositiveCoefficient (centeredCube z r hr))
    (err factor : ℝ) : Prop :=
  let Q := centeredCube z r hr
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
    0 ≤ Kf → Measurable F → (∀ x ∈ Q, |F x| ≤ Kf) →
    (∫ x in (Q : Set (SpatialCoordinates d)), F x) = 0 →
    ∀ u : meanZeroSobolevGraph Q, SolvesNeumann aSource F u →
    ∃ ncell : ℕ, ∃ centers : Fin ncell → SpatialCoordinates d,
      ∃ sides : Fin ncell → ℝ, ∃ hside : ∀ i, 0 < sides i,
      let cell := fun i => centeredCube (centers i) (sides i) (hside i)
      ∃ hle : ∀ i, cell i ≤ Q,
        (∀ i, ((∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
          (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧ sides i ≤ smax) ∧
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
          (∑ i : Fin ncell,
            @dirichletResponse d (cell i)
              (@killedResponseSpace d (cell i) (hPcell i))
              (positiveCoefficientRestrict (hle i) aTarget)
              ⟨sobolevDataRestrict (hle i) u.val,
                sobolevDataRestrict_mem_weak (hle i)
                  ((mem_meanZeroSobolevGraph_iff u.val).mp u.property).1⟩) ≤
            factor * sobolevCoefficientForm aSource u.val u.val +
              err * Kf ^ 2



/-- Weight factors: `(1+ρ) c (1+X) ≤ c (1 + (Cg+1) η L^D)` when `ρ(1+X) ≤ η`, `X = Cg η L^D`, `L^D ≥ 1`. -/
theorem aux_lfsc_main_factor (c Cg eta LD rho : ℝ) (hc : 0 ≤ c) (hCg : 0 ≤ Cg) (heta : 0 ≤ eta)
    (hLD : 1 ≤ LD) (hrho0 : 0 ≤ rho) (hrho : rho * (1 + Cg * eta * LD) ≤ eta) :
    (1 + rho) * c * (1 + Cg * eta * LD) ≤ c * (1 + (Cg + 1) * eta * LD) := by
  have h1 : c * (rho * (1 + Cg * eta * LD)) ≤ c * eta := mul_le_mul_of_nonneg_left hrho hc
  have h2 : c * eta ≤ c * (eta * LD) := mul_le_mul_of_nonneg_left (by nlinarith) hc
  nlinarith

theorem aux_lfsc_main_finish (S' c' X E factor errS errT : ℝ) (hsum : S' ≤ c' * (1 + X) * E + errS)
    (hE : 0 ≤ E) (hfac : c' * (1 + X) ≤ factor) (herr : errS = errT) : S' ≤ factor * E + errT := by
  rw [← herr]
  have := mul_le_mul_of_nonneg_right hfac hE
  linarith

theorem aux_lfsc_partDir_mono (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ) (smax : ℝ)
    (aTarget aSource : PositiveCoefficient (centeredCube z r hr)) (err factor factor' : ℝ)
    (h : aux_lfsc_partition_main_partDir d z r hr N smax aTarget aSource err factor)
    (hf : factor ≤ factor') :
    aux_lfsc_partition_main_partDir d z r hr N smax aTarget aSource err factor' := by
  dsimp only [aux_lfsc_partition_main_partDir] at h ⊢
  intro F Kf hKf hFm hFb phi hphi b u hb hsol
  obtain ⟨ncell, centers, sides, hside, hle, hs, hd', hc', hP, hsum⟩ :=
    h F Kf hKf hFm hFb phi hphi b u hb hsol
  refine ⟨ncell, centers, sides, hside, hle, hs, hd', hc', hP, hsum.trans ?_⟩
  have := mul_le_mul_of_nonneg_right hf (sobolevCoefficientForm_nonneg aSource (u : SobolevData _))
  linarith

theorem aux_lfsc_partNeu_mono (d : ℕ) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) (N : ℕ) (smax : ℝ)
    (aTarget aSource : PositiveCoefficient (centeredCube z r hr)) (err factor factor' : ℝ)
    (h : aux_lfsc_partition_main_partNeu d z r hr N smax aTarget aSource err factor)
    (hf : factor ≤ factor') :
    aux_lfsc_partition_main_partNeu d z r hr N smax aTarget aSource err factor' := by
  dsimp only [aux_lfsc_partition_main_partNeu] at h ⊢
  intro F Kf hKf hFm hFb hFint u hsol
  obtain ⟨ncell, centers, sides, hside, hle, hs, hd', hc', hP, hsum⟩ :=
    h F Kf hKf hFm hFb hFint u hsol
  refine ⟨ncell, centers, sides, hside, hle, hs, hd', hc', hP, hsum.trans ?_⟩
  have := mul_le_mul_of_nonneg_right hf (sobolevCoefficientForm_nonneg aSource (u : SobolevData _))
  linarith



/-- The crude lower bound of the reference scale at every stage-2 cell (clause (i) of the sourced ChildB). -/
def aux_lfsc_partition_main_hiProp {d : ℕ} [NeZero d] (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Hused : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (z : SpatialCoordinates d) (j : ℤ) (hr : 0 < (3 : ℝ) ^ j) (H1 N M : ℕ) (reverse : Bool)
    (theta eps : ℝ) : Prop :=
  ∀ (w0 : Fin (obsT0 H1 N j) → OddGridIndex d 1) (s : ℕ)
        (w : Fin s → OddGridIndex d (subdivisionHalfWidth H1)), s ≤ obsB H1 N →
      (reference model Hused omega (if reverse then N else M) (H1 * (obsLo H1 N + s))
        (descendantCenter (subdivisionHalfWidth H1)
          (descendantCenter 1 z ((3 : ℝ) ^ j) (obsT0 H1 N j) w0)
          (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j)) s w))⁻¹ ≤
        (3 : ℝ) ^ (eps * (N : ℝ)) *
          (descendantSide (subdivisionHalfWidth H1) s
            (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ (-(min (theta / 16) 1 / 2))

/-- Global energy and residual-leaf cost for every Dirichlet source solution (clauses (ii),(iii) of the sourced ChildB). -/
def aux_lfsc_partition_main_dataDProp {d : ℕ} [NeZero d] (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Hused : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (z : SpatialCoordinates d) (j : ℤ) (hr : 0 < (3 : ℝ) ^ j) (H1 N M : ℕ) (reverse : Bool)
    (theta eps : ℝ) : Prop :=
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf → Measurable F →
      (∀ x ∈ centeredCube z ((3 : ℝ) ^ j) hr, |F x| ≤ Kf) →
      ∀ phi : SpatialCoordinates d → ℝ, ContDiff ℝ 2 phi →
      ∀ b u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr),
        ((b : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d))] phi →
        SolvesDirichlet (cutoffPositiveCoefficient model Hused omega (if reverse then N else M) z hr) F b u →
        (∀ (w0 : Fin (obsT0 H1 N j) → OddGridIndex d 1)
            (w : Fin (obsB H1 N) → OddGridIndex d (subdivisionHalfWidth H1)),
          respOn (cutoffPositiveCoefficient model Hused omega (if reverse then M else N) z hr) u
              (cell2_le_root z hr (obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (obsB H1 N) w)
              (cell2_killedPoincare z hr (obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (obsB H1 N) w) ≤
            (3 : ℝ) ^ (eps * (N : ℝ)) *
              (descendantSide (subdivisionHalfWidth H1) (obsB H1 N)
                (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ ((d : ℝ) - theta / 16) *
              (Kf + c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi) ^ 2) ∧
        energyOn (cutoffPositiveCoefficient model Hused omega (if reverse then N else M) z hr)
            (u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr))
            (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) ≤
          (3 : ℝ) ^ (eps * (N : ℝ)) *
            (Kf + c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi) ^ 2

/-- The same for every mean-zero Neumann source solution. -/
def aux_lfsc_partition_main_dataNProp {d : ℕ} [NeZero d] (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Hused : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (z : SpatialCoordinates d) (j : ℤ) (hr : 0 < (3 : ℝ) ^ j) (H1 N M : ℕ) (reverse : Bool)
    (theta eps : ℝ) : Prop :=
  ∀ (F : SpatialCoordinates d → ℝ) (Kf : ℝ), 0 ≤ Kf → Measurable F →
      (∀ x ∈ centeredCube z ((3 : ℝ) ^ j) hr, |F x| ≤ Kf) →
      (∫ x in (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)), F x) = 0 →
      ∀ u : meanZeroSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr),
        SolvesNeumann (cutoffPositiveCoefficient model Hused omega (if reverse then N else M) z hr) F u →
        (∀ (w0 : Fin (obsT0 H1 N j) → OddGridIndex d 1)
            (w : Fin (obsB H1 N) → OddGridIndex d (subdivisionHalfWidth H1)),
          respOn (cutoffPositiveCoefficient model Hused omega (if reverse then M else N) z hr)
              (⟨(u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)),
                ((mem_meanZeroSobolevGraph_iff u.val).mp u.property).1⟩ :
                weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
              (cell2_le_root z hr (obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (obsB H1 N) w)
              (cell2_killedPoincare z hr (obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (obsB H1 N) w) ≤
            (3 : ℝ) ^ (eps * (N : ℝ)) *
              (descendantSide (subdivisionHalfWidth H1) (obsB H1 N)
                (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ ((d : ℝ) - theta / 16) * Kf ^ 2) ∧
        energyOn (cutoffPositiveCoefficient model Hused omega (if reverse then N else M) z hr)
            (u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr))
            (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) ≤
          (3 : ℝ) ^ (eps * (N : ℝ)) * Kf ^ 2

open Classical in
/-- One root, one infrared coefficient `Hused`, one exceptional-event complement: the sourced partition of both branches. -/
theorem aux_lfsc_main_flag {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Hused : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (z : SpatialCoordinates d) (j : ℤ) (hr : 0 < (3 : ℝ) ^ j)
    (H1 : ℕ) (hH1 : 0 < H1) (P a0 : ℕ) (ha0 : d * (2 * P) ≤ 3 ^ a0) (h8a0 : 8 * a0 ≤ H1)
    (theta : ℝ) (htheta : 0 < theta) (hH1θ : 12 ≤ theta * (H1 : ℝ)) (Dg : ℝ) (hDg : 0 < Dg)
    (hDθ : theta / 64 + 1 + 3 * (d : ℝ) / 4 ≤ theta * Dg / 16)
    (Cg eta : ℝ) (hCg : 0 < Cg) (heta : 0 < eta) (c2n : ℕ)
    (hc2n : 1 + ((3 : ℝ) ^ j) ^ d < (3 : ℝ) ^ c2n)
    (CA CB γ : ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hγz : γ ≤ 1 / 8) (hγ13 : γ ≤ 13 / 64 * theta)
    (eps : ℝ) (heps0 : 0 ≤ eps) (hepsθ : eps ≤ theta / 64) (hεζ : eps + 1 / 8 ≤ 3 / 8)
    (N M : ℕ) (hNH : 4 * H1 ≤ N) (hNj : 4 * j.natAbs ≤ N)
    (c : ℝ) (hc : 0 < c) (hc4 : c ≤ 4) (S : ℕ → Prop)
    (hS : theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
      (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ))
    (reverse : Bool) (wt : ℝ) (hwt : 0 ≤ wt)
    (hratio : ∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
      wt * kappaRatio model H1 (if reverse then M else N) (if reverse then N else M) n ≤ c)
    (hgood : good_steps_src_at model Hused P H1 (theta / 16) Cg eta wt z j N M reverse omega)
    (hi : aux_lfsc_partition_main_hiProp model Hused omega z j hr H1 N M reverse theta eps)
    (hdataD : aux_lfsc_partition_main_dataDProp model Hused omega z j hr H1 N M reverse theta eps)
    (hdataN : aux_lfsc_partition_main_dataNProp model Hused omega z j hr H1 N M reverse theta eps) :
    aux_lfsc_partition_main_partDir d z ((3 : ℝ) ^ j) hr N (1 * (3 : ℝ) ^ (-((N : ℝ) / 4)))
        (cutoffPositiveCoefficient model Hused omega (if reverse then M else N) z hr)
        (cutoffPositiveCoefficient model Hused omega (if reverse then N else M) z hr)
        (((CA + CB + 4 * (Cg * eta) * ((3 : ℝ) ^ H1) ^ Dg * ((3 : ℝ) ^ j) ^ d +
          (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + (7 / 8) * (theta * H1 + 2 * H1 + (c2n : ℝ) / Dg)))) *
            (3 : ℝ) ^ (-γ * (N : ℝ)))
        (c * (1 + Cg * eta * ((3 : ℝ) ^ H1) ^ Dg)) ∧
    aux_lfsc_partition_main_partNeu d z ((3 : ℝ) ^ j) hr N (1 * (3 : ℝ) ^ (-((N : ℝ) / 4)))
        (cutoffPositiveCoefficient model Hused omega (if reverse then M else N) z hr)
        (cutoffPositiveCoefficient model Hused omega (if reverse then N else M) z hr)
        (((CA + CB + 4 * (Cg * eta) * ((3 : ℝ) ^ H1) ^ Dg * ((3 : ℝ) ^ j) ^ d +
          (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + (7 / 8) * (theta * H1 + 2 * H1 + (c2n : ℝ) / Dg)))) *
            (3 : ℝ) ^ (-γ * (N : ℝ)))
        (c * (1 + Cg * eta * ((3 : ℝ) ^ H1) ^ Dg)) := by
  classical
  constructor
  · dsimp only [aux_lfsc_partition_main_partDir]
    intro F Kf hKf hFm hFb phi hphi b u hb hsolves
    have hc2N : 0 ≤ c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi :=
      aux_lem_finite_stopping_partition_c2Norm_nonneg _ _
    obtain ⟨hcr, hgl⟩ := hdataD F Kf hKf hFm hFb phi hphi b u hb hsolves
    obtain ⟨ncell, centers, sides, hside, hle, hsides, hdisj, hcov, hPcell, hsum⟩ :=
      lfsc_partition_main_sample hd model Hused omega z j hr H1 hH1 P a0 ha0 h8a0 theta htheta hH1θ Dg hDg hDθ
        Cg eta hCg heta c2n hc2n CA CB γ hCA hCB (1 / 8) (by norm_num) (by norm_num) hγz hγ13 eps
        heps0 hepsθ hεζ N M hNH hNj c hc hc4 S hS reverse wt hwt hratio hgood hi u F Kf hFm hKf hFb
        hsolves.2 (Kf + c2Norm (closedCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) phi)
        (add_nonneg hKf hc2N) (le_add_of_nonneg_right hc2N) hcr hgl
    refine ⟨ncell, centers, sides, hside, hle, ?_, hdisj, hcov, hPcell, ?_⟩
    · intro i
      exact ⟨(hsides i).1, by simpa only [one_mul] using (hsides i).2⟩
    · rw [aux_lem_finite_stopping_partition_sobolevCoefficientForm_self_eq_energyOn]
      exact hsum
  · dsimp only [aux_lfsc_partition_main_partNeu]
    intro F Kf hKf hFm hFb hFint u hsolves
    obtain ⟨hcr, hgl⟩ := hdataN F Kf hKf hFm hFb hFint u hsolves
    obtain ⟨ncell, centers, sides, hside, hle, hsides, hdisj, hcov, hPcell, hsum⟩ :=
      lfsc_partition_main_sample hd model Hused omega z j hr H1 hH1 P a0 ha0 h8a0 theta htheta hH1θ Dg hDg hDθ
        Cg eta hCg heta c2n hc2n CA CB γ hCA hCB (1 / 8) (by norm_num) (by norm_num) hγz hγ13 eps
        heps0 hepsθ hεζ N M hNH hNj c hc hc4 S hS reverse wt hwt hratio hgood hi
        (⟨(u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)),
          ((mem_meanZeroSobolevGraph_iff u.val).mp u.property).1⟩ :
          weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
        F Kf hFm hKf hFb
        (fun psi => hsolves ⟨psi.val, killedSobolevGraph_le_weakSobolevGraph psi.property⟩)
        Kf hKf le_rfl hcr hgl
    refine ⟨ncell, centers, sides, hside, hle, ?_, hdisj, hcov, hPcell, ?_⟩
    · intro i
      exact ⟨(hsides i).1, by simpa only [one_mul] using (hsides i).2⟩
    · rw [aux_lem_finite_stopping_partition_sobolevCoefficientForm_self_eq_energyOn]
      exact hsum



theorem aux_lfsc_main_childB_dir (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (theta : ℝ) (htheta : 0 < theta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d model)
      (Sreg : in_6_16 d model) (It : in_iteration d model E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization model H → model.delta ≤ delta0 →
    ∀ (z : SpatialCoordinates d) (j : ℤ) (H1 : ℕ), 0 < H1 →
    ∀ eps : ℝ, 0 < eps → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
    ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool,
    ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
      (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧
      ∀ omega ∉ Bad, ∀ infrared : Bool,
        @aux_lfsc_partition_main_hiProp d ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ model
          (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega z j
          (zpow_pos (by norm_num) j) H1 N M reverse theta eps ∧
        @aux_lfsc_partition_main_dataDProp d ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ model
          (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega z j
          (zpow_pos (by norm_num) j) H1 N M reverse theta eps := by
  haveI : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  obtain ⟨delta0, hdelta0, h⟩ := lfsc_childB_src_dir d hd E P X Sf W Cp D (theta / 16) (by positivity)
  refine ⟨delta0, hdelta0, ?_⟩
  intro model Rm Sreg It H hH hs z j H1 hH1 eps heps
  exact h model Rm Sreg It H hH hs z j H1 hH1 eps heps


theorem aux_lfsc_main_childB_neu (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (theta : ℝ) (htheta : 0 < theta) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d model)
      (Sreg : in_6_16 d model) (It : in_iteration d model E Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization model H → model.delta ≤ delta0 →
    ∀ (z : SpatialCoordinates d) (j : ℤ) (H1 : ℕ), 0 < H1 →
    ∀ eps : ℝ, 0 < eps → ∃ (C γ : ℝ) (N0 : ℕ), 0 < C ∧ 0 < γ ∧
    ∀ N M : ℕ, N0 ≤ N → N ≤ M → ∀ reverse : Bool,
    ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
      (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (C * (3 : ℝ) ^ (-γ * (N : ℝ))) ∧
      ∀ omega ∉ Bad, ∀ infrared : Bool,
        @aux_lfsc_partition_main_hiProp d ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ model
          (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega z j
          (zpow_pos (by norm_num) j) H1 N M reverse theta eps ∧
        @aux_lfsc_partition_main_dataNProp d ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩ model
          (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ))) omega z j
          (zpow_pos (by norm_num) j) H1 N M reverse theta eps := by
  haveI : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩
  obtain ⟨delta0, hdelta0, h⟩ := lfsc_childB_src_neu d hd E P X Sf W Cp D (theta / 16) (by positivity)
  refine ⟨delta0, hdelta0, ?_⟩
  intro model Rm Sreg It H hH hs z j H1 hH1 eps heps
  exact h model Rm Sreg It H hH hs z j H1 hH1 eps heps

theorem lfsc_partition_main
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E)
    (X : in_extension d hd E) (W : SmallPerturbationInput d)
    (Cp : CampanatoInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (theta : ℝ) (htheta : 0 < theta) :
    ∃ (H1 : ℕ) (Dgeom Cgeom delta0 : ℝ),
      0 < H1 ∧ 0 < Dgeom ∧ 0 < Cgeom ∧ 0 < delta0 ∧
      ∀ (model : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d model)
        (Sreg : in_6_16 d model) (It : in_iteration d model E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization model H → model.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), (∃ j : ℤ, r = (3 : ℝ) ^ j) →
      ∀ eta : ℝ, 0 < eta →
      ∃ (Ceta gamma Cside : ℝ) (N0 : ℕ), 0 < Ceta ∧ 0 < gamma ∧ 0 ≤ Cside ∧
      ∀ (N M : ℕ), N0 ≤ N → N ≤ M →
      ∀ (c : ℝ), 0 < c → c ≤ 2 →
      ∀ (S : ℕ → Prop),
      theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
          (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) →
      ∀ reverse : Bool,
      (∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
        ((Real.exp ((((if reverse then M else N) - H1 * n : ℕ) + 1 : ℝ) *
              SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model ((if reverse then M else N) - H1 * n)) /
          (Real.exp ((((if reverse then M else N : ℕ) : ℝ) + 1) *
              SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model (if reverse then M else N))) /
        ((Real.exp ((((if reverse then N else M) - H1 * n : ℕ) + 1 : ℝ) *
              SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model ((if reverse then N else M) - H1 * n)) /
          (Real.exp ((((if reverse then N else M : ℕ) : ℝ) + 1) *
              SubdiffusiveProcess.Frozen.Assumptions.tauSq model.P) *
            SubdiffusiveProcess.CoarseGrainingVocab.ahom model (if reverse then N else M))) ≤ c) →
      ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
        (chaosSampleLaw model).toMeasure Bad ≤
          ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ))) ∧
        ∀ omega ∉ Bad, ∀ infrared : Bool,
          aux_lfsc_partition_main_partDir d z r hr N
              (Cside * (3 : ℝ) ^ (-((N : ℝ) / 4)))
              (cutoffPositiveCoefficient model
                (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
                omega (if reverse then M else N) z hr)
              (cutoffPositiveCoefficient model
                (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
                omega (if reverse then N else M) z hr)
              (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)))
              (c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom)) ∧
            aux_lfsc_partition_main_partNeu d z r hr N
              (Cside * (3 : ℝ) ^ (-((N : ℝ) / 4)))
              (cutoffPositiveCoefficient model
                (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
                omega (if reverse then M else N) z hr)
              (cutoffPositiveCoefficient model
                (if infrared then H else (0 : BilateralField d → C(SpatialCoordinates d, ℝ)))
                omega (if reverse then N else M) z hr)
              (Ceta * (3 : ℝ) ^ (-gamma * (N : ℝ)))
              (c * (1 + Cgeom * eta * ((3 : ℝ) ^ H1) ^ Dgeom)) 

:= by
  classical
  haveI instNZ : NeZero d := ⟨by omega⟩
  have Step : Paper.cutoff_good_scale_input d := inputs_step_witness d hd
  have hES := inputs_hES_witness
  have Dbase : Paper.sum_errors_baseline_input d := inputs_baseline_witness d hd
  obtain ⟨P0, hP1, hA1⟩ := lfsc_good_steps_src_constants d hd E P X Sf W Cp Step D hES Dbase
  obtain ⟨H1min, hA2⟩ := hA1 (theta / 16) (by positivity)
  obtain ⟨dBd, hdBd, hBd⟩ := aux_lfsc_main_childB_dir d hd E P X W Cp Sf D theta htheta
  obtain ⟨dBn, hdBn, hBn⟩ := aux_lfsc_main_childB_neu d hd E P X W Cp Sf D theta htheta
  obtain ⟨Hθ, hHθ⟩ : ∃ n : ℕ, 12 / theta ≤ (n : ℝ) := exists_nat_ge _
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℕ, d * (2 * P0) ≤ 3 ^ a0 := ⟨_, (Nat.lt_pow_self (by norm_num)).le⟩
  obtain ⟨H1, hH1pos, hH1min, h8a0, hHθH1⟩ : ∃ H1 : ℕ, 0 < H1 ∧ H1min ≤ H1 ∧ 8 * a0 ≤ H1 ∧ Hθ ≤ H1 :=
    ⟨max (max H1min 1) (max (8 * a0) Hθ), by omega, by omega, by omega, by omega⟩
  have hH1θ : 12 ≤ theta * (H1 : ℝ) := by
    have h1 : (Hθ : ℝ) ≤ H1 := by exact_mod_cast hHθH1
    have h2 : 12 / theta * theta = 12 := div_mul_cancel₀ _ htheta.ne'
    nlinarith
  obtain ⟨Cg, delta0A, hCg, hδA, hA3⟩ := hA2 H1 hH1min hH1pos
  obtain ⟨Dg, hDg, hDθ⟩ : ∃ Dg : ℝ, 0 < Dg ∧ theta / 64 + 1 + 3 * (d : ℝ) / 4 ≤ theta * Dg / 16 := by
    refine ⟨16 * (theta / 64 + 1 + 3 * (d : ℝ) / 4) / theta + 1, by positivity, ?_⟩
    have h : theta * (16 * (theta / 64 + 1 + 3 * (d : ℝ) / 4) / theta + 1) / 16 =
        (theta / 64 + 1 + 3 * (d : ℝ) / 4) + theta / 16 := by
      field_simp
    rw [h]
    linarith
  refine ⟨H1, Dg, Cg + 1, min delta0A (min dBd dBn), hH1pos, hDg, by linarith,
    lt_min hδA (lt_min hdBd hdBn), ?_⟩
  intro model Rm Sreg It H hH hsmall z r hr htri eta heta
  obtain ⟨j, rfl⟩ := htri
  have hsmallA : model.delta ≤ delta0A := hsmall.trans (min_le_left _ _)
  have hsmallBd : model.delta ≤ dBd := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallBn : model.delta ≤ dBn := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hL1 : (1 : ℝ) ≤ (3 : ℝ) ^ H1 := one_le_pow₀ (by norm_num)
  have hLD1 : (1 : ℝ) ≤ ((3 : ℝ) ^ H1) ^ Dg := Real.one_le_rpow hL1 hDg.le
  set LD : ℝ := ((3 : ℝ) ^ H1) ^ Dg with hLDdef
  have hXpos : 0 ≤ Cg * eta * LD := by positivity
  set rho : ℝ := min 1 (eta / (1 + Cg * eta * LD)) with hrhodef
  have hrho0 : 0 < rho := lt_min one_pos (by positivity)
  have hrho1 : rho ≤ 1 := min_le_left _ _
  have hrhoX : rho * (1 + Cg * eta * LD) ≤ eta := by
    have h : rho ≤ eta / (1 + Cg * eta * LD) := min_le_right _ _
    have hpos : 0 < 1 + Cg * eta * LD := by linarith
    calc rho * (1 + Cg * eta * LD) ≤ eta / (1 + Cg * eta * LD) * (1 + Cg * eta * LD) :=
          mul_le_mul_of_nonneg_right h hpos.le
      _ = eta := div_mul_cancel₀ _ hpos.ne'
  obtain ⟨CA, γA, N0A, hCA, hγA, hA4⟩ := hA3 model Rm Sreg It H hH hsmallA z j eta heta rho hrho0
  set eps : ℝ := min (theta / 64) (1 / 16) with hepsdef
  have heps : 0 < eps := lt_min (by positivity) (by norm_num)
  have hepsθ : eps ≤ theta / 64 := min_le_left _ _
  have hεζ : eps + 1 / 8 ≤ 3 / 8 := by
    have : eps ≤ 1 / 16 := min_le_right _ _
    linarith
  obtain ⟨CBd, γBd, N0Bd, hCBd, hγBd, hBd4⟩ :=
    hBd model Rm Sreg It H hH hsmallBd z j H1 hH1pos eps heps
  obtain ⟨CBn, γBn, N0Bn, hCBn, hγBn, hBn4⟩ :=
    hBn model Rm Sreg It H hH hsmallBn z j H1 hH1pos eps heps
  obtain ⟨c2n, hc2n⟩ : ∃ c2n : ℕ, 1 + ((3 : ℝ) ^ j) ^ d < (3 : ℝ) ^ c2n :=
    pow_unbounded_of_one_lt _ (by norm_num)
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ j := hr
  set Ceta : ℝ := CA + (CBd + CBn) + 4 * (Cg * eta) * LD * ((3 : ℝ) ^ j) ^ d +
    (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + (7 / 8) * (theta * H1 + 2 * H1 + (c2n : ℝ) / Dg)) with hCetadef
  set γ : ℝ := min (min γA (min γBd γBn)) (min (1 / 8) (13 / 64 * theta)) with hγdef
  have hCeta : 0 < Ceta := by
    have : 0 < (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + (7 / 8) * (theta * H1 + 2 * H1 + (c2n : ℝ) / Dg)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have : 0 ≤ 4 * (Cg * eta) * LD * ((3 : ℝ) ^ j) ^ d := by positivity
    have : 0 ≤ CA + (CBd + CBn) := by positivity
    linarith
  have hγpos : 0 < γ := lt_min (lt_min hγA (lt_min hγBd hγBn)) (lt_min (by norm_num) (by positivity))
  refine ⟨Ceta, γ, 1, max (max N0A (max N0Bd N0Bn)) (max (4 * H1) (4 * j.natAbs)), hCeta, hγpos,
    zero_le_one, ?_⟩
  intro N M hN hNM c hc hc2 S hS reverse hratio
  have hNA : N0A ≤ N := by omega
  have hNBd : N0Bd ≤ N := by omega
  have hNBn : N0Bn ≤ N := by omega
  have hNH : 4 * H1 ≤ N := by omega
  have hNj : 4 * j.natAbs ≤ N := by omega
  obtain ⟨BadA, hmA, hpA, hgoodA⟩ := hA4 N M hNA hNM
  obtain ⟨BadBd, hmBd, hpBd, hdirB⟩ := hBd4 N M hNBd hNM reverse
  obtain ⟨BadBn, hmBn, hpBn, hneuB⟩ := hBn4 N M hNBn hNM reverse
  have hγA' : γ ≤ γA := (min_le_left _ _).trans (min_le_left _ _)
  have hγBd' : γ ≤ γBd := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγBn' : γ ≤ γBn := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hγz : γ ≤ 1 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hγ13 : γ ≤ 13 / 64 * theta := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨BadA ∪ (BadBd ∪ BadBn), hmA.union (hmBd.union hmBn), ?_, ?_⟩
  · have hBB : (chaosSampleLaw model).toMeasure (BadBd ∪ BadBn) ≤
        ENNReal.ofReal ((CBd + CBn) * (3 : ℝ) ^ (-γ * (N : ℝ))) :=
      aux_lem_finite_stopping_partition_prob_union_le _ BadBd BadBn CBd CBn γBd γBn γ (CBd + CBn) (N : ℝ)
        hCBd.le hCBn.le hγBd' hγBn' (Nat.cast_nonneg N) le_rfl hpBd hpBn
    refine aux_lem_finite_stopping_partition_prob_union_le _ BadA (BadBd ∪ BadBn) CA (CBd + CBn) γA γ γ Ceta
      (N : ℝ) hCA.le (by positivity) hγA' le_rfl (Nat.cast_nonneg N) ?_ hpA hBB
    have : 0 ≤ 4 * (Cg * eta) * LD * ((3 : ℝ) ^ j) ^ d := by positivity
    have : 0 < (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + (7 / 8) * (theta * H1 + 2 * H1 + (c2n : ℝ) / Dg)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    rw [hCetadef]
    linarith
  · intro omega hom infrared
    have homA : omega ∉ BadA := fun h => hom (Or.inl h)
    have homBd : omega ∉ BadBd := fun h => hom (Or.inr (Or.inl h))
    have homBn : omega ∉ BadBn := fun h => hom (Or.inr (Or.inr h))
    obtain ⟨hgoodH, hgood0⟩ := hgoodA omega homA reverse
    obtain ⟨hiD, hdataD⟩ := hdirB omega homBd infrared
    obtain ⟨hiN, hdataN⟩ := hneuB omega homBn infrared
    have hcLD : 0 < c := hc
    have hc2' : c ≤ 2 := hc2
    cases infrared with
    | true =>
      have hres := aux_lfsc_main_flag hd model H omega z j hr H1 hH1pos P0 a0 ha0 h8a0 theta htheta hH1θ Dg hDg
        hDθ Cg eta hCg heta c2n hc2n CA (CBd + CBn) γ hCA.le (by positivity) hγz hγ13 eps heps.le hepsθ hεζ
        N M hNH hNj c hc (by linarith) S hS reverse 1 zero_le_one
        (by intro n hn h1 h2; simpa only [one_mul] using hratio n hn h1 h2) hgoodH hiD hdataD hdataN
      have hfac : c * (1 + Cg * eta * LD) ≤ c * (1 + (Cg + 1) * eta * LD) := by
        apply mul_le_mul_of_nonneg_left _ hc.le
        have h : (Cg + 1) * eta * LD = Cg * eta * LD + eta * LD := by ring
        have h0 : 0 ≤ eta * LD := by positivity
        rw [h]
        linarith only [h0]
      exact ⟨aux_lfsc_partDir_mono _ _ _ _ _ _ _ _ _ _ _ hres.1 hfac,
        aux_lfsc_partNeu_mono _ _ _ _ _ _ _ _ _ _ _ hres.2 hfac⟩
    | false =>
      have hres := aux_lfsc_main_flag hd model 0 omega z j hr H1 hH1pos P0 a0 ha0 h8a0 theta htheta hH1θ Dg hDg
        hDθ Cg eta hCg heta c2n hc2n CA (CBd + CBn) γ hCA.le (by positivity) hγz hγ13 eps heps.le hepsθ hεζ
        N M hNH hNj ((1 + rho) * c) (by positivity)
        (le_trans (mul_le_mul (show 1 + rho ≤ 2 by linarith only [hrho1]) hc2 hc.le (by norm_num))
          (by norm_num))
        S hS reverse (1 + rho) (by positivity)
        (by
          intro n hn h1 h2
          have := mul_le_mul_of_nonneg_left (hratio n hn h1 h2) (by positivity : (0 : ℝ) ≤ 1 + rho)
          simpa only [mul_assoc] using this)
        hgood0 hiD hdataD hdataN
      have hfac := aux_lfsc_main_factor c Cg eta LD rho hc.le hCg.le heta.le hLD1 hrho0.le hrhoX
      exact ⟨aux_lfsc_partDir_mono _ _ _ _ _ _ _ _ _ _ _ hres.1 hfac,
        aux_lfsc_partNeu_mono _ _ _ _ _ _ _ _ _ _ _ hres.2 hfac⟩

end Paper
