module

public import SubdiffusiveProcess.Paper.lfsc_partition_assembly
public import SubdiffusiveProcess.Paper.lfsc_good_steps_src_constants
public import SubdiffusiveProcess.Paper.lfsc_childB_src_dir
public import SubdiffusiveProcess.Paper.lfsc_childB_src_neu

@[expose] public section

/-!
# `lfsc_partition_main_sample` — one sample (one root, one infrared flag, one source solution) of the sourced partition

Glue between the sourced good-step event (`good_steps_src_at`), the sourced ChildB data (crude reference bound, residual
leaf cost, global energy) and the sourced one-sample bookkeeping (`lfsc_partition_assembly` /
`omega_zero_src`): the source term `Src` of the local comparison is absorbed in the floor mass `3^{-ζN}B²` of the parent
(paper `\label{mfd:lem-finite-source-comparison}`, first paragraph: "it is absorbed in the lower bound
`λ(q) ≥ 3^{-ζN}B²|q|`").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter TopologicalSpace Topology Metric ProbabilityTheory
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open SubdiffusiveProcess.FiniteStopping
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace SubdiffusiveProcess.Paper

/-- Absorption of the source term into the mass floor. -/
theorem aux_lfsc_partition_main_sample_src_bound (rQ refInv Kf Bd Lr : ℝ) (N d : ℕ) (eps zeta eta0 : ℝ)
    (hr : 0 < rQ) (hrN : rQ ≤ (3 : ℝ) ^ (-((N : ℝ) / 4))) (_hz : 0 ≤ zeta)
    (hε : eps + zeta ≤ 3 / 8) (hη0 : eta0 ≤ 1 / 2) (_hη0pos : 0 ≤ eta0)
    (href : refInv ≤ (3 : ℝ) ^ (eps * (N : ℝ)) * rQ ^ (-eta0)) (_hrefnn : 0 ≤ refInv)
    (hKf : 0 ≤ Kf) (hKB : Kf ≤ Bd) (hLr : rQ ^ d ≤ Lr) :
    rQ ^ ((d : ℝ) + 2) * refInv * Kf ^ 2 ≤ (3 : ℝ) ^ (-(zeta * (N : ℝ))) * (Bd * Bd) * Lr := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hBd : 0 ≤ Bd := hKf.trans hKB
  -- the side power
  have hp2 : rQ ^ (2 - eta0) ≤ (3 : ℝ) ^ (-((3 : ℝ) / 8 * (N : ℝ))) := by
    have h1 : rQ ^ (2 - eta0) ≤ ((3 : ℝ) ^ (-((N : ℝ) / 4))) ^ (2 - eta0) :=
      Real.rpow_le_rpow hr.le hrN (by linarith)
    have h2 : ((3 : ℝ) ^ (-((N : ℝ) / 4))) ^ (2 - eta0) =
        (3 : ℝ) ^ (-((N : ℝ) / 4) * (2 - eta0)) := by
      rw [← Real.rpow_mul h3.le]
    refine h1.trans (h2.le.trans ?_)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    nlinarith
  have hcomb : (3 : ℝ) ^ (eps * (N : ℝ)) * rQ ^ (2 - eta0) ≤ (3 : ℝ) ^ (-(zeta * (N : ℝ))) := by
    calc (3 : ℝ) ^ (eps * (N : ℝ)) * rQ ^ (2 - eta0)
        ≤ (3 : ℝ) ^ (eps * (N : ℝ)) * (3 : ℝ) ^ (-((3 : ℝ) / 8 * (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hp2 (Real.rpow_nonneg h3.le _)
      _ = (3 : ℝ) ^ (eps * (N : ℝ) + -((3 : ℝ) / 8 * (N : ℝ))) := by
          rw [← Real.rpow_add h3]
      _ ≤ (3 : ℝ) ^ (-(zeta * (N : ℝ))) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          nlinarith
  have hrd : rQ ^ ((d : ℝ) + 2) * (3 : ℝ) ^ (eps * (N : ℝ)) * rQ ^ (-eta0) =
      rQ ^ (d : ℝ) * ((3 : ℝ) ^ (eps * (N : ℝ)) * rQ ^ (2 - eta0)) := by
    have : rQ ^ ((d : ℝ) + 2) * rQ ^ (-eta0) = rQ ^ (d : ℝ) * rQ ^ (2 - eta0) := by
      rw [← Real.rpow_add hr, ← Real.rpow_add hr]
      congr 1
      ring
    calc rQ ^ ((d : ℝ) + 2) * (3 : ℝ) ^ (eps * (N : ℝ)) * rQ ^ (-eta0)
        = (3 : ℝ) ^ (eps * (N : ℝ)) * (rQ ^ ((d : ℝ) + 2) * rQ ^ (-eta0)) := by ring
      _ = _ := by rw [this]; ring
  have hrdnat : rQ ^ (d : ℝ) = rQ ^ d := Real.rpow_natCast rQ d
  have hKB2 : Kf ^ 2 ≤ Bd * Bd := by nlinarith
  have hpos : 0 ≤ rQ ^ ((d : ℝ) + 2) := Real.rpow_nonneg hr.le _
  calc rQ ^ ((d : ℝ) + 2) * refInv * Kf ^ 2
      ≤ rQ ^ ((d : ℝ) + 2) * ((3 : ℝ) ^ (eps * (N : ℝ)) * rQ ^ (-eta0)) * (Bd * Bd) := by
        apply mul_le_mul _ hKB2 (sq_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left href hpos
    _ = rQ ^ d * ((3 : ℝ) ^ (eps * (N : ℝ)) * rQ ^ (2 - eta0)) * (Bd * Bd) := by
        rw [← hrdnat, ← hrd]; ring
    _ ≤ rQ ^ d * (3 : ℝ) ^ (-(zeta * (N : ℝ))) * (Bd * Bd) := by
        apply mul_le_mul_of_nonneg_right _ (mul_self_nonneg _)
        exact mul_le_mul_of_nonneg_left hcomb (by positivity)
    _ ≤ Lr * (3 : ℝ) ^ (-(zeta * (N : ℝ))) * (Bd * Bd) := by
        apply mul_le_mul_of_nonneg_right _ (mul_self_nonneg _)
        exact mul_le_mul_of_nonneg_right hLr (Real.rpow_nonneg h3.le _)
    _ = _ := by ring


open Classical in
theorem lfsc_partition_main_sample {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d)
    (Hused : BilateralField d → C(SpatialCoordinates d, ℝ)) (omega : BilateralField d)
    (z : SpatialCoordinates d) (j : ℤ) (hr : 0 < (3 : ℝ) ^ j)
    (H1 : ℕ) (hH1 : 0 < H1) (P a0 : ℕ) (ha0 : d * (2 * P) ≤ 3 ^ a0) (h8a0 : 8 * a0 ≤ H1)
    (theta : ℝ) (htheta : 0 < theta) (hH1θ : 12 ≤ theta * (H1 : ℝ)) (Dg : ℝ) (hDg : 0 < Dg)
    (hDθ : theta / 64 + 1 + 3 * (d : ℝ) / 4 ≤ theta * Dg / 16)
    (Cg eta : ℝ) (hCg : 0 < Cg) (heta : 0 < eta) (c2n : ℕ)
    (hc2n : 1 + ((3 : ℝ) ^ j) ^ d < (3 : ℝ) ^ c2n)
    (CA CB γ : ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (zeta : ℝ) (hz0 : 0 < zeta) (hz1 : zeta ≤ 1)
    (hγz : γ ≤ zeta) (hγ13 : γ ≤ 13 / 64 * theta)
    (eps : ℝ) (heps0 : 0 ≤ eps) (hepsθ : eps ≤ theta / 64) (hεζ : eps + zeta ≤ 3 / 8)
    (N M : ℕ) (hNH : 4 * H1 ≤ N) (hNj : 4 * j.natAbs ≤ N)
    (c : ℝ) (hc : 0 < c) (hc4 : c ≤ 4) (S : ℕ → Prop)
    (hS : theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
      (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ))
    (reverse : Bool) (wt : ℝ) (hwt : 0 ≤ wt)
    (hratio : ∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N →
      wt * kappaRatio model H1 (if reverse then M else N) (if reverse then N else M) n ≤ c)
    (hgood : good_steps_src_at model Hused P H1 (theta / 16) Cg eta wt z j N M reverse omega)
    (hi : ∀ (w0 : Fin (obsT0 H1 N j) → OddGridIndex d 1) (s : ℕ)
        (w : Fin s → OddGridIndex d (subdivisionHalfWidth H1)), s ≤ obsB H1 N →
      (reference model Hused omega (if reverse then N else M) (H1 * (obsLo H1 N + s))
        (descendantCenter (subdivisionHalfWidth H1)
          (descendantCenter 1 z ((3 : ℝ) ^ j) (obsT0 H1 N j) w0)
          (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j)) s w))⁻¹ ≤
        (3 : ℝ) ^ (eps * (N : ℝ)) *
          (descendantSide (subdivisionHalfWidth H1) s
            (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ (-(min (theta / 16) 1 / 2)))
    (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
    (F : SpatialCoordinates d → ℝ) (Kf : ℝ) (hFm : Measurable F) (hKf : 0 ≤ Kf)
    (hFb : ∀ x ∈ centeredCube z ((3 : ℝ) ^ j) hr, |F x| ≤ Kf)
    (hsol : ∀ psi : killedSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr),
      sobolevCoefficientForm
          (cutoffPositiveCoefficient model Hused omega (if reverse then N else M) z hr)
          (u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr))
          (psi : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)) =
        ∫ x in (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)),
          F x * (psi : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr)).1 x)
    (Bd : ℝ) (hBd0 : 0 ≤ Bd) (hKB : Kf ≤ Bd)
    (hcrude : ∀ (w0 : Fin (obsT0 H1 N j) → OddGridIndex d 1)
        (w : Fin (obsB H1 N) → OddGridIndex d (subdivisionHalfWidth H1)),
      respOn (cutoffPositiveCoefficient model Hused omega (if reverse then M else N) z hr) u
          (cell2_le_root z hr (obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (obsB H1 N) w)
          (cell2_killedPoincare z hr (obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (obsB H1 N) w) ≤
        (3 : ℝ) ^ (eps * (N : ℝ)) *
          (descendantSide (subdivisionHalfWidth H1) (obsB H1 N)
            (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ ((d : ℝ) - theta / 16) * Bd ^ 2)
    (hglobal : energyOn (cutoffPositiveCoefficient model Hused omega (if reverse then N else M) z hr)
        (u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr))
        (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) ≤
      (3 : ℝ) ^ (eps * (N : ℝ)) * Bd ^ 2) :
    ∃ (ncell : ℕ) (centers : Fin ncell → SpatialCoordinates d)
      (sides : Fin ncell → ℝ) (hside : ∀ i, 0 < sides i),
    let cell := fun i => centeredCube (centers i) (sides i) (hside i)
    ∃ hle : ∀ i, cell i ≤ centeredCube z ((3 : ℝ) ^ j) hr,
    (∀ i, ((∃ j : ℤ, sides i = (3 : ℝ) ^ j) ∧
      (3 : ℝ) ^ (-(N : ℤ)) ≤ sides i) ∧ sides i ≤ (3 : ℝ) ^ (-((N : ℝ) / 4))) ∧
    Pairwise (fun i j => Disjoint (cell i : Set (SpatialCoordinates d))
      (cell j : Set (SpatialCoordinates d))) ∧
    ((⋃ i, (cell i : Set (SpatialCoordinates d))) =ᵐ[volume]
      (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d))) ∧
    ∃ hPcell : ∀ i, ∃ K : ℝ≥0, ∀ v : killedSobolevGraph (cell i),
      ‖(v : SobolevData (cell i)).1‖ ≤
        K * ‖@subspaceGradient d (cell i) (killedSobolevGraph (cell i)) v‖,
    let bcell : ∀ i, weakSobolevGraph (cell i) := fun i =>
      ⟨sobolevDataRestrict (hle i) u.val, sobolevDataRestrict_mem_weak (hle i) u.property⟩
    (∑ i : Fin ncell,
      @dirichletResponse d (cell i) (@killedResponseSpace d (cell i) (hPcell i))
        (positiveCoefficientRestrict (hle i)
          (cutoffPositiveCoefficient model Hused omega (if reverse then M else N) z hr)) (bcell i)) ≤
      c * (1 + Cg * eta * ((3 : ℝ) ^ H1) ^ Dg) *
          energyOn (cutoffPositiveCoefficient model Hused omega (if reverse then N else M) z hr)
            (u : SobolevData (centeredCube z ((3 : ℝ) ^ j) hr))
            (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) +
        (CA + CB + 4 * (Cg * eta) * ((3 : ℝ) ^ H1) ^ Dg * ((3 : ℝ) ^ j) ^ d +
          (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + (7 / 8) * (theta * H1 + 2 * H1 + (c2n : ℝ) / Dg))) *
          (3 : ℝ) ^ (-γ * (N : ℝ)) * Bd ^ 2 := by
  classical
  obtain ⟨Good, hcount, hstep⟩ := hgood
  have hρ0 : ∀ n : ℕ, 0 ≤ wt * kappaRatio model H1 (if reverse then M else N)
      (if reverse then N else M) n := fun n => mul_nonneg hwt (kappaRatio_nonneg' model H1 _ _ n)
  have hη0 : min (theta / 16) 1 / 2 ≤ 1 / 2 := by
    have : min (theta / 16) 1 ≤ 1 := min_le_right _ _
    linarith
  have hη0pos : 0 ≤ min (theta / 16) 1 / 2 := by
    have : 0 ≤ min (theta / 16) 1 := le_min (by positivity) zero_le_one
    linarith
  have hsrc : ∀ (w0 : Fin (obsT0 H1 N j) → OddGridIndex d 1) (s : ℕ)
      (w : Fin (s + 1) → OddGridIndex d (subdivisionHalfWidth H1)),
      s + 1 ≤ obsB H1 N →
      (descendantSide (subdivisionHalfWidth H1) (s + 1) (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j))) ^
          ((d : ℝ) + 2) *
        (reference model Hused omega (if reverse then N else M) (H1 * (obsLo H1 N + (s + 1)))
          (descendantCenter (subdivisionHalfWidth H1)
            (descendantCenter 1 z ((3 : ℝ) ^ j) (obsT0 H1 N j) w0)
            (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j)) (s + 1) w))⁻¹ * Kf ^ 2 ≤
      (3 : ℝ) ^ (-(zeta * (N : ℝ))) * (Bd * Bd) *
        MeasureTheory.volume.real (cell2 z hr (obsT0 H1 N j) (subdivisionHalfWidth H1) w0 s
          (fun i => w i.castSucc) : Set (SpatialCoordinates d)) := by
    intro w0 s w hsB
    have hrQ : 0 < descendantSide (subdivisionHalfWidth H1) (s + 1)
        (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j)) :=
      descendantSide_pos _ _ (descendantSide_pos _ _ hr)
    have hvol : MeasureTheory.volume.real (cell2 z hr (obsT0 H1 N j) (subdivisionHalfWidth H1) w0 s
          (fun i => w i.castSucc) : Set (SpatialCoordinates d)) =
        (3 ^ H1 * descendantSide (subdivisionHalfWidth H1) (s + 1)
          (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j)) : ℝ) ^ d := by
      rw [cell2_eq_centeredCube, centeredCube_volume_real, cell2_parent_side_eq H1 _ s]
    rw [hvol]
    have hLr : (descendantSide (subdivisionHalfWidth H1) (s + 1)
        (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ d ≤
        (3 ^ H1 * descendantSide (subdivisionHalfWidth H1) (s + 1)
          (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j)) : ℝ) ^ d := by
      apply pow_le_pow_left₀ hrQ.le
      have h1 : (1 : ℝ) ≤ 3 ^ H1 := one_le_pow₀ (by norm_num)
      nlinarith
    exact aux_lfsc_partition_main_sample_src_bound _ _ Kf Bd _ N d eps zeta (min (theta / 16) 1 / 2) hrQ
      (aux_lfsc_partition_assembly_side_le hH1 hNj _ ⟨s + 1, hsB, rfl⟩) hz0.le hεζ hη0 hη0pos
      (hi w0 (s + 1) w hsB) (inv_nonneg.2 (reference_pos _ _ _ _ _ _).le) hKf hKB hLr
  have hcrude' : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1)
      (w : Fin (aux_lem_finite_stopping_partition_obsB H1 N) → OddGridIndex d (subdivisionHalfWidth H1)),
      aux_lem_finite_stopping_partition_respOn
          (cutoffPositiveCoefficient model Hused omega (if reverse then M else N) z hr) u
          (aux_lem_finite_stopping_partition_cell2_le_root z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j)
            (subdivisionHalfWidth H1) w0 (aux_lem_finite_stopping_partition_obsB H1 N) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr
            (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0
            (aux_lem_finite_stopping_partition_obsB H1 N) w) ≤
        (3 : ℝ) ^ (theta / 64 * (N : ℝ)) *
          (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
            (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^
              ((d : ℝ) - theta / 16) * (Bd * Bd) := by
    intro w0 w
    refine (hcrude w0 w).trans ?_
    have h3 : (3 : ℝ) ^ (eps * (N : ℝ)) ≤ (3 : ℝ) ^ (theta / 64 * (N : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right hepsθ (Nat.cast_nonneg N))
    have hs0 : 0 ≤ (descendantSide (subdivisionHalfWidth H1) (obsB H1 N)
        (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ ((d : ℝ) - theta / 16) :=
      Real.rpow_nonneg (descendantSide_pos _ _ (descendantSide_pos _ _ hr)).le _
    rw [sq]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hs0) (mul_self_nonneg _)
  have hglobal' : aux_lem_finite_stopping_partition_energyOn
      (cutoffPositiveCoefficient model Hused omega (if reverse then N else M) z hr) u.val
      (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) ≤
      (3 : ℝ) ^ (theta / 64 * (N : ℝ)) * (Bd * Bd) := by
    refine hglobal.trans ?_
    have h3 : (3 : ℝ) ^ (eps * (N : ℝ)) ≤ (3 : ℝ) ^ (theta / 64 * (N : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right hepsθ (Nat.cast_nonneg N))
    rw [sq]
    exact mul_le_mul_of_nonneg_right h3 (mul_self_nonneg _)
  have hbranch : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1)
      (w : Fin (aux_lem_finite_stopping_partition_obsB H1 N) → OddGridIndex d (subdivisionHalfWidth H1)),
      ((((Finset.univ : Finset (Fin (aux_lem_finite_stopping_partition_obsB H1 N))).filter fun i =>
        ¬ Good w0 (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card : ℕ) : ℝ) ≤
          theta / 16 * (N : ℝ) / (H1 : ℝ) := fun w0 w => hcount w0 w
  by_cases hBz : Bd = 0
  · exact aux_lfsc_partition_assembly_omega_zero z j hr H1 hH1 P a0 ha0 h8a0 theta htheta hH1θ Dg hDg hDθ
      Cg eta hCg heta c2n hc2n CA CB γ hCA hCB zeta hz0 hz1 hγz hγ13 N hNH hNj c hc hc4 S hS Bd hBz
      (fun n => wt * kappaRatio model H1 (if reverse then M else N) (if reverse then N else M) n)
      hρ0 hratio _ _ u Good hbranch hcrude' hglobal'
  · exact lfsc_partition_assembly hd z j hr H1 hH1 P a0 ha0 h8a0 theta htheta hH1θ Dg hDg hDθ
      Cg eta hCg heta c2n hc2n CA CB γ hCA hCB zeta hz0 hz1 hγz hγ13 N hNH hNj c hc hc4 S hS Bd
      (lt_of_le_of_ne hBd0 (Ne.symm hBz))
      (fun n => wt * kappaRatio model H1 (if reverse then M else N) (if reverse then N else M) n)
      hρ0 hratio _ _ u Good
      (fun w0 s w => (descendantSide (subdivisionHalfWidth H1) (s + 1)
          (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ ((d : ℝ) + 2) *
        (reference model Hused omega (if reverse then N else M) (H1 * (obsLo H1 N + (s + 1)))
          (descendantCenter (subdivisionHalfWidth H1)
            (descendantCenter 1 z ((3 : ℝ) ^ j) (obsT0 H1 N j) w0)
            (descendantSide 1 (obsT0 H1 N j) ((3 : ℝ) ^ j)) (s + 1) w))⁻¹ * Kf ^ 2)
      hbranch
      (fun w0 s w hsB hG hPd => hstep w0 s w hsB hG hPd u F Kf hFm hKf hFb hsol)
      hsrc hcrude' hglobal'


end SubdiffusiveProcess.Paper
