import SubdiffusiveProcess.Paper.lfsc_partition_core

/-!
# `lfsc_partition_assembly` — one-sample exponent bookkeeping of the sourced stopping partition

Sourced analogue of `aux_lem_finite_stopping_partition_omega_positive / omega_zero` (paper
`\label{mfd:lem-finite-stopping}` Steps 1-3 with the floor `3^{-ζN}B² dx` of `\label{mfd:lem-finite-source-comparison}`):
the regularized mass floor is `3^{-ζN} B²` (`0 < ζ ≤ 1`) instead of `3^{-N}φ²`, the local hypothesis at a stopped cell carries a source
term `Src` that is bounded by the floor mass of the parent, and `u` is any weak function.  The number of mass drops `g`, the
residual count and the exponent inequality are those of the unsourced proof (a smaller floor exponent only lowers the needed `g`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter TopologicalSpace Topology Finset
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section
namespace Paper

/-- The regularized mass is below `L^(D(g+1))` times the final floor mass (floor exponent `ζ`). -/
theorem aux_lfsc_partition_assembly_mass_lt_drops_zeta (Γ φ2 rd ε N ζ c2 a K : ℝ) (hφ : 0 < φ2)
    (hΓ : Γ ≤ (3 : ℝ) ^ (ε * N) * φ2) (hrd : 0 ≤ rd) (hc2 : 1 + rd ≤ (3 : ℝ) ^ c2)
    (hεN : -(ζ * N) ≤ ε * N) (hX : (ε + ζ) * N + a + c2 < K) :
    Γ + (3 : ℝ) ^ (-(ζ * N)) * φ2 * rd <
      (3 : ℝ) ^ K * ((3 : ℝ) ^ (-(ζ * N)) * φ2 * (3 : ℝ) ^ (-a)) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hmN : (3 : ℝ) ^ (-(ζ * N)) ≤ (3 : ℝ) ^ (ε * N) :=
    aux_lem_finite_stopping_partition_rpow3_anti hεN
  have hrhs : (3 : ℝ) ^ K * ((3 : ℝ) ^ (-(ζ * N)) * φ2 * (3 : ℝ) ^ (-a)) =
      (3 : ℝ) ^ (K + (-(ζ * N)) + (-a)) * φ2 := by
    rw [Real.rpow_add h3, Real.rpow_add h3]
    ring
  rw [hrhs]
  have hlt : (3 : ℝ) ^ (ε * N + c2) < (3 : ℝ) ^ (K + (-(ζ * N)) + (-a)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hmid : Γ + (3 : ℝ) ^ (-(ζ * N)) * φ2 * rd ≤ (3 : ℝ) ^ (ε * N + c2) * φ2 := by
    rw [Real.rpow_add h3]
    have h1 : (3 : ℝ) ^ (-(ζ * N)) * φ2 * rd ≤ (3 : ℝ) ^ (ε * N) * φ2 * rd :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmN hφ.le) hrd
    have h2 : (3 : ℝ) ^ (ε * N) * φ2 * (1 + rd) ≤ (3 : ℝ) ^ (ε * N) * φ2 * (3 : ℝ) ^ c2 :=
      mul_le_mul_of_nonneg_left hc2 (mul_nonneg (Real.rpow_nonneg h3.le _) hφ.le)
    nlinarith
  exact lt_of_le_of_lt hmid (mul_lt_mul_of_pos_right hlt hφ)

/-- The regularized mass drops at most `g` times (paper 4254--4258), floor exponent `ζ`. -/
theorem aux_lfsc_partition_assembly_mass_budget_zeta {d : ℕ} (z : SpatialCoordinates d) (j : ℤ) (hr : 0 < (3 : ℝ) ^ j)
    (H1 : ℕ) (hH1 : 0 < H1) (N : ℕ) (hNH : 4 * H1 ≤ N) (hNj : 4 * j.natAbs ≤ N)
    (theta D : ℝ) (htheta : 0 < theta) (hD : 0 < D) (c2n : ℕ)
    (hc2n : 1 + ((3 : ℝ) ^ j) ^ d < (3 : ℝ) ^ c2n) (g : ℕ)
    (hg1 : ((theta / 64 + 1) * (N : ℝ) + (d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) +
        (c2n : ℝ)) / ((H1 : ℝ) * D) ≤ g)
    (aS : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ j) hr))
    (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
    (zeta : ℝ) (hzeta0 : 0 < zeta) (hzeta1 : zeta ≤ 1) (φ : ℝ) (hφ : 0 < φ)
    (hglob : aux_lem_finite_stopping_partition_energyOn aS u.val (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) ≤
      (3 : ℝ) ^ (theta / 64 * (N : ℝ)) * (φ * φ)) :
    aux_lem_finite_stopping_partition_massOn aS u.val ((3 : ℝ) ^ (-(zeta * (N : ℝ))) * (φ * φ))
        (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) <
      (((3 : ℝ) ^ H1) ^ D) ^ (g + 1) * ((3 : ℝ) ^ (-(zeta * (N : ℝ))) * (φ * φ) *
        (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
          (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ d) := by
  have hH1D : 0 < (H1 : ℝ) * D := mul_pos (by exact_mod_cast hH1) hD
  have hmv : aux_lem_finite_stopping_partition_massOn aS u.val ((3 : ℝ) ^ (-(zeta * (N : ℝ))) * (φ * φ))
      (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) =
      aux_lem_finite_stopping_partition_energyOn aS u.val (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) +
        (3 : ℝ) ^ (-(zeta * (N : ℝ))) * (φ * φ) * ((3 : ℝ) ^ j) ^ d := by
    unfold aux_lem_finite_stopping_partition_massOn
    rw [centeredCube_volume_real]
  have hLDg : (((3 : ℝ) ^ H1) ^ D) ^ (g + 1) = (3 : ℝ) ^ ((H1 : ℝ) * D * ((g : ℝ) + 1)) := by
    rw [← Real.rpow_natCast (3 : ℝ) H1, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_natCast _ (g + 1), ← Real.rpow_mul (by norm_num)]
    push_cast
    ring_nf
  have hsd : (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
      (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ d =
      (3 : ℝ) ^ (-((d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)))) := by
    rw [aux_lem_finite_stopping_partition_final_side_rpow hH1 hNH hNj, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    ring_nf
  rw [hmv, hLDg, hsd]
  have hc2r : 1 + ((3 : ℝ) ^ j) ^ d ≤ (3 : ℝ) ^ (c2n : ℝ) := by
    rw [Real.rpow_natCast]
    exact hc2n.le
  have hXK : (theta / 64 + 1) * (N : ℝ) + (d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) +
      (c2n : ℝ) < (H1 : ℝ) * D * ((g : ℝ) + 1) := by
    have h1 := (div_le_iff₀ hH1D).1 hg1
    nlinarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  exact aux_lfsc_partition_assembly_mass_lt_drops_zeta _ _ _ (theta / 64) (N : ℝ) zeta (c2n : ℝ) _ _ (mul_pos hφ hφ) hglob
    (by positivity) hc2r (by nlinarith) (by nlinarith)

/-- Every stage cell has side at most `3^{-N/4}`. -/
theorem aux_lfsc_partition_assembly_side_le {H1 N : ℕ} (hH1 : 0 < H1) {j : ℤ} (hNj : 4 * j.natAbs ≤ N) (x : ℝ)
    (hx : ∃ s ≤ aux_lem_finite_stopping_partition_obsB H1 N, x = descendantSide (subdivisionHalfWidth H1) s
      (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) :
    x ≤ (3 : ℝ) ^ (-((N : ℝ) / 4)) := by
  obtain ⟨s, hs, rfl⟩ := hx
  rw [aux_lem_finite_stopping_partition_stage_side_eq hH1 hNj s]
  have hle : N ≤ 4 * (H1 * aux_lem_finite_stopping_partition_obsLo H1 N) :=
    aux_lem_finite_stopping_partition_four_H1_obsLo_ge hH1 N
  have h1 : (3 : ℝ) ^ (-((H1 * (aux_lem_finite_stopping_partition_obsLo H1 N + s) : ℕ) : ℤ)) =
      (3 : ℝ) ^ (-(((H1 * (aux_lem_finite_stopping_partition_obsLo H1 N + s) : ℕ) : ℝ))) := by
    rw [← Real.rpow_intCast]
    push_cast
    rfl
  rw [h1]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have h2 : (N : ℝ) ≤ 4 * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsLo H1 N : ℝ)) := by
    exact_mod_cast hle
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) H1, Nat.cast_nonneg (α := ℝ) s]

/-- Final combination of the stopped budget and the residual remainder (floor exponent `ζ`, decay `γ ≤ ζ`). -/
theorem aux_lfsc_partition_assembly_final_combine_zeta (c Λ A LD fl rd RKc Cres g13 γ ζ N φ2 CA CB : ℝ)
    (hc2 : c ≤ 4) (hA : 0 ≤ A) (hLD : 0 ≤ LD) (hrd : 0 ≤ rd) (hφ : 0 ≤ φ2)
    (hN : 0 ≤ N) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCres : 0 ≤ Cres)
    (hfl : fl = (3 : ℝ) ^ (-(ζ * N)) * φ2) (hγz : γ ≤ ζ) (hγ13 : γ ≤ g13)
    (hR : RKc ≤ Cres * (3 : ℝ) ^ (-(g13 * N)) * φ2) :
    c * Λ + A * c * LD * (Λ + fl * rd) + RKc ≤
      c * (1 + A * LD) * Λ +
        (CA + CB + 4 * A * LD * rd + Cres) * (3 : ℝ) ^ (-γ * N) * φ2 := by
  have h3N : (3 : ℝ) ^ (-(ζ * N)) ≤ (3 : ℝ) ^ (-γ * N) :=
    aux_lem_finite_stopping_partition_rpow3_anti (by nlinarith)
  have h3g : (3 : ℝ) ^ (-(g13 * N)) ≤ (3 : ℝ) ^ (-γ * N) :=
    aux_lem_finite_stopping_partition_rpow3_anti (by nlinarith)
  have hpos : 0 ≤ (3 : ℝ) ^ (-γ * N) := Real.rpow_nonneg (by norm_num) _
  have hpos2 : 0 ≤ (3 : ℝ) ^ (-(ζ * N)) := Real.rpow_nonneg (by norm_num) _
  have hstop : A * c * LD * (fl * rd) ≤ 4 * A * LD * rd * ((3 : ℝ) ^ (-γ * N) * φ2) := by
    rw [hfl]
    have hALr : 0 ≤ A * LD * rd := by positivity
    have h1 : c * ((3 : ℝ) ^ (-(ζ * N)) * φ2) ≤ 4 * ((3 : ℝ) ^ (-γ * N) * φ2) :=
      mul_le_mul hc2 (mul_le_mul_of_nonneg_right h3N hφ) (by positivity) (by norm_num)
    have := mul_le_mul_of_nonneg_left h1 hALr
    nlinarith
  have hres : RKc ≤ Cres * ((3 : ℝ) ^ (-γ * N) * φ2) := by
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3g hφ) hCres
    nlinarith
  have hrest : 0 ≤ (CA + CB) * ((3 : ℝ) ^ (-γ * N) * φ2) := by positivity
  nlinarith

open Classical in
theorem lfsc_partition_assembly {d : ℕ} (hd : 2 ≤ d) [NeZero d] (z : SpatialCoordinates d) (j : ℤ)
    (hr : 0 < (3 : ℝ) ^ j)
    (H1 : ℕ) (hH1 : 0 < H1) (P a0 : ℕ) (ha0 : d * (2 * P) ≤ 3 ^ a0) (h8a0 : 8 * a0 ≤ H1)
    (theta : ℝ) (htheta : 0 < theta) (hH1θ : 12 ≤ theta * (H1 : ℝ)) (D : ℝ) (hD : 0 < D)
    (hDθ : theta / 64 + 1 + 3 * (d : ℝ) / 4 ≤ theta * D / 16)
    (Cg eta : ℝ) (hCg : 0 < Cg) (heta : 0 < eta) (c2n : ℕ)
    (hc2n : 1 + ((3 : ℝ) ^ j) ^ d < (3 : ℝ) ^ c2n)
    (CA CB γ : ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (zeta : ℝ) (hzeta0 : 0 < zeta) (hzeta1 : zeta ≤ 1)
    (hγz : γ ≤ zeta) (hγ13 : γ ≤ 13 / 64 * theta)
    (N : ℕ) (hNH : 4 * H1 ≤ N) (hNj : 4 * j.natAbs ≤ N)
    (c : ℝ) (hc : 0 < c) (hc2 : c ≤ 4) (S : ℕ → Prop)
    (hS : theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
      (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ))
    (φ : ℝ) (hφ : 0 < φ)
    (ρ : ℕ → ℝ) (hρ0 : ∀ n, 0 ≤ ρ n)
    (hratio : ∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N → ρ n ≤ c)
    (aT aS : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ j) hr))
    (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
    (Good : (Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1) → (n : ℕ) →
      (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Prop)
    (Src : (Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1) → (s : ℕ) →
      (Fin (s + 1) → OddGridIndex d (subdivisionHalfWidth H1)) → ℝ)
    (hbranch : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1)
      (w : Fin (aux_lem_finite_stopping_partition_obsB H1 N) → OddGridIndex d (subdivisionHalfWidth H1)),
      ((((Finset.univ : Finset (Fin (aux_lem_finite_stopping_partition_obsB H1 N))).filter fun i =>
        ¬ Good w0 (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card : ℕ) : ℝ) ≤
          theta / 16 * (N : ℝ) / (H1 : ℝ))
    (hcomp : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1) (s : ℕ)
      (w : Fin (s + 1) → OddGridIndex d (subdivisionHalfWidth H1)),
      s + 1 ≤ aux_lem_finite_stopping_partition_obsB H1 N → Good w0 (s + 1) w → aux_lem_finite_stopping_partition_padLabel P (w (Fin.last s)) →
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w) ≤
        ρ (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) *
            aux_lem_finite_stopping_partition_respOn aS u (aux_lem_finite_stopping_partition_cell2_le_root z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w)
              (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w) +
          Cg * eta * ρ (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) *
            (aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 s
              (fun i => w i.castSucc)) + Src w0 s w))
    (hsrc : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1) (s : ℕ)
      (w : Fin (s + 1) → OddGridIndex d (subdivisionHalfWidth H1)),
      s + 1 ≤ aux_lem_finite_stopping_partition_obsB H1 N →
      Src w0 s w ≤ (3 : ℝ) ^ (-(zeta * (N : ℝ))) * (φ * φ) *
        volume.real (aux_lem_finite_stopping_partition_cell2 z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j)
          (subdivisionHalfWidth H1) w0 s (fun i => w i.castSucc) : Set (SpatialCoordinates d)))
    (hcrude : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1)
      (w : Fin (aux_lem_finite_stopping_partition_obsB H1 N) → OddGridIndex d (subdivisionHalfWidth H1)),
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (aux_lem_finite_stopping_partition_obsB H1 N) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (aux_lem_finite_stopping_partition_obsB H1 N) w) ≤
        (3 : ℝ) ^ (theta / 64 * (N : ℝ)) *
          (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
            (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ ((d : ℝ) - theta / 16) *
          (φ * φ))
    (hglobal : aux_lem_finite_stopping_partition_energyOn aS u.val
        (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) ≤
      (3 : ℝ) ^ (theta / 64 * (N : ℝ)) * (φ * φ)) :
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
        (positiveCoefficientRestrict (hle i) aT) (bcell i)) ≤
      c * (1 + Cg * eta * ((3 : ℝ) ^ H1) ^ D) *
          aux_lem_finite_stopping_partition_energyOn aS u.val
            (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) +
        (CA + CB + 4 * (Cg * eta) * ((3 : ℝ) ^ H1) ^ D * ((3 : ℝ) ^ j) ^ d +
          (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + (7 / 8) * (theta * H1 + 2 * H1 + (c2n : ℝ) / D))) *
          (3 : ℝ) ^ (-γ * (N : ℝ)) * φ ^ 2 := by
  classical
  have hH1D : 0 < (H1 : ℝ) * D := mul_pos (by exact_mod_cast hH1) hD
  have hX0 : 0 ≤ (theta / 64 + 1) * (N : ℝ) + (d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) +
      (c2n : ℝ) := by positivity
  have hgex : ∃ g : ℕ, ((theta / 64 + 1) * (N : ℝ) + (d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) +
      (c2n : ℝ)) / ((H1 : ℝ) * D) ≤ g ∧ (g : ℝ) < ((theta / 64 + 1) * (N : ℝ) +
        (d : ℝ) * ((H1 : ℝ) * (aux_lem_finite_stopping_partition_obsHi H1 N : ℝ)) + (c2n : ℝ)) / ((H1 : ℝ) * D) + 1 :=
    ⟨_, Nat.le_ceil _, Nat.ceil_lt_add_one (div_nonneg hX0 hH1D.le)⟩
  obtain ⟨g, hg1, hg2⟩ := hgex
  have hnbex : ∃ nbad : ℕ, (nbad : ℝ) ≤ theta / 16 * (N : ℝ) / (H1 : ℝ) ∧
      ∀ m : ℕ, (m : ℝ) ≤ theta / 16 * (N : ℝ) / (H1 : ℝ) → m ≤ nbad :=
    ⟨_, Nat.floor_le (by positivity), fun m hm => Nat.le_floor hm⟩
  obtain ⟨nbad, hnb1, hnb2⟩ := hnbex
  have hnselex : ∃ nsel : ℕ, nsel = ((Finset.univ : Finset (Fin (aux_lem_finite_stopping_partition_obsB H1 N))).filter
      (fun i => S (aux_lem_finite_stopping_partition_obsLo H1 N + (i.val + 1)))).card := ⟨_, rfl⟩
  obtain ⟨nsel, hnsel⟩ := hnselex
  have hnselB : nsel ≤ aux_lem_finite_stopping_partition_obsB H1 N := by
    rw [hnsel]
    exact (Finset.card_le_univ _).trans (by simp)
  have hnselθ : theta * ((aux_lem_finite_stopping_partition_obsB H1 N : ℝ) + 1) ≤ (nsel : ℝ) + 1 :=
    aux_lem_finite_stopping_partition_nsel_lower hH1 hNH S theta hS nsel hnsel.ge
  have hmassQ := aux_lfsc_partition_assembly_mass_budget_zeta z j hr H1 hH1 N hNH hNj theta D htheta hD c2n hc2n g hg1 aS u
    zeta hzeta0 hzeta1 φ hφ hglobal
  have hL1 : (1 : ℝ) < (3 : ℝ) ^ H1 := one_lt_pow₀ (by norm_num) hH1.ne'
  have hLD1 : (1 : ℝ) < ((3 : ℝ) ^ H1) ^ D := Real.one_lt_rpow hL1 hD
  have hcell' : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1) (s : ℕ)
      (w : Fin (s + 1) → OddGridIndex d (subdivisionHalfWidth H1)),
      s + 1 ≤ aux_lem_finite_stopping_partition_obsB H1 N →
      (S (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) ∧ 1 ≤ s + 1 ∧ s + 1 ≤ aux_lem_finite_stopping_partition_obsB H1 N) →
      Good w0 (s + 1) w → aux_lem_finite_stopping_partition_padLabel P (w (Fin.last s)) →
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w) ≤
        ρ (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) *
            aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w) +
          Cg * eta * ρ (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) *
            aux_lem_finite_stopping_partition_massOn aS u.val ((3 : ℝ) ^ (-(zeta * (N : ℝ))) * (φ * φ))
              (aux_lem_finite_stopping_partition_cell2 z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 s
                (fun i => w i.castSucc) : Set (SpatialCoordinates d)) := by
    intro w0 s w hsB _ hG hPd
    have h1 := hcomp w0 s w hsB hG hPd
    have h2 : aux_lem_finite_stopping_partition_respOn aS u
          (aux_lem_finite_stopping_partition_cell2_le_root z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w) ≤
        aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (s + 1) w) :=
      aux_lem_finite_stopping_partition_dirichletResponse_restrict_le_energyOn _ _ _ _
    have h3 := mul_le_mul_of_nonneg_left h2 (hρ0 (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)))
    have hs := hsrc w0 s w hsB
    have hcoef : 0 ≤ Cg * eta * ρ (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) :=
      mul_nonneg (mul_nonneg hCg.le heta.le) (hρ0 _)
    have h4 : Cg * eta * ρ (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) *
        (aux_lem_finite_stopping_partition_energyOn aS u.val (aux_lem_finite_stopping_partition_cell2 z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 s
          (fun i => w i.castSucc)) + Src w0 s w) ≤
        Cg * eta * ρ (aux_lem_finite_stopping_partition_obsLo H1 N + (s + 1)) *
          aux_lem_finite_stopping_partition_massOn aS u.val ((3 : ℝ) ^ (-(zeta * (N : ℝ))) * (φ * φ))
            (aux_lem_finite_stopping_partition_cell2 z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 s
              (fun i => w i.castSucc) : Set (SpatialCoordinates d)) := by
      refine mul_le_mul_of_nonneg_left ?_ hcoef
      unfold aux_lem_finite_stopping_partition_massOn
      linarith only [hs]
    linarith only [h1, h3, h4]
  have hρ' : ∀ s, (S (aux_lem_finite_stopping_partition_obsLo H1 N + s) ∧ 1 ≤ s ∧ s ≤ aux_lem_finite_stopping_partition_obsB H1 N) →
      0 ≤ ρ (aux_lem_finite_stopping_partition_obsLo H1 N + s) ∧ ρ (aux_lem_finite_stopping_partition_obsLo H1 N + s) ≤ c := by
    intro s hs
    refine ⟨hρ0 _, ?_⟩
    have hw1 : N ≤ 4 * (H1 * (aux_lem_finite_stopping_partition_obsLo H1 N + s)) :=
      (aux_lem_finite_stopping_partition_obsLo_le_iff hH1 N _).1 (Nat.le_add_right _ _)
    have hw2 : 4 * (H1 * (aux_lem_finite_stopping_partition_obsLo H1 N + s)) ≤ 3 * N := by
      apply (aux_lem_finite_stopping_partition_le_obsHi_iff hH1 N _).1
      have := hs.2.2
      unfold aux_lem_finite_stopping_partition_obsB at this
      omega
    exact hratio (aux_lem_finite_stopping_partition_obsLo H1 N + s) hs.1 hw1 hw2
  have hfl : (0 : ℝ) < (3 : ℝ) ^ (-(zeta * (N : ℝ))) * (φ * φ) :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (mul_pos hφ hφ)
  have hcore := lfsc_partition_core z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N) aT aS u
    ((3 : ℝ) ^ (-(zeta * (N : ℝ))) * (φ * φ)) (((3 : ℝ) ^ H1) ^ D)
    (fun s => S (aux_lem_finite_stopping_partition_obsLo H1 N + s) ∧ 1 ≤ s ∧ s ≤ aux_lem_finite_stopping_partition_obsB H1 N) Good (aux_lem_finite_stopping_partition_padLabel P) hfl hLD1
    (Cg * eta) c _ (by positivity) hc.le (fun s => ρ (aux_lem_finite_stopping_partition_obsLo H1 N + s)) hρ' hcell' nsel nbad g
    (fun w0 w => hnb2 _ (by convert hbranch w0 w))
    (by
      rw [hnsel]
      exact aux_lem_finite_stopping_partition_card_filter_mono_inst _ _ _ (fun i hi => ⟨hi, by omega, by have := i.isLt; omega⟩))
    hmassQ hcrude
  obtain ⟨ncell, centers, sides, hside, hle, hsides, hdisj, hcov, hPcell, hsum⟩ := hcore
  refine ⟨ncell, centers, sides, hside, hle,
    fun i => ⟨aux_lem_finite_stopping_partition_stage_sides_ok hH1 hNH hNj _ (hsides i),
      aux_lfsc_partition_assembly_side_le hH1 hNj _ (hsides i)⟩, hdisj, hcov, hPcell, ?_⟩
  intro bcell
  obtain ⟨R, hRle, hsum'⟩ := hsum
  refine le_trans hsum' ?_
  have hmv : aux_lem_finite_stopping_partition_massOn aS u.val ((3 : ℝ) ^ (-(zeta * (N : ℝ))) * (φ * φ))
      (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) =
      aux_lem_finite_stopping_partition_energyOn aS u.val (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) +
        (3 : ℝ) ^ (-(zeta * (N : ℝ))) * (φ * φ) * ((3 : ℝ) ^ j) ^ d := by
    unfold aux_lem_finite_stopping_partition_massOn
    rw [centeredCube_volume_real]
  rw [hmv]
  have hRK := aux_lem_finite_stopping_partition_aux_remainder hd j H1 hH1 P a0 ha0 h8a0 theta htheta hH1θ D hD hDθ c2n N hNH hNj
    nsel nbad g hnselB hnselθ hnb1 hg2 _ R (by convert aux_lem_finite_stopping_partition_card_not_padLabel_le _ P) hRle φ
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  exact aux_lfsc_partition_assembly_final_combine_zeta c _ (Cg * eta) (((3 : ℝ) ^ H1) ^ D)
    ((3 : ℝ) ^ (-(zeta * (N : ℝ))) * (φ * φ))
    (((3 : ℝ) ^ j) ^ d) _ _ (13 / 64 * theta) γ zeta N (φ ^ 2) CA CB hc2 (by positivity)
    (by positivity) (by positivity) (sq_nonneg φ) hN0 hCA hCB (by positivity) (by rw [sq])
    hγz hγ13 hRK

open Classical in
theorem aux_lfsc_partition_assembly_omega_zero {d : ℕ} [NeZero d] (z : SpatialCoordinates d) (j : ℤ)
    (hr : 0 < (3 : ℝ) ^ j)
    (H1 : ℕ) (hH1 : 0 < H1) (P a0 : ℕ) (ha0 : d * (2 * P) ≤ 3 ^ a0) (h8a0 : 8 * a0 ≤ H1)
    (theta : ℝ) (htheta : 0 < theta) (hH1θ : 12 ≤ theta * (H1 : ℝ)) (D : ℝ) (hD : 0 < D)
    (hDθ : theta / 64 + 1 + 3 * (d : ℝ) / 4 ≤ theta * D / 16)
    (Cg eta : ℝ) (hCg : 0 < Cg) (heta : 0 < eta) (c2n : ℕ)
    (hc2n : 1 + ((3 : ℝ) ^ j) ^ d < (3 : ℝ) ^ c2n)
    (CA CB γ : ℝ) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (zeta : ℝ) (hzeta0 : 0 < zeta) (hzeta1 : zeta ≤ 1)
    (hγz : γ ≤ zeta) (hγ13 : γ ≤ 13 / 64 * theta)
    (N : ℕ) (hNH : 4 * H1 ≤ N) (hNj : 4 * j.natAbs ≤ N)
    (c : ℝ) (hc : 0 < c) (hc2 : c ≤ 4) (S : ℕ → Prop)
    (hS : theta * (Nat.card {n : ℕ // N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ) ≤
      (Nat.card {n : ℕ // S n ∧ N ≤ 4 * (H1 * n) ∧ 4 * (H1 * n) ≤ 3 * N} : ℝ))
    (φ : ℝ) (hφ : φ = 0)
    (ρ : ℕ → ℝ) (hρ0 : ∀ n, 0 ≤ ρ n)
    (hratio : ∀ n : ℕ, S n → N ≤ 4 * (H1 * n) → 4 * (H1 * n) ≤ 3 * N → ρ n ≤ c)
    (aT aS : PositiveCoefficient (centeredCube z ((3 : ℝ) ^ j) hr))
    (u : weakSobolevGraph (centeredCube z ((3 : ℝ) ^ j) hr))
    (Good : (Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1) → (n : ℕ) →
      (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Prop)
    (hbranch : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1)
      (w : Fin (aux_lem_finite_stopping_partition_obsB H1 N) → OddGridIndex d (subdivisionHalfWidth H1)),
      ((((Finset.univ : Finset (Fin (aux_lem_finite_stopping_partition_obsB H1 N))).filter fun i =>
        ¬ Good w0 (i.val + 1) (aux_lem_finite_stopping_partition_wordPrefix w (i.val + 1) i.isLt)).card : ℕ) : ℝ) ≤
          theta / 16 * (N : ℝ) / (H1 : ℝ))
    (hcrude : ∀ (w0 : Fin (aux_lem_finite_stopping_partition_obsT0 H1 N j) → OddGridIndex d 1)
      (w : Fin (aux_lem_finite_stopping_partition_obsB H1 N) → OddGridIndex d (subdivisionHalfWidth H1)),
      aux_lem_finite_stopping_partition_respOn aT u (aux_lem_finite_stopping_partition_cell2_le_root z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (aux_lem_finite_stopping_partition_obsB H1 N) w)
          (aux_lem_finite_stopping_partition_cell2_killedPoincare z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) w0 (aux_lem_finite_stopping_partition_obsB H1 N) w) ≤
        (3 : ℝ) ^ (theta / 64 * (N : ℝ)) *
          (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
            (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ ((d : ℝ) - theta / 16) *
          (φ * φ))
    (hglobal : aux_lem_finite_stopping_partition_energyOn aS u.val
        (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) ≤
      (3 : ℝ) ^ (theta / 64 * (N : ℝ)) * (φ * φ)) :
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
        (positiveCoefficientRestrict (hle i) aT) (bcell i)) ≤
      c * (1 + Cg * eta * ((3 : ℝ) ^ H1) ^ D) *
          aux_lem_finite_stopping_partition_energyOn aS u.val
            (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) +
        (CA + CB + 4 * (Cg * eta) * ((3 : ℝ) ^ H1) ^ D * ((3 : ℝ) ^ j) ^ d +
          (3 : ℝ) ^ ((d : ℝ) * (j : ℝ) + (7 / 8) * (theta * H1 + 2 * H1 + (c2n : ℝ) / D))) *
          (3 : ℝ) ^ (-γ * (N : ℝ)) * φ ^ 2 := by
  classical
  have hL1 : (1 : ℝ) < (3 : ℝ) ^ H1 := one_lt_pow₀ (by norm_num) hH1.ne'
  have hLD1 : (1 : ℝ) < ((3 : ℝ) ^ H1) ^ D := Real.one_lt_rpow hL1 hD
  have hr0 : (0 : ℝ) < (3 : ℝ) ^ j := hr
  have hsd : 0 < (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
      (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ d :=
    pow_pos (descendantSide_pos _ _ (descendantSide_pos _ _ hr0)) d
  have hmass' : ∃ g : ℕ, aux_lem_finite_stopping_partition_massOn aS u.val 1
      (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) /
        (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
          (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ d < (((3 : ℝ) ^ H1) ^ D) ^ g :=
    pow_unbounded_of_one_lt _ hLD1
  obtain ⟨g, hg⟩ := hmass'
  have hmassQ : aux_lem_finite_stopping_partition_massOn aS u.val 1
      (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) <
      (((3 : ℝ) ^ H1) ^ D) ^ (g + 1) * (1 * (descendantSide (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
        (descendantSide 1 (aux_lem_finite_stopping_partition_obsT0 H1 N j) ((3 : ℝ) ^ j))) ^ d) := by
    rw [div_lt_iff₀ hsd] at hg
    rw [one_mul]
    calc _ < (((3 : ℝ) ^ H1) ^ D) ^ g * _ := hg
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hLD1.le (Nat.le_succ g)) hsd.le
  have hcore := lfsc_partition_core z hr (aux_lem_finite_stopping_partition_obsT0 H1 N j) (subdivisionHalfWidth H1) (aux_lem_finite_stopping_partition_obsB H1 N)
    aT aS u 1 (((3 : ℝ) ^ H1) ^ D) (fun _ => False) Good (aux_lem_finite_stopping_partition_padLabel P) one_pos hLD1 0 c 0
    le_rfl hc.le (fun _ => 0) (fun s h => h.elim) (fun w0 s w _ h => h.elim) 0 (aux_lem_finite_stopping_partition_obsB H1 N) g
    (fun w0 w => (Finset.card_le_univ _).trans (by simp)) (Nat.zero_le _) hmassQ
    (fun w0 w => by
      have h := hcrude w0 w
      rw [hφ, mul_zero, mul_zero] at h
      exact h)
  obtain ⟨ncell, centers, sides, hside, hle, hsides, hdisj, hcov, hPcell, hsum⟩ := hcore
  refine ⟨ncell, centers, sides, hside, hle,
    fun i => ⟨aux_lem_finite_stopping_partition_stage_sides_ok hH1 hNH hNj _ (hsides i),
      aux_lfsc_partition_assembly_side_le hH1 hNj _ (hsides i)⟩, hdisj, hcov, hPcell, ?_⟩
  intro bcell
  obtain ⟨R, -, hsum'⟩ := hsum
  refine le_trans hsum' ?_
  rw [hφ]
  have hΛ0 : 0 ≤ aux_lem_finite_stopping_partition_energyOn aS u.val
      (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) :=
    aux_lem_finite_stopping_partition_energyOn_nonneg aS u.val (subset_of_eq rfl)
  have hX : 0 ≤ Cg * eta * ((3 : ℝ) ^ H1) ^ D := by positivity
  have h1 : c * aux_lem_finite_stopping_partition_energyOn aS u.val
        (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) * 1 ≤
      c * aux_lem_finite_stopping_partition_energyOn aS u.val
        (centeredCube z ((3 : ℝ) ^ j) hr : Set (SpatialCoordinates d)) *
        (1 + Cg * eta * ((3 : ℝ) ^ H1) ^ D) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hX) (mul_nonneg hc.le hΛ0)
  simp only [zero_mul, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow]
  linarith


end Paper
