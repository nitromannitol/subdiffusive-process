module

public import SubdiffusiveProcess.Paper.lfgc_root_bridge

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open SubdiffusiveProcess.Lfgc




open MeasureTheory Filter Topology SubdiffusiveProcess SubdiffusiveProcess.Lane3
  SubdiffusiveProcess.Lane4
open scoped ENNReal

namespace Paper
variable {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]

/-- Level offsets of the enlarged roots in lem_band's parametrisation. -/
def aux_lfgc_rhs_bridge_lfgcOffset {en ns : ℕ} (enDepth : Fin en → ℕ) : Fin (en * ns) → ℤ :=
  fun i => -((enDepth (finProdFinEquiv.symm i).1 : ℕ) : ℤ)

/-- Centre shifts of the enlarged roots in lem_band's parametrisation. -/
def aux_lfgc_rhs_bridge_lfgcShift {en ns : ℕ} (enDepth : Fin en → ℕ) (shift : Fin ns → SpatialCoordinates d) :
    Fin (en * ns) → SpatialCoordinates d :=
  fun i => ((3 : ℝ) ^ enDepth (finProdFinEquiv.symm i).1) • shift (finProdFinEquiv.symm i).2

theorem aux_lfgc_rhs_bridge_lfgcOffset_apply {en ns : ℕ} (enDepth : Fin en → ℕ) (e : Fin en × Fin ns) :
    aux_lfgc_rhs_bridge_lfgcOffset (ns := ns) enDepth (finProdFinEquiv e) = -((enDepth e.1 : ℕ) : ℤ) := by
  simp only [aux_lfgc_rhs_bridge_lfgcOffset, Equiv.symm_apply_apply]

theorem aux_lfgc_rhs_bridge_lfgc_centre_eq {en ns : ℕ} (enDepth : Fin en → ℕ) (shift : Fin ns → SpatialCoordinates d)
    (e : Fin en × Fin ns) (k : ℕ) (z : SpatialCoordinates d) :
    z + ((3 : ℝ) ^ (-(k : ℤ))) • aux_lfgc_rhs_bridge_lfgcShift enDepth shift (finProdFinEquiv e) =
      z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth e.1) • shift e.2 := by
  simp only [aux_lfgc_rhs_bridge_lfgcShift, Equiv.symm_apply_apply, smul_smul]

theorem aux_lfgc_rhs_bridge_lfgc_side_eq (k n : ℕ) :
    (3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ n = (3 : ℝ) ^ (-((k : ℤ) - (n : ℤ))) := by
  rw [neg_sub, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_neg, zpow_natCast, zpow_natCast]
  ring



theorem lfgc_rhs_bridge (I : Paper.in_J d) (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (Hu : BilateralField d → C(SpatialCoordinates d, ℝ)) (sigma θ : ℝ) {en ns : ℕ}
    (enDepth : Fin en → ℕ) (shift : Fin ns → SpatialCoordinates d) (N k : ℕ)
    (z : SpatialCoordinates d) (omega : BilateralField d)
    (hnear : aux_lfgc_root_stat_nearAll I M Hu sigma (en * ns) (aux_lfgc_rhs_bridge_lfgcOffset enDepth) (aux_lfgc_rhs_bridge_lfgcShift enDepth shift) N
      (k : ℤ) z θ omega) (e : Fin en × Fin ns) :
    aux_lfgc_near_tests_NearChart sigma (aux_lfgc_root_stat_rootChart I M Hu omega N ((k : ℤ) - (enDepth e.1 : ℤ))
        (z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth e.1) • shift e.2))
      (Paper.aux_lem_band_U2_reference M Hu N ((k : ℤ) - (enDepth e.1 : ℤ))
        (z + ((3 : ℝ) ^ (-(k : ℤ)) * (3 : ℝ) ^ enDepth e.1) • shift e.2) omega) θ := by
  have hn := hnear (finProdFinEquiv e)
  rw [aux_lfgc_rhs_bridge_lfgcOffset_apply, aux_lfgc_rhs_bridge_lfgc_centre_eq, ← sub_eq_add_neg] at hn
  exact hn



def aux_lfgc_rhs_bridge_rhsDrawOK (en nc ns : ℕ) (enDepth : Fin en → ℕ) (cmpShift : Fin nc → SpatialCoordinates d)
    (shift : Fin ns → SpatialCoordinates d) (buffer : ℕ)
    (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (m k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d) : Prop :=
  let N := m + k
  let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  let rootSide : Fin en × Fin ns → ℝ :=
    fun U => r * (3 : ℝ) ^ enDepth U.1
  let rootCentre : Fin en × Fin ns → SpatialCoordinates d :=
    fun U => z + rootSide U • shift U.2
  let centres : (Fin en × Fin ns) → ℕ → Finset (SpatialCoordinates d) :=
    fun U D => by
      classical
      exact ((Finset.univ : Finset (Fin en × Fin ns)).image rootCentre) ∪
        ((Finset.univ : Finset (Fin nc)).image (fun c => z + r • cmpShift c)) ∪
        ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
          (descendantCenter 1 (rootCentre U) (rootSide U) D))
  let pre : (Fin en × Fin ns) → ℕ → SpatialCoordinates d → Finset ℤ :=
    fun U D _ =>
      Finset.Icc ((k : ℤ) - enDepth U.1 - buffer)
        (min (N : ℤ) ((k : ℤ) - enDepth U.1 + D + buffer))
  ∀ e D, ∀ w ∈ centres e D, ∀ j ∈ pre e D w,
    0 ≤ (N : ℤ) - j →
      Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) omega ≠ ⊤



def aux_lfgc_rhs_bridge_rhsFPOK (en ns : ℕ) (padRoot : Fin en) (enDepth : Fin en → ℕ)
    (shift : Fin ns → SpatialCoordinates d)
    (F Praw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (m k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d) : Prop :=
  let N := m + k
  let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  let rootSide : Fin en × Fin ns → ℝ :=
    fun U => r * (3 : ℝ) ^ enDepth U.1
  let rootCentre : Fin en × Fin ns → SpatialCoordinates d :=
    fun U => z + rootSide U • shift U.2
  ∀ t : Fin ns,
    F N (m + enDepth padRoot)
      ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 1 ∧
    Praw N (m + enDepth padRoot)
      ((3 : ℝ) ^ N • rootCentre (padRoot, t)) omega ≤ 12



def aux_lfgc_rhs_bridge_rhsP1OK (en nc ns : ℕ) (enDepth : Fin en → ℕ) (cmpShift : Fin nc → SpatialCoordinates d)
    (shift : Fin ns → SpatialCoordinates d) (buffer k0 : ℕ) (lam : ℝ)
    (Draw : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ENNReal)
    (Z : ℕ → ℕ → SpatialCoordinates d → BilateralField d → ℝ)
    (m k : ℕ) (z : SpatialCoordinates d) (omega : BilateralField d) : Prop :=
  let N := m + k
  let r : ℝ := (3 : ℝ) ^ (-(k : ℤ))
  let rootSide : Fin en × Fin ns → ℝ :=
    fun U => r * (3 : ℝ) ^ enDepth U.1
  let rootCentre : Fin en × Fin ns → SpatialCoordinates d :=
    fun U => z + rootSide U • shift U.2
  let centres : (Fin en × Fin ns) → ℕ → Finset (SpatialCoordinates d) :=
    fun U D => by
      classical
      exact ((Finset.univ : Finset (Fin en × Fin ns)).image rootCentre) ∪
        ((Finset.univ : Finset (Fin nc)).image (fun c => z + r • cmpShift c)) ∪
        ((Finset.univ : Finset (Fin D → OddGridIndex d 1)).image
          (descendantCenter 1 (rootCentre U) (rootSide U) D))
  let pre : (Fin en × Fin ns) → ℕ → SpatialCoordinates d → Finset ℤ :=
    fun U D _ =>
      Finset.Icc ((k : ℤ) - enDepth U.1 - buffer)
        (min (N : ℤ) ((k : ℤ) - enDepth U.1 + D + buffer))
  let Zphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
    if 0 ≤ (N : ℤ) - j then Z N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om else 0
  let Dphys := fun (j : ℤ) (w : SpatialCoordinates d) (om : BilateralField d) =>
    if 0 ≤ (N : ℤ) - j then
      (Draw N ((N : ℤ) - j).toNat ((3 : ℝ) ^ N • w) om).toReal else 0
  ∀ (U : Fin en × Fin ns) (D : ℕ), k0 ≤ D → ∀ w ∈ centres U D,
    (∑ j ∈ pre U D w, Zphys j w omega) < lam * (D : ℝ) ∧
      (∑ j ∈ pre U D w, Dphys j w omega) < lam * (D : ℝ)

end Paper
