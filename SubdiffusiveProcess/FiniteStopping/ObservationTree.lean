module

public import SubdiffusiveProcess.EllipticRegularity.Carriers
public import SubdiffusiveProcess.Main.ChaosSampleLaw
public import SubdiffusiveProcess.Main.InfraredCharacterization
public import SubdiffusiveProcess.Sobolev.DirichletResponse
public import SubdiffusiveProcess.Sobolev.EvenReflectionEquation
public import SubdiffusiveProcess.Sobolev.CoefficientRestriction
public import SubdiffusiveProcess.ResponseMoments.Subdivision
public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.Geometry.OddGrid
public import SubdiffusiveProcess.VariationalResponses.CellDirichlet
public import SubdiffusiveProcess.VariationalResponses.BoundaryResponse
public import SubdiffusiveProcess.Sobolev.DomainPoincare
public import SubdiffusiveProcess.EllipticRegularity.Inputs
public import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import SubdiffusiveProcess.CoarseGrainingVocab.CrudeJDeterministic
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Stopping.RestrictedPotentialBorel
public import SubdiffusiveProcess.Assumptions.Actions
public import SubdiffusiveProcess.Main.LayerScaling
public import Mathlib.Tactic

@[expose] public section

/-! This module establishes cell2 le root for finite stopping; it does not assert the full stopping theorem. -/

open MeasureTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments _root_.SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace SubdiffusiveProcess.FiniteStopping

variable {d : ℕ}

/-- obsLo in the finite stopping construction. -/
def obsLo (H1 N : ℕ) : ℕ := (N + (4 * H1 - 1)) / (4 * H1)

/-- obsHi in the finite stopping construction. -/
def obsHi (H1 N : ℕ) : ℕ := 3 * N / (4 * H1)

/-- obsT0 in the finite stopping construction. -/
def obsT0 (H1 N : ℕ) (j : ℤ) : ℕ :=
  (((H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℕ) : ℤ) + j).toNat

/-- obsB in the finite stopping construction. -/
def obsB (H1 N : ℕ) : ℕ :=
  SubdiffusiveProcess.FiniteStopping.obsHi H1 N - SubdiffusiveProcess.FiniteStopping.obsLo H1 N

/-- descendantSide zpow in the finite stopping construction. -/
theorem descendantSide_zpow (h m : ℕ) (hm : 2 * m + 1 = 3 ^ h)
    (j : ℤ) (n : ℕ) :
    descendantSide m n ((3 : ℝ) ^ j) = (3 : ℝ) ^ (j - ((h * n : ℕ) : ℤ)) := by
  unfold descendantSide
  have hcast : (2 * (m : ℝ) + 1) = (3 : ℝ) ^ h := by exact_mod_cast hm
  rw [hcast, ← pow_mul, zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]

/-- wordPrefix in the finite stopping construction. -/
def wordPrefix {α : Type*} {n : ℕ} (w : Fin n → α) (k : ℕ)
    (hk : k ≤ n) : Fin k → α :=
  fun i => w (Fin.castLE hk i)

/-- wordPrefix self in the finite stopping construction. -/
theorem wordPrefix_self {α : Type*} {n : ℕ} (w : Fin n → α)
    (hk : n ≤ n) :
    SubdiffusiveProcess.FiniteStopping.wordPrefix w n hk = w := by
  funext i
  simp only [wordPrefix, Fin.castLE_refl]

/-- wordPrefix castSucc in the finite stopping construction. -/
theorem wordPrefix_castSucc {α : Type*} {n : ℕ}
    (w : Fin (n + 1) → α) (k : ℕ) (hk : k ≤ n) :
    SubdiffusiveProcess.FiniteStopping.wordPrefix (fun i : Fin n => w i.castSucc) k hk =
      SubdiffusiveProcess.FiniteStopping.wordPrefix w k (hk.trans (Nat.le_succ n)) := by
  funext i
  rfl

/-- descendantSide add in the finite stopping construction. -/
theorem descendantSide_add (m a b : ℕ) (r : ℝ) :
    descendantSide m (a + b) r = descendantSide m b (descendantSide m a r) := by
  unfold descendantSide
  rw [pow_add, div_div]

/-- descendantCenter add in the finite stopping construction. -/
theorem descendantCenter_add (m a b : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (w : Fin (a + b) → OddGridIndex d m) :
    descendantCenter m z r (a + b) w =
      descendantCenter m
        (descendantCenter m z r a (fun i => w (Fin.castLE (Nat.le_add_right a b) i)))
        (descendantSide m a r) b (fun i => w (Fin.natAdd a i)) := by
  induction b with
  | zero =>
    show descendantCenter m z r a _ = descendantCenter m _ (descendantSide m a r) 0 _
    congr 1
  | succ b ih =>
    show descendantCenter m z r ((a + b) + 1) w =
      oddGridCenter
        (descendantCenter m
          (descendantCenter m z r a (fun i => w (Fin.castLE (Nat.le_add_right a (b + 1)) i)))
          (descendantSide m a r) b
          (fun i : Fin b => w (Fin.natAdd a i.castSucc)))
        (descendantSide m b (descendantSide m a r)) m
        (w (Fin.natAdd a (Fin.last b)))
    have hlhs : descendantCenter m z r ((a + b) + 1) w =
        oddGridCenter (descendantCenter m z r (a + b) (fun i => w i.castSucc))
          (descendantSide m (a + b) r) m (w (Fin.last (a + b))) := rfl
    rw [hlhs, ih (fun i => w i.castSucc)]
    have hlast : w (Fin.last (a + b)) = w (Fin.natAdd a (Fin.last b)) := by
      congr 1
    have hpref : (fun i : Fin a => (fun i => w i.castSucc) (Fin.castLE (Nat.le_add_right a b) i))
        = (fun i : Fin a => w (Fin.castLE (Nat.le_add_right a (b + 1)) i)) := by
      funext i; congr 1
    have hmid : (fun i : Fin b => (fun i => w i.castSucc) (Fin.natAdd a i))
        = (fun i : Fin b => w (Fin.natAdd a i.castSucc)) := by
      funext i; congr 1
    rw [hpref, hmid, ← SubdiffusiveProcess.FiniteStopping.descendantSide_add, hlast]

/-- subdivisionHalfWidth succ in the finite stopping construction. -/
theorem subdivisionHalfWidth_succ (H1 : ℕ) :
    subdivisionHalfWidth (H1 + 1) = 3 * subdivisionHalfWidth H1 + 1 := by
  have h1 := two_mul_subdivisionHalfWidth_add_one H1
  have h2 := two_mul_subdivisionHalfWidth_add_one (H1 + 1)
  have : 3 ^ (H1 + 1) = 3 * 3 ^ H1 := by ring
  omega

/-- combineDigits in the finite stopping construction. -/
def combineDigits : (H1 : ℕ) → (Fin H1 → Fin 3) → ℕ
  | 0, _ => 0
  | (H1 + 1), v => 3 * SubdiffusiveProcess.FiniteStopping.combineDigits H1
      (fun i => v i.castSucc) + (v (Fin.last H1)).val

/-- combineDigits lt in the finite stopping construction. -/
theorem combineDigits_lt (H1 : ℕ) (v : Fin H1 → Fin 3) :
    SubdiffusiveProcess.FiniteStopping.combineDigits H1 v < 3 ^ H1 := by
  induction H1 with
  | zero => simp only [combineDigits, pow_zero, zero_lt_one]
  | succ H1 ih =>
    unfold SubdiffusiveProcess.FiniteStopping.combineDigits
    have h1 := ih (fun i => v i.castSucc)
    have h2 := (v (Fin.last H1)).isLt
    have : 3 ^ (H1 + 1) = 3 * 3 ^ H1 := by ring
    omega

/-- encWord in the finite stopping construction. -/
def encWord (H1 : ℕ) (v : Fin H1 → OddGridIndex d 1) :
    OddGridIndex d (subdivisionHalfWidth H1) :=
  fun i => ⟨SubdiffusiveProcess.FiniteStopping.combineDigits H1 (fun n => v n i), by
    rw [two_mul_subdivisionHalfWidth_add_one]
    exact SubdiffusiveProcess.FiniteStopping.combineDigits_lt H1 _⟩

/-- descendantCenter encWord in the finite stopping construction. -/
theorem descendantCenter_encWord (H1 : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (v : Fin H1 → OddGridIndex d 1) :
    descendantCenter 1 z r H1 v =
      oddGridCenter z r (subdivisionHalfWidth H1) (SubdiffusiveProcess.FiniteStopping.encWord H1 v) := by
  induction H1 with
  | zero =>
    have h1 : descendantCenter 1 z r 0 v = z := rfl
    have hM0 : subdivisionHalfWidth 0 = 0 := rfl
    rw [h1]
    funext i
    unfold oddGridCenter
    have hlt := (SubdiffusiveProcess.FiniteStopping.encWord 0 v i).isLt
    have hv : (SubdiffusiveProcess.FiniteStopping.encWord 0 v i).val = 0 := by omega
    rw [hv, hM0]
    push_cast
    ring
  | succ H1 ih =>
    show oddGridCenter (descendantCenter 1 z r H1 (fun i => v i.castSucc))
        (descendantSide 1 H1 r) 1 (v (Fin.last H1)) = _
    rw [ih (fun i => v i.castSucc)]
    set mg := subdivisionHalfWidth H1 with hmg
    set k1 := SubdiffusiveProcess.FiniteStopping.encWord H1 (fun j => v j.castSucc) with hk1
    set k2 := v (Fin.last H1) with hk2
    have hside : descendantSide 1 H1 r = r / (2 * (mg : ℝ) + 1) := by
      have h1 : descendantSide 1 H1 r = r / (3 : ℝ) ^ H1 := by
        unfold descendantSide; norm_num
      have hcast : (2 * (mg : ℝ) + 1) = (3 : ℝ) ^ H1 := by
        have := two_mul_subdivisionHalfWidth_add_one H1
        exact_mod_cast this
      rw [h1, hcast]
    rw [hside]
    have hval : ∀ i, (SubdiffusiveProcess.FiniteStopping.encWord (H1 + 1) v i).val =
        3 * (k1 i).val + (k2 i).val := fun i => rfl
    have hM : ((subdivisionHalfWidth (H1 + 1) : ℕ) : ℝ) = 3 * (mg : ℝ) + 1 := by
      exact_mod_cast SubdiffusiveProcess.FiniteStopping.subdivisionHalfWidth_succ H1
    funext i
    unfold oddGridCenter
    rw [hval i, hM]
    have hmgpos : (0 : ℝ) < 2 * (mg : ℝ) + 1 := by positivity
    push_cast
    field_simp
    ring

/-- blockWord in the finite stopping construction. -/
def blockWord : (H1 m : ℕ) →
    (Fin (H1 * m) → OddGridIndex d 1) → Fin m → OddGridIndex d (subdivisionHalfWidth H1)
  | _, 0, _ => Fin.elim0
  | H1, (m + 1), u =>
      Fin.snoc (SubdiffusiveProcess.FiniteStopping.blockWord H1 m
          (fun i => u (Fin.castLE (Nat.le_add_right (H1 * m) H1) i)))
        (SubdiffusiveProcess.FiniteStopping.encWord H1 (fun i => u (Fin.natAdd (H1 * m) i)))

/-- descendantSide block in the finite stopping construction. -/
theorem descendantSide_block (H1 m : ℕ) (r : ℝ) :
    descendantSide 1 (H1 * m) r = descendantSide (subdivisionHalfWidth H1) m r := by
  have hcast : (2 * (subdivisionHalfWidth H1 : ℝ) + 1) = (3 : ℝ) ^ H1 := by
    exact_mod_cast two_mul_subdivisionHalfWidth_add_one H1
  have h1 : descendantSide 1 (H1 * m) r = r / ((3 : ℝ) ^ H1) ^ m := by
    unfold descendantSide
    rw [pow_mul]
    norm_num
  rw [h1, ← hcast]
  rfl

/-- descendantCenter blockWord in the finite stopping construction. -/
theorem descendantCenter_blockWord (H1 m : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (u : Fin (H1 * m) → OddGridIndex d 1) :
    descendantCenter 1 z r (H1 * m) u =
      descendantCenter (subdivisionHalfWidth H1) z r m
        (SubdiffusiveProcess.FiniteStopping.blockWord H1 m u) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show descendantCenter 1 z r (H1 * m + H1) u = _
    rw [SubdiffusiveProcess.FiniteStopping.descendantCenter_add 1 (H1 * m) H1 z r u,
      ih (fun i => u (Fin.castLE (Nat.le_add_right (H1 * m) H1) i)),
      SubdiffusiveProcess.FiniteStopping.descendantCenter_encWord H1 _
        (descendantSide 1 (H1 * m) r) (fun i => u (Fin.natAdd (H1 * m) i)),
      SubdiffusiveProcess.FiniteStopping.descendantSide_block H1 m r]
    show oddGridCenter
        (descendantCenter (subdivisionHalfWidth H1) z r m
          (SubdiffusiveProcess.FiniteStopping.blockWord H1 m
            (fun i => u (Fin.castLE (Nat.le_add_right (H1 * m) H1) i))))
        (descendantSide (subdivisionHalfWidth H1) m r) (subdivisionHalfWidth H1)
        (SubdiffusiveProcess.FiniteStopping.encWord H1 (fun i => u (Fin.natAdd (H1 * m) i))) =
      oddGridCenter
        (descendantCenter (subdivisionHalfWidth H1) z r m
          (fun i => SubdiffusiveProcess.FiniteStopping.blockWord H1 (m + 1) u i.castSucc))
        (descendantSide (subdivisionHalfWidth H1) m r) (subdivisionHalfWidth H1)
        (SubdiffusiveProcess.FiniteStopping.blockWord H1 (m + 1) u (Fin.last m))
    have heq : SubdiffusiveProcess.FiniteStopping.blockWord H1 (m + 1) u =
        Fin.snoc (SubdiffusiveProcess.FiniteStopping.blockWord H1 m
            (fun i => u (Fin.castLE (Nat.le_add_right (H1 * m) H1) i)))
          (SubdiffusiveProcess.FiniteStopping.encWord H1
            (fun i => u (Fin.natAdd (H1 * m) i))) := rfl
    have hX : (fun j : Fin m => SubdiffusiveProcess.FiniteStopping.blockWord H1 (m + 1) u
        j.castSucc) = SubdiffusiveProcess.FiniteStopping.blockWord H1 m
          (fun i => u (Fin.castLE (Nat.le_add_right (H1 * m) H1) i)) := by
      funext j; rw [heq, Fin.snoc_castSucc]
    have hL : SubdiffusiveProcess.FiniteStopping.blockWord H1 (m + 1) u (Fin.last m) =
        SubdiffusiveProcess.FiniteStopping.encWord H1
          (fun i => u (Fin.natAdd (H1 * m) i)) := by
      rw [heq, Fin.snoc_last]
    rw [hX, hL]

/-- rootQ in the finite stopping construction. -/
def rootQ (H1 : ℕ) (j : ℤ) : ℤ := j / (H1 : ℤ)

/-- rootRho in the finite stopping construction. -/
def rootRho (H1 : ℕ) (j : ℤ) : ℕ := (j % (H1 : ℤ)).toNat

/-- rootRho cast in the finite stopping construction. -/
theorem rootRho_cast (H1 : ℕ) (hH1 : 0 < H1) (j : ℤ) :
    (SubdiffusiveProcess.FiniteStopping.rootRho H1 j : ℤ) = j % (H1 : ℤ) := by
  unfold SubdiffusiveProcess.FiniteStopping.rootRho
  have h2 := Int.emod_nonneg j (show (H1 : ℤ) ≠ 0 by exact_mod_cast hH1.ne')
  omega

/-- root decomp in the finite stopping construction. -/
theorem root_decomp (H1 : ℕ) (hH1 : 0 < H1) (j : ℤ) :
    (H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j +
      (SubdiffusiveProcess.FiniteStopping.rootRho H1 j : ℤ) = j := by
  rw [SubdiffusiveProcess.FiniteStopping.rootRho_cast H1 hH1 j]
  unfold SubdiffusiveProcess.FiniteStopping.rootQ
  exact Int.mul_ediv_add_emod j (H1 : ℤ)

/-- rootCell in the finite stopping construction. -/
def rootCell (H1 : ℕ) (j : ℤ) (z : SpatialCoordinates d)
    (v : Fin (SubdiffusiveProcess.FiniteStopping.rootRho H1 j) → OddGridIndex d 1) :
    SpatialCoordinates d :=
  descendantCenter 1 z ((3 : ℝ) ^ j) (SubdiffusiveProcess.FiniteStopping.rootRho H1 j) v

/-- rootCell side in the finite stopping construction. -/
theorem rootCell_side (H1 : ℕ) (hH1 : 0 < H1) (j : ℤ) :
    descendantSide 1 (SubdiffusiveProcess.FiniteStopping.rootRho H1 j) ((3 : ℝ) ^ j) =
      (3 : ℝ) ^ ((H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j) := by
  have hm : 2 * 1 + 1 = 3 ^ 1 := by norm_num
  rw [SubdiffusiveProcess.FiniteStopping.descendantSide_zpow 1 1 hm j
    (SubdiffusiveProcess.FiniteStopping.rootRho H1 j)]
  congr 1
  have h := SubdiffusiveProcess.FiniteStopping.root_decomp H1 hH1 j
  omega

/-- initial cell eq coarse root in the finite stopping construction. -/
theorem initial_cell_eq_coarse_root (H1 : ℕ) (hH1 : 0 < H1)
    (j : ℤ) (z : SpatialCoordinates d) (m t0 : ℕ)
    (hsplit : t0 = SubdiffusiveProcess.FiniteStopping.rootRho H1 j + H1 * m)
    (w0 : Fin t0 → OddGridIndex d 1) :
    descendantCenter 1 z ((3 : ℝ) ^ j) t0 w0 =
      descendantCenter (subdivisionHalfWidth H1)
        (SubdiffusiveProcess.FiniteStopping.rootCell H1 j z
          (fun i => w0 (Fin.castLE (by omega) i)))
        ((3 : ℝ) ^ ((H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j)) m
        (SubdiffusiveProcess.FiniteStopping.blockWord H1 m
          (fun i => w0 (Fin.cast hsplit.symm (Fin.natAdd
            (SubdiffusiveProcess.FiniteStopping.rootRho H1 j) i)))) := by
  subst hsplit
  rw [SubdiffusiveProcess.FiniteStopping.descendantCenter_add 1
      (SubdiffusiveProcess.FiniteStopping.rootRho H1 j) (H1 * m) z ((3 : ℝ) ^ j) w0,
    SubdiffusiveProcess.FiniteStopping.rootCell_side H1 hH1 j,
    SubdiffusiveProcess.FiniteStopping.descendantCenter_blockWord H1 m _ _
      (fun i => w0 (Fin.natAdd (SubdiffusiveProcess.FiniteStopping.rootRho H1 j) i))]
  congr 2

/-- fip union over roots in the finite stopping construction. -/
theorem fip_union_over_roots
    {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (model : _root_.SubdiffusiveProcess.Model.GMCModel d) (H1 : ℕ) (mgrid : ℕ)
    (zroot : ι → SpatialCoordinates d) (jroot : ℤ)
    (Reg : ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (TraceClose : ℕ → ℕ → ℕ → SpatialCoordinates d → BilateralField d → Prop)
    (a b theta : ℝ) (m0 : ℕ)
    (hi : ∀ i : ι, ∃ Ceta ceta : ℝ, ∃ N0 : ℕ, 0 < Ceta ∧ 0 < ceta ∧
      ∀ N M : ℕ, N0 ≤ N → N ≤ M →
        (∀ k : ℤ, a * (N : ℝ) ≤ (k : ℝ) → (k : ℝ) ≤ b * (N : ℝ) →
          0 ≤ k ∧ m0 ≤ N - k.toNat ∧ m0 ≤ M - k.toNat) ∧
        ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
          (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-ceta * (N : ℝ))) ∧
          ∀ omega : BilateralField d, omega ∉ Bad →
            ∀ w : ℕ → OddGridIndex d mgrid,
              let k : ℕ → ℤ := fun n => (H1 : ℤ) * (n : ℤ) - jroot
              let z : ℕ → SpatialCoordinates d := fun n =>
                descendantCenter mgrid (zroot i) ((3 : ℝ) ^ jroot) n (fun j : Fin n => w j)
              (Nat.card {n : ℕ // a * (N : ℝ) ≤ (k n : ℝ) ∧
                (k n : ℝ) ≤ b * (N : ℝ) ∧
                ¬(Reg N (k n).toNat (z n) omega ∧
                  Reg M (k n).toNat (z n) omega ∧
                  TraceClose N M (k n).toNat (z n) omega)} : ℝ) ≤
                theta * (N : ℝ) / (H1 : ℝ)) :
    ∃ Ceta ceta : ℝ, ∃ N0 : ℕ, 0 < Ceta ∧ 0 < ceta ∧
      ∀ N M : ℕ, N0 ≤ N → N ≤ M →
        (∀ k : ℤ, a * (N : ℝ) ≤ (k : ℝ) → (k : ℝ) ≤ b * (N : ℝ) →
          0 ≤ k ∧ m0 ≤ N - k.toNat ∧ m0 ≤ M - k.toNat) ∧
        ∃ Bad : Set (BilateralField d), MeasurableSet Bad ∧
          (chaosSampleLaw model).toMeasure Bad ≤ ENNReal.ofReal (Ceta * (3 : ℝ) ^ (-ceta * (N : ℝ))) ∧
          ∀ omega : BilateralField d, omega ∉ Bad →
            ∀ (i : ι) (w : ℕ → OddGridIndex d mgrid),
              let k : ℕ → ℤ := fun n => (H1 : ℤ) * (n : ℤ) - jroot
              let z : ℕ → SpatialCoordinates d := fun n =>
                descendantCenter mgrid (zroot i) ((3 : ℝ) ^ jroot) n (fun j : Fin n => w j)
              (Nat.card {n : ℕ // a * (N : ℝ) ≤ (k n : ℝ) ∧
                (k n : ℝ) ≤ b * (N : ℝ) ∧
                ¬(Reg N (k n).toNat (z n) omega ∧
                  Reg M (k n).toNat (z n) omega ∧
                  TraceClose N M (k n).toNat (z n) omega)} : ℝ) ≤
                theta * (N : ℝ) / (H1 : ℝ) := by
  classical
  choose Ceta ceta N0 hCetapos hcetapos hbound using hi
  obtain ⟨i0⟩ : Nonempty ι := inferInstance
  refine ⟨∑ i, Ceta i, Finset.univ.inf' ⟨i0, Finset.mem_univ i0⟩ ceta, Finset.univ.sup N0,
    Finset.sum_pos (fun i _ => hCetapos i) ⟨i0, Finset.mem_univ i0⟩,
    (Finset.lt_inf'_iff _).2 (fun i _ => hcetapos i), ?_⟩
  intro N M hN0 hNM
  have hN0i : ∀ i, N0 i ≤ N := fun i => le_trans (Finset.le_sup (Finset.mem_univ i)) hN0
  have hpieces := fun i => hbound i N M (hN0i i) hNM
  set cetamin := Finset.univ.inf' ⟨i0, Finset.mem_univ i0⟩ ceta with hcetamin_def
  refine ⟨(hpieces i0).1, ⋃ i, (hpieces i).2.choose, ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion (fun i => (hpieces i).2.choose_spec.1)
  · have hcetale : ∀ i, cetamin ≤ ceta i := fun i =>
      Finset.inf'_le ceta (Finset.mem_univ i)
    calc (chaosSampleLaw model).toMeasure (⋃ i, (hpieces i).2.choose)
        ≤ ∑ i, (chaosSampleLaw model).toMeasure ((hpieces i).2.choose) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ i, ENNReal.ofReal (Ceta i * (3 : ℝ) ^ (-ceta i * (N : ℝ))) := by
          apply Finset.sum_le_sum
          intro i _
          exact (hpieces i).2.choose_spec.2.1
      _ ≤ ∑ i, ENNReal.ofReal (Ceta i * (3 : ℝ) ^ (-cetamin * (N : ℝ))) := by
          apply Finset.sum_le_sum
          intro i _
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ (hCetapos i).le
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have := hcetale i
          nlinarith only [this, Nat.cast_nonneg (α := ℝ) N]
      _ = ENNReal.ofReal (∑ i, Ceta i * (3 : ℝ) ^ (-cetamin * (N : ℝ))) :=
          (ENNReal.ofReal_sum_of_nonneg (fun i _ =>
            mul_nonneg (hCetapos i).le (Real.rpow_nonneg (by norm_num) _))).symm
      _ = ENNReal.ofReal ((∑ i, Ceta i) * (3 : ℝ) ^ (-cetamin * (N : ℝ))) := by
          rw [Finset.sum_mul]
  · intro omega homega i w
    have homegai : omega ∉ (hpieces i).2.choose := fun hmem =>
      homega (Set.mem_iUnion.mpr ⟨i, hmem⟩)
    exact (hpieces i).2.choose_spec.2.2 omega homegai w



theorem card_bridge
    (H1 obsLoZ B N : ℕ) (a b : ℝ) (jroot : ℤ) (K : ℕ)
    (P : ℕ → Prop) [DecidablePred fun s : Fin B => P (obsLoZ + s.val + 1)]
    (hK : ∀ n : ℕ, a * (N : ℝ) ≤ (((H1 : ℤ) * (n : ℤ) - jroot : ℤ) : ℝ) →
        (((H1 : ℤ) * (n : ℤ) - jroot : ℤ) : ℝ) ≤ b * (N : ℝ) → n ≤ K)
    (hwin : ∀ s : Fin B, a * (N : ℝ) ≤ (((H1 : ℤ) * ((obsLoZ + s.val + 1 : ℕ) : ℤ) - jroot : ℤ) : ℝ) ∧
        (((H1 : ℤ) * ((obsLoZ + s.val + 1 : ℕ) : ℤ) - jroot : ℤ) : ℝ) ≤ b * (N : ℝ)) :
    ((Finset.univ.filter (fun s : Fin B => P (obsLoZ + s.val + 1))).card : ℝ) ≤
      (Nat.card {n : ℕ // a * (N : ℝ) ≤ (((H1 : ℤ) * (n : ℤ) - jroot : ℤ) : ℝ) ∧
        (((H1 : ℤ) * (n : ℤ) - jroot : ℤ) : ℝ) ≤ b * (N : ℝ) ∧ P n} : ℝ) := by
  classical
  set β := {n : ℕ // a * (N : ℝ) ≤ (((H1 : ℤ) * (n : ℤ) - jroot : ℤ) : ℝ) ∧
      (((H1 : ℤ) * (n : ℤ) - jroot : ℤ) : ℝ) ≤ b * (N : ℝ) ∧ P n} with hβ
  have hfin : Finite β := by
    have hemb : β ↪ Fin (K + 1) := ⟨fun x => ⟨x.1, by
      have h2 := hK x.1 x.2.1 x.2.2.1
      omega⟩, by
      intro x y hxy
      apply Subtype.ext
      simpa only using congrArg Fin.val hxy⟩
    exact Finite.of_injective hemb.1 hemb.2
  have hinj : Function.Injective (fun s : {s : Fin B // P (obsLoZ + s.val + 1)} =>
      (⟨obsLoZ + s.1.val + 1, (hwin s.1).1, (hwin s.1).2, s.2⟩ : β)) := by
    intro x y hxy
    apply Subtype.ext
    apply Fin.ext
    have := congrArg Subtype.val hxy
    simp only at this
    omega
  have hcard : Nat.card {s : Fin B // P (obsLoZ + s.val + 1)} ≤ Nat.card β :=
    Nat.card_le_card_of_injective _ hinj
  have heq : Nat.card {s : Fin B // P (obsLoZ + s.val + 1)} =
      (Finset.univ.filter (fun s : Fin B => P (obsLoZ + s.val + 1))).card := by
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype]
  rw [← heq]
  exact_mod_cast hcard

/-- obsLoZ in the finite stopping construction. -/
def obsLoZ (H1 N : ℕ) (j : ℤ) : ℕ :=
  ((SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℤ) +
    SubdiffusiveProcess.FiniteStopping.rootQ H1 j).toNat

/-- t0 split in the finite stopping construction. -/
theorem t0_split (H1 N : ℕ) (hH1 : 0 < H1) (j : ℤ)
    (hj0 : 0 ≤ ((H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℕ) : ℤ) + j)
    (hq0 : 0 ≤ (SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℤ) +
      SubdiffusiveProcess.FiniteStopping.rootQ H1 j) :
    SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j =
      SubdiffusiveProcess.FiniteStopping.rootRho H1 j +
        H1 * SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j := by
  have hdecomp := SubdiffusiveProcess.FiniteStopping.root_decomp H1 hH1 j
  have ht0 : (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j : ℤ) =
      ((H1 * SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℕ) : ℤ) + j := by
    unfold SubdiffusiveProcess.FiniteStopping.obsT0
    exact Int.toNat_of_nonneg hj0
  have hZ : (SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j : ℤ) =
      (SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℤ) +
        SubdiffusiveProcess.FiniteStopping.rootQ H1 j := by
    unfold SubdiffusiveProcess.FiniteStopping.obsLoZ
    exact Int.toNat_of_nonneg hq0
  have hcast : (SubdiffusiveProcess.FiniteStopping.obsT0 H1 N j : ℤ) =
      (SubdiffusiveProcess.FiniteStopping.rootRho H1 j : ℤ) +
        (H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j := by
    rw [ht0, hZ, mul_add]
    push_cast at ht0 ⊢
    omega
  exact_mod_cast hcast

/-- side split in the finite stopping construction. -/
theorem side_split (H1 : ℕ) (hH1 : 0 < H1) (j : ℤ) (m t0 : ℕ)
    (hsplit : t0 = SubdiffusiveProcess.FiniteStopping.rootRho H1 j + H1 * m) :
    descendantSide 1 t0 ((3 : ℝ) ^ j) =
      descendantSide (subdivisionHalfWidth H1) m
        ((3 : ℝ) ^ ((H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j)) := by
  subst hsplit
  rw [SubdiffusiveProcess.FiniteStopping.descendantSide_add,
    SubdiffusiveProcess.FiniteStopping.rootCell_side H1 hH1 j,
    SubdiffusiveProcess.FiniteStopping.descendantSide_block]

/-- H1 obsLo ge real in the finite stopping construction. -/
theorem H1_obsLo_ge_real {H1 : ℕ} (hH1 : 0 < H1) (N : ℕ) :
    (N : ℝ) / 4 ≤ (H1 : ℝ) * (SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℝ) := by
  have hk : 0 < 4 * H1 := by omega
  have hdm : (4 * H1) * ((N + (4 * H1 - 1)) / (4 * H1)) + (N + (4 * H1 - 1)) % (4 * H1) =
      N + (4 * H1 - 1) :=
    Nat.div_add_mod (N + (4 * H1 - 1)) (4 * H1)
  have hmod : (N + (4 * H1 - 1)) % (4 * H1) < 4 * H1 := Nat.mod_lt _ hk
  have hnat0 : N ≤ (4 * H1) * ((N + (4 * H1 - 1)) / (4 * H1)) := by omega
  have hobsLo : SubdiffusiveProcess.FiniteStopping.obsLo H1 N =
      (N + (4 * H1 - 1)) / (4 * H1) := rfl
  have hcast : (N : ℝ) ≤ ((4 * H1) * ((N + (4 * H1 - 1)) / (4 * H1)) : ℕ) := by
    exact_mod_cast hnat0
  rw [hobsLo]
  push_cast at hcast
  linarith only [hH1, hk, hdm, hmod, hnat0, hobsLo, hcast]

/-- H1 obsHi le real in the finite stopping construction. -/
theorem H1_obsHi_le_real (H1 N : ℕ) :
    (H1 : ℝ) * (SubdiffusiveProcess.FiniteStopping.obsHi H1 N : ℝ) ≤ 3 * (N : ℝ) / 4 := by
  have hdm : (4 * H1) * (3 * N / (4 * H1)) + (3 * N) % (4 * H1) = 3 * N :=
    Nat.div_add_mod (3 * N) (4 * H1)
  have hnat0 : (4 * H1) * (3 * N / (4 * H1)) ≤ 3 * N := by omega
  have hobsHi : SubdiffusiveProcess.FiniteStopping.obsHi H1 N = 3 * N / (4 * H1) := rfl
  have hnat : 4 * (H1 * SubdiffusiveProcess.FiniteStopping.obsHi H1 N) ≤ 3 * N := by
    rw [hobsHi]; nlinarith only [hdm, hnat0, hobsHi, hnat0]
  have hcast : ((4 * (H1 * SubdiffusiveProcess.FiniteStopping.obsHi H1 N) : ℕ) : ℝ) ≤
      ((3 * N : ℕ) : ℝ) := by exact_mod_cast hnat
  push_cast at hcast
  linarith only [hdm, hnat0, hobsHi, hnat, hcast]

/-- obsB index in window in the finite stopping construction. -/
theorem obsB_index_in_window {H1 : ℕ} (hH1 : 0 < H1) (N : ℕ)
    (i : Fin (SubdiffusiveProcess.FiniteStopping.obsB H1 N)) :
    (N : ℝ) / 4 ≤ (H1 : ℝ) * ((SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℝ) +
        (i.val + 1 : ℝ)) ∧
      (H1 : ℝ) * ((SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℝ) + (i.val + 1 : ℝ)) ≤
        3 * (N : ℝ) / 4 := by
  have hlo := SubdiffusiveProcess.FiniteStopping.H1_obsLo_ge_real hH1 N
  have hhi := SubdiffusiveProcess.FiniteStopping.H1_obsHi_le_real H1 N
  have hle : SubdiffusiveProcess.FiniteStopping.obsLo H1 N ≤
      SubdiffusiveProcess.FiniteStopping.obsHi H1 N := by
    have hiB' : i.val + 1 ≤ SubdiffusiveProcess.FiniteStopping.obsB H1 N := i.isLt
    unfold SubdiffusiveProcess.FiniteStopping.obsB at hiB'
    omega
  have hiB : (i.val : ℝ) + 1 ≤ (SubdiffusiveProcess.FiniteStopping.obsHi H1 N : ℝ) -
      (SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℝ) := by
    have hiB' : i.val + 1 ≤ SubdiffusiveProcess.FiniteStopping.obsB H1 N := i.isLt
    have hcast : ((i.val + 1 : ℕ) : ℝ) ≤
        (SubdiffusiveProcess.FiniteStopping.obsB H1 N : ℝ) := by exact_mod_cast hiB'
    unfold SubdiffusiveProcess.FiniteStopping.obsB at hcast
    rw [Nat.cast_sub hle] at hcast
    push_cast at hcast
    linarith only [hH1, hlo, hhi, hle, hiB', hcast]
  have hHnn : (0 : ℝ) ≤ (H1 : ℝ) := Nat.cast_nonneg H1
  constructor
  · nlinarith only [hH1, hlo, hhi, hle, hiB, hHnn, hlo, mul_nonneg hHnn (have this := le_of_lt (Right.add_pos_of_nonneg_of_pos (Nat.cast_nonneg' ↑i) (Mathlib.Meta.Positivity.pos_of_isNat (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl (Nat.ble 1 1)))); this)]
  · nlinarith only [hH1, hlo, hhi, hle, hiB, hHnn, hhi, hiB, mul_le_mul_of_nonneg_left hiB hHnn]



theorem card_bridge_window
    (H1 : ℕ) (hH1 : 0 < H1) (j : ℤ) (N : ℕ)
    (hq0 : 0 ≤ (SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℤ) +
      SubdiffusiveProcess.FiniteStopping.rootQ H1 j) :
    ∀ i : Fin (SubdiffusiveProcess.FiniteStopping.obsB H1 N),
      (1 / 4 : ℝ) * (N : ℝ) ≤
          (((H1 : ℤ) * ((SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j + i.val + 1 : ℕ) : ℤ) -
            (H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j : ℤ) : ℝ) ∧
        (((H1 : ℤ) * ((SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j + i.val + 1 : ℕ) : ℤ) -
            (H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j : ℤ) : ℝ) ≤
          (3 / 4 : ℝ) * (N : ℝ) := by
  intro i
  have hwin := SubdiffusiveProcess.FiniteStopping.obsB_index_in_window hH1 N i
  have hZ : (SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j : ℤ) =
      (SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℤ) +
        SubdiffusiveProcess.FiniteStopping.rootQ H1 j := by
    unfold SubdiffusiveProcess.FiniteStopping.obsLoZ
    exact Int.toNat_of_nonneg hq0
  have heq : (((H1 : ℤ) * ((SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j + i.val + 1 : ℕ) : ℤ) -
      (H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j : ℤ) : ℝ) =
      (H1 : ℝ) * ((SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℝ) + (i.val + 1 : ℝ)) := by
    have hz2 : ((H1 : ℤ) * ((SubdiffusiveProcess.FiniteStopping.obsLoZ H1 N j + i.val + 1 : ℕ) : ℤ) -
        (H1 : ℤ) * SubdiffusiveProcess.FiniteStopping.rootQ H1 j : ℤ) =
        (H1 : ℤ) * ((SubdiffusiveProcess.FiniteStopping.obsLo H1 N : ℤ) + (i.val : ℤ) + 1) := by
      push_cast [hZ]
      ring
    rw [hz2]
    push_cast
    ring
  rw [heq]
  exact ⟨by linarith only [hH1, hq0, hwin, hZ, heq, hwin.left], by linarith only [hH1, hq0, hwin, hZ, heq, hwin.right]⟩

/-- descendantCell zero in the finite stopping construction. -/
theorem descendantCell_zero (m : ℕ) (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (w : Fin 0 → OddGridIndex d m) :
    (descendantCell m z hr 0 w : Set (SpatialCoordinates d)) = centeredCube z r hr := by
  rw [descendantCell_coe]
  change Metric.ball z (descendantSide m 0 r / 2) = Metric.ball z (r / 2)
  rw [descendantSide_zero]

/-- descendantCell subset prefix in the finite stopping construction. -/
theorem descendantCell_subset_prefix (m : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) :
    ∀ (n : ℕ) (w : Fin n → OddGridIndex d m) (k : ℕ) (hk : k ≤ n),
      (descendantCell m z hr n w : Set (SpatialCoordinates d)) ⊆
        descendantCell m z hr k (SubdiffusiveProcess.FiniteStopping.wordPrefix w k hk) := by
  intro n
  induction n with
  | zero =>
    intro w k hk
    obtain rfl : k = 0 := by omega
    rw [SubdiffusiveProcess.FiniteStopping.descendantCell_zero,
      SubdiffusiveProcess.FiniteStopping.descendantCell_zero]
  | succ n ih =>
    intro w k hk
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · have hkn : k ≤ n := by omega
      refine (descendantCell_succ_subset m z hr n w).trans ?_
      have h := ih (fun i => w i.castSucc) k hkn
      rwa [SubdiffusiveProcess.FiniteStopping.wordPrefix_castSucc] at h
    · obtain rfl : k = n + 1 := by omega
      rw [SubdiffusiveProcess.FiniteStopping.wordPrefix_self]

/-- descendantCell subset root in the finite stopping construction. -/
theorem descendantCell_subset_root (m : ℕ)
    (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (n : ℕ) (w : Fin n → OddGridIndex d m) :
    (descendantCell m z hr n w : Set (SpatialCoordinates d)) ⊆ centeredCube z r hr := by
  have h := SubdiffusiveProcess.FiniteStopping.descendantCell_subset_prefix m z hr n w 0
    (Nat.zero_le n)
  rwa [SubdiffusiveProcess.FiniteStopping.descendantCell_zero] at h

/-- cell2 in the finite stopping construction. -/
def cell2 (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (t0 mg : ℕ) (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ) (w : Fin s → OddGridIndex d mg) :
    Opens (SpatialCoordinates d) :=
  descendantCell mg (descendantCenter 1 z r t0 w0) (descendantSide_pos 1 t0 hr) s w

/-- cell2 eq centeredCube in the finite stopping construction. -/
theorem cell2_eq_centeredCube (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (t0 mg : ℕ) (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ)
    (w : Fin s → OddGridIndex d mg) :
    SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 s w =
      centeredCube (descendantCenter mg (descendantCenter 1 z r t0 w0)
          (descendantSide 1 t0 r) s w)
        (descendantSide mg s (descendantSide 1 t0 r))
        (descendantSide_pos mg s (descendantSide_pos 1 t0 hr)) := rfl

/-- cell2 subset initial in the finite stopping construction. -/
theorem cell2_subset_initial (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (t0 mg : ℕ) (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ)
    (w : Fin s → OddGridIndex d mg) :
    (SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 s w : Set (SpatialCoordinates d)) ⊆
      descendantCell 1 z hr t0 w0 :=
  SubdiffusiveProcess.FiniteStopping.descendantCell_subset_root mg _ _ s w

/-- cell2 subset root in the finite stopping construction. -/
theorem cell2_subset_root (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (t0 mg : ℕ) (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ)
    (w : Fin s → OddGridIndex d mg) :
    (SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 s w : Set (SpatialCoordinates d)) ⊆
      centeredCube z r hr :=
  (SubdiffusiveProcess.FiniteStopping.cell2_subset_initial z hr t0 mg w0 s w).trans
    (SubdiffusiveProcess.FiniteStopping.descendantCell_subset_root 1 z hr t0 w0)

/-- cell2 le root in the finite stopping construction. -/
theorem cell2_le_root (z : SpatialCoordinates d) {r : ℝ}
    (hr : 0 < r) (t0 mg : ℕ) (w0 : Fin t0 → OddGridIndex d 1) (s : ℕ)
    (w : Fin s → OddGridIndex d mg) :
    SubdiffusiveProcess.FiniteStopping.cell2 z hr t0 mg w0 s w ≤ centeredCube z r hr :=
  SubdiffusiveProcess.FiniteStopping.cell2_subset_root z hr t0 mg w0 s w

end SubdiffusiveProcess.FiniteStopping
