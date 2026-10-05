module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.ShellGauge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored.GammaTwoEnvelope

@[expose] public section

/-!
# The growing-ball derivative Borel–Cantelli

Step `.1` of the proof of
`l.finite.cutoff.coefficient.convergence`, i.e. the display
`e.finite.cutoff.derivative.Borel.Cantelli` :

```
‖∇^r g_k‖_{L^∞(B_{C 2ⁿ})} ≤ C_ω 3^{-rk} √(n+k+1),   simultaneously in (n, k).
```

The printed argument is: *cover each ball by cubes of side `3^k`*; the cover
has at most `C (1 + 2ⁿ 3^{-k})^d` members; stationarity `e.same.law.shift` and
the regularity moment `e.coefficient.field.regularity` give a common Gaussian
tail for the per-cube `(g2)` gauge; the failure probabilities at the displayed
threshold are summable in `(n, k)`.

This is exactly the *multiplicative* graded `Γ₂` envelope
`ae_exists_forall_le_sqrt_mul_of_isBigOWith_gammaTwo` read on the **diagonal
rows** `m = n + k`, which is what turns the two-parameter family into the
one-parameter rows the envelope wants and simultaneously produces the printed
price `√(n+k+1) = √(m+1)`:

* row `m` = `Finset.antidiagonal m ×ˢ shellCoverShifts d (m+2)`, i.e. a
  splitting `n + k = m` together with a cube of the cover;
* the entry observable is `translatedShellG2 k (shellCoverCenter p)`, whose
  `Γ₂` scale `(1 + log 2)^{1/2} δ` is *uniform in the shift and in the shell*
  (`isBigOWith_gammaTwo_translatedShellG2`) — this is what makes the cover free;
* the row scale is therefore constant, so the graded price is carried entirely
  by `√(m+1)`, and the row entropy is the cover cardinality.

Two ingredients are genuinely new here and are not needed by the fixed-ball
form `ShellC11Summable` of `ShellSummable.lean` (where the whole ball rescales
into a single unit cube, so no cover occurs):

* **the cover** (`exists_shellCoverShift_mem`, with the row-uniform shift set
  `shellCoverShifts_subset`), and
* **segment chaining** (`norm_sub_le_mul_of_forall_norm_sub_le`): a Lipschitz
  seminorm on a large cube is *not* the maximum of the seminorms of the
  covering unit cubes.  Two points of the big ball need not share a cube, so
  the segment between them is split into steps of sup-length `≤ 1/6`, each of
  which does lie in a single cube of the `1/3`-mesh cover
  (`exists_shellCoverShift_mem_pair`).  Chaining is lossless: the per-step
  bounds telescope to exactly `G ‖u - v‖`.

The three readouts `r = 0, 1` and the gradient Lipschitz seminorm (the repo's
stand-in for `r = 2`, since `PotentialField` stores one derivative plus a
Lipschitz certificate) are delivered with a **single** random constant, which
is what the downstream dyadic bookkeeping 
consumes.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored

open MeasureTheory
open Homogenization Homogenization.IndependentSums
open _root_.SubdiffusiveProcess.Model
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The chain rule for translation -/

/-- The chain rule for the translation action, the sibling of
`deriv_spatialScale`. -/
theorem deriv_translate (z : Vec d) (g : PotentialField d) (x : Vec d) :
    _root_.SubdiffusiveProcess.Model.PotentialField.deriv (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) x =
      _root_.SubdiffusiveProcess.Model.PotentialField.deriv g (x + z) := by
  have hcomp : HasFDerivAt (fun y : Vec d => g (y + z))
      (_root_.SubdiffusiveProcess.Model.PotentialField.deriv g (x + z)) x := by
    have h := (g.hasFDerivAt (x + z)).comp x ((hasFDerivAt_id x).add_const z)
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def] using! h
  have hstored : HasFDerivAt (fun y : Vec d => g (y + z))
      (_root_.SubdiffusiveProcess.Model.PotentialField.deriv (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g) x) x := by
    simpa only [_root_.SubdiffusiveProcess.Model.PotentialField.translate, _root_.SubdiffusiveProcess.Model.PotentialField.translate_apply,
      Function.comp_def] using!
      (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g).hasFDerivAt x
  exact hstored.unique hcomp

/-! ## Segment chaining: a local Lipschitz bound on a convex set is global -/

/-- **Segment chaining.**  A bound `‖F u - F v‖ ≤ L ‖u - v‖` that is only known
for *nearby* pairs of a convex set holds for all pairs: split the segment into
steps shorter than `eps` and telescope.  No constant is lost.

This is the device the printed proof needs for the second-derivative clause of
`e.finite.cutoff.derivative.Borel.Cantelli`, where the two points of the large
ball need not lie in a common cube of the cover. -/
theorem norm_sub_le_mul_of_forall_norm_sub_le
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
    {S : Set V} (hS : Convex ℝ S) {F : V → E} {L eps : ℝ} (heps : 0 < eps)
    (hloc : ∀ u ∈ S, ∀ v ∈ S, ‖u - v‖ ≤ eps → ‖F u - F v‖ ≤ L * ‖u - v‖)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) :
    ‖F u - F v‖ ≤ L * ‖u - v‖ := by
  classical
  set N : ℕ := ⌈‖v - u‖ / eps⌉₊ + 1 with hNdef
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hN : 0 < N := Nat.succ_pos _
    exact_mod_cast hN
  set w : ℕ → V := fun j => u + ((j : ℝ) / (N : ℝ)) • (v - u) with hwdef
  have hwmem : ∀ j : ℕ, j ≤ N → w j ∈ S := by
    intro j hj
    refine hS.add_smul_sub_mem hu hv ⟨by positivity, ?_⟩
    rw [div_le_one hNpos]
    exact_mod_cast hj
  have hw0 : w 0 = u := by simp [hwdef]
  have hwN : w N = v := by
    simp only [hwdef]
    rw [div_self (ne_of_gt hNpos), one_smul]
    abel
  have hnorm : ∀ j : ℕ, ‖w j - w (j + 1)‖ = ‖v - u‖ / (N : ℝ) := by
    intro j
    have hdiff : w j - w (j + 1) =
        (((j : ℝ) / (N : ℝ)) - (((j + 1 : ℕ) : ℝ) / (N : ℝ))) • (v - u) := by
      simp only [hwdef, sub_smul]
      abel
    have hcoef : ((j : ℝ) / (N : ℝ)) - (((j + 1 : ℕ) : ℝ) / (N : ℝ)) =
        -((N : ℝ)⁻¹) := by
      push_cast
      field_simp
      ring
    rw [hdiff, hcoef, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity : (0 : ℝ) < ((N : ℝ)⁻¹))]
    field_simp
  have hshort : ‖v - u‖ / (N : ℝ) ≤ eps := by
    rw [div_le_iff₀ hNpos]
    have hceil : ‖v - u‖ / eps ≤ (⌈‖v - u‖ / eps⌉₊ : ℝ) := Nat.le_ceil _
    have hle : ‖v - u‖ / eps ≤ (N : ℝ) := by
      rw [hNdef]
      push_cast
      linarith
    calc ‖v - u‖ = (‖v - u‖ / eps) * eps := by field_simp
      _ ≤ (N : ℝ) * eps := mul_le_mul_of_nonneg_right hle heps.le
      _ = eps * (N : ℝ) := by ring
  have hstep : ∀ j : ℕ, j < N →
      dist (F (w j)) (F (w (j + 1))) ≤ L * (‖v - u‖ / (N : ℝ)) := by
    intro j hj
    have h1 := hwmem j (le_of_lt hj)
    have h2 := hwmem (j + 1) hj
    have hle : ‖w j - w (j + 1)‖ ≤ eps := by rw [hnorm j]; exact hshort
    have h := hloc _ h1 _ h2 hle
    rw [hnorm j] at h
    rwa [dist_eq_norm]
  have hchain := dist_le_range_sum_dist (fun j => F (w j)) N
  have hsum : ∑ j ∈ Finset.range N, dist (F (w j)) (F (w (j + 1))) ≤
      (N : ℝ) * (L * (‖v - u‖ / (N : ℝ))) := by
    calc ∑ j ∈ Finset.range N, dist (F (w j)) (F (w (j + 1)))
        ≤ ∑ _j ∈ Finset.range N, L * (‖v - u‖ / (N : ℝ)) :=
          Finset.sum_le_sum fun j hj => hstep j (Finset.mem_range.mp hj)
      _ = (N : ℝ) * (L * (‖v - u‖ / (N : ℝ))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfinal := hchain.trans hsum
  rw [hw0, hwN, dist_eq_norm] at hfinal
  have hEq : (N : ℝ) * (L * (‖v - u‖ / (N : ℝ))) = L * ‖u - v‖ := by
    rw [norm_sub_rev u v]
    field_simp
  rwa [hEq] at hfinal

/-! ## A cube of the cover containing two nearby points -/

/-- Two points of a triadic cube at sup-distance at most `1/6` lie in a
**common** cube of the `1/3`-mesh unit-cube cover.  This is the two-point
refinement of `exists_shellCoverShift_mem` that segment chaining needs: the
cube is centred at the rounding of the first point, which leaves room `1/6` on
every side for the second. -/
theorem exists_shellCoverShift_mem_pair {r : ℤ} {u v : Vec d}
    (hu : u ∈ openCubeSet (originCube d r)) (huv : ‖u - v‖ ≤ (6 : ℝ)⁻¹) :
    ∃ p ∈ shellCoverShifts d r,
      u ∈ translateSet (shellCoverCenter p) (openCubeSet (originCube d 0)) ∧
        v ∈ translateSet (shellCoverCenter p) (openCubeSet (originCube d 0)) := by
  have hR1 : (1 : ℝ) ≤ (shellCoverRadius r : ℝ) := by
    exact_mod_cast Nat.one_le_pow (r + 1).toNat 3 (by norm_num)
  have hRpow : (3 : ℝ) ^ (r + 1) ≤ (shellCoverRadius r : ℝ) := by
    have hcast : ((shellCoverRadius r : ℕ) : ℝ) =
        (3 : ℝ) ^ (((r + 1).toNat : ℕ) : ℤ) := by
      rw [zpow_natCast, shellCoverRadius]
      norm_cast
    rw [hcast]
    exact zpow_le_zpow_right₀ (by norm_num) (Int.self_le_toNat _)
  set p : Fin d → ℤ := fun i => round ((3 : ℝ) * u i) with hp_def
  have hcenter : ∀ i, shellCoverCenter (d := d) p i =
      (3 : ℝ)⁻¹ * ((round ((3 : ℝ) * u i) : ℤ) : ℝ) := fun _ => rfl
  have hnear : ∀ i, |u i - shellCoverCenter (d := d) p i| ≤ (6 : ℝ)⁻¹ := by
    intro i
    have hround := abs_le.mp (abs_sub_round ((3 : ℝ) * u i))
    have hrw : u i - shellCoverCenter (d := d) p i =
        (3 : ℝ)⁻¹ * ((3 : ℝ) * u i - ((round ((3 : ℝ) * u i) : ℤ) : ℝ)) := by
      rw [hcenter i]
      ring
    rw [hrw, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < (3 : ℝ)⁻¹)]
    have habs := abs_le.mpr hround
    nlinarith [abs_nonneg ((3 : ℝ) * u i - ((round ((3 : ℝ) * u i) : ℤ) : ℝ))]
  have huvcoord : ∀ i, |u i - v i| ≤ (6 : ℝ)⁻¹ := by
    intro i
    have h : ‖(u - v) i‖ ≤ ‖u - v‖ := norm_le_pi_norm (u - v) i
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using h.trans huv
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [shellCoverShifts, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hui := (mem_openCubeSet_originCube_iff.mp hu) i
    have hround := abs_le.mp (abs_sub_round ((3 : ℝ) * u i))
    have hthree : (3 : ℝ) * ((1 / 2 : ℝ) * (3 : ℝ) ^ r) = (1 / 2 : ℝ) * (3 : ℝ) ^ (r + 1) := by
      rw [zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring
    have hlow : -((shellCoverRadius r : ℤ) : ℝ) ≤ ((p i : ℤ) : ℝ) := by
      rw [hp_def]
      push_cast
      nlinarith [hui.1, hui.2]
    have hhigh : ((p i : ℤ) : ℝ) ≤ ((shellCoverRadius r : ℤ) : ℝ) := by
      rw [hp_def]
      push_cast
      nlinarith [hui.1, hui.2]
    constructor
    · exact_mod_cast hlow
    · exact_mod_cast hhigh
  · rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_originCube_iff]
    intro i
    have h := abs_le.mp (hnear i)
    have hone : (1 / 2 : ℝ) * (3 : ℝ) ^ (0 : ℤ) = 1 / 2 := by norm_num
    rw [hone]
    have hcoord : (u - shellCoverCenter (d := d) p) i =
        u i - shellCoverCenter (d := d) p i := rfl
    rw [hcoord]
    constructor <;> [linarith [h.1]; linarith [h.2]]
  · rw [mem_translateSet_iff_sub_mem, mem_openCubeSet_originCube_iff]
    intro i
    have h := abs_le.mp (hnear i)
    have h' := abs_le.mp (huvcoord i)
    have hone : (1 / 2 : ℝ) * (3 : ℝ) ^ (0 : ℤ) = 1 / 2 := by norm_num
    rw [hone]
    have hcoord : (v - shellCoverCenter (d := d) p) i =
        v i - shellCoverCenter (d := d) p i := rfl
    rw [hcoord]
    constructor <;> [linarith [h.1, h'.2]; linarith [h.2, h'.1]]

/-! ## Per-cube readouts of the translated `(g2)` gauge -/

variable {omega : PotentialSample d}

/-- The gradient of the reverse-scaled shell at a point of a cube of the cover
is bounded by that cube's `(g2)` gauge. -/
theorem norm_deriv_unscalePotential_le_translatedShellG2 (k : ℕ)
    (omega : PotentialSample d) (p : Fin d → ℤ) {w : Vec d}
    (hw : w ∈ translateSet (shellCoverCenter p) (openCubeSet (originCube d 0))) :
    ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (unscalePotential k (omega k)) w‖ ≤
      translatedShellG2 k (shellCoverCenter p) omega := by
  rw [mem_translateSet_iff_sub_mem] at hw
  have h := _root_.SubdiffusiveProcess.Model.PotentialField.norm_deriv_le_g2Observable
    (_root_.SubdiffusiveProcess.Model.PotentialField.translate (shellCoverCenter p) (unscalePotential k (omega k))) hw
  rw [deriv_translate] at h
  have hcancel : w - shellCoverCenter p + shellCoverCenter p = w := by abel
  rwa [hcancel] at h

/-- The gradient Lipschitz readout inside a single cube of the cover. -/
theorem norm_deriv_unscalePotential_sub_le_translatedShellG2_mul (k : ℕ)
    (omega : PotentialSample d) (p : Fin d → ℤ) {w w' : Vec d}
    (hw : w ∈ translateSet (shellCoverCenter p) (openCubeSet (originCube d 0)))
    (hw' : w' ∈ translateSet (shellCoverCenter p) (openCubeSet (originCube d 0))) :
    ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (unscalePotential k (omega k)) w -
        _root_.SubdiffusiveProcess.Model.PotentialField.deriv (unscalePotential k (omega k)) w'‖ ≤
      translatedShellG2 k (shellCoverCenter p) omega * ‖w - w'‖ := by
  rw [mem_translateSet_iff_sub_mem] at hw hw'
  have h := _root_.SubdiffusiveProcess.Model.PotentialField.norm_deriv_sub_deriv_le_g2Observable_mul
    (_root_.SubdiffusiveProcess.Model.PotentialField.translate (shellCoverCenter p) (unscalePotential k (omega k))) hw hw'
  rw [deriv_translate, deriv_translate] at h
  have hcancel : w - shellCoverCenter p + shellCoverCenter p = w := by abel
  have hcancel' : w' - shellCoverCenter p + shellCoverCenter p = w' := by abel
  have hdiff : w - shellCoverCenter p - (w' - shellCoverCenter p) = w - w' := by abel
  rwa [hcancel, hcancel', hdiff] at h

/-- **The chained Lipschitz bound on a whole cube.**  A uniform bound `G` on
the gauges of every cube of the cover of `cu_r` gives the seminorm bound `G` on
any convex subset of `cu_r`, with no loss. -/
theorem norm_deriv_unscalePotential_sub_le_of_forall_le (k : ℕ)
    (omega : PotentialSample d) {r : ℤ} {G : ℝ}
    (hG : ∀ p ∈ shellCoverShifts d r,
      translatedShellG2 k (shellCoverCenter p) omega ≤ G)
    {S : Set (Vec d)} (hS : Convex ℝ S)
    (hSsub : S ⊆ openCubeSet (originCube d r))
    {w w' : Vec d} (hw : w ∈ S) (hw' : w' ∈ S) :
    ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (unscalePotential k (omega k)) w -
        _root_.SubdiffusiveProcess.Model.PotentialField.deriv (unscalePotential k (omega k)) w'‖ ≤ G * ‖w - w'‖ := by
  refine norm_sub_le_mul_of_forall_norm_sub_le hS
    (by norm_num : (0 : ℝ) < (6 : ℝ)⁻¹) ?_ hw hw'
  intro a ha b hb hab
  obtain ⟨p, hp, hap, hbp⟩ := exists_shellCoverShift_mem_pair (hSsub ha) hab
  exact (norm_deriv_unscalePotential_sub_le_translatedShellG2_mul k omega p hap hbp).trans
    (mul_le_mul_of_nonneg_right (hG p hp) (norm_nonneg _))

/-! ## The growing ball and its cover -/

/-- The printed `C 2ⁿ` with `C = 2`: the radius of the ball on which the shell
derivative bounds are asserted at dyadic scale `n`. -/
def growingBallRadius (n : ℕ) : ℝ := 2 ^ (n + 1)

theorem growingBallRadius_pos (n : ℕ) : 0 < growingBallRadius n := by
  rw [growingBallRadius]
  positivity

/-- The triadic scale of a cube containing the whole rescaled ball
`3^{-k} B_{2^{n+1}}`. -/
def coverExp (n k : ℕ) : ℤ := (n : ℤ) + 2 - (k : ℤ)

theorem coverExp_le_rowExp (n k : ℕ) : coverExp n k ≤ ((n + k : ℕ) : ℤ) + 2 := by
  simp only [coverExp]
  omega

/-- The shift set of the cover grows with the cube: this is what lets one row
of the graded envelope use a single shift set for all its entries. -/
theorem shellCoverShifts_subset {r r' : ℤ} (h : r ≤ r') :
    shellCoverShifts d r ⊆ shellCoverShifts d r' := by
  intro p hp
  rw [shellCoverShifts, Fintype.mem_piFinset] at hp ⊢
  intro i
  have hnat : shellCoverRadius r ≤ shellCoverRadius r' := by
    rw [shellCoverRadius, shellCoverRadius]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hR : (shellCoverRadius r : ℤ) ≤ (shellCoverRadius r' : ℤ) := by
    exact_mod_cast hnat
  have hmem := Finset.mem_Icc.mp (hp i)
  exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩

theorem mem_originCube_of_mem_scaledBall (n k : ℕ) {w : Vec d}
    (hw : w ∈ Metric.closedBall (0 : Vec d)
      ((((3 : ℝ) ^ k)⁻¹) * growingBallRadius n)) :
    w ∈ openCubeSet (originCube d (coverExp n k)) := by
  have h3 : (0 : ℝ) < (((3 : ℝ) ^ k)⁻¹) := by positivity
  rw [Metric.mem_closedBall, dist_zero_right] at hw
  rw [mem_openCubeSet_originCube_iff]
  have hpow : (3 : ℝ) ^ (coverExp n k) =
      (3 : ℝ) ^ (n + 2) * (((3 : ℝ) ^ k)⁻¹) := by
    have hne : (3 : ℝ) ≠ 0 := by norm_num
    rw [coverExp, zpow_sub₀ hne,
      show ((n : ℤ) + 2) = ((n + 2 : ℕ) : ℤ) by push_cast; ring]
    simp only [zpow_natCast]
    rw [div_eq_mul_inv]
  have hkey : (2 : ℝ) ^ (n + 1) < (1 / 2 : ℝ) * (3 : ℝ) ^ (n + 2) := by
    have h : (2 : ℝ) ^ (n + 2) < (3 : ℝ) ^ (n + 2) :=
      pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    have hsplit : (2 : ℝ) ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
    linarith
  have hbound : (((3 : ℝ) ^ k)⁻¹) * growingBallRadius n <
      (1 / 2 : ℝ) * (3 : ℝ) ^ (coverExp n k) := by
    rw [hpow, growingBallRadius]
    nlinarith [mul_lt_mul_of_pos_left hkey h3]
  intro i
  have hwi : |w i| ≤ (((3 : ℝ) ^ k)⁻¹) * growingBallRadius n :=
    (norm_le_pi_norm w i).trans hw
  have habs := abs_le.mp hwi
  constructor
  · linarith [habs.1]
  · linarith [habs.2]

theorem smul_mem_scaledBall (n k : ℕ) {x : Vec d}
    (hx : x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n)) :
    (((3 : ℝ) ^ k)⁻¹) • x ∈ Metric.closedBall (0 : Vec d)
      ((((3 : ℝ) ^ k)⁻¹) * growingBallRadius n) := by
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < (((3 : ℝ) ^ k)⁻¹))]
  exact mul_le_mul_of_nonneg_left hx (by positivity)

/-! ## The diagonal rows and their entropy -/

/-- Row `m` of the derivative index: a splitting `n + k = m` of the diagonal
together with a cube of the cover.  A single shift set serves the whole row
because `coverExp n k ≤ m + 2` (`coverExp_le_rowExp`). -/
def derivIndex (d m : ℕ) : Finset ((ℕ × ℕ) × (Fin d → ℤ)) :=
  Finset.antidiagonal m ×ˢ shellCoverShifts d ((m : ℤ) + 2)

theorem card_derivIndex (d m : ℕ) :
    (derivIndex d m).card = (m + 1) * (2 * 3 ^ (m + 3) + 1) ^ d := by
  have htoNat : (((m : ℤ) + 2) + 1).toNat = m + 3 := by omega
  rw [derivIndex, Finset.card_product, Finset.Nat.card_antidiagonal,
    card_shellCoverShifts, shellCoverRadius, htoNat]

theorem card_derivIndex_le_pow (d m : ℕ) :
    (derivIndex d m).card ≤ 3 ^ ((4 * d + 1) * (m + 1)) := by
  have h1 : m + 1 ≤ 3 ^ (m + 1) := by
    have h : m + 1 < 3 ^ (m + 1) := Nat.lt_pow_self (by norm_num)
    omega
  have h2 : 2 * 3 ^ (m + 3) + 1 ≤ 3 ^ (m + 4) := by
    have h3 : (1 : ℕ) ≤ 3 ^ (m + 3) := Nat.one_le_pow _ _ (by norm_num)
    have hsplit : 3 ^ (m + 4) = 3 * 3 ^ (m + 3) := by ring
    omega
  calc (derivIndex d m).card = (m + 1) * (2 * 3 ^ (m + 3) + 1) ^ d :=
        card_derivIndex d m
    _ ≤ 3 ^ (m + 1) * (3 ^ (m + 4)) ^ d :=
        Nat.mul_le_mul h1 (Nat.pow_le_pow_left h2 d)
    _ = 3 ^ ((m + 1) + (m + 4) * d) := by rw [← pow_mul, ← pow_add]
    _ ≤ 3 ^ ((4 * d + 1) * (m + 1)) := by
        refine Nat.pow_le_pow_right (by norm_num) ?_
        nlinarith

/-- The row-entropy exponent of the cover. -/
def derivRowGrowth (d : ℕ) : ℝ := (4 * (d : ℝ) + 1) * Real.log 3

theorem derivRowGrowth_nonneg (d : ℕ) : 0 ≤ derivRowGrowth d := by
  have hlog : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  rw [derivRowGrowth]
  nlinarith

theorem card_derivIndex_le (d m : ℕ) :
    ((derivIndex d m).card : ℝ) ≤
      Real.exp (derivRowGrowth d * ((m : ℝ) + 1)) := by
  have hexp : Real.exp (derivRowGrowth d * ((m : ℝ) + 1)) =
      ((3 ^ ((4 * d + 1) * (m + 1)) : ℕ) : ℝ) := by
    have hrw : derivRowGrowth d * ((m : ℝ) + 1) =
        (((4 * d + 1) * (m + 1) : ℕ) : ℝ) * Real.log 3 := by
      rw [derivRowGrowth]
      push_cast
      ring
    rw [hrw, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    push_cast
    ring
  rw [hexp]
  exact_mod_cast card_derivIndex_le_pow d m

/-- The Gaussian threshold multiplier of the cover rows. -/
def derivLam (d : ℕ) : ℝ := 1 + Real.sqrt (derivRowGrowth d + 2)

theorem one_le_derivLam (d : ℕ) : 1 ≤ derivLam d := by
  have := Real.sqrt_nonneg (derivRowGrowth d + 2)
  rw [derivLam]
  linarith

theorem derivRowGrowth_add_two_le_derivLam_sq (d : ℕ) :
    derivRowGrowth d + 2 ≤ derivLam d ^ 2 := by
  have hnn : (0 : ℝ) ≤ derivRowGrowth d + 2 := by
    have := derivRowGrowth_nonneg d
    linarith
  have hsq : Real.sqrt (derivRowGrowth d + 2) ^ 2 = derivRowGrowth d + 2 :=
    Real.sq_sqrt hnn
  have hs : (0 : ℝ) ≤ Real.sqrt (derivRowGrowth d + 2) := Real.sqrt_nonneg _
  rw [derivLam]
  nlinarith

/-! ## The per-entry `Γ₂` input -/

/-- The observable of a row entry: the `(g2)` gauge of the reverse-scaled shell
translated to the cube of the cover. -/
def coverGauge (i : (ℕ × ℕ) × (Fin d → ℤ)) (omega : PotentialSample d) : ℝ :=
  translatedShellG2 i.1.2 (shellCoverCenter i.2) omega

/-- The row scale is constant: the `Γ₂` scale of `translatedShellG2` is uniform
in the shell and in the shift (`isBigOWith_gammaTwo_translatedShellG2`), which
is `e.same.law.shift` together with `e.coefficient.field.regularity`. -/
def coverGaugeScale (M : GMCModel d) : ℝ := (1 + Real.log 2) ^ (2 : ℝ)⁻¹ * M.delta

theorem coverGaugeScale_nonneg (M : GMCModel d) : 0 ≤ coverGaugeScale M := by
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hrpow : (0 : ℝ) ≤ (1 + Real.log 2) ^ (2 : ℝ)⁻¹ :=
    Real.rpow_nonneg (by linarith) _
  exact mul_nonneg hrpow M.shellPrefix.delta_pos.le

theorem isBigOWith_gammaTwo_coverGauge (M : GMCModel d)
    (i : (ℕ × ℕ) × (Fin d → ℤ)) :
    IsBigOWith M.P.toMeasure (gammaSigma 2) (coverGauge i) (coverGaugeScale M) :=
  isBigOWith_gammaTwo_translatedShellG2 M i.1.2 (shellCoverCenter i.2)

/-! ## The gauge envelope -/

/-- The probabilistic core of `e.finite.cutoff.derivative.Borel.Cantelli`:
almost surely one finite random constant dominates **every** cube gauge of
**every** cover, at the price `√(n+k+1)`. -/
theorem ae_exists_forall_translatedShellG2_le (M : GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∃ C : ℝ, 0 ≤ C ∧
      ∀ n k : ℕ, ∀ p ∈ shellCoverShifts d (coverExp n k),
        translatedShellG2 k (shellCoverCenter p) omega ≤
          C * Real.sqrt ((n : ℝ) + (k : ℝ) + 1) := by
  have henv := ae_exists_forall_le_sqrt_mul_of_isBigOWith_gammaTwo
    (mu := M.P.toMeasure) (I := derivIndex d)
    (X := fun _ i => coverGauge i) (a := fun _ => coverGaugeScale M)
    (derivRowGrowth_nonneg d) (one_le_derivLam d)
    (derivRowGrowth_add_two_le_derivLam_sq d) (card_derivIndex_le d)
    (fun _ i _ => isBigOWith_gammaTwo_coverGauge M i)
  refine henv.mono ?_
  rintro omega ⟨C, hC0, hC⟩
  refine ⟨C * coverGaugeScale M, mul_nonneg hC0 (coverGaugeScale_nonneg M), ?_⟩
  intro n k p hp
  have hmem : ((n, k), p) ∈ derivIndex d (n + k) :=
    Finset.mem_product.2 ⟨Finset.mem_antidiagonal.2 rfl,
      shellCoverShifts_subset (coverExp_le_rowExp n k) hp⟩
  have h := hC (n + k) ((n, k), p) hmem
  simp only [coverGauge] at h
  refine h.trans_eq ?_
  have hcast : (((n + k : ℕ) : ℝ) + 1) = (n : ℝ) + (k : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  ring

/-! ## The growing-ball derivative bound -/

/-- **The growing-ball derivative Borel–Cantelli**,
`e.finite.cutoff.derivative.Borel.Cantelli`.

Almost surely there is one finite `C_ω ≥ 0` such that, simultaneously for every
dyadic scale `n` and every shell `k`, on the ball `B_{2^{n+1}}`:

* `‖∇g_k‖ ≤ C_ω 3^{-k} √(n+k+1)` (the printed `r = 1`);
* `‖∇g_k(x) - ∇g_k(y)‖ ≤ C_ω 3^{-2k} √(n+k+1) ‖x - y‖` (the printed `r = 2`, in
  the `C^{1,1}` form the carrier stores);
* `|g_k(x) - g_k(0)| ≤ 2^{n+1} · C_ω 3^{-k} √(n+k+1)` (the anchored `r = 0`
  readout obtained from the gradient bound by the mean value inequality; this
  is the estimate the printed proof uses ). -/
theorem ae_exists_forall_growingBall_shell_bounds (M : GMCModel d) :
    ∀ᵐ omega ∂M.P.toMeasure, ∃ C : ℝ, 0 ≤ C ∧ ∀ n k : ℕ,
      (∀ x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
          ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega k) x‖ ≤
            C * ((((3 : ℝ) ^ k)⁻¹) * Real.sqrt ((n : ℝ) + (k : ℝ) + 1))) ∧
        (∀ x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
            ∀ y ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
              ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega k) x -
                  _root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega k) y‖ ≤
                C * ((((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹) *
                  Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * ‖x - y‖) ∧
        (∀ x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
            |omega k x - omega k 0| ≤
              growingBallRadius n *
                (C * ((((3 : ℝ) ^ k)⁻¹) *
                  Real.sqrt ((n : ℝ) + (k : ℝ) + 1)))) := by
  refine (ae_exists_forall_translatedShellG2_le M).mono ?_
  rintro omega ⟨C, hC0, hC⟩
  refine ⟨C, hC0, fun n k => ?_⟩
  have h3 : (0 : ℝ) < (((3 : ℝ) ^ k)⁻¹) := by positivity
  set G : ℝ := C * Real.sqrt ((n : ℝ) + (k : ℝ) + 1) with hG_def
  have hGmem : ∀ p ∈ shellCoverShifts d (coverExp n k),
      translatedShellG2 k (shellCoverCenter p) omega ≤ G := hC n k
  have hgrad : ∀ x ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n),
      ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega k) x‖ ≤ (((3 : ℝ) ^ k)⁻¹) * G := by
    intro x hx
    have hball := smul_mem_scaledBall (d := d) n k hx
    have hcube := mem_originCube_of_mem_scaledBall (d := d) n k hball
    obtain ⟨p, hp, hmem⟩ := exists_shellCoverShift_mem hcube
    have hbox := norm_deriv_unscalePotential_le_translatedShellG2 k omega p hmem
    rw [deriv_eq_smul_deriv_unscalePotential k (omega k) x, norm_smul,
      Real.norm_eq_abs, abs_of_pos h3]
    exact mul_le_mul_of_nonneg_left (hbox.trans (hGmem p hp)) h3.le
  refine ⟨fun x hx => (hgrad x hx).trans_eq (by rw [hG_def]; ring), ?_, ?_⟩
  · intro x hx y hy
    have hballx := smul_mem_scaledBall (d := d) n k hx
    have hbally := smul_mem_scaledBall (d := d) n k hy
    have hchain := norm_deriv_unscalePotential_sub_le_of_forall_le k omega hGmem
      (S := Metric.closedBall (0 : Vec d) ((((3 : ℝ) ^ k)⁻¹) * growingBallRadius n))
      (convex_closedBall _ _)
      (fun w hw => mem_originCube_of_mem_scaledBall n k hw) hballx hbally
    have hkey : _root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega k) x - _root_.SubdiffusiveProcess.Model.PotentialField.deriv (omega k) y =
        (((3 : ℝ) ^ k)⁻¹) •
          (_root_.SubdiffusiveProcess.Model.PotentialField.deriv (unscalePotential k (omega k))
              ((((3 : ℝ) ^ k)⁻¹) • x) -
            _root_.SubdiffusiveProcess.Model.PotentialField.deriv (unscalePotential k (omega k))
              ((((3 : ℝ) ^ k)⁻¹) • y)) := by
      rw [smul_sub, ← deriv_eq_smul_deriv_unscalePotential k (omega k) x,
        ← deriv_eq_smul_deriv_unscalePotential k (omega k) y]
    have hscaled : ‖(((3 : ℝ) ^ k)⁻¹) • x - (((3 : ℝ) ^ k)⁻¹) • y‖ =
        (((3 : ℝ) ^ k)⁻¹) * ‖x - y‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos h3]
    rw [hscaled] at hchain
    rw [hkey, norm_smul, Real.norm_eq_abs, abs_of_pos h3]
    calc (((3 : ℝ) ^ k)⁻¹) *
          ‖_root_.SubdiffusiveProcess.Model.PotentialField.deriv (unscalePotential k (omega k))
              ((((3 : ℝ) ^ k)⁻¹) • x) -
            _root_.SubdiffusiveProcess.Model.PotentialField.deriv (unscalePotential k (omega k))
              ((((3 : ℝ) ^ k)⁻¹) • y)‖
        ≤ (((3 : ℝ) ^ k)⁻¹) * (G * ((((3 : ℝ) ^ k)⁻¹) * ‖x - y‖)) :=
          mul_le_mul_of_nonneg_left hchain h3.le
      _ = C * ((((3 : ℝ) ^ k)⁻¹ * ((3 : ℝ) ^ k)⁻¹) *
            Real.sqrt ((n : ℝ) + (k : ℝ) + 1)) * ‖x - y‖ := by
          rw [hG_def]; ring
  · intro x hx
    have hconv : Convex ℝ (Metric.closedBall (0 : Vec d) (growingBallRadius n)) :=
      convex_closedBall _ _
    have hzero : (0 : Vec d) ∈ Metric.closedBall (0 : Vec d) (growingBallRadius n) := by
      simpa using (growingBallRadius_pos n).le
    have hmean := hconv.norm_image_sub_le_of_norm_fderiv_le
      (f := fun z : Vec d => omega k z)
      (fun z _ => ((omega k).hasFDerivAt z).differentiableAt)
      (fun z hz => by
        rw [((omega k).hasFDerivAt z).fderiv]
        exact hgrad z hz)
      hzero hx
    rw [Real.norm_eq_abs] at hmean
    have hxnorm : ‖x - (0 : Vec d)‖ ≤ growingBallRadius n := by simpa using hx
    have hGnn : 0 ≤ G := by
      rw [hG_def]
      exact mul_nonneg hC0 (Real.sqrt_nonneg _)
    have hCnn : 0 ≤ (((3 : ℝ) ^ k)⁻¹) * G := mul_nonneg h3.le hGnn
    refine hmean.trans ?_
    calc (((3 : ℝ) ^ k)⁻¹) * G * ‖x - (0 : Vec d)‖
        ≤ (((3 : ℝ) ^ k)⁻¹) * G * growingBallRadius n :=
          mul_le_mul_of_nonneg_left hxnorm hCnn
      _ = growingBallRadius n *
            (C * ((((3 : ℝ) ^ k)⁻¹) * Real.sqrt ((n : ℝ) + (k : ℝ) + 1))) := by
          rw [hG_def]; ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Anchored
