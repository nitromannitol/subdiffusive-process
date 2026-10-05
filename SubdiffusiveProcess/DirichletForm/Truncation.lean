/-
# The zero-trace truncation `T_ε(s) = sgn(s)(|s| - ε)₊`
-/
module

public import SubdiffusiveProcess.DirichletForm.EnergyMeasure

@[expose] public section

/-!
# The zero-trace truncation

`T_ε(s) = sgn(s)(|s| - ε)₊`, written here as the soft threshold
`max (s - ε) 0 - max (-s - ε) 0`, is the normal contraction used to show that a
continuous function of the domain vanishing on the boundary of an open set lies
in the killed space of that set.  This file records its elementary properties:
it is a normal contraction, it vanishes on `[-ε, ε]`, it differs from the
identity by at most `ε`, and it has derivative `1` off `[-ε, ε]` and `0` inside.
-/

open Real

noncomputable section

namespace SubdiffusiveProcess.DirichletForm

/-- The zero-trace truncation `T_ε(s) = sgn(s)(|s| - ε)₊`, as a soft threshold. -/
def truncation (ε s : ℝ) : ℝ := max (s - ε) 0 - max (-s - ε) 0

@[simp] theorem truncation_zero (ε : ℝ) : truncation ε 0 = 0 := by
  simp [truncation]

/-- `T_ε` is the identity minus `ε` above the threshold. -/
theorem truncation_of_lt {ε s : ℝ} (hε : 0 ≤ ε) (hs : ε < s) : truncation ε s = s - ε := by
  rw [truncation, max_eq_left (by linarith : (0:ℝ) ≤ s - ε),
    max_eq_right (by linarith : -s - ε ≤ 0)]
  ring

/-- `T_ε` is the identity plus `ε` below the threshold. -/
theorem truncation_of_lt_neg {ε s : ℝ} (hε : 0 ≤ ε) (hs : s < -ε) :
    truncation ε s = s + ε := by
  rw [truncation, max_eq_right (by linarith : s - ε ≤ 0),
    max_eq_left (by linarith : (0:ℝ) ≤ -s - ε)]
  ring

/-- `T_ε` vanishes on `[-ε, ε]`. -/
theorem truncation_of_abs_le {ε s : ℝ} (hs : |s| ≤ ε) : truncation ε s = 0 := by
  have h1 : s ≤ ε := (abs_le.mp hs).2
  have h2 : -ε ≤ s := (abs_le.mp hs).1
  rw [truncation, max_eq_right (by linarith : s - ε ≤ 0),
    max_eq_right (by linarith : -s - ε ≤ 0)]
  ring

/-- `T_ε` is a normal contraction. -/
theorem isIsNormalContraction_truncation {ε : ℝ} (hε : 0 ≤ ε) :
    IsNormalContraction (truncation ε) where
  map_zero := truncation_zero ε
  dist_le s t := by
    have h1 := le_abs_self (s - t)
    have h2 := neg_abs_le (s - t)
    rw [abs_le]
    constructor <;>
      · simp only [truncation, max_def]
        split_ifs <;> linarith

/-- `T_ε` differs from the identity by at most `ε`. -/
theorem abs_truncation_sub_self_le {ε : ℝ} (hε : 0 ≤ ε) (s : ℝ) :
    |truncation ε s - s| ≤ ε := by
  rw [abs_le]
  constructor <;>
    · simp only [truncation, max_def]
      split_ifs <;> linarith

/-- Above the threshold `T_ε` has derivative `1`. -/
theorem hasDerivAt_truncation_of_lt {ε s : ℝ} (hε : 0 ≤ ε) (hs : ε < s) :
    HasDerivAt (truncation ε) 1 s := by
  have hev : (truncation ε) =ᶠ[nhds s] fun x => x - ε := by
    filter_upwards [eventually_gt_nhds hs] with x hx using truncation_of_lt hε hx
  have hd : HasDerivAt (fun x : ℝ => x - ε) 1 s := (hasDerivAt_id s).sub_const ε
  exact hd.congr_of_eventuallyEq hev

/-- Below the negative threshold `T_ε` has derivative `1`. -/
theorem hasDerivAt_truncation_of_lt_neg {ε s : ℝ} (hε : 0 ≤ ε) (hs : s < -ε) :
    HasDerivAt (truncation ε) 1 s := by
  have hev : (truncation ε) =ᶠ[nhds s] fun x => x + ε := by
    filter_upwards [eventually_lt_nhds hs] with x hx using truncation_of_lt_neg hε hx
  have hd : HasDerivAt (fun x : ℝ => x + ε) 1 s := (hasDerivAt_id s).add_const ε
  exact hd.congr_of_eventuallyEq hev

/-- Strictly inside the threshold `T_ε` has derivative `0`. -/
theorem hasDerivAt_truncation_of_abs_lt {ε s : ℝ} (hs : |s| < ε) :
    HasDerivAt (truncation ε) 0 s := by
  have hev : (truncation ε) =ᶠ[nhds s] fun _ => (0 : ℝ) := by
    have hopen : IsOpen {x : ℝ | |x| < ε} := isOpen_lt (by fun_prop) continuous_const
    filter_upwards [hopen.mem_nhds hs] with x hx using truncation_of_abs_le (le_of_lt hx)
  have hd : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 s := hasDerivAt_const s (0 : ℝ)
  exact hd.congr_of_eventuallyEq hev

section Level

variable {X : Type*} [TopologicalSpace X]

/-- **The compact level set of the truncation argument**
(`mfd:lem-truncation`).  If `v` is continuous, vanishes on
`frontier q` and `closure q` is compact, then
`K_ε = {|v| ≥ ε} ∩ closure q` is compact and contained in `q`.

Containment is the point: `ε > 0` forces `v ≠ 0` on `K_ε`, so `K_ε` misses
`frontier q`, and a point of `closure q` off the frontier is interior. -/
theorem isCompact_levelSet {vc : X → ℝ} (hvc : Continuous vc) {q : Set X}
    (hqc : IsCompact (closure q)) (ε : ℝ) :
    IsCompact ({x : X | ε ≤ |vc x|} ∩ closure q) := by
  have hclosed : IsClosed {x : X | ε ≤ |vc x|} :=
    isClosed_le continuous_const hvc.abs
  exact hqc.inter_left hclosed

theorem levelSet_subset {vc : X → ℝ} {q : Set X} (hq : IsOpen q)
    (hvanish : ∀ x ∈ frontier q, vc x = 0) {ε : ℝ} (hε : 0 < ε) :
    {x : X | ε ≤ |vc x|} ∩ closure q ⊆ q := by
  rintro x ⟨hx1, hx2⟩
  simp only [Set.mem_ofPred_eq] at hx1
  have hne : vc x ≠ 0 := by
    intro h
    rw [h, abs_zero] at hx1
    linarith
  have hnf : x ∉ frontier q := fun hf => hne (hvanish x hf)
  have : x ∈ interior q := by
    by_contra hint
    exact hnf ⟨hx2, hint⟩
  rwa [hq.interior_eq] at this

end Level

end SubdiffusiveProcess.DirichletForm
