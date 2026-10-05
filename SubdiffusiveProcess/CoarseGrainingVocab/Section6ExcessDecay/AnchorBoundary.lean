module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.AnchorCompetitor
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.CorrectorPrice
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.OneStepL2
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.AnchorInterior
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.ComposeGlue
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6OddClass.Interface



@[expose] public section

/-!
# The excess-decay assembly at a boundary-touching window

The twin of `AnchorInterior.excess_decay_good_scales_interior` under the negated
interior gate

```text
  ¬ (translatedCube d (n-4) x ⊆ cube d m) ,
```

which by `AnchorCompetitor.exists_meetsFace_of_not_translatedCube_subset` is
exactly the statement that the one-step window meets a face of `∂□_m`, and by
`AnchorInterior.boundaryTouches_of_not_translatedCube_subset` switches on the two
`BoundaryTouches` legs of the frozen conclusion.

The two premises are the same two hypothesis-shaped conclusions the
interior branch carries, and the conclusion is the frozen conclusion of
`l.excess.decay.good.scales.GMC` verbatim.

## What replaces the interior Schauder step

Steps `.1`, `.2`, `.6`, `.7`, `.8` and the arithmetic of `.9` are unchanged.
Step `.3` — the Schauder estimate — and steps `.4`/`.5` — the one-step
contraction — are the boundary versions:

* the competitor is the **odd extension** of the datum split
  `V_odd = v − ℓ_h − v₁` across every met face, produced from the anchor's
  enveloping-cube trace datum by
  `Section6BoundaryL2.exists_classicalCompetitor_datumSplit_anchor`;
* the Schauder estimate is the **odd-class fold's** endpoint,
  `Section6OddClass.Interface.exists_gradientHolder_boundary_metSet_truncatedCube`,
  whose bound is by the excess alone — `K_hS = 0`, so the additive leg of the
  one-step conclusion vanishes identically;
* the corrector `v₁` is the weakly harmonic replacement of the mean-zero datum
  deviation on the anchor's replacement cube, and is priced in `L̲²` by
  `Section6BoundaryL2.normalizedL2On_harmonicCorrector_le`.  That price is
  linear in the Hölder seminorm of `∇h` and lies, after the `3^{-n}` weight of
  the one-step, in the frozen conclusion's fourth line — the only line of the
  display that carries `[∇h]_{C^{0,1/2}}`, and the line whose indicator is on
  precisely here.

## References

* paper label `l.excess.decay.good.scales.GMC` (statement and proof).
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### The constant of the corrector leg -/

/-- The constant of the `L̲²`-priced corrector leg: two scaled Poincaré
constants, the volume ratio `|Y| / |W| ≤ 81^d` between the anchor's
replacement cube and the one-step window, and the two factors `√d` coming from
the coordinate sums. -/
def correctorLegConst (d : ℕ) [NeZero d] : ℝ :=
  (d : ℝ) ^ 2 * (2 * unitDirichletPoincareConst d
    + unitMeanZeroPoincareConst d * Real.sqrt ((81 : ℝ) ^ d))

theorem correctorLegConst_nonneg (d : ℕ) [NeZero d] : 0 ≤ correctorLegConst d := by
  have h1 := unitDirichletPoincareConst_nonneg d
  have h2 := unitMeanZeroPoincareConst_nonneg d
  have h3 : (0 : ℝ) ≤ Real.sqrt ((81 : ℝ) ^ d) := Real.sqrt_nonneg _
  have h4 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  have h5 : (0 : ℝ) ≤ 2 * unitDirichletPoincareConst d
      + unitMeanZeroPoincareConst d * Real.sqrt ((81 : ℝ) ^ d) := by positivity
  exact mul_nonneg h4 h5

/-! ### The constant of the boundary assembly -/

/-- The constant of the boundary assembly: the boundary Schauder contraction,
the remainder route through the harmonic-approximation constant `CA`, the
`𝓔`-cap constant `CB` and the corrector leg, and the crude `k < 6` branch. -/
def anchorBoundaryConst (d : ℕ) [NeZero d] (CA CB Csch : ℝ) : ℝ :=
  oneStepContractionConst d * Csch
    + (81 * taylorConst d * Csch + 1) *
        (CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
          + correctorLegConst d)
    + 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) + 1

section ConstBounds

variable (d : ℕ) [NeZero d] {CA CB Csch : ℝ}

omit [NeZero d] in
private theorem boundaryRemainderFactor_nonneg (hCsch : 0 ≤ Csch) :
    (0 : ℝ) ≤ 81 * taylorConst d * Csch + 1 := by
  have h1 := taylorConst_nonneg d
  nlinarith

private theorem boundaryBracket_nonneg (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) :
    (0 : ℝ) ≤ CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
      + correctorLegConst d := by
  have h1 : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have h2 := fractionalHolderConst_nonneg d
  have h3 := correctorLegConst_nonneg d
  have h4 : (0 : ℝ) ≤ CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d := by
    linarith
  nlinarith

theorem anchorBoundaryConst_contraction_le (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCsch : 0 ≤ Csch) :
    oneStepContractionConst d * Csch ≤ anchorBoundaryConst d CA CB Csch := by
  have h1 : (0 : ℝ) ≤ (81 * taylorConst d * Csch + 1) *
      (CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
        + correctorLegConst d) :=
    mul_nonneg (boundaryRemainderFactor_nonneg d hCsch) (boundaryBracket_nonneg d hCA hCB)
  have h2 : (0 : ℝ) ≤ 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) := by positivity
  rw [anchorBoundaryConst]
  linarith

theorem anchorBoundaryConst_remainder_le (hCsch : 0 ≤ Csch) :
    (81 * taylorConst d * Csch + 1) *
        (CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
          + correctorLegConst d)
      ≤ anchorBoundaryConst d CA CB Csch := by
  have h1 : (0 : ℝ) ≤ oneStepContractionConst d * Csch :=
    mul_nonneg (oneStepContractionConst_nonneg d) hCsch
  have h2 : (0 : ℝ) ≤ 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) := by positivity
  rw [anchorBoundaryConst]
  linarith

theorem anchorBoundaryConst_crude_le (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCsch : 0 ≤ Csch) :
    3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) ≤ anchorBoundaryConst d CA CB Csch := by
  have h1 : (0 : ℝ) ≤ oneStepContractionConst d * Csch :=
    mul_nonneg (oneStepContractionConst_nonneg d) hCsch
  have h2 : (0 : ℝ) ≤ (81 * taylorConst d * Csch + 1) *
      (CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
        + correctorLegConst d) :=
    mul_nonneg (boundaryRemainderFactor_nonneg d hCsch) (boundaryBracket_nonneg d hCA hCB)
  rw [anchorBoundaryConst]
  linarith

theorem one_le_anchorBoundaryConst (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCsch : 0 ≤ Csch) :
    (1 : ℝ) ≤ anchorBoundaryConst d CA CB Csch := by
  have h := anchorBoundaryConst_crude_le d hCA hCB hCsch
  have h3 : (1 : ℝ) ≤ 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) := by
    have hs : (1 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ (7 * d)) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (one_le_pow₀ (by norm_num))
    nlinarith
  linarith

theorem anchorBoundaryConst_nonneg (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCsch : 0 ≤ Csch) :
    (0 : ℝ) ≤ anchorBoundaryConst d CA CB Csch :=
  le_trans zero_le_one (one_le_anchorBoundaryConst d hCA hCB hCsch)

theorem anchorBoundaryConst_pos (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCsch : 0 ≤ Csch) :
    (0 : ℝ) < anchorBoundaryConst d CA CB Csch :=
  lt_of_lt_of_le zero_lt_one (one_le_anchorBoundaryConst d hCA hCB hCsch)

end ConstBounds

/-! ### The boundary one-step at the anchor -/

/-- **The boundary one-step contraction, from the anchor's data alone.**

At a window meeting a face of `∂□_m`, the anchor's harmonic replacement `v` on
the enveloping cube `Y = y + □_{n-2}` and its Dirichlet datum `h` (of which only
the Hölder bound on the *weak* gradient is used) produce the boundary one-step
contraction with a constant depending on `d` alone.

The three legs of the conclusion are the contraction, the `L̲²` comparison error
`‖u − v‖_{L̲²(U_{m,n-4})}` which the harmonic-approximation anchor controls, and
the corrector leg, priced by `[∇h]_{C^{0,1/2}}` alone.  There is **no** fourth
leg: the odd-class fold's Schauder endpoint has no additive term, so the
`taylorConst · (3^{n-k})^{1/2} · K_hS` line of
`Section6BoundaryL2.excess_oneStep_boundary_datumSplit_l2` is identically `0`. -/
theorem exists_excess_oneStep_boundary_anchor (d : ℕ) [NeZero d] (hd : d ≠ 0) :
    ∃ Csch : ℝ, 0 ≤ Csch ∧
      ∀ m n k : ℕ, 6 ≤ k → n + 5 ≤ m →
      ∀ x y : Vec d, x ∈ cube d m →
        truncatedCube d m ((n : ℤ) - 4) x ⊆ translatedCube d ((n : ℤ) - 2) y →
        translatedCube d ((n : ℤ) - 2) y ⊆ truncatedCube d m ((n : ℤ) - 1) x →
        ¬ translatedCube d ((n : ℤ) - 4) x ⊆ cube d m →
      ∀ u h : H1Function (openCubeSet (originCube d m)),
        MemH10 (openCubeSet (originCube d m)) (fun p => u.toFun p - h.toFun p) →
        MemHolder (truncatedCube d m (n : ℤ) x) (1 / 2) h.grad →
      ∀ v : H1Function (translatedCube d ((n : ℤ) - 2) y),
        IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d ((n : ℤ) - 2) y) v →
        MemH10 (translatedCube d ((n : ℤ) - 2) y) (fun p => v.toFun p - u.toFun p) →
      excess ((n : ℤ) - (k : ℤ)) (truncatedCube d m ((n : ℤ) - (k : ℤ)) x) u.toFun
        ≤ oneStepContractionConst d * Csch * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
              excess (n : ℤ) (truncatedCube d m (n : ℤ) x) u.toFun
          + oneStepRemainderConst d Csch k * ((3 : ℝ) ^ (-(n : ℤ)) *
              normalizedL2On (truncatedCube d m ((n : ℤ) - 4) x)
                (fun p => u.toFun p - v.toFun p))
          + oneStepRemainderConst d Csch k *
              (correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) *
                holderSeminormOn (truncatedCube d m (n : ℤ) x) (1 / 2) h.grad) := by
  classical
  obtain ⟨C0, hC00, hC0⟩ :=
    Section6OddClass.exists_gradientHolder_boundary_metSet_truncatedCube d hd
  refine ⟨C0, hC00, ?_⟩
  intro m n k hk6 hnm5 x y hx hy1 hy2 hgate u h hdat hhold
  -- the two windows
  revert hy1 hy2
  set W : Set (Vec d) := truncatedCube d (m : ℤ) ((n : ℤ) - 4) x with hWdef
  set Y : Set (Vec d) := translatedCube d ((n : ℤ) - 2) y with hYdef
  intro hy1 hy2 v hvharm hvu
  set Csch : ℝ := C0 with hCschdef
  have hCsch0 : (0 : ℝ) ≤ Csch := hC00
  have hkm : (n : ℤ) - 4 < (m : ℤ) := by
    have : (n : ℤ) + 5 ≤ (m : ℤ) := by exact_mod_cast hnm5
    omega
  have hWopen : IsOpen W := Section6Schauder.isOpen_truncatedWindow x (m : ℤ) ((n : ℤ) - 4)
  have hYopen : IsOpen Y := Section6Schauder.isOpen_translatedCube d ((n : ℤ) - 2) y
  have hYsub : Y ⊆ cube d (m : ℤ) :=
    hy2.trans (truncatedCube_subset_cube d (m : ℤ) ((n : ℤ) - 1) x)
  have hYsub' : Y ⊆ openCubeSet (originCube d (m : ℤ)) := hYsub
  have hYdom : Homogenization.IsOpenBoundedConvexDomain Y := by
    rw [hYdef, Section6BoundaryL2.translatedCube_eq_axisCube]
    exact Homogenization.isOpenBoundedConvexDomain_axisCube _ _
  have hYfin : IsFiniteMeasure (Homogenization.volumeMeasureOn Y) :=
    hYdom.isFiniteMeasure_restrict_volume
  have hSobY : Homogenization.IsSobolevRegularDomain Y := hYdom.isSobolevRegularDomain
  -- the datum deviation on the replacement cube, normalized to mean zero
  set A : Vec d := h.grad x with hAdef
  set fY : H1Function Y :=
    (h.restrict hYopen hYsub') - Section6SchauderDatum.affineLiftH1 hSobY x 0 A with hfYdef
  set Phi : H1Function Y := fY.subAverage with hPhidef
  set c : ℝ := Homogenization.integralAverage Y fY.toFun with hcdef
  have hfYfun : ∀ p, fY.toFun p = h.toFun p - affineLift x 0 A p := by
    intro p
    have h1 : fY.toFun = fun q => (h.restrict hYopen hYsub').toFun q
        - (Section6SchauderDatum.affineLiftH1 hSobY x 0 A).toFun q := by
      rw [hfYdef]
      exact Homogenization.H1Function.sub_toFun _ _
    rw [h1]
    simp only [Section6SchauderDatum.affineLiftH1_toFun]
    rfl
  have hfYgradfun : fY.grad = fun q => (h.restrict hYopen hYsub').grad q
      - (Section6SchauderDatum.affineLiftH1 hSobY x 0 A).grad q := by
    rw [hfYdef]
    exact Homogenization.H1Function.sub_grad _ _
  have hPhiFun : ∀ p, Phi.toFun p = h.toFun p - affineLift x c A p := by
    intro p
    have h1 : Phi.toFun p = fY.toFun p - c := by
      rw [hPhidef, hcdef]
      exact Homogenization.H1Function.subAverage_apply fY p
    rw [h1, hfYfun p, affineLift, affineLift]
    ring
  have hPhiGrad : ∀ p i, Phi.grad p i = h.grad p i - A i := by
    intro p i
    have h1 : Phi.grad p = fY.grad p := by
      rw [hPhidef]
      exact Homogenization.H1Function.grad_subAverage fY p
    rw [h1, hfYgradfun]
    simp only [Pi.sub_apply, Section6SchauderDatum.affineLiftH1_grad]
    rfl
  have hmean : Homogenization.volumeAverage Y Phi.toFun = 0 := by
    have h0 : Homogenization.MeanZeroOn Y fY.subAverage :=
      Homogenization.H1Function.meanZeroOn_subAverage fY
    have h1 : ∫ p in Y, Phi.toFun p ∂volume = 0 := h0
    rw [Homogenization.volumeAverage, h1, mul_zero]
  -- the pointwise gradient bound
  set Hh : ℝ := holderSeminormOn (truncatedCube d (m : ℤ) (n : ℤ) x) (1 / 2) h.grad with hHhdef
  have hHh0 : 0 ≤ Hh := holderSeminormOn_nonneg hhold
  set B : ℝ := Hh * ((d : ℝ) * ((3 : ℝ) ^ ((n : ℤ) - 1) / 2)) ^ (1 / 2 : ℝ) with hBdef
  have hB0 : 0 ≤ B := mul_nonneg hHh0 (Real.rpow_nonneg (by positivity) _)
  have hxW : x ∈ truncatedCube d (m : ℤ) (n : ℤ) x := mem_truncatedCube_self _ hx
  have hholbd := holderSeminormBoundOn_holderSeminormOn (by norm_num : (0 : ℝ) < 1 / 2) hhold
  have hgradB : ∀ p ∈ Y, ∀ i, |Phi.grad p i| ≤ B := by
    intro p hp i
    have hpn1 : p ∈ truncatedCube d (m : ℤ) ((n : ℤ) - 1) x := hy2 hp
    have hpW : p ∈ truncatedCube d (m : ℤ) (n : ℤ) x :=
      truncatedCube_mono d (m : ℤ) x (by omega) hpn1
    have h1 : |Phi.grad p i| ≤ Homogenization.euclideanNorm (h.grad p - h.grad x) := by
      rw [hPhiGrad p i]
      have h2 : ‖(h.grad p - h.grad x) i‖ ≤ ‖h.grad p - h.grad x‖ :=
        norm_le_pi_norm (h.grad p - h.grad x) i
      have h3 : ‖h.grad p - h.grad x‖
          ≤ Homogenization.euclideanNorm (h.grad p - h.grad x) :=
        Homogenization.norm_le_euclideanNorm _
      have h4 : |h.grad p i - h.grad x i| = ‖(h.grad p - h.grad x) i‖ := by
        rw [Real.norm_eq_abs]
        rfl
      rw [h4]
      linarith only [h2, h3]
    have h2 : Homogenization.euclideanNorm (h.grad p - h.grad x)
        ≤ Hh * Homogenization.euclideanNorm (p - x) ^ (1 / 2 : ℝ) :=
      hholbd p hpW x hxW
    have h3 : Homogenization.euclideanNorm (p - x) ≤ (d : ℝ) * ((3 : ℝ) ^ ((n : ℤ) - 1) / 2) := by
      refine le_trans (Homogenization.euclideanNorm_le_dimension_mul_norm (p - x)) ?_
      exact mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_truncatedCube hpn1)
        (Nat.cast_nonneg d)
    have h4 : Homogenization.euclideanNorm (p - x) ^ (1 / 2 : ℝ)
        ≤ ((d : ℝ) * ((3 : ℝ) ^ ((n : ℤ) - 1) / 2)) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (Homogenization.euclideanNorm_nonneg _) h3 (by norm_num)
    calc |Phi.grad p i| ≤ Homogenization.euclideanNorm (h.grad p - h.grad x) := h1
      _ ≤ Hh * Homogenization.euclideanNorm (p - x) ^ (1 / 2 : ℝ) := h2
      _ ≤ B := by rw [hBdef]; exact mul_le_mul_of_nonneg_left h4 hHh0
  -- the corrector
  have hWdom : Homogenization.IsOpenBoundedConvexDomain W :=
    Section6SchauderDatum.isOpenBoundedConvexDomain_truncatedWindow x (m : ℤ) ((n : ℤ) - 4)
  have hWne : W.Nonempty := ⟨x, mem_truncatedCube_self _ hx⟩
  obtain ⟨rho, hrhoharm⟩ :=
    Section6BoundaryL2.exists_h10Witness_isUnitWeaklyHarmonicOn hWdom hWne
      (Phi.restrict hWopen hy1)
  set Psi : H1Function W := Phi.restrict hWopen hy1 with hPsidef
  set v₁ : H1Function W := Psi + rho.toH1Function with hv₁def
  have hv₁harm : Section6Schauder.IsUnitWeaklyHarmonicOn W v₁ := hrhoharm
  have hPsiFun : ∀ p ∈ W, Psi.toFun p = h.toFun p - affineLift x c A p :=
    fun p _ => hPhiFun p
  have hv₁Psi : Homogenization.MemH10 W (fun p => v₁.toFun p - Psi.toFun p) := by
    refine ⟨rho, ?_⟩
    funext p
    have h1 : v₁.toFun p = Psi.toFun p + rho.toH1Function.toFun p := by
      rw [hv₁def, Homogenization.H1Function.add_toFun]
    rw [h1]
    ring
  -- volumes
  have hWpos : 0 < (volume W).toReal :=
    volume_toReal_truncatedCube_pos x hx (by omega)
  have hWtop : volume W ≠ ⊤ := (volume_truncatedCube_lt_top d (m : ℤ) ((n : ℤ) - 4) x).ne
  have hYvol : (volume Y).toReal = ((3 : ℝ) ^ ((n : ℤ) - 2)) ^ d := by
    rw [hYdef, Section6BoundaryL2.translatedCube_eq_axisCube,
      Section6Iteration.volume_axisCube_toReal _ (by positivity)]
  have hYpos : 0 < (volume Y).toReal := by
    rw [hYvol]; positivity
  have hWcube : W ⊆ translatedCube d ((n : ℤ) - 4) x :=
    truncatedCube_subset_translatedCube d (m : ℤ) ((n : ℤ) - 4) x
  -- the price
  have hprice := Section6BoundaryL2.normalizedL2On_harmonicCorrector_le
    (d := d) (W := W) (j := (n : ℤ) - 4) (jY := (n : ℤ) - 2) (zW := x) (zY := y) (B := B)
    hWopen hWpos hWtop hYpos hy1 hWcube hB0 Phi rho hmean hgradB hrhoharm
  set rt : ℝ := Real.sqrt ((volume Y).toReal / (volume W).toReal) with hrtdef
  set R : ℝ := (d : ℝ) * Real.sqrt (d : ℝ) *
      (2 * unitDirichletPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 4)
        + unitMeanZeroPoincareConst d * (3 : ℝ) ^ ((n : ℤ) - 2) * rt) * B with hRdef
  have hpriceR : normalizedL2On W v₁.toFun ≤ R := hprice
  -- the volume ratio
  have hratio : (volume Y).toReal / (volume W).toReal ≤ (81 : ℝ) ^ d := by
    have hlo : ((3 : ℝ) ^ ((n : ℤ) - 6)) ^ d ≤ (volume W).toReal := by
      have h := (volume_toReal_truncatedCube_bounds (m := (m : ℤ)) (j := (n : ℤ) - 4) x hx
        (by omega)).1
      rw [show (n : ℤ) - 4 - 2 = (n : ℤ) - 6 by ring] at h
      exact h
    have hlopos : (0 : ℝ) < ((3 : ℝ) ^ ((n : ℤ) - 6)) ^ d := by positivity
    have hhi : (volume Y).toReal ≤ ((3 : ℝ) ^ ((n : ℤ) - 2)) ^ d := le_of_eq hYvol
    have h35 : (3 : ℝ) ^ ((n : ℤ) - 2) = 81 * (3 : ℝ) ^ ((n : ℤ) - 6) := by
      rw [show ((n : ℤ) - 2) = 4 + ((n : ℤ) - 6) by ring,
        zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      norm_num
    rw [div_le_iff₀ hWpos]
    calc (volume Y).toReal = ((3 : ℝ) ^ ((n : ℤ) - 2)) ^ d := hYvol
      _ = (81 : ℝ) ^ d * ((3 : ℝ) ^ ((n : ℤ) - 6)) ^ d := by rw [h35, mul_pow]
      _ ≤ (81 : ℝ) ^ d * (volume W).toReal :=
          mul_le_mul_of_nonneg_left hlo (by positivity)
  have hrtle : rt ≤ Real.sqrt ((81 : ℝ) ^ d) := Real.sqrt_le_sqrt hratio
  have hrt0 : 0 ≤ rt := Real.sqrt_nonneg _
  -- the corrector leg, after the `3^{-n}` weight
  have hBle : B ≤ Hh * (Real.sqrt (d : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2)) := by
    have hstep : ((d : ℝ) * ((3 : ℝ) ^ ((n : ℤ) - 1) / 2)) ^ (1 / 2 : ℝ)
        ≤ Real.sqrt (d : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) := by
      have hle : (d : ℝ) * ((3 : ℝ) ^ ((n : ℤ) - 1) / 2) ≤ (d : ℝ) * (3 : ℝ) ^ (n : ℤ) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
        have h1 : (3 : ℝ) ^ ((n : ℤ) - 1) ≤ (3 : ℝ) ^ (n : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        have h2 : (0 : ℝ) < (3 : ℝ) ^ ((n : ℤ) - 1) := zpow_pos (by norm_num) _
        linarith only [h1, h2]
      have h3 : ((d : ℝ) * ((3 : ℝ) ^ ((n : ℤ) - 1) / 2)) ^ (1 / 2 : ℝ)
          ≤ ((d : ℝ) * (3 : ℝ) ^ (n : ℤ)) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hle (by norm_num)
      have h4 : ((d : ℝ) * (3 : ℝ) ^ (n : ℤ)) ^ (1 / 2 : ℝ)
          = Real.sqrt (d : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) := by
        rw [Real.mul_rpow (Nat.cast_nonneg d) (by positivity), ← Real.sqrt_eq_rpow]
        congr 1
        have h5 := three_zpow_rpow_half_eq (n : ℤ)
        rw [h5]
        norm_num
      exact h3.trans h4.le
    rw [hBdef]
    exact mul_le_mul_of_nonneg_left hstep hHh0
  have hRle : (3 : ℝ) ^ (-(n : ℤ)) * R
      ≤ correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh := by
    have e1 : (3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ ((n : ℤ) - 4) = (3 : ℝ) ^ (-4 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      ring
    have e2 : (3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ ((n : ℤ) - 2) = (3 : ℝ) ^ (-2 : ℤ) := by
      rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 1
      ring
    have hCD0 : (0 : ℝ) ≤ unitDirichletPoincareConst d := unitDirichletPoincareConst_nonneg d
    have hCM0 : (0 : ℝ) ≤ unitMeanZeroPoincareConst d := unitMeanZeroPoincareConst_nonneg d
    have hkey : (3 : ℝ) ^ (-(n : ℤ)) * R
        = (d : ℝ) * Real.sqrt (d : ℝ) *
            (2 * unitDirichletPoincareConst d * ((3 : ℝ) ^ (-4 : ℤ))
              + unitMeanZeroPoincareConst d * ((3 : ℝ) ^ (-2 : ℤ)) * rt) * B := by
      rw [hRdef, ← e1, ← e2]
      ring
    have hb1 : 2 * unitDirichletPoincareConst d * ((3 : ℝ) ^ (-4 : ℤ))
          + unitMeanZeroPoincareConst d * ((3 : ℝ) ^ (-2 : ℤ)) * rt
        ≤ 2 * unitDirichletPoincareConst d
          + unitMeanZeroPoincareConst d * Real.sqrt ((81 : ℝ) ^ d) := by
      have h1 : (3 : ℝ) ^ (-4 : ℤ) ≤ 1 := by norm_num
      have h2 : (3 : ℝ) ^ (-2 : ℤ) ≤ 1 := by norm_num
      have h3 : (0 : ℝ) < (3 : ℝ) ^ (-4 : ℤ) := by norm_num
      have h4 : (0 : ℝ) < (3 : ℝ) ^ (-2 : ℤ) := by norm_num
      have hA1 : 2 * unitDirichletPoincareConst d * ((3 : ℝ) ^ (-4 : ℤ))
          ≤ 2 * unitDirichletPoincareConst d :=
            mul_le_of_le_one_right (mul_nonneg (by norm_num) hCD0) h1
      have hA2 : unitMeanZeroPoincareConst d * ((3 : ℝ) ^ (-2 : ℤ)) * rt
          ≤ unitMeanZeroPoincareConst d * Real.sqrt ((81 : ℝ) ^ d) := by
        have hstep1 : unitMeanZeroPoincareConst d * ((3 : ℝ) ^ (-2 : ℤ)) * rt
            ≤ unitMeanZeroPoincareConst d * rt := by
          calc
            _ = (unitMeanZeroPoincareConst d * rt) * ((3 : ℝ) ^ (-2 : ℤ)) := by ring
            _ ≤ unitMeanZeroPoincareConst d * rt :=
              mul_le_of_le_one_right (mul_nonneg hCM0 hrt0) h2
        have hstep2 : unitMeanZeroPoincareConst d * rt
            ≤ unitMeanZeroPoincareConst d * Real.sqrt ((81 : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left hrtle hCM0
        exact hstep1.trans hstep2
      exact add_le_add hA1 hA2
    have hbr0 : (0 : ℝ) ≤ 2 * unitDirichletPoincareConst d
        + unitMeanZeroPoincareConst d * Real.sqrt ((81 : ℝ) ^ d) := by
      have hs0 : (0 : ℝ) ≤ Real.sqrt ((81 : ℝ) ^ d) := Real.sqrt_nonneg _
      exact add_nonneg (mul_nonneg (by norm_num) hCD0) (mul_nonneg hCM0 hs0)
    have hd0 : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt (d : ℝ) :=
      mul_nonneg (Nat.cast_nonneg d) (Real.sqrt_nonneg _)
    have hstep1 : (3 : ℝ) ^ (-(n : ℤ)) * R
        ≤ (d : ℝ) * Real.sqrt (d : ℝ) *
            (2 * unitDirichletPoincareConst d
              + unitMeanZeroPoincareConst d * Real.sqrt ((81 : ℝ) ^ d)) * B := by
      rw [hkey]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb1 hd0) hB0
    have hstep2 : (d : ℝ) * Real.sqrt (d : ℝ) *
          (2 * unitDirichletPoincareConst d
            + unitMeanZeroPoincareConst d * Real.sqrt ((81 : ℝ) ^ d)) * B
        ≤ correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh := by
      have hcoef : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt (d : ℝ) *
          (2 * unitDirichletPoincareConst d
            + unitMeanZeroPoincareConst d * Real.sqrt ((81 : ℝ) ^ d)) :=
        mul_nonneg hd0 hbr0
      have h1 := mul_le_mul_of_nonneg_left hBle hcoef
      have hsq : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) :=
        Real.mul_self_sqrt (Nat.cast_nonneg d)
      have heq : (d : ℝ) * Real.sqrt (d : ℝ) *
            (2 * unitDirichletPoincareConst d
              + unitMeanZeroPoincareConst d * Real.sqrt ((81 : ℝ) ^ d)) *
            (Hh * (Real.sqrt (d : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2)))
          = correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh := by
        rw [correctorLegConst]
        linear_combination ((2 * unitDirichletPoincareConst d
          + unitMeanZeroPoincareConst d * Real.sqrt ((81 : ℝ) ^ d)) * Hh *
          (3 : ℝ) ^ ((n : ℝ) / 2) * (d : ℝ)) * hsq
      exact h1.trans heq.le
    exact hstep1.trans hstep2
  -- the competitor
  have hvharmU : Section6Schauder.IsUnitWeaklyHarmonicOn Y v :=
    Section6Schauder.isUnitWeaklyHarmonicOn_iff.2 hvharm
  have hvharmW : Section6Schauder.IsUnitWeaklyHarmonicOn W (v.restrict hWopen hy1) :=
    Section6BoundaryL2.isUnitWeaklyHarmonicOn_restrict hYopen hWopen hy1 hvharmU
  obtain ⟨V, hoddU, hoddL, hharmV, hVmem, hVae⟩ :=
    Section6BoundaryL2.exists_classicalCompetitor_datumSplit_anchor (x := x) (m := (m : ℤ))
      (k := (n : ℤ) - 4) hkm hYopen hy1 hYsub' hdat hvharmW hvu hv₁harm hPsiFun hv₁Psi
  -- the met face, the affine minimizer and the Schauder endpoint
  obtain ⟨i, hmet⟩ :=
    Section6BoundaryL2.exists_meetsFace_of_not_translatedCube_subset hgate
  have hVW : MemLp V 2 (volume.restrict W) := hVmem.restrict W
  have hVR : MemLp V 2 (volume.restrict (Section6Schauder.reflectedWindow x (m : ℤ)
      ((n : ℤ) - 4))) := hVmem.restrict _
  obtain ⟨cV, AV, hminV⟩ :=
    Section6OddClass.exists_isAffineMinimizer_shifted_truncatedWindow hx (by omega) hVW
  obtain ⟨K, hK0, hint, hgradV, hholV, hschauder⟩ :=
    hC0 (m : ℤ) (n : ℤ) x i V cV AV hx (by omega) hmet hoddU hoddL hharmV hVR hminV
  -- the one-step
  have hu_n : MemLp u.toFun 2 (volume.restrict (truncatedCube d (m : ℤ) (n : ℤ) x)) :=
    u.memL2.mono_measure
      (Measure.restrict_mono (truncatedCube_subset_cube d (m : ℤ) (n : ℤ) x) le_rfl)
  have hvW : MemLp v.toFun 2 (volume.restrict W) := (v.restrict hWopen hy1).memL2
  have hschauder0 : K ≤ Csch * ((3 : ℝ) ^ (-(n : ℤ))) ^ (1 / 2 : ℝ) *
      excess ((n : ℤ) - 4) (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x) V + 0 := by
    rw [add_zero]
    exact hschauder
  have hone := Section6BoundaryL2.excess_oneStep_boundary_datumSplit_l2
    (d := d) (m := (m : ℤ)) (n := (n : ℤ)) (k := k) (KhS := 0) (Csch := Csch) (R := R)
    (D := normalizedL2On W (fun p => u.toFun p - v.toFun p))
    hk6 hx (by omega) hK0 hCsch0 hu_n hvW hVW hVae hpriceR hint hgradV hholV
    hschauder0 le_rfl
  rw [mul_zero, add_zero] at hone
  have hKr0 : (0 : ℝ) ≤ oneStepRemainderConst d Csch k :=
    oneStepRemainderConst_nonneg d hCsch0 k
  have hfinal := mul_le_mul_of_nonneg_left hRle hKr0
  linarith only [hone, hfinal]

/-! ### The assembly -/

/-- **The excess-decay estimate of `l.excess.decay.good.scales.GMC` at a
boundary-touching window.**

The conclusion is the frozen conclusion of `l.excess.decay.good.scales.GMC`
verbatim; the binders are the frozen binders plus the negation of the interior
gate of `excess_decay_good_scales_interior`.  The two premises are the byte-exact
conclusions of the two conditional inputs used by the excess-decay argument. -/
theorem excess_decay_good_scales_boundary (d : ℕ)
    (hharm : HarmonicApproximationInput d) (hcap : MathcalECapInput d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1, ∀ k : ℕ, 0 < k →
      ∀ L m n : ℕ, k ≤ n → m ≤ L → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      ¬ translatedCube d ((n : ℤ) - 4) x ⊆ cube d m →
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        indicatorValue (goodEvent M none (n + 2) z epsilon (s / 8))
              (fun _ => excess (n - k) (truncatedCube d m (n - k) x) u.toFun) ω ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) * epsilon) *
                excess n (truncatedCube d m n x) u.toFun +
              C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) *
                section6HomogenizationError M (s / 8) L (n + 2) ω z *
                (Real.sqrt (vecNormSq ell.slope) +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) *
                      Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                  else 0)) +
              C * s ^ (-8 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                (3 : ℝ) ^ (s * n) *
                (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
              (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (3 : ℝ) ^ ((n : ℝ) / 2) *
                  holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
              else 0) := by
  by_cases hd2 : 2 ≤ d
  · have : NeZero d := ⟨by omega⟩
    have hdne : d ≠ 0 := by omega
    obtain ⟨CA, hCApos, hA⟩ := hharm
    obtain ⟨CB, hCBpos, hB⟩ := hcap
    obtain ⟨Csch, hCsch0, hstep⟩ := exists_excess_oneStep_boundary_anchor d hdne
    refine ⟨anchorBoundaryConst d CA CB Csch,
      anchorBoundaryConst_pos d hCApos.le hCBpos.le hCsch0, ?_⟩
    have hC0 : (0 : ℝ) ≤ anchorBoundaryConst d CA CB Csch :=
      anchorBoundaryConst_nonneg d hCApos.le hCBpos.le hCsch0
    have hCcontr : oneStepContractionConst d * Csch ≤ anchorBoundaryConst d CA CB Csch :=
      anchorBoundaryConst_contraction_le d hCApos.le hCBpos.le hCsch0
    have hCrem : (81 * taylorConst d * Csch + 1) *
        (CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
          + correctorLegConst d)
        ≤ anchorBoundaryConst d CA CB Csch := anchorBoundaryConst_remainder_le d hCsch0
    have hCcrude : 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))
        ≤ anchorBoundaryConst d CA CB Csch :=
      anchorBoundaryConst_crude_le d hCApos.le hCBpos.le hCsch0
    set C : ℝ := anchorBoundaryConst d CA CB Csch with hCdef
    intro M s hs epsilon heps k hk L m n hkn hmL hnm x hx z hz hxz hgate ω u h g hsol hgfrac
      hhold ell hell
    -- the standing numerical facts
    have hd1 : 1 ≤ d := by omega
    have hdel : 0 < M.delta := M.shellPrefix.delta_pos
    have hdel2 : (0 : ℝ) < M.delta ^ 2 := pow_pos hdel 2
    have hs0 : 0 < s := lt_of_lt_of_le (mul_pos (by norm_num) hdel2) hs.1
    have hs4 : s ≤ 1 / 4 := hs.2
    have heps0 : 0 ≤ epsilon :=
      le_trans (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.2 hs0.le)) hdel2.le) heps.1
    have heps1 : epsilon ≤ 1 := heps.2
    -- signs of the atoms appearing on the right
    have hMemHW : MemHolder (truncatedCube d m n x) (1 / 2) h.grad :=
      memHolder_mono hhold (truncatedCube_subset_cube d m n x)
    have hEn : 0 ≤ excess (n : ℤ) (truncatedCube d m n x) u.toFun := excess_nonneg _ _ _
    have hErr : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) ω z := ENNReal.toReal_nonneg
    have hTail : 0 ≤ (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ :=
      inv_nonneg.2 (tailAverage_nonneg _ _ _ _ _)
    have hFg : 0 ≤ (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
      ENNReal.toReal_nonneg
    have hSl : 0 ≤ Real.sqrt (vecNormSq ell.slope) := Real.sqrt_nonneg _
    have hAh : 0 ≤ Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad)) :=
      Real.sqrt_nonneg _
    have hHh : 0 ≤ holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad :=
      holderSeminormOn_nonneg hMemHW
    have hpow1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have hpow2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := Real.rpow_nonneg (by norm_num) _
    have hpow3 : (0 : ℝ) ≤ (3 : ℝ) ^ (s * n) := Real.rpow_nonneg (by norm_num) _
    have hpow4 : (0 : ℝ) ≤ (3 : ℝ) ^ ((n : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have hss : (0 : ℝ) ≤ s ^ (-2 : ℝ) := Real.rpow_nonneg hs0.le _
    have hssIn : (0 : ℝ) ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
    have hs15 : (0 : ℝ) ≤ s ^ (-8 : ℝ) := Real.rpow_nonneg hs0.le _
    have hs3 : (0 : ℝ) ≤ s ^ (-7 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
    have hI1 : (0 : ℝ) ≤ (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
        s ^ (-3 / 2 : ℝ) *
          Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad)) else 0) := by
      split_ifs
      · exact mul_nonneg hssIn hAh
      · exact le_rfl
    have hI2 : (0 : ℝ) ≤ (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
        C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * (3 : ℝ) ^ ((n : ℝ) / 2) *
          holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad else 0) := by
      split_ifs
      · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hs3) hpow2) hpow4) hHh
      · exact le_rfl
    have hP : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) * epsilon :=
      mul_nonneg (mul_nonneg hpow2 hss) heps0
    have hT2 : (0 : ℝ) ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) *
        section6HomogenizationError M (s / 8) L (n + 2) ω z *
        (Real.sqrt (vecNormSq ell.slope) +
          (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
            s ^ (-3 / 2 : ℝ) *
              Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
          else 0)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hpow2) hss) hErr) (add_nonneg hSl hI1)
    have hT3 : (0 : ℝ) ≤ C * s ^ (-8 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
        (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ * (3 : ℝ) ^ (s * n) *
        (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hs15) hpow2) hTail) hpow3) hFg
    refine indicatorValue_le ?_ ?_
    · exact add_nonneg (add_nonneg (add_nonneg
        (mul_nonneg (mul_nonneg hC0 (add_nonneg hpow1 hP)) hEn) hT2) hT3) hI2
    intro homega
    have hu_n : MemLp u.toFun 2 (volume.restrict (truncatedCube d m n x)) :=
      u.memL2.mono_measure (Measure.restrict_mono (truncatedCube_subset_cube d m n x) le_rfl)
    -- the boundary case switches both indicators on
    have hBT : BoundaryTouches (truncatedCube d m n x) (cube d m) :=
      boundaryTouches_of_not_translatedCube_subset (j := (n : ℤ) - 4) (l := (n : ℤ))
        hx (by omega) hgate
    by_cases hk6 : 6 ≤ k
    · -- the boundary branch `6 ≤ k`
      obtain ⟨y, hy, hy1, hy2⟩ := exists_windowChoice (m := (m : ℤ)) (n := (n : ℤ)) hx (by omega)
      have hYsub : translatedCube d ((n : ℤ) - 2) y ⊆ cube d (m : ℤ) :=
        hy2.trans (truncatedCube_subset_cube d m ((n : ℤ) - 1) x)
      have hYopen : IsOpen (translatedCube d ((n : ℤ) - 2) y) :=
        Section6Schauder.isOpen_translatedCube d _ y
      -- step `.2`: the harmonic-approximation premise, at the replacement cube
      have hhfrac : MemFractionalOn (cube d m) s h.grad :=
        memFractionalOn_cube_of_memHolder hd1 hs0 hs4 hhold
      obtain ⟨⟨v, hvharm, hvzt⟩, -, hHA⟩ :=
        hA M s hs L m n hmL hnm z hz x hxz ω u h g hsol hgfrac hhfrac y hy hy1 hy2
          (u.restrict hYopen hYsub) (fun _ => rfl) (fun _ => rfl)
      -- the two `H¹₀` data the boundary competitor needs
      have hdat : Homogenization.MemH10 (openCubeSet (originCube d m))
          (fun p => u.toFun p - h.toFun p) := by
        obtain ⟨w, hval, -⟩ := hsol.1
        refine ⟨w, funext fun p => ?_⟩
        show w.toH1Function.toFun p = u.toFun p - h.toFun p
        rw [hval p]
        ring
      have hvu : Homogenization.MemH10 (translatedCube d ((n : ℤ) - 2) y)
          (fun p => v.toFun p - u.toFun p) := by
        obtain ⟨w, hval, -⟩ := hvzt
        refine ⟨w, funext fun p => ?_⟩
        show w.toH1Function.toFun p = v.toFun p - u.toFun p
        rw [hval p]
        show w.toH1Function.toFun p = u.toFun p + w.toH1Function.toFun p - u.toFun p
        ring
      -- steps `.3`/`.4`/`.5`: the boundary one-step
      have hone := hstep m n k hk6 hnm x y hx hy1 hy2 hgate u h hdat hMemHW v hvharm hvu
      -- step `.2` continued: the harmonic-approximation bound on the good event
      have homega1 : ω ∈ goodEvent M none (n + 2) z 1 (s / 8) :=
        goodEvent_mono heps0 heps1 homega
      have hD := hHA v hvharm hvzt
      rw [indicatorValue_of_mem homega1] at hD
      -- step `.7`: the `𝓔`-cap, transported to the translate `z`
      have hcapz : section6HomogenizationError M (s / 8) L (n + 2) ω z ≤ CB * epsilon := by
        refine Section6Covariance.section6HomogenizationError_le_of_translate_zero ?_ z homega
        intro ν hν
        refine hB M (s / 8) ⟨by linarith [hs.1], by linarith⟩ L (n + 2) (by omega) ν epsilon
          ⟨?_, heps1⟩ hν
        have hrw : (s / 8)⁻¹ * M.delta ^ 2 = 8 * s⁻¹ * M.delta ^ 2 := by
          field_simp
        rw [hrw]
        exact heps.1
      -- step `.6`: the slope split of the normalized oscillation
      have hstep6 := normalizedL2On_sub_average_le (m := (m : ℤ)) (n := (n : ℤ)) (x := x)
        hx (by omega) hu_n hell
      
      have hstep8 := holderLeg_le (m := (m : ℤ)) (j := (n : ℤ)) (x := x) (f := h.grad)
        (s := s) hd1 hx hs0 hs4 hMemHW
      -- notation for the atoms of the display
      set E := excess (n : ℤ) (truncatedCube d m n x) u.toFun with hEdef
      set Err := section6HomogenizationError M (s / 8) L (n + 2) ω z with hErrdef
      set Sl := Real.sqrt (vecNormSq ell.slope) with hSldef
      set Ah := Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad)) with hAhdef
      set Fg := (fractionalSeminormOn (truncatedCube d m n x) s g).toReal with hFgdef
      set Fh := (fractionalSeminormOn (truncatedCube d m n x) s h.grad).toReal with hFhdef
      set Hhv := holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad with hHhdef
      set Tinv := (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ with hTinvdef
      set Dv := normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
        (fun q => u.toFun q - v.toFun q) with hDdef
      set N := normalizedL2On (truncatedCube d m n x)
        (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) with hNdef
      -- the remainder constant is bounded by the printed `3^{(1+d/2)k}`
      have hKr0 : (0 : ℝ) ≤ oneStepRemainderConst d Csch k :=
        oneStepRemainderConst_nonneg d hCsch0 k
      have hb0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := hpow2
      have hb1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        have h0 : (3 : ℝ) ^ (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          positivity
        simpa using h0
      have h81 : (0 : ℝ) ≤ 81 * taylorConst d * Csch :=
        mul_nonneg (mul_nonneg (by norm_num) (taylorConst_nonneg d)) hCsch0
      have hCrm0 : (0 : ℝ) ≤ 81 * taylorConst d * Csch + 1 := by linarith only [h81]
      have hKrb : oneStepRemainderConst d Csch k
          ≤ (81 * taylorConst d * Csch + 1) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        have hleft : 81 * taylorConst d * Csch * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
            ≤ 81 * taylorConst d * Csch * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
          mul_le_mul_of_nonneg_left (le_trans three_zpow_rpow_half_le_one hb1) h81
        have hright : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d)
            ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
          have ht0 : (0 : ℝ) < (3 : ℝ) ^ ((k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
          have htz : (3 : ℝ) ^ ((k : ℤ)) = (3 : ℝ) ^ ((k : ℝ)) := by
            rw [← Real.rpow_intCast (3 : ℝ) ((k : ℤ))]
            norm_num
          have hsq : Real.sqrt (((3 : ℝ) ^ ((k : ℝ))) ^ d) = ((3 : ℝ) ^ ((k : ℝ))) ^ ((d : ℝ) / 2) :=
            sqrt_pow_eq_rpow_half ht0.le d
          have hmono : Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d)
              ≤ Real.sqrt (((3 : ℝ) ^ ((k : ℝ))) ^ d) := by
            refine Real.sqrt_le_sqrt ?_
            rw [← htz]
            exact pow_le_pow_left₀ (zpow_nonneg (by norm_num) _)
              (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
          have hsplit : (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
              = (3 : ℝ) ^ ((k : ℝ)) * ((3 : ℝ) ^ ((k : ℝ))) ^ ((d : ℝ) / 2) :=
            three_rpow_one_add_mul (k : ℝ) ((d : ℝ) / 2)
          rw [hsplit, htz]
          exact mul_le_mul_of_nonneg_left (le_trans hmono (le_of_eq hsq)) ht0.le
        rw [oneStepRemainderConst]
        linarith only [hleft, hright]
      -- the coefficient budgets
      have hCH0 : (0 : ℝ) ≤ fractionalHolderConst d := fractionalHolderConst_nonneg d
      have hsd0 : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
      have hcorr0 : (0 : ℝ) ≤ correctorLegConst d := correctorLegConst_nonneg d
      have hbudget : ∀ c : ℝ, 0 ≤ c →
          CA * c ≤ CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
            + correctorLegConst d →
          oneStepRemainderConst d Csch k * CA * c
            ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        intro c hc0 hcle
        have hassoc : oneStepRemainderConst d Csch k * CA * c
            = oneStepRemainderConst d Csch k * (CA * c) := by ring
        rw [hassoc]
        have hCAc0 : (0 : ℝ) ≤ CA * c := mul_nonneg hCApos.le hc0
        have h1 : oneStepRemainderConst d Csch k * (CA * c)
            ≤ ((81 * taylorConst d * Csch + 1) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) * (CA * c) :=
          mul_le_mul_of_nonneg_right hKrb hCAc0
        have h2 : ((81 * taylorConst d * Csch + 1) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) * (CA * c)
            = ((81 * taylorConst d * Csch + 1) * (CA * c)) *
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by ring
        have h3 : (81 * taylorConst d * Csch + 1) * (CA * c)
            ≤ (81 * taylorConst d * Csch + 1) *
              (CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
                + correctorLegConst d) :=
          mul_le_mul_of_nonneg_left hcle hCrm0
        have h4 : ((81 * taylorConst d * Csch + 1) * (CA * c)) *
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
            ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
          mul_le_mul_of_nonneg_right (le_trans h3 hCrem) hb0
        linarith only [h1, h2.le, h2.ge, h4]
      have hbrk : ∀ c : ℝ, c ≤ CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d →
          CA * c ≤ CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
            + correctorLegConst d := by
        intro c hcle
        have h1 : CA * c ≤ CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d) :=
          mul_le_mul_of_nonneg_left hcle hCApos.le
        linarith only [h1, hcorr0]
      have hbCB := hbudget CB hCBpos.le (hbrk CB (by linarith only [hCH0, hsd0]))
      have hbOne := hbudget 1 zero_le_one (hbrk 1 (by linarith only [hCH0, hsd0, hCBpos.le]))
      have hbSqrt := hbudget (Real.sqrt (d : ℝ) / 2) (by linarith only [hsd0])
        (hbrk (Real.sqrt (d : ℝ) / 2) (by linarith only [hCH0, hsd0, hCBpos.le]))
      have hb3 : oneStepRemainderConst d Csch k * CA
          ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        have := hbOne
        rw [mul_one] at this
        exact this
      -- the joint budget of the two Hölder legs of the fourth line
      have hbHolder : oneStepRemainderConst d Csch k *
            (CA * fractionalHolderConst d + correctorLegConst d)
          ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        have hnn : (0 : ℝ) ≤ CA * fractionalHolderConst d + correctorLegConst d := by
          have h0 : (0 : ℝ) ≤ CA * fractionalHolderConst d := mul_nonneg hCApos.le hCH0
          linarith only [h0, hcorr0]
        have h1 : oneStepRemainderConst d Csch k *
              (CA * fractionalHolderConst d + correctorLegConst d)
            ≤ ((81 * taylorConst d * Csch + 1) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) *
              (CA * fractionalHolderConst d + correctorLegConst d) :=
          mul_le_mul_of_nonneg_right hKrb hnn
        have h2 : ((81 * taylorConst d * Csch + 1) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) *
              (CA * fractionalHolderConst d + correctorLegConst d)
            = ((81 * taylorConst d * Csch + 1) *
                (CA * fractionalHolderConst d + correctorLegConst d)) *
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by ring
        have h3 : (81 * taylorConst d * Csch + 1) *
              (CA * fractionalHolderConst d + correctorLegConst d)
            ≤ (81 * taylorConst d * Csch + 1) *
              (CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
                + correctorLegConst d) := by
          refine mul_le_mul_of_nonneg_left ?_ hCrm0
          have hexpb : CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
              = CA * (CB + 1 + Real.sqrt (d : ℝ) / 2) + CA * fractionalHolderConst d := by ring
          have hnn2 : (0 : ℝ) ≤ CA * (CB + 1 + Real.sqrt (d : ℝ) / 2) :=
            mul_nonneg hCApos.le (by linarith only [hCBpos.le, hsd0])
          linarith only [hexpb.le, hexpb.ge, hnn2]
        have h4 : ((81 * taylorConst d * Csch + 1) *
                (CA * fractionalHolderConst d + correctorLegConst d)) *
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
            ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
          mul_le_mul_of_nonneg_right (le_trans h3 hCrem) hb0
        linarith only [h1, h2.le, h2.ge, h4]
      -- step `.8` in the `ℕ`-cast shape of the harmonic-approximation input
      simp only [Int.cast_natCast] at hstep8
      -- the `3^{-n}` weight, distributed over the harmonic-approximation bound
      have h3n : (0 : ℝ) < (3 : ℝ) ^ (-(n : ℤ)) := zpow_pos (by norm_num) _
      have h3nn : (3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ (n : ℕ) = 1 := by
        rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity)]
      have hJeq : (3 : ℝ) ^ (-(n : ℤ)) *
            (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah else 0)
          = (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              s ^ (-3 / 2 : ℝ) * Ah else 0) := by
        rw [ite_eq_left hBT, ite_eq_left hBT]
        calc (3 : ℝ) ^ (-(n : ℤ)) * (s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ (n : ℕ) * Ah)
            = ((3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ (n : ℕ)) * (s ^ (-3 / 2 : ℝ) * Ah) := by ring
          _ = s ^ (-3 / 2 : ℝ) * Ah := by rw [h3nn, one_mul]
      have hfront : (3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ ((1 + s) * (n : ℝ))
          = (3 : ℝ) ^ (s * (n : ℝ)) := by
        rw [← Real.rpow_intCast (3 : ℝ) (-(n : ℤ)), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        push_cast
        ring
      have hXHle : (3 : ℝ) ^ (-(n : ℤ)) *
            (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              CA * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0)
          ≤ (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
             else 0) := by
        rw [ite_eq_left hBT, ite_eq_left hBT]
        have hre : (3 : ℝ) ^ (-(n : ℤ)) *
              (CA * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh)
            = CA * (s ^ (-4 : ℝ) * ((3 : ℝ) ^ (-(n : ℤ)) *
                ((3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh))) := by ring
        rw [hre]
        exact mul_le_mul_of_nonneg_left hstep8 hCApos.le
      have hCAErr : (0 : ℝ) ≤ CA * s ^ (-2 : ℝ) * Err :=
        mul_nonneg (mul_nonneg hCApos.le hss) hErr
      have hNterm : CA * s ^ (-2 : ℝ) * Err * ((3 : ℝ) ^ (-(n : ℤ)) * N)
          ≤ CA * s ^ (-2 : ℝ) * Err * E +
            CA * s ^ (-2 : ℝ) * Err * (Real.sqrt (d : ℝ) / 2 * Sl) := by
        have hstepN := mul_le_mul_of_nonneg_left hstep6 hCAErr
        linarith only [hstepN]
      have hDsD : (3 : ℝ) ^ (-(n : ℤ)) * Dv
          ≤ CA * s ^ (-2 : ℝ) * Err * E
            + CA * s ^ (-2 : ℝ) * Err * (Real.sqrt (d : ℝ) / 2 * Sl)
            + CA * s ^ (-2 : ℝ) * Err *
                (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                  s ^ (-3 / 2 : ℝ) * Ah else 0)
            + CA * s ^ (-8 : ℝ) * Tinv * (3 : ℝ) ^ (s * (n : ℝ)) * Fg
            + (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
               else 0) := by
        have hbase := mul_le_mul_of_nonneg_left hD h3n.le
        have hexp : (3 : ℝ) ^ (-(n : ℤ)) *
              (CA * s ^ (-2 : ℝ) * Err *
                  (N + (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah else 0)) +
                CA * s ^ (-8 : ℝ) * Tinv * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fg +
                (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                  CA * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0))
            = CA * s ^ (-2 : ℝ) * Err * ((3 : ℝ) ^ (-(n : ℤ)) * N)
              + CA * s ^ (-2 : ℝ) * Err * ((3 : ℝ) ^ (-(n : ℤ)) *
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah else 0))
              + CA * s ^ (-8 : ℝ) * Tinv *
                  ((3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ ((1 + s) * (n : ℝ))) * Fg
              + (3 : ℝ) ^ (-(n : ℤ)) *
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    CA * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0) := by
          ring
        rw [hexp, hJeq, hfront] at hbase
        linarith only [hbase, hNterm, hXHle]
      -- the corrector leg joins the fourth line
      set XH : ℝ := (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
          CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
         else 0) + correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv with hXHdef
      set Ds : ℝ := (3 : ℝ) ^ (-(n : ℤ)) * Dv
          + correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv with hDsdef
      have hone' : excess ((n : ℤ) - (k : ℤ))
            (truncatedCube d m ((n : ℤ) - (k : ℤ)) x) u.toFun
          ≤ oneStepContractionConst d * Csch * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * E
            + oneStepRemainderConst d Csch k * Ds := by
        have hexp : oneStepRemainderConst d Csch k * Ds
            = oneStepRemainderConst d Csch k * ((3 : ℝ) ^ (-(n : ℤ)) * Dv)
              + oneStepRemainderConst d Csch k *
                (correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) := by
          rw [hDsdef]; ring
        linarith only [hone, hexp.le, hexp.ge]
      have hDs : Ds ≤ CA * s ^ (-2 : ℝ) * Err * E
            + CA * s ^ (-2 : ℝ) * Err * (Real.sqrt (d : ℝ) / 2 * Sl)
            + CA * s ^ (-2 : ℝ) * Err *
                (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                  s ^ (-3 / 2 : ℝ) * Ah else 0)
            + CA * s ^ (-8 : ℝ) * Tinv * (3 : ℝ) ^ (s * (n : ℝ)) * Fg + XH := by
        rw [hDsdef, hXHdef]
        linarith only [hDsD]
      have hKcle : oneStepContractionConst d * Csch * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
          ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
        have hpe : ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) = (3 : ℝ) ^ (-(k : ℝ) / 2) := by
          rw [three_zpow_rpow_half_eq]
          push_cast
          ring_nf
        rw [hpe]
        exact mul_le_mul_of_nonneg_right hCcontr hpow1
      have hs3one : (1 : ℝ) ≤ s ^ (-7 / 2 : ℝ) := by
        have h := Real.rpow_le_rpow_of_exponent_ge hs0
          (by linarith only [hs4]) (show (-7 / 2 : ℝ) ≤ 0 by norm_num)
        simpa using h
      have hXHfin : oneStepRemainderConst d Csch k * XH
          ≤ (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv
             else 0) := by
        rw [hXHdef, ite_eq_left hBT, ite_eq_left hBT]
        have hbase : (0 : ℝ) ≤ s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) :=
          mul_nonneg hs3 (mul_nonneg hpow4 hHh)
        have hsecond : correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv
            ≤ correctorLegConst d * (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)) := by
          have hph : (0 : ℝ) ≤ (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv := mul_nonneg hpow4 hHh
          have h1 : (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv
              ≤ s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) := by
            have := mul_le_mul_of_nonneg_right hs3one hph
            linarith only [this]
          have h2 := mul_le_mul_of_nonneg_left h1 hcorr0
          linarith only [h2]
        have hrewrite : oneStepRemainderConst d Csch k *
              (CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
                + correctorLegConst d * (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)))
            = (oneStepRemainderConst d Csch k *
                (CA * fractionalHolderConst d + correctorLegConst d)) *
              (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)) := by ring
        have hmid : (oneStepRemainderConst d Csch k *
              (CA * fractionalHolderConst d + correctorLegConst d)) *
            (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv))
            ≤ (C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) *
              (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)) :=
          mul_le_mul_of_nonneg_right hbHolder hbase
        have hfin : (C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) *
              (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv))
            = C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
              (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv := by ring
        have hleg := mul_le_mul_of_nonneg_left hsecond hKr0
        have hsum : oneStepRemainderConst d Csch k *
              (CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
                + correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
            ≤ oneStepRemainderConst d Csch k *
              (CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
                + correctorLegConst d * (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv))) := by
          have hd1' : oneStepRemainderConst d Csch k *
                (CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
                  + correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
              = oneStepRemainderConst d Csch k *
                  (CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) *
                    (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv))
                + oneStepRemainderConst d Csch k *
                  (correctorLegConst d * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv) := by ring
          have hd2' : oneStepRemainderConst d Csch k *
                (CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)
                  + correctorLegConst d * (s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv)))
              = oneStepRemainderConst d Csch k *
                  (CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) *
                    (3 : ℝ) ^ ((n : ℝ) / 2) * Hhv))
                + oneStepRemainderConst d Csch k *
                  (correctorLegConst d * (s ^ (-7 / 2 : ℝ) *
                    ((3 : ℝ) ^ ((n : ℝ) / 2) * Hhv))) := by ring
          linarith only [hleg, hd1'.le, hd1'.ge, hd2'.le, hd2'.ge]
        linarith only [hsum, hrewrite.le, hrewrite.ge, hmid, hfin.le, hfin.ge]
      exact excessDecayCombine hEn hErr hSl hFg hTail hI1 heps0 hss hs15 hpow3 hKr0 hCApos.le
        hone' hDs hcapz hKcle hbCB hbSqrt hb3 hXHfin
    -- the crude branch `k < 6`: no harmonic input at all
    have hcrude := excess_truncatedCube_le (m := (m : ℤ)) (j := (n : ℤ) - (k : ℤ))
      (l := (n : ℤ)) (x := x) hx (by omega) (by omega) (by omega) hu_n
    rw [show (n : ℤ) - ((n : ℤ) - (k : ℤ)) = (k : ℤ) by ring] at hcrude
    have hcoef : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d)
        ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
      have hA1 : (3 : ℝ) ^ ((k : ℤ)) ≤ 243 := by
        calc (3 : ℝ) ^ ((k : ℤ)) ≤ (3 : ℝ) ^ (5 : ℤ) :=
              zpow_le_zpow_right₀ (by norm_num) (by omega)
          _ = 243 := by norm_num
      have hA2 : Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) ≤ Real.sqrt ((3 : ℝ) ^ (7 * d)) := by
        refine Real.sqrt_le_sqrt ?_
        calc ((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d ≤ ((3 : ℝ) ^ (7 : ℤ)) ^ d :=
              pow_le_pow_left₀ (zpow_nonneg (by norm_num) _)
                (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
          _ = (3 : ℝ) ^ (7 * d) := by
              rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast, ← pow_mul]
      have hA3 : (3 : ℝ) ^ (-(3 : ℝ)) ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hkr : (k : ℝ) ≤ 5 := by exact_mod_cast (by omega : k ≤ 5)
        linarith
      have hA4 : (3 : ℝ) ^ (-(3 : ℝ)) = 1 / 27 := by
        rw [show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        norm_num
      have hsq0 : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ (7 * d)) := Real.sqrt_nonneg _
      have hsq1 : (0 : ℝ) ≤ Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) := Real.sqrt_nonneg _
      have hleft : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d)
          ≤ 243 * Real.sqrt ((3 : ℝ) ^ (7 * d)) :=
        mul_le_mul hA1 hA2 hsq1 (by norm_num)
      have hmid : (243 : ℝ) * Real.sqrt ((3 : ℝ) ^ (7 * d))
          = (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) * ((1 : ℝ) / 27) := by
        rw [show ((3 : ℝ) ^ (8 : ℕ)) = 6561 by norm_num]; ring
      have hright : (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) * ((1 : ℝ) / 27)
          ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
        rw [← hA4]
        refine mul_le_mul hCcrude hA3 (by rw [hA4]; norm_num) hC0
      linarith only [hleft, hmid, hright]
    have hstepc : excess ((n : ℤ) - (k : ℤ)) (truncatedCube d m (n - k) x) u.toFun
        ≤ C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) * epsilon) *
            excess (n : ℤ) (truncatedCube d m n x) u.toFun := by
      have h1 : excess ((n : ℤ) - (k : ℤ)) (truncatedCube d m (n - k) x) u.toFun
          ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) * excess (n : ℤ) (truncatedCube d m n x) u.toFun :=
        le_trans hcrude (mul_le_mul_of_nonneg_right hcoef hEn)
      have h2 : C * (3 : ℝ) ^ (-(k : ℝ) / 2) ≤ C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) * epsilon) :=
        mul_le_mul_of_nonneg_left (by linarith only [hP]) hC0
      exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hEn)
    exact le_trans (le_trans (le_trans hstepc (le_add_of_nonneg_right hT2))
      (le_add_of_nonneg_right hT3)) (le_add_of_nonneg_right hI2)
  · exact ⟨1, one_pos, fun M => absurd M.shellPrefix.dimension hd2⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
