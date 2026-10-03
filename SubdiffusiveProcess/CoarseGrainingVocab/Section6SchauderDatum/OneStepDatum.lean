module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.DatumSplit
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.OneStep

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/ExcessDecay/OneStepBoundaryHonest.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/OneStepBoundaryHonest.lean

@[expose] public section

/-!
# The boundary one-step contraction at the datum-split competitor

`Section6ExcessDecay.excess_oneStep_of_schauder` is the deterministic one-step
contraction; its Schauder slot is discharged in the flat-face regime by
`Section6Schauder.exists_gradientHolder_boundary_odd_truncatedCube`, but only for
a competitor that is **odd** about the met face — which, applied to the harmonic
replacement `v` itself, forces `v` to vanish on the met portion of `∂□_m` and so
is the `[∇h] = 0` specialization.

This module asks the odd binders of the manuscript's **shifted** competitor

```text
  V_odd = v − ℓ_h − v₁
```

— the object whose zero trace on the met faces `ZeroTrace` produces and whose
`H¹` odd extension `OddPackaging` packages — while the `L̲²` comparison binder
stays on `u − v`, the anchor's own object.  The datum then enters the conclusion
through the corrector's `L^∞` scale `datumResidualBound d (n-2) [∇h]`, at the
printed `K_h ≍ (3^{n-k})^{1/2} [∇h]_{C^{0,1/2}(U_{m,n-4})}`.

## What is *not* claimed

No boundary Schauder estimate for `∇v` itself is proved or assumed: the
`C^{1,1/2}` data lives on `V_odd`, and `v₁` is never differentiated.  This is the
honest reading ("subtract a controlled extension first"); the manuscript's
printed sentence
`[∇v]_{C^{0,1/2}(U_{m,n-5})} ≤ C 3^{-n/2} E(v,U_{m,n-4}) + C[∇h]` is *reproduced
at the level of the excess conclusion*, not re-derived as a gradient-seminorm
statement.

## The two atoms

* **the excess is affine-shift free** (`excess_sub_affineLift`), so replacing `u`
  by `u − ℓ_h` costs nothing on either side of the one-step display;
* **the corrector's `L^∞` bound is an `L̲²` bound**
  (`normalizedL2On_le_of_ae_abs_le`), and the propagation of that bound through
  the remainder weight `oneStepRemainderConst d C k · 3^{-n}` is an **exact
  identity** (`oneStepRemainder_mul_datumResidual`), not an estimate.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum

open MeasureTheory
open Homogenization (Vec volumeAverage)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ### The excess is free under an affine shift -/

/-- **The competitor set is unchanged by an affine shift.**  Subtracting a fixed
affine function permutes the affine competitors, so it moves no distance. -/
theorem affineDistSet_sub_affineEval (W : Set (Vec d)) (u : Vec d → ℝ) (c : ℝ)
    (g : Vec d) :
    affineDistSet W (fun y => u y - affineEval c g y) = affineDistSet W u := by
  ext r
  constructor
  · rintro ⟨⟨c', g'⟩, rfl⟩
    refine ⟨(c + c', g + g'), ?_⟩
    show affineDistOn W u (c + c') (g + g')
      = affineDistOn W (fun y => u y - affineEval c g y) c' g'
    simp only [affineDistOn]
    congr 1
    funext y
    have h : affineEval (c + c') (g + g') y
        = affineEval c g y + affineEval c' g' y := by
      have h1 : affineEval (c + c') (g + g') y - affineEval c g y
          = affineEval (c + c' - c) (g + g' - g) y := affineEval_sub _ _ _ _ _
      have h2 : c + c' - c = c' := by ring
      have h3 : g + g' - g = g' := by abel
      rw [h2, h3] at h1
      linarith only [h1]
    rw [h]
    ring
  · rintro ⟨⟨c', g'⟩, rfl⟩
    refine ⟨(c' - c, g' - g), ?_⟩
    show affineDistOn W (fun y => u y - affineEval c g y) (c' - c) (g' - g)
      = affineDistOn W u c' g'
    simp only [affineDistOn]
    congr 1
    funext y
    have h : affineEval (c' - c) (g' - g) y
        = affineEval c' g' y - affineEval c g y := (affineEval_sub _ _ _ _ _).symm
    rw [h]
    ring

theorem affineExcessRaw_sub_affineEval (W : Set (Vec d)) (u : Vec d → ℝ) (c : ℝ)
    (g : Vec d) :
    affineExcessRaw W (fun y => u y - affineEval c g y) = affineExcessRaw W u := by
  rw [affineExcessRaw, affineExcessRaw, affineDistSet_sub_affineEval]

/-- **The affine shift is excess-free** for the scale-normalized excess. -/
theorem excess_sub_affineEval (j : ℤ) (W : Set (Vec d)) (u : Vec d → ℝ) (c : ℝ)
    (g : Vec d) :
    excess j W (fun y => u y - affineEval c g y) = excess j W u := by
  rw [excess_eq_affineExcessScaled, excess_eq_affineExcessScaled, affineExcessScaled,
    affineExcessScaled, affineExcessRaw_sub_affineEval]

/-- **`E(u − ℓ_h, W) = E(u, W)`**: the datum's affine part is invisible to the
excess. -/
theorem excess_sub_affineLift (j : ℤ) (W : Set (Vec d)) (x : Vec d) (c : ℝ)
    (A : Vec d) (u : Vec d → ℝ) :
    excess j W (fun y => u y - affineLift x c A y) = excess j W u := by
  have h : (fun y => u y - affineLift x c A y)
      = fun y => u y - affineEval (c - Homogenization.vecDot A x) A y := by
    funext y
    rw [affineLift_eq_affineEval]
  rw [h, excess_sub_affineEval]

/-! ### The `L̲²` price of an almost-everywhere bounded corrector -/

/-- `‖·‖_{L̲²(W)}` only sees the a.e. class on `W`. -/
theorem normalizedL2On_congr_ae {W : Set (Vec d)} {f g : Vec d → ℝ}
    (h : f =ᵐ[volume.restrict W] g) : normalizedL2On W f = normalizedL2On W g := by
  have hsq : (fun y => f y ^ 2) =ᵐ[volume.restrict W] fun y => g y ^ 2 := by
    filter_upwards [h] with y hy
    rw [hy]
  show Real.sqrt (volumeAverage W fun y => f y ^ 2)
    = Real.sqrt (volumeAverage W fun y => g y ^ 2)
  unfold volumeAverage
  rw [integral_congr_ae hsq]

/-- **`L^∞ → L̲²` at an almost-everywhere bound.**  The corrector's bound is
delivered a.e. by `DatumSplit.exists_datumCorrector`, so the pointwise version of
this step is not available. -/
theorem normalizedL2On_le_of_ae_abs_le {W : Set (Vec d)}
    (hWpos : 0 < (volume W).toReal) (hWtop : volume W ≠ ⊤) {f : Vec d → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hf : MemLp f 2 (volume.restrict W))
    (hbd : ∀ᵐ y ∂(volume.restrict W), |f y| ≤ R) :
    normalizedL2On W f ≤ R := by
  refine normalizedL2On_le_of_sq_le hR ?_
  have hint1 : IntegrableOn (fun y => f y ^ 2) W volume := hf.integrable_sq
  have hint2 : IntegrableOn (fun _ : Vec d => R ^ 2) W volume := integrableOn_const hWtop
  have hle : (∫ y in W, f y ^ 2) ≤ ∫ _y in W, R ^ 2 := by
    refine setIntegral_mono_ae_restrict hint1 hint2 ?_
    filter_upwards [hbd] with y hy
    obtain ⟨hl, hr⟩ := abs_le.1 hy
    exact sq_le_sq' hl hr
  have hconst : (∫ _y in W, R ^ 2) = (volume W).toReal * R ^ 2 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul]
  rw [hconst] at hle
  show (volume W).toReal⁻¹ * ∫ y in W, f y ^ 2 ≤ R ^ 2
  have hmul := mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hWpos.le)
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hWpos), one_mul] at hmul
  exact hmul

/-! ### The datum leg's constant, and the exact propagation identity -/

/-- **The constant of the boundary datum leg.**  The corrector's `L̲²` price,
carried at the one-step remainder weight `oneStepRemainderConst d C k · 3^{-n}`,
appears in the conclusion against the printed weight `(3^{n-k})^{1/2}`; this is
the constant that remains. -/
def boundaryDatumLegConst (d : ℕ) (Csch : ℝ) (k : ℕ) : ℝ :=
  oneStepRemainderConst d Csch k * (2 * (d : ℝ) * Real.sqrt (d : ℝ) / 243)
    * (2 : ℝ) ^ (-(3 / 2) : ℝ) * ((3 : ℝ) ^ ((k : ℤ) - 2)) ^ (1 / 2 : ℝ)

theorem boundaryDatumLegConst_nonneg (d : ℕ) {Csch : ℝ} (hCsch : 0 ≤ Csch) (k : ℕ) :
    0 ≤ boundaryDatumLegConst d Csch k := by
  have h1 : (0 : ℝ) ≤ oneStepRemainderConst d Csch k :=
    oneStepRemainderConst_nonneg d hCsch k
  have h2 : (0 : ℝ) ≤ ((3 : ℝ) ^ ((k : ℤ) - 2)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (zpow_pos (by norm_num) _).le _
  have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h4 : (0 : ℝ) ≤ 2 * (d : ℝ) * Real.sqrt (d : ℝ) / 243 := by positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h4) h3) h2

/-- **The propagation is exact.**  The corrector's `L̲²` price, carried at the
one-step remainder weight, *is* the printed `K_h` leg
`boundaryDatumLegConst d C k · (3^{n-k})^{1/2} · [∇h]`.  No inequality, no
slack. -/
theorem oneStepRemainder_mul_datumResidual (d : ℕ) (Csch : ℝ) (k : ℕ) (n : ℤ)
    (Kh : ℝ) :
    oneStepRemainderConst d Csch k * ((3 : ℝ) ^ (-n) * datumResidualBound d (n - 2) Kh)
      = boundaryDatumLegConst d Csch k * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) * Kh := by
  have h3ne : (3 : ℝ) ≠ 0 := by norm_num
  have hshift : (3 : ℝ) ^ (-n) = (1 / 9 : ℝ) * (3 : ℝ) ^ (-(n - 2)) := by
    rw [show -(n - 2) = -n + 2 by ring, zpow_add₀ h3ne]
    have h9 : (3 : ℝ) ^ (2 : ℤ) = 9 := by norm_num
    rw [h9]
    ring
  have hbase := datumResidualBound_zpow_mul d (n - 2) Kh
  have hsplit : ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
        * ((3 : ℝ) ^ ((k : ℤ) - 2)) ^ (1 / 2 : ℝ)
      = ((3 : ℝ) ^ (n - 2)) ^ (1 / 2 : ℝ) := by
    rw [← Real.mul_rpow (zpow_pos (by norm_num) _).le (zpow_pos (by norm_num) _).le,
      ← zpow_add₀ h3ne, show n - (k : ℤ) + ((k : ℤ) - 2) = n - 2 by ring]
  have h27 : (3 : ℝ) ^ (-3 : ℝ) = 1 / 27 := by
    rw [show (-3 : ℝ) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  calc oneStepRemainderConst d Csch k
        * ((3 : ℝ) ^ (-n) * datumResidualBound d (n - 2) Kh)
      = oneStepRemainderConst d Csch k
          * ((1 / 9 : ℝ) * ((3 : ℝ) ^ (-(n - 2)) * datumResidualBound d (n - 2) Kh)) := by
        rw [hshift]; ring
    _ = oneStepRemainderConst d Csch k
          * ((1 / 9 : ℝ) * (2 * (d : ℝ) * (Kh * Real.sqrt (d : ℝ))
              * ((3 : ℝ) ^ (-3 : ℝ) * (2 : ℝ) ^ (-(3 / 2) : ℝ))
              * ((3 : ℝ) ^ (n - 2)) ^ (1 / 2 : ℝ))) := by rw [hbase]
    _ = oneStepRemainderConst d Csch k * (2 * (d : ℝ) * Real.sqrt (d : ℝ) / 243)
          * (2 : ℝ) ^ (-(3 / 2) : ℝ)
          * (((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ)
              * ((3 : ℝ) ^ ((k : ℤ) - 2)) ^ (1 / 2 : ℝ)) * Kh := by
        rw [hsplit, h27]; ring
    _ = boundaryDatumLegConst d Csch k * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) * Kh := by
        rw [boundaryDatumLegConst]; ring

/-! ### The boundary one-step contraction at the shifted competitor -/

/-- **The one-step excess contraction at the manuscript competitor
`V_odd = v − ℓ_h − v₁`, with the printed `[∇h]` leg.**

The `C^{1,1/2}` data is asked of `V` on `U_{m,n-5}(x)`, the `L̲²` comparison of
`u − v` on `U_{m,n-4}(x)`, and the corrector `v₁` only through its `L^∞` bound
`datumResidualBound d (n-2) K_h` — which
`DatumSplit.exists_datumCorrector` produces from
`K_h = [∇h]_{C^{0,1/2}(U_{m,n-4}(x))}`.  The conclusion is
`Section6ExcessDecay.excess_oneStep_of_schauder`'s display, with the fourth leg
`boundaryDatumLegConst d C k · (3^{n-k})^{1/2} · [∇h]`.

No probability, no good event: this is the deterministic boundary branch. -/
theorem excess_oneStep_boundary_datumSplit {m n : ℤ} {k : ℕ} (hk : 6 ≤ k) {x : Vec d}
    (hx : x ∈ cube d m) (hnm : n - 1 ≤ m)
    {u v v₁ V : Vec d → ℝ} {cl : ℝ} {Al : Vec d} {Gv : Vec d → Vec d}
    {K Kh KhS Csch D : ℝ} (hKh : 0 ≤ Kh) (hK : 0 ≤ K) (hCsch : 0 ≤ Csch)
    (hu : MemLp u 2 (volume.restrict (truncatedCube d m n x)))
    (hv : MemLp v 2 (volume.restrict (truncatedCube d m (n - 4) x)))
    (hV : MemLp V 2 (volume.restrict (truncatedCube d m (n - 4) x)))
    (hVae : V =ᵐ[volume.restrict (truncatedCube d m (n - 4) x)]
      (fun y => v y - affineLift x cl Al y - v₁ y))
    (hv₁ : ∀ᵐ y ∂(volume.restrict (truncatedCube d m (n - 4) x)),
      |v₁ y| ≤ datumResidualBound d (n - 2) Kh)
    (hint : ∀ i, IntegrableOn (fun p => Gv p i) (truncatedCube d m (n - 5) x) volume)
    (hgrad : HasGradientOn (truncatedCube d m (n - 5) x) V Gv)
    (hhol : HolderSeminormBoundOn (truncatedCube d m (n - 5) x) (1 / 2 : ℝ) K Gv)
    (hschauder : K ≤ Csch * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) *
      excess (n - 4) (truncatedCube d m (n - 4) x) V + KhS)
    (hD : normalizedL2On (truncatedCube d m (n - 4) x) (fun y => u y - v y) ≤ D) :
    excess (n - (k : ℤ)) (truncatedCube d m (n - (k : ℤ)) x) u
      ≤ oneStepContractionConst d * Csch * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
            excess n (truncatedCube d m n x) u
        + oneStepRemainderConst d Csch k * ((3 : ℝ) ^ (-n) * D)
        + taylorConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) * KhS
        + boundaryDatumLegConst d Csch k * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) * Kh := by
  have h4n : n - 4 ≤ n := by omega
  have hm4 : n - 4 - 1 ≤ m := by omega
  have hsub : truncatedCube d m (n - 4) x ⊆ truncatedCube d m n x :=
    truncatedCube_mono d m x h4n
  -- the affine-shifted datum
  have haffn : MemLp (affineLift x cl Al) 2 (volume.restrict (truncatedCube d m n x)) := by
    rw [affineLift_eq_affineEval]
    exact memLp_affineEval_truncatedCube x _ _
  have hU : MemLp (fun y => u y - affineLift x cl Al y) 2
      (volume.restrict (truncatedCube d m n x)) := hu.sub haffn
  -- the one-step at the shifted pair
  have htri := excess_oneStep_of_schauder hk hx hnm hU hV hK hCsch hint hgrad hhol hschauder
  rw [excess_sub_affineLift, excess_sub_affineLift] at htri
  -- the corrector's `L̲²` price on `U_{m,n-4}`
  have hu4 : MemLp u 2 (volume.restrict (truncatedCube d m (n - 4) x)) :=
    memLp_restrict_of_subset hsub hu
  have haff4 : MemLp (affineLift x cl Al) 2
      (volume.restrict (truncatedCube d m (n - 4) x)) :=
    memLp_restrict_of_subset hsub haffn
  have hcorr : MemLp v₁ 2 (volume.restrict (truncatedCube d m (n - 4) x)) := by
    refine ((hv.sub haff4).sub hV).ae_eq ?_
    filter_upwards [hVae] with y hy
    show v y - affineLift x cl Al y - V y = v₁ y
    rw [hy]
    ring
  have huv4 : MemLp (fun y => u y - v y) 2
      (volume.restrict (truncatedCube d m (n - 4) x)) := hu4.sub hv
  have hRnn : (0 : ℝ) ≤ datumResidualBound d (n - 2) Kh :=
    datumResidualBound_nonneg d (n - 2) hKh
  have hcorrL2 : normalizedL2On (truncatedCube d m (n - 4) x) v₁
      ≤ datumResidualBound d (n - 2) Kh :=
    normalizedL2On_le_of_ae_abs_le (volume_toReal_truncatedCube_pos x hx hm4)
      (ne_of_lt (volume_truncatedCube_lt_top d m (n - 4) x)) hRnn hcorr hv₁
  have hL2ae : (fun y => (u y - affineLift x cl Al y) - V y)
      =ᵐ[volume.restrict (truncatedCube d m (n - 4) x)]
        (fun y => (u y - v y) + v₁ y) := by
    filter_upwards [hVae] with y hy
    show (u y - affineLift x cl Al y) - V y = (u y - v y) + v₁ y
    rw [hy]
    ring
  have hL2 : normalizedL2On (truncatedCube d m (n - 4) x)
      (fun y => (u y - affineLift x cl Al y) - V y)
      ≤ D + datumResidualBound d (n - 2) Kh := by
    rw [normalizedL2On_congr_ae hL2ae]
    exact (normalizedL2On_add_le huv4 hcorr).trans (add_le_add hD hcorrL2)
  -- the extra leg proves in the printed `K_h` slot
  have h3npos : (0 : ℝ) < (3 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  have hstep : oneStepRemainderConst d Csch k
        * ((3 : ℝ) ^ (-n) * normalizedL2On (truncatedCube d m (n - 4) x)
            (fun y => (u y - affineLift x cl Al y) - V y))
      ≤ oneStepRemainderConst d Csch k * ((3 : ℝ) ^ (-n) * D)
        + boundaryDatumLegConst d Csch k * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) * Kh := by
    have h1 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hL2 h3npos.le)
      (oneStepRemainderConst_nonneg d hCsch k)
    have h2 : oneStepRemainderConst d Csch k
          * ((3 : ℝ) ^ (-n) * (D + datumResidualBound d (n - 2) Kh))
        = oneStepRemainderConst d Csch k * ((3 : ℝ) ^ (-n) * D)
          + oneStepRemainderConst d Csch k
              * ((3 : ℝ) ^ (-n) * datumResidualBound d (n - 2) Kh) := by ring
    rw [h2, oneStepRemainder_mul_datumResidual] at h1
    exact h1
  linarith only [htri, hstep]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum
