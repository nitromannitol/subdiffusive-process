module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.OneStepDatum

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2

open MeasureTheory
open Homogenization (Vec)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum

noncomputable section

variable {d : ℕ}

/-- **The boundary one-step contraction at the datum-split competitor, with the
corrector priced in `L̲²`.**

Identical to `Section6SchauderDatum.excess_oneStep_boundary_datumSplit` except
that the corrector enters through

```text
  hv₁ : normalizedL2On (U_{m,n-4}(x)) v₁ ≤ R
```

instead of an almost-everywhere `L^∞` bound, and the fourth leg of the
conclusion is correspondingly `oneStepRemainderConst d Csch k · 3^{-n} · R`.
Since `R` is an arbitrary nonnegative real, the caller is free to price the
corrector by any route — in particular by the Dirichlet-energy/Poincaré route,
which needs no classical gradient for the datum. -/
theorem excess_oneStep_boundary_datumSplit_l2 {m n : ℤ} {k : ℕ} (hk : 6 ≤ k) {x : Vec d}
    (hx : x ∈ cube d m) (hnm : n - 1 ≤ m)
    {u v v₁ V : Vec d → ℝ} {cl : ℝ} {Al : Vec d} {Gv : Vec d → Vec d}
    {K R KhS Csch D : ℝ} (hK : 0 ≤ K) (hCsch : 0 ≤ Csch)
    (hu : MemLp u 2 (volume.restrict (truncatedCube d m n x)))
    (hv : MemLp v 2 (volume.restrict (truncatedCube d m (n - 4) x)))
    (hV : MemLp V 2 (volume.restrict (truncatedCube d m (n - 4) x)))
    (hVae : V =ᵐ[volume.restrict (truncatedCube d m (n - 4) x)]
      (fun y => v y - affineLift x cl Al y - v₁ y))
    (hv₁ : normalizedL2On (truncatedCube d m (n - 4) x) v₁ ≤ R)
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
        + oneStepRemainderConst d Csch k * ((3 : ℝ) ^ (-n) * R) := by
  have h4n : n - 4 ≤ n := by omega
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
  -- the corrector's `L̲²` membership on `U_{m,n-4}`
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
  have hL2ae : (fun y => (u y - affineLift x cl Al y) - V y)
      =ᵐ[volume.restrict (truncatedCube d m (n - 4) x)]
        (fun y => (u y - v y) + v₁ y) := by
    filter_upwards [hVae] with y hy
    show (u y - affineLift x cl Al y) - V y = (u y - v y) + v₁ y
    rw [hy]
    ring
  have hL2 : normalizedL2On (truncatedCube d m (n - 4) x)
      (fun y => (u y - affineLift x cl Al y) - V y) ≤ D + R := by
    rw [normalizedL2On_congr_ae hL2ae]
    exact (normalizedL2On_add_le huv4 hcorr).trans (add_le_add hD hv₁)
  -- the extra leg, priced in `L̲²`
  have h3npos : (0 : ℝ) < (3 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  have hstep : oneStepRemainderConst d Csch k
        * ((3 : ℝ) ^ (-n) * normalizedL2On (truncatedCube d m (n - 4) x)
            (fun y => (u y - affineLift x cl Al y) - V y))
      ≤ oneStepRemainderConst d Csch k * ((3 : ℝ) ^ (-n) * D)
        + oneStepRemainderConst d Csch k * ((3 : ℝ) ^ (-n) * R) := by
    have h1 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hL2 h3npos.le)
      (oneStepRemainderConst_nonneg d hCsch k)
    have h2 : oneStepRemainderConst d Csch k * ((3 : ℝ) ^ (-n) * (D + R))
        = oneStepRemainderConst d Csch k * ((3 : ℝ) ^ (-n) * D)
          + oneStepRemainderConst d Csch k * ((3 : ℝ) ^ (-n) * R) := by ring
    rw [h2] at h1
    exact h1
  linarith only [htri, hstep]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2
