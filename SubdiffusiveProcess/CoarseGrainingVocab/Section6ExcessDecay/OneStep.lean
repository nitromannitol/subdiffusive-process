module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.TaylorCompetitor
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Triangle

-- REUSE-CANDIDATE: Algsuperdiff/Section4/Provider/ExcessDecay/OneStepAssembly.lean
-- Adapted from Algsuperdiff/Section4/Provider/ExcessDecay/OneStepAssembly.lean

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

open MeasureTheory
open Homogenization (vecDot volumeAverageVec)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration

noncomputable section

variable {d : ℕ}

/-! ### `zpow`/`rpow` bookkeeping on the base `3` -/

theorem three_zpow_rpow_half_mul (a b : ℤ) :
    ((3 : ℝ) ^ a) ^ (1 / 2 : ℝ) * ((3 : ℝ) ^ b) ^ (1 / 2 : ℝ)
      = ((3 : ℝ) ^ (a + b)) ^ (1 / 2 : ℝ) := by
  rw [← Real.mul_rpow (by positivity) (by positivity),
    ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]

theorem three_zpow_rpow_half_nonneg (a : ℤ) : 0 ≤ ((3 : ℝ) ^ a) ^ (1 / 2 : ℝ) :=
  Real.rpow_nonneg (by positivity) _

theorem three_zpow_rpow_half_le_one {k : ℕ} : ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) ≤ 1 := by
  refine Real.rpow_le_one (by positivity) ?_ (by norm_num)
  have h : (3 : ℝ) ^ (-(k : ℤ)) = ((3 : ℝ) ^ (k : ℕ))⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  rw [h]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- The `rpow` form of a triadic power: `(3^j)^{1/2} = 3^{j/2}`. -/
theorem three_zpow_rpow_half_eq (j : ℤ) :
    ((3 : ℝ) ^ j) ^ (1 / 2 : ℝ) = (3 : ℝ) ^ ((j : ℝ) / 2) := by
  rw [← Real.rpow_intCast (3 : ℝ) j, ← Real.rpow_mul (by norm_num)]
  ring_nf

/-! ### Integrability slots -/

theorem integrableOn_sq_truncatedCube {m j : ℤ} (x : Vec d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (truncatedCube d m j x))) :
    IntegrableOn (fun p => f p ^ 2) (truncatedCube d m j x) := by
  have h := integrableOn_sub_const_sq_truncatedCube x hf 0
  have hfun : (fun p => (f p - 0) ^ 2) = fun p => f p ^ 2 := by
    funext p; ring
  rwa [hfun] at h

/-- `HolderSeminormBoundOn` is antitone in the window. -/
theorem holderSeminormBoundOn_mono_set {U V : Set (Vec d)} {alpha K : ℝ}
    {f : Vec d → Vec d} (hf : HolderSeminormBoundOn U alpha K f) (hVU : V ⊆ U) :
    HolderSeminormBoundOn V alpha K f :=
  fun p hp q hq => hf p (hVU hp) q (hVU hq)

/-! ### The constants -/

/-- The contraction constant of the one-step estimate: the Taylor constant
times the quasi-monotonicity ratio `81·3^{3d}` of the four-scale gap. -/
def oneStepContractionConst (d : ℕ) : ℝ :=
  taylorConst d * (81 * Real.sqrt (((3 : ℝ) ^ (6 : ℤ)) ^ d))

theorem oneStepContractionConst_nonneg (d : ℕ) : 0 ≤ oneStepContractionConst d :=
  mul_nonneg (taylorConst_nonneg d) (by positivity)

/-- The remainder constant of the one-step estimate: the two routes by which the
`L̲²` comparison error `3^{-n}‖u-v‖_{L̲²(U_{m,n-4})}` reaches the conclusion. -/
def oneStepRemainderConst (d : ℕ) (Csch : ℝ) (k : ℕ) : ℝ :=
  81 * taylorConst d * Csch * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) +
    (3 : ℝ) ^ (k : ℤ) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d)

theorem oneStepRemainderConst_nonneg (d : ℕ) {Csch : ℝ} (hCsch : 0 ≤ Csch) (k : ℕ) :
    0 ≤ oneStepRemainderConst d Csch k := by
  refine add_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (by norm_num) (taylorConst_nonneg d)) hCsch) ?_) (by positivity)
  exact three_zpow_rpow_half_nonneg _

/-! ### The one-step contraction -/

/-- **The deterministic one-step excess contraction.**

Given the competitor's `C^{1,1/2}` data on `U_{m,n-5}(x)` and the Schauder
bound `hschauder` on its gradient-Hölder constant — and *nothing else* — the
excess of `u` on `U_{m,n-k}(x)` contracts:

```text
  E(u,U_{m,n-k}) ≤ C(d) C_S (3^{-k})^{1/2} E(u,U_{m,n})
                    + C(d,C_S,k) · 3^{-n}‖u-v‖_{L̲²(U_{m,n-4})}
                    + C(d) (3^{n-k})^{1/2} K_h .
```
-/
theorem excess_oneStep_of_schauder {m n : ℤ} {k : ℕ} (hk : 6 ≤ k) {x : Vec d}
    (hx : x ∈ cube d m) (hnm : n - 1 ≤ m) {u v : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedCube d m n x)))
    (hv : MemLp v 2 (volume.restrict (truncatedCube d m (n - 4) x)))
    {Gv : Vec d → Vec d} {K Kh Csch : ℝ} (hK : 0 ≤ K) (hCsch : 0 ≤ Csch)
    (hint : ∀ i, IntegrableOn (fun p => Gv p i) (truncatedCube d m (n - 5) x) volume)
    (hgrad : HasGradientOn (truncatedCube d m (n - 5) x) v Gv)
    (hhol : HolderSeminormBoundOn (truncatedCube d m (n - 5) x) (1 / 2 : ℝ) K Gv)
    (hschauder : K ≤ Csch * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) *
      excess (n - 4) (truncatedCube d m (n - 4) x) v + Kh) :
    excess (n - (k : ℤ)) (truncatedCube d m (n - (k : ℤ)) x) u
      ≤ oneStepContractionConst d * Csch * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) *
            excess n (truncatedCube d m n x) u
        + oneStepRemainderConst d Csch k *
            ((3 : ℝ) ^ (-n) * normalizedL2On (truncatedCube d m (n - 4) x)
              (fun p => u p - v p))
        + taylorConst d * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) * Kh := by
  have h3ne : (3 : ℝ) ≠ 0 := by norm_num
  -- window bookkeeping
  have hk5 : n - (k : ℤ) ≤ n - 5 := by omega
  have hk4 : n - (k : ℤ) ≤ n - 4 := by omega
  have h54 : n - 5 ≤ n - 4 := by omega
  have h4n : n - 4 ≤ n := by omega
  have hmk : n - (k : ℤ) - 1 ≤ m := by omega
  have hm5 : n - 5 - 1 ≤ m := by omega
  have hm4 : n - 4 - 1 ≤ m := by omega
  have hsub_k4 : truncatedCube d m (n - (k : ℤ)) x ⊆ truncatedCube d m (n - 4) x :=
    truncatedCube_mono d m x hk4
  have hsub_k5 : truncatedCube d m (n - (k : ℤ)) x ⊆ truncatedCube d m (n - 5) x :=
    truncatedCube_mono d m x hk5
  have hsub_4n : truncatedCube d m (n - 4) x ⊆ truncatedCube d m n x :=
    truncatedCube_mono d m x h4n
  -- the `MemLp` slots
  have hu4 : MemLp u 2 (volume.restrict (truncatedCube d m (n - 4) x)) :=
    memLp_restrict_of_subset hsub_4n hu
  have huk : MemLp u 2 (volume.restrict (truncatedCube d m (n - (k : ℤ)) x)) :=
    memLp_restrict_of_subset hsub_k4 hu4
  have hvk : MemLp v 2 (volume.restrict (truncatedCube d m (n - (k : ℤ)) x)) :=
    memLp_restrict_of_subset hsub_k4 hv
  have huv4 : MemLp (fun p => u p - v p) 2 (volume.restrict (truncatedCube d m (n - 4) x)) :=
    hu4.sub hv
  have huvk : MemLp (fun p => u p - v p) 2
      (volume.restrict (truncatedCube d m (n - (k : ℤ)) x)) :=
    memLp_restrict_of_subset hsub_k4 huv4
  have hvu4 : MemLp (fun p => v p - u p) 2 (volume.restrict (truncatedCube d m (n - 4) x)) :=
    hv.sub hu4
  -- abbreviations
  set E0 := excess n (truncatedCube d m n x) u with hE0
  set S4 := normalizedL2On (truncatedCube d m (n - 4) x) (fun p => u p - v p) with hS4
  have hS4nn : 0 ≤ S4 := normalizedL2On_nonneg _ _
  have hE0nn : 0 ≤ E0 := by
    rw [hE0, excess_eq_affineExcessScaled]
    exact affineExcessScaled_nonneg _ _ _
  have h3npos : (0 : ℝ) < (3 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  -- (1) the excess triangle on `U_{m,n-k}`
  have h1 : excess (n - (k : ℤ)) (truncatedCube d m (n - (k : ℤ)) x) u
      ≤ excess (n - (k : ℤ)) (truncatedCube d m (n - (k : ℤ)) x) v +
          (3 : ℝ) ^ (-(n - (k : ℤ))) *
            normalizedL2On (truncatedCube d m (n - (k : ℤ)) x) (fun p => u p - v p) :=
    excess_le_add _ huvk (fun c g => memLp_sub_affineEval_truncatedCube x hvk c g)
  -- (2) the affine competitor on `U_{m,n-k}`
  have h2 : excess (n - (k : ℤ)) (truncatedCube d m (n - (k : ℤ)) x) v
      ≤ taylorConst d * K * ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) :=
    excess_le_taylor hx hmk hK hvk (fun i => (hint i).mono_set hsub_k5)
      (hgrad.mono_set hsub_k5) (holderSeminormBoundOn_mono_set hhol hsub_k5)
  -- (3) the excess triangle on `U_{m,n-4}`, with `u` and `v` interchanged
  have h3 : excess (n - 4) (truncatedCube d m (n - 4) x) v
      ≤ excess (n - 4) (truncatedCube d m (n - 4) x) u +
          (3 : ℝ) ^ (-(n - 4)) *
            normalizedL2On (truncatedCube d m (n - 4) x) (fun p => v p - u p) :=
    excess_le_add _ hvu4 (fun c g => memLp_sub_affineEval_truncatedCube x hu4 c g)
  rw [normalizedL2On_sub_comm, ← hS4] at h3
  -- (4) quasi-monotonicity `E(u,U_{m,n-4}) ≤ 81·3^{3d} E(u,U_{m,n})`
  have h4 : excess (n - 4) (truncatedCube d m (n - 4) x) u
      ≤ 81 * Real.sqrt (((3 : ℝ) ^ (6 : ℤ)) ^ d) * E0 := by
    have h := excess_truncatedCube_le (j := n - 4) (l := n) hx hm4 hnm h4n hu
    rw [show n - (n - 4) + 2 = (6 : ℤ) by ring, show n - (n - 4) = (4 : ℤ) by ring] at h
    rw [hE0]
    calc excess (n - 4) (truncatedCube d m (n - 4) x) u
        ≤ (3 : ℝ) ^ (4 : ℤ) * Real.sqrt (((3 : ℝ) ^ (6 : ℤ)) ^ d) *
            excess n (truncatedCube d m n x) u := h
      _ = 81 * Real.sqrt (((3 : ℝ) ^ (6 : ℤ)) ^ d) * excess n (truncatedCube d m n x) u := by
          rw [show ((3 : ℝ) ^ (4 : ℤ)) = 81 by norm_num]
  -- (5) the window transfer of the comparison error
  have h5 : normalizedL2On (truncatedCube d m (n - (k : ℤ)) x) (fun p => u p - v p)
      ≤ Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d) * S4 := by
    have h := normalizedL2On_truncatedCube_le (j := n - (k : ℤ)) (l := n - 4) hx hmk hm4 hk4
      (f := fun p => u p - v p) (integrableOn_sq_truncatedCube x huv4)
    rwa [show n - 4 - (n - (k : ℤ)) + 2 = (k : ℤ) - 2 by ring] at h
  -- the two `3`-power rewrites
  have hpow_k : (3 : ℝ) ^ (-(n - (k : ℤ))) = (3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-n) := by
    rw [show -(n - (k : ℤ)) = (k : ℤ) + -n by ring, zpow_add₀ h3ne]
  have hpow_4 : (3 : ℝ) ^ (-(n - 4)) = 81 * (3 : ℝ) ^ (-n) := by
    rw [show -(n - 4) = (4 : ℤ) + -n by ring, zpow_add₀ h3ne]
    norm_num
  rw [hpow_k] at h1
  rw [hpow_4] at h3
  -- the Schauder leg, expanded
  set T := ((3 : ℝ) ^ (n - (k : ℤ))) ^ (1 / 2 : ℝ) with hT
  set Q := ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) with hQ
  have hTnn : 0 ≤ T := three_zpow_rpow_half_nonneg _
  have hQnn : 0 ≤ Q := three_zpow_rpow_half_nonneg _
  have hprod : ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) * T = Q := by
    rw [hT, hQ, three_zpow_rpow_half_mul, show -n + (n - (k : ℤ)) = -(k : ℤ) by ring]
  have hKT : taylorConst d * K * T
      ≤ taylorConst d * Csch * Q * excess (n - 4) (truncatedCube d m (n - 4) x) v +
          taylorConst d * T * Kh := by
    have hstep : taylorConst d * K * T
        ≤ taylorConst d * (Csch * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) *
            excess (n - 4) (truncatedCube d m (n - 4) x) v + Kh) * T := by
      refine mul_le_mul_of_nonneg_right ?_ hTnn
      exact mul_le_mul_of_nonneg_left hschauder (taylorConst_nonneg d)
    have hexp : taylorConst d * (Csch * ((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) *
          excess (n - 4) (truncatedCube d m (n - 4) x) v + Kh) * T
        = taylorConst d * Csch * (((3 : ℝ) ^ (-n)) ^ (1 / 2 : ℝ) * T) *
            excess (n - 4) (truncatedCube d m (n - 4) x) v + taylorConst d * T * Kh := by
      ring
    rw [hexp, hprod] at hstep
    exact hstep
  -- assemble
  have hcoef : 0 ≤ taylorConst d * Csch * Q := mul_nonneg (mul_nonneg (taylorConst_nonneg d) hCsch) hQnn
  have hlegA : taylorConst d * Csch * Q * excess (n - 4) (truncatedCube d m (n - 4) x) v
      ≤ taylorConst d * Csch * Q * (81 * Real.sqrt (((3 : ℝ) ^ (6 : ℤ)) ^ d) * E0) +
          taylorConst d * Csch * Q * (81 * ((3 : ℝ) ^ (-n) * S4)) := by
    have hcomb : excess (n - 4) (truncatedCube d m (n - 4) x) v
        ≤ 81 * Real.sqrt (((3 : ℝ) ^ (6 : ℤ)) ^ d) * E0 + 81 * (3 : ℝ) ^ (-n) * S4 := by
      linarith only [h3, h4]
    calc taylorConst d * Csch * Q * excess (n - 4) (truncatedCube d m (n - 4) x) v
        ≤ taylorConst d * Csch * Q *
            (81 * Real.sqrt (((3 : ℝ) ^ (6 : ℤ)) ^ d) * E0 + 81 * (3 : ℝ) ^ (-n) * S4) :=
          mul_le_mul_of_nonneg_left hcomb hcoef
      _ = taylorConst d * Csch * Q * (81 * Real.sqrt (((3 : ℝ) ^ (6 : ℤ)) ^ d) * E0) +
            taylorConst d * Csch * Q * (81 * ((3 : ℝ) ^ (-n) * S4)) := by ring
  have hlegB : (3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-n) *
        normalizedL2On (truncatedCube d m (n - (k : ℤ)) x) (fun p => u p - v p)
      ≤ (3 : ℝ) ^ (k : ℤ) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d) *
          ((3 : ℝ) ^ (-n) * S4) := by
    have hc : (0 : ℝ) ≤ (3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-n) := by positivity
    calc (3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-n) *
          normalizedL2On (truncatedCube d m (n - (k : ℤ)) x) (fun p => u p - v p)
        ≤ (3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-n) *
            (Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d) * S4) :=
          mul_le_mul_of_nonneg_left h5 hc
      _ = (3 : ℝ) ^ (k : ℤ) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d) *
            ((3 : ℝ) ^ (-n) * S4) := by ring
  have hfinal : oneStepContractionConst d * Csch * Q * E0
      = taylorConst d * Csch * Q * (81 * Real.sqrt (((3 : ℝ) ^ (6 : ℤ)) ^ d) * E0) := by
    rw [oneStepContractionConst]
    ring
  have hrem : oneStepRemainderConst d Csch k * ((3 : ℝ) ^ (-n) * S4)
      = taylorConst d * Csch * Q * (81 * ((3 : ℝ) ^ (-n) * S4)) +
          (3 : ℝ) ^ (k : ℤ) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d) *
            ((3 : ℝ) ^ (-n) * S4) := by
    rw [oneStepRemainderConst, hQ]
    ring
  rw [hfinal, hrem]
  linarith only [h1, h2, hKT, hlegA, hlegB]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
