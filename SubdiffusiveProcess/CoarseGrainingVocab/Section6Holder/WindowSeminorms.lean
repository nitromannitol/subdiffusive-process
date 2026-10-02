import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.FractionalHolderBridge

/-!
# Hölder Step 3: global-to-window seminorm estimates

The frozen assumptions put the Hölder seminorm on the top cube, whereas the
one-step excess theorem reads it on a truncated window.  This file records
the monotonicity of the literal `sSup` carrier and the resulting forcing
display with its exact `3^(j/2)` scale.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization

noncomputable section

/-- A pointwise Hölder bound bounds the literal supremum seminorm. -/
theorem holderSeminormOn_le_of_bound {d : ℕ} {W : Set (Vec d)}
    {alpha K : ℝ} {f : Vec d → Vec d} (hK : 0 ≤ K)
    (hf : HolderSeminormBoundOn W alpha K f) :
    holderSeminormOn W alpha f ≤ K := by
  classical
  let S : Set ℝ := {r : ℝ | ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧
    r = euclideanNorm (f x - f y) / euclideanNorm (x - y) ^ alpha}
  change sSup S ≤ K
  by_cases hne : S.Nonempty
  · apply csSup_le hne
    intro r hr
    rcases hr with ⟨x, hx, y, hy, hxy, rfl⟩
    have hdist : 0 < euclideanNorm (x - y) ^ alpha := by
      apply Real.rpow_pos_of_pos
      exact lt_of_le_of_ne (euclideanNorm_nonneg _)
        (Ne.symm (fun h => hxy (sub_eq_zero.mp (euclideanNorm_eq_zero_iff.mp h))))
    exact (div_le_iff₀ hdist).2 (hf x hx y hy)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sSup_empty]
    exact hK



theorem holderSeminormOn_mono {d : ℕ} {V W : Set (Vec d)} {alpha : ℝ}
    {f : Vec d → Vec d} (halpha : 0 < alpha) (hf : MemHolder W alpha f)
    (hVW : V ⊆ W) : holderSeminormOn V alpha f ≤ holderSeminormOn W alpha f := by
  have hW0 := Section6ExcessDecay.holderSeminormOn_nonneg hf
  apply holderSeminormOn_le_of_bound hW0
  intro p hp q hq
  exact (Section6ExcessDecay.holderSeminormBoundOn_holderSeminormOn halpha hf)
    p (hVW hp) q (hVW hq)

/-- The forcing part of Step 3, already expressed against the top-cube
Hölder seminorm. -/
theorem forcing_fractional_window_le {d : ℕ} [NeZero d]
    {m j : ℤ} {x : Vec d} {g : Vec d → Vec d} {s : ℝ}
    (hx : x ∈ cube d m) (hs0 : 0 < s) (hs : s ≤ 1 / 4)
    (hg : MemHolder (cube d m) (1 / 2) g) :
    (3 : ℝ) ^ (s * (j : ℝ)) *
        (fractionalSeminormOn (truncatedCube d m j x) s g).toReal ≤
      Section6ExcessDecay.fractionalHolderConst d * Real.sqrt s *
        (3 : ℝ) ^ ((j : ℝ) / 2) * holderSeminormOn (cube d m) (1 / 2) g := by
  have hd : 1 ≤ d := (Nat.one_le_iff_ne_zero).2 (NeZero.ne d)
  have hlocal : MemHolder (truncatedCube d m j x) (1 / 2) g :=
    Section6ExcessDecay.memHolder_mono hg
      (Section6ExcessDecay.truncatedCube_subset_cube d m j x)
  have hbase :=
    Section6ExcessDecay.three_rpow_mul_fractionalSeminormOn_truncatedCube_le_holderSeminormOn
      hd hx hs0 hs hlocal
  have hmono := holderSeminormOn_mono (by norm_num : (0 : ℝ) < 1 / 2) hg
    (Section6ExcessDecay.truncatedCube_subset_cube d m j x)
  have hcoeff : 0 ≤ Section6ExcessDecay.fractionalHolderConst d * Real.sqrt s *
      (3 : ℝ) ^ ((j : ℝ) / 2) :=
    mul_nonneg
      (mul_nonneg (Section6ExcessDecay.fractionalHolderConst_nonneg d)
        (Real.sqrt_nonneg s))
      (Real.rpow_nonneg (by norm_num) _)
  exact hbase.trans (mul_le_mul_of_nonneg_left hmono hcoeff)

/-- The elementary scale identity used for both the forcing and boundary
Hölder terms. -/
theorem three_half_scale_decay (m j : ℤ) :
    (3 : ℝ) ^ ((j : ℝ) / 2) =
      (3 : ℝ) ^ (-(((m : ℝ) - (j : ℝ)) / 2)) *
        (3 : ℝ) ^ ((m : ℝ) / 2) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6Holder
