import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.FractionalHolderBridge




namespace SubdiffusiveProcess.ExcessDecayLive

open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
open Homogenization hiding Vec
open Homogenization.Book

noncomputable section

variable {d : ℕ}

theorem holderLeg_live {m j : ℤ} {x : Vec d} {f : Vec d → Vec d} {s : ℝ}
    (hd : 1 ≤ d) (hx : x ∈ cube d m) (hs0 : 0 < s) (hs : s ≤ 1 / 4)
    (hf : MemHolder (truncatedCube d m j x) (1 / 2) f) :
    s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ (-j) *
        ((3 : ℝ) ^ ((1 + s) * (j : ℝ)) *
          (fractionalSeminormOn (truncatedCube d m j x) s f).toReal)) ≤
      fractionalHolderConst d * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((j : ℝ) / 2) *
        holderSeminormOn (truncatedCube d m j x) (1 / 2) f := by
  have h := holderLeg_le (m := m) (j := j) (x := x) (f := f) (s := s) hd hx hs0 hs hf
  have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have e1 : s ^ (-7 / 2 : ℝ) = Real.sqrt s * s ^ (-4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs0]
    norm_num
  have e2 : s ^ (-3 : ℝ) = Real.sqrt s * s ^ (-7 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs0]
    norm_num
  calc s ^ (-7 / 2 : ℝ) * ((3 : ℝ) ^ (-j) *
        ((3 : ℝ) ^ ((1 + s) * (j : ℝ)) *
          (fractionalSeminormOn (truncatedCube d m j x) s f).toReal))
      = Real.sqrt s * (s ^ (-4 : ℝ) * ((3 : ℝ) ^ (-j) *
        ((3 : ℝ) ^ ((1 + s) * (j : ℝ)) *
          (fractionalSeminormOn (truncatedCube d m j x) s f).toReal))) := by
        rw [e1]; ring
    _ ≤ Real.sqrt s * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((j : ℝ) / 2) *
        holderSeminormOn (truncatedCube d m j x) (1 / 2) f) :=
        mul_le_mul_of_nonneg_left h hsq
    _ = fractionalHolderConst d * (Real.sqrt s * s ^ (-7 / 2 : ℝ)) * (3 : ℝ) ^ ((j : ℝ) / 2) *
        holderSeminormOn (truncatedCube d m j x) (1 / 2) f := by ring
    _ = fractionalHolderConst d * s ^ (-3 : ℝ) * (3 : ℝ) ^ ((j : ℝ) / 2) *
        holderSeminormOn (truncatedCube d m j x) (1 / 2) f := by rw [← e2]

end

end SubdiffusiveProcess.ExcessDecayLive
