module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Support

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The four-term excess-decay right-hand side is monotone in its common
constant when all displayed factors have their manuscript signs. -/
theorem excess_decay_rhs_mono {C C' : ℝ} (hCC : C ≤ C')
    {p : Prop} [Decidable p]
    {a E b ss eps Err Sl J sourceWeight Tinv scaleWeight Fg
      holderWeight holderScale Hh X : ℝ}
    (hE : 0 ≤ E) (ha : 0 ≤ a) (hb : 0 ≤ b) (hss : 0 ≤ ss)
    (heps : 0 ≤ eps) (hErr : 0 ≤ Err) (hSl : 0 ≤ Sl) (hJ : 0 ≤ J)
    (hsourceWeight : 0 ≤ sourceWeight) (hTinv : 0 ≤ Tinv)
    (hscaleWeight : 0 ≤ scaleWeight) (hFg : 0 ≤ Fg)
    (hholderWeight : 0 ≤ holderWeight) (hholderScale : 0 ≤ holderScale)
    (hHh : 0 ≤ Hh)
    (hX : X ≤ C * (a + b * ss * eps) * E +
      C * b * ss * Err * (Sl + J) +
      C * sourceWeight * b * Tinv * scaleWeight * Fg +
      (if p then C * holderWeight * b * holderScale * Hh else 0)) :
    X ≤ C' * (a + b * ss * eps) * E +
      C' * b * ss * Err * (Sl + J) +
      C' * sourceWeight * b * Tinv * scaleWeight * Fg +
      (if p then C' * holderWeight * b * holderScale * Hh else 0) := by
  have hfirst : 0 ≤ a + b * ss * eps :=
    add_nonneg ha (mul_nonneg (mul_nonneg hb hss) heps)
  have h1 : C * (a + b * ss * eps) * E ≤ C' * (a + b * ss * eps) * E :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC hfirst) hE
  have h2 : C * b * ss * Err * (Sl + J) ≤ C' * b * ss * Err * (Sl + J) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCC hb) hss) hErr)
      (add_nonneg hSl hJ)
  have h3 : C * sourceWeight * b * Tinv * scaleWeight * Fg ≤
      C' * sourceWeight * b * Tinv * scaleWeight * Fg :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCC hsourceWeight) hb) hTinv)
        hscaleWeight) hFg
  have h4 : (if p then C * holderWeight * b * holderScale * Hh else 0) ≤
      (if p then C' * holderWeight * b * holderScale * Hh else 0) := by
    split_ifs
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCC hholderWeight) hb) hholderScale) hHh
    · exact le_rfl
  linarith only [hX, h1, h2, h3, h4]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
