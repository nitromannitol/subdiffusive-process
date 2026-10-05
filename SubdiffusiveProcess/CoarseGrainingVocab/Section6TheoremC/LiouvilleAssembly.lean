module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.LiouvilleConstancy

@[expose] public section

/-!
# The Liouville half, assembled for term application

Every step of Theorem C's Liouville clause is now proved:

| step | source | module |
|---|---|---|
| Borel–Cantelli | `t.large.scale.Holder.multifractal` | `MinimalScaleSummability` |
| Radii and scales | `t.large.scale.Holder.multifractal` | `LiouvilleGeometry`, `LiouvilleV4` |
| The average minimizes | `t.large.scale.Holder.multifractal` | `VarianceMinimization` |
| Constancy | `t.large.scale.Holder.multifractal` | `LiouvilleV4`, `LiouvilleConstancy` |
| Countable intersection | `t.large.scale.Holder.multifractal` | `CountableFullEvents` |
| The representative | `t.large.scale.Holder.multifractal` | `ConstantRepresentative` |

`liouville_representative_of_displays` chains them.  Its hypotheses are exactly
what Theorem C supplies at `γ = γ_reg`: the v4 growth condition, local
integrability of `u`, and the oscillation display available at every
sufficiently large scale.  Its conclusion is the frozen Liouville conclusion
package verbatim.  The eventual provider applies it as a term.

The display hypothesis is phrased as "for each `n` there is a threshold beyond
which the display holds", which is how Theorem C delivers it: the constraint
`n ≤ m - 𝓛(γ,m)` and the interior condition `𝔠_n ⊆ 𝔠_{m-1}` are both eventually
satisfied in `m`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- Splitting the display's decay factor across the two scales. -/
theorem rpow_neg_sub_split (gamma : ℝ) (m n : ℤ) :
    (3 : ℝ) ^ (-gamma * ((m : ℝ) - (n : ℝ))) =
      (3 : ℝ) ^ (gamma * (n : ℝ)) * (3 : ℝ) ^ (-gamma * (m : ℝ)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  ring_nf

/-- **The Liouville half, assembled.**  From the v4 growth hypothesis and the
oscillation display, produce the frozen conclusion package. -/
theorem liouville_representative_of_displays
    {gamma C : ℝ} {u : Vec d → ℝ} (hgamma : 0 < gamma) (hC : 0 ≤ C)
    (hfreq : ∀ ε > 0, ∃ᶠ R : ℝ in atTop,
      liouvilleFunctional (d := d) gamma u R < ε)
    (huInt : ∀ m : ℤ, IntegrableOn u (cube d m))
    (huSq : ∀ m : ℤ, IntegrableOn (fun x ↦ u x ^ 2) (cube d m))
    (hball : ∀ (R : ℝ) (c : ℝ),
      IntegrableOn (fun x ↦ (u x - c) ^ 2) (Metric.ball (0 : Vec d) R))
    (hcent : ∀ n : ℤ,
      IntegrableOn (fun x ↦ (u x - averageOn (cube d n) u) ^ 2) (cube d n))
    (hdisplay : ∀ n : ℤ, ∃ N : ℤ, ∀ m : ℤ, N ≤ m →
      normalizedL2On (cube d n) (fun x ↦ u x - averageOn (cube d n) u) ≤
        C * (3 : ℝ) ^ (-gamma * ((m : ℝ) - (n : ℝ))) *
          normalizedL2On (cube d m)
            (fun x ↦ u x - averageOn (cube d m) u))
    (P : ∀ m : ℤ, H1Function (openCubeSet (originCube d m)) → Prop) :
    ∃ uRep : Vec d → ℝ,
      Continuous uRep ∧
      uRep =ᵐ[volume] u ∧
      (∀ m : ℤ, ∀ um : H1Function (openCubeSet (originCube d m)),
        (∀ x, um.toFun x = u x) → P m um →
        uRep =ᵐ[volume.restrict (openCubeSet (originCube d m))] um.toFun) ∧
      ∃ c' : ℝ, ∀ x, uRep x = c' := by
  -- Local constancy on each centered cube, from S8 plus the display.
  have hlocal : ∀ n : ℕ,
      u =ᵐ[volume.restrict (cube d (n : ℤ))]
        fun _ ↦ averageOn (cube d (n : ℤ)) u := by
    intro n
    refine ae_eq_average_of_disp (gamma := gamma) hC (n : ℤ) (hcent (n : ℤ)) ?_
    intro eps heps
    obtain ⟨N, hN⟩ := hdisplay (n : ℤ)
    obtain ⟨m, hmN, hmlt⟩ :=
      exists_scale_ge_and_lt_v4 hgamma hfreq huInt huSq hball heps N
    have hY : 0 ≤ normalizedL2On (cube d m)
        (fun x ↦ u x - averageOn (cube d m) u) :=
      Section6Iteration.normalizedL2On_nonneg _ _
    have hstep := hN m hmN
    refine hstep.trans ?_
    rw [rpow_neg_sub_split gamma m (n : ℤ)]
    have hfac : (0 : ℝ) ≤ C * (3 : ℝ) ^ (gamma * (n : ℝ)) := by positivity
    calc C * ((3 : ℝ) ^ (gamma * (n : ℝ)) *
            (3 : ℝ) ^ (-gamma * (m : ℝ))) *
          normalizedL2On (cube d m)
            (fun x ↦ u x - averageOn (cube d m) u)
        = (C * (3 : ℝ) ^ (gamma * (n : ℝ))) *
            ((3 : ℝ) ^ (-gamma * (m : ℝ)) *
              normalizedL2On (cube d m)
                (fun x ↦ u x - averageOn (cube d m) u)) := by ring
      _ ≤ (C * (3 : ℝ) ^ (gamma * (n : ℝ))) * eps :=
          mul_le_mul_of_nonneg_left hmlt.le hfac
      _ = C * (3 : ℝ) ^ (gamma * (n : ℝ)) * eps := by ring
  -- Upgrade to a global constant and package.
  have hcube : ∀ n : ℕ, ∀ᵐ x ∂volume,
      x ∈ cube d (n : ℤ) → u x = averageOn (cube d (n : ℤ)) u := by
    intro n
    refine (ae_restrict_iff' ?_).1 (hlocal n)
    exact measurableSet_openCubeSet (originCube d (n : ℤ))
  exact exists_liouville_representative_of_forall_cube hcube P

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
