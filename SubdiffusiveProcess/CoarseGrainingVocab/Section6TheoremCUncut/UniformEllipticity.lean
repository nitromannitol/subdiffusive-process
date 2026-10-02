import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.CutoffEllipticity
import SubdiffusiveProcess.Frozen.Section6.FiniteCutoffCoefficientConvergence




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.Frozen.Assumptions

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### A bounded window has a norm bound -/

/-- Every point of the centered paper cube has norm at most an `m`-dependent
constant. -/
theorem exists_norm_bound_cube (d : ℕ) (m : ℤ) :
    ∃ R : ℝ, ∀ x ∈ cube d m, ‖x‖ ≤ R := by
  obtain ⟨R, hR⟩ := (isBounded_openCubeSet (originCube d m)).subset_closedBall 0
  refine ⟨R, fun x hx ↦ ?_⟩
  have hx' : x ∈ Metric.closedBall (0 : Vec d) R := hR hx
  simpa [Metric.mem_closedBall, dist_eq_norm] using hx'

/-! ### Two-sided bounds from a growth envelope -/

/-- **The envelope bound, localized.**  A positive function whose value, its
reciprocal, and a nonnegative extra term are jointly dominated by
`C (1+‖x‖)^κ` is bounded above and below on any window of bounded norm, with
the bounds depending only on `C`, `κ` and the norm bound. -/
theorem bounds_of_envelope {W : Set (Vec d)} {s e : Vec d → ℝ}
    {Cw kappa R : ℝ} (hkappa : 0 ≤ kappa) (hCw : 0 ≤ Cw)
    (hs : ∀ x, 0 < s x) (he : ∀ x, 0 ≤ e x)
    (henv : ∀ x : Vec d, s x + (s x)⁻¹ + e x ≤ Cw * (1 + ‖x‖) ^ kappa)
    (hR : ∀ x ∈ W, ‖x‖ ≤ R) :
    ∀ x ∈ W, (Cw * (1 + R) ^ kappa)⁻¹ ≤ s x ∧ s x ≤ Cw * (1 + R) ^ kappa := by
  intro x hx
  set Lam : ℝ := Cw * (1 + R) ^ kappa with hLamdef
  have hnormnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hmono : (1 + ‖x‖) ^ kappa ≤ (1 + R) ^ kappa :=
    Real.rpow_le_rpow (by linarith) (by linarith [hR x hx]) hkappa
  have henvx : s x + (s x)⁻¹ + e x ≤ Lam := by
    refine (henv x).trans ?_
    exact mul_le_mul_of_nonneg_left hmono hCw
  have hsx : 0 < s x := hs x
  have hinvpos : 0 < (s x)⁻¹ := inv_pos.2 hsx
  have hupper : s x ≤ Lam := by
    have := he x
    linarith
  have hinv : (s x)⁻¹ ≤ Lam := by
    have := he x
    linarith
  refine ⟨?_, hupper⟩
  have hLampos : 0 < Lam := lt_of_lt_of_le hinvpos hinv
  rw [inv_le_comm₀ hLampos hsx]
  exact hinv

/-! ### Continuity of the two anchored coefficients -/

/-- The anchored finite cutoff `ã_L` is continuous. -/
theorem continuous_anchoredCutoff (M : GMCModel d) (L : ℕ)
    (ω : PotentialSample d) : Continuous (anchoredCutoff M L ω) := by
  have : (anchoredCutoff M L ω) =
      fun x ↦ aCutoff M L ω x / aCutoff M L ω 0 := rfl
  rw [this]
  exact (continuous_aCutoff M L ω).div_const _

/-! ### The uniform ellipticity pair -/

/-- **The `J`-uniform ellipticity pair on `𝔠_m`.**  From the growth envelope of
`l.finite.cutoff.coefficient.convergence` at a single sample, the anchored limit
and *every* anchored finite cutoff are bounded between the same
`0 < λ` and `Λ` on the centered paper cube. -/
theorem exists_uniform_bounds_cube (M : GMCModel d) (ω : AnchoredC11Sample d)
    (m : ℤ) {kappa Cw : ℝ} (hkappa : 0 ≤ kappa) (hCw : 0 ≤ Cw)
    (henvLim : ∀ x : Vec d,
      aAnchored M ω x + (aAnchored M ω x)⁻¹ +
          euclideanNorm (aAnchored M ω x • shellGradient (anchoredLog ω) x) ≤
        Cw * (1 + ‖x‖) ^ kappa)
    (henvCut : ∀ x : Vec d, ∀ L : ℕ,
      anchoredCutoff M L ω.1 x + (anchoredCutoff M L ω.1 x)⁻¹ +
          euclideanNorm (anchoredCutoff M L ω.1 x •
            shellGradient (anchoredPartialSumField ω.1 L) x) ≤
        Cw * (1 + ‖x‖) ^ kappa) :
    ∃ lam Lam : ℝ, 0 < lam ∧
      (∀ x ∈ cube d m, lam ≤ aAnchored M ω x ∧ aAnchored M ω x ≤ Lam) ∧
      (∀ L : ℕ, ∀ x ∈ cube d m,
        lam ≤ anchoredCutoff M L ω.1 x ∧ anchoredCutoff M L ω.1 x ≤ Lam) := by
  obtain ⟨R, hR⟩ := exists_norm_bound_cube d m
  set Lam : ℝ := Cw * (1 + R) ^ kappa with hLamdef
  have hlim := bounds_of_envelope (W := cube d m) (s := aAnchored M ω)
    (e := fun x ↦ euclideanNorm (aAnchored M ω x • shellGradient (anchoredLog ω) x))
    hkappa hCw (aAnchored_pos M ω) (fun x ↦ euclideanNorm_nonneg _) henvLim hR
  have hcut : ∀ L : ℕ, ∀ x ∈ cube d m,
      Lam⁻¹ ≤ anchoredCutoff M L ω.1 x ∧ anchoredCutoff M L ω.1 x ≤ Lam := by
    intro L
    exact bounds_of_envelope (W := cube d m) (s := anchoredCutoff M L ω.1)
      (e := fun x ↦ euclideanNorm (anchoredCutoff M L ω.1 x •
        shellGradient (anchoredPartialSumField ω.1 L) x))
      hkappa hCw
      (Section6TheoremC.anchoredCutoff_pos M L ω.1)
      (fun x ↦ euclideanNorm_nonneg _) (fun x ↦ henvCut x L) hR
  obtain ⟨x0, hx0⟩ := Section6TheoremC.nonempty_cube d m
  have hLampos : 0 < Lam :=
    lt_of_lt_of_le (aAnchored_pos M ω x0) (hlim x0 hx0).2
  exact ⟨Lam⁻¹, Lam, inv_pos.2 hLampos, hlim, hcut⟩

/-- The ellipticity carrier attached to a two-sided bound on the anchored
limit. -/
theorem isEllipticFieldOn_aAnchored {M : GMCModel d} {ω : AnchoredC11Sample d}
    {m : ℤ} {lam Lam : ℝ} (hlam : 0 < lam)
    (hb : ∀ x ∈ cube d m, lam ≤ aAnchored M ω x ∧ aAnchored M ω x ≤ Lam) :
    IsEllipticFieldOn lam Lam (cube d m)
      (scalarCoeffField (aAnchored M ω)) := by
  refine Section6TheoremC.isEllipticFieldOn_scalarCoeffField_of_bounds hlam ?_
    (fun x hx ↦ (hb x hx).1) (fun x hx ↦ (hb x hx).2)
  exact (continuous_aAnchored M ω).measurable.ite
    (measurableSet_openCubeSet (originCube d m)) measurable_const

/-- The ellipticity carrier attached to a two-sided bound on an anchored finite
cutoff. -/
theorem isEllipticFieldOn_anchoredCutoff {M : GMCModel d}
    {ω : AnchoredC11Sample d} {m : ℤ} {lam Lam : ℝ} (L : ℕ) (hlam : 0 < lam)
    (hb : ∀ x ∈ cube d m,
      lam ≤ anchoredCutoff M L ω.1 x ∧ anchoredCutoff M L ω.1 x ≤ Lam) :
    IsEllipticFieldOn lam Lam (cube d m)
      (scalarCoeffField (anchoredCutoff M L ω.1)) := by
  refine Section6TheoremC.isEllipticFieldOn_scalarCoeffField_of_bounds hlam ?_
    (fun x hx ↦ (hb x hx).1) (fun x hx ↦ (hb x hx).2)
  exact (continuous_anchoredCutoff M L ω.1).measurable.ite
    (measurableSet_openCubeSet (originCube d m)) measurable_const

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut
