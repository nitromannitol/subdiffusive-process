module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.Corrector
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Carrier
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.ResolventDatumRepresentative

@[expose] public section

/-!
# The difference form of the weak maximum principle

Establishes that two weakly harmonic `H¹` functions whose comparison data
(`Φ1`, `Φ2`) differ everywhere on the domain by at most `M`, and whose own
boundary traces match those comparison data in the zero-trace sense, are
themselves everywhere-close a.e. in the interior. This generalizes
`SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.ae_abs_le_of_isUnitWeaklyHarmonicOn`
(one harmonic function vs. one bounded comparison datum) to a PAIR of harmonic
functions, which is the comparison shape that a two-index Cauchy argument on a
sequence of finite-cutoff harmonic replacements needs.

Does NOT claim: that any concrete comparison datum `Φ1`/`Φ2` exists for a given
application (constructing one, e.g. from a pointwise boundary bound between two
continuous representatives, is a separate step left to the caller), and does
not touch the `GMC` `weakSobolevGraph`/`killedSobolevGraph`
representation directly (a caller there must first pass through
`SubdiffusiveProcess.exists_nativeH1Function_of_weakSobolevGraph`/
`exists_nativeH10Function_of_killedSobolevGraph`).
-/

open MeasureTheory Set
open SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder (IsUnitWeaklyHarmonicOn isUnitWeaklyHarmonicOn_iff)
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent (H1Function.ofAEEq)
open Homogenization

namespace SubdiffusiveProcess

variable {d : ℕ}

/-- Re-basing a zero-trace witness on an a.e.-equal value function (same gradient
and approximating sequence). -/
def H10Function.ofAEEq {W : Set (Homogenization.Vec d)} (ρ : H10Function W) (g : Homogenization.Vec d → ℝ)
    (hg : g =ᵐ[volume.restrict W] ρ.toH1Function.toFun) : H10Function W where
  toH1Function := H1Function.ofAEEq ρ.toH1Function g hg
  approx := ρ.approx
  approx_smooth := ρ.approx_smooth
  approx_hasCompactSupport := ρ.approx_hasCompactSupport
  approx_support_subset := ρ.approx_support_subset
  tendsto_approx := by
    refine ρ.tendsto_approx.congr (fun n => ?_)
    refine eLpNorm_congr_ae ?_
    filter_upwards [hg] with x hx
    simp [hx]
  tendsto_approx_grad := ρ.tendsto_approx_grad

/-- `H¹₀` membership only sees the function a.e. on the domain. -/
theorem memH10_congr {W : Set (Homogenization.Vec d)} {f g : Homogenization.Vec d → ℝ}
    (hf : MemH10 W f) (hfg : f =ᵐ[volume.restrict W] g) : MemH10 W g := by
  obtain ⟨ρ, hρ⟩ := hf
  have hv : g =ᵐ[volume.restrict W] ρ.toH1Function.toFun := by rw [hρ]; exact hfg.symm
  exact ⟨H10Function.ofAEEq ρ g hv, rfl⟩

variable [NeZero d]

/-- The two-sided weak maximum principle for a DIFFERENCE of weakly harmonic
`H¹` functions: if `w1`, `w2` are weakly harmonic on an open bounded convex `K`,
each matching (in the zero-trace sense) a comparison datum `Φ1`/`Φ2`, and the
comparison data differ everywhere on `K` by at most `M`, then `w1` and `w2`
themselves differ a.e. on `K` by at most `M`. -/
theorem ae_abs_sub_le_of_isWeaklyHarmonicOn {K : Set (Homogenization.Vec d)}
    (hK : IsOpenBoundedConvexDomain K)
    {w1 w2 Φ1 Φ2 : H1Function K}
    (hw1 : IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) K w1)
    (hw2 : IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) K w2)
    (hdiff1 : MemH10 K (fun y => w1.toFun y - Φ1.toFun y))
    (hdiff2 : MemH10 K (fun y => w2.toFun y - Φ2.toFun y))
    {M : ℝ} (hM : 0 ≤ M) (hΦ : ∀ y ∈ K, |Φ1.toFun y - Φ2.toFun y| ≤ M) :
    ∀ᵐ y ∂(volume.restrict K), |w1.toFun y - w2.toFun y| ≤ M := by
  have hw : IsWeaklyHarmonicOn (fun _ => (1 : ℝ)) K (w1 - w2) := by
    intro φ
    have h1 := hw1 φ
    have h2 := hw2 φ
    have hInt1 : IntegrableOn
        (fun x => vecDot ((1 : ℝ) • w1.grad x) (φ.toH1Function.grad x)) K volume := by
      simpa using integrableOn_vecDot_grad w1 φ.toH1Function
    have hInt2 : IntegrableOn
        (fun x => vecDot ((1 : ℝ) • w2.grad x) (φ.toH1Function.grad x)) K volume := by
      simpa using integrableOn_vecDot_grad w2 φ.toH1Function
    have hfun : (fun x => vecDot ((1 : ℝ) • (w1 - w2).grad x) (φ.toH1Function.grad x)) =
        fun x => vecDot ((1 : ℝ) • w1.grad x) (φ.toH1Function.grad x) -
          vecDot ((1 : ℝ) • w2.grad x) (φ.toH1Function.grad x) := by
      funext x
      simp only [H1Function.add_grad, H1Function.neg_grad, one_smul,
        sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
    show ∫ x in K, vecDot ((1 : ℝ) • (w1 - w2).grad x) (φ.toH1Function.grad x) ∂volume = 0
    rw [hfun, integral_sub hInt1 hInt2, h1, h2, sub_zero]
  have hdiff : MemH10 K (fun y => (w1 - w2).toFun y - (Φ1 - Φ2).toFun y) := by
    have hraw := memH10_sub hdiff1 hdiff2
    have hfun : (fun y => (w1.toFun y - Φ1.toFun y) - (w2.toFun y - Φ2.toFun y)) =
        fun y => (w1 - w2).toFun y - (Φ1 - Φ2).toFun y := by
      funext y
      rw [H1Function.sub_toFun, H1Function.sub_toFun]
      ring
    rwa [hfun] at hraw
  obtain ⟨Ψ, hΨu, hΨl, hΨeq⟩ := exists_h1_clamp hK (Φ1 - Φ2) hM
  have hdiff' : MemH10 K (fun y => (w1 - w2).toFun y - Ψ.toFun y) := by
    refine memH10_congr hdiff ?_
    filter_upwards [ae_restrict_mem hK.isOpen.measurableSet] with y hy
    rw [hΨeq y (by rw [H1Function.sub_toFun]; exact hΦ y hy)]
  have hup : HasBoundaryUpperBoundOn K (w1 - w2) M :=
    hasBoundaryUpperBoundOn_of_datum_le hK hdiff' hΨu
  have hdiffneg : MemH10 K (fun y => (-(w1 - w2)).toFun y - (-Ψ).toFun y) := by
    have h := Homogenization.memH10_neg hdiff'
    have hfun : (fun y => -((w1 - w2).toFun y - Ψ.toFun y)) =
        fun y => (-(w1 - w2)).toFun y - (-Ψ).toFun y := by
      funext y
      rw [H1Function.neg_toFun, H1Function.neg_toFun]
      ring
    rwa [hfun] at h
  have hlow : HasBoundaryUpperBoundOn K (-(w1 - w2)) M :=
    hasBoundaryUpperBoundOn_of_datum_le hK hdiffneg fun y => by
      rw [H1Function.neg_toFun]; linarith [hΨl y]
  have hae := ae_abs_le_of_isUnitWeaklyHarmonicOn hK
    (isUnitWeaklyHarmonicOn_iff.2 hw) hup hlow
  filter_upwards [hae] with y hy
  rwa [H1Function.sub_toFun] at hy

end SubdiffusiveProcess
