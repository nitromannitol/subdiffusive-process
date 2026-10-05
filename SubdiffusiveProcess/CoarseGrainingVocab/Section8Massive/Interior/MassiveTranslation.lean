module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.WeakEquationBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellTransport
public import Homogenization.Sobolev.H1.Translation

@[expose] public section

/-!
# Translation of massive weak equations and residual lifts

All terms are transported with the restricted-volume translation identities.
No extra regularity or integrability hypotheses are needed for transport.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent

open MeasureTheory Homogenization
open SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-! `isMassiveWeakSolutionOn_untranslate` is NOT redeclared here.  The identical
statement is already proved in
`SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.WholeSpaceRowsCellTransport`, in this
same namespace, and redeclaring it made any module importing both fail to
elaborate.  That file is imported above; use its version, which takes `u`
explicitly. -/

/-- Translate a massive weak solution and all of its data to the shifted set. -/
theorem isMassiveWeakSolutionOn_translate {W : Set (Vec d)} (z : Vec d)
    {c rho : Vec d → ℝ} {mu : ℝ} {u : H1Function W} {f : Vec d → ℝ}
    (hu : IsMassiveWeakSolutionOn c rho mu W u f) :
    IsMassiveWeakSolutionOn (fun x ↦ c (x - z)) (fun x ↦ rho (x - z)) mu
      (translateSet z W) (u.translate z) (fun x ↦ f (x - z)) := by
  intro phi
  have hphi := hu (H10Function.untranslate z phi)
  simp only [H10Function.untranslate_toH1Function, H1Function.untranslate_toFun,
    H1Function.untranslate_grad] at hphi
  have hmass := setIntegral_comp_subRight_translateSet z W
    (fun x ↦ rho x * u.toFun x * phi.toH1Function.toFun (x + z))
  have henergy := setIntegral_comp_subRight_translateSet z W
    (fun x ↦ vecDot (c x • u.grad x) (phi.toH1Function.grad (x + z)))
  have hsource := setIntegral_comp_subRight_translateSet z W
    (fun x ↦ rho x * f x * phi.toH1Function.toFun (x + z))
  simp only [sub_add_cancel] at hmass henergy hsource
  simp only [H1Function.translate_toFun, H1Function.translate_grad]
  rw [hmass, henergy, hsource]
  exact hphi

/-- Recenter a residual lift with the same translation as its massive datum. -/
theorem isMassiveResidualLiftOn_untranslate {W : Set (Vec d)} (z : Vec d)
    {rho : Vec d → ℝ} {mu : ℝ}
    {u : H1Function (translateSet z W)} {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hg : IsMassiveResidualLiftOn rho mu (translateSet z W) u f g) :
    IsMassiveResidualLiftOn (fun x ↦ rho (x + z)) mu W
      (H1Function.untranslate z u) (fun x ↦ f (x + z)) (fun x ↦ g (x + z)) := by
  intro phi
  have hphi := hg (phi.translate z)
  simp only [H10Function.translate_toH1Function, H1Function.translate_toFun,
    H1Function.translate_grad] at hphi
  have hsource := setIntegral_comp_addRight_translateSet z W
    (fun x ↦ rho x * f x * phi.toH1Function.toFun (x - z))
  have hmass := setIntegral_comp_addRight_translateSet z W
    (fun x ↦ rho x * u.toFun x * phi.toH1Function.toFun (x - z))
  have hdiv := setIntegral_comp_addRight_translateSet z W
    (fun x ↦ vecDot (g x) (phi.toH1Function.grad (x - z)))
  simp only [add_sub_cancel_right] at hsource hmass hdiv
  simp only [H1Function.untranslate_toFun]
  rw [hsource, hmass, hdiv]
  exact hphi

/-- Translate a residual lift to the shifted massive equation. -/
theorem isMassiveResidualLiftOn_translate {W : Set (Vec d)} (z : Vec d)
    {rho : Vec d → ℝ} {mu : ℝ} {u : H1Function W}
    {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hg : IsMassiveResidualLiftOn rho mu W u f g) :
    IsMassiveResidualLiftOn (fun x ↦ rho (x - z)) mu (translateSet z W)
      (u.translate z) (fun x ↦ f (x - z)) (fun x ↦ g (x - z)) := by
  intro phi
  have hphi := hg (H10Function.untranslate z phi)
  simp only [H10Function.untranslate_toH1Function, H1Function.untranslate_toFun,
    H1Function.untranslate_grad] at hphi
  have hsource := setIntegral_comp_subRight_translateSet z W
    (fun x ↦ rho x * f x * phi.toH1Function.toFun (x + z))
  have hmass := setIntegral_comp_subRight_translateSet z W
    (fun x ↦ rho x * u.toFun x * phi.toH1Function.toFun (x + z))
  have hdiv := setIntegral_comp_subRight_translateSet z W
    (fun x ↦ vecDot (g x) (phi.toH1Function.grad (x + z)))
  simp only [sub_add_cancel] at hsource hmass hdiv
  simp only [H1Function.translate_toFun]
  rw [hsource, hmass, hdiv]
  exact hphi

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
