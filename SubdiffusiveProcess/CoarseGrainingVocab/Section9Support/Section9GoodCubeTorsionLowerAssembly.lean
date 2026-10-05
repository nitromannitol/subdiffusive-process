module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTorsionContinuous
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTorsionOscillation
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeTorsionReadout
@[expose] public section

set_option autoImplicit false
open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- A positive profile, local strict contraction and the actual Poisson corrections give pointwise exit lower bounds. -/
theorem goodCube_meanExit_lower_of_profile_and_local_contraction
    {d : ℕ} [NeZero d] (hd : 2 ≤ d) {ι : Type*}
    {c rho : Vec d → ℝ} {law : Kernel (Vec d) (Path d)}
    (hD : LocalDiffusionData c rho law)
    {U T : Set (Vec d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUconv : IsOpenBoundedConvexDomain U) (hc : ContinuousOn c U)
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam U (scalarCoeffField c))
    (inner outer : ι → Set (Vec d)) (hT : IsOpen T)
    (hcover : T ⊆ ⋃ i, inner i)
    (hinner : ∀ i, MeasurableSet (inner i))
    (hnested : ∀ i, inner i ⊆ outer i)
    (houter : ∀ i, IsOpen (outer i))
    (houterU : ∀ i, outer i ⊆ U)
    (g : Vec d → ℝ) {a b E eta eps k : ℝ}
    (hb : 0 < b) (hE : 0 ≤ E) (heta : 0 ≤ eta) (heps : 0 ≤ eps) (hk : 0 ≤ k)
    (hbudget : k ≤ a - b - (eps * (E + 2 * eta) + 2 * eta))
    (hmeanU : ∀ x ∈ U, meanExit law U x ≤ ENNReal.ofReal E)
    (hmeanOuter : ∀ i, ∀ x ∈ outer i, meanExit law (outer i) x ≤ ENNReal.ofReal eta)
    (hcontract : ∀ i, ∀ h : Vec d → ℝ, WeakHarmonic c (outer i) h →
      oscillation (inner i) h ≤ ENNReal.ofReal eps * oscillation (outer i) h)
    (hg : ∀ i, ∀ᵐ x ∂volume.restrict (inner i), a ≤ g x)
    (hcompare : ∀ u : H10Function U,
      IsMassiveWeakSolutionOn c rho 0 U u.toH1Function (fun _ => 1) →
        ∀ i, eLpNorm (fun x => u.toH1Function.toFun x - g x) 2 (volume.restrict U) <
          ENNReal.ofReal b * volume (inner i) ^ (1 / 2 : ℝ)) :
    ∀ x ∈ T, ENNReal.ofReal k ≤ meanExit law U x := by
  obtain ⟨u, h, hcont, hbounds, huhae, hmeanae, huSol⟩ :=
    goodCube_exists_continuous_h10_meanExit hd hD.1 hU hUb hUconv hc hlam hEll hE hmeanU
  have hTU : T ⊆ U := fun x hx => by
    obtain ⟨i, hi⟩ : ∃ i, x ∈ inner i := by simpa using hcover hx
    exact houterU i (hnested i hi)
  have hstep : ∀ i, ∀ x ∈ inner i, k ≤ h x := by
    intro i x hx
    have hoi := houter i
    have houb : Bornology.IsBounded (outer i) := hUb.subset (houterU i)
    have hEllO : IsEllipticFieldOn lam Lam (outer i) (scalarCoeffField c) :=
      hEll.mono hoi.measurableSet (houterU i)
    have hcontO : ContinuousOn c (outer i) := hc.mono (houterU i)
    let hP : H1Function (outer i) := u.toH1Function.restrict hoi (houterU i)
    have hPae : ∀ᵐ z ∂(volume.restrict (outer i)), hP.toFun z = h z :=
      ae_mono (Measure.restrict_mono (houterU i) le_rfl) huhae
    have hPsol : IsMassiveWeakSolutionOn c rho 0 (outer i) hP (fun _ => (1 : ℝ)) :=
      IsMassiveWeakSolutionOn.restrict hoi hU (houterU i) huSol
    obtain ⟨v, hvb, hwharm⟩ :=
      exists_harmonic_correction_of_bounded_forcing hd hD.1 hoi houb hcontO hlam hEllO
        (q := fun _ => (1 : ℝ)) measurable_const (hcont.mono (houterU i)) (K := (1 : ℝ)) (E := eta)
        (by norm_num) heta (by intro z _; simp) (hmeanOuter i) hPae hPsol
    have hvbi : ∀ z ∈ outer i, |v z| ≤ eta := by
      intro z hz; simpa using hvb z hz
    have hcontracti : oscillation (inner i) (fun y => h y - v y) ≤
        ENNReal.ofReal eps * oscillation (outer i) (fun y => h y - v y) :=
      hcontract i (fun y => h y - v y) hwharm
    have hdist : eLpNorm (fun x => h x - g x) 2 (volume.restrict U) <
        ENNReal.ofReal b * volume (inner i) ^ (1 / 2 : ℝ) := by
      have hnormEq : eLpNorm (fun x => h x - g x) 2 (volume.restrict U) =
          eLpNorm (fun x => u.toH1Function.toFun x - g x) 2 (volume.restrict U) := by
        apply eLpNorm_congr_ae
        filter_upwards [huhae] with y hy
        rw [hy]
      rw [hnormEq]
      exact hcompare u huSol i
    have hlow := goodCube_lower_of_l2_and_harmonic_correction
      (V := inner i) (W := outer i) (U := U) (hinner i) (hnested i) (houterU i)
      h g v hb hE heta heps
      (fun z hz => hbounds z (houterU i hz)) hvbi hcontracti (hg i) hdist
    exact le_trans hbudget (hlow x hx)
  refine goodCube_meanExit_lower_of_h10 hD hU hUb hT hTU u ?_ hk ?_
  · filter_upwards [huhae, hmeanae] with y hy1 hy2
    rw [hy1]; exact hy2
  · filter_upwards [huhae] with y hy hyT
    rw [hy]
    obtain ⟨i, hi⟩ : ∃ i, y ∈ inner i := by simpa using hcover hyT
    exact hstep i y hi

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
