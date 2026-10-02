import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation.BoundaryEnergy
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.ZeroTrace
import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.Windows
import Homogenization.Sobolev.H1.LocalizedZeroTrace
import Homogenization.Sobolev.H1.Algebra.H10Function
import Homogenization.Sobolev.H1.BasicLemmas

/-!
# Localizing an ambient zero trace to a boundary patch

An `H¹₀(Ω)` witness descends to an open subdomain `W` when the multiplier
window meets `Ω` only inside `W`.  This is the analytic half of the projected
boundary-cover construction in harmonic approximation.

PROVENANCE: ported from
`Algsuperdiff/Section4/Provider/ExcessDecay/BoundaryCoveringTrace.lean`.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation

open Homogenization Homogenization.Book Homogenization.Book.Ch03
  MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-- Restrict an `H¹₀` function whose smooth approximants are supported in the
smaller open set. -/
def h10RestrictOfApproxSupport {Ω W : Set (Vec d)} (hWopen : IsOpen W)
    (hWΩ : W ⊆ Ω) (u : H10Function Ω) (hsupp : ∀ n, tsupport (u.approx n) ⊆ W) :
    H10Function W where
  toH1Function := u.toH1Function.restrict hWopen hWΩ
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_support_subset := hsupp
  tendsto_approx := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      u.tendsto_approx (fun _ => zero_le _) fun n => ?_
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hWΩ)
  tendsto_approx_grad := by
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (u.tendsto_approx_grad i) (fun _ => zero_le _) fun n => ?_
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hWΩ)

@[simp] theorem h10RestrictOfApproxSupport_toFun {Ω W : Set (Vec d)}
    (hWopen : IsOpen W) (hWΩ : W ⊆ Ω) (u : H10Function Ω)
    (hsupp : ∀ n, tsupport (u.approx n) ⊆ W) :
    (h10RestrictOfApproxSupport hWopen hWΩ u hsupp).toH1Function.toFun =
      u.toH1Function.toFun := rfl

/-- A global zero trace gives localized zero trace through a window `V` when
`V ∩ Ω` lies inside the local domain `W`. -/
theorem localizedZeroTraceFunctionOn_of_memH10_of_inter_subset
    {Ω W V : Set (Vec d)} (hWopen : IsOpen W) (hWΩ : W ⊆ Ω)
    (hVW : V ∩ Ω ⊆ W) (u : H10Function Ω) :
    LocalizedZeroTraceFunctionOn W V u.toH1Function.toFun := by
  intro eta heta heta_compact heta_sub
  refine ⟨h10RestrictOfApproxSupport hWopen hWΩ
    (u.mulContDiffHasCompactSupport heta heta_compact) ?_, ?_⟩
  · intro n
    show tsupport (fun x => eta x * u.approx n x) ⊆ W
    intro p hp
    refine hVW ⟨heta_sub ?_, u.approx_support_subset n ?_⟩
    · exact tsupport_mul_subset_left (f := eta) (g := u.approx n) hp
    · exact tsupport_mul_subset_right (f := eta) (g := u.approx n) hp
  · rw [h10RestrictOfApproxSupport_toFun,
      H10Function.mulContDiffHasCompactSupport_toFun]

/-- Subtracting a local Dirichlet lift from an ambient Dirichlet solution gives
the localized zero trace required by boundary Caccioppoli.  The two exact
witnesses may use different domains; only the ambient witness needs the
support-localization argument above. -/
theorem localizedZeroTraceFunctionOn_sub_dirichletLift
    {Ω W V : Set (Vec d)} (hWopen : IsOpen W) (hWΩ : W ⊆ Ω)
    (hVW : V ∩ Ω ⊆ W) {u h v : Vec d → ℝ}
    (wu : H10Function Ω) (hu : ∀ y, wu.toH1Function.toFun y = u y - h y)
    (wv : H10Function W) (hv : ∀ y, wv.toH1Function.toFun y = v y - h y) :
    LocalizedZeroTraceFunctionOn W V (fun y => u y - v y) := by
  have hambient : LocalizedZeroTraceFunctionOn W V wu.toH1Function.toFun :=
    localizedZeroTraceFunctionOn_of_memH10_of_inter_subset hWopen hWΩ hVW wu
  have hlocal : LocalizedZeroTraceFunctionOn W V wv.toH1Function.toFun :=
    Section6SchauderDatum.localizedZeroTraceFunctionOn_of_memH10 ⟨wv, rfl⟩
  have hsub := Homogenization.localizedZeroTraceFunctionOn_sub hambient hlocal
  exact Section6SchauderDatum.localizedZeroTraceFunctionOn_congr
    (fun y => by rw [hu y, hv y]; ring) hsub

/-- Localized zero trace is covariant under pulling a translated domain back
to its origin frame. -/
theorem localizedZeroTraceFunctionOn_untranslate {U V : Set (Vec d)} (c : Vec d)
    {f : Vec d → ℝ}
    (h : LocalizedZeroTraceFunctionOn (translateSet c U) (translateSet c V) f) :
    LocalizedZeroTraceFunctionOn U V (fun y => f (y + c)) := by
  intro eta heta heta_compact heta_sub
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) fun y : Vec d => eta (y - c) :=
    heta.comp (contDiff_id.sub contDiff_const)
  have hcompact : HasCompactSupport fun y : Vec d => eta (y - c) := by
    simpa only [Function.comp_apply] using
      heta_compact.comp_homeomorph (Homeomorph.subRight c)
  have hsupp : tsupport (fun y : Vec d => eta (y - c)) ⊆ translateSet c V := by
    intro p hp
    have hp' : p - c ∈ tsupport eta := by
      have hcomp : (fun y : Vec d => eta (y - c)) =
          eta ∘ Homeomorph.subRight c := rfl
      rw [hcomp, tsupport_comp_eq_preimage eta (Homeomorph.subRight c)] at hp
      exact hp
    exact (mem_translateSet_iff_sub_mem).2 (heta_sub hp')
  obtain ⟨w, hw⟩ := h (fun y => eta (y - c)) hsmooth hcompact hsupp
  refine ⟨H10Function.untranslate c w, ?_⟩
  funext p
  rw [H10Function.untranslate_toH1Function, H1Function.untranslate_toFun, hw]
  change eta (p + c - c) * f (p + c) = eta p * f (p + c)
  rw [add_sub_cancel_right]

/-- The ambient zero-trace witness, localized to a well-placed cube and read
in that cube's origin frame. -/
theorem localizedZeroTraceFunctionOn_wellPlacedCube_untranslate
    {m k : ℤ} (x : Vec d) (hkm : k ≤ m)
    (rho : H10Function (openCubeSet (originCube d m))) :
    LocalizedZeroTraceFunctionOn (openCubeSet (originCube d k))
      (openCubeAtScale
        (x - Section6ExcessDecay.wellPlacedCentre x m k) (k - 1))
      (fun y => rho.toH1Function.toFun
        (y + Section6ExcessDecay.wellPlacedCentre x m k)) := by
  let c : Vec d := Section6ExcessDecay.wellPlacedCentre x m k
  have hW : translateSet c (openCubeSet (originCube d k)) = translatedCube d k c := by
    rw [translatedCube, cube,
      Section6SchauderDatum.image_add_eq_translateSet]
  have hV : translateSet c (openCubeAtScale (x - c) (k - 1)) =
      openCubeAtScale x (k - 1) := by
    ext p
    rw [mem_translateSet_iff_sub_mem]
    constructor
    · intro hp i
      have hi := hp i
      have heq : (p - c) i - (x - c) i = p i - x i := by
        simp only [Pi.sub_apply]
        ring
      rwa [heq] at hi
    · intro hp i
      have hi := hp i
      have heq : (p - c) i - (x - c) i = p i - x i := by
        simp only [Pi.sub_apply]
        ring
      rwa [heq]
  refine localizedZeroTraceFunctionOn_untranslate c ?_
  rw [hW, hV]
  have hWΩ : translatedCube d k c ⊆ openCubeSet (originCube d m) := by
    simpa [c, cube] using
      (Section6ExcessDecay.translatedCube_wellPlacedCentre_subset_cube x hkm)
  have hVW : openCubeAtScale x (k - 1) ∩ openCubeSet (originCube d m) ⊆
      translatedCube d k c := by
    intro p hp
    have hp' : p ∈ truncatedCube d m (k - 1) x := by
      refine ⟨?_, hp.2⟩
      rw [Section6ExcessDecay.mem_translatedCube_iff, cube,
        Homogenization.mem_openCubeSet_originCube_iff]
      intro i
      have hi := hp.1 i
      change |p i - x i| < Real.rpow 3 (((k - 1 : ℤ) : ℝ)) / 2 at hi
      have hpow : Real.rpow (3 : ℝ) (((k - 1 : ℤ) : ℝ)) =
          (3 : ℝ) ^ (k - 1) := Real.rpow_intCast 3 (k - 1)
      rw [hpow] at hi
      rw [Pi.sub_apply]
      rw [abs_lt] at hi
      constructor <;> linarith only [hi.1, hi.2]
    exact Section6ExcessDecay.truncatedCube_subset_translatedCube_wellPlacedCentre
      x hkm (by omega) hp'
  exact localizedZeroTraceFunctionOn_of_memH10_of_inter_subset
    (Section6ExcessDecay.isOpenBoundedConvexDomain_translatedCube d k c).isOpen
    hWΩ hVW rho

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicApproximation
