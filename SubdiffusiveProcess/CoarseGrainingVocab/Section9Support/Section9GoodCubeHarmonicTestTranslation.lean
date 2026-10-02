import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
import Homogenization.Sobolev.H1.Translation
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeReferenceGeometry
/-! Weak harmonicity and its full extended-real oscillation contraction transport with the coefficient, without assuming pointwise H1 representatives or finite oscillation. -/

set_option autoImplicit false
open Homogenization hiding Vec cubeSet
open MeasureTheory Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab
open scoped ENNReal
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
theorem goodCube_weakHarmonic_untranslate
    {d : ℕ} (z : Vec d) (U : Set (Vec d)) (a h : Vec d → ℝ)
    (hH : WeakHarmonic a (translateSet z U) h) :
    WeakHarmonic (fun x => a (x + z)) U (fun x => h (x + z))
:= by
  have hmem : ∀ x ∈ U, x + z ∈ translateSet z U :=
    fun x hx => ⟨x, hx, rfl⟩
  refine ⟨hH.1.comp (continuous_id.add continuous_const).continuousOn hmem, ?_⟩
  intro W hWo hWc hWU
  have hTopen : IsOpen (translateSet z W) := by
    rw [← preimage_subRight_eq_translateSet]
    exact hWo.preimage (continuous_id.sub continuous_const)
  have hclosure : closure (translateSet z W) = translateSet z (closure W) := by
    rw [← image_addRight_eq_translateSet, ← image_addRight_eq_translateSet]
    simpa only [one_smul, add_comm] using goodCube_affine_closure z (s := 1) one_ne_zero W
  have hTcompact : IsCompact (closure (translateSet z W)) := by
    rw [hclosure, ← image_addRight_eq_translateSet]
    exact hWc.image (continuous_id.add continuous_const)
  have hTU : closure (translateSet z W) ⊆ translateSet z U := by
    rw [hclosure]
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, hWU hy, rfl⟩
  obtain ⟨u, hu, hEq⟩ := hH.2 (translateSet z W) hTopen hTcompact hTU
  refine ⟨u.untranslate z, ?_, ?_⟩
  · exact (measurePreserving_addRight_restrict_translateSet z W).quasiMeasurePreserving.ae hu
  · intro phi
    have hI := setIntegral_comp_addRight_translateSet z W
      (fun x => a x * vecDot (u.grad x) ((phi.translate z).toH1Function.grad x))
    have hI' : (∫ x in W, a (x + z) *
        vecDot ((u.untranslate z).grad x) (phi.toH1Function.grad x)) =
        ∫ x in translateSet z W, a x *
          vecDot (u.grad x) ((phi.translate z).toH1Function.grad x) := by
      simpa only [H1Function.untranslate_grad, H10Function.translate_toH1Function,
        H1Function.translate_grad, add_sub_cancel_right] using hI
    exact hI'.trans (hEq (phi.translate z))

theorem goodCube_oscillation_untranslate
    {d : ℕ} (z : Vec d) (U : Set (Vec d)) (h : Vec d → ℝ) :
    oscillation U (fun x => h (x + z)) = oscillation (translateSet z U) h
:= by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.oscillation
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
    exact le_iSup_of_le (x + z) (le_iSup_of_le (show x + z ∈ translateSet z U from ⟨x, hx, rfl⟩)
      (le_iSup_of_le (y + z) (le_iSup_of_le (show y + z ∈ translateSet z U from ⟨y, hy, rfl⟩)
        le_rfl)))
  · refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
    obtain ⟨x0, hx0, rfl⟩ := hx
    obtain ⟨y0, hy0, rfl⟩ := hy
    exact le_iSup_of_le x0 (le_iSup_of_le hx0 (le_iSup_of_le y0 (le_iSup_of_le hy0 le_rfl)))

theorem goodCube_harmonicContraction_translate
    {d : ℕ} (z : Vec d) (S T : Set (Vec d)) (a : Vec d → ℝ) (eps : ℝ)
    (hcontract : ∀ h : Vec d → ℝ,
      WeakHarmonic (fun x => a (x + z)) T h →
        oscillation S h ≤ ENNReal.ofReal eps * oscillation T h) :
    ∀ h : Vec d → ℝ, WeakHarmonic a (translateSet z T) h →
      oscillation (translateSet z S) h ≤
        ENNReal.ofReal eps * oscillation (translateSet z T) h
:= by
  intro h hH
  have h0 := hcontract (fun x => h (x + z)) (goodCube_weakHarmonic_untranslate z T a h hH)
  simpa only [goodCube_oscillation_untranslate] using h0

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
