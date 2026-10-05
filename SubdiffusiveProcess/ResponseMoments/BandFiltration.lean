module

public import SubdiffusiveProcess.ResponseMoments.Interfaces
public import SubdiffusiveProcess.Probability.LayerProductBlocks
public import Mathlib.Tactic

@[expose] public section

/-!
# The band filtration on the layer product

`bandSigma Y H` is the `σ`-field of the layers `|j| ≤ H`
(`mfd:lem-endpoints`).  Here it is identified
with the comap of the coordinate restriction, shown to be a filtration, and
shown to generate the whole product `σ`-field.
-/

open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

namespace SubdiffusiveProcess
namespace ResponseMoments

variable {Y : ℤ → Type} [instY : ∀ j, MeasurableSpace (Y j)]

/-- The band index set of radius `H`. -/
def bandSet (H : ℕ) : Set ℤ := Set.Icc (-(H : ℤ)) (H : ℤ)

theorem bandSigma_eq_comap (H : ℕ) :
    bandSigma Y H =
      (inferInstance : MeasurableSpace ((i : bandSet H) → Y i)).comap
        (bandSet H).domRestrict := by
  have h :
      (inferInstance : MeasurableSpace ((i : bandSet H) → Y i)).comap
        (bandSet H).domRestrict =
      ⨆ j ∈ bandSet H, (instY j).comap (fun w : (j : ℤ) → Y j => w j) :=
    comap_restrict_eq_iSup (X := Y) (bandSet H)
  rw [h]
  rfl

theorem bandSigma_le (H : ℕ) :
    bandSigma Y H ≤ (inferInstance : MeasurableSpace ((j : ℤ) → Y j)) := by
  refine iSup_le fun j => iSup_le fun _ => ?_
  exact (measurable_pi_apply j).comap_le

theorem bandSigma_mono : Monotone (fun H : ℕ => bandSigma Y H) := by
  intro a b hab
  refine iSup_le fun j => iSup_le fun hj => ?_
  have hj' : j ∈ Set.Icc (-(b : ℤ)) (b : ℤ) := by
    rcases hj with ⟨h1, h2⟩
    have : (a : ℤ) ≤ (b : ℤ) := by exact_mod_cast hab
    exact ⟨by omega, by omega⟩
  exact le_iSup₂ (f := fun (k : ℤ) (_ : k ∈ Set.Icc (-(b : ℤ)) (b : ℤ)) =>
    (instY k).comap fun ω : (j : ℤ) → Y j => ω k) j hj' 

/-- The band filtration. -/
def bandFiltration : Filtration ℕ (inferInstance : MeasurableSpace ((j : ℤ) → Y j)) :=
  ⟨fun H => bandSigma Y H, bandSigma_mono, bandSigma_le⟩

theorem iSup_bandFiltration :
    (⨆ H : ℕ, (bandFiltration (Y := Y)) H) =
      (inferInstance : MeasurableSpace ((j : ℤ) → Y j)) := by
  refine le_antisymm (iSup_le fun H => bandSigma_le H) ?_
  show (⨆ j : ℤ, (instY j).comap fun ω : (j : ℤ) → Y j => ω j) ≤ _
  refine iSup_le fun j => ?_
  obtain ⟨H, hH⟩ : ∃ H : ℕ, j ∈ Set.Icc (-(H : ℤ)) (H : ℤ) := by
    refine ⟨j.natAbs, ?_⟩
    rw [Set.mem_Icc]
    rcases Int.natAbs_eq j with h | h <;> omega
  refine le_trans ?_ (le_iSup (fun H : ℕ => (bandFiltration (Y := Y)) H) H)
  show _ ≤ bandSigma Y H
  exact le_iSup₂ (f := fun (k : ℤ) (_ : k ∈ Set.Icc (-(H : ℤ)) (H : ℤ)) =>
    (instY k).comap fun ω : (j : ℤ) → Y j => ω k) j hH

end ResponseMoments
end SubdiffusiveProcess
