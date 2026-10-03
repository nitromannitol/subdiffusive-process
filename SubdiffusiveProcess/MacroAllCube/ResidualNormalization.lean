module

public import SubdiffusiveProcess.MacroAllCube.AhomDilation
public import SubdiffusiveProcess.MacroAllCube.ResidualModelData

@[expose] public section




open MeasureTheory SubdiffusiveProcess.Frozen.Assumptions

noncomputable section

namespace ResidualNormalization

variable {d : ℕ}

/-- **Exact normalization.**  The residual model has the same infinite-volume
homogenized coefficient as `M`, at every cutoff. -/
theorem ahom_residualModel (M : GMCModel d) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3)
    (hδ : M.delta ≤ (2 * ResidualModel.residualDisorderFactor d)⁻¹) (n : ℕ) :
    SubdiffusiveProcess.CoarseGrainingVocab.ahom (ResidualModel.residualModel M hs1 hs3 hδ) n =
      SubdiffusiveProcess.CoarseGrainingVocab.ahom M n :=
  AhomDilation.ahom_eq_of_seed_eq M _ (lt_of_lt_of_le one_pos hs1)
    (ResidualModel.residualModel_seed M hs1 hs3 hδ) n

/-- The literal `normalization` premise with `B = 1`. -/
theorem residualModel_normalization (M : GMCModel d) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3)
    (hδ : M.delta ≤ (2 * ResidualModel.residualDisorderFactor d)⁻¹) :
    ∀ n : ℕ,
      SubdiffusiveProcess.CoarseGrainingVocab.ahom (ResidualModel.residualModel M hs1 hs3 hδ) n /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M n ≤ 1 ∧
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M n /
          SubdiffusiveProcess.CoarseGrainingVocab.ahom (ResidualModel.residualModel M hs1 hs3 hδ) n ≤ 1 := by
  intro n
  rw [ahom_residualModel M hs1 hs3 hδ n]
  exact ⟨div_self_le_one _, div_self_le_one _⟩



def residualModelData (M : GMCModel d) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3)
    (hδ : M.delta ≤ (2 * ResidualModel.residualDisorderFactor d)⁻¹) :
    MacroAllCube.ResidualModelData d M s (ResidualModel.residualDisorderFactor d) where
  model := ResidualModel.residualModel M hs1 hs3 hδ
  disorder := le_of_eq (ResidualModel.residualModel_delta M hs1 hs3 hδ)
  seed_eq := ResidualModel.residualModel_seed M hs1 hs3 hδ
  B := 1
  B_ge_one := le_rfl
  normalization := residualModel_normalization M hs1 hs3 hδ

theorem residualModelData_B (M : GMCModel d) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3)
    (hδ : M.delta ≤ (2 * ResidualModel.residualDisorderFactor d)⁻¹) :
    (residualModelData M hs1 hs3 hδ).B = 1 := rfl

theorem residualModelData_model (M : GMCModel d) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3)
    (hδ : M.delta ≤ (2 * ResidualModel.residualDisorderFactor d)⁻¹) :
    (residualModelData M hs1 hs3 hδ).model = ResidualModel.residualModel M hs1 hs3 hδ := rfl



theorem exists_residualModelData (d : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (M : GMCModel d) (s : ℝ), 1 ≤ s → s ≤ 3 →
      M.delta ≤ (2 * D)⁻¹ →
      ∃ data : MacroAllCube.ResidualModelData d M s D, data.B = 1 :=
  ⟨ResidualModel.residualDisorderFactor d, ResidualModel.one_le_residualDisorderFactor d,
    fun M _s hs1 hs3 hδ => ⟨residualModelData M hs1 hs3 hδ, rfl⟩⟩

/-- **The normalization field is redundant**: every inhabitant of the interface
(for a positive dilation) has exactly the `ahom` of the original model. -/
theorem ResidualModelData.ahom_model_eq {M : GMCModel d} {s D : ℝ} (hs : 0 < s)
    (data : MacroAllCube.ResidualModelData d M s D) (n : ℕ) :
    SubdiffusiveProcess.CoarseGrainingVocab.ahom data.model n = SubdiffusiveProcess.CoarseGrainingVocab.ahom M n :=
  AhomDilation.ahom_eq_of_seed_eq M data.model hs data.seed_eq n

end ResidualNormalization





