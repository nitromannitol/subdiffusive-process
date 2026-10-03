module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLowerOccupationSolution

@[expose] public section




set_option autoImplicit false

open Homogenization MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open scoped ENNReal NNReal Topology

noncomputable section

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower

variable {d : ℕ}

/-- A locally `C^{1,1}` coefficient is continuous on its window: it is differentiable at
every point of `U`. -/
theorem continuousOn_of_coefficientC11On {U : Set (Vec d)} {a : Vec d → ℝ}
    (ha : CoefficientC11On U a) : ContinuousOn a U := by
  obtain ⟨Da, hDa, -⟩ := ha
  exact fun x hx => ((hDa x hx).differentiableAt.continuousAt).continuousWithinAt

/-- **Almost-everywhere bounds upgrade to pointwise bounds on an open set.**  If `a` is
continuous on the open set `W` and satisfies `lo ≤ a ≤ hi` almost everywhere on `W`, then it
satisfies them at every point of `W`: the failure set is open, and a nonempty open subset of
`Vec d` has positive Lebesgue measure. -/
theorem forall_mem_of_ae_of_continuousOn {W : Set (Vec d)} (hW : IsOpen W)
    {a : Vec d → ℝ} (ha : ContinuousOn a W) {lo hi : ℝ}
    (hae : ∀ᵐ x ∂(volume.restrict W), lo ≤ a x ∧ a x ≤ hi) :
    ∀ x ∈ W, lo ≤ a x ∧ a x ≤ hi := by
  have hnull : (volume.restrict W) {x | ¬ (lo ≤ a x ∧ a x ≤ hi)} = 0 := ae_iff.mp hae
  intro x hx
  by_contra hcon
  -- the failure set is relatively open in `W`, hence open
  set S : Set (Vec d) := {y | y ∈ W ∧ ¬ (lo ≤ a y ∧ a y ≤ hi)} with hS
  have hSopen : IsOpen S := by
    have hpre : IsOpen {r : ℝ | ¬ (lo ≤ r ∧ r ≤ hi)} := by
      have : {r : ℝ | ¬ (lo ≤ r ∧ r ≤ hi)} = (Set.Icc lo hi)ᶜ := by
        ext r; simp [Set.mem_Icc]
      rw [this]
      exact isClosed_Icc.isOpen_compl
    obtain ⟨V, hV, hVeq⟩ := (continuousOn_iff'.mp ha) _ hpre
    have hSV : S = V ∩ W := by
      rw [hS, ← hVeq]
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
      tauto
    rw [hSV]
    exact hV.inter hW
  have hSne : S.Nonempty := ⟨x, hx, hcon⟩
  have hpos : 0 < volume S := hSopen.measure_pos volume hSne
  have hsub : (volume.restrict W) S ≤ (volume.restrict W) {y | ¬ (lo ≤ a y ∧ a y ≤ hi)} :=
    measure_mono fun y hy => hy.2
  have hSW : (volume.restrict W) S = volume S := by
    rw [Measure.restrict_apply (hSopen.measurableSet)]
    congr 1
    exact Set.inter_eq_self_of_subset_left fun y hy => hy.1
  rw [hSW, hnull] at hsub
  exact absurd (le_antisymm hsub (zero_le)) hpos.ne'

/-- **The ellipticity carrier from the version-2 hypothesis.**  If `c` is `C^{1,1}` on `U`
and satisfies the `LocalDiffusion` coefficient clause, then on every open `W ⊆ U` with
compact closure inside a bounded set it is pointwise bounded between positive constants, and
the associated scalar matrix field is uniformly elliptic there. -/
theorem exists_isEllipticFieldOn_of_coefficientC11On {U W : Set (Vec d)} (hW : IsOpen W)
    (hWU : W ⊆ U) {a : Vec d → ℝ} (ha : CoefficientC11On U a) (haW : CoefficientOn W a) :
    ∃ lam Lam : ℝ, 0 < lam ∧
      IsEllipticFieldOn lam Lam W (scalarCoeffField a) := by
  classical
  obtain ⟨-, lo, hi, hlo, hbnd⟩ := haW
  have hcont : ContinuousOn a W := (continuousOn_of_coefficientC11On ha).mono hWU
  have hptw : ∀ x ∈ W, lo ≤ a x ∧ a x ≤ hi :=
    forall_mem_of_ae_of_continuousOn hW hcont hbnd
  refine ⟨lo, hi, hlo, ?_, ?_⟩
  · have hpiece : Measurable (W.piecewise a fun _ => (0 : ℝ)) :=
      hcont.measurable_piecewise continuous_const.continuousOn hW.measurableSet
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    by_cases hij : i = j
    · subst hij
      simpa [Set.piecewise, scalarCoeffField, Homogenization.scalarMatrix] using! hpiece
    · have hzero : (fun x : Vec d => if x ∈ W then scalarCoeffField a x i j else 0)
          = fun _ => (0 : ℝ) := by
        funext x
        simp [scalarCoeffField, Homogenization.scalarMatrix, hij]
      rw [hzero]
      exact measurable_const
  · intro x hx
    have hax : 0 < a x := lt_of_lt_of_le hlo (hptw x hx).1
    exact (Homogenization.isEllipticMatrix_scalarMatrix hax).mono hlo
      (hptw x hx).1 (hptw x hx).2

end SubdiffusiveProcess.CoarseGrainingVocab.Section8Support.LocalKilledLower
