module

public import SubdiffusiveProcess.CoarseGrainingVocab.NegativeBesovSupport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.PointwiseRangeDependence

@[expose] public section

namespace SubdiffusiveProcess

open MeasureTheory ProbabilityTheory Homogenization
open _root_.SubdiffusiveProcess.Model

noncomputable section

theorem integral_prod_exp_sub_tauSq_eq_one_of_separated
    {d : ℕ} (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (p : ℕ)
    (x : Fin p → Homogenization.Vec d)
    (hsep : Pairwise (fun i j : Fin p => Real.sqrt (d : ℝ) <
      Homogenization.euclideanNorm (x i - x j))) :
    (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
        ∏ i : Fin p, Real.exp (g (x i) - _root_.SubdiffusiveProcess.Model.tauSq M.P)
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) = 1 := by
  let : NeZero d := ⟨by
    have hd := M.shellPrefix.dimension
    omega⟩
  have hexists : ∃ eps : ℝ, 0 < eps ∧
      Pairwise (fun i j : Fin p =>
        SubdiffusiveProcess.CoarseGrainingVocab.PotentialRangeSeparated
          (Metric.ball (x i) eps) (Metric.ball (x j) eps)) := by
    classical
    by_cases hp : p ≤ 1
    · refine ⟨1, by norm_num, ?_⟩
      intro i j hij
      have hij' : i = j := by
        apply Fin.ext
        omega
      exact (hij hij').elim
    · have hp2 : 2 ≤ p := by omega
      let s : Finset (Fin p × Fin p) :=
        (Finset.univ.product Finset.univ).filter (fun ij => ij.1 ≠ ij.2)
      let margin : Fin p × Fin p → ℝ := fun ij =>
        (Homogenization.euclideanNorm (x ij.1 - x ij.2) - Real.sqrt (d : ℝ)) /
          (2 * (d : ℝ) + 2)
      have hs_nonempty : s.Nonempty := by
        let i₀ : Fin p := ⟨0, by omega⟩
        let i₁ : Fin p := ⟨1, by omega⟩
        refine ⟨(i₀, i₁), ?_⟩
        simp [s, i₀, i₁]
      have hmargin_pos : ∀ ij ∈ s, 0 < margin ij := by
        intro ij hij
        have hne : ij.1 ≠ ij.2 := by
          simpa [s] using hij
        dsimp [margin]
        exact div_pos (sub_pos.mpr (hsep hne)) (by positivity)
      let vals : Finset ℝ := s.image margin
      have hvals_nonempty : vals.Nonempty := hs_nonempty.image margin
      have hvals_pos : ∀ v ∈ vals, 0 < v := by
        intro v hv
        obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hv
        exact hmargin_pos ij hij
      let eps : ℝ := vals.min' hvals_nonempty
      have heps_pos : 0 < eps := by
        exact hvals_pos _ (Finset.min'_mem vals hvals_nonempty)
      refine ⟨eps, heps_pos, ?_⟩
      intro i j hij
      have hij' : (i, j) ∈ s := by
        simp [s, hij]
      have heps_le : eps ≤ margin (i, j) := by
        exact Finset.min'_le vals _ (Finset.mem_image.mpr ⟨(i, j), hij', rfl⟩)
      have hden : 0 < 2 * (d : ℝ) + 2 := by positivity
      have hmul : eps * (2 * (d : ℝ) + 2) ≤
          Homogenization.euclideanNorm (x i - x j) - Real.sqrt (d : ℝ) := by
        exact (le_div_iff₀ hden).mp heps_le
      apply SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.potentialRangeSeparated_ball
      calc
        Real.sqrt (d : ℝ) + 2 * (d : ℝ) * eps ≤
            Real.sqrt (d : ℝ) + (2 * (d : ℝ) + 2) * eps := by
              nlinarith [Nat.cast_nonneg (α := ℝ) d, heps_pos]
        _ ≤ Homogenization.euclideanNorm (x i - x j) := by
          nlinarith [hmul]
  obtain ⟨eps, heps_pos, hballs⟩ := hexists
  let U : Fin p → Set (Homogenization.Vec d) :=
    fun i => Metric.ball (x i) eps
  let X : ∀ i : Fin p,
      _root_.SubdiffusiveProcess.Model.PotentialField d → ℝ :=
    fun i g => Real.exp (g (x i) - _root_.SubdiffusiveProcess.Model.tauSq M.P)
  have hU : ∀ i, MeasurableSet (U i) := by
    intro i
    exact measurableSet_ball
  have hXlocal : ∀ i,
      @Measurable (_root_.SubdiffusiveProcess.Model.PotentialField d) ℝ
        (_root_.SubdiffusiveProcess.Model.PotentialField.localSigma (U i)) _ (X i) := by
    intro i
    have heval :=
      SubdiffusiveProcess.CoarseGrainingVocab.measurable_eval_potentialFieldLocalSigma_of_mem_isOpen
        (U := U i) Metric.isOpen_ball (Metric.mem_ball_self heps_pos)
    dsimp [X]
    exact (heval.sub measurable_const).exp
  have hInd : iIndepFun X
      (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
    exact SubdiffusiveProcess.CoarseGrainingVocab.iIndepFun_of_G1_of_potentialFieldLocal
      M hU (by simpa [U] using hballs) hXlocal
  have hfactor := hInd.integral_fun_prod_eq_prod_integral (fun i =>
    Measurable.aestronglyMeasurable
      ((hXlocal i).mono
        (SubdiffusiveProcess.CoarseGrainingVocab.potentialFieldLocalSigma_le_borel (U i)) le_rfl))
  calc
    (∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d,
        ∏ i : Fin p, Real.exp (g (x i) - _root_.SubdiffusiveProcess.Model.tauSq M.P)
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure) =
        ∏ i : Fin p, ∫ g : _root_.SubdiffusiveProcess.Model.PotentialField d, X i g
          ∂(_root_.SubdiffusiveProcess.Model.zeroPotentialLaw M.P).toMeasure := by
      simpa [X] using hfactor
    _ = 1 := by
      simp only [X]
      simp_rw [SubdiffusiveProcess.CoarseGrainingVocab.integral_exp_sub_tauSq_zeroPotential_apply_eq_one M]
      simp

end
end SubdiffusiveProcess
