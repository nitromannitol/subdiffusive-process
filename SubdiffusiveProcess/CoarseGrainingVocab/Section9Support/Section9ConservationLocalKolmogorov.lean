import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationProbabilityMoments

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open Homogenization hiding Vec
open MeasureTheory ProbabilityTheory MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open scoped ENNReal NNReal

theorem unitKolmogorov_of_centeredFourth {d : ℕ}
    (P : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)
    (K : NNReal) (E : NNReal → NNReal) (hE : Monotone E)
    (hmom : ∀ t x, (∫⁻ y, ENNReal.ofReal ((vecNormSq (y-x))^2) ∂P t x) ≤
      (K : ENNReal)*(t : ENNReal)^2*(E t : ENNReal)*ENNReal.ofReal ((1+vecNormSq x)^2))
    (x : Vec d) (n : ℕ) :
    ∃ M : NNReal, IsKolmogorovProcess
      (fun s : NNRat ↦ fun omega : DenseTime → Vec d ↦ omega ((n : NNRat)+min s 1))
      (denseTimeTrajectory P hP DenseTime.enumeration DenseTime.castOrderEmbedding.toEmbedding x) 4 2 M := by
  let iota := DenseTime.castOrderEmbedding.toEmbedding
  let kappa := denseTimeTrajectory P hP DenseTime.enumeration iota
  let U : NNReal := (n : NNReal)+1
  let M : NNReal := K*E 1*(8*(1+K*U^2*E U)*Real.toNNReal ((1+vecNormSq x)^2))
  refine ⟨M, IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun s ↦ measurable_pi_apply _) ?_ (by norm_num) (by norm_num)⟩
  have hordered (s t : DenseTime) (hst : s ≤ t) :
      (∫⁻ omega, edist (omega ((n : NNRat)+min s 1))
          (omega ((n : NNRat)+min t 1))^(4:ℝ) ∂kappa x) ≤ (M : ENNReal)*edist s t^(2:ℝ) := by
    let a : DenseTime := (n : NNRat)+min s 1
    let b : DenseTime := (n : NNRat)+min t 1
    let delta : NNReal := iota b-iota a
    have hab : a ≤ b := by dsimp only [a,b]; gcongr
    have hbounds := clipped_increment_bounds (n : NNReal) (iota s) (iota t)
      (DenseTime.castOrderEmbedding.monotone hst)
    have hd1 : delta ≤ 1 := by
      change DenseTime.castOrderEmbedding b-DenseTime.castOrderEmbedding a ≤ 1
      simpa only [a, b, cast_clipped_time] using hbounds.2.1
    have hd : delta ≤ iota t-iota s := by
      change DenseTime.castOrderEmbedding b-DenseTime.castOrderEmbedding a ≤ iota t-iota s
      simpa only [a, b, cast_clipped_time] using hbounds.2.2.1
    have haU : iota a ≤ U := by
      change DenseTime.castOrderEmbedding a ≤ U
      simpa only [a, U, cast_clipped_time] using hbounds.2.2.2
    have he1 : (E delta : ENNReal) ≤ (E 1 : ENNReal) := by exact_mod_cast hE hd1
    have hea : (E (iota a) : ENNReal) ≤ (E U : ENNReal) := by exact_mod_cast hE haU
    have haU' : (iota a : ENNReal) ≤ (U : ENNReal) := by exact_mod_cast haU
    have hmain := denseTime_fourth_increment_le P hP K E hmom x hab
    change (∫⁻ omega, edist (omega a) (omega b)^(4:ℝ) ∂kappa x) ≤
      (K : ENNReal)*(delta : ENNReal)^2*(E delta : ENNReal)*
        (8*(1+(K : ENNReal)*(iota a : ENNReal)^2*(E (iota a) : ENNReal))*
          ENNReal.ofReal ((1+vecNormSq x)^2)) at hmain
    calc
      _ ≤ (K : ENNReal)*(delta : ENNReal)^2*(E delta : ENNReal)*
          (8*(1+(K : ENNReal)*(iota a : ENNReal)^2*(E (iota a) : ENNReal))*
            ENNReal.ofReal ((1+vecNormSq x)^2)) := hmain
      _ ≤ (K : ENNReal)*(delta : ENNReal)^2*(E 1 : ENNReal)*
          (8*(1+(K : ENNReal)*(U : ENNReal)^2*(E U : ENNReal))*
            ENNReal.ofReal ((1+vecNormSq x)^2)) := by gcongr
      _ = (M : ENNReal)*(delta : ENNReal)^2 := by
        dsimp only [M]
        push_cast
        simp only [ENNReal.ofReal]
        ring
      _ ≤ (M : ENNReal)*edist s t^(2:ℝ) := by
        rw [DenseTime.edist_eq_castOrderEmbedding_sub hst, ENNReal.rpow_two]
        gcongr
        exact hd
  intro s t
  rcases le_total s t with hst | hts
  · exact hordered s t hst
  · simpa only [edist_comm] using hordered t s hts

theorem supportedOnContinuousPaths_of_centeredFourth {d : ℕ}
    (P : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)
    (K : NNReal) (E : NNReal → NNReal) (hE : Monotone E)
    (hmom : ∀ t x, (∫⁻ y, ENNReal.ofReal ((vecNormSq (y-x))^2) ∂P t x) ≤
      (K : ENNReal)*(t : ENNReal)^2*(E t : ENNReal)*ENNReal.ofReal ((1+vecNormSq x)^2)) :
    Kernel.IsSupportedOnContinuousPaths (denseTimeTrajectory P hP DenseTime.enumeration
      DenseTime.castOrderEmbedding.toEmbedding) := by
  apply supportedOnContinuousPaths_of_unitKolmogorov
  intro x n
  exact unitKolmogorov_of_centeredFourth P hP K E hE hmom x n

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
