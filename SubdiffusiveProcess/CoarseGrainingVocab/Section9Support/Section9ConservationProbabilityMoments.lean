import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationMomentAlgebra
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationContinuousSupport
import MarkovProcess.DenseTime.TwoPointMarginals

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open Homogenization hiding Vec
open MeasureTheory ProbabilityTheory MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open scoped ENNReal NNReal

theorem compProd_prodMkLeft_apply {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (kappa : Kernel A B) [IsSFiniteKernel kappa]
    (eta : Kernel B C) [IsSFiniteKernel eta] (x : A) :
    (kappa ⊗ₖ Kernel.prodMkLeft A eta) x = (kappa x) ⊗ₘ eta := by
  ext s hs
  rw [Kernel.compProd_apply hs, Measure.compProd_apply hs]
  simp only [Kernel.prodMkLeft_apply]
theorem lintegral_quadraticSquare_of_centeredFourth {d : ℕ}
    (P : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)
    (K : NNReal) (E : NNReal → NNReal)
    (hmom : ∀ t x, (∫⁻ y, ENNReal.ofReal ((vecNormSq (y-x))^2) ∂P t x) ≤
      (K : ENNReal)*(t : ENNReal)^2*(E t : ENNReal)*ENNReal.ofReal ((1+vecNormSq x)^2))
    (t : NNReal) (x : Vec d) :
    (∫⁻ y, ENNReal.ofReal ((1+vecNormSq y)^2) ∂P t x) ≤
      8*(1+(K : ENNReal)*(t : ENNReal)^2*(E t : ENNReal))*ENNReal.ofReal ((1+vecNormSq x)^2) := by
  calc
    _ ≤ ∫⁻ y, 8*(ENNReal.ofReal ((1+vecNormSq x)^2)+
        ENNReal.ofReal ((vecNormSq (y-x))^2)) ∂P t x :=
      lintegral_mono (ofReal_quadratic_square_translate_le x)
    _ = 8*(ENNReal.ofReal ((1+vecNormSq x)^2)+
        ∫⁻ y, ENNReal.ofReal ((vecNormSq (y-x))^2) ∂P t x) := by
      rw [lintegral_const_mul _ (measurable_const.add (measurable_ofReal_centeredQuartic x)),
        lintegral_add_left measurable_const, lintegral_const, hP t x, mul_one]
    _ ≤ 8*(ENNReal.ofReal ((1+vecNormSq x)^2)+
        (K : ENNReal)*(t : ENNReal)^2*(E t : ENNReal)*ENNReal.ofReal ((1+vecNormSq x)^2)) := by
      gcongr
      exact hmom t x
    _ = _ := by ring

theorem denseTime_fourth_increment_le {d : ℕ}
    (P : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)
    (K : NNReal) (E : NNReal → NNReal)
    (hmom : ∀ t x, (∫⁻ y, ENNReal.ofReal ((vecNormSq (y-x))^2) ∂P t x) ≤
      (K : ENNReal)*(t : ENNReal)^2*(E t : ENNReal)*ENNReal.ofReal ((1+vecNormSq x)^2))
    (x : Vec d) {s t : DenseTime} (hst : s ≤ t) :
    let iota := DenseTime.castOrderEmbedding.toEmbedding
    let delta := iota t-iota s
    (∫⁻ omega, edist (omega s) (omega t)^(4:ℝ)
      ∂denseTimeTrajectory P hP DenseTime.enumeration iota x) ≤
      (K : ENNReal)*(delta : ENNReal)^2*(E delta : ENNReal)*
        (8*(1+(K : ENNReal)*(iota s : ENNReal)^2*(E (iota s) : ENNReal))*
          ENNReal.ofReal ((1+vecNormSq x)^2)) := by
  let iota := DenseTime.castOrderEmbedding.toEmbedding
  let delta := iota t-iota s
  rcases hst.eq_or_lt with rfl | hst
  · simp
  have hlt : iota s < iota t := DenseTime.castOrderEmbedding.strictMono hst
  letI : IsFiniteKernel (P (iota s)) := (P.isSubMarkovKernel (iota s)).isFiniteKernel
  letI : IsFiniteKernel (P delta) := (P.isSubMarkovKernel delta).isFiniteKernel
  have hF : Measurable (fun z : Vec d × Vec d ↦ edist z.1 z.2^(4:ℝ)) :=
    measurable_edist.pow_const 4
  have hev : Measurable (fun omega : DenseTime → Vec d ↦ (omega s, omega t)) := by fun_prop
  have hmapint :
      (∫⁻ z, edist z.1 z.2^(4:ℝ) ∂(denseTimeTrajectory P hP DenseTime.enumeration iota x).map
        (fun omega ↦ (omega s, omega t))) =
      ∫⁻ omega, edist (omega s) (omega t)^(4:ℝ)
        ∂denseTimeTrajectory P hP DenseTime.enumeration iota x := lintegral_map hF hev
  have hlaw : (denseTimeTrajectory P hP DenseTime.enumeration iota x).map
      (fun omega ↦ (omega s, omega t)) = (P (iota s) x) ⊗ₘ P delta := by
    rw [← Kernel.map_apply _ hev,
      denseTimeTrajectory_map_pair P hP DenseTime.enumeration iota hlt,
      compProd_prodMkLeft_apply]
  have hinner (y : Vec d) : (∫⁻ z, edist y z^(4:ℝ) ∂P delta y) ≤
      (K : ENNReal)*(delta : ENNReal)^2*(E delta : ENNReal)*ENNReal.ofReal ((1+vecNormSq y)^2) :=
    (lintegral_mono (edist_rpow_four_le_vecNormSq y)).trans (hmom delta y)
  dsimp only
  rw [← hmapint, hlaw, Measure.lintegral_compProd hF]
  calc
    _ ≤ ∫⁻ y, (K : ENNReal)*(delta : ENNReal)^2*(E delta : ENNReal)*
        ENNReal.ofReal ((1+vecNormSq y)^2) ∂P (iota s) x := lintegral_mono hinner
    _ = (K : ENNReal)*(delta : ENNReal)^2*(E delta : ENNReal)*
        (∫⁻ y, ENNReal.ofReal ((1+vecNormSq y)^2) ∂P (iota s) x) :=
      lintegral_const_mul _ measurable_ofReal_quadraticSquare
    _ ≤ _ := mul_le_mul_right (lintegral_quadraticSquare_of_centeredFourth P hP K E hmom (iota s) x) _

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
