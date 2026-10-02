import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationPairGenerator
import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9ConservationCoupled

namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
open Homogenization hiding Vec contDiff_vecNormSq
open SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent
open Filter Topology MeasureTheory MarkovProcess MarkovProcess.Semigroup
open scoped ZeroAtInfty

theorem centeredNormSq_self {d : ℕ} (x : Vec d) : vecNormSq (x-x) = 0 := by
  simp [vecNormSq, vecDot]

theorem lintegral_centered_fourth_le_exp {d : ℕ} {c rho : Vec d → ℝ}
    (B : MassiveCubeBounds c rho) (hc : ContDiff ℝ 1 c) (hrho : Continuous rho)
    (D : C0ResolventDatum (Vec d)) (hdense : ∀ mu, DenseRange (D.operator mu))
    (hD : IsWeakEllipticResolvent c rho D) (hcnn : ∀ y, 0 ≤ c y)
    (hP : (D.fellerKernelSemigroup hdense).IsConservative)
    (x : Vec d) {C Bcap a : ℝ} (hC : 0 ≤ C) (hBcap : 0 ≤ Bcap) (ha : 1 ≤ a)
    (hquad : ∀ y, |coeffFluxDiv c (fun z ↦ vecNormSq (z-x)) y/rho y| ≤ C*(a+vecNormSq (y-x)))
    (hcap : ∀ y, c y/rho y ≤ Bcap*(a+vecNormSq (y-x))) (t : NNReal) :
    (∫⁻ y, ENNReal.ofReal ((vecNormSq (y-x))^2) ∂D.fellerKernelSemigroup hdense t x) ≤
      ENNReal.ofReal ((2*C+8*Bcap)*C*a^2*(t:ℝ)^2*Real.exp ((C+(2*C+8*Bcap))*(t:ℝ))) := by
  let P := D.fellerKernelSemigroup hdense
  let hF := D.isFellerKernelSemigroup_fellerKernelSemigroup hdense
  let mu := P t x
  letI : IsProbabilityMeasure mu := ⟨hP t x⟩
  let eps : ℕ → ℝ := fun n ↦ 1/((n:ℝ)+1)
  have heps : ∀ n, 0<eps n ∧ eps n≤1 := reciprocalNatSucc_pos_le_one
  have hex := fun n ↦ exists_distance_pair_generators B hc hrho D hdense hD hcnn x
    hC hBcap ha (heps n).1 (heps n).2 hquad hcap
  choose f g hf hg hLf hLg using hex
  let v : ℕ → Vec d → ℝ := fun n y ↦ (vecNormSq (y-x)/(1+eps n*vecNormSq (y-x)))^2
  have hi : ∀ n, Integrable (v n) mu := by
    intro n
    have h : Integrable (fun y ↦ ((eps n)⁻¹)^2+(g n : C₀(Vec d, ℝ)) y) mu :=
      (integrable_const _).add ((g n : C₀(Vec d, ℝ)).toBCF.integrable mu)
    exact h.congr (Eventually.of_forall (hg n))
  apply lintegral_ofReal_le_of_approximation mu v _ _ hi
  · intro n y
    exact sq_nonneg _
  · intro y
    exact (tendsto_distanceRegularization (vecNormSq (y-x))).pow 2
  · intro n
    have hfx : (eps n)⁻¹+(f n : C₀(Vec d, ℝ)) x = 0 := by
      rw [hf, centeredNormSq_self]
      norm_num
    have hgx : ((eps n)⁻¹)^2+(g n : C₀(Vec d, ℝ)) x = 0 := by
      rw [hg, centeredNormSq_self]
      norm_num
    have hcomp := affine_c0Semigroup_coupled_bound P hP hF (f n) (g n)
      (eps n)⁻¹ (((eps n)⁻¹)^2) C (2*C+8*Bcap) a hC (by positivity)
      (zero_le_one.trans ha) (hLf n) (hLg n) x hfx hgx t
    have hI : (∫ y, v n y ∂mu) = ((eps n)⁻¹)^2+hF.c0Semigroup t (g n) x := by
      calc
        _ = ∫ y, ((eps n)⁻¹)^2+(g n : C₀(Vec d, ℝ)) y ∂mu :=
          integral_congr_ae (Eventually.of_forall fun y ↦ (hg n y).symm)
        _ = ((eps n)⁻¹)^2+∫ y, (g n : C₀(Vec d, ℝ)) y ∂mu := by
          simpa only [one_mul] using integral_affine_c0 mu (g n) (((eps n)⁻¹)^2) 1
        _ = _ := rfl
    rw [hI]
    exact hcomp

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
