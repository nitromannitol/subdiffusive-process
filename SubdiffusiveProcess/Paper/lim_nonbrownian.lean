module

public import SubdiffusiveProcess.Paper.lim_thm_nonbrownian
public import SubdiffusiveProcess.Paper.physical_rescaling
public import SubdiffusiveProcess.Section10.LegacyPhysicalAttachment
public import SubdiffusiveProcess.Paper.in_crossing
public import SubdiffusiveProcess.Paper.in_J
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.in_extension
public import SubdiffusiveProcess.Paper.in_responses
public import SubdiffusiveProcess.Paper.in_6_16
public import SubdiffusiveProcess.Paper.in_iteration
public import SubdiffusiveProcess.Lane4.Inputs
public import SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
public import MarkovProcess.Path.ExitTime
public import SubdiffusiveProcess.Paper.lim_brownian_law
public import SubdiffusiveProcess.Main.DiffusionPath

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Paper



theorem lim_nonbrownian
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : Lane4.SobolevFoundationalInput d hd) (W : Lane4.SmallPerturbationInput d)
    (Cp : Lane4.CampanatoInput d) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg),
        M.delta ≤ delta0 → ∃ C eta : ℝ, 0 < C ∧ 0 < eta ∧
        (d = 2 → eta = SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P / Real.log 3) ∧
        (∀ l m : ℕ, l ≤ m →
          SubdiffusiveProcess.CoarseGrainingVocab.ahom M m / SubdiffusiveProcess.CoarseGrainingVocab.ahom M l ≤
            C * (3 : ℝ) ^ (-(eta * ((m : ℝ) - (l : ℝ))))) ∧
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
        (PN : ℕ → BilateralField d → SubMarkovKernelSemigroup (SpatialCoordinates d))
        (KN : ℕ → Kernel (BilateralField d × SpatialCoordinates d) (DiffusionPath d))
        (hKN : ∀ N, IsMarkovKernel (KN N))
        (hin : in_crossing M H PN KN)
        (L : ℕ → BilateralField d → Kernel (SpatialCoordinates d)
          (SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.Path d))
        (hL : ∀ N omega x,
          Measure.map MarkovProcess.LifetimePath.ofContinuousPath (KN N (omega, x)) =
            L N omega x)
        (hLloc : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ N,
          SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput.LocalDiffusion
            (cutoffCoefficient M H omega N) (cutoffSpeedDensity M H omega N) (L N omega))
        (phi : ℕ → ℕ) (hphi : StrictMono phi)
        (xs : ℕ → SpatialCoordinates d) (x : SpatialCoordinates d)
        (hxs : Tendsto xs atTop (𝓝 x))
        (Plim : ProbabilityMeasure (DiffusionPath d))
        (hPlim : ∀ G : BoundedContinuousFunction (DiffusionPath d) ℝ,
          Tendsto (fun n => ∫ omega, (∫ w, G w ∂(KN (phi n) (omega, xs n)))
              ∂(chaosSampleLaw M).toMeasure) atTop
            (𝓝 (∫ w, G w ∂(Plim : Measure (DiffusionPath d))))),
        -- `σ_k`: exit of `Z - Z_0` from the open cube `3^{-k} Q` (sup-norm ball of radius `3^{-k}/2`)
        (∀ k : ℕ, ∫⁻ w, ContinuousPath.exitTime
            (Metric.ball (w 0) ((3 : ℝ) ^ (-(k : ℤ)) / 2)) w ∂(Plim : Measure (DiffusionPath d)) ≤
          ENNReal.ofReal (C * (3 : ℝ) ^ (-((2 + eta) * (k : ℝ))))) ∧
        (∀ Q : Measure (DiffusionPath d), lim_brownian_law Q →
          (Plim : Measure (DiffusionPath d)) ⟂ₘ Q) ∧
        (∀ (Θ : Type) [MeasurableSpace Θ] (nu : Measure Θ) [IsProbabilityMeasure nu]
            (kappa : Kernel Θ (DiffusionPath d)), (∀ θ, lim_brownian_law (kappa θ)) →
          (Plim : Measure (DiffusionPath d)) ⟂ₘ nu.bind kappa) ∧
        ∀ Lam : Measure (ProbabilityMeasure (DiffusionPath d)), IsProbabilityMeasure Lam →
          (∀ G : BoundedContinuousFunction (DiffusionPath d) ℝ,
            Tendsto (fun n => ∫ omega, (∫ w, G w ∂(KN (phi n) (omega, xs n)))
                ∂(chaosSampleLaw M).toMeasure) atTop
              (𝓝 (∫ P, (∫ w, G w ∂(P : Measure (DiffusionPath d))) ∂Lam))) →
          ∀ᵐ (P : ProbabilityMeasure (DiffusionPath d)) ∂Lam,
            (∀ Q : Measure (DiffusionPath d), lim_brownian_law Q →
              (P : Measure (DiffusionPath d)) ⟂ₘ Q) ∧
            ∀ (Θ : Type) [MeasurableSpace Θ] (nu : Measure Θ) [IsProbabilityMeasure nu]
              (kappa : Kernel Θ (DiffusionPath d)), (∀ θ, lim_brownian_law (kappa θ)) →
              (P : Measure (DiffusionPath d)) ⟂ₘ nu.bind kappa := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨delta0, hdelta0, hmodels⟩ := lim_thm_nonbrownian hd
  refine ⟨delta0, hdelta0, ?_⟩
  intro M Rm Sreg It hM
  obtain ⟨eta, Cdecay, heta, hCdecay, hplanar, hdecay, Cexit, hCexit,
    hannealed, hrandom, _⟩ := hmodels M hM
  refine ⟨max Cdecay Cexit, eta, hCdecay.trans_le (le_max_left _ _), heta,
    hplanar, ?_, ?_⟩
  · intro l m hlm
    exact (hdecay l m hlm).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_pos_of_pos (by norm_num) _).le)
  · intro H hH PN KN hKN hin L hL hLloc phi hphi xs x hxs Plim hPlim
    obtain ⟨X, hX, hphysical, hphysicalLimit⟩ :=
      SubdiffusiveProcess.Section10.LegacyPhysicalAttachment.exists_annealed_limit
        aux_physical_rescaling_kernel_conjugacy_massive_unscale
        M H hH PN KN hKN hin phi xs Plim hPlim
    have hsource : aux_lim_thm_nonbrownian_IsAnnealedLimit M X true phi xs Plim :=
      hphysicalLimit
    obtain ⟨hexit, hsingular, hmixtures⟩ :=
      hannealed X hX hphysical true phi hphi xs x hxs Plim hsource
    refine ⟨?_, hsingular, hmixtures, ?_⟩
    · intro k
      exact (hexit k).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_pos_of_pos (by norm_num) _).le))
    · intro Lam hLam hbarycentre
      apply hrandom X hX hphysical true phi hphi xs Lam hLam
      intro G
      change Tendsto (fun n => ∫ omega,
        (∫ w, G (SubdiffusiveProcess.Section10.LegacyPhysicalAttachment.rescale M (phi n) w)
          ∂X ⊤ (omega, (3 : ℝ)^(phi n) • xs n))
        ∂(SubdiffusiveProcess.Section10.PhysicalAttachment.physicalLaw M).toMeasure) atTop _
      convert hbarycentre G using 1
      funext n
      exact SubdiffusiveProcess.Section10.LegacyPhysicalAttachment.top_annealed_integral
        aux_physical_rescaling_kernel_conjugacy_massive_unscale
        M H hH PN KN hKN hin X hX hphysical (phi n) (xs n) G

end Paper
