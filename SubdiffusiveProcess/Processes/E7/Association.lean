module

public import SubdiffusiveProcess.Processes.E7.DatumIdentification
public import SubdiffusiveProcess.Processes.E7.FellerFromResolvent
public import SubdiffusiveProcess.Processes.E7.Leaves

@[expose] public section

/-!
# The association of the path measure with the gradient form

For the realization `K` of the semigroup `P` whose Laplace transform is the weak elliptic `C₀`
resolvent datum `D`, the Laplace transform of `K` on continuous compactly supported data is
`ρ`-almost everywhere the resolvent of the gradient form (`D = G`).
-/
open MeasureTheory ProbabilityTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology CompactlySupported ZeroAtInfty
noncomputable section
namespace SubdiffusiveProcess.E7

variable {d : ℕ}

/-- The Laplace transform of the path measure is the datum. -/
theorem laplace_path_eq_datum
    (P : SubMarkovKernelSemigroup (Fin d → ℝ))
    (D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (Fin d → ℝ))
    (hlaplace : ∀ (mu : Semigroup.PositiveShift) (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ),
      D.solution mu f x = ∫ t in Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
        kernelIntegral (P (Real.toNNReal t)) f x)
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) [IsMarkovKernel K]
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x)
    (mu : Semigroup.PositiveShift) (g : C_c(Fin d → ℝ, ℝ)) (x : Fin d → ℝ) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
        ∫ w, g (w (Real.toNNReal t)) ∂(K x)) =
      D.solution mu (SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.compactSupportToC0 g) x := by
  rw [hlaplace]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [kernelIntegral_eq_path_integral P K hfdd _ x (Real.toNNReal t)]
  rfl

/-- **The association hypothesis of the part-process leaf holds for the gradient form.** -/
theorem association_of_datum [NeZero d]
    {c ρ : (Fin d → ℝ) → ℝ} (hc : Continuous c) (hρ : Continuous ρ)
    (hcpos : ∀ x, 0 < c x) (hρpos : ∀ x, 0 < ρ x)
    (P : SubMarkovKernelSemigroup (Fin d → ℝ))
    (D : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.C0ResolventDatum (Fin d → ℝ))
    (hweak : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsWeakEllipticResolvent c ρ D)
    (hlaplace : ∀ (mu : Semigroup.PositiveShift) (f : C₀(Fin d → ℝ, ℝ)) (x : Fin d → ℝ),
      D.solution mu f x = ∫ t in Ioi (0 : ℝ), Real.exp (-(mu : ℝ) * t) *
        kernelIntegral (P (Real.toNNReal t)) f x)
    (K : Kernel (Fin d → ℝ) (ContinuousPath (Fin d → ℝ))) [IsMarkovKernel K]
    (hfdd : ∀ I x, K.map (ContinuousPath.finsetEvaluation I) x =
      SubMarkovKernelSemigroup.finiteSetKernel P I x) :
    ∀ (μ : ℝ), 0 < μ → ∀ G : Lp ℝ 2 (wm ρ) →L[ℝ] Lp ℝ 2 (wm ρ),
      DirichletForm.IsResolvent (gradDirichletForm hc hρ hcpos hρpos).toClosedForm μ G →
        ∀ (g : (Fin d → ℝ) → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g)
          (hgL : MemLp g 2 (wm ρ)),
          (fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-μ * t) *
              ∫ w, g (w (Real.toNNReal t)) ∂(K x)) =ᵐ[wm ρ] ⇑(G (hgL.toLp g)) := by
  intro μ hμ G hG g hg hgc hgL
  let mu : Semigroup.PositiveShift := ⟨μ, hμ⟩
  let gcc : C_c(Fin d → ℝ, ℝ) := ⟨⟨g, hg⟩, hgc⟩
  have hgL' : MemLp (fun x => gcc x) 2 (wm ρ) := hgL
  have h := datum_eq_resolvent hc hρ hcpos hρpos hweak mu hG gcc hgL'
  refine ae_wm_of_ae_volume hρ hρpos ?_
  filter_upwards [h] with x hx
  have := laplace_path_eq_datum P D hlaplace K hfdd mu gcc x
  refine Eq.trans ?_ hx
  exact this

end SubdiffusiveProcess.E7
