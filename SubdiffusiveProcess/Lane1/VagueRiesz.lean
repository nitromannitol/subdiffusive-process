module

public import SubdiffusiveProcess.Lane1.VagueFunctional
public import SubdiffusiveProcess.Main.MeasuresConvergeLocally
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

@[expose] public section

/-!
# The vague limit measure

Once every test integral converges, the limiting functional is positive and
linear, and Riesz-Markov-Kakutani turns it into a measure whose integrals are
those limits -- which is exactly local weak convergence.
-/

open Filter MeasureTheory

open scoped CompactlySupported ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess

/-- **The vague limit exists.**  If every test integral converges along the
sequence, the limits are the integrals against one measure. -/
theorem exists_vague_limit
    {d : ℕ} (nuN : ℕ → Measure (SpatialCoordinates d))
    (hint : ∀ (N : ℕ) (f : C_c(SpatialCoordinates d, ℝ)),
      Integrable (f : SpatialCoordinates d → ℝ) (nuN N))
    (hconv : ∀ f : C_c(SpatialCoordinates d, ℝ),
      ∃ L : ℝ, Tendsto (fun N => ∫ x, f x ∂(nuN N)) atTop (nhds L)) :
    ∃ mu : Measure (SpatialCoordinates d), MeasuresConvergeLocally nuN mu := by
  classical
  set Lam : C_c(SpatialCoordinates d, ℝ) → ℝ :=
    fun f => limUnder atTop (fun N => ∫ x, f x ∂(nuN N)) with hLamdef
  have hLam : ∀ f : C_c(SpatialCoordinates d, ℝ),
      Tendsto (fun N => ∫ x, f x ∂(nuN N)) atTop (nhds (Lam f)) := by
    intro f
    obtain ⟨L, hL⟩ := hconv f
    have hEq : Lam f = L := hL.limUnder_eq
    rw [hEq]
    exact hL
  have hadd : ∀ f g : C_c(SpatialCoordinates d, ℝ), Lam (f + g) = Lam f + Lam g := by
    intro f g
    refine tendsto_nhds_unique (hLam (f + g)) ?_
    have hpt : ∀ N : ℕ, ∫ x, (f + g) x ∂(nuN N)
        = (∫ x, f x ∂(nuN N)) + ∫ x, g x ∂(nuN N) := by
      intro N
      simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
      exact integral_add (hint N f) (hint N g)
    simp only [hpt]
    exact (hLam f).add (hLam g)
  have hsmul : ∀ (c : ℝ) (f : C_c(SpatialCoordinates d, ℝ)),
      Lam (c • f) = c * Lam f := by
    intro c f
    refine tendsto_nhds_unique (hLam (c • f)) ?_
    have hpt : ∀ N : ℕ, ∫ x, (c • f) x ∂(nuN N)
        = c * ∫ x, f x ∂(nuN N) := by
      intro N
      simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply,
        smul_eq_mul]
      exact integral_const_mul c _
    simp only [hpt]
    exact (hLam f).const_mul c
  have hmono : Monotone Lam := by
    intro f g hfg
    refine le_of_tendsto_of_tendsto (hLam f) (hLam g) ?_
    filter_upwards with N
    refine integral_mono (hint N f) (hint N g) ?_
    intro x
    exact hfg x
  let Lm : C_c(SpatialCoordinates d, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := Lam
      map_add' := hadd
      map_smul' := by
        intro c f
        simpa using hsmul c f }
  let Lp : C_c(SpatialCoordinates d, ℝ) →ₚ[ℝ] ℝ :=
    { Lm with monotone' := hmono }
  refine ⟨RealRMK.rieszMeasure Lp, ?_⟩
  intro f
  have hval : ∫ x, f x ∂(RealRMK.rieszMeasure Lp) = Lam f :=
    RealRMK.integral_rieszMeasure Lp f
  rw [hval]
  exact hLam f

end SubdiffusiveProcess
