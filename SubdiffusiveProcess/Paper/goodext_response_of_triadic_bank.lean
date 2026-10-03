module

public import SubdiffusiveProcess.Paper.goodext_partition_trace_of_eventual_uniform_bank
public import SubdiffusiveProcess.Paper.inputs_classical_triadic_boundary_partitions
public import SubdiffusiveProcess.DirichletForm.BoundaryRefinementResponse

@[expose] public section

/-! A shared actual triadic minimizer bank gives continuous traces on every contained cube.
The coefficient bounds and minimizer compactness are explicit inputs. -/
open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper

/-- A countable shared bank with summable energy costs supplies every contained cube's trace response. -/
theorem goodext_response_of_triadic_bank
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (S : ResponseSpace (centeredCube z r hr))
    (hS : S.space = killedSobolevGraph (centeredCube z r hr))
    (a : ℕ → PositiveCoefficient (centeredCube z r hr))
    (A : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a)
    (c : ℕ → SpatialCoordinates d → ℝ) (hc : ∀ n, Continuous (c n))
    (hell : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), lam ≤ c n x ∧ c n x ≤ Lam)
    (hrep : ∀ n, (a n).val =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] c n)
    (t alpha : ℝ) (ha : 0 < alpha)
    (hcell : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr c t alpha)
    (GN : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (G : DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr))
    (hGN : ∀ n f, GN n f =
      (responseSolution S (a n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1)
    (hConv : Tendsto GN atTop (𝓝 G))
    (E : DirichletForm.ClosedForm (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hE : ∀ u, E.energy u = limitFormEnergy G u)
    (hcont : ∀ f : DomainL2 (centeredCube z r hr),
      (∃ fc : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ fc ∧ HasCompactSupport fc ∧
        tsupport fc ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
        (f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] fc) →
      ∃ U : SpatialCoordinates d → ℝ,
        ContinuousOn U (closure (centeredCube z r hr : Set (SpatialCoordinates d))) ∧
        (G f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] U ∧
        ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), U x = 0)
    (Gamma : DirichletForm.EnergyMeasure E)
    [NeZero d]
    (minLevel : ℕ) (s H A0 : ℝ) (hs : (d : ℝ) - 1 < s) (hH : 0 ≤ H) (hA0 : 0 ≤ A0)
    (g : SpatialCoordinates d → ℝ)
    (hg0 : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), g x = 0)
    (b : ∀ q : {q : TriadicGridLabel d // minLevel ≤ q.1},
      ℕ → PositiveCoefficient (triadicGridCell z r hr q.val))
    (hab : ∀ q n, (a n).val =ᵐ[volume.restrict
      (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))] (b q n).val)
    (u : ∀ q : {q : TriadicGridLabel d // minLevel ≤ q.1},
      ℕ → weakSobolevGraph (triadicGridCell z r hr q.val))
    (U : {q : TriadicGridLabel d // minLevel ≤ q.1} → ℕ → SpatialCoordinates d → ℝ)
    (Vcell : {q : TriadicGridLabel d // minLevel ≤ q.1} → SpatialCoordinates d → ℝ)
    (hUc : ∀ q n, ContinuousOn (U q n)
      (closure (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))))
    (hUr : ∀ q n, ((u q n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))] U q n)
    (hUt : ∀ q n x, x ∈ frontier (triadicGridCell z r hr q.val : Set (SpatialCoordinates d)) → U q n x = g x)
    (hlimit : ∀ q, TendstoUniformlyOn (U q) (Vcell q) atTop
      (closure (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))))
    (hEnergy : ∀ q, ∀ᶠ n in atTop,
      sobolevCoefficientForm (b q n) (u q n).val (u q n).val ≤ A0 * (triadicGridSide r q.val) ^ s)
    (hOsc : ∀ q n x, x ∈ closure (triadicGridCell z r hr q.val : Set (SpatialCoordinates d)) →
      |U q n x - g x| ≤ H * (triadicGridSide r q.val) ^ alpha) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (w : SpatialCoordinates d) (R : ℝ), 0 < R →
      Metric.ball w (R / 2) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      (Gamma.continuousTraceValues (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
        (Metric.ball w (R / 2)) g).Nonempty ∧
      IsGLB (Gamma.continuousTraceValues (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
        (Metric.ball w (R / 2)) g)
        (sInf (Gamma.continuousTraceValues (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
          (Metric.ball w (R / 2)) g)) ∧
      sInf (Gamma.continuousTraceValues (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
        (Metric.ball w (R / 2)) g) ≤ K * R ^ s := by
  classical
  obtain ⟨C, hC, hPartition⟩ := inputs_classical_triadic_boundary_partitions s hs z r hr minLevel
  refine ⟨A0 * C, mul_nonneg hA0 hC.le, ?_⟩
  intro w R hR hsub
  obtain ⟨P⟩ := hPartition w R hR hsub
  let q : (n : ℕ) → Fin (P.count n) → {q : TriadicGridLabel d // minLevel ≤ q.1} :=
    fun n i => ⟨P.label n i, P.depth_ge n i⟩
  have hBank (n : ℕ) := goodext_partition_trace_of_eventual_uniform_bank hd z r hr S hS a A
    c hc hell hrep t alpha ha hcell GN G hGN hConv E hE hcont Gamma
    (P.count n) (fun i => triadicGridCenter z r (P.label n i))
    (fun i => triadicGridSide r (P.label n i))
    (fun i => triadicGridSide_pos hr (P.label n i))
    (fun i => triadicGridCell_subset z hr (P.label n i))
    (P.disjoint n) (P.cover n) (P.cover_ae n) g hg0
    (fun k i => b (q n i) k) (fun k i => hab (q n i) k)
    (fun i => u (q n i)) (fun i => U (q n i))
    (fun i => hUc (q n i)) (fun i => hUr (q n i)) (fun i => hUt (q n i))
    (fun i => Vcell (q n i)) (fun i => hlimit (q n i))
    (fun i => A0 * (triadicGridSide r (P.label n i)) ^ s)
    (fun i => H * (triadicGridSide r (P.label n i)) ^ alpha)
    (fun i => mul_nonneg hA0 (Real.rpow_nonneg (triadicGridSide_pos hr _).le _))
    (fun i => hEnergy (q n i)) (fun i => hOsc (q n i))
  choose v V hv hVc hVr hEq hVOsc hCaps using hBank
  let Vall : TriadicGridLabel d → SpatialCoordinates d → ℝ := fun q =>
    if hq : minLevel ≤ q.1 then Vcell ⟨q, hq⟩ else g
  have hEqAll : ∀ n i, EqOn (V n) (Vall (P.label n i))
      (closure (triadicGridCell z r hr (P.label n i) : Set (SpatialCoordinates d))) := by
    intro n i
    simpa only [Vall, dif_pos (P.depth_ge n i)] using! hEq n i
  have hTotal : ∀ n, E.form (v n) (v n) ≤ A0 * ∑ i, (triadicGridSide r (P.label n i)) ^ s := by
    intro n
    have hcap := hCaps n Set.univ isOpen_univ
      (fun i => A0 * (triadicGridSide r (P.label n i)) ^ s)
      (fun i => mul_nonneg hA0 (Real.rpow_nonneg (triadicGridSide_pos hr _).le _))
      (fun _ _ => le_rfl)
    rw [Gamma.measure_univ (v n) (hv n)] at hcap
    simpa only [Finset.mul_sum] using hcap
  have hLocal : ∀ n, (Gamma.measure (v n) (Metric.ball w (R / 2))).toReal ≤ A0 * ∑ i,
      if ((triadicGridCell z r hr (P.label n i) : Set (SpatialCoordinates d)) ∩ Metric.ball w (R / 2)).Nonempty
      then (triadicGridSide r (P.label n i)) ^ s else 0 := by
    intro n
    let cap : Fin (P.count n) → ℝ := fun i =>
      if ((triadicGridCell z r hr (P.label n i) : Set (SpatialCoordinates d)) ∩ Metric.ball w (R / 2)).Nonempty
      then A0 * (triadicGridSide r (P.label n i)) ^ s else 0
    have hcap0 : ∀ i, 0 ≤ cap i := by
      intro i
      dsimp only [cap]
      split_ifs
      · exact mul_nonneg hA0 (Real.rpow_nonneg (triadicGridSide_pos hr _).le _)
      · exact le_rfl
    have hcap := hCaps n (Metric.ball w (R / 2)) Metric.isOpen_ball cap hcap0
      (fun i hi => by
        change ((triadicGridCell z r hr (P.label n i) : Set (SpatialCoordinates d)) ∩
          Metric.ball w (R / 2)).Nonempty at hi
        simp only [cap, if_pos hi, le_refl])
    refine hcap.trans_eq ?_
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [cap]
    split_ifs <;> simp only [mul_zero]
  exact Gamma.continuousTraceValues_of_boundary_refinement z r hr
    (Metric.ball w (R / 2)) Metric.isOpen_ball.measurableSet R s C hR minLevel P
    alpha H A0 ha hH hA0 g v hv V hVc hVr Vall hEqAll
    (fun n i => (hVOsc n i).2) hTotal hLocal

end Paper
