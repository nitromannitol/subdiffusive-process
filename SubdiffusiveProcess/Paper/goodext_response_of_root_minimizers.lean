import SubdiffusiveProcess.Paper.goodext_response_of_triadic_bank
import SubdiffusiveProcess.Paper.goodext_countable_harmonic_trace_bank
import SubdiffusiveProcess.Paper.goodext_dirichlet_response_bound
import SubdiffusiveProcess.Sobolev.HolderTraceScaling
import SubdiffusiveProcess.Sobolev.MinimizerDatumOscillation
import SubdiffusiveProcess.Sobolev.HolderCubeOscillation




open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff BigOperators
noncomputable section
namespace Paper
/-- Actual root-cell minimizers and eventual coefficient caps supply every contained cube's response. -/
theorem goodext_response_of_root_minimizers
    {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (X : in_extension d hd I) (Sob : SubdiffusiveProcess.Lane4.SobolevFoundationalInput d hd) (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
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
    (minLevel : ℕ) (beta eta K : ℝ) (hb : beta ∈ Ioo (1 / 2 : ℝ) 1)
    (hba : beta ≤ alpha) (hEta : 1 + eta < 2 * alpha) (hK : 0 ≤ K)
    (hSide : ∀ q : {q : TriadicGridLabel d // minLevel ≤ q.1}, triadicGridSide r q.val ≤ 1)
    (g : SpatialCoordinates d → ℝ)
    (hgc : ContinuousOn g (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hgh : IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) g)
    (hg0 : ∀ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), g x = 0)
    (b : ∀ q : {q : TriadicGridLabel d // minLevel ≤ q.1},
      ℕ → PositiveCoefficient (triadicGridCell z r hr q.val))
    (hab : ∀ q n, (a n).val =ᵐ[volume.restrict
      (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))] (b q n).val)
    (hReg : ∀ q : {q : TriadicGridLabel d // minLevel ≤ q.1}, ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ datum : weakSobolevGraph (centeredCube (triadicGridCenter z r q.val) (triadicGridSide r q.val) (triadicGridSide_pos hr q.val)),
        ((datum.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (triadicGridCenter z r q.val) (triadicGridSide r q.val) (triadicGridSide_pos hr q.val) : Set (SpatialCoordinates d))] phi) →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
          ContinuousOn V (closure (centeredCube (triadicGridCenter z r q.val) (triadicGridSide r q.val) (triadicGridSide_pos hr q.val) : Set (SpatialCoordinates d))) ∧
          ((dirichletMinimizer (killedResponseSpace (centeredCube_killedPoincare (triadicGridCenter z r q.val) (triadicGridSide_pos hr q.val)))
            (b q n) datum).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (centeredCube (triadicGridCenter z r q.val) (triadicGridSide r q.val) (triadicGridSide_pos hr q.val) : Set (SpatialCoordinates d))] V ∧
          IsHolderOn alpha (closure (centeredCube (triadicGridCenter z r q.val) (triadicGridSide r q.val) (triadicGridSide_pos hr q.val) : Set (SpatialCoordinates d))) V ∧
          cAlphaNorm alpha (closure (centeredCube (triadicGridCenter z r q.val) (triadicGridSide r q.val) (triadicGridSide_pos hr q.val) : Set (SpatialCoordinates d))) V ≤ C)
    (hLam : ∀ q : {q : TriadicGridLabel d // minLevel ≤ q.1}, ∀ᶠ n in atTop,
      I.Lam (triadicGridCenter z r q.val) (triadicGridSide r q.val) (triadicGridSide_pos hr q.val)
        (b q n) (triadicGridCenter z r q.val) (triadicGridSide r q.val) ((beta - 1 / 2) / 4) 2 ≤
          K * (triadicGridSide r q.val) ^ (-eta)) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ (w : SpatialCoordinates d) (R : ℝ), 0 < R →
      Metric.ball w (R / 2) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) →
      (Gamma.continuousTraceValues (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
        (Metric.ball w (R / 2)) g).Nonempty ∧
      IsGLB (Gamma.continuousTraceValues (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
        (Metric.ball w (R / 2)) g)
        (sInf (Gamma.continuousTraceValues (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
          (Metric.ball w (R / 2)) g)) ∧
      sInf (Gamma.continuousTraceValues (closure (centeredCube z r hr : Set (SpatialCoordinates d)))
        (Metric.ball w (R / 2)) g) ≤ K0 * R ^ ((d : ℝ) - 2 + 2 * alpha - eta) := by
  classical
  obtain ⟨C, hC, hResponseBound⟩ :=
    goodext_dirichlet_response_bound d hd I X Sob beta hb
  let T : ℝ := (Real.sqrt d) ^ (alpha - beta) *
    holderSeminorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) g
  let H : ℝ := (Real.sqrt d) ^ alpha *
    holderSeminorm alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) g
  have hT : 0 ≤ T := by
    dsimp only [T]
    exact mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      (SubdiffusiveProcess.holderSeminorm_nonneg _ _ _)
  have hH : 0 ≤ H := by
    dsimp only [H]
    exact mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
      (SubdiffusiveProcess.holderSeminorm_nonneg _ _ _)
  let J : Type := {q : TriadicGridLabel d // minLevel ≤ q.1}
  let localLam : J → ℕ → ℝ := fun q n =>
    I.Lam (triadicGridCenter z r q.val) (triadicGridSide r q.val)
      (triadicGridSide_pos hr q.val) (b q n)
      (triadicGridCenter z r q.val) (triadicGridSide r q.val)
      ((beta - 1 / 2) / 4) 2
  let localTrace : J → ℝ := fun q =>
    (triadicGridSide r q.val) ^ beta *
      holderSeminorm beta
        (frontier (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))) g
  let Ebound : J → ℕ → ℝ := fun q n =>
    C * localLam q n * (triadicGridSide r q.val) ^ ((d : ℝ) - 2) *
      (localTrace q) ^ 2
  have hcellClosure : ∀ q : J,
      closure (triadicGridCell z r hr q.val : Set (SpatialCoordinates d)) ⊆
        closure (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    intro q
    exact closure_mono (triadicGridCell_subset z hr q.val)
  have hscaled : ∀ q : J,
      IsHolderOn beta (frontier (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))) g ∧
        localTrace q ≤ T * (triadicGridSide r q.val) ^ alpha := by
    intro q
    have hfront :
        frontier (Metric.ball (triadicGridCenter z r q.val)
          (triadicGridSide r q.val / 2)) ⊆
          closure (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      simpa only [triadicGridCell, centeredCube] using
        (frontier_subset_closure.trans (hcellClosure q))
    have hscale := scaled_holderSeminorm_frontier_le
      (triadicGridCenter z r q.val) (triadicGridSide r q.val)
      (triadicGridSide_pos hr q.val) hba hfront hgh
    constructor
    · simpa only [triadicGridCell, centeredCube] using hscale.1
    · simpa only [localTrace, T, triadicGridCell, centeredCube] using hscale.2
  have hgcCell : ∀ q : J,
      ContinuousOn g (closure (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))) := by
    intro q
    exact hgc.mono (hcellClosure q)
  have hellForReindex := hell
  choose lam Lam hlam hboundsRoot using hell
  have hboundsClosure : ∀ n x,
      x ∈ closure (centeredCube z r hr : Set (SpatialCoordinates d)) →
        lam n ≤ c n x ∧ c n x ≤ Lam n := by
    intro n x hx
    have hclosedLower : IsClosed {y : SpatialCoordinates d | lam n ≤ c n y} := by
      exact isClosed_Ici.preimage (hc n)
    have hclosedUpper : IsClosed {y : SpatialCoordinates d | c n y ≤ Lam n} := by
      exact isClosed_Iic.preimage (hc n)
    have hlower :
        closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
          {y : SpatialCoordinates d | lam n ≤ c n y} :=
      closure_minimal (fun y hy => (hboundsRoot n y hy).1) hclosedLower
    have hupper :
        closure (centeredCube z r hr : Set (SpatialCoordinates d)) ⊆
          {y : SpatialCoordinates d | c n y ≤ Lam n} :=
      closure_minimal (fun y hy => (hboundsRoot n y hy).2) hclosedUpper
    exact ⟨hlower hx, hupper hx⟩
  have hboundsCell : ∀ q : J, ∀ n x,
      x ∈ closure (triadicGridCell z r hr q.val : Set (SpatialCoordinates d)) →
        lam n ≤ c n x ∧ c n x ≤ Lam n := by
    intro q n x hx
    exact hboundsClosure n x (hcellClosure q hx)
  have hrepCell : ∀ q : J, ∀ n,
      (b q n).val =ᵐ[volume.restrict
        (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))] c n := by
    intro q n
    exact (hab q n).symm.trans
      (ae_restrict_of_ae_restrict_of_subset
        (triadicGridCell_subset z hr q.val) (hrep n))
  have hResponse : ∀ q : J, ∀ n
      (datum : weakSobolevGraph (triadicGridCell z r hr q.val))
      (B : SpatialCoordinates d → ℝ),
      ContinuousOn B (closure (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))) →
      ((datum.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))] B) →
      EqOn B g (frontier (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))) →
      dirichletResponse
        (killedResponseSpace (centeredCube_killedPoincare
          (triadicGridCenter z r q.val) (triadicGridSide_pos hr q.val)))
        (b q n) datum ≤ Ebound q n := by
    intro q n datum B hBcont hBae hBeq
    have hresponse := hResponseBound
      (triadicGridCenter z r q.val) (triadicGridSide r q.val)
      (triadicGridSide_pos hr q.val) (hSide q)
      (centeredCube_killedPoincare
        (triadicGridCenter z r q.val) (triadicGridSide_pos hr q.val))
      (b q n) g (localLam q n) le_rfl (hscaled q).1 datum B
      hBcont hBae hBeq
    simpa only [Ebound, localTrace] using hresponse
  letI rootCellsCountable : Countable J := inferInstance
  obtain ⟨datum, VN, rho, Vcell, hrho, hmin, hVcell⟩ :=
    goodext_countable_harmonic_trace_bank (d := d) hd Sob (I := J)
      (fun q => triadicGridCenter z r q.val)
      (fun q => triadicGridSide r q.val)
      (fun q => triadicGridSide_pos hr q.val)
      beta alpha hb ha (fun q n => b q n) c hc hrepCell
      (fun q n => lam n) (fun q n => Lam n) (fun q n => hlam n)
      hboundsCell g
      (fun q => hgcCell q) (fun q => (hscaled q).1) hReg Ebound hResponse
  let a' : ℕ → PositiveCoefficient (centeredCube z r hr) := fun n => a (rho n)
  let c' : ℕ → SpatialCoordinates d → ℝ := fun n => c (rho n)
  let GN' : ℕ → DomainL2 (centeredCube z r hr) →L[ℝ] DomainL2 (centeredCube z r hr) :=
    fun n => GN (rho n)
  have hA' : aux_prop_conc_controlled_forms_analytic_controls d hd z r hr S a' :=
    aux_prop_conc_controlled_forms_controls_reindex A rho
  have hc' : ∀ n, Continuous (c' n) := fun n => hc (rho n)
  have hell' : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
        lam ≤ c' n x ∧ c' n x ≤ Lam := by
    intro n
    exact hellForReindex (rho n)
  have hrep' : ∀ n,
      (a' n).val =ᵐ[volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d))] c' n :=
    fun n => hrep (rho n)
  have hcell' : aux_prop_conc_mesh_cutoff_family_AllCellBounds z r hr c' t alpha := by
    intro Jmesh hJmesh theta htheta thetaH hthetaH
    intro k
    rcases hcell Jmesh hJmesh theta htheta thetaH hthetaH k with
      ⟨Ecell, Grcell, Hocell, hEcell, hGrcell, hHocell, hbounds⟩
    refine ⟨Ecell, Grcell, Hocell, hEcell, hGrcell, hHocell, ?_⟩
    intro n w hw htrace hwcont
    exact hbounds (rho n) w hw htrace hwcont
  have hGN' : ∀ n f, GN' n f =
      (responseSolution S (a' n) ((sobolevVolumeLoad f).comp S.space.subtypeL)).val.1 := by
    intro n f
    exact hGN (rho n) f
  have hConv' : Tendsto GN' atTop (𝓝 G) := hConv.comp hrho.tendsto_atTop
  let s : ℝ := (d : ℝ) - 2 + 2 * alpha - eta
  have hs : (d : ℝ) - 1 < s := by
    dsimp only [s]
    linarith only [hEta]
  let A0 : ℝ := (C * K) * T ^ 2
  have hA0 : 0 ≤ A0 := by
    dsimp only [A0]
    exact mul_nonneg (mul_nonneg hC.le hK) (sq_nonneg T)
  let b' : ∀ q : J, ℕ → PositiveCoefficient (triadicGridCell z r hr q.val) :=
    fun q n => b q (rho n)
  have hab' : ∀ q n, (a' n).val =ᵐ[volume.restrict
      (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))] (b' q n).val := by
    intro q n
    exact hab q (rho n)
  let u' : ∀ q : J, ℕ → weakSobolevGraph (triadicGridCell z r hr q.val) := fun q n =>
    dirichletMinimizer
      (killedResponseSpace (centeredCube_killedPoincare
        (triadicGridCenter z r q.val) (triadicGridSide_pos hr q.val)))
      (b' q n) (datum q)
  let U' : J → ℕ → SpatialCoordinates d → ℝ := fun q n => VN q (rho n)
  have hUc : ∀ q n,
      ContinuousOn (U' q n)
        (closure (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))) := by
    intro q n
    exact (hmin q (rho n)).1
  have hUr : ∀ q n,
      ((u' q n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))] U' q n := by
    intro q n
    exact (hmin q (rho n)).2.1
  have hUt : ∀ q n x,
      x ∈ frontier (triadicGridCell z r hr q.val : Set (SpatialCoordinates d)) → U' q n x = g x := by
    intro q n x hx
    exact (hmin q (rho n)).2.2.1 x hx
  have hlimit : ∀ q, TendstoUniformlyOn (U' q) (Vcell q) atTop
      (closure (triadicGridCell z r hr q.val : Set (SpatialCoordinates d))) := by
    intro q
    exact (hVcell q).2.1
  have htraceNonneg : ∀ q, 0 ≤ localTrace q := by
    intro q
    exact mul_nonneg
      (Real.rpow_nonneg (triadicGridSide_pos hr q.val).le _)
      (SubdiffusiveProcess.holderSeminorm_nonneg _ _ _)
  have hTraceBound : ∀ q, localTrace q ≤ T * (triadicGridSide r q.val) ^ alpha := by
    intro q
    exact (hscaled q).2
  have hLamR : ∀ q : J, ∀ᶠ n in atTop,
      localLam q (rho n) ≤ K * (triadicGridSide r q.val) ^ (-eta) := by
    intro q
    exact hrho.tendsto_atTop.eventually (hLam q)
  have hEnergy : ∀ q : J, ∀ᶠ n in atTop,
      sobolevCoefficientForm (b' q n) (u' q n).val (u' q n).val ≤
        A0 * (triadicGridSide r q.val) ^ s := by
    intro q
    filter_upwards [hLamR q] with n hLamN
    let side := triadicGridSide r q.val
    have hside : 0 < side := triadicGridSide_pos hr q.val
    have hlocal : C * localLam q (rho n) * side ^ ((d : ℝ) - 2) ≤
        (C * K) * side ^ ((d : ℝ) - 2 - eta) := by
      calc
        C * localLam q (rho n) * side ^ ((d : ℝ) - 2) ≤
            C * (K * side ^ (-eta)) * side ^ ((d : ℝ) - 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hLamN hC.le)
            (Real.rpow_nonneg hside.le _)
        _ = (C * K) * (side ^ (-eta) * side ^ ((d : ℝ) - 2)) := by ring
        _ = (C * K) * side ^ ((-eta) + ((d : ℝ) - 2)) := by
          rw [← Real.rpow_add hside]
        _ = (C * K) * side ^ ((d : ℝ) - 2 - eta) := by
          congr 2
          ring
    have hbase : dirichletResponse
        (killedResponseSpace (centeredCube_killedPoincare
          (triadicGridCenter z r q.val) (triadicGridSide_pos hr q.val)))
        (b' q n) (datum q) ≤
          (C * K) * side ^ ((d : ℝ) - 2 - eta) * (localTrace q) ^ 2 := by
      calc
        _ ≤ Ebound q (rho n) := (hmin q (rho n)).2.2.2
        _ = C * localLam q (rho n) * side ^ ((d : ℝ) - 2) *
              (localTrace q) ^ 2 := by rfl
        _ ≤ (C * K) * side ^ ((d : ℝ) - 2 - eta) * (localTrace q) ^ 2 :=
          mul_le_mul_of_nonneg_right hlocal (sq_nonneg _)
    have hpower := SubdiffusiveProcess.trace_response_power_bound
      (d := d) (alpha := alpha) (eta := eta) (C := C * K) (K := T)
      (r := side) (trace := localTrace q)
      (energy := dirichletResponse
        (killedResponseSpace (centeredCube_killedPoincare
          (triadicGridCenter z r q.val) (triadicGridSide_pos hr q.val)))
        (b' q n) (datum q))
      hside (mul_nonneg hC.le hK) hT (htraceNonneg q) (hTraceBound q) hbase
    simpa only [u', A0, dirichletResponse] using hpower
  have hOsc : ∀ q : J, ∀ n x,
      x ∈ closure (triadicGridCell z r hr q.val : Set (SpatialCoordinates d)) →
      |U' q n x - g x| ≤ H * (triadicGridSide r q.val) ^ alpha := by
    intro q n x hx
    have hdom : IsOpenBoundedConvexDomain
        (triadicGridCell z r hr q.val : Set (SpatialCoordinates d)) := by
      refine ⟨(triadicGridCell z r hr q.val).isOpen,
        (centeredCube_isBounded (triadicGridCenter z r q.val)
          (triadicGridSide_pos hr q.val)).isBoundedDomain, ?_⟩
      exact convex_ball (triadicGridCenter z r q.val)
        (triadicGridSide r q.val / 2)
    have hOscData : ∀ x ∈ closure
        (triadicGridCell z r hr q.val : Set (SpatialCoordinates d)),
        ∀ y ∈ frontier (triadicGridCell z r hr q.val : Set (SpatialCoordinates d)),
          |g y - g x| ≤ H * (triadicGridSide r q.val) ^ alpha := by
      intro x hx y hy
      have hholder := holder_cube_oscillation_le
        (triadicGridCenter z r q.val) (triadicGridSide r q.val)
        (triadicGridSide_pos hr q.val) ha.le (hcellClosure q) hgh x y hx
        (frontier_subset_closure hy)
      simpa only [H] using hholder
    have hboundsOpen : ∀ x ∈
        (triadicGridCell z r hr q.val : Set (SpatialCoordinates d)),
        lam (rho n) ≤ c (rho n) x ∧ c (rho n) x ≤ Lam (rho n) := by
      intro y hy
      exact hboundsCell q (rho n) y (subset_closure hy)
    have hmax := dirichletMinimizer_abs_sub_datum_le hdom
      (killedResponseSpace (centeredCube_killedPoincare
        (triadicGridCenter z r q.val) (triadicGridSide_pos hr q.val)))
      rfl (b' q n) (c (rho n)) (hc (rho n))
      (hrepCell q (rho n)) (lam (rho n)) (Lam (rho n)) (hlam (rho n))
      hboundsOpen (datum q) (U' q n) g (hUc q n) (hUr q n)
      (hUt q n) (H * (triadicGridSide r q.val) ^ alpha) hOscData
    exact hmax x hx
  exact goodext_response_of_triadic_bank hd z r hr S hS a' hA' c' hc' hell' hrep'
    t alpha ha hcell' GN' G hGN' hConv' E hE hcont Gamma minLevel s H A0 hs hH hA0
    g hg0 b' hab' u' U' Vcell hUc hUr hUt hlimit hEnergy hOsc

end Paper
