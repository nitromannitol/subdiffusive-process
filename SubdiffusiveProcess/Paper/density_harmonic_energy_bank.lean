module

public import SubdiffusiveProcess.Paper.goodext_countable_harmonic_trace_bank
public import SubdiffusiveProcess.Paper.goodext_dirichlet_response_bound
public import SubdiffusiveProcess.Sobolev.HolderTraceScaling
public import SubdiffusiveProcess.Sobolev.MinimizerDatumOscillation
public import SubdiffusiveProcess.Sobolev.HolderCubeOscillation
public import Mathlib.Order.Filter.IsBounded
@[expose] public section

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess Homogenization
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology ContDiff BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Paper
/-- Construct actual harmonic minimizers on a countable family of contained cells,
with a common uniform subsequence, convergent energies, a power-law energy cap,
and the maximum-principle oscillation estimate. Smooth-minimizer regularity and
the eventual coefficient cap are explicit analytic inputs. -/
theorem density_harmonic_energy_bank
    {d : ℕ} (hd : 2 ≤ d) [NeZero d]
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (I : in_J d) (X : in_extension d hd I) (Sob : SobolevFoundationalInput d hd)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (Cells : Type) [Countable Cells]
    (centre : Cells → SpatialCoordinates d) (radius : Cells → ℝ) (hRadius : ∀ q, 0 < radius q)
    (hSide : ∀ q, radius q ≤ 1)
    (hsub : ∀ q, (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (c : ℕ → SpatialCoordinates d → ℝ) (hc : ∀ n, Continuous (c n))
    (hell : ∀ n, ∃ lam Lam : ℝ, 0 < lam ∧
      ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), lam ≤ c n x ∧ c n x ≤ Lam)
    (alpha beta eta K : ℝ) (ha : 0 < alpha) (hb : beta ∈ Ioo (1 / 2 : ℝ) 1)
    (hba : beta ≤ alpha) (hK : 0 ≤ K)
    (g : SpatialCoordinates d → ℝ)
    (hgc : ContinuousOn g (closure (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hgh : IsHolderOn alpha (closure (centeredCube z r hr : Set (SpatialCoordinates d))) g)
    (b : ∀ q, ℕ → PositiveCoefficient (centeredCube (centre q) (radius q) (hRadius q)))
    (hrepCell : ∀ q n, (b q n).val =ᵐ[volume.restrict
      (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))] c n)
    (hReg : ∀ q : Cells, ∀ (phi : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ phi →
      ∀ datum : weakSobolevGraph (centeredCube (centre q) (radius q) (hRadius q)),
        ((datum.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))] phi) →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∃ V : SpatialCoordinates d → ℝ,
          ContinuousOn V (closure (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))) ∧
          ((dirichletMinimizer (killedResponseSpace (centeredCube_killedPoincare (centre q) (hRadius q)))
            (b q n) datum).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))] V ∧
          IsHolderOn alpha (closure (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))) V ∧
          cAlphaNorm alpha (closure (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))) V ≤ C)
    (hLam : ∀ q : Cells, ∀ᶠ n in atTop,
      I.Lam (centre q) (radius q) (hRadius q)
        (b q n) (centre q) (radius q) ((beta - 1 / 2) / 4) 2 ≤
          K * (radius q) ^ (-eta)) :
    ∃ A0 H : ℝ, 0 ≤ A0 ∧ 0 ≤ H ∧
      ∃ (datum : ∀ q, weakSobolevGraph (centeredCube (centre q) (radius q) (hRadius q)))
        (VN : Cells → ℕ → SpatialCoordinates d → ℝ)
        (rho : ℕ → ℕ) (Vcell : Cells → SpatialCoordinates d → ℝ) (cost : Cells → ℝ),
      StrictMono rho ∧ ∀ q,
        (∀ n, ContinuousOn (VN q n)
            (closure (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))) ∧
          ((dirichletMinimizer (killedResponseSpace (centeredCube_killedPoincare (centre q) (hRadius q)))
            (b q (rho n)) (datum q)).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
              (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))] VN q n ∧
          (∀ x ∈ frontier (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d)),
            VN q n x = g x) ∧
          ∀ x ∈ closure (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d)),
            |VN q n x - g x| ≤ H * radius q ^ alpha) ∧
        ContinuousOn (Vcell q)
          (closure (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))) ∧
        TendstoUniformlyOn (VN q) (Vcell q) atTop
          (closure (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))) ∧
        Tendsto (fun n => dirichletResponse
          (killedResponseSpace (centeredCube_killedPoincare (centre q) (hRadius q)))
          (b q (rho n)) (datum q)) atTop (𝓝 (cost q)) ∧
        0 ≤ cost q ∧ cost q ≤ A0 * radius q ^ ((d : ℝ) - 2 + 2 * alpha - eta) := by
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
  let J : Type := Cells
  let localLam : J → ℕ → ℝ := fun q n =>
    I.Lam (centre q) (radius q)
      (hRadius q) (b q n)
      (centre q) (radius q)
      ((beta - 1 / 2) / 4) 2
  let localTrace : J → ℝ := fun q =>
    (radius q) ^ beta *
      holderSeminorm beta
        (frontier (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))) g
  let Ebound : J → ℕ → ℝ := fun q n =>
    C * localLam q n * (radius q) ^ ((d : ℝ) - 2) *
      (localTrace q) ^ 2
  have hcellClosure : ∀ q : J,
      closure (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d)) ⊆
        closure (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    intro q
    exact closure_mono (hsub q)
  have hscaled : ∀ q : J,
      IsHolderOn beta (frontier (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))) g ∧
        localTrace q ≤ T * (radius q) ^ alpha := by
    intro q
    have hfront :
        frontier (Metric.ball (centre q)
          (radius q / 2)) ⊆
          closure (centeredCube z r hr : Set (SpatialCoordinates d)) := by
      exact frontier_subset_closure.trans (hcellClosure q)
    have hscale := scaled_holderSeminorm_frontier_le
      (centre q) (radius q)
      (hRadius q) hba hfront hgh
    constructor
    · exact hscale.1
    · exact hscale.2
  have hgcCell : ∀ q : J,
      ContinuousOn g (closure (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))) := by
    intro q
    exact hgc.mono (hcellClosure q)
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
      x ∈ closure (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d)) →
        lam n ≤ c n x ∧ c n x ≤ Lam n := by
    intro q n x hx
    exact hboundsClosure n x (hcellClosure q hx)
  have hResponse : ∀ q : J, ∀ n
      (datum : weakSobolevGraph (centeredCube (centre q) (radius q) (hRadius q)))
      (B : SpatialCoordinates d → ℝ),
      ContinuousOn B (closure (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))) →
      ((datum.val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))] B) →
      EqOn B g (frontier (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))) →
      dirichletResponse
        (killedResponseSpace (centeredCube_killedPoincare
          (centre q) (hRadius q)))
        (b q n) datum ≤ Ebound q n := by
    intro q n datum B hBcont hBae hBeq
    have hresponse := hResponseBound
      (centre q) (radius q)
      (hRadius q) (hSide q)
      (centeredCube_killedPoincare
        (centre q) (hRadius q))
      (b q n) g (localLam q n) le_rfl (hscaled q).1 datum B
      hBcont hBae hBeq
    simpa only [Ebound, localTrace] using hresponse
  letI rootCellsCountable : Countable J := inferInstance
  obtain ⟨datum, VN, rho, Vcell, hrho, hmin, hVcell⟩ :=
    goodext_countable_harmonic_trace_bank (d := d) hd Sob (I := J)
      (fun q => centre q)
      (fun q => radius q)
      (fun q => hRadius q)
      beta alpha hb ha (fun q n => b q n) c hc hrepCell
      (fun q n => lam n) (fun q n => Lam n) (fun q n => hlam n)
      hboundsCell g
      (fun q => hgcCell q) (fun q => (hscaled q).1) hReg Ebound hResponse
  let s : ℝ := (d : ℝ) - 2 + 2 * alpha - eta
  let A0 : ℝ := (C * K) * T ^ 2
  have hA0 : 0 ≤ A0 := by
    dsimp only [A0]
    exact mul_nonneg (mul_nonneg hC.le hK) (sq_nonneg T)
  let b' : ∀ q : J, ℕ → PositiveCoefficient (centeredCube (centre q) (radius q) (hRadius q)) :=
    fun q n => b q (rho n)
  let u' : ∀ q : J, ℕ → weakSobolevGraph (centeredCube (centre q) (radius q) (hRadius q)) := fun q n =>
    dirichletMinimizer
      (killedResponseSpace (centeredCube_killedPoincare
        (centre q) (hRadius q)))
      (b' q n) (datum q)
  let U' : J → ℕ → SpatialCoordinates d → ℝ := fun q n => VN q (rho n)
  have hUc : ∀ q n,
      ContinuousOn (U' q n)
        (closure (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))) := by
    intro q n
    exact (hmin q (rho n)).1
  have hUr : ∀ q n,
      ((u' q n).val.1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))] U' q n := by
    intro q n
    exact (hmin q (rho n)).2.1
  have hUt : ∀ q n x,
      x ∈ frontier (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d)) → U' q n x = g x := by
    intro q n x hx
    exact (hmin q (rho n)).2.2.1 x hx
  have hlimit : ∀ q, TendstoUniformlyOn (U' q) (Vcell q) atTop
      (closure (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d))) := by
    intro q
    exact (hVcell q).2.1
  have htraceNonneg : ∀ q, 0 ≤ localTrace q := by
    intro q
    exact mul_nonneg
      (Real.rpow_nonneg (hRadius q).le _)
      (SubdiffusiveProcess.holderSeminorm_nonneg _ _ _)
  have hTraceBound : ∀ q, localTrace q ≤ T * (radius q) ^ alpha := by
    intro q
    exact (hscaled q).2
  have hLamR : ∀ q : J, ∀ᶠ n in atTop,
      localLam q (rho n) ≤ K * (radius q) ^ (-eta) := by
    intro q
    exact hrho.tendsto_atTop.eventually (hLam q)
  have hEnergy : ∀ q : J, ∀ᶠ n in atTop,
      sobolevCoefficientForm (b' q n) (u' q n).val (u' q n).val ≤
        A0 * (radius q) ^ s := by
    intro q
    filter_upwards [hLamR q] with n hLamN
    let side := radius q
    have hside : 0 < side := hRadius q
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
          (centre q) (hRadius q)))
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
          (centre q) (hRadius q)))
        (b' q n) (datum q))
      hside (mul_nonneg hC.le hK) hT (htraceNonneg q) (hTraceBound q) hbase
    simpa only [u', A0, dirichletResponse] using hpower
  have hOsc : ∀ q : J, ∀ n x,
      x ∈ closure (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d)) →
      |U' q n x - g x| ≤ H * (radius q) ^ alpha := by
    intro q n x hx
    have hdom : IsOpenBoundedConvexDomain
        (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d)) := by
      refine ⟨(centeredCube (centre q) (radius q) (hRadius q)).isOpen,
        (centeredCube_isBounded (centre q)
          (hRadius q)).isBoundedDomain, ?_⟩
      exact convex_ball (centre q)
        (radius q / 2)
    have hOscData : ∀ x ∈ closure
        (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d)),
        ∀ y ∈ frontier (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d)),
          |g y - g x| ≤ H * (radius q) ^ alpha := by
      intro x hx y hy
      have hholder := holder_cube_oscillation_le
        (centre q) (radius q)
        (hRadius q) ha.le (hcellClosure q) hgh x y hx
        (frontier_subset_closure hy)
      simpa only [H] using hholder
    have hboundsOpen : ∀ x ∈
        (centeredCube (centre q) (radius q) (hRadius q) : Set (SpatialCoordinates d)),
        lam (rho n) ≤ c (rho n) x ∧ c (rho n) x ≤ Lam (rho n) := by
      intro y hy
      exact hboundsCell q (rho n) y (subset_closure hy)
    have hmax := dirichletMinimizer_abs_sub_datum_le hdom
      (killedResponseSpace (centeredCube_killedPoincare
        (centre q) (hRadius q)))
      rfl (b' q n) (c (rho n)) (hc (rho n))
      (hrepCell q (rho n)) (lam (rho n)) (Lam (rho n)) (hlam (rho n))
      hboundsOpen (datum q) (U' q n) g (hUc q n) (hUr q n)
      (hUt q n) (H * (radius q) ^ alpha) hOscData
    exact hmax x hx
  let energy : Cells → ℕ → ℝ := fun q n =>
    sobolevCoefficientForm (b' q n) (u' q n).val (u' q n).val
  have hnonneg : ∀ q n, 0 ≤ energy q n := fun q n =>
    sobolevCoefficientForm_nonneg (b' q n) (u' q n).val
  have hcompact : ∀ q (sigma : ℕ → ℕ), StrictMono sigma →
      ∃ (x : ℝ) (tau : ℕ → ℕ), StrictMono tau ∧
        Tendsto (fun n => energy q (sigma (tau n))) atTop (𝓝 x) := by
    intro q sigma _hsigma
    have hbounded : IsBoundedUnder (· ≤ ·) atTop (energy q) :=
      ⟨A0 * radius q ^ s, hEnergy q⟩
    obtain ⟨B, hB⟩ := hbounded.bddAbove_range
    obtain ⟨x, _hx, tau, htau, hlim⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) B)).tendsto_subseq
      (fun n => ⟨hnonneg q (sigma n), hB (mem_range_self (sigma n))⟩)
    exact ⟨x, tau, htau, hlim⟩
  obtain ⟨tau, cost, htau, hcost⟩ := exists_joint_subseq_of_countable_subseq_compact energy hcompact
  refine ⟨A0, H, hA0, hH, datum, (fun q n => U' q (tau n)), (fun n => rho (tau n)),
    Vcell, cost, hrho.comp htau, ?_⟩
  intro q
  refine ⟨(fun n => ⟨hUc q (tau n), hUr q (tau n), hUt q (tau n), hOsc q (tau n)⟩),
    (hVcell q).1, (fun u hu => htau.tendsto_atTop.eventually (hlimit q u hu)), hcost q,
    ge_of_tendsto' (hcost q) (fun n => hnonneg q (tau n)), ?_⟩
  exact le_of_tendsto (hcost q) (htau.tendsto_atTop.eventually (hEnergy q))
end Paper
