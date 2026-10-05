module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.EnergyMinimality
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2.ScaledPoincare
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.NormalizedL2
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6SchauderDatum.Corrector

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2

open MeasureTheory
open Homogenization (Vec H1Function H10Function vecDot volumeAverage
  unitDirichletPoincareConst unitMeanZeroPoincareConst)
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder

noncomputable section

variable {d : ℕ}

/-! ### The Dirichlet energy as a coordinate sum -/

theorem vecDot_self_eq_sum_sq (F : Vec d → Vec d) :
    (fun y => vecDot (F y) (F y)) = fun y => ∑ i : Fin d, F y i ^ 2 := by
  funext y
  show (∑ i : Fin d, F y i * F y i) = ∑ i : Fin d, F y i ^ 2
  exact Finset.sum_congr rfl fun i _ => (pow_two (F y i)).symm

theorem integrableOn_vecDot_self {W : Set (Vec d)} {F : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun p => F p i) 2 (volume.restrict W)) :
    IntegrableOn (fun y => vecDot (F y) (F y)) W volume := by
  rw [IntegrableOn, vecDot_self_eq_sum_sq]
  exact integrable_finsetSum _ fun i _ => (hF i).integrable_sq

/-- **The Dirichlet energy is the sum of the squared coordinate `L²` norms.** -/
theorem integral_vecDot_self_eq_sum_sq {W : Set (Vec d)} {F : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun p => F p i) 2 (volume.restrict W)) :
    ∫ y in W, vecDot (F y) (F y) ∂volume
      = ∑ i : Fin d, (eLpNorm (fun p => F p i) 2 (volume.restrict W)).toReal ^ 2 := by
  rw [vecDot_self_eq_sum_sq, integral_finsetSum _ fun i _ => (hF i).integrable_sq]
  exact Finset.sum_congr rfl fun i _ =>
    (Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq (hF i)).symm

theorem integral_vecDot_self_nonneg (W : Set (Vec d)) (F : Vec d → Vec d) :
    0 ≤ ∫ y in W, vecDot (F y) (F y) ∂volume :=
  integral_nonneg fun _ => vecDot_self_nonneg _

/-- **The coordinate sum of the `L²` norms is controlled by the Dirichlet
energy**, at the cost of a factor `d`. -/
theorem sum_toReal_eLpNorm_coord_le {W : Set (Vec d)} {F : Vec d → Vec d}
    (hF : ∀ i, MemLp (fun p => F p i) 2 (volume.restrict W)) :
    ∑ i : Fin d, (eLpNorm (fun p => F p i) 2 (volume.restrict W)).toReal
      ≤ (d : ℝ) * Real.sqrt (∫ y in W, vecDot (F y) (F y) ∂volume) := by
  have hQ := integral_vecDot_self_eq_sum_sq hF
  have hstep : ∀ i : Fin d,
      (eLpNorm (fun p => F p i) 2 (volume.restrict W)).toReal
        ≤ Real.sqrt (∫ y in W, vecDot (F y) (F y) ∂volume) := by
    intro i
    have hle : (eLpNorm (fun p => F p i) 2 (volume.restrict W)).toReal ^ 2
        ≤ ∫ y in W, vecDot (F y) (F y) ∂volume := by
      rw [hQ]
      refine Finset.single_le_sum (f := fun l : Fin d =>
        (eLpNorm (fun p => F p l) 2 (volume.restrict W)).toReal ^ 2) ?_ (Finset.mem_univ i)
      exact fun l _ => sq_nonneg _
    have h1 : Real.sqrt ((eLpNorm (fun p => F p i) 2 (volume.restrict W)).toReal ^ 2)
        ≤ Real.sqrt (∫ y in W, vecDot (F y) (F y) ∂volume) := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq ENNReal.toReal_nonneg] at h1
  calc ∑ i : Fin d, (eLpNorm (fun p => F p i) 2 (volume.restrict W)).toReal
      ≤ ∑ _i : Fin d, Real.sqrt (∫ y in W, vecDot (F y) (F y) ∂volume) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = (d : ℝ) * Real.sqrt (∫ y in W, vecDot (F y) (F y) ∂volume) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **A pointwise coordinate bound prices the Dirichlet energy.** -/
theorem integral_vecDot_self_le_of_forall_abs_le {W : Set (Vec d)} {F : Vec d → Vec d}
    {B : ℝ} (hWmeas : MeasurableSet W) (hWtop : volume W ≠ ⊤)
    (hF : ∀ i, MemLp (fun p => F p i) 2 (volume.restrict W))
    (hB : ∀ p ∈ W, ∀ i, |F p i| ≤ B) :
    ∫ y in W, vecDot (F y) (F y) ∂volume ≤ (d : ℝ) * B ^ 2 * (volume W).toReal := by
  have hint : IntegrableOn (fun y => vecDot (F y) (F y)) W volume :=
    integrableOn_vecDot_self hF
  have hfin : IsFiniteMeasure (volume.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_of_le_of_ne le_top hWtop⟩
  have hconst : IntegrableOn (fun _ : Vec d => (d : ℝ) * B ^ 2) W volume :=
    integrable_const _
  have hptw : ∀ y ∈ W, vecDot (F y) (F y) ≤ (d : ℝ) * B ^ 2 := by
    intro y hy
    have hsum : vecDot (F y) (F y) = ∑ i : Fin d, F y i ^ 2 :=
      congrFun (vecDot_self_eq_sum_sq F) y
    rw [hsum]
    calc ∑ i : Fin d, F y i ^ 2 ≤ ∑ _i : Fin d, B ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := hB y hy i
          nlinarith [abs_nonneg (F y i), sq_abs (F y i)]
      _ = (d : ℝ) * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc ∫ y in W, vecDot (F y) (F y) ∂volume
      ≤ ∫ _y in W, (d : ℝ) * B ^ 2 ∂volume := setIntegral_mono_on hint hconst hWmeas hptw
    _ = (d : ℝ) * B ^ 2 * (volume W).toReal := by
        rw [setIntegral_const, smul_eq_mul, mul_comm, measureReal_def]

/-! ### The `L²` triangle inequality in `toReal` form -/

theorem toReal_eLpNorm_sub_le {mu : Measure (Vec d)} {a b : Vec d → ℝ}
    (ha : MemLp a 2 mu) (hb : MemLp b 2 mu) :
    (eLpNorm (fun p => a p - b p) 2 mu).toReal
      ≤ (eLpNorm a 2 mu).toReal + (eLpNorm b 2 mu).toReal := by
  have hle : eLpNorm (fun p => a p - b p) 2 mu ≤ eLpNorm a 2 mu + eLpNorm b 2 mu := by
    have h : eLpNorm (a - b) 2 mu ≤ eLpNorm a 2 mu + eLpNorm b 2 mu :=
      eLpNorm_sub_le one_le_two
    exact h
  have hne : eLpNorm a 2 mu + eLpNorm b 2 mu ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ha.ne, hb.ne⟩
  rw [← ENNReal.toReal_add ha.ne hb.ne]
  exact ENNReal.toReal_mono hne hle

/-! ### The corrector, with its `H¹₀` witness exposed -/

/-- **The residual corrector, with the realizing `H¹₀` witness returned.**

`Section6SchauderDatum.Corrector.exists_unitWeaklyHarmonicOn_of_datum` produces
the weakly harmonic replacement `w` of a datum `Phi` together with
`MemH10 V (w - Phi)`.  That membership pins only the *value* representative,
whereas `EnergyMinimality.integral_vecDot_grad_self_le_of_isUnitWeaklyHarmonicOn`
needs the pointwise **gradient** identity `∇w = ∇Phi + ∇rho`.  The identity is
free at the construction site, where the corrector is literally
`Phi + rho.toH1Function`; this is that construction, restated so that the
witness survives. -/
theorem exists_h10Witness_isUnitWeaklyHarmonicOn [NeZero d] {V : Set (Vec d)}
    (hV : Homogenization.IsOpenBoundedConvexDomain V) (hne : V.Nonempty)
    (Phi : H1Function V) :
    ∃ rho : H10Function V, IsUnitWeaklyHarmonicOn V (Phi + rho.toH1Function) := by
  have : IsFiniteMeasure (Homogenization.volumeMeasureOn V) :=
    hV.isFiniteMeasure_restrict_volume
  have hgrad : Homogenization.MemVectorL2 V Phi.grad := Phi.grad_memVectorL2
  have hg : Homogenization.MemVectorL2 V (fun y => -Phi.grad y) := hgrad.neg
  have hrealize :
      Homogenization.PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization V :=
    Homogenization.PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      hV
  obtain ⟨rho, hrho⟩ :=
    Homogenization.exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := Section6SchauderDatum.unitCoeffField d) (U := V) (g := fun y => -Phi.grad y)
      (lam := 1) (Lam := 1) hg hrealize hne
      (Section6SchauderDatum.isEllipticFieldOn_unitCoeffField hV.isOpen.measurableSet)
  refine ⟨rho, ?_⟩
  intro φ
  have hrhomem : Homogenization.MemVectorL2 V rho.toH1Function.grad :=
    rho.toH1Function.grad_memVectorL2
  have hsplit := Section6SchauderDatum.integral_vecDot_add_left_split (U := V) hgrad hrhomem
    (H := (Phi + rho.toH1Function).grad)
    (fun x => by rw [Homogenization.H1Function.add_grad]) φ
  have hid := hrho φ
  have hcongr : ∫ x in V, vecDot (Homogenization.matVecMul
        (Section6SchauderDatum.unitCoeffField d x) (rho.toH1Function.grad x))
        (φ.toH1Function.grad x) ∂volume =
      ∫ x in V, vecDot (rho.toH1Function.grad x) (φ.toH1Function.grad x) ∂volume :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      show vecDot (Homogenization.matVecMul (Section6SchauderDatum.unitCoeffField d x)
          (rho.toH1Function.grad x)) (φ.toH1Function.grad x) =
        vecDot (rho.toH1Function.grad x) (φ.toH1Function.grad x)
      rw [Section6SchauderDatum.matVecMul_unitCoeffField])
  rw [hcongr] at hid
  have hneg : ∫ x in V, vecDot ((fun y => -Phi.grad y) x) (φ.toH1Function.grad x) ∂volume =
      -∫ x in V, vecDot (Phi.grad x) (φ.toH1Function.grad x) ∂volume := by
    have hfun : (fun x => vecDot ((fun y => -Phi.grad y) x) (φ.toH1Function.grad x)) =
        fun x => -vecDot (Phi.grad x) (φ.toH1Function.grad x) := by
      funext x
      show vecDot (-Phi.grad x) (φ.toH1Function.grad x) = _
      rw [Homogenization.vecDot_neg_left]
    rw [hfun, integral_neg]
  rw [hneg] at hid
  rw [hsplit, hid]
  ring

/-! ### The price -/

/-- **The `L̲²` price of the harmonic replacement of a mean-zero datum.**

`Phi` is the datum deviation on the full cube `Y = zY + □_{jY}`, normalized to
mean zero there and with all its weak-gradient coordinates bounded by `B`;
`W ⊆ Y` is the one-step window, inscribed in a cube `zW + □_j`; and
`Phi|_W + rho` is the weakly harmonic replacement of `Phi` on `W`, `rho` being
the `H¹₀(W)` witness of the trace match.

The bound is linear in `B` with a constant that depends only on `d`, on the two
scales, and on the volume ratio `|Y| / |W|`.  Nothing about a classical gradient
for the datum enters. -/
theorem normalizedL2On_harmonicCorrector_le [NeZero d]
    {W : Set (Vec d)} {j jY : ℤ} {zW zY : Vec d} {B : ℝ}
    (hWopen : IsOpen W) (hWpos : 0 < (volume W).toReal) (hWtop : volume W ≠ ⊤)
    (hYpos : 0 < (volume (translatedCube d jY zY)).toReal)
    (hWY : W ⊆ translatedCube d jY zY) (hWcube : W ⊆ translatedCube d j zW)
    (hB0 : 0 ≤ B)
    (Phi : H1Function (translatedCube d jY zY)) (rho : H10Function W)
    (hmean : volumeAverage (translatedCube d jY zY) Phi.toFun = 0)
    (hgradB : ∀ p ∈ translatedCube d jY zY, ∀ i, |Phi.grad p i| ≤ B)
    (hharm : IsUnitWeaklyHarmonicOn W (Phi.restrict hWopen hWY + rho.toH1Function)) :
    normalizedL2On W (Phi.restrict hWopen hWY + rho.toH1Function).toFun
      ≤ (d : ℝ) * Real.sqrt (d : ℝ) *
          (2 * unitDirichletPoincareConst d * (3 : ℝ) ^ j
            + unitMeanZeroPoincareConst d * (3 : ℝ) ^ jY *
                Real.sqrt ((volume (translatedCube d jY zY)).toReal
                  / (volume W).toReal)) * B := by
  classical
  set PhiW : H1Function W := Phi.restrict hWopen hWY with hPhiW
  set v₁ : H1Function W := PhiW + rho.toH1Function with hv₁
  have hWmeas : MeasurableSet W := hWopen.measurableSet
  have hYtop : volume (translatedCube d jY zY) ≠ ⊤ := by
    rw [translatedCube_eq_axisCube]
    exact volume_axisCube_ne_top _ _
  have hYmeas : MeasurableSet (translatedCube d jY zY) := by
    rw [translatedCube_eq_axisCube]
    exact (Homogenization.isOpen_axisCube _ _).measurableSet
  have hsqW : 0 < Real.sqrt ((volume W).toReal) := Real.sqrt_pos.2 hWpos
  have hsqY : 0 < Real.sqrt ((volume (translatedCube d jY zY)).toReal) :=
    Real.sqrt_pos.2 hYpos
  -- gradients
  have hgradv₁ : ∀ y, v₁.grad y = PhiW.grad y + rho.toH1Function.grad y := by
    intro y
    rw [hv₁, Homogenization.H1Function.add_grad]
  have hPhiWgrad : ∀ y, PhiW.grad y = Phi.grad y := fun _ => rfl
  have hPhiWfun : ∀ y, PhiW.toFun y = Phi.toFun y := fun _ => rfl
  -- coordinate `L²` memberships
  have hmemPhiW : ∀ i, MemLp (fun p => PhiW.grad p i) 2 (volume.restrict W) :=
    fun i => PhiW.gradMemL2 i
  have hmemPhiY : ∀ i,
      MemLp (fun p => Phi.grad p i) 2 (volume.restrict (translatedCube d jY zY)) :=
    fun i => Phi.gradMemL2 i
  have hmemv₁ : ∀ i, MemLp (fun p => v₁.grad p i) 2 (volume.restrict W) :=
    fun i => v₁.gradMemL2 i
  have hmemrho : ∀ i, MemLp (fun p => rho.toH1Function.grad p i) 2 (volume.restrict W) :=
    fun i => rho.toH1Function.gradMemL2 i
  -- the two Dirichlet energies against `B`
  have hQW : ∫ y in W, vecDot (PhiW.grad y) (PhiW.grad y) ∂volume
      ≤ (d : ℝ) * B ^ 2 * (volume W).toReal :=
    integral_vecDot_self_le_of_forall_abs_le hWmeas hWtop hmemPhiW
      (fun p hp i => by rw [hPhiWgrad p]; exact hgradB p (hWY hp) i)
  have hQY : ∫ y in translatedCube d jY zY, vecDot (Phi.grad y) (Phi.grad y) ∂volume
      ≤ (d : ℝ) * B ^ 2 * (volume (translatedCube d jY zY)).toReal :=
    integral_vecDot_self_le_of_forall_abs_le hYmeas hYtop hmemPhiY hgradB
  -- the square root of the pointwise energy budget
  have hsqrt_split : ∀ V : ℝ, 0 ≤ V →
      Real.sqrt ((d : ℝ) * B ^ 2 * V) = Real.sqrt (d : ℝ) * B * Real.sqrt V := by
    intro V hV
    rw [Real.sqrt_mul (by positivity) V, Real.sqrt_mul (Nat.cast_nonneg d) (B ^ 2),
      Real.sqrt_sq hB0]
  -- leg A: the corrector `rho`
  have hArho : ∑ i : Fin d, (eLpNorm (fun p => rho.toH1Function.grad p i) 2
        (volume.restrict W)).toReal
      ≤ 2 * ((d : ℝ) * (Real.sqrt (d : ℝ) * B * Real.sqrt ((volume W).toReal))) := by
    have hcoord : ∀ i, (eLpNorm (fun p => rho.toH1Function.grad p i) 2
          (volume.restrict W)).toReal
        ≤ (eLpNorm (fun p => v₁.grad p i) 2 (volume.restrict W)).toReal
          + (eLpNorm (fun p => PhiW.grad p i) 2 (volume.restrict W)).toReal := by
      intro i
      have hfun : (fun p => rho.toH1Function.grad p i)
          = fun p => v₁.grad p i - PhiW.grad p i := by
        funext p
        rw [hgradv₁ p]
        show rho.toH1Function.grad p i = (PhiW.grad p + rho.toH1Function.grad p) i
            - PhiW.grad p i
        show rho.toH1Function.grad p i
            = (PhiW.grad p i + rho.toH1Function.grad p i) - PhiW.grad p i
        ring
      rw [hfun]
      exact toReal_eLpNorm_sub_le (hmemv₁ i) (hmemPhiW i)
    have henergy : ∫ y in W, vecDot (v₁.grad y) (v₁.grad y) ∂volume
        ≤ ∫ y in W, vecDot (PhiW.grad y) (PhiW.grad y) ∂volume :=
      integral_vecDot_grad_self_le_of_isUnitWeaklyHarmonicOn hharm rho hgradv₁
    have hv₁sum : ∑ i : Fin d, (eLpNorm (fun p => v₁.grad p i) 2 (volume.restrict W)).toReal
        ≤ (d : ℝ) * (Real.sqrt (d : ℝ) * B * Real.sqrt ((volume W).toReal)) := by
      refine le_trans (sum_toReal_eLpNorm_coord_le hmemv₁) ?_
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
      rw [← hsqrt_split _ ENNReal.toReal_nonneg]
      exact Real.sqrt_le_sqrt (le_trans henergy hQW)
    have hPhisum : ∑ i : Fin d, (eLpNorm (fun p => PhiW.grad p i) 2
          (volume.restrict W)).toReal
        ≤ (d : ℝ) * (Real.sqrt (d : ℝ) * B * Real.sqrt ((volume W).toReal)) := by
      refine le_trans (sum_toReal_eLpNorm_coord_le hmemPhiW) ?_
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
      rw [← hsqrt_split _ ENNReal.toReal_nonneg]
      exact Real.sqrt_le_sqrt hQW
    have hsplit : ∑ i : Fin d, (eLpNorm (fun p => rho.toH1Function.grad p i) 2
          (volume.restrict W)).toReal
        ≤ (∑ i : Fin d, (eLpNorm (fun p => v₁.grad p i) 2 (volume.restrict W)).toReal)
          + ∑ i : Fin d, (eLpNorm (fun p => PhiW.grad p i) 2 (volume.restrict W)).toReal := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => hcoord i
    linarith only [hsplit, hv₁sum, hPhisum]
  have hCD0 : (0 : ℝ) ≤ unitDirichletPoincareConst d :=
    Homogenization.unitDirichletPoincareConst_nonneg d
  have hCM0 : (0 : ℝ) ≤ unitMeanZeroPoincareConst d :=
    Homogenization.unitMeanZeroPoincareConst_nonneg d
  have h3j : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) _
  have h3jY : (0 : ℝ) < (3 : ℝ) ^ jY := zpow_pos (by norm_num) _
  have hrhoL2 : (eLpNorm rho.toH1Function.toFun 2 (volume.restrict W)).toReal
      ≤ unitDirichletPoincareConst d * (3 : ℝ) ^ j *
          (2 * ((d : ℝ) * (Real.sqrt (d : ℝ) * B * Real.sqrt ((volume W).toReal)))) := by
    refine le_trans (eLpNorm_le_dirichletPoincare_translatedCube hWmeas hWcube rho) ?_
    exact mul_le_mul_of_nonneg_left hArho (by positivity)
  have hrhoNorm : normalizedL2On W rho.toH1Function.toFun
      ≤ 2 * (d : ℝ) * Real.sqrt (d : ℝ) * unitDirichletPoincareConst d * (3 : ℝ) ^ j * B := by
    rw [normalizedL2On_eq_toReal_eLpNorm_div rho.toH1Function.memL2, div_le_iff₀ hsqW]
    refine le_trans hrhoL2 (le_of_eq ?_)
    ring
  -- leg B: the datum `Phi`
  have hPhiY : ∑ i : Fin d, (eLpNorm (fun p => Phi.grad p i) 2
        (volume.restrict (translatedCube d jY zY))).toReal
      ≤ (d : ℝ) * (Real.sqrt (d : ℝ) * B *
          Real.sqrt ((volume (translatedCube d jY zY)).toReal)) := by
    refine le_trans (sum_toReal_eLpNorm_coord_le hmemPhiY) ?_
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
    rw [← hsqrt_split _ ENNReal.toReal_nonneg]
    exact Real.sqrt_le_sqrt hQY
  have hPhiL2 : (eLpNorm Phi.toFun 2 (volume.restrict (translatedCube d jY zY))).toReal
      ≤ unitMeanZeroPoincareConst d * (3 : ℝ) ^ jY *
          ((d : ℝ) * (Real.sqrt (d : ℝ) * B *
            Real.sqrt ((volume (translatedCube d jY zY)).toReal))) := by
    have hpo := eLpNorm_sub_average_le_meanZeroPoincare_translatedCube
      (d := d) (j := jY) (z := zY) Phi
    rw [hmean] at hpo
    have hfun : (fun p => Phi.toFun p - (0 : ℝ)) = Phi.toFun := by
      funext p
      ring
    rw [hfun] at hpo
    exact le_trans hpo (mul_le_mul_of_nonneg_left hPhiY (by positivity))
  have hPhiNormY : normalizedL2On (translatedCube d jY zY) Phi.toFun
      ≤ (d : ℝ) * Real.sqrt (d : ℝ) * unitMeanZeroPoincareConst d * (3 : ℝ) ^ jY * B := by
    rw [normalizedL2On_eq_toReal_eLpNorm_div Phi.memL2, div_le_iff₀ hsqY]
    refine le_trans hPhiL2 (le_of_eq ?_)
    ring
  have hPhiNormW : normalizedL2On W Phi.toFun
      ≤ Real.sqrt ((volume (translatedCube d jY zY)).toReal / (volume W).toReal) *
          ((d : ℝ) * Real.sqrt (d : ℝ) * unitMeanZeroPoincareConst d * (3 : ℝ) ^ jY * B) := by
    refine le_trans (normalizedL2On_le_of_subset hWY hYpos hWpos ?_) ?_
    · exact Phi.memL2.integrable_sq
    · exact mul_le_mul_of_nonneg_left hPhiNormY (Real.sqrt_nonneg _)
  -- the triangle inequality on `W`
  have hfun : v₁.toFun = fun p => Phi.toFun p + rho.toH1Function.toFun p := by
    funext p
    have h := Homogenization.H1Function.add_toFun PhiW rho.toH1Function
    calc v₁.toFun p = (PhiW + rho.toH1Function).toFun p := by rw [hv₁]
      _ = PhiW.toFun p + rho.toH1Function.toFun p := by rw [h]
      _ = Phi.toFun p + rho.toH1Function.toFun p := by rw [hPhiWfun p]
  have htri : normalizedL2On W v₁.toFun
      ≤ normalizedL2On W Phi.toFun + normalizedL2On W rho.toH1Function.toFun := by
    rw [hfun]
    exact normalizedL2On_add_le PhiW.memL2 rho.toH1Function.memL2
  have hB1 : (0 : ℝ)
      ≤ Real.sqrt ((volume (translatedCube d jY zY)).toReal / (volume W).toReal) :=
    Real.sqrt_nonneg _
  nlinarith [htri, hPhiNormW, hrhoNorm, Real.sqrt_nonneg ((d : ℝ)), hB0, hCD0, hCM0,
    h3j.le, h3jY.le, hB1]

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6BoundaryL2
