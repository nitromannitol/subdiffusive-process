import SubdiffusiveProcess.Paper.rem_bank
import SubdiffusiveProcess.Paper.prop_16
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic




open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open SubdiffusiveProcess SubdiffusiveProcess.Lane3 SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal BigOperators ContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper




/-- Generic six-term extraction, all six individual bounds (reused pattern from
`rembank_moments_PROVED.lean`, restated locally so this file is self-contained). -/
theorem aux_prop16_le_of_add_six {a1 a2 a3 a4 a5 a6 B : ℝ≥0∞}
    (h : a1 + a2 + a3 + a4 + a5 + a6 ≤ B) :
    a1 ≤ B ∧ a2 ≤ B ∧ a3 ≤ B ∧ a4 ≤ B ∧ a5 ≤ B ∧ a6 ≤ B := by
  have e1 : a1 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a1 = a1 + 0 + 0 + 0 + 0 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le _
  have e2 : a2 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a2 = 0 + a2 + 0 + 0 + 0 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le _
  have e3 : a3 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a3 = 0 + 0 + a3 + 0 + 0 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le _
  have e4 : a4 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a4 = 0 + 0 + 0 + a4 + 0 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le _
  have e5 : a5 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a5 = 0 + 0 + 0 + 0 + a5 + 0 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le _
  have e6 : a6 ≤ a1 + a2 + a3 + a4 + a5 + a6 := by
    calc a6 = 0 + 0 + 0 + 0 + 0 + a6 := by ring
      _ ≤ a1 + a2 + a3 + a4 + a5 + a6 := by gcongr <;> exact zero_le _
  exact ⟨e1.trans h, e2.trans h, e3.trans h, e4.trans h, e5.trans h, e6.trans h⟩



def aux_prop16_kap {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) : ℝ :=
  Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P) * SubdiffusiveProcess.CoarseGrainingVocab.ahom M N

theorem aux_prop16_kap_pos {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    0 < aux_prop16_kap M N :=
  mul_pos (Real.exp_pos _) (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N)

/-- The `prop_16` Dirichlet band exponent at `t = d - 1/2` (`rem_bank`'s `aexpOf d (d - 1/2)`,
matches `prop_16`'s own exponent literally — `PROGRESS-TRACEW4.md` identification #3). -/
def aux_prop16_aD (d : ℕ) : ℝ :=
  ((d : ℝ) - 1 / 2) * (((d : ℝ) - 1 / 2) - (d : ℝ) + 1) / (((d : ℝ) - 1 / 2) + 1) /
    (8 * Real.log 3)



theorem aux_prop16_cutoff_ae_exp {d : ℕ} (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (N : ℕ) (omega : BilateralField d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ((cutoffPositiveCoefficient M H omega N z hr).val : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))]
      (fun x => Real.exp (cutoffPotential H omega N x - Real.log (aux_prop16_kap M N))) := by
  haveI instCubeClosure : Fact ((centeredCube z r hr : Set (SpatialCoordinates d)) ⊆ closedCube z r hr) :=
    ⟨centeredCube_subset_closedCube z hr⟩
  have h0 := normalizedContinuousPositiveCoefficient_coeFn
    (Ω := centeredCube z r hr) (closedCube z r hr) (cutoffCoefficientCM M H omega N z hr)
    (cutoffCoefficientCM_pos M H omega N z hr) 1 one_pos
  filter_upwards [h0, ae_restrict_mem (centeredCube z r hr).isOpen.measurableSet] with x hx hxm
  have := hx hxm
  change (cutoffPositiveCoefficient M H omega N z hr).val x = _
  unfold cutoffPositiveCoefficient
  rw [this, div_one]
  change cutoffCoefficient M H omega N x = _
  unfold cutoffCoefficient aux_prop16_kap
  have hA := SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N
  have key : ∀ u : ℝ, Real.exp (u - Real.log (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)) =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ * Real.exp u := by
    intro u; rw [Real.exp_sub, Real.exp_log hA, div_eq_inv_mul]
  rw [Real.log_mul (Real.exp_pos _).ne' hA.ne', Real.log_exp, sub_add_eq_sub_sub]
  exact (key _).symm

/-- Local energy on `ball ∩ Ω` equals local energy on `ball` (the gradient lives on `Ω`; copy of
`deep/U2_ref_band.lean`'s `aux_U2_lge_inter`, independently reproved here). Bridges `rem_bank`'s
a.e. gradient bound (stated on `ball ∩ Q`) to `prop_16`'s hypothesis shape (stated on `ball` alone). -/
theorem aux_prop16_lge_inter {d : ℕ} {Ω : Opens (SpatialCoordinates d)} (a : PositiveCoefficient Ω)
    (x : SpatialCoordinates d) (rho : ℝ) (g : HilbertGradient Ω) :
    localGradientEnergy a (s := Metric.ball x rho ∩ (Ω : Set (SpatialCoordinates d)))
        (Metric.isOpen_ball.inter Ω.isOpen).measurableSet g =
      localGradientEnergy a (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet g := by
  simp only [localGradientEnergy_eq_integral]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Measure.restrict_restrict (Metric.isOpen_ball.inter Ω.isOpen).measurableSet,
    Measure.restrict_restrict Metric.isOpen_ball.measurableSet, Set.inter_assoc, Set.inter_self]

/-- A smooth, compactly-supported, nonzero-somewhere, `[0,1]`-valued function on
`centeredCube z r hr` (copy of `bump_construction_PROVED.lean`'s `aux_bump_construction`, extended
there this round with the `[0,1]`-bound conjunct needed to build `prop_16`'s `fL2` argument via
`MemLp.of_bound`). Supplies `prop_16`'s `f`/`hf`/`hfc`/`hfsupp`/`hf0` Neumann-side hypotheses, which
`rem_bank`'s `f := 0` trick cannot satisfy here (`prop_16` genuinely requires `hf0 : ∃x∈Q, f x≠0`). -/
theorem aux_prop16_bump {d : ℕ} (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r) :
    ∃ f : SpatialCoordinates d → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) ∧
      (∃ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)), f x ≠ 0) ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) := by
  have hcube : (centeredCube z r hr : Set (SpatialCoordinates d)) = Metric.ball z (r / 2) := rfl
  set bmp : ContDiffBump z := ⟨r / 8, r / 4, by linarith only [hr, hcube], by linarith only [hr, hcube]⟩ with hbmp
  refine ⟨bmp, bmp.contDiff, bmp.hasCompactSupport, ?_, ⟨z, ?_, ?_⟩,
    fun x => ⟨bmp.nonneg' x, bmp.le_one⟩⟩
  · rw [bmp.tsupport_eq, hcube]
    apply Metric.closedBall_subset_ball
    dsimp [bmp]
    linarith only [hr, hcube, hbmp]
  · rw [hcube]
    exact Metric.mem_ball_self (by linarith only [hr, hcube, hbmp])
  · have := bmp.one_of_mem_closedBall (Metric.mem_closedBall_self (by dsimp [bmp]; linarith only [hr, hcube, hbmp]))
    rw [this]
    norm_num

/-- The `prop_16` half of the `hmom`/`hband` recipe at any moment order `p ≥ 2`. -/
theorem aux_test_prop16_rd_band
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (W : SmallPerturbationInput d) (Sf : SobolevFoundationalInput d hd)
    (D : @lane4_deterministic_good_scale_input d ⟨by omega⟩)
    (p : ℝ) (hp : 2 ≤ p) :
    ∃ (delta0 : ℝ), 0 < delta0 ∧
    ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r), r ≤ 1 →
    ∀ (hP : ∃ K : ℝ≥0, ∀ w : killedSobolevGraph (centeredCube z r hr),
        ‖(w : SobolevData (centeredCube z r hr)).1‖ ≤
          K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) w‖)
      (phi : SpatialCoordinates d → ℝ) (hphi : ContDiff ℝ ∞ phi)
      (hnonconst : ∃ x ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∃ y ∈ frontier (centeredCube z r hr : Set (SpatialCoordinates d)), phi x ≠ phi y)
      (b : weakSobolevGraph (centeredCube z r hr))
      (hb : ((b : SobolevData (centeredCube z r hr)).1 : SpatialCoordinates d → ℝ)
        =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] phi),
    ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
      (Rm : in_responses d M) (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg)
      (H : BilateralField d → C(SpatialCoordinates d, ℝ))
      (hH : InfraredCharacterization M H),
      M.delta ≤ min 1 delta0 →
      let Pm : Measure (BilateralField d) := (chaosSampleLaw M).toMeasure
      let a : ℕ → BilateralField d → PositiveCoefficient (centeredCube z r hr) :=
        fun N omega => cutoffPositiveCoefficient M H omega N z hr
      let RD : ℕ → BilateralField d → ℝ :=
        fun N omega => dirichletResponse (killedResponseSpace hP) (a N omega) b
      ∃ Cband : ℝ, 0 < Cband ∧
        ∀ (h N : ℕ),
          eLpNorm (fun omega => RD N omega -
              (Pm[RD N | bandSigma (fun _ : ℤ => C(SpatialCoordinates d, ℝ)) h]) omega)
            (ENNReal.ofReal p) Pm ≤
          ENNReal.ofReal (Cband * M.delta * (3 : ℝ) ^ (-(aux_prop16_aD d) * (h : ℝ))) := by
  have ht0 : (d : ℝ) - 1 < (d : ℝ) - 1 / 2 := by linarith only [hd, hp]
  have ht1 : (d : ℝ) - 1 / 2 < (d : ℝ) := by linarith only [hd, hp, ht0]
  obtain ⟨aexpOf, qOf, ordersOf, thresholdOf, _, _, haexppos, haexpeq, hmain0⟩ :=
    rem_bank d hd Jc Pc Xc W Sf D ((d : ℝ) - 1 / 2) ht0 ht1
  obtain ⟨hpq, hdeltapos, h3p, hqmem, h12p, h4q, hall⟩ := hmain0 p hp
  refine ⟨thresholdOf d ((d:ℝ)-1/2) (ordersOf p d ((d:ℝ)-1/2)), hdeltapos, ?_⟩
  intro z r hr hrle hP phi hphi hnonconst b hb M Rm Sreg It H hH hdelta
  intro Pm a RD
  obtain ⟨hdir, -, -⟩ := hall M Rm Sreg It H hH hdelta
  obtain ⟨f, hf, hfc, hfsupp, hf0, hfbdd⟩ := aux_prop16_bump z r hr
  have hfmem : MemLp f 2 (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))) :=
    MemLp.of_bound hf.continuous.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hfbdd x).1]; exact (hfbdd x).2)
  have hfL2 : ((hfmem.toLp f : DomainL2 (centeredCube z r hr)) : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))] f := hfmem.coeFn_toLp
  obtain ⟨KD, KK, B, hB0, hae, hmemLp, hnormsum⟩ :=
    hdir z r hr hrle hP phi hphi b hb f hf hfc hfsupp (hfmem.toLp f) hfL2
  obtain ⟨C, hC, hbmain⟩ := Paper.prop_16.1 d hd z r hr hP phi hphi hnonconst b hb f hf hfc hfsupp
    hf0 (hfmem.toLp f) hfL2 ((d : ℝ) - 1 / 2) p B ht0 ht1 hp hB0 true
  refine ⟨C, hC, ?_⟩
  intro h N
  have hδpos : 0 < M.delta := M.shellPrefix.delta_pos
  have hK : (∀ n, AEStronglyMeasurable (KD n) Pm) ∧ (∀ᵐ omega ∂Pm, ∀ n, 0 ≤ KD n omega) :=
    ⟨fun n => (hmemLp n).1.1, hae.mono (fun omega hom n => (hom n).1)⟩
  have hMor : ∀ᵐ omega ∂Pm, ∀ n, ∀ x ∈ (centeredCube z r hr : Set (SpatialCoordinates d)),
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
        localGradientEnergy (a n omega) (s := Metric.ball x rho) Metric.isOpen_ball.measurableSet
          (sobolevGradient (dirichletMinimizer (killedResponseSpace hP) (a n omega) b).val) ≤
          KD n omega * rho ^ ((d : ℝ) - 1 / 2) := by
    filter_upwards [hae] with omega hom n x hx rho h0 h1
    have := (hom n).2.2.1 x hx rho h0 h1
    rwa [aux_prop16_lge_inter] at this
  have hmoms : ∀ n, MemLp (KD n) (ENNReal.ofReal (3 * p)) Pm ∧
      MemLp (RD n) (ENNReal.ofReal (3 * p)) Pm ∧
      eLpNorm (KD n) (ENNReal.ofReal (3 * p)) Pm ≤ ENNReal.ofReal B ∧
      eLpNorm (RD n) (ENNReal.ofReal (3 * p)) Pm ≤ ENNReal.ofReal B := fun n =>
    ⟨(hmemLp n).1, (hmemLp n).2.2.1, (aux_prop16_le_of_add_six (hnormsum n)).1,
      (aux_prop16_le_of_add_six (hnormsum n)).2.2.1⟩
  refine (hbmain M.delta hδpos (hdelta.trans (min_le_left _ _)) M.P M.G1 M.G2 H hH.1 hH.2
    (aux_prop16_kap M) (aux_prop16_kap_pos M) (fun n omega => cutoffPositiveCoefficient M H omega n z hr)
    (fun n omega => aux_prop16_cutoff_ae_exp M H n omega z r hr) KD ?_ ?_ ?_).1 h N
  · exact hK
  · exact hMor
  · exact hmoms

end Paper
end

