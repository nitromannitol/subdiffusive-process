import SubdiffusiveProcess.Paper.tight_static_estimates
import SubdiffusiveProcess.Paper.tight_scale_covariance
import SubdiffusiveProcess.Paper.chaos_growth_cutoff
import SubdiffusiveProcess.Paper.lem_coercivity
import SubdiffusiveProcess.Paper.prop_growth
import SubdiffusiveProcess.Paper.in_J
import SubdiffusiveProcess.Paper.in_poincare
import SubdiffusiveProcess.Paper.in_extension
import SubdiffusiveProcess.Paper.in_responses
import SubdiffusiveProcess.Paper.in_6_16
import SubdiffusiveProcess.Paper.in_iteration
import SubdiffusiveProcess.Lane4.Inputs
import SubdiffusiveProcess.Main.CutoffCoefficient
import SubdiffusiveProcess.Main.CutoffSpeedDensity
import SubdiffusiveProcess.Main.ChaosSampleLaw
import SubdiffusiveProcess.Main.InfraredCharacterization
import SubdiffusiveProcess.Paper.Foundations.CollarSmoothPackage
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import SubdiffusiveProcess.Paper.lem_cutoffs
import SubdiffusiveProcess.Paper.lem_chaos_moments
import SubdiffusiveProcess.Paper.lem_extremes
import SubdiffusiveProcess.Section9.CutoffTranslatedCubeTail
import SubdiffusiveProcess.CoarseGrainingVocab.DeltaLogSquaredTail
import SubdiffusiveProcess.Probability.GrowingMeshEnvelope
import SubdiffusiveProcess.Probability.NativeCommonScaleLaw
import SubdiffusiveProcess.Paper.Foundations.PrefixFieldTransport
import SubdiffusiveProcess.Geometry.Cube
import SubdiffusiveProcess.Paper.tight_static_cut
import SubdiffusiveProcess.Paper.tight_static_coer
import SubdiffusiveProcess.Paper.tight_static_low

open Filter MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open SubdiffusiveProcess
open scoped ENNReal NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Paper

theorem aux_tight_static_speed_measure {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ) :
    volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z)) =
      weightedChaosCutoff M H N om := by
  unfold weightedChaosCutoff
  congr 1
  funext z
  congr 1
  simp only [cutoffSpeedDensity, cutoffPotential, fineDensity, finePotential,
    ← Real.exp_add]
  congr 1
  ring

theorem aux_tight_static_prefix_map {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ) :
    Measure.map (fun omega : BilateralField d => fun i : ℕ =>
      aux_lem_crossing_unforget
        (SubdiffusiveProcess.layerScaling d (N : ℤ)
          (omega ((i : ℤ) - (N : ℤ)))))
      (chaosSampleLaw M).toMeasure = M.P.toMeasure := by
  exact prefix_relabelled_potential_law M N

theorem aux_tight_static_layerScaling_forget {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (j : ℤ) (g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) :
    SubdiffusiveProcess.layerScaling d j
        (aux_lem_crossing_forget g) =
      aux_lem_crossing_forget
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale
          ((3 : ℝ) ^ (-j)) g) := by
  apply ContinuousMap.ext
  intro x
  simp only [SubdiffusiveProcess.layerScaling,
    ContinuousMap.compRightContinuousMap_apply,
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale_apply,
    aux_lem_crossing_forget]
  rfl

theorem aux_tight_static_forget_unforget_ae {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure, ∀ k : ℤ,
      aux_lem_crossing_forget
          (aux_lem_crossing_unforget (omega k)) = omega k := by
  rw [ae_all_iff]
  intro k
  let ν : ProbabilityMeasure C(SpatialCoordinates d, ℝ) :=
    chaosRootFieldLaw M
  have hrange : MeasurableSet (Set.range
      (aux_lem_crossing_forget (d := d))) :=
    aux_lem_crossing_measurableEmbedding_forget.measurableSet_range
  have hfull : ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      omega k ∈ Set.range (aux_lem_crossing_forget (d := d)) := by
    have hmeas : MeasurableSet {omega : BilateralField d |
        omega k ∈ Set.range (aux_lem_crossing_forget (d := d))} :=
      (measurable_pi_apply k) hrange
    rw [ae_iff, ← Set.compl_setOf]
    rw [prob_compl_eq_zero_iff hmeas]
    change (Measure.infinitePi (fun j : ℤ =>
        (SubdiffusiveProcess.scaledLayerLaw d ν j :
          Measure C(SpatialCoordinates d, ℝ))))
      ((fun omega : BilateralField d => omega k) ⁻¹'
        Set.range aux_lem_crossing_forget) = 1
    rw [← Measure.map_apply (measurable_pi_apply k) hrange,
      Measure.infinitePi_map_eval]
    change (Measure.map (SubdiffusiveProcess.layerScaling d k)
        (Measure.map aux_lem_crossing_forget
          (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure)) _ = 1
    rw [Measure.map_map
        (SubdiffusiveProcess.layerScaling d k).continuous.measurable
        aux_lem_crossing_measurable_forget,
      Measure.map_apply
        ((SubdiffusiveProcess.layerScaling d k).continuous.measurable.comp
          aux_lem_crossing_measurable_forget) hrange]
    have hpre : (SubdiffusiveProcess.layerScaling d k ∘
        aux_lem_crossing_forget) ⁻¹'
          Set.range aux_lem_crossing_forget = Set.univ := by
      ext g
      simp only [Set.mem_preimage, Function.comp_apply, Set.mem_range,
        Set.mem_univ, iff_true]
      exact ⟨_, (aux_tight_static_layerScaling_forget k g).symm⟩
    rw [hpre, measure_univ]
  filter_upwards [hfull] with omega homega
  obtain ⟨g, hg⟩ := homega
  rw [← hg]
  exact congrArg aux_lem_crossing_forget
    (aux_lem_crossing_unforget_forget g)

theorem aux_tight_static_prefix_density {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (omega : BilateralField d) (x : SpatialCoordinates d) :
    (hω : ∀ i : ℕ,
      aux_lem_crossing_forget
          (aux_lem_crossing_unforget
            (SubdiffusiveProcess.layerScaling d (N : ℤ)
              (omega ((i : ℤ) - (N : ℤ))))) =
        SubdiffusiveProcess.layerScaling d (N : ℤ)
          (omega ((i : ℤ) - (N : ℤ)))) →
    SubdiffusiveProcess.Frozen.Assumptions.aCutoff M N
        (fun i : ℕ => aux_lem_crossing_unforget
          (SubdiffusiveProcess.layerScaling d (N : ℤ)
            (omega ((i : ℤ) - (N : ℤ))))) x =
      fineDensity M N omega ((3 : ℝ) ^ (-(N : ℤ)) • x) := by
  intro hω
  have hsum : ∀ i : ℕ,
      (aux_lem_crossing_unforget
          (SubdiffusiveProcess.layerScaling d (N : ℤ)
            (omega ((i : ℤ) - (N : ℤ))))).1.1 x =
    (omega ((i : ℤ) - (N : ℤ))) ((3 : ℝ) ^ (-(N : ℤ)) • x) := by
    intro i
    change aux_lem_crossing_forget
        (aux_lem_crossing_unforget
          (SubdiffusiveProcess.layerScaling d (N : ℤ)
            (omega ((i : ℤ) - (N : ℤ))))) x = _
    rw [hω i]
    rfl
  unfold SubdiffusiveProcess.Frozen.Assumptions.aCutoff fineDensity finePotential
  simp_rw [hsum]
  congr 1
  let f : ℕ → ℝ := fun j =>
    (omega (-Int.ofNat j)) ((3 : ℝ) ^ (-(N : ℤ)) • x) -
      SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P
  calc
    (∑ i ∈ Finset.range (N + 1),
        ((omega ((i : ℤ) - (N : ℤ))) ((3 : ℝ) ^ (-(N : ℤ)) • x) -
          SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P)) =
      ∑ i ∈ Finset.range (N + 1), f (N - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [f]
        congr 2
        have hiN : i ≤ N := by
          exact Nat.lt_succ_iff.mp (by simpa using hi)
        push_cast
        rw [Nat.cast_sub hiN]
        ring_nf
    _ = ∑ i ∈ Finset.range (N + 1), f i := by
      simpa using Finset.sum_range_reflect f (N + 1)
    _ = ∑ j ∈ Finset.range (N + 1),
        (omega (-Int.ofNat j)) ((3 : ℝ) ^ (-(N : ℤ)) • x) -
          (N + 1 : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P := by
      dsimp [f]
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_range]
      push_cast
      ring

theorem aux_tight_static_prefix_density_ae {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (N : ℕ)
    (x : SpatialCoordinates d) :
    ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M N
          (fun i : ℕ => aux_lem_crossing_unforget
            (SubdiffusiveProcess.layerScaling d (N : ℤ)
              (omega ((i : ℤ) - (N : ℤ))))) x =
        fineDensity M N omega ((3 : ℝ) ^ (-(N : ℤ)) • x) := by
  filter_upwards [aux_tight_static_forget_unforget_ae M] with omega hω
  apply aux_tight_static_prefix_density M N omega x
  intro i
  let k : ℤ := (i : ℤ) - (N : ℤ)
  let g : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d :=
    aux_lem_crossing_unforget (omega k)
  let g' : SubdiffusiveProcess.Frozen.Assumptions.PotentialField d :=
    SubdiffusiveProcess.Frozen.Assumptions.PotentialField.spatialScale
      ((3 : ℝ) ^ (-(N : ℤ))) g
  have hg : aux_lem_crossing_forget g = omega k := hω k
  have hscaled : SubdiffusiveProcess.layerScaling d (N : ℤ)
        (omega k) = aux_lem_crossing_forget g' := by
    rw [← hg]
    exact (aux_tight_static_layerScaling_forget (N : ℤ) g).symm
  calc
    aux_lem_crossing_forget
          (aux_lem_crossing_unforget
            (SubdiffusiveProcess.layerScaling d (N : ℤ)
              (omega ((i : ℤ) - (N : ℤ))))) =
        aux_lem_crossing_forget
          (aux_lem_crossing_unforget
            (SubdiffusiveProcess.layerScaling d (N : ℤ) (omega k))) := by
          rfl
    _ = aux_lem_crossing_forget (aux_lem_crossing_unforget
          (aux_lem_crossing_forget g')) := by rw [hscaled]
    _ = aux_lem_crossing_forget g' := by
      exact congrArg aux_lem_crossing_forget
        (aux_lem_crossing_unforget_forget g')
    _ = SubdiffusiveProcess.layerScaling d (N : ℤ) (omega k) := hscaled.symm

theorem aux_tight_static_measurable_majorant {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsFiniteMeasure P] {f : Omega → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p P) :
    ∃ K : Omega → ℝ, Measurable K ∧ (∀ om, 1 ≤ K om) ∧ MemLp K p P ∧
      ∀ᵐ om ∂P, f om ≤ K om := by
  let g := hf.1.mk f
  have hg : Measurable g := hf.1.measurable_mk
  have hfg : f =ᵐ[P] g := hf.1.ae_eq_mk
  have hgp : MemLp g p P := (memLp_congr_ae hfg).mp hf
  have hconst : MemLp (fun _ : Omega => (1 : ℝ)) p P := memLp_const 1
  have hsum : MemLp (fun om => (1 : ℝ) + ‖g om‖) p P := hconst.add hgp.norm
  have hmeas : Measurable (fun om => (1 : ℝ) + ‖g om‖) := measurable_const.add hg.norm
  refine ⟨fun om => (1 : ℝ) + ‖g om‖, hmeas,
    fun om => le_add_of_nonneg_right (norm_nonneg _), hsum, ?_⟩
  filter_upwards [hfg] with om hom
  rw [hom]
  exact (le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)

theorem aux_tight_static_tail_recursion_tendsto_zero
    (g err : ℕ → ℝ) (rho : ℝ) (hg : Antitone g) (hgnonneg : ∀ n, 0 ≤ g n)
    (hgrho : ∀ n, g n ≤ rho) (hrho : rho < 1)
    (herr : Tendsto err atTop (𝓝 0))
    (hrec : ∀ n, g (n + 1) ≤ err n + (g n) ^ 2) : Tendsto g atTop (𝓝 0) := by
  have hbdd : BddBelow (Set.range g) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hgnonneg n⟩
  have ht := tendsto_atTop_ciInf hg hbdd
  have hlimnonneg : 0 ≤ iInf g := ge_of_tendsto ht (Eventually.of_forall hgnonneg)
  have hlimrho : iInf g ≤ rho := le_of_tendsto ht (Eventually.of_forall hgrho)
  have hshift : Tendsto (fun n : ℕ => g (n + 1)) atTop (𝓝 (iInf g)) :=
    ht.comp (tendsto_add_atTop_nat 1)
  have hlimsq : iInf g ≤ (iInf g) ^ 2 := by
    have h := le_of_tendsto_of_tendsto hshift (herr.add (ht.pow 2))
      (Eventually.of_forall hrec)
    simpa only [zero_add] using h
  have hzero : iInf g = 0 := by
    have hlt : iInf g < 1 := hlimrho.trans_lt hrho
    nlinarith
  simpa only [hzero] using ht

theorem aux_tight_static_tail_recursion_exp_bound
    (g err : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hb2 : b ≤ 2)
    (hg : ∀ n, 0 ≤ g n)
    (hbase : g 0 ≤ (1 / 2 : ℝ) * Real.exp (-a))
    (herr : ∀ n, err n ≤ (1 / 4 : ℝ) * Real.exp (-a * b ^ (n + 1)))
    (hrec : ∀ n, g (n + 1) ≤ err n + (g n) ^ 2) :
    ∀ n, g n ≤ (1 / 2 : ℝ) * Real.exp (-a * b ^ n) := by
  intro n
  induction n with
  | zero => simpa only [pow_zero, mul_one] using hbase
  | succ n ih =>
      have hsquare : (g n) ^ 2 ≤ ((1 / 2 : ℝ) * Real.exp (-a * b ^ n)) ^ 2 :=
        pow_le_pow_left₀ (hg n) ih 2
      have hpow : -a * b ^ n + -a * b ^ n ≤ -a * b ^ (n + 1) := by
        rw [pow_succ]
        have hmul := mul_le_mul_of_nonneg_left hb2 (mul_nonneg ha (pow_nonneg hb n))
        nlinarith only [hmul]
      have hexp := Real.exp_le_exp.mpr hpow
      have hs : ((1 / 2 : ℝ) * Real.exp (-a * b ^ n)) ^ 2 ≤
          (1 / 4 : ℝ) * Real.exp (-a * b ^ (n + 1)) := by
        calc
          _ = (1 / 4 : ℝ) * Real.exp (-a * b ^ n + -a * b ^ n) := by
            rw [Real.exp_add]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by norm_num)
      exact (hrec n).trans (by linarith only [herr n, hsquare, hs])

theorem aux_tight_static_mass_split_probability
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (X B Y Z : Omega → ℝ) (b u : ℝ) (hb : 0 ≤ b)
    (hindep : IndepFun Y Z P)
    (hbound : ∀ᵐ om ∂P, 0 ≤ Y om ∧ 0 ≤ Z om ∧ B om * (Y om + Z om) ≤ X om) :
    P ({om : Omega | X om < b * u} : Set Omega) ≤
      P ({om : Omega | B om < b} : Set Omega) +
        P ({om : Omega | Y om < u} : Set Omega) *
          P ({om : Omega | Z om < u} : Set Omega) := by
  have hsubset : ({om : Omega | X om < b * u} : Set Omega) ≤ᵐ[P]
      (Set.union ({om : Omega | B om < b} : Set Omega)
        (Set.inter ({om : Omega | Y om < u} : Set Omega)
          ({om : Omega | Z om < u} : Set Omega))) := by
    filter_upwards [hbound] with om hom
    intro hx
    by_cases hB : B om < b
    · exact Or.inl hB
    · have hbB : b ≤ B om := le_of_not_gt hB
      have hsum : 0 ≤ Y om + Z om := add_nonneg hom.1 hom.2.1
      have hprod : b * (Y om + Z om) ≤ X om :=
        (mul_le_mul_of_nonneg_right hbB hsum).trans hom.2.2
      refine Or.inr ⟨?_, ?_⟩
      · by_contra hY
        have hu : u ≤ Y om + Z om :=
          (le_of_not_gt hY).trans (le_add_of_nonneg_right hom.2.1)
        exact (not_lt_of_ge ((mul_le_mul_of_nonneg_left hu hb).trans hprod)) hx
      · by_contra hZ
        have hu : u ≤ Y om + Z om :=
          (le_of_not_gt hZ).trans (le_add_of_nonneg_left hom.1)
        exact (not_lt_of_ge ((mul_le_mul_of_nonneg_left hu hb).trans hprod)) hx
  calc
    _ ≤ P (Set.union ({om : Omega | B om < b} : Set Omega)
        (Set.inter ({om : Omega | Y om < u} : Set Omega)
          ({om : Omega | Z om < u} : Set Omega))) :=
      measure_mono_ae hsubset
    _ ≤ P ({om : Omega | B om < b} : Set Omega) +
        P (Set.inter ({om : Omega | Y om < u} : Set Omega)
          ({om : Omega | Z om < u} : Set Omega)) := measure_union_le _ _
    _ = _ := by
      change P ({om : Omega | B om < b} : Set Omega) +
          P ((Y ⁻¹' Set.Iio u) ∩ (Z ⁻¹' Set.Iio u)) =
        P ({om : Omega | B om < b} : Set Omega) +
          P (Y ⁻¹' Set.Iio u) * P (Z ⁻¹' Set.Iio u)
      have hi : P ((Y ⁻¹' Set.Iio u) ∩ (Z ⁻¹' Set.Iio u)) =
          P (Y ⁻¹' Set.Iio u) * P (Z ⁻¹' Set.Iio u) :=
        hindep.measure_inter_preimage_eq_mul (Set.Iio u) (Set.Iio u)
          measurableSet_Iio measurableSet_Iio
      rw [hi]

theorem aux_tight_static_mass_split_exp_probability
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (X B Y Z : Omega → ℝ) (s err g : ℝ) (herr : 0 ≤ err)
    (hindep : IndepFun Y Z P)
    (hbound : ∀ᵐ om ∂P, 0 ≤ Y om ∧ 0 ≤ Z om ∧ B om * (Y om + Z om) ≤ X om)
    (hB : P ({om : Omega | B om < Real.exp (-s / 4)} : Set Omega) ≤ ENNReal.ofReal err)
    (hY : P ({om : Omega | Y om < Real.exp (-(3 * s / 4))} : Set Omega) ≤
      ENNReal.ofReal g)
    (hZ : P ({om : Omega | Z om < Real.exp (-(3 * s / 4))} : Set Omega) ≤
      ENNReal.ofReal g) :
    P ({om : Omega | X om < Real.exp (-s)} : Set Omega) ≤
      ENNReal.ofReal (err + g ^ 2) := by
  have heq : Real.exp (-s / 4) * Real.exp (-(3 * s / 4)) = Real.exp (-s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h := aux_tight_static_mass_split_probability P X B Y Z
    (Real.exp (-s / 4)) (Real.exp (-(3 * s / 4))) (Real.exp_pos _).le hindep hbound
  rw [heq] at h
  calc
    _ ≤ ENNReal.ofReal err + ENNReal.ofReal g * ENNReal.ofReal g :=
      h.trans (add_le_add hB (mul_le_mul' hY hZ))
    _ ≤ ENNReal.ofReal err + ENNReal.ofReal (g ^ 2) := by
      have hpow : ENNReal.ofReal g * ENNReal.ofReal g ≤
          ENNReal.ofReal (g ^ 2) := by
        by_cases hg : 0 ≤ g
        · rw [← ENNReal.ofReal_mul hg]
          simp [pow_two]
        · have hg' : g ≤ 0 := le_of_not_ge hg
          simp [ENNReal.ofReal_of_nonpos hg']
      exact add_le_add_right hpow _
    _ = _ := (ENNReal.ofReal_add herr (sq_nonneg g)).symm

theorem aux_tight_static_inverse_memLp {Omega : Type*} [MeasurableSpace Omega]
    {μ : Measure Omega} [IsProbabilityMeasure μ] {V : Omega → ℝ} {A q : ℝ}
    (hV : Measurable V) (hVpos : ∀ om, 0 < V om)
    (hA : 0 < A) (hq : 0 < q) (hqa : q * A ≤ 1)
    (hX : SubdiffusiveProcess.OGammaLE μ 1 A
      (fun om => |Real.log (V om)| - Real.log 2)) :
    MemLp (fun om => (V om)⁻¹) (ENNReal.ofReal q) μ := by
  let G : Omega → ℝ := fun om =>
    Real.exp (A⁻¹ * max (|Real.log (V om)| - Real.log 2) 0)
  have hGm : Measurable G := by
    dsimp only [G]
    fun_prop
  have hGi : Integrable G μ := by
    simpa only [G, SubdiffusiveProcess.OGammaLE, Real.rpow_one] using hX.1
  have hG : MemLp G 1 μ := memLp_one_iff_integrable.mpr hGi
  have hFm : Measurable (fun om => |(V om)⁻¹| ^ q) := by
    fun_prop
  have hFbound : ∀ om, |(V om)⁻¹| ^ q ≤ (2 : ℝ) ^ q * G om := by
    intro om
    have hV0 : 0 ≤ V om := (hVpos om).le
    have hbase : (V om)⁻¹ ≤ 2 *
        Real.exp (max (|Real.log (V om)| - Real.log 2) 0) := by
      by_cases hsmall : V om ≤ 1 / 2
      · have hlog : Real.log (V om) ≤ Real.log (1 / 2 : ℝ) :=
          Real.strictMonoOn_log.monotoneOn (hVpos om) (by norm_num) hsmall
        have hlog' : Real.log (V om) ≤ -Real.log 2 := by
          simpa [Real.log_div] using hlog
        have hlognonpos : Real.log (V om) ≤ 0 := by
          exact hlog'.trans (neg_nonpos.mpr (Real.log_nonneg (by norm_num)))
        have hneg : 0 ≤ -Real.log (V om) - Real.log 2 := by linarith
        rw [abs_of_nonpos hlognonpos, max_eq_left hneg]
        rw [Real.exp_sub, Real.exp_neg, Real.exp_log (hVpos om),
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        field_simp
        rfl
      · have hhalf : (1 / 2 : ℝ) ≤ V om := le_of_not_ge hsmall
        have hlogabs : |Real.log (V om)| - Real.log 2 ≤
            max (|Real.log (V om)| - Real.log 2) 0 := le_max_left _ _
        have hmax : 1 / V om ≤ 2 * Real.exp (max
            (|Real.log (V om)| - Real.log 2) 0) := by
          have hpos : 0 < Real.exp (max
              (|Real.log (V om)| - Real.log 2) 0) := Real.exp_pos _
          have htwo : (1 : ℝ) ≤ 2 * Real.exp (max
              (|Real.log (V om)| - Real.log 2) 0) * V om := by
            by_cases hlarge : 0 ≤ |Real.log (V om)| - Real.log 2
            · rw [max_eq_left hlarge]
              calc
                1 ≤ Real.exp (Real.log 2 +
                    (|Real.log (V om)| - Real.log 2) + Real.log (V om)) := by
                  apply Real.one_le_exp
                  nlinarith [neg_le_abs (Real.log (V om))]
                _ = 2 * Real.exp (|Real.log (V om)| - Real.log 2) * V om := by
                  rw [Real.exp_add, Real.exp_add,
                    Real.exp_log (by norm_num : (0 : ℝ) < 2),
                    Real.exp_log (hVpos om)]
            · have hle : |Real.log (V om)| - Real.log 2 ≤ 0 := le_of_not_ge hlarge
              rw [max_eq_right hle]
              simp only [Real.exp_zero]
              nlinarith [hhalf]
          exact (div_le_iff₀ (hVpos om)).2 (by simpa [mul_comm] using htwo)
        simpa [one_div] using hmax
    have hbase_nonneg : 0 ≤ (V om)⁻¹ := inv_nonneg.mpr hV0
    have hexp_nonneg : 0 ≤ Real.exp (max
        (|Real.log (V om)| - Real.log 2) 0) := (Real.exp_pos _).le
    have hpow := Real.rpow_le_rpow hbase_nonneg hbase (le_of_lt hq)
    have hqA : q ≤ A⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ hA).2
      nlinarith
    have hGpow : Real.exp (max
        (|Real.log (V om)| - Real.log 2) 0) ^ q ≤ G om := by
      dsimp only [G]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      apply Real.exp_le_exp.mpr
      have hmaxnonneg : 0 ≤ max (|Real.log (V om)| - Real.log 2) 0 :=
        le_max_right _ _
      nlinarith
    calc
      |(V om)⁻¹| ^ q ≤ (2 * Real.exp (max
          (|Real.log (V om)| - Real.log 2) 0)) ^ q := by
            simpa only [abs_of_nonneg hbase_nonneg] using hpow
      _ = (2 : ℝ) ^ q * Real.exp (max
          (|Real.log (V om)| - Real.log 2) 0) ^ q := by
        rw [Real.mul_rpow (by norm_num) hexp_nonneg]
      _ ≤ (2 : ℝ) ^ q * G om := by
        exact mul_le_mul_of_nonneg_left hGpow (Real.rpow_nonneg (by norm_num) _)
  have hF : MemLp (fun om => |(V om)⁻¹| ^ q) 1 μ := by
    apply (hG.const_mul ((2 : ℝ) ^ q)).of_le hFm.aestronglyMeasurable
    filter_upwards with om
    have hleft : 0 ≤ |(V om)⁻¹| ^ q := Real.rpow_nonneg (abs_nonneg _) _
    have hcoef : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
    have hGnonneg : 0 ≤ G om := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hleft, abs_mul,
      abs_of_nonneg hcoef, abs_of_nonneg hGnonneg] using hFbound om
  have hq0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
  have hqtop : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  apply (integrable_norm_rpow_iff ((hV.inv).aestronglyMeasurable)
    hq0 hqtop).mp
  simpa only [ENNReal.toReal_ofReal hq.le, Real.norm_eq_abs] using hF.integrable le_rfl

theorem aux_tight_static_source_inverse_memLp
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (p Ctail : ℝ)
    (hp : 0 < p) (hCtail : 0 < Ctail)
    (hsmall : p * (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤ 1)
    (hsource : SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
      (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2)
      (fun omega ↦ |Real.log (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage M m omega)| -
        Real.log 2)) :
    MemLp (fun omega ↦ (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage M m omega)⁻¹)
    (ENNReal.ofReal p) M.P.toMeasure := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdelta_le : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
  have hlog : Real.log M.delta ≠ 0 := by
    exact (Real.log_ne_zero_of_pos_of_ne_one hdelta
      (ne_of_lt (lt_of_le_of_lt hdelta_le (by norm_num))))
  have hA : 0 < Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2 := by
    positivity
  exact aux_tight_static_inverse_memLp
    (SubdiffusiveProcess.Section9.measurable_cutoffOriginCubeAverage M m)
    (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage_pos M m)
    hA hp hsmall hsource

theorem aux_tight_static_source_inverse_uniform
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) (p : ℝ)
    (hp : 0 < p) :
    ∃ delta0 Ctail : ℝ, 0 < delta0 ∧ 0 < Ctail ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ m : ℕ,
        p * (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤ 1 →
        MemLp (fun omega ↦
          (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage M m omega)⁻¹)
          (ENNReal.ofReal p) M.P.toMeasure := by
  obtain ⟨Ctail, delta0, hCtail, hdelta0, hsource⟩ :=
    SubdiffusiveProcess.Section9.exists_cutoffOriginCube_logAbs_ogamma d
  refine ⟨delta0, Ctail, hdelta0, hCtail, ?_⟩
  intro M hM m hsmall
  exact aux_tight_static_source_inverse_memLp hd M m p Ctail hp hCtail hsmall
    (hsource M hM m)

theorem aux_tight_static_inverse_integral_bound {Omega : Type*} [MeasurableSpace Omega]
    {μ : Measure Omega} [IsProbabilityMeasure μ] {V : Omega → ℝ} {A q : ℝ}
    (hV : Measurable V) (hVpos : ∀ om, 0 < V om)
    (hA : 0 < A) (hq : 0 < q) (hqa : q * A ≤ 1)
    (hX : SubdiffusiveProcess.OGammaLE μ 1 A
      (fun om => |Real.log (V om)| - Real.log 2)) :
    ∫ om, |(V om)⁻¹| ^ q ∂μ ≤ (2 : ℝ) ^ q * 2 := by
  let G : Omega → ℝ := fun om =>
    Real.exp (A⁻¹ * max (|Real.log (V om)| - Real.log 2) 0)
  have hGm : Measurable G := by
    dsimp only [G]
    fun_prop
  have hGi : Integrable G μ := by
    simpa only [G, SubdiffusiveProcess.OGammaLE, Real.rpow_one] using hX.1
  have hFm : Measurable (fun om => |(V om)⁻¹| ^ q) := by
    fun_prop
  have hFbound : ∀ om, |(V om)⁻¹| ^ q ≤ (2 : ℝ) ^ q * G om := by
    intro om
    have hV0 : 0 ≤ V om := (hVpos om).le
    have hbase : (V om)⁻¹ ≤ 2 *
        Real.exp (max (|Real.log (V om)| - Real.log 2) 0) := by
      by_cases hsmall : V om ≤ 1 / 2
      · have hlog : Real.log (V om) ≤ Real.log (1 / 2 : ℝ) :=
          Real.strictMonoOn_log.monotoneOn (hVpos om) (by norm_num) hsmall
        have hlog' : Real.log (V om) ≤ -Real.log 2 := by
          simpa [Real.log_div] using hlog
        have hlognonpos : Real.log (V om) ≤ 0 := by
          exact hlog'.trans (neg_nonpos.mpr (Real.log_nonneg (by norm_num)))
        have hneg : 0 ≤ -Real.log (V om) - Real.log 2 := by linarith
        rw [abs_of_nonpos hlognonpos, max_eq_left hneg]
        rw [Real.exp_sub, Real.exp_neg, Real.exp_log (hVpos om),
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        field_simp
        rfl
      · have hhalf : (1 / 2 : ℝ) ≤ V om := le_of_not_ge hsmall
        have hmax : 1 / V om ≤ 2 * Real.exp (max
            (|Real.log (V om)| - Real.log 2) 0) := by
          have hpos : 0 < Real.exp (max
              (|Real.log (V om)| - Real.log 2) 0) := Real.exp_pos _
          have htwo : (1 : ℝ) ≤ 2 * Real.exp (max
              (|Real.log (V om)| - Real.log 2) 0) * V om := by
            by_cases hlarge : 0 ≤ |Real.log (V om)| - Real.log 2
            · rw [max_eq_left hlarge]
              calc
                1 ≤ Real.exp (Real.log 2 +
                    (|Real.log (V om)| - Real.log 2) + Real.log (V om)) := by
                  apply Real.one_le_exp
                  nlinarith [neg_le_abs (Real.log (V om))]
                _ = 2 * Real.exp (|Real.log (V om)| - Real.log 2) * V om := by
                  rw [Real.exp_add, Real.exp_add,
                    Real.exp_log (by norm_num : (0 : ℝ) < 2),
                    Real.exp_log (hVpos om)]
            · have hle : |Real.log (V om)| - Real.log 2 ≤ 0 := le_of_not_ge hlarge
              rw [max_eq_right hle]
              simp only [Real.exp_zero]
              nlinarith [hhalf]
          exact (div_le_iff₀ (hVpos om)).2 (by simpa [mul_comm] using htwo)
        simpa [one_div] using hmax
    have hbase_nonneg : 0 ≤ (V om)⁻¹ := inv_nonneg.mpr hV0
    have hexp_nonneg : 0 ≤ Real.exp (max
        (|Real.log (V om)| - Real.log 2) 0) := (Real.exp_pos _).le
    have hpow := Real.rpow_le_rpow hbase_nonneg hbase (le_of_lt hq)
    have hqA : q ≤ A⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ hA).2
      nlinarith
    have hGpow : Real.exp (max
        (|Real.log (V om)| - Real.log 2) 0) ^ q ≤ G om := by
      dsimp only [G]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      apply Real.exp_le_exp.mpr
      have hmaxnonneg : 0 ≤ max (|Real.log (V om)| - Real.log 2) 0 :=
        le_max_right _ _
      nlinarith
    calc
      |(V om)⁻¹| ^ q ≤ (2 * Real.exp (max
          (|Real.log (V om)| - Real.log 2) 0)) ^ q := by
            simpa only [abs_of_nonneg hbase_nonneg] using hpow
      _ = (2 : ℝ) ^ q * Real.exp (max
          (|Real.log (V om)| - Real.log 2) 0) ^ q := by
        rw [Real.mul_rpow (by norm_num) hexp_nonneg]
      _ ≤ (2 : ℝ) ^ q * G om := by
        exact mul_le_mul_of_nonneg_left hGpow (Real.rpow_nonneg (by norm_num) _)
  have hFint : Integrable (fun om => |(V om)⁻¹| ^ q) μ := by
    apply hGi.const_mul ((2 : ℝ) ^ q) |>.mono' hFm.aestronglyMeasurable
    filter_upwards with om
    have hleft : 0 ≤ |(V om)⁻¹| ^ q := Real.rpow_nonneg (abs_nonneg _) _
    have hcoef : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
    have hGnonneg : 0 ≤ G om := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hleft, abs_mul,
      abs_of_nonneg hcoef, abs_of_nonneg hGnonneg] using hFbound om
  calc
    ∫ om, |(V om)⁻¹| ^ q ∂μ ≤ ∫ om, (2 : ℝ) ^ q * G om ∂μ :=
      integral_mono_ae hFint
        (hGi.const_mul ((2 : ℝ) ^ q)) (Filter.Eventually.of_forall hFbound)
    _ = (2 : ℝ) ^ q * ∫ om, G om ∂μ := integral_const_mul _ _
    _ ≤ (2 : ℝ) ^ q * 2 := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
      simpa only [G, Real.rpow_one] using hX.2

theorem aux_tight_static_source_inverse_integral_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ) (p Ctail : ℝ)
    (hp : 0 < p) (hCtail : 0 < Ctail)
    (hsmall : p * (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤ 1)
    (hsource : SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
      (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2)
      (fun omega ↦ |Real.log (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage M m omega)| -
        Real.log 2)) :
    ∫ omega, |(SubdiffusiveProcess.Section9.cutoffOriginCubeAverage M m omega)⁻¹| ^ p
      ∂M.P.toMeasure ≤ (2 : ℝ) ^ p * 2 := by
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hdelta_le : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
  have hlog : Real.log M.delta ≠ 0 := by
    exact (Real.log_ne_zero_of_pos_of_ne_one hdelta
      (ne_of_lt (lt_of_le_of_lt hdelta_le (by norm_num))))
  have hA : 0 < Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2 := by
    positivity
  exact aux_tight_static_inverse_integral_bound
    (SubdiffusiveProcess.Section9.measurable_cutoffOriginCubeAverage M m)
    (SubdiffusiveProcess.Section9.cutoffOriginCubeAverage_pos M m)
    hA hp hsmall hsource

theorem aux_tight_static_translated_source_inverse_integral_bound
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (m : ℕ)
    (z : Homogenization.Vec d) (p Ctail : ℝ) (hp : 0 < p) (hCtail : 0 < Ctail)
    (hsmall : p * (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤ 1)
    (hsource : SubdiffusiveProcess.OGammaLE M.P.toMeasure 1
      (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2)
      (fun omega ↦
        |Real.log (SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M m z omega)| -
          Real.log 2)) :
    ∫ omega, |(SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M m z omega)⁻¹| ^ p
      ∂M.P.toMeasure ≤ (2 : ℝ) ^ p * 2 := by
  let c : Homogenization.Vec d := fun i ↦ z i + (3 : ℝ) ^ m / 2
  have heq : SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M m z =
      SubdiffusiveProcess.Section9.cutoffOriginCubeAverage M m ∘
        SubdiffusiveProcess.CoarseGrainingVocab.translatePotentialSequence c := by
    funext omega
    exact SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage_eq_origin_translate M m z omega
  have hmeas : Measurable (SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M m z) := by
    rw [heq]
    exact (SubdiffusiveProcess.Section9.measurable_cutoffOriginCubeAverage M m).comp
      (SubdiffusiveProcess.CoarseGrainingVocab.measurable_translatePotentialSequence c)
  have hpos : ∀ omega, 0 < SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M m z omega := by
    intro omega
    rw [heq]
    exact SubdiffusiveProcess.Section9.cutoffOriginCubeAverage_pos M m _
  have hdelta : 0 < M.delta := M.shellPrefix.delta_pos
  have hA : 0 < Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2 := by
    have hdelta_le : M.delta ≤ 1 / 2 := M.shellPrefix.delta_le_half
    have hlog : Real.log M.delta ≠ 0 := by
      exact (Real.log_ne_zero_of_pos_of_ne_one hdelta
        (ne_of_lt (lt_of_le_of_lt hdelta_le (by norm_num))))
    positivity
  exact aux_tight_static_inverse_integral_bound hmeas hpos hA hp hsmall hsource

theorem aux_tight_static_density_scale_nat_explicit
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hH : InfraredCharacterization M H) (j N : ℕ) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ x : SpatialCoordinates d,
      cutoffSpeedDensity M H om N ((3 : ℝ) ^ j • x) =
        Real.exp ((j : ℝ) * SubdiffusiveProcess.Frozen.Assumptions.tauSq M.P -
          aux_prop_growth_large_root_irAnchor j om) *
          cutoffSpeedDensity M H
            (aux_tight_scale_covariance_scaleShift (j : ℤ) om) (N + j) x := by
  filter_upwards [aux_prop_growth_large_root_ae_infrared_scaleShift hH j] with om hom
  intro x
  have hpot0 := aux_prop_growth_large_root_cutoffPotential_scaleShift H om j N hom x
  have hpot : cutoffPotential H om N ((3 : ℝ) ^ j • x) =
      cutoffPotential H
          (aux_tight_scale_covariance_scaleShift (j : ℤ) om) (N + j) x -
        aux_prop_growth_large_root_irAnchor j om := by
    simpa only [aux_tight_scale_covariance_scaleShift_nat] using hpot0
  unfold cutoffSpeedDensity
  rw [hpot, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem aux_tight_static_translated_source_inverse_uniform
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d) (p : ℝ)
    (hp : 0 < p) :
    ∃ delta0 Ctail : ℝ, 0 < delta0 ∧ 0 < Ctail ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ (m : ℕ) (z : Homogenization.Vec d),
        p * (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤ 1 →
        ∫ omega,
            |(SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M m z omega)⁻¹| ^ p
          ∂M.P.toMeasure ≤ (2 : ℝ) ^ p * 2 := by
  obtain ⟨Ctail, delta0, hCtail, hdelta0, hsource⟩ :=
    SubdiffusiveProcess.Section9.exists_cutoffTranslatedAxisCube_logAbs_ogamma d
  refine ⟨delta0, Ctail, hdelta0, hCtail, ?_⟩
  intro M hM m z hsmall
  exact aux_tight_static_translated_source_inverse_integral_bound hd M m z p Ctail
    hp hCtail hsmall (hsource M hM m z)

theorem aux_tight_static_log_square_threshold (q Ctail : ℝ) (hq : 0 < q)
    (hCtail : 0 < Ctail) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        q * (Ctail * delta ^ 2 * |Real.log delta| ^ 2) ≤ 1 := by
  let A : ℝ := q * Ctail
  have hA : 0 < A := mul_pos hq hCtail
  have hAplus : 0 < A + 1 := by linarith
  obtain ⟨delta0, hdelta0, _, hcal⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.exists_smallDelta_mul_abs_log_le
      (eps := (A + 1)⁻¹) (by positivity)
  refine ⟨delta0, hdelta0, ?_⟩
  intro delta hdelta hle
  have hcal' := hcal delta hdelta hle
  have hcal_nonneg : 0 ≤ delta * |Real.log delta| := by positivity
  have hcal_rhs_nonneg : 0 ≤ (A + 1)⁻¹ := inv_nonneg.mpr hAplus.le
  have hsq : (delta * |Real.log delta|) ^ 2 ≤ ((A + 1)⁻¹) ^ 2 := by
    nlinarith [sq_nonneg (delta * |Real.log delta| - (A + 1)⁻¹)]
  have hbound : A * ((A + 1)⁻¹) ^ 2 ≤ 1 := by
    rw [inv_pow]
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ (sq_pos_of_pos hAplus)).2
    nlinarith [sq_nonneg A]
  dsimp only [A] at hA hbound ⊢
  calc
    q * (Ctail * delta ^ 2 * |Real.log delta| ^ 2) =
        (q * Ctail) * (delta * |Real.log delta|) ^ 2 := by ring
    _ ≤ (q * Ctail) * ((q * Ctail + 1)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hA.le
    _ ≤ 1 := hbound

theorem aux_tight_static_upper
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (q : ℝ) (hq : 1 ≤ q) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d), M.delta ≤ delta0 →
      ∀ rho0 : ℝ, 1 ≤ rho0 → ∃ C : ℝ, 0 < C ∧
      ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ), InfraredCharacterization M H →
      ∃ K : BilateralField d → ℝ, Measurable K ∧ (∀ om, 1 ≤ K om) ∧
        (∫⁻ om, ENNReal.ofReal (K om ^ q) ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal C ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ,
          ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
            x ∈ Metric.ball (0 : SpatialCoordinates d) (rho0 / 2) →
            volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z))
                (Metric.ball x r) ≤ ENNReal.ofReal (K om * r ^ ((d : ℝ) - 1 / 2)) := by
  obtain ⟨p, hp⟩ := exists_nat_gt (max q (2 * (d : ℝ)))
  have hpq : q ≤ (p : ℝ) := (le_max_left _ _).trans hp.le
  have hpd : (d : ℝ) < (p : ℝ) * (1 / 2) := by
    have h := (le_max_right q (2 * (d : ℝ))).trans_lt hp
    linarith
  obtain ⟨delta0, hd0, hdelta⟩ := chaos_growth_cutoff hd (1 / 2) (by norm_num) p hpd
  refine ⟨delta0, hd0, ?_⟩
  intro M hM rho0 hrho
  obtain ⟨H0, hH0⟩ := exists_infraredCharacterization hd M
  obtain ⟨f, hf, hbound⟩ := hdelta M H0 hH0 hM
    (Metric.ball (0 : SpatialCoordinates d) (rho0 / 2)) Metric.isBounded_ball
  obtain ⟨K, hKmeas, hKone, hKp, hKf⟩ := aux_tight_static_measurable_majorant hf
  have hKq : MemLp K (ENNReal.ofReal q) (chaosSampleLaw M).toMeasure := by
    apply hKp.mono_exponent
    exact_mod_cast (ENNReal.ofReal_le_ofReal hpq)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hKnonneg : ∀ om, 0 ≤ K om := fun om => zero_le_one.trans (hKone om)
  have hfin : (∫⁻ om, ENNReal.ofReal (K om ^ q) ∂(chaosSampleLaw M).toMeasure) < ⊤ := by
    have ht := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (ENNReal.ofReal_ne_zero_iff.mpr hqpos) ENNReal.ofReal_ne_top hKq.2
    simpa only [ENNReal.toReal_ofReal hqpos.le, Real.enorm_eq_ofReal (hKnonneg _),
      ENNReal.ofReal_rpow_of_nonneg (hKnonneg _) hqpos.le] using ht
  let C := (∫⁻ om, ENNReal.ofReal (K om ^ q) ∂(chaosSampleLaw M).toMeasure).toReal + 1
  have hC : 0 < C := add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one
  refine ⟨C, hC, ?_⟩
  intro H hH
  refine ⟨K, hKmeas, hKone, ?_, ?_⟩
  · calc
      _ = ENNReal.ofReal (∫⁻ om, ENNReal.ofReal (K om ^ q)
          ∂(chaosSampleLaw M).toMeasure).toReal := (ENNReal.ofReal_toReal hfin.ne).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)
  · filter_upwards [hbound, hKf, hH.2, hH0.2] with om hb hk hom hom0
    have heq : H om = H0 om := tendsto_nhds_unique hom hom0
    intro N x r hr hr1 hx
    rw [aux_tight_static_speed_measure]
    have hw : weightedChaosCutoff M H N om = weightedChaosCutoff M H0 N om := by
      unfold weightedChaosCutoff
      rw [heq]
    rw [hw]
    exact (hb.2 N x hx r hr hr1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hr.le _)))

theorem aux_tight_static_lower_density_of_pointwise
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (b : SpatialCoordinates d → ℝ) (K : ℝ) (x : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (hK : 0 < K)
    (hpoint : ∀ y ∈ Metric.ball x r,
      K⁻¹ * r ^ (1 / 2 : ℝ) ≤ b y) :
    ENNReal.ofReal (K⁻¹ * r ^ ((d : ℝ) + 1 / 2)) ≤
      volume.withDensity (fun z => ENNReal.ofReal (b z)) (Metric.ball x r) := by
  rw [withDensity_apply _ Metric.isOpen_ball.measurableSet]
  calc
    ENNReal.ofReal (K⁻¹ * r ^ ((d : ℝ) + 1 / 2)) ≤
        ENNReal.ofReal (K⁻¹ * r ^ (1 / 2 : ℝ)) *
          ENNReal.ofReal ((2 * r) ^ d) := by
      rw [← ENNReal.ofReal_mul]
      · apply ENNReal.ofReal_le_ofReal
        have hKinv : 0 ≤ K⁻¹ := inv_nonneg.mpr hK.le
        have hr0 : 0 ≤ r := hr.le
        have hrpow : 0 ≤ r ^ (1 / 2 : ℝ) := Real.rpow_nonneg hr0 _
        have hrd : 0 ≤ r ^ (d : ℝ) := Real.rpow_nonneg hr0 _
        have htwo : 1 ≤ (2 : ℝ) ^ d := by
          exact one_le_pow₀ (by norm_num)
        have hmul : r ^ (1 / 2 : ℝ) * r ^ (d : ℝ) =
            r ^ ((d : ℝ) + 1 / 2) := by
          rw [← Real.rpow_add hr]
          congr 1
          ring
        have hrd2 : r ^ (d : ℝ) ≤ (2 : ℝ) ^ d * r ^ (d : ℝ) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right htwo hrd
        rw [show (2 * r) ^ d = (2 : ℝ) ^ d * r ^ d by ring]
        calc
          K⁻¹ * r ^ ((d : ℝ) + 1 / 2) =
              K⁻¹ * (r ^ (1 / 2 : ℝ) * r ^ (d : ℝ)) := by rw [hmul]
          _ ≤ K⁻¹ * (r ^ (1 / 2 : ℝ) * ((2 : ℝ) ^ d * r ^ (d : ℝ))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hrd2 hrpow)
              hKinv
          _ = K⁻¹ * r ^ (1 / 2 : ℝ) * ((2 : ℝ) ^ d * r ^ d) := by
            simp only [Real.rpow_natCast]
            ring
      · exact mul_nonneg (inv_nonneg.mpr hK.le) (Real.rpow_nonneg hr.le _)
    _ = ∫⁻ y in Metric.ball x r,
          ENNReal.ofReal (K⁻¹ * r ^ (1 / 2 : ℝ)) ∂volume := by
      rw [setLIntegral_const, volume_ball_spatial x hr]
    _ ≤ ∫⁻ y in Metric.ball x r, ENNReal.ofReal (b y) ∂volume := by
      apply setLIntegral_mono'
        Metric.isOpen_ball.measurableSet
      intro y hy
      exact ENNReal.ofReal_le_ofReal (hpoint y hy)

theorem aux_tight_static_estimates_mono
    {d : ℕ} (b A : SpatialCoordinates d → ℝ) (rho0 K₁ K₂ B : ℝ)
    (hrho0 : 0 < rho0) (hK₁ : 0 < K₁) (hKle : K₁ ≤ K₂)
    (hE : tight_static_estimates b A rho0 K₁ B) :
    tight_static_estimates b A rho0 K₂ B := by
  have hK₂ : 0 < K₂ := lt_of_lt_of_le hK₁ hKle
  have hinv : K₂⁻¹ ≤ K₁⁻¹ := by
    exact (inv_le_inv₀ hK₂ hK₁).2 hKle
  unfold tight_static_estimates at hE ⊢
  rcases hE with ⟨hMass, hCoer, hCut⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x r hr hr1 hsub
    constructor
    · exact (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hinv (Real.rpow_nonneg hr.le _))).trans
        (hMass x r hr hr1 hsub).1
    · exact (hMass x r hr hr1 hsub).2.trans
        (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hKle (Real.rpow_nonneg hr.le _)))
  · intro q hq hq1
    constructor
    · intro v
      refine (hCoer q hq hq1).1 v |>.trans ?_
      apply mul_le_mul'
      · exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hKle (by positivity))
      · exact le_rfl
    · intro v
      refine (hCoer q hq hq1).2 v |>.trans ?_
      apply mul_le_mul'
      · exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hKle (by positivity))
      · exact le_rfl
  · intro q1 q2 hq1 hq12 hq2
    obtain ⟨chi, hchi0, hchi1, hsupp, henergy⟩ := hCut q1 q2 hq1 hq12 hq2
    refine ⟨chi, hchi0, hchi1, hsupp, ?_⟩
    intro x r hr hr1
    refine henergy x r hr hr1 |>.trans ?_
    exact ENNReal.ofReal_le_ofReal (by
      calc
        K₁ * (rho0 * ((q2 : ℝ) - q1) / 2) ^ (-B : ℝ) *
              r ^ ((d : ℝ) - 1 / 2) =
            (K₁ * (rho0 * ((q2 : ℝ) - q1) / 2) ^ (-B : ℝ)) *
              r ^ ((d : ℝ) - 1 / 2) := by ring
        _ ≤ (K₂ * (rho0 * ((q2 : ℝ) - q1) / 2) ^ (-B : ℝ)) *
              r ^ ((d : ℝ) - 1 / 2) := by
          apply mul_le_mul_of_nonneg_right
          · have hqgapRat : (q1 : ℝ) < (q2 : ℝ) := by exact_mod_cast hq12
            have hqgap : 0 < (q2 : ℝ) - q1 := sub_pos.mpr hqgapRat
            have hbase : 0 ≤ rho0 * ((q2 : ℝ) - q1) / 2 := by positivity
            exact mul_le_mul_of_nonneg_right hKle (Real.rpow_nonneg
              hbase _)
          · exact Real.rpow_nonneg hr.le _
        _ = K₂ * (rho0 * ((q2 : ℝ) - q1) / 2) ^ (-B : ℝ) *
              r ^ ((d : ℝ) - 1 / 2) := by ring)

theorem aux_tight_static_max_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (q : ℝ) (hq : 1 ≤ q) (f g h k : Ω → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (hk : Measurable k)
    (hf1 : ∀ om, 1 ≤ f om) (hg1 : ∀ om, 1 ≤ g om)
    (hh1 : ∀ om, 1 ≤ h om) (hk1 : ∀ om, 1 ≤ k om)
    (Cf Cg Ch Ck : ℝ)
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hCh : 0 ≤ Ch) (hCk : 0 ≤ Ck)
    (hfm : (∫⁻ om, ENNReal.ofReal (f om ^ q) ∂μ) ≤ ENNReal.ofReal Cf)
    (hgm : (∫⁻ om, ENNReal.ofReal (g om ^ q) ∂μ) ≤ ENNReal.ofReal Cg)
    (hhm : (∫⁻ om, ENNReal.ofReal (h om ^ q) ∂μ) ≤ ENNReal.ofReal Ch)
    (hkm : (∫⁻ om, ENNReal.ofReal (k om ^ q) ∂μ) ≤ ENNReal.ofReal Ck) :
    (∫⁻ om, ENNReal.ofReal ((max (max f g) (max h k)) om ^ q) ∂μ) ≤
      ENNReal.ofReal (Cf + Cg + Ch + Ck) := by
  have hpow : ∀ om, ENNReal.ofReal ((max (max f g) (max h k)) om ^ q) ≤
      ENNReal.ofReal (f om ^ q) + ENNReal.ofReal (g om ^ q) +
        ENNReal.ofReal (h om ^ q) + ENNReal.ofReal (k om ^ q) := by
    intro om
    change ENNReal.ofReal ((max (max (f om) (g om)) (max (h om) (k om))) ^ q) ≤ _
    have hnon (u : ℝ) : 0 ≤ ENNReal.ofReal (u ^ q) := bot_le
    by_cases hout : max (f om) (g om) ≤ max (h om) (k om)
    · rw [max_eq_right hout]
      by_cases hhk : h om ≤ k om
      · rw [max_eq_right hhk]
        calc
          ENNReal.ofReal (k om ^ q) ≤
              ENNReal.ofReal (h om ^ q) + ENNReal.ofReal (k om ^ q) :=
            le_add_of_nonneg_left (hnon _)
          _ ≤ (ENNReal.ofReal (f om ^ q) + ENNReal.ofReal (g om ^ q)) +
              (ENNReal.ofReal (h om ^ q) + ENNReal.ofReal (k om ^ q)) := by
            exact le_add_of_nonneg_left (by positivity)
          _ = _ := by ring
      · have hkh : k om ≤ h om := le_of_not_ge hhk
        rw [max_eq_left hkh]
        calc
          ENNReal.ofReal (h om ^ q) ≤
              ENNReal.ofReal (h om ^ q) + ENNReal.ofReal (k om ^ q) :=
            le_add_of_nonneg_right (hnon _)
          _ ≤ (ENNReal.ofReal (f om ^ q) + ENNReal.ofReal (g om ^ q)) +
              (ENNReal.ofReal (h om ^ q) + ENNReal.ofReal (k om ^ q)) := by
            exact le_add_of_nonneg_left (by positivity)
          _ = _ := by ring
    · have hout' : max (h om) (k om) ≤ max (f om) (g om) := le_of_not_ge hout
      rw [max_eq_left hout']
      by_cases hfg : f om ≤ g om
      · rw [max_eq_right hfg]
        calc
          ENNReal.ofReal (g om ^ q) ≤
              ENNReal.ofReal (f om ^ q) + ENNReal.ofReal (g om ^ q) :=
            le_add_of_nonneg_left (hnon _)
          _ ≤ (ENNReal.ofReal (f om ^ q) + ENNReal.ofReal (g om ^ q)) +
              (ENNReal.ofReal (h om ^ q) + ENNReal.ofReal (k om ^ q)) := by
            exact le_add_of_nonneg_right (by positivity)
          _ = _ := by ring
      · have hgf : g om ≤ f om := le_of_not_ge hfg
        rw [max_eq_left hgf]
        calc
          ENNReal.ofReal (f om ^ q) ≤
              ENNReal.ofReal (f om ^ q) + ENNReal.ofReal (g om ^ q) :=
            le_add_of_nonneg_right (hnon _)
          _ ≤ (ENNReal.ofReal (f om ^ q) + ENNReal.ofReal (g om ^ q)) +
              (ENNReal.ofReal (h om ^ q) + ENNReal.ofReal (k om ^ q)) := by
            exact le_add_of_nonneg_right (by positivity)
          _ = _ := by ring
  have hmeas : Measurable (fun om =>
      ENNReal.ofReal ((max (max f g) (max h k)) om ^ q)) := by
    fun_prop
  have hfgm : Measurable (fun om => ENNReal.ofReal (f om ^ q)) := by fun_prop
  have hggm : Measurable (fun om => ENNReal.ofReal (g om ^ q)) := by fun_prop
  have hhgm : Measurable (fun om => ENNReal.ofReal (h om ^ q)) := by fun_prop
  have hkgm : Measurable (fun om => ENNReal.ofReal (k om ^ q)) := by fun_prop
  calc
    _ ≤ ∫⁻ om, ENNReal.ofReal (f om ^ q) + ENNReal.ofReal (g om ^ q) +
        ENNReal.ofReal (h om ^ q) + ENNReal.ofReal (k om ^ q) ∂μ :=
      lintegral_mono hpow
    _ = (∫⁻ om, ENNReal.ofReal (f om ^ q) ∂μ) +
        (∫⁻ om, ENNReal.ofReal (g om ^ q) ∂μ) +
        (∫⁻ om, ENNReal.ofReal (h om ^ q) ∂μ) +
        (∫⁻ om, ENNReal.ofReal (k om ^ q) ∂μ) := by
      rw [lintegral_add_left' ((hfgm.add hggm).add hhgm).aemeasurable,
        lintegral_add_left' (hfgm.add hggm).aemeasurable,
        lintegral_add_left' hfgm.aemeasurable]
    _ ≤ ENNReal.ofReal Cf + ENNReal.ofReal Cg + ENNReal.ofReal Ch + ENNReal.ofReal Ck := by
      gcongr
    _ = ENNReal.ofReal (Cf + Cg + Ch + Ck) := by
      rw [← ENNReal.ofReal_add hCf hCg,
        ← ENNReal.ofReal_add (add_nonneg hCf hCg) hCh,
        ← ENNReal.ofReal_add (add_nonneg (add_nonneg hCf hCg) hCh) hCk]

theorem aux_tight_static_two_max_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (q : ℝ) (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (Cf Cg : ℝ) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hfm : (∫⁻ om, ENNReal.ofReal (f om ^ q) ∂μ) ≤ ENNReal.ofReal Cf)
    (hgm : (∫⁻ om, ENNReal.ofReal (g om ^ q) ∂μ) ≤ ENNReal.ofReal Cg) :
    (∫⁻ om, ENNReal.ofReal ((max f g) om ^ q) ∂μ) ≤
      ENNReal.ofReal (Cf + Cg) := by
  have hpoint : ∀ om, ENNReal.ofReal ((max f g) om ^ q) ≤
      ENNReal.ofReal (f om ^ q) + ENNReal.ofReal (g om ^ q) := by
    intro om
    change ENNReal.ofReal ((max (f om) (g om)) ^ q) ≤ _
    by_cases h : f om ≤ g om
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (by positivity)
    · have h' : g om ≤ f om := le_of_not_ge h
      rw [max_eq_left h']
      exact le_add_of_nonneg_right (by positivity)
  have hfm' : Measurable (fun om => ENNReal.ofReal (f om ^ q)) := by fun_prop
  have hgm' : Measurable (fun om => ENNReal.ofReal (g om ^ q)) := by fun_prop
  calc
    _ ≤ ∫⁻ om, ENNReal.ofReal (f om ^ q) + ENNReal.ofReal (g om ^ q) ∂μ :=
      lintegral_mono hpoint
    _ = (∫⁻ om, ENNReal.ofReal (f om ^ q) ∂μ) +
        (∫⁻ om, ENNReal.ofReal (g om ^ q) ∂μ) :=
      lintegral_add_left' hfm'.aemeasurable _
    _ ≤ ENNReal.ofReal Cf + ENNReal.ofReal Cg := by gcongr
      _ = ENNReal.ofReal (Cf + Cg) := (ENNReal.ofReal_add hCf hCg).symm

theorem aux_tight_static_smooth_cutoff_basic
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ chi : Homogenization.H10Function
        (centeredCube z R hR : Set (SpatialCoordinates d)),
      (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
      (∀ x,
        Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r →
          chi.toFun x = 0) ∧
      (∀ x,
        3 * r ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
          chi.toFun x = 1) ∧
      tsupport chi.toFun ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) := by
  obtain ⟨theta, htheta, hrange, hzero, hone, _⟩ :=
    lem_20_collar_family_smooth_collar d hd z R hR r hr hr1
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  have hclosed : IsClosed {x : SpatialCoordinates d |
      r ≤ Metric.infDist x Qᶜ} := by
    exact isClosed_le continuous_const (Metric.continuous_infDist_pt Qᶜ)
  have hsupport : Function.support theta ⊆
      {x : SpatialCoordinates d | r ≤ Metric.infDist x Qᶜ} := by
    intro x hx
    by_contra hnot
    exact hx (hzero x (le_of_not_ge hnot))
  have htsupp : tsupport theta ⊆
      {x : SpatialCoordinates d | r ≤ Metric.infDist x Qᶜ} :=
    closure_minimal hsupport hclosed
  have hQ : tsupport theta ⊆ Q := by
    intro x hx
    have hxpos : 0 < Metric.infDist x Qᶜ := lt_of_lt_of_le hr (htsupp hx)
    have hnot : x ∉ Qᶜ := by
      intro hxc
      have hz : Metric.infDist x Qᶜ = 0 := Metric.infDist_zero_of_mem hxc
      exact (ne_of_gt hxpos) hz
    exact Set.notMem_compl_iff.mp hnot
  have hcompact : HasCompactSupport theta := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((centeredCube_isBounded z hR).isCompact_closure)
    exact (subset_tsupport theta).trans (hQ.trans subset_closure)
  let chi : Homogenization.H10Function (centeredCube z R hR : Set (SpatialCoordinates d)) :=
    Homogenization.H10Function.ofContDiff (centeredCube z R hR).isOpen
      htheta hcompact hQ
  refine ⟨chi, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa [chi, Q] using hrange x
  · intro x hx
    simpa [chi, Q] using hzero x hx
  · intro x hx
    simpa [chi, Q] using hone x hx
  · simpa [chi] using hQ

theorem aux_tight_static_smooth_cutoff_with_grad
    {d : ℕ} (hd : 2 ≤ d) (z : SpatialCoordinates d) (R : ℝ) (hR : 0 < R)
    (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ Cgrad : ℝ, 0 < Cgrad ∧
      ∃ chi : Homogenization.H10Function
          (centeredCube z R hR : Set (SpatialCoordinates d)),
        (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
        (∀ x,
          Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ ≤ r →
            chi.toFun x = 0) ∧
        (∀ x,
          3 * r ≤ Metric.infDist x (centeredCube z R hR : Set (SpatialCoordinates d))ᶜ →
            chi.toFun x = 1) ∧
        tsupport chi.toFun ⊆ (centeredCube z R hR : Set (SpatialCoordinates d)) ∧
        (∀ x, ‖chi.grad x‖ ≤ Cgrad / r) := by
  obtain ⟨Cgrad, hCgrad, hCgradAll⟩ :=
    aux_lem_20_collar_family_smooth_collar_uniform_grad d hd z R hR
  obtain ⟨theta, htheta, hthetaSmooth, hthetaRange, hthetaZero,
      hthetaOne, hthetaDerivZero, hthetaGrad⟩ := hCgradAll r hr hr1
  let Q : Set (SpatialCoordinates d) := centeredCube z R hR
  have hclosed : IsClosed {x : SpatialCoordinates d |
      r ≤ Metric.infDist x Qᶜ} := by
    exact isClosed_le continuous_const (Metric.continuous_infDist_pt Qᶜ)
  have hsupport : Function.support theta ⊆
      {x : SpatialCoordinates d | r ≤ Metric.infDist x Qᶜ} := by
    intro x hx
    by_contra hnot
    exact hx (hthetaZero x (le_of_not_ge hnot))
  have htsupp : tsupport theta ⊆
      {x : SpatialCoordinates d | r ≤ Metric.infDist x Qᶜ} :=
    closure_minimal hsupport hclosed
  have hQ : tsupport theta ⊆ Q := by
    intro x hx
    have hxpos : 0 < Metric.infDist x Qᶜ := lt_of_lt_of_le hr (htsupp hx)
    have hnot : x ∉ Qᶜ := by
      intro hxc
      have hz : Metric.infDist x Qᶜ = 0 := Metric.infDist_zero_of_mem hxc
      exact (ne_of_gt hxpos) hz
    exact Set.notMem_compl_iff.mp hnot
  have hcompact : HasCompactSupport theta := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((centeredCube_isBounded z hR).isCompact_closure)
    exact (subset_tsupport theta).trans (hQ.trans subset_closure)
  let chi : Homogenization.H10Function Q :=
    Homogenization.H10Function.ofContDiff (centeredCube z R hR).isOpen
      hthetaSmooth hcompact hQ
  have hgrad : ∀ x, ‖chi.grad x‖ ≤ Cgrad / r := by
    intro x
    rw [show chi.grad x = fun i : Fin d =>
        (fderiv ℝ theta x) (Homogenization.basisVec i) by
      rfl]
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    exact (ContinuousLinearMap.le_opNorm (fderiv ℝ theta x)
      (Homogenization.basisVec i)).trans
      (by simp [hthetaGrad])
  refine ⟨Cgrad, hCgrad, chi, ?_, ?_, ?_, ?_, hgrad⟩
  · intro x
    simpa [chi, Q] using hthetaRange x
  · intro x hx
    simpa [chi, Q] using hthetaZero x hx
  · intro x hx
    simpa [chi, Q] using hthetaOne x hx
  · simpa [chi, Q] using hQ

theorem aux_tight_static_cutoff_geometry
    {d : ℕ} (hd : 2 ≤ d) (rho0 : ℝ) (hrho0 : 1 ≤ rho0)
    (q1 q2 : ℚ) (hq1 : 0 < q1) (hq12 : q1 < q2) (hq2 : q2 ≤ 1) :
    ∃ chi : Homogenization.H10Function
        (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2)),
      (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
      (∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (rho0 * (q1 : ℝ) / 2),
        chi.toFun x = 1) ∧
      tsupport chi.toFun ⊆
        Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2) := by
  have hq1r : 0 < (q1 : ℝ) := by exact_mod_cast hq1
  have hq2r : 0 < (q2 : ℝ) := lt_of_lt_of_le hq1r (by exact_mod_cast hq12.le)
  have hgap : 0 < (q2 : ℝ) - q1 := sub_pos.mpr (by exact_mod_cast hq12)
  let R : ℝ := rho0 * (q2 : ℝ)
  have hR : 0 < R := mul_pos (lt_of_lt_of_le zero_lt_one hrho0) hq2r
  let r : ℝ := min 1 (rho0 * ((q2 : ℝ) - q1) / 10)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r ≤ 1 := min_le_left _ _
  obtain ⟨chi, hrange, hzero, hone, hsupp⟩ :=
    aux_tight_static_smooth_cutoff_basic hd 0 R hR r hr hr1
  let Qset : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) R hR : Set (SpatialCoordinates d))
  have hcomp : Qsetᶜ.Nonempty := by
    exact aux_lem_20_collar_family_smooth_collar_compl_nonempty d hd 0 R hR
  have hplateau : ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (rho0 * (q1 : ℝ) / 2),
      3 * r ≤ Metric.infDist x Qsetᶜ := by
    intro x hx
    apply (Metric.le_infDist hcomp).2
    intro y hy
    have hyout : R / 2 ≤ dist y 0 := by
      have hy' : ¬ dist y 0 < R / 2 := by
        intro hy'
        apply hy
        simpa [Qset, centeredCube, Metric.mem_ball, dist_comm] using hy'
      exact le_of_not_gt hy'
    have hxinner : dist x 0 < rho0 * (q1 : ℝ) / 2 := by
      simpa [Metric.mem_ball, dist_comm] using hx
    have htri : dist y 0 ≤ dist x y + dist x 0 := by
      simpa [dist_comm] using (dist_triangle y x 0)
    have hxy : R / 2 - rho0 * (q1 : ℝ) / 2 ≤ dist x y := by
      linarith
    have hRgap : 0 ≤ rho0 * ((q2 : ℝ) - q1) :=
      mul_nonneg (le_trans zero_le_one hrho0) hgap.le
    have hrbound : 3 * r ≤ rho0 * ((q2 : ℝ) - q1) / 2 := by
      have hrmin : r ≤ rho0 * ((q2 : ℝ) - q1) / 10 := min_le_right _ _
      nlinarith
    have heq : R / 2 - rho0 * (q1 : ℝ) / 2 =
        rho0 * ((q2 : ℝ) - q1) / 2 := by
      dsimp [R]
      ring
    exact hrbound.trans (heq ▸ hxy)
  refine ⟨chi, hrange, ?_, ?_⟩
  · intro x hx
    exact hone x (hplateau x hx)
  · simpa [R, centeredCube] using hsupp

theorem aux_tight_static_cutoff_geometry_with_grad
    {d : ℕ} (hd : 2 ≤ d) (rho0 : ℝ) (hrho0 : 1 ≤ rho0)
    (q1 q2 : ℚ) (hq1 : 0 < q1) (hq12 : q1 < q2) (hq2 : q2 ≤ 1) :
    ∃ Cgrad : ℝ, 0 < Cgrad ∧
      ∃ chi : Homogenization.H10Function
          (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2)),
        (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
        (∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (rho0 * (q1 : ℝ) / 2),
          chi.toFun x = 1) ∧
        tsupport chi.toFun ⊆
          Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2) ∧
        (∀ x, ‖chi.grad x‖ ≤ Cgrad /
          (min 1 (rho0 * ((q2 : ℝ) - q1) / 10))) := by
  have hq1r : 0 < (q1 : ℝ) := by exact_mod_cast hq1
  have hq2r : 0 < (q2 : ℝ) := lt_of_lt_of_le hq1r (by exact_mod_cast hq12.le)
  have hgap : 0 < (q2 : ℝ) - q1 := sub_pos.mpr (by exact_mod_cast hq12)
  let R : ℝ := rho0 * (q2 : ℝ)
  have hR : 0 < R := mul_pos (lt_of_lt_of_le zero_lt_one hrho0) hq2r
  let r : ℝ := min 1 (rho0 * ((q2 : ℝ) - q1) / 10)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r ≤ 1 := min_le_left _ _
  obtain ⟨Cgrad, hCgrad, chi, hrange, hzero, hone, hsupp, hgrad⟩ :=
    aux_tight_static_smooth_cutoff_with_grad hd 0 R hR r hr hr1
  let Qset : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) R hR : Set (SpatialCoordinates d))
  have hcomp : Qsetᶜ.Nonempty := by
    exact aux_lem_20_collar_family_smooth_collar_compl_nonempty d hd 0 R hR
  have hplateau : ∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (rho0 * (q1 : ℝ) / 2),
      3 * r ≤ Metric.infDist x Qsetᶜ := by
    intro x hx
    apply (Metric.le_infDist hcomp).2
    intro y hy
    have hyout : R / 2 ≤ dist y 0 := by
      have hy' : ¬ dist y 0 < R / 2 := by
        intro hy'
        apply hy
        simpa [Qset, centeredCube, Metric.mem_ball, dist_comm] using hy'
      exact le_of_not_gt hy'
    have hxinner : dist x 0 < rho0 * (q1 : ℝ) / 2 := by
      simpa [Metric.mem_ball, dist_comm] using hx
    have htri : dist y 0 ≤ dist x y + dist x 0 := by
      simpa [dist_comm] using (dist_triangle y x 0)
    have hxy : R / 2 - rho0 * (q1 : ℝ) / 2 ≤ dist x y := by
      linarith
    have hrbound : 3 * r ≤ rho0 * ((q2 : ℝ) - q1) / 2 := by
      have hrmin : r ≤ rho0 * ((q2 : ℝ) - q1) / 10 := min_le_right _ _
      nlinarith
    have heq : R / 2 - rho0 * (q1 : ℝ) / 2 =
        rho0 * ((q2 : ℝ) - q1) / 2 := by
      dsimp [R]
      ring
    exact hrbound.trans (heq ▸ hxy)
  refine ⟨Cgrad, hCgrad, chi, ?_, ?_, ?_, ?_⟩
  · exact hrange
  · intro x hx
    exact hone x (hplateau x hx)
  · simpa [R, centeredCube] using hsupp
  · simpa [r] using hgrad

theorem aux_tight_static_local_energy_from_mass
    {d : ℕ} (A : SpatialCoordinates d → ℝ)
    (G : SpatialCoordinates d → Homogenization.Vec d)
    (U V : Set (SpatialCoordinates d)) (g : ℝ) (Vmass : ℝ≥0∞)
    (hg : 0 ≤ g) (hA : ∀ z, 0 ≤ A z)
    (hG : ∀ z, ‖G z‖ ≤ g) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hMass : (∫⁻ z in U, ENNReal.ofReal (A z)) ≤ Vmass) :
    (∫⁻ z in U ∩ V,
        ENNReal.ofReal (A z * Homogenization.vecDot (G z) (G z))) ≤
      ENNReal.ofReal ((d : ℝ) * g ^ 2) * Vmass := by
  have hpoint : ∀ z,
      ENNReal.ofReal (A z * Homogenization.vecDot (G z) (G z)) ≤
        ENNReal.ofReal ((d : ℝ) * g ^ 2) * ENNReal.ofReal (A z) := by
    intro z
    have hdot_nonneg : 0 ≤ Homogenization.vecDot (G z) (G z) := by
      simpa [Homogenization.vecNormSq] using
        (Homogenization.vecNormSq_nonneg (G z))
    have hdot_le : Homogenization.vecDot (G z) (G z) ≤
        (d : ℝ) * g ^ 2 := by
      have hcard := Homogenization.vecNormSq_le_card_mul_norm_sq (G z)
      have hnorm : ‖G z‖ ^ 2 ≤ g ^ 2 := by
        have hsquare := mul_self_le_mul_self (norm_nonneg (G z)) (hG z)
        simpa [pow_two] using hsquare
      simpa [Homogenization.vecNormSq] using
        (le_trans hcard (mul_le_mul_of_nonneg_left hnorm (by positivity)))
    calc
      ENNReal.ofReal (A z * Homogenization.vecDot (G z) (G z)) =
          ENNReal.ofReal (A z) *
            ENNReal.ofReal (Homogenization.vecDot (G z) (G z)) :=
        ENNReal.ofReal_mul (hA z)
      _ ≤ ENNReal.ofReal (A z) * ENNReal.ofReal ((d : ℝ) * g ^ 2) := by
        exact mul_le_mul_left' (ENNReal.ofReal_le_ofReal hdot_le) _
      _ = ENNReal.ofReal ((d : ℝ) * g ^ 2) * ENNReal.ofReal (A z) := by
        ring
  have hfirst :
      (∫⁻ z in U ∩ V,
          ENNReal.ofReal (A z * Homogenization.vecDot (G z) (G z))) ≤
        ∫⁻ z in U ∩ V,
          ENNReal.ofReal ((d : ℝ) * g ^ 2) * ENNReal.ofReal (A z) := by
    exact setLIntegral_mono' (hU.inter hV) (fun z hz => hpoint z)
  have hsecond :
      (∫⁻ z in U ∩ V,
          ENNReal.ofReal ((d : ℝ) * g ^ 2) * ENNReal.ofReal (A z)) ≤
        ∫⁻ z in U,
          ENNReal.ofReal ((d : ℝ) * g ^ 2) * ENNReal.ofReal (A z) := by
    exact lintegral_mono'
      (Measure.restrict_mono Set.inter_subset_left le_rfl) le_rfl
  have hthird :
      (∫⁻ z in U,
          ENNReal.ofReal ((d : ℝ) * g ^ 2) * ENNReal.ofReal (A z)) ≤
        ENNReal.ofReal ((d : ℝ) * g ^ 2) *
          (∫⁻ z in U, ENNReal.ofReal (A z)) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact hfirst.trans (hsecond.trans (hthird.trans
    (mul_le_mul_left' hMass _)))

/- The cutoff, coercivity and lower-mass clauses are supplied by the nodes `tight_static_cut`,
`tight_static_coer` and `tight_static_low`. -/

/-! ## Lower-mass building blocks: H-split (AM-GM) and mass factorization. -/

/-- General AM-GM split for a negative moment across an `H`-factor: if `mass ≥ mass0 * exp(-H)`
pointwise (`H ≥ 0`), then the `q`-th negative moment of `mass` is controlled by the average of
the `2q`-exponential moment of `H` and the `2q`-th negative moment of `mass0`. -/
theorem aux_tight_static_h_split_negative_moment
    {Omega : Type*} [MeasurableSpace Omega] {μ : Measure Omega} [IsProbabilityMeasure μ]
    (mass mass0 H : Omega → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hmass_pos : ∀ om, 0 < mass om) (hmass0_pos : ∀ om, 0 < mass0 om)
    (hlb : ∀ om, mass0 om * Real.exp (-H om) ≤ mass om)
    (hmeasMass : Measurable mass) (hmeasMass0 : Measurable mass0) (hmeasH : Measurable H)
    (hIntH : Integrable (fun om => Real.exp (2 * q * H om)) μ)
    (hIntMass0 : Integrable (fun om => (mass0 om) ^ (-(2 * q))) μ) :
    Integrable (fun om => (mass om) ^ (-q)) μ ∧
    ∫ om, (mass om) ^ (-q) ∂μ ≤
      ((∫ om, Real.exp (2 * q * H om) ∂μ) + ∫ om, (mass0 om) ^ (-(2 * q)) ∂μ) / 2 := by
  set f : Omega → ℝ := fun om => Real.exp (q * H om) with hfdef
  set g : Omega → ℝ := fun om => (mass0 om) ^ (-q) with hgdef
  have hfnn : ∀ om, 0 ≤ f om := fun om => (Real.exp_pos _).le
  have hgnn : ∀ om, 0 ≤ g om := fun om => Real.rpow_nonneg (hmass0_pos om).le _
  have hf2eq : (fun om => f om ^ (2 : ℝ)) = fun om => Real.exp (2 * q * H om) := by
    funext om
    show (Real.exp (q * H om)) ^ (2 : ℝ) = Real.exp (2 * q * H om)
    rw [← Real.exp_mul]
    congr 1
    ring
  have hg2eq : (fun om => g om ^ (2 : ℝ)) = fun om => (mass0 om) ^ (-(2 * q)) := by
    funext om
    show ((mass0 om) ^ (-q)) ^ (2 : ℝ) = (mass0 om) ^ (-(2 * q))
    rw [← Real.rpow_mul (hmass0_pos om).le]
    congr 1
    ring
  have hIntf2 : Integrable (fun om => f om ^ (2 : ℝ)) μ := by rw [hf2eq]; exact hIntH
  have hIntg2 : Integrable (fun om => g om ^ (2 : ℝ)) μ := by rw [hg2eq]; exact hIntMass0
  have hpointwise : ∀ om, (mass om) ^ (-q) ≤ f om * g om := by
    intro om
    have hstep1 : (mass om) ^ (-q) ≤ (mass0 om * Real.exp (-H om)) ^ (-q) := by
      have hmpos : 0 < mass0 om * Real.exp (-H om) := mul_pos (hmass0_pos om) (Real.exp_pos _)
      exact Real.rpow_le_rpow_of_nonpos hmpos (hlb om) (neg_nonpos.mpr hq)
    have hstep2 : (mass0 om * Real.exp (-H om)) ^ (-q) = f om * g om := by
      rw [Real.mul_rpow (hmass0_pos om).le (Real.exp_pos _).le]
      show (mass0 om) ^ (-q) * (Real.exp (-H om)) ^ (-q) = f om * g om
      rw [hfdef, hgdef]
      dsimp only
      rw [mul_comm]
      congr 1
      rw [← Real.exp_mul]
      congr 1
      ring
    linarith [hstep1, hstep2 ▸ hstep1]
  have hamgm : ∀ om, f om * g om ≤ (f om ^ (2 : ℝ) + g om ^ (2 : ℝ)) / 2 := by
    intro om
    have hfsq : f om ^ (2 : ℝ) = f om * f om := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    have hgsq : g om ^ (2 : ℝ) = g om * g om := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [hfsq, hgsq]
    nlinarith [sq_nonneg (f om - g om)]
  have hmeasf : Measurable f := by
    rw [hfdef]; fun_prop
  have hmeasg : Measurable g := by
    rw [hgdef]; fun_prop
  have hmeasmassq : Measurable (fun om => (mass om) ^ (-q)) := by fun_prop
  have hIntmassq : Integrable (fun om => (mass om) ^ (-q)) μ := by
    apply Integrable.mono' (hIntf2.add hIntg2 |>.const_mul (1 / 2 : ℝ)) hmeasmassq.aestronglyMeasurable
    filter_upwards with om
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hmass_pos om).le _)]
    calc (mass om) ^ (-q) ≤ f om * g om := hpointwise om
      _ ≤ (f om ^ (2:ℝ) + g om ^ (2:ℝ)) / 2 := hamgm om
      _ = (1/2 : ℝ) * (f om ^ (2:ℝ) + g om ^ (2:ℝ)) := by ring
  refine ⟨hIntmassq, ?_⟩
  calc ∫ om, (mass om) ^ (-q) ∂μ
      ≤ ∫ om, (f om ^ (2:ℝ) + g om ^ (2:ℝ)) / 2 ∂μ := by
        apply integral_mono hIntmassq ((hIntf2.add hIntg2).div_const 2)
        intro om
        exact (hpointwise om).trans (hamgm om)
    _ = ((∫ om, Real.exp (2 * q * H om) ∂μ) + ∫ om, (mass0 om) ^ (-(2 * q)) ∂μ) / 2 := by
        rw [integral_div, integral_add hIntf2 hIntg2, hf2eq, hg2eq]

/-- `cutoffSpeedDensity` factors exactly as `exp(H ω x) * (the H = 0 density)`: trivial from
`cutoffPotential`'s definition (`H` is an additive term, everything else is unchanged). -/
theorem aux_tight_static_cutoffSpeedDensity_eq_exp_mul_zero {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (x : SpatialCoordinates d) :
    cutoffSpeedDensity M H om N x =
      Real.exp (H om x) * cutoffSpeedDensity M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x := by
  unfold cutoffSpeedDensity cutoffPotential
  rw [← Real.exp_add]
  congr 1
  simp only [ContinuousMap.zero_apply, zero_add]
  ring

/-- Pointwise lower bound on the `H`-density by the `H = 0` density, on a compact set `K`, via
the sup-norm control `|H ω x| ≤ ‖(H ω).restrict K‖`. -/
theorem aux_tight_static_cutoffSpeedDensity_ge_of_mem {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (K : TopologicalSpace.Compacts (SpatialCoordinates d))
    (x : SpatialCoordinates d) (hx : x ∈ (K : Set (SpatialCoordinates d))) :
    Real.exp (-‖(H om).restrict (K : Set (SpatialCoordinates d))‖) *
        cutoffSpeedDensity M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x ≤
      cutoffSpeedDensity M H om N x := by
  have hHx : -‖(H om).restrict (K : Set (SpatialCoordinates d))‖ ≤ H om x := by
    have hb := ContinuousMap.norm_coe_le_norm
      ((H om).restrict (K : Set (SpatialCoordinates d))) (⟨x, hx⟩ : K)
    rw [ContinuousMap.restrict_apply, Real.norm_eq_abs] at hb
    linarith [abs_le.mp hb |>.1]
  have hexp : Real.exp (-‖(H om).restrict (K : Set (SpatialCoordinates d))‖) ≤ Real.exp (H om x) :=
    Real.exp_le_exp.mpr hHx
  have hz0 : 0 ≤ cutoffSpeedDensity M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N x := by
    unfold cutoffSpeedDensity; exact (Real.exp_pos _).le
  have hkey := mul_le_mul_of_nonneg_right hexp hz0
  have hEq := aux_tight_static_cutoffSpeedDensity_eq_exp_mul_zero M H om N x
  linarith [hkey, hEq]

/-- Integrating the pointwise bound over a ball `B ⊆ K`: the `H`-mass of `B` dominates
`e^{-‖H‖_K} ·` the `H = 0` mass of `B`, as an ENNReal `withDensity` inequality. -/
theorem aux_tight_static_withDensity_ge_of_subset {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (om : BilateralField d) (N : ℕ)
    (K : TopologicalSpace.Compacts (SpatialCoordinates d))
    (B : Set (SpatialCoordinates d)) (hBmeas : MeasurableSet B)
    (hB : B ⊆ (K : Set (SpatialCoordinates d))) :
    ENNReal.ofReal (Real.exp (-‖(H om).restrict (K : Set (SpatialCoordinates d))‖)) *
        volume.withDensity
          (fun z => ENNReal.ofReal
            (cutoffSpeedDensity M (fun _ => (0 : C(SpatialCoordinates d, ℝ))) om N z)) B ≤
      volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H om N z)) B := by
  rw [withDensity_apply' _ B, withDensity_apply' _ B,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' hBmeas
  intro x hxB
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal
    (aux_tight_static_cutoffSpeedDensity_ge_of_mem M H om N K x (hB hxB))


/-- Lemma `tight:lem-static` (Static local estimates from Sections 1–6).  By
`tight_scale_covariance` the local normalization of any cube is the standard cutoff-`m` object at
the origin for an environment with the same law, so "`sup_{L,m,z} E K^q < ∞`" is the moment bound
below, uniform in the cutoff `N`, on a fixed reference cube of side `rho0`.  The exponent `B` is
deterministic and fixed before the moment order `q`; the disorder threshold depends on `q`.
The standing inputs are those of `prop_growth` / `lem_coercivity` (author rule: standing inputs
may be carried). -/
theorem tight_static
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)] (hd : 2 ≤ d)
    (Jc : in_J d) (Pc : in_poincare d hd Jc) (Xc : in_extension d hd Jc)
    (Sf : Lane4.SobolevFoundationalInput d hd) (W : Lane4.SmallPerturbationInput d)
    (Cp : Lane4.CampanatoInput d) :
    ∃ B : ℝ, 0 < B ∧ ∀ q : ℝ, 1 ≤ q → ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (Rm : in_responses d M)
        (Sreg : in_6_16 d M) (It : in_iteration d M Jc Sreg),
        M.delta ≤ delta0 →
      ∀ rho0 : ℝ, 1 ≤ rho0 → ∃ C : ℝ, 0 < C ∧
      ∀ H : BilateralField d → C(SpatialCoordinates d, ℝ), InfraredCharacterization M H →
      ∀ N : ℕ, ∃ K : BilateralField d → ℝ, Measurable K ∧ (∀ omega, 1 ≤ K omega) ∧
        ∫⁻ omega, ENNReal.ofReal (K omega ^ q) ∂(chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal C ∧
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          tight_static_estimates (cutoffSpeedDensity M H omega N)
            (cutoffCoefficient M H omega N) rho0 (K omega) B := by
  refine ⟨5, by norm_num, ?_⟩
  intro q hq
  obtain ⟨delta0, hdelta0, hupper⟩ := aux_tight_static_upper hd q hq
  obtain ⟨Ctail, deltaTail, hCtail, hdeltaTail, htail⟩ :=
    SubdiffusiveProcess.Section9.exists_cutoffTranslatedAxisCube_logAbs_ogamma d
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  obtain ⟨deltaSq, hdeltaSq, hsmallSq⟩ :=
    aux_tight_static_log_square_threshold q Ctail hqpos hCtail
  obtain ⟨deltaCut, hdeltaCut, hCutFull⟩ :=
    tight_static_cut hd Jc Pc Xc Sf W Cp (aux_tight_static_upper hd) q hq
  obtain ⟨deltaCoer, hdeltaCoer, hCoerFull⟩ :=
    tight_static_coer hd Jc Pc Sf q hq
  obtain ⟨deltaLow, hdeltaLow, hlow⟩ := tight_static_low hd q hq
  refine ⟨min (min (min (min (min delta0 deltaTail) deltaSq) deltaCut) deltaCoer) deltaLow,
    lt_min (lt_min (lt_min (lt_min (lt_min hdelta0 hdeltaTail) hdeltaSq) hdeltaCut) hdeltaCoer)
      hdeltaLow, ?_⟩
  intro M Rm Sreg It hM rho0 hrho
  have hMprev : M.delta ≤ min (min (min (min delta0 deltaTail) deltaSq) deltaCut) deltaCoer :=
    hM.trans (min_le_left _ _)
  have hMlow : M.delta ≤ deltaLow := hM.trans (min_le_right _ _)
  have hMA : M.delta ≤ min (min (min delta0 deltaTail) deltaSq) deltaCut := hMprev.trans (min_le_left _ _)
  have hMcoer : M.delta ≤ deltaCoer := hMprev.trans (min_le_right _ _)
  have hMA' : M.delta ≤ min (min delta0 deltaTail) deltaSq := hMA.trans (min_le_left _ _)
  have hMcut : M.delta ≤ deltaCut := hMA.trans (min_le_right _ _)
  have hMupper : M.delta ≤ delta0 :=
    hMA'.trans (le_trans (min_le_left _ _) (min_le_left _ _))
  have hMtail : M.delta ≤ deltaTail :=
    hMA'.trans (le_trans (min_le_left _ _) (min_le_right _ _))
  have hMsq : M.delta ≤ deltaSq :=
    hMA'.trans (min_le_right _ _)
  have hsmall : q * (Ctail * M.delta ^ 2 * |Real.log M.delta| ^ 2) ≤ 1 :=
    hsmallSq M.delta M.shellPrefix.delta_pos hMsq
  obtain ⟨C0, hC0, hCM⟩ := hupper M hMupper (rho0 + 2) (by linarith)
  have hS4_translated_inverse :
      ∀ (m : ℕ) (z : Homogenization.Vec d),
        ∫ om,
            |(SubdiffusiveProcess.Section9.cutoffTranslatedAxisCubeAverage M m z om)⁻¹| ^ q
          ∂M.P.toMeasure ≤ (2 : ℝ) ^ q * 2 := by
    intro m z
    exact aux_tight_static_translated_source_inverse_integral_bound hd M m z q
      Ctail hqpos hCtail hsmall (htail M hMtail m z)
  have hLowSupplier := hlow M Rm hMlow rho0 hrho
  have hCoerSupplier :
      ∃ Ccoer : ℝ, 0 < Ccoer ∧
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → ∀ N : ℕ,
      ∃ Kcoer : BilateralField d → ℝ, Measurable Kcoer ∧ (∀ omega, 1 ≤ Kcoer omega) ∧
        (∫⁻ omega, ENNReal.ofReal (Kcoer omega ^ q)
            ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal Ccoer ∧
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ q' : ℚ, 0 < q' → q' ≤ 1 →
            (∀ v : Homogenization.H1Function
                (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2)),
              (∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ∫⁻ z in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                    ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
                      ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
                ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ENNReal.ofReal (v.toFun x ^ 2) ≤
              ENNReal.ofReal (Kcoer omega * (q'.den : ℝ) ^ (5 : ℝ)) *
                ((∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                    ENNReal.ofReal ((cutoffCoefficient M H omega N x) *
                      Homogenization.vecDot (v.grad x) (v.grad x))) +
                  ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                    ENNReal.ofReal (v.toFun x ^ 2))) ∧
            (∀ v : Homogenization.H10Function
                (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2)),
              (∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ∫⁻ z in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                    ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
                      ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
                ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ENNReal.ofReal (v.toFun x ^ 2) ≤
              ENNReal.ofReal (Kcoer omega * (q'.den : ℝ) ^ (5 : ℝ)) *
                ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ENNReal.ofReal ((cutoffCoefficient M H omega N x) *
                    Homogenization.vecDot (v.grad x) (v.grad x))) :=
    hCoerFull M Rm hMcoer rho0 hrho
  have hCutSupplier :
      ∃ Ccut : ℝ, 0 < Ccut ∧
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → ∀ N : ℕ,
      ∃ Kcut : BilateralField d → ℝ, Measurable Kcut ∧ (∀ omega, 1 ≤ Kcut omega) ∧
        (∫⁻ omega, ENNReal.ofReal (Kcut omega ^ q)
            ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal Ccut ∧
        ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
          ∀ q1 q2 : ℚ, 0 < q1 → q1 < q2 → q2 ≤ 1 →
            ∃ chi : Homogenization.H10Function
                (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2)),
              (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
              (∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (rho0 * (q1 : ℝ) / 2),
                chi.toFun x = 1) ∧
              tsupport chi.toFun ⊆
                Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2) ∧
            ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
                ∫⁻ z in Metric.ball x r ∩
                    Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2),
                  ENNReal.ofReal ((cutoffCoefficient M H omega N z) *
                    Homogenization.vecDot (chi.grad z) (chi.grad z)) ≤
                  ENNReal.ofReal
                    (Kcut omega * (rho0 * ((q2 : ℝ) - q1) / 2) ^ (-5 : ℝ) *
                      r ^ ((d : ℝ) - 1 / 2)) :=
    hCutFull M Rm Sreg It hMcut rho0 hrho
  obtain ⟨Clow, hClow, hLowSupplier⟩ := hLowSupplier
  obtain ⟨Ccoer, hCcoer, hCoerSupplier⟩ := hCoerSupplier
  obtain ⟨Ccut, hCcut, hCutSupplier⟩ := hCutSupplier
  let C : ℝ := C0 + Clow + Ccoer + Ccut
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro H hH N
  obtain ⟨Kup, hKupmeas, hKupone, hKupmom, hKupupper⟩ := hCM H hH
  obtain ⟨Klow, hKlowmeas, hKlowone, hKlowmom, hKlow⟩ := hLowSupplier H hH N
  obtain ⟨Kcoer, hKcoermeas, hKcoerone, hKcoermom, hKcoer⟩ := hCoerSupplier H hH N
  obtain ⟨Kcut, hKcutmeas, hKcutone, hKcutmom, hKcut⟩ := hCutSupplier H hH N
  let K : BilateralField d → ℝ :=
    fun omega => max (max (Kup omega) (Klow omega)) (max (Kcoer omega) (Kcut omega))
  have hKmeas : Measurable K := (hKupmeas.max hKlowmeas).max (hKcoermeas.max hKcutmeas)
  have hKone : ∀ omega, 1 ≤ K omega := by
    intro omega
    exact (hKupone omega).trans
      ((le_max_left _ _).trans (le_max_left _ _))
  have hKmom :
      (∫⁻ omega, ENNReal.ofReal (K omega ^ q)
        ∂(chaosSampleLaw M).toMeasure) ≤ ENNReal.ofReal C := by
    dsimp [K, C]
    exact (aux_tight_static_max_moment q hq Kup Klow Kcoer Kcut
      hKupmeas hKlowmeas hKcoermeas hKcutmeas
      hKupone hKlowone hKcoerone hKcutone C0 Clow Ccoer Ccut
      hC0.le hClow.le hCcoer.le hCcut.le hKupmom hKlowmom hKcoermom hKcutmom)
  refine ⟨K, hKmeas, hKone, hKmom, ?_⟩
  have hupper_fixed :
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
          Metric.ball x r ⊆ Metric.ball (0 : SpatialCoordinates d) (rho0 / 2) →
          volume.withDensity (fun z => ENNReal.ofReal (cutoffSpeedDensity M H omega N z))
              (Metric.ball x r) ≤ ENNReal.ofReal (K omega * r ^ ((d : ℝ) - 1 / 2)) := by
    filter_upwards [hKupupper] with omega homega
    intro x r hr hr1 hsub
    have hxsmall : x ∈ Metric.ball (0 : SpatialCoordinates d) (rho0 / 2) :=
      hsub (Metric.mem_ball_self hr)
    have hxlarge : x ∈ Metric.ball (0 : SpatialCoordinates d) ((rho0 + 2) / 2) := by
      have hxnorm : ‖x‖ < rho0 / 2 := by
        simpa [Metric.mem_ball, dist_zero_right] using hxsmall
      have hxnorm' : ‖x‖ < (rho0 + 2) / 2 := by linarith
      simpa [Metric.mem_ball, dist_zero_right] using hxnorm'
    exact (homega N x r hr hr1 hxlarge).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_left _ _))
        (Real.rpow_nonneg hr.le _)))
  have hremaining :
      ∀ᵐ omega ∂(chaosSampleLaw M).toMeasure,
        tight_static_estimates (cutoffSpeedDensity M H omega N)
          (cutoffCoefficient M H omega N) rho0 (K omega) 5 := by
    filter_upwards [hupper_fixed, hKlow, hKcoer, hKcut]
      with omega homega hlowomega hcoeromega hcutomega
    have hLowerMass :
        ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
          Metric.ball x r ⊆ Metric.ball (0 : SpatialCoordinates d) (rho0 / 2) →
          ENNReal.ofReal ((K omega)⁻¹ * r ^ ((d : ℝ) + 1 / 2)) ≤
              volume.withDensity
              (fun z => ENNReal.ofReal (cutoffSpeedDensity M H omega N z))
              (Metric.ball x r) := by
      intro x r hr hr1 hsub
      have hKpos : 0 < K omega := lt_of_lt_of_le zero_lt_one (hKone omega)
      have hKlowpos : 0 < Klow omega := lt_of_lt_of_le zero_lt_one (hKlowone omega)
      have hKinvlower : (K omega)⁻¹ ≤ (Klow omega)⁻¹ := by
        exact (inv_le_inv₀ hKpos hKlowpos).2
          ((le_max_right _ _).trans (le_max_left _ _))
      exact (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hKinvlower (Real.rpow_nonneg hr.le _))).trans
        (hlowomega x r hr hr1 hsub)
    have hCoercivity :
        ∀ q' : ℚ, 0 < q' → q' ≤ 1 →
          (∀ v : Homogenization.H1Function
              (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2)),
            (∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                ∫⁻ z in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
                    ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
              ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                ENNReal.ofReal (v.toFun x ^ 2) ≤
            ENNReal.ofReal (K omega * (q'.den : ℝ) ^ (5 : ℝ)) *
              ((∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ENNReal.ofReal ((cutoffCoefficient M H omega N x) *
                    Homogenization.vecDot (v.grad x) (v.grad x))) +
                ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ENNReal.ofReal (v.toFun x ^ 2))) ∧
          (∀ v : Homogenization.H10Function
              (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2)),
            (∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                ∫⁻ z in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                  ENNReal.ofReal ((v.toFun x - v.toFun z) ^ 2) /
                    ENNReal.ofReal (‖x - z‖ ^ ((d : ℝ) + 3 / 2))) +
              ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
                ENNReal.ofReal (v.toFun x ^ 2) ≤
            ENNReal.ofReal (K omega * (q'.den : ℝ) ^ (5 : ℝ)) *
              ∫⁻ x in Metric.ball (0 : SpatialCoordinates d) (rho0 * (q' : ℝ) / 2),
            ENNReal.ofReal ((cutoffCoefficient M H omega N x) *
                  Homogenization.vecDot (v.grad x) (v.grad x))) := by
      have hKcoerK : Kcoer omega ≤ K omega := by
        exact (le_max_left _ _).trans (le_max_right _ _)
      intro q' hq' hq'1
      obtain ⟨hH1, hH10⟩ := hcoeromega q' hq' hq'1
      constructor
      · intro v
        refine (hH1 v).trans ?_
        apply mul_le_mul'
        · exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right hKcoerK (by positivity))
        · exact le_rfl
      · intro v
        refine (hH10 v).trans ?_
        apply mul_le_mul'
        · exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right hKcoerK (by positivity))
        · exact le_rfl
    have hCutoffs :
        ∀ q1 q2 : ℚ, 0 < q1 → q1 < q2 → q2 ≤ 1 →
          ∃ chi : Homogenization.H10Function
              (Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2)),
            (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
            (∀ x ∈ Metric.ball (0 : SpatialCoordinates d) (rho0 * (q1 : ℝ) / 2),
              chi.toFun x = 1) ∧
            tsupport chi.toFun ⊆
              Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2) ∧
            ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
              ∫⁻ z in Metric.ball x r ∩
                  Metric.ball (0 : SpatialCoordinates d) (rho0 * (q2 : ℝ) / 2),
                ENNReal.ofReal ((cutoffCoefficient M H omega N z) *
                  Homogenization.vecDot (chi.grad z) (chi.grad z)) ≤
                ENNReal.ofReal
                  (K omega * (rho0 * ((q2 : ℝ) - q1) / 2) ^ (-5 : ℝ) *
                    r ^ ((d : ℝ) - 1 / 2)) := by
      have hKcutK : Kcut omega ≤ K omega := by
        exact (le_max_right _ _).trans (le_max_right _ _)
      intro q1 q2 hq1 hq12 hq2
      obtain ⟨chi, hchi0, hchi1, hsupp, henergy⟩ :=
        hcutomega q1 q2 hq1 hq12 hq2
      refine ⟨chi, hchi0, hchi1, hsupp, ?_⟩
      intro x r hr hr1
      have hgap : 0 < (q2 : ℝ) - q1 := by
        exact sub_pos.mpr (by exact_mod_cast hq12)
      have hbase : 0 ≤ rho0 * ((q2 : ℝ) - q1) / 2 := by
        positivity
      refine (henergy x r hr hr1).trans ?_
      exact ENNReal.ofReal_le_ofReal (by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_right hKcutK
          exact Real.rpow_nonneg hbase _
        · exact Real.rpow_nonneg hr.le _)
    have hMass :
        ∀ (x : SpatialCoordinates d) (r : ℝ), 0 < r → r ≤ 1 →
          Metric.ball x r ⊆ Metric.ball (0 : SpatialCoordinates d) (rho0 / 2) →
          ENNReal.ofReal ((K omega)⁻¹ * r ^ ((d : ℝ) + 1 / 2)) ≤
              volume.withDensity
                (fun z => ENNReal.ofReal (cutoffSpeedDensity M H omega N z))
                (Metric.ball x r) ∧
            volume.withDensity
                (fun z => ENNReal.ofReal (cutoffSpeedDensity M H omega N z))
                (Metric.ball x r) ≤
              ENNReal.ofReal (K omega * r ^ ((d : ℝ) - 1 / 2)) := by
      intro x r hr hr1 hsub
      exact ⟨hLowerMass x r hr hr1 hsub, homega x r hr hr1 hsub⟩
    exact And.intro hMass (And.intro hCoercivity hCutoffs)
  exact hremaining

end Paper

