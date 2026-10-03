module

public import SubdiffusiveProcess.Section10.RetainedPrefixSparseStepSupport

@[expose] public section

/-!
# One sparse contraction for the literal retained-prefix field

The Section 5 sparse induction step is read at scales `ell + N*R`, with
D0 providing the genuine retained-block independence and selection-fiber
factorization. The lawful induction premise remains explicit. This helper
neither supplies the initial energy bound nor closes `lim_strict_decay`.
-/

namespace SubdiffusiveProcess.Section10

open Homogenization Homogenization.Book MeasureTheory ProbabilityTheory Set
open SubdiffusiveProcess.Frozen.Assumptions
open SubdiffusiveProcess.CoarseGrainingVocab (potentialIndexSigma potentialIndexSigma_le_borel)
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
open SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn

noncomputable section

variable {d : ℕ}

/-- The actual retained-prefix energy bound contracts by the same unit-scale
qR at one successor generation, independently of the starting scale. -/
theorem retainedPrefixSparseBound_succ (M : GMCModel d) (ell : ℕ) {R : ℕ} (hR : 0 < R) (N : ℕ)
    {kap qq : ℝ} (hkap : 0 ≤ kap)
    (hIH : RetainedPrefixSparseBound M ell R N kap)
    (hqR : ∀ pi : Equiv.Perm (Fin d),
      qRCell M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) ≤ qq) :
    RetainedPrefixSparseBound M ell R (N + 1) (kap * qq) := by
  intro c pi p
  set k : ℕ := ell + (N + 1) * R with hk
  set U : KuhnCell d := dilatedCell k c pi with hU
  set S : Finset (KuhnCell d) := dilatedSubMesh k R c pi with hS
  have hvolU : 0 < (volume U.openCarrier).toReal :=
    volume_toReal_pos (kuhnCellDomain U)
  have hUmeas : MeasurableSet U.openCarrier := (isOpen_openCarrier U).measurableSet
  refine le_mul_vecNormSq_of_forall_unit
    (f := fun q => ∫ omega, retainedPrefixEnergy M ell R (N + 1) U omega q ∂M.P.toMeasure)
    (kappa := kap * qq) ?_ ?_ p
  · intro t r
    calc ∫ omega, retainedPrefixEnergy M ell R (N + 1) U omega (t • r) ∂M.P.toMeasure
        = ∫ omega, t ^ 2 * retainedPrefixEnergy M ell R (N + 1) U omega r ∂M.P.toMeasure := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
          exact retainedPrefixEnergy_smul M ell R (N + 1) U omega t r
      _ = t ^ 2 * ∫ omega, retainedPrefixEnergy M ell R (N + 1) U omega r ∂M.P.toMeasure := integral_const_mul _ _
  intro u hu
  have hu1 : vecNormSq u = 1 := hu
  -- it suffices to bound by `kap * qq` up to an arbitrary positive error
  refine le_of_forall_pos_le_add fun err herr => ?_
  set eps : ℝ := err * (volume U.openCarrier).toReal / (kap + 1) with heps'
  have hkap1 : (0 : ℝ) < kap + 1 := by linarith
  have heps : 0 < eps := by
    rw [heps']
    positivity
  -- the measurable, countably valued selection, on the outer layer's block
  obtain ⟨D, n, hD, hn, hopt⟩ :=
    @exists_measurable_eps_optimal_kuhnSlopes d (PotentialSample d)
      (potentialIndexSigma ({k} : Set ℕ))
      (fun omega => shellFactor M k omega) S U.openCarrier u
      (fun omega => continuous_shellFactor M k omega)
      (fun omega x => (shellFactor_pos M k omega x).le)
      (fun T _ => measurable_cellSup_shellFactor_singleton M k T) eps heps
  have hn' : Measurable n := hn.mono (potentialIndexSigma_le_borel _) le_rfl
  choose comp hcomp using hD
  -- the two integrands
  set X : PotentialSample d → ℝ := fun omega =>
    retainedPrefixEnergy M ell R (N + 1) U omega u with hXdef
  set H : PotentialSample d → ℝ := fun omega =>
    (volume U.openCarrier).toReal⁻¹ *
      (kuhnDirichletInf (shellFactor M k omega) S U.openCarrier u + eps) with hHdef
  have hXint : Integrable X M.P.toMeasure :=
    integrable_retainedPrefixEnergy M ell R (N + 1) U u
  have hHint : Integrable H M.P.toMeasure :=
    Integrable.const_mul (Integrable.add
      (integrable_kuhnDirichletInf_shellFactor_dilated M R k c pi u)
      (integrable_const eps)) _
  have hkapHint : Integrable (fun omega => kap * H omega) M.P.toMeasure :=
    hHint.const_mul _
  -- integrability of the pieces
  have hcellint : ∀ T ∈ S, Integrable (fun omega : PotentialSample d =>
      cellSup (shellFactor M k omega) T) M.P.toMeasure := fun T hT =>
    integrable_cellSup_shellFactor_mem_dilatedSubMesh M R k c pi hT
  -- the scale of a cell of the mesh
  have hTscale : ∀ T ∈ S, T.supportCube.scale = ((ell + N * R : ℕ) : ℤ) := by
    intro T hT
    exact scale_of_mem_retainedPrefix_next_subMesh ell R N c pi hT
  -- the induction hypothesis, read at a cell of the mesh
  have hIHcell : ∀ T ∈ S, ∀ q : Vec d,
      ∫ omega, retainedPrefixEnergy M ell R N T omega q ∂M.P.toMeasure ≤ kap * vecNormSq q := by
    intro T hT q
    have hTeq : T = dilatedCell (ell + N * R) T.supportCube.index T.order :=
      eq_dilatedCell (hTscale T hT)
    rw [hTeq]
    exact hIH _ _ q
  -- the fibrewise comparison
  have hfiber : ∀ m : ℕ,
      ∫ omega in {omega | n omega = m}, X omega ∂M.P.toMeasure ≤
        ∫ omega in {omega | n omega = m}, kap * H omega ∂M.P.toMeasure := by
    intro m
    have hFmeas : MeasurableSet {omega : PotentialSample d | n omega = m} :=
      measurableSet_index_fiber hn' m
    -- the deterministic display at the frozen slopes
    have hstep1 : ∀ omega : PotentialSample d, X omega ≤
        ∑ T ∈ S, (volume T.openCarrier).toReal /
            (volume U.openCarrier).toReal *
          (cellSup (shellFactor M k omega) T *
            retainedPrefixEnergy M ell R N T omega (u + D m T)) := by
      intro omega
      have h := retainedPrefixEnergy_succ_le M ell hR N c pi u omega (comp m)
      rw [hcomp m] at h
      exact h
    have hterm : ∀ T ∈ S, Integrable (fun omega : PotentialSample d =>
        (volume T.openCarrier).toReal / (volume U.openCarrier).toReal *
          (cellSup (shellFactor M k omega) T *
            retainedPrefixEnergy M ell R N T omega (u + D m T))) M.P.toMeasure := by
      intro T hT
      refine Integrable.const_mul ?_ _
      exact integrable_cellSup_next_mul_retainedPrefix_energy M ell hR N c pi hT (u + D m T)
    -- integrate the display over the fiber
    have hstep2 : ∫ omega in {omega | n omega = m}, X omega ∂M.P.toMeasure ≤
        ∑ T ∈ S, (volume T.openCarrier).toReal /
            (volume U.openCarrier).toReal *
          ((∫ omega in {omega | n omega = m},
              cellSup (shellFactor M k omega) T ∂M.P.toMeasure) *
            ∫ omega, retainedPrefixEnergy M ell R N T omega (u + D m T) ∂M.P.toMeasure) := by
      have hle := setIntegral_mono_on hXint.integrableOn
        (integrable_finset_sum S hterm).integrableOn hFmeas
        (fun omega _ => hstep1 omega)
      refine hle.trans (le_of_eq ?_)
      rw [integral_finset_sum S fun T hT => (hterm T hT).integrableOn]
      refine Finset.sum_congr rfl fun T hT => ?_
      rw [integral_const_mul]
      congr 1
      exact setIntegral_fiber_cellSup_next_mul_retainedPrefix_energy M ell hR N hn m T (u + D m T)
    -- apply the induction hypothesis termwise
    have hstep3 : ∑ T ∈ S, (volume T.openCarrier).toReal /
            (volume U.openCarrier).toReal *
          ((∫ omega in {omega | n omega = m},
              cellSup (shellFactor M k omega) T ∂M.P.toMeasure) *
            ∫ omega, retainedPrefixEnergy M ell R N T omega (u + D m T) ∂M.P.toMeasure) ≤
        kap * ∫ omega in {omega | n omega = m},
          (volume U.openCarrier).toReal⁻¹ *
            kuhnDiscreteEnergy (shellFactor M k omega) S U.openCarrier u (D m)
            ∂M.P.toMeasure := by
      have hweight : ∀ T ∈ S, 0 ≤ ∫ omega in {omega | n omega = m},
          cellSup (shellFactor M k omega) T ∂M.P.toMeasure := by
        intro T hT
        refine setIntegral_nonneg hFmeas fun omega _ => ?_
        exact le_trans (shellFactor_pos M k omega (T.vertex 0)).le
          (le_cellSup T (continuous_shellFactor M k omega).continuousOn
            (T.vertex_mem_closedCarrier 0))
      have hbound : ∀ T ∈ S,
          (volume T.openCarrier).toReal / (volume U.openCarrier).toReal *
            ((∫ omega in {omega | n omega = m},
                cellSup (shellFactor M k omega) T ∂M.P.toMeasure) *
              ∫ omega, retainedPrefixEnergy M ell R N T omega (u + D m T) ∂M.P.toMeasure) ≤
            kap * ∫ omega in {omega | n omega = m},
              (volume U.openCarrier).toReal⁻¹ *
                (volume.real (U.openCarrier ∩ T.openCarrier) *
                  (cellSup (shellFactor M k omega) T *
                    vecNormSq (u + D m T))) ∂M.P.toMeasure := by
        intro T hT
        have hsetT : U.openCarrier ∩ T.openCarrier = T.openCarrier :=
          Set.inter_eq_self_of_subset_right
            (openCarrier_subset_of_mem_dilatedSubMesh hT)
        have hinner := hIHcell T hT (u + D m T)
        have hmul := mul_le_mul_of_nonneg_left hinner (hweight T hT)
        have hmul2 := mul_le_mul_of_nonneg_left hmul
          (show (0 : ℝ) ≤ (volume T.openCarrier).toReal /
            (volume U.openCarrier).toReal by positivity)
        refine hmul2.trans (le_of_eq ?_)
        rw [hsetT]
        have hC : ∀ omega : PotentialSample d,
            (volume U.openCarrier).toReal⁻¹ *
              (volume.real T.openCarrier *
                (cellSup (shellFactor M k omega) T * vecNormSq (u + D m T))) =
              ((volume U.openCarrier).toReal⁻¹ *
                (volume.real T.openCarrier * vecNormSq (u + D m T))) *
                cellSup (shellFactor M k omega) T := fun omega => by ring
        simp only [hC]
        rw [integral_const_mul]
        have hvne : (volume U.openCarrier).toReal ≠ 0 := ne_of_gt hvolU
        have hreal : volume.real T.openCarrier = (volume T.openCarrier).toReal := rfl
        rw [hreal]
        field_simp
      have hsum : ∑ T ∈ S, ∫ omega in {omega | n omega = m},
          (volume U.openCarrier).toReal⁻¹ *
            (volume.real (U.openCarrier ∩ T.openCarrier) *
              (cellSup (shellFactor M k omega) T * vecNormSq (u + D m T)))
            ∂M.P.toMeasure =
          ∫ omega in {omega | n omega = m},
            (volume U.openCarrier).toReal⁻¹ *
              kuhnDiscreteEnergy (shellFactor M k omega) S U.openCarrier u (D m)
              ∂M.P.toMeasure := by
        rw [← integral_finset_sum S fun T hT =>
          ((((hcellint T hT).mul_const _).const_mul _).const_mul _).integrableOn]
        refine integral_congr_ae (Filter.Eventually.of_forall fun omega => ?_)
        simp only [kuhnDiscreteEnergy, Finset.mul_sum]
      refine (Finset.sum_le_sum hbound).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, hsum]
    -- the selection is `eps`-optimal on its fiber
    have hstep4 : kap * ∫ omega in {omega | n omega = m},
          (volume U.openCarrier).toReal⁻¹ *
            kuhnDiscreteEnergy (shellFactor M k omega) S U.openCarrier u (D m)
            ∂M.P.toMeasure ≤
        ∫ omega in {omega | n omega = m}, kap * H omega ∂M.P.toMeasure := by
      conv_rhs => rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ hkap
      refine setIntegral_mono_on ?_ hHint.integrableOn hFmeas fun omega homega => ?_
      · refine Integrable.integrableOn ?_
        refine Integrable.const_mul ?_ _
        refine integrable_finset_sum S fun T hT => ?_
        exact ((hcellint T hT).mul_const _).const_mul _
      · have hval : D (n omega) = D m := by
          rw [show n omega = m from homega]
        have := hopt omega
        rw [hval] at this
        refine mul_le_mul_of_nonneg_left (le_of_lt this) (by positivity)
    exact hstep2.trans (hstep3.trans hstep4)
  -- assemble
  have hmain : ∫ omega, X omega ∂M.P.toMeasure ≤
      ∫ omega, kap * H omega ∂M.P.toMeasure :=
    integral_le_of_setIntegral_fiber_le hn' hXint hkapHint hfiber
  have hHval : ∫ omega, H omega ∂M.P.toMeasure ≤
      qRSlope M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) u +
        (volume U.openCarrier).toReal⁻¹ * eps := by
    rw [hHdef]
    rw [integral_const_mul, integral_add
      (integrable_kuhnDirichletInf_shellFactor_dilated M R k c pi u)
      (integrable_const eps), integral_const, mul_add]
    have hq := integral_normalized_kuhnDirichletInf_shellFactor_le M R k c pi u
    rw [integral_const_mul] at hq
    have hmeasure : (M.P.toMeasure).real Set.univ = 1 := by simp
    rw [smul_eq_mul, hmeasure, one_mul]
    linarith [hq]
  have hqfinal : qRSlope M (unitMesh d (-(R : ℤ))) (originKuhnCell d pi 0) u ≤ qq := by
    refine le_trans (qRSlope_le_qRCell M ?_ _ hu) (hqR pi)
    intro V hV
    exact closedCarrier_subset_of_mem_unitMesh (by omega) hV
  have herrbound : kap * ((volume U.openCarrier).toReal⁻¹ * eps) ≤ err := by
    rw [heps']
    have hvne : (volume U.openCarrier).toReal ≠ 0 := ne_of_gt hvolU
    rw [show (volume U.openCarrier).toReal⁻¹ *
        (err * (volume U.openCarrier).toReal / (kap + 1)) = err / (kap + 1) by
      field_simp]
    rw [mul_div_assoc']
    rw [div_le_iff₀ hkap1]
    nlinarith [herr.le, hkap]
  calc ∫ omega, X omega ∂M.P.toMeasure
      ≤ ∫ omega, kap * H omega ∂M.P.toMeasure := hmain
    _ = kap * ∫ omega, H omega ∂M.P.toMeasure := integral_const_mul _ _
    _ ≤ kap * (qq + (volume U.openCarrier).toReal⁻¹ * eps) := by
        refine mul_le_mul_of_nonneg_left ?_ hkap
        linarith [hHval, hqfinal]
    _ = kap * qq + kap * ((volume U.openCarrier).toReal⁻¹ * eps) := by ring
    _ ≤ kap * qq + err := by linarith [herrbound]

end

end SubdiffusiveProcess.Section10
