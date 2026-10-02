import SubdiffusiveProcess.CoarseGrainingVocab.ACutoffRestrictionLaw
import SubdiffusiveProcess.CoarseGrainingVocab.NegativeBesovSupport
import SubdiffusiveProcess.CoarseGrainingVocab.RestrictionIndependence

/-!
# Integral locality and the natural range of a finite GMC cutoff

The finite cutoff depends only on the finitely many shell restrictions over
the observation set.  This module records that fact for CoarseGraining's
integral-local sigma fields and transports (g1) through the marginal scaling
law.

PROVENANCE: the organization and the one-shell transport mirror
`Algsuperdiff/Section3/Cutoff/LocalScaling.lean` and
`Algsuperdiff/Section3/Cutoff/ShellRange.lean`.  The nonlinear exponential
cutoff needs a separate joint-measurability argument, since it is not a linear
sum of coefficient fields.
-/

namespace SubdiffusiveProcess.CoarseGrainingVocab

open Homogenization MeasureTheory ProbabilityTheory
open scoped BigOperators Pointwise

noncomputable section


private abbrev Sample (d : ℕ) :=
  SubdiffusiveProcess.Frozen.Assumptions.PotentialSample d

variable {d : ℕ}

private theorem support_comp_inv_smul_subset_smul {d : ℕ}
    (r : ℝ) (hr : r ≠ 0) {U : Set (Vec d)} {phi : Vec d → ℝ}
    (hphi : Function.support phi ⊆ U) :
    Function.support (phi ∘ fun y : Vec d => r⁻¹ • y) ⊆ r • U := by
  intro y hy
  have hy' : r⁻¹ • y ∈ U := hphi hy
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr]
  exact hy'

/-- Spatial rescaling transports the integral-local sigma field by the
corresponding spatial image. -/
theorem measurable_smulReg_local (r : ℝ) (hr : r ≠ 0)
    (U : Set (Vec d)) :
    @Measurable (RegCoeffField d) (RegCoeffField d)
      (LocalSigmaR (r • U)) (LocalSigmaR U) (smulReg r hr) := by
  refine @measurable_generateFrom (RegCoeffField d) (RegCoeffField d)
    (LocalSigmaR (r • U)) _ _ ?_
  rintro s ⟨i, j, phi, hphi, hphiU, t, ht, rfl⟩
  let psi : Vec d → ℝ := phi ∘ fun y : Vec d => r⁻¹ • y
  have hpsi : IsProbeR psi :=
    hphi.comp_homeomorph (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr))
  have hpsiSupp : Function.support psi ⊆ r • U :=
    support_comp_inv_smul_subset_smul r hr hphiU
  have hentry : @Measurable (RegCoeffField d) ℝ
      (LocalSigmaR (r • U)) (borel ℝ) (entryTestR i j psi) := by
    intro w hw
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨i, j, psi, hpsi, hpsiSupp, w, hw, rfl⟩
  have hEq : entryTestR i j phi ∘ smulReg r hr =
      fun a => |(r ^ Module.finrank ℝ (Vec d))⁻¹| * entryTestR i j psi a := by
    funext a
    exact entryTestR_smulReg i j phi r hr a
  change @MeasurableSet (RegCoeffField d) (LocalSigmaR (r • U))
    ((entryTestR i j phi ∘ smulReg r hr) ⁻¹' t)
  rw [hEq]
  exact (hentry.const_mul _) ht

/-- The finite join of shell restrictions which the cutoff observes on `U`. -/
def aCutoffPotentialLocalSigma {d : ℕ} (L : ℕ) (U : Set (Vec d)) :
    MeasurableSpace (Sample d) :=
  ⨆ k : Fin (L + 1),
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U).comap
      (fun omega : Sample d => omega k)

private theorem measurable_aCutoff_eval_local {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {U : Set (Vec d)} (hU : IsOpen U) {x : Vec d} (hx : x ∈ U) :
    @Measurable (Sample d) ℝ (aCutoffPotentialLocalSigma L U) _
      (fun omega => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) := by
  have hcoord (k : Fin (L + 1)) :
      @Measurable (Sample d) (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
        (aCutoffPotentialLocalSigma L U)
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U)
        (fun omega => omega k) :=
    Measurable.of_comap_le (le_iSup
      (fun q : Fin (L + 1) =>
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U).comap
          (fun omega : Sample d => omega q)) k)
  have heval (k : Fin (L + 1)) :
      @Measurable (Sample d) ℝ (aCutoffPotentialLocalSigma L U) _
        (fun omega => omega k x) :=
    (measurable_eval_potentialFieldLocalSigma_of_mem_isOpen hU hx).comp
      (hcoord k)
  unfold SubdiffusiveProcess.Frozen.Assumptions.aCutoff
  apply Measurable.exp
  refine Finset.measurable_sum (Finset.range (L + 1)) fun k hk => ?_
  have hkLt : k < L + 1 := Finset.mem_range.mp hk
  exact (heval ⟨k, hkLt⟩).sub_const _

private theorem aux_heartbeat_measurable_aCutoff_pair_local {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {U : Set (Vec d)} (hU : IsOpen U) :
    @Measurable (Sample d × U) ℝ
      ((aCutoffPotentialLocalSigma L U).prod inferInstance) _
      (fun z => SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.1 z.2) := by
  letI : MeasurableSpace (Sample d) := aCutoffPotentialLocalSigma L U
  have hjoint : Measurable (fun z : U × Sample d =>
      SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.2 z.1) := by
    simpa only [Function.uncurry_apply_pair] using
      (measurable_uncurry_of_continuous_of_measurable
      (m := aCutoffPotentialLocalSigma L U) (mβ := (inferInstance : MeasurableSpace ℝ))
      (u := fun (x : U) (omega : Sample d) =>
        SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega (x : Vec d))
      (fun (omega : Sample d) =>
        (SubdiffusiveProcess.Frozen.Assumptions.continuous_aCutoff M L omega).comp
        continuous_subtype_val)
      (fun (x : U) => measurable_aCutoff_eval_local M L hU x.property))
  exact measurable_swap_iff.mp hjoint

private theorem aux_heartbeat_measurable_entryTest_aCutoff_local {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {U : Set (Vec d)} (hU : IsOpen U) (i j : Fin d) {phi : Vec d → ℝ}
    (hphi : IsProbeR phi) (hphiU : Function.support phi ⊆ U) :
    @Measurable (Sample d) ℝ (aCutoffPotentialLocalSigma L U) _
      (fun omega => entryTestR i j phi (aCutoffRegCoeffField M L omega)) := by
  letI : MeasurableSpace (Sample d) := aCutoffPotentialLocalSigma L U
  let F : Sample d × U → ℝ := fun z =>
    scalarMatrix (d := d) (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.1 z.2) i j * phi z.2
  have hF : Measurable F := by
    have hcut := aux_heartbeat_measurable_aCutoff_pair_local M L hU
    change Measurable (fun z : Sample d × U =>
      (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L z.1 z.2 * (1 : Mat d) i j) * phi z.2)
    exact (hcut.mul_const ((1 : Mat d) i j)).mul
      (hphi.measurable.comp (measurable_subtype_coe.comp measurable_snd))
  let embed : Sample d × U → Sample d × Vec d :=
    Prod.map id Subtype.val
  have hembed : MeasurableEmbedding embed :=
    MeasurableEmbedding.id.prodMap
      (MeasurableEmbedding.subtype_coe hU.measurableSet)
  let G : Sample d × Vec d → ℝ :=
    Function.extend embed F (fun _ => 0)
  have hG : Measurable G :=
    hembed.measurable_extend hF measurable_const
  have hInt : Measurable (fun omega : Sample d =>
      ∫ x : Vec d, G (omega, x) ∂(volume.restrict U)) :=
    hG.stronglyMeasurable.integral_prod_right'.measurable
  have hEq : (fun omega : Sample d =>
      ∫ x : Vec d, G (omega, x) ∂(volume.restrict U)) =
      fun omega => entryTestR i j phi (aCutoffRegCoeffField M L omega) := by
    funext omega
    change (∫ x in U, G (omega, x) ∂volume) =
      ∫ x, scalarMatrix
        (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) i j * phi x ∂volume
    calc
      (∫ x in U, G (omega, x) ∂volume) =
          ∫ x in U, scalarMatrix
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) i j * phi x ∂volume := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
        have hembedApply : embed (omega, ⟨x, hx⟩) = (omega, x) := rfl
        rw [← hembedApply]
        exact hembed.injective.extend_apply F (fun _ => 0) (omega, ⟨x, hx⟩)
      _ = ∫ x, scalarMatrix
            (SubdiffusiveProcess.Frozen.Assumptions.aCutoff M L omega x) i j * phi x ∂volume := by
        rw [← integral_indicator hU.measurableSet]
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ U
        · simp [Set.indicator_of_mem hx]
        · have hphiZero : phi x = 0 := by
            by_contra hne
            exact hx (hphiU hne)
          simp [Set.indicator_of_notMem hx, hphiZero]
  exact hEq ▸ hInt

/-- The nonlinear finite cutoff is measurable from its finite shell-local
source sigma field into the integral-local coefficient sigma field. -/
theorem measurable_aCutoffRegCoeffField_local {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    {U : Set (Vec d)} (hU : IsOpen U) :
    @Measurable (Sample d) (RegCoeffField d)
      (aCutoffPotentialLocalSigma L U) (LocalSigmaR U)
      (aCutoffRegCoeffField M L) := by
  refine @measurable_generateFrom (Sample d) (RegCoeffField d)
    (aCutoffPotentialLocalSigma L U) _ _ ?_
  rintro s ⟨i, j, phi, hphi, hphiU, t, ht, rfl⟩
  exact (aux_heartbeat_measurable_entryTest_aCutoff_local M L hU i j hphi hphiU) ht

private theorem vecNorm_smul {d : ℕ} (c : ℝ) (v : Vec d) :
    Homogenization.Book.Ch02.vecNorm (c • v) =
      |c| * Homogenization.Book.Ch02.vecNorm v := by
  change ‖(WithLp.toLp 2 (c • v) : EuclideanSpace ℝ (Fin d))‖ =
    |c| * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖
  have h : (WithLp.toLp 2 (c • v) : EuclideanSpace ℝ (Fin d)) =
      c • (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) := by
    ext i
    rfl
  rw [h, norm_smul, Real.norm_eq_abs]

private theorem scaled_separation_of_le {d : ℕ} (L k : ℕ) (hkL : k ≤ L)
    {U V : Set (Vec d)}
    (hsep : ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤
        Homogenization.Book.Ch02.vecNorm (x - y)) :
    ∀ ⦃x y : Vec d⦄,
      x ∈ ((3 : ℝ) ^ k)⁻¹ • U → y ∈ ((3 : ℝ) ^ k)⁻¹ • V →
      Real.sqrt (d : ℝ) ≤ Homogenization.Book.Ch02.vecNorm (x - y) := by
  rintro x y ⟨x0, hx0, rfl⟩ ⟨y0, hy0, rfl⟩
  have hthree : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hfactor : 1 ≤ (3 : ℝ) ^ (L - k) :=
    one_le_pow₀ (by norm_num)
  have hsource := hsep hx0 hy0
  have hscaled : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (L - k) ≤
      ((3 : ℝ) ^ k)⁻¹ * Homogenization.Book.Ch02.vecNorm (x0 - y0) := by
    have heq : Real.sqrt (d : ℝ) * (3 : ℝ) ^ (L - k) =
        ((3 : ℝ) ^ k)⁻¹ *
          (Real.sqrt (d : ℝ) * (3 : ℝ) ^ L) := by
      rw [show (3 : ℝ) ^ L = (3 : ℝ) ^ k * (3 : ℝ) ^ (L - k) by
        rw [← pow_add, Nat.add_sub_of_le hkL]]
      field_simp [ne_of_gt hthree]
    rw [heq]
    exact mul_le_mul_of_nonneg_left hsource (inv_nonneg.mpr hthree.le)
  calc
    Real.sqrt (d : ℝ) ≤ Real.sqrt (d : ℝ) * (3 : ℝ) ^ (L - k) := by
      nlinarith [Real.sqrt_nonneg (d : ℝ)]
    _ ≤ ((3 : ℝ) ^ k)⁻¹ * Homogenization.Book.Ch02.vecNorm (x0 - y0) := hscaled
    _ = Homogenization.Book.Ch02.vecNorm
        (((3 : ℝ) ^ k)⁻¹ • x0 - ((3 : ℝ) ^ k)⁻¹ • y0) := by
      rw [← smul_sub, vecNorm_smul, abs_of_pos (inv_pos.mpr hthree)]

private theorem measurable_triadicScale_local {d : ℕ} (k : ℕ)
    (U : Set (Vec d)) :
    @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma
        (((3 : ℝ) ^ k)⁻¹ • U))
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U)
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k) := by
  let r : ℝ := ((3 : ℝ) ^ k)⁻¹
  have hr : r ≠ 0 := by positivity
  have hforget : @Measurable
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d) (RegCoeffField d)
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma (r • U))
      (LocalSigmaR (r • U))
      SubdiffusiveProcess.Frozen.Assumptions.PotentialField.forgetPotential :=
    Measurable.of_comap_le le_rfl
  change @Measurable (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d)
    (MeasurableSpace.comap SubdiffusiveProcess.Frozen.Assumptions.PotentialField.forgetPotential
      (LocalSigmaR (r • U)))
    (MeasurableSpace.comap SubdiffusiveProcess.Frozen.Assumptions.PotentialField.forgetPotential
      (LocalSigmaR U))
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
  rw [measurable_comap_iff]
  have h := (measurable_smulReg_local r hr U).comp hforget
  simpa only [Function.comp_apply, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.forgetPotential_apply,
    smulReg_apply, SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale_apply] using h

private theorem euclideanNorm_eq_vecNorm {d : ℕ} (x : Vec d) :
    Homogenization.euclideanNorm x = Homogenization.Book.Ch02.vecNorm x := by
  rw [← sq_eq_sq₀ (Homogenization.euclideanNorm_nonneg x)
    (Homogenization.Book.Ch02.vecNorm_nonneg x),
    Homogenization.euclideanNorm_sq,
    Homogenization.Book.Ch02.vecNorm_sq_eq_vecNormSq]

/-- One scaled shell has the cutoff's natural integral-local range. -/
theorem indep_potentialShellLocal_of_cutoff_separation {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ) (k : Fin (L + 1))
    (U V : Set (Vec d)) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hsep : ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤
        Homogenization.Book.Ch02.vecNorm (x - y)) :
    Indep ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U).comap
      (fun omega : Sample d => omega k))
      ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma V).comap
      (fun omega : Sample d => omega k)) M.P.toMeasure := by
  let r : ℝ := ((3 : ℝ) ^ (k : ℕ))⁻¹
  have hr : r ≠ 0 := by positivity
  have hUscaled : MeasurableSet (r • U) := hU.const_smul_of_ne_zero hr
  have hVscaled : MeasurableSet (r • V) := hV.const_smul_of_ne_zero hr
  have hzero : Indep
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma (r • U))
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma (r • V))
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
    M.G1.range_dependence (r • U) (r • V) hUscaled hVscaled (by
      simpa only [r, euclideanNorm_eq_vecNorm] using
        scaled_separation_of_le L (k : ℕ)
          (Nat.le_of_lt_succ k.isLt) hsep)
  have hcomap : Indep
      ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U).comap
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k))
      ((SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma V).comap
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k))
      (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure :=
    indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hzero
        (measurable_triadicScale_local k U).comap_le)
      (measurable_triadicScale_local k V).comap_le
  have hmarginal : Indep
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U)
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma V)
      (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure := by
    have hmap := (indep_comap_iff_indep_map
      (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.measurable_triadicScale k).aemeasurable
      (potentialFieldLocalSigma_le_borel U)
      (potentialFieldLocalSigma_le_borel V)).mp hcomap
    have hscale := congrArg ProbabilityMeasure.toMeasure
      (M.shellPrefix.marginal_scaling (k : ℕ))
    change (SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw M.P k).toMeasure =
      Measure.map (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.triadicScale k)
        (SubdiffusiveProcess.Frozen.Assumptions.zeroPotentialLaw M.P).toMeasure at hscale
    rwa [hscale]
  exact (indep_comap_iff_indep_map
    (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k).aemeasurable
    (potentialFieldLocalSigma_le_borel U)
    (potentialFieldLocalSigma_le_borel V)).mpr (by
      simpa [SubdiffusiveProcess.Frozen.Assumptions.potentialMarginalLaw] using hmarginal)

/-- The two finite cutoff source sigma fields are independent at the literal
natural range `sqrt(d) * 3^L`. -/
theorem indep_aCutoffPotentialLocalSigma_of_separation {d : ℕ}
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (U V : Set (Vec d)) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hsep : ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤
        Homogenization.Book.Ch02.vecNorm (x - y)) :
    Indep (aCutoffPotentialLocalSigma L U) (aCutoffPotentialLocalSigma L V)
      M.P.toMeasure := by
  let kappa : Fin (L + 1) → MeasurableSpace (Sample d) := fun k =>
    MeasurableSpace.comap (fun omega : Sample d => omega k)
      (inferInstance : MeasurableSpace
        (SubdiffusiveProcess.Frozen.Assumptions.PotentialField d))
  let a : Fin (L + 1) → MeasurableSpace (Sample d) := fun k =>
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma U).comap
      (fun omega : Sample d => omega k)
  let b : Fin (L + 1) → MeasurableSpace (Sample d) := fun k =>
    (SubdiffusiveProcess.Frozen.Assumptions.PotentialField.localSigma V).comap
      (fun omega : Sample d => omega k)
  have hkappa : iIndep kappa M.P.toMeasure := by
    simpa [kappa, Function.comp_def] using
      M.shellPrefix.independent.iIndep.precomp
        (g := fun k : Fin (L + 1) => (k : ℕ)) Fin.val_injective
  have hle (k : Fin (L + 1)) :
      kappa k ≤ (inferInstance : MeasurableSpace (Sample d)) :=
    (SubdiffusiveProcess.Frozen.Assumptions.measurable_potentialCoordinate k).comap_le
  have ha (k : Fin (L + 1)) : a k ≤ kappa k :=
    MeasurableSpace.comap_mono (potentialFieldLocalSigma_le_borel U)
  have hb (k : Fin (L + 1)) : b k ≤ kappa k :=
    MeasurableSpace.comap_mono (potentialFieldLocalSigma_le_borel V)
  have hab (k : Fin (L + 1)) : Indep (a k) (b k) M.P.toMeasure :=
    indep_potentialShellLocal_of_cutoff_separation M L k U V hU hV hsep
  simpa [aCutoffPotentialLocalSigma, a, b] using
    indep_iSup_of_indep_of_iIndep hkappa hle ha hb hab

/-- The literal finite-cutoff coefficient has integral-local range at most
`sqrt(d) * 3^L`. -/
theorem indep_aCutoffRegCoeffField_local_of_separation {d : ℕ} [NeZero d]
    (M : SubdiffusiveProcess.Frozen.Assumptions.GMCModel d) (L : ℕ)
    (U V : Set (Vec d)) (hU : IsOpen U) (hV : IsOpen V)
    (hsep : ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V →
      Real.sqrt (d : ℝ) * (3 : ℝ) ^ L ≤
        Homogenization.Book.Ch02.vecNorm (x - y)) :
    Indep ((LocalSigmaR U).comap (aCutoffRegCoeffField M L))
      ((LocalSigmaR V).comap (aCutoffRegCoeffField M L)) M.P.toMeasure := by
  exact indep_of_indep_of_le_right
    (indep_of_indep_of_le_left
      (indep_aCutoffPotentialLocalSigma_of_separation M L U V
        hU.measurableSet hV.measurableSet hsep)
      (measurable_aCutoffRegCoeffField_local M L hU).comap_le)
    (measurable_aCutoffRegCoeffField_local M L hV).comap_le

end

end SubdiffusiveProcess.CoarseGrainingVocab
