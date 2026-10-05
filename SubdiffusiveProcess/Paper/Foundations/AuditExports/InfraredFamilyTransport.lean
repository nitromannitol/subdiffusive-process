module

public import SubdiffusiveProcess.Paper.Foundations.AuditExports.InfraredFamilyRegularity
public import SubdiffusiveProcess.Paper.neumann_ht_campanato
public import SubdiffusiveProcess.Paper.neumann_ht_energy
public import SubdiffusiveProcess.Paper.lem_as_regularity

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric Filter
open SubdiffusiveProcess SubdiffusiveProcess.Paper SubdiffusiveProcess.EllipticRegularity
open scoped ENNReal NNReal BigOperators ContDiff Topology

noncomputable section
namespace SubdiffusiveProcess.AuditExports

/-- Both bounded-source estimates for a fixed deleted coarse block, with
all prescribed finite moments. The threshold precedes the block length. -/
theorem top_block_neumann_source :
  ∀ (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (_P : in_poincare d hd E)
    (_X : in_extension d hd E) (_W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (_Cp : CampanatoInput d) (t alpha : ℝ)
    (k : ℕ) (ps : Fin k → ℝ),
    (d : ℝ) - 1 < t → t < d → 0 < alpha → alpha < 1 → (∀ i, 1 ≤ ps i) →
  ∃ delta0 : ℝ, 0 < delta0 ∧
    ∀ (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
      (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg),
      M.delta ≤ delta0 → ∀ j : ℕ, 0 < j →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cbound : Fin k → ℝ),
        (∀ N om, 0 ≤ K N om) ∧
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cbound i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
        ∀ (N : ℕ)
          (F : SpatialCoordinates d → ℝ) (Kf : ℝ),
          0 ≤ Kf →
          AEMeasurable F
            (volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))) →
          (∀ᵐ x ∂(volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))),
            |F x| ≤ Kf) →
          (∫ x in (unitNeumannCube d : Set (SpatialCoordinates d)), F x) = 0 →
        ∀ v : meanZeroSobolevGraph (unitNeumannCube d),
          SolvesNeumann
              (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) (fun _ => (1 / 2 : ℝ)) one_pos) F v →
          (∃ U : SpatialCoordinates d → ℝ, Continuous U ∧
            IsHolderOn alpha
                (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)) U ∧
            ((v : SobolevData (unitNeumannCube d)).1 : SpatialCoordinates d → ℝ)
                =ᵐ[volume.restrict (unitNeumannCube d : Set (SpatialCoordinates d))] U ∧
            cAlphaNorm alpha
                (closedCube (fun _ : Fin d => (1 / 2 : ℝ)) 1 one_pos :
                  Set (SpatialCoordinates d)) U ≤ K N om * Kf) ∧
          (∀ (x : SpatialCoordinates d) (rad : ℝ), x ∈ unitNeumannCube d →
            0 < rad → rad ≤ 1 →
            localGradientEnergy
                (cutoffPositiveCoefficient M (calib3_HT d j) om (N + j) (fun _ => (1 / 2 : ℝ)) one_pos)
                (s := Metric.ball x rad ∩
                  (unitNeumannCube d : Set (SpatialCoordinates d)))
                (isOpen_ball.measurableSet.inter (unitNeumannCube d).isOpen.measurableSet)
                (sobolevGradient (v : SobolevData (unitNeumannCube d))) ≤
              K N om * Kf ^ 2 * rad ^ t) := by
  intro d hd _ _ E P X W D Cp t alpha k ps ht1 htd ha0 ha1 hps
  obtain ⟨deltaE, hdeltaE, hEn⟩ :=
    neumann_ht_energy d hd E P X W D t k ps ht1 htd hps
  obtain ⟨deltaC, hdeltaC, hCa⟩ :=
    neumann_ht_campanato d hd E P X W D alpha k ps ha0 ha1 hps
  refine ⟨min deltaE deltaC, lt_min hdeltaE hdeltaC, ?_⟩
  intro M Rm Sreg It hdelta j hj
  obtain ⟨KE, CE, hKE0, hKEL, hKEB, hEae⟩ :=
    hEn M Rm Sreg It (hdelta.trans (min_le_left _ _)) j hj
  obtain ⟨Kc, Cc, hKc0, hKcL, hKcB, hCae⟩ :=
    hCa M Rm Sreg It (hdelta.trans (min_le_right _ _)) j hj
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = max 1 ((2 + Real.sqrt d) * Cp.C alpha) := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := hcdef ▸ le_max_left _ _
  have hc0 : 0 ≤ c := by linarith
  have hcC : (2 + Real.sqrt d) * Cp.C alpha ≤ c := hcdef ▸ le_max_right _ _
  refine ⟨fun N om => 1 + c * (KE N om + Kc N om),
    fun i => 1 + c * (max (CE i) 0 + max (Cc i) 0),
    fun N om => add_nonneg zero_le_one
      (mul_nonneg hc0 (add_nonneg (hKE0 N om) (hKc0 N om))), ?_, ?_, ?_⟩
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (KE N) (Kc N) hc0
      (hKEL i N) (hKcL i N) (hKEB i N) (hKcB i N)).1
  · intro i N
    exact (aux_prop_growth_holder_assembly_moment _ (hps i) (KE N) (Kc N) hc0
      (hKEL i N) (hKcL i N) (hKEB i N) (hKcB i N)).2
  · filter_upwards [hEae, hCae] with om hE hC
    intro N F Kf hKf hFm hFb hmean v hsol
    have hKE := hKE0 N om
    have hKc := hKc0 N om
    obtain ⟨U, hUc, hUH, hUae, hUn⟩ := aux_cor_neumann_source_holder_of_campanato Cp ha0 ha1 v
      hKc hKf (hC N F Kf hKf hFm hFb hmean v hsol)
    refine ⟨⟨U, hUc, hUH, hUae, hUn.trans ?_⟩, ?_⟩
    · have h1 : (2 + Real.sqrt d) * Cp.C alpha * Kc N om ≤ c * Kc N om :=
        mul_le_mul_of_nonneg_right hcC hKc
      have h2 : c * Kc N om ≤ c * (KE N om + Kc N om) :=
        mul_le_mul_of_nonneg_left (by linarith) hc0
      have h3 : (2 + Real.sqrt d) * Cp.C alpha * Kc N om ≤ 1 + c * (KE N om + Kc N om) := by
        linarith
      exact mul_le_mul_of_nonneg_right h3 hKf
    · intro x rad hx hrad hrad1
      have h := hE N F Kf hKf hFm hFb hmean v hsol x rad hx hrad hrad1
      have h1 : KE N om ≤ c * KE N om := le_mul_of_one_le_left hKE hc1
      have h2 : c * KE N om ≤ c * (KE N om + Kc N om) :=
        mul_le_mul_of_nonneg_left (by linarith) hc0
      have hKle : KE N om ≤ 1 + c * (KE N om + Kc N om) := by linarith
      calc _ ≤ KE N om * Kf ^ 2 * rad ^ t := h
        _ ≤ (1 + c * (KE N om + Kc N om)) * Kf ^ 2 * rad ^ t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKle (sq_nonneg _))
            (Real.rpow_nonneg hrad.le _)

/-- Signed finite infrared conventions used only in affine transport.
Nonnegative indices are positive truncations; a negative index deletes that
many coarse ultraviolet layers. -/
def signedInfrared {d : ℕ} (j : ℤ) :
    BilateralField d → C(SpatialCoordinates d, ℝ) :=
  if 0 ≤ j then fun om => infraredPartialSum om j.toNat
  else calib3_HT d (-j).toNat

/-- One unit-cube bank covers the infinite positive family, its limit,
and any fixed finite collection of deleted coarse blocks. Its disorder
threshold is independent of the lower bound of the signed indices. -/
theorem infrared_extended_neumann_source
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (ht1 : (d : ℝ) - 1 < t) (htd : t < d)
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
        InfraredCharacterization M H → M.delta ≤ delta0 → ∀ m : ℕ,
        ∃ (K : ℕ → BilateralField d → ℝ) (Cb : Fin k → ℝ),
          (∀ N om, 0 ≤ K N om) ∧
          (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
          (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
            ENNReal.ofReal (Cb i)) ∧
          ∀ᵐ om ∂(chaosSampleLaw M).toMeasure,
            (∀ N, aux_lem_as_regularity_nc_estimate (fun _ => (1 / 2 : ℝ)) 1 one_pos
              (cutoffPositiveCoefficient M H om N (fun _ => (1 / 2 : ℝ)) one_pos)
              t alpha (K N om)) ∧
            ∀ (j : ℤ) (N : ℕ), -(m : ℤ) ≤ j → -(N : ℤ) ≤ j →
              aux_lem_as_regularity_nc_estimate (fun _ => (1 / 2 : ℝ)) 1 one_pos
                (cutoffPositiveCoefficient M (signedInfrared j) om N
                  (fun _ => (1 / 2 : ℝ)) one_pos) t alpha (K N om) := by
  classical
  obtain ⟨dp, hdp, hpositive⟩ :=
    infrared_family_neumann_source d hd E P X W D Cp t alpha k ps ht1 htd ha0 ha1 hps
  obtain ⟨dn, hdn, hnegative⟩ :=
    top_block_neumann_source d hd E P X W D Cp t alpha k ps ht1 htd ha0 ha1 hps
  refine ⟨min dp dn, lt_min hdp hdn, ?_⟩
  intro M Rm Sreg It H hH hdelta m
  obtain ⟨Kp, Cp0, hKp0, hKpL, hKpB, hKpae⟩ :=
    hpositive M Rm Sreg It H hH (hdelta.trans (min_le_left _ _))
  choose Kn Cn hKn0 hKnL hKnB hKnae using fun l : Fin m =>
    hnegative M Rm Sreg It (hdelta.trans (min_le_right _ _)) (l.val + 1) (Nat.succ_pos _)
  let Ksum : ℕ → BilateralField d → ℝ := fun N om =>
    ∑ l : Fin m, Kn l (N - (l.val + 1)) om
  let K : ℕ → BilateralField d → ℝ := fun N om => Kp N om + Ksum N om
  have hsum0 : ∀ N om, 0 ≤ Ksum N om := fun N om =>
    Finset.sum_nonneg fun l _ => hKn0 l _ om
  have hKpK : ∀ N om, Kp N om ≤ K N om := fun N om =>
    le_add_of_nonneg_right (hsum0 N om)
  have hKnK : ∀ l : Fin m, ∀ N om, Kn l (N - (l.val + 1)) om ≤ K N om := by
    intro l N om
    exact (Finset.single_le_sum (f := fun j : Fin m => Kn j (N - (j.val + 1)) om)
      (fun j _ => hKn0 j _ om) (Finset.mem_univ l)).trans
      (le_add_of_nonneg_left (hKp0 N om))
  have hsumLp : ∀ i N, MemLp (Ksum N) (ENNReal.ofReal (ps i))
      (chaosSampleLaw M).toMeasure := fun i N =>
    memLp_finsetSum Finset.univ (fun l _ => hKnL l i _)
  have hsumBd : ∀ i N, eLpNorm (Ksum N) (ENNReal.ofReal (ps i))
      (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (∑ l : Fin m, max (Cn l i) 0) := by
    intro i N
    have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (ps i) := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hps i)
    calc
      _ ≤ ∑ l : Fin m, eLpNorm (Kn l (N - (l.val + 1))) (ENNReal.ofReal (ps i))
          (chaosSampleLaw M).toMeasure := by
        simpa only [Ksum, Finset.sum_fn] using
          (eLpNorm_sum_le (μ := (chaosSampleLaw M).toMeasure) (s := Finset.univ)
            (f := fun l : Fin m => Kn l (N - (l.val + 1))) hp)
      _ ≤ ∑ l : Fin m, ENNReal.ofReal (max (Cn l i) 0) :=
        Finset.sum_le_sum fun l _ =>
          (hKnB l i _).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun l _ => le_max_right _ _)).symm
  refine ⟨K, fun i => max (Cp0 i) 0 + ∑ l : Fin m, max (Cn l i) 0,
    fun N om => add_nonneg (hKp0 N om) (hsum0 N om),
    fun i N => (hKpL i N).add (hsumLp i N), ?_, ?_⟩
  · intro i N
    have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (ps i) := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hps i)
    calc
      _ ≤ eLpNorm (Kp N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure +
          eLpNorm (Ksum N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure := eLpNorm_add_le hp
      _ ≤ ENNReal.ofReal (max (Cp0 i) 0) +
          ENNReal.ofReal (∑ l : Fin m, max (Cn l i) 0) :=
        add_le_add ((hKpB i N).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) (hsumBd i N)
      _ = _ := (ENNReal.ofReal_add (le_max_right _ _)
        (Finset.sum_nonneg (fun l _ => le_max_right _ _))).symm
  · filter_upwards [hKpae, ae_all_iff.mpr hKnae] with om hp hn
    constructor
    · intro N
      exact aux_lem_as_regularity_nc_estimate_mono (hKpK N om) (hp none N)
    · intro j N hjm hjN
      by_cases hj : 0 ≤ j
      · simpa only [signedInfrared, ite_eq_left hj, infraredFamily, Option.elim_some] using
          aux_lem_as_regularity_nc_estimate_mono (hKpK N om) (hp (some j.toNat) N)
      · let l : Fin m := ⟨(-j).toNat - 1, by omega⟩
        have hl : (l.val + 1 : ℤ) = -j := by dsimp [l]; omega
        have hlN : l.val + 1 ≤ N := by omega
        have hNN : N - (l.val + 1) + (l.val + 1) = N := Nat.sub_add_cancel hlN
        have heq : signedInfrared (d := d) j = calib3_HT d (l.val + 1) := by
          simp only [signedInfrared, ite_eq_right hj]
          congr 1
          omega
        rw [heq]
        have hh := aux_lem_as_regularity_nc_estimate_mono (hKnK l N om) (hn l (N - (l.val + 1)))
        simpa only [hNN] using hh
/-- The single affine shift obtained by composing the integer field shift
with the bounded residual-model dilation. -/
def infraredAffineShift {d : ℕ} (s : ℤ) (w : SpatialCoordinates d) (r : ℝ)
    (om : BilateralField d) : BilateralField d :=
  fun j => (om (j - s)).comp ⟨fun x => w + r • x, by fun_prop⟩

theorem infraredAffineShift_apply {d : ℕ} (s : ℤ) (w x : SpatialCoordinates d)
    (r : ℝ) (om : BilateralField d) (j : ℤ) :
    infraredAffineShift s w r om j x = om (j - s) (w + r • x) := rfl

theorem infraredAffineShift_eq_residualShift {d : ℕ}
    (m : ℤ) (w : SpatialCoordinates d) (r rho : ℝ)
    (hreq : r = (3 : ℝ) ^ (-m) * rho) :
    infraredAffineShift (m + 1) w r =
      SubdiffusiveProcess.MacroAllCube.residualShift rho 1 ∘ aux_transport_S m w := by
  funext om j
  ext x
  rw [infraredAffineShift_apply]
  change om (j - (m + 1)) (w + r • x) =
    aux_transport_S m w om (j - (1 : ℤ)) (rho • x)
  rw [aux_transport_S_apply, smul_smul, hreq]
  congr 2
  ring

/-- The affine field map preserves the law of the genuine residual model;
the model and its disorder are constructed, rather than supplied as a
scale-covariance premise. -/
theorem infraredAffineShift_measurePreserving
    {d : ℕ} [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Model.GMCModel d) (m : ℤ) (w : SpatialCoordinates d)
    (r rho : ℝ) (hs1 : 1 ≤ rho * (3 : ℝ)) (hs3 : rho * (3 : ℝ) ≤ 3)
    (hdelta : M.delta ≤ (2 * SubdiffusiveProcess.ResidualModel.residualDisorderFactor d)⁻¹)
    (hreq : r = (3 : ℝ) ^ (-m) * rho) :
    MeasurePreserving (infraredAffineShift (m + 1) w r)
      (chaosSampleLaw M).toMeasure
      (chaosSampleLaw (SubdiffusiveProcess.ResidualModel.residualModel M hs1 hs3 hdelta)).toMeasure := by
  rw [infraredAffineShift_eq_residualShift m w r rho hreq]
  simpa only [pow_one] using (SubdiffusiveProcess.ResidualModel.measurePreserving_residualModel M rho 1
    (by simpa only [pow_one] using hs1) (by simpa only [pow_one] using hs3) hdelta).comp
    (aux_transport_S_measurePreserving M m w)

/-- Finite positive infrared sums obey the same affine identity as the
limit, provided the shifted upper index is nonnegative. -/
theorem infraredPartialSum_affineShift {d : ℕ}
    (s : ℤ) (w x : SpatialCoordinates d) (r : ℝ)
    (om : BilateralField d) (L : ℕ) (hL : 0 ≤ (L : ℤ) + s) :
    infraredPartialSum (infraredAffineShift s w r om) ((L : ℤ) + s).toNat x =
      (infraredPartialSum om L (w + r • x) - infraredPartialSum om L w) +
        (aux_transport_retained s (w + r • x) om - aux_transport_retained s w om) := by
  let J : ℕ := ((L : ℤ) + s).toNat
  have hsJ : s ≤ (J : ℤ) := by dsimp [J]; omega
  have hJL : ((J : ℤ) - s).toNat = L := by dsimp [J]; omega
  rw [aux_transport_infraredPartialSum_apply]
  have hstep : ∀ n : ℕ,
      infraredAffineShift s w r om (Int.ofNat (n + 1)) x -
          infraredAffineShift s w r om (Int.ofNat (n + 1)) 0 =
        om (Int.ofNat (n + 1) - s) (w + r • x) -
          om (Int.ofNat (n + 1) - s) w := by
    intro n
    simp only [infraredAffineShift_apply, smul_zero, add_zero]
  simp_rw [hstep]
  have hf := aux_transport_infrared_sum
    (fun i => om i (w + r • x) - om i w) s J hsJ
  rw [hf, hJL, aux_transport_infraredPartialSum_diff]
  exact congrArg ((infraredPartialSum om L (w + r • x) - infraredPartialSum om L w) + ·)
    (aux_transport_ret_sub s (fun i => om i (w + r • x)) (fun i => om i w))

/-- Exact finite-window potential identity in the positive branch. -/
theorem cutoffPotential_affineShift_positive {d : ℕ}
    (s : ℤ) (w x : SpatialCoordinates d) (r : ℝ)
    (om : BilateralField d) (N L : ℕ)
    (hN : s ≤ (N : ℤ)) (hL : 0 ≤ (L : ℤ) + s) :
    cutoffPotential (fun eta => infraredPartialSum eta L) om N (w + r • x) =
      cutoffPotential (signedInfrared ((L : ℤ) + s)) (infraredAffineShift s w r om)
        ((N : ℤ) - s).toNat x + infraredPartialSum om L w + aux_transport_retained s w om := by
  have hir := infraredPartialSum_affineShift s w x r om L hL
  have huv := aux_transport_potential_sum (fun i => om i (w + r • x)) N s hN
  have hnew : ∑ k ∈ Finset.range (((N : ℤ) - s).toNat + 1),
      infraredAffineShift s w r om (-(Int.ofNat k)) x =
      ∑ k ∈ Finset.range (((N : ℤ) - s).toNat + 1), om (-(Int.ofNat k) - s) (w + r • x) :=
    Finset.sum_congr rfl (fun k _ => infraredAffineShift_apply s w x r om _)
  simp only [cutoffPotential, signedInfrared, ite_eq_left hL]
  rw [hnew, hir]
  change (∑ k ∈ Finset.range (N + 1), om (-(Int.ofNat k)) (w + r • x)) =
    (∑ k ∈ Finset.range (((N : ℤ) - s).toNat + 1), om (-(Int.ofNat k) - s) (w + r • x)) +
      aux_transport_retained s (w + r • x) om at huv
  linarith

/-- The few negative shifted indices are precisely the deleted coarse
blocks from the already proved `neumann_ht_*` producers. -/
theorem cutoffPotential_affineShift_negative {d : ℕ}
    (s : ℤ) (w x : SpatialCoordinates d) (r : ℝ)
    (om : BilateralField d) (N L : ℕ)
    (hN : s ≤ (N : ℤ)) (hL : (L : ℤ) + s < 0) :
    cutoffPotential (fun eta => infraredPartialSum eta L) om N (w + r • x) =
      cutoffPotential (signedInfrared ((L : ℤ) + s)) (infraredAffineShift s w r om)
        ((N : ℤ) - s).toNat x -
          ∑ i ∈ Finset.range L, om (Int.ofNat (i + 1)) 0 := by
  let j : ℕ := (-((L : ℤ) + s)).toNat
  let k : ℕ := (-s).toNat
  have hsk : (k : ℤ) = -s := by dsimp [k]; omega
  have hjk : j + L = k := by dsimp [j, k]; omega
  have hret := aux_fscc_holNeuH_retained_eq_neg s (by omega) (w + r • x) om
  let f : ℕ → ℝ := fun i => om (-s - (i : ℤ)) (w + r • x)
  have htail : ∑ i ∈ Finset.range L, f (j + i) =
      ∑ i ∈ Finset.range L, om (Int.ofNat (i + 1)) (w + r • x) := by
    have hreflect := Finset.sum_range_reflect
      (fun i : ℕ => om (Int.ofNat (i + 1)) (w + r • x)) L
    calc
      _ = ∑ i ∈ Finset.range L, om (Int.ofNat (L - 1 - i + 1)) (w + r • x) := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [f]
        congr 2
        have hiL := Finset.mem_range.mp hi
        dsimp [j] at *
        omega
      _ = _ := hreflect
  have hsplit : ∑ i ∈ Finset.range k, f i =
      (∑ i ∈ Finset.range j, f i) +
        ∑ i ∈ Finset.range L, om (Int.ofNat (i + 1)) (w + r • x) := by
    rw [← hjk, Finset.sum_range_add, htail]
  have hHT : signedInfrared ((L : ℤ) + s) (infraredAffineShift s w r om) x =
      -∑ i ∈ Finset.range j, f i := by
    simp only [signedInfrared, ite_eq_right (not_le.mpr hL), calib3_HT,
      ContinuousMap.neg_apply, ContinuousMap.sum_apply, infraredAffineShift_apply]
    apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro i _
    dsimp [f]
    congr 2
    ring
  have huv := aux_transport_potential_sum (fun i => om i (w + r • x)) N s hN
  have hnew : ∑ i ∈ Finset.range (((N : ℤ) - s).toNat + 1),
      infraredAffineShift s w r om (-(Int.ofNat i)) x =
      ∑ i ∈ Finset.range (((N : ℤ) - s).toNat + 1), om (-(Int.ofNat i) - s) (w + r • x) :=
    Finset.sum_congr rfl (fun i _ => infraredAffineShift_apply s w x r om _)
  unfold cutoffPotential
  rw [hHT, hnew,
    aux_transport_infraredPartialSum_apply, Finset.sum_sub_distrib]
  change (∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat i)) (w + r • x)) =
    (∑ i ∈ Finset.range (((N : ℤ) - s).toNat + 1), om (-(Int.ofNat i) - s) (w + r • x)) +
      aux_transport_retained s (w + r • x) om at huv
  change aux_transport_retained s (w + r • x) om = -∑ i ∈ Finset.range k, f i at hret
  linarith [hret, hsplit]

/-- Adding one integer layer to the retained block adds exactly that layer.
This identity includes the crossing from negative to nonnegative blocks. -/
theorem retained_add_one {d : ℕ} (m : ℤ) (w : SpatialCoordinates d)
    (om : BilateralField d) :
    aux_transport_retained (m + 1) w om = aux_transport_retained m w om + om (-m) w := by
  let N : ℕ := (m + 1).toNat
  let n : ℕ := ((N : ℤ) - (m + 1)).toNat
  have hmN : m ≤ (N : ℤ) := by dsimp [N]; omega
  have hsN : m + 1 ≤ (N : ℤ) := by dsimp [N]; omega
  have hdiff : ((N : ℤ) - m).toNat = n + 1 := by dsimp [n]; omega
  have h0 := aux_transport_potential_sum (fun i => om i w) N m hmN
  have h1 := aux_transport_potential_sum (fun i => om i w) N (m + 1) hsN
  rw [hdiff] at h0
  have hsum : (∑ i ∈ Finset.range (n + 1 + 1), om (-(Int.ofNat i) - m) w) =
      om (-m) w + ∑ i ∈ Finset.range (n + 1), om (-(Int.ofNat i) - (m + 1)) w := by
    rw [Finset.sum_range_succ', add_comm]
    have hz : -(Int.ofNat 0) - m = -m := by norm_num [Int.ofNat_eq_natCast]
    rw [hz]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
    ring
  rw [hsum] at h0
  change (∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat i)) w) =
    (∑ i ∈ Finset.range (n + 1), om (-(Int.ofNat i) - (m + 1)) w) +
      aux_transport_retained (m + 1) w om at h1
  change (∑ i ∈ Finset.range (N + 1), om (-(Int.ofNat i)) w) =
    (om (-m) w + ∑ i ∈ Finset.range (n + 1), om (-(Int.ofNat i) - (m + 1)) w) +
      aux_transport_retained m w om at h0
  linarith

/-- The two existing normalizations are precisely the scalar in the
one-step affine potential identity. -/
theorem affine_normalization_eq {d : ℕ}
    (M M' : SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (m : ℤ) (w : SpatialCoordinates d) (om : BilateralField d)
    (N : ℕ) (hN : m + 1 ≤ (N : ℤ)) :
    aux_transport_reference M H N m w om *
        aux_prop_growth_macro_energy_shiftC M M' 1 ((N : ℤ) - (m + 1)).toNat
          (aux_transport_S m w om) =
      (SubdiffusiveProcess.CoarseGrainingVocab.ahom M' ((N : ℤ) - (m + 1)).toNat /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) *
        Real.exp (H om w + aux_transport_retained (m + 1) w om -
          ((m + 1 : ℤ) : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ((N : ℤ) - (m + 1)).toNat := ⟨_, rfl⟩
  have hdiff : ((N : ℤ) - m).toNat = n + 1 := by rw [hn]; omega
  have hcast : (n : ℝ) - N = -((m + 1 : ℤ) : ℝ) := by
    have hh : (n : ℤ) + (m + 1) = N := by rw [hn]; omega
    exact_mod_cast (by omega : (n : ℤ) - N = -(m + 1))
  have hanchor : SubdiffusiveProcess.MacroAllCube.lowAnchor 1 (aux_transport_S m w om) = om (-m) w := by
    simp only [SubdiffusiveProcess.MacroAllCube.lowAnchor, Finset.sum_range_one]
    rw [aux_transport_S_apply]
    simp only [smul_zero, add_zero]
    norm_num [Int.ofNat_eq_natCast]
  unfold aux_transport_reference aux_transport_kappa aux_prop_growth_macro_energy_shiftC
  rw [hdiff, ← hn, hanchor, retained_add_one]
  simp only [Nat.cast_add, Nat.cast_one, one_mul]
  have ha := (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M (n + 1)).ne'
  have hb := (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M N).ne'
  have he := (Real.exp_pos (((N : ℝ) + 1) * SubdiffusiveProcess.Model.tauSq M.P)).ne'
  calc
    _ = (SubdiffusiveProcess.CoarseGrainingVocab.ahom M' n / SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) *
        (Real.exp (((n : ℝ) + 1 + 1) * SubdiffusiveProcess.Model.tauSq M.P) /
          Real.exp (((N : ℝ) + 1) * SubdiffusiveProcess.Model.tauSq M.P) *
          Real.exp (H om w + aux_transport_retained m w om) *
          Real.exp (om (-m) w - SubdiffusiveProcess.Model.tauSq M.P)) := by
      field_simp
    _ = _ := by
      rw [← Real.exp_sub, ← Real.exp_add, ← Real.exp_add]
      congr 2
      have hh := congrArg (fun a : ℝ => a * SubdiffusiveProcess.Model.tauSq M.P) hcast
      nlinarith [hh]

/-- A potential identity gives the normalized coefficient identity, including
both ultraviolet normalizations and the exact integer disorder offset. -/
theorem cutoffCoefficient_affine_of_potential {d : ℕ}
    (M M' : SubdiffusiveProcess.Model.GMCModel d)
    (F F' : BilateralField d → C(SpatialCoordinates d, ℝ))
    (om eta : BilateralField d) (N : ℕ) (s : ℤ) (hN : s ≤ (N : ℤ))
    (x y : SpatialCoordinates d) (b : ℝ)
    (htau : SubdiffusiveProcess.Model.tauSq M'.P = SubdiffusiveProcess.Model.tauSq M.P)
    (hpot : cutoffPotential F om N y =
      cutoffPotential F' eta ((N : ℤ) - s).toNat x + b) :
    cutoffCoefficient M F om N y =
      ((SubdiffusiveProcess.CoarseGrainingVocab.ahom M' ((N : ℤ) - s).toNat /
        SubdiffusiveProcess.CoarseGrainingVocab.ahom M N) * Real.exp (b - (s : ℝ) * SubdiffusiveProcess.Model.tauSq M.P)) *
      cutoffCoefficient M' F' eta ((N : ℤ) - s).toNat x := by
  have hn : (((N : ℤ) - s).toNat : ℝ) = (N : ℝ) - (s : ℝ) := by
    have hh : (((N : ℤ) - s).toNat : ℤ) = (N : ℤ) - s := Int.toNat_of_nonneg (by omega)
    exact_mod_cast hh
  unfold cutoffCoefficient
  rw [hpot, htau]
  have hp := (SubdiffusiveProcess.CoarseGrainingVocab.ahom_pos M' ((N : ℤ) - s).toNat).ne'
  rw [div_eq_mul_inv]
  have hexp : Real.exp (b - (s : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) *
      Real.exp (cutoffPotential F' eta ((N : ℤ) - s).toNat x -
        ((((N : ℤ) - s).toNat : ℝ) + 1) * SubdiffusiveProcess.Model.tauSq M.P) =
      Real.exp (cutoffPotential F' eta ((N : ℤ) - s).toNat x + b -
        ((N : ℝ) + 1) * SubdiffusiveProcess.Model.tauSq M.P) := by
    rw [← Real.exp_add, hn]
    congr 1
    ring
  calc _ = (SubdiffusiveProcess.CoarseGrainingVocab.ahom M N)⁻¹ *
      (Real.exp (b - (s : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) *
        Real.exp (cutoffPotential F' eta ((N : ℤ) - s).toNat x -
          ((((N : ℤ) - s).toNat : ℝ) + 1) * SubdiffusiveProcess.Model.tauSq M.P)) := by rw [hexp]
    _ = _ := by field_simp

/-- The common affine scalar, with its only family-dependent factor being
an anchor value or one of the finitely many exceptional anchor sums. -/
def familyAffineScalar {d : ℕ}
    (M M' : SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (m : ℤ) (w : SpatialCoordinates d) (idx : Option ℕ)
    (N : ℕ) (om : BilateralField d) : ℝ :=
  (aux_transport_reference M 0 N m w om *
    aux_prop_growth_macro_energy_shiftC M M' 1 ((N : ℤ) - (m + 1)).toNat
      (aux_transport_S m w om)) * Real.exp
    (idx.elim (H om w) (fun L =>
      if 0 ≤ (L : ℤ) + (m + 1) then infraredPartialSum om L w
      else -(∑ i ∈ Finset.range L, om (Int.ofNat (i + 1)) 0) -
        aux_transport_retained (m + 1) w om))

theorem familyAffineScalar_pos {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M M' : SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (m : ℤ) (w : SpatialCoordinates d) (idx : Option ℕ)
    (N : ℕ) (om : BilateralField d) : 0 < familyAffineScalar M M' H m w idx N om :=
  mul_pos (mul_pos (aux_transport_reference_pos M 0 N m w om)
    (aux_prop_growth_macro_energy_shiftC_pos M M' 1 _ _)) (Real.exp_pos _)

/-- Exact coefficient covariance for every finite positive-layer infrared
convention. The signed convention in the target is chosen by the shifted
upper index; the coefficient itself remains the actual source coefficient. -/
theorem cutoffCoefficient_family_affine {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M M' : SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (m : ℤ) (w x : SpatialCoordinates d) (r : ℝ)
    (om : BilateralField d) (N L : ℕ) (hN : m + 1 ≤ (N : ℤ))
    (htau : SubdiffusiveProcess.Model.tauSq M'.P = SubdiffusiveProcess.Model.tauSq M.P) :
    cutoffCoefficient M (fun eta => infraredPartialSum eta L) om N (w + r • x) =
      familyAffineScalar M M' H m w (some L) N om *
        cutoffCoefficient M' (signedInfrared ((L : ℤ) + (m + 1)))
          (infraredAffineShift (m + 1) w r om) ((N : ℤ) - (m + 1)).toNat x := by
  have hb := affine_normalization_eq M M' 0 m w om N hN
  simp only [Pi.zero_apply, ContinuousMap.zero_apply, zero_add] at hb
  by_cases hL : 0 ≤ (L : ℤ) + (m + 1)
  · have hp := cutoffPotential_affineShift_positive (m + 1) w x r om N L hN hL
    have hc := cutoffCoefficient_affine_of_potential M M'
      (fun eta => infraredPartialSum eta L) (signedInfrared ((L : ℤ) + (m + 1)))
      om (infraredAffineShift (m + 1) w r om) N (m + 1) hN x (w + r • x)
      (infraredPartialSum om L w + aux_transport_retained (m + 1) w om) htau (by simpa only [add_assoc] using hp)
    rw [hc]
    congr 1
    simp only [familyAffineScalar, Option.elim_some, ite_eq_left hL, hb]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring
  · have hp := cutoffPotential_affineShift_negative (m + 1) w x r om N L hN (lt_of_not_ge hL)
    have hc := cutoffCoefficient_affine_of_potential M M'
      (fun eta => infraredPartialSum eta L) (signedInfrared ((L : ℤ) + (m + 1)))
      om (infraredAffineShift (m + 1) w r om) N (m + 1) hN x (w + r • x)
      (-(∑ i ∈ Finset.range L, om (Int.ofNat (i + 1)) 0)) htau (by simpa only [sub_eq_add_neg] using hp)
    rw [hc]
    congr 1
    simp only [familyAffineScalar, Option.elim_some, ite_eq_right hL, hb]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring

/-- Exponential moments of a finite positive-layer anchor envelope.
The finite sum is used only for exceptional negative shifted indices. -/
theorem positive_anchor_envelope_integrable {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Model.GMCModel d) (q : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    Integrable (fun om => Real.exp (c * ∑ i ∈ Finset.range q, |om (Int.ofNat (i + 1)) 0|))
      (chaosSampleLaw M).toMeasure := by
  by_cases hq : q = 0
  · subst q
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, Real.exp_zero]
    exact integrable_const 1
  · have hq0 : 0 < q := Nat.pos_of_ne_zero hq
    have hi : Integrable (fun om : BilateralField d =>
        ∑ i ∈ Finset.range q, Real.exp (c * q * |om (Int.ofNat (i + 1)) 0|))
        (chaosSampleLaw M).toMeasure := by
      apply integrable_finsetSum
      intro i _
      exact aux_prop_growth_macro_energy_integrable_exp_mul_abs_layer M _ _ (by positivity)
    have hm : Measurable (fun om : BilateralField d =>
        Real.exp (c * ∑ i ∈ Finset.range q, |om (Int.ofNat (i + 1)) 0|)) := by
      have hs : Measurable (fun om : BilateralField d =>
          ∑ i ∈ Finset.range q, |om (Int.ofNat (i + 1)) 0|) :=
        Finset.measurable_sum _ (fun i _ =>
          (((continuous_eval_const (0 : SpatialCoordinates d)).measurable.comp
            (measurable_pi_apply (Int.ofNat (i + 1)))).abs))
      exact (hs.const_mul c).exp
    refine hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun om => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact aux_prop_growth_macro_energy_exp_mul_sum_le
      (fun i => |om (Int.ofNat (i + 1)) 0|) c hc q hq0

theorem familyAffineScalar_none_eq {d : ℕ}
    (M M' : SubdiffusiveProcess.Model.GMCModel d)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ))
    (m : ℤ) (w : SpatialCoordinates d) (N : ℕ) (om : BilateralField d) :
    familyAffineScalar M M' H m w none N om =
      aux_transport_reference M H N m w om *
        aux_prop_growth_macro_energy_shiftC M M' 1 ((N : ℤ) - (m + 1)).toNat
          (aux_transport_S m w om) := by
  unfold familyAffineScalar aux_transport_reference
  simp only [Option.elim_none, Pi.zero_apply, ContinuousMap.zero_apply, zero_add]
  rw [Real.exp_add]
  ring

/-- The characterized limit obeys the same normalization as the finite
family. The two sample-law changes are the existing genuine field shifts. -/
theorem cutoffCoefficient_limit_affine {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M M' : SubdiffusiveProcess.Model.GMCModel d)
    (H H' : BilateralField d → C(SpatialCoordinates d, ℝ))
    (hIR : InfraredCharacterization M H) (hIR' : InfraredCharacterization M' H')
    (htau : SubdiffusiveProcess.Model.tauSq M'.P = SubdiffusiveProcess.Model.tauSq M.P)
    (m : ℤ) (w : SpatialCoordinates d) (r rho : ℝ)
    (hreq : r = (3 : ℝ) ^ (-m) * rho)
    (hR : MeasurePreserving (SubdiffusiveProcess.MacroAllCube.residualShift (d := d) rho 1)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure) :
    ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, m + 1 ≤ (N : ℤ) →
      ∀ x : SpatialCoordinates d,
        cutoffCoefficient M H om N (w + r • x) =
          familyAffineScalar M M' H m w none N om *
            cutoffCoefficient M' H' (infraredAffineShift (m + 1) w r om)
              ((N : ℤ) - (m + 1)).toNat x := by
  let S := aux_transport_S m w
  have hS : MeasurePreserving S (chaosSampleLaw M).toMeasure (chaosSampleLaw M).toMeasure :=
    aux_transport_S_measurePreserving M m w
  have hfirst : ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ N : ℕ, m ≤ (N : ℤ) →
      ∀ x : SpatialCoordinates d,
        cutoffCoefficient M H om N (w + (3 : ℝ) ^ (-m) • x) =
          aux_transport_reference M H N m w om *
            cutoffCoefficient M H (S om) ((N : ℤ) - m).toNat x := by
    apply ae_all_iff.mpr
    intro N
    apply ae_all_iff.mpr
    intro hN
    exact aux_transport_coefficient M m w hIR N hN
  have hsecond := hS.quasiMeasurePreserving.ae
    (aux_prop_growth_macro_energy_coeff_identity M M' htau H H' hIR hIR' rho 1 hR)
  filter_upwards [hfirst, hsecond] with om hf hs N hN x
  have hmN : m ≤ (N : ℤ) := by omega
  have hI : ((N : ℤ) - (m + 1)).toNat + 1 = ((N : ℤ) - m).toNat := by omega
  have hpoint : w + r • x = w + (3 : ℝ) ^ (-m) • (rho • x) := by
    rw [smul_smul, hreq]
  rw [hpoint, hf N hmN (rho • x), ← hI,
    hs.2 ((N : ℤ) - (m + 1)).toNat x, familyAffineScalar_none_eq]
  rw [infraredAffineShift_eq_residualShift m w r rho hreq]
  exact (mul_assoc _ _ _).symm

/-- A single cutoff-independent inverse-scalar envelope serves the limit,
all positive truncations and every exceptional signed affine branch. -/
theorem familyAffineScalar_inverse_envelope {d : ℕ} (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (M : SubdiffusiveProcess.Model.GMCModel d) {rho : ℝ}
    (hs1 : 1 ≤ rho * (3 : ℝ)) (hs3 : rho * (3 : ℝ) ≤ 3)
    (hdelta : M.delta ≤ (2 * SubdiffusiveProcess.ResidualModel.residualDisorderFactor d)⁻¹)
    (H : BilateralField d → C(SpatialCoordinates d, ℝ)) (hH : InfraredCharacterization M H)
    (m : ℤ) (w : SpatialCoordinates d) :
    ∃ B : BilateralField d → ℝ,
      (∀ om, 0 ≤ B om) ∧
      (∀ p : ℝ, 1 ≤ p → MemLp B (ENNReal.ofReal p) (chaosSampleLaw M).toMeasure) ∧
      ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ idx : Option ℕ, ∀ N : ℕ,
        m + 1 ≤ (N : ℤ) →
          (familyAffineScalar M (SubdiffusiveProcess.ResidualModel.residualModel M hs1 hs3 hdelta)
            H m w idx N om)⁻¹ ≤ B om := by
  classical
  let M' := SubdiffusiveProcess.ResidualModel.residualModel M hs1 hs3 hdelta
  let μ := (chaosSampleLaw M).toMeasure
  let sh := aux_transport_S m w
  have hsh : MeasurePreserving sh μ μ := aux_transport_S_measurePreserving M m w
  obtain ⟨A, hA, hEnv⟩ := infrared_family_envelope hd w 1 one_pos
  obtain ⟨S, hSm, hS0, hSae, -, hSE⟩ := hEnv M H hH
  let q : ℕ := (-(m + 1)).toNat
  let anchors : BilateralField d → ℝ := fun om =>
    ∑ i ∈ Finset.range q, |om (Int.ofNat (i + 1)) 0|
  have hAm : Measurable anchors := by fun_prop
  let Rm : BilateralField d → ℝ := fun om => aux_transport_retained m w om
  let Rs : BilateralField d → ℝ := fun om => aux_transport_retained (m + 1) w om
  have hRm : Measurable Rm := aux_fscc_holNeuH_retained_measurable m w
  have hRs : Measurable Rs := aux_fscc_holNeuH_retained_measurable (m + 1) w
  let B0 : BilateralField d → ℝ := fun om =>
    Real.exp ((m.natAbs : ℝ) * SubdiffusiveProcess.Model.tauSq M.P) * Real.exp (-Rm om) *
      aux_prop_growth_macro_energy_env M 1 (sh om)
  let B : BilateralField d → ℝ := fun om => B0 om *
    (Real.exp (S om) + Real.exp (Rs om + anchors om))
  have hB00 : ∀ om, 0 ≤ B0 om := fun om =>
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (zero_le_one.trans (aux_prop_growth_macro_energy_one_le_env M 1 (sh om)))
  have hB0Lp : ∀ p : ℝ, 1 ≤ p → MemLp B0 (ENNReal.ofReal p) μ := by
    intro p hp
    have hR : MemLp (fun om => Real.exp (-Rm om)) (ENNReal.ofReal (2 * p)) μ :=
      exponential_memLp μ (fun om => -Rm om) hRm.neg (2 * p) (by linarith)
        (by simpa only [mul_neg, neg_mul] using aux_lem_as_regularity_nc_retained_exp M m w (-(2 * p)))
    have hE : MemLp (fun om => aux_prop_growth_macro_energy_env M 1 (sh om))
        (ENNReal.ofReal (2 * p)) μ := by
      have hh := (aux_prop_growth_macro_energy_memLp_env_pow M 1 1 (2 * p) (by linarith)).comp_measurePreserving hsh
      simpa only [pow_one, Function.comp_def] using hh
    have := aux_aux_macro_moment_bank_holderTriple p
    have hh := MemLp.fun_mul (p := ENNReal.ofReal (2 * p)) (q := ENNReal.ofReal (2 * p))
      (r := ENNReal.ofReal p) (hR.const_mul (Real.exp ((m.natAbs : ℝ) * SubdiffusiveProcess.Model.tauSq M.P))) hE
    exact hh
  have hBLp : ∀ p : ℝ, 1 ≤ p → MemLp B (ENNReal.ofReal p) μ := by
    intro p hp
    have hS : MemLp (fun om => Real.exp (S om)) (ENNReal.ofReal (2 * p)) μ :=
      exponential_memLp μ S hSm (2 * p) (by linarith) (hSE (2 * p) (by linarith)).1
    have hRA : MemLp (fun om => Real.exp (Rs om + anchors om)) (ENNReal.ofReal (2 * p)) μ :=
      exponential_memLp μ (fun om => Rs om + anchors om) (hRs.add hAm) (2 * p) (by linarith)
        (aux_lem_as_regularity_nc_exp_add_integrable μ Rs anchors hRs hAm (2 * p)
          (aux_lem_as_regularity_nc_retained_exp M (m + 1) w _)
          (positive_anchor_envelope_integrable M q _ (by linarith)))
    have := aux_aux_macro_moment_bank_holderTriple p
    exact MemLp.fun_mul (p := ENNReal.ofReal (2 * p)) (q := ENNReal.ofReal (2 * p))
      (r := ENNReal.ofReal p) (hB0Lp (2 * p) (by linarith)) (hS.add hRA)
  refine ⟨B, fun om => mul_nonneg (hB00 om) (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le),
    hBLp, ?_⟩
  filter_upwards [hSae] with om hSom
  intro idx N hN
  have hmN : m ≤ (N : ℤ) := by omega
  let c0 : ℝ := aux_transport_reference M 0 N m w om *
    aux_prop_growth_macro_energy_shiftC M M' 1 ((N : ℤ) - (m + 1)).toNat (sh om)
  have hc0 : 0 < c0 := mul_pos (aux_transport_reference_pos M 0 N m w om)
    (aux_prop_growth_macro_energy_shiftC_pos M M' 1 _ _)
  have hc0B : c0⁻¹ ≤ B0 om := by
    have hRef := aux_lem_as_regularity_nc_reference_uniform M 0 m w om N hmN
    have hShift := (aux_prop_growth_macro_energy_shiftC_bounds M hs1 hs3 hdelta
      1 ((N : ℤ) - (m + 1)).toNat (sh om)).2
    dsimp only [c0]
    rw [mul_inv]
    have hh := mul_le_mul hRef hShift (inv_pos.mpr
      (aux_prop_growth_macro_energy_shiftC_pos M M' 1 _ _)).le
      (by positivity)
    simpa only [Pi.zero_apply, ContinuousMap.zero_apply, zero_add] using hh
  have hval : ∀ F : C(SpatialCoordinates d, ℝ), ‖restrictC (closedCube w 1 one_pos) F‖ ≤ S om →
      -F w ≤ S om := by
    intro F hF
    have hw : w ∈ (closedCube w 1 one_pos : Set (SpatialCoordinates d)) := by
      change dist w w ≤ 1 / 2
      norm_num
    have hv := ContinuousMap.norm_coe_le_norm (restrictC (closedCube w 1 one_pos) F) ⟨w, hw⟩
    change ‖F w‖ ≤ _ at hv
    rw [Real.norm_eq_abs] at hv
    exact (neg_le_abs _).trans (hv.trans hF)
  have hpos : ∀ b : ℝ, -b ≤ S om → (c0 * Real.exp b)⁻¹ ≤ B om := by
    intro b hb
    rw [mul_inv, ← Real.exp_neg]
    calc _ ≤ B0 om * Real.exp (S om) :=
        mul_le_mul hc0B (Real.exp_le_exp.mpr hb) (Real.exp_pos _).le (hB00 om)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.exp_pos _).le) (hB00 om)
  cases idx with
  | none => exact hpos (H om w) (hval _ hSom.1.1)
  | some L =>
    by_cases hL : 0 ≤ (L : ℤ) + (m + 1)
    · simpa only [familyAffineScalar, Option.elim_some, ite_eq_left hL] using
        hpos (infraredPartialSum om L w) (hval _ (hSom.2 L).1)
    · have hLq : L ≤ q := by dsimp [q]; omega
      have hanchor : ∑ i ∈ Finset.range L, om (Int.ofNat (i + 1)) 0 ≤ anchors om := by
        calc _ ≤ ∑ i ∈ Finset.range L, |om (Int.ofNat (i + 1)) 0| :=
            Finset.sum_le_sum (fun i _ => le_abs_self _)
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hLq)
            (fun i _ _ => abs_nonneg _)
      simp only [familyAffineScalar, Option.elim_some, ite_eq_right hL]
      change (c0 * Real.exp (-(∑ i ∈ Finset.range L, om (Int.ofNat (i + 1)) 0) - Rs om))⁻¹ ≤ B om
      rw [mul_inv, ← Real.exp_neg]
      calc _ ≤ B0 om * Real.exp (Rs om + anchors om) :=
          mul_le_mul hc0B (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (hB00 om)
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.exp_pos _).le) (hB00 om)

/-- Common family bank in the entire nonnegative affine cutoff range on
an arbitrary fixed cube. The genuine residual model and all its input
witnesses are constructed inside the proof. -/
theorem infrared_family_affine_high
    (d : ℕ) (hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (E : in_J d) (P : in_poincare d hd E) (X : in_extension d hd E)
    (W : SmallPerturbationInput d)
    (D : @deterministic_good_scale_input d
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) hd)⟩)
    (Cp : CampanatoInput d) (t alpha : ℝ) (k : ℕ) (ps : Fin k → ℝ)
    (ht1 : (d : ℝ) - 1 < t) (htd : t < d)
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (hps : ∀ i, 1 ≤ ps i) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ (M : SubdiffusiveProcess.Model.GMCModel d) (_Rm : in_responses d M)
        (Sreg : in_6_16 d M) (_It : in_iteration d M E Sreg)
        (H : BilateralField d → C(SpatialCoordinates d, ℝ)),
      InfraredCharacterization M H → M.delta ≤ delta0 →
      ∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
        (m : ℤ) (rho : ℝ), 1 ≤ rho * (3 : ℝ) → rho * (3 : ℝ) ≤ 3 →
        r = (3 : ℝ) ^ (-m) * rho →
      ∃ (K : ℕ → BilateralField d → ℝ) (Cb : Fin k → ℝ),
        (∀ N om, 0 ≤ K N om) ∧
        (∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure) ∧
        (∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
          ENNReal.ofReal (Cb i)) ∧
        ∀ᵐ om ∂(chaosSampleLaw M).toMeasure, ∀ idx : Option ℕ, ∀ N : ℕ,
          m + 1 ≤ (N : ℤ) →
          aux_lem_as_regularity_nc_estimate z r hr
            (cutoffPositiveCoefficient M (infraredFamily H idx) om N z hr) t alpha (K N om) := by
  classical
  have hps2 : ∀ i : Fin k, 1 ≤ 2 * ps i := fun i => by linarith [hps i]
  obtain ⟨du, hdu, hunit⟩ := infrared_extended_neumann_source d hd E P X W D Cp t alpha
    k (fun i => 2 * ps i) ht1 htd ha0 ha1 hps2
  have hRes := SubdiffusiveProcess.ResidualModel.residualDisorderFactor_pos d
  refine ⟨min (du / SubdiffusiveProcess.ResidualModel.residualDisorderFactor d)
    (2 * SubdiffusiveProcess.ResidualModel.residualDisorderFactor d)⁻¹,
    lt_min (div_pos hdu hRes) (by positivity), ?_⟩
  intro M Rm Sreg It H hH hdelta z r hr m rho hs1 hs3 hreq
  have hdRes := hdelta.trans (min_le_right _ _)
  let M' := SubdiffusiveProcess.ResidualModel.residualModel M hs1 hs3 hdRes
  have hdU : M'.delta ≤ du := by
    rw [SubdiffusiveProcess.ResidualModel.residualModel_delta]
    simpa only [mul_comm] using (le_div_iff₀ hRes).mp (hdelta.trans (min_le_left _ _))
  obtain ⟨H', hH'⟩ := exists_infraredCharacterization hd M'
  let Rm' := Classical.choice (aux_lem_as_regularity_nonempty_responses d hd M')
  obtain ⟨Ku, Cu, hKu, hKuL, hKuB, hKuAE⟩ := hunit M' Rm'
    (aux_prop_growth_macro_energy_nativeSreg M') (aux_lem_as_regularity_native_iteration d hd M' E)
    H' hH' hdU (-(m + 1)).toNat
  let w : SpatialCoordinates d := fun i => z i - r * (1 / 2 : ℝ)
  let T := infraredAffineShift (m + 1) w r
  let I : ℕ → ℕ := fun N => ((N : ℤ) - (m + 1)).toNat
  have hT : MeasurePreserving T (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure :=
    infraredAffineShift_measurePreserving M m w r rho hs1 hs3 hdRes hreq
  obtain ⟨B, hB0, hBL, hBAE⟩ := familyAffineScalar_inverse_envelope hd M hs1 hs3 hdRes H hH m w
  let A : ℝ := aux_lem_as_regularity_nc_factor d r t alpha
  have hA : 0 ≤ A := by dsimp [A, aux_lem_as_regularity_nc_factor]; positivity
  let K : ℕ → BilateralField d → ℝ := fun N om => A * (Ku (I N) (T om) * B om)
  let CB : Fin k → ℝ := fun i =>
    (eLpNorm B (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure).toReal
  have hBm : ∀ i, MemLp B (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure :=
    fun i => hBL _ (hps2 i)
  have hBnorm : ∀ i, eLpNorm B (ENNReal.ofReal (2 * ps i)) (chaosSampleLaw M).toMeasure =
      ENNReal.ofReal (CB i) := fun i => (ENNReal.ofReal_toReal (hBm i).eLpNorm_ne_top).symm
  have hKL : ∀ i N, MemLp (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure := by
    intro i N
    have := aux_aux_macro_moment_bank_holderTriple (ps i)
    exact (MemLp.fun_mul (p := ENNReal.ofReal (2 * ps i)) (q := ENNReal.ofReal (2 * ps i))
      (r := ENNReal.ofReal (ps i)) ((hKuL i (I N)).comp_measurePreserving hT) (hBm i)).const_mul A
  have hKB : ∀ i N, eLpNorm (K N) (ENNReal.ofReal (ps i)) (chaosSampleLaw M).toMeasure ≤
      ENNReal.ofReal (A * (max (Cu i) 0 * CB i)) := by
    intro i N
    have hU := (hKuL i (I N)).comp_measurePreserving hT
    have hUb : eLpNorm (fun om => Ku (I N) (T om)) (ENNReal.ofReal (2 * ps i))
        (chaosSampleLaw M).toMeasure ≤ ENNReal.ofReal (max (Cu i) 0) := by
      have heq := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal (2 * ps i))
        (hKuL i (I N)).aestronglyMeasurable hT
      change eLpNorm ((Ku (I N)) ∘ T) _ _ ≤ _
      rw [heq]
      exact (hKuB i (I N)).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    have hprod := aux_rem_resolved_microscopic_product_lq_bound (chaosSampleLaw M).toMeasure
      (ps i) (2 * ps i) (by linarith [hps i]) le_rfl
      (fun om => Ku (I N) (T om)) B hU (hBm i)
    change eLpNorm (A • (fun om => Ku (I N) (T om) * B om)) _ _ ≤ _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hA]
    calc _ ≤ ENNReal.ofReal A * (ENNReal.ofReal (max (Cu i) 0) * ENNReal.ofReal (CB i)) :=
        mul_le_mul_right (hprod.trans (mul_le_mul' hUb (hBnorm i).le)) _
      _ = _ := by rw [← ENNReal.ofReal_mul (le_max_right _ _), ← ENNReal.ofReal_mul hA]
  refine ⟨K, fun i => A * (max (Cu i) 0 * CB i),
    fun N om => mul_nonneg hA (mul_nonneg (hKu (I N) (T om)) (hB0 om)), hKL, hKB, ?_⟩
  have hR : MeasurePreserving (SubdiffusiveProcess.MacroAllCube.residualShift (d := d) rho 1)
      (chaosSampleLaw M).toMeasure (chaosSampleLaw M').toMeasure := by
    simpa only [pow_one, M'] using SubdiffusiveProcess.ResidualModel.measurePreserving_residualModel M rho 1
      (by simpa only [pow_one] using hs1) (by simpa only [pow_one] using hs3) hdRes
  have htau : SubdiffusiveProcess.Model.tauSq M'.P = SubdiffusiveProcess.Model.tauSq M.P :=
    SubdiffusiveProcess.ResidualModel.residualModel_tauSq M hs1 hs3 hdRes
  have hfull := cutoffCoefficient_limit_affine M M' H H' hH hH' htau m w r rho hreq hR
  have ht0 : 0 ≤ t := by
    have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  filter_upwards [hfull, hT.quasiMeasurePreserving.ae hKuAE, hBAE] with om hfull hu hb
  intro idx N hN
  let F' : BilateralField d → C(SpatialCoordinates d, ℝ) :=
    idx.elim H' (fun L => signedInfrared ((L : ℤ) + (m + 1)))
  have hest : aux_lem_as_regularity_nc_estimate (fun _ => (1 / 2 : ℝ)) 1 one_pos
      (cutoffPositiveCoefficient M' F' (T om) (I N) (fun _ => (1 / 2 : ℝ)) one_pos)
      t alpha (Ku (I N) (T om)) := by
    cases idx with
    | none => exact hu.1 (I N)
    | some L => exact hu.2 ((L : ℤ) + (m + 1)) (I N) (by omega) (by dsimp [I]; omega)
  have hpoint : ∀ x : SpatialCoordinates d,
      cutoffCoefficient M (infraredFamily H idx) om N
          (cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x) =
        familyAffineScalar M M' H m w idx N om * cutoffCoefficient M' F' (T om) (I N) x := by
    intro x
    have hdil : cubeDilation z (fun _ : Fin d => (1 / 2 : ℝ)) r x = w + r • x := by
      funext i
      simp only [cubeDilation_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      dsimp [w]
      ring
    rw [hdil]
    cases idx with
    | none => exact hfull N hN x
    | some L => exact cutoffCoefficient_family_affine M M' H m w x r om N L hN htau
  obtain ⟨a1, ha1, -, hNeu⟩ := lem_as_regularity_affine_transport d M (infraredFamily H idx) om N z r hr
  have hc := familyAffineScalar_pos M M' H m w idx N om
  have hcoef : a1 = scalePositiveCoefficient (familyAffineScalar M M' H m w idx N om) hc
      (cutoffPositiveCoefficient M' F' (T om) (I N) (fun _ => (1 / 2 : ℝ)) one_pos) := by
    have hq := dilation_quasi_measure_preserving d z (fun _ : Fin d => (1 / 2 : ℝ)) r hr one_pos
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [ha1, hq.ae (aux_fscc_holNeuH_cutoffPos_val M (infraredFamily H idx) om N z hr),
      aux_fscc_holNeuH_cutoffPos_val M' F' (T om) (I N) (fun _ => (1 / 2 : ℝ)) one_pos,
      scalePositiveCoefficient_coeFn _ hc
        (cutoffPositiveCoefficient M' F' (T om) (I N) (fun _ => (1 / 2 : ℝ)) one_pos)]
      with x hx1 hx2 hx3 hx4
    erw [hx1, hx2, hpoint x, hx4, hx3]
  have hraw : aux_lem_as_regularity_nc_estimate z r hr
      (cutoffPositiveCoefficient M (infraredFamily H idx) om N z hr) t alpha
      (A * Ku (I N) (T om) / familyAffineScalar M M' H m w idx N om) := by
    intro F Kf hKf hFm hFb hFz v hsol
    obtain ⟨F1, v1, -, hF1m, hF1b, hF1z, hsol1, hv1, -, henergy⟩ :=
      hNeu F Kf hKf hFm hFb hFz v hsol
    exact aux_lem_as_regularity_nc_transfer_data z (fun _ : Fin d => (1 / 2 : ℝ)) r hr
      t alpha (Ku (I N) (T om)) _ ht0 ha0.le (hKu _ _) hc
      _ a1 _ hcoef hest v v1 F1 Kf hKf hF1m hF1b hF1z hsol1 hv1 henergy
  apply aux_lem_as_regularity_nc_estimate_mono _ hraw
  rw [div_eq_mul_inv]
  calc _ ≤ A * Ku (I N) (T om) * B om :=
      mul_le_mul_of_nonneg_left (hb idx N hN) (mul_nonneg hA (hKu _ _))
    _ = K N om := by dsimp [K]; ring

end SubdiffusiveProcess.AuditExports
