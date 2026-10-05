module

public import SubdiffusiveProcess.Paper.Support.Cor32ExtraChainSupport

@[expose] public section





open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Matrix
open SubdiffusiveProcess _root_.SubdiffusiveProcess.ResponseMoments
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SubdiffusiveProcess.Paper
noncomputable section
theorem aux_cor_32_of_base_and_concentration
    (d : ℕ) (_hd : 2 ≤ d)
    (H1 : ℕ) (hH1 : 1 ≤ H1)
    (eps : ℝ) (heps : 0 < eps)
    (theta : ℝ) (htheta : 0 < theta) (htheta1 : theta < 1)
    (C0 : ℝ) (_hC0 : 1 ≤ C0)
    (c0 : ℝ) (hc0 : 0 < c0)
    (p : ℝ) (hp : 0 < p)
    (Cp : ℝ) (hCp : 0 < Cp)
    (aexp : ℝ) (haexp : 0 < aexp)
    (hpRate : 2 * (2 * Real.log 2 + 1 + (48 / theta) *
        (((H1 * d : ℕ) : ℝ) * Real.log 3 + Real.log 2 + 2)) ≤ p * aexp * Real.log 3) :
    ∃ delta0 epsPrime : ℝ, 0 < delta0 ∧ 0 < epsPrime ∧
      ∀ [MeasurableSpace C(SpatialCoordinates d, ℝ)]
        [BorelSpace C(SpatialCoordinates d, ℝ)]
        (model : _root_.SubdiffusiveProcess.Model.GMCModel d),
        model.delta ≤ delta0 →
      ∀ (H : BilateralField d → C(SpatialCoordinates d, ℝ))
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (field : Ω → BilateralField d)
        (z : ℕ → SpatialCoordinates d) (r : ℕ → ℝ)
        (hr : ∀ i, 0 < r i)
        (Sspace : (i : ℕ) → ResponseSpace
          (centeredCube (z i) (r i) (hr i)))
        (GN : (i : ℕ) → ℕ → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (GE GF : (i : ℕ) → Ω →
          DomainL2 (centeredCube (z i) (r i) (hr i)) →L[ℝ]
            DomainL2 (centeredCube (z i) (r i) (hr i)))
        (NE NF : ℕ → ℕ)
        (_hJoint : in_joint_extracted_candidates d model H Ω P field z r hr
          Sspace GN GE GF NE NF)
        (m M : ℝ) (_hm : C0⁻¹ ≤ m) (_hmM : m ≤ M) (_hM : M ≤ C0)
        (_horder : ∀ᵐ omega ∂P, ∀ i,
          limitFormDomain (GE i omega) = limitFormDomain (GF i omega) ∧
            ∀ u : DomainL2 (centeredCube (z i) (r i) (hr i)),
              u ∈ limitFormDomain (GE i omega) →
                m * (limitFormEnergy (GE i omega) u).toReal ≤
                    (limitFormEnergy (GF i omega) u).toReal ∧
                  (limitFormEnergy (GF i omega) u).toReal ≤
                    M * (limitFormEnergy (GE i omega) u).toReal)
        (rootCenter : SpatialCoordinates d)
        (idx : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → ℕ)
        (_hidx : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
          z (idx n w) =
              descendantCenter (subdivisionHalfWidth H1) rootCenter 1 n w ∧
            r (idx n w) = descendantSide (subdivisionHalfWidth H1) n 1),
      let nodeCenter : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) →
          SpatialCoordinates d :=
        fun n w => descendantCenter (subdivisionHalfWidth H1) rootCenter 1 n w
      let nodeSide : ℕ → ℝ := fun n => descendantSide (subdivisionHalfWidth H1) n 1
      let q : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) →
          Opens (SpatialCoordinates d) :=
        fun n w => centeredCube (nodeCenter n w) (nodeSide n)
          (descendantSide_pos (subdivisionHalfWidth H1) n one_pos)
      ∀ (hPnode : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
          ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (q n w),
            ‖(u : SobolevData (q n w)).1‖ ≤
              K * ‖subspaceGradient (killedSobolevGraph (q n w)) u‖),
      ∀ (AE AF : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Ω →
          Matrix (Fin d) (Fin d) ℝ)
        (_hsymAE : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (omega : Ω),
          (AE n w omega).transpose = AE n w omega)
        (_hsymAF : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (omega : Ω),
          (AF n w omega).transpose = AF n w omega)
        (_hAE : ∀ᵐ omega ∂P, ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1))
          (pvec : Fin d → ℝ),
          Tendsto
            (fun j : ℕ =>
              affineDirichletResponse
                (centeredCube_isBounded (nodeCenter n w)
                  (descendantSide_pos (subdivisionHalfWidth H1) n one_pos))
                (hPnode n w)
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (field omega)
                  (NE j) (nodeCenter n w)
                  (descendantSide_pos (subdivisionHalfWidth H1) n one_pos)) pvec /
                (volume (q n w : Set (SpatialCoordinates d))).toReal)
            atTop
            (𝓝 (pvec ⬝ᵥ (AE n w omega).mulVec pvec)))
        (_hAF : ∀ᵐ omega ∂P, ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1))
          (pvec : Fin d → ℝ),
          Tendsto
            (fun j : ℕ =>
              affineDirichletResponse
                (centeredCube_isBounded (nodeCenter n w)
                  (descendantSide_pos (subdivisionHalfWidth H1) n one_pos))
                (hPnode n w)
                (_root_.SubdiffusiveProcess.EllipticRegularity.cutoffPositiveCoefficient model H (field omega)
                  (NF j) (nodeCenter n w)
                  (descendantSide_pos (subdivisionHalfWidth H1) n one_pos)) pvec /
                (volume (q n w : Set (SpatialCoordinates d))).toReal)
            atTop
            (𝓝 (pvec ⬝ᵥ (AF n w omega).mulVec pvec)))
        (_hAEmeas : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (i j : Fin d),
          Measurable (fun omega : Ω => AE n w omega i j))
        (_hAFmeas : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (i j : Fin d),
          Measurable (fun omega : Ω => AF n w omega i j)),
      let ck : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → ℝ :=
        (fun n w =>
          ∫ omega, Matrix.trace (AF n w omega) /
            Matrix.trace (AE n w omega) ∂P)
      let Bk : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Ω →
          Matrix (Fin d) (Fin d) ℝ :=
        fun n w omega =>
          (Matrix.trace (AE n w omega))⁻¹ •
            (AF n w omega - ck n w • AE n w omega)
      let Band : ℕ → ℕ → MeasurableSpace Ω := fun n H =>
        ⨆ (j : ℤ) (_h : |j + ((H1 * n : ℕ) : ℤ)| ≤ (H : ℤ)),
          (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
            (fun omega : Ω => field omega j)
      ∀ (BaseGood : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Set Ω)
        (_hBaseMeas : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
          MeasurableSet (BaseGood n w))
        (_hBaseCondition : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1))
          (omega : Ω), omega ∈ BaseGood n w →
          0 < Matrix.trace (AE n w omega) ∧
            ∀ (xi : Fin d → ℝ),
              c0 * Matrix.trace (AE n w omega) * (xi ⬝ᵥ xi) ≤
                xi ⬝ᵥ (AE n w omega).mulVec xi)
        (_hBaseChain : ∃ Bbase : Ω → ℝ,
          Measurable Bbase ∧ (∀ omega, 0 ≤ Bbase omega) ∧
          ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
            ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
              Nat.card {j : Fin J //
                ¬ omega ∈ BaseGood (j.val + 1)
                  (fun t : Fin (j.val + 1) =>
                    pi ⟨t.val, by omega⟩)} ≤
                (theta / 2) * (J : ℝ) + Bbase omega)
      (_hBkMean : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1))
          (i j : Fin d),
          ∫ omega, Bk n w omega i j ∂P = 0)
      (_hBkMoment : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
          eLpNorm
              (fun omega => ∑ i : Fin d, ∑ j : Fin d,
                |Bk n w omega i j|)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal (Cp * model.delta * (M - m)))
      (_hBkBand : ∀ (n : ℕ)
          (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1))
          (Hband : ℕ),
          eLpNorm
              (fun omega => ∑ i : Fin d, ∑ j : Fin d,
                |Bk n w omega i j -
                  ((P[fun omega => Bk n w omega i j |
                    Band n Hband]) omega)|)
              (ENNReal.ofReal p) P ≤
            ENNReal.ofReal
              (Cp * model.delta * (M - m) *
                (3 : ℝ) ^ (-aexp * (Hband : ℝ)))),
      let ExtraGood : (n : ℕ) →
          (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Set Ω :=
        fun n w =>
          {omega | omega ∈ BaseGood n w ∧
            (∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) ≤
              epsPrime * (M - m)}
      (∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
          MeasurableSet (ExtraGood n w)) ∧
      (∃ Bnew : Ω → ℝ,
        Measurable Bnew ∧ (∀ omega, 0 ≤ Bnew omega) ∧
          (∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
            ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
              Nat.card {j : Fin J //
                ¬ omega ∈ ExtraGood (j.val + 1)
                  (fun t : Fin (j.val + 1) =>
                    pi ⟨t.val, by omega⟩)} ≤
                theta * (J : ℝ) + Bnew omega) ∧
          ∀ (n : ℕ)
            (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (omega : Ω),
            omega ∈ ExtraGood n w →
            ∀ xi : Fin d → ℝ,
              |(volume (q n w : Set (SpatialCoordinates d))).toReal *
                  (xi ⬝ᵥ (AF n w omega).mulVec xi) -
                ck n w * (volume (q n w : Set (SpatialCoordinates d))).toReal *
                  (xi ⬝ᵥ (AE n w omega).mulVec xi)| ≤
                eps * (M - m) *
                  (volume (q n w : Set (SpatialCoordinates d))).toReal *
                  (xi ⬝ᵥ (AE n w omega).mulVec xi)) := by
  -- `delta0` is NOT free (it is exactly the small-disorder
  -- threshold `prop_allchain`'s own witness/Markov construction needs); computed here via
  -- `aux_cor_32_rate_and_delta0` from `hpRate`, matching `lem_witness`'s own `eta0` mechanism.
  -- `epsPrime = eps * c0`, so that `epsPrime / c0 = eps` exactly, unchanged.
  obtain ⟨A, gq, gr, K0, delta0, hApos, hqeq, hgq, hgq1, hgr, hgr1, hK0def, hK0pos, hdelta0pos,
      hbudget0, hAbeats⟩ :=
    aux_cor_32_rate_and_delta0 H1 d theta eps c0 p Cp aexp htheta htheta1 heps hc0 hp hCp haexp
      hpRate
  refine ⟨delta0, eps * c0, hdelta0pos, mul_pos heps hc0, ?_⟩
  intro _ _ model hmodel H Ω _ P field z r hr Sspace GN GE GF NE NF hJoint m M hm hmM hM horder
    rootCenter idx hidx nodeCenter nodeSide q hPnode AE AF hsymAE hsymAF hAE hAF hAEmeas hAFmeas
    ck Bk Band BaseGood hBaseMeas hBaseCondition hBaseChain hBkMean hBkMoment hBkBand ExtraGood
  refine ⟨?_, ?_⟩
  · 
    -- `ExtraGood n w` unfolds (definitionally, it is a `let`) to the set proved measurable by
    -- `aux_cor_32_extragood_measurable`, using the new `hAEmeas`/`hAFmeas` entrywise-measurable
    -- response matrices together with `hBaseMeas`.
    intro n w
    exact aux_cor_32_extragood_measurable AE AF hAEmeas hAFmeas ck BaseGood hBaseMeas
      (eps * c0 * (M - m)) n w
  · -- Extract Bbase from hBaseChain (already a hypothesis of cor_32, from good_event/prop_allchain
    -- upstream; not reproved here).
    obtain ⟨Bbase, hBbaseMeas, hBbaseNonneg, hBbaseBound⟩ := hBaseChain
    -- The extra-test alone, as a `Good2`-shaped predicate (paper eq:mfd-31, ).
    let Good2 : (n : ℕ) → (Fin n → OddGridIndex d (subdivisionHalfWidth H1)) → Set Ω :=
      fun n w => {omega | (∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) ≤ eps * c0 * (M - m)}
    have hExtraGood_eq : ∀ n w, ExtraGood n w = {omega | omega ∈ BaseGood n w ∧ omega ∈ Good2 n w} := by
      intro n w; rfl
    -- Deterministic affine-inequality step (paper cor-32, ): ellipticity of `AE`
    -- on `BaseGood` (condition (a) of `good_event`) plus the quadratic-form bound
    -- `aux_cor_32_abs_quadratic_form_le` turn the extra test's bound on `Bk` into the displayed affine
    -- saving inequality \eqref{eq:mfd-32}, with `eps = epsPrime / c0`.
    have hExtraTest : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (omega : Ω),
        omega ∈ ExtraGood n w → ∀ xi : Fin d → ℝ,
          |(volume (q n w : Set (SpatialCoordinates d))).toReal *
              (xi ⬝ᵥ (AF n w omega).mulVec xi) -
            ck n w * (volume (q n w : Set (SpatialCoordinates d))).toReal *
              (xi ⬝ᵥ (AE n w omega).mulVec xi)| ≤
            eps * (M - m) *
              (volume (q n w : Set (SpatialCoordinates d))).toReal *
              (xi ⬝ᵥ (AE n w omega).mulVec xi) := by
      intro n w omega hExi xi
      rw [hExtraGood_eq] at hExi
      rcases hExi with ⟨hBase, hSum⟩
      rcases hBaseCondition n w omega hBase with ⟨hTrPos, hEllip⟩
      have hvol_pos : 0 < (volume (q n w : Set (SpatialCoordinates d))).toReal := by
        have h := centeredCube_volume_pos (nodeCenter n w)
          (descendantSide_pos (subdivisionHalfWidth H1) n one_pos)
        rw [measureReal_def] at h
        exact h
      have h_key : AF n w omega - ck n w • AE n w omega =
          (Matrix.trace (AE n w omega)) • Bk n w omega := by
        have hTr_ne_zero : Matrix.trace (AE n w omega) ≠ 0 := by linarith
        dsimp [Bk]
        rw [smul_smul, mul_inv_cancel₀ hTr_ne_zero, one_smul]
      have h_diff : (volume (q n w : Set (SpatialCoordinates d))).toReal *
          (xi ⬝ᵥ (AF n w omega).mulVec xi) -
          ck n w * (volume (q n w : Set (SpatialCoordinates d))).toReal *
            (xi ⬝ᵥ (AE n w omega).mulVec xi) =
          (volume (q n w : Set (SpatialCoordinates d))).toReal *
            (Matrix.trace (AE n w omega)) *
            (xi ⬝ᵥ (Bk n w omega).mulVec xi) := by
        calc
          (volume (q n w : Set (SpatialCoordinates d))).toReal *
              (xi ⬝ᵥ (AF n w omega).mulVec xi) -
            ck n w * (volume (q n w : Set (SpatialCoordinates d))).toReal *
              (xi ⬝ᵥ (AE n w omega).mulVec xi) =
            (volume (q n w : Set (SpatialCoordinates d))).toReal *
              ((xi ⬝ᵥ (AF n w omega).mulVec xi) -
                ck n w * (xi ⬝ᵥ (AE n w omega).mulVec xi)) := by ring
          _ = (volume (q n w : Set (SpatialCoordinates d))).toReal *
              (xi ⬝ᵥ ((AF n w omega - ck n w • AE n w omega).mulVec xi)) := by
            simp [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul]
          _ = (volume (q n w : Set (SpatialCoordinates d))).toReal *
              (xi ⬝ᵥ (((Matrix.trace (AE n w omega)) • Bk n w omega).mulVec xi)) := by
            rw [h_key]
          _ = (volume (q n w : Set (SpatialCoordinates d))).toReal *
              (Matrix.trace (AE n w omega)) *
              (xi ⬝ᵥ (Bk n w omega).mulVec xi) := by
            simp [smul_mulVec, dotProduct_smul, mul_assoc]
      rw [h_diff]
      have hvol_pos' : 0 ≤ (volume (q n w : Set (SpatialCoordinates d))).toReal := by
        positivity
      rw [abs_mul, abs_mul, abs_of_pos hvol_pos]
      have h_nonneg_tr : 0 ≤ Matrix.trace (AE n w omega) := hTrPos.le
      rw [abs_of_nonneg h_nonneg_tr]
      have hxixi_nonneg : 0 ≤ xi ⬝ᵥ xi :=
        Finset.sum_nonneg fun i _ => mul_self_nonneg (xi i)
      have hineq1 : (volume (q n w : Set (SpatialCoordinates d))).toReal *
          (Matrix.trace (AE n w omega)) *
          |xi ⬝ᵥ (Bk n w omega).mulVec xi| ≤
          (volume (q n w : Set (SpatialCoordinates d))).toReal *
            (Matrix.trace (AE n w omega)) *
            ((∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) * (xi ⬝ᵥ xi)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hvol_pos.le h_nonneg_tr)
        exact aux_cor_32_abs_quadratic_form_le (Bk n w omega) xi
      have hSum' : (∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) ≤ eps * c0 * (M - m) := hSum
      have hM_minus_m_nonneg : 0 ≤ M - m := by
        have : m ≤ M := hmM
        linarith
      have h_sum_nonneg : 0 ≤ ∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j| :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
      have hineq2 : (volume (q n w : Set (SpatialCoordinates d))).toReal *
          (Matrix.trace (AE n w omega)) *
          ((∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) * (xi ⬝ᵥ xi)) ≤
          (volume (q n w : Set (SpatialCoordinates d))).toReal *
            (Matrix.trace (AE n w omega)) *
            ((eps * c0) * (M - m) * (xi ⬝ᵥ xi)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hvol_pos.le h_nonneg_tr)
        exact mul_le_mul_of_nonneg_right hSum' hxixi_nonneg
      have hkey : (Matrix.trace (AE n w omega)) * (xi ⬝ᵥ xi) ≤
          (1 / c0) * (xi ⬝ᵥ (AE n w omega).mulVec xi) := by
        have h := hEllip xi
        have e1 : (1 / c0 : ℝ) *
            (c0 * Matrix.trace (AE n w omega) * (xi ⬝ᵥ xi)) =
            Matrix.trace (AE n w omega) * (xi ⬝ᵥ xi) := by
          rw [show (1 / c0 : ℝ) * (c0 * Matrix.trace (AE n w omega) * (xi ⬝ᵥ xi)) =
              (1 / c0 * c0) * (Matrix.trace (AE n w omega) * (xi ⬝ᵥ xi)) from by ring,
            one_div, inv_mul_cancel₀ (ne_of_gt hc0), one_mul]
        calc
          Matrix.trace (AE n w omega) * (xi ⬝ᵥ xi) =
              (1 / c0) * (c0 * Matrix.trace (AE n w omega) * (xi ⬝ᵥ xi)) := e1.symm
          _ ≤ (1 / c0) * (xi ⬝ᵥ (AE n w omega).mulVec xi) := by
            apply mul_le_mul_of_nonneg_left h
            positivity
      have hineq3 : (volume (q n w : Set (SpatialCoordinates d))).toReal *
          (Matrix.trace (AE n w omega)) *
          ((eps * c0) * (M - m) * (xi ⬝ᵥ xi)) ≤
          (volume (q n w : Set (SpatialCoordinates d))).toReal *
            ((eps * c0) / c0) * (M - m) *
            (xi ⬝ᵥ (AE n w omega).mulVec xi) := by
        have h_factor : (Matrix.trace (AE n w omega)) * ((eps * c0) * (M - m) * (xi ⬝ᵥ xi)) ≤
            ((eps * c0) / c0) * (M - m) * (xi ⬝ᵥ (AE n w omega).mulVec xi) := by
          calc
            (Matrix.trace (AE n w omega)) * ((eps * c0) * (M - m) * (xi ⬝ᵥ xi)) =
                ((eps * c0) * (M - m)) * ((Matrix.trace (AE n w omega)) * (xi ⬝ᵥ xi)) := by ring
            _ ≤ ((eps * c0) * (M - m)) * ((1 / c0) * (xi ⬝ᵥ (AE n w omega).mulVec xi)) :=
              mul_le_mul_of_nonneg_left hkey
                (mul_nonneg (mul_pos heps hc0).le hM_minus_m_nonneg)
            _ = ((eps * c0) / c0) * (M - m) * (xi ⬝ᵥ (AE n w omega).mulVec xi) := by ring
        calc
          (volume (q n w : Set (SpatialCoordinates d))).toReal *
              (Matrix.trace (AE n w omega)) *
              ((eps * c0) * (M - m) * (xi ⬝ᵥ xi)) =
            (volume (q n w : Set (SpatialCoordinates d))).toReal *
              ((Matrix.trace (AE n w omega)) *
                ((eps * c0) * (M - m) * (xi ⬝ᵥ xi))) := by ring
          _ ≤ (volume (q n w : Set (SpatialCoordinates d))).toReal *
              (((eps * c0) / c0) * (M - m) * (xi ⬝ᵥ (AE n w omega).mulVec xi)) :=
            mul_le_mul_of_nonneg_left h_factor hvol_pos.le
          _ = (volume (q n w : Set (SpatialCoordinates d))).toReal *
              ((eps * c0) / c0) * (M - m) * (xi ⬝ᵥ (AE n w omega).mulVec xi) := by ring
      have h_epsPrime_div_c0 : (eps * c0) / c0 = eps := by
        rw [mul_div_assoc, div_self (ne_of_gt hc0), mul_one]
      rw [h_epsPrime_div_c0] at hineq3
      have h_total : (volume (q n w : Set (SpatialCoordinates d))).toReal *
          (Matrix.trace (AE n w omega)) *
          |xi ⬝ᵥ (Bk n w omega).mulVec xi| ≤
          (volume (q n w : Set (SpatialCoordinates d))).toReal * eps * (M - m) *
            (xi ⬝ᵥ (AE n w omega).mulVec xi) := by
        linarith
      simpa [abs_mul, abs_of_nonneg hvol_pos', abs_of_nonneg h_nonneg_tr,
        mul_comm, mul_left_comm, mul_assoc] using h_total
    -- The bound follows from `aux_cor_32_extra_chain`, assembled from
    -- `hBkMoment`/`hBkBand` (Markov + band-conditional-expectation dyadic telescoping),
    -- `hAEmeas`/`hAFmeas` (measurability of the test), `hJoint` (pushforward independence
    -- transport of the field's layers), and `hpRate`/`delta0` (the rate margin and disorder
    -- threshold computed at the top of the proof).
    have hExtraChain : ∃ Bextra : Ω → ℝ, Measurable Bextra ∧ (∀ omega, 0 ≤ Bextra omega) ∧
        ∀ᵐ omega ∂P, ∀ J : ℕ, 1 ≤ J →
          ∀ pi : Fin J → OddGridIndex d (subdivisionHalfWidth H1),
            (Nat.card {j : Fin J // ¬ omega ∈ Good2 (j.val + 1)
                (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} : ℝ) ≤
              (theta / 2) * (J : ℝ) + Bextra omega := by
      have hfield_meas : Measurable field := hJoint.2.1
      have hfield_map : Measure.map field P = (chaosSampleLaw model).toMeasure := hJoint.2.2.1
      have hPprob : IsProbabilityMeasure P := hJoint.1
      have hBand_def : ∀ (n H : ℕ), Band n H =
          ⨆ (j : ℤ) (_h : |j + ((H1 * n : ℕ) : ℤ)| ≤ (H : ℤ)),
            (inferInstance : MeasurableSpace C(SpatialCoordinates d, ℝ)).comap
              (fun omega : Ω => field omega j) := fun n H => rfl
      have hTest_meas : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
          Measurable (fun omega : Ω => ∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) :=
        fun n w => aux_cor_32_test_measurable AE AF hAEmeas hAFmeas ck n w
      have hTestB_meas : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (H : ℕ),
          StronglyMeasurable[Band n H]
            (fun omega : Ω => ∑ i : Fin d, ∑ j : Fin d,
              |(P[fun om' => Bk n w om' i j | Band n H]) omega|) := by
        intro n w H
        apply Finset.stronglyMeasurable_fun_sum
        intro i _
        apply Finset.stronglyMeasurable_fun_sum
        intro j _
        exact continuous_abs.comp_stronglyMeasurable stronglyMeasurable_condExp
      have hBand_le : ∀ (n H : ℕ), Band n H ≤ (inferInstance : MeasurableSpace Ω) := by
        intro n H
        rw [hBand_def n H]
        apply iSup_le; intro j; apply iSup_le; intro _hj
        exact ((measurable_pi_apply j).comp hfield_meas).comap_le
      have hTestB_ae : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (H : ℕ),
          AEStronglyMeasurable
            (fun omega : Ω => ∑ i : Fin d, ∑ j : Fin d,
              |(P[fun om' => Bk n w om' i j | Band n H]) omega|) P :=
        fun n w H => ((hTestB_meas n w H).mono (hBand_le n H)).aestronglyMeasurable
      have hTest_ae : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
          AEStronglyMeasurable (fun omega : Ω => ∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) P :=
        fun n w => (hTest_meas n w).aestronglyMeasurable
      have hthetap0 : 0 < theta / 2 := by linarith
      have hthetap1 : theta / 2 < 1 := by linarith
      rcases hmM.lt_or_eq with hMgt | hMeq
      · -- M > m: the genuine construction.
        have hMm_pos : 0 < M - m := by linarith
        have hMm_ne : (M - m) ≠ 0 := ne_of_gt hMm_pos
        have hdeltapos : 0 < model.delta := model.shellPrefix.delta_pos
        set Cbound : ℝ := Cp * model.delta * (M - m) with hCbounddef
        set lam0 : ℝ := eps * c0 * (M - m) with hlam0def
        set K : ℝ := K0 * (M - m) with hKdef2
        have hCbound_nonneg : 0 ≤ Cbound := by positivity
        have hlam0_pos : 0 < lam0 := by positivity
        have hKdefFull : K = lam0 * (1 - gr) / 2 := by
          rw [hKdef2, hlam0def, hK0def]; ring
        have hbudget : ∀ k : ℕ, 2 * ((2 * (Cbound / gq * gq ^ k) / (K * gr ^ k)) ^ p) ≤
            Real.exp (-(A * ((k : ℝ) + 1))) := by
          have hb0 := hbudget0 model.delta hdeltapos hmodel
          have := aux_cor_32_budget_scale p (Cp * model.delta) gq K0 A gr (M - m)
            (ne_of_gt hgq) (ne_of_gt hK0pos) (ne_of_gt hgr) hMm_ne hb0
          rw [hCbounddef, hKdef2]
          exact this
        have hTest_moment : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
            eLpNorm (fun omega : Ω => ∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|)
                (ENNReal.ofReal p) P ≤ ENNReal.ofReal Cbound := by
          intro n w; rw [hCbounddef]; exact hBkMoment n w
        have hTest_err : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)) (H : ℕ),
            eLpNorm (fun om : Ω => (∑ i : Fin d, ∑ j : Fin d, |Bk n w om i j|) -
                (∑ i : Fin d, ∑ j : Fin d, |(P[fun om' => Bk n w om' i j | Band n H]) om|))
                (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cbound * gq ^ H) := by
          intro n w H
          have hpointwise : ∀ omega : Ω,
              |(∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) -
                  (∑ i : Fin d, ∑ j : Fin d, |(P[fun om' => Bk n w om' i j | Band n H]) omega|)| ≤
                ∑ i : Fin d, ∑ j : Fin d,
                  |Bk n w omega i j - (P[fun om' => Bk n w om' i j | Band n H]) omega| := by
            intro omega
            have hstep : (∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) -
                (∑ i : Fin d, ∑ j : Fin d, |(P[fun om' => Bk n w om' i j | Band n H]) omega|) =
                ∑ i : Fin d, ∑ j : Fin d,
                  (|Bk n w omega i j| - |(P[fun om' => Bk n w om' i j | Band n H]) omega|) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i _
              rw [← Finset.sum_sub_distrib]
            rw [hstep]
            calc |∑ i : Fin d, ∑ j : Fin d,
                  (|Bk n w omega i j| - |(P[fun om' => Bk n w om' i j | Band n H]) omega|)| ≤
                ∑ i : Fin d, |∑ j : Fin d,
                  (|Bk n w omega i j| - |(P[fun om' => Bk n w om' i j | Band n H]) omega|)| :=
                  Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ i : Fin d, ∑ j : Fin d,
                  (|(|Bk n w omega i j| - |(P[fun om' => Bk n w om' i j | Band n H]) omega|)|) :=
                  Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ i : Fin d, ∑ j : Fin d,
                  |Bk n w omega i j - (P[fun om' => Bk n w om' i j | Band n H]) omega| :=
                  Finset.sum_le_sum fun i _ => Finset.sum_le_sum
                    fun j _ => abs_abs_sub_abs_le_abs_sub _ _
          have hg_nonneg : ∀ omega : Ω, 0 ≤ ∑ i : Fin d, ∑ j : Fin d,
              |Bk n w omega i j - (P[fun om' => Bk n w om' i j | Band n H]) omega| :=
            fun omega => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
          have hmono : eLpNorm (fun om : Ω => (∑ i : Fin d, ∑ j : Fin d, |Bk n w om i j|) -
                (∑ i : Fin d, ∑ j : Fin d, |(P[fun om' => Bk n w om' i j | Band n H]) om|))
                (ENNReal.ofReal p) P ≤
              eLpNorm (fun om : Ω => ∑ i : Fin d, ∑ j : Fin d,
                |Bk n w om i j - (P[fun om' => Bk n w om' i j | Band n H]) om|)
                (ENNReal.ofReal p) P :=
            eLpNorm_mono ((hTest_ae n w).sub (hTestB_ae n w H)) (fun omega => by
              rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hg_nonneg omega)]
              exact hpointwise omega)
          refine hmono.trans ?_
          have hqH : Cbound * gq ^ H = Cp * model.delta * (M - m) * (3 : ℝ) ^ (-aexp * (H : ℝ)) := by
            rw [hCbounddef, hqeq]
            congr 1
            rw [← Real.rpow_natCast ((3:ℝ) ^ (-aexp)) H, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
          rw [hqH]
          exact hBkBand n w H
        obtain ⟨Bextra, hBextraMeas, hBextraNonneg, hExtra⟩ :=
          aux_cor_32_extra_chain P model field hfield_meas hfield_map H1 hH1 (theta / 2) hthetap0
            hthetap1 p Cbound gq gr K A lam0 hp hgq hgq1 hgr hgr1 hCbound_nonneg hKdefFull
            hlam0_pos hApos hbudget hAbeats Band hBand_def
            (fun n w omega => ∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|)
            (fun n w H omega => ∑ i : Fin d, ∑ j : Fin d,
              |(P[fun om' => Bk n w om' i j | Band n H]) omega|)
            hTest_meas hTest_ae hTestB_meas hTestB_ae hTest_moment hTest_err
        exact ⟨Bextra, hBextraMeas, hBextraNonneg, hExtra⟩
      · -- M = m: `hBkMoment` forces the test to vanish a.e., so `Good2` holds a.e. trivially.
        refine ⟨fun _ => 0, measurable_const, fun _ => le_refl 0, ?_⟩
        have hgood2ae : ∀ (n : ℕ) (w : Fin n → OddGridIndex d (subdivisionHalfWidth H1)),
            ∀ᵐ omega ∂P, omega ∈ Good2 n w := by
          intro n w
          have hle := hBkMoment n w
          rw [← hMeq, sub_self, mul_zero, ENNReal.ofReal_zero] at hle
          have hmomZero : eLpNorm (fun omega => ∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|)
              (ENNReal.ofReal p) P = 0 := le_antisymm hle zero_le
          have hp0 : (ENNReal.ofReal p) ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
          have hae0 : (fun omega => ∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) =ᵐ[P]
              (fun _ => (0 : ℝ)) :=
            (eLpNorm_eq_zero_iff hp0).mp hmomZero
          filter_upwards [hae0] with omega homega
          show (∑ i : Fin d, ∑ j : Fin d, |Bk n w omega i j|) ≤ eps * c0 * (M - m)
          rw [homega, ← hMeq, sub_self, mul_zero]
        obtain ⟨Sigma0, hSigma0meas, hSigma0P, hSigma0prop⟩ :=
          aux_exists_measurable_full_measure_of_ae P
            (fun omega => ∀ qi : Σ n : ℕ, Fin n → OddGridIndex d (subdivisionHalfWidth H1),
              omega ∈ Good2 qi.1 qi.2)
            (ae_all_iff.mpr (fun qi => hgood2ae qi.1 qi.2))
        have hSigma0ae : ∀ᵐ omega ∂P, omega ∈ Sigma0 := by
          have hcompl : P Sigma0ᶜ = 0 := by
            rw [prob_compl_eq_one_sub hSigma0meas, hSigma0P, tsub_self]
          rw [ae_iff]
          exact hcompl
        filter_upwards [hSigma0ae] with omega homega J hJ pi
        have hall : ∀ j : Fin J, omega ∈ Good2 (j.val + 1)
            (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩) :=
          fun j => hSigma0prop omega homega ⟨j.val + 1, fun t => pi ⟨t.val, by omega⟩⟩
        have hempty : IsEmpty {j : Fin J // ¬ omega ∈ Good2 (j.val + 1)
            (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} :=
          ⟨fun j => j.2 (hall j.1)⟩
        have hcard0 : Nat.card {j : Fin J // ¬ omega ∈ Good2 (j.val + 1)
            (fun t : Fin (j.val + 1) => pi ⟨t.val, by omega⟩)} = 0 :=
          @Nat.card_of_isEmpty _ hempty
        rw [hcard0]
        have hJ0 : (0 : ℝ) ≤ (J : ℝ) := by positivity
        have : (0:ℝ) ≤ (theta / 2) * (J : ℝ) := by positivity
        simpa using this
    obtain ⟨Bextra, hBextraMeas, hBextraNonneg, hExtra⟩ := hExtraChain
    obtain ⟨Bnew, hBnewMeas, hBnewNonneg, hBound⟩ :=
      aux_cor_32_hBound_of_base_and_extra H1 P BaseGood Good2 theta Bbase Bextra
        hBbaseMeas hBbaseNonneg hBextraMeas hBextraNonneg hBbaseBound hExtra
    refine ⟨Bnew, hBnewMeas, hBnewNonneg, ?_, hExtraTest⟩
    filter_upwards [hBound] with omega h J hJ pi
    have h' := h J hJ pi
    simpa [hExtraGood_eq, mem_ofPred_eq] using h'

end
end SubdiffusiveProcess.Paper
