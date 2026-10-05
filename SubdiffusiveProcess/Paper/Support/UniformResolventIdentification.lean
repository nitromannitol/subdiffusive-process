module

public import SubdiffusiveProcess.Paper.prop_uniform_resolvent
public import SubdiffusiveProcess.Paper.Support.UniformResolventTracePassage

@[expose] public section

/-!
Internal proof support for the unconditional killed-resolvent proposition.
These declarations are not paper statement principals.
Supports: mfd_prop_uniform_resolvent
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter MeasureTheory Topology Set Metric SubdiffusiveProcess SubdiffusiveProcess.Section9
open scoped ENNReal NNReal ContDiff
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_mfd_prop_uniform_resolvent_ident_functional_passage {d : ℕ} (hd : 2 ≤ d)
    (zc : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (SInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (ν : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    [IsFiniteMeasure μ]
    (hμsupp : μ (closure (centeredCube zc
      r hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (Kμ Mbar : ℝ) (hKμ : 0 ≤ Kμ)
    (hνfin : ∀ k, ν k univ < ⊤)
    (hνsupp : ∀ k, ν k (closure (centeredCube zc
      r hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (hνmass : ∀ k, (ν k (closure (centeredCube zc
      r hr : Set (SpatialCoordinates d)))).toReal ≤ Mbar)
    (hνgrowth : ∀ k, ∀ x ∈ closure (centeredCube zc
        r hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 → ν k (ball x rr) ≤ ENNReal.ofReal (Kμ * rr ^ t))
    (hνdens : ∀ k, ∃ D : ℝ, 0 ≤ D ∧ ν k ≤ ENNReal.ofReal D •
      volume.restrict (centeredCube zc
        r hr : Set (SpatialCoordinates d)))
    (hW : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun k => ∫ x, h x ∂(ν k)) atTop (𝓝 (∫ x, h x ∂μ)))
    (T : CubeFractionalL2 (k := 1) hd zc
        r hr halfFractionalOrder → Lp ℝ 2 μ)
    (Ktr Ctr : ℝ) (hKtr : 0 ≤ Ktr) (hCtr : 0 ≤ Ctr)
    (hT : CubeTraceCharacterization hd zc hr μ Ktr Ctr T)
    (s : ℕ → DomainL2 (centeredCube zc
      r hr))
    (z : CubeFractionalL2 (k := 1) hd zc
        r hr halfFractionalOrder)
    (hs : Tendsto s atTop (𝓝 (z.val 0)))
    (w3 : ℕ → CubeFractionalL2 (k := 1) hd zc
        r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder)
    (hw3 : ∀ k, (w3 k).val 0 = s k) (B : ℝ)
    (hB : ∀ k, cubeFractionalL2Norm hd zc
      r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder (w3 k) ≤ B)
    (lam : ℝ) (F : SpatialCoordinates d → ℝ) (hF : Continuous F) :
    Tendsto (fun k => lam * ∫ x, (s k x) ^ 2 ∂(ν k) - 2 * ∫ x, F x * s k x ∂(ν k)) atTop
      (𝓝 (lam * ∫ x, (T z x) ^ 2 ∂μ - 2 * ∫ x, F x * T z x ∂μ)) := by
  have hKc : IsCompact (closure (centeredCube zc
      r hr : Set (SpatialCoordinates d))) :=
    (centeredCube_isBounded zc hr).isCompact_closure
  have : ∀ k, IsFiniteMeasure (ν k) := fun k => ⟨hνfin k⟩
  have h0 := aux_mfd_prop_uniform_resolvent_ident_trace_passage hd zc r hr SInterp t ht ν μ hμsupp
    Kμ Mbar hKμ hνfin hνsupp hνmass hνgrowth hνdens hW T Ktr Ctr hKtr hCtr hT s z hs w3 hw3 B hB
    (fun _ => 0) continuous_const
  have h1 := aux_mfd_prop_uniform_resolvent_ident_trace_passage hd zc r hr SInterp t ht ν μ hμsupp
    Kμ Mbar hKμ hνfin hνsupp hνmass hνgrowth hνdens hW T Ktr Ctr hKtr hCtr hT s z hs w3 hw3 B hB
    F hF
  have h2 := hW (fun x => F x ^ 2) (hF.pow 2)
  simp only [sub_zero] at h0
  have hsk : ∀ k, MemLp (s k : SpatialCoordinates d → ℝ) 2 (ν k) := by
    intro k
    obtain ⟨D, _, hD⟩ := hνdens k
    exact (Lp.memLp _).of_measure_le_smul ENNReal.ofReal_ne_top hD
  have hFk : ∀ k, MemLp F 2 (ν k) := fun k =>
    aux_prop_uniform_resolvent_ident_memLp_of_continuous (ν k) _ hKc (hνsupp k) F hF
  have hFμ : MemLp F 2 μ :=
    aux_prop_uniform_resolvent_ident_memLp_of_continuous μ _ hKc hμsupp F hF
  have heqk : ∀ k, lam * ∫ x, (s k x) ^ 2 ∂(ν k) - 2 * ∫ x, F x * s k x ∂(ν k) =
      lam * ∫ x, (s k x) ^ 2 ∂(ν k) - (∫ x, (s k x) ^ 2 ∂(ν k) + ∫ x, F x ^ 2 ∂(ν k) -
        ∫ x, (s k x - F x) ^ 2 ∂(ν k)) := by
    intro k
    rw [aux_prop_uniform_resolvent_ident_mul_eq (hsk k) (hFk k)]
    ring
  have heqμ : lam * ∫ x, (T z x) ^ 2 ∂μ - 2 * ∫ x, F x * T z x ∂μ =
      lam * ∫ x, (T z x) ^ 2 ∂μ - (∫ x, (T z x) ^ 2 ∂μ + ∫ x, F x ^ 2 ∂μ -
        ∫ x, (T z x - F x) ^ 2 ∂μ) := by
    rw [aux_prop_uniform_resolvent_ident_mul_eq (Lp.memLp (T z)) hFμ]
    ring
  rw [heqμ]
  exact ((h0.const_mul lam).sub ((h0.add h2).sub h1)).congr (fun k => (heqk k).symm)

theorem aux_mfd_prop_uniform_resolvent_ident_deterministic {d : ℕ} (hd : 2 ≤ d)
    (zc : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (SInterp : CubeFractionalInterpolationInput d hd)
    (t : ℝ) (ht : (d : ℝ) - 1 < t)
    (a : ℕ → PositiveCoefficient (centeredCube zc
      r hr))
    (EN : ℕ → DomainL2 (centeredCube zc
      r hr) → ℝ≥0∞)
    (hEN : ∀ N u, EN N u = ⨅ v : {v : killedSobolevGraph (centeredCube
        zc r hr) //
        (v : SobolevData (centeredCube zc
          r hr)).1 = u},
      ENNReal.ofReal (sobolevCoefficientForm (a N)
        (v.val : SobolevData (centeredCube zc
          r hr))
        (v.val : SobolevData (centeredCube zc
          r hr))))
    (Elim : DomainL2 (centeredCube zc
      r hr) → ℝ≥0∞)
    (hliminf : _root_.SubdiffusiveProcess.ResponseMoments.MoscoLiminf EN Elim) (hrec : _root_.SubdiffusiveProcess.ResponseMoments.MoscoRecovery EN Elim)
    (ν : ℕ → Measure (SpatialCoordinates d)) (μ : Measure (SpatialCoordinates d))
    [IsFiniteMeasure μ]
    (hμsupp : μ (closure (centeredCube zc
      r hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (Kμ Mbar : ℝ) (hKμ : 0 ≤ Kμ)
    (hνfin : ∀ k, ν k univ < ⊤)
    (hνsupp : ∀ k, ν k (closure (centeredCube zc
      r hr : Set (SpatialCoordinates d)))ᶜ = 0)
    (hνmass : ∀ k, (ν k (closure (centeredCube zc
      r hr : Set (SpatialCoordinates d)))).toReal ≤ Mbar)
    (hνgrowth : ∀ k, ∀ x ∈ closure (centeredCube zc
        r hr : Set (SpatialCoordinates d)),
      ∀ rr : ℝ, 0 < rr → rr ≤ 1 → ν k (ball x rr) ≤ ENNReal.ofReal (Kμ * rr ^ t))
    (hνdens : ∀ k, ∃ D : ℝ, 0 ≤ D ∧ ν k ≤ ENNReal.ofReal D •
      volume.restrict (centeredCube zc
        r hr : Set (SpatialCoordinates d)))
    (hW : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun k => ∫ x, h x ∂(ν k)) atTop (𝓝 (∫ x, h x ∂μ)))
    (T : CubeFractionalL2 (k := 1) hd zc
        r hr halfFractionalOrder → Lp ℝ 2 μ)
    (Ktr Ctr : ℝ) (hKtr : 0 ≤ Ktr) (hCtr : 0 ≤ Ctr)
    (hT : CubeTraceCharacterization hd zc hr μ Ktr Ctr T)
    (i : (u : DomainL2 (centeredCube zc
        r hr)) → Elim u ≠ ⊤ →
      CubeFractionalL2 (k := 1) hd zc
        r hr halfFractionalOrder)
    (hival : ∀ u (hu : Elim u ≠ ⊤), (i u hu).val 0 = u)
    (J : DomainL2 (centeredCube zc
      r hr) → SpatialCoordinates d → ℝ)
    (hJ : ∀ u (hu : Elim u ≠ ⊤), J u =ᵐ[μ] (T (i u hu) : SpatialCoordinates d → ℝ))
    (lam : ℝ) (hlam : 0 < lam) (f : BoundedContinuousFunction (SpatialCoordinates d) ℝ)
    (ustar : DomainL2 (centeredCube zc
      r hr))
    (hmin : Elim ustar ≠ ⊤ ∧
      (∀ w, Elim w ≠ ⊤ →
        (Elim ustar).toReal + lam * (∫ x, (J ustar x) ^ 2 ∂μ) -
            2 * (∫ x, f x * J ustar x ∂μ) ≤
          (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂μ) - 2 * (∫ x, f x * J w x ∂μ)) ∧
      (∀ w, Elim w ≠ ⊤ →
        (∀ v, Elim v ≠ ⊤ →
          (Elim w).toReal + lam * (∫ x, (J w x) ^ 2 ∂μ) - 2 * (∫ x, f x * J w x ∂μ) ≤
            (Elim v).toReal + lam * (∫ x, (J v x) ^ 2 ∂μ) - 2 * (∫ x, f x * J v x ∂μ)) →
        w = ustar))
    (u : ℕ → killedSobolevGraph (centeredCube zc
      r hr))
    (R : ℕ → SpatialCoordinates d → ℝ)
    (hRu : ∀ N, R N =ᵐ[volume.restrict (centeredCube zc
        r hr : Set (SpatialCoordinates d))]
      ((u N : SobolevData (centeredCube zc
        r hr)).1 : SpatialCoordinates d → ℝ))
    (hweak : ∀ N (w : killedSobolevGraph (centeredCube zc
        r hr)),
      sobolevCoefficientForm (a N)
          (u N : SobolevData (centeredCube zc
            r hr))
          (w : SobolevData (centeredCube zc
            r hr)) =
        ∫ x, (f x - lam * R N x) * (w : SobolevData (centeredCube
          zc r hr)).1 x ∂(ν N))
    (henergy : ∀ N, sobolevCoefficientForm (a N)
        (u N : SobolevData (centeredCube zc
          r hr))
        (u N : SobolevData (centeredCube zc
          r hr)) ≤
      ‖f‖ ^ 2 * (ν N (centeredCube zc
        r hr : Set (SpatialCoordinates d))).toReal / lam)
    (Kc : ℕ → ℝ)
    (hcoer3 : ∀ N (v : killedSobolevGraph (centeredCube zc
        r hr)),
      ∃ v3 : CubeFractionalL2 (k := 1) hd zc
          r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
        v3.val 0 = (v : SobolevData (centeredCube zc
          r hr)).1 ∧
        (cubeFractionalL2Norm hd zc
          r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3) ^ 2 ≤
          Kc N * sobolevCoefficientForm (a N)
            (v : SobolevData (centeredCube zc
              r hr))
            (v : SobolevData (centeredCube zc
              r hr)))
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (Mb : ℝ) (hMb : ∀ k, Kc (σ k) ≤ Mb)
    (ubar : DomainL2 (centeredCube zc
      r hr))
    (hconv : Tendsto (fun k => (u (σ k) : SobolevData (centeredCube
      zc r hr)).1) atTop
      (𝓝 ubar)) :
    ubar = ustar := by
  set Qs : Set (SpatialCoordinates d) := (centeredCube zc
    r hr : Set (SpatialCoordinates d)) with hQs
  have hKc : IsCompact (closure Qs) :=
    (centeredCube_isBounded zc hr).isCompact_closure
  have : ∀ k, IsFiniteMeasure (ν k) := fun k => ⟨hνfin k⟩
  obtain ⟨hustar, hminle, huniq⟩ := hmin
  -- subsequence data
  have hWσ : ∀ h : SpatialCoordinates d → ℝ, Continuous h →
      Tendsto (fun k => ∫ x, h x ∂(ν (σ k))) atTop (𝓝 (∫ x, h x ∂μ)) := fun h hh =>
    (hW h hh).comp hσ.tendsto_atTop
  -- energy bound
  obtain ⟨Eb, hEb⟩ : ∃ Eb : ℝ, Eb = ‖f‖ ^ 2 * Mbar / lam := ⟨_, rfl⟩
  have hform_nn : ∀ N (v : killedSobolevGraph (centeredCube zc
      r hr)),
      0 ≤ sobolevCoefficientForm (a N) (v : SobolevData _) (v : SobolevData _) :=
    fun N v => sobolevCoefficientForm_nonneg _ _
  have hEbN : ∀ N, sobolevCoefficientForm (a N) (u N : SobolevData _) (u N : SobolevData _)
      ≤ Eb := by
    intro N
    refine (henergy N).trans ?_
    have hm : (ν N Qs).toReal ≤ Mbar := by
      refine le_trans ?_ (hνmass N)
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono subset_closure)
    rw [hEb]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm (sq_nonneg _)) hlam.le
  have hENle : ∀ N (v : killedSobolevGraph (centeredCube zc
      r hr)),
      EN N (v : SobolevData _).1 ≤
        ENNReal.ofReal (sobolevCoefficientForm (a N) (v : SobolevData _) (v : SobolevData _)) := by
    intro N v
    rw [hEN]
    exact iInf_le_of_le ⟨v, rfl⟩ le_rfl
  -- the cluster has finite limit energy
  have hubar : Elim ubar ≠ ⊤ := by
    have hle : Elim ubar ≤ ENNReal.ofReal Eb :=
      aux_prop_uniform_resolvent_ident_liminf_subseq EN Elim hliminf σ hσ _ ubar hconv _
        (Frequently.of_forall fun k =>
          (hENle (σ k) (u (σ k))).trans (ENNReal.ofReal_le_ofReal (hEbN (σ k))))
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  -- `H^{3/4}` bounds along the subsequence
  have hu3 : ∀ k, ∃ v3 : CubeFractionalL2 (k := 1) hd zc
      r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
      v3.val 0 = (u (σ k) : SobolevData _).1 ∧
      cubeFractionalL2Norm hd zc
        r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3 ≤
        Real.sqrt (max Mb 0 * Eb) := by
    intro k
    obtain ⟨v3, hv3, hb⟩ := hcoer3 (σ k) (u (σ k))
    exact ⟨v3, hv3, aux_prop_uniform_resolvent_ident_norm_bound _ _ _ Mb Eb hb (hMb k)
      (hform_nn _ _) (hEbN (σ k))⟩
  choose U3 hU3 hU3b using hu3
  -- passage on the minimizer side
  have hcu := aux_mfd_prop_uniform_resolvent_ident_functional_passage hd zc r hr SInterp t ht (fun k => ν (σ k)) μ
    hμsupp Kμ Mbar hKμ (fun k => hνfin (σ k)) (fun k => hνsupp (σ k)) (fun k => hνmass (σ k))
    (fun k => hνgrowth (σ k)) (fun k => hνdens (σ k)) hWσ T Ktr Ctr hKtr hCtr hT
    (fun k => (u (σ k) : SobolevData _).1) (i ubar hubar)
    (by rw [hival]; exact hconv) U3 hU3 _ hU3b lam f f.continuous
  -- recovery sequence for `ustar`
  obtain ⟨v, hvb, hvconv, hvev⟩ :=
    aux_prop_uniform_resolvent_ident_recovery_reps _ a EN hEN Elim hrec ustar hustar
  obtain ⟨Es, hEs⟩ : ∃ Es : ℝ, Es = (Elim ustar).toReal + 2 := ⟨_, rfl⟩
  have hv3 : ∀ k, ∃ v3 : CubeFractionalL2 (k := 1) hd zc
      r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder,
      v3.val 0 = (v (σ k) : SobolevData _).1 ∧
      cubeFractionalL2Norm hd zc
        r hr _root_.SubdiffusiveProcess.EllipticRegularity.threeQuarterOrder v3 ≤
        Real.sqrt (max Mb 0 * Es) := by
    intro k
    obtain ⟨v3, hv3, hb⟩ := hcoer3 (σ k) (v (σ k))
    exact ⟨v3, hv3, aux_prop_uniform_resolvent_ident_norm_bound _ _ _ Mb Es hb (hMb k)
      (hform_nn _ _) (hEs ▸ hvb (σ k))⟩
  choose V3 hV3 hV3b using hv3
  have hcv := aux_mfd_prop_uniform_resolvent_ident_functional_passage hd zc r hr SInterp t ht (fun k => ν (σ k)) μ
    hμsupp Kμ Mbar hKμ (fun k => hνfin (σ k)) (fun k => hνsupp (σ k)) (fun k => hνmass (σ k))
    (fun k => hνgrowth (σ k)) (fun k => hνdens (σ k)) hWσ T Ktr Ctr hKtr hCtr hT
    (fun k => (v (σ k) : SobolevData _).1) (i ustar hustar)
    (by rw [hival]; exact hvconv.comp hσ.tendsto_atTop) V3 hV3 _ hV3b lam f f.continuous
  -- finite-cutoff minimality along the subsequence
  have hfk : ∀ k, MemLp (f : SpatialCoordinates d → ℝ) 2 (ν (σ k)) := fun k =>
    aux_prop_uniform_resolvent_ident_memLp_of_continuous (ν (σ k)) _ hKc (hνsupp (σ k)) f
      f.continuous
  have hmink : ∀ k,
      sobolevCoefficientForm (a (σ k)) (u (σ k) : SobolevData _) (u (σ k) : SobolevData _) +
          (lam * ∫ x, ((u (σ k) : SobolevData (centeredCube zc
              r hr)).1 x) ^ 2 ∂(ν (σ k)) -
            2 * ∫ x, f x * (u (σ k) : SobolevData (centeredCube zc
              r hr)).1 x ∂(ν (σ k))) ≤
        sobolevCoefficientForm (a (σ k)) (v (σ k) : SobolevData _) (v (σ k) : SobolevData _) +
          (lam * ∫ x, ((v (σ k) : SobolevData (centeredCube zc
              r hr)).1 x) ^ 2 ∂(ν (σ k)) -
            2 * ∫ x, f x * (v (σ k) : SobolevData (centeredCube zc
              r hr)).1 x ∂(ν (σ k))) := by
    intro k
    obtain ⟨D, _, hD⟩ := hνdens (σ k)
    have := aux_prop_uniform_resolvent_ident_finite_min _ (a (σ k)) (ν (σ k)) D hD f (hfk k)
      lam hlam.le (R (σ k)) (u (σ k)) (hRu (σ k)) (hweak (σ k)) (v (σ k))
    linarith
  -- identify the limits with the functional of the parent
  have hJb2 : ∫ x, (J ubar x) ^ 2 ∂μ = ∫ x, (T (i ubar hubar) x) ^ 2 ∂μ :=
    integral_congr_ae ((hJ ubar hubar).mono fun x hx => by simp only [hx])
  have hJb1 : ∫ x, f x * J ubar x ∂μ = ∫ x, f x * T (i ubar hubar) x ∂μ :=
    integral_congr_ae ((hJ ubar hubar).mono fun x hx => by simp only [hx])
  have hJs2 : ∫ x, (J ustar x) ^ 2 ∂μ = ∫ x, (T (i ustar hustar) x) ^ 2 ∂μ :=
    integral_congr_ae ((hJ ustar hustar).mono fun x hx => by simp only [hx])
  have hJs1 : ∫ x, f x * J ustar x ∂μ = ∫ x, f x * T (i ustar hustar) x ∂μ :=
    integral_congr_ae ((hJ ustar hustar).mono fun x hx => by simp only [hx])
  obtain ⟨cT, hcT⟩ : ∃ cT : ℝ, cT = lam * ∫ x, (T (i ubar hubar) x) ^ 2 ∂μ -
    2 * ∫ x, f x * T (i ubar hubar) x ∂μ := ⟨_, rfl⟩
  obtain ⟨dT, hdT⟩ : ∃ dT : ℝ, dT = lam * ∫ x, (T (i ustar hustar) x) ^ 2 ∂μ -
    2 * ∫ x, f x * T (i ustar hustar) x ∂μ := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (Elim ubar).toReal := ⟨_, rfl⟩
  obtain ⟨Bs, hBs⟩ : ∃ Bs : ℝ, Bs = (Elim ustar).toReal := ⟨_, rfl⟩
  rw [← hcT] at hcu
  rw [← hdT] at hcv
  -- the key inequality `Func ubar ≤ Func ustar`
  have key : A + cT ≤ Bs + dT := by
    by_contra hcon
    push Not at hcon
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = A + cT - (Bs + dT) := ⟨_, rfl⟩
    have hδpos : 0 < δ := by linarith
    have e1 := (tendsto_order.1 hcu).1 (cT - δ / 4) (by linarith)
    have e2 := (tendsto_order.1 hcv).2 (dT + δ / 4) (by linarith)
    have e3 := hσ.tendsto_atTop.eventually (hvev (δ / 4) (by linarith))
    rw [← hBs] at e3
    have e4 : ∀ᶠ k in atTop,
        sobolevCoefficientForm (a (σ k)) (u (σ k) : SobolevData _) (u (σ k) : SobolevData _) <
          A - δ / 4 := by
      filter_upwards [e1, e2, e3] with k h1 h2 h3
      have := hmink k
      linarith
    obtain ⟨k0, hk0⟩ := e4.exists
    have hpos : 0 < A - δ / 4 := lt_of_le_of_lt (hform_nn _ _) hk0
    have hle : Elim ubar ≤ ENNReal.ofReal (A - δ / 4) :=
      aux_prop_uniform_resolvent_ident_liminf_subseq EN Elim hliminf σ hσ _ ubar hconv _
        (e4.mono fun k hk => (hENle (σ k) (u (σ k))).trans
          (ENNReal.ofReal_le_ofReal hk.le)).frequently
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_ofReal hpos.le, ← hA] at this
    linarith
  -- `ubar` is a minimizer, hence `ubar = ustar`
  refine huniq ubar hubar (fun w hw => ?_)
  have := hminle w hw
  rw [hJb2, hJb1]
  rw [hJs2, hJs1] at this
  rw [hA, hBs, hcT, hdT] at key
  linarith

end SubdiffusiveProcess.Paper
