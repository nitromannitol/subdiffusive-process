module

public import SubdiffusiveProcess.Paper.affine_gap_cell

@[expose] public section




open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

noncomputable section
namespace Paper

/-- The square-root source budget at scale `r` is dominated by the one with the cell mass. -/
theorem aux_affine_cell_assembly_source {d : ℕ} (r c s S src0 : ℝ) (hr : 0 < r) (hc : 0 < c)
    (hs : 0 < s) (hsrc0 : 0 ≤ src0) (hS : c * r ^ d ≤ S) :
    src0 * Real.sqrt c * r * s ^ (-(1 : ℝ) / 2) ≤
      src0 * r ^ ((2 - (d : ℝ)) / 2) * Real.sqrt (S / s) := by
  have hSs : c * r ^ d / s ≤ S / s := div_le_div_of_nonneg_right hS hs.le
  have hsq : Real.sqrt (c * r ^ d / s) ≤ Real.sqrt (S / s) := Real.sqrt_le_sqrt hSs
  have hid : r ^ ((2 - (d : ℝ)) / 2) * Real.sqrt (c * r ^ d / s) =
      Real.sqrt c * r * s ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_div' _ hs.le, Real.sqrt_mul hc.le, ← Real.rpow_natCast r d,
      Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hr.le]
    have hrr : r ^ ((2 - (d : ℝ)) / 2) * r ^ ((d : ℝ) * (1 / 2)) = r := by
      rw [← Real.rpow_add hr]
      have : (2 - (d : ℝ)) / 2 + (d : ℝ) * (1 / 2) = 1 := by ring
      rw [this, Real.rpow_one]
    have hneg : s ^ (-(1 : ℝ) / 2) = (s ^ ((1 : ℝ) / 2))⁻¹ := by
      rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring, Real.rpow_neg hs.le]
    rw [hneg]
    calc r ^ ((2 - (d : ℝ)) / 2) * (c ^ ((1 : ℝ) / 2) * r ^ ((d : ℝ) * (1 / 2)) / s ^ ((1 : ℝ) / 2))
        = c ^ ((1 : ℝ) / 2) * (r ^ ((2 - (d : ℝ)) / 2) * r ^ ((d : ℝ) * (1 / 2))) *
          (s ^ ((1 : ℝ) / 2))⁻¹ := by ring
      _ = c ^ ((1 : ℝ) / 2) * r * (s ^ ((1 : ℝ) / 2))⁻¹ := by rw [hrr]
  calc src0 * Real.sqrt c * r * s ^ (-(1 : ℝ) / 2)
      = src0 * (r ^ ((2 - (d : ℝ)) / 2) * Real.sqrt (c * r ^ d / s)) := by rw [hid]; ring
    _ ≤ src0 * (r ^ ((2 - (d : ℝ)) / 2) * Real.sqrt (S / s)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hr.le _)) hsrc0
    _ = _ := by ring

/-- Per-cell conclusion of `lem_affine` from almost-sure cell events and `affine_gap_cell`. -/
theorem affine_cell_assembly
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (alpha beta gamma zeta rho : ℝ) (ha : 0 < alpha)
    (Cin Lt epshom src0 : ℝ) (heps : 0 ≤ epshom) (hsrc0 : 0 ≤ src0)
    (hGCN : aux_affine_gap_cell_gcnInstance d alpha beta gamma zeta rho Cin Lt epshom src0)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    (Qcentre : SpatialCoordinates d) (Qside : ℝ) (hQside : 0 < Qside)
    (GE : Ω → DomainL2 (centeredCube Qcentre Qside hQside) →L[ℝ] DomainL2 (centeredCube Qcentre Qside hQside))
    (E : Ω → DirichletForm.ClosedForm (volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))))
    (GammaE : ∀ om, DirichletForm.EnergyMeasure (E om))
    (Good : Set Ω) (baseMesh : Ω → (SpatialCoordinates d → ℝ) → ℝ)
    (z zP zc : SpatialCoordinates d) (hzc : zc = z) (r m L : ℝ) (hr : 0 < r) (hm : 0 < m)
    (hRlo : Lt ^ gamma * r ≤ m / 729) (hRhi : m / 729 ≤ Cin * Lt ^ gamma * r)
    (hpad : Metric.closedBall z (m / 2) ⊆ Metric.ball zP (L * r / 2))
    (hparentQ : Metric.ball zP (L * r / 2) ⊆ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)))
    (hwide : 27 * m ≤ L * r) (hLt : 0 < Lt) (hLLt : Lt ≤ L)
    (c : ℝ) (hc : 0 < c) (sE sCmp : Ω → ℝ)
    (Ctotal KP Cext : ℝ) (hCtotal : 0 ≤ Ctotal) (hKP : 0 ≤ KP)
    (hCinC : Real.sqrt d ^ alpha * Ctotal ≤ Cin) (hCinE : Cext ≤ Cin)
    (hCinP : 729 * Real.sqrt (2 * KP) * (L / Lt) ^ (((d : ℝ) + zeta) / 2) ≤ Cin)
    (hbank : ∀ᵐ om ∂P, ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
      ∀ (fL2 : DomainL2 (centeredCube Qcentre Qside hQside)), ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f) →
      ∃ U : SpatialCoordinates d → ℝ, ContinuousOn U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
        ((GE om fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) ∧
        ∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), U x = 0)
    (hsE : ∀ᵐ om ∂P, 0 < sE om) (hsCmp : ∀ᵐ om ∂P, 0 < sCmp om)
    (hratio : ∀ᵐ om ∂P, om ∈ Good → (sCmp om)⁻¹ ≤ 2 * (sE om)⁻¹)
    (hCGE : ∀ᵐ om ∂P, om ∈ Good → ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
      ∀ (fL2 : DomainL2 (centeredCube Qcentre Qside hQside)), ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f) →
      ∃ U : SpatialCoordinates d → ℝ, ContinuousOn U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
        ((GE om fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) ∧
        (∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), U x = 0) ∧
        Lane4.IsHolderOn alpha (closure (Metric.ball z (r / 2))) U ∧
        (∃ cq : ℝ, Lane4.cAlphaNorm alpha
            (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
            (fun x => U (z + r • x) - cq) ≤
          Ctotal * (normalizedL2On (Metric.ball z (3 * r / 2))
            (fun x => U x - (volume.real (Metric.ball z (3 * r / 2)))⁻¹ *
              ∫ y in Metric.ball z (3 * r / 2), U y) + r ^ 2 * (sE om)⁻¹ * sSup {v : ℝ | ∃ x ∈ closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), v = |f x|})) ∧
        (∀ w : SpatialCoordinates d,
          Metric.closedBall zc (m / 18) ⊆ Metric.ball w (27 * m / 2) →
          Metric.ball w (27 * m / 2) ⊆ (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)) →
          ∃ (v : weakSobolevGraph (centeredCube zc (m / 81) (div_pos hm (by norm_num)))) (V : SpatialCoordinates d → ℝ),
            ContinuousOn V (closure (centeredCube zc (m / 81) (div_pos hm (by norm_num)) : Set (SpatialCoordinates d))) ∧
            (((v : SobolevData (centeredCube zc (m / 81) (div_pos hm (by norm_num)))).1 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube zc (m / 81) (div_pos hm (by norm_num)) : Set (SpatialCoordinates d))] V) ∧
            (∀ x ∈ frontier (centeredCube zc (m / 81) (div_pos hm (by norm_num)) : Set (SpatialCoordinates d)), V x = U x) ∧
            (∀ psi : killedSobolevGraph (centeredCube zc (m / 81) (div_pos hm (by norm_num))),
              inner ℝ (sobolevGradient (v : SobolevData (centeredCube zc (m / 81) (div_pos hm (by norm_num)))))
                (subspaceGradient (killedSobolevGraph (centeredCube zc (m / 81) (div_pos hm (by norm_num)))) psi) = 0) ∧
            normalizedL2On (Metric.ball zc (m / 1458)) (fun x => U x - V x) ≤
              epshom * normalizedL2On (Metric.ball zc (m / 18))
                (fun x => U x - (volume.real (Metric.ball zc (m / 18)))⁻¹ *
                  ∫ y in Metric.ball zc (m / 18), U y) +
              Ctotal * (m / 9) ^ 2 * (sCmp om)⁻¹ * sSup {v : ℝ | ∃ x ∈ closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), v = |f x|}))
    (hPoinc : ∀ᵐ om ∂P, om ∈ Good → ∀ (fL2 : DomainL2 (centeredCube Qcentre Qside hQside)) (U : SpatialCoordinates d → ℝ),
      ((GE om fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) →
      (normalizedL2On (centeredCube z m hm : Set (SpatialCoordinates d))
          (fun x => U x - (volume.real (centeredCube z m hm : Set (SpatialCoordinates d)))⁻¹ *
            ∫ y in (centeredCube z m hm : Set (SpatialCoordinates d)), U y)) ^ 2 ≤
        (KP * m ^ 2 / volume.real (centeredCube z m hm : Set (SpatialCoordinates d))) *
          (sCmp om)⁻¹ * ((GammaE om).measure (GE om fL2) (Metric.ball zP (L * r / 2))).toReal)
    (hext : ∀ᵐ om ∂P, om ∈ Good → ∀ g : SpatialCoordinates d → ℝ,
      ContinuousOn g (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) →
      Lane4.IsHolderOn beta (frontier (Metric.ball z (r / 2))) g →
      ∃ (v : DomainL2 (centeredCube Qcentre Qside hQside)) (V : SpatialCoordinates d → ℝ),
        v ∈ (E om).domain ∧ ContinuousOn V (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
        ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] V) ∧
        (∀ x ∈ frontier (Metric.ball z (r / 2)), V x = g x) ∧
        ((GammaE om).measure v (Metric.ball z (r / 2))).toReal ≤
          Cext * sE om * r ^ ((d : ℝ) - 2) * (r ^ beta * Lane4.holderSeminorm beta
            (frontier (Metric.ball z (r / 2))) g) ^ 2)
    (hsrc : ∀ᵐ om ∂P, om ∈ Good → ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
      r ≤ baseMesh om f →
      Ctotal * (m / 9) ^ 2 * (sCmp om)⁻¹ * sSup {v : ℝ | ∃ x ∈ closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), v = |f x|} + r ^ 2 * (sE om)⁻¹ * sSup {v : ℝ | ∃ x ∈ closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), v = |f x|} ≤
        src0 * Real.sqrt c * r * (sE om) ^ (-(1 : ℝ) / 2)) :
    ∀ᵐ om ∂P, ∀ (f : SpatialCoordinates d → ℝ), ContDiff ℝ ∞ f →
      ∀ (fL2 : DomainL2 (centeredCube Qcentre Qside hQside)), ((fL2 : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] f) →
      (let u := GE om fL2
       ∃ U : SpatialCoordinates d → ℝ,
         ContinuousOn U (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
         ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] U) ∧
         (∀ x ∈ frontier (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), U x = 0) ∧
         (r ≤ baseMesh om f → om ∈ Good →
           Lane4.IsHolderOn alpha (closure (Metric.ball z (r / 2))) U ∧
           (let lambda : Set (SpatialCoordinates d) → ℝ :=
              fun A => ((GammaE om).measure u A).toReal + c * (volume A).toReal
            lambda (Metric.ball zP (L * r / 2)) ≤ L ^ ((d : ℝ) + zeta) * lambda (Metric.ball z (r / 2)) →
            ∃ pc : (Fin d → ℝ) × ℝ,
              (let ell : SpatialCoordinates d → ℝ := fun x => (∑ i, pc.1 i * x i) + pc.2
               let b : SpatialCoordinates d → ℝ := fun x => U x - ell x
               let eSet : Set ℝ :=
                 {e : ℝ | ∃ (v : DomainL2 (centeredCube Qcentre Qside hQside)) (V : SpatialCoordinates d → ℝ),
                     v ∈ (E om).domain ∧
                     ContinuousOn V (closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))) ∧
                     ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d))] V) ∧
                     (∀ x ∈ frontier (Metric.ball z (r / 2)), V x = b x) ∧
                     e = ((GammaE om).measure v (Metric.ball z (r / 2))).toReal}
               ∃ Lambda : ℝ,
                 IsGLB eSet Lambda ∧
                 eSet.Nonempty ∧
                 Lambda ≤ rho * lambda (Metric.ball z (r / 2)))))) := by
  subst hzc
  filter_upwards [hbank, hsE, hsCmp, hratio, hCGE, hPoinc, hext, hsrc] with om hbankom hsEom hsCmpom
    hratioom hCGEom hPoincom hextom hsrcom
  intro f hf fL2 hfL2
  by_cases hG : om ∈ Good
  · obtain ⟨U, hUc, hUr, hUb, hUh, ⟨cq, hnorm⟩, hharm⟩ := hCGEom hG f hf fL2 hfL2
    refine ⟨U, hUc, hUr, hUb, fun hmesh _ => ⟨hUh, ?_⟩⟩
    intro lambda hpar
    have hfsup : 0 ≤ sSup {v : ℝ | ∃ x ∈ closure (centeredCube Qcentre Qside hQside : Set (SpatialCoordinates d)), v = |f x|} := by
      apply Real.sSup_nonneg
      rintro v ⟨x, _, rfl⟩
      exact abs_nonneg _
    have hS0 : c * r ^ d ≤ ((GammaE om).measure (GE om fL2) (Metric.ball zc (r / 2))).toReal +
        c * (volume (Metric.ball zc (r / 2))).toReal := by
      rw [aux_lem_affine_gcn_competitor_ball_volume zc r hr]
      linarith only [ENNReal.toReal_nonneg (a := (GammaE om).measure (GE om fL2)
        (Metric.ball zc (r / 2)))]
    have hsrc' := (hsrcom hG f hf hmesh).trans
      (aux_affine_cell_assembly_source (d := d) r c (sE om) _ src0 hr hc hsEom hsrc0 hS0)
    exact affine_gap_cell d hd alpha beta gamma zeta rho ha Cin Lt epshom src0 heps hGCN
      (centeredCube Qcentre Qside hQside) (E om) (GammaE om) (GE om fL2) U hUc hUr zc zP r m L hr hm hRlo hRhi hpad hparentQ
      hwide hLt hLLt c (sE om) (sCmp om) hc hsEom hsCmpom (hratioom hG) _ Ctotal KP Cext hfsup
      hCtotal hKP hUh cq hnorm hharm (hPoincom hG fL2 U hUr) (hextom hG) hpar hCinC hCinE hCinP
      hsrc'
  · obtain ⟨U, hUc, hUr, hUb⟩ := hbankom f hf fL2 hfL2
    exact ⟨U, hUc, hUr, hUb, fun _ hG' => absurd hG' hG⟩

end Paper
