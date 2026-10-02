import SubdiffusiveProcess.Paper.lem_affine_gcn_competitor_l2
import SubdiffusiveProcess.Geometry.BallBetween
import SubdiffusiveProcess.Sobolev.NormalizedHolderPointwise
import SubdiffusiveProcess.AffineGap.ComparisonOscillationScalar
import SubdiffusiveProcess.Analysis.NormalizedMeanMinimizer

/-! Per-cell core of `lem_affine`: for one good cell, the candidate outputs (normalized Hölder
bound, harmonic comparison on the comparison window), the comparison-cube Poincaré bound, the
local trace extension and a small source feed `lem_affine_gcn_competitor_l2`, producing the
affine trace approximation `Λ ≤ ρ λ(q)`.  No probabilistic statement is made here. -/

open Filter MeasureTheory Set TopologicalSpace Matrix
open SubdiffusiveProcess SubdiffusiveProcess.Lane3
open SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open scoped ENNReal NNReal BigOperators Topology ContDiff

noncomputable section
namespace Paper

/-- The per-scale instance of `lem_affine_gcn_competitor_l2` once `L`, `epshom` and `src0`
are fixed. -/
def aux_affine_gap_cell_gcnInstance (d : ℕ) (alpha beta gamma zeta rho Cin L epshom src0 : ℝ) :
    Prop :=
    ∀ (Q : Opens (SpatialCoordinates d))
      (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
      (GammaE : DirichletForm.EnergyMeasure E)
      (u : DomainL2 Q) (U : SpatialCoordinates d → ℝ)
      (hUcont : ContinuousOn U (closure (Q : Set (SpatialCoordinates d))))
      (hUae : ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
        (Q : Set (SpatialCoordinates d))] U))
      (z : SpatialCoordinates d) (r R : ℝ) (hr : 0 < r)
      (hRlo : L ^ gamma * r ≤ R) (hRhi : R ≤ Cin * L ^ gamma * r)
      (hQR : Metric.ball z (R / 2) ⊆ (Q : Set (SpatialCoordinates d)))
      (c s : ℝ) (hc : 0 < c) (hs : 0 < s)
      (Os Src c0 : ℝ) (hOs0 : 0 ≤ Os) (hSrc0 : 0 ≤ Src),
      let q : Set (SpatialCoordinates d) := Metric.ball z (r / 2)
      let p : Set (SpatialCoordinates d) := Metric.ball z (3 * r / 2)
      let S : ℝ := (GammaE.measure u q).toReal + c * (volume q).toReal
      normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - c0) ≤ Os →
      Os ≤ Cin * R ^ ((2 - (d : ℝ)) / 2) * L ^ (((d : ℝ) + zeta) / 2) * Real.sqrt (S / s) →
      (∃ (R2 : ℝ) (hR2 : 0 < R2), R ≤ R2 ∧
        ∃ (Ubar : weakSobolevGraph (centeredCube z R2 hR2))
          (Vbar : SpatialCoordinates d → ℝ),
        ContinuousOn Vbar (closure (centeredCube z R2 hR2 : Set (SpatialCoordinates d))) ∧
        (((Ubar : SobolevData (centeredCube z R2 hR2)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R2 hR2 : Set (SpatialCoordinates d))] Vbar) ∧
        (∀ psi : killedSobolevGraph (centeredCube z R2 hR2),
          inner ℝ (sobolevGradient (Ubar : SobolevData (centeredCube z R2 hR2)))
            (subspaceGradient (killedSobolevGraph (centeredCube z R2 hR2)) psi) = 0) ∧
        normalizedL2On (Metric.ball z (R / 2)) (fun x => U x - Vbar x) ≤ epshom * Os + Src) →
      (∀ x ∈ closure q, ∀ y ∈ closure q,
        |U x - U y| ≤ Cin * (normalizedL2On p
          (fun x => U x - (volume.real p)⁻¹ * ∫ y in p, U y) + Src) * (dist x y / r) ^ alpha) →
      (∀ g : SpatialCoordinates d → ℝ,
        ContinuousOn g (closure (Q : Set (SpatialCoordinates d))) →
        Lane4.IsHolderOn beta (frontier q) g →
        ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
          v ∈ E.domain ∧
          ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
          ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (Q : Set (SpatialCoordinates d))] V) ∧
          (∀ x ∈ frontier q, V x = g x) ∧
          (GammaE.measure v q).toReal ≤
            Cin * s * r ^ ((d : ℝ) - 2) * (r ^ beta * Lane4.holderSeminorm beta (frontier q) g) ^ 2) →
      Src ≤ src0 * r ^ ((2 - (d : ℝ)) / 2) * Real.sqrt (S / s) →
      ∃ pc : (Fin d → ℝ) × ℝ,
        (let ell : SpatialCoordinates d → ℝ := fun x => (∑ i, pc.1 i * x i) + pc.2
         let b : SpatialCoordinates d → ℝ := fun x => U x - ell x
         let eSet : Set ℝ :=
           {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
               v ∈ E.domain ∧
               ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
               ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
                 (Q : Set (SpatialCoordinates d))] V) ∧
               (∀ x ∈ frontier q, V x = b x) ∧
               e = (GammaE.measure v q).toReal}
         ∃ Lambda : ℝ, IsGLB eSet Lambda ∧ eSet.Nonempty ∧ Lambda ≤ rho * S)
/-- The normalized oscillation on a concentric sub-ball is controlled by the one on the
cube `m` times the volume ratio. -/
theorem aux_affine_gap_cell_subball {d : ℕ} (z : SpatialCoordinates d) (m ρ c0 : ℝ)
    (hm : 0 < m) (hρ : 0 < ρ) (hρm : ρ ≤ m) (U : SpatialCoordinates d → ℝ)
    (hU : MemLp U 2 (volume.restrict (Metric.ball z (m / 2)))) :
    normalizedL2On (Metric.ball z (ρ / 2)) (fun x => U x - c0) ≤
      (m / ρ) ^ ((d : ℝ) / 2) * normalizedL2On (Metric.ball z (m / 2)) (fun x => U x - c0) := by
  have hsub : Metric.ball z (ρ / 2) ⊆ Metric.ball z (m / 2) :=
    Metric.ball_subset_ball (by linarith only [hρm])
  letI : IsFiniteMeasure (volume.restrict (Metric.ball z (m / 2))) := by
    change IsFiniteMeasure (volume.restrict (centeredCube z m hm : Set (SpatialCoordinates d)))
    infer_instance
  have h := Section6Iteration.normalizedL2On_le_of_subset hsub
    (by rw [aux_lem_affine_gcn_competitor_ball_volume z m hm]; positivity)
    (by rw [aux_lem_affine_gcn_competitor_ball_volume z ρ hρ]; positivity)
    (hU.sub (memLp_const c0)).integrable_sq
  rw [aux_lem_affine_gcn_competitor_volume_ratio z ρ m hρ hm] at h
  exact h

/-- The centered oscillation on the outer comparison window `B(z, m/18)` is at most
`729^{d/2}` times the oscillation on the comparison cube about its mean. -/
theorem aux_affine_gap_cell_outer {d : ℕ} (z : SpatialCoordinates d) (m c0 : ℝ) (hm : 0 < m)
    (U : SpatialCoordinates d → ℝ)
    (hU : MemLp U 2 (volume.restrict (centeredCube z m hm : Set (SpatialCoordinates d)))) :
    normalizedL2On (Metric.ball z (m / 18))
      (fun x => U x - (volume.real (Metric.ball z (m / 18)))⁻¹ *
        ∫ y in Metric.ball z (m / 18), U y) ≤
      (729 : ℝ) ^ ((d : ℝ) / 2) *
        normalizedL2On (centeredCube z m hm : Set (SpatialCoordinates d)) (fun x => U x - c0) := by
  have hm9 : 0 < m / 9 := by positivity
  have hball : Metric.ball z (m / 18) = Metric.ball z (m / 9 / 2) := by
    congr 1; ring
  have hsub : Metric.ball z (m / 18) ⊆ (centeredCube z m hm : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_ball (by linarith only [hm])
  have htop : volume (Metric.ball z (m / 18)) ≠ ⊤ := by
    rw [hball]
    change volume (centeredCube z (m / 9) hm9 : Set (SpatialCoordinates d)) ≠ ⊤
    rw [centeredCube_volume]; exact ENNReal.ofReal_ne_top
  have hUo : MemLp U 2 (volume.restrict (Metric.ball z (m / 18))) :=
    hU.mono_measure (Measure.restrict_mono hsub le_rfl)
  have h1 := normalizedL2On_sub_average_le_sub_const (Metric.ball z (m / 18)) htop U hUo c0
  have h2 := aux_affine_gap_cell_subball z m (m / 9) c0 hm hm9 (by linarith only [hm]) U hU
  rw [← hball] at h2
  have hratio : m / (m / 9) = 9 := by field_simp
  rw [hratio] at h2
  have h9 : (9 : ℝ) ^ ((d : ℝ) / 2) ≤ 729 ^ ((d : ℝ) / 2) :=
    Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity)
  have hN0 := Section6Iteration.normalizedL2On_nonneg
    (centeredCube z m hm : Set (SpatialCoordinates d)) (fun x => U x - c0)
  exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right h9 hN0))

/-- Enlarging the constant of a local trace-extension bound. -/
theorem aux_affine_gap_cell_ext_mono {d : ℕ} (Q : Opens (SpatialCoordinates d))
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E) (q : Set (SpatialCoordinates d))
    (beta r s Cext Cin : ℝ) (hr : 0 < r) (hs : 0 < s) (hC : Cext ≤ Cin)
    (hext : ∀ g : SpatialCoordinates d → ℝ,
        ContinuousOn g (closure (Q : Set (SpatialCoordinates d))) →
        Lane4.IsHolderOn beta (frontier q) g →
        ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
          v ∈ E.domain ∧
          ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
          ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (Q : Set (SpatialCoordinates d))] V) ∧
          (∀ x ∈ frontier q, V x = g x) ∧
          (GammaE.measure v q).toReal ≤
            Cext * s * r ^ ((d : ℝ) - 2) * (r ^ beta * Lane4.holderSeminorm beta (frontier q) g) ^ 2) :
    ∀ g : SpatialCoordinates d → ℝ,
      ContinuousOn g (closure (Q : Set (SpatialCoordinates d))) →
      Lane4.IsHolderOn beta (frontier q) g →
      ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
        v ∈ E.domain ∧
        ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
        ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (Q : Set (SpatialCoordinates d))] V) ∧
        (∀ x ∈ frontier q, V x = g x) ∧
        (GammaE.measure v q).toReal ≤
          Cin * s * r ^ ((d : ℝ) - 2) * (r ^ beta * Lane4.holderSeminorm beta (frontier q) g) ^ 2 := by
  intro g hg hgH
  obtain ⟨v, V, hv, hVc, hvV, hVb, hbound⟩ := hext g hg hgH
  refine ⟨v, V, hv, hVc, hvV, hVb, hbound.trans ?_⟩
  have hX : 0 ≤ s * r ^ ((d : ℝ) - 2) *
      (r ^ beta * Lane4.holderSeminorm beta (frontier q) g) ^ 2 := by positivity
  calc Cext * s * r ^ ((d : ℝ) - 2) * (r ^ beta * Lane4.holderSeminorm beta (frontier q) g) ^ 2
      = Cext * (s * r ^ ((d : ℝ) - 2) *
        (r ^ beta * Lane4.holderSeminorm beta (frontier q) g) ^ 2) := by ring
    _ ≤ Cin * (s * r ^ ((d : ℝ) - 2) *
        (r ^ beta * Lane4.holderSeminorm beta (frontier q) g) ^ 2) :=
        mul_le_mul_of_nonneg_right hC hX
    _ = _ := by ring

/-- The normalized `C^α` bound of the candidate estimate gives the `q`-scale Hölder premise of
the `L²` competitor lemma. -/
theorem aux_affine_gap_cell_holder {d : ℕ} (alpha : ℝ) (ha : 0 < alpha)
    (z : SpatialCoordinates d) (r cq Ctotal Cin a Src : ℝ) (hr : 0 < r)
    (U : SpatialCoordinates d → ℝ) (hCtotal : 0 ≤ Ctotal) (ha0 : 0 ≤ a) (haS : a ≤ Src)
    (hCinC : Real.sqrt d ^ alpha * Ctotal ≤ Cin)
    (hHolU : Lane4.IsHolderOn alpha (closure (Metric.ball z (r / 2))) U)
    (hnorm : Lane4.cAlphaNorm alpha
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => U (z + r • x) - cq) ≤
        Ctotal * (normalizedL2On (Metric.ball z (3 * r / 2))
          (fun x => U x - (volume.real (Metric.ball z (3 * r / 2)))⁻¹ *
            ∫ y in Metric.ball z (3 * r / 2), U y) + a)) :
    ∀ x ∈ closure (Metric.ball z (r / 2)), ∀ y ∈ closure (Metric.ball z (r / 2)),
      |U x - U y| ≤ Cin * (normalizedL2On (Metric.ball z (3 * r / 2))
        (fun x => U x - (volume.real (Metric.ball z (3 * r / 2)))⁻¹ *
          ∫ y in Metric.ball z (3 * r / 2), U y) + Src) * (dist x y / r) ^ alpha := by
  intro x hx y hy
  have h := abs_sub_le_of_normalized_cAlphaNorm alpha ha z r cq _ hr U hHolU hnorm x hx y hy
  set Np : ℝ := normalizedL2On (Metric.ball z (3 * r / 2))
    (fun x => U x - (volume.real (Metric.ball z (3 * r / 2)))⁻¹ *
      ∫ y in Metric.ball z (3 * r / 2), U y) with hNpdef
  have hNp : 0 ≤ Np := Section6Iteration.normalizedL2On_nonneg _ _
  have ht : 0 ≤ (dist x y / r) ^ alpha := by positivity
  have hsd : 0 ≤ Real.sqrt d ^ alpha * Ctotal := by positivity
  calc |U x - U y| ≤ Real.sqrt d ^ alpha * (Ctotal * (Np + a)) * (dist x y / r) ^ alpha := h
    _ = (Real.sqrt d ^ alpha * Ctotal) * (Np + a) * (dist x y / r) ^ alpha := by ring
    _ ≤ Cin * (Np + Src) * (dist x y / r) ^ alpha := by
        apply mul_le_mul_of_nonneg_right _ ht
        exact mul_le_mul hCinC (by linarith only [haS]) (by positivity) (le_trans hsd hCinC)

/-- Per-cell affine trace approximation from the candidate outputs on one good cell. -/
theorem affine_gap_cell
    (d : ℕ) (hd : 2 ≤ d) [NeZero d]
    (alpha beta gamma zeta rho : ℝ) (ha : 0 < alpha)
    (Cin Lt epshom src0 : ℝ) (heps : 0 ≤ epshom)
    (hGCN : aux_affine_gap_cell_gcnInstance d alpha beta gamma zeta rho Cin Lt epshom src0)
    (Q : Opens (SpatialCoordinates d))
    (E : DirichletForm.ClosedForm (volume.restrict (Q : Set (SpatialCoordinates d))))
    (GammaE : DirichletForm.EnergyMeasure E)
    (u : DomainL2 Q) (U : SpatialCoordinates d → ℝ)
    (hUcont : ContinuousOn U (closure (Q : Set (SpatialCoordinates d))))
    (hUae : ((u : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
      (Q : Set (SpatialCoordinates d))] U))
    (z zP : SpatialCoordinates d) (r cmpSide L : ℝ) (hr : 0 < r) (hcmp : 0 < cmpSide)
    (hRlo : Lt ^ gamma * r ≤ cmpSide / 729) (hRhi : cmpSide / 729 ≤ Cin * Lt ^ gamma * r)
    (hpad : Metric.closedBall z (cmpSide / 2) ⊆ Metric.ball zP (L * r / 2))
    (hparentQ : Metric.ball zP (L * r / 2) ⊆ (Q : Set (SpatialCoordinates d)))
    (hwide : 27 * cmpSide ≤ L * r) (hLt : 0 < Lt) (hLLt : Lt ≤ L)
    (c s sCmp : ℝ) (hc : 0 < c) (hs : 0 < s) (hsCmp : 0 < sCmp) (hratio : sCmp⁻¹ ≤ 2 * s⁻¹)
    (fsup Ctotal KP Cext : ℝ) (hfsup : 0 ≤ fsup) (hCtotal : 0 ≤ Ctotal) (hKP : 0 ≤ KP)
    (hHolU : Lane4.IsHolderOn alpha (closure (Metric.ball z (r / 2))) U)
    (cq : ℝ)
    (hnorm : Lane4.cAlphaNorm alpha
      (closedCube (0 : SpatialCoordinates d) 1 one_pos : Set (SpatialCoordinates d))
      (fun x => U (z + r • x) - cq) ≤
        Ctotal * (normalizedL2On (Metric.ball z (3 * r / 2))
          (fun x => U x - (volume.real (Metric.ball z (3 * r / 2)))⁻¹ *
            ∫ y in Metric.ball z (3 * r / 2), U y) + r ^ 2 * s⁻¹ * fsup))
    (hharmCGE : ∀ w : SpatialCoordinates d,
      Metric.closedBall z (cmpSide / 18) ⊆ Metric.ball w (27 * cmpSide / 2) →
      Metric.ball w (27 * cmpSide / 2) ⊆ (Q : Set (SpatialCoordinates d)) →
      ∃ (v : weakSobolevGraph (centeredCube z (cmpSide / 81) (div_pos hcmp (by norm_num))))
        (V : SpatialCoordinates d → ℝ),
        ContinuousOn V (closure (centeredCube z (cmpSide / 81) (div_pos hcmp (by norm_num)) :
          Set (SpatialCoordinates d))) ∧
        (((v : SobolevData (centeredCube z (cmpSide / 81) (div_pos hcmp (by norm_num)))).1 :
            SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube z (cmpSide / 81) (div_pos hcmp (by norm_num)) :
            Set (SpatialCoordinates d))] V) ∧
        (∀ x ∈ frontier (centeredCube z (cmpSide / 81) (div_pos hcmp (by norm_num)) :
          Set (SpatialCoordinates d)), V x = U x) ∧
        (∀ psi : killedSobolevGraph (centeredCube z (cmpSide / 81) (div_pos hcmp (by norm_num))),
          inner ℝ (sobolevGradient
            (v : SobolevData (centeredCube z (cmpSide / 81) (div_pos hcmp (by norm_num)))))
            (subspaceGradient (killedSobolevGraph
              (centeredCube z (cmpSide / 81) (div_pos hcmp (by norm_num)))) psi) = 0) ∧
        normalizedL2On (Metric.ball z (cmpSide / 1458)) (fun x => U x - V x) ≤
          epshom * normalizedL2On (Metric.ball z (cmpSide / 18))
            (fun x => U x - (volume.real (Metric.ball z (cmpSide / 18)))⁻¹ *
              ∫ y in Metric.ball z (cmpSide / 18), U y) +
          Ctotal * (cmpSide / 9) ^ 2 * sCmp⁻¹ * fsup)
    (hPoinc : (normalizedL2On (centeredCube z cmpSide hcmp : Set (SpatialCoordinates d))
        (fun x => U x - (volume.real (centeredCube z cmpSide hcmp : Set (SpatialCoordinates d)))⁻¹ *
          ∫ y in (centeredCube z cmpSide hcmp : Set (SpatialCoordinates d)), U y)) ^ 2 ≤
      (KP * cmpSide ^ 2 / volume.real (centeredCube z cmpSide hcmp : Set (SpatialCoordinates d))) *
        sCmp⁻¹ * (GammaE.measure u (Metric.ball zP (L * r / 2))).toReal)
    (hext : ∀ g : SpatialCoordinates d → ℝ,
        ContinuousOn g (closure (Q : Set (SpatialCoordinates d))) →
        Lane4.IsHolderOn beta (frontier (Metric.ball z (r / 2))) g →
        ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
          v ∈ E.domain ∧
          ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
          ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
            (Q : Set (SpatialCoordinates d))] V) ∧
          (∀ x ∈ frontier (Metric.ball z (r / 2)), V x = g x) ∧
          (GammaE.measure v (Metric.ball z (r / 2))).toReal ≤
            Cext * s * r ^ ((d : ℝ) - 2) * (r ^ beta * Lane4.holderSeminorm beta
              (frontier (Metric.ball z (r / 2))) g) ^ 2)
    (hpar : (GammaE.measure u (Metric.ball zP (L * r / 2))).toReal +
        c * (volume (Metric.ball zP (L * r / 2))).toReal ≤
      L ^ ((d : ℝ) + zeta) * ((GammaE.measure u (Metric.ball z (r / 2))).toReal +
        c * (volume (Metric.ball z (r / 2))).toReal))
    (hCinC : Real.sqrt d ^ alpha * Ctotal ≤ Cin) (hCinE : Cext ≤ Cin)
    (hCinP : 729 * Real.sqrt (2 * KP) * (L / Lt) ^ (((d : ℝ) + zeta) / 2) ≤ Cin)
    (hSrc : Ctotal * (cmpSide / 9) ^ 2 * sCmp⁻¹ * fsup + r ^ 2 * s⁻¹ * fsup ≤
      src0 * r ^ ((2 - (d : ℝ)) / 2) *
        Real.sqrt (((GammaE.measure u (Metric.ball z (r / 2))).toReal +
          c * (volume (Metric.ball z (r / 2))).toReal) / s)) :
    ∃ pc : (Fin d → ℝ) × ℝ,
      (let ell : SpatialCoordinates d → ℝ := fun x => (∑ i, pc.1 i * x i) + pc.2
       let b : SpatialCoordinates d → ℝ := fun x => U x - ell x
       let eSet : Set ℝ :=
         {e : ℝ | ∃ (v : DomainL2 Q) (V : SpatialCoordinates d → ℝ),
             v ∈ E.domain ∧
             ContinuousOn V (closure (Q : Set (SpatialCoordinates d))) ∧
             ((v : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
               (Q : Set (SpatialCoordinates d))] V) ∧
             (∀ x ∈ frontier (Metric.ball z (r / 2)), V x = b x) ∧
             e = (GammaE.measure v (Metric.ball z (r / 2))).toReal}
       ∃ Lambda : ℝ, IsGLB eSet Lambda ∧ eSet.Nonempty ∧
         Lambda ≤ rho * ((GammaE.measure u (Metric.ball z (r / 2))).toReal +
           c * (volume (Metric.ball z (r / 2))).toReal)) := by
  have hR : 0 < cmpSide / 729 := by positivity
  obtain ⟨w, hw1, hw2⟩ := SubdiffusiveProcess.exists_ball_between (E := SpatialCoordinates d)
    (z := z) (p := zP) (c := cmpSide) (P := L * r / 2) hcmp hpad (by linarith only [hwide])
  obtain ⟨v, V, hVc, hvV, hVb, hEq, herrCGE⟩ := hharmCGE w hw1 (hw2.trans hparentQ)
  have hcmpQ : (centeredCube z cmpSide hcmp : Set (SpatialCoordinates d)) ⊆
      (Q : Set (SpatialCoordinates d)) :=
    Metric.ball_subset_closedBall.trans (hpad.trans hparentQ)
  have hUQ : MemLp U 2 (volume.restrict (Q : Set (SpatialCoordinates d))) :=
    (Lp.memLp u).ae_eq hUae
  have hUcmp : MemLp U 2 (volume.restrict
      (centeredCube z cmpSide hcmp : Set (SpatialCoordinates d))) :=
    hUQ.mono_measure (Measure.restrict_mono hcmpQ le_rfl)
  let c0 : ℝ := (volume.real (centeredCube z cmpSide hcmp : Set (SpatialCoordinates d)))⁻¹ *
    ∫ y in (centeredCube z cmpSide hcmp : Set (SpatialCoordinates d)), U y
  let Ncmp : ℝ := normalizedL2On (centeredCube z cmpSide hcmp : Set (SpatialCoordinates d))
    (fun x => U x - c0)
  let Os : ℝ := (729 : ℝ) ^ ((d : ℝ) / 2) * Ncmp
  let Src : ℝ := Ctotal * (cmpSide / 9) ^ 2 * sCmp⁻¹ * fsup + r ^ 2 * s⁻¹ * fsup
  have hN0 : 0 ≤ Ncmp := Section6Iteration.normalizedL2On_nonneg _ _
  have hOs0 : 0 ≤ Os := by positivity
  have hSrc0 : 0 ≤ Src := by positivity
  have hQR : Metric.ball z (cmpSide / 729 / 2) ⊆ (Q : Set (SpatialCoordinates d)) :=
    (Metric.ball_subset_ball (by linarith only [hcmp])).trans hcmpQ
  have hosc : normalizedL2On (Metric.ball z (cmpSide / 729 / 2)) (fun x => U x - c0) ≤ Os := by
    have h := aux_affine_gap_cell_subball z cmpSide (cmpSide / 729) c0 hcmp hR
      (by linarith only [hcmp]) U hUcmp
    have hratio : cmpSide / (cmpSide / 729) = 729 := by field_simp
    rw [hratio] at h
    exact h
  have hS0 : 0 ≤ (GammaE.measure u (Metric.ball z (r / 2))).toReal +
      c * (volume (Metric.ball z (r / 2))).toReal := by positivity
  have hGam : (GammaE.measure u (Metric.ball zP (L * r / 2))).toReal ≤
      L ^ ((d : ℝ) + zeta) * ((GammaE.measure u (Metric.ball z (r / 2))).toReal +
        c * (volume (Metric.ball z (r / 2))).toReal) := by
    have hcv : 0 ≤ c * (volume (Metric.ball zP (L * r / 2))).toReal := by positivity
    linarith only [hpar, hcv]
  have hN : Ncmp ^ 2 ≤ (KP * cmpSide ^ 2 / cmpSide ^ d) * sCmp⁻¹ *
      (GammaE.measure u (Metric.ball zP (L * r / 2))).toReal := by
    have hvol := centeredCube_volume_real z hcmp
    calc Ncmp ^ 2 ≤ (KP * cmpSide ^ 2 /
          volume.real (centeredCube z cmpSide hcmp : Set (SpatialCoordinates d))) * sCmp⁻¹ *
          (GammaE.measure u (Metric.ball zP (L * r / 2))).toReal := hPoinc
      _ = _ := by rw [hvol]
  have hOs : Os ≤ Cin * (cmpSide / 729) ^ ((2 - (d : ℝ)) / 2) * Lt ^ (((d : ℝ) + zeta) / 2) *
      Real.sqrt (((GammaE.measure u (Metric.ball z (r / 2))).toReal +
        c * (volume (Metric.ball z (r / 2))).toReal) / s) :=
    comparison_oscillation_scalar d Ncmp KP cmpSide (cmpSide / 729) L Lt zeta Cin _ s sCmp _
      hR (by ring) hKP hs hratio hS0 ENNReal.toReal_nonneg hGam hLt hLLt hN0 hN hCinP
  have hqo := aux_affine_gap_cell_outer z cmpSide c0 hcmp U hUcmp
  have hball : Metric.ball z (cmpSide / 729 / 2) = Metric.ball z (cmpSide / 1458) := by
    congr 1; ring
  have herr : normalizedL2On (Metric.ball z (cmpSide / 729 / 2)) (fun x => U x - V x) ≤
      epshom * Os + Src := by
    rw [hball]
    refine herrCGE.trans (add_le_add (mul_le_mul_of_nonneg_left hqo heps) ?_)
    have : 0 ≤ r ^ 2 * s⁻¹ * fsup := by positivity
    show Ctotal * (cmpSide / 9) ^ 2 * sCmp⁻¹ * fsup ≤
      Ctotal * (cmpSide / 9) ^ 2 * sCmp⁻¹ * fsup + r ^ 2 * s⁻¹ * fsup
    linarith only [this]
  have hharm : ∃ (R2 : ℝ) (hR2 : 0 < R2), cmpSide / 729 ≤ R2 ∧
      ∃ (Ubar : weakSobolevGraph (centeredCube z R2 hR2)) (Vbar : SpatialCoordinates d → ℝ),
        ContinuousOn Vbar (closure (centeredCube z R2 hR2 : Set (SpatialCoordinates d))) ∧
        (((Ubar : SobolevData (centeredCube z R2 hR2)).1 : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (centeredCube z R2 hR2 : Set (SpatialCoordinates d))] Vbar) ∧
        (∀ psi : killedSobolevGraph (centeredCube z R2 hR2),
          inner ℝ (sobolevGradient (Ubar : SobolevData (centeredCube z R2 hR2)))
            (subspaceGradient (killedSobolevGraph (centeredCube z R2 hR2)) psi) = 0) ∧
        normalizedL2On (Metric.ball z (cmpSide / 729 / 2)) (fun x => U x - Vbar x) ≤
          epshom * Os + Src :=
    ⟨cmpSide / 81, div_pos hcmp (by norm_num), by linarith only [hcmp], v, V, hVc, hvV, hEq, herr⟩
  have hsrcle : r ^ 2 * s⁻¹ * fsup ≤ Src := by
    have : 0 ≤ Ctotal * (cmpSide / 9) ^ 2 * sCmp⁻¹ * fsup := by positivity
    show r ^ 2 * s⁻¹ * fsup ≤ Ctotal * (cmpSide / 9) ^ 2 * sCmp⁻¹ * fsup + r ^ 2 * s⁻¹ * fsup
    linarith only [this]
  have hHolq := aux_affine_gap_cell_holder alpha ha z r cq Ctotal Cin (r ^ 2 * s⁻¹ * fsup) Src hr U
    hCtotal (by positivity) hsrcle hCinC hHolU hnorm
  have hext' := aux_affine_gap_cell_ext_mono Q E GammaE (Metric.ball z (r / 2)) beta r s Cext Cin
    hr hs hCinE hext
  exact hGCN Q E GammaE u U hUcont hUae z r (cmpSide / 729) hr hRlo hRhi hQR c s hc hs
    Os Src c0 hOs0 hSrc0 hosc hOs hharm hHolq hext' hSrc

end Paper
