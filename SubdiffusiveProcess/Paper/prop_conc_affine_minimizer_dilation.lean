module

public import SubdiffusiveProcess.Paper.prop_conc_affine_cutoff_growth
public import SubdiffusiveProcess.Paper.lem_as_regularity_affine_transport
public import SubdiffusiveProcess.Paper.lane4_weak_gradient_chain_rule
public import SubdiffusiveProcess.Paper.lane4_dilation_quasi_measure_preserving
public import SubdiffusiveProcess.Lane4.CubeDilation
public import SubdiffusiveProcess.Sobolev.AffineResponses
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology BigOperators

/-! Level-cell / unit-cell transport of the canonical affine Dirichlet minimizer.
For a coefficient `a` on the cube of side `r` about `z` and `b` on the unit cube, tied by
`a ∘ T = lam * b` (`T = cubeDilation z 0 r`), the affine minimizers correspond by `u ∘ T`,
the minimal energy scales by `r ^ d * lam`, and the finite energy measure of the level-cell
minimizer is `ofReal (r ^ d * lam)` times the pullback of the unit-cell measure.
Deterministic; no probability, no cutoff, no limit. -/

namespace Paper
noncomputable section

theorem aux_prop_conc_affine_minimizer_dilation_integral {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (h1 : (0 : ℝ) < 1) (f : SpatialCoordinates d → ℝ) :
    (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)), f x) =
      r ^ d * ∫ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
        f (cubeDilation z 0 r x) := by
  have hcoe : ⇑(cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne') = cubeDilation z 0 r := rfl
  have h := integral_map_equiv
    (μ := volume.restrict (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)))
    (e := cubeDilationEquiv z (0 : SpatialCoordinates d) hr.ne') (f := f)
  rw [hcoe, map_cubeDilation_restrict z 0 hr h1] at h
  have hcoef : (ENNReal.ofReal |(r ^ d)⁻¹|).toReal = (r ^ d)⁻¹ := by
    rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr (pow_pos hr d))]
  rw [integral_smul_measure, hcoef, smul_eq_mul] at h
  rw [← h, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hr.ne'), one_mul]


theorem aux_prop_conc_affine_minimizer_dilation_datum_grad {d : ℕ} {Ω : Opens (SpatialCoordinates d)}
    [IsFiniteMeasure (volume.restrict (Ω : Set (SpatialCoordinates d)))]
    (hΩ : Bornology.IsBounded (Ω : Set (SpatialCoordinates d))) (p : Fin d → ℝ) (i : Fin d) :
    ((sobolevGradient ((affineSobolev hΩ p 0 : weakSobolevGraph Ω) : SobolevData Ω) i : DomainL2 Ω) :
        SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set (SpatialCoordinates d))]
      fun _ => p i := by
  exact domainConstantL2_coeFn (Ω := Ω) (p i)

/-- The unit-cell affine minimizer of the dilated coefficient has the dilated gradient. -/
theorem aux_prop_conc_affine_minimizer_dilation_grad {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (h1 : (0 : ℝ) < 1)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (lam : ℝ) (hlam : 0 < lam)
    (hab : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      a.val (cubeDilation z 0 r x) = lam * b.val x)
    (hPq : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (hP0 : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1),
      ‖(u : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1)) u‖)
    (p : Fin d → ℝ) (i : Fin d) :
    ∀ᵐ y ∂volume.restrict
        (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      sobolevGradient (dirichletMinimizer (killedResponseSpace hP0) b
          (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) h1) p 0) :
          SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) i y =
        sobolevGradient (dirichletMinimizer (killedResponseSpace hPq) a
          (affineSobolev (centeredCube_isBounded z hr) p 0) :
          SobolevData (centeredCube z r hr)) i (cubeDilation z 0 r y) := by
  classical
  have hq := lane4_dilation_quasi_measure_preserving d z (0 : SpatialCoordinates d) r hr h1
  -- the level-cell minimizer and its datum
  let lq : weakSobolevGraph (centeredCube z r hr) :=
    affineSobolev (centeredCube_isBounded z hr) p 0
  let l0 : weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1) :=
    affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) h1) p 0
  let u := dirichletMinimizer (killedResponseSpace hPq) a lq
  let ut := dirichletMinimizer (killedResponseSpace hP0) b l0
  -- killed part of the level minimizer, pulled back to the unit cell
  let v : killedSobolevGraph (centeredCube z r hr) :=
    ⟨u.val - lq.val, dirichletMinimizer_mem_affine (killedResponseSpace hPq) a lq⟩
  obtain ⟨wv, hwv_val, hwv_grad⟩ :=
    aux_lem_as_regularity_affine_transport_killed_pullback d z (0 : SpatialCoordinates d) r hr h1 v
  -- a.e. gradient identity `ut'.2 i y = u.2 i (T y)` for the candidate
  let ut' : weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1) :=
    ⟨r⁻¹ • wv.val + l0.val, (weakSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1)).add_mem
      ((weakSobolevGraph _).smul_mem _ (killedSobolevGraph_le_weakSobolevGraph wv.property))
      l0.property⟩
  have hgradu : ∀ j : Fin d, ∀ᵐ y ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      (ut'.val.2 j : SpatialCoordinates d → ℝ) y =
        (u.val.2 j : SpatialCoordinates d → ℝ) (cubeDilation z 0 r y) := by
    intro j
    have hdat_q := aux_prop_conc_affine_minimizer_dilation_datum_grad
      (centeredCube_isBounded z hr) p j
    have hdat_0 := aux_prop_conc_affine_minimizer_dilation_datum_grad
      (centeredCube_isBounded (0 : SpatialCoordinates d) h1) p j
    have hvsub : ∀ᵐ x ∂volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)),
        (v.val.2 j : SpatialCoordinates d → ℝ) x =
          (u.val.2 j : SpatialCoordinates d → ℝ) x - (lq.val.2 j : SpatialCoordinates d → ℝ) x := by
      have h := Lp.coeFn_sub (u.val.2 j) (lq.val.2 j)
      filter_upwards [h] with x hx
      simpa [v] using hx
    filter_upwards [hq.ae hvsub, hq.ae hdat_q, hwv_grad j, Lp.coeFn_add (r⁻¹ • wv.val.2 j) (l0.val.2 j),
      Lp.coeFn_smul r⁻¹ (wv.val.2 j), hdat_0] with y h1' h2' h3' h4' h5' h6'
    have e1 : (ut'.val.2 j : SpatialCoordinates d → ℝ) y =
        r⁻¹ * (wv.val.2 j : SpatialCoordinates d → ℝ) y + p j := by
      have : (ut'.val.2 j) = (r⁻¹ • wv.val.2 j) + l0.val.2 j := rfl
      rw [this, h4', Pi.add_apply, h5', Pi.smul_apply, smul_eq_mul]
      congr 1
    rw [e1, h3']
    have hr0 : r ≠ 0 := hr.ne'
    have h2'' : (lq.val.2 j : SpatialCoordinates d → ℝ) (cubeDilation z 0 r y) = p j := h2'
    rw [h1', h2'']
    field_simp
    ring
  have hut' : ut' = ut := by
    apply dirichletMinimizer_eq_of_euler (killedResponseSpace hP0) b l0 ut'
    · have hsub : ut'.val - l0.val = r⁻¹ • wv.val := by
        change r⁻¹ • wv.val + l0.val - l0.val = r⁻¹ • wv.val
        abel
      rw [hsub]
      exact Submodule.smul_mem _ _ wv.property
    · intro ψ
      obtain ⟨ψq, hψq⟩ := aux_lem_as_regularity_affine_transport_killed_pushforward d z
        (0 : SpatialCoordinates d) r hr h1 ψ
      have hψgrad := lane4_weak_gradient_chain_rule d z (0 : SpatialCoordinates d) r hr h1
        ψq.val ψ.val (killedSobolevGraph_le_weakSobolevGraph ψq.property)
        (killedSobolevGraph_le_weakSobolevGraph ψ.property) hψq
      have hE := dirichletMinimizer_euler (killedResponseSpace hPq) a lq ψq
      rw [sobolevCoefficientForm_apply] at hE
      have hterm : ∀ j : Fin d,
          (∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
            a.val x * ((u.val.2 j : SpatialCoordinates d → ℝ) x *
              (ψq.val.2 j : SpatialCoordinates d → ℝ) x)) =
          (r ^ d * (lam * r⁻¹)) * ∫ y in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
              Set (SpatialCoordinates d)),
            b.val y * ((ut'.val.2 j : SpatialCoordinates d → ℝ) y *
              (ψ.val.2 j : SpatialCoordinates d → ℝ) y) := by
        intro j
        rw [aux_prop_conc_affine_minimizer_dilation_integral z r hr h1, mul_assoc]
        congr 1
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hab, hgradu j, hψgrad j] with y hy1 hy2 hy3
        have hy3' : (ψ.val.2 j : SpatialCoordinates d → ℝ) y =
            r * (ψq.val.2 j : SpatialCoordinates d → ℝ) (cubeDilation z 0 r y) := hy3
        rw [hy1, ← hy2, hy3']
        have hr0 : r ≠ 0 := hr.ne'
        field_simp
      have hsum : sobolevCoefficientForm b ut'.val ψ.val =
          ∑ j : Fin d, ∫ y in (centeredCube (0 : SpatialCoordinates d) 1 h1 :
              Set (SpatialCoordinates d)),
            b.val y * ((ut'.val.2 j : SpatialCoordinates d → ℝ) y *
              (ψ.val.2 j : SpatialCoordinates d → ℝ) y) :=
        sobolevCoefficientForm_apply b ut'.val ψ.val
      have hE' : ∑ j : Fin d, ∫ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          a.val x * ((u.val.2 j : SpatialCoordinates d → ℝ) x *
            (ψq.val.2 j : SpatialCoordinates d → ℝ) x) = 0 := hE
      rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, ← hsum] at hE'
      have hne : r ^ d * (lam * r⁻¹) ≠ 0 := by
        have := hr.ne'
        positivity
      exact (mul_eq_zero.mp hE').resolve_left hne
  have hgrad_i : ∀ᵐ y ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      sobolevGradient (ut : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) i y =
        sobolevGradient (u : SobolevData (centeredCube z r hr)) i (cubeDilation z 0 r y) := by
    filter_upwards [hgradu i] with y hy
    rw [← hut']
    exact hy
  exact hgrad_i


/-- The affine response of the level cell is `r^d lam` times the unit-cell response. -/
theorem aux_prop_conc_affine_minimizer_dilation_response {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (h1 : (0 : ℝ) < 1)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (lam : ℝ) (hlam : 0 < lam)
    (hab : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      a.val (cubeDilation z 0 r x) = lam * b.val x)
    (hPq : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (hP0 : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1),
      ‖(u : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1)) u‖)
    (p : Fin d → ℝ) :
    affineDirichletResponse (centeredCube_isBounded z hr) hPq a p =
      r ^ d * lam * affineDirichletResponse
        (centeredCube_isBounded (0 : SpatialCoordinates d) h1) hP0 b p := by
  classical
  let u := dirichletMinimizer (killedResponseSpace hPq) a
    (affineSobolev (centeredCube_isBounded z hr) p 0)
  let ut := dirichletMinimizer (killedResponseSpace hP0) b
    (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) h1) p 0)
  have hu : affineDirichletResponse (centeredCube_isBounded z hr) hPq a p =
      sobolevCoefficientForm a u.val u.val := rfl
  have hut : affineDirichletResponse (centeredCube_isBounded (0 : SpatialCoordinates d) h1) hP0 b p =
      sobolevCoefficientForm b ut.val ut.val := rfl
  rw [hu, hut, sobolevCoefficientForm_apply, sobolevCoefficientForm_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [aux_prop_conc_affine_minimizer_dilation_integral z r hr h1, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hab, aux_prop_conc_affine_minimizer_dilation_grad z r hr h1 a b lam hlam hab hPq
    hP0 p j] with y hy1 hy2
  have hy2' : (ut.val.2 j : SpatialCoordinates d → ℝ) y =
      (u.val.2 j : SpatialCoordinates d → ℝ) (cubeDilation z 0 r y) := hy2
  rw [hy1, ← hy2']
  ring

/-- The energy measure of the level-cell affine minimizer is the dilated unit-cell measure. -/
theorem aux_prop_conc_affine_minimizer_dilation_measure {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (h1 : (0 : ℝ) < 1)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (lam : ℝ) (hlam : 0 < lam)
    (hab : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      a.val (cubeDilation z 0 r x) = lam * b.val x)
    (hPq : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (hP0 : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1),
      ‖(u : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1)) u‖)
    (p : Fin d → ℝ) (S : Set (SpatialCoordinates d)) (hS : MeasurableSet S) :
    aux_prop_conc_affine_cutoff_growth_measure (centeredCube_isBounded z hr) hPq a p S =
      ENNReal.ofReal (r ^ d * lam) *
        aux_prop_conc_affine_cutoff_growth_measure
          (centeredCube_isBounded (0 : SpatialCoordinates d) h1) hP0 b p
          (cubeDilation z 0 r ⁻¹' S) := by
  classical
  let u := dirichletMinimizer (killedResponseSpace hPq) a
    (affineSobolev (centeredCube_isBounded z hr) p 0)
  let ut := dirichletMinimizer (killedResponseSpace hP0) b
    (affineSobolev (centeredCube_isBounded (0 : SpatialCoordinates d) h1) p 0)
  let fa : SpatialCoordinates d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (∑ j : Fin d, a.val x * ((sobolevGradient (u : SobolevData (centeredCube z r hr))) j x) ^ 2)
  let fb : SpatialCoordinates d → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (∑ j : Fin d, b.val x *
      ((sobolevGradient (ut : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))) j x) ^ 2)
  have hTm : Measurable (cubeDilation z (0 : SpatialCoordinates d) r) :=
    (continuous_cubeDilation z 0 r).measurable
  have hS' : MeasurableSet (cubeDilation z (0 : SpatialCoordinates d) r ⁻¹' S) := hTm hS
  have hma : aux_prop_conc_affine_cutoff_growth_measure (centeredCube_isBounded z hr) hPq a p S =
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), S.indicator fa x := by
    unfold aux_prop_conc_affine_cutoff_growth_measure
    rw [withDensity_apply _ hS, ← lintegral_indicator hS]
  have hmb : aux_prop_conc_affine_cutoff_growth_measure
      (centeredCube_isBounded (0 : SpatialCoordinates d) h1) hP0 b p
        (cubeDilation z 0 r ⁻¹' S) =
      ∫⁻ x in (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
        (cubeDilation z 0 r ⁻¹' S).indicator fb x := by
    unfold aux_prop_conc_affine_cutoff_growth_measure
    rw [withDensity_apply _ hS', ← lintegral_indicator hS']
  rw [hma, hmb, lintegral_centeredCube_cubeDilation z (0 : SpatialCoordinates d) hr h1]
  have hgradall : ∀ᵐ y ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      ∀ j : Fin d, sobolevGradient (ut : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)) j y =
        sobolevGradient (u : SobolevData (centeredCube z r hr)) j (cubeDilation z 0 r y) :=
    ae_all_iff.mpr fun j =>
      aux_prop_conc_affine_minimizer_dilation_grad z r hr h1 a b lam hlam hab hPq hP0 p j
  have hpt : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      S.indicator fa (cubeDilation z 0 r x) =
        ENNReal.ofReal lam * (cubeDilation z 0 r ⁻¹' S).indicator fb x := by
    filter_upwards [hab, hgradall] with x hx1 hx2
    by_cases hxS : cubeDilation z (0 : SpatialCoordinates d) r x ∈ S
    · have hxS' : x ∈ cubeDilation z (0 : SpatialCoordinates d) r ⁻¹' S := hxS
      rw [Set.indicator_of_mem hxS, Set.indicator_of_mem hxS']
      change ENNReal.ofReal (∑ j : Fin d, a.val (cubeDilation z 0 r x) *
        ((sobolevGradient (u : SobolevData (centeredCube z r hr))) j (cubeDilation z 0 r x)) ^ 2) =
        ENNReal.ofReal lam * ENNReal.ofReal (∑ j : Fin d, b.val x *
          ((sobolevGradient (ut : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1))) j x) ^ 2)
      rw [← ENNReal.ofReal_mul hlam.le, hx1]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hx2 j]
      ring
    · have hxS' : x ∉ cubeDilation z (0 : SpatialCoordinates d) r ⁻¹' S := hxS
      rw [Set.indicator_of_notMem hxS, Set.indicator_of_notMem hxS', mul_zero]
  rw [lintegral_congr_ae hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ENNReal.ofReal_mul (pow_pos hr d).le, mul_assoc]

/-- Affine-minimizer dilation (paper `prop-conc` Step 2, scaling of the cell energy): the
affine Dirichlet response and the energy measure of the canonical affine minimizer on the cube of
side `r` about `z` are the unit-cell ones times `r ^ d * lam`, and the measure is transported by
`T = cubeDilation z 0 r`, whenever the coefficients satisfy `a ∘ T = lam * b`. -/
theorem prop_conc_affine_minimizer_dilation {d : ℕ} (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r) (h1 : (0 : ℝ) < 1)
    (a : PositiveCoefficient (centeredCube z r hr))
    (b : PositiveCoefficient (centeredCube (0 : SpatialCoordinates d) 1 h1))
    (lam : ℝ) (hlam : 0 < lam)
    (hab : ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) 1 h1 : Set (SpatialCoordinates d)),
      a.val (cubeDilation z 0 r x) = lam * b.val x)
    (hPq : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤
        K * ‖subspaceGradient (killedSobolevGraph (centeredCube z r hr)) u‖)
    (hP0 : ∃ K : ℝ≥0, ∀ u : killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1),
      ‖(u : SobolevData (centeredCube (0 : SpatialCoordinates d) 1 h1)).1‖ ≤
        K * ‖subspaceGradient
          (killedSobolevGraph (centeredCube (0 : SpatialCoordinates d) 1 h1)) u‖)
    (p : Fin d → ℝ) :
    (affineDirichletResponse (centeredCube_isBounded z hr) hPq a p =
      r ^ d * lam * affineDirichletResponse
        (centeredCube_isBounded (0 : SpatialCoordinates d) h1) hP0 b p) ∧
    ∀ S : Set (SpatialCoordinates d), MeasurableSet S →
      aux_prop_conc_affine_cutoff_growth_measure (centeredCube_isBounded z hr) hPq a p S =
        ENNReal.ofReal (r ^ d * lam) *
          aux_prop_conc_affine_cutoff_growth_measure
            (centeredCube_isBounded (0 : SpatialCoordinates d) h1) hP0 b p
            (cubeDilation z 0 r ⁻¹' S) :=
  ⟨aux_prop_conc_affine_minimizer_dilation_response z r hr h1 a b lam hlam hab hPq hP0 p,
    fun S hS => aux_prop_conc_affine_minimizer_dilation_measure z r hr h1 a b lam hlam hab hPq
      hP0 p S hS⟩

end
end Paper
