module

public import SubdiffusiveProcess.Main.CommonScaleLaw
public import SubdiffusiveProcess.Main.BilateralField
public import SubdiffusiveProcess.Model.ShellLawG1
public import SubdiffusiveProcess.Model.ShellLawG2
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Set TopologicalSpace SubdiffusiveProcess
open scoped ENNReal NNReal Topology

noncomputable section
namespace SubdiffusiveProcess.Paper

/-! ### The cube supremum as a sup norm -/


/-- The supremum over the fixed cube, written as a supremum over the subtype. -/
theorem aux_lem_15_layer_tail_sSup_eq_iSup {d : ℕ} (Q : Set (SpatialCoordinates d))
    (f : C(SpatialCoordinates d, ℝ)) :
    sSup ((fun x : SpatialCoordinates d => ‖f x‖) '' Q)
      = ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖ := by
  rw [Set.image_eq_range]
  rfl

/-- On a compact cube the supremum is the sup norm of the restriction. -/
theorem aux_lem_15_layer_tail_iSup_eq_norm {d : ℕ} (Q : Set (SpatialCoordinates d))
    [CompactSpace Q] (f : C(SpatialCoordinates d, ℝ)) :
    (⨆ x : Q, ‖f (x : SpatialCoordinates d)‖) =
      ‖(ContinuousMap.compRightContinuousMap ℝ
          (⟨(Subtype.val : Q → SpatialCoordinates d), continuous_subtype_val⟩)) f‖ := by
  rw [ContinuousMap.norm_eq_iSup_norm]
  rfl

theorem aux_lem_15_layer_tail_continuous {d : ℕ} (Q : Set (SpatialCoordinates d))
    [CompactSpace Q] :
    Continuous (fun f : C(SpatialCoordinates d, ℝ) => ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖) := by
  have h : (fun f : C(SpatialCoordinates d, ℝ) => ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖) =
      fun f => ‖(ContinuousMap.compRightContinuousMap ℝ
          (⟨(Subtype.val : Q → SpatialCoordinates d), continuous_subtype_val⟩)) f‖ := by
    funext f
    exact aux_lem_15_layer_tail_iSup_eq_norm Q f
  rw [h]
  exact continuous_norm.comp (map_continuous _)

theorem aux_lem_15_layer_tail_iSup_nonneg {d : ℕ} (Q : Set (SpatialCoordinates d))
    [CompactSpace Q] (f : C(SpatialCoordinates d, ℝ)) :
    0 ≤ ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖ := by
  rw [aux_lem_15_layer_tail_iSup_eq_norm]
  exact norm_nonneg _

/-! ### The half-integer lattice cover -/

/-- The half-integer lattice point attached to an index vector. -/
def aux_lem_15_layer_tail_site {d : ℕ} (m : Fin d → ℤ) : SpatialCoordinates d :=
  fun i => (m i : ℝ) / 2

/-- Translates of the open unit cube centred on the half-integer lattice cover every
sup-norm ball; the lattice indices stay inside an explicit box. -/
theorem aux_lem_15_layer_tail_cover {d : ℕ} (R : ℝ) (M : ℕ) (hM : 2 * R + 1 ≤ (M : ℝ))
    (y : SpatialCoordinates d) (hy : ∀ i, |y i| ≤ R) :
    ∃ m ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(M : ℤ)) (M : ℤ)),
      y - aux_lem_15_layer_tail_site m ∈
        Homogenization.openCubeSet (Homogenization.originCube d 0) := by
  classical
  have key : ∀ i : Fin d, -(1 / 2 : ℝ) ≤ 2 * y i - (round (2 * y i) : ℝ) ∧
      2 * y i - (round (2 * y i) : ℝ) ≤ 1 / 2 := fun i => abs_le.mp (abs_sub_round _)
  refine ⟨fun i => round (2 * y i), ?_, ?_⟩
  · simp only [Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have hyi := abs_le.mp (hy i)
    have hup : (round (2 * y i) : ℝ) ≤ ((M : ℤ) : ℝ) := by
      push_cast
      linarith [(key i).1, (key i).2, hyi.1, hyi.2]
    have hlo : ((-(M : ℤ) : ℤ) : ℝ) ≤ (round (2 * y i) : ℝ) := by
      push_cast
      linarith [(key i).1, (key i).2, hyi.1, hyi.2]
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hup⟩
  · rw [Homogenization.mem_openCubeSet_originCube_iff]
    intro i
    have hval : (y - aux_lem_15_layer_tail_site (fun i => round (2 * y i))) i
        = (2 * y i - (round (2 * y i) : ℝ)) / 2 := by
      simp only [Pi.sub_apply, aux_lem_15_layer_tail_site]
      ring
    rw [hval]
    have h := key i
    norm_num
    constructor <;> linarith [h.1, h.2]

theorem aux_lem_15_layer_tail_card {d : ℕ} (M : ℕ) :
    (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(M : ℤ)) (M : ℤ))).card
      = (2 * M + 1) ^ d := by
  classical
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

theorem aux_lem_15_layer_tail_rpow {j d : ℕ} :
    (((3 : ℝ) ^ (-(j : ℝ))) ^ (-(d : ℝ))) = ((3 : ℝ) ^ j) ^ d := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ j) d, ← Real.rpow_natCast (3 : ℝ) j,
    ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num)]
  ring_nf

theorem aux_lem_15_layer_tail_growth (R : ℝ) (d j M : ℕ)
    (hM : (M : ℝ) < 2 * ((3 : ℝ) ^ j * R) + 2) :
    ((2 * M + 1 : ℕ) : ℝ) ^ d ≤ (4 * R + 5) ^ d * ((3 : ℝ) ^ j) ^ d := by
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ j := by positivity
  have hstep : ((2 * M + 1 : ℕ) : ℝ) ≤ (4 * R + 5) * (3 : ℝ) ^ j := by
    push_cast
    nlinarith [hM, h3, h3pos]
  calc ((2 * M + 1 : ℕ) : ℝ) ^ d ≤ ((4 * R + 5) * (3 : ℝ) ^ j) ^ d :=
        pow_le_pow_left₀ (by positivity) hstep d
    _ = (4 * R + 5) ^ d * ((3 : ℝ) ^ j) ^ d := by rw [mul_pow]

/-! ### The sub-Gaussian tail of the unit-cube observable -/

/-- Markov's inequality in the form supplied by the `(g2)` expectation convention. -/
theorem aux_lem_15_layer_tail_markov {Om : Type} [MeasurableSpace Om] (mu : Measure Om)
    [IsProbabilityMeasure mu] (delta : ℝ) (hdelta : 0 < delta) (X : Om → ℝ)
    (hG : SubdiffusiveProcess.OGammaLE mu 2 delta X) (s : ℝ) (hs : 0 ≤ s) :
    mu {w | s < X w} ≤ ENNReal.ofReal (2 * Real.exp (-(s ^ 2 / delta ^ 2))) := by
  obtain ⟨hint, hle⟩ := hG
  set f : Om → ℝ := fun w => Real.exp ((delta⁻¹ * max (X w) 0) ^ (2 : ℝ)) with hf
  set eps : ℝ := Real.exp ((delta⁻¹ * s) ^ (2 : ℝ)) with heps
  have hepspos : 0 < eps := Real.exp_pos _
  have h0 : 0 ≤ᵐ[mu] f := Filter.Eventually.of_forall fun w => (Real.exp_pos _).le
  have hkey := mul_meas_ge_le_integral_of_nonneg h0 hint eps
  have hsub : {w | s < X w} ⊆ {w | eps ≤ f w} := by
    intro w hw
    have hXw : s < X w := hw
    have hmax : max (X w) 0 = X w := max_eq_left (le_trans hs hXw.le)
    have h1 : delta⁻¹ * s ≤ delta⁻¹ * max (X w) 0 := by
      rw [hmax]
      exact mul_le_mul_of_nonneg_left hXw.le (by positivity)
    have h2 : (0 : ℝ) ≤ delta⁻¹ * s := by positivity
    exact Real.exp_le_exp.mpr (Real.rpow_le_rpow h2 h1 (by norm_num : (0 : ℝ) ≤ (2 : ℝ)))
  have hmono : mu.real {w | s < X w} ≤ mu.real {w | eps ≤ f w} :=
    measureReal_mono hsub (measure_ne_top _ _)
  have hfinal : eps * mu.real {w | s < X w} ≤ 2 := by
    calc eps * mu.real {w | s < X w} ≤ eps * mu.real {w | eps ≤ f w} :=
          mul_le_mul_of_nonneg_left hmono hepspos.le
      _ ≤ ∫ w, f w ∂mu := hkey
      _ ≤ 2 := hle
  have hexp : (delta⁻¹ * s) ^ (2 : ℝ) = s ^ 2 / delta ^ 2 := by
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hbound : mu.real {w | s < X w} ≤ 2 * Real.exp (-(s ^ 2 / delta ^ 2)) := by
    rw [← hexp, Real.exp_neg, ← heps, ← div_eq_mul_inv, le_div_iff₀ hepspos]
    linarith [hfinal]
  calc mu {w | s < X w} = ENNReal.ofReal (mu.real {w | s < X w}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(s ^ 2 / delta ^ 2))) := ENNReal.ofReal_le_ofReal hbound

/-- The `(g1)` translation invariance moves the tail of the unit-cube observable to any
translate of the unit cube. -/
theorem aux_lem_15_layer_tail_translated_tail {d : ℕ} (delta : ℝ) (hdelta : 0 < delta)
    (Praw : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d))
    (hG1 : _root_.SubdiffusiveProcess.Model.ShellLawG1 d Praw)
    (hG2 : _root_.SubdiffusiveProcess.Model.ShellLawG2 d delta Praw)
    (z : Homogenization.Vec d) (s : ℝ) (hs : 0 ≤ s) :
    (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw Praw).toMeasure
        {g | s < _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
          (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)}
      ≤ ENNReal.ofReal (2 * Real.exp (-(s ^ 2 / delta ^ 2))) := by
  have hmeas : MeasurableSet
      {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
        s < _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g} :=
    _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable_measurable measurableSet_Ioi
  have hpre : {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
      s < _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
        (_root_.SubdiffusiveProcess.Model.PotentialField.translate z g)}
      = (_root_.SubdiffusiveProcess.Model.PotentialField.translate z) ⁻¹'
        {g | s < _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable g} := rfl
  rw [hpre, ← Measure.map_apply
      (_root_.SubdiffusiveProcess.Model.PotentialField.measurable_translate z) hmeas,
    hG1.stationary z]
  exact aux_lem_15_layer_tail_markov _ delta hdelta _ hG2.regularity_expectation s hs

/-! ### The layer marginal of the common scale law -/

theorem aux_lem_15_layer_tail_transport {d : ℕ}
    [MeasurableSpace C(SpatialCoordinates d, ℝ)] [BorelSpace C(SpatialCoordinates d, ℝ)]
    (Praw : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d))
    (fg : C(_root_.SubdiffusiveProcess.Model.PotentialField d, C(SpatialCoordinates d, ℝ)))
    (k : ℤ) (A : Set C(SpatialCoordinates d, ℝ)) (hA : MeasurableSet A) :
    (commonScaleLaw d ((_root_.SubdiffusiveProcess.Model.zeroPotentialLaw Praw).map
        fg)).toMeasure
        ((fun omega : BilateralField d => omega k) ⁻¹' A)
      = (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw Praw).toMeasure
        ((fun g => layerScaling d k (fg g)) ⁻¹' A) := by
  set nu := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw Praw).map
    fg with hnu
  have h1 : (commonScaleLaw d nu).toMeasure
      = Measure.infinitePi (fun i : ℤ => (scaledLayerLaw d nu i : Measure _)) := rfl
  have heval := Measure.infinitePi_map_eval
    (X := fun _ : ℤ => C(SpatialCoordinates d, ℝ))
    (fun i : ℤ => (scaledLayerLaw d nu i : Measure C(SpatialCoordinates d, ℝ))) k
  rw [h1, ← Measure.map_apply (measurable_pi_apply k) hA, heval]
  rw [show ((scaledLayerLaw d nu k : ProbabilityMeasure _) : Measure _)
      = Measure.map (layerScaling d k) (nu : Measure _) from
    ProbabilityMeasure.toMeasure_map _]
  rw [hnu, ProbabilityMeasure.toMeasure_map,
    Measure.map_map (layerScaling d k).continuous.measurable fg.continuous.measurable,
    Measure.map_apply (((layerScaling d k).continuous.comp fg.continuous).measurable) hA]
  rfl

/-! ### The layer-tail interface -/

/--
Proof-step interface for the layer-norm applications in `lem_15`, paper label `mfd:lem-15`.

Docstring tick list:

- the fixed cube is concrete and its compact/nonempty carrier is explicit;
- `S j omega` is the actual supremum of the norm of the negative layer on
  that cube, not an arbitrary random majorant;
- the common product law is the law from the raw zero-potential marginal;
- shell laws G1 and G2 supply measurability, nonnegativity, cover growth,
  and the raw tail required by `lem_layer_norms`;
- the constant `Cc` and the cover counts `covers` are *produced* here,
  existentially and after the defining equation for `S`, so the conclusion is
  not vacuous: `Cc` is `max 1 ((4 R + 5) ^ d)` for a sup-norm radius `R` of the
  cube, and `covers j` is the cardinality of an explicit half-integer lattice
  cover of `3 ^ j` times the cube;
- no layer-norm estimate or decay conclusion is assumed here. -/
theorem aux_lem_15_layer_tail
    (d : ℕ) (_hd : 2 ≤ d)
    [MeasurableSpace C(SpatialCoordinates d, ℝ)]
    [BorelSpace C(SpatialCoordinates d, ℝ)]
    (delta : ℝ) (hdelta : 0 < delta) (_hdelta_le : delta ≤ 1)
    (Praw : ProbabilityMeasure (_root_.SubdiffusiveProcess.Model.PotentialSample d))
    (hG1 : _root_.SubdiffusiveProcess.Model.ShellLawG1 d Praw)
    (hG2 : _root_.SubdiffusiveProcess.Model.ShellLawG2 d delta Praw)
    (Q : Set (SpatialCoordinates d)) (hQ : IsCompact Q) (hQne : Q.Nonempty) :
    let forget : C(_root_.SubdiffusiveProcess.Model.PotentialField d,
        C(SpatialCoordinates d, ℝ)) :=
      ⟨fun g => g.1.1, continuous_subtype_val.fst⟩
    let nu := (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw Praw).map
      forget
    let P := (commonScaleLaw d nu).toMeasure
    ∀ S : ℕ → BilateralField d → ℝ,
      (∀ j omega, S j omega =
        sSup ((fun x : SpatialCoordinates d =>
          ‖omega (-(j : ℤ)) x‖) '' Q)) →
      ∃ Cc : ℝ, 1 ≤ Cc ∧ ∃ covers : ℕ → ℝ,
        (∀ j, 1 ≤ covers j) ∧
        (∀ j, covers j ≤ Cc * ((3 : ℝ) ^ (-(j : ℝ))) ^ (-(d : ℝ))) ∧
        (∀ j, AEStronglyMeasurable (S j) P) ∧
        (∀ j omega, 0 ≤ S j omega) ∧
        (∀ (j : ℕ) (s : ℝ), 0 ≤ s →
          P {omega | s < S j omega} ≤
            ENNReal.ofReal
              (2 * covers j * Real.exp (-(s ^ 2 / (Cc * delta ^ 2)))))
    := by
  classical
  intro forget nu P S hS
  have hQc : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  have : Nonempty Q := hQne.to_subtype
  obtain ⟨R0, hR0⟩ := isBounded_iff_forall_norm_le.mp hQ.isBounded
  set R : ℝ := max 0 R0 with hRdef
  have hR : (0 : ℝ) ≤ R := le_max_left _ _
  have hQR : ∀ x ∈ Q, ∀ i, |x i| ≤ R := by
    intro x hx i
    have h1 := hR0 x hx
    have h2 : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
    rw [Real.norm_eq_abs] at h2
    exact h2.trans (h1.trans (le_max_right _ _))
  set M : ℕ → ℕ := fun j => ⌈2 * ((3 : ℝ) ^ j * R) + 1⌉₊ with hMdef
  set L : ℕ → Finset (Fin d → ℤ) := fun j =>
    Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(M j : ℤ)) (M j : ℤ)) with hLdef
  set Cc : ℝ := max 1 ((4 * R + 5) ^ d) with hCcdef
  have hCc : (1 : ℝ) ≤ Cc := le_max_left _ _
  have hcardval : ∀ j, (L j).card = (2 * M j + 1) ^ d := by
    intro j
    rw [hLdef]
    exact aux_lem_15_layer_tail_card (M j)
  have hiSup : ∀ j omega, S j omega
      = ⨆ x : Q, ‖(omega (-(j : ℤ)) : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d)‖ := by
    intro j omega
    rw [hS j omega, aux_lem_15_layer_tail_sSup_eq_iSup]
  refine ⟨Cc, hCc, fun j => ((L j).card : ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    show (1 : ℝ) ≤ ((L j).card : ℝ)
    have h1 : 1 ≤ (L j).card := by
      rw [hcardval j]
      exact Nat.one_le_pow _ _ (by omega)
    exact_mod_cast h1
  · intro j
    show ((L j).card : ℝ) ≤ Cc * ((3 : ℝ) ^ (-(j : ℝ))) ^ (-(d : ℝ))
    rw [aux_lem_15_layer_tail_rpow]
    have hMlt : ((M j : ℝ)) < 2 * ((3 : ℝ) ^ j * R) + 2 := by
      have h := Nat.ceil_lt_add_one (a := 2 * ((3 : ℝ) ^ j * R) + 1) (by positivity)
      rw [hMdef]
      simpa using h.trans_le (by linarith)
    have hcast : ((L j).card : ℝ) = ((2 * M j + 1 : ℕ) : ℝ) ^ d := by
      rw [hcardval j]; push_cast; ring
    calc ((L j).card : ℝ) = ((2 * M j + 1 : ℕ) : ℝ) ^ d := hcast
      _ ≤ (4 * R + 5) ^ d * ((3 : ℝ) ^ j) ^ d :=
          aux_lem_15_layer_tail_growth R d j (M j) hMlt
      _ ≤ Cc * ((3 : ℝ) ^ j) ^ d :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · intro j
    have hfun : S j = (fun f : C(SpatialCoordinates d, ℝ) =>
        ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖) ∘
        (fun omega : BilateralField d => omega (-(j : ℤ))) := by
      funext omega
      exact hiSup j omega
    rw [hfun]
    exact (((aux_lem_15_layer_tail_continuous Q).measurable).comp
      (measurable_pi_apply _)).aestronglyMeasurable
  · intro j omega
    rw [hiSup j omega]
    exact aux_lem_15_layer_tail_iSup_nonneg Q _
  · intro j s hs
    show P {omega | s < S j omega} ≤
      ENNReal.ofReal (2 * ((L j).card : ℝ) * Real.exp (-(s ^ 2 / (Cc * delta ^ 2))))
    have hA : MeasurableSet {f : C(SpatialCoordinates d, ℝ) |
        s < ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖} :=
      (aux_lem_15_layer_tail_continuous Q).measurable measurableSet_Ioi
    have hset : {omega : BilateralField d | s < S j omega}
        = (fun omega : BilateralField d => omega (-(j : ℤ))) ⁻¹'
          {f : C(SpatialCoordinates d, ℝ) | s < ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖} := by
      ext omega
      simp only [mem_ofPred_eq, Set.mem_preimage]
      rw [hiSup j omega]
    rw [hset]
    have htrans := aux_lem_15_layer_tail_transport Praw forget (-(j : ℤ)) _ hA
    rw [show P = (commonScaleLaw d ((_root_.SubdiffusiveProcess.Model.zeroPotentialLaw Praw).map
        forget)).toMeasure from rfl, htrans]
    have hsubset : (fun g : _root_.SubdiffusiveProcess.Model.PotentialField d =>
          layerScaling d (-(j : ℤ)) (forget g)) ⁻¹'
          {f : C(SpatialCoordinates d, ℝ) | s < ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖}
        ⊆ ⋃ m ∈ L j, {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
            s < _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
              (_root_.SubdiffusiveProcess.Model.PotentialField.translate
                (aux_lem_15_layer_tail_site m) g)} := by
      intro g hg
      have hg' : s < sSup ((fun x : SpatialCoordinates d =>
          ‖(layerScaling d (-(j : ℤ)) (forget g)) x‖) '' Q) := by
        rw [aux_lem_15_layer_tail_sSup_eq_iSup]
        exact hg
      obtain ⟨b, hb, hsb⟩ := exists_lt_of_lt_csSup (hQne.image _) hg'
      obtain ⟨x, hxQ, rfl⟩ := hb
      have hpow : ((3 : ℝ) ^ (-(-(j : ℤ)))) = (3 : ℝ) ^ (j : ℕ) := by
        rw [neg_neg, zpow_natCast]
      have hyv : (layerScaling d (-(j : ℤ)) (forget g)) x
          = (forget g) (((3 : ℝ) ^ (j : ℕ)) • x) := by
        show (forget g) (((3 : ℝ) ^ (-(-(j : ℤ)))) • x) = _
        rw [hpow]
      have hybound : ∀ i, |(((3 : ℝ) ^ (j : ℕ)) • x) i| ≤ (3 : ℝ) ^ j * R := by
        intro i
        have hxi : (((3 : ℝ) ^ (j : ℕ)) • x) i = (3 : ℝ) ^ j * x i := rfl
        rw [hxi, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ j)]
        exact mul_le_mul_of_nonneg_left (hQR x hxQ i) (by positivity)
      have hMle : 2 * ((3 : ℝ) ^ j * R) + 1 ≤ (M j : ℝ) := by
        rw [hMdef]
        exact Nat.le_ceil _
      obtain ⟨m, hm, hmem⟩ := aux_lem_15_layer_tail_cover ((3 : ℝ) ^ j * R) (M j) hMle
        (((3 : ℝ) ^ (j : ℕ)) • x) hybound
      refine Set.mem_biUnion (show m ∈ L j by rw [hLdef]; exact hm) ?_
      have hbound := _root_.SubdiffusiveProcess.Model.PotentialField.abs_apply_le_g2Observable
        (_root_.SubdiffusiveProcess.Model.PotentialField.translate (aux_lem_15_layer_tail_site m) g) hmem
      rw [_root_.SubdiffusiveProcess.Model.PotentialField.translate_apply, sub_add_cancel] at hbound
      show s < _
      refine lt_of_lt_of_le ?_ hbound
      simpa [hyv, Real.norm_eq_abs] using! hsb
    calc (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw Praw).toMeasure
          ((fun g => layerScaling d (-(j : ℤ)) (forget g)) ⁻¹'
            {f : C(SpatialCoordinates d, ℝ) | s < ⨆ x : Q, ‖f (x : SpatialCoordinates d)‖})
        ≤ (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw Praw).toMeasure
            (⋃ m ∈ L j, {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
              s < _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
                (_root_.SubdiffusiveProcess.Model.PotentialField.translate
                  (aux_lem_15_layer_tail_site m) g)}) := measure_mono hsubset
      _ ≤ ∑ m ∈ L j, (_root_.SubdiffusiveProcess.Model.zeroPotentialLaw Praw).toMeasure
            {g : _root_.SubdiffusiveProcess.Model.PotentialField d |
              s < _root_.SubdiffusiveProcess.Model.PotentialField.g2Observable
                (_root_.SubdiffusiveProcess.Model.PotentialField.translate
                  (aux_lem_15_layer_tail_site m) g)} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _m ∈ L j, ENNReal.ofReal (2 * Real.exp (-(s ^ 2 / delta ^ 2))) :=
          Finset.sum_le_sum (fun m _ =>
            aux_lem_15_layer_tail_translated_tail delta hdelta Praw hG1 hG2 _ s hs)
      _ = ((L j).card : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-(s ^ 2 / delta ^ 2))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (2 * ((L j).card : ℝ) *
            Real.exp (-(s ^ 2 / (Cc * delta ^ 2)))) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hd2 : (0 : ℝ) < delta ^ 2 := by positivity
          have hle : delta ^ 2 ≤ Cc * delta ^ 2 := by nlinarith [hCc, hd2]
          have hdiv : s ^ 2 / (Cc * delta ^ 2) ≤ s ^ 2 / delta ^ 2 := by
            gcongr
          have hE : Real.exp (-(s ^ 2 / delta ^ 2))
              ≤ Real.exp (-(s ^ 2 / (Cc * delta ^ 2))) := by
            exact Real.exp_le_exp.mpr (by linarith)
          have hc : (0 : ℝ) ≤ ((L j).card : ℝ) := Nat.cast_nonneg _
          nlinarith [Real.exp_pos (-(s ^ 2 / delta ^ 2)),
            Real.exp_pos (-(s ^ 2 / (Cc * delta ^ 2)))]

end SubdiffusiveProcess.Paper
