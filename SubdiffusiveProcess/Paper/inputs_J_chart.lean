module

public import SubdiffusiveProcess.Paper.in_J

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff
open SubdiffusiveProcess
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

noncomputable def aux_inputs_J_chart_clippedData {d : ℕ} {lo hi : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) {f : SpatialCoordinates d → ℝ}
    (hf : Measurable f) :
    SubdiffusiveProcess.CoarseGrainingVocab.ScalarTriadicCoeffData
      (fun x => max lo (min hi (f x))) := by
  classical
  let b : SpatialCoordinates d → ℝ := fun x => max lo (min hi (f x))
  have hb : Measurable b := by
    dsimp [b]
    fun_prop
  refine ⟨fun Q => ?_⟩
  let U : Homogenization.Book.Ch02.Domain d := Homogenization.Book.Ch02.cubeDomain Q
  refine {
    lam := lo
    Lam := hi
    lam_pos := hlo
    lam_le_Lam := hlohi
    aeStronglyMeasurable := ?_
    aeBounds := ?_
  }
  · intro i j
    have hentry : Measurable (fun x : Homogenization.Vec d =>
        Homogenization.scalarMatrix (d := d) (b x) i j) := by
      fun_prop
    refine hentry.aestronglyMeasurable.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hx
    have hx' : x ∈ Homogenization.openCubeSet Q := by simpa [U] using hx
    simp [SubdiffusiveProcess.CoarseGrainingVocab.scalarCoeffField,
      Homogenization.restrictCoeffField_apply_of_mem hx', b]
  · exact Filter.Eventually.of_forall fun x =>
      ⟨le_max_left _ _, max_le hlohi (min_le_left _ _)⟩

noncomputable def aux_inputs_J_chart_construct {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) :
    Homogenization.Book.Ch02.TriadicCoeffFamily d := by
  classical
  let lo : ℝ := Classical.choose a.property
  have hlo_data := Classical.choose_spec a.property
  have hlo : 0 < lo := hlo_data.1
  let hi : ℝ := max lo ‖a.val‖
  let rep : SpatialCoordinates d → ℝ :=
    (MeasureTheory.Lp.aestronglyMeasurable a.val).mk a.val
  have hrep : Measurable rep :=
    (MeasureTheory.Lp.aestronglyMeasurable a.val).stronglyMeasurable_mk.measurable
  have hAffine : Measurable
      (fun x : SpatialCoordinates d => fun i => w i + r' * x i) := by
    fun_prop
  have hfun : Measurable (fun x : SpatialCoordinates d =>
      rep (fun i => w i + r' * x i)) := hrep.comp hAffine
  exact (aux_inputs_J_chart_clippedData (d := d) (lo := lo) (hi := hi)
    hlo (le_max_left _ _) (f := fun x => rep (fun i => w i + r' * x i)) hfun).toTriadicCoeffFamily

theorem aux_inputs_J_chart_construct_eq {d : ℕ}
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (a : PositiveCoefficient (centeredCube z r hr))
    (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r')
    (hinner : (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
      (centeredCube z r hr : Set (SpatialCoordinates d)))
    (Q : Homogenization.TriadicCube d)
    (hQ : Homogenization.openCubeSet Q ⊆
      Homogenization.openCubeSet (Homogenization.originCube d 0)) :
    ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet Q),
      ((aux_inputs_J_chart_construct z r hr a w r').coeffOn Q).toCoeffField x =
        Homogenization.scalarMatrix (a.val (fun i => w i + r' * x i)) := by
  classical
  let lo : ℝ := Classical.choose a.property
  have hlo_data := Classical.choose_spec a.property
  have hlo : 0 < lo := hlo_data.1
  have hlo_ae : ∀ᵐ y ∂volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)), lo ≤ a.val y := hlo_data.2
  let hi : ℝ := max lo ‖a.val‖
  let rep : SpatialCoordinates d → ℝ :=
    (MeasureTheory.Lp.aestronglyMeasurable a.val).mk a.val
  have hrep : a.val =ᵐ[volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d))] rep :=
    (MeasureTheory.Lp.aestronglyMeasurable a.val).ae_eq_mk
  have hnorm : ∀ᵐ y ∂volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)), a.val y ≤ ‖a.val‖ := by
    have hnorm' : ∀ᵐ y ∂volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d)),
        ‖a.val y‖ₑ ≤ ‖a.val‖ₑ := by
      simpa only [← MeasureTheory.eLpNorm_exponent_top (MeasureTheory.Lp.aestronglyMeasurable a.val),
        ← MeasureTheory.Lp.enorm_def] using!
        (MeasureTheory.enorm_ae_le_eLpNormEssSup
          (a.val : SpatialCoordinates d → ℝ)
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    filter_upwards [hnorm'] with y hy
    have hy' : ENNReal.ofReal |a.val y| ≤ ENNReal.ofReal ‖a.val‖ := by
      simpa [enorm, Real.norm_eq_abs] using! hy
    exact le_trans (le_abs_self _) ((ENNReal.ofReal_le_ofReal_iff
      (norm_nonneg _)).mp hy')
  have hgood : ∀ᵐ y ∂volume.restrict
      (centeredCube z r hr : Set (SpatialCoordinates d)),
      rep y = a.val y ∧ lo ≤ a.val y ∧ a.val y ≤ hi := by
    filter_upwards [hrep.symm, hlo_ae, hnorm] with y hy₁ hy₂ hy₃
    refine ⟨hy₁, hy₂, le_trans hy₃ (le_max_right _ _)⟩
  let affine : SpatialCoordinates d → SpatialCoordinates d :=
    fun x i => w i + r' * x i
  have hscale : MeasureTheory.Measure.QuasiMeasurePreserving
      (fun x : SpatialCoordinates d => r' • x) volume volume :=
    MeasureTheory.Measure.quasiMeasurePreserving_smul volume (ne_of_gt hr')
  have htranslate : MeasureTheory.Measure.QuasiMeasurePreserving
      (fun y : SpatialCoordinates d => w + y) volume volume :=
    MeasureTheory.quasiMeasurePreserving_add_left volume w
  have haffine : MeasureTheory.Measure.QuasiMeasurePreserving affine volume volume := by
    change MeasureTheory.Measure.QuasiMeasurePreserving
      (fun x : SpatialCoordinates d => w + r' • x) volume volume
    exact htranslate.comp hscale
  have hmaps : Set.MapsTo affine (Homogenization.openCubeSet Q)
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    intro x hx
    have hxcoords : ∀ i : Fin d,
        -(1 / 2 : ℝ) < x i ∧ x i < 1 / 2 := by
      simpa using
        (Homogenization.mem_openCubeSet_originCube_iff.mp (hQ hx))
    have hinnerx : affine x ∈ (centeredCube w r' hr' : Set (SpatialCoordinates d)) := by
      rw [SubdiffusiveProcess.centeredCube_eq_pi w hr']
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]
      intro i
      constructor
      · dsimp [affine]
        nlinarith [hr', (hxcoords i).1]
      · dsimp [affine]
        nlinarith [hr', (hxcoords i).2]
    exact hinner hinnerx
  have hrestricted := haffine.restrict hmaps
  have hpull := hrestricted.ae hgood
  change ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet Q),
    Homogenization.scalarMatrix
        (max lo (min hi (rep (fun i => w i + r' * x i)))) =
      Homogenization.scalarMatrix (a.val (fun i => w i + r' * x i))
    
  filter_upwards [hpull] with x hx
  have hclip : max lo (min hi (rep (affine x))) = a.val (affine x) := by
    rw [hx.1, min_eq_right hx.2.2, max_eq_right hx.2.1]
  exact congrArg (Homogenization.scalarMatrix (d := d)) hclip

theorem inputs_J_chart (d : ℕ) (hd : 2 ≤ d) :
    (∃ chart : (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    PositiveCoefficient (centeredCube z r hr) →
      SpatialCoordinates d → ℝ →
        Homogenization.Book.Ch02.TriadicCoeffFamily d), (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (a : PositiveCoefficient (centeredCube z r hr))
      (w : SpatialCoordinates d) (r' : ℝ) (hr' : 0 < r'),
      (centeredCube w r' hr' : Set (SpatialCoordinates d)) ⊆
        (centeredCube z r hr : Set (SpatialCoordinates d)) →
      ∀ Q : Homogenization.TriadicCube d,
        Homogenization.openCubeSet Q ⊆
          Homogenization.openCubeSet (Homogenization.originCube d 0) →
        ∀ᵐ x ∂volume.restrict (Homogenization.openCubeSet Q),
          ((chart z r hr a w r').coeffOn Q).toCoeffField x =
            Homogenization.scalarMatrix (a.val (fun i => w i + r' * x i)))) := by
  have _hd : 2 ≤ d := hd
  exact ⟨fun z r hr a w r' => aux_inputs_J_chart_construct z r hr a w r',
    by
      intro z r hr a w r' hr' hinner Q hQ
      exact aux_inputs_J_chart_construct_eq z r hr a w r' hr' hinner Q hQ⟩

end SubdiffusiveProcess.Paper
