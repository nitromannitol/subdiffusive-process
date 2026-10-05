module

public import SubdiffusiveProcess.Paper.inputs_poincare_detach_interior
public import SubdiffusiveProcess.Paper.inputs_poincare_detach_endpoint
public import SubdiffusiveProcess.Paper.in_poincare
public import SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable
public import SubdiffusiveProcess.Paper.inputs_Sf_besov_finite

@[expose] public section

open MeasureTheory Set TopologicalSpace Metric
open scoped ENNReal NNReal BigOperators ContDiff Pointwise
open SubdiffusiveProcess _root_.SubdiffusiveProcess.EllipticRegularity
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SubdiffusiveProcess.Paper

theorem aux_inputs_poincare_detach_exact_term_zero_le_half (d : ℕ)
    (f : SpatialCoordinates d → ℝ)
    (hu : Homogenization.ExactOverlapIntegrable (Homogenization.originCube d 0) f)
    (j : ℕ) :
    Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) 0 2 f hu j ≤
      Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) (1 / 2) 2 f hu j := by
  let Q := Homogenization.originCube d 0
  have hdepth : -((Homogenization.exactOverlapSourceDepth Q j : ℤ) : ℝ) = (j : ℝ) := by
    simp [Q, Homogenization.exactOverlapSourceDepth, Homogenization.originCube]
  have hweight : Homogenization.exactOverlapDepthWeight Q 0 j ≤
      Homogenization.exactOverlapDepthWeight Q (1 / 2) j := by
    calc
      Homogenization.exactOverlapDepthWeight Q 0 j = (3 : ℝ≥0∞) ^ 0 := by
        simp [Homogenization.exactOverlapDepthWeight, hdepth]
      _ ≤ (3 : ℝ≥0∞) ^ ((j : ℝ) * (1 / 2)) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by positivity)
      _ = Homogenization.exactOverlapDepthWeight Q (1 / 2) j := by
        simp [Homogenization.exactOverlapDepthWeight, hdepth]
  rw [Homogenization.exactOverlapDepthTerm_eq,
    Homogenization.exactOverlapDepthTerm_eq]
  exact mul_le_mul_left hweight _

theorem aux_inputs_poincare_detach_depth_iSup_finite (d : ℕ) (hd : 2 ≤ d)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1)
    (u : weakSobolevGraph (centeredCube z r hr)) :
    (iSup fun j : ℕ =>
      Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) (1 - s) 2
        (fun x => (u : SobolevData (centeredCube z r hr)).1
          (fun i => z i + r * x i))
        (_root_.SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable d hd z r hr
          (u : SobolevData (centeredCube z r hr)).1) j) < ⊤ := by
  by_cases hsend : s < 1
  · have ht : 1 - s ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hs.1, hs.2, hsend]
    exact _root_.SubdiffusiveProcess.Paper.inputs_Sf_besov_finite d hd z r hr (1 - s) ht u
  · have hs_lower : (1 : ℝ) ≤ s := by
      by_contra h
      exact hsend (lt_of_not_ge h)
    have hs_eq : s = 1 := le_antisymm hs.2 hs_lower
    subst s
    let Q := Homogenization.originCube d 0
    let f : SpatialCoordinates d → ℝ := fun x =>
      (u : SobolevData (centeredCube z r hr)).1 (fun i => z i + r * x i)
    let hu := _root_.SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable d hd z r hr
      (u : SobolevData (centeredCube z r hr)).1
    have hhalf : (iSup fun j : ℕ =>
        Homogenization.exactOverlapDepthTerm Q (1 / 2) 2 f hu j) < ⊤ := by
      simpa [Q, f, hu] using
        (_root_.SubdiffusiveProcess.Paper.inputs_Sf_besov_finite d hd z r hr (1 / 2 : ℝ)
          ⟨by norm_num, by norm_num⟩ u)
    have hmono : ∀ j : ℕ,
        Homogenization.exactOverlapDepthTerm Q 0 2 f hu j ≤
          Homogenization.exactOverlapDepthTerm Q (1 / 2) 2 f hu j := by
      intro j
      exact aux_inputs_poincare_detach_exact_term_zero_le_half d f hu j
    have hsup : (iSup fun j : ℕ =>
        Homogenization.exactOverlapDepthTerm Q 0 2 f hu j) ≤
          iSup (fun j : ℕ =>
            Homogenization.exactOverlapDepthTerm Q (1 / 2) 2 f hu j) := by
      apply iSup_le
      intro j
      exact le_trans (hmono j) (le_iSup
        (fun k : ℕ => Homogenization.exactOverlapDepthTerm Q (1 / 2) 2 f hu k) j)
    simpa [Q, f, hu] using lt_of_le_of_lt hsup hhalf

theorem aux_inputs_poincare_detach_castH1_grad {d : ℕ}
    {U V : Set (SpatialCoordinates d)} (hUV : U = V)
    (w : Homogenization.H1Function U) (x : SpatialCoordinates d) :
    (hUV ▸ w : Homogenization.H1Function V).grad x = w.grad x := by
  cases hUV
  rfl

theorem aux_inputs_poincare_detach_affineH1 (d : ℕ)
    (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr)) :
    ∃ H : Homogenization.H1Function
        (Homogenization.openCubeSet (Homogenization.originCube d 0)),
      (∀ x, H.toFun x =
        (u : SobolevData (centeredCube z r hr)).1
          (fun i : Fin d => z i + r * x i)) ∧
      (∀ x i, H.grad x i = r * (u : SobolevData (centeredCube z r hr)).2 i
          (fun j : Fin d => z j + r * x j)) := by
  obtain ⟨V, hV, hVgrad⟩ :=
    SubdiffusiveProcess.exists_nativeH1Function_of_weakSobolevGraph u
  let hphysical : Homogenization.H1Function
      (centeredCube z r hr : Set (SpatialCoordinates d)) := V
  have htranslate := aux_inputs_Sf_besov_finite_centeredCube_translate d z r hr
  let hcenter : Homogenization.H1Function
      (Homogenization.translateSet z
        (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d))) :=
    htranslate ▸ hphysical
  let h0r : Homogenization.H1Function
      (centeredCube (0 : SpatialCoordinates d) r hr : Set (SpatialCoordinates d)) :=
    hcenter.untranslate z
  have hcenter_apply (x : SpatialCoordinates d) : hcenter.toFun x = V.toFun x := by
    change (htranslate ▸ hphysical).toFun x = V.toFun x
    exact aux_inputs_Sf_besov_finite_castH1_toFun htranslate hphysical x
  have hcenter_grad (x : SpatialCoordinates d) : hcenter.grad x = V.grad x := by
    change (htranslate ▸ hphysical).grad x = V.grad x
    exact aux_inputs_poincare_detach_castH1_grad htranslate hphysical x
  have h0r_apply (x : SpatialCoordinates d) : h0r.toFun x = V.toFun (x + z) := by
    change (hcenter.untranslate z).toFun x = V.toFun (x + z)
    rw [Homogenization.H1Function.untranslate_toFun]
    exact hcenter_apply (x + z)
  have h0r_grad (x : SpatialCoordinates d) : h0r.grad x = V.grad (x + z) := by
    change (hcenter.untranslate z).grad x = V.grad (x + z)
    rw [Homogenization.H1Function.untranslate_grad]
    exact hcenter_grad (x + z)
  have hscale := aux_inputs_Sf_besov_finite_centeredCube_scale d r hr
  let hscaled : Homogenization.H1Function
      (r • Homogenization.openCubeSet (Homogenization.originCube d 0)) := hscale ▸ h0r
  have hscaled_apply (x : SpatialCoordinates d) : hscaled.toFun x = h0r.toFun x := by
    change (hscale ▸ h0r).toFun x = h0r.toFun x
    exact aux_inputs_Sf_besov_finite_castH1_toFun hscale h0r x
  have hscaled_grad (x : SpatialCoordinates d) : hscaled.grad x = h0r.grad x := by
    change (hscale ▸ h0r).grad x = h0r.grad x
    exact aux_inputs_poincare_detach_castH1_grad hscale h0r x
  let hpull : Homogenization.H1Function
      (Homogenization.openCubeSet (Homogenization.originCube d 0)) :=
    hscaled.undilateSet hr rfl
  let H : Homogenization.H1Function
      (Homogenization.openCubeSet (Homogenization.originCube d 0)) := r • hpull
  refine ⟨H, ?_, ?_⟩
  · intro x
    simp only [H, hpull, Homogenization.H1Function.smul_toFun,
      Homogenization.H1Function.undilateSet_toFun]
    rw [hscaled_apply, h0r_apply, hV]
    have harg : r • x + z = (fun i : Fin d => z i + r * x i) := by
      ext i
      simp [Pi.smul_apply, smul_eq_mul, add_comm]
    rw [harg]
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  · intro x i
    have hgradH : H.grad x i = r * hscaled.grad (r • x) i := by
      simp [H, hpull, Homogenization.H1Function.smul_grad,
        Homogenization.H1Function.undilateSet_grad, Pi.smul_apply, smul_eq_mul]
    rw [hgradH, hscaled_grad, h0r_grad, hVgrad]
    have harg : r • x + z = (fun j : Fin d => z j + r * x j) := by
      ext j
      simp [Pi.smul_apply, smul_eq_mul, add_comm]
    rw [harg]

theorem aux_inputs_poincare_detach_unit_paperNorm_nonneg (d : ℕ)
    (s : ℝ) (hs : 0 ≤ s)
    (F : SpatialCoordinates d → SpatialCoordinates d) :
    0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
      (Homogenization.originCube d 0) s (.finite 1) F := by
  have hraw : 0 ≤ Homogenization.Book.Ch03.scaleNormalizedNegativeBesovVectorNorm
      (Homogenization.originCube d 0) s (.finite 1) F := by
    change 0 ≤ sSup (Set.range (fun N : ℕ =>
      Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite
        (Homogenization.originCube d 0) s 1 N F))
    by_cases hb : BddAbove (Set.range (fun N : ℕ =>
        Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite
          (Homogenization.originCube d 0) s 1 N F))
    · exact (Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite_nonneg
          (Homogenization.originCube d 0) s 1 0 F).trans
        (le_csSup hb ⟨0, rfl⟩)
    · rw [Real.sSup_of_not_bddAbove hb]
  simpa [SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm] using
    mul_nonneg (Real.rpow_nonneg hs 1) hraw

theorem aux_inputs_poincare_detach_unit_estimate_interior (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (s : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ H : Homogenization.H1Function
          (Homogenization.openCubeSet (Homogenization.originCube d 0)),
          ∀ hu : Homogenization.ExactOverlapIntegrable
            (Homogenization.originCube d 0) H.toFun,
            (iSup fun j : ℕ =>
              Homogenization.exactOverlapDepthTerm
                (Homogenization.originCube d 0) (1 - s) 2 H.toFun hu j).toReal ≤
              C * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
                (Homogenization.originCube d 0) s (.finite 1) H.grad) := by
  exact inputs_poincare_detach_interior d hd

theorem aux_inputs_poincare_detach_unit_estimate_endpoint (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      (∀ H : Homogenization.H1Function
          (Homogenization.openCubeSet (Homogenization.originCube d 0)),
          ∀ hu : Homogenization.ExactOverlapIntegrable
            (Homogenization.originCube d 0) H.toFun,
            (iSup fun j : ℕ =>
              Homogenization.exactOverlapDepthTerm
                (Homogenization.originCube d 0) 0 2 H.toFun hu j).toReal ≤
              C * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
                (Homogenization.originCube d 0) 1 (.finite 1) H.grad) := by
  exact inputs_poincare_detach_endpoint d hd

theorem aux_inputs_poincare_detach_unit_estimate (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
        ∀ H : Homogenization.H1Function
          (Homogenization.openCubeSet (Homogenization.originCube d 0)),
          ∀ hu : Homogenization.ExactOverlapIntegrable
            (Homogenization.originCube d 0) H.toFun,
            (iSup fun j : ℕ =>
              Homogenization.exactOverlapDepthTerm
                (Homogenization.originCube d 0) (1 - s) 2 H.toFun hu j).toReal ≤
              C * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
                (Homogenization.originCube d 0) s (.finite 1) H.grad) := by
  obtain ⟨C₀, hC₀, hinterior⟩ :=
    aux_inputs_poincare_detach_unit_estimate_interior d hd
  obtain ⟨C₁, hC₁, hendpoint⟩ :=
    aux_inputs_poincare_detach_unit_estimate_endpoint d hd
  let C := max C₀ C₁
  refine ⟨C, lt_max_of_lt_left hC₀, ?_⟩
  intro s hs H hu
  have hnorm := aux_inputs_poincare_detach_unit_paperNorm_nonneg d s hs.1.le H.grad
  by_cases hslt : s < 1
  · have hs' : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs.1, hslt⟩
    calc
      (iSup fun j : ℕ =>
          Homogenization.exactOverlapDepthTerm
            (Homogenization.originCube d 0) (1 - s) 2 H.toFun hu j).toReal ≤
        C₀ * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
          (Homogenization.originCube d 0) s (.finite 1) H.grad := hinterior s hs' H hu
      _ ≤ C * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
          (Homogenization.originCube d 0) s (.finite 1) H.grad :=
        mul_le_mul_of_nonneg_right (le_max_left C₀ C₁) hnorm
  · have hse : s = 1 := le_antisymm hs.2 (le_of_not_gt hslt)
    subst s
    calc
      (iSup fun j : ℕ =>
          Homogenization.exactOverlapDepthTerm
            (Homogenization.originCube d 0) (1 - (1 : ℝ)) 2 H.toFun hu j).toReal ≤
        C₁ * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
          (Homogenization.originCube d 0) 1 (.finite 1) H.grad := by
            simpa using hendpoint H hu
      _ ≤ C * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
          (Homogenization.originCube d 0) 1 (.finite 1) H.grad :=
        mul_le_mul_of_nonneg_right (le_max_right C₀ C₁) hnorm

theorem aux_inputs_poincare_detach_paperNorm_smul (d : ℕ) (s c : ℝ)
    (hc : 0 ≤ c) (F : SpatialCoordinates d → SpatialCoordinates d) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
        (Homogenization.originCube d 0) s (.finite 1)
        (fun x i => c * F x i) =
      c * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
        (Homogenization.originCube d 0) s (.finite 1) F := by
  let Q : Homogenization.TriadicCube d := Homogenization.originCube d 0
  let G : SpatialCoordinates d → SpatialCoordinates d := fun x i => c * F x i
  have havg (R : Homogenization.TriadicCube d) :
      Homogenization.cubeAverageVec R G = c • Homogenization.cubeAverageVec R F := by
    funext i
    change Homogenization.cubeAverage R (fun x => c * F x i) =
      c * Homogenization.cubeAverage R (fun x => F x i)
    unfold Homogenization.cubeAverage
    rw [MeasureTheory.integral_const_mul]
    ring
  have hsqrt (j : ℕ) :
      Real.sqrt (Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q G j) =
        c * Real.sqrt (Homogenization.Book.Ch03.negativeBesovVectorDepthAverage Q F j) := by
    simpa [Homogenization.Book.Ch03.negativeBesovVectorDepthAverage, G, havg] using
      Homogenization.sqrt_descendantsAverage_vecNormSq_const_smul_eq Q j c
        (fun R => Homogenization.cubeAverageVec R F) hc
  have hdepth (j : ℕ) :
      Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm Q s G j =
        c * Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm Q s F j := by
    unfold Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm
    rw [hsqrt j]
    ring
  have hpartial (N : ℕ) :
      Homogenization.cubeBesovNegativeVectorPartialSeminorm Q s N G =
        c * Homogenization.cubeBesovNegativeVectorPartialSeminorm Q s N F := by
    unfold Homogenization.cubeBesovNegativeVectorPartialSeminorm
    calc
      (Finset.range (N + 1)).sum
          (fun j => Homogenization.cubeBesovNegativeVectorDepthSeminorm Q s G j) =
        (Finset.range (N + 1)).sum
          (fun j => c * Homogenization.cubeBesovNegativeVectorDepthSeminorm Q s F j) := by
            apply Finset.sum_congr rfl
            intro j hj
            simpa [Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm_eq_old] using
              hdepth j
      _ = c * (Finset.range (N + 1)).sum
          (fun j => Homogenization.cubeBesovNegativeVectorDepthSeminorm Q s F j) := by
            rw [Finset.mul_sum]
  have hsemi :
      Homogenization.cubeBesovNegativeVectorSeminorm Q s G =
        c * Homogenization.cubeBesovNegativeVectorSeminorm Q s F := by
    by_cases hcz : c = 0
    · subst c
      have hzero : ∀ N : ℕ,
          Homogenization.cubeBesovNegativeVectorPartialSeminorm Q s N G = 0 := by
        intro N
        rw [hpartial]
        simp
      unfold Homogenization.cubeBesovNegativeVectorSeminorm
      have hrange : Set.range
          (fun N : ℕ => Homogenization.cubeBesovNegativeVectorPartialSeminorm Q s N G) =
          {0} := by
        ext x
        simp only [Set.mem_range, Set.mem_singleton_iff]
        constructor
        · rintro ⟨N, rfl⟩
          exact hzero N
        · intro hx
          subst x
          exact ⟨0, hzero 0⟩
      rw [hrange]
      simp
    · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hcz)
      let A : Set ℝ := Set.range
        (fun N : ℕ => Homogenization.cubeBesovNegativeVectorPartialSeminorm Q s N F)
      let B : Set ℝ := Set.range
        (fun N : ℕ => Homogenization.cubeBesovNegativeVectorPartialSeminorm Q s N G)
      have hrange : B = (OrderIso.mulLeft₀ c hcpos) '' A := by
        ext x
        constructor
        · rintro ⟨N, rfl⟩
          refine ⟨Homogenization.cubeBesovNegativeVectorPartialSeminorm Q s N F,
            ⟨N, rfl⟩, ?_⟩
          change c * Homogenization.cubeBesovNegativeVectorPartialSeminorm Q s N F = _
          exact (hpartial N).symm
        · rintro ⟨y, ⟨N, rfl⟩, hy⟩
          refine ⟨N, ?_⟩
          change Homogenization.cubeBesovNegativeVectorPartialSeminorm Q s N G = x
          rw [hpartial N]
          exact hy
      have hAne : A.Nonempty := ⟨_, ⟨0, rfl⟩⟩
      by_cases hAbdd : BddAbove A
      · have hBb : BddAbove B := by
          rcases hAbdd with ⟨M, hM⟩
          refine ⟨c * M, ?_⟩
          rintro x ⟨N, rfl⟩
          change Homogenization.cubeBesovNegativeVectorPartialSeminorm Q s N G ≤ c * M
          rw [hpartial N]
          exact mul_le_mul_of_nonneg_left
            (hM ⟨N, rfl⟩) hc
        unfold Homogenization.cubeBesovNegativeVectorSeminorm
        change sSup B = c * sSup A
        calc
          sSup B = sSup ((OrderIso.mulLeft₀ c hcpos) '' A) := by rw [hrange]
          _ = OrderIso.mulLeft₀ c hcpos (sSup A) :=
            ((OrderIso.mulLeft₀ c hcpos).map_csSup' hAne hAbdd).symm
          _ = c * sSup A := rfl
      · have hBnot : ¬ BddAbove B := by
          intro hBb
          apply hAbdd
          rcases hBb with ⟨M, hM⟩
          refine ⟨M / c, ?_⟩
          rintro x ⟨N, rfl⟩
          apply (le_div_iff₀ hcpos).2
          have hbound := hM ⟨N, rfl⟩
          have hbound' : c * Homogenization.cubeBesovNegativeVectorPartialSeminorm Q s N F ≤ M := by
            simpa only [hpartial N] using hbound
          nlinarith [hbound']
        unfold Homogenization.cubeBesovNegativeVectorSeminorm
        change sSup B = c * sSup A
        rw [Real.sSup_of_not_bddAbove hBnot,
          Real.sSup_of_not_bddAbove hAbdd]
        simp
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
  simp only [Homogenization.Book.Ch03.scaleNormalizedNegativeBesovVectorNorm_finite_one_eq_cubeBesovNegativeVectorSeminorm]
  rw [hsemi]
  ring

theorem aux_inputs_poincare_detach_all_radii_core (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
          (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
        ∀ u : weakSobolevGraph (centeredCube z r hr),
          r ^ (s - 1) *
              (iSup fun j : ℕ =>
                Homogenization.exactOverlapDepthTerm
                  (Homogenization.originCube d 0) (1 - s) 2
                  (fun x => (u : SobolevData (centeredCube z r hr)).1
                    (fun i => z i + r * x i))
                  (_root_.SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable d hd z r hr
                    (u : SobolevData (centeredCube z r hr)).1) j).toReal ≤
            C * (r ^ s *
              SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
                (Homogenization.originCube d 0) s (.finite 1)
                (fun x i => (u : SobolevData (centeredCube z r hr)).2 i
                  (fun j => z j + r * x j)))) := by
  obtain ⟨C, hC, hunit⟩ := aux_inputs_poincare_detach_unit_estimate d hd
  refine ⟨C, hC, ?_⟩
  intro z r hr s hs u
  obtain ⟨H, hHval, hHgrad⟩ := aux_inputs_poincare_detach_affineH1 d z r hr u
  let Q := Homogenization.originCube d 0
  let f : SpatialCoordinates d → ℝ := fun x =>
    (u : SobolevData (centeredCube z r hr)).1 (fun i => z i + r * x i)
  let hu := _root_.SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable d hd z r hr
    (u : SobolevData (centeredCube z r hr)).1
  have hfun : H.toFun = f := by
    funext x
    exact hHval x
  have huH : Homogenization.ExactOverlapIntegrable Q H.toFun := by
    rw [hfun]
    exact hu
  have hterms : ∀ j : ℕ,
      Homogenization.exactOverlapDepthTerm Q (1 - s) 2 f hu j =
        Homogenization.exactOverlapDepthTerm Q (1 - s) 2 H.toFun huH j := by
    intro j
    exact Homogenization.exactOverlapDepthTerm_congr_ae Q (1 - s) 2 hu huH
      (fun _ _ _ => Filter.Eventually.of_forall fun x => (hHval x).symm) j
  have hsup :
      (iSup fun j : ℕ =>
        Homogenization.exactOverlapDepthTerm Q (1 - s) 2 f hu j) =
      iSup (fun j : ℕ =>
        Homogenization.exactOverlapDepthTerm Q (1 - s) 2 H.toFun huH j) := by
    apply iSup_congr
    intro j
    exact hterms j
  have hunit := hunit s hs H huH
  rw [← hsup] at hunit
  let F : SpatialCoordinates d → SpatialCoordinates d := fun x i =>
    (u : SobolevData (centeredCube z r hr)).2 i (fun j => z j + r * x j)
  have hgrad : H.grad = fun x i => r * F x i := by
    funext x i
    exact hHgrad x i
  have hnorm :
      SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm Q s (.finite 1)
          H.grad =
        r * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
          Q s (.finite 1) F := by
    rw [hgrad]
    exact aux_inputs_poincare_detach_paperNorm_smul d s r hr.le F
  have hrpow : r ^ (s - 1) * r = r ^ s := by
    calc
      r ^ (s - 1) * r = Real.rpow r (s - 1) * Real.rpow r 1 := by
        exact congrArg (fun t : ℝ => Real.rpow r (s - 1) * t)
          (Real.rpow_one r).symm
      _ = Real.rpow r ((s - 1) + 1) := (Real.rpow_add hr _ _).symm
      _ = r ^ s := by congr 1 ; ring
  have hfactor : 0 ≤ r ^ (s - 1) :=
    Real.rpow_nonneg hr.le _
  rw [hnorm] at hunit
  calc
    r ^ (s - 1) *
            (iSup fun j : ℕ => Homogenization.exactOverlapDepthTerm Q (1 - s) 2 f hu j).toReal
        ≤ r ^ (s - 1) *
            (C * (r * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
              Q s (.finite 1) F)) :=
          mul_le_mul_of_nonneg_left hunit hfactor
    _ = C * (r ^ s * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
          Q s (.finite 1) F) := by
        calc
          r ^ (s - 1) * (C * (r *
              SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
                Q s (.finite 1) F)) =
              C * ((r ^ (s - 1) * r) *
                SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
                  Q s (.finite 1) F) := by ring
          _ = C * (r ^ s *
                SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
                  Q s (.finite 1) F) := by rw [hrpow]

theorem inputs_poincare_detach (d : ℕ) (hd : 2 ≤ d) (_Jc : _root_.SubdiffusiveProcess.Paper.in_J d) :
    (let besovGradSeminorm : (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    SobolevData (centeredCube z r hr) → ℝ → ℝ≥0∞ → ℝ) := fun z r _hr u s q =>
      r ^ s * SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
        (Homogenization.originCube d 0) s (if q = ⊤ then .infinity else .finite q.toReal)
        (fun x i => u.2 i (fun j => z j + r * x j));
let positive_integrable := _root_.SubdiffusiveProcess.Paper.inputs_poincare_positive_integrable d hd;
    let besovSeminorm : (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r),
    DomainL2 (centeredCube z r hr) → ℝ → ℝ) := fun z r hr v s =>
      r ^ (s - 1) * (iSup (fun j : ℕ =>
        Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) (1 - s) 2
          (fun x => v (fun i => z i + r * x i)) (positive_integrable z r hr v) j)).toReal;
∃ C : ℝ, 0 < C ∧ (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ u : weakSobolevGraph (centeredCube z r hr),
    (iSup (fun j : ℕ =>
      Homogenization.exactOverlapDepthTerm (Homogenization.originCube d 0) (1 - s) 2
        (fun x => (u : SobolevData (centeredCube z r hr)).1 (fun j => z j + r * x j))
        (positive_integrable z r hr (u : SobolevData (centeredCube z r hr)).1) j)) < ⊤) ∧ (∀ (z : SpatialCoordinates d) (r : ℝ) (hr : 0 < r)
      (s : ℝ), s ∈ Set.Ioc (0 : ℝ) 1 →
    ∀ u : weakSobolevGraph (centeredCube z r hr),
      besovSeminorm z r hr (u : SobolevData (centeredCube z r hr)).1 s ≤
        C * besovGradSeminorm z r hr (u : SobolevData _) s 1)) := by
  obtain ⟨C, hC, hdetach⟩ := aux_inputs_poincare_detach_all_radii_core d hd
  refine ⟨C, hC, ?_, ?_⟩
  · intro z r hr s hs u
    exact aux_inputs_poincare_detach_depth_iSup_finite d hd z r hr s hs u
  · intro z r hr s hs u
    exact hdetach z r hr s hs u

end SubdiffusiveProcess.Paper

