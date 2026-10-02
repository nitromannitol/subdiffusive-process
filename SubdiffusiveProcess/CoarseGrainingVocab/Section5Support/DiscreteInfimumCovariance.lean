import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.DiscreteSlopeSeparability
import SubdiffusiveProcess.CoarseGrainingVocab.Section5Support.Kuhn.CellDilation
import Homogenization.Sobolev.Foundations.CoerciveH1Dilation
import Homogenization.Sobolev.H1.Translation




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section5Support

open Homogenization Kuhn MeasureTheory Set

open scoped Pointwise

noncomputable section

variable {d : ℕ}

/-! ## Transport of the `H^1_0` carrier -/

private def castH10 {U V : Set (Vec d)} (h : U = V) (u : H10Function U) :
    H10Function V := h ▸ u

private theorem castH10_grad {U V : Set (Vec d)} (h : U = V) (u : H10Function U) :
    (castH10 h u).toH1Function.grad = u.toH1Function.grad := by
  subst h
  rfl

private theorem smul_set_eq_preimage' {a : ℝ} (ha : a ≠ 0) (U : Set (Vec d)) :
    a • U = (fun x : Vec d => a⁻¹ • x) ⁻¹' U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_smul, ha] using hy
  · intro hx
    exact ⟨a⁻¹ • x, hx, by simp [smul_smul, ha]⟩

private theorem inv_smul_smul_set' {a : ℝ} (ha : a ≠ 0) (U : Set (Vec d)) :
    a⁻¹ • (a • U) = U := by
  rw [smul_set_eq_preimage' (inv_ne_zero ha), smul_set_eq_preimage' ha]
  ext x
  simp [smul_smul, ha]

/-- The competitor on `a • U` induced by a competitor on `U`. -/
private def dilationPushforward {U : Set (Vec d)} {a : ℝ} (ha : 0 < a)
    (w : H10Function U) : H10Function (a • U) :=
  a • H10Function.unscale (inv_pos.mpr ha)
    (castH10 (inv_smul_smul_set' ha.ne' U).symm w)

private theorem dilationPushforward_grad {U : Set (Vec d)} {a : ℝ} (ha : 0 < a)
    (w : H10Function U) (x : Vec d) :
    (dilationPushforward ha w).toH1Function.grad (a • x) =
      w.toH1Function.grad x := by
  show a • ((H10Function.unscale (inv_pos.mpr ha)
    (castH10 (inv_smul_smul_set' ha.ne' U).symm w)).toH1Function.grad (a • x)) = _
  rw [H10Function.unscale_toH1Function, H1Function.unscale_grad, castH10_grad,
    smul_smul, mul_inv_cancel₀ ha.ne', one_smul, smul_smul, inv_mul_cancel₀ ha.ne',
    one_smul]

/-- **The `H^1_0` competitor transported by the affine map `phi`.** -/
def affinePushforward (k : ℕ) (c : Fin d → ℤ) {U : Set (Vec d)}
    (w : H10Function U) : H10Function (cellAffineMap k c '' U) :=
  castH10 (image_cellAffineMap_eq k c U).symm
    ((dilationPushforward (three_zpow_pos' (k : ℤ)) w).translate
      (cubeCenter (⟨(k : ℤ), c⟩ : TriadicCube d)))

theorem cellAffineMap_sub_cubeCenter (k : ℕ) (c : Fin d → ℤ) (y : Vec d) :
    cellAffineMap k c y - cubeCenter (⟨(k : ℤ), c⟩ : TriadicCube d) =
      ((3 : ℝ) ^ (k : ℤ)) • y := by
  rw [cellAffineMap_eq_smul_add, add_sub_cancel_right]

/-- **The pushforward preserves the gradient**, read at corresponding points. -/
theorem affinePushforward_grad (k : ℕ) (c : Fin d → ℤ) {U : Set (Vec d)}
    (w : H10Function U) (y : Vec d) :
    (affinePushforward k c w).toH1Function.grad (cellAffineMap k c y) =
      w.toH1Function.grad y := by
  rw [affinePushforward]
  show (castH10 (image_cellAffineMap_eq k c U).symm
      ((dilationPushforward (three_zpow_pos' (k : ℤ)) w).translate
        (cubeCenter (⟨(k : ℤ), c⟩ : TriadicCube d)))).toH1Function.grad
      (cellAffineMap k c y) = _
  rw [castH10_grad]
  show (dilationPushforward (three_zpow_pos' (k : ℤ)) w).toH1Function.grad
      (cellAffineMap k c y - cubeCenter (⟨(k : ℤ), c⟩ : TriadicCube d)) = _
  rw [cellAffineMap_sub_cubeCenter]
  exact dilationPushforward_grad (three_zpow_pos' (k : ℤ)) w y

/-! ## Transport of an almost-everywhere statement -/

theorem ae_restrict_image_cellAffineMap {k : ℕ} {c : Fin d → ℤ} {A : Set (Vec d)}
    (hA : MeasurableSet A) {F f : Vec d → Vec d} {v : Vec d}
    (hF : ∀ y, F (cellAffineMap k c y) = f y)
    (h : ∀ᵐ y ∂(volume.restrict A), f y = v) :
    ∀ᵐ x ∂(volume.restrict (cellAffineMap k c '' A)), F x = v := by
  have hAimg : MeasurableSet (cellAffineMap k c '' A) :=
    measurableSet_image_cellAffineMap k c hA
  rw [ae_iff, Measure.restrict_apply' hA] at h
  rw [ae_iff, Measure.restrict_apply' hAimg]
  have hEq : {x | ¬ F x = v} ∩ (cellAffineMap k c '' A) =
      cellAffineMap k c '' ({y | ¬ f y = v} ∩ A) := by
    ext x
    constructor
    · rintro ⟨hx, y, hyA, rfl⟩
      exact ⟨y, ⟨fun hv => hx (by rw [hF y]; exact hv), hyA⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hyA⟩, rfl⟩
      exact ⟨fun hv => hy (by rw [← hF y]; exact hv), ⟨y, hyA, rfl⟩⟩
  rw [hEq, volume_image_cellAffineMap, h, mul_zero]

/-! ## Transport of a conforming competitor -/

/-- The inverse cell map, used to read the transported slopes. -/
def undilateKuhnCell (k R : ℕ) (c : Fin d → ℤ) (T : KuhnCell d) : KuhnCell d :=
  ⟨⟨T.supportCube.scale - (k : ℤ), fun i => T.supportCube.index i - 3 ^ R * c i⟩,
    T.order⟩

@[simp] theorem undilateKuhnCell_dilateKuhnCell (k R : ℕ) (c : Fin d → ℤ)
    (V : KuhnCell d) : undilateKuhnCell k R c (dilateKuhnCell k R c V) = V := by
  cases V with
  | mk Q sigma =>
      cases Q with
      | mk s idx =>
          simp [undilateKuhnCell, dilateKuhnCell]

/-- The transported slope assignment. -/
def dilateSlopes (k R : ℕ) (c : Fin d → ℤ) (q : KuhnCell d → Vec d) :
    KuhnCell d → Vec d := fun T => q (undilateKuhnCell k R c T)

@[simp] theorem dilateSlopes_dilateKuhnCell (k R : ℕ) (c : Fin d → ℤ)
    (q : KuhnCell d → Vec d) (V : KuhnCell d) :
    dilateSlopes k R c q (dilateKuhnCell k R c V) = q V := by
  simp [dilateSlopes]

/-- **The conforming competitor transports.** -/
def transportKuhnCompetitor (k R : ℕ) (c : Fin d → ℤ) {U : Set (Vec d)}
    {S₀ : Finset (KuhnCell d)} (hS : ∀ V ∈ S₀, V.supportCube.scale = -(R : ℤ))
    (hU : MeasurableSet U) (c₀ : KuhnCompetitor U S₀) :
    KuhnCompetitor (cellAffineMap k c '' U) (S₀.image (dilateKuhnCell k R c)) where
  toH10Function := affinePushforward k c c₀.toH10Function
  slope := dilateSlopes k R c c₀.slope
  isCellwiseSlope := by
    intro T hT
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hT
    have hset : cellAffineMap k c '' U ∩ (dilateKuhnCell k R c V).openCarrier =
        cellAffineMap k c '' (U ∩ V.openCarrier) := by
      rw [openCarrier_dilateKuhnCell (hS V hV), image_cellAffineMap_inter]
    rw [hset, dilateSlopes_dilateKuhnCell]
    exact ae_restrict_image_cellAffineMap
      (hU.inter (isOpen_openCarrier V).measurableSet)
      (fun y => affinePushforward_grad k c c₀.toH10Function y)
      (c₀.isCellwiseSlope V hV)

theorem mem_kuhnSlopeSet_dilateSlopes (k R : ℕ) (c : Fin d → ℤ) {U : Set (Vec d)}
    {S₀ : Finset (KuhnCell d)} (hS : ∀ V ∈ S₀, V.supportCube.scale = -(R : ℤ))
    (hU : MeasurableSet U) {q : KuhnCell d → Vec d} (hq : q ∈ kuhnSlopeSet U S₀) :
    dilateSlopes k R c q ∈
      kuhnSlopeSet (cellAffineMap k c '' U) (S₀.image (dilateKuhnCell k R c)) := by
  obtain ⟨c₀, hc₀⟩ := hq
  exact ⟨transportKuhnCompetitor k R c hS hU c₀, by rw [← hc₀]; rfl⟩

/-! ## The discrete energy identity -/

/-- **The discrete energy transports by the single factor `3^{kd}`.** -/
theorem kuhnDiscreteEnergy_dilate (k R : ℕ) (c : Fin d → ℤ) {U : Set (Vec d)}
    {S₀ : Finset (KuhnCell d)} (hS : ∀ V ∈ S₀, V.supportCube.scale = -(R : ℤ))
    (B : Vec d → ℝ) (p : Vec d) (q : KuhnCell d → Vec d) :
    kuhnDiscreteEnergy B (S₀.image (dilateKuhnCell k R c))
        (cellAffineMap k c '' U) p (dilateSlopes k R c q) =
      ((3 : ℝ) ^ (k : ℤ)) ^ d *
        kuhnDiscreteEnergy (fun y => B (cellAffineMap k c y)) S₀ U p q := by
  rw [kuhnDiscreteEnergy,
    Finset.sum_image (fun a _ b _ h => dilateKuhnCell_injective k R c h),
    kuhnDiscreteEnergy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun V hV => ?_
  have hset : cellAffineMap k c '' U ∩ (dilateKuhnCell k R c V).openCarrier =
      cellAffineMap k c '' (U ∩ V.openCarrier) := by
    rw [openCarrier_dilateKuhnCell (hS V hV), image_cellAffineMap_inter]
  have hvol : volume.real (cellAffineMap k c '' U ∩
      (dilateKuhnCell k R c V).openCarrier) =
      ((3 : ℝ) ^ (k : ℤ)) ^ d * volume.real (U ∩ V.openCarrier) := by
    rw [hset]
    exact volume_toReal_image_cellAffineMap k c _
  rw [hvol, cellSup_dilateKuhnCell (hS V hV), dilateSlopes_dilateKuhnCell]
  ring

/-! ## The covariance of the discrete minimum -/

/-- **The discrete minimum only decreases under the normalized transport.** -/
theorem kuhnDirichletInf_dilate_le (k R : ℕ) (c : Fin d → ℤ) {U : Set (Vec d)}
    {S₀ : Finset (KuhnCell d)} (hS : ∀ V ∈ S₀, V.supportCube.scale = -(R : ℤ))
    (hU : MeasurableSet U) {B : Vec d → ℝ} (hB : Continuous B)
    (hB0 : ∀ x, 0 ≤ B x) (p : Vec d) :
    kuhnDirichletInf B (S₀.image (dilateKuhnCell k R c))
        (cellAffineMap k c '' U) p ≤
      ((3 : ℝ) ^ (k : ℤ)) ^ d *
        kuhnDirichletInf (fun y => B (cellAffineMap k c y)) S₀ U p := by
  have hpos : (0 : ℝ) < ((3 : ℝ) ^ (k : ℤ)) ^ d :=
    pow_pos (three_zpow_pos' (k : ℤ)) d
  have hkey : kuhnDirichletInf B (S₀.image (dilateKuhnCell k R c))
      (cellAffineMap k c '' U) p / ((3 : ℝ) ^ (k : ℤ)) ^ d ≤
      kuhnDirichletInf (fun y => B (cellAffineMap k c y)) S₀ U p := by
    refine le_csInf (kuhnDiscreteEnergy_image_nonempty _ _ _ _) ?_
    rintro E ⟨q, hq, rfl⟩
    rw [div_le_iff₀ hpos]
    obtain ⟨c₀, hc₀⟩ := hq
    have hle := kuhnDirichletInf_le (B := B)
      (S := S₀.image (dilateKuhnCell k R c)) (U := cellAffineMap k c '' U) hB hB0 p
      (transportKuhnCompetitor k R c hS hU c₀)
    have hslope : (transportKuhnCompetitor k R c hS hU c₀).slope =
        dilateSlopes k R c q := by
      rw [← hc₀]
      rfl
    rw [hslope, kuhnDiscreteEnergy_dilate k R c hS B p q] at hle
    calc kuhnDirichletInf B (S₀.image (dilateKuhnCell k R c))
            (cellAffineMap k c '' U) p
        ≤ ((3 : ℝ) ^ (k : ℤ)) ^ d *
            kuhnDiscreteEnergy (fun y => B (cellAffineMap k c y)) S₀ U p q := hle
      _ = kuhnDiscreteEnergy (fun y => B (cellAffineMap k c y)) S₀ U p q *
            ((3 : ℝ) ^ (k : ℤ)) ^ d := mul_comm _ _
  calc kuhnDirichletInf B (S₀.image (dilateKuhnCell k R c))
        (cellAffineMap k c '' U) p
      = kuhnDirichletInf B (S₀.image (dilateKuhnCell k R c))
          (cellAffineMap k c '' U) p / ((3 : ℝ) ^ (k : ℤ)) ^ d *
          ((3 : ℝ) ^ (k : ℤ)) ^ d := by
        field_simp
    _ ≤ kuhnDirichletInf (fun y => B (cellAffineMap k c y)) S₀ U p *
          ((3 : ℝ) ^ (k : ℤ)) ^ d := mul_le_mul_of_nonneg_right hkey hpos.le
    _ = ((3 : ℝ) ^ (k : ℤ)) ^ d *
          kuhnDirichletInf (fun y => B (cellAffineMap k c y)) S₀ U p := mul_comm _ _

/-- **The normalized covariance**, in the shape the induction consumes. -/
theorem normalized_kuhnDirichletInf_dilate_le (k R : ℕ) (c : Fin d → ℤ)
    {U : Set (Vec d)} {S₀ : Finset (KuhnCell d)}
    (hS : ∀ V ∈ S₀, V.supportCube.scale = -(R : ℤ)) (hU : MeasurableSet U)
    (hvol : 0 < (volume U).toReal) {B : Vec d → ℝ} (hB : Continuous B)
    (hB0 : ∀ x, 0 ≤ B x) (p : Vec d) :
    (volume (cellAffineMap k c '' U)).toReal⁻¹ *
        kuhnDirichletInf B (S₀.image (dilateKuhnCell k R c))
          (cellAffineMap k c '' U) p ≤
      (volume U).toReal⁻¹ *
        kuhnDirichletInf (fun y => B (cellAffineMap k c y)) S₀ U p := by
  have hpos : (0 : ℝ) < ((3 : ℝ) ^ (k : ℤ)) ^ d :=
    pow_pos (three_zpow_pos' (k : ℤ)) d
  have hvolimg : (volume (cellAffineMap k c '' U)).toReal =
      ((3 : ℝ) ^ (k : ℤ)) ^ d * (volume U).toReal :=
    volume_toReal_image_cellAffineMap k c U
  rw [hvolimg]
  have hle := kuhnDirichletInf_dilate_le k R c hS hU hB hB0 p
  have hmul := mul_le_mul_of_nonneg_left hle
    (le_of_lt (inv_pos.mpr (mul_pos hpos hvol)))
  refine hmul.trans (le_of_eq ?_)
  field_simp

/-! ## Passing to the full cube mesh -/

theorem mem_kuhnSlopeSet_of_subset {U : Set (Vec d)} {S₀ S : Finset (KuhnCell d)}
    (hsub : S₀ ⊆ S) {q : KuhnCell d → Vec d} (hq : q ∈ kuhnSlopeSet U S) :
    q ∈ kuhnSlopeSet U S₀ := by
  obtain ⟨c, hc⟩ := hq
  exact ⟨⟨c.toH10Function, c.slope, fun T hT => c.isCellwiseSlope T (hsub hT)⟩, hc⟩

theorem kuhnDiscreteEnergy_of_subset {B : Vec d → ℝ} {S₀ S : Finset (KuhnCell d)}
    {U : Set (Vec d)} (hsub : S₀ ⊆ S)
    (hzero : ∀ T ∈ S, T ∉ S₀ → volume.real (U ∩ T.openCarrier) = 0)
    (p : Vec d) (q : KuhnCell d → Vec d) :
    kuhnDiscreteEnergy B S U p q = kuhnDiscreteEnergy B S₀ U p q := by
  refine (Finset.sum_subset hsub fun T hT hTn => ?_).symm
  rw [hzero T hT hTn, zero_mul]

/-- **The mesh restriction.**  Dropping the cells that miss the domain leaves the
discrete minimum no larger, because their weights vanish and every conforming
competitor for the larger mesh is one for the smaller. -/
theorem kuhnDirichletInf_mono_subset {B : Vec d → ℝ} {S₀ S : Finset (KuhnCell d)}
    {U : Set (Vec d)} (hsub : S₀ ⊆ S)
    (hzero : ∀ T ∈ S, T ∉ S₀ → volume.real (U ∩ T.openCarrier) = 0)
    (hB : Continuous B) (hB0 : ∀ x, 0 ≤ B x) (p : Vec d) :
    kuhnDirichletInf B S₀ U p ≤ kuhnDirichletInf B S U p := by
  refine le_csInf (kuhnDiscreteEnergy_image_nonempty B S U p) ?_
  rintro E ⟨q, hq, rfl⟩
  rw [kuhnDiscreteEnergy_of_subset hsub hzero p q]
  exact csInf_le (bddBelow_kuhnDiscreteEnergy_image hB hB0 p)
    ⟨q, mem_kuhnSlopeSet_of_subset hsub hq, rfl⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section5Support
