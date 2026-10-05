module

public import SubdiffusiveProcess.Static.HarmonicCutoffPatching
public import SubdiffusiveProcess.Static.HarmonicCutoffMaximum
public import SubdiffusiveProcess.CoarseGrainingVocab.DirichletUniqueness

@[expose] public section

/-! # Native harmonic cells supply the cutoff patching hypotheses -/

open MeasureTheory Homogenization SubdiffusiveProcess.CoarseGrainingVocab SubdiffusiveProcess Metric
open scoped ENNReal NNReal

noncomputable section
namespace SubdiffusiveProcess.Static

variable {d : ℕ}

/-- Restriction of the smooth cutoff datum to a grid cell. -/
def smoothCellDatum {h : ℝ} (_hh : 0 < h) (f : (Fin d → ℝ) → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (k : Fin d → ℤ) :
    H1Function (aux_hcut_cell h k) :=
  H1Function.ofContDiff isOpen_ball (hf.of_le (by simp)) hfc

/-- A continuous positive scalar coefficient is uniformly elliptic on each fixed cell. -/
theorem exists_cell_ellipticity (A : (Fin d → ℝ) → ℝ) (hA : Continuous A)
    (hApos : ∀ x, 0 < A x) {h : ℝ} (_hh : 0 < h) (k : Fin d → ℤ) :
    ∃ lam Lam : ℝ, 0 < lam ∧
      (∀ x ∈ aux_hcut_cell h k, lam ≤ A x ∧ A x ≤ Lam) ∧
      IsEllipticFieldOn lam Lam (aux_hcut_cell h k) (scalarCoeffField A) := by
  have hcompact := isCompact_closedBall (aux_hcut_cc h k) (h / 2)
  obtain ⟨lam, hlam, hlamb⟩ := hcompact.exists_forall_le' hA.continuousOn
    (a := (0 : ℝ)) (fun x _ => hApos x)
  obtain ⟨Lam, hLamb⟩ := hcompact.exists_bound_of_continuousOn hA.continuousOn
  have hb : ∀ x ∈ aux_hcut_cell h k, lam ≤ A x ∧ A x ≤ Lam := by
    intro x hx
    have hx' := ball_subset_closedBall hx
    exact ⟨hlamb x hx', (le_abs_self _).trans (hLamb x hx')⟩
  exact ⟨lam, Lam, hlam, hb,
    isEllipticFieldOn_scalar measurableSet_ball hA.measurable hlam hb⟩

/-- Native Dirichlet energy growth on the transition cells constructs a cutoff
with a global plateau, compact interior support, and all-radius energy growth. -/
theorem exists_harmonic_cutoff_of_cell_energy_growth
    (hd : 1 ≤ d) (A : (Fin d → ℝ) → ℝ) (hA : Continuous A)
    (hApos : ∀ x, 0 < A x) (R1 R2 h G : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1 / 2) (hG : 0 ≤ G)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hf1 : ∀ x, ‖x‖ ≤ R1 + h → f x = 1)
    (hf0 : ∀ x, R2 - 2 * h ≤ ‖x‖ → f x = 0)
    (hgrowth : ∀ k : Fin d → ℤ, aux_hcut_IsTrans h R1 R2 k →
      ∀ u : H1Function (aux_hcut_cell h k),
        IsWeaklyHarmonicOn A (aux_hcut_cell h k) u →
        HasZeroTraceDifferenceOn (aux_hcut_cell h k) u
          (smoothCellDatum hh f hf (aux_hcut_f_compact hf0) k) →
        ∀ x ∈ aux_hcut_cell h k, ∀ r : ℝ, 0 < r → r ≤ 1 →
          ∫⁻ z in ball x r ∩ aux_hcut_cell h k,
            ENNReal.ofReal (A z * vecDot (u.grad z) (u.grad z)) ≤
              ENNReal.ofReal (G * r ^ ((d : ℝ) - 1 / 2))) :
    ∃ chi : H10Function (ball (0 : Fin d → ℝ) R2),
      (∀ x, 0 ≤ chi.toFun x ∧ chi.toFun x ≤ 1) ∧
      (∀ x ∈ ball (0 : Fin d → ℝ) R1, chi.toFun x = 1) ∧
      tsupport chi.toFun ⊆ ball (0 : Fin d → ℝ) R2 ∧
      ∀ (x : Fin d → ℝ) (r : ℝ), 0 < r → r ≤ 1 →
        ∫⁻ z in ball x r ∩ ball (0 : Fin d → ℝ) R2,
          ENNReal.ofReal (A z * vecDot (chi.grad z) (chi.grad z)) ≤
            ENNReal.ofReal (8 ^ d * G * h ^ (-(1 / 2 : ℝ)) *
              r ^ ((d : ℝ) - 1 / 2)) := by
  have : NeZero d := ⟨by omega⟩
  refine aux_hcut_hcut_core hd A hApos R1 R2 h G hh hh1 hG f hf hf01 hf1 hf0 ?_
  intro k hk
  have hgeom : IsOpenBoundedConvexDomain (aux_hcut_cell h k) :=
    isOpenBoundedConvexDomain_centeredCube (aux_hcut_cc h k) hh
  obtain ⟨lam, Lam, hlam, hb, hEll⟩ := exists_cell_ellipticity A hA hApos hh k
  let datum := smoothCellDatum hh f hf (aux_hcut_f_compact hf0) k
  obtain ⟨u, hu, htr⟩ := exists_isWeaklyHarmonicOn_and_hasZeroTraceDifferenceOn
    hgeom ⟨aux_hcut_cc h k, mem_ball_self (half_pos hh)⟩ hEll datum
  have hbd : ∀ᵐ x ∂(volume.restrict (aux_hcut_cell h k)), lam ≤ A x ∧ A x ≤ Lam := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hb x hx
  have hup := ae_le_of_harmonic hgeom hlam hA.aestronglyMeasurable hbd hu htr
    (M := 1) (fun x _ => (hf01 x).2)
  have hlo := le_ae_of_harmonic hgeom hlam hA.aestronglyMeasurable hbd hu htr
    (m := 0) (fun x _ => (hf01 x).1)
  have henergy := hgrowth k hk u hu htr
  obtain ⟨e, heval, hegrad⟩ := htr
  refine ⟨e, ?_, ?_⟩
  · filter_upwards [hlo, hup] with x hx0 hx1
    change 0 ≤ datum.toFun x + e.toFun x ∧ datum.toFun x + e.toFun x ≤ 1
    rw [← heval x]
    exact ⟨hx0, hx1⟩
  · intro x hx r hr hr1
    have heq : (fun z => ENNReal.ofReal (A z * vecDot
        (aux_hcut_gradVec f z + e.grad z) (aux_hcut_gradVec f z + e.grad z))) =
        fun z => ENNReal.ofReal (A z * vecDot (u.grad z) (u.grad z)) := by
      funext z
      rw [hegrad z]
      rfl
    rw [heq]
    exact henergy x hx r hr hr1

end SubdiffusiveProcess.Static
