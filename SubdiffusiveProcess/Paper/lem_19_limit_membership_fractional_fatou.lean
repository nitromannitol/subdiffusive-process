module

public import SubdiffusiveProcess.Paper.lem_19_limit_membership_ae_subsequence

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set TopologicalSpace
open SubdiffusiveProcess Homogenization
open scoped ENNReal NNReal Topology ContDiff

noncomputable section
namespace Paper

/-- Fine proof step of Lemma 19 (paper 1943--1945).
Carried-input tick list:
- SOURCE: the fixed cube, the H3/4 representatives `w`, the L2 class `vlim`,
  and the subsequence `sigma` with its a.e. convergence, supplied by
  `lem_19_limit_membership_ae_subsequence`.
- CONCLUDED HERE: the lower-semicontinuity inequality for the concrete
  nonnegative Gagliardo integral, with the limit class represented by the
  constant-coordinate family `fun _ : Fin 1 => vlim`.
No fractional membership of the limit is assumed; finiteness is obtained
from this inequality together with the uniform bound in the parent. -/
theorem lem_19_limit_membership_fractional_fatou
    (d : ℕ) (hd : 2 ≤ d) (z : SpatialCoordinates d)
    (r : ℝ) (hr : 0 < r)
    (threeQuarters : Set.Ioo (0 : ℝ) 1)
    (hthree : (threeQuarters : ℝ) = 3 / 4)
    (w : ℕ → CubeFractionalL2 (k := 1) hd z r hr threeQuarters)
    (vlim : DomainL2 (centeredCube z r hr))
    (sigma : ℕ → ℕ) (hsigma : StrictMono sigma)
    (hae : ∀ᵐ x ∂volume.restrict
        (centeredCube z r hr : Set (SpatialCoordinates d)),
      Tendsto (fun j : ℕ => (w (sigma j)).val 0 x) atTop
        (𝓝 (vlim x))) :
    cubeFractionalL2Seminorm hd z r hr threeQuarters
        (fun _ : Fin 1 => vlim) ≤
      liminf (fun j : ℕ =>
        cubeFractionalL2Seminorm hd z r hr threeQuarters (w (sigma j)).val)
        atTop := by
  let U : Set (SpatialCoordinates d) :=
    (centeredCube z r hr : Set (SpatialCoordinates d))
  let μ : Measure (SpatialCoordinates d) := volume.restrict U
  let exponent : ℝ := (d : ℝ) + 2 * (threeQuarters : ℝ)
  let den : (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞ := fun p =>
    (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (p.1 j - p.2 j) ^ 2))) ^ exponent
  let q : ℕ → (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal (((w (sigma n)).val 0 p.1 - (w (sigma n)).val 0 p.2) ^ 2) /
      den p
  let qlim : (SpatialCoordinates d × SpatialCoordinates d) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((vlim p.1 - vlim p.2) ^ 2) / den p
  let I : ℕ → ℝ≥0∞ := fun n => ∫⁻ p, q n p ∂μ.prod μ
  let Ilim : ℝ≥0∞ := ∫⁻ p, qlim p ∂μ.prod μ

  have hden : Measurable den := by
    dsimp [den, exponent]
    fun_prop

  have hfn (n : ℕ) :
      AEMeasurable ((w (sigma n)).val 0) μ := by
    exact (Lp.aestronglyMeasurable ((w (sigma n)).val 0)).aemeasurable

  have hnum (n : ℕ) :
      AEMeasurable
        (fun p : SpatialCoordinates d × SpatialCoordinates d =>
          ENNReal.ofReal (((w (sigma n)).val 0 p.1 - (w (sigma n)).val 0 p.2) ^ 2))
        (μ.prod μ) := by
    apply AEMeasurable.ennreal_ofReal
    exact ((hfn n).comp_fst.sub (hfn n).comp_snd).pow_const 2

  have hq (n : ℕ) : AEMeasurable (q n) (μ.prod μ) := by
    exact (hnum n).div hden.aemeasurable

  have hlimfn : AEMeasurable vlim μ := by
    exact (Lp.aestronglyMeasurable vlim).aemeasurable

  have hnumlim :
      AEMeasurable
        (fun p : SpatialCoordinates d × SpatialCoordinates d =>
          ENNReal.ofReal ((vlim p.1 - vlim p.2) ^ 2))
        (μ.prod μ) := by
    apply AEMeasurable.ennreal_ofReal
    exact (hlimfn.comp_fst.sub hlimfn.comp_snd).pow_const 2

  have hqlim : AEMeasurable qlim (μ.prod μ) := by
    exact hnumlim.div hden.aemeasurable

  have hae' : ∀ᵐ x ∂μ,
      Tendsto (fun j : ℕ => (w (sigma j)).val 0 x) atTop (𝓝 (vlim x)) := by
    simpa only [μ, U] using hae

  have hfst : ∀ᵐ p ∂μ.prod μ,
      Tendsto (fun j : ℕ => (w (sigma j)).val 0 p.1) atTop (𝓝 (vlim p.1)) := by
    simpa only [Function.comp_apply] using!
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hae'

  have hsnd : ∀ᵐ p ∂μ.prod μ,
      Tendsto (fun j : ℕ => (w (sigma j)).val 0 p.2) atTop (𝓝 (vlim p.2)) := by
    simpa only [Function.comp_apply] using!
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hae'

  have hq_tendsto : ∀ᵐ p ∂μ.prod μ,
      Tendsto (fun n : ℕ => q n p) atTop (𝓝 (qlim p)) := by
    filter_upwards [hfst, hsnd] with p hp hq'
    rcases p with ⟨x, y⟩
    by_cases hxy : x = y
    · subst y
      simp [q, qlim]
    · have hcoord : ∃ j : Fin d, x j ≠ y j := by
        by_contra h
        push_neg at h
        exact hxy (funext h)
      have hsum : 0 < ∑ j : Fin d, (x j - y j) ^ 2 := by
        classical
        exact Finset.sum_pos' (fun j _ => sq_nonneg (x j - y j))
          ⟨hcoord.choose, Finset.mem_univ _,
            sq_pos_of_ne_zero (sub_ne_zero.mpr hcoord.choose_spec)⟩
      have hden0 : den (x, y) ≠ 0 := by
        dsimp [den, exponent]
        apply ne_of_gt
        apply ENNReal.rpow_pos_of_nonneg
        · exact ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hsum)
        · positivity
      have hdiff :
          Tendsto
            (fun n : ℕ => (w (sigma n)).val 0 x - (w (sigma n)).val 0 y)
            atTop (𝓝 (vlim x - vlim y)) := hp.sub hq'
      have hsq :
          Tendsto
            (fun n : ℕ => ((w (sigma n)).val 0 x - (w (sigma n)).val 0 y) ^ 2)
            atTop (𝓝 ((vlim x - vlim y) ^ 2)) := hdiff.pow 2
      have hnum_tendsto :
          Tendsto
            (fun n : ℕ =>
              ENNReal.ofReal
                (((w (sigma n)).val 0 x - (w (sigma n)).val 0 y) ^ 2))
            atTop (𝓝 (ENNReal.ofReal ((vlim x - vlim y) ^ 2))) :=
        ENNReal.tendsto_ofReal hsq
      simpa [q, qlim] using
        (ENNReal.Tendsto.div_const hnum_tendsto (Or.inr hden0))

  have hfatou : Ilim ≤ liminf (fun n : ℕ => I n) atTop := by
    calc
      Ilim = ∫⁻ p, liminf (fun n : ℕ => q n p) atTop ∂μ.prod μ := by
        apply lintegral_congr_ae
        filter_upwards [hq_tendsto] with p hp
        exact hp.liminf_eq.symm
      _ ≤ liminf (fun n : ℕ => I n) atTop := by
        exact MeasureTheory.lintegral_liminf_le' hq

  have htonelli (n : ℕ) :
      I n = ∫⁻ x, ∫⁻ y, q n (x, y) ∂μ ∂μ := by
    exact MeasureTheory.lintegral_prod (q n) (hq n)

  have htonelli_lim :
      Ilim = ∫⁻ x, ∫⁻ y, qlim (x, y) ∂μ ∂μ := by
    exact MeasureTheory.lintegral_prod qlim hqlim

  let c : ℝ≥0∞ := ENNReal.ofReal (threeQuarters : ℝ) / volume U
  have hvol0 : volume U ≠ 0 := by
    simp only [U, centeredCube_volume]
    exact ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hr d)
  have hvoltop : volume U ≠ (⊤ : ℝ≥0∞) := by
    simp [U, centeredCube_volume]
  have hc0 : c ≠ 0 := by
    dsimp [c]
    exact ENNReal.div_ne_zero.mpr
      ⟨ENNReal.ofReal_ne_zero_iff.mpr threeQuarters.2.1, hvoltop⟩
  have hctop : c ≠ (⊤ : ℝ≥0∞) := by
    dsimp [c]
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top hvol0
  have hcunit : IsUnit c := ENNReal.isUnit_iff.mpr ⟨hc0, hctop⟩
  have hmul_liminf :
      c * Ilim ≤ liminf (fun n : ℕ => c * I n) atTop := by
    have hmap :
        c * liminf (fun n : ℕ => I n) atTop =
          liminf (fun n : ℕ => c * I n) atTop := by
      simpa only [Function.comp_apply] using!
        (ENNReal.mulLeftOrderIso c hcunit).liminf_apply
    calc
      c * Ilim ≤ c * liminf (fun n : ℕ => I n) atTop := by
        gcongr
      _ = liminf (fun n : ℕ => c * I n) atTop := hmap
  have hraw :
      (c * Ilim) ^ (1 / 2 : ℝ) ≤
        liminf (fun n : ℕ => (c * I n) ^ (1 / 2 : ℝ)) atTop := by
    have hmap :
        (liminf (fun n : ℕ => c * I n) atTop) ^ (1 / 2 : ℝ) =
          liminf (fun n : ℕ => (c * I n) ^ (1 / 2 : ℝ)) atTop := by
      simpa only [Function.comp_apply] using!
        (ENNReal.orderIsoRpow (1 / 2 : ℝ) (by norm_num)).liminf_apply
    exact (ENNReal.rpow_le_rpow hmul_liminf (by norm_num)).trans_eq hmap

  have hleft :
      cubeFractionalL2Seminorm hd z r hr threeQuarters
          (fun _ : Fin 1 => vlim) = (c * Ilim) ^ (1 / 2 : ℝ) := by
    have h := congrArg (fun t : ℝ≥0∞ => (c * t) ^ (1 / 2 : ℝ)) htonelli_lim
    simpa [cubeFractionalL2Seminorm, c, Ilim, qlim, μ, U, den, exponent] using h.symm

  have hright (n : ℕ) :
      cubeFractionalL2Seminorm hd z r hr threeQuarters
          (w (sigma n)).val = (c * I n) ^ (1 / 2 : ℝ) := by
    have h := congrArg (fun t : ℝ≥0∞ => (c * t) ^ (1 / 2 : ℝ)) (htonelli n)
    simpa [cubeFractionalL2Seminorm, c, I, q, μ, U, den, exponent] using h.symm

  rw [hleft]
  simp_rw [hright]
  exact hraw

end Paper
