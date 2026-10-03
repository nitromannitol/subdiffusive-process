module

public import SubdiffusiveProcess.Besov.DetachAssembly
public import SubdiffusiveProcess.Besov.DetachReal
public import SubdiffusiveProcess.CoarseGrainingVocab.Norms

@[expose] public section

/-!
# The detach inequality `\eqref{e.nabla.u.detach}` on the unit cube

`detach_main`: there is `C > 0` such that for every `s ∈ (0,1)` and every `H ∈ H¹(Q₀)`,
`sup_j exactOverlapDepthTerm Q₀ (1-s) 2 H j ≤ C · paperScaleNormalizedNegativeBesovVectorNorm Q₀ s (finite 1) ∇H`.
-/

open MeasureTheory
open Homogenization

namespace SubdiffusiveProcess.Besov.Detach

noncomputable section

theorem overlapDepthSeminorm_eq {d : ℕ} (σ : ℝ) (u : Vec d → ℝ) (j : ℕ) :
    cubeBesovOverlapDepthSeminorm (originCube d 0) σ (2 : ENNReal) u j =
      (3 : ℝ) ^ ((j : ℝ) * σ) *
        Real.sqrt (ScalarOverlap.centersAverage (originCube d 0) j
          (fun S => (cubeBesovOverlapOscillation S 2 u) ^ 2)) := by
  unfold cubeBesovOverlapDepthSeminorm cubeBesovOverlapDepthWeight cubeBesovDepthWeight
    cubeBesovOverlapDepthAverage
  simp only [cubeScaleFactor_originCube, zpow_zero, ENNReal.toReal_ofNat, one_div]
  congr 1
  · rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  · rw [Real.sqrt_eq_rpow, one_div]
    congr 1
    congr 1
    funext S
    rw [Real.rpow_two]

theorem exactDepthTerm_eq {d : ℕ} (σ : ℝ) (H : H1Function (openCubeSet (originCube d 0)))
    (hu : ExactOverlapIntegrable (originCube d 0) H.toFun) (j : ℕ) :
    exactOverlapDepthTerm (originCube d 0) σ 2 H.toFun hu j =
      ENNReal.ofReal (cubeBesovOverlapDepthSeminorm (originCube d 0) σ (2 : ENNReal) H.toFun j) := by
  have hmem : MemLp H.toFun (ENNReal.ofReal 2) (normalizedCubeMeasure (originCube d 0)) := by
    have h1 : MemLp H.toFun 2 (volume.restrict (openCubeSet (originCube d 0))) := H.memL2
    have h2 : volume.restrict (cubeSet (originCube d 0)) =
        volume.restrict (openCubeSet (originCube d 0)) :=
      Measure.restrict_congr_set (cubeSet_ae_eq_openCubeSet _)
    rw [ENNReal.ofReal_ofNat]
    unfold normalizedCubeMeasure cubeMeasure
    rw [h2]
    exact h1.smul_measure ENNReal.ofReal_ne_top
  have := exactOverlapDepthTerm_eq_ofReal_cubeBesovOverlapDepthSeminorm (originCube d 0) σ 2
    (by norm_num) H.toFun hmem j
  simp only [ENNReal.ofReal_ofNat] at this
  exact this

theorem negBesovDepthSeminorm_eq {d : ℕ} (s : ℝ) (H : H1Function (openCubeSet (originCube d 0)))
    (m : ℕ) :
    Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm (originCube d 0) s H.grad m =
      (3 : ℝ) ^ (-s * (m : ℝ)) * gradX H m := by
  unfold Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm
    Homogenization.Book.Ch03.negativeBesovVectorDepthAverage gradX
  have h : descendantsAverage (originCube d 0) m (fun R => vecNormSq (cubeAverageVec R H.grad)) =
      ∑ i : Fin d, theta (originCube d 0) m (fun x => H.grad x i) := by
    unfold descendantsAverage theta vecNormSq vecDot cubeAverageVec
    simp only [pow_two]
    rw [Finset.sum_comm, Finset.mul_sum]
    rfl
  rw [h]
  rfl

theorem paperNorm_eq {d : ℕ} (s : ℝ) (H : H1Function (openCubeSet (originCube d 0))) :
    SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm (originCube d 0) s
        (.finite 1) H.grad =
      s * sSup (Set.range fun N : ℕ =>
        ∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ (-s * (m : ℝ)) * gradX H m) := by
  unfold SubdiffusiveProcess.CoarseGrainingVocab.paperScaleNormalizedNegativeBesovVectorNorm
    Homogenization.Book.Ch03.scaleNormalizedNegativeBesovVectorNorm
    Homogenization.Book.Ch03.negativeBesovVectorPartialNormFinite
  simp only [div_one, Real.rpow_eq_pow, Real.rpow_one]
  have hfun : (fun N : ℕ => ∑ m ∈ Finset.range (N + 1),
      Homogenization.Book.Ch03.negativeBesovVectorDepthSeminorm (originCube d 0) s H.grad m) =
      fun N : ℕ => ∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ (-s * (m : ℝ)) * gradX H m :=
    funext fun N => Finset.sum_congr rfl fun m _ => negBesovDepthSeminorm_eq s H m
  rw [hfun]

theorem tsum_le_sSup_partial (y : ℕ → ℝ) (hy0 : ∀ m, 0 ≤ y m) (hy : Summable y) :
    ∑' m, y m ≤ sSup (Set.range fun N : ℕ => ∑ m ∈ Finset.range (N + 1), y m) := by
  have hbdd : BddAbove (Set.range fun N : ℕ => ∑ m ∈ Finset.range (N + 1), y m) := by
    refine ⟨∑' m, y m, ?_⟩
    rintro _ ⟨N, rfl⟩
    exact hy.sum_le_tsum _ (fun i _ => hy0 i)
  have hnn : 0 ≤ sSup (Set.range fun N : ℕ => ∑ m ∈ Finset.range (N + 1), y m) :=
    Real.sSup_nonneg (by
      rintro _ ⟨N, rfl⟩
      exact Finset.sum_nonneg fun i _ => hy0 i)
  refine Real.tsum_le_of_sum_range_le hy0 (fun n => ?_)
  cases n with
  | zero => simpa using hnn
  | succ N => exact le_csSup hbdd ⟨N, rfl⟩

theorem iSup_ofReal_toReal_le (t : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (ht : ∀ j, t j ≤ B) :
    (⨆ j : ℕ, ENNReal.ofReal (t j)).toReal ≤ B := by
  apply ENNReal.toReal_le_of_le_ofReal hB
  exact iSup_le fun j => ENNReal.ofReal_le_ofReal (ht j)

theorem depth_term_le {d : ℕ} [NeZero d] (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (H : H1Function (openCubeSet (originCube d 0))) (j : ℕ) :
    cubeBesovOverlapDepthSeminorm (originCube d 0) (1 - s) (2 : ENNReal) H.toFun j ≤
      2 * Cd d * s * ∑' m : ℕ, (3 : ℝ) ^ (-s * (m : ℝ)) * gradX H m := by
  obtain ⟨G, hG⟩ := gradX_bdd H
  have hD := depth_bound H j
  have hR := detach_real s hs0 hs1 (gradX H) (gradX_nonneg H) (gradX_mono H) G hG j
  have hw : 0 ≤ (3 : ℝ) ^ ((j : ℝ) * (1 - s)) := Real.rpow_nonneg (by norm_num) _
  rw [overlapDepthSeminorm_eq]
  calc (3 : ℝ) ^ ((j : ℝ) * (1 - s)) *
        Real.sqrt (ScalarOverlap.centersAverage (originCube d 0) j
          (fun S => (cubeBesovOverlapOscillation S 2 H.toFun) ^ 2))
      ≤ (3 : ℝ) ^ ((j : ℝ) * (1 - s)) *
        (Cd d * ∑' k : ℕ, ((3 : ℝ) ^ (j + 1 + k))⁻¹ * gradX H (j + 1 + k)) :=
        mul_le_mul_of_nonneg_left hD hw
    _ = Cd d * ((3 : ℝ) ^ ((j : ℝ) * (1 - s)) *
        ∑' k : ℕ, ((3 : ℝ) ^ (j + 1 + k))⁻¹ * gradX H (j + 1 + k)) := by ring
    _ ≤ Cd d * (2 * s * ∑' m : ℕ, (3 : ℝ) ^ (-s * (m : ℝ)) * gradX H m) :=
        mul_le_mul_of_nonneg_left hR (Cd_nonneg d)
    _ = 2 * Cd d * s * ∑' m : ℕ, (3 : ℝ) ^ (-s * (m : ℝ)) * gradX H m := by ring



theorem detach_main (d : ℕ) [NeZero d] :
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
  refine ⟨2 * Cd d + 1, by linarith [Cd_nonneg d], ?_⟩
  intro s hs H hu
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨G, hG⟩ := gradX_bdd H
  have hy0 : ∀ m : ℕ, 0 ≤ (3 : ℝ) ^ (-s * (m : ℝ)) * gradX H m := fun m =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (gradX_nonneg H m)
  have hysum : Summable (fun m : ℕ => (3 : ℝ) ^ (-s * (m : ℝ)) * gradX H m) :=
    summable_weighted s hs0 (gradX H) (gradX_nonneg H) G hG
  have hS : 0 ≤ sSup (Set.range fun N : ℕ =>
      ∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ (-s * (m : ℝ)) * gradX H m) :=
    Real.sSup_nonneg (by
      rintro _ ⟨N, rfl⟩
      exact Finset.sum_nonneg fun m _ => hy0 m)
  have hT : ∀ j : ℕ,
      cubeBesovOverlapDepthSeminorm (originCube d 0) (1 - s) (2 : ENNReal) H.toFun j ≤
        2 * Cd d * s * sSup (Set.range fun N : ℕ =>
          ∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ (-s * (m : ℝ)) * gradX H m) := by
    intro j
    refine (depth_term_le s hs0 hs1 H j).trans ?_
    exact mul_le_mul_of_nonneg_left (tsum_le_sSup_partial _ hy0 hysum)
      (by have := Cd_nonneg d; positivity)
  have hB : 0 ≤ 2 * Cd d * s * sSup (Set.range fun N : ℕ =>
      ∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ (-s * (m : ℝ)) * gradX H m) := by
    have := Cd_nonneg d
    positivity
  have hlhs : (iSup fun j : ℕ => exactOverlapDepthTerm (originCube d 0) (1 - s) 2 H.toFun hu j) =
      ⨆ j : ℕ, ENNReal.ofReal
        (cubeBesovOverlapDepthSeminorm (originCube d 0) (1 - s) (2 : ENNReal) H.toFun j) := by
    congr 1
    funext j
    exact exactDepthTerm_eq (1 - s) H hu j
  rw [hlhs, paperNorm_eq]
  refine (iSup_ofReal_toReal_le _ _ hB hT).trans ?_
  have : 0 ≤ s * sSup (Set.range fun N : ℕ =>
      ∑ m ∈ Finset.range (N + 1), (3 : ℝ) ^ (-s * (m : ℝ)) * gradX H m) := mul_nonneg hs0.le hS
  nlinarith [Cd_nonneg d]

end

end SubdiffusiveProcess.Besov.Detach
