import SubdiffusiveProcess.Analysis.FractionalFaceAbsorption
import SubdiffusiveProcess.Analysis.CubeFaceH10Weight
import SubdiffusiveProcess.Analysis.CubeFractionalH1Finite
import SubdiffusiveProcess.Sobolev.NativeH10

open MeasureTheory Filter Set Homogenization SubdiffusiveProcess.Lane4
open scoped ENNReal NNReal Topology
noncomputable section
attribute [local instance] Classical.propDecidable
namespace SubdiffusiveProcess


/-- Maximum-norm distance to the boundary of the unit cube. -/
def cubeBoundaryDistance {d : ℕ} (x : SpatialCoordinates d) : ℝ := 1 / 2 - ‖x‖

def cubeBoundaryWeightedIntegral {d : ℕ} (s : ℝ) (f : SpatialCoordinates d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in cubeExtensionBox d, ENNReal.ofReal (f x ^ 2) *
    ENNReal.ofReal (cubeBoundaryDistance x) ^ (-(2 * s))

theorem cubeBoundaryDistance_pos {d : ℕ} {x : SpatialCoordinates d}
    (hx : x ∈ cubeExtensionBox d) : 0 < cubeBoundaryDistance x := by
  rw [cubeExtensionBox_eq] at hx
  change ‖x - 0‖ < 1 / 2 at hx
  change 0 < 1 / 2 - ‖x‖
  have hn : ‖x‖ < 1 / 2 := by simpa using hx
  linarith

theorem cubeBoundaryWeight_le_sum_faces {d : ℕ} (hd : 0 < d) (s : ℝ) (hs : 0 ≤ s)
    {x : SpatialCoordinates d} (hx : x ∈ cubeExtensionBox d) :
    ENNReal.ofReal (cubeBoundaryDistance x) ^ (-(2 * s)) ≤
      ∑ upper : Bool, ∑ i : Fin d, cubeFaceWeight s upper i x := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i : Fin d => |x i|)
    Finset.univ_nonempty
  have hn : ‖x‖ = |x i| := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (abs_nonneg (x i))).mpr
      intro j
      simpa only [Real.norm_eq_abs] using hi j (Finset.mem_univ j)
    · simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  obtain ⟨upper, he⟩ : ∃ upper : Bool, cubeFaceDistance upper i x = cubeBoundaryDistance x := by
    by_cases hxi : 0 ≤ x i
    · exact ⟨true, by simp [cubeFaceDistance, cubeBoundaryDistance, hn, abs_of_nonneg hxi]⟩
    · exact ⟨false, by simp [cubeFaceDistance, cubeBoundaryDistance, hn, abs_of_neg (lt_of_not_ge hxi)]; ring⟩
  calc
    _ = cubeFaceWeight s upper i x := by rw [cubeFaceWeight, he]
    _ ≤ ∑ j : Fin d, cubeFaceWeight s upper j x := Finset.single_le_sum
      (f := fun j : Fin d => cubeFaceWeight s upper j x)
      (fun _ _ => zero_le _) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum
      (f := fun b : Bool => ∑ j : Fin d, cubeFaceWeight s b j x)
      (fun _ _ => zero_le _) (Finset.mem_univ upper)

/-- The Hardy constant depends only on d,s; zero trace is used only for weighted finiteness. -/
theorem exists_cubeBoundary_fractional_hardy (d : ℕ) (hd : 0 < d)
    (s : ℝ) (hs : 1 / 2 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : H10Function (cubeExtensionBox d)),
      Measurable (u : SpatialCoordinates d → ℝ) →
      cubeBoundaryWeightedIntegral s u ≤ ENNReal.ofReal C * unitCubeFractionalEnergy s u := by
  obtain ⟨C, hC, hface⟩ := exists_cubeFace_fractional_hardy d hd s hs
  refine ⟨(2 * d : ℝ) * C, by positivity, ?_⟩
  intro u hu
  have hs0 : 0 ≤ s := by linarith
  let F : SpatialCoordinates d → ℝ≥0∞ := fun x => ENNReal.ofReal (u x ^ 2)
  have hF : Measurable F := (hu.pow_const 2).ennreal_ofReal
  have hW : ∀ upper : Bool, ∀ i : Fin d,
      Measurable (fun x => F x * cubeFaceWeight s upper i x) :=
    fun upper i => hF.mul (measurable_cubeFaceWeight s upper i)
  calc
    cubeBoundaryWeightedIntegral s u ≤
        ∫⁻ x in cubeExtensionBox d, ∑ upper : Bool, ∑ i : Fin d,
          F x * cubeFaceWeight s upper i x := by
      apply setLIntegral_mono' (measurableSet_cubeExtensionBox d)
      intro x hx
      have h := cubeBoundaryWeight_le_sum_faces hd s hs0 hx
      calc
        _ ≤ F x * (∑ upper : Bool, ∑ i : Fin d, cubeFaceWeight s upper i x) :=
          mul_le_mul_of_nonneg_left h (zero_le _)
        _ = _ := by simp only [Finset.mul_sum]
    _ = ∑ upper : Bool, ∑ i : Fin d, cubeFaceWeightedIntegral s upper i u := by
      rw [lintegral_finset_sum Finset.univ
        (fun upper _ => Finset.measurable_sum Finset.univ (fun i _ => hW upper i))]
      apply Finset.sum_congr rfl
      intro upper _
      exact lintegral_finset_sum Finset.univ (fun i _ => hW upper i)
    _ ≤ ∑ _upper : Bool, ∑ _i : Fin d, ENNReal.ofReal C * unitCubeFractionalEnergy s u := by
      apply Finset.sum_le_sum
      intro upper _
      apply Finset.sum_le_sum
      intro i _
      exact hface upper i u hu (cubeFaceWeightedIntegral_ne_top_of_H10Function s hs1 u upper i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_bool,
        nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * d by positivity)]
      rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
      simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
      ring

end SubdiffusiveProcess
