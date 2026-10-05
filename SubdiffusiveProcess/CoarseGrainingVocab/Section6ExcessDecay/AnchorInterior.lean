module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section4Support.SubunitGridMaximum
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Covariance.Transport
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.FractionalHolderBridge
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.GoodEventCap
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay.OneStep
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6Schauder.Composition



@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay

open Filter MeasureTheory SubdiffusiveProcess.CoarseGrainingVocab
open Homogenization hiding Vec
open Homogenization.Book
open scoped BigOperators ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}



def HarmonicApproximationInput (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ L m n : ℕ, m ≤ L → n + 5 ≤ m → ∀ z ∈ cube d m,
      ∀ x ∈ truncatedCube d m (n - 3) z,
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemFractionalOn (cube d m) s h.grad →
        ∀ y ∈ cube d m,
          truncatedCube d m (n - 4) x ⊆ translatedCube d (n - 2) y →
          translatedCube d (n - 2) y ⊆ truncatedCube d m (n - 1) x →
          ∀ uD : H1Function (translatedCube d (n - 2) y),
            (∀ q, uD.toFun q = u.toFun q) → (∀ q, uD.grad q = u.grad q) →
          (∃ v : H1Function (translatedCube d (n - 2) y),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
              HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) ∧
          (∀ v v' : H1Function (translatedCube d (n - 2) y),
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD) →
            (IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v' ∧
                HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v' uD) →
            v.toFun =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.toFun ∧
              v.grad =ᵐ[volume.restrict (translatedCube d (n - 2) y)] v'.grad) ∧
          ∀ (v : H1Function (translatedCube d (n - 2) y)),
            IsWeaklyHarmonicOn (fun _ => 1) (translatedCube d (n - 2) y) v →
            HasZeroTraceDifferenceOn (translatedCube d (n - 2) y) v uD →
            indicatorValue (goodEvent M none (n + 2) z 1 (s / 8))
                  (fun _ => normalizedL2On (truncatedCube d m (n - 4) x)
                    (fun q => u.toFun q - v.toFun q)) ω ≤
                C * s ^ (-2 : ℝ) * section6HomogenizationError M (s / 8) L (n + 2) ω z *
                    (normalizedL2On (truncatedCube d m n x)
                      (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) +
                    (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                      s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n *
                        Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                    else 0)) +
                  C * s ^ (-8 : ℝ) *
                    (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                    (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    C * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * n) *
                    (fractionalSeminormOn (truncatedCube d m n x) s h.grad).toReal else 0)



def MathcalECapInput (d : ℕ) : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (64 * M.delta ^ 2) (1 / 2 : ℝ),
      ∀ L m : ℕ, m ≤ L → ∀ ω,
        ∀ epsilon ∈ Set.Icc (s⁻¹ * M.delta ^ 2) 1,
          ω ∈ goodEvent M none m 0 epsilon s →
            section6HomogenizationError M s L m ω 0 ≤ C * epsilon

/-! ### Sign lemmas for the four legs of the right-hand side -/

theorem volumeAverage_nonneg {W : Set (Vec d)} {f : Vec d → ℝ} (hf : ∀ p, 0 ≤ f p) :
    0 ≤ volumeAverage W f :=
  mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (integral_nonneg fun p => hf p)

/-- The tail-coefficient average is nonnegative on every window: the tail
coefficient is `ahom · (a_L/a_{m∧L})`, a product of positive factors. -/
theorem tailAverage_nonneg (M : _root_.SubdiffusiveProcess.Model.GMCModel d) (L m : ℕ)
    (ω : _root_.SubdiffusiveProcess.Model.PotentialSample d) (W : Set (Vec d)) :
    0 ≤ tailAverage M L m ω W :=
  volumeAverage_nonneg fun p =>
    (tailCoefficient_pos_of_ahom_pos M L m ω (ahom_pos M (min m L)) p).le

theorem excess_nonneg (j : ℤ) (W : Set (Vec d)) (u : Vec d → ℝ) : 0 ≤ excess j W u := by
  rw [Section6Iteration.excess_eq_affineExcessScaled]
  exact Section6Iteration.affineExcessScaled_nonneg _ _ _

theorem normalizedL2On_congr_ae {W : Set (Vec d)} {f f' : Vec d → ℝ}
    (hff : f =ᵐ[volume.restrict W] f') : normalizedL2On W f = normalizedL2On W f' := by
  unfold normalizedL2On volumeAverage
  refine congrArg Real.sqrt (congrArg _ (integral_congr_ae ?_))
  filter_upwards [hff] with p hp
  rw [hp]


/-! ### The constant -/

/-- The constant of the interior assembly: the interior Schauder contraction,
the remainder route through the harmonic-approximation constant `CA` and the
`𝓔`-cap constant `CB`, and the crude `k < 6` branch. -/
def anchorInteriorConst (d : ℕ) [NeZero d] (CA CB : ℝ) : ℝ :=
  oneStepContractionConst d * Section6Schauder.schauderInteriorConst d
    + (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) * CA *
        (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
    + 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) + 1

section ConstBounds

variable (d : ℕ) [NeZero d] {CA CB : ℝ}

theorem anchorInteriorConst_contraction_le (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) :
    oneStepContractionConst d * Section6Schauder.schauderInteriorConst d
      ≤ anchorInteriorConst d CA CB := by
  have ha : (0 : ℝ) ≤ 81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1 := by
    have h1 := taylorConst_nonneg d
    have h2 := Section6Schauder.schauderInteriorConst_nonneg d
    nlinarith
  have hb : (0 : ℝ) ≤ CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d := by
    have h1 := Real.sqrt_nonneg ((d : ℝ))
    have h2 := fractionalHolderConst_nonneg d
    linarith
  have h2 : (0 : ℝ) ≤ (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) *
      CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d) :=
    mul_nonneg (mul_nonneg ha hCA) hb
  have h3 : (0 : ℝ) ≤ 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) := by positivity
  rw [anchorInteriorConst]
  linarith

theorem anchorInteriorConst_remainder_le :
    (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) * CA *
        (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
      ≤ anchorInteriorConst d CA CB := by
  have h1 : (0 : ℝ) ≤ oneStepContractionConst d * Section6Schauder.schauderInteriorConst d :=
    mul_nonneg (oneStepContractionConst_nonneg d)
      (Section6Schauder.schauderInteriorConst_nonneg d)
  have h3 : (0 : ℝ) ≤ 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) := by positivity
  rw [anchorInteriorConst]
  linarith

theorem anchorInteriorConst_crude_le (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) :
    3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) ≤ anchorInteriorConst d CA CB := by
  have h1 : (0 : ℝ) ≤ oneStepContractionConst d * Section6Schauder.schauderInteriorConst d :=
    mul_nonneg (oneStepContractionConst_nonneg d)
      (Section6Schauder.schauderInteriorConst_nonneg d)
  have ha : (0 : ℝ) ≤ 81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1 := by
    have h1 := taylorConst_nonneg d
    have h2 := Section6Schauder.schauderInteriorConst_nonneg d
    nlinarith
  have hb : (0 : ℝ) ≤ CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d := by
    have h1 := Real.sqrt_nonneg ((d : ℝ))
    have h2 := fractionalHolderConst_nonneg d
    linarith
  have h2 : (0 : ℝ) ≤ (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) *
      CA * (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d) :=
    mul_nonneg (mul_nonneg ha hCA) hb
  rw [anchorInteriorConst]
  linarith

theorem one_le_anchorInteriorConst (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) :
    (1 : ℝ) ≤ anchorInteriorConst d CA CB := by
  have h := anchorInteriorConst_crude_le d hCA hCB
  have h3 : (1 : ℝ) ≤ 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) := by
    have hs : (1 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ (7 * d)) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (one_le_pow₀ (by norm_num))
    nlinarith
  linarith

theorem anchorInteriorConst_nonneg (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) :
    (0 : ℝ) ≤ anchorInteriorConst d CA CB :=
  le_trans zero_le_one (one_le_anchorInteriorConst d hCA hCB)

theorem anchorInteriorConst_pos (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) :
    (0 : ℝ) < anchorInteriorConst d CA CB :=
  lt_of_lt_of_le zero_lt_one (one_le_anchorInteriorConst d hCA hCB)

end ConstBounds



/-! ### The interior/boundary dichotomy -/

/-- **A window whose centre sees a face of `∂□_m` inside it touches that
frontier.**  If `c` is a coordinate value on a face of `∂□_m` at distance less
than `3^l/2` from `x`, then the point obtained from `x` by moving coordinate
`i₀` to `c` lies in the closure of `U_{m,l}(x)` and on the frontier of `□_m`. -/
theorem boundaryTouches_of_face_value {m l : ℤ} {x : Vec d} (hx : x ∈ cube d m)
    (i₀ : Fin d) {c : ℝ} (hc : |c| = (1 / 2 : ℝ) * (3 : ℝ) ^ m)
    (hcx : |c - x i₀| < (1 / 2 : ℝ) * (3 : ℝ) ^ l) :
    BoundaryTouches (truncatedCube d m l x) (cube d m) := by
  classical
  have hmpos : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by positivity
  have hlpos : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ l := by positivity
  have hxm : ∀ i, |x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hx
    intro i
    rw [abs_lt]
    exact ⟨by linarith [(hx i).1], (hx i).2⟩
  have hmem_cube : ∀ w : Vec d, (∀ i, |w i| < (1 / 2 : ℝ) * (3 : ℝ) ^ m) → w ∈ cube d m := by
    intro w hw
    rw [cube, Homogenization.mem_openCubeSet_originCube_iff]
    intro i
    have hi := abs_lt.mp (hw i)
    exact ⟨by linarith [hi.1], hi.2⟩
  have hmem_trunc : ∀ w : Vec d, (∀ i, |w i - x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ l) →
      (∀ i, |w i| < (1 / 2 : ℝ) * (3 : ℝ) ^ m) → w ∈ truncatedCube d m l x := by
    intro w h1 h2
    refine ⟨?_, hmem_cube w h2⟩
    rw [mem_translatedCube_iff, cube, Homogenization.mem_openCubeSet_originCube_iff]
    intro i
    have hi := abs_lt.mp (h1 i)
    simp only [Pi.sub_apply]
    exact ⟨by linarith [hi.1], hi.2⟩
  have hcne : c ≠ x i₀ := by
    intro heq
    rw [heq] at hc
    exact absurd hc (ne_of_lt (hxm i₀))
  have hA0 : (0 : ℝ) < |x i₀ - c| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hcne))
  -- the approximating points, moving coordinate `i₀` from the face towards `x`
  set w : ℝ → Vec d := fun θ => Function.update x i₀ (c + θ * (x i₀ - c)) with hwdef
  have hwapp : ∀ θ : ℝ, w θ i₀ = c + θ * (x i₀ - c) := by
    intro θ; simp [hwdef]
  have hwoff : ∀ (θ : ℝ) (i : Fin d), i ≠ i₀ → w θ i = x i := by
    intro θ i hi; simp [hwdef, Function.update_of_ne hi]
  have hwcube : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∀ i, |w θ i| < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    intro θ hθ0 hθ1 i
    rcases eq_or_ne i i₀ with rfl | hi
    · rw [hwapp]
      have hcc : |c + θ * (x i - c)| ≤ (1 - θ) * |c| + θ * |x i| := by
        have hre : c + θ * (x i - c) = (1 - θ) * c + θ * x i := by ring
        rw [hre]
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ),
          abs_of_pos hθ0]
      have hlt : (1 - θ) * |c| + θ * |x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
        rw [hc]
        nlinarith [hxm i, hθ0]
      linarith
    · rw [hwoff θ i hi]; exact hxm i
  have hwwin : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∀ i,
      |w θ i - x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ l := by
    intro θ hθ0 hθ1 i
    rcases eq_or_ne i i₀ with rfl | hi
    · rw [hwapp]
      have hre : c + θ * (x i - c) - x i = (1 - θ) * (c - x i) := by ring
      rw [hre, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ)]
      nlinarith [abs_nonneg (c - x i), hcx, hθ0]
    · rw [hwoff θ i hi, sub_self, abs_zero]; exact hlpos
  -- the face point lies in both closures
  set q : Vec d := Function.update x i₀ c with hqdef
  have hqapp : q i₀ = c := by simp [hqdef]
  have hqoff : ∀ i : Fin d, i ≠ i₀ → q i = x i := by
    intro i hi; simp [hqdef, Function.update_of_ne hi]
  have hqcl : ∀ S : Set (Vec d), (∀ θ : ℝ, 0 < θ → θ ≤ 1 → w θ ∈ S) → q ∈ closure S := by
    intro S hS
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hθpos : (0 : ℝ) < ε / (2 * |x i₀ - c|) := by positivity
    refine ⟨w (min 1 (ε / (2 * |x i₀ - c|))), hS _ (lt_min one_pos hθpos)
      (min_le_left _ _), ?_⟩
    rw [dist_pi_lt_iff hε]
    intro i
    rcases eq_or_ne i i₀ with rfl | hi
    · rw [Real.dist_eq, hqapp, hwapp]
      have hre : c - (c + min 1 (ε / (2 * |x i - c|)) * (x i - c))
          = -(min 1 (ε / (2 * |x i - c|)) * (x i - c)) := by ring
      rw [hre, abs_neg, abs_mul, abs_of_pos (lt_min one_pos hθpos)]
      have hmin : min 1 (ε / (2 * |x i - c|)) ≤ ε / (2 * |x i - c|) := min_le_right _ _
      have hkey : ε / (2 * |x i - c|) * |x i - c| = ε / 2 := by
        field_simp
      nlinarith [hA0, hmin, hkey, hε]
    · rw [hwoff _ i hi, hqoff i hi, dist_self]
      exact hε
  have hqtr : q ∈ closure (truncatedCube d m l x) :=
    hqcl _ fun θ hθ0 hθ1 => hmem_trunc _ (hwwin θ hθ0 hθ1) (hwcube θ hθ0 hθ1)
  have hqfr : q ∈ frontier (cube d m) := by
    have hopen : IsOpen (cube d m) := (isOpenBoundedConvexDomain_cube d m).isOpen
    refine ⟨hqcl _ fun θ hθ0 hθ1 => hmem_cube _ (hwcube θ hθ0 hθ1), ?_⟩
    rw [hopen.interior_eq]
    intro hqin
    rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hqin
    have hb := hqin i₀
    rw [hqapp] at hb
    rcases (abs_eq hmpos.le).mp hc with hcv | hcv
    · linarith [hb.2]
    · linarith [hb.1]
  exact Set.nonempty_iff_ne_empty.mp ⟨q, hqtr, hqfr⟩

/-- **The interior gate is exactly the complement of the boundary case.**  If the
full cube `x + □_j` is not contained in `□_m`, then every window `U_{m,l}(x)`
with `j ≤ l` touches the frontier of `□_m`, so the conclusion's boundary
legs are switched on. -/
theorem boundaryTouches_of_not_translatedCube_subset {m j l : ℤ} {x : Vec d}
    (hx : x ∈ cube d m) (hjl : j ≤ l) (hnot : ¬ translatedCube d j x ⊆ cube d m) :
    BoundaryTouches (truncatedCube d m l x) (cube d m) := by
  classical
  rw [Set.not_subset] at hnot
  obtain ⟨p, hp, hpn⟩ := hnot
  have hjle : (1 / 2 : ℝ) * (3 : ℝ) ^ j ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ l := by
    have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hjl
    linarith
  have hpx : ∀ i, |p i - x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ j := by
    have hmem := mem_translatedCube_iff.mp hp
    rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hmem
    intro i
    have hi := hmem i
    simp only [Pi.sub_apply] at hi
    rw [abs_lt]
    exact ⟨by linarith [hi.1], hi.2⟩
  have hout : ∃ i, (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ p i ∨ p i ≤ -((1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
    by_contra hcon
    push Not at hcon
    refine hpn ?_
    rw [cube, Homogenization.mem_openCubeSet_originCube_iff]
    intro i
    obtain ⟨h1, h2⟩ := hcon i
    exact ⟨by linarith, by linarith⟩
  obtain ⟨i₀, hi₀⟩ := hout
  have hmpos : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by positivity
  have hxm : |x i₀| < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    rw [cube, Homogenization.mem_openCubeSet_originCube_iff] at hx
    rw [abs_lt]
    exact ⟨by linarith [(hx i₀).1], (hx i₀).2⟩
  obtain ⟨hxb1, hxb2⟩ := abs_lt.mp hxm
  obtain ⟨hpb1, hpb2⟩ := abs_lt.mp (hpx i₀)
  rcases hi₀ with hup | hlo
  · refine boundaryTouches_of_face_value hx i₀ (c := (1 / 2 : ℝ) * (3 : ℝ) ^ m)
      (abs_of_pos hmpos) ?_
    rw [abs_of_pos (by linarith : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ m - x i₀)]
    linarith
  · refine boundaryTouches_of_face_value hx i₀ (c := -((1 / 2 : ℝ) * (3 : ℝ) ^ m))
      (by rw [abs_neg]; exact abs_of_pos hmpos) ?_
    rw [abs_of_neg (by linarith : -((1 / 2 : ℝ) * (3 : ℝ) ^ m) - x i₀ < 0)]
    linarith

/-! ### Two `rpow` identities -/

theorem sqrt_pow_eq_rpow_half {t : ℝ} (ht : 0 ≤ t) (e : ℕ) :
    Real.sqrt (t ^ e) = t ^ ((e : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast t e, ← Real.rpow_mul ht]
  ring_nf

theorem three_rpow_one_add_mul (kk c : ℝ) :
    (3 : ℝ) ^ ((1 + c) * kk) = (3 : ℝ) ^ kk * ((3 : ℝ) ^ kk) ^ c := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [mul_comm, Real.rpow_mul h3.le, Real.rpow_add (Real.rpow_pos_of_pos h3 kk), Real.rpow_one]

/-! ### The arithmetic core of step `.9` -/

/-- **Step `.9` as pure real arithmetic.**

`Ek` is the excess at scale `n-k`, `E` the excess at scale `n`, `Ds` the
`3^{-n}`-weighted `L̲²` comparison error, `Err` the section 6 homogenization
error, and `XH`/`XG` the boundary Hölder legs of the harmonic-approximation
input and of the conclusion.  Everything else is a coefficient.  The
hypotheses are: the one-step contraction, the harmonic-approximation bound after
the `3^{-n}` weight has been distributed, the `𝓔`-cap, and the five coefficient
budgets. -/
theorem excessDecayCombine {Ek E Ds Err Sl Fg Tinv J eps XH XG : ℝ}
    {Kc Kr CA CB Cc bb ss s15 pk qn r2 : ℝ}
    (hE : 0 ≤ E) (hErrn : 0 ≤ Err) (hSl : 0 ≤ Sl) (hFg : 0 ≤ Fg) (hTinv : 0 ≤ Tinv)
    (hJ : 0 ≤ J) (heps : 0 ≤ eps) (hss : 0 ≤ ss) (hs15 : 0 ≤ s15) (hqn : 0 ≤ qn)
    (hKr : 0 ≤ Kr) (hCA : 0 ≤ CA)
    (hone : Ek ≤ Kc * E + Kr * Ds)
    (hDs : Ds ≤ CA * ss * Err * E + CA * ss * Err * (r2 * Sl) + CA * ss * Err * J +
      CA * s15 * Tinv * qn * Fg + XH)
    (hcap : Err ≤ CB * eps)
    (hKc : Kc ≤ Cc * pk) (hb1 : Kr * CA * CB ≤ Cc * bb) (hb2 : Kr * CA * r2 ≤ Cc * bb)
    (hb3 : Kr * CA ≤ Cc * bb) (hXH : Kr * XH ≤ XG) :
    Ek ≤ Cc * (pk + bb * ss * eps) * E + Cc * bb * ss * Err * (Sl + J) +
      Cc * s15 * bb * Tinv * qn * Fg + XG := by
  have ha : Kc * E ≤ Cc * pk * E := mul_le_mul_of_nonneg_right hKc hE
  have hb : Kr * (CA * ss * Err * E) ≤ Cc * bb * ss * eps * E := by
    have h1 : CA * ss * Err * E ≤ CA * ss * (CB * eps) * E :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcap (mul_nonneg hCA hss)) hE
    have h2 : Kr * (CA * ss * Err * E) ≤ Kr * (CA * ss * (CB * eps) * E) :=
      mul_le_mul_of_nonneg_left h1 hKr
    have h3 : Kr * (CA * ss * (CB * eps) * E) = (Kr * CA * CB) * (ss * eps * E) := by ring
    have h4 : (Kr * CA * CB) * (ss * eps * E) ≤ (Cc * bb) * (ss * eps * E) :=
      mul_le_mul_of_nonneg_right hb1 (mul_nonneg (mul_nonneg hss heps) hE)
    have h5 : (Cc * bb) * (ss * eps * E) = Cc * bb * ss * eps * E := by ring
    linarith only [h2, h3, h4, h5]
  have hc : Kr * (CA * ss * Err * (r2 * Sl)) ≤ Cc * bb * (ss * Err * Sl) := by
    have h3 : Kr * (CA * ss * Err * (r2 * Sl)) = (Kr * CA * r2) * (ss * Err * Sl) := by ring
    have h4 : (Kr * CA * r2) * (ss * Err * Sl) ≤ (Cc * bb) * (ss * Err * Sl) :=
      mul_le_mul_of_nonneg_right hb2 (mul_nonneg (mul_nonneg hss hErrn) hSl)
    linarith only [h3, h4]
  have hdd : Kr * (CA * ss * Err * J) ≤ Cc * bb * (ss * Err * J) := by
    have h3 : Kr * (CA * ss * Err * J) = (Kr * CA) * (ss * Err * J) := by ring
    have h4 : (Kr * CA) * (ss * Err * J) ≤ (Cc * bb) * (ss * Err * J) :=
      mul_le_mul_of_nonneg_right hb3 (mul_nonneg (mul_nonneg hss hErrn) hJ)
    linarith only [h3, h4]
  have he : Kr * (CA * s15 * Tinv * qn * Fg) ≤ Cc * s15 * bb * Tinv * qn * Fg := by
    have h3 : Kr * (CA * s15 * Tinv * qn * Fg) = (Kr * CA) * (s15 * Tinv * qn * Fg) := by ring
    have h4 : (Kr * CA) * (s15 * Tinv * qn * Fg) ≤ (Cc * bb) * (s15 * Tinv * qn * Fg) :=
      mul_le_mul_of_nonneg_right hb3
        (mul_nonneg (mul_nonneg (mul_nonneg hs15 hTinv) hqn) hFg)
    have h5 : (Cc * bb) * (s15 * Tinv * qn * Fg) = Cc * s15 * bb * Tinv * qn * Fg := by ring
    linarith only [h3, h4, h5]
  have hsum : Kr * Ds ≤ Kr * (CA * ss * Err * E) + Kr * (CA * ss * Err * (r2 * Sl)) +
      Kr * (CA * ss * Err * J) + Kr * (CA * s15 * Tinv * qn * Fg) + Kr * XH := by
    have h := mul_le_mul_of_nonneg_left hDs hKr
    linarith only [h]
  have hexp : Cc * bb * ss * Err * (Sl + J)
      = Cc * bb * (ss * Err * Sl) + Cc * bb * (ss * Err * J) := by ring
  linarith only [hone, hsum, ha, hb, hc, hdd, he, hXH, hexp]

/-! ### The assembly -/

/-- **The excess-decay estimate of `l.excess.decay.good.scales.GMC` at an
interior window.**

The conclusion is the conclusion of `l.excess.decay.good.scales.GMC`
verbatim; the binders are the binders plus the single interior gate
`translatedCube d (n-4) x ⊆ cube d m`, which is the scope of the interior
Schauder producer.  The two premises are the exact conclusions of the two
anchors the printed proof cites. -/
theorem excess_decay_good_scales_interior (d : ℕ)
    (hharm : HarmonicApproximationInput d) (hcap : MathcalECapInput d) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : _root_.SubdiffusiveProcess.Model.GMCModel d,
      ∀ s ∈ Set.Icc (512 * M.delta ^ 2) (1 / 4 : ℝ),
      ∀ epsilon ∈ Set.Icc (8 * s⁻¹ * M.delta ^ 2) 1, ∀ k : ℕ, 0 < k →
      ∀ L m n : ℕ, k ≤ n → m ≤ L → n + 5 ≤ m →
      ∀ x ∈ cube d m, ∀ z ∈ cube d m, x ∈ truncatedCube d m (n - 3) z →
      translatedCube d ((n : ℤ) - 4) x ⊆ cube d m →
      ∀ ω,
      ∀ (u h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d),
        IsDirichletSolutionOn (_root_.SubdiffusiveProcess.Model.aCutoff M L ω) (originCube d m) u h g →
        (∃ sOrder : FractionalOrder, sOrder.1 = s ∧
          Homogenization.Book.Ch03.ABK26.MemCubeEuclideanFullWsp
            (originCube d m) sOrder FiniteLpExponent.two g) →
        MemHolder (cube d m) (1 / 2) h.grad →
        ∀ ell : Affine d, ell ∈ affineMinimizers (truncatedCube d m n x) u.toFun →
        indicatorValue (goodEvent M none (n + 2) z epsilon (s / 8))
              (fun _ => excess (n - k) (truncatedCube d m (n - k) x) u.toFun) ω ≤
            C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) * epsilon) *
                excess n (truncatedCube d m n x) u.toFun +
              C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) *
                section6HomogenizationError M (s / 8) L (n + 2) ω z *
                (Real.sqrt (vecNormSq ell.slope) +
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) *
                      Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
                  else 0)) +
              C * s ^ (-8 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ *
                (3 : ℝ) ^ (s * n) *
                (fractionalSeminormOn (truncatedCube d m n x) s g).toReal +
              (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (3 : ℝ) ^ ((n : ℝ) / 2) *
                  holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad
              else 0) := by
  by_cases hd2 : 2 ≤ d
  · have : NeZero d := ⟨by omega⟩
    obtain ⟨CA, hCApos, hA⟩ := hharm
    obtain ⟨CB, hCBpos, hB⟩ := hcap
    refine ⟨anchorInteriorConst d CA CB,
      anchorInteriorConst_pos d hCApos.le hCBpos.le, ?_⟩
    have hC0 : (0 : ℝ) ≤ anchorInteriorConst d CA CB :=
      anchorInteriorConst_nonneg d hCApos.le hCBpos.le
    have hCcontr : oneStepContractionConst d * Section6Schauder.schauderInteriorConst d
        ≤ anchorInteriorConst d CA CB :=
      anchorInteriorConst_contraction_le d hCApos.le hCBpos.le
    have hCrem : (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) * CA *
        (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d)
        ≤ anchorInteriorConst d CA CB := anchorInteriorConst_remainder_le d
    have hCcrude : 3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d)) ≤ anchorInteriorConst d CA CB :=
      anchorInteriorConst_crude_le d hCApos.le hCBpos.le
    set C : ℝ := anchorInteriorConst d CA CB with hCdef
    intro M s hs epsilon heps k hk L m n hkn hmL hnm x hx z hz hxz hgate ω u h g hsol hgfrac
      hhold ell hell
    -- the standing numerical facts
    have hd1 : 1 ≤ d := by omega
    have hdne : d ≠ 0 := by omega
    have hdel : 0 < M.delta := M.shellPrefix.delta_pos
    have hdel2 : (0 : ℝ) < M.delta ^ 2 := pow_pos hdel 2
    have hs0 : 0 < s := lt_of_lt_of_le (mul_pos (by norm_num) hdel2) hs.1
    have hs4 : s ≤ 1 / 4 := hs.2
    have heps0 : 0 ≤ epsilon :=
      le_trans (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.2 hs0.le)) hdel2.le) heps.1
    have heps1 : epsilon ≤ 1 := heps.2
    -- signs of the atoms appearing on the right
    have hMemHW : MemHolder (truncatedCube d m n x) (1 / 2) h.grad :=
      memHolder_mono hhold (truncatedCube_subset_cube d m n x)
    have hEn : 0 ≤ excess (n : ℤ) (truncatedCube d m n x) u.toFun := excess_nonneg _ _ _
    have hErr : 0 ≤ section6HomogenizationError M (s / 8) L (n + 2) ω z := ENNReal.toReal_nonneg
    have hTail : 0 ≤ (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ :=
      inv_nonneg.2 (tailAverage_nonneg _ _ _ _ _)
    have hFg : 0 ≤ (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
      ENNReal.toReal_nonneg
    have hSl : 0 ≤ Real.sqrt (vecNormSq ell.slope) := Real.sqrt_nonneg _
    have hAh : 0 ≤ Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad)) :=
      Real.sqrt_nonneg _
    have hHh : 0 ≤ holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad :=
      holderSeminormOn_nonneg hMemHW
    have hpow1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have hpow2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := Real.rpow_nonneg (by norm_num) _
    have hpow3 : (0 : ℝ) ≤ (3 : ℝ) ^ (s * n) := Real.rpow_nonneg (by norm_num) _
    have hpow4 : (0 : ℝ) ≤ (3 : ℝ) ^ ((n : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
    have hss : (0 : ℝ) ≤ s ^ (-2 : ℝ) := Real.rpow_nonneg hs0.le _
    have hssIn : (0 : ℝ) ≤ s ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
    have hs15 : (0 : ℝ) ≤ s ^ (-8 : ℝ) := Real.rpow_nonneg hs0.le _
    have hs3 : (0 : ℝ) ≤ s ^ (-7 / 2 : ℝ) := Real.rpow_nonneg hs0.le _
    have hI1 : (0 : ℝ) ≤ (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
        s ^ (-3 / 2 : ℝ) *
          Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad)) else 0) := by
      split_ifs
      · exact mul_nonneg hssIn hAh
      · exact le_rfl
    have hI2 : (0 : ℝ) ≤ (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
        C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * (3 : ℝ) ^ ((n : ℝ) / 2) *
          holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad else 0) := by
      split_ifs
      · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hs3) hpow2) hpow4) hHh
      · exact le_rfl
    have hP : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) * epsilon :=
      mul_nonneg (mul_nonneg hpow2 hss) heps0
    have hT2 : (0 : ℝ) ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) *
        section6HomogenizationError M (s / 8) L (n + 2) ω z *
        (Real.sqrt (vecNormSq ell.slope) +
          (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
            s ^ (-3 / 2 : ℝ) *
              Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad))
          else 0)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hpow2) hss) hErr) (add_nonneg hSl hI1)
    have hT3 : (0 : ℝ) ≤ C * s ^ (-8 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
        (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ * (3 : ℝ) ^ (s * n) *
        (fractionalSeminormOn (truncatedCube d m n x) s g).toReal :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC0 hs15) hpow2) hTail) hpow3) hFg
    refine indicatorValue_le ?_ ?_
    · exact add_nonneg (add_nonneg (add_nonneg
        (mul_nonneg (mul_nonneg hC0 (add_nonneg hpow1 hP)) hEn) hT2) hT3) hI2
    intro homega
    have hu_n : MemLp u.toFun 2 (volume.restrict (truncatedCube d m n x)) :=
      u.memL2.mono_measure (Measure.restrict_mono (truncatedCube_subset_cube d m n x) le_rfl)
    by_cases hk6 : 6 ≤ k
    · -- the interior branch `6 ≤ k`
      -- step `.1`: the window choice `U_{m,n-4}(x) ⊆ y + □_{n-2} ⊆ U_{m,n-1}(x)`
      obtain ⟨y, hy, hy1, hy2⟩ := exists_windowChoice (m := (m : ℤ)) (n := (n : ℤ)) hx (by omega)
      have hYsub : translatedCube d ((n : ℤ) - 2) y ⊆ cube d (m : ℤ) :=
        hy2.trans (truncatedCube_subset_cube d m ((n : ℤ) - 1) x)
      have hYopen : IsOpen (translatedCube d ((n : ℤ) - 2) y) :=
        Section6Schauder.isOpen_translatedCube d _ y
      -- step `.2`: the harmonic-approximation premise, at the replacement cube
      have hhfrac : MemFractionalOn (cube d m) s h.grad :=
        memFractionalOn_cube_of_memHolder hd1 hs0 hs4 hhold
      obtain ⟨⟨v, hvharm, hvzt⟩, -, hHA⟩ :=
        hA M s hs L m n hmL hnm z hz x hxz ω u h g hsol hgfrac hhfrac y hy hy1 hy2
          (u.restrict hYopen hYsub) (fun _ => rfl) (fun _ => rfl)
      -- step `.3`: Weyl's lemma and the interior Schauder estimate
      obtain ⟨v', K, hv'ae, hv'mem, hK0, hint, hgradv, hholK, hschauder⟩ :=
        Section6Schauder.exists_gradientHolder_of_weaklyHarmonic (d := d) (m := (m : ℤ))
          (n := (n : ℤ)) (x := x) (y := y) hdne hx (by omega) hgate hy1 hvharm
      -- steps `.4`/`.5`: the deterministic one-step contraction
      have hv'4 : MemLp v' 2 (volume.restrict (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)) :=
        hv'mem.restrict _
      have hone := excess_oneStep_of_schauder (d := d) (m := (m : ℤ)) (n := (n : ℤ)) (k := k)
        (Kh := 0) hk6 hx (by omega) hu_n hv'4 hK0
        (Section6Schauder.schauderInteriorConst_nonneg d) hint hgradv hholK hschauder
      have hDeq : normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
            (fun p => u.toFun p - v' p)
          = normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
            (fun q => u.toFun q - v.toFun q) := by
        refine normalizedL2On_congr_ae ?_
        have hres : v' =ᵐ[volume.restrict (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)] v.toFun :=
          hv'ae.filter_mono (ae_mono (Measure.restrict_mono hy1 le_rfl))
        filter_upwards [hres] with p hp
        rw [hp]
      rw [hDeq, mul_zero, add_zero] at hone
      -- step `.2` continued: the harmonic-approximation bound on the good event
      have homega1 : ω ∈ goodEvent M none (n + 2) z 1 (s / 8) :=
        goodEvent_mono heps0 heps1 homega
      have hD := hHA v hvharm hvzt
      rw [indicatorValue_of_mem homega1] at hD
      -- step `.7`: the `𝓔`-cap, transported to the translate `z`
      have hcapz : section6HomogenizationError M (s / 8) L (n + 2) ω z ≤ CB * epsilon := by
        refine Section6Covariance.section6HomogenizationError_le_of_translate_zero ?_ z homega
        intro ν hν
        refine hB M (s / 8) ⟨by linarith [hs.1], by linarith⟩ L (n + 2) (by omega) ν epsilon
          ⟨?_, heps1⟩ hν
        have hrw : (s / 8)⁻¹ * M.delta ^ 2 = 8 * s⁻¹ * M.delta ^ 2 := by
          field_simp
        rw [hrw]
        exact heps.1
      -- step `.6`: the slope split of the normalized oscillation
      have hstep6 := normalizedL2On_sub_average_le (m := (m : ℤ)) (n := (n : ℤ)) (x := x)
        hx (by omega) hu_n hell
      
      have hstep8 := holderLeg_le (m := (m : ℤ)) (j := (n : ℤ)) (x := x) (f := h.grad)
        (s := s) hd1 hx hs0 hs4 hMemHW
      -- notation for the atoms of the display
      set E := excess (n : ℤ) (truncatedCube d m n x) u.toFun with hEdef
      set Err := section6HomogenizationError M (s / 8) L (n + 2) ω z with hErrdef
      set Sl := Real.sqrt (vecNormSq ell.slope) with hSldef
      set Ah := Real.sqrt (vecNormSq (averageVecOn (truncatedCube d m n x) h.grad)) with hAhdef
      set Fg := (fractionalSeminormOn (truncatedCube d m n x) s g).toReal with hFgdef
      set Fh := (fractionalSeminormOn (truncatedCube d m n x) s h.grad).toReal with hFhdef
      set Hh := holderSeminormOn (truncatedCube d m n x) (1 / 2) h.grad with hHhdef
      set Tinv := (tailAverage M L (n + 2) ω (translatedCube d (n + 2) z))⁻¹ with hTinvdef
      set D := normalizedL2On (truncatedCube d (m : ℤ) ((n : ℤ) - 4) x)
        (fun q => u.toFun q - v.toFun q) with hDdef
      set N := normalizedL2On (truncatedCube d m n x)
        (fun q => u.toFun q - averageOn (truncatedCube d m n x) u.toFun) with hNdef
      -- the remainder constant is bounded by the printed `3^{(1+d/2)k}`
      have hKr0 : (0 : ℝ) ≤ oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k :=
        oneStepRemainderConst_nonneg d (Section6Schauder.schauderInteriorConst_nonneg d) k
      have hb0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := hpow2
      have hb1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        have h0 : (3 : ℝ) ^ (0 : ℝ) ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          positivity
        simpa using h0
      have h81 : (0 : ℝ) ≤ 81 * taylorConst d * Section6Schauder.schauderInteriorConst d :=
        mul_nonneg (mul_nonneg (by norm_num) (taylorConst_nonneg d))
          (Section6Schauder.schauderInteriorConst_nonneg d)
      have hCrm0 : (0 : ℝ) ≤ 81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1 := by
        linarith only [h81]
      have hKrb : oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k
          ≤ (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) *
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        have hleft : 81 * taylorConst d * Section6Schauder.schauderInteriorConst d *
              ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
            ≤ 81 * taylorConst d * Section6Schauder.schauderInteriorConst d *
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
          exact mul_le_mul_of_nonneg_left (le_trans three_zpow_rpow_half_le_one hb1) h81
        have hright : (3 : ℝ) ^ ((k : ℤ)) *
              Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d)
            ≤ (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
          have ht0 : (0 : ℝ) < (3 : ℝ) ^ ((k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
          have htz : (3 : ℝ) ^ ((k : ℤ)) = (3 : ℝ) ^ ((k : ℝ)) := by
            rw [← Real.rpow_intCast (3 : ℝ) ((k : ℤ))]
            norm_num
          have hsq : Real.sqrt (((3 : ℝ) ^ ((k : ℝ))) ^ d) = ((3 : ℝ) ^ ((k : ℝ))) ^ ((d : ℝ) / 2) :=
            sqrt_pow_eq_rpow_half ht0.le d
          have hmono : Real.sqrt (((3 : ℝ) ^ ((k : ℤ) - 2)) ^ d)
              ≤ Real.sqrt (((3 : ℝ) ^ ((k : ℝ))) ^ d) := by
            refine Real.sqrt_le_sqrt ?_
            rw [← htz]
            exact pow_le_pow_left₀ (zpow_nonneg (by norm_num) _)
              (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
          have hsplit : (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
              = (3 : ℝ) ^ ((k : ℝ)) * ((3 : ℝ) ^ ((k : ℝ))) ^ ((d : ℝ) / 2) :=
            three_rpow_one_add_mul (k : ℝ) ((d : ℝ) / 2)
          rw [hsplit, htz]
          exact mul_le_mul_of_nonneg_left (le_trans hmono (le_of_eq hsq)) ht0.le
        rw [oneStepRemainderConst]
        linarith only [hleft, hright]
      -- the four coefficient budgets
      have hbudget : ∀ c : ℝ, 0 ≤ c →
          c ≤ CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d →
          oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k * CA * c
            ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by
        intro c hc0 hcle
        have h1 : oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k * CA * c
            ≤ ((81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) *
                (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) * CA * c :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKrb hCApos.le) hc0
        have h2 : ((81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) *
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) * CA * c
            = ((81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) * CA * c) *
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by ring
        have h3 : (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) * CA * c
            ≤ (81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) * CA *
              (CB + 1 + Real.sqrt (d : ℝ) / 2 + fractionalHolderConst d) :=
          mul_le_mul_of_nonneg_left hcle (mul_nonneg hCrm0 hCApos.le)
        have h4 : ((81 * taylorConst d * Section6Schauder.schauderInteriorConst d + 1) * CA * c) *
              (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)
            ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) :=
          mul_le_mul_of_nonneg_right (le_trans h3 hCrem) hb0
        linarith only [h1, h2.le, h2.ge, h4]
      have hCH0 : (0 : ℝ) ≤ fractionalHolderConst d := fractionalHolderConst_nonneg d
      have hsd0 : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
      have hbCB := hbudget CB hCBpos.le (by linarith only [hCH0, hsd0])
      have hbOne := hbudget 1 zero_le_one (by linarith only [hCH0, hsd0, hCBpos])
      have hbSqrt := hbudget (Real.sqrt (d : ℝ) / 2) (by linarith only [hsd0])
        (by linarith only [hCH0, hCBpos])
      have hbCH := hbudget (fractionalHolderConst d) hCH0 (by linarith only [hsd0, hCBpos])
      have hb3 : oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k * CA
          ≤ C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) := by simpa using hbOne
      -- step `.8` in the `ℕ`-cast shape of the harmonic-approximation input
      simp only [Int.cast_natCast] at hstep8
      -- the `3^{-n}` weight, distributed over the harmonic-approximation bound
      have h3n : (0 : ℝ) < (3 : ℝ) ^ (-(n : ℤ)) := zpow_pos (by norm_num) _
      have h3nn : (3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ (n : ℕ) = 1 := by
        rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (by positivity)]
      have hJeq : (3 : ℝ) ^ (-(n : ℤ)) *
            (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah else 0)
          = (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              s ^ (-3 / 2 : ℝ) * Ah else 0) := by
        split_ifs
        · calc (3 : ℝ) ^ (-(n : ℤ)) * (s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ (n : ℕ) * Ah)
              = ((3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ (n : ℕ)) * (s ^ (-3 / 2 : ℝ) * Ah) := by ring
            _ = s ^ (-3 / 2 : ℝ) * Ah := by rw [h3nn, one_mul]
        · rw [mul_zero]
      have hfront : (3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ ((1 + s) * (n : ℝ))
          = (3 : ℝ) ^ (s * (n : ℝ)) := by
        rw [← Real.rpow_intCast (3 : ℝ) (-(n : ℤ)), ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        congr 1
        push_cast
        ring
      have hXHle : (3 : ℝ) ^ (-(n : ℤ)) *
            (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              CA * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0)
          ≤ (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh)
             else 0) := by
        split_ifs
        · have hre : (3 : ℝ) ^ (-(n : ℤ)) *
                (CA * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh)
              = CA * (s ^ (-4 : ℝ) * ((3 : ℝ) ^ (-(n : ℤ)) *
                  ((3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh))) := by ring
          rw [hre]
          exact mul_le_mul_of_nonneg_left hstep8 hCApos.le
        · rw [mul_zero]
      have hCAErr : (0 : ℝ) ≤ CA * s ^ (-2 : ℝ) * Err :=
        mul_nonneg (mul_nonneg hCApos.le hss) hErr
      have hNterm : CA * s ^ (-2 : ℝ) * Err * ((3 : ℝ) ^ (-(n : ℤ)) * N)
          ≤ CA * s ^ (-2 : ℝ) * Err * E +
            CA * s ^ (-2 : ℝ) * Err * (Real.sqrt (d : ℝ) / 2 * Sl) := by
        have hstep := mul_le_mul_of_nonneg_left hstep6 hCAErr
        linarith only [hstep]
      have hDs : (3 : ℝ) ^ (-(n : ℤ)) * D
          ≤ CA * s ^ (-2 : ℝ) * Err * E
            + CA * s ^ (-2 : ℝ) * Err * (Real.sqrt (d : ℝ) / 2 * Sl)
            + CA * s ^ (-2 : ℝ) * Err *
                (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                  s ^ (-3 / 2 : ℝ) * Ah else 0)
            + CA * s ^ (-8 : ℝ) * Tinv * (3 : ℝ) ^ (s * (n : ℝ)) * Fg
            + (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh)
               else 0) := by
        have hbase := mul_le_mul_of_nonneg_left hD h3n.le
        have hexp : (3 : ℝ) ^ (-(n : ℤ)) *
              (CA * s ^ (-2 : ℝ) * Err *
                  (N + (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah else 0)) +
                CA * s ^ (-8 : ℝ) * Tinv * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fg +
                (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                  CA * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0))
            = CA * s ^ (-2 : ℝ) * Err * ((3 : ℝ) ^ (-(n : ℤ)) * N)
              + CA * s ^ (-2 : ℝ) * Err * ((3 : ℝ) ^ (-(n : ℤ)) *
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    s ^ (-3 / 2 : ℝ) * (3 : ℝ) ^ n * Ah else 0))
              + CA * s ^ (-8 : ℝ) * Tinv *
                  ((3 : ℝ) ^ (-(n : ℤ)) * (3 : ℝ) ^ ((1 + s) * (n : ℝ))) * Fg
              + (3 : ℝ) ^ (-(n : ℤ)) *
                  (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
                    CA * s ^ (-4 : ℝ) * (3 : ℝ) ^ ((1 + s) * (n : ℝ)) * Fh else 0) := by
          ring
        rw [hexp, hJeq, hfront] at hbase
        linarith only [hbase, hNterm, hXHle]
      have hKcle : oneStepContractionConst d * Section6Schauder.schauderInteriorConst d *
            ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
          ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
        have hpe : ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) = (3 : ℝ) ^ (-(k : ℝ) / 2) := by
          rw [three_zpow_rpow_half_eq]
          push_cast
          ring_nf
        rw [hpe]
        exact mul_le_mul_of_nonneg_right hCcontr hpow1
      have hXHfin : oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k *
            (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh)
             else 0)
          ≤ (if BoundaryTouches (truncatedCube d m n x) (cube d m) then
              C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh
             else 0) := by
        split_ifs
        · have hre : oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k *
                (CA * (fractionalHolderConst d * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh))
              = (oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k * CA *
                  fractionalHolderConst d) *
                (s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh) := by ring
          have hbnd : (oneStepRemainderConst d (Section6Schauder.schauderInteriorConst d) k * CA *
                fractionalHolderConst d) * (s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh)
              ≤ (C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) *
                (s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh) :=
            mul_le_mul_of_nonneg_right hbCH
              (mul_nonneg (mul_nonneg hs3 hpow4) hHh)
          have hfin : (C * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k)) *
                (s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((n : ℝ) / 2) * Hh)
              = C * s ^ (-7 / 2 : ℝ) * (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) *
                (3 : ℝ) ^ ((n : ℝ) / 2) * Hh := by ring
          linarith only [hre.le, hre.ge, hbnd, hfin.le, hfin.ge]
        · rw [mul_zero]
      exact excessDecayCombine hEn hErr hSl hFg hTail hI1 heps0 hss hs15 hpow3 hKr0 hCApos.le
        hone hDs hcapz hKcle hbCB hbSqrt hb3 hXHfin
    -- the crude branch `k < 6`: no harmonic input at all
    have hcrude := excess_truncatedCube_le (m := (m : ℤ)) (j := (n : ℤ) - (k : ℤ))
      (l := (n : ℤ)) (x := x) hx (by omega) (by omega) (by omega) hu_n
    rw [show (n : ℤ) - ((n : ℤ) - (k : ℤ)) = (k : ℤ) by ring] at hcrude
    have hcoef : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d)
        ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
      have hA1 : (3 : ℝ) ^ ((k : ℤ)) ≤ 243 := by
        calc (3 : ℝ) ^ ((k : ℤ)) ≤ (3 : ℝ) ^ (5 : ℤ) :=
              zpow_le_zpow_right₀ (by norm_num) (by omega)
          _ = 243 := by norm_num
      have hA2 : Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) ≤ Real.sqrt ((3 : ℝ) ^ (7 * d)) := by
        refine Real.sqrt_le_sqrt ?_
        calc ((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d ≤ ((3 : ℝ) ^ (7 : ℤ)) ^ d :=
              pow_le_pow_left₀ (zpow_nonneg (by norm_num) _)
                (zpow_le_zpow_right₀ (by norm_num) (by omega)) d
          _ = (3 : ℝ) ^ (7 * d) := by
              rw [show (7 : ℤ) = ((7 : ℕ) : ℤ) by norm_num, zpow_natCast, ← pow_mul]
      have hA3 : (3 : ℝ) ^ (-(3 : ℝ)) ≤ (3 : ℝ) ^ (-(k : ℝ) / 2) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hkr : (k : ℝ) ≤ 5 := by exact_mod_cast (by omega : k ≤ 5)
        linarith
      have hA4 : (3 : ℝ) ^ (-(3 : ℝ)) = 1 / 27 := by
        rw [show (-(3 : ℝ)) = ((-3 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        norm_num
      have hsq0 : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ (7 * d)) := Real.sqrt_nonneg _
      have hsq1 : (0 : ℝ) ≤ Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d) := Real.sqrt_nonneg _
      have hzp : (0 : ℝ) < (3 : ℝ) ^ ((k : ℤ)) := zpow_pos (by norm_num) _
      have hleft : (3 : ℝ) ^ ((k : ℤ)) * Real.sqrt (((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d)
          ≤ 243 * Real.sqrt ((3 : ℝ) ^ (7 * d)) :=
        mul_le_mul hA1 hA2 hsq1 (by norm_num)
      have hmid : (243 : ℝ) * Real.sqrt ((3 : ℝ) ^ (7 * d))
          = (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) * ((1 : ℝ) / 27) := by
        rw [show ((3 : ℝ) ^ (8 : ℕ)) = 6561 by norm_num]; ring
      have hright : (3 ^ (8 : ℕ) * Real.sqrt ((3 : ℝ) ^ (7 * d))) * ((1 : ℝ) / 27)
          ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) := by
        rw [← hA4]
        refine mul_le_mul hCcrude hA3 (by rw [hA4]; norm_num) hC0
      linarith only [hleft, hmid, hright]
    have hstep : excess ((n : ℤ) - (k : ℤ)) (truncatedCube d m (n - k) x) u.toFun
        ≤ C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
            (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) * epsilon) *
            excess (n : ℤ) (truncatedCube d m n x) u.toFun := by
      have h1 : excess ((n : ℤ) - (k : ℤ)) (truncatedCube d m (n - k) x) u.toFun
          ≤ C * (3 : ℝ) ^ (-(k : ℝ) / 2) * excess (n : ℤ) (truncatedCube d m n x) u.toFun :=
        le_trans hcrude (mul_le_mul_of_nonneg_right hcoef hEn)
      have h2 : C * (3 : ℝ) ^ (-(k : ℝ) / 2) ≤ C * ((3 : ℝ) ^ (-(k : ℝ) / 2) +
          (3 : ℝ) ^ ((1 + (d : ℝ) / 2) * k) * s ^ (-2 : ℝ) * epsilon) :=
        mul_le_mul_of_nonneg_left (by linarith only [hP]) hC0
      exact le_trans h1 (mul_le_mul_of_nonneg_right h2 hEn)
    exact le_trans (le_trans (le_trans hstep (le_add_of_nonneg_right hT2))
      (le_add_of_nonneg_right hT3)) (le_add_of_nonneg_right hI2)
  · exact ⟨1, one_pos, fun M => absurd M.shellPrefix.dimension hd2⟩

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6ExcessDecay
