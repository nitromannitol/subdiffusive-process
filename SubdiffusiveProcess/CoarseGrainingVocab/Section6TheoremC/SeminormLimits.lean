import SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration.NormalizedL2




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6Iteration
open Homogenization (volumeAverage)

noncomputable section

variable {d : ℕ}

/-! ### Monotonicity of the scalar seminorm -/

/-- The volume average is monotone on integrable functions. -/
theorem volumeAverage_mono {W : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f W) (hg : IntegrableOn g W)
    (hle : ∀ x, f x ≤ g x) :
    volumeAverage W f ≤ volumeAverage W g := by
  have hint : ∫ x in W, f x ≤ ∫ x in W, g x :=
    integral_mono hf hg hle
  unfold volumeAverage
  exact mul_le_mul_of_nonneg_left hint (by positivity)

/-- Monotonicity of `‖·‖_{L̲²(W)}` under a pointwise bound on the squares. -/
theorem normalizedL2On_mono_of_sq_le {W : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn (fun x ↦ f x ^ 2) W)
    (hg : IntegrableOn (fun x ↦ g x ^ 2) W)
    (hle : ∀ x, f x ^ 2 ≤ g x ^ 2) :
    normalizedL2On W f ≤ normalizedL2On W g :=
  Real.sqrt_le_sqrt (volumeAverage_mono hf hg hle)

/-- Monotonicity of `‖·‖_{L̲²(W)}` under a pointwise bound between nonnegative
functions. -/
theorem normalizedL2On_mono_of_nonneg {W : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn (fun x ↦ f x ^ 2) W)
    (hg : IntegrableOn (fun x ↦ g x ^ 2) W)
    (hf0 : ∀ x, 0 ≤ f x) (hle : ∀ x, f x ≤ g x) :
    normalizedL2On W f ≤ normalizedL2On W g :=
  normalizedL2On_mono_of_sq_le hf hg fun x ↦
    pow_le_pow_left₀ (hf0 x) (hle x) 2

/-! ### The reverse triangle inequality -/

/-- Splitting `f = g + (f - g)` in Minkowski's inequality. -/
theorem normalizedL2On_le_add_sub {W : Set (Vec d)} {f g : Vec d → ℝ}
    (hg : MemLp g 2 (volume.restrict W))
    (hfg : MemLp (fun x ↦ f x - g x) 2 (volume.restrict W)) :
    normalizedL2On W f ≤
      normalizedL2On W g + normalizedL2On W (fun x ↦ f x - g x) := by
  have hsplit : f = fun x ↦ g x + (f x - g x) := by funext x; ring
  calc normalizedL2On W f
      = normalizedL2On W (fun x ↦ g x + (f x - g x)) := by rw [← hsplit]
    _ ≤ normalizedL2On W g + normalizedL2On W (fun x ↦ f x - g x) :=
        normalizedL2On_add_le hg hfg

/-- **Reverse triangle inequality** for `‖·‖_{L̲²(W)}`.  This is the engine of
every limit passage in Theorem C's proof. -/
theorem abs_normalizedL2On_sub_le {W : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict W)) (hg : MemLp g 2 (volume.restrict W)) :
    |normalizedL2On W f - normalizedL2On W g| ≤
      normalizedL2On W (fun x ↦ f x - g x) := by
  have hfg : MemLp (fun x ↦ f x - g x) 2 (volume.restrict W) := hf.sub hg
  have hgf : MemLp (fun x ↦ g x - f x) 2 (volume.restrict W) := hg.sub hf
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · have := normalizedL2On_le_add_sub (f := f) (g := g) hg hfg
    linarith
  · have h := normalizedL2On_le_add_sub (f := g) (g := f) hf hgf
    rw [normalizedL2On_sub_comm W g f] at h
    linarith

/-! ### Continuity along `L²`-convergent sequences -/

/-- If `f j → f` in `L̲²(W)` then `‖f j‖_{L̲²(W)} → ‖f‖_{L̲²(W)}`. -/
theorem tendsto_normalizedL2On_of_tendsto_sub {W : Set (Vec d)}
    {f : ℕ → Vec d → ℝ} {flim : Vec d → ℝ}
    (hf : ∀ j, MemLp (f j) 2 (volume.restrict W))
    (hflim : MemLp flim 2 (volume.restrict W))
    (h : Tendsto (fun j ↦ normalizedL2On W (fun x ↦ f j x - flim x))
      atTop (nhds 0)) :
    Tendsto (fun j ↦ normalizedL2On W (f j)) atTop
      (nhds (normalizedL2On W flim)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun j ↦ dist_nonneg) (fun j ↦ ?_) h
  rw [Real.dist_eq]
  exact abs_normalizedL2On_sub_le (hf j) hflim

/-! ### The vector seminorm -/

/-- The triangle inequality for the explicit Euclidean magnitude, through the
Hilbert realization. -/
theorem euclideanNorm_add_le (u v : Vec d) :
    euclideanNorm (u + v) ≤ euclideanNorm u + euclideanNorm v := by
  simp only [euclideanNorm_eq_norm_ofVec]
  simpa only [← HilbertVec.ofVecL_apply, map_add] using
    norm_add_le (HilbertVec.ofVec u) (HilbertVec.ofVec v)

/-- Splitting `F = G + (F - G)` for the vector seminorm. -/
theorem vectorNormalizedL2On_le_add_sub {W : Set (Vec d)}
    {F G : Vec d → Vec d}
    (hF : IntegrableOn (fun x ↦ euclideanNorm (F x) ^ 2) W)
    (hG : MemLp (fun x ↦ euclideanNorm (G x)) 2 (volume.restrict W))
    (hFG : MemLp (fun x ↦ euclideanNorm (F x - G x)) 2 (volume.restrict W)) :
    vectorNormalizedL2On W F ≤
      vectorNormalizedL2On W G +
        vectorNormalizedL2On W (fun x ↦ F x - G x) := by
  have hpt : ∀ x, euclideanNorm (F x) ≤
      euclideanNorm (G x) + euclideanNorm (F x - G x) := by
    intro x
    have hsum : G x + (F x - G x) = F x := by ext i; simp
    calc euclideanNorm (F x)
        = euclideanNorm (G x + (F x - G x)) := by rw [hsum]
      _ ≤ euclideanNorm (G x) + euclideanNorm (F x - G x) :=
          euclideanNorm_add_le _ _
  have hsumMem : MemLp
      (fun x ↦ euclideanNorm (G x) + euclideanNorm (F x - G x)) 2
      (volume.restrict W) := hG.add hFG
  calc vectorNormalizedL2On W F
      ≤ normalizedL2On W
          (fun x ↦ euclideanNorm (G x) + euclideanNorm (F x - G x)) :=
        normalizedL2On_mono_of_nonneg hF hsumMem.integrable_sq
          (fun x ↦ euclideanNorm_nonneg _) hpt
    _ ≤ vectorNormalizedL2On W G +
          vectorNormalizedL2On W (fun x ↦ F x - G x) :=
        normalizedL2On_add_le hG hFG

/-- **Reverse triangle inequality** for the vector seminorm
`‖·‖_{L̲²(W)}` of `e.large.scale.energy.multifractal`. -/
theorem abs_vectorNormalizedL2On_sub_le {W : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : MemLp (fun x ↦ euclideanNorm (F x)) 2 (volume.restrict W))
    (hG : MemLp (fun x ↦ euclideanNorm (G x)) 2 (volume.restrict W))
    (hFG : MemLp (fun x ↦ euclideanNorm (F x - G x)) 2 (volume.restrict W)) :
    |vectorNormalizedL2On W F - vectorNormalizedL2On W G| ≤
      vectorNormalizedL2On W (fun x ↦ F x - G x) := by
  have hGF : MemLp (fun x ↦ euclideanNorm (G x - F x)) 2
      (volume.restrict W) := by
    have hrw : (fun x ↦ euclideanNorm (G x - F x)) =
        fun x ↦ euclideanNorm (F x - G x) := by
      funext x
      rw [show G x - F x = -(F x - G x) by ext i; simp, euclideanNorm_neg]
    rw [hrw]; exact hFG
  have hsymm : vectorNormalizedL2On W (fun x ↦ G x - F x) =
      vectorNormalizedL2On W (fun x ↦ F x - G x) := by
    unfold vectorNormalizedL2On
    congr 1
    funext x
    show euclideanNorm (G x - F x) = euclideanNorm (F x - G x)
    rw [show G x - F x = -(F x - G x) by ext i; simp, euclideanNorm_neg]
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · have := vectorNormalizedL2On_le_add_sub (F := F) (G := G)
      hF.integrable_sq hG hFG
    linarith
  · have h := vectorNormalizedL2On_le_add_sub (F := G) (G := F)
      hG.integrable_sq hF hGF
    rw [hsymm] at h
    linarith

/-- If `F j → F` in the vector `L̲²(W)` seminorm then the seminorms converge. -/
theorem tendsto_vectorNormalizedL2On_of_tendsto_sub {W : Set (Vec d)}
    {F : ℕ → Vec d → Vec d} {Flim : Vec d → Vec d}
    (hF : ∀ j, MemLp (fun x ↦ euclideanNorm (F j x)) 2 (volume.restrict W))
    (hFlim : MemLp (fun x ↦ euclideanNorm (Flim x)) 2 (volume.restrict W))
    (hFsub : ∀ j, MemLp (fun x ↦ euclideanNorm (F j x - Flim x)) 2
      (volume.restrict W))
    (h : Tendsto (fun j ↦ vectorNormalizedL2On W (fun x ↦ F j x - Flim x))
      atTop (nhds 0)) :
    Tendsto (fun j ↦ vectorNormalizedL2On W (F j)) atTop
      (nhds (vectorNormalizedL2On W Flim)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun j ↦ dist_nonneg) (fun j ↦ ?_) h
  rw [Real.dist_eq]
  exact abs_vectorNormalizedL2On_sub_le (hF j) hFlim (hFsub j)

/-! ### Passing an inequality to the limit -/

/-- A termwise estimate `A j ≤ K * B j` survives the limit.  This is the final
move of each of the three limit passages listed in the module docstring. -/
theorem le_mul_of_forall_le_mul_of_tendsto {A B : ℕ → ℝ} {Alim Blim K : ℝ}
    (hA : Tendsto A atTop (nhds Alim)) (hB : Tendsto B atTop (nhds Blim))
    (hle : ∀ j, A j ≤ K * B j) :
    Alim ≤ K * Blim :=
  le_of_tendsto_of_tendsto hA (hB.const_mul K) (Eventually.of_forall hle)

/-- The form in which Theorem C's two displays are passed to the limit: both
sides are seminorms of an `L²`-convergent sequence. -/
theorem normalizedL2On_le_mul_of_tendsto {V W : Set (Vec d)}
    {f : ℕ → Vec d → ℝ} {flim : Vec d → ℝ} {K : ℝ}
    (hfV : ∀ j, MemLp (f j) 2 (volume.restrict V))
    (hflimV : MemLp flim 2 (volume.restrict V))
    (hV : Tendsto (fun j ↦ normalizedL2On V (fun x ↦ f j x - flim x))
      atTop (nhds 0))
    (hfW : ∀ j, MemLp (f j) 2 (volume.restrict W))
    (hflimW : MemLp flim 2 (volume.restrict W))
    (hW : Tendsto (fun j ↦ normalizedL2On W (fun x ↦ f j x - flim x))
      atTop (nhds 0))
    (hle : ∀ j, normalizedL2On V (f j) ≤ K * normalizedL2On W (f j)) :
    normalizedL2On V flim ≤ K * normalizedL2On W flim :=
  le_mul_of_forall_le_mul_of_tendsto
    (tendsto_normalizedL2On_of_tendsto_sub hfV hflimV hV)
    (tendsto_normalizedL2On_of_tendsto_sub hfW hflimW hW) hle

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
