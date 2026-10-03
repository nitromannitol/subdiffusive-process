module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.LiouvilleAssembly
public import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut.PerScaleDataTop

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab
open SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-! ### Geometry: the centered cube is its own translate at the origin -/

/-- The origin lies on every triadic grid. -/
theorem onTriadicGrid_zero (n : ℕ) : OnTriadicGrid n (0 : Vec d) :=
  fun _ ↦ ⟨0, by simp⟩

/-- Translating the centered cube by the origin does nothing. -/
theorem translatedCube_zero_eq_cube (d : ℕ) (n : ℤ) :
    translatedCube d n (0 : Vec d) = cube d n := by
  rw [translatedCube]
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    simpa using hy
  · intro x hx
    exact ⟨x, hx, by simp⟩

/-! ### Finiteness of the cube -/

/-- The restricted volume on a centered cube is finite. -/
theorem isFiniteMeasure_restrict_cube (d : ℕ) (m : ℤ) :
    IsFiniteMeasure (volume.restrict (cube d m)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact lt_top_iff_ne_top.2 (volume_ne_top_of_domain (isOpenBoundedConvexDomain_cube d m))

/-! ### The four integrability inputs, from the clause's own hypothesis -/

/-- A pointwise `H¹` witness on every cube makes `u` locally `L²`, hence
locally integrable together with its square and every centered square. -/
theorem liouville_integrability_of_witnesses {u : Vec d → ℝ}
    (hw : ∀ m : ℤ, ∃ um : H1Function (openCubeSet (originCube d m)),
      ∀ x, um.toFun x = u x) :
    (∀ m : ℤ, MemLp u 2 (volume.restrict (cube d m))) ∧
      (∀ m : ℤ, IntegrableOn u (cube d m)) ∧
      (∀ m : ℤ, IntegrableOn (fun x ↦ u x ^ 2) (cube d m)) ∧
      (∀ (R : ℝ) (c : ℝ),
        IntegrableOn (fun x ↦ (u x - c) ^ 2) (Metric.ball (0 : Vec d) R)) ∧
      (∀ n : ℤ,
        IntegrableOn (fun x ↦ (u x - averageOn (cube d n) u) ^ 2) (cube d n)) := by
  have hmem : ∀ m : ℤ, MemLp u 2 (volume.restrict (cube d m)) := by
    intro m
    obtain ⟨um, hum⟩ := hw m
    have hfun : u = um.toFun := funext fun x ↦ (hum x).symm
    rw [hfun]
    exact um.memL2
  have hsub : ∀ (m : ℤ) (c : ℝ),
      MemLp (fun x ↦ u x - c) 2 (volume.restrict (cube d m)) := by
    intro m c
    haveI := isFiniteMeasure_restrict_cube d m
    exact (hmem m).sub (memLp_const c)
  refine ⟨hmem, fun m ↦ ?_, fun m ↦ (hmem m).integrable_sq, fun R c ↦ ?_,
    fun n ↦ (hsub n _).integrable_sq⟩
  · haveI := isFiniteMeasure_restrict_cube d m
    exact (hmem m).integrable one_le_two
  · -- enclose the ball in a large centered cube
    obtain ⟨k, hk⟩ :=
      pow_unbounded_of_one_lt (2 * max R 0) (by norm_num : (1 : ℝ) < 3)
    have hincl : Metric.ball (0 : Vec d) R ⊆ cube d (k : ℤ) := by
      rw [cube_eq_ball]
      refine Metric.ball_subset_ball ?_
      have h2 : ((3 : ℝ) ^ k) = (3 : ℝ) ^ (k : ℤ) := (zpow_natCast 3 k).symm
      have h3 : R ≤ max R 0 := le_max_left _ _
      rw [← h2]
      linarith
    have hInt : IntegrableOn (fun x ↦ (u x - c) ^ 2) (cube d (k : ℤ)) :=
      (hsub (k : ℤ) c).integrable_sq
    exact hInt.mono_set hincl

/-! ### The `ℕ`-indexed Liouville assembly -/



theorem liouville_representative_of_natDisplays
    {gamma C : ℝ} {u : Vec d → ℝ} (hgamma : 0 < gamma) (hC : 0 ≤ C)
    (hfreq : ∀ ε > 0, ∃ᶠ R : ℝ in atTop,
      liouvilleFunctional (d := d) gamma u R < ε)
    (huInt : ∀ m : ℤ, IntegrableOn u (cube d m))
    (huSq : ∀ m : ℤ, IntegrableOn (fun x ↦ u x ^ 2) (cube d m))
    (hball : ∀ (R : ℝ) (c : ℝ),
      IntegrableOn (fun x ↦ (u x - c) ^ 2) (Metric.ball (0 : Vec d) R))
    (hcent : ∀ n : ℤ,
      IntegrableOn (fun x ↦ (u x - averageOn (cube d n) u) ^ 2) (cube d n))
    (hdisplay : ∀ n : ℕ, ∃ N : ℤ, ∀ m : ℤ, N ≤ m →
      normalizedL2On (cube d (n : ℤ))
          (fun x ↦ u x - averageOn (cube d (n : ℤ)) u) ≤
        C * (3 : ℝ) ^ (-gamma * ((m : ℝ) - ((n : ℤ) : ℝ))) *
          normalizedL2On (cube d m)
            (fun x ↦ u x - averageOn (cube d m) u))
    (P : ∀ m : ℤ, H1Function (openCubeSet (originCube d m)) → Prop) :
    ∃ uRep : Vec d → ℝ,
      Continuous uRep ∧
      uRep =ᵐ[volume] u ∧
      (∀ m : ℤ, ∀ um : H1Function (openCubeSet (originCube d m)),
        (∀ x, um.toFun x = u x) → P m um →
        uRep =ᵐ[volume.restrict (openCubeSet (originCube d m))] um.toFun) ∧
      ∃ c' : ℝ, ∀ x, uRep x = c' := by
  have hlocal : ∀ n : ℕ,
      u =ᵐ[volume.restrict (cube d (n : ℤ))]
        fun _ ↦ averageOn (cube d (n : ℤ)) u := by
    intro n
    refine ae_eq_average_of_disp (gamma := gamma) hC (n : ℤ) (hcent (n : ℤ)) ?_
    intro eps heps
    obtain ⟨N, hN⟩ := hdisplay n
    obtain ⟨m, hmN, hmlt⟩ :=
      exists_scale_ge_and_lt_v4 hgamma hfreq huInt huSq hball heps N
    have hY : 0 ≤ normalizedL2On (cube d m)
        (fun x ↦ u x - averageOn (cube d m) u) :=
      Section6Iteration.normalizedL2On_nonneg _ _
    have hstep := hN m hmN
    refine hstep.trans ?_
    rw [rpow_neg_sub_split gamma m (n : ℤ)]
    have hfac : (0 : ℝ) ≤ C * (3 : ℝ) ^ (gamma * (n : ℝ)) := by positivity
    calc C * ((3 : ℝ) ^ (gamma * (n : ℝ)) *
            (3 : ℝ) ^ (-gamma * (m : ℝ))) *
          normalizedL2On (cube d m)
            (fun x ↦ u x - averageOn (cube d m) u)
        = (C * (3 : ℝ) ^ (gamma * (n : ℝ))) *
            ((3 : ℝ) ^ (-gamma * (m : ℝ)) *
              normalizedL2On (cube d m)
                (fun x ↦ u x - averageOn (cube d m) u)) := by ring
      _ ≤ (C * (3 : ℝ) ^ (gamma * (n : ℝ))) * eps :=
          mul_le_mul_of_nonneg_left hmlt.le hfac
      _ = C * (3 : ℝ) ^ (gamma * (n : ℝ)) * eps := by ring
  have hcube : ∀ n : ℕ, ∀ᵐ x ∂volume,
      x ∈ cube d (n : ℤ) → u x = averageOn (cube d (n : ℤ)) u := by
    intro n
    refine (ae_restrict_iff' ?_).1 (hlocal n)
    exact measurableSet_openCubeSet (originCube d (n : ℤ))
  exact exists_liouville_representative_of_forall_cube hcube P

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremCUncut
