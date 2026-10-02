import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.LiouvilleV4




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-! ### The cubes exhaust the space -/

/-- Every point lies in some centered cube. -/
theorem exists_mem_cube (x : Vec d) : ∃ n : ℕ, x ∈ cube d (n : ℤ) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * ‖x‖) (by norm_num : (1 : ℝ) < 3)
  refine ⟨n, ?_⟩
  rw [cube_eq_ball, mem_ball_zero_iff]
  have hzp : ((3 : ℝ) ^ (n : ℤ)) = (3 : ℝ) ^ n := zpow_natCast 3 n
  rw [hzp]
  have hnn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  linarith

/-! ### Comparing two constants on a set of positive measure -/

/-- Two constants that agree almost everywhere on a set of positive measure are
equal. -/
theorem eq_of_ae_mem_imp {a b : ℝ} {W : Set (Vec d)} (hW : volume W ≠ 0)
    (h : ∀ᵐ x ∂volume, x ∈ W → a = b) : a = b := by
  by_contra hne
  have hnm : ∀ᵐ x ∂volume, x ∉ W := by
    filter_upwards [h] with x hx
    intro hxW
    exact hne (hx hxW)
  exact hW (measure_eq_zero_iff_ae_notMem.2 hnm)

/-- The centered cube has nonzero volume. -/
theorem volume_cube_ne_zero (d : ℕ) (m : ℤ) : volume (cube d m) ≠ 0 := by
  intro h
  have := volume_cube_toReal_pos d m
  rw [h] at this
  simp at this

/-! ### The global constant -/

/-- If `u` is almost everywhere equal to a single constant on every centered
cube, it is almost everywhere equal to that constant. -/
theorem ae_eq_const_of_forall_cube {u : Vec d → ℝ} {c : ℝ}
    (h : ∀ n : ℕ, ∀ᵐ x ∂volume, x ∈ cube d (n : ℤ) → u x = c) :
    u =ᵐ[volume] fun _ ↦ c := by
  have hall : ∀ᵐ x ∂volume, ∀ n : ℕ, x ∈ cube d (n : ℤ) → u x = c :=
    ae_all_iff.2 h
  filter_upwards [hall] with x hx
  obtain ⟨n, hn⟩ := exists_mem_cube x
  exact hx n hn

/-- **S10, global.**  Local constancy on every centered cube, with a priori
different constants, upgrades to a single global constant. -/
theorem exists_const_ae_of_forall_cube {u : Vec d → ℝ} {c : ℕ → ℝ}
    (h : ∀ n : ℕ, ∀ᵐ x ∂volume, x ∈ cube d (n : ℤ) → u x = c n) :
    ∃ a : ℝ, u =ᵐ[volume] fun _ ↦ a := by
  refine ⟨c 0, ae_eq_const_of_forall_cube fun n ↦ ?_⟩
  -- The constants agree, compared on the smallest cube.
  have hsub : cube d ((0 : ℕ) : ℤ) ⊆ cube d (n : ℤ) :=
    Section6ExcessDecay.cube_subset_cube_of_le (by positivity)
  have hcmp : ∀ᵐ x ∂volume, x ∈ cube d ((0 : ℕ) : ℤ) → c n = c 0 := by
    filter_upwards [h n, h 0] with x hxn hx0
    intro hx
    rw [← hxn (hsub hx), hx0 hx]
  have hcc : c n = c 0 :=
    eq_of_ae_mem_imp (volume_cube_ne_zero d ((0 : ℕ) : ℤ)) hcmp
  filter_upwards [h n] with x hx
  intro hxn
  rw [hx hxn, hcc]

/-! ### The frozen Liouville conclusion package -/

/-- **The Liouville clause, assembled.**  From local constancy on every centered
cube, produce the frozen conclusion package of Theorem C: a continuous,
constant representative, almost everywhere equal to `u`, coherent with every
pointwise-equal local witness.

This composes S10 (this file) with S12 (`ConstantRepresentative`). -/
theorem exists_liouville_representative_of_forall_cube {u : Vec d → ℝ}
    {c : ℕ → ℝ}
    (h : ∀ n : ℕ, ∀ᵐ x ∂volume, x ∈ cube d (n : ℤ) → u x = c n)
    (P : ∀ m : ℤ, H1Function (openCubeSet (originCube d m)) → Prop) :
    ∃ uRep : Vec d → ℝ,
      Continuous uRep ∧
      uRep =ᵐ[volume] u ∧
      (∀ m : ℤ, ∀ um : H1Function (openCubeSet (originCube d m)),
        (∀ x, um.toFun x = u x) → P m um →
        uRep =ᵐ[volume.restrict (openCubeSet (originCube d m))] um.toFun) ∧
      ∃ c' : ℝ, ∀ x, uRep x = c' := by
  obtain ⟨a, ha⟩ := exists_const_ae_of_forall_cube h
  exact exists_constant_continuous_representative_frozenShape ha P

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
