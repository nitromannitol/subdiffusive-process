module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section9Support.Section9GoodCubeGeometry

@[expose] public section




set_option autoImplicit false
open Set MeasureTheory
open SubdiffusiveProcess.CoarseGrainingVocab.Section9SupportInput
open SubdiffusiveProcess.CoarseGrainingVocab.Section9GoodCube
open SubdiffusiveProcess.CoarseGrainingVocab.Section9Percolation
open SubdiffusiveProcess.Section9 (centeredAxisCube)
noncomputable section
namespace SubdiffusiveProcess.CoarseGrainingVocab.Section9Support

/-- Coordinate difference under a common affine map. -/
theorem goodCube_affine_sub {d : ℕ} (y x z : Fin d → ℝ) (s : ℝ) (i : Fin d) :
    (y + s • x) i - (y + s • z) i = s * (x i - z i) := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The affine inverse recovers each point. -/
theorem goodCube_affine_inverse {d : ℕ} (y x : Fin d → ℝ) {s : ℝ} (hs : s ≠ 0) :
    y + s • (s⁻¹ • (x - y)) = x := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  field_simp
  ring

/-- Positive affine scaling preserves cube membership. -/
theorem goodCube_mem_affine_cube {d : ℕ} (y x z : Vec d) (L : ℝ) {s : ℝ} (hs : 0 < s) :
    y + s • x ∈ centeredAxisCube (y + s • z) (s * L) ↔ x ∈ centeredAxisCube z L := by
  simp only [mem_centeredAxisCube, goodCube_affine_sub, abs_mul, abs_of_pos hs,
    mul_div_assoc, mul_lt_mul_iff_right₀ hs]

/-- The transported cube is the exact image of its reference set. -/
theorem goodCube_affine_cube_image {d : ℕ} (y z : Vec d) (L : ℝ) {s : ℝ} (hs : 0 < s) :
    centeredAxisCube (y+s•z) (s*L) = (fun x => y+s•x) '' centeredAxisCube z L := by
  ext x
  constructor
  · intro hx
    refine ⟨s⁻¹ • (x - y), ?_, goodCube_affine_inverse y x hs.ne'⟩
    exact (goodCube_mem_affine_cube y _ z L hs).mp
      (by simpa only [goodCube_affine_inverse y x hs.ne'] using hx)
  · rintro ⟨w, hw, rfl⟩
    exact (goodCube_mem_affine_cube y w z L hs).mpr hw



theorem goodCube_isGridCube_affine {d : ℕ} {grid : Finset (Vec d)} {x y : Vec d} {L : ℝ}
    (h : IsGridCube grid x L) (hL : L ≤ 1)
    (n : ℕ) (w : Fin d → ℤ) (hy : y = fun i => (w i : ℝ) * (3 : ℝ) ^ n) :
    IsGridCube grid (y+(3:ℝ)^n•x) ((3:ℝ)^n*L) := by
  subst hy
  obtain ⟨g, hg, m, k, hm, hx⟩ := h
  have h3ne : (3:ℝ) ≠ 0 := by norm_num
  have hmle : m ≤ 0 := by
    have h1 : (3:ℝ)^m ≤ (3:ℝ)^(0:ℤ) := by rw [← hm]; simpa using hL
    exact (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ) < 3)).mp h1
  obtain ⟨e, he⟩ : ∃ e : ℕ, ((e : ℤ)) = -m :=
    ⟨(-m).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hme : (3:ℝ)^m * (3:ℝ)^(e:ℕ) = 1 := by
    rw [← zpow_natCast (3:ℝ) e, ← zpow_add₀ h3ne, he]
    simp
  refine ⟨g, hg, (n:ℤ)+m, (fun i => (3:ℤ)^e * w i + k i), ?_, ?_⟩
  · rw [hm, zpow_add₀ h3ne, zpow_natCast]
  · funext i
    have hxi : x i = (3:ℝ)^m*(g i + (k i:ℝ)) := congrFun hx i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hxi]
    rw [zpow_add₀ h3ne, zpow_natCast]
    push_cast
    linear_combination (-((3:ℝ)^n * (w i : ℝ))) * hme



theorem goodCube_isGridCube_pointTransport_refutation {d : ℕ} (i0 : Fin d) :
    IsGridCube {(fun _ => 1/3 : Vec d)} (fun _ => 1/3 : Vec d) 1 ∧
      IsGridCube {(fun _ => 1/3 : Vec d)}
        ((0 : Vec d)+(3:ℝ)^(1:ℕ)•(fun _ => 1/3 : Vec d)) ((3:ℝ)^(1:ℕ)*1) ∧
      ¬ IsGridCube
          (Finset.image (fun x : Vec d => (0 : Vec d)+(3:ℝ)^(1:ℕ)•x)
            {(fun _ => 1/3 : Vec d)})
          ((0 : Vec d)+(3:ℝ)^(1:ℕ)•(fun _ => 1/3 : Vec d)) ((3:ℝ)^(1:ℕ)*1) := by
  have hbase : IsGridCube {(fun _ => 1/3 : Vec d)} (fun _ => 1/3 : Vec d) 1 := by
    refine ⟨(fun _ => 1/3 : Vec d), Finset.mem_singleton_self _, 0, fun _ => 0, ?_, ?_⟩
    · norm_num
    · funext i; norm_num
  refine ⟨hbase, goodCube_isGridCube_affine hbase le_rfl 1 (fun _ => 0) ?_, ?_⟩
  · funext i; norm_num
  · rintro ⟨g, hg, m, k, hm, hcentre⟩
    -- the side pins the scale exponent to `1`
    have hm1 : m = 1 := by
      have h1 : (3:ℝ)^m = (3:ℝ)^(1:ℤ) := by rw [← hm]; norm_num
      exact zpow_right_injective₀ (by norm_num) (by norm_num) h1
    -- the only point-transported offset is the constant `1`
    have hg1 : g i0 = 1 := by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
      rw [Finset.mem_singleton] at hx
      subst hx
      norm_num
    -- so the centre equation forces `3 * k i0 = -2` in `ℤ`
    have hci := congrFun hcentre i0
    rw [hm1, hg1] at hci
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zpow_one] at hci
    have hk3 : (3 * k i0 : ℤ) = -2 := by
      have hR : (3 : ℝ) * ((k i0 : ℤ) : ℝ) = -2 := by
        have h1 : (0:ℝ) + (3:ℝ)^(1:ℕ) * (1/3 : ℝ) = 1 := by norm_num
        nlinarith [hci, h1]
      exact_mod_cast hR
    omega

/-- The middle quarter is transported by the same affine map. -/
theorem goodCube_affine_middleQuarter {d : ℕ} (y : Vec d) (Q : Cube d) {s : ℝ} (hs : 0 < s) :
    middleQuarter (y+s•Q.1,s*Q.2) = (fun x=>y+s•x) '' middleQuarter Q := by
  unfold middleQuarter
  have h : s*Q.2/4 = s*(Q.2/4) := by ring
  rw [h]
  exact goodCube_affine_cube_image y Q.1 (Q.2/4) hs

/-- The two relative side constraints survive a common dilation. -/
theorem goodCube_scaled_pair_sides {s r t L K U : ℝ} (hL : L = r * U) (hK : K = t * L) :
    s * L = r * (s * U) ∧ s * K = t * (s * L) := by
  subst hL
  subst hK
  constructor <;> ring

/-- The unit reference cube maps to the native cube. -/
theorem goodCube_affine_reference {d : ℕ} (n : ℕ) (z : Lattice d) :
    (goodCubeCentre n z+(3:ℝ)^n•(0:Vec d), (3:ℝ)^n*(1:ℝ)) =
      (goodCubeCentre n z,(3:ℝ)^n) := by
  simp

/-- A nondegenerate affine map transports closures exactly. -/
theorem goodCube_affine_closure {d : ℕ} (y : Vec d) {s : ℝ} (hs : s ≠ 0) (S : Set (Vec d)) :
    closure ((fun x=>y+s•x) '' S) = (fun x=>y+s•x) '' closure S := by
  let h : Vec d ≃ₜ Vec d := (Homeomorph.smulOfNeZero s hs).trans (Homeomorph.addLeft y)
  exact (h.image_closure S).symm

end SubdiffusiveProcess.CoarseGrainingVocab.Section9Support
