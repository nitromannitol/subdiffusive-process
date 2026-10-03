module

public import SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary.WindowCellCover

@[expose] public section




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary

open SubdiffusiveProcess.CoarseGrainingVocab Homogenization Homogenization.Book MeasureTheory
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

theorem measurableSet_cube (d : ℕ) (m : ℤ) : MeasurableSet (cube d m) :=
  measurableSet_openCubeSet (originCube d m)

theorem boundaryWindow_eq_inter (m : ℤ) (x : Vec d) (r : ℝ) :
    boundaryWindow d m x r = supWindow x r ∩ cube d m := rfl

theorem truncatedCube_eq_inter (d : ℕ) (m j : ℤ) (y : Vec d) :
    truncatedCube d m j y = translatedCube d j y ∩ cube d m := rfl



theorem setIntegral_supWindow_indicator_cube (m : ℤ) (x : Vec d) (r : ℝ)
    (F : Vec d → ℝ) :
    ∫ p in supWindow x r, (cube d m).indicator F p =
      ∫ p in boundaryWindow d m x r, F p := by
  rw [setIntegral_indicator (measurableSet_cube d m), boundaryWindow_eq_inter]

/-- The same identity on a cell of the triadic cover: the cell contributes its
*truncated* cube, which is the carrier of the committed per-cell prices. -/
theorem setIntegral_cellCube_indicator_cube (m j : ℤ) (idx : Fin d → ℤ)
    (F : Vec d → ℝ) :
    ∫ p in cubeSet (cellCube j idx), (cube d m).indicator F p =
      ∫ p in truncatedCube d m j (cellCentre j idx), F p := by
  rw [setIntegral_cubeSet_cellCube_eq_translatedCube,
    setIntegral_indicator (measurableSet_cube d m), truncatedCube_eq_inter]

/-- On a set already inside `𝔠_m` the restriction is invisible. -/
theorem setIntegral_indicator_cube_of_subset {m : ℤ} {V : Set (Vec d)}
    (hV : V ⊆ cube d m) (F : Vec d → ℝ) :
    ∫ p in V, (cube d m).indicator F p = ∫ p in V, F p := by
  rw [setIntegral_indicator (measurableSet_cube d m),
    Set.inter_eq_self_of_subset_left hV]

/-- **The summed cover step.**

Let `F, G ≥ 0` be densities integrable on `𝔠_m`, and let every scale-`j` cell of
the index box of the window of radius `ρ` carry a row

```text
∫_{U_{m,j}(q)} F ≤ Θ ∫_{P_q} F + A ∫_{P_q} G + price_q
```

whose two integral legs live on a set `P_q = S idx` contained in `𝔠_m` and in
the cell's own parent ball of radius `3^{j+3}/2`.  Then, for every outer radius
`R ≥ ρ + 14·3^j`,

```text
∫_{window ρ} F ≤ 28^d Θ ∫_{window R} F + 28^d A ∫_{window R} G + ∑_q price_q .
```

**No volume ratio appears.**  The dimension-only `28^d` is the bounded overlap
of the projected parents; the per-cell prices are summed as they stand, which
is what makes the parent-*normalized* form of the committed interior collapse
(`InteriorCellAtScale.exists_interiorCellEnergy_le_parentPrices_atScale`)
usable at a free cover depth. -/
theorem setIntegral_boundaryWindow_step_of_cellRow (j m : ℤ) (x : Vec d)
    {rho Rr : ℝ} {F G : Vec d → ℝ} (hF0 : ∀ p, 0 ≤ F p) (hG0 : ∀ p, 0 ≤ G p)
    {Theta Acoef : ℝ} (hTheta : 0 ≤ Theta) (hAcoef : 0 ≤ Acoef)
    (Price : (Fin d → ℤ) → ℝ)
    (S : (Fin d → ℤ) → Set (Vec d)) (hSmeas : ∀ idx, MeasurableSet (S idx))
    (hSdom : ∀ idx, S idx ⊆ cube d m)
    (hSball : ∀ idx ∈ windowBox j x rho,
      S idx ⊆ supWindow (cellCentre j idx) ((3 : ℝ) ^ (j + 3) / 2))
    (hrow : ∀ idx ∈ windowBox j x rho,
      ∫ p in truncatedCube d m j (cellCentre j idx), F p ≤
        Theta * (∫ p in S idx, F p) + Acoef * (∫ p in S idx, G p) + Price idx)
    (hgap : rho + 14 * (3 : ℝ) ^ j ≤ Rr)
    (hintF : IntegrableOn F (cube d m)) (hintG : IntegrableOn G (cube d m)) :
    ∫ p in boundaryWindow d m x rho, F p ≤
      (28 : ℝ) ^ d * Theta * (∫ p in boundaryWindow d m x Rr, F p) +
        (28 : ℝ) ^ d * Acoef * (∫ p in boundaryWindow d m x Rr, G p) +
        ∑ idx ∈ windowBox j x rho, Price idx := by
  classical
  have hcubeMeas : MeasurableSet (cube d m) := measurableSet_cube d m
  set F' : Vec d → ℝ := (cube d m).indicator F with hF'
  set G' : Vec d → ℝ := (cube d m).indicator G with hG'
  have hF'0 : ∀ p, 0 ≤ F' p := fun p =>
    Set.indicator_nonneg (fun q _ => hF0 q) p
  have hG'0 : ∀ p, 0 ≤ G' p := fun p =>
    Set.indicator_nonneg (fun q _ => hG0 q) p
  have hF'int : Integrable F' := hintF.integrable_indicator hcubeMeas
  have hG'int : Integrable G' := hintG.integrable_indicator hcubeMeas
  -- the cover of the inner window by the cells of its index box
  have hcover := setIntegral_supWindow_le_sum_cells j x rho hF'0
    (hF'int.integrableOn)
  -- the per-cell row, transported to the `F'` normalization
  have hrow' : ∀ idx ∈ windowBox j x rho,
      ∫ p in cubeSet (cellCube j idx), F' p ≤
        Theta * (∫ p in S idx, F' p) + Acoef * (∫ p in S idx, G' p) +
          Price idx := by
    intro idx hidx
    rw [hF', hG', setIntegral_cellCube_indicator_cube,
      setIntegral_indicator_cube_of_subset (hSdom idx),
      setIntegral_indicator_cube_of_subset (hSdom idx)]
    exact hrow idx hidx
  have hsumrow : ∑ idx ∈ windowBox j x rho, ∫ p in cubeSet (cellCube j idx), F' p ≤
      ∑ idx ∈ windowBox j x rho,
        (Theta * (∫ p in S idx, F' p) + Acoef * (∫ p in S idx, G' p) +
          Price idx) := Finset.sum_le_sum hrow'
  have hsplit : ∑ idx ∈ windowBox j x rho,
      (Theta * (∫ p in S idx, F' p) + Acoef * (∫ p in S idx, G' p) + Price idx) =
      Theta * (∑ idx ∈ windowBox j x rho, ∫ p in S idx, F' p) +
        Acoef * (∑ idx ∈ windowBox j x rho, ∫ p in S idx, G' p) +
        ∑ idx ∈ windowBox j x rho, Price idx := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
  -- the bounded overlap of the projected parents
  have hoverF := sum_setIntegral_parents_le j x rho hF'0 S hSmeas hSball
    hF'int.integrableOn
  have hoverG := sum_setIntegral_parents_le j x rho hG'0 S hSmeas hSball
    hG'int.integrableOn
  -- monotonicity in the radius
  have hsub : supWindow x (rho + 14 * (3 : ℝ) ^ j) ⊆ supWindow x Rr :=
    supWindow_mono hgap
  have hmonoF : ∫ p in supWindow x (rho + 14 * (3 : ℝ) ^ j), F' p ≤
      ∫ p in supWindow x Rr, F' p :=
    setIntegral_mono_set hF'int.integrableOn
      (Filter.Eventually.of_forall hF'0) (HasSubset.Subset.eventuallyLE hsub)
  have hmonoG : ∫ p in supWindow x (rho + 14 * (3 : ℝ) ^ j), G' p ≤
      ∫ p in supWindow x Rr, G' p :=
    setIntegral_mono_set hG'int.integrableOn
      (Filter.Eventually.of_forall hG'0) (HasSubset.Subset.eventuallyLE hsub)
  have hF : Theta * (∑ idx ∈ windowBox j x rho, ∫ p in S idx, F' p) ≤
      (28 : ℝ) ^ d * Theta * (∫ p in supWindow x Rr, F' p) := by
    have h1 := mul_le_mul_of_nonneg_left hoverF hTheta
    have h2 := mul_le_mul_of_nonneg_left hmonoF
      (by positivity : (0 : ℝ) ≤ Theta * (28 : ℝ) ^ d)
    nlinarith [h1, h2]
  have hG : Acoef * (∑ idx ∈ windowBox j x rho, ∫ p in S idx, G' p) ≤
      (28 : ℝ) ^ d * Acoef * (∫ p in supWindow x Rr, G' p) := by
    have h1 := mul_le_mul_of_nonneg_left hoverG hAcoef
    have h2 := mul_le_mul_of_nonneg_left hmonoG
      (by positivity : (0 : ℝ) ≤ Acoef * (28 : ℝ) ^ d)
    nlinarith [h1, h2]
  have hchain : ∫ p in supWindow x rho, F' p ≤
      (28 : ℝ) ^ d * Theta * (∫ p in supWindow x Rr, F' p) +
        (28 : ℝ) ^ d * Acoef * (∫ p in supWindow x Rr, G' p) +
        ∑ idx ∈ windowBox j x rho, Price idx := by
    calc ∫ p in supWindow x rho, F' p
        ≤ ∑ idx ∈ windowBox j x rho, ∫ p in cubeSet (cellCube j idx), F' p := hcover
      _ ≤ Theta * (∑ idx ∈ windowBox j x rho, ∫ p in S idx, F' p) +
          Acoef * (∑ idx ∈ windowBox j x rho, ∫ p in S idx, G' p) +
          ∑ idx ∈ windowBox j x rho, Price idx := hsplit ▸ hsumrow
      _ ≤ _ := by linarith [hF, hG]
  simpa only [hF', hG', setIntegral_supWindow_indicator_cube] using hchain

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6HarmonicBoundary
