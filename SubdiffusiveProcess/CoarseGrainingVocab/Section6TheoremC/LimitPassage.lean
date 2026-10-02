import SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC.EnergyIdentity




namespace SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC

open MeasureTheory Filter Homogenization SubdiffusiveProcess.CoarseGrainingVocab

noncomputable section

variable {d : ℕ}

/-- **The energy display passes to the limit.**  Both sides of
`e.large.scale.energy.multifractal` are vector seminorms of the same composite
field `√(a) ∇u`, so a termwise estimate survives convergence of that field in
the seminorm on each of the two windows. -/
theorem vectorNormalizedL2On_le_mul_of_tendsto {V W : Set (Vec d)}
    {F : ℕ → Vec d → Vec d} {Flim : Vec d → Vec d} {K : ℝ}
    (hFV : ∀ j, MemLp (fun x ↦ euclideanNorm (F j x)) 2 (volume.restrict V))
    (hFlimV : MemLp (fun x ↦ euclideanNorm (Flim x)) 2 (volume.restrict V))
    (hFsubV : ∀ j, MemLp (fun x ↦ euclideanNorm (F j x - Flim x)) 2
      (volume.restrict V))
    (hV : Tendsto (fun j ↦ vectorNormalizedL2On V (fun x ↦ F j x - Flim x))
      atTop (nhds 0))
    (hFW : ∀ j, MemLp (fun x ↦ euclideanNorm (F j x)) 2 (volume.restrict W))
    (hFlimW : MemLp (fun x ↦ euclideanNorm (Flim x)) 2 (volume.restrict W))
    (hFsubW : ∀ j, MemLp (fun x ↦ euclideanNorm (F j x - Flim x)) 2
      (volume.restrict W))
    (hW : Tendsto (fun j ↦ vectorNormalizedL2On W (fun x ↦ F j x - Flim x))
      atTop (nhds 0))
    (hle : ∀ j, vectorNormalizedL2On V (F j) ≤
      K * vectorNormalizedL2On W (F j)) :
    vectorNormalizedL2On V Flim ≤ K * vectorNormalizedL2On W Flim :=
  le_mul_of_forall_le_mul_of_tendsto
    (tendsto_vectorNormalizedL2On_of_tendsto_sub hFV hFlimV hFsubV hV)
    (tendsto_vectorNormalizedL2On_of_tendsto_sub hFW hFlimW hFsubW hW) hle

/-- The centered oscillation display in the same shape, recorded for symmetry
with the energy display: the centering constant is part of the field, so the
scalar limit lemma applies verbatim once the centered functions converge. -/
theorem normalizedL2On_centered_le_mul_of_tendsto {V W : Set (Vec d)}
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
  normalizedL2On_le_mul_of_tendsto hfV hflimV hV hfW hflimW hW hle

end

end SubdiffusiveProcess.CoarseGrainingVocab.Section6TheoremC
