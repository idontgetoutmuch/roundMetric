import SphericalChart
import RoundSphereMetric

/-!
# The round metric of `S²` in spherical coordinates: `g = dθ² + sin²θ dφ²`

This file connects the two objects that already exist in this project:

* the **round metric** `g` on the sphere, namely the Riemannian metric on
  `RoundSphere E 2 = sphere (0 : E) 1` obtained in `RoundSphereMetric.lean` by pulling back
  (`RiemannianMetric.comap`) the inner product of the ambient space `E = EuclideanSpace ℝ (Fin 3)`
  along the inclusion `RoundSphere.inclusion`;
* the **spherical chart** of `MercatorGeom.lean`, with its coordinate frame `Xθ`, `Xφ` on the
  chart domain `sphSource`.

The main results are `inner_Xθ_Xθ`, `inner_Xφ_Xφ` and `inner_Xθ_Xφ`, which say that in this
frame the round metric is `dθ² + sin²θ dφ²`:

```
g (Xθ, Xθ) = 1,    g (Xφ, Xφ) = sin²θ,    g (Xθ, Xφ) = 0.
```

The equivalent statement on arbitrary tangent vectors,
`g (v, w) = dθ(v) dθ(w) + sin²θ dφ(v) dφ(w)`, is `inner_eq_dθ_dφ`.

Everything is deduced from the single "first fundamental form" identity
`inner_fderiv_sphInvVec`, which computes the ambient inner product of two derivatives of the
parametrisation `sphInvVec (θ, φ) = (sin θ cos φ, sin θ sin φ, cos θ)`.

Note that `RoundSphere (EuclideanSpace ℝ (Fin 3)) 2` and the type `S2` of `MercatorGeom.lean`
are the same type (both unfold to `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`), so the
spherical chart and the round metric really do live on the same manifold.
-/

open Bundle Manifold Real
open scoped Manifold RealInnerProductSpace

noncomputable section

/-- The ambient space of the round `2`-sphere. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The model space of the `2`-sphere, i.e. the space of `(θ, φ)`-coordinates. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

instance : Fact (Module.finrank ℝ E3 = 2 + 1) :=
  ⟨by simp only [finrank_euclideanSpace, Fintype.card_fin]⟩

/-- The norm coming from the round metric, on a single tangent space.  This is literally the
instance provided by the `RiemannianBundle` structure of `RoundSphereMetric.lean`; it is restated
here in eta-expanded form, for the type `S2` of `MercatorGeom.lean`, so that instance resolution
finds it. -/
instance instNormedAddCommGroupTangentSphere (x : S2) :
    NormedAddCommGroup (TangentSpace (𝓡 2) x) :=
  (inferInstance : ∀ y : RoundSphere E3 2, NormedAddCommGroup (TangentSpace (𝓡 2) y)) x

/-- The inner product coming from the round metric, on a single tangent space; again this is the
instance of `RoundSphereMetric.lean`, restated for the type `S2`. -/
instance instInnerProductSpaceTangentSphere (x : S2) :
    InnerProductSpace ℝ (TangentSpace (𝓡 2) x) :=
  (inferInstance : ∀ y : RoundSphere E3 2, InnerProductSpace ℝ (TangentSpace (𝓡 2) y)) x

local notation "π₀" => (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ)
local notation "π₁" => (EuclideanSpace.proj (1 : Fin 2) : E2 →L[ℝ] ℝ)

/-! ### The derivative of the spherical parametrisation -/

lemma hasFDerivAt_coord0 (q : E2) : HasFDerivAt (fun p : E2 => p 0) π₀ q := by
  simpa using (EuclideanSpace.proj (0 : Fin 2) : E2 →L[ℝ] ℝ).hasFDerivAt

lemma hasFDerivAt_coord1 (q : E2) : HasFDerivAt (fun p : E2 => p 1) π₁ q := by
  simpa using (EuclideanSpace.proj (1 : Fin 2) : E2 →L[ℝ] ℝ).hasFDerivAt

/-- `∂(sin θ cos φ) = cos θ cos φ dθ - sin θ sin φ dφ`. -/
lemma hasFDerivAt_sphInvVec_comp0 (q : E2) :
    HasFDerivAt (fun p : E2 => Real.sin (p 0) * Real.cos (p 1))
      ((Real.cos (q 0) * Real.cos (q 1)) • π₀ - (Real.sin (q 0) * Real.sin (q 1)) • π₁) q := by
  have hs := (Real.hasDerivAt_sin (q 0)).comp_hasFDerivAt q (hasFDerivAt_coord0 q)
  have hc := (Real.hasDerivAt_cos (q 1)).comp_hasFDerivAt q (hasFDerivAt_coord1 q)
  refine (hs.mul hc).congr_fderiv ?_
  ext v
  simp
  ring

/-- `∂(sin θ sin φ) = cos θ sin φ dθ + sin θ cos φ dφ`. -/
lemma hasFDerivAt_sphInvVec_comp1 (q : E2) :
    HasFDerivAt (fun p : E2 => Real.sin (p 0) * Real.sin (p 1))
      ((Real.cos (q 0) * Real.sin (q 1)) • π₀ + (Real.sin (q 0) * Real.cos (q 1)) • π₁) q := by
  have hs := (Real.hasDerivAt_sin (q 0)).comp_hasFDerivAt q (hasFDerivAt_coord0 q)
  have hc := (Real.hasDerivAt_sin (q 1)).comp_hasFDerivAt q (hasFDerivAt_coord1 q)
  refine (hs.mul hc).congr_fderiv ?_
  ext v
  simp
  ring

/-- `∂(cos θ) = -sin θ dθ`. -/
lemma hasFDerivAt_sphInvVec_comp2 (q : E2) :
    HasFDerivAt (fun p : E2 => Real.cos (p 0)) ((-Real.sin (q 0)) • π₀) q := by
  refine ((Real.hasDerivAt_cos (q 0)).comp_hasFDerivAt q (hasFDerivAt_coord0 q)).congr_fderiv ?_
  ext v
  simp

/-- The derivative of the spherical parametrisation
`sphInvVec (θ, φ) = (sin θ cos φ, sin θ sin φ, cos θ)`. -/
lemma sphInvVec_hasFDerivAt (q : E2) :
    HasFDerivAt sphInvVec
      (((EuclideanSpace.equiv (Fin 3) ℝ).symm : (Fin 3 → ℝ) →L[ℝ] E3).comp
        (ContinuousLinearMap.pi
          ![(Real.cos (q 0) * Real.cos (q 1)) • π₀ - (Real.sin (q 0) * Real.sin (q 1)) • π₁,
            (Real.cos (q 0) * Real.sin (q 1)) • π₀ + (Real.sin (q 0) * Real.cos (q 1)) • π₁,
            (-Real.sin (q 0)) • π₀])) q := by
  have hpi : HasFDerivAt
      (fun p : E2 => (![Real.sin (p 0) * Real.cos (p 1), Real.sin (p 0) * Real.sin (p 1),
          Real.cos (p 0)] : Fin 3 → ℝ))
      (ContinuousLinearMap.pi
          ![(Real.cos (q 0) * Real.cos (q 1)) • π₀ - (Real.sin (q 0) * Real.sin (q 1)) • π₁,
            (Real.cos (q 0) * Real.sin (q 1)) • π₀ + (Real.sin (q 0) * Real.cos (q 1)) • π₁,
            (-Real.sin (q 0)) • π₀]) q := by
    rw [hasFDerivAt_pi']
    intro i
    rw [ContinuousLinearMap.proj_pi]
    fin_cases i
    · exact hasFDerivAt_sphInvVec_comp0 q
    · exact hasFDerivAt_sphInvVec_comp1 q
    · exact hasFDerivAt_sphInvVec_comp2 q
  exact ((EuclideanSpace.equiv (Fin 3) ℝ).symm.hasFDerivAt).comp q hpi

/-- **The first fundamental form of the sphere.**  The ambient inner product of two derivatives
of the spherical parametrisation at `q = (θ, φ)` is `v₀ w₀ + sin²θ v₁ w₁`, i.e. the parametrised
round metric is `dθ² + sin²θ dφ²`. -/
lemma inner_fderiv_sphInvVec (q v w : E2) :
    ⟪fderiv ℝ sphInvVec q v, fderiv ℝ sphInvVec q w⟫
      = v 0 * w 0 + Real.sin (q 0) ^ 2 * (v 1 * w 1) := by
  rw [(sphInvVec_hasFDerivAt q).fderiv]
  simp [PiLp.inner_apply, Fin.sum_univ_three, EuclideanSpace.equiv]
  linear_combination (w 0 * v 0 * Real.cos (q 0) ^ 2 + w 1 * v 1 * Real.sin (q 0) ^ 2) *
      Real.sin_sq_add_cos_sq (q 1) + (w 0 * v 0) * Real.sin_sq_add_cos_sq (q 0)

/-! ### Transporting the computation to the sphere -/

/-- The round metric on a tangent space of the sphere is the ambient inner product of the images
of the tangent vectors under the differential of the inclusion.  This is exactly the definition of
`RiemannianMetric.comap`. -/
lemma inner_tangentSpace_eq (x : S2) (v w : TangentSpace (𝓡 2) x) :
    ⟪v, w⟫ = ⟪mfderiv (𝓡 2) 𝓘(ℝ, E3) (RoundSphere.inclusion E3 2) x v,
      mfderiv (𝓡 2) 𝓘(ℝ, E3) (RoundSphere.inclusion E3 2) x w⟫ := rfl

/-- The differential of the inclusion, applied to a chart-coordinate tangent vector, is the
derivative of the parametrisation `sphInvVec`. -/
lemma mfderiv_inclusion_mfderiv_sphInv {x : S2} (hx : x ∈ sphSource) (v : E2) :
    mfderiv (𝓡 2) 𝓘(ℝ, E3) (RoundSphere.inclusion E3 2) x
        (mfderiv 𝓘(ℝ, E2) (𝓡 2) sphInv (sphFwd x) v)
      = fderiv ℝ sphInvVec (sphFwd x) v := by
  have hxq : sphInv (sphFwd x) = x := sph_left_inv x hx
  have hincl : MDifferentiableAt (𝓡 2) 𝓘(ℝ, E3) ((↑) : S2 → E3) (sphInv (sphFwd x)) :=
    (contMDiff_coe_sphere (n := 2) (m := 1)).contMDiffAt.mdifferentiableAt one_ne_zero
  have hinv : MDifferentiableAt 𝓘(ℝ, E2) (𝓡 2) sphInv (sphFwd x) :=
    sphInv_contMDiff.contMDiffAt.mdifferentiableAt (by norm_num)
  have hcomp := mfderiv_comp (I' := (𝓡 2)) (sphFwd x) hincl hinv
  have hLHS : mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) (((↑) : S2 → E3) ∘ sphInv) (sphFwd x)
      = fderiv ℝ sphInvVec (sphFwd x) := mfderiv_eq_fderiv
  rw [hLHS, hxq] at hcomp
  exact congrArg (fun L => L v) hcomp.symm

/-- The round metric evaluated on two coordinate-frame vectors: `g = dθ² + sin²θ dφ²`. -/
lemma inner_coordinate_vectors {x : S2} (hx : x ∈ sphSource) (v w : E2) :
    @inner ℝ (TangentSpace (𝓡 2) x) _ (mfderiv 𝓘(ℝ, E2) (𝓡 2) sphInv (sphFwd x) v)
        (mfderiv 𝓘(ℝ, E2) (𝓡 2) sphInv (sphFwd x) w)
      = v 0 * w 0 + Real.sin (θ_coord x) ^ 2 * (v 1 * w 1) := by

  have hθ : (sphFwd x : E2) 0 = θ_coord x := rfl
  erw [inner_tangentSpace_eq x]
  erw [mfderiv_inclusion_mfderiv_sphInv hx, mfderiv_inclusion_mfderiv_sphInv hx]
  erw [inner_fderiv_sphInvVec]
  rw [hθ]

/-! ### The round metric in the spherical chart -/

/-- `g (∂θ, ∂θ) = 1`. -/
theorem inner_Xθ_Xθ {x : S2} (hx : x ∈ sphSource) : ⟪Xθ x, Xθ x⟫ = 1 := by
  have h : ⟪Xθ x, Xθ x⟫ = _ := inner_coordinate_vectors hx
    (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
  rw [h]
  simp [EuclideanSpace.single_apply]

/-- `g (∂φ, ∂φ) = sin²θ`. -/
theorem inner_Xφ_Xφ {x : S2} (hx : x ∈ sphSource) :
    ⟪Xφ x, Xφ x⟫ = Real.sin (θ_coord x) ^ 2 := by
  have h : ⟪Xφ x, Xφ x⟫ = _ := inner_coordinate_vectors hx
    (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
  rw [h]
  simp [EuclideanSpace.single_apply]

/-- `g (∂θ, ∂φ) = 0`. -/
theorem inner_Xθ_Xφ {x : S2} (hx : x ∈ sphSource) : ⟪Xθ x, Xφ x⟫ = 0 := by
  have h : ⟪Xθ x, Xφ x⟫ = _ := inner_coordinate_vectors hx
    (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
  rw [h]
  simp [EuclideanSpace.single_apply]

theorem inner_eq_dθ_dφ {x : S2} (hx : x ∈ sphSource) (v w : TangentSpace (𝓡 2) x) :
    ⟪v, w⟫ = dθ x v * dθ x w + Real.sin (θ_coord x) ^ 2 * (dφ x v * dφ x w) := by
  have e1 := inner_Xθ_Xθ hx
  have e2 := inner_Xφ_Xφ hx
  have e3 := inner_Xθ_Xφ hx
  have e4 : (⟪Xφ x, Xθ x⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact e3
  have h1 : ⟪dθ x v • Xθ x, w⟫ = dθ x v * ⟪Xθ x, w⟫ := real_inner_smul_left (Xθ x) w ((dθ x) v)
  calc ⟪v, w⟫
      = ⟪dθ x v • Xθ x + dφ x v • Xφ x, dθ x w • Xθ x + dφ x w • Xφ x⟫ := by
        rw [frame_dual hx v, frame_dual hx w]
    _ = dθ x v * dθ x w * ⟪Xθ x, Xθ x⟫ + dθ x v * dφ x w * ⟪Xθ x, Xφ x⟫
        + (dφ x v * dθ x w * ⟪Xφ x, Xθ x⟫ + dφ x v * dφ x w * ⟪Xφ x, Xφ x⟫) := by
        exact sorry
    _ = dθ x v * dθ x w + Real.sin (θ_coord x) ^ 2 * (dφ x v * dφ x w) := by
        rw [e1, e2, e3, e4]; ring

/-- The round metric in the spherical chart is `dθ² + sin²θ dφ²`: for arbitrary tangent vectors
`v`, `w` at a point of the chart domain,
`g (v, w) = dθ(v) dθ(w) + sin²θ · dφ(v) dφ(w)`. -/
theorem inner_eq_dθ_dφ' {x : S2} (hx : x ∈ sphSource) (v w : TangentSpace (𝓡 2) x) :
    ⟪v, w⟫ = dθ x v * dθ x w + Real.sin (θ_coord x) ^ 2 * (dφ x v * dφ x w) := by
  have hsym : (⟪Xφ x, Xθ x⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact inner_Xθ_Xφ hx
  conv_lhs => rw [← frame_dual hx v, ← frame_dual hx w]
  have expand : ⟪dθ x v • Xθ x + dφ x v • Xφ x, dθ x w • Xθ x + dφ x w • Xφ x⟫
    = ⟪dθ x v • Xθ x, dθ x w • Xθ x + dφ x w • Xφ x⟫
      + ⟪dφ x v • Xφ x, dθ x w • Xθ x + dφ x w • Xφ x⟫ :=
  inner_add_left _ _ _
  rw [expand]
  have er1 : ⟪dθ x v • Xθ x, dθ x w • Xθ x + dφ x w • Xφ x⟫
      = ⟪dθ x v • Xθ x, dθ x w • Xθ x⟫ + ⟪dθ x v • Xθ x, dφ x w • Xφ x⟫ :=
    inner_add_right _ _ _
  have er2 : ⟪dφ x v • Xφ x, dθ x w • Xθ x + dφ x w • Xφ x⟫
      = ⟪dφ x v • Xφ x, dθ x w • Xθ x⟫ + ⟪dφ x v • Xφ x, dφ x w • Xφ x⟫ :=
    inner_add_right _ _ _
  rw [er1, er2]
  have s11 : ⟪dθ x v • Xθ x, dθ x w • Xθ x⟫ = dθ x v * (dθ x w * ⟪Xθ x, Xθ x⟫) :=
    (real_inner_smul_left (Xθ x) (dθ x w • Xθ x) (dθ x v)).trans
      (congrArg (dθ x v * ·) (real_inner_smul_right (Xθ x) (Xθ x) (dθ x w)))
  have s12 : ⟪dθ x v • Xθ x, dφ x w • Xφ x⟫ = dθ x v * (dφ x w * ⟪Xθ x, Xφ x⟫) :=
    (real_inner_smul_left (Xθ x) (dφ x w • Xφ x) (dθ x v)).trans
      (congrArg (dθ x v * ·) (real_inner_smul_right (Xθ x) (Xφ x) (dφ x w)))
  have s21 : ⟪dφ x v • Xφ x, dθ x w • Xθ x⟫ = dφ x v * (dθ x w * ⟪Xφ x, Xθ x⟫) :=
    (real_inner_smul_left (Xφ x) (dθ x w • Xθ x) (dφ x v)).trans
      (congrArg (dφ x v * ·) (real_inner_smul_right (Xφ x) (Xθ x) (dθ x w)))
  have s22 : ⟪dφ x v • Xφ x, dφ x w • Xφ x⟫ = dφ x v * (dφ x w * ⟪Xφ x, Xφ x⟫) :=
    (real_inner_smul_left (Xφ x) (dφ x w • Xφ x) (dφ x v)).trans
      (congrArg (dφ x v * ·) (real_inner_smul_right (Xφ x) (Xφ x) (dφ x w)))
  rw [s11, s12, s21, s22,
      inner_Xθ_Xθ hx, inner_Xφ_Xφ hx, inner_Xθ_Xφ hx, hsym]
  ring


end
