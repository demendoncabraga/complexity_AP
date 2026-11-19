import PaperFormalization.BorelAssignment

namespace PaperFormalization

open Filter Set Topology

instance compactSpace_cantorSet : CompactSpace cantorSet :=
  isCompact_iff_compactSpace.mp isCompact_cantorSet

theorem one_mem_cantorSet : (1 : ℝ) ∈ cantorSet :=
  Set.mem_iInter.mpr fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [preCantorSet_succ]
      exact Or.inr ⟨1, ih, by norm_num⟩

theorem cantorLeft_isGreatest (x : unitInterval) :
    IsGreatest (cantorSet ∩ Iic (x : ℝ)) (sSup (cantorSet ∩ Iic (x : ℝ))) :=
  (isCompact_cantorSet.inter_right isClosed_Iic).isGreatest_sSup
    ⟨0, zero_mem_cantorSet, x.property.1⟩

theorem cantorRight_isLeast (x : unitInterval) :
    IsLeast (cantorSet ∩ Ici (x : ℝ)) (sInf (cantorSet ∩ Ici (x : ℝ))) :=
  (isCompact_cantorSet.inter_right isClosed_Ici).isLeast_sInf
    ⟨1, one_mem_cantorSet, x.property.2⟩

/-- Greatest Cantor point at or to the left of x. -/
noncomputable def cantorLeft (x : unitInterval) : cantorSet :=
  ⟨_, (cantorLeft_isGreatest x).1.1⟩

/-- Least Cantor point at or to the right of x. -/
noncomputable def cantorRight (x : unitInterval) : cantorSet :=
  ⟨_, (cantorRight_isLeast x).1.1⟩

theorem cantorLeft_le (x : unitInterval) : (cantorLeft x : ℝ) ≤ x :=
  (cantorLeft_isGreatest x).1.2

theorem le_cantorRight (x : unitInterval) : (x : ℝ) ≤ cantorRight x :=
  (cantorRight_isLeast x).1.2

theorem cantorLeft_max (x : unitInterval) (z : cantorSet) (hz : (z : ℝ) ≤ x) :
    (z : ℝ) ≤ cantorLeft x :=
  (cantorLeft_isGreatest x).2 ⟨z.property, hz⟩

theorem cantorRight_min (x : unitInterval) (z : cantorSet) (hz : (x : ℝ) ≤ z) :
    (cantorRight x : ℝ) ≤ z :=
  (cantorRight_isLeast x).2 ⟨z.property, hz⟩

theorem cantorGap (x : unitInterval) (z : cantorSet) :
    (z : ℝ) ≤ cantorLeft x ∨ (cantorRight x : ℝ) ≤ z :=
  if h : (z : ℝ) ≤ x then Or.inl (cantorLeft_max x z h)
  else Or.inr (cantorRight_min x z (le_of_not_ge h))

theorem cantorLeft_eq (x : unitInterval) (hx : (x : ℝ) ∈ cantorSet) :
    (cantorLeft x : ℝ) = x :=
  le_antisymm (cantorLeft_le x) (cantorLeft_max x ⟨x, hx⟩ le_rfl)

theorem cantorRight_eq (x : unitInterval) (hx : (x : ℝ) ∈ cantorSet) :
    (cantorRight x : ℝ) = x :=
  le_antisymm (cantorRight_min x ⟨x, hx⟩ le_rfl) (le_cantorRight x)

noncomputable def cantorWeight (x : unitInterval) : ℝ :=
  ((x : ℝ) - cantorLeft x) / ((cantorRight x : ℝ) - cantorLeft x)

theorem cantorWeight_nonneg (x : unitInterval) : 0 ≤ cantorWeight x :=
  div_nonneg (sub_nonneg.mpr (cantorLeft_le x))
    (sub_nonneg.mpr ((cantorLeft_le x).trans (le_cantorRight x)))

theorem cantorWeight_le_one (x : unitInterval) : cantorWeight x ≤ 1 := by
  have hab := (cantorLeft_le x).trans (le_cantorRight x)
  rcases hab.eq_or_lt with h | h
  · simp [cantorWeight, h]
  · exact (div_le_one (sub_pos.mpr h)).mpr (sub_le_sub_right (le_cantorRight x) _)

theorem cantorWeight_barycenter (x : unitInterval) :
    (1 - cantorWeight x) * (cantorLeft x : ℝ) + cantorWeight x * (cantorRight x : ℝ) = x := by
  by_cases h : (cantorRight x : ℝ) - cantorLeft x = 0
  · have hab := sub_eq_zero.mp h
    have hx := le_antisymm (le_cantorRight x) (hab ▸ cantorLeft_le x)
    simp [cantorWeight, hab, hx]
  · unfold cantorWeight
    field_simp
    ring

theorem cantorEndpoints_constant_on_gap (x y : unitInterval)
    (ha : (cantorLeft x : ℝ) < y) (hb : (y : ℝ) < cantorRight x) :
    cantorLeft y = cantorLeft x ∧ cantorRight y = cantorRight x := by
  refine ⟨Subtype.ext (le_antisymm ?_ (cantorLeft_max y (cantorLeft x) ha.le)),
    Subtype.ext (le_antisymm (cantorRight_min y (cantorRight x) hb.le) ?_)⟩
  · exact (cantorGap x (cantorLeft y)).elim id fun h =>
      False.elim (not_le_of_gt hb (h.trans (cantorLeft_le y)))
  · exact (cantorGap x (cantorRight y)).elim
      (fun h => False.elim (not_le_of_gt ha ((le_cantorRight y).trans h))) id

theorem cantorWeight_distance_barycenter (x : unitInterval) (z : cantorSet) :
    (1 - cantorWeight x) * |(cantorLeft x : ℝ) - z| +
      cantorWeight x * |(cantorRight x : ℝ) - z| = |(x : ℝ) - z| := by
  rcases cantorGap x z with hz | hz
  · rw [abs_of_nonneg (sub_nonneg.mpr hz),
      abs_of_nonneg (sub_nonneg.mpr (hz.trans ((cantorLeft_le x).trans (le_cantorRight x)))),
      abs_of_nonneg (sub_nonneg.mpr (hz.trans (cantorLeft_le x)))]
    nlinarith only [cantorWeight_barycenter x]
  · rw [abs_of_nonpos (sub_nonpos.mpr (((cantorLeft_le x).trans (le_cantorRight x)).trans hz)),
      abs_of_nonpos (sub_nonpos.mpr hz),
      abs_of_nonpos (sub_nonpos.mpr ((le_cantorRight x).trans hz))]
    nlinarith only [cantorWeight_barycenter x]

/-- Affine interpolation on each complementary interval. -/
noncomputable def cantorInterp (f : C(cantorSet, ℝ)) (x : unitInterval) : ℝ :=
  (1 - cantorWeight x) * f (cantorLeft x) + cantorWeight x * f (cantorRight x)

theorem cantorInterp_of_mem (f : C(cantorSet, ℝ)) (x : unitInterval)
    (hx : (x : ℝ) ∈ cantorSet) : cantorInterp f x = f ⟨x, hx⟩ := by
  have ha : cantorLeft x = (⟨x, hx⟩ : cantorSet) := Subtype.ext (cantorLeft_eq x hx)
  have hb : cantorRight x = (⟨x, hx⟩ : cantorSet) := Subtype.ext (cantorRight_eq x hx)
  rw [cantorInterp, ha, hb]
  ring

theorem cantorInterp_local_bound (f : C(cantorSet, ℝ)) (x : unitInterval) (z : cantorSet)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hf : ∀ q : cantorSet, |(q : ℝ) - z| < δ → |f q - f z| ≤ ε) :
    |cantorInterp f x - f z| ≤ ε + (2 * ‖f‖ / δ + 1) * |(x : ℝ) - z| := by
  let C := 2 * ‖f‖ / δ + 1
  let t := cantorWeight x
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ht : 0 ≤ t := cantorWeight_nonneg x
  have ht' : 0 ≤ 1 - t := sub_nonneg.mpr (cantorWeight_le_one x)
  have hz (q : cantorSet) : |f q - f z| ≤ ε + C * |(q : ℝ) - z| := by
    by_cases hq : |(q : ℝ) - z| < δ
    · exact (hf q hq).trans (le_add_of_nonneg_right (mul_nonneg hC (abs_nonneg _)))
    · have hnorm : |f q - f z| ≤ 2 * ‖f‖ := by
        rw [← Real.norm_eq_abs, two_mul]
        exact (norm_sub_le _ _).trans (add_le_add
          (ContinuousMap.norm_coe_le_norm f q) (ContinuousMap.norm_coe_le_norm f z))
      have hscale : 2 * ‖f‖ ≤ C * δ := by
        dsimp [C]
        rw [add_mul, div_mul_cancel₀ _ hδ.ne', one_mul]
        exact le_add_of_nonneg_right hδ.le
      exact ((hnorm.trans hscale).trans (mul_le_mul_of_nonneg_left (le_of_not_gt hq) hC)).trans
        (le_add_of_nonneg_left hε)
  calc
    |cantorInterp f x - f z| =
        |(1 - t) * (f (cantorLeft x) - f z) + t * (f (cantorRight x) - f z)| := by
      unfold cantorInterp
      dsimp [t]
      congr 1
      ring
    _ ≤ (1 - t) * |f (cantorLeft x) - f z| + t * |f (cantorRight x) - f z| := by
      have h := norm_add_le ((1 - t) * (f (cantorLeft x) - f z))
        (t * (f (cantorRight x) - f z))
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht, abs_of_nonneg ht'] using h
    _ ≤ (1 - t) * (ε + C * |(cantorLeft x : ℝ) - z|) +
        t * (ε + C * |(cantorRight x : ℝ) - z|) :=
      add_le_add (mul_le_mul_of_nonneg_left (hz (cantorLeft x)) ht')
        (mul_le_mul_of_nonneg_left (hz (cantorRight x)) ht)
    _ = ε + (2 * ‖f‖ / δ + 1) * |(x : ℝ) - z| := by
      rw [← cantorWeight_distance_barycenter x z]
      dsimp [C, t]
      ring

theorem continuousAt_cantorInterp_off (f : C(cantorSet, ℝ)) (x : unitInterval)
    (hx : (x : ℝ) ∉ cantorSet) : ContinuousAt (cantorInterp f) x := by
  let a := cantorLeft x
  let b := cantorRight x
  have ha : (a : ℝ) < x :=
    lt_of_le_of_ne (cantorLeft_le x) fun h => hx (h ▸ a.property)
  have hb : (x : ℝ) < b :=
    lt_of_le_of_ne (le_cantorRight x) fun h => hx (h.symm ▸ b.property)
  let g (y : unitInterval) : ℝ :=
    (1 - ((y : ℝ) - a) / ((b : ℝ) - a)) * f a + ((y : ℝ) - a) / ((b : ℝ) - a) * f b
  have hg : ContinuousAt g x := by
    dsimp [g]
    fun_prop
  have hneigh : (Subtype.val ⁻¹' Ioo (a : ℝ) (b : ℝ) : Set unitInterval) ∈ 𝓝 x :=
    (isOpen_Ioo.preimage continuous_subtype_val).mem_nhds ⟨ha, hb⟩
  have he : cantorInterp f =ᶠ[𝓝 x] g := Filter.mem_of_superset hneigh fun y hy => by
    have hends := cantorEndpoints_constant_on_gap x y hy.1 hy.2
    simp [cantorInterp, cantorWeight, g, a, b, hends.1, hends.2]
  exact (continuousAt_congr he).mpr hg

theorem continuousAt_cantorInterp_on (f : C(cantorSet, ℝ)) (x : unitInterval)
    (hx : (x : ℝ) ∈ cantorSet) : ContinuousAt (cantorInterp f) x := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let z : cantorSet := ⟨x, hx⟩
  obtain ⟨δ, hδ, hf⟩ := Metric.continuousAt_iff.mp
    (show ContinuousAt (f : cantorSet → ℝ) z from f.continuous.continuousAt) (ε / 2) (half_pos hε)
  let C := 2 * ‖f‖ / δ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ε / (2 * C), div_pos hε (by positivity), ?_⟩
  intro y hy
  have hy' : |(y : ℝ) - x| < ε / (2 * C) := by
    change dist (y : ℝ) (x : ℝ) < _ at hy
    simpa only [Real.dist_eq] using hy
  have hf' (q : cantorSet) (hq : |(q : ℝ) - z| < δ) : |f q - f z| ≤ ε / 2 :=
    le_of_lt (by
      have hd : dist q z < δ := by
        change dist (q : ℝ) (z : ℝ) < δ
        simpa only [Real.dist_eq] using hq
      simpa only [Real.dist_eq] using hf hd)
  have ht : C * |(y : ℝ) - x| < ε / 2 :=
    (mul_lt_mul_of_pos_left hy' hC).trans_eq (by field_simp [hC.ne'])
  rw [Real.dist_eq, cantorInterp_of_mem f x hx]
  exact (cantorInterp_local_bound f y z (half_pos hε).le hδ hf').trans_lt (by
    change ε / 2 + C * |(y : ℝ) - x| < ε
    linarith)

theorem continuous_cantorInterp (f : C(cantorSet, ℝ)) : Continuous (cantorInterp f) :=
  continuous_iff_continuousAt.mpr fun x => by
    by_cases h : (x : ℝ) ∈ cantorSet
    · exact continuousAt_cantorInterp_on f x h
    · exact continuousAt_cantorInterp_off f x h

/-- Interpolation extends Cantor functions linearly and isometrically to the unit interval. -/
noncomputable def cantorExtensionIsometry : C(cantorSet, ℝ) →ₗᵢ[ℝ] BanachAmbient where
  toFun f := ⟨cantorInterp f, continuous_cantorInterp f⟩
  map_add' f g := ContinuousMap.ext fun x => by
    change cantorInterp (f + g) x = cantorInterp f x + cantorInterp g x
    simp only [cantorInterp, ContinuousMap.add_apply]
    ring
  map_smul' a f := ContinuousMap.ext fun x => by
    change cantorInterp (a • f) x = a • cantorInterp f x
    simp only [cantorInterp, ContinuousMap.smul_apply, smul_eq_mul]
    ring
  norm_map' f := by
    let g : BanachAmbient := ⟨cantorInterp f, continuous_cantorInterp f⟩
    change ‖g‖ = ‖f‖
    apply le_antisymm
    · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      let t := cantorWeight x
      have ht : 0 ≤ t := cantorWeight_nonneg x
      have ht' : 0 ≤ 1 - t := sub_nonneg.mpr (cantorWeight_le_one x)
      change ‖(1 - t) * f (cantorLeft x) + t * f (cantorRight x)‖ ≤ ‖f‖
      calc
        _ ≤ ‖(1 - t) * f (cantorLeft x)‖ + ‖t * f (cantorRight x)‖ := norm_add_le _ _
        _ = (1 - t) * ‖f (cantorLeft x)‖ + t * ‖f (cantorRight x)‖ := by
          rw [norm_mul, norm_mul, Real.norm_of_nonneg ht, Real.norm_of_nonneg ht']
        _ ≤ (1 - t) * ‖f‖ + t * ‖f‖ := add_le_add
          (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f _) ht')
          (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f _) ht)
        _ = ‖f‖ := by ring
    · apply (ContinuousMap.norm_le _ (norm_nonneg g)).mpr
      intro z
      let x : unitInterval := ⟨z, cantorSet_subset_unitInterval z.property⟩
      have he : g x = f z := cantorInterp_of_mem f x z.property
      rw [← he]
      exact ContinuousMap.norm_coe_le_norm g x

end PaperFormalization
