import PaperFormalization.BanachProperties

namespace PaperFormalization

open Filter Set Topology
open scoped BigOperators ENNReal Classical

/-- Weak convergence to zero, tested by continuous linear functionals. -/
def WeaklyNull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : ℕ → E) : Prop :=
  ∀ f : StrongDual ℝ E, Tendsto (fun n => f (x n)) atTop (𝓝 0)

/-- The Schur property, in the equivalent weakly null sequence formulation. -/
def HasSchurProperty (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ x : ℕ → E, WeaklyNull x → Tendsto x atTop (𝓝 0)

theorem WeaklyNull.map {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {x : ℕ → E} (hx : WeaklyNull x)
    (T : E →L[ℝ] F) : WeaklyNull (T ∘ x) :=
  fun f => hx (f.comp T)

theorem HasSchurProperty.iff_weaklyConvergent {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] :
    HasSchurProperty E ↔ ∀ (x : ℕ → E) (y : E),
      (∀ f : StrongDual ℝ E, Tendsto (fun n => f (x n)) atTop (𝓝 (f y))) →
      Tendsto x atTop (𝓝 y) := by
  constructor
  · intro h x y hf
    have hn : WeaklyNull (fun n => x n - y) := fun f => by
      simpa only [map_sub, sub_self] using (hf f).sub (tendsto_const_nhds (x := f y))
    have ht := (h _ hn).add (tendsto_const_nhds (x := y))
    simpa only [sub_add_cancel, zero_add] using ht
  · intro h x hx
    exact h x 0 (fun f => by simpa only [map_zero] using hx f)

theorem HasSchurProperty.of_complementablyEmbeds {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hF : HasSchurProperty F) (hEF : ComplementablyEmbeds E F) : HasSchurProperty E := by
  obtain ⟨i, r, hir⟩ := hEF
  intro x hx
  have h := r.continuous.continuousAt.tendsto.comp (hF _ (hx.map i))
  change Tendsto (fun n => r (i (x n))) atTop (𝓝 (r 0)) at h
  have he : (fun n => r (i (x n))) = x := funext fun n => hir (x n)
  rwa [he, map_zero] at h

section L1Sum

variable {ι : Type*} (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]

private noncomputable def truncate (s : Finset ι) (x : lp E 1) : lp E 1 :=
  ∑ i ∈ s, lp.single 1 i (x i)

private theorem norm_truncate (s : Finset ι) (x : lp E 1) :
    ‖truncate E s x‖ = ∑ i ∈ s, ‖x i‖ := by
  simpa only [truncate, ENNReal.toReal_one, Real.rpow_one] using
    lp.norm_sum_single (p := 1) (by simp) (fun i => x i) s

private theorem eventually_norm_tail_lt (x : lp E 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s : Finset ι in atTop, ‖x - truncate E s x‖ < ε := by
  have h := (Metric.tendsto_nhds.mp (lp.hasSum_single (p := 1) (by simp) x)) ε hε
  change ∀ᶠ s : Finset ι in atTop, dist (truncate E s x) x < ε at h
  simpa only [dist_eq_norm, norm_sub_rev] using h

private theorem schur_bad_sequence_blocks (x : ℕ → lp E 1)
    (hcoord : ∀ i, Tendsto (fun n => x n i) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε)
    (hlarge : ∀ n, ∃ m ≥ n, ε ≤ ‖x m‖) :
    ∃ (p : ℕ → ℕ) (s : ℕ → Finset ι), StrictMono p ∧ Monotone s ∧
      ∀ k, ε ≤ ‖x (p k)‖ ∧ ‖truncate E (s k) (x (p k))‖ < ε / 8 ∧
        ‖x (p k) - truncate E (s (k + 1)) (x (p k))‖ < ε / 8 := by
  have hsmall (s : Finset ι) :
      Tendsto (fun n => ‖truncate E s (x n)‖) atTop (𝓝 0) := by
    simp_rw [norm_truncate]
    have ht (i : ι) : Tendsto (fun n => ‖x n i‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using (hcoord i).norm
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum s (fun i _ => ht i)
  have hstep (k : ℕ) (s : Finset ι) : ∃ (m : ℕ) (t : Finset ι),
      k < m ∧ s ⊆ t ∧ ε ≤ ‖x m‖ ∧ ‖truncate E s (x m)‖ < ε / 8 ∧
        ‖x m - truncate E t (x m)‖ < ε / 8 := by
    have hnb : Iio (ε / 8) ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds (show (0 : ℝ) < ε / 8 by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((hsmall s).eventually hnb)
    obtain ⟨m, hm, hmx⟩ := hlarge (max (k + 1) N)
    obtain ⟨T, hT⟩ := eventually_atTop.mp
      (eventually_norm_tail_lt E (x m) (show 0 < ε / 8 by positivity))
    exact ⟨m, T ∪ s, (Nat.lt_succ_self k).trans_le ((le_max_left _ _).trans hm),
      Finset.subset_union_right, hmx, hN _ ((le_max_right _ _).trans hm),
      hT _ Finset.subset_union_left⟩
  choose nextN nextS hnext using hstep
  let z : ℕ → ℕ × Finset ι := Nat.rec (0, ∅)
    (fun _ w => (nextN w.1 w.2, nextS w.1 w.2))
  have hsucc (k : ℕ) := hnext (z k).1 (z k).2
  exact ⟨fun k => (z (k + 1)).1, fun k => (z k).2,
    strictMono_nat_of_lt_succ fun k => (hsucc (k + 1)).1,
    monotone_nat_of_le_succ fun k => (hsucc k).2.1, fun k => (hsucc k).2.2⟩

variable [∀ i, NormedSpace ℝ (E i)]

private theorem exists_norming_block_family (x : ℕ → lp E 1) (p : ℕ → ℕ)
    (s : ℕ → Finset ι) (hs : Monotone s) :
    ∃ f : ∀ i, StrongDual ℝ (E i), (∀ i, ‖f i‖ ≤ 1) ∧
      ∀ k i, i ∈ s (k + 1) \ s k → f i (x (p k) i) = ‖x (p k) i‖ := by
  have hunique (i : ι) {k l : ℕ} (hk : i ∈ s (k + 1) \ s k)
      (hl : i ∈ s (l + 1) \ s l) : k = l := by
    have hlt {j m : ℕ} (h : j < m) (hj : i ∈ s (j + 1) \ s j)
        (hm : i ∈ s (m + 1) \ s m) : False :=
      (Finset.mem_sdiff.mp hm).2 (hs h (Finset.mem_sdiff.mp hj).1)
    exact le_antisymm (le_of_not_gt (fun h => hlt h hl hk))
      (le_of_not_gt (fun h => hlt h hk hl))
  have h (i : ι) : ∃ f : StrongDual ℝ (E i), ‖f‖ ≤ 1 ∧
      ∀ k, i ∈ s (k + 1) \ s k → f (x (p k) i) = ‖x (p k) i‖ := by
    by_cases hi : ∃ k, i ∈ s (k + 1) \ s k
    · obtain ⟨k, hk⟩ := hi
      obtain ⟨f, hf, he⟩ := exists_dual_vector'' ℝ (x (p k) i)
      exact ⟨f, hf, fun l hl => hunique i hk hl ▸ he⟩
    · exact ⟨0, by simp, fun k hk => False.elim (hi ⟨k, hk⟩)⟩
  choose f hf he using h
  exact ⟨f, hf, fun k i => he i k⟩

/-- Arbitrary ℓ₁ sums of Schur spaces have the Schur property. -/
theorem HasSchurProperty.lp_one (hE : ∀ i, HasSchurProperty (E i)) : HasSchurProperty (lp E 1) := by
  intro x hx
  by_contra hnull
  have hcoord (i : ι) : Tendsto (fun n => x n i) atTop (𝓝 0) :=
    hE i _ (hx.map (lp.evalCLM ℝ E 1 i))
  rw [Metric.tendsto_atTop] at hnull
  push Not at hnull
  obtain ⟨ε, hε, hlarge⟩ := hnull
  have hlarge' : ∀ n, ∃ m ≥ n, ε ≤ ‖x m‖ := by
    simpa only [dist_zero_right] using hlarge
  obtain ⟨p, s, hp, hs, hmass⟩ := schur_bad_sequence_blocks E x hcoord hε hlarge'
  obtain ⟨f, hf, hnorming⟩ := exists_norming_block_family E x p s hs
  let A := lp.mapCLM 1 f zero_le_one hf
  let F : StrongDual ℝ (lp E 1) := (lp.tsumCLM ℝ ι ℝ).comp A
  have hF (z : lp E 1) : ‖F z‖ ≤ ‖z‖ := by
    change ‖∑' i, A z i‖ ≤ ‖z‖
    refine (lp.norm_tsum_le _).trans ((A.le_opNorm z).trans ?_)
    simpa using mul_le_mul_of_nonneg_right (lp.norm_mapCLM_le 1 f zero_le_one hf) (norm_nonneg z)
  have hsingle (i : ι) (y : E i) : F (lp.single 1 i y) = f i y := by
    change (∑' j, f j ((lp.single 1 i y) j)) = f i y
    exact (tsum_eq_single i (fun j hj => by rw [lp.single_apply_ne _ _ _ hj, map_zero])).trans
      (by rw [lp.single_apply_self])
  have hbound (k : ℕ) : ε / 2 ≤ F (x (p k)) := by
    let z := x (p k)
    let t := s (k + 1) \ s k
    let u := truncate E (s k) z
    let v := truncate E t z
    let w := z - truncate E (s (k + 1)) z
    have hsum : v + u = truncate E (s (k + 1)) z :=
      Finset.sum_sdiff (hs (Nat.le_succ k))
    have hz : z = u + v + w := by
      rw [add_comm u v, hsum]
      dsimp [w]
      abel
    have hv : F v = ‖v‖ := by
      rw [norm_truncate]
      simp only [v, truncate, map_sum, hsingle]
      exact Finset.sum_congr rfl (fun i hi => hnorming k i hi)
    have hnorm : ‖z‖ ≤ ‖u‖ + ‖v‖ + ‖w‖ := by
      calc
        _ = ‖u + v + w‖ := congrArg norm hz
        _ ≤ ‖u + v‖ + ‖w‖ := norm_add_le _ _
        _ ≤ ‖u‖ + ‖v‖ + ‖w‖ := add_le_add (norm_add_le _ _) le_rfl
    have hFz : F z = F u + ‖v‖ + F w := by
      nth_rw 1 [hz]
      rw [map_add, map_add, hv]
    have hu : -‖u‖ ≤ F u := (neg_le_neg (hF u)).trans (neg_abs_le _)
    have hw : -‖w‖ ≤ F w := (neg_le_neg (hF w)).trans (neg_abs_le _)
    have h := hmass k
    change ε ≤ ‖z‖ ∧ ‖u‖ < ε / 8 ∧ ‖w‖ < ε / 8 at h
    change ε / 2 ≤ F z
    linarith [h.1, h.2.1, h.2.2]
  have ht := (hx F).comp hp.tendsto_atTop
  obtain ⟨k, hk⟩ := (Metric.tendsto_nhds.mp ht (ε / 2) (by positivity)).exists
  have he : ‖F (x (p k))‖ < ε / 2 := by simpa only [Function.comp_apply, dist_zero_right] using hk
  exact ((hbound k).trans (le_abs_self _)).not_gt he

end L1Sum

/-- The Schur property belongs to the manuscript's complemented-hereditary class. -/
theorem schurProperty_isL1StableComplemented :
    IsL1StableComplementedProperty (fun E => HasSchurProperty E) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun h hF => hF.of_complementablyEmbeds h⟩
  · intro X Y e hX
    exact hX.of_complementablyEmbeds
      ⟨e.symm.toContinuousLinearMap, e.toContinuousLinearMap, e.apply_symm_apply⟩
  · intro x _
    exact tendsto_const_nhds.congr (fun _ => Subsingleton.elim _ _)
  · intro x hx
    exact hx (ContinuousLinearMap.id ℝ ℝ)
  · intro ι F hF
    exact @HasSchurProperty.lp_one ι (fun i => RealBanachSpace.instCoeSort.coe (F i))
      (fun i => (F i).normedAddCommGroup) (fun i => (F i).normedSpace) hF

end PaperFormalization
