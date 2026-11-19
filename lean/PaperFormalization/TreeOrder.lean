import PaperFormalization.TreeInduction

namespace PaperFormalization.NatTree

open Order Set
open scoped Ordinal Classical

/-- Remove the terminal nodes of a tree. -/
def derivative (T : NatTree) : NatTree :=
  ⟨{s | ∃ m : ℕ, s ++ [m] ∈ T.val}, by
    intro s t hst ht
    obtain ⟨m, hm⟩ := ht
    obtain ⟨u, rfl⟩ := hst
    cases u with
    | nil => exact ⟨m, by simpa only [List.append_nil] using hm⟩
    | cons i u =>
      exact ⟨i, T.property _ _ ⟨u ++ [m], by simp [List.append_assoc]⟩ hm⟩⟩

theorem derivative_subset (T : NatTree) : T.derivative.val ⊆ T.val :=
  fun s ⟨m, hm⟩ => T.property s _ ⟨[m], rfl⟩ hm

private def intersectStages (α : Ordinal.{0}) (prev : ∀ β < α, NatTree) : NatTree :=
  ⟨{s | ∀ β (h : β < α), s ∈ (prev β h).val},
    fun a b hab hb β hβ => (prev β hβ).property a b hab (hb β hβ)⟩

/-- Iterated pruning at every ordinal, with intersections at limit stages. -/
noncomputable def prune (T : NatTree) (α : Ordinal.{0}) : NatTree :=
  @Ordinal.limitRecOn (fun _ => NatTree) α T (fun _ S => S.derivative)
    (fun α _ prev => intersectStages α prev)

theorem prune_zero (T : NatTree) : T.prune 0 = T :=
  @Ordinal.limitRecOn_zero (fun _ : Ordinal.{0} => NatTree) _ _ _

theorem prune_add_one (T : NatTree) (α : Ordinal.{0}) :
    T.prune (α + 1) = (T.prune α).derivative :=
  @Ordinal.limitRecOn_add_one (fun _ : Ordinal.{0} => NatTree) α _ _ _

theorem mem_prune_limit (T : NatTree) {α : Ordinal.{0}} (hα : IsSuccLimit α) (s : List ℕ) :
    s ∈ (T.prune α).val ↔ ∀ β < α, s ∈ (T.prune β).val := by
  have he : T.prune α = intersectStages α (fun β _ => T.prune β) :=
    @Ordinal.limitRecOn_limit (fun _ : Ordinal.{0} => NatTree) α _ _ _ hα
  exact congrArg (fun S : NatTree => s ∈ S.val) he |>.to_iff

theorem prune_subset (T : NatTree) (α : Ordinal) : (T.prune α).val ⊆ T.val := by
  induction α using Ordinal.limitRecOn with
  | zero => simp [prune_zero]
  | add_one α ih => rw [prune_add_one]; exact (derivative_subset _).trans ih
  | limit α hα _ =>
    intro s hs
    simpa only [prune_zero] using (mem_prune_limit T hα s).mp hs 0 hα.bot_lt

private theorem derivative_successor (T : NatTree) (m : ℕ) :
    (T.successor m).derivative = T.derivative.successor m := by
  apply Subtype.ext
  rfl

theorem prune_successor (T : NatTree) (m : ℕ) (α : Ordinal) :
    (T.successor m).prune α = (T.prune α).successor m := by
  induction α using Ordinal.limitRecOn with
  | zero => simp [prune_zero]
  | add_one α ih => rw [prune_add_one, prune_add_one, ih, derivative_successor]
  | limit α hα ih =>
    apply Subtype.ext
    ext s
    rw [mem_prune_limit _ hα]
    change (∀ β < α, s ∈ ((T.successor m).prune β).val) ↔ m :: s ∈ (T.prune α).val
    rw [mem_prune_limit _ hα]
    constructor <;> intro h β hβ
    · have hh := h β hβ
      rw [ih β hβ] at hh
      exact hh
    · rw [ih β hβ]
      exact h β hβ

private theorem root_mem_prune_iff_rank (α : Ordinal) :
    ∀ (T : NatTree) (hT : Acc IsChild T),
      [] ∈ (T.prune α).val ↔ [] ∈ T.val ∧ α ≤ hT.rank := by
  induction α using Ordinal.limitRecOn with
  | zero => intro T hT; simp [prune_zero]
  | add_one α ih =>
    intro T hT
    rw [prune_add_one]
    change (∃ m, [m] ∈ (T.prune α).val) ↔ [] ∈ T.val ∧ α + 1 ≤ hT.rank
    have he : α + 1 ≤ hT.rank ↔ ∃ S : {S // IsChild S T}, α ≤ (hT.inv S.property).rank := by
      rw [← succ_eq_add_one, succ_le_iff, hT.rank_eq, Ordinal.lt_iSup_iff]
      exact exists_congr fun S => lt_succ_iff
    rw [he]
    constructor
    · rintro ⟨m, hm⟩
      have hmT : [m] ∈ T.val := prune_subset T α hm
      let S : {S // IsChild S T} := ⟨T.successor m, ⟨m, hmT, rfl⟩⟩
      have hsm : [] ∈ (S.val.prune α).val := by
        change [] ∈ ((T.successor m).prune α).val
        rw [prune_successor]
        exact hm
      exact ⟨T.property _ _ List.nil_prefix hmT, S, ((ih _ _).mp hsm).2⟩
    · rintro ⟨_, ⟨S, m, hm, rfl⟩, ha⟩
      refine ⟨m, ?_⟩
      have hsm := (ih (T.successor m) (hT.inv ⟨m, hm, rfl⟩)).mpr ⟨hm, ha⟩
      rw [prune_successor] at hsm
      exact hsm
  | limit α hα ih =>
    intro T hT
    rw [mem_prune_limit T hα]
    constructor
    · intro h
      have hh (β : Ordinal) (hβ : β < α) := (ih β hβ T hT).mp (h β hβ)
      refine ⟨(hh 0 hα.bot_lt).1, ?_⟩
      by_contra! hn
      have hlt := hα.succ_lt hn
      exact (not_lt_of_ge (hh _ hlt).2) (lt_succ _)
    · exact fun ⟨hr, ha⟩ β hβ => (ih β hβ T hT).mpr ⟨hr, hβ.le.trans ha⟩

private theorem accRank_lt_omega_one {T : NatTree} (hT : Acc IsChild T) :
    hT.rank < ω₁ := by
  induction hT with
  | intro T next ih =>
    let f (m : {m : ℕ // [m] ∈ T.val}) : {S // IsChild S T} :=
      ⟨T.successor m.val, ⟨m.val, m.property, rfl⟩⟩
    have hf : Function.Surjective f := by
      rintro ⟨S, m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
    have : Countable {S // IsChild S T} := hf.countable
    rw [Acc.rank_eq]
    exact Ordinal.iSup_lt_omega_one fun S => (Cardinal.isSuccLimit_omega 1).succ_lt (ih _ S.property)

/-- The order of a well-founded tree is the least pruning stage with no nodes. -/
noncomputable def order (T : NatTree) (hT : T.IsWellFounded) : Ordinal :=
  if [] ∈ T.val then Order.succ (acc_isChild hT).rank else 0

theorem order_lt_omega_one (T : NatTree) (hT : T.IsWellFounded) :
    T.order hT < ω₁ := by
  classical
  unfold order
  split
  · exact (Cardinal.isSuccLimit_omega 1).succ_lt (accRank_lt_omega_one (acc_isChild hT))
  · exact (Cardinal.isSuccLimit_omega 1).bot_lt

theorem prune_empty_iff_order_le (T : NatTree) (hT : T.IsWellFounded) (α : Ordinal) :
    (T.prune α).val = ∅ ↔ T.order hT ≤ α := by
  classical
  have he : (T.prune α).val = ∅ ↔ [] ∉ (T.prune α).val := by
    constructor
    · intro h
      simp [h]
    · exact fun h => not_nonempty_iff_eq_empty.mp fun ⟨s, hs⟩ =>
        h ((T.prune α).property [] s List.nil_prefix hs)
  rw [he, not_congr (root_mem_prune_iff_rank α T (acc_isChild hT)), order]
  by_cases hr : [] ∈ T.val
  · simp [hr]
  · simp [hr]

theorem isWellFounded_successor {T : NatTree} (hT : T.IsWellFounded) (m : ℕ) :
    (T.successor m).IsWellFounded := by
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨b, hb⟩
  let c : ℕ → ℕ := fun n => Nat.casesOn n m b
  apply not_nonempty_iff_eq_empty.mpr hT
  refine ⟨c, fun n => ?_⟩
  have hm : [m] ∈ T.val := hb 0
  cases n with
  | zero => exact T.property [] [m] List.nil_prefix hm
  | succ n =>
    change List.ofFn (fun i : Fin (n + 1) => c i) ∈ T.val
    have hn : m :: List.ofFn (fun i : Fin n => b i) ∈ T.val := hb n
    rw [List.ofFn_succ]
    exact hn

/-- Removing the initial node strictly decreases the order of an actual successor subtree. -/
theorem order_successor_lt (T : NatTree) (hT : T.IsWellFounded) (m : ℕ)
    (hm : [m] ∈ T.val) :
    (T.successor m).order (isWellFounded_successor hT m) < T.order hT := by
  classical
  have hr : [] ∈ T.val := T.property _ _ List.nil_prefix hm
  have hSr : [] ∈ (T.successor m).val := hm
  simp only [order, if_pos hr, if_pos hSr, succ_lt_succ_iff]
  exact (acc_isChild hT).rank_lt_of_rel (show IsChild (T.successor m) T from ⟨m, hm, rfl⟩)

end PaperFormalization.NatTree
