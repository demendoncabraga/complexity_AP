import PaperFormalization.Basic

namespace PaperFormalization.NatTree

/-- The subtree obtained by removing an initial node (m). -/
def successor (T : NatTree) (m : ℕ) : NatTree :=
  ⟨{s | m :: s ∈ T.val}, fun s t hst ht =>
    T.property (m :: s) (m :: t) (List.cons_prefix_cons.mpr ⟨rfl, hst⟩) ht⟩

/-- The successor subtrees indexed by actual children of the root. -/
def IsChild (S T : NatTree) : Prop :=
  ∃ m : ℕ, [m] ∈ T.val ∧ S = T.successor m

/-- A tree with no infinite branch is accessible under the successor relation. -/
theorem acc_isChild {T : NatTree} (hT : T.IsWellFounded) : Acc IsChild T := by
  apply acc_iff_isEmpty_descending_chain.mpr
  refine ⟨fun ⟨f, hf, hchain⟩ => ?_⟩
  choose m hnode hnext using hchain
  have hprefix (n k : ℕ) : List.ofFn (fun i : Fin n => m (k + i)) ∈ (f k).val := by
    induction n generalizing k with
    | zero => exact (f k).property [] [m k] List.nil_prefix (hnode k)
    | succ n ih =>
      have hstep := ih (k + 1)
      rw [hnext k] at hstep
      change m k :: List.ofFn (fun i : Fin n => m (k + 1 + i)) ∈ (f k).val at hstep
      rw [List.ofFn_succ]
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep
  exact (Set.not_nonempty_iff_eq_empty.mpr hT)
    ⟨m, fun n => by simpa only [Nat.zero_add, hf] using hprefix n 0⟩

/-- Induction from immediate successor subtrees on a branchless tree. -/
theorem induction_on_successors {Q : NatTree → Prop} {T : NatTree} (hT : T.IsWellFounded)
    (step : ∀ S, (∀ m, [m] ∈ S.val → Q (S.successor m)) → Q S) : Q T :=
  Acc.recOn (motive := fun S _ => Q S) (acc_isChild hT) fun S _ ih =>
    step S fun m hm => ih _ ⟨m, hm, rfl⟩

end PaperFormalization.NatTree
