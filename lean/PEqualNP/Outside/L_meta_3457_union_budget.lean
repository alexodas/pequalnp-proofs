import Mathlib

/-!
A combinatorial counting tool for the OR shadow. Each nontrivial
support can be expanded into two earlier supports, and the same
node is charged only once, even when its support is shared.
-/

namespace PEqualNP.Outside.L_meta_3457_union_budget

variable {α : Type*} [DecidableEq α]

noncomputable def budget (Q : ℕ → Prop) (m : ℕ) : ℕ := by
  classical
  exact ((Finset.range m).filter Q).card

theorem budget_succ (Q : ℕ → Prop) [DecidablePred Q] (m : ℕ) :
    budget Q (m+1) = budget Q m + (if Q m then 1 else 0) := by
  classical
  unfold budget
  rw [Finset.range_succ]
  by_cases h : Q m <;> simp [h]

theorem budget_mono_succ (Q : ℕ → Prop) (m : ℕ) :
    budget Q m ≤ budget Q (m+1) := by
  classical
  rw [budget_succ]
  omega

/-- An OR-DAG support union uses at most one leaf per root plus
    one extra leaf per charged branching node. Nontrivial support
    nodes have two earlier operands; singleton and empty nodes
    need not be expanded. -/
theorem union_card_le_budget (S : ℕ → Finset α) (Q : ℕ → Prop)
    (hsplit : ∀ j, 1 < (S j).card →
      Q j ∧ ∃ a b, a < j ∧ b < j ∧ S j = S a ∪ S b) :
    ∀ (m : ℕ) (R : Finset ℕ), R ⊆ Finset.range m →
      (R.biUnion S).card ≤ R.card + budget Q m := by
  classical
  intro m
  induction m with
  | zero =>
    intro R hR
    have he : R = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => by
      have h := hR hx
      simp at h)
    subst R
    simp [budget]
  | succ m ih =>
    intro R hR
    let R0 := R.erase m
    have hR0 : R0 ⊆ Finset.range m := by
      intro j hj
      have h := Finset.mem_erase.mp hj
      have hlt := Finset.mem_range.mp (hR h.2)
      exact Finset.mem_range.mpr (by omega)
    by_cases hm : m ∈ R
    · have he : insert m R0 = R := Finset.insert_erase hm
      have hcard : R0.card + 1 = R.card := Finset.card_erase_add_one hm
      have hU : R.biUnion S = S m ∪ R0.biUnion S := by
        rw [← he, Finset.biUnion_insert]
      by_cases hsmall : (S m).card ≤ 1
      · have h := ih R0 hR0
        have hb := budget_mono_succ Q m
        rw [hU]
        have hu := Finset.card_union_le (S m) (R0.biUnion S)
        omega
      · obtain ⟨hq,a,b,ha,hb,hs⟩ := hsplit m (by omega)
        let R1 := insert a (insert b R0)
        have hR1 : R1 ⊆ Finset.range m := by
          intro j hj
          have hj' : j = a ∨ j = b ∨ j ∈ R0 := by simpa [R1] using hj
          rcases hj' with h | h | h
          · subst j
            exact Finset.mem_range.mpr ha
          · subst j
            exact Finset.mem_range.mpr hb
          · exact hR0 h
        have h1 : R1.card ≤ R0.card + 2 := by
          have hA := Finset.card_insert_le a (insert b R0)
          have hB := Finset.card_insert_le b R0
          change (insert a (insert b R0)).card ≤ R0.card + 2
          omega
        have heq : R1.biUnion S = R.biUnion S := by
          rw [hU, hs]
          simp only [R1, Finset.biUnion_insert, Finset.union_assoc]
        have h := ih R1 hR1
        rw [heq] at h
        have hbud : budget Q (m+1) = budget Q m + 1 := by
          rw [budget_succ]
          simp [hq]
        omega
    · have he : R0 = R := Finset.erase_eq_of_notMem hm
      rw [he] at hR0
      have h := ih R hR0
      have hb := budget_mono_succ Q m
      omega

/-- A support family restricted to a given neighbourhood still
    satisfies the same split invariant: every child of a permitted
    union is also permitted. -/
noncomputable def restrictSupport (S : ℕ → Finset α) (V : Finset α)
    (j : ℕ) : Finset α := by
  classical
  exact if S j ⊆ V then S j else ∅

theorem restricted_union_bound (S : ℕ → Finset α)
    (hsplit : ∀ j, 1 < (S j).card →
      ∃ a b, a < j ∧ b < j ∧ S j = S a ∪ S b)
    (V : Finset α) (m : ℕ) (R : Finset ℕ)
    (hR : R ⊆ Finset.range m) (hsub : ∀ j ∈ R, S j ⊆ V) :
    (R.biUnion S).card ≤ R.card +
      budget (fun j => 1 < (S j).card ∧ S j ⊆ V) m := by
  classical
  let S' := restrictSupport S V
  have hsplit' : ∀ j, 1 < (S' j).card →
      (1 < (S j).card ∧ S j ⊆ V) ∧
        ∃ a b, a < j ∧ b < j ∧ S' j = S' a ∪ S' b := by
    intro j hj
    have hjsub : S j ⊆ V := by
      by_contra hn
      simp [S', restrictSupport, hn] at hj
    have he : S' j = S j := by simp [S', restrictSupport, hjsub]
    rw [he] at hj
    obtain ⟨a,b,ha,hb,h⟩ := hsplit j hj
    have hab : S a ∪ S b ⊆ V := h ▸ hjsub
    have ha' : S a ⊆ V := fun x hx => hab (Finset.mem_union.mpr (Or.inl hx))
    have hb' : S b ⊆ V := fun x hx => hab (Finset.mem_union.mpr (Or.inr hx))
    refine ⟨⟨hj,hjsub⟩,a,b,ha,hb,?_⟩
    simp only [S', restrictSupport, hjsub, ha', hb', if_true]
    exact h
  have heq : R.biUnion S' = R.biUnion S := by
    ext x
    simp only [Finset.mem_biUnion]
    constructor <;> rintro ⟨j,hj,hx⟩
    · exact ⟨j,hj,by simpa [S', restrictSupport, hsub j hj] using hx⟩
    · exact ⟨j,hj,by simpa [S', restrictSupport, hsub j hj] using hx⟩
  have h := union_card_le_budget S' _ hsplit' m R hR
  rw [heq] at h
  exact h

end PEqualNP.Outside.L_meta_3457_union_budget
