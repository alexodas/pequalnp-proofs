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
  by_cases h : Q m
  · have he : (Finset.range (m+1)).filter Q = insert m ((Finset.range m).filter Q) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      constructor
      · rintro ⟨hi,hq⟩
        by_cases e : i = m
        · exact Or.inl e
        · exact Or.inr ⟨by omega,hq⟩
      · rintro (rfl | ⟨hi,hq⟩)
        · exact ⟨by omega,h⟩
        · exact ⟨by omega,hq⟩
    rw [he, Finset.card_insert_of_notMem (by simp), if_pos h]
  · have he : (Finset.range (m+1)).filter Q = (Finset.range m).filter Q := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hi,hq⟩
        have hn : i ≠ m := fun e => h (e ▸ hq)
        exact ⟨by omega,hq⟩
      · rintro ⟨hi,hq⟩
        exact ⟨by omega,hq⟩
    rw [he, if_neg h, Nat.add_zero]

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


/-- If each node is chargeable to at most one centre, the sum of
    the centre-specific budgets is at most the number of nodes. -/
theorem unique_budget_sum {β : Type*} [Fintype β] (Q : β → ℕ → Prop)
    (huniq : ∀ j c d, Q c j → Q d j → c = d) (m : ℕ) :
    (∑ c : β, budget (Q c) m) ≤ m := by
  classical
  induction m with
  | zero => simp [budget]
  | succ m ih =>
    simp_rw [budget_succ]
    rw [Finset.sum_add_distrib]
    have hstep : (∑ c : β, if Q c m then 1 else 0) ≤ 1 := by
      by_cases he : ∃ c, Q c m
      · obtain ⟨c,hc⟩ := he
        calc
          (∑ d : β, if Q d m then 1 else 0) ≤
              ∑ d : β, if d = c then 1 else 0 := by
            apply Finset.sum_le_sum
            intro d hd
            by_cases h : Q d m
            · have hh := huniq m d c h hc
              simp [hc,hh]
            · simp [h]
          _ = 1 := by simp
      · have hn : ∀ c, ¬ Q c m := fun c h => he ⟨c,h⟩
        simp [hn]
    omega

/-- If two different neighbourhoods intersect in at most one
    vertex, no nontrivial OR support can be charged to both.
    Thus sharing of OR nodes does not invalidate the root/leaf
    bound when summed over all centres. -/
theorem neighbourhood_union_sum {β : Type*} [Fintype β]
    (S : ℕ → Finset α) (V : β → Finset α) (R : β → Finset ℕ)
    (hsplit : ∀ j, 1 < (S j).card →
      ∃ a b, a < j ∧ b < j ∧ S j = S a ∪ S b)
    (hinter : ∀ c d, c ≠ d → (V c ∩ V d).card ≤ 1)
    (m : ℕ) (hR : ∀ c, R c ⊆ Finset.range m)
    (hsub : ∀ c j, j ∈ R c → S j ⊆ V c) :
    (∑ c : β, ((R c).biUnion S).card) ≤
      (∑ c : β, (R c).card) + m := by
  classical
  let Q := fun c : β => fun j : ℕ => 1 < (S j).card ∧ S j ⊆ V c
  have hu : ∀ j c d, Q c j → Q d j → c = d := by
    intro j c d hc hd
    by_contra hn
    have hle : (S j).card ≤ (V c ∩ V d).card :=
      Finset.card_le_card (fun x hx => Finset.mem_inter.mpr ⟨hc.2 hx,hd.2 hx⟩)
    have hb := hinter c d hn
    have hlarge := hc.1
    omega
  calc
    (∑ c : β, ((R c).biUnion S).card) ≤
        ∑ c : β, ((R c).card + budget (Q c) m) := by
      apply Finset.sum_le_sum
      intro c hc
      exact restricted_union_bound S hsplit (V c) m (R c) (hR c) (hsub c)
    _ = (∑ c : β, (R c).card) + ∑ c : β, budget (Q c) m := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ c : β, (R c).card) + m :=
      Nat.add_le_add_left (unique_budget_sum Q hu m) _


/-- Charge only nodes in an allowed class, rather than all wire indices. -/
theorem unique_budget_sum_le {β : Type*} [Fintype β]
    (Q : β → ℕ → Prop) (Allowed : ℕ → Prop)
    (huniq : ∀ j c d, Q c j → Q d j → c = d)
    (hallowed : ∀ j c, Q c j → Allowed j) (m : ℕ) :
    (∑ c : β, budget (Q c) m) ≤ budget Allowed m := by
  classical
  induction m with
  | zero => simp [budget]
  | succ m ih =>
    simp_rw [budget_succ]
    rw [Finset.sum_add_distrib]
    have hstep : (∑ c : β, if Q c m then 1 else 0) ≤
        (if Allowed m then 1 else 0) := by
      by_cases he : ∃ c, Q c m
      · obtain ⟨c,hc⟩ := he
        rw [if_pos (hallowed m c hc)]
        calc
          (∑ d : β, if Q d m then 1 else 0) ≤
              ∑ d : β, if d = c then 1 else 0 := by
            apply Finset.sum_le_sum
            intro d hd
            by_cases h : Q d m
            · have hh := huniq m d c h hc
              simp [hc,hh]
            · simp [h]
          _ = 1 := by simp
      · have hn : ∀ c, ¬ Q c m := fun c h => he ⟨c,h⟩
        simp [hn]
    omega

theorem neighbourhood_union_budget {β : Type*} [Fintype β]
    (S : ℕ → Finset α) (V : β → Finset α) (R : β → Finset ℕ)
    (Allowed : ℕ → Prop)
    (hsplit : ∀ j, 1 < (S j).card →
      ∃ a b, a < j ∧ b < j ∧ S j = S a ∪ S b)
    (hallowed : ∀ j, 1 < (S j).card → Allowed j)
    (hinter : ∀ c d, c ≠ d → (V c ∩ V d).card ≤ 1)
    (m : ℕ) (hR : ∀ c, R c ⊆ Finset.range m)
    (hsub : ∀ c j, j ∈ R c → S j ⊆ V c) :
    (∑ c : β, ((R c).biUnion S).card) ≤
      (∑ c : β, (R c).card) + budget Allowed m := by
  classical
  let Q := fun c : β => fun j : ℕ => 1 < (S j).card ∧ S j ⊆ V c
  have hu : ∀ j c d, Q c j → Q d j → c = d := by
    intro j c d hc hd
    by_contra hn
    have hle : (S j).card ≤ (V c ∩ V d).card :=
      Finset.card_le_card (fun x hx => Finset.mem_inter.mpr ⟨hc.2 hx,hd.2 hx⟩)
    have hb := hinter c d hn
    have hlarge := hc.1
    omega
  calc
    (∑ c : β, ((R c).biUnion S).card) ≤
        ∑ c : β, ((R c).card + budget (Q c) m) := by
      apply Finset.sum_le_sum
      intro c hc
      exact restricted_union_bound S hsplit (V c) m (R c) (hR c) (hsub c)
    _ = (∑ c : β, (R c).card) + ∑ c : β, budget (Q c) m := by
      rw [Finset.sum_add_distrib]
    _ ≤ (∑ c : β, (R c).card) + budget Allowed m :=
      Nat.add_le_add_left (unique_budget_sum_le Q Allowed hu
        (fun j c h => hallowed j h.1) m) _

end PEqualNP.Outside.L_meta_3457_union_budget
