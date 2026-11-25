import Mathlib
import PEqualNP.Defs

/-!
Research cut: a first-active AND has two singleton supports.
Its mixed-pair trace is the union of two oriented rectangles.
For a clean trace in a C4-free relation each nonempty rectangle
has a centre, but the two centres need not coincide.
The circuit-to-support reduction is a separate obligation.
-/

namespace PEqualNP.Outside.L_meta_3457_rectangles

def C4Free (N : ℕ) (I : Fin N → Fin N → Prop) : Prop :=
  ∀ p q l m, p ≠ q → l ≠ m → ¬ (I p l ∧ I p m ∧ I q l ∧ I q m)

def Hits {N : ℕ} (c : Sum (Fin N) (Fin N)) (p l : Fin N) : Prop :=
  c = Sum.inl p ∨ c = Sum.inr l

theorem rectangle_star (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfree : C4Free N I) (A B : Fin N → Prop)
    (hrect : ∀ p l, A p → B l → I p l)
    (ha : ∃ p, A p) (hb : ∃ l, B l) :
    ∃ c : Sum (Fin N) (Fin N), ∀ p l, A p → B l → Hits c p l := by
  classical
  obtain ⟨p₀, hp₀⟩ := ha
  obtain ⟨l₀, hl₀⟩ := hb
  by_cases h : ∀ p, A p → p = p₀
  · refine ⟨Sum.inl p₀, ?_⟩
    intro p l hp hl
    exact Or.inl (congrArg Sum.inl (h p hp).symm)
  · push_neg at h
    obtain ⟨p₁, hp₁, hne⟩ := h
    refine ⟨Sum.inr l₀, ?_⟩
    intro p l hp hl
    have he : l = l₀ := by
      by_contra hn
      exact hfree p₁ p₀ l l₀ hne hn
        ⟨hrect _ _ hp₁ hl, hrect _ _ hp₁ hl₀,
          hrect _ _ hp₀ hl, hrect _ _ hp₀ hl₀⟩
    exact Or.inr (congrArg Sum.inr he.symm)

def Cross {N : ℕ} (ap al bp bl : Fin N → Bool) (p l : Fin N) : Prop :=
  ((ap p || al l) && (bp p || bl l)) = true

theorem cross_iff (N : ℕ) (ap al bp bl : Fin N → Bool)
    (hp : ∀ p, (ap p && bp p) = false)
    (hl : ∀ l, (al l && bl l) = false) (p l : Fin N) :
    Cross ap al bp bl p l ↔
      (ap p = true ∧ bl l = true) ∨ (bp p = true ∧ al l = true) := by
  have h₁ := hp p
  have h₂ := hl l
  unfold Cross
  cases hap : ap p <;> cases hal : al l <;>
    cases hbp : bp p <;> cases hbl : bl l <;> simp_all

theorem rectangle_cover (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfree : C4Free N I) (A B : Fin N → Prop)
    (hrect : ∀ p l, A p → B l → I p l) :
    ∃ T : Finset (Sum (Fin N) (Fin N)), T.card ≤ 1 ∧
      ∀ p l, A p → B l → ∃ c ∈ T, Hits c p l := by
  classical
  by_cases ha : ∃ p, A p
  · by_cases hb : ∃ l, B l
    · obtain ⟨c, hc⟩ := rectangle_star N I hfree A B hrect ha hb
      refine ⟨{c}, by simp, ?_⟩
      intro p l hp hl
      exact ⟨c, by simp, hc p l hp hl⟩
    · refine ⟨∅, by simp, ?_⟩
      intro p l hp hl
      exact False.elim (hb ⟨l, hl⟩)
  · refine ⟨∅, by simp, ?_⟩
    intro p l hp hl
    exact False.elim (ha ⟨p, hp⟩)

/-- A clean mixed-pair trace has a cover of at most two vertices. -/
theorem cross_two_centres (N : ℕ) (I : Fin N → Fin N → Prop)
    (hfree : C4Free N I) (ap al bp bl : Fin N → Bool)
    (hp : ∀ p, (ap p && bp p) = false)
    (hl : ∀ l, (al l && bl l) = false)
    (hc : ∀ p l, Cross ap al bp bl p l → I p l) :
    ∃ T : Finset (Sum (Fin N) (Fin N)), T.card ≤ 2 ∧
      ∀ p l, Cross ap al bp bl p l → ∃ c ∈ T, Hits c p l := by
  classical
  obtain ⟨A, hA, hAc⟩ := rectangle_cover N I hfree
    (fun p => ap p = true) (fun l => bl l = true)
    (fun p l h₁ h₂ => hc p l ((cross_iff N ap al bp bl hp hl p l).mpr
      (Or.inl ⟨h₁, h₂⟩)))
  obtain ⟨B, hB, hBc⟩ := rectangle_cover N I hfree
    (fun p => bp p = true) (fun l => al l = true)
    (fun p l h₁ h₂ => hc p l ((cross_iff N ap al bp bl hp hl p l).mpr
      (Or.inr ⟨h₁, h₂⟩)))
  refine ⟨A ∪ B, le_trans (Finset.card_union_le A B) (by omega), ?_⟩
  intro p l h
  rcases (cross_iff N ap al bp bl hp hl p l).mp h with h | h
  · obtain ⟨c, hmem, hh⟩ := hAc p l h.1 h.2
    exact ⟨c, Finset.mem_union.mpr (Or.inl hmem), hh⟩
  · obtain ⟨c, hmem, hh⟩ := hBc p l h.1 h.2
    exact ⟨c, Finset.mem_union.mpr (Or.inr hmem), hh⟩

/-- If both orientations are used, a same-side two-hot row activates
    the gate. This is the precise extra dirt missed by mixed tests. -/
theorem both_orientations_activate_same_side (N : ℕ)
    (ap al bp bl : Fin N → Bool)
    (hp : ∀ p, (ap p && bp p) = false)
    (hl : ∀ l, (al l && bl l) = false)
    (ha : ∃ p l, ap p = true ∧ bl l = true)
    (hb : ∃ q m, bp q = true ∧ al m = true) :
    ∃ p q l m, p ≠ q ∧ l ≠ m ∧
      ((ap p || ap q) && (bp p || bp q)) = true ∧
      ((al l || al m) && (bl l || bl m)) = true := by
  obtain ⟨p, l, hpa, hlb⟩ := ha
  obtain ⟨q, m, hqb, hma⟩ := hb
  refine ⟨p, q, l, m, ?_, ?_, ?_, ?_⟩
  · intro he
    subst q
    have hh := hp p
    simp [hpa, hqb] at hh
  · intro he
    subst m
    have hh := hl l
    simp [hma, hlb] at hh
  · simp [hpa, hqb]
  · simp [hma, hlb]

end PEqualNP.Outside.L_meta_3457_rectangles
