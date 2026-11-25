import PEqualNP.Outside.L_meta_3457_critical_cut
import PEqualNP.Outside.L_meta_3457_cofactor

/-!
A boundary criterion for a candidate monotone implementation.
There are the positive edge rows and at most 2^N negative rows,
one per set of active points, with every compatible line active.
No assumption of C4-freeness is needed.
-/

namespace PEqualNP.Outside.L_meta_3457_boundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_suppress
open PEqualNP.Outside.L_meta_3457_critical_cut
open PEqualNP.Outside.L_meta_3457_cofactor

noncomputable def negativeRow (N : ℕ) (I : Fin N → Fin N → Prop)
    (a : Fin N → Bool) : Fin (N+N) → Bool := by
  classical
  exact Fin.addCases a (fun l => decide (∀ p, a p = true → ¬ I p l))

theorem negative_point (N : ℕ) (I : Fin N → Fin N → Prop)
    (a : Fin N → Bool) (p : Fin N) :
    negativeRow N I a (Fin.castAdd N p) = a p := by
  classical
  simp only [negativeRow, Fin.addCases_left]

theorem negative_line (N : ℕ) (I : Fin N → Fin N → Prop)
    (a : Fin N → Bool) (l : Fin N) :
    negativeRow N I a (Fin.natAdd N l) = true ↔
      ∀ p, a p = true → ¬ I p l := by
  classical
  simp only [negativeRow, Fin.addCases_right, decide_eq_true_eq]

theorem negative_no_edge (N : ℕ) (I : Fin N → Fin N → Prop)
    (a : Fin N → Bool) :
    ¬ ∃ p l : Fin N, I p l ∧ negativeRow N I a (Fin.castAdd N p) = true ∧
      negativeRow N I a (Fin.natAdd N l) = true := by
  rintro ⟨p,l,hi,hp,hl⟩
  rw [negative_point] at hp
  exact ((negative_line N I a l).mp hl) p hp hi

theorem negative_dominates (N : ℕ) (I : Fin N → Fin N → Prop)
    (z : Fin (N+N) → Bool)
    (hz : ¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
      z (Fin.natAdd N l) = true) :
    ∀ k, z k = true →
      negativeRow N I (fun p => z (Fin.castAdd N p)) k = true := by
  intro k
  refine Fin.addCases (m := N) (n := N) ?_ ?_ k
  · intro p hp
    rw [negative_point]
    exact hp
  · intro l hl
    apply (negative_line N I _ l).mpr
    intro p hp hi
    exact hz ⟨p,l,hi,hp,hl⟩

theorem ofFn_below {n : ℕ} (a b : Fin n → Bool)
    (h : ∀ k, a k = true → b k = true) : Below (List.ofFn a) (List.ofFn b) := by
  refine ⟨by simp,?_⟩
  intro i hi
  by_cases hi' : i < n
  · have ha : a ⟨i,hi'⟩ = true := by
      simpa [List.getD_eq_getElem?_getD, hi'] using hi
    simpa [List.getD_eq_getElem?_getD, hi'] using h ⟨i,hi'⟩ ha
  · simp [List.getD_eq_getElem?_getD, hi'] at hi

theorem boundary_iff (N : ℕ) (I : Fin N → Fin N → Prop)
    (D : Circuit) (hm : Monotone2 D) :
    (∀ z : Fin (N+N) → Bool,
      D.eval (List.ofFn z) = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true) ↔
    (∀ p l : Fin N, I p l →
      D.eval (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true) ∧
    (∀ a : Fin N → Bool, D.eval (List.ofFn (negativeRow N I a)) = false) := by
  classical
  constructor
  · intro h
    constructor
    · intro p l hi
      let z := fun k : Fin (N+N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
      change D.eval (List.ofFn z) = true
      exact (h z).mpr ⟨p,l,hi,by simp [z],by simp [z]⟩
    · intro a
      cases he : D.eval (List.ofFn (negativeRow N I a)) with
      | false => rfl
      | true => exact False.elim (negative_no_edge N I a ((h _).mp he))
  · rintro ⟨hpos,hneg⟩ z
    constructor
    · intro hv
      by_contra hn
      have hb := ofFn_below z (negativeRow N I (fun p => z (Fin.castAdd N p)))
        (negative_dominates N I z hn)
      have he := eval_upward D hm _ _ hb hv
      rw [hneg] at he
      cases he
    · rintro ⟨p,l,hi,hp,hl⟩
      exact eval_upward D hm _ _ (pair_below_input _ _ z hp hl) (hpos p l hi)

/-- The exact positive/negative obligations for a slot replacement:
    critical edge rows must turn the replacement on, and sensitive
    negative boundary rows must turn it off. -/
theorem repair_boundary_iff (N : ℕ) (I : Fin N → Fin N → Prop)
    (pre post : List Gate) (g r : Gate) (o : ℕ)
    (hpost : MonoList post) (hm : Monotone2 (slot pre post r o))
    (hfun : ∀ z : Fin (N+N) → Bool,
      (slot pre post g o).eval (List.ofFn z) = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true) :
    (∀ z : Fin (N+N) → Bool,
      (slot pre post r o).eval (List.ofFn z) = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true) ↔
    (∀ p l : Fin N, I p l →
      low pre post o (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = false →
      preValue pre r (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true) ∧
    (∀ a : Fin N → Bool, high pre post o (List.ofFn (negativeRow N I a)) = true →
      preValue pre r (List.ofFn (negativeRow N I a)) = false) := by
  rw [boundary_iff N I _ hm]
  have hpos : ∀ p l : Fin N, I p l →
      (slot pre post g o).eval (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true := by
    intro p l hi
    let z := fun k : Fin (N+N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
    change (slot pre post g o).eval (List.ofFn z) = true
    exact (hfun z).mpr ⟨p,l,hi,by simp [z],by simp [z]⟩
  have hneg : ∀ a : Fin N → Bool,
      (slot pre post g o).eval (List.ofFn (negativeRow N I a)) = false := by
    intro a
    cases he : (slot pre post g o).eval (List.ofFn (negativeRow N I a)) with
    | false => rfl
    | true => exact False.elim (negative_no_edge N I a ((hfun _).mp he))
  constructor
  · rintro ⟨hp,hn⟩
    refine ⟨?_,?_⟩
    · intro p l hi
      exact (slot_preserves_positive_iff pre post g r o _ hpost (hpos p l hi)).mp (hp p l hi)
    · intro a
      exact (slot_preserves_negative_iff pre post g r o _ hpost (hneg a)).mp (hn a)
  · rintro ⟨hp,hn⟩
    refine ⟨?_,?_⟩
    · intro p l hi
      exact (slot_preserves_positive_iff pre post g r o _ hpost (hpos p l hi)).mpr (hp p l hi)
    · intro a
      exact (slot_preserves_negative_iff pre post g r o _ hpost (hneg a)).mpr (hn a)

end PEqualNP.Outside.L_meta_3457_boundary
