import PEqualNP.Outside.L_meta_3457_suppress

/-!
Critical-edge test and a strictly decreasing dirty-site potential.
Deleting a nonessential dirty gate is never the counting obstruction.
-/

namespace PEqualNP.Outside.L_meta_3457_critical_cut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.Helpers.CoverCircB
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_suppress

theorem pair_below_input {n : ℕ} (p l : Fin n) (z : Fin n → Bool)
    (hp : z p = true) (hl : z l = true) :
    Below (doubleRow p l) (List.ofFn z) := by
  refine ⟨by simp [doubleRow], ?_⟩
  intro i hi
  by_cases h : i < n
  · have hh : (⟨i,h⟩ : Fin n) = p ∨ (⟨i,h⟩ : Fin n) = l := by
      simpa [doubleRow, List.getD_eq_getElem?_getD, h] using hi
    have hz : z ⟨i,h⟩ = true := by
      rcases hh with hh | hh
      · rw [hh]; exact hp
      · rw [hh]; exact hl
    simpa [List.getD_eq_getElem?_getD, h] using hz
  · simp [doubleRow, List.getD_eq_getElem?_getD, h] at hi

theorem eval_upward (C : Circuit) (hm : Monotone2 C) (u v : List Bool)
    (h : Below u v) : C.eval u = true → C.eval v = true := by
  have hmono : MonoList C.gates := by
    intro g hg
    simpa using (hm g hg).1
  exact (fold_below C.gates u v h hmono).2 C.output

/-- Suppression preserves the entire function iff it keeps its positive
    incidence pairs. The only-if direction does not require monotonicity. -/
theorem suppression_iff_edges (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (j : ℕ) (hm : Monotone2 C)
    (hfun : ∀ z : Fin (N+N) → Bool,
      C.eval (List.ofFn z) = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    (∀ z : Fin (N+N) → Bool,
      (suppress C j).eval (List.ofFn z) = C.eval (List.ofFn z)) ↔
      (∀ p l : Fin N, I p l →
        (suppress C j).eval (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true) := by
  constructor
  · intro h p l hi
    let z := fun k : Fin (N+N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
    change (suppress C j).eval (List.ofFn z) = true
    rw [h z]
    exact (hfun z).mpr ⟨p,l,hi,by simp [z],by simp [z]⟩
  · intro he z
    have hf : (suppress C j).eval (List.ofFn z) = true ↔ C.eval (List.ofFn z) = true := by
      constructor
      · exact suppress_eval_below C j hm _
      · intro hc
        obtain ⟨p,l,hi,hp,hl⟩ := (hfun z).mp hc
        exact eval_upward (suppress C j) (suppress_monotone C j hm) _ _
          (pair_below_input _ _ z hp hl) (he p l hi)
    cases hd : (suppress C j).eval (List.ofFn z) <;>
      cases hc : C.eval (List.ofFn z) <;> simp_all

noncomputable def dirtySites (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) :
    Finset (ℕ × (Fin N × Fin N)) := by
  classical
  exact ((Finset.range C.gates.length).product Finset.univ).filter (fun s =>
    ¬ I s.2.1 s.2.2 ∧ (gateAt C s.1).op = GateOp.and ∧
      (C.wires (doubleRow (Fin.castAdd N s.2.1) (Fin.natAdd N s.2.2))).getD
        (N+N+s.1) false = true)

theorem mem_dirtySites (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (k : ℕ) (p l : Fin N) :
    (k,p,l) ∈ dirtySites N I C ↔
      k < C.gates.length ∧ ¬ I p l ∧ (gateAt C k).op = GateOp.and ∧
      (C.wires (doubleRow (Fin.castAdd N p) (Fin.natAdd N l))).getD
        (N+N+k) false = true := by
  classical
  simp [dirtySites, Finset.mem_product]

theorem suppression_dirty_subset (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (j : ℕ) (hm : Monotone2 C) :
    dirtySites N I (suppress C j) ⊆ dirtySites N I C := by
  rintro ⟨k,p,l⟩ h
  obtain ⟨hk,hi,hop,hv⟩ := (mem_dirtySites N I _ k p l).mp h
  let w := doubleRow (Fin.castAdd N p) (Fin.natAdd N l)
  have hw : w.length = N+N := by simp [w,doubleRow]
  change ((suppress C j).wires w).getD (N+N+k) false = true at hv
  rw [← hw] at hv
  obtain ⟨hk',hop',hv',_⟩ := suppress_active_subset C j k hm hk hop w hv
  rw [hw] at hv'
  exact (mem_dirtySites N I C k p l).mpr ⟨hk',hi,hop',hv'⟩

/-- The dirty-site potential decreases strictly if a dirty gate is
    suppressed, even if other gates remain true on the same pair. -/
theorem suppression_dirty_decreases (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (j : ℕ) (hm : Monotone2 C)
    (p l : Fin N) (h : (j,p,l) ∈ dirtySites N I C) :
    (dirtySites N I (suppress C j)).card < (dirtySites N I C).card := by
  have hs := suppression_dirty_subset N I C j hm
  have hn : (j,p,l) ∉ dirtySites N I (suppress C j) := by
    intro hh
    obtain ⟨hj,_,hop,_⟩ := (mem_dirtySites N I _ j p l).mp hh
    have hj' : j < C.gates.length := by simpa [suppress] using hj
    rw [suppress_at_self C j hj'] at hop
    cases hop
  apply Finset.card_lt_card
  exact ⟨hs, fun hback => hn (hback h)⟩

theorem dirty_empty_iff (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) :
    dirtySites N I C = ∅ ↔
      ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∀ p l : Fin N, ¬ I p l →
          (C.wires (doubleRow (Fin.castAdd N p) (Fin.natAdd N l))).getD
            (N+N+j) false = false := by
  constructor
  · intro h j hj hop p l hi
    cases hv : (C.wires (doubleRow (Fin.castAdd N p) (Fin.natAdd N l))).getD
      (N+N+j) false with
    | false => rfl
    | true =>
      have hh := (mem_dirtySites N I C j p l).mpr ⟨hj,hi,hop,hv⟩
      rw [h] at hh
      simpa using hh
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨j,p,l⟩ hj
    obtain ⟨hj,hi,hop,hv⟩ := (mem_dirtySites N I C j p l).mp hj
    rw [h j hj hop p l hi] at hv
    cases hv

end PEqualNP.Outside.L_meta_3457_critical_cut
