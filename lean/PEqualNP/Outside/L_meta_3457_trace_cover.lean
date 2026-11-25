import PEqualNP.Outside.L_meta_3457_first_gate

/-!
Extract a vertex cover from the first-active AND traces of a
mixed-clean incidence circuit. The bound is twice the AND count;
it is not the required full gate-budget bound.
-/

namespace PEqualNP.Outside.L_meta_3457_trace_cover

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.CoverCircB
open PEqualNP.Outside.L_meta_3457_cover_cut
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_rectangles
open PEqualNP.Outside.L_meta_3457_first_gate
open PEqualNP.MetaComplexity.NestedCover

local instance : DecidableEq GateOp := gateOpDecEq

def andIndices (C : Circuit) : Finset (Fin C.gates.length) :=
  Finset.univ.filter (fun j => (atGate C.gates j.val).op = GateOp.and)

theorem gate_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    atGate C.gates j ∈ C.gates := by
  simp [atGate, List.getD_eq_getElem?_getD, hj]

theorem silent_of_ands_false (C : Circuit) (hm : Monotone2 C) (w : List Bool)
    (h : ∀ j < C.gates.length, (atGate C.gates j).op = GateOp.and →
      (C.gates.foldl step w).getD (w.length+j) false = false) :
    Silent C.gates w :=
  fun j hj hn => h j hj (monotone_gate_nonor_is_and C hm j hj hn)

theorem shadow_and_false (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hop : (atGate C.gates j).op = GateOp.and) (w : List Bool)
    (hs : Silent C.gates w) :
    gateTest (C.gates.take j) (atGate C.gates j) w = false := by
  have hpre := prefix_silent C.gates w j (Nat.le_of_lt hj)
    (fun i hi hn => hs i (lt_trans hi hj) hn)
  rw [gateTest_eq_wire C.gates w j hj hpre]
  apply hs j hj
  rw [hop]
  decide

theorem trace_local_cover (N : ℕ) (I : Fin N → Fin N → Prop)
    (hf : C4Free N I) (C : Circuit) (hm : Monotone2 C)
    (hs : ∀ k : Fin (N+N), Silent C.gates (singletonRow k))
    (hc : ∀ p l : Fin N, ¬ I p l →
      Silent C.gates (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)))
    (j : Fin C.gates.length) (hop : (atGate C.gates j.val).op = GateOp.and) :
    ∃ T : Finset (Sum (Fin N) (Fin N)), T.card ≤ 2 ∧
      ∀ p l : Fin N,
        gateTest (C.gates.take j.val) (atGate C.gates j.val)
          (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true →
        ∃ c ∈ T, Hits c p l := by
  apply gateTest_two_centres N I hf _ _ hop (hm _ (gate_mem C j.val j.isLt)).2
  · intro k
    exact shadow_and_false C j.val j.isLt hop _ (hs k)
  · intro p l h
    by_contra hn
    have he := shadow_and_false C j.val j.isLt hop _ (hc p l hn)
    rw [h] at he
    cases he

/-- A clean circuit with a silent singleton row for each input
    induces a vertex cover with at most twice its number of ANDs. -/
theorem clean_trace_cover_bound (N : ℕ) (I : Fin N → Fin N → Prop)
    (hf : C4Free N I) (C : Circuit) (hm : Monotone2 C)
    (hs : ∀ k : Fin (N+N), Silent C.gates (singletonRow k))
    (hc : ∀ p l : Fin N, ¬ I p l →
      Silent C.gates (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)))
    (hS : ∀ k : Fin (N+N), C.eval (singletonRow k) = false)
    (hP : ∀ p l : Fin N, I p l →
      C.eval (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true) :
    ∃ T : Finset (Sum (Fin N) (Fin N)), T.card ≤ 2 * (andIndices C).card ∧
      ∀ p l : Fin N, I p l → ∃ c ∈ T, Hits c p l := by
  classical
  have hlocal : ∀ j : Fin C.gates.length,
      ∃ T : Finset (Sum (Fin N) (Fin N)), T.card ≤ 2 ∧
        ((atGate C.gates j.val).op = GateOp.and →
          ∀ p l : Fin N,
            gateTest (C.gates.take j.val) (atGate C.gates j.val)
              (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true →
              ∃ c ∈ T, Hits c p l) := by
    intro j
    by_cases hj : (atGate C.gates j.val).op = GateOp.and
    · obtain ⟨T, ht, hh⟩ := trace_local_cover N I hf C hm hs hc j hj
      exact ⟨T, ht, fun _ => hh⟩
    · exact ⟨∅, by simp, fun h => False.elim (hj h)⟩
  choose T ht hh using hlocal
  refine ⟨(andIndices C).biUnion T, ?_, ?_⟩
  · calc
      ((andIndices C).biUnion T).card ≤ ∑ j ∈ andIndices C, (T j).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ andIndices C, 2 := Finset.sum_le_sum (fun j _ => ht j)
      _ = 2 * (andIndices C).card := by simp [Nat.mul_comm]
  · intro p l hi
    have hU := hS (Fin.castAdd N p)
    have hV := hS (Fin.natAdd N l)
    have hW := hP p l hi
    simp only [Circuit.eval, wires_eq] at hU hV hW
    obtain ⟨j,hj,hn,hw⟩ := earliest_shadow_witness C.gates C.output
      (Fin.castAdd N p) (Fin.natAdd N l) (hs _) (hs _) hU hV hW
    have hop := monotone_gate_nonor_is_and C hm j hj hn
    let jf : Fin C.gates.length := ⟨j,hj⟩
    have hmj : jf ∈ andIndices C := by simp [andIndices, jf, hop]
    obtain ⟨c,hc,hits⟩ := hh jf hop p l hw
    exact ⟨c,Finset.mem_biUnion.mpr ⟨jf,hmj,hc⟩,hits⟩

end PEqualNP.Outside.L_meta_3457_trace_cover
