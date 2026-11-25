import PEqualNP.Outside.L_meta_3457_shadow

/-!
Bridge from actual circuit wires to the OR-shadow traces.
The local two-centre theorem then applies to each AND trace.
-/

namespace PEqualNP.Outside.L_meta_3457_first_gate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.CoverCircB
open PEqualNP.Outside.L_meta_3457_cover_cut
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_rectangles

theorem prefix_wire_eq (gs : List Gate) (w : List Bool) (j i : ℕ)
    (hi : i < w.length + (gs.take j).length) :
    (gs.foldl step w).getD i false =
      ((gs.take j).foldl step w).getD i false := by
  calc
    (gs.foldl step w).getD i false =
        (((gs.take j) ++ (gs.drop j)).foldl step w).getD i false := by
      rw [List.take_append_drop]
    _ = ((gs.take j).foldl step w).getD i false := by
      rw [List.foldl_append]
      exact fold_keep (gs.drop j) _ (by rw [fold_length]; exact hi)

theorem atGate_take (gs : List Gate) (i j : ℕ) (h : i < j) :
    atGate (gs.take j) i = atGate gs i := by
  simp only [atGate, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

theorem prefix_silent (gs : List Gate) (w : List Bool) (j : ℕ)
    (hj : j ≤ gs.length)
    (h : ∀ i < j, (atGate gs i).op ≠ GateOp.or →
      (gs.foldl step w).getD (w.length+i) false = false) :
    Silent (gs.take j) w := by
  intro i hi hop
  have ht : (gs.take j).length = j := by simp [List.length_take, Nat.min_eq_left hj]
  have hij : i < j := by omega
  rw [atGate_take gs i j hij] at hop
  rw [← prefix_wire_eq gs w j (w.length+i) (by omega)]
  exact h i hij hop

theorem wire_at_gate (gs : List Gate) (w : List Bool) (j : ℕ)
    (hj : j < gs.length) :
    (gs.foldl step w).getD (w.length+j) false =
      (atGate gs j).op.eval
        ((atGate gs j).inputs.map fun i => ((gs.take j).foldl step w).getD i false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.foldl_cons, Nat.add_zero, atGate, List.getD_cons_zero,
        List.take_zero, List.foldl_nil]
      rw [fold_keep gs (step w g) (by rw [step_length]; omega)]
      exact getD_snoc' w _ _ rfl
    | succ j =>
      have hj' : j < gs.length := by simp at hj; omega
      have hidx : w.length + (j+1) = (step w g).length + j := by
        rw [step_length]
        omega
      simp only [List.foldl_cons, atGate, List.getD_cons_succ, List.take_succ_cons]
      rw [show w.length + j.succ = (step w g).length + j from hidx]
      exact ih (step w g) j hj'

def shadowRead (gs : List Gate) (w : List Bool) (i : ℕ) : Bool :=
  (gs.foldl shadowStep w).getD i false

def gateTest (gs : List Gate) (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => shadowRead gs w i)

theorem gateTest_eq_wire (gs : List Gate) (w : List Bool) (j : ℕ)
    (hj : j < gs.length) (hs : Silent (gs.take j) w) :
    gateTest (gs.take j) (atGate gs j) w =
      (gs.foldl step w).getD (w.length+j) false := by
  rw [wire_at_gate gs w j hj]
  simp only [gateTest, shadowRead, shadow_fold_eq _ _ hs]

theorem gateTest_binary (gs : List Gate) (g : Gate) (w : List Bool)
    (hop : g.op = GateOp.and) (a b : ℕ) (hi : g.inputs = [a,b]) :
    gateTest gs g w = (shadowRead gs w a && shadowRead gs w b) := by
  simp only [gateTest, hop, hi, GateOp.eval, List.map_cons, List.map_nil,
    List.all_cons, List.all_nil, id, Bool.and_true]

theorem shadow_read_pair (gs : List Gate) {n : ℕ} (p l : Fin n) (i : ℕ) :
    shadowRead gs (doubleRow p l) i =
      (shadowRead gs (singletonRow p) i || shadowRead gs (singletonRow l) i) :=
  (shadow_fold_merge gs _ _ _ (merge_double_row p l)).2.2 i

/-- If an AND of fan-in at most two is false on every singleton
    but true on a pair, it has exactly two operand positions. -/
theorem test_has_two_operands (gs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and) (hlen : g.inputs.length ≤ 2)
    {n : ℕ} (p l : Fin n)
    (hp : gateTest gs g (singletonRow p) = false)
    (hl : gateTest gs g (singletonRow l) = false)
    (hpl : gateTest gs g (doubleRow p l) = true) :
    ∃ a b, g.inputs = [a,b] := by
  cases hi : g.inputs with
  | nil => simp [gateTest, hop, hi, GateOp.eval] at hp
  | cons a rest =>
    cases rest with
    | nil =>
      simp only [gateTest, hop, hi, GateOp.eval, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, id, Bool.and_true] at hp hl hpl
      rw [shadow_read_pair gs p l a, hp, hl] at hpl
      cases hpl
    | cons b rest =>
      cases rest with
      | nil => exact ⟨a,b,hi⟩
      | cons c rest => simp [hi] at hlen

/-- The local two-centre cover holds for every clean AND's OR-shadow
    trace, not merely for an abstract Boolean rectangle. -/
theorem gateTest_two_centres (N : ℕ) (I : Fin N → Fin N → Prop)
    (hf : C4Free N I) (gs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and) (hlen : g.inputs.length ≤ 2)
    (hS : ∀ k : Fin (N+N), gateTest gs g (singletonRow k) = false)
    (hC : ∀ p l : Fin N,
      gateTest gs g (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true → I p l) :
    ∃ T : Finset (Sum (Fin N) (Fin N)), T.card ≤ 2 ∧
      ∀ p l : Fin N,
        gateTest gs g (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true →
        ∃ c ∈ T, Hits c p l := by
  classical
  by_cases he : ∃ p l : Fin N,
    gateTest gs g (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true
  · obtain ⟨p,l,hpl⟩ := he
    obtain ⟨a,b,hab⟩ := test_has_two_operands gs g hop hlen
      (Fin.castAdd N p) (Fin.natAdd N l) (hS _) (hS _) hpl
    let ap := fun p : Fin N => shadowRead gs (singletonRow (Fin.castAdd N p)) a
    let al := fun l : Fin N => shadowRead gs (singletonRow (Fin.natAdd N l)) a
    let bp := fun p : Fin N => shadowRead gs (singletonRow (Fin.castAdd N p)) b
    let bl := fun l : Fin N => shadowRead gs (singletonRow (Fin.natAdd N l)) b
    have hp : ∀ p, (ap p && bp p) = false := by
      intro p
      exact (gateTest_binary gs g _ hop a b hab).symm.trans (hS _)
    have hl : ∀ l, (al l && bl l) = false := by
      intro l
      exact (gateTest_binary gs g _ hop a b hab).symm.trans (hS _)
    have hiff : ∀ p l : Fin N,
        gateTest gs g (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true ↔
          Cross ap al bp bl p l := by
      intro p l
      rw [gateTest_binary gs g _ hop a b hab,
        shadow_read_pair gs _ _ a, shadow_read_pair gs _ _ b]
      rfl
    obtain ⟨T,ht,hcover⟩ := cross_two_centres N I hf ap al bp bl hp hl
      (fun p l h => hC p l ((hiff p l).mpr h))
    exact ⟨T,ht,fun p l h => hcover p l ((hiff p l).mp h)⟩
  · refine ⟨∅, by simp, ?_⟩
    intro p l hp
    exact False.elim (he ⟨p,l,hp⟩)

/-- Every true pair whose two singleton outputs are false has an
    earliest active non-OR gate, witnessed by its shadow trace. -/
theorem earliest_shadow_witness (gs : List Gate) (o : ℕ) {n : ℕ}
    (p l : Fin n)
    (hp : Silent gs (singletonRow p)) (hl : Silent gs (singletonRow l))
    (hP : (gs.foldl step (singletonRow p)).getD o false = false)
    (hL : (gs.foldl step (singletonRow l)).getD o false = false)
    (hPL : (gs.foldl step (doubleRow p l)).getD o false = true) :
    ∃ j < gs.length, (atGate gs j).op ≠ GateOp.or ∧
      gateTest (gs.take j) (atGate gs j) (doubleRow p l) = true := by
  obtain ⟨j,hj,hop,hval,hprev⟩ := earliest_active_nonor gs (doubleRow p l)
    (exists_active_nonor gs _ _ _ o (merge_double_row p l) hp hl hP hL hPL)
  refine ⟨j,hj,hop,?_⟩
  rw [gateTest_eq_wire gs _ j hj (prefix_silent gs _ j (by omega) hprev)]
  exact hval

end PEqualNP.Outside.L_meta_3457_first_gate
