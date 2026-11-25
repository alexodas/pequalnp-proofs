import PEqualNP.Outside.L_meta_3457_trace_cover

/-!
Exact characterization of mixed dirt by OR-shadow tests.
This reduces the cleanliness obligation to support rectangles
rather than arbitrary intermediate circuit values.
-/

namespace PEqualNP.Outside.L_meta_3457_trace_exact

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers.CoverCircB
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3457_cover_cut
open PEqualNP.Outside.L_meta_3457_rectangles
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_first_gate
open PEqualNP.Outside.L_meta_3457_trace_cover

theorem silent_iff_shadow_tests (gs : List Gate) (w : List Bool) :
    Silent gs w ↔
      ∀ j < gs.length, (atGate gs j).op ≠ GateOp.or →
        gateTest (gs.take j) (atGate gs j) w = false := by
  constructor
  · intro hs j hj hop
    have hpre := prefix_silent gs w j (Nat.le_of_lt hj)
      (fun i hi hn => hs i (lt_trans hi hj) hn)
    rw [gateTest_eq_wire gs w j hj hpre]
    exact hs j hj hop
  · intro ht
    by_contra hn
    have he : ∃ j < gs.length, (atGate gs j).op ≠ GateOp.or ∧
        (gs.foldl step w).getD (w.length+j) false = true := by
      classical
      by_contra h
      apply hn
      intro j hj hop
      cases hv : (gs.foldl step w).getD (w.length+j) false with
      | false => rfl
      | true => exact False.elim (h ⟨j,hj,hop,hv⟩)
    obtain ⟨j,hj,hop,hv,hprev⟩ := earliest_active_nonor gs w he
    have hpre := prefix_silent gs w j (Nat.le_of_lt hj) hprev
    have hfalse := ht j hj hop
    rw [gateTest_eq_wire gs w j hj hpre, hv] at hfalse
    cases hfalse

def Trace (C : Circuit) (w : List Bool) : Prop :=
  ∃ j < C.gates.length, (atGate C.gates j).op = GateOp.and ∧
    gateTest (C.gates.take j) (atGate C.gates j) w = true

theorem trace_iff_not_silent (C : Circuit) (hm : Monotone2 C) (w : List Bool) :
    Trace C w ↔ ¬ Silent C.gates w := by
  constructor
  · rintro ⟨j,hj,hop,hv⟩ hs
    have hnon : (atGate C.gates j).op ≠ GateOp.or := by
      rw [hop]
      intro he
      cases he
    have hf := (silent_iff_shadow_tests C.gates w).mp hs j hj hnon
    rw [hv] at hf
    cases hf
  · intro hn
    classical
    by_contra h
    apply hn
    apply (silent_iff_shadow_tests C.gates w).mpr
    intro j hj hop
    cases he : gateTest (C.gates.take j) (atGate C.gates j) w with
    | false => rfl
    | true =>
      exact False.elim (h ⟨j,hj,monotone_gate_nonor_is_and C hm j hj hop,he⟩)

theorem trace_iff_active_and (C : Circuit) (hm : Monotone2 C) (w : List Bool) :
    Trace C w ↔
      ∃ j < C.gates.length, (atGate C.gates j).op = GateOp.and ∧
        (C.gates.foldl step w).getD (w.length+j) false = true := by
  rw [trace_iff_not_silent C hm w]
  constructor
  · intro hn
    classical
    by_contra h
    apply hn
    apply silent_of_ands_false C hm w
    intro j hj hop
    cases hv : (C.gates.foldl step w).getD (w.length+j) false with
    | false => rfl
    | true => exact False.elim (h ⟨j,hj,hop,hv⟩)
  · rintro ⟨j,hj,hop,hv⟩ hs
    have hnon : (atGate C.gates j).op ≠ GateOp.or := by
      rw [hop]
      intro he
      cases he
    have hf := hs j hj hnon
    rw [hv] at hf
    cases hf

def MixedTrace (N : ℕ) (C : Circuit) (p l : Fin N) : Prop :=
  Trace C (doubleRow (Fin.castAdd N p) (Fin.natAdd N l))

def MixedDirty (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (p l : Fin N) : Prop :=
  ¬ I p l ∧ MixedTrace N C p l

theorem mixed_trace_contains_incidence (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (hm : Monotone2 C)
    (hs : ∀ k : Fin (N+N), Silent C.gates (singletonRow k))
    (hS : ∀ k : Fin (N+N), C.eval (singletonRow k) = false)
    (hP : ∀ p l : Fin N, I p l →
      C.eval (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true) :
    ∀ p l : Fin N, I p l → MixedTrace N C p l := by
  intro p l hi
  have hu := hS (Fin.castAdd N p)
  have hv := hS (Fin.natAdd N l)
  have hw := hP p l hi
  simp only [Circuit.eval, wires_eq] at hu hv hw
  obtain ⟨j,hj,hop,hjv⟩ := earliest_shadow_witness C.gates C.output
    (Fin.castAdd N p) (Fin.natAdd N l) (hs _) (hs _) hu hv hw
  exact ⟨j,hj,monotone_gate_nonor_is_and C hm j hj hop,hjv⟩

/-- The union of shadow traces is exactly the target incidence
    relation plus the mixed dirt, even before normalization. -/
theorem mixed_trace_decomposition (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (hm : Monotone2 C)
    (hs : ∀ k : Fin (N+N), Silent C.gates (singletonRow k))
    (hS : ∀ k : Fin (N+N), C.eval (singletonRow k) = false)
    (hP : ∀ p l : Fin N, I p l →
      C.eval (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true)
    (p l : Fin N) :
    MixedTrace N C p l ↔ I p l ∨ MixedDirty N I C p l := by
  classical
  constructor
  · intro h
    by_cases hi : I p l
    · exact Or.inl hi
    · exact Or.inr ⟨hi,h⟩
  · rintro (hi | ⟨_,h⟩)
    · exact mixed_trace_contains_incidence N I C hm hs hS hP p l hi
    · exact h

/-- The cleanliness condition in the assigned problem is equivalent
    to inclusion of the union of mixed shadow traces in the incidence
    relation. No assumption about same-side pairs is used. -/
theorem mixed_clean_iff_trace_subset (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (hm : Monotone2 C) :
    (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ p l : Fin N, ¬ I p l →
        (C.wires (doubleRow (Fin.castAdd N p) (Fin.natAdd N l))).getD
          (N+N+j) false = false) ↔
      (∀ p l : Fin N, MixedTrace N C p l → I p l) := by
  classical
  constructor
  · intro h p l ht
    by_contra hn
    obtain ⟨j,hj,hop,hv⟩ := (trace_iff_active_and C hm _).mp ht
    have hf := h j hj hop p l hn
    change (C.gates.foldl step (doubleRow (Fin.castAdd N p) (Fin.natAdd N l))).getD
      (N+N+j) false = false at hf
    simp only [doubleRow, List.length_ofFn] at hv
    rw [hv] at hf
    cases hf
  · intro h j hj hop p l hn
    cases hv : (C.wires (doubleRow (Fin.castAdd N p) (Fin.natAdd N l))).getD
        (N+N+j) false with
    | false => rfl
    | true =>
      apply False.elim
      apply hn
      apply h p l
      apply (trace_iff_active_and C hm _).mpr
      refine ⟨j,hj,hop,?_⟩
      simpa only [doubleRow, List.length_ofFn, ← wires_eq] using hv

end PEqualNP.Outside.L_meta_3457_trace_exact
