import PEqualNP.Outside.L_meta_3457_critical_cut

/-!
A precise sufficient reduction of L-meta-3457:
only a circuit all of whose dirty gates are edge-critical needs
a new size-preserving transformation. The other case is automatic.
-/

namespace PEqualNP.Outside.L_meta_3457_essential_cut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_suppress
open PEqualNP.Outside.L_meta_3457_critical_cut

def Admissible (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) : Prop :=
  Monotone2 C ∧ ReadsBack (N+N) C ∧
  (∀ z : Fin (N+N) → Bool,
    C.eval (List.ofFn z) = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true) ∧
  (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
    ∀ k : Fin (N+N),
      (C.wires (singletonRow k)).getD (N+N+j) false = false)

def Critical (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) (j : ℕ) : Prop :=
  ∃ p l : Fin N, I p l ∧
    (suppress C j).eval (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = false

def AllDirtyCritical (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) : Prop :=
  ∀ j p l, (j,p,l) ∈ dirtySites N I C → Critical N I C j

theorem suppress_admissible (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (j : ℕ) (h : Admissible N I C)
    (hc : ¬ Critical N I C j) : Admissible N I (suppress C j) := by
  classical
  obtain ⟨hm,hr,hfun,hs⟩ := h
  have he : ∀ p l : Fin N, I p l →
      (suppress C j).eval (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true := by
    intro p l hi
    cases hv : (suppress C j).eval (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) with
    | false => exact False.elim (hc ⟨p,l,hi,hv⟩)
    | true => rfl
  have hf := (suppression_iff_edges N I C j hm hfun).mpr he
  refine ⟨suppress_monotone C j hm, suppress_reads_back _ C j hr, ?_, ?_⟩
  · intro z
    rw [hf z]
    exact hfun z
  · intro k hk hop i
    let w := singletonRow i
    have hw : w.length = N+N := by simp [w,singletonRow]
    change ((suppress C j).wires w).getD (N+N+k) false = false
    rw [← hw]
    cases hv : ((suppress C j).wires w).getD (w.length+k) false with
    | false => rfl
    | true =>
      obtain ⟨hk',hop',hv',_⟩ := suppress_active_subset C j k hm hk hop w hv
      rw [hw] at hv'
      have hfalse := hs k hk' hop' i
      change (C.wires w).getD (N+N+k) false = false at hfalse
      rw [hfalse] at hv'
      cases hv'

/-- Choose a least-dirty representative of bounded size; all its
    remaining dirty sites belong to edge-critical gates. -/
theorem reduce_to_critical (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (h : Admissible N I C) :
    ∃ D : Circuit, Admissible N I D ∧ D.size ≤ C.size ∧
      AllDirtyCritical N I D := by
  classical
  let P := fun k : ℕ => ∃ D : Circuit, Admissible N I D ∧ D.size ≤ C.size ∧
    (dirtySites N I D).card = k
  have hex : ∃ k, P k := ⟨_, C, h, le_rfl, rfl⟩
  obtain ⟨D,hD,hs,hmin⟩ := Nat.find_spec hex
  refine ⟨D,hD,hs,?_⟩
  intro j p l hd
  by_contra hn
  have hnew := suppress_admissible N I D j hD hn
  have hsize : (suppress D j).size ≤ C.size := by rw [suppress_size]; exact hs
  have hp : P (dirtySites N I (suppress D j)).card :=
    ⟨_, hnew, hsize, rfl⟩
  have hle := Nat.find_min' hex hp
  have hlt := suppression_dirty_decreases N I D j hD.1 p l hd
  omega

/-- A one-step progress theorem only for the all-critical case
    suffices for complete normalization, by strong induction. -/
theorem normalize_of_critical_progress (N : ℕ) (I : Fin N → Fin N → Prop)
    (progress : ∀ D : Circuit, Admissible N I D →
      AllDirtyCritical N I D → dirtySites N I D ≠ ∅ →
      ∃ E : Circuit, Admissible N I E ∧ E.size ≤ D.size ∧
        (dirtySites N I E).card < (dirtySites N I D).card)
    (C : Circuit) (hC : Admissible N I C) :
    ∃ D : Circuit, Admissible N I D ∧ D.size ≤ C.size ∧
      dirtySites N I D = ∅ := by
  classical
  let P := fun k : ℕ => ∃ D : Circuit, Admissible N I D ∧ D.size ≤ C.size ∧
    (dirtySites N I D).card = k
  have hex : ∃ k, P k := ⟨_, C, hC, le_rfl, rfl⟩
  obtain ⟨D,hD,hs,hmin⟩ := Nat.find_spec hex
  refine ⟨D,hD,hs,?_⟩
  by_contra hn
  have hcritical : AllDirtyCritical N I D := by
    intro j p l hd
    by_contra hc
    have hnew := suppress_admissible N I D j hD hc
    have hsize : (suppress D j).size ≤ C.size := by rw [suppress_size]; exact hs
    have hp : P (dirtySites N I (suppress D j)).card :=
      ⟨_,hnew,hsize,rfl⟩
    have hle := Nat.find_min' hex hp
    have hlt := suppression_dirty_decreases N I D j hD.1 p l hd
    omega
  obtain ⟨E,hE,he,hlt⟩ := progress D hD hcritical hn
  have hp : P (dirtySites N I E).card := ⟨E,hE,le_trans he hs,rfl⟩
  have hle := Nat.find_min' hex hp
  omega

end PEqualNP.Outside.L_meta_3457_essential_cut
