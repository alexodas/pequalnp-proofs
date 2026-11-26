import PEqualNP.Outside.L_meta_3457_essential_cut
import PEqualNP.Outside.L_meta_3457_rectangles

/-!
Bridge the posted mixed-clean normalization statement to the
critical-progress cut. This is a conditional research theorem;
the progress premise is the outstanding mathematical problem.
-/
namespace PEqualNP.Outside.L_meta_3457_main_cut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_critical_cut
open PEqualNP.Outside.L_meta_3457_essential_cut
open PEqualNP.Outside.L_meta_3457_rectangles

def SingletonSafe (N : ℕ) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
    (∀ p : Fin N, (C.wires (List.ofFn (fun k : Fin (N+N) =>
      decide (k = Fin.castAdd N p)))).getD (N+N+j) false = false) ∧
    ∀ l : Fin N, (C.wires (List.ofFn (fun k : Fin (N+N) =>
      decide (k = Fin.natAdd N l)))).getD (N+N+j) false = false

def MixedClean (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) : Prop :=
  ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
    ∀ p l : Fin N, ¬ I p l →
      (C.wires (List.ofFn (fun k : Fin (N+N) =>
        decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD
          (N+N+j) false = false

def Correct (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) : Prop :=
  ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z = true ↔
    ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
      z (Fin.natAdd N l) = true

theorem singleton_safe_iff (N : ℕ) (C : Circuit) :
    SingletonSafe N C ↔
      ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ∀ k : Fin (N+N), (C.wires (singletonRow k)).getD (N+N+j) false = false := by
  constructor
  · intro h j hj hop k
    refine Fin.addCases (m := N) (n := N) ?_ ?_ k
    · intro p
      exact (h j hj hop).1 p
    · intro l
      exact (h j hj hop).2 l
  · intro h j hj hop
    exact ⟨fun p => h j hj hop (Fin.castAdd N p),fun l => h j hj hop (Fin.natAdd N l)⟩

theorem admissible_iff (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) :
    Admissible N I C ↔ Monotone2 C ∧ ReadsBack (N+N) C ∧
      Correct N I C ∧ SingletonSafe N C := by
  constructor
  · rintro ⟨hm,hr,hf,hs⟩
    exact ⟨hm,hr,hf,(singleton_safe_iff N C).mpr hs⟩
  · rintro ⟨hm,hr,hf,hs⟩
    exact ⟨hm,hr,hf,(singleton_safe_iff N C).mp hs⟩

theorem mixed_clean_iff (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) :
    MixedClean N I C ↔ dirtySites N I C = ∅ :=
  (dirty_empty_iff N I C).symm

def CriticalProgress (N : ℕ) (I : Fin N → Fin N → Prop) : Prop :=
  ∀ D : Circuit, Admissible N I D → AllDirtyCritical N I D →
    dirtySites N I D ≠ ∅ →
    ∃ E : Circuit, Admissible N I E ∧ E.size ≤ D.size ∧
      (dirtySites N I E).card < (dirtySites N I D).card

def Normalize (N : ℕ) (I : Fin N → Fin N → Prop) : Prop :=
  ∀ C : Circuit, Monotone2 C → ReadsBack (N+N) C → Correct N I C →
    SingletonSafe N C →
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack (N+N) D ∧ D.size ≤ C.size ∧
      Correct N I D ∧ MixedClean N I D ∧ SingletonSafe N D

/-- Exact equivalence of normalization with progress on the reduced
    all-critical class. The forward direction is included to show
    that no stronger global size hypothesis is being imposed. -/
theorem normalization_iff_critical_progress (N : ℕ) (I : Fin N → Fin N → Prop) :
    Normalize N I ↔ CriticalProgress N I := by
  constructor
  · intro h D hD _ hn
    obtain ⟨hm,hr,hf,hs⟩ := (admissible_iff N I D).mp hD
    obtain ⟨E,he,her,hsize,hef,hclean,hes⟩ := h D hm hr hf hs
    refine ⟨E,(admissible_iff N I E).mpr ⟨he,her,hef,hes⟩,hsize,?_⟩
    rw [(mixed_clean_iff N I E).mp hclean, Finset.card_empty]
    exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hn)
  · intro hp C hm hr hf hs
    have hC := (admissible_iff N I C).mpr ⟨hm,hr,hf,hs⟩
    obtain ⟨D,hD,hsize,hclean⟩ := normalize_of_critical_progress N I hp C hC
    obtain ⟨hm,hr,hf,hs⟩ := (admissible_iff N I D).mp hD
    exact ⟨D,hm,hr,hsize,hf,(mixed_clean_iff N I D).mpr hclean,hs⟩

end PEqualNP.Outside.L_meta_3457_main_cut
