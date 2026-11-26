import PEqualNP.Outside.L_meta_3457_support_dag
import PEqualNP.Outside.L_meta_3457_edge_budget
import PEqualNP.Outside.L_meta_3457_trace_exact

/-!
Extract at most two star roots per AND, using the actual OR-shadow
supports. A root records its centre and the wire supplying the
opposite side of the star. The extraction does not assume that the
two orientations have the same centre.
-/
namespace PEqualNP.Outside.L_meta_3457_root_extract

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3457_cover_cut
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_first_gate
open PEqualNP.Outside.L_meta_3457_rectangles
open PEqualNP.Outside.L_meta_3457_support_dag
open PEqualNP.Outside.L_meta_3457_edge_budget
open PEqualNP.Outside.L_meta_3457_trace_cover
open PEqualNP.Outside.L_meta_3457_trace_exact

abbrev Root (N : ℕ) := Sum (Fin N) (Fin N) × ℕ

def PS (N : ℕ) (C : Circuit) := support C (Fin.castAdd N : Fin N → Fin (N+N))
def LS (N : ℕ) (C : Circuit) := support C (Fin.natAdd N : Fin N → Fin (N+N))

def ValidRoot (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (r : Root N) : Prop :=
  r.2 < N+N+C.gates.length ∧
    match r.1 with
    | .inl p => LS N C r.2 ⊆ pointNeighbours N I p
    | .inr l => PS N C r.2 ⊆ lineNeighbours N I l

def Covers (N : ℕ) (C : Circuit) (r : Root N) (p l : Fin N) : Prop :=
  match r.1 with
  | .inl q => p = q ∧ l ∈ LS N C r.2
  | .inr m => l = m ∧ p ∈ PS N C r.2

theorem oriented_rectangle_root (N : ℕ) (I : Fin N → Fin N → Prop)
    (hf : C4Free N I) (C : Circuit) (a b : ℕ)
    (ha : a < N+N+C.gates.length) (hb : b < N+N+C.gates.length)
    (hrect : ∀ p l, p ∈ PS N C a → l ∈ LS N C b → I p l) :
    ∃ R : Finset (Root N), R.card ≤ 1 ∧
      (∀ r ∈ R, ValidRoot N I C r) ∧
      (∀ p l, p ∈ PS N C a → l ∈ LS N C b →
        ∃ r ∈ R, Covers N C r p l) := by
  classical
  by_cases hp : ∃ p, p ∈ PS N C a
  · by_cases hl : ∃ l, l ∈ LS N C b
    · obtain ⟨c,hc⟩ := rectangle_star N I hf
        (fun p => p ∈ PS N C a) (fun l => l ∈ LS N C b) hrect hp hl
      cases c with
      | inl q =>
        obtain ⟨p₀,hp₀⟩ := hp
        obtain ⟨l₀,hl₀⟩ := hl
        have hpoint : ∀ p ∈ PS N C a, p = q := by
          intro p h
          have hh := hc p l₀ h hl₀
          simp [Hits] at hh
          exact hh.symm
        have hq : q ∈ PS N C a := hpoint p₀ hp₀ ▸ hp₀
        refine ⟨{(.inl q,b)},by simp,?_,?_⟩
        · intro r hr
          have he : r = (.inl q,b) := by simpa using hr
          subst r
          refine ⟨hb,?_⟩
          intro l h
          simpa [pointNeighbours] using hrect q l hq h
        · intro p l hp hl
          exact ⟨(.inl q,b),by simp,hpoint p hp,hl⟩
      | inr m =>
        obtain ⟨p₀,hp₀⟩ := hp
        obtain ⟨l₀,hl₀⟩ := hl
        have hline : ∀ l ∈ LS N C b, l = m := by
          intro l h
          have hh := hc p₀ l hp₀ h
          simp [Hits] at hh
          exact hh.symm
        have hm : m ∈ LS N C b := hline l₀ hl₀ ▸ hl₀
        refine ⟨{(.inr m,a)},by simp,?_,?_⟩
        · intro r hr
          have he : r = (.inr m,a) := by simpa using hr
          subst r
          refine ⟨ha,?_⟩
          intro p h
          simpa [lineNeighbours] using hrect p m h hm
        · intro p l hp hl
          exact ⟨(.inr m,a),by simp,hline l hl,hp⟩
    · refine ⟨∅,by simp,by simp,?_⟩
      intro p l hp' hl'
      exact False.elim (hl ⟨l,hl'⟩)
  · refine ⟨∅,by simp,by simp,?_⟩
    intro p l hp' hl'
    exact False.elim (hp ⟨p,hp'⟩)

theorem full_support_test (N : ℕ) (C : Circuit) (hr : ReadsBack (N+N) C)
    (j : ℕ) (hj : j < C.gates.length)
    (hop : (atGate C.gates j).op = GateOp.and)
    (a b : ℕ) (hab : (atGate C.gates j).inputs = [a,b])
    (p l : Fin N)
    (hs : ∀ k : Fin (N+N), gateTest (C.gates.take j) (atGate C.gates j)
      (singletonRow k) = false) :
    gateTest (C.gates.take j) (atGate C.gates j)
      (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true ↔
      (p ∈ PS N C a ∧ l ∈ LS N C b) ∨ (p ∈ PS N C b ∧ l ∈ LS N C a) := by
  have ha : a < N+N+j := hr j hj a (by change _ ∈ (atGate C.gates _).inputs; rw [hab]; simp)
  have hb : b < N+N+j := hr j hj b (by change _ ∈ (atGate C.gates _).inputs; rw [hab]; simp)
  have hread : ∀ k : Fin (N+N), ∀ i < N+N+j,
      shadowRead C.gates (singletonRow k) i =
        shadowRead (C.gates.take j) (singletonRow k) i := by
    intro k i hi
    apply shadow_prefix_eq
    simpa [singletonRow, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] using hi
  let ap := fun p : Fin N => shadowRead (C.gates.take j) (singletonRow (Fin.castAdd N p)) a
  let al := fun l : Fin N => shadowRead (C.gates.take j) (singletonRow (Fin.natAdd N l)) a
  let bp := fun p : Fin N => shadowRead (C.gates.take j) (singletonRow (Fin.castAdd N p)) b
  let bl := fun l : Fin N => shadowRead (C.gates.take j) (singletonRow (Fin.natAdd N l)) b
  have hp : ∀ p, (ap p && bp p) = false := fun p =>
    (gateTest_binary _ _ _ hop a b hab).symm.trans (hs (Fin.castAdd N p))
  have hl : ∀ l, (al l && bl l) = false := fun l =>
    (gateTest_binary _ _ _ hop a b hab).symm.trans (hs (Fin.natAdd N l))
  rw [gateTest_binary _ _ _ hop a b hab, shadow_read_pair _ _ _ a,
    shadow_read_pair _ _ _ b]
  change Cross ap al bp bl p l ↔ _
  rw [cross_iff N ap al bp bl hp hl p l]
  simp only [PS, LS, mem_support, hread _ a ha, hread _ b hb, ap, al, bp, bl]

theorem gate_roots (N : ℕ) (I : Fin N → Fin N → Prop)
    (hf : C4Free N I) (C : Circuit) (hm : Monotone2 C)
    (hr : ReadsBack (N+N) C)
    (hs : ∀ k : Fin (N+N), Silent C.gates (singletonRow k))
    (hc : ∀ p l : Fin N, ¬ I p l →
      Silent C.gates (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)))
    (j : Fin C.gates.length) (hop : (atGate C.gates j.val).op = GateOp.and) :
    ∃ R : Finset (Root N), R.card ≤ 2 ∧
      (∀ r ∈ R, ValidRoot N I C r) ∧
      (∀ p l : Fin N,
        gateTest (C.gates.take j.val) (atGate C.gates j.val)
          (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true →
        ∃ r ∈ R, Covers N C r p l) := by
  classical
  have hS : ∀ k : Fin (N+N), gateTest (C.gates.take j.val) (atGate C.gates j.val)
      (singletonRow k) = false :=
    fun k => shadow_and_false C j.val j.isLt hop _ (hs k)
  have hC : ∀ p l : Fin N,
      gateTest (C.gates.take j.val) (atGate C.gates j.val)
        (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true → I p l := by
    intro p l h
    by_contra hn
    have he := shadow_and_false C j.val j.isLt hop _ (hc p l hn)
    rw [h] at he
    cases he
  by_cases he : ∃ p l : Fin N,
      gateTest (C.gates.take j.val) (atGate C.gates j.val)
        (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true
  · obtain ⟨p,l,hpl⟩ := he
    obtain ⟨a,b,hab⟩ := test_has_two_operands _ _ hop
      (hm _ (gate_mem C j.val j.isLt)).2
      (Fin.castAdd N p) (Fin.natAdd N l) (hS _) (hS _) hpl
    have ha : a < N+N+C.gates.length := by
      have hh := hr j.val j.isLt a (by change _ ∈ (atGate C.gates _).inputs; rw [hab]; simp)
      omega
    have hb : b < N+N+C.gates.length := by
      have hh := hr j.val j.isLt b (by change _ ∈ (atGate C.gates _).inputs; rw [hab]; simp)
      omega
    have ht := full_support_test N C hr j.val j.isLt hop a b hab
    obtain ⟨A,hA,hAv,hAc⟩ := oriented_rectangle_root N I hf C a b ha hb
      (fun p l hp hl => hC p l ((ht p l hS).mpr (Or.inl ⟨hp,hl⟩)))
    obtain ⟨B,hB,hBv,hBc⟩ := oriented_rectangle_root N I hf C b a hb ha
      (fun p l hp hl => hC p l ((ht p l hS).mpr (Or.inr ⟨hp,hl⟩)))
    refine ⟨A ∪ B,le_trans (Finset.card_union_le A B) (by omega),?_,?_⟩
    · intro r hr
      rcases Finset.mem_union.mp hr with h | h
      · exact hAv r h
      · exact hBv r h
    · intro p l h
      rcases (ht p l hS).mp h with h | h
      · obtain ⟨r,hm,hc⟩ := hAc p l h.1 h.2
        exact ⟨r,Finset.mem_union.mpr (Or.inl hm),hc⟩
      · obtain ⟨r,hm,hc⟩ := hBc p l h.1 h.2
        exact ⟨r,Finset.mem_union.mpr (Or.inr hm),hc⟩
  · refine ⟨∅,by simp,by simp,?_⟩
    intro p l h
    exact False.elim (he ⟨p,l,h⟩)

end PEqualNP.Outside.L_meta_3457_root_extract
