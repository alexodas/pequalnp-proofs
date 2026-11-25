import PEqualNP.Outside.L_meta_3457_root_extract

/-! Combine the star-root extraction with the shared OR budgets.
This is a necessary size bound for a clean circuit, not a proof
that an arbitrary circuit admits a clean normalization. -/

namespace PEqualNP.Outside.L_meta_3457_clean_edge_bound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.Helpers.CoverCircB
open PEqualNP.Outside.L_meta_3457_cover_cut
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_rectangles
open PEqualNP.Outside.L_meta_3457_trace_cover
open PEqualNP.Outside.L_meta_3457_trace_exact
open PEqualNP.Outside.L_meta_3457_support_dag
open PEqualNP.Outside.L_meta_3457_union_budget
open PEqualNP.Outside.L_meta_3457_edge_budget
open PEqualNP.Outside.L_meta_3457_root_extract

theorem all_roots (N : ℕ) (I : Fin N → Fin N → Prop)
    (hf : C4Free N I) (C : Circuit) (hm : Monotone2 C)
    (hr : ReadsBack (N+N) C)
    (hs : ∀ k : Fin (N+N), Silent C.gates (singletonRow k))
    (hc : ∀ p l : Fin N, ¬ I p l →
      Silent C.gates (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)))
    (hS : ∀ k : Fin (N+N), C.eval (singletonRow k) = false)
    (hP : ∀ p l : Fin N, I p l →
      C.eval (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true) :
    ∃ R : Finset (Root N), R.card ≤ 2 * (andIndices C).card ∧
      (∀ r ∈ R, ValidRoot N I C r) ∧
      ∀ p l : Fin N, I p l → ∃ r ∈ R, Covers N C r p l := by
  classical
  have hex : ∀ j : Fin C.gates.length,
      ∃ R : Finset (Root N), R.card ≤ 2 ∧
        (∀ r ∈ R, ValidRoot N I C r) ∧
        ((atGate C.gates j.val).op = GateOp.and →
          ∀ p l : Fin N,
            PEqualNP.Outside.L_meta_3457_first_gate.gateTest
              (C.gates.take j.val) (atGate C.gates j.val)
              (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true →
            ∃ r ∈ R, Covers N C r p l) := by
    intro j
    by_cases hj : (atGate C.gates j.val).op = GateOp.and
    · obtain ⟨R,hR,hv,hh⟩ := gate_roots N I hf C hm hr hs hc j hj
      exact ⟨R,hR,hv,fun _ => hh⟩
    · exact ⟨∅,by simp,by simp,fun h => False.elim (hj h)⟩
  choose R hR hv hh using hex
  refine ⟨(andIndices C).biUnion R,?_,?_,?_⟩
  · calc
      ((andIndices C).biUnion R).card ≤ ∑ j ∈ andIndices C, (R j).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ andIndices C, 2 := Finset.sum_le_sum (fun j _ => hR j)
      _ = 2 * (andIndices C).card := by simp [Nat.mul_comm]
  · intro r h
    obtain ⟨j,hj,hr⟩ := Finset.mem_biUnion.mp h
    exact hv j r hr
  · intro p l hi
    obtain ⟨j,hj,hop,hval⟩ := mixed_trace_contains_incidence N I C hm hs hS hP p l hi
    let k : Fin C.gates.length := ⟨j,hj⟩
    have hk : k ∈ andIndices C := by simp [andIndices,k,hop]
    obtain ⟨r,hmr,hcov⟩ := hh k hop p l hval
    exact ⟨r,Finset.mem_biUnion.mpr ⟨k,hk,hmr⟩,hcov⟩

theorem or_and_budget_le (n : ℕ) (C : Circuit) :
    budget (OrWire n C) (n+C.gates.length) + (andIndices C).card ≤ C.size := by
  classical
  let A := (Finset.range (n+C.gates.length)).filter (OrWire n C)
  let B := (Finset.univ : Finset (Fin C.gates.length)).filter
    (fun j => ¬ (atGate C.gates j.val).op = GateOp.and)
  have hsub : A ⊆ B.image (fun j => n+j.val) := by
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    obtain ⟨hn,hg,hop⟩ := h
    let j : Fin C.gates.length := ⟨i-n,by omega⟩
    refine Finset.mem_image.mpr ⟨j,?_,by dsimp [j]; omega⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change (atGate C.gates (i-n)).op ≠ GateOp.and
    rw [hop]
    intro he
    cases he
  have h1 := Finset.card_le_card hsub
  have h2 : (B.image (fun j => n+j.val)).card ≤ B.card := Finset.card_image_le
  have h3 : (andIndices C).card + B.card = C.gates.length := by
    simpa [andIndices,B] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin C.gates.length)))
        (fun j => (atGate C.gates j.val).op = GateOp.and))
  change A.card + (andIndices C).card ≤ C.gates.length
  omega

theorem clean_edge_bound (N : ℕ) (I : Fin N → Fin N → Prop)
    (hf : C4Free N I) (C : Circuit) (hm : Monotone2 C)
    (hr : ReadsBack (N+N) C)
    (hs : ∀ k : Fin (N+N), Silent C.gates (singletonRow k))
    (hc : ∀ p l : Fin N, ¬ I p l →
      Silent C.gates (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)))
    (hS : ∀ k : Fin (N+N), C.eval (singletonRow k) = false)
    (hP : ∀ p l : Fin N, I p l →
      C.eval (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true) :
    (edgePairs N I).card ≤ 2 * C.size := by
  classical
  obtain ⟨R,hR,hv,hcover⟩ := all_roots N I hf C hm hr hs hc hS hP
  let RP := fun p : Fin N => (R.filter (fun r => r.1 = Sum.inl p)).image Prod.snd
  let RL := fun l : Fin N => (R.filter (fun r => r.1 = Sum.inr l)).image Prod.snd
  let m := N+N+C.gates.length
  have hRP : ∀ p, RP p ⊆ Finset.range m := by
    intro p i hi
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (hv r (Finset.mem_filter.mp hr).1).1
  have hRL : ∀ l, RL l ⊆ Finset.range m := by
    intro l i hi
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (hv r (Finset.mem_filter.mp hr).1).1
  have hp : ∀ p i, i ∈ RP p → LS N C i ⊆ pointNeighbours N I p := by
    intro p i hi
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hi
    have he := (Finset.mem_filter.mp hr).2
    have hh := (hv r (Finset.mem_filter.mp hr).1).2
    rw [he] at hh
    exact hh
  have hl : ∀ l i, i ∈ RL l → PS N C i ⊆ lineNeighbours N I l := by
    intro l i hi
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hi
    have he := (Finset.mem_filter.mp hr).2
    have hh := (hv r (Finset.mem_filter.mp hr).1).2
    rw [he] at hh
    exact hh
  have hcov : ∀ p l, I p l →
      l ∈ (RP p).biUnion (LS N C) ∨ p ∈ (RL l).biUnion (PS N C) := by
    intro p l hi
    obtain ⟨⟨c,i⟩,hmr,h⟩ := hcover p l hi
    cases c with
    | inl q =>
      change p = q ∧ l ∈ LS N C i at h
      obtain ⟨rfl,h⟩ := h
      exact Or.inl (Finset.mem_biUnion.mpr ⟨i,
        Finset.mem_image.mpr ⟨(.inl p,i),Finset.mem_filter.mpr ⟨hmr,rfl⟩,rfl⟩,h⟩)
    | inr q =>
      change l = q ∧ p ∈ PS N C i at h
      obtain ⟨rfl,h⟩ := h
      exact Or.inr (Finset.mem_biUnion.mpr ⟨i,
        Finset.mem_image.mpr ⟨(.inr l,i),Finset.mem_filter.mpr ⟨hmr,rfl⟩,rfl⟩,h⟩)
  have hinjP : Function.Injective (Fin.castAdd N : Fin N → Fin (N+N)) := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun k : Fin (N+N) => k.val) h
  have hinjL : Function.Injective (Fin.natAdd N : Fin N → Fin (N+N)) := by
    intro a b h
    apply Fin.ext
    have hh := congrArg (fun k : Fin (N+N) => k.val) h
    simp only [Fin.val_natAdd] at hh
    omega
  have hbound := edge_budget N I hf (PS N C) (LS N C) RP RL
    (OrWire (N+N) C) m
    (fun j => support_split C _ hinjP hm hr j)
    (fun j => support_split C _ hinjL hm hr j)
    (fun j => support_large_is_or C _ hinjP j)
    (fun j => support_large_is_or C _ hinjL j)
    hRP hRL hp hl hcov
  have hgroup := grouped_roots_bound R Prod.fst Prod.snd
  have hcount : (∑ p : Fin N, (RP p).card) + (∑ l : Fin N, (RL l).card) ≤ R.card := by
    simpa only [Fintype.sum_sum_type,RP,RL] using hgroup
  have hb := or_and_budget_le (N+N) C
  change budget (OrWire (N+N) C) m + (andIndices C).card ≤ C.size at hb
  omega

end PEqualNP.Outside.L_meta_3457_clean_edge_bound
