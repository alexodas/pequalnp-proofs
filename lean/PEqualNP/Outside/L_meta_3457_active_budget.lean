import PEqualNP.Outside.L_meta_3457_cover_cut
import PEqualNP.MetaComplexity.Helpers.Support

/-!
An input-dependence budget for arbitrary incidence graphs.
For vertex-disjoint star blocks the standard clean cover circuit
uses one less gate than the number of active vertices, so the
dependence lower bound pays for the whole normalization.
-/
namespace PEqualNP.Outside.L_meta_3457_active_budget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3457_cover_cut
open PEqualNP.MetaComplexity.Helpers

def DependsOn (n : ℕ) (C : Circuit) (i : Fin n) : Prop :=
  ∃ x y : Fin n → Bool, (∀ k, k ≠ i → x k = y k) ∧
    C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)

theorem dependent_inputs_budget (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (A : Finset (Fin n)) (hA : ∀ i ∈ A, DependsOn n C i) :
    A.card ≤ C.size + 1 := by
  classical
  let S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅
  have hsub : A ⊆ S := by
    intro i hi
    by_contra hn
    obtain ⟨x,y,hxy,hne⟩ := hA i hi
    have hag := (agree_wiresFrom x y C.gates _ _ _ (agree_inputs x y)).2.2 C.output
      (fun k hk => hxy k (fun e => hn (e ▸ hk)))
    exact hne hag
  have hok : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    obtain ⟨ho,hl⟩ := hm g hg
    refine ⟨?_,hl⟩
    have he : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using ho
    rcases he with he | he <;> simp [he]
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) hok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion,Finset.card_singleton,zero_add] at hc
  exact le_trans (Finset.card_le_card hsub) hc

def Active (N : ℕ) (I : Fin N → Fin N → Prop) (i : Fin (N+N)) : Prop :=
  (∃ p l : Fin N, I p l ∧ (i = Fin.castAdd N p ∨ i = Fin.natAdd N l))

noncomputable def activeVertices (N : ℕ) (I : Fin N → Fin N → Prop) :
    Finset (Fin (N+N)) := by
  classical
  exact Finset.univ.filter (Active N I)

theorem active_depends (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hfun : ∀ z : Fin (N+N) → Bool, C.eval (List.ofFn z) = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (i : Fin (N+N)) (hi : Active N I i) : DependsOn (N+N) C i := by
  obtain ⟨p,l,hI,hi⟩ := hi
  let a := Fin.castAdd N p
  let b := Fin.natAdd N l
  let x := fun k : Fin (N+N) => decide (k = a ∨ k = b)
  have hx : C.eval (List.ofFn x) = true :=
    (hfun x).mpr ⟨p,l,hI,by simp [x,a],by simp [x,b]⟩
  rcases hi with hi | hi
  · let y := fun k : Fin (N+N) => decide (k = b)
    have hy : C.eval (List.ofFn y) = false := by
      cases he : C.eval (List.ofFn y) with
      | false => rfl
      | true =>
        obtain ⟨q,m,_,hq,_⟩ := (hfun y).mp he
        exact False.elim (point_line_distinct N q l (of_decide_eq_true hq))
    refine ⟨x,y,?_,by rw [hx,hy]; decide⟩
    intro k hk
    have hka : k ≠ a := fun he => hk (he.trans hi.symm)
    simp [x,y,hka]
  · let y := fun k : Fin (N+N) => decide (k = a)
    have hy : C.eval (List.ofFn y) = false := by
      cases he : C.eval (List.ofFn y) with
      | false => rfl
      | true =>
        obtain ⟨q,m,_,_,hm⟩ := (hfun y).mp he
        exact False.elim ((point_line_distinct N p m).symm (of_decide_eq_true hm))
    refine ⟨x,y,?_,by rw [hx,hy]; decide⟩
    intro k hk
    have hkb : k ≠ b := fun he => hk (he.trans hi.symm)
    simp [x,y,hkb]

theorem active_vertices_budget (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (hm : Monotone2 C)
    (hfun : ∀ z : Fin (N+N) → Bool, C.eval (List.ofFn z) = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    (activeVertices N I).card ≤ C.size + 1 := by
  apply dependent_inputs_budget _ C hm
  intro i hi
  exact active_depends N I C hfun i ((Finset.mem_filter.mp hi).2)

def blockVertices (own : List (ℕ × List ℕ)) : List ℕ :=
  own.flatMap (fun p => p.1 :: p.2)

theorem block_vertices_length (own : List (ℕ × List ℕ)) :
    (blockVertices own).length =
      (own.map (fun p : ℕ × List ℕ => p.2.length)).sum + own.length := by
  induction own with
  | nil => rfl
  | cons p own ih =>
    simp only [blockVertices,List.flatMap_cons,List.length_append,List.length_cons,
      List.map_cons,List.sum_cons] at *
    omega

/-- A disjoint star cover with active vertices has sufficient
    budget for the clean normalization. The cover correctness is
    supplied separately by the incidence/block correspondence. -/
theorem disjoint_block_budget (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (hm : Monotone2 C)
    (hfun : ∀ z : Fin (N+N) → Bool, C.eval (List.ofFn z) = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (own : List (ℕ × List ℕ)) (hne : own ≠ [])
    (hblocks : ∀ p ∈ own, p.2 ≠ [])
    (hdis : (blockVertices own).Nodup)
    (hactive : ∀ t ∈ blockVertices own, ∃ i ∈ activeVertices N I, i.val = t) :
    (coverCircuitB (N+N) own).size ≤ C.size := by
  classical
  have hsub : (blockVertices own).toFinset ⊆ (activeVertices N I).image Fin.val := by
    intro t ht
    obtain ⟨i,hi,he⟩ := hactive t (List.mem_toFinset.mp ht)
    exact Finset.mem_image.mpr ⟨i,hi,he⟩
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hdis,block_vertices_length] at hcard
  have hImage : ((activeVertices N I).image Fin.val).card ≤ (activeVertices N I).card :=
    Finset.card_image_le
  have hb := active_vertices_budget N I C hm hfun
  have hsize := PEqualNP.MetaComplexity.Helpers.CoverCircB.circuit_size (N+N) own hne hblocks
  omega

end PEqualNP.Outside.L_meta_3457_active_budget
