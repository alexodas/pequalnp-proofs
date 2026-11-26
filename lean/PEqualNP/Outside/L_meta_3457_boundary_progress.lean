import PEqualNP.Outside.L_meta_3457_replace
import PEqualNP.Outside.L_meta_3457_boundary

/-!
A weaker, finite-row repair criterion. Global pointwise domination
of the old gate is not needed. The output is tested on the incidence
boundary, and domination is imposed only on singleton and negative
mixed rows, where it prevents new dirty AND sites.
An OR replacement is allowed: it removes the selected AND site.
-/
namespace PEqualNP.Outside.L_meta_3457_boundary_progress

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_3457_shadow
open PEqualNP.Outside.L_meta_3457_suppress
open PEqualNP.Outside.L_meta_3457_cofactor
open PEqualNP.Outside.L_meta_3457_critical_cut
open PEqualNP.Outside.L_meta_3457_essential_cut
open PEqualNP.Outside.L_meta_3457_or_suffix
open PEqualNP.Outside.L_meta_3457_replace
open PEqualNP.Outside.L_meta_3457_boundary

theorem replacement_and_was_and (C : Circuit) (j k : ℕ) (r : Gate)
    (hj : j < C.gates.length) (hjo : (gateAt C j).op = GateOp.and)
    (hk : (gateAt (replaceGate C j r) k).op = GateOp.and) :
    (gateAt C k).op = GateOp.and := by
  by_cases he : j = k
  · simpa [← he] using hjo
  · rw [replace_at_other C j k r he] at hk
    exact hk

theorem boundary_replacement_progress (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (j : ℕ) (r : Gate) (p₀ l₀ : Fin N)
    (h : Admissible N I C) (hd : (j,p₀,l₀) ∈ dirtySites N I C)
    (hop : r.op = GateOp.and ∨ r.op = GateOp.or)
    (hlen : r.inputs.length ≤ 2)
    (hback : ∀ i ∈ r.inputs, i < N+N+j)
    (hcrit : ∀ p l : Fin N, CriticalPair N I C j p l →
      preValue (C.gates.take j) r (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true)
    (hneg : ∀ a : Fin N → Bool,
      (replaceGate C j r).eval (List.ofFn (negativeRow N I a)) = false)
    (hsing : ∀ k : Fin (N+N),
      preValue (C.gates.take j) r (singletonRow k) = true →
        preValue (C.gates.take j) (atGate C.gates j) (singletonRow k) = true)
    (hmixed : ∀ p l : Fin N, ¬ I p l →
      preValue (C.gates.take j) r (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true →
        preValue (C.gates.take j) (atGate C.gates j)
          (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) = true)
    (hremove : r.op = GateOp.or ∨ preValue (C.gates.take j) r
      (doubleRow (Fin.castAdd N p₀) (Fin.natAdd N l₀)) = false) :
    ∃ D : Circuit, Admissible N I D ∧ D.size ≤ C.size ∧
      (dirtySites N I D).card < (dirtySites N I C).card := by
  obtain ⟨hj,hn,hjo,_⟩ := (mem_dirtySites N I C j p₀ l₀).mp hd
  let D := replaceGate C j r
  have hm : Monotone2 D := replace_monotone C j r h.1 hop hlen
  have hr : ReadsBack (N+N) D := replace_reads_back _ C j r h.2.1 hback
  have hf := (boundary_iff N I D hm).mpr
    ⟨fun p l hi => replace_preserves_positive N I C j r hj h hcrit p l hi,hneg⟩
  have hs : ∀ k < D.gates.length, (gateAt D k).op = GateOp.and →
      ∀ i : Fin (N+N), (D.wires (singletonRow i)).getD (N+N+k) false = false := by
    intro k hk ho i
    have hk' : k < C.gates.length := by simpa [D,replaceGate] using hk
    have ho' := replacement_and_was_and C j k r hj hjo ho
    have hb := replace_wires_below C j r hj h.1 (singletonRow i) (hsing i)
    have he := h.2.2.2 k hk' ho' i
    cases hv : (D.wires (singletonRow i)).getD (N+N+k) false with
    | false => rfl
    | true =>
      have hh := hb.2 _ hv
      rw [he] at hh
      cases hh
  have hsub : dirtySites N I D ⊆ dirtySites N I C := by
    rintro ⟨k,p,l⟩ he
    obtain ⟨hk,hi,ho,hv⟩ := (mem_dirtySites N I D k p l).mp he
    have hk' : k < C.gates.length := by simpa [D,replaceGate] using hk
    have ho' := replacement_and_was_and C j k r hj hjo ho
    have hb := replace_wires_below C j r hj h.1
      (doubleRow (Fin.castAdd N p) (Fin.natAdd N l)) (hmixed p l hi)
    exact (mem_dirtySites N I C k p l).mpr ⟨hk',hi,ho',hb.2 _ hv⟩
  have hnot : (j,p₀,l₀) ∉ dirtySites N I D := by
    intro he
    obtain ⟨_,_,ho,hv⟩ := (mem_dirtySites N I D j p₀ l₀).mp he
    rcases hremove with hor | hz
    · change (gateAt (replaceGate C j r) j).op = GateOp.and at ho
      rw [replace_at_self C j r hj,hor] at ho
      cases ho
    · let w := doubleRow (Fin.castAdd N p₀) (Fin.natAdd N l₀)
      have hw : w.length = N+N := by simp [w,doubleRow]
      change ((replaceGate C j r).wires w).getD (N+N+j) false = true at hv
      have he := replace_slot_value C j r hj w
      rw [hw] at he
      rw [he,hz] at hv
      cases hv
  exact ⟨D,⟨hm,hr,hf,hs⟩,le_of_eq (replace_size C j r),
    Finset.card_lt_card ⟨hsub,fun hback => hnot (hback hd)⟩⟩

end PEqualNP.Outside.L_meta_3457_boundary_progress
