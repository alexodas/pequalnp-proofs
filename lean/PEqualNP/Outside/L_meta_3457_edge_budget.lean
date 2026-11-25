import PEqualNP.Outside.L_meta_3457_rectangles
import PEqualNP.Outside.L_meta_3457_union_budget

/-!
A global edge bound from star roots and two OR support DAGs.
The remaining circuit-specific step is to extract the star roots
from the clean shadow traces with at most two roots per AND.
-/

namespace PEqualNP.Outside.L_meta_3457_edge_budget

open PEqualNP.Outside.L_meta_3457_rectangles
open PEqualNP.Outside.L_meta_3457_union_budget

noncomputable def pointNeighbours (N : ℕ) (I : Fin N → Fin N → Prop)
    (p : Fin N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (I p)

noncomputable def lineNeighbours (N : ℕ) (I : Fin N → Fin N → Prop)
    (l : Fin N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun p => I p l)

theorem point_neighbour_inter_small (N : ℕ) (I : Fin N → Fin N → Prop)
    (hf : C4Free N I) (p q : Fin N) (hn : p ≠ q) :
    (pointNeighbours N I p ∩ pointNeighbours N I q).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro l hl m hm
  have h₁ : I p l ∧ I q l := by simpa [pointNeighbours] using hl
  have h₂ : I p m ∧ I q m := by simpa [pointNeighbours] using hm
  by_contra hne
  exact hf p q l m hn hne ⟨h₁.1,h₂.1,h₁.2,h₂.2⟩

theorem line_neighbour_inter_small (N : ℕ) (I : Fin N → Fin N → Prop)
    (hf : C4Free N I) (l m : Fin N) (hn : l ≠ m) :
    (lineNeighbours N I l ∩ lineNeighbours N I m).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have h₁ : I p l ∧ I p m := by simpa [lineNeighbours] using hp
  have h₂ : I q l ∧ I q m := by simpa [lineNeighbours] using hq
  by_contra hne
  exact hf p q l m hne hn ⟨h₁.1,h₁.2,h₂.1,h₂.2⟩

noncomputable def edgePairs (N : ℕ) (I : Fin N → Fin N → Prop) :
    Finset (Fin N × Fin N) := by
  classical
  exact Finset.univ.filter (fun e => I e.1 e.2)

/-- Gathering roots by centre can only reduce their count, since
    the same wire at the same centre need not be paid for twice. -/
theorem grouped_roots_bound {β γ : Type*} [Fintype γ] [DecidableEq γ]
    (T : Finset β) (centre : β → γ) (wire : β → ℕ) :
    (∑ c : γ, (((T.filter (fun t => centre t = c)).image wire)).card) ≤ T.card := by
  classical
  calc
    (∑ c : γ, (((T.filter (fun t => centre t = c)).image wire)).card) ≤
        ∑ c : γ, (T.filter (fun t => centre t = c)).card := by
      apply Finset.sum_le_sum
      intro c hc
      exact Finset.card_image_le
    _ = T.card := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
      simp

/-- Every incidence is covered by a point-centred or line-centred
    root. Each OR node can be charged at most once per side. -/
theorem edge_budget (N : ℕ) (I : Fin N → Fin N → Prop)
    (hf : C4Free N I)
    (SP SL : ℕ → Finset (Fin N))
    (RP RL : Fin N → Finset ℕ)
    (Allowed : ℕ → Prop) (m : ℕ)
    (hSP : ∀ j, 1 < (SP j).card → ∃ a b, a < j ∧ b < j ∧ SP j = SP a ∪ SP b)
    (hSL : ∀ j, 1 < (SL j).card → ∃ a b, a < j ∧ b < j ∧ SL j = SL a ∪ SL b)
    (hAP : ∀ j, 1 < (SP j).card → Allowed j)
    (hAL : ∀ j, 1 < (SL j).card → Allowed j)
    (hRP : ∀ p, RP p ⊆ Finset.range m)
    (hRL : ∀ l, RL l ⊆ Finset.range m)
    (hsubP : ∀ p j, j ∈ RP p → SL j ⊆ pointNeighbours N I p)
    (hsubL : ∀ l j, j ∈ RL l → SP j ⊆ lineNeighbours N I l)
    (hcover : ∀ p l, I p l →
      l ∈ (RP p).biUnion SL ∨ p ∈ (RL l).biUnion SP) :
    (edgePairs N I).card ≤
      (∑ p : Fin N, (RP p).card) + (∑ l : Fin N, (RL l).card) +
        2 * budget Allowed m := by
  classical
  let A : Finset (Fin N × Fin N) := Finset.univ.biUnion
    (fun p : Fin N => ((RP p).biUnion SL).image (fun l => (p,l)))
  let B : Finset (Fin N × Fin N) := Finset.univ.biUnion
    (fun l : Fin N => ((RL l).biUnion SP).image (fun p => (p,l)))
  have hsub : edgePairs N I ⊆ A ∪ B := by
    rintro ⟨p,l⟩ h
    have hi : I p l := by simpa [edgePairs] using h
    rcases hcover p l hi with hp | hl
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_univ _,Finset.mem_image.mpr ⟨l,hp,rfl⟩⟩
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ _,Finset.mem_image.mpr ⟨p,hl,rfl⟩⟩
  have hA : A.card ≤ ∑ p : Fin N, ((RP p).biUnion SL).card := by
    calc
      A.card ≤ ∑ p : Fin N, (((RP p).biUnion SL).image (fun l => (p,l))).card :=
        Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum (fun p _ => Finset.card_image_le)
  have hB : B.card ≤ ∑ l : Fin N, ((RL l).biUnion SP).card := by
    calc
      B.card ≤ ∑ l : Fin N, (((RL l).biUnion SP).image (fun p => (p,l))).card :=
        Finset.card_biUnion_le
      _ ≤ _ := Finset.sum_le_sum (fun l _ => Finset.card_image_le)
  have hp := neighbourhood_union_budget SL (pointNeighbours N I) RP Allowed hSL hAL
    (point_neighbour_inter_small N I hf) m hRP hsubP
  have hl := neighbourhood_union_budget SP (lineNeighbours N I) RL Allowed hSP hAP
    (line_neighbour_inter_small N I hf) m hRL hsubL
  have he := Finset.card_le_card hsub
  have hab := Finset.card_union_le A B
  omega

end PEqualNP.Outside.L_meta_3457_edge_budget
