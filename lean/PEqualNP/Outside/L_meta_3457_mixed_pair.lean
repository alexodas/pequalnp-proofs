import PEqualNP.Outside.L_meta_3457_cover_cut

/-!
The mixed-pair cleanliness condition of L-meta-3457 does not force
a star profile. A matching of size two admits a clean (not minimal)
circuit with a gate owning both disjoint edges. This is not a
counterexample to the assigned normalization theorem.
-/

namespace PEqualNP.Outside.L_meta_3457_mixed_pair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

local instance : DecidableEq GateOp := gateOpDecEq

def sample : Circuit :=
  ⟨[⟨GateOp.or, [0,3]⟩, ⟨GateOp.or, [1,2]⟩,
    ⟨GateOp.and, [4,5]⟩, ⟨GateOp.or, [0,1]⟩,
    ⟨GateOp.or, [2,3]⟩, ⟨GateOp.and, [6,7]⟩,
    ⟨GateOp.and, [9,8]⟩], 10⟩

def target (a b c d : Bool) : Bool :=
  (a && c) || (b && d)

theorem computes_matching : ∀ a b c d : Bool,
    sample.eval [a,b,c,d] = target a b c d := by decide

theorem backwards : ReadsBack 4 sample := by decide

theorem singleton_safe :
    ∀ j : Fin 7, (gateAt sample j.val).op = GateOp.and →
      ∀ k : Fin 4, gateVal 4 sample j.val (fun i => decide (i = k)) = false := by
  decide

theorem mixed_safe :
    ∀ j : Fin 7, (gateAt sample j.val).op = GateOp.and →
      gateVal 4 sample j.val (pairInput (0 : Fin 4) 3) = false ∧
      gateVal 4 sample j.val (pairInput (1 : Fin 4) 2) = false := by
  decide

theorem same_side_dirty :
    gateVal 4 sample 2 (pairInput (0 : Fin 4) 1) = true ∧
    gateVal 4 sample 2 (pairInput (2 : Fin 4) 3) = true := by decide

theorem disjoint_owned :
    Owns 4 sample 2 (0 : Fin 4) 2 ∧
    Owns 4 sample 2 (1 : Fin 4) 3 := by decide

def matching : SimpleGraph (Fin 4) := edgeGraph 4 [(0,2),(1,3)]

theorem not_star : ¬ HasStarProfile 4 matching sample := by
  intro h
  have h₁ : matching.Adj (0 : Fin 4) 2 := by
    change (edgeGraph 4 [(0,2),(1,3)]).Adj 0 2
    decide
  have h₂ : matching.Adj (1 : Fin 4) 3 := by
    change (edgeGraph 4 [(0,2),(1,3)]).Adj 1 3
    decide
  rcases h 2 (by decide) (by decide) with hn | ⟨c, hc⟩
  · exact hn 0 2 h₁ disjoint_owned.1
  · have ha := hc 0 2 h₁ disjoint_owned.1
    have hb := hc 1 3 h₂ disjoint_owned.2
    fin_cases c <;> simp_all

end PEqualNP.Outside.L_meta_3457_mixed_pair
