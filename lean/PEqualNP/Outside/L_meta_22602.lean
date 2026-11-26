import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22602_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [5, 11]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [14, 13]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [6, 17]⟩, ⟨GateOp.and, [3, 18]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [19, 20]⟩], 21⟩

theorem shape : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem represents : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (2072186 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22602_aux

theorem PEqualNP.Outside.L_meta_22602 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (2072186 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_22602_aux.circ, PEqualNP.Outside.L_meta_22602_aux.shape, by decide, PEqualNP.Outside.L_meta_22602_aux.represents⟩
