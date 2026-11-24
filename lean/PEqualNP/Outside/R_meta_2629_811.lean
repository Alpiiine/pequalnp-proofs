import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2629_811
    (h1 : ∀ (n : ℕ) (f : (Fin n → Bool) → Bool)
      (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n),
      PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = f →
      (∀ s, PEqualNP.MetaComplexity.HasCircuitSize n f s → C.size ≤ s) →
      (∃ x y, f (Function.update x v false) ≠ f (Function.update y v false)) →
      2 ≤ (C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val &&
          !(g.op.eval [true, false])).length →
      ∃ s, s + 4 ≤ C.size ∧ PEqualNP.MetaComplexity.HasCircuitSize n
        (fun x => f (Function.update x v false)) s)
    (h2 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ (∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∃ x18 ∈ x7 x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18 := by
  classical
  intro n G inst S C
  dsimp only
  intro hdeg hcycle hS hE hF hf hmin hr hwit
  obtain ⟨v, hv, hcount, hnot⟩ := hwit
  let readers := C.gates.filter fun g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
  change readers.length = 2 at hcount
  change ∃ g ∈ readers, g.op = PEqualNP.CircuitLowerBounds.GateOp.not at hnot
  by_cases hor : ∃ g ∈ readers, g.op = PEqualNP.CircuitLowerBounds.GateOp.or
  · exact h2 n G S C hdeg hcycle hS hE hF hf hmin hr ⟨v, hv, hcount, hnot, hor⟩
  have hread : 2 ≤ (C.gates.filter fun g =>
      (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val &&
        !(g.op.eval [true, false])).length := by
    have heq : (C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val &&
          !(g.op.eval [true, false])) = readers := by
      apply List.filter_congr
      intro g hg
      by_cases hmem : (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val = true
      · have hgor : g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or := by
          intro he
          exact hor ⟨g, List.mem_filter.mpr ⟨hg, hmem⟩, he⟩
        have hop := (hF g hg).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with ha | ho | hn
        · have heval : g.op.eval [true, false] = false := by rw [ha]; rfl
          simp only [heval, Bool.not_false, Bool.and_true]
        · exact (hgor ho).elim
        · have heval : g.op.eval [true, false] = false := by rw [hn]; rfl
          simp only [heval, Bool.not_false, Bool.and_true]
      · simp only [Bool.eq_false_iff.mpr hmem, Bool.false_and]
    simpa only [heq, hcount] using (le_rfl : 2 ≤ 2)
  have hnc : ∃ x y : Fin n → Bool,
      PEqualNP.MetaComplexity.NestedCover.graphFun G S (Function.update x v false) ≠
      PEqualNP.MetaComplexity.NestedCover.graphFun G S (Function.update y v false) := by
    have hvdeg : 1 < (G.neighborSet v).ncard := by rw [hdeg v hv]; decide
    obtain ⟨u, hu, huv⟩ := Set.exists_ne_of_one_lt_ncard hvdeg v
    have hvu : G.Adj v u := hu
    have huS : u ∉ S := hS u v hvu.symm
    have hudeg : 1 < (G.neighborSet u).ncard := by rw [hdeg u huS]; decide
    obtain ⟨w, hw, hwv⟩ := Set.exists_ne_of_one_lt_ncard hudeg v
    refine ⟨fun _ => false, PEqualNP.EdgeOwnership.pairInput u w, ?_⟩
    have hz : PEqualNP.MetaComplexity.NestedCover.graphFun G S
        (Function.update (fun _ => false) v false) = false := by
      have hzero : Function.update (fun _ : Fin n => false) v false = fun _ => false := by
        funext i
        simp [Function.update]
      rw [hzero]
      change (decide (∃ a ∈ S, (false : Bool) = true) ||
        decide (∃ a b, G.Adj a b ∧ (false : Bool) = true ∧ (false : Bool) = true)) = false
      simp
    have ht : PEqualNP.MetaComplexity.NestedCover.graphFun G S
        (Function.update (PEqualNP.EdgeOwnership.pairInput u w) v false) = true := by
      apply Bool.or_eq_true_iff.mpr
      right
      apply decide_eq_true
      refine ⟨u, w, hw, ?_, ?_⟩
      · rw [Function.update_of_ne huv]
        exact decide_eq_true (Or.inl rfl)
      · rw [Function.update_of_ne hwv]
        exact decide_eq_true (Or.inr rfl)
    rw [hz, ht]
    decide
  obtain ⟨s, hs, hc⟩ := h1 n (PEqualNP.MetaComplexity.NestedCover.graphFun G S) C v hF hf hmin hnc hread
  exact ⟨v, hv, s, hs, hc⟩
