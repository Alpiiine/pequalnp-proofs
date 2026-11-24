import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2658_1
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      0 < n → PEqualNP.MetaComplexity.Monotone2 C →
      (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ u v : Fin n, ¬ G.Adj u v →
        (C.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD (n + j) false = false) →
      ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g →
        g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD (n + j) false = true →
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)
    (h2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔
          ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) ∧
        D.size ≤ C.size ∧ ∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
        D.gates[j]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ u v : Fin n, ¬ G.Adj u v →
        (D.wires (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v))).getD (n + j) false = false) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x4 : Fin x1) (x5 : Fin x1), x2.Adj x4 x5) → (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x5 ≠ x7 → x5 ≠ x8 → x6 ≠ x7 → x6 ≠ x8 → x7 ≠ x8 → x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → ¬x2.Adj x8 x5) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin x1 → Bool), x3.eval (List.ofFn x7) = Bool.true ↔ ∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ (∀ (x9 : Fin x1 → Bool), x8.eval (List.ofFn x9) = Bool.true ↔ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) ∧ x8.size ≤ x3.size ∧ ∀ (x9 : ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate), x8.gates[x9]? = Option.some x10 → x10.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x13 : Fin x1 → Bool), (x8.wires (List.ofFn x13)).getD (x1 + x9) Bool.false = Bool.true → ∃ (x15 : Fin x1) (x16 : Fin x1), x2.Adj x15 x16 ∧ x13 x15 = Bool.true ∧ x13 x16 = Bool.true := by
  intro n G C hE hC4 hM hcomp
  obtain ⟨D, hMD, hcD, hsD, hpD⟩ := h2 n G C hE hC4 hM hcomp
  have hn : 0 < n := by
    obtain ⟨u, v, huv⟩ := hE
    exact Nat.zero_lt_of_lt u.isLt
  exact ⟨D, hMD, hcD, hsD, h1 n G D hn hMD hpD⟩
