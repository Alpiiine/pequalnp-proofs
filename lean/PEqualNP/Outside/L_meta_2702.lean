import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2702

open PEqualNP.MetaComplexity.NestedCover

-- The cover number of a graph whose edges all meet D or lie in the matching M:
-- a least cover K splits as K inter D, the outside neighbours of D minus K, and one end
-- of each matching edge that those neighbours leave untouched.
theorem core (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
    (D : Finset (Fin 11)) (M : Finset (Fin 11 × Fin 11))
    (hM1 : ∀ p ∈ M, p.1 ∉ D ∧ p.2 ∉ D)
    (hM2 : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2)
    (hE : ∀ x y : Fin 11, G.Adj x y → x ∈ D ∨ y ∈ D ∨ (x, y) ∈ M ∨ (y, x) ∈ M)
    (K : Finset (Fin 11)) (hK : IsMinCover G K)
    (N : Finset (Fin 11))
    (hN : N = {v ∈ Finset.univ \ D | ∃ d ∈ D \ (K ∩ D), G.Adj d v})
    (P : Finset (Fin 11 × Fin 11))
    (hP : P = {p ∈ M | G.Adj p.1 p.2 ∧ p.1 ∉ N ∧ p.2 ∉ N}) :
    K.card = (K ∩ D).card + N.card + P.card := by
  obtain ⟨hcov, hmin⟩ := hK
  have memN : ∀ v, v ∈ N ↔ v ∉ D ∧ ∃ d ∈ D, d ∉ K ∧ G.Adj d v := by
    intro v
    subst hN
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_inter]
    constructor
    · rintro ⟨hv, d, ⟨hd, hdK⟩, hadj⟩
      exact ⟨hv, d, hd, fun h => hdK ⟨h, hd⟩, hadj⟩
    · rintro ⟨hv, d, hd, hdK, hadj⟩
      exact ⟨hv, d, ⟨hd, fun h => hdK h.1⟩, hadj⟩
  have memP : ∀ p, p ∈ P ↔ p ∈ M ∧ G.Adj p.1 p.2 ∧ p.1 ∉ N ∧ p.2 ∉ N := by
    intro p
    subst hP
    simp only [Finset.mem_filter]
  have hNK : N ⊆ K := by
    intro v hv
    obtain ⟨_, d, _, hdK, hadj⟩ := (memN v).1 hv
    rcases hcov hadj with h | h
    · exact absurd h hdK
    · exact h
  have hND : ∀ v ∈ N, v ∉ D := fun v hv => ((memN v).1 hv).1
  obtain ⟨rep, hrep⟩ : ∃ rep : Fin 11 × Fin 11 → Fin 11,
      ∀ p, (p.1 ∈ K → rep p = p.1) ∧ (p.1 ∉ K → rep p = p.2) :=
    ⟨fun p => if p.1 ∈ K then p.1 else p.2, fun p =>
      ⟨fun h => by simp only [h, ite_true], fun h => by simp only [h, ite_false]⟩⟩
  have hrep_or : ∀ p : Fin 11 × Fin 11, rep p = p.1 ∨ rep p = p.2 := by
    intro p
    by_cases h : p.1 ∈ K
    · exact Or.inl ((hrep p).1 h)
    · exact Or.inr ((hrep p).2 h)
  have hrepK : ∀ p ∈ P, rep p ∈ K := by
    intro p hp
    obtain ⟨_, hadj, _, _⟩ := (memP p).1 hp
    by_cases h : p.1 ∈ K
    · rw [(hrep p).1 h]
      exact h
    · rw [(hrep p).2 h]
      rcases hcov hadj with h' | h'
      · exact absurd h' h
      · exact h'
  have hrepinj : Set.InjOn rep (P : Set (Fin 11 × Fin 11)) := by
    intro p hp q hq hpq
    by_contra hne
    have hpM := ((memP p).1 (Finset.mem_coe.1 hp)).1
    have hqM := ((memP q).1 (Finset.mem_coe.1 hq)).1
    obtain ⟨h1, h2, h3, h4⟩ := hM2 p hpM q hqM hne
    rcases hrep_or p with hp' | hp' <;> rcases hrep_or q with hq' | hq' <;>
      rw [hp', hq'] at hpq
    · exact h1 hpq
    · exact h2 hpq
    · exact h3 hpq
    · exact h4 hpq
  have hQcard : (P.image rep).card = P.card := Finset.card_image_of_injOn hrepinj
  have hQK : P.image rep ⊆ K := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv
    exact hrepK p hp
  have hQD : ∀ v ∈ P.image rep, v ∉ D ∧ v ∉ N := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨hpM, _, hn1, hn2⟩ := (memP p).1 hp
    obtain ⟨hd1, hd2⟩ := hM1 p hpM
    rcases hrep_or p with h | h
    · rw [h]
      exact ⟨hd1, hn1⟩
    · rw [h]
      exact ⟨hd2, hn2⟩
  have hdis1 : Disjoint (K ∩ D) N := by
    rw [Finset.disjoint_left]
    intro v hv hvN
    exact hND v hvN (Finset.mem_inter.1 hv).2
  have hdis2 : Disjoint ((K ∩ D) ∪ N) (P.image rep) := by
    rw [Finset.disjoint_left]
    intro v hv hvQ
    obtain ⟨hvD, hvN⟩ := hQD v hvQ
    rcases Finset.mem_union.1 hv with h | h
    · exact hvD (Finset.mem_inter.1 h).2
    · exact hvN h
  have hsub : (K ∩ D) ∪ N ∪ P.image rep ⊆ K :=
    Finset.union_subset (Finset.union_subset Finset.inter_subset_left hNK) hQK
  have hlow : (K ∩ D).card + N.card + P.card ≤ K.card := by
    have h := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis2, Finset.card_union_of_disjoint hdis1, hQcard] at h
    exact h
  have memT : ∀ v, v ∈ (K ∩ D) ∪ N ∪ P.image Prod.fst ↔
      (v ∈ K ∧ v ∈ D) ∨ v ∈ N ∨ ∃ p ∈ P, p.1 = v := by
    intro v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_image, or_assoc]
  have key : ∀ a b : Fin 11, G.Adj a b → a ∈ D →
      a ∈ (K ∩ D) ∪ N ∪ P.image Prod.fst ∨ b ∈ (K ∩ D) ∪ N ∪ P.image Prod.fst := by
    intro a b hab haD
    by_cases haK : a ∈ K
    · exact Or.inl ((memT a).2 (Or.inl ⟨haK, haD⟩))
    · refine Or.inr ((memT b).2 ?_)
      by_cases hbD : b ∈ D
      · have hbK : b ∈ K := by
          rcases hcov hab with h | h
          · exact absurd h haK
          · exact h
        exact Or.inl ⟨hbK, hbD⟩
      · exact Or.inr (Or.inl ((memN b).2 ⟨hbD, a, haD, haK, hab⟩))
  have key2 : ∀ a b : Fin 11, G.Adj a b → (a, b) ∈ M →
      a ∈ (K ∩ D) ∪ N ∪ P.image Prod.fst ∨ b ∈ (K ∩ D) ∪ N ∪ P.image Prod.fst := by
    intro a b hab hM
    by_cases ha : a ∈ N
    · exact Or.inl ((memT a).2 (Or.inr (Or.inl ha)))
    · by_cases hb : b ∈ N
      · exact Or.inr ((memT b).2 (Or.inr (Or.inl hb)))
      · exact Or.inl ((memT a).2 (Or.inr (Or.inr ⟨(a, b), (memP (a, b)).2 ⟨hM, hab, ha, hb⟩, rfl⟩)))
  have hcovT : G.IsVertexCover (↑((K ∩ D) ∪ N ∪ P.image Prod.fst) : Set (Fin 11)) := by
    intro x y hadj
    simp only [Finset.mem_coe]
    rcases hE x y hadj with h | h | h | h
    · exact key x y hadj h
    · exact (key y x hadj.symm h).symm
    · exact key2 x y hadj h
    · exact (key2 y x hadj.symm h).symm
  have hup : K.card ≤ (K ∩ D).card + N.card + P.card := by
    have h1 := hmin _ hcovT
    have h2 := Finset.card_union_le ((K ∩ D) ∪ N) (P.image Prod.fst)
    have h3 := Finset.card_union_le (K ∩ D) N
    have h4 : (P.image Prod.fst).card ≤ P.card := Finset.card_image_le
    omega
  omega

theorem pairsOutside : ∀ p ∈ ({(1, 4), (2, 5), (6, 7)} : Finset (Fin 11 × Fin 11)),
    p.1 ∉ ({3, 8, 9, 10} : Finset (Fin 11)) ∧ p.2 ∉ ({3, 8, 9, 10} : Finset (Fin 11)) := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem pairsApart : ∀ p ∈ ({(1, 4), (2, 5), (6, 7)} : Finset (Fin 11 × Fin 11)),
    ∀ q ∈ ({(1, 4), (2, 5), (6, 7)} : Finset (Fin 11 × Fin 11)), p ≠ q →
      p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 := by
  intro p hp q hq hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hne
      | decide

end PEqualNP.Outside.L_meta_2702

theorem PEqualNP.Outside.L_meta_2702 : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj],   have x3 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};   have x4 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};   (∀ (x5 x6 : Fin (11 : ℕ)), x1.Adj x5 x6 → x5 ∈ x3 ∨ x6 ∈ x3 ∨ (x5, x6) ∈ x4 ∨ (x6, x5) ∈ x4) →     ∀ (x6 : Finset (Fin (11 : ℕ))),       PEqualNP.MetaComplexity.NestedCover.IsMinCover x1 x6 →         ∃ x8 ⊆ x3,           (∀ x9 ∈ x3 \ x8, ∀ x11 ∈ x3 \ x8, ¬x1.Adj x9 x11) ∧             have x9 : Finset (Fin (11 : ℕ)) := {x9 ∈ Finset.univ \ x3 | ∃ x10 ∈ x3 \ x8, x1.Adj x10 x9};             have x10 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x10 ∈ x4 | x1.Adj x10.1 x10.2 ∧ x10.1 ∉ x9 ∧ x10.2 ∉ x9};             x6.card = x8.card + x9.card + x10.card := by
  intro G _
  dsimp only
  intro hE K hK
  refine ⟨K ∩ {3, 8, 9, 10}, Finset.inter_subset_right, ?_, ?_⟩
  · intro a ha b hb hadj
    rw [Finset.mem_sdiff] at ha hb
    rcases hK.1 hadj with h | h
    · exact ha.2 (Finset.mem_inter.2 ⟨h, ha.1⟩)
    · exact hb.2 (Finset.mem_inter.2 ⟨h, hb.1⟩)
  · exact PEqualNP.Outside.L_meta_2702.core G {3, 8, 9, 10} {(1, 4), (2, 5), (6, 7)}
      PEqualNP.Outside.L_meta_2702.pairsOutside PEqualNP.Outside.L_meta_2702.pairsApart
      hE K hK _ rfl _ rfl
