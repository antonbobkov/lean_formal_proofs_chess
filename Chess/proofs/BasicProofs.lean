import ChessRules

-- ============================================================
-- BASIC PROOFS ABOUT THE CORE PREDICATES
-- ============================================================
-- Symmetry of WithinOne / KingAttacks, and the consequence that a
-- legal setup keeps the kings non-adjacent — used by downstream proofs.


theorem WithinOne_comm (a b : Nat) : WithinOne a b ↔ WithinOne b a := by
  unfold WithinOne
  rw [Nat.max_comm, Nat.min_comm]


theorem KingAttacks_comm {n : Nat} (a b : Pos n) :
    KingAttacks a b ↔ KingAttacks b a := by
  unfold KingAttacks
  rw [WithinOne_comm a.1.val b.1.val, WithinOne_comm a.2.val b.2.val]
  exact ⟨fun ⟨h, x, y⟩ => ⟨h.symm, x, y⟩, fun ⟨h, x, y⟩ => ⟨h.symm, x, y⟩⟩


-- ============================================================
-- IsLegalSetup ⇒ kings are not adjacent
-- ============================================================
-- If the kings were adjacent, each would attack the other (KingAttacks
-- is symmetric), so the side that ISN'T to move would have its king in
-- check — contradicting `IsLegalSetup`'s no-check clause.  Whichever
-- color is to move, the case-split picks the correct witness.
theorem IsLegalSetup.kings_not_adjacent {n : Nat} {b : Board n}
    (hlegal : IsLegalSetup b) (wp bp : Pos n)
    (hw : b wp = some ⟨.White, .King⟩)
    (hb : b bp = some ⟨.Black, .King⟩) :
    ¬ KingAttacks wp bp := by
  obtain ⟨_, _, hno_check⟩ := hlegal
  intro hattack
  apply hno_check
  cases hturn : b.turn with
  | White =>
    -- opponent of turn is Black; black king is checked by the white king.
    refine ⟨bp, hb, wp, .inr ⟨?_, hattack⟩⟩
    simpa [Color.opponent] using hw
  | Black =>
    -- opponent of turn is White; white king is checked by the black king.
    refine ⟨wp, hw, bp, .inr ⟨?_, (KingAttacks_comm _ _).mp hattack⟩⟩
    simpa [Color.opponent] using hb
