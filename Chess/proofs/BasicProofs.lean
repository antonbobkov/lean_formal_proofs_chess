import ChessRules

-- ============================================================
-- BASIC PROOFS ABOUT THE CORE PREDICATES
-- ============================================================
-- Symmetry of WithinOne / ValidKingMove, and the consequence that a
-- legal setup keeps the kings non-adjacent — used by downstream proofs.


theorem WithinOne_comm (a b : Nat) : WithinOne a b ↔ WithinOne b a := by
  unfold WithinOne
  rw [Nat.max_comm, Nat.min_comm]


theorem ValidKingMove_comm {n : Nat} (a b : Pos n) :
    ValidKingMove a b ↔ ValidKingMove b a := by
  unfold ValidKingMove
  rw [WithinOne_comm a.rank.val b.rank.val, WithinOne_comm a.file.val b.file.val]
  exact ⟨fun ⟨h, x, y⟩ => ⟨h.symm, x, y⟩, fun ⟨h, x, y⟩ => ⟨h.symm, x, y⟩⟩


-- ============================================================
-- IsLegalSetup ⇒ kings are not adjacent
-- ============================================================
-- If the kings were adjacent, each would attack the other (ValidKingMove
-- is symmetric), so the side that ISN'T to move would have its king in
-- check — contradicting `IsLegalSetup`'s no-check clause.  Whichever
-- color is to move, the case-split picks the correct witness.
theorem IsLegalSetup.kings_not_adjacent {n : Nat} {b : Board n}
    (hlegal : IsLegalSetup b) (wp bp : Pos n)
    (hw : b wp = some ⟨.White, .King⟩)
    (hb : b bp = some ⟨.Black, .King⟩) :
    ¬ ValidKingMove wp bp := by
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
    refine ⟨wp, hw, bp, .inr ⟨?_, (ValidKingMove_comm _ _).mp hattack⟩⟩
    simpa [Color.opponent] using hb
