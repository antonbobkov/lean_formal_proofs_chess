import ChessRules
import TRC_FunctionWithInvariant
import HelperLemmas

-- ------------------------------------------------------------
-- INDIVIDUAL PRESERVATION SUB-LEMMAS
-- ------------------------------------------------------------
-- Each of the conjuncts in `LadderShape` has its own preservation lemma
-- below. They are stated independently of `LadderShape` on the result
-- board so that the moveK case (where the new rank may not satisfy the
-- bound `rank.val + 2 < n`) does not block them.

-- One white ply (`applyLadderStep`) flips turn White → Black; one further
-- ply (the black reply) flips Black → White. So the resulting turn is
-- White regardless of which squares the black move uses.
lemma LadderShape_TurnPreserved {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) (bsrc bdst : Pos n) :
    (applyMove (applyLadderStep lsh) bsrc bdst).turn = .White := by
  obtain ⟨turn_white, _⟩ := lsh.unfold
  show (board.turn.opponent).opponent = .White
  rw [turn_white]; rfl

-- A legal black move into the post-white-ply board produces a legal
-- setup — that is the last conjunct of `IsLegalMove`.
lemma LadderShape_LegalSetupPreserved {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    IsLegalSetup (applyMove (applyLadderStep lsh) bsrc bdst) := by
  obtain ⟨_, _, _, _, h_legal⟩ := black_move
  exact h_legal

-- "Every black-occupied square is a king" survives a full White+Black
-- cycle: white's ply is into an empty square (so doesn't introduce any
-- non-king black piece), and black's ply only relocates a black piece.
-- Each ply is handled by `applyMove_PreservesOnlyBlackKing`.
lemma LadderShape_OnlyBlackKingPreserved {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) (bsrc bdst : Pos n) :
    ∀ p k, (applyMove (applyLadderStep lsh) bsrc bdst) p = some ⟨.Black, k⟩ →
           k = .King := by
  obtain ⟨_, _, _, _, _, _, only_bk, _⟩ := lsh.unfold
  have step_only_bk : ∀ p k, (applyLadderStep lsh) p = some ⟨.Black, k⟩ → k = .King :=
    applyMove_PreservesOnlyBlackKing board _ _ only_bk
  exact applyMove_PreservesOnlyBlackKing _ _ _ step_only_bk
