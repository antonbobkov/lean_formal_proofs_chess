import ChessRules
import TRC_FunctionWithInvariant
import TRC_Invariant_SimpleCases
import TRC_Invariant_PieceLocations
import TRC_Q_Lemma
import TRC_Invariant_BlackEmpty
import TRC_Invariant_KingRank
import HelperLemmas
import LadderStepIsLegal
import Mathlib.Data.Finset.Card

-- ============================================================
-- LADDER SHAPE PRESERVATION
-- ============================================================
-- After one White ply (`applyLadderStep`) followed by any legal Black reply,
-- the resulting board still satisfies `LadderShape` for the advanced
-- rank and the next phase. This is the inductive invariant that drives
-- `ladderMate_termination` below.


-- ------------------------------------------------------------
-- HELPERS FOR WHITE-PIECE PRESERVATION
-- ------------------------------------------------------------
-- Used inline by `LadderShape.preservation` (the per-phase plumbing
-- for "white piece p is unchanged across the full White+Black cycle").
-- Both rely on the simplifying assumption that black's reply targets
-- an empty square (no white piece is captured); ruling that out is
-- still future work.

-- Helper: bsrc carries a black piece (since `IsLegalMove`'s piece
-- belongs to the side to move, which is `(applyLadderStep lsh).turn = Black`).
private lemma blackMove_src_isBlack {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ∃ k, (applyLadderStep lsh) bsrc = some ⟨.Black, k⟩ := by
  obtain ⟨turn_white, _⟩ := lsh.unfold
  obtain ⟨piece, hat_src, _⟩ := black_move
  have h_turn : (applyLadderStep lsh).turn = .Black := by
    show board.turn.opponent = .Black
    rw [turn_white]; rfl
  rw [h_turn] at hat_src
  exact ⟨piece, hat_src⟩

-- Closes a "white piece preservation" goal using a step-board hypothesis
-- `h_pc_at : (applyLadderStep lsh) p = some ⟨.White, _⟩` and the fact that
-- bsrc carries a black piece.
private lemma whitePiecePreserved {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    {lsh : LadderShape board rank φ} {bsrc bdst p : Pos n} {pc : Piece}
    (h_pc_at : (applyLadderStep lsh) p = some pc)
    (h_white : pc.color = .White)
    (h_bsrc_black : ∃ k, (applyLadderStep lsh) bsrc = some ⟨.Black, k⟩)
    (bdst_empty : (applyLadderStep lsh) bdst = none) :
    (applyMove (applyLadderStep lsh) bsrc bdst) p = some pc := by
  obtain ⟨k, hbsrc⟩ := h_bsrc_black
  refine NoCaptureMove_PreservesPiece _ _ _ _ _ h_pc_at ?_ bdst_empty
  intro heq
  rw [heq, h_pc_at] at hbsrc
  rw [Option.some.injEq] at hbsrc
  have : pc.color = (⟨.Black, k⟩ : Piece).color := congrArg Piece.color hbsrc
  rw [h_white] at this
  cases this

-- ------------------------------------------------------------
-- PRESERVATION THEOREM
-- ------------------------------------------------------------
-- The `hMoveK` hypothesis supplies the next-rank bound when φ = moveK:
-- the conclusion uses `nextRank rank φ lsh.hRfits`, which on the moveK
-- ply produces ⟨rank.val + 1, _⟩, and `LadderShape` then requires
-- (rank+1).val + 2 < n, i.e. rank.val + 3 < n. Callers (e.g.
-- `ladderMate_termination`) must ensure this — at the boundary
-- rank.val + 2 = n − 1 the bound fails, but at that point Black is
-- already checkmated so preservation is not invoked.
theorem LadderShape.preservation {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ)
    (hMoveK : φ = .moveK → rank.val + 3 < n)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    LadderShape
      (applyMove (applyLadderStep lsh) bsrc bdst)
      (nextRank rank φ lsh.hRfits)
      (nextPhase φ) := by
  have h_turn    := LadderShape_TurnPreserved lsh bsrc bdst
  have h_legal   := LadderShape_LegalSetupPreserved lsh black_move
  have h_only_bk := LadderShape_OnlyBlackKingPreserved lsh bsrc bdst
  have hbsrc     := blackMove_src_isBlack lsh black_move
  have bdst_empty := BlackReply_DstEmpty lsh black_move
  have h_card := whiteCount_le_three_after_cycle (bsrc := bsrc) lsh bdst_empty
  cases φ with
  | moveRb =>
    obtain ⟨hK, hRb, hRa⟩ := applyLadderStep_PiecesAt_moveRb lsh
    have hK'  := whitePiecePreserved hK  rfl hbsrc bdst_empty
    have hRb' := whitePiecePreserved hRb rfl hbsrc bdst_empty
    have hRa' := whitePiecePreserved hRa rfl hbsrc bdst_empty
    have hQ' := Q_of_subset_card_le _ .White
      ⟨.King, hK'⟩ ⟨.Rook, hRb'⟩ ⟨.Rook, hRa'⟩
      (ladderPos_pairwise_distinct rank .moveRa lsh.hRfits)
      h_card
    show LadderShape (applyMove (applyLadderStep lsh) bsrc bdst) rank .moveRa
    unfold LadderShape
    rw [dif_pos lsh.hRfits]
    refine ⟨h_turn, hK', hRb', hRa', hQ', ?_, h_only_bk, h_legal⟩
    · exact LadderMove_BlackKingAboveNextRa_moveRb lsh black_move
  | moveRa =>
    obtain ⟨hK, hRb, hRa⟩ := applyLadderStep_PiecesAt_moveRa lsh
    have hK'  := whitePiecePreserved hK  rfl hbsrc bdst_empty
    have hRb' := whitePiecePreserved hRb rfl hbsrc bdst_empty
    have hRa' := whitePiecePreserved hRa rfl hbsrc bdst_empty
    have hQ' := Q_of_subset_card_le _ .White
      ⟨.King, hK'⟩ ⟨.Rook, hRb'⟩ ⟨.Rook, hRa'⟩
      (ladderPos_pairwise_distinct rank .moveK lsh.hRfits)
      h_card
    show LadderShape (applyMove (applyLadderStep lsh) bsrc bdst) rank .moveK
    unfold LadderShape
    rw [dif_pos lsh.hRfits]
    refine ⟨h_turn, hK', hRb', hRa', hQ', ?_, h_only_bk, h_legal⟩
    · exact LadderMove_BlackKingAboveNextRa_moveRa lsh black_move
  | moveK =>
    have hRoom := hMoveK rfl
    obtain ⟨hK, hRb, hRa⟩ := applyLadderStep_PiecesAt_moveK lsh hRoom
    have hK'  := whitePiecePreserved hK  rfl hbsrc bdst_empty
    have hRb' := whitePiecePreserved hRb rfl hbsrc bdst_empty
    have hRa' := whitePiecePreserved hRa rfl hbsrc bdst_empty
    let rank' : Fin n := ⟨rank.val + 1, by omega⟩
    have h' : rank'.val + 2 < n := hRoom
    have hQ' := Q_of_subset_card_le _ .White
      ⟨.King, hK'⟩ ⟨.Rook, hRb'⟩ ⟨.Rook, hRa'⟩
      (ladderPos_pairwise_distinct rank' .moveRb h')
      h_card
    show LadderShape (applyMove (applyLadderStep lsh) bsrc bdst) rank' .moveRb
    unfold LadderShape
    rw [dif_pos h']
    refine ⟨h_turn, hK', hRb', hRa', hQ', ?_, h_only_bk, h_legal⟩
    · exact LadderMove_BlackKingAboveNextRa_moveK lsh hRoom black_move
