import ChessRules
import TRC_FunctionWithInvariant
import TRC_Invariant_PieceLocations
import TRC_Invariant_BlackEmpty
import TRC_Invariant_CheckLocations
import HelperLemmas
import LadderStepIsLegal

-- ============================================================
-- BLACK KING'S RANK STAYS STRICTLY ABOVE ROOK A
-- ============================================================
-- After a full White ply (`applyLadderStep`) followed by any legal Black
-- reply, the black king's rank is strictly greater than the *next-state*
-- rookA rank. This file packages that conclusion phase by phase, closing
-- the `black_loc` conjunct of `LadderShape.preservation` (currently
-- three `sorry`s, one per phase).
--
-- ── Strategy (Ra.rank below denotes the *pre-move* rookA rank) ──
--   1. `BlackReply_DstBounds` (in `TRC_Invariant_BlackEmpty`):
--        bdst.file ≥ 1 and bdst.rank ≥ Ra.rank.
--   We then exclude the four boundary cases:
--     • file = 1, rank = Ra.rank      → `BlackReply_NotAtFileOneRaRank`
--                                         (already proved, in `TRC_Invariant_BlackEmpty`)
--     • file = 1, rank > Ra.rank      → `BlackReply_NotAboveRaRank_FileOne`
--     • file ≥ 2, rank = Ra.rank      → `BlackReply_NotAtRaRank_FileGe2`
--     • file ≥ 2, rank = Ra.rank + 1  → `BlackReply_NotAtRaRankPlusOne_FileGe2_moveRa`
--                                         (only needed in phase moveRa, where the
--                                          post-move Ra.rank is one greater than the
--                                          pre-move Ra.rank)
--   3. Combine the bounds + exclusions into `BlackReply_DstRank_gt_NextRa_*`,
--      one per phase.
--   4. Lift to the `LadderShape` invariant form (any `bp` carrying the
--      black king on the post-black-move board) using uniqueness of the
--      black king. These are the plug-ins for the three `sorry`s in
--      `LadderShape.preservation`.

-- ------------------------------------------------------------
-- DESTINATION EXCLUSIONS  (each says: a legal Black reply cannot
-- land on the named region, because doing so would leave Black in
-- check on the post-black-move board, contradicting `IsLegalSetup`).
-- ------------------------------------------------------------

-- (file = 1, rank > pre-Ra.rank): the post-step Rb sits at (rank+1, 1)
-- in every phase and Ra.rank ≥ rank+1, so a black king above pre-Ra.rank
-- on file 1 would be attacked vertically by Rb. Line of sight is supplied
-- by `LadderMove_NoWhiteAboveRb` and the rook is preserved across the
-- (non-capturing) Black reply.
lemma BlackReply_NotAboveRaRank_FileOne {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ¬ (bdst.file.val = 1 ∧
       (rookAPos rank φ lsh.hRfits).rank.val < bdst.rank.val) := by
  sorry

-- (file ≥ 2, rank = pre-Ra.rank): in moveRb / moveRa the post-step Rb at
-- (rank+1, 1) attacks rightward on rank+1 = pre-Ra.rank; in moveK the
-- post-step Ra at (rank+2, 0) attacks rightward on rank+2 = pre-Ra.rank.
-- Line of sight is supplied per phase by `LadderMove_NoWhiteRightOfRb_*`
-- / `LadderMove_NoWhiteRightOfRa_moveK`.
lemma BlackReply_NotAtRaRank_FileGe2 {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ¬ (2 ≤ bdst.file.val ∧
       bdst.rank.val = (rookAPos rank φ lsh.hRfits).rank.val) := by
  sorry

-- moveRa-only: (file ≥ 2, rank = pre-Ra.rank + 1). After Ra's ply the
-- post-step Ra sits at (rank+2, 0) = (pre-Ra.rank + 1, 0); it attacks
-- rightward on that rank, with line of sight from
-- `LadderMove_NoWhiteRightOfRa_moveRa`.
lemma BlackReply_NotAtRaRankPlusOne_FileGe2_moveRa
    {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveRa)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ¬ (2 ≤ bdst.file.val ∧
       bdst.rank.val = (rookAPos rank .moveRa lsh.hRfits).rank.val + 1) := by
  sorry

-- ------------------------------------------------------------
-- DESTINATION RANK STRICTLY ABOVE NEXT-STATE Ra
-- ------------------------------------------------------------
-- For each input phase, combine `BlackReply_DstBounds` with the four
-- (or three) exclusions above to conclude `bdst.rank > next-state-Ra.rank`.

-- Phase moveRb (next state .moveRa, same base rank): next-Ra.rank = rank+1.
-- Equal to pre-Ra.rank, so three exclusions suffice (no rank+1 step).
lemma BlackReply_DstRank_gt_NextRa_moveRb {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveRb)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    (rookAPos rank .moveRa lsh.hRfits).rank.val < bdst.rank.val := by
  sorry

-- Phase moveRa (next state .moveK, same base rank): next-Ra.rank = rank+2.
-- One greater than pre-Ra.rank = rank+1, so the extra
-- `BlackReply_NotAtRaRankPlusOne_FileGe2_moveRa` exclusion is needed to
-- close the rank = rank+1, file ≥ 2 case that previously was permissible.
lemma BlackReply_DstRank_gt_NextRa_moveRa {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveRa)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    (rookAPos rank .moveK lsh.hRfits).rank.val < bdst.rank.val := by
  sorry

-- Phase moveK (next state .moveRb at rank' = rank + 1): next-Ra.rank
-- = rank' + 1 = rank + 2. Equal to pre-Ra.rank, so the same three
-- exclusions used in moveRb close all boundary cases.
lemma BlackReply_DstRank_gt_NextRa_moveK {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveK)
    (hRoom : rank.val + 3 < n)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    let rank' : Fin n := ⟨rank.val + 1, by omega⟩
    let h' : rank'.val + 2 < n := hRoom
    (rookAPos rank' .moveRb h').rank.val < bdst.rank.val := by
  sorry

-- ------------------------------------------------------------
-- INVARIANT PRESERVATION  (plug-ins for the three `sorry`s in
-- `LadderShape.preservation`)
-- ------------------------------------------------------------
-- On the post-black-move board the only black piece is the (unique)
-- black king sitting at bdst, so the `bdst.rank > next-Ra.rank` bound
-- above lifts to "every bp carrying the black king has rank > next-Ra.rank".

lemma LadderMove_BlackKingAboveNextRa_moveRb {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveRb)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ∀ bp,
      (applyMove (applyLadderStep lsh) bsrc bdst) bp =
        some ⟨.Black, .King⟩ →
      (rookAPos rank .moveRa lsh.hRfits).rank < bp.rank := by
  sorry

lemma LadderMove_BlackKingAboveNextRa_moveRa {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveRa)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ∀ bp,
      (applyMove (applyLadderStep lsh) bsrc bdst) bp =
        some ⟨.Black, .King⟩ →
      (rookAPos rank .moveK lsh.hRfits).rank < bp.rank := by
  sorry

lemma LadderMove_BlackKingAboveNextRa_moveK {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveK)
    (hRoom : rank.val + 3 < n)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    let rank' : Fin n := ⟨rank.val + 1, by omega⟩
    let h' : rank'.val + 2 < n := hRoom
    ∀ bp,
      (applyMove (applyLadderStep lsh) bsrc bdst) bp =
        some ⟨.Black, .King⟩ →
      (rookAPos rank' .moveRb h').rank < bp.rank := by
  sorry
