import ChessRules
import TRC_FunctionWithInvariant
import TRC_Invariant_SimpleCases
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
-- SHARED BOOKKEEPING FOR THE EXCLUSION LEMMAS
-- ------------------------------------------------------------
-- The three exclusion proofs all assume Black's reply landed at bdst
-- with some forbidden coordinates and derive a contradiction by exhibiting
-- a White rook on the post-black-move board attacking bdst (via
-- `RookCheckUp` / `RookCheckRight`), which contradicts the `IsLegalSetup`
-- "side-not-to-move not in check" clause.

-- The black king on the step board sits at bsrc (the moving piece),
-- and the step board has Black to move. Packaged once for the helpers
-- below so we don't pattern-match `black_move` and lose its name.
private lemma BlackReply_BlackKingAtSrc_StepBoard {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    (applyLadderStep lsh) bsrc = some ⟨.Black, .King⟩ := by
  obtain ⟨piece, hat_src, _⟩ := black_move
  obtain ⟨turn_white, _⟩ := lsh.unfold
  have h_turn_step : (applyLadderStep lsh).turn = .Black := by
    show board.turn.opponent = .Black
    rw [turn_white]; rfl
  rw [h_turn_step] at hat_src
  have hk : piece = .King :=
    LadderMove_PreservesOnlyBlackKing lsh bsrc piece hat_src
  subst hk
  exact hat_src

-- Black king sits at bdst on the post-black-move board.
private lemma BlackReply_BlackKingAtDst {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    (applyMove (applyLadderStep lsh) bsrc bdst) bdst =
      some ⟨.Black, .King⟩ := by
  rw [applyMove_pieces, if_pos rfl]
  exact BlackReply_BlackKingAtSrc_StepBoard lsh black_move

-- A white rook on the step board is still there on the post-black-move
-- board: bsrc carries the (black) moving king and bdst is empty
-- (`BlackReply_DstEmpty`), so neither equals rp.
private lemma BlackReply_RookPreserved {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst)
    {rp : Pos n}
    (h_step : (applyLadderStep lsh) rp = some ⟨.White, .Rook⟩) :
    (applyMove (applyLadderStep lsh) bsrc bdst) rp =
      some ⟨.White, .Rook⟩ := by
  have hbsrc := BlackReply_BlackKingAtSrc_StepBoard lsh black_move
  have bdst_empty := BlackReply_DstEmpty lsh black_move
  have h_rp_ne_bsrc : rp ≠ bsrc := by
    intro heq; subst heq
    rw [hbsrc] at h_step; simp at h_step
  have h_rp_ne_bdst : rp ≠ bdst := by
    intro heq; subst heq
    rw [bdst_empty] at h_step; simp at h_step
  rw [applyMove_pieces, if_neg h_rp_ne_bdst, if_neg h_rp_ne_bsrc]
  exact h_step

-- Pull a post-board white-piece witness back to the step board: a Black
-- ply only relocates the (unique) black king, so any white square on the
-- post board was already a white square on the step board.
private lemma BlackReply_StepWhite_Of_PostWhite {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst)
    {p : Pos n} {k : PieceType}
    (h_post : (applyMove (applyLadderStep lsh) bsrc bdst) p =
              some ⟨.White, k⟩) :
    (applyLadderStep lsh) p = some ⟨.White, k⟩ := by
  have hbsrc := BlackReply_BlackKingAtSrc_StepBoard lsh black_move
  rw [applyMove_pieces] at h_post
  by_cases h1 : p = bdst
  · rw [if_pos h1, hbsrc] at h_post; simp at h_post
  · rw [if_neg h1] at h_post
    by_cases h2 : p = bsrc
    · rw [if_pos h2] at h_post; simp at h_post
    · rw [if_neg h2] at h_post; exact h_post

-- After a legal Black reply, Black is not in check on the post-board:
-- that is the third conjunct of `IsLegalSetup`, transported via the
-- two turn-flips.
private lemma BlackReply_PostBoard_NotInCheck {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ¬ IsCheck (applyMove (applyLadderStep lsh) bsrc bdst) .Black := by
  obtain ⟨_, _, _, _, h_legal⟩ := black_move
  obtain ⟨turn_white, _⟩ := lsh.unfold
  have h_turn_step : (applyLadderStep lsh).turn = .Black := by
    show board.turn.opponent = .Black
    rw [turn_white]; rfl
  obtain ⟨_, _, h_no_check⟩ := h_legal
  have h_b''_opp :
      (applyMove (applyLadderStep lsh) bsrc bdst).turn.opponent = .Black := by
    show (applyLadderStep lsh).turn.opponent.opponent = .Black
    rw [h_turn_step]; rfl
  rw [h_b''_opp] at h_no_check
  exact h_no_check

-- Uniqueness of the black king on the post-board (used as `unique_bk`
-- by `RookCheckUp` / `RookCheckRight`). Pulled out of `IsLegalSetup`
-- on the post-board.
private lemma BlackReply_UniqueBlackKingPost {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ∀ p, (applyMove (applyLadderStep lsh) bsrc bdst) p =
           some ⟨.Black, .King⟩ →
         p = bdst := by
  intro p hp
  have hbdst_post := BlackReply_BlackKingAtDst lsh black_move
  obtain ⟨_, _, _, _, h_legal⟩ := black_move
  obtain ⟨_, ⟨_, _, hbk_uniq⟩, _⟩ := h_legal
  exact (hbk_uniq p hp).trans (hbk_uniq bdst hbdst_post).symm

-- ------------------------------------------------------------
-- DESTINATION EXCLUSIONS  (each says: a legal Black reply cannot
-- land on the named region, because doing so would leave Black in
-- check on the post-black-move board, contradicting `IsLegalSetup`).
-- ------------------------------------------------------------

-- (file = 1, rank > pre-Ra.rank): apply `RookCheckUp` on the post-board
-- using the witness `LadderMove_RookAttacker_AboveRaRank_FileOne` (the
-- post-step Rb at (rank+1, 1) attacks vertically up file 1), with the
-- step-board no-white-above clause lifted across the Black ply.
lemma BlackReply_NotAboveRaRank_FileOne {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ¬ (bdst.file.val = 1 ∧
       (rookAPos rank φ lsh.hRfits).rank.val < bdst.rank.val) := by
  rintro ⟨hfile, hrank⟩
  obtain ⟨rp, hRb_at, hRb_rank, hRb_file, no_white_above⟩ :=
    LadderMove_RookAttacker_AboveRaRank_FileOne lsh
  have hpreRa_ge :
      rank.val + 1 ≤ (rookAPos rank φ lsh.hRfits).rank.val := by
    cases φ <;> simp [rookAPos]
  have hsame_file : bdst.file = rp.file := by
    apply Fin.ext; rw [hRb_file]; exact hfile
  have hbdst_above : rp.rank.val < bdst.rank.val := by
    rw [hRb_rank]; omega
  have no_white_above_post :
      ∀ p k, p.file = rp.file → rp.rank.val < p.rank.val →
             (applyMove (applyLadderStep lsh) bsrc bdst) p ≠
               some ⟨.White, k⟩ := fun p k hpf hpr hpw =>
    no_white_above p k hpf hpr
      (BlackReply_StepWhite_Of_PostWhite lsh black_move hpw)
  exact BlackReply_PostBoard_NotInCheck lsh black_move
    (RookCheckUp _ rp bdst
      (BlackReply_RookPreserved lsh black_move hRb_at)
      (BlackReply_BlackKingAtDst lsh black_move)
      (LadderShape_OnlyBlackKingPreserved lsh bsrc bdst)
      (BlackReply_UniqueBlackKingPost lsh black_move)
      no_white_above_post hsame_file hbdst_above)

-- (file ≥ 2, rank = pre-Ra.rank): apply `RookCheckRight` on the post-board
-- using the witness `LadderMove_RookAttacker_AtRaRank_FileGe2` with the
-- step-board no-white-right clause lifted across the Black ply.
lemma BlackReply_NotAtRaRank_FileGe2 {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ¬ (2 ≤ bdst.file.val ∧
       bdst.rank.val = (rookAPos rank φ lsh.hRfits).rank.val) := by
  rintro ⟨hfile, hrank⟩
  obtain ⟨rp, hRook_at, hrp_rank, hrp_file_lt, no_white_right⟩ :=
    LadderMove_RookAttacker_AtRaRank_FileGe2 lsh
  have hsame_rank : bdst.rank = rp.rank := by
    apply Fin.ext; rw [hrank, hrp_rank]
  have hking_right : rp.file.val < bdst.file.val := by omega
  have no_white_right_post :
      ∀ p k, p.rank = rp.rank → rp.file.val < p.file.val →
             (applyMove (applyLadderStep lsh) bsrc bdst) p ≠
               some ⟨.White, k⟩ := fun p k hpr hpf hpw =>
    no_white_right p k hpr hpf
      (BlackReply_StepWhite_Of_PostWhite lsh black_move hpw)
  exact BlackReply_PostBoard_NotInCheck lsh black_move
    (RookCheckRight _ rp bdst
      (BlackReply_RookPreserved lsh black_move hRook_at)
      (BlackReply_BlackKingAtDst lsh black_move)
      (LadderShape_OnlyBlackKingPreserved lsh bsrc bdst)
      (BlackReply_UniqueBlackKingPost lsh black_move)
      no_white_right_post hsame_rank hking_right)

-- moveRa-only: apply `RookCheckRight` on the post-board using
-- `LadderMove_RookAttacker_AtRaRankPlusOne_FileGe2_moveRa`.
lemma BlackReply_NotAtRaRankPlusOne_FileGe2_moveRa
    {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveRa)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ¬ (2 ≤ bdst.file.val ∧
       bdst.rank.val = (rookAPos rank .moveRa lsh.hRfits).rank.val + 1) := by
  rintro ⟨hfile, hrank⟩
  obtain ⟨rp, hRa_at, hrp_rank, hrp_file, no_white_right⟩ :=
    LadderMove_RookAttacker_AtRaRankPlusOne_FileGe2_moveRa lsh
  have hsame_rank : bdst.rank = rp.rank := by
    apply Fin.ext; rw [hrank, hrp_rank]
  have hking_right : rp.file.val < bdst.file.val := by
    rw [hrp_file]; omega
  have no_white_right_post :
      ∀ p k, p.rank = rp.rank → rp.file.val < p.file.val →
             (applyMove (applyLadderStep lsh) bsrc bdst) p ≠
               some ⟨.White, k⟩ := fun p k hpr hpf hpw =>
    no_white_right p k hpr hpf
      (BlackReply_StepWhite_Of_PostWhite lsh black_move hpw)
  exact BlackReply_PostBoard_NotInCheck lsh black_move
    (RookCheckRight _ rp bdst
      (BlackReply_RookPreserved lsh black_move hRa_at)
      (BlackReply_BlackKingAtDst lsh black_move)
      (LadderShape_OnlyBlackKingPreserved lsh bsrc bdst)
      (BlackReply_UniqueBlackKingPost lsh black_move)
      no_white_right_post hsame_rank hking_right)

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
  obtain ⟨hf, hr⟩ := BlackReply_DstBounds lsh black_move
  have hpreRa : (rookAPos rank .moveRb lsh.hRfits).rank.val = rank.val + 1 := by
    simp [rookAPos]
  have hnextRa : (rookAPos rank .moveRa lsh.hRfits).rank.val = rank.val + 1 := by
    simp [rookAPos]
  rw [hpreRa] at hr
  rw [hnextRa]
  by_contra hle
  have heq : bdst.rank.val = rank.val + 1 := by omega
  by_cases hfile : bdst.file.val = 1
  · refine BlackReply_NotAtFileOneRaRank lsh black_move ⟨hfile, ?_⟩
    rw [heq, hpreRa]
  · refine BlackReply_NotAtRaRank_FileGe2 lsh black_move ⟨?_, ?_⟩
    · omega
    · rw [heq, hpreRa]

-- Phase moveRa (next state .moveK, same base rank): next-Ra.rank = rank+2.
-- One greater than pre-Ra.rank = rank+1, so the extra
-- `BlackReply_NotAtRaRankPlusOne_FileGe2_moveRa` exclusion is needed to
-- close the rank = rank+1, file ≥ 2 case that previously was permissible.
lemma BlackReply_DstRank_gt_NextRa_moveRa {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveRa)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    (rookAPos rank .moveK lsh.hRfits).rank.val < bdst.rank.val := by
  obtain ⟨hf, hr⟩ := BlackReply_DstBounds lsh black_move
  have hpreRa : (rookAPos rank .moveRa lsh.hRfits).rank.val = rank.val + 1 := by
    simp [rookAPos]
  have hnextRa : (rookAPos rank .moveK lsh.hRfits).rank.val = rank.val + 2 := by
    simp [rookAPos]
  rw [hpreRa] at hr
  rw [hnextRa]
  by_contra hle
  rcases (show bdst.rank.val = rank.val + 1 ∨ bdst.rank.val = rank.val + 2 by omega)
    with heq | heq
  · -- bdst.rank = pre-Ra.rank: same exclusions as in moveRb.
    by_cases hfile : bdst.file.val = 1
    · refine BlackReply_NotAtFileOneRaRank lsh black_move ⟨hfile, ?_⟩
      rw [heq, hpreRa]
    · refine BlackReply_NotAtRaRank_FileGe2 lsh black_move ⟨?_, ?_⟩
      · omega
      · rw [heq, hpreRa]
  · -- bdst.rank = pre-Ra.rank + 1: the moveRa-only exclusion handles file ≥ 2,
    -- and the file=1 case is killed by the "above-Ra" exclusion.
    by_cases hfile : bdst.file.val = 1
    · refine BlackReply_NotAboveRaRank_FileOne lsh black_move ⟨hfile, ?_⟩
      rw [heq, hpreRa]; omega
    · refine BlackReply_NotAtRaRankPlusOne_FileGe2_moveRa lsh black_move ⟨?_, ?_⟩
      · omega
      · rw [heq, hpreRa]

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
  intro rank' h'
  obtain ⟨hf, hr⟩ := BlackReply_DstBounds lsh black_move
  have hpreRa : (rookAPos rank .moveK lsh.hRfits).rank.val = rank.val + 2 := by
    simp [rookAPos]
  have hnextRa : (rookAPos rank' .moveRb h').rank.val = rank.val + 2 := by
    show rank'.val + 1 = rank.val + 2
    show rank.val + 1 + 1 = rank.val + 2
    rfl
  rw [hpreRa] at hr
  rw [hnextRa]
  by_contra hle
  have heq : bdst.rank.val = rank.val + 2 := by omega
  by_cases hfile : bdst.file.val = 1
  · refine BlackReply_NotAtFileOneRaRank lsh black_move ⟨hfile, ?_⟩
    rw [heq, hpreRa]
  · refine BlackReply_NotAtRaRank_FileGe2 lsh black_move ⟨?_, ?_⟩
    · omega
    · rw [heq, hpreRa]

-- ------------------------------------------------------------
-- INVARIANT PRESERVATION  (plug-ins for the three `sorry`s in
-- `LadderShape.preservation`)
-- ------------------------------------------------------------
-- On the post-black-move board the only black piece is the (unique)
-- black king sitting at bdst, so the `bdst.rank > next-Ra.rank` bound
-- above lifts to "every bp carrying the black king has rank > next-Ra.rank".

-- Common plumbing: on the post-black-move board the black king sits at
-- bdst (and that is the unique black-king square, by `IsLegalSetup`).
private lemma BlackReply_BlackKingUniqueAtDst {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ∀ bp,
      (applyMove (applyLadderStep lsh) bsrc bdst) bp =
        some ⟨.Black, .King⟩ →
      bp = bdst := by
  intro bp hbp
  obtain ⟨piece, hat_src, _, _, h_legal⟩ := black_move
  obtain ⟨turn_white, _⟩ := lsh.unfold
  have h_turn_step : (applyLadderStep lsh).turn = .Black := by
    show board.turn.opponent = .Black
    rw [turn_white]; rfl
  rw [h_turn_step] at hat_src
  have hk : piece = .King :=
    LadderMove_PreservesOnlyBlackKing lsh bsrc piece hat_src
  subst hk
  have hb''_bdst :
      (applyMove (applyLadderStep lsh) bsrc bdst) bdst = some ⟨.Black, .King⟩ := by
    rw [applyMove_pieces, if_pos rfl]; exact hat_src
  obtain ⟨_, ⟨_, _, h_uniq⟩, _⟩ := h_legal
  exact (h_uniq bp hbp).trans (h_uniq bdst hb''_bdst).symm

lemma LadderMove_BlackKingAboveNextRa_moveRb {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveRb)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ∀ bp,
      (applyMove (applyLadderStep lsh) bsrc bdst) bp =
        some ⟨.Black, .King⟩ →
      (rookAPos rank .moveRa lsh.hRfits).rank < bp.rank := by
  intro bp hbp
  have hbp_eq : bp = bdst := BlackReply_BlackKingUniqueAtDst lsh black_move bp hbp
  subst hbp_eq
  exact BlackReply_DstRank_gt_NextRa_moveRb lsh black_move

lemma LadderMove_BlackKingAboveNextRa_moveRa {n : Nat} {board : Board n}
    {rank : Fin n} (lsh : LadderShape board rank .moveRa)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (applyLadderStep lsh) bsrc bdst) :
    ∀ bp,
      (applyMove (applyLadderStep lsh) bsrc bdst) bp =
        some ⟨.Black, .King⟩ →
      (rookAPos rank .moveK lsh.hRfits).rank < bp.rank := by
  intro bp hbp
  have hbp_eq : bp = bdst := BlackReply_BlackKingUniqueAtDst lsh black_move bp hbp
  subst hbp_eq
  exact BlackReply_DstRank_gt_NextRa_moveRa lsh black_move

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
  intro _ _ bp hbp
  have hbp_eq : bp = bdst := BlackReply_BlackKingUniqueAtDst lsh black_move bp hbp
  subst hbp_eq
  exact BlackReply_DstRank_gt_NextRa_moveK lsh hRoom black_move
