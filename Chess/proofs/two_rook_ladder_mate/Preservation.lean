import ChessRules
import FunctionDefinition
import HelperLemmas
import NextWhiteMoveIsLegal
import Mathlib.Data.Finset.Card

-- ============================================================
-- LADDER SHAPE PRESERVATION
-- ============================================================
-- After one White ply (`ladderStep`) followed by any legal Black reply,
-- the resulting board still satisfies `LadderShape` for the advanced
-- rank and the next phase. This is the inductive invariant that drives
-- `ladderMate_termination` below.


-- ------------------------------------------------------------
-- INDIVIDUAL PRESERVATION SUB-LEMMAS
-- ------------------------------------------------------------
-- Each of the conjuncts in `LadderShape` has its own preservation lemma
-- below. They are stated independently of `LadderShape` on the result
-- board so that the moveK case (where the new rank may not satisfy the
-- bound `rank.val + 2 < n`) does not block them.

-- One white ply (`ladderStep`) flips turn White → Black; one further
-- ply (the black reply) flips Black → White. So the resulting turn is
-- White regardless of which squares the black move uses.
lemma LadderShape_TurnPreserved {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) (bsrc bdst : Pos n) :
    (applyMove (ladderStep lsh) bsrc bdst).turn = .White := by
  obtain ⟨turn_white, _⟩ := lsh.unfold
  show (board.turn.opponent).opponent = .White
  rw [turn_white]; rfl

-- A legal black move into the post-white-ply board produces a legal
-- setup — that is the last conjunct of `IsLegalMove`.
lemma LadderShape_LegalSetupPreserved {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) {bsrc bdst : Pos n}
    (black_move : IsLegalMove (ladderStep lsh) bsrc bdst) :
    IsLegalSetup (applyMove (ladderStep lsh) bsrc bdst) := by
  obtain ⟨_, _, _, _, h_legal⟩ := black_move
  exact h_legal

-- "Every black-occupied square is a king" survives a full White+Black
-- cycle: white's ply is into an empty square (so doesn't introduce any
-- non-king black piece), and black's ply only relocates a black piece.
-- Each ply is handled by `applyMove_PreservesOnlyBlackKing`.
lemma LadderShape_OnlyBlackKingPreserved {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) (bsrc bdst : Pos n) :
    ∀ p k, (applyMove (ladderStep lsh) bsrc bdst) p = some ⟨.Black, k⟩ →
           k = .King := by
  obtain ⟨_, _, _, _, _, _, only_bk, _⟩ := lsh.unfold
  have step_only_bk : ∀ p k, (ladderStep lsh) p = some ⟨.Black, k⟩ → k = .King :=
    applyMove_PreservesOnlyBlackKing board _ _ only_bk
  exact applyMove_PreservesOnlyBlackKing _ _ _ step_only_bk


-- ------------------------------------------------------------
-- WHITE-PIECE POSITIONS AFTER ONE LADDER PLY
-- ------------------------------------------------------------
-- After white's ladder ply, the three white pieces sit at specific
-- squares — namely the squares predicted by the *next* `LadderShape`
-- state's position helpers (`nextRank` for rank, `nextPhase` for the
-- rook configuration). Two pieces are unchanged (proved via
-- `NoCaptureMove_PreservesPiece`); the third is at the move's `dst`.
-- The moveK case additionally needs the next-rank bound
-- `rank.val + 3 < n` to form `kingPos` / `rookXPos` for `rank+1`.

-- Phase moveRb: white moves Rb (rank,1) → (rank+1,1).
-- Resulting positions match `LadderShape` for (rank, .moveRa).
lemma LadderStep_PiecesAt_moveRb {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveRb) :
    let h := lsh.hRfits
    let b' := ladderStep lsh
    b' (kingPos rank h) = some ⟨.White, .King⟩ ∧
    b' (rookBPos rank .moveRa h) = some ⟨.White, .Rook⟩ ∧
    b' (rookAPos rank .moveRa h) = some ⟨.White, .Rook⟩ := by
  obtain ⟨_, hK_at, hRb_at, hRa_at, _⟩ := lsh.unfold
  have dst_empty := LadderMove_IntoEmptySquare lsh
  have h_src_eq : (nextWhiteMove lsh).1 = rookBPos rank .moveRb lsh.hRfits := rfl
  refine ⟨?_, ?_, ?_⟩
  · -- King unchanged at (rank, 0)
    apply NoCaptureMove_PreservesPiece _ _ _ _ _ hK_at _ dst_empty
    rw [h_src_eq]; intro heq
    have := congrArg (fun p : Pos n => p.file.val) heq
    simp [kingPos, rookBPos] at this
  · -- Rb moved to (rank+1, 1) = dst
    show (applyMove board _ (rookBPos rank .moveRa lsh.hRfits)).pieces _ = _
    unfold applyMove; simp; rw [h_src_eq]; exact hRb_at
  · -- Ra unchanged at (rank+1, 0)
    apply NoCaptureMove_PreservesPiece _ _ _ _ _ hRa_at _ dst_empty
    rw [h_src_eq]; intro heq
    have := congrArg (fun p : Pos n => p.file.val) heq
    simp [rookBPos, rookAPos] at this

-- Phase moveRa: white moves Ra (rank+1,0) → (rank+2,0).
-- Resulting positions match `LadderShape` for (rank, .moveK).
lemma LadderStep_PiecesAt_moveRa {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveRa) :
    let h := lsh.hRfits
    let b' := ladderStep lsh
    b' (kingPos rank h) = some ⟨.White, .King⟩ ∧
    b' (rookBPos rank .moveK h) = some ⟨.White, .Rook⟩ ∧
    b' (rookAPos rank .moveK h) = some ⟨.White, .Rook⟩ := by
  obtain ⟨_, hK_at, hRb_at, hRa_at, _⟩ := lsh.unfold
  have dst_empty := LadderMove_IntoEmptySquare lsh
  have h_src_eq : (nextWhiteMove lsh).1 = rookAPos rank .moveRa lsh.hRfits := rfl
  refine ⟨?_, ?_, ?_⟩
  · -- King unchanged at (rank, 0)
    apply NoCaptureMove_PreservesPiece _ _ _ _ _ hK_at _ dst_empty
    rw [h_src_eq]; intro heq
    have := congrArg (fun p : Pos n => p.rank.val) heq
    simp [kingPos, rookAPos] at this
  · -- Rb unchanged at (rank+1, 1)
    apply NoCaptureMove_PreservesPiece _ _ _ _ _ hRb_at _ dst_empty
    rw [h_src_eq]; intro heq
    have := congrArg (fun p : Pos n => p.file.val) heq
    simp [rookBPos, rookAPos] at this
  · -- Ra moved to (rank+2, 0) = dst
    show (applyMove board _ (rookAPos rank .moveK lsh.hRfits)).pieces _ = _
    unfold applyMove; simp; rw [h_src_eq]; exact hRa_at

-- Phase moveK: white moves K (rank,0) → (rank+1,0).
-- Resulting positions match `LadderShape` for (rank+1, .moveRb), i.e.
-- the next state's position helpers — paralleling moveRb/moveRa above.
-- This requires the next-rank bound `rank.val + 3 < n`.
lemma LadderStep_PiecesAt_moveK {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveK)
    (hRoom : rank.val + 3 < n) :
    let rank' : Fin n := ⟨rank.val + 1, by omega⟩
    let h' : rank'.val + 2 < n := hRoom
    let b' := ladderStep lsh
    b' (kingPos rank' h') = some ⟨.White, .King⟩ ∧
    b' (rookBPos rank' .moveRb h') = some ⟨.White, .Rook⟩ ∧
    b' (rookAPos rank' .moveRb h') = some ⟨.White, .Rook⟩ := by
  obtain ⟨_, hK_at, hRb_at, hRa_at, _⟩ := lsh.unfold
  have dst_empty := LadderMove_IntoEmptySquare lsh
  have h_src_eq : (nextWhiteMove lsh).1 = kingPos rank lsh.hRfits := rfl
  refine ⟨?_, ?_, ?_⟩
  · -- King moved to dst; rewrite the target square as `(nextWhiteMove lsh).2`
    -- (defeq to `kingPos rank' h'` modulo proof irrelevance) so the `==` in
    -- `applyMove` reduces.
    show (applyMove board (nextWhiteMove lsh).1 (nextWhiteMove lsh).2).pieces
        (nextWhiteMove lsh).2 = some ⟨.White, .King⟩
    unfold applyMove; simp; rw [h_src_eq]; exact hK_at
  · -- Rb unchanged at (rank+1, 1) = rookBPos (rank+1) .moveRb _
    apply NoCaptureMove_PreservesPiece _ _ _ _ _ hRb_at _ dst_empty
    rw [h_src_eq]; intro heq
    have := congrArg (fun p : Pos n => p.file.val) heq
    simp [kingPos, rookBPos] at this
  · -- Ra unchanged at (rank+2, 0) = rookAPos (rank+1) .moveRb _
    apply NoCaptureMove_PreservesPiece _ _ _ _ _ hRa_at _ dst_empty
    rw [h_src_eq]; intro heq
    have := congrArg (fun p : Pos n => p.rank.val) heq
    simp [kingPos, rookAPos] at this


-- ------------------------------------------------------------
-- HELPERS FOR WHITE-PIECE PRESERVATION
-- ------------------------------------------------------------
-- Used inline by `LadderShape.preservation` (the per-phase plumbing
-- for "white piece p is unchanged across the full White+Black cycle").
-- Both rely on the simplifying assumption that black's reply targets
-- an empty square (no white piece is captured); ruling that out is
-- still future work.

-- Helper: bsrc carries a black piece (since `IsLegalMove`'s piece
-- belongs to the side to move, which is `(ladderStep lsh).turn = Black`).
private lemma blackMove_src_isBlack {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) {bsrc bdst : Pos n}
    (black_move : IsLegalMove (ladderStep lsh) bsrc bdst) :
    ∃ k, (ladderStep lsh) bsrc = some ⟨.Black, k⟩ := by
  obtain ⟨turn_white, _⟩ := lsh.unfold
  obtain ⟨piece, hat_src, _⟩ := black_move
  have h_turn : (ladderStep lsh).turn = .Black := by
    show board.turn.opponent = .Black
    rw [turn_white]; rfl
  rw [h_turn] at hat_src
  exact ⟨piece, hat_src⟩

-- Closes a "white piece preservation" goal using a step-board hypothesis
-- `h_pc_at : (ladderStep lsh) p = some ⟨.White, _⟩` and the fact that
-- bsrc carries a black piece.
private lemma whitePiecePreserved {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    {lsh : LadderShape board rank φ} {bsrc bdst p : Pos n} {pc : Piece}
    (h_pc_at : (ladderStep lsh) p = some pc)
    (h_white : pc.color = .White)
    (h_bsrc_black : ∃ k, (ladderStep lsh) bsrc = some ⟨.Black, k⟩)
    (bdst_empty : (ladderStep lsh) bdst = none) :
    (applyMove (ladderStep lsh) bsrc bdst) p = some pc := by
  obtain ⟨k, hbsrc⟩ := h_bsrc_black
  refine NoCaptureMove_PreservesPiece _ _ _ _ _ h_pc_at ?_ bdst_empty
  intro heq
  rw [heq, h_pc_at] at hbsrc
  rw [Option.some.injEq] at hbsrc
  have : pc.color = (⟨.Black, k⟩ : Piece).color := congrArg Piece.color hbsrc
  rw [h_white] at this
  cases this

-- ------------------------------------------------------------
-- HELPERS FOR Q PRESERVATION (white pieces confined to K, Rb, Ra)
-- ------------------------------------------------------------
-- The Q conjunct of `LadderShape` says the only white-occupied
-- squares are the three named ladder squares. After one White ply
-- + one legal Black reply (with bdst empty), Q on the input board
-- transports to Q on the output board via the counting machinery
-- in `HelperLemmas`:
--
--   (1) `colorSquares_card_le_three_of_Q` turns input Q into
--       a `card ≤ 3` bound on white squares.
--   (2) `colorSquares_card_eq_ourMove` carries that bound through
--       the white ply (white's own legal move can't add a fresh
--       white square — captures only swap an opponent square for
--       a white one), and `colorSquares_card_eq_nonCapture` carries
--       it through the black ply (target empty by hypothesis).
--   (3) `Q_of_subset_card_le` collapses the bound back to Q on the
--       output board, given the three named squares each carry a
--       white piece (from `LadderStep_PiecesAt_*` + `whitePiecePreserved`)
--       and are pairwise distinct (the three lemmas just below).

-- The three named ladder squares (kingPos, rookBPos, rookAPos) are
-- pairwise distinct for every phase. Each pair separates either by
-- file or by rank; the value table in `FunctionDefinition.lean`
-- shows the gap explicitly.
private lemma ladderPos_pairwise_distinct {n : Nat} (rank : Fin n) (φ : LadderPhase)
    (h : rank.val + 2 < n) :
    kingPos rank h ≠ rookBPos rank φ h ∧
    kingPos rank h ≠ rookAPos rank φ h ∧
    rookBPos rank φ h ≠ rookAPos rank φ h := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have := congrArg (fun p : Pos n => p.file.val) heq
    cases φ <;> simp [kingPos, rookBPos] at this
  · intro heq
    have := congrArg (fun p : Pos n => p.rank.val) heq
    cases φ <;> simp [kingPos, rookAPos] at this
  · intro heq
    have := congrArg (fun p : Pos n => p.file.val) heq
    cases φ <;> simp [rookBPos, rookAPos] at this

-- After White's ladder ply the count of white-occupied squares is
-- unchanged: the ply targets an empty square (`LadderMove_IntoEmptySquare`),
-- so it doesn't drop a piece on top of an existing white-occupied square.
-- Combined with the input Q, this gives the `≤ 3` bound on the step
-- board's white squares — the seed needed to recover Q on the step
-- board (used both by the full-cycle bound below and by
-- `LadderMove_OnlyFileOneRaRank_InRegion`).
private lemma whiteCount_le_three_after_step {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) :
    (colorSquares (ladderStep lsh) .White).card ≤ 3 := by
  obtain ⟨_, _, _, _, hQ, _, _, _⟩ := lsh.unfold
  have h_init : (colorSquares board .White).card ≤ 3 :=
    colorSquares_card_le_three_of_Q board .White hQ
  have h_white_ply : (colorSquares (ladderStep lsh) .White).card =
      (colorSquares board .White).card :=
    colorSquares_card_eq_nonCapture board .White
      (nextWhiteMove lsh).1 (nextWhiteMove lsh).2
      (LadderMove_IntoEmptySquare lsh)
  omega

-- Extends `whiteCount_le_three_after_step` across the Black ply: the
-- black ply also targets an empty square (`bdst_empty`), so the count
-- is preserved a second time.
private lemma whiteCount_le_three_after_cycle {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ) {bsrc bdst : Pos n}
    (bdst_empty : (ladderStep lsh) bdst = none) :
    (colorSquares (applyMove (ladderStep lsh) bsrc bdst) .White).card ≤ 3 := by
  have h_step := whiteCount_le_three_after_step lsh
  have h_black_ply :
      (colorSquares (applyMove (ladderStep lsh) bsrc bdst) .White).card =
      (colorSquares (ladderStep lsh) .White).card :=
    colorSquares_card_eq_nonCapture (ladderStep lsh) .White
      bsrc bdst bdst_empty
  omega


-- ------------------------------------------------------------
-- Q ON THE STEP BOARD
-- ------------------------------------------------------------
-- Companions to `LadderStep_PiecesAt_*`: not only do the three named
-- squares carry white pieces after White's ply, those are the *only*
-- squares carrying white pieces. Recovered from the input Q via the
-- counting machinery — `whiteCount_le_three_after_step` for the count
-- bound and the `LadderStep_PiecesAt_*` triple plus
-- `ladderPos_pairwise_distinct` for the saturating subset, fed into
-- `Q_of_subset_card_le`.
--
-- Like `LadderStep_PiecesAt_*`, the three squares are phase-dependent
-- (they are the next state's named positions), so this is split into
-- one lemma per input phase.

lemma LadderStep_QPart_moveRb {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveRb) :
    let h := lsh.hRfits
    let b' := ladderStep lsh
    ∀ p, (∃ k, b' p = some ⟨.White, k⟩) →
         p = kingPos rank h ∨
         p = rookBPos rank .moveRa h ∨
         p = rookAPos rank .moveRa h := by
  obtain ⟨hK, hRb, hRa⟩ := LadderStep_PiecesAt_moveRb lsh
  exact Q_of_subset_card_le _ .White
    ⟨.King, hK⟩ ⟨.Rook, hRb⟩ ⟨.Rook, hRa⟩
    (ladderPos_pairwise_distinct rank .moveRa lsh.hRfits)
    (whiteCount_le_three_after_step lsh)

lemma LadderStep_QPart_moveRa {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveRa) :
    let h := lsh.hRfits
    let b' := ladderStep lsh
    ∀ p, (∃ k, b' p = some ⟨.White, k⟩) →
         p = kingPos rank h ∨
         p = rookBPos rank .moveK h ∨
         p = rookAPos rank .moveK h := by
  sorry

lemma LadderStep_QPart_moveK {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveK) (hRoom : rank.val + 3 < n) :
    let rank' : Fin n := ⟨rank.val + 1, by omega⟩
    let h' : rank'.val + 2 < n := hRoom
    let b' := ladderStep lsh
    ∀ p, (∃ k, b' p = some ⟨.White, k⟩) →
         p = kingPos rank' h' ∨
         p = rookBPos rank' .moveRb h' ∨
         p = rookAPos rank' .moveRb h' := by
  sorry


-- ------------------------------------------------------------
-- BLACK REPLY TARGETS AN EMPTY SQUARE
-- ------------------------------------------------------------
-- Closes the `bdst_empty` hypothesis used inside `LadderShape.preservation`
-- (currently `sorry`'d). The argument chains four facts about the step
-- board (the board after White's ladder ply):
--
--   (i)   The (unique) black king still has file ≥ 2 and rank strictly
--         greater than `rookAPos rank φ` — White's ply moves into an
--         empty square (`LadderMove_IntoEmptySquare`), so it doesn't
--         relocate the black king, and the file/rank bounds carry over
--         from `LadderShape_KingsApart` and the `black_loc` conjunct.
--   (ii)  A legal Black king reply moves at most one square in each
--         coordinate, so its destination has file ≥ 1 and
--         rank ≥ rookAPos.rank.
--   (iii) The square at (file = 1, rank = rookAPos.rank) is attacked
--         by the White king on the step board in every phase, so a
--         legal Black reply cannot land there (it would leave Black
--         in check).
--   (iv)  The only White piece on the step board sitting at
--         (file ≥ 1, rank ≥ rookAPos.rank) is at (file = 1,
--         rank = rookAPos.rank). For phases moveRb / moveRa this is
--         the post-step rookB square; for phase moveK no white piece
--         lies in the region at all (vacuous). Proving this needs Q
--         transported through White's ply (via the same
--         `colorSquares_card_eq_nonCapture` /  `Q_of_subset_card_le`
--         machinery used by `whiteCount_le_three_after_cycle`).
--
-- (ii)+(iii)+(iv) together say `bdst` carries no white piece on the
-- step board; combined with "only black piece is the king, sitting at
-- bsrc ≠ bdst", this gives `bdst` is empty.

-- (i) The black king's square on the step board has file ≥ 2 and
-- rank > rookAPos.rank.
lemma LadderMove_BlackKing_FarFromRa {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    ∀ bp, (ladderStep lsh) bp = some ⟨.Black, .King⟩ →
          2 ≤ bp.file.val ∧
          (rookAPos rank φ lsh.hRfits).rank.val < bp.rank.val := by
  intro bp hbp
  obtain ⟨_, hK_at, hRb_at, hRa_at, _, black_loc, _, _⟩ := lsh.unfold
  -- The white move's source carries some white piece (Rook in moveRb /
  -- moveRa, King in moveK), and its destination is empty
  -- (`LadderMove_IntoEmptySquare`). So bp can be neither src nor dst —
  -- the black king at bp on the step board is already at bp on the
  -- original board.
  have hbp' : (applyMove board (nextWhiteMove lsh).1 (nextWhiteMove lsh).2) bp
              = some ⟨.Black, .King⟩ := hbp
  rw [applyMove_pieces] at hbp'
  have h_src_white :
      ∃ k, board (nextWhiteMove lsh).1 = some ⟨.White, k⟩ := by
    cases φ
    · exact ⟨.Rook, hRb_at⟩
    · exact ⟨.Rook, hRa_at⟩
    · exact ⟨.King, hK_at⟩
  have hbp_orig : board bp = some ⟨.Black, .King⟩ := by
    by_cases h1 : bp = (nextWhiteMove lsh).2
    · rw [if_pos h1] at hbp'
      obtain ⟨_, hk⟩ := h_src_white
      rw [hk] at hbp'; simp at hbp'
    · rw [if_neg h1] at hbp'
      by_cases h2 : bp = (nextWhiteMove lsh).1
      · rw [if_pos h2] at hbp'; simp at hbp'
      · rw [if_neg h2] at hbp'; exact hbp'
  exact ⟨LadderShape_KingsApart lsh bp hbp_orig, black_loc bp hbp_orig⟩

-- (ii) After any legal Black king reply on the step board, the
-- destination has file ≥ 1 and rank ≥ rookAPos.rank.
lemma BlackReply_DstBounds {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (ladderStep lsh) bsrc bdst) :
    1 ≤ bdst.file.val ∧
    (rookAPos rank φ lsh.hRfits).rank.val ≤ bdst.rank.val := by
  obtain ⟨turn_white, _⟩ := lsh.unfold
  -- The step board has Black to move (White's ply flips the turn).
  have h_turn : (ladderStep lsh).turn = .Black := by
    show board.turn.opponent = .Black
    rw [turn_white]; rfl
  -- Unpack IsLegalMove and pin the moving piece to .King via
  -- `LadderMove_PreservesOnlyBlackKing`.
  obtain ⟨piece, hat_src, h_valid, _, _⟩ := black_move
  rw [h_turn] at hat_src
  have hk : piece = .King :=
    LadderMove_PreservesOnlyBlackKing lsh bsrc piece hat_src
  subst hk
  -- bsrc inherits the BlackKing bounds; ValidKingMove gives WithinOne
  -- on each coordinate, so bdst is at most one square away.
  obtain ⟨h_bsrc_file, h_bsrc_rank⟩ :=
    LadderMove_BlackKing_FarFromRa lsh bsrc hat_src
  change ValidKingMove bsrc bdst at h_valid
  obtain ⟨_, h_rank, h_file⟩ := h_valid
  unfold WithinOne at h_rank h_file
  refine ⟨?_, ?_⟩
  · omega
  · omega

-- (iii) On the step board, the White king attacks the square at
-- (file = 1, rank = rookAPos.rank). Pure phase-by-phase check: the
-- White king sits one step diagonally below this square in moveRb /
-- moveRa, and one step left of it in moveK (after the King's own ply
-- has advanced by one rank).
lemma LadderMove_WhiteKingAttacks_FileOneRaRank {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    ∀ wk q, (ladderStep lsh) wk = some ⟨.White, .King⟩ →
            q.file.val = 1 →
            q.rank.val = (rookAPos rank φ lsh.hRfits).rank.val →
            ValidKingMove wk q := by
  sorry

-- Corollary of (iii): a legal Black reply cannot land on the
-- (file = 1, rank = rookAPos.rank) square — going there would leave
-- the Black king attacked by the protecting White king and thus
-- violate `IsLegalSetup` (¬ IsCheck Black) on the post-reply board.
lemma BlackReply_NotAtFileOneRaRank {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (ladderStep lsh) bsrc bdst) :
    ¬ (bdst.file.val = 1 ∧
       bdst.rank.val = (rookAPos rank φ lsh.hRfits).rank.val) := by
  sorry

-- (iv) On the step board, any White piece at file ≥ 1 and
-- rank ≥ rookAPos.rank sits at exactly (file = 1, rank = rookAPos.rank).
-- For moveRb / moveRa this is the (post-step) rookB square; for moveK
-- there is no White piece in the region at all, so the conclusion is
-- vacuous.
--
-- Note: the proof case-splits on φ and dispatches to the
-- corresponding `LadderStep_QPart_*` lemma (Q on the step board for
-- that phase) to enumerate the three candidate white squares.
lemma LadderMove_OnlyFileOneRaRank_InRegion {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ) :
    ∀ p, 1 ≤ p.file.val →
         (rookAPos rank φ lsh.hRfits).rank.val ≤ p.rank.val →
         (∃ k, (ladderStep lsh) p = some ⟨.White, k⟩) →
         p.file.val = 1 ∧
         p.rank.val = (rookAPos rank φ lsh.hRfits).rank.val := by
  sorry

-- Corollary of (ii)+(iii)+(iv): a legal Black reply's destination
-- carries no white piece on the step board.
lemma BlackReply_DstNotWhite {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (ladderStep lsh) bsrc bdst) :
    ∀ k, (ladderStep lsh) bdst ≠ some ⟨.White, k⟩ := by
  sorry

-- Final: the destination is empty on the step board. Combines
-- `BlackReply_DstNotWhite` with "any black piece on the step board is
-- the (unique) black king, which sits at bsrc ≠ bdst", to rule out
-- both colors at bdst.
lemma BlackReply_DstEmpty {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase} (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (ladderStep lsh) bsrc bdst) :
    (ladderStep lsh) bdst = none := by
  sorry


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
    (black_move : IsLegalMove (ladderStep lsh) bsrc bdst) :
    LadderShape
      (applyMove (ladderStep lsh) bsrc bdst)
      (nextRank rank φ lsh.hRfits)
      (nextPhase φ) := by
  have h_turn    := LadderShape_TurnPreserved lsh bsrc bdst
  have h_legal   := LadderShape_LegalSetupPreserved lsh black_move
  have h_only_bk := LadderShape_OnlyBlackKingPreserved lsh bsrc bdst
  have hbsrc     := blackMove_src_isBlack lsh black_move
  -- Black's reply might capture a white piece; ruling that out is
  -- future work. Until then, white-piece preservation borrows it as
  -- an assumption.
  have bdst_empty : (ladderStep lsh) bdst = none := sorry
  have h_card := whiteCount_le_three_after_cycle (bsrc := bsrc) lsh bdst_empty
  cases φ with
  | moveRb =>
    obtain ⟨hK, hRb, hRa⟩ := LadderStep_PiecesAt_moveRb lsh
    have hK'  := whitePiecePreserved hK  rfl hbsrc bdst_empty
    have hRb' := whitePiecePreserved hRb rfl hbsrc bdst_empty
    have hRa' := whitePiecePreserved hRa rfl hbsrc bdst_empty
    have hQ' := Q_of_subset_card_le _ .White
      ⟨.King, hK'⟩ ⟨.Rook, hRb'⟩ ⟨.Rook, hRa'⟩
      (ladderPos_pairwise_distinct rank .moveRa lsh.hRfits)
      h_card
    show LadderShape (applyMove (ladderStep lsh) bsrc bdst) rank .moveRa
    unfold LadderShape
    rw [dif_pos lsh.hRfits]
    refine ⟨h_turn, hK', hRb', hRa', hQ', ?_, h_only_bk, h_legal⟩
    · sorry  -- black king's rank is strictly above rookA
  | moveRa =>
    obtain ⟨hK, hRb, hRa⟩ := LadderStep_PiecesAt_moveRa lsh
    have hK'  := whitePiecePreserved hK  rfl hbsrc bdst_empty
    have hRb' := whitePiecePreserved hRb rfl hbsrc bdst_empty
    have hRa' := whitePiecePreserved hRa rfl hbsrc bdst_empty
    have hQ' := Q_of_subset_card_le _ .White
      ⟨.King, hK'⟩ ⟨.Rook, hRb'⟩ ⟨.Rook, hRa'⟩
      (ladderPos_pairwise_distinct rank .moveK lsh.hRfits)
      h_card
    show LadderShape (applyMove (ladderStep lsh) bsrc bdst) rank .moveK
    unfold LadderShape
    rw [dif_pos lsh.hRfits]
    refine ⟨h_turn, hK', hRb', hRa', hQ', ?_, h_only_bk, h_legal⟩
    · sorry  -- black king's rank is strictly above rookA
  | moveK =>
    have hRoom := hMoveK rfl
    obtain ⟨hK, hRb, hRa⟩ := LadderStep_PiecesAt_moveK lsh hRoom
    have hK'  := whitePiecePreserved hK  rfl hbsrc bdst_empty
    have hRb' := whitePiecePreserved hRb rfl hbsrc bdst_empty
    have hRa' := whitePiecePreserved hRa rfl hbsrc bdst_empty
    let rank' : Fin n := ⟨rank.val + 1, by omega⟩
    have h' : rank'.val + 2 < n := hRoom
    have hQ' := Q_of_subset_card_le _ .White
      ⟨.King, hK'⟩ ⟨.Rook, hRb'⟩ ⟨.Rook, hRa'⟩
      (ladderPos_pairwise_distinct rank' .moveRb h')
      h_card
    show LadderShape (applyMove (ladderStep lsh) bsrc bdst) rank' .moveRb
    unfold LadderShape
    rw [dif_pos h']
    refine ⟨h_turn, hK', hRb', hRa', hQ', ?_, h_only_bk, h_legal⟩
    · sorry  -- black king's rank is strictly above rookA


-- ------------------------------------------------------------
-- TERMINATION / CHECKMATE THEOREM (statement only)
-- ------------------------------------------------------------
-- The ladder forces checkmate for Black in finitely many full cycles
-- (one White ply + one legal Black ply each), regardless of how Black
-- plays.
--
-- `reply` is an arbitrary Black strategy: given the board after the
-- White ply it picks (src, dst).  `hreply` witnesses that every chosen
-- move is legal.  The iteration uses `Function.iterate` (^[k]) on the
-- one-cycle step that advances the LadderState via
-- `LadderShape.preservation`.
theorem ladderMate_termination {n : Nat}
    (s₀    : LadderState n)
    (reply  : (b : Board n) → Pos n × Pos n)
    (hreply : ∀ s : LadderState n,
        IsLegalMove (ladderStep s.shape)
                    (reply (ladderStep s.shape)).1
                    (reply (ladderStep s.shape)).2) :
    ∃ k : Nat,
      IsCheckmate
        ((fun s : LadderState n =>
            { board := applyMove (ladderStep s.shape)
                         (reply (ladderStep s.shape)).1
                         (reply (ladderStep s.shape)).2
              rank  := nextRank s.rank s.phase s.shape.hRfits
              phase := nextPhase s.phase
              -- TODO: restructure `step` to skip the boundary moveK case
              -- (where `s.rank.val + 3 < n` fails); at that boundary Black
              -- is already checkmated so preservation is not needed.
              shape := LadderShape.preservation s.shape sorry (hreply s) })^[k] s₀).board
        .Black := by
  sorry
  /-
  PROOF SKETCH

  ── Core idea: contradiction via rank exhaustion ─────────────────────────────

  Every full cycle (one White ply + one legal Black reply) advances the base
  rank by exactly 1 (via `nextRank` on the `.moveK` ply; the other two plies
  leave the rank unchanged). The `space_left` bound baked into every
  `LadderShape` proof requires `rank.val + 2 < n`. So if the current base rank
  is R the bound says R ≤ n − 3, and after k full cycles the rank is R₀ + k,
  still needing R₀ + k ≤ n − 3.

  This means there is a hard finite ceiling: after at most
      K := n − 2 − s₀.rank.val     (which satisfies 0 ≤ K because s₀.shape.hRfits gives R₀ + 2 < n)
  full cycles the base rank would reach n − 2, making `space_left` false and
  therefore `LadderShape board (n−2) φ` definitionally equal to `False`.

  If checkmate has not yet occurred, `LadderShape.preservation` (together with
  `hreply`) lets us build a valid `LadderState` after each cycle. After K
  cycles we would hold a `LadderState` whose `.shape` field has type
  `LadderShape _ ⟨n−2, …⟩ _`. Unfolding the definition reduces that to `False`,
  and we derive anything — in particular the ∃ k goal — ex falso. So checkmate
  must have occurred strictly before cycle K.

  ── Why the measure is strictly monotone ─────────────────────────────────────

  Define the *headroom* of a `LadderState s` as `n − 2 − s.rank.val` (a Nat,
  which is always well-defined because `s.shape.hRfits` gives `s.rank.val + 2 < n`).
  After one full cycle `nextRank` replaces `s.rank` with `⟨s.rank.val + 1, _⟩`,
  strictly decreasing the headroom. Headroom ≥ 0 because it lives in ℕ, so the
  process terminates in at most K steps.

  ── Formal proof structure ────────────────────────────────────────────────────

  Let `step` be the one-cycle function appearing in the goal (let-bind it for
  clarity). The concrete proof can be written as induction on the headroom:

  (1) Base case (headroom = 0, i.e., rank = n − 2):
      Unfold `LadderShape` at `s.shape`; the `dif_neg` branch fires because
      `n − 2 + 2 < n` is false, so `s.shape : False`.  Apply `s.shape.elim`.
      (This base case is vacuously true — it proves the ∃ k goal from False.)

  (2) Inductive step (headroom = h + 1):
      Either the board after the White ply is already checkmate for Black …
        · If `IsCheckmate (ladderStep s.shape).board .Black` holds, use k = 0.
          (One subtle point: the k in the goal indexes full cycles White+Black,
          so k = 0 means the board is already checkmate before any Black reply.
          Confirm the iteration at 0 returns `s₀.board` untouched — that's
          `Function.iterate_zero` — and close with the checkmate witness.)
        … or it is not checkmate, so a legal Black reply exists …
        · If not, `hreply s` gives a legal Black reply.  Apply
          `LadderShape.preservation s.shape (hreply s)` to obtain `s' : LadderState n`
          with `s'.rank.val = s.rank.val + 1` and headroom h.
        · Apply the inductive hypothesis to `s'` with the same `reply` and
          the same `hreply` (which quantifies over all `LadderState`s) to get
          `k'` and the checkmate proof for `(step^[k'] s').board`.
        · Set k = k' + 1 and rewrite `step^[k'+1] s₀ = step^[k'] (step s₀) = step^[k'] s'`
          using `Function.iterate_succ_apply`.

  ── Decidability of `IsCheckmate` ────────────────────────────────────────────

  To perform the case split "is the board checkmate or not" we need
  `Decidable (IsCheckmate b .Black)`.  `IsCheckmate` is built from
  `IsInCheck` (which is a finite conjunction of board-lookup equalities) and
  `∀ src dst, ¬ IsLegalMove b src dst` (a finite universal over `Fin n × Fin n`,
  hence decidable on a finite board).  Both facts should follow from
  `DecidableEq` on `Piece` and finiteness of `Fin n`.

  ── Choosing k explicitly ────────────────────────────────────────────────────

  If we want a computable witness rather than a classical existence proof we
  can instead run the iteration up to the hard bound K and check at each step:

      decide_ladder_mate : ∀ s : LadderState n,
          ∃ k ≤ n − 2 − s.rank.val,
            IsCheckmate (step^[k] s).board .Black

  proved by Nat.rec on the headroom, using decidability of `IsCheckmate` at each
  step to pick k = 0 or recurse.  The bound k ≤ K is a pleasant bonus: it gives
  a concrete worst-case number of full cycles.

  ── What `LadderShape.preservation` must actually show ───────────────────────

  The inductive step leans entirely on `preservation` (currently `sorry`'d).
  That theorem needs to establish:
  · The white pieces stay in their prescribed slots after the White ply.
  · Any legal Black reply cannot capture a white rook or king (the rooks sit
    on the file boundary the black king cannot cross, and the king is protected).
  · The black king remains strictly above `rookAPos` rank after the Black reply.
  · The board remains a legal setup.
  Proving preservation is the hard part; once it is in place the termination
  argument above is almost purely combinatorial.
  -/
