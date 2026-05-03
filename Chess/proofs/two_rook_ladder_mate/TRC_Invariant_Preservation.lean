import ChessRules
import TRC_FunctionWithInvariant
import TRC_Invariant_SimpleCases
import TRC_Invariant_PieceLocations
import TRC_Q_Lemma
import TRC_Invariant_BlackEmpty
import HelperLemmas
import NextWhiteMoveIsLegal
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
    · sorry  -- black king's rank is strictly above rookA
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
    · sorry  -- black king's rank is strictly above rookA
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
        IsLegalMove (applyLadderStep s.shape)
                    (reply (applyLadderStep s.shape)).1
                    (reply (applyLadderStep s.shape)).2) :
    ∃ k : Nat,
      IsCheckmate
        ((fun s : LadderState n =>
            { board := applyMove (applyLadderStep s.shape)
                         (reply (applyLadderStep s.shape)).1
                         (reply (applyLadderStep s.shape)).2
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
        · If `IsCheckmate (applyLadderStep s.shape).board .Black` holds, use k = 0.
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
