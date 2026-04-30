import ChessRules
import FunctionDefinition
import HelperLemmas
import NextWhiteMoveIsLegal

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
-- WHITE-PIECE POSITIONS AFTER ONE LADDER PLY (lemma A)
-- ------------------------------------------------------------
-- After white's ladder ply, the three white pieces sit at specific
-- squares determined by the original phase. Two pieces are unchanged
-- (proved via `NoCaptureMove_PreservesPiece`); the third is at the
-- move's `dst`. We split by phase because the configuration after
-- moveK has the king on rank+1, which doesn't match any
-- `LadderShape` position helper using the original `h`.

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
  show
    (applyMove board (nextWhiteMove lsh).1 (nextWhiteMove lsh).2)
      (kingPos rank lsh.hRfits) = some ⟨.White, .King⟩ ∧
    (applyMove board (nextWhiteMove lsh).1 (nextWhiteMove lsh).2)
      (rookBPos rank .moveRa lsh.hRfits) = some ⟨.White, .Rook⟩ ∧
    (applyMove board (nextWhiteMove lsh).1 (nextWhiteMove lsh).2)
      (rookAPos rank .moveRa lsh.hRfits) = some ⟨.White, .Rook⟩
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
  show
    (applyMove board (nextWhiteMove lsh).1 (nextWhiteMove lsh).2)
      (kingPos rank lsh.hRfits) = some ⟨.White, .King⟩ ∧
    (applyMove board (nextWhiteMove lsh).1 (nextWhiteMove lsh).2)
      (rookBPos rank .moveK lsh.hRfits) = some ⟨.White, .Rook⟩ ∧
    (applyMove board (nextWhiteMove lsh).1 (nextWhiteMove lsh).2)
      (rookAPos rank .moveK lsh.hRfits) = some ⟨.White, .Rook⟩
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
-- The king's new square doesn't match any `kingPos rank _`, so we use
-- the raw position (which is `(nextWhiteMove lsh).2`).
lemma LadderStep_PiecesAt_moveK {n : Nat} {board : Board n} {rank : Fin n}
    (lsh : LadderShape board rank .moveK) :
    let h := lsh.hRfits
    let b' := ladderStep lsh
    b' (nextWhiteMove lsh).2 = some ⟨.White, .King⟩ ∧
    b' (rookBPos rank .moveK h) = some ⟨.White, .Rook⟩ ∧
    b' (rookAPos rank .moveK h) = some ⟨.White, .Rook⟩ := by
  obtain ⟨_, hK_at, hRb_at, hRa_at, _⟩ := lsh.unfold
  have dst_empty := LadderMove_IntoEmptySquare lsh
  have h_src_eq : (nextWhiteMove lsh).1 = kingPos rank lsh.hRfits := rfl
  refine ⟨?_, ?_, ?_⟩
  · -- King moved to dst
    show (applyMove board _ _).pieces _ = _
    unfold applyMove; simp; rw [h_src_eq]; exact hK_at
  · -- Rb unchanged at (rank+1, 1)
    apply NoCaptureMove_PreservesPiece _ _ _ _ _ hRb_at _ dst_empty
    rw [h_src_eq]; intro heq
    have := congrArg (fun p : Pos n => p.file.val) heq
    simp [kingPos, rookBPos] at this
  · -- Ra unchanged at (rank+2, 0)
    apply NoCaptureMove_PreservesPiece _ _ _ _ _ hRa_at _ dst_empty
    rw [h_src_eq]; intro heq
    have := congrArg (fun p : Pos n => p.rank.val) heq
    simp [kingPos, rookAPos] at this


-- ------------------------------------------------------------
-- WHITE-PIECE PRESERVATION (assumption S: black's move is non-capture)
-- ------------------------------------------------------------
-- Under the simplifying assumption that black's move targets an empty
-- square (no white piece is captured), every white piece is preserved
-- by the full White+Black cycle. The argument: lemma A gives the
-- post-white positions; the black piece sits on a black square, so
-- `bsrc` differs from each white square; lemma B then propagates each
-- white piece across black's ply.

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

-- moveRb case
lemma LadderShape_WhitePiecesPreserved_moveRb {n : Nat} {board : Board n}
    {rank : Fin n}
    (lsh : LadderShape board rank .moveRb) {bsrc bdst : Pos n}
    (black_move : IsLegalMove (ladderStep lsh) bsrc bdst)
    (bdst_empty : (ladderStep lsh) bdst = none) :
    let h := lsh.hRfits
    let b'' := applyMove (ladderStep lsh) bsrc bdst
    b'' (kingPos rank h) = some ⟨.White, .King⟩ ∧
    b'' (rookBPos rank .moveRa h) = some ⟨.White, .Rook⟩ ∧
    b'' (rookAPos rank .moveRa h) = some ⟨.White, .Rook⟩ := by
  obtain ⟨hK_step, hRb_step, hRa_step⟩ := LadderStep_PiecesAt_moveRb lsh
  have hbsrc := blackMove_src_isBlack lsh black_move
  exact ⟨whitePiecePreserved hK_step rfl hbsrc bdst_empty,
         whitePiecePreserved hRb_step rfl hbsrc bdst_empty,
         whitePiecePreserved hRa_step rfl hbsrc bdst_empty⟩

-- moveRa case
lemma LadderShape_WhitePiecesPreserved_moveRa {n : Nat} {board : Board n}
    {rank : Fin n}
    (lsh : LadderShape board rank .moveRa) {bsrc bdst : Pos n}
    (black_move : IsLegalMove (ladderStep lsh) bsrc bdst)
    (bdst_empty : (ladderStep lsh) bdst = none) :
    let h := lsh.hRfits
    let b'' := applyMove (ladderStep lsh) bsrc bdst
    b'' (kingPos rank h) = some ⟨.White, .King⟩ ∧
    b'' (rookBPos rank .moveK h) = some ⟨.White, .Rook⟩ ∧
    b'' (rookAPos rank .moveK h) = some ⟨.White, .Rook⟩ := by
  obtain ⟨hK_step, hRb_step, hRa_step⟩ := LadderStep_PiecesAt_moveRa lsh
  have hbsrc := blackMove_src_isBlack lsh black_move
  exact ⟨whitePiecePreserved hK_step rfl hbsrc bdst_empty,
         whitePiecePreserved hRb_step rfl hbsrc bdst_empty,
         whitePiecePreserved hRa_step rfl hbsrc bdst_empty⟩

-- moveK case
lemma LadderShape_WhitePiecesPreserved_moveK {n : Nat} {board : Board n}
    {rank : Fin n}
    (lsh : LadderShape board rank .moveK) {bsrc bdst : Pos n}
    (black_move : IsLegalMove (ladderStep lsh) bsrc bdst)
    (bdst_empty : (ladderStep lsh) bdst = none) :
    let h := lsh.hRfits
    let b'' := applyMove (ladderStep lsh) bsrc bdst
    b'' (nextWhiteMove lsh).2 = some ⟨.White, .King⟩ ∧
    b'' (rookBPos rank .moveK h) = some ⟨.White, .Rook⟩ ∧
    b'' (rookAPos rank .moveK h) = some ⟨.White, .Rook⟩ := by
  obtain ⟨hK_step, hRb_step, hRa_step⟩ := LadderStep_PiecesAt_moveK lsh
  have hbsrc := blackMove_src_isBlack lsh black_move
  exact ⟨whitePiecePreserved hK_step rfl hbsrc bdst_empty,
         whitePiecePreserved hRb_step rfl hbsrc bdst_empty,
         whitePiecePreserved hRa_step rfl hbsrc bdst_empty⟩


-- ------------------------------------------------------------
-- PRESERVATION THEOREM (statement only)
-- ------------------------------------------------------------
theorem LadderShape.preservation {n : Nat} {board : Board n}
    {rank : Fin n} {φ : LadderPhase}
    (lsh : LadderShape board rank φ)
    {bsrc bdst : Pos n}
    (black_move : IsLegalMove (ladderStep lsh) bsrc bdst) :
    LadderShape
      (applyMove (ladderStep lsh) bsrc bdst)
      (nextRank rank φ lsh.hRfits)
      (nextPhase φ) := by
  sorry


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
              shape := LadderShape.preservation s.shape (hreply s) })^[k] s₀).board
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
