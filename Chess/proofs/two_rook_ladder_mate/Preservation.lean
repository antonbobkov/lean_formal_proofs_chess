import ChessRules
import FunctionDefinition
import HelperLemmas

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
