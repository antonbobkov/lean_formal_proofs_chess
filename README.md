# Mini Chess in Lean 4

A formal verification project implementing a tiny chess variant (Kings and Rooks on an n×n board) in Lean 4, combining executable game logic with mathematical proofs about chess rules and combinatorics.

## Project Structure

```
Chess/
├── ChessRules.lean          # Core types, predicates, and game logic
├── ChessTests.lean          # Compile-time correctness tests (#guard)
└── proofs/
    ├── BasicProofs.lean         # Symmetry of king attacks; kings-not-adjacent
    ├── HelperLemmas.lean        # Shared move/check/counting lemmas
    ├── HowManyRooks.lean        # Proof: at most n non-attacking rooks fit on n×n board
    ├── TwoKingNoCheckmate.lean  # Proof: checkmate is impossible with only two kings
    └── two_rook_ladder_mate/    # In progress: K+2R vs K forces mate
        ├── TRC_FunctionWithInvariant.lean   # LadderShape invariant + move function
        ├── LadderStepIsLegal.lean           # White's ladder ply is always legal
        ├── TRC_Invariant_SimpleCases.lean   # Turn / legal-setup / only-black-king conjuncts
        ├── TRC_Invariant_PieceLocations.lean # Where the white pieces sit after the ply
        ├── TRC_Q_Lemma.lean                 # "Only three white squares" via cardinality
        ├── TRC_Invariant_BlackEmpty.lean    # Black's reply targets an empty square
        ├── TRC_Invariant_CheckLocations.lean # White-piece-free regions on the step board
        ├── TRC_Invariant_KingRank.lean      # Black king stays above rook A
        ├── TRC_Invariant_Preservation.lean  # The inductive invariant theorem
        ├── TRC_FinalState.lean              # Mate at the final state (open)
        ├── TRC_BlackHasLegalMove.lean       # Black always has a reply until mate (open)
        ├── TRC_Termination.lean             # The ladder terminates in mate (open)
        └── TRC_Tests.lean                   # #guard sanity checks on an 8×8 ladder
```

## Overview

The project models a simplified chess game with only Kings and Rooks. Every game predicate — check, checkmate, legal setup — is implemented as a decidable `Prop`, meaning Lean can evaluate it computationally at compile time. This dual nature (proof-relevant and executable) is the central design goal.

## Core Types

**`Color`** — `.White` | `.Black`, with `Color.opponent` for flipping sides.

**`PieceType`** — `.King` | `.Rook`.

**`Piece`** — A record bundling `color : Color` and `kind : PieceType`.

**`Pos n`** — A position on an n×n board, defined as `Fin n × Fin n`. The type system statically enforces that coordinates stay in bounds.

**`Board n`** — A function `Pos n → Option Piece` mapping each square to its optional occupant.

## Game Logic

### Decidability Infrastructure

`allPositions n` enumerates all n² squares in row-major order. The key theorem `mem_allPositions` proves every position appears in this list, which enables two critical instances:

```lean
instance instDecidableForallPos : Decidable (∀ p : Pos n, P p)
instance instDecidableExistsPos : Decidable (∃ p : Pos n, P p)
```

These convert quantification over all board squares into finite list checks, making every board predicate decidable.

### Attack Rules

**Rook attacks** (`ValidRookMove b src tgt`): True when `src ≠ tgt`, they share a row or column, and no piece occupies any square strictly between them. The `Between a b x` helper handles either ordering of `a` and `b`.

**King attacks** (`ValidKingMove src tgt`): True when `src ≠ tgt` and both coordinates are within one step (`WithinOne`), covering all 8 adjacent squares including diagonals.

### Check and Checkmate

**`IsCheck b c`**: Color `c`'s king is under attack by any opponent piece (Rook or King) anywhere on the board.

**`IsCheckmate b c`**: The king is in check and every legal move by every friendly piece (both kings and rooks) leaves the king still in check. This covers escape, capture, and interposition.

**`IsLegalSetup b`**: The board has exactly one White King, exactly one Black King (`∃!`), and the side that just moved (`b.turn.opponent`) is not in check. Since `applyMove` flips the turn, requiring `IsLegalSetup` of the *result* board is exactly the rule that you may not move into — or stay in — check. Kings never being adjacent is a consequence, not a separate clause (`IsLegalSetup.kings_not_adjacent` in `BasicProofs.lean`).

**`IsLegalMove b src dst`**: The piece at `src` belongs to the side to move, its movement is geometrically valid for its kind (`PieceMoveLogic`), the target is not occupied by a friendly piece, and the resulting board is an `IsLegalSetup`.

## Compile-Time Tests

`ChessTests.lean` uses `#guard` to assert correctness at compile time — no runtime required:

- **Rook checks:** Horizontal/vertical attacks, blocking by friendly pieces, diagonals don't count
- **King checks:** Adjacent squares (including diagonals), out-of-range squares
- **Edge cases:** Missing kings, two-king boards, corner positions
- **Legal setup:** One king each far apart (legal), adjacent kings (illegal), missing/duplicate kings (illegal)
- **Checkmate scenarios:** Three-rook mate, escapable check, capturable attacker, blockable rook

Example checkmate position (4×4 board):
```
BK . . .    ← Black king trapped at (0,0)
WR . . .    ← Rook controls column 0
WR . . .    ← Rook controls (1,0) escape square
. . . WR    ← Rook controls row 0
```

## Formal Proofs

### HowManyRooks — Combinatorial Bound

**Theorem:** At most n non-attacking rooks fit on an n×n board.

```lean
theorem rooks_le {n : Nat} (ps : List (Fin n × Fin n))
    (hnd : ps.Nodup) (hna : nonAttackingRooks ps) : ps.length ≤ n
```

**Proof sketch:**
1. Non-attacking rooks must occupy distinct rows (`row_nodup` lemma, proved by list induction).
2. A list of distinct `Fin n` values has length ≤ n (`nodup_fin_length_le`, using Mathlib's subpermutation library).
3. The row list has the same length as the original list.

This is essentially the Pigeonhole Principle: n distinct rows → at most n rooks.

### TwoKingNoCheckmate — Endgame Impossibility

**Theorem:** When only kings remain on a legal board, neither player can be in checkmate.

```lean
theorem checkmate_impossible_two_kings {n : Nat} (b : Board n)
    (hlegal : IsLegalSetup b) (hokings : only_kings_on_board b) :
    ∀ c, ¬IsCheckmate b c
```

**Proof sketch:**
1. A legal setup guarantees the two kings are not adjacent (`hno_attack`).
2. Assume for contradiction that a king is in check.
3. The attacking piece must be a Rook or a King.
   - **Rook:** Contradicts `only_kings_on_board` — no rooks exist.
   - **King:** The attacking king is unique (from `∃!`), so it must be the opponent's king. But `ValidKingMove` is symmetric (`ValidKingMove_comm`), contradicting `hno_attack`.
4. No check → no checkmate (by `not_check_implies_not_checkmate`).

### TwoRookLadderMate — Forced Mate (in progress)

**Goal:** White (King + two Rooks) mates Black (lone King) on an n×n board, whatever Black plays.

White follows the textbook ladder: with base rank `R`, the pieces sit at `K = (R,0)`, `R_b = (R,1)`, `R_a = (R+1,0)`, and a three-ply cycle shifts the whole setup up one rank.

| phase | White's ply | K | R_b | R_a |
|---|---|---|---|---|
| `.moveRb` | `R_b : (R,1) → (R+1,1)` | `(R,0)` | `(R,1)` | `(R+1,0)` |
| `.moveRa` | `R_a : (R+1,0) → (R+2,0)` | `(R,0)` | `(R+1,1)` | `(R+1,0)` |
| `.moveK`  | `K : (R,0) → (R+1,0)`   | `(R,0)` | `(R+1,1)` | `(R+2,0)` |

`LadderShape board rank φ` is the invariant: White to move, the three white pieces on their phase squares, *no other* white piece anywhere, the black king strictly above `R_a`'s rank, no black rook, and `IsLegalSetup`. It is a decidable `Prop`, so `TRC_Tests.lean` checks concrete 8×8 boards with `#guard`. `ladderStep` reads the next White move off a `LadderShape` proof, and `LadderState n` bundles a board with its invariant so cycles can be iterated with `^[k]`.

**Proved:**

```lean
theorem ladderStep_isLegal      -- White's ladder ply is always a legal move
theorem LadderShape.preservation -- one White ply + ANY legal Black reply
                                 -- ⟹ LadderShape at the next rank/phase
```

`preservation` is the bulk of the work: each conjunct of the invariant has its own transport lemma, with the "only three white squares" clause going through a `Finset.card` argument in `HelperLemmas.lean`, and the black-king rank bound handled phase by phase in `TRC_Invariant_KingRank.lean`.

In `TRC_FinalState.lean`, mate at the final state is assembled from three facts: rook A lands on `(n-1,0)` giving check, no king destination escapes it, and Black has no rook. The third (`LadderStep_NoBlackRook`) is proved outright, and `IsCheckmate_AtFinal` assembles all three — so that theorem type-checks today, but still depends on `sorryAx` through its two open inputs.

**Still open** (5 `sorry`s — the build reports each one):

- `TRC_FinalState.lean` — `LadderStep_IsCheck_AtFinal` and `LadderStep_NoKingEscape_AtFinal`, the geometry of the mating position. The latter is the substantial one.
- `TRC_BlackHasLegalMove.lean` — `Black_HasLegalReply_NonFinal`: away from the final state the black king has a destination that is legal, i.e. genuinely unattacked by both rooks and the white king. (`blackLegalReply_isLegal` is then just the `Classical.indefiniteDescription` spec.)
- `TRC_Termination.lean` — `exists_iter_final`: iterating the cycle reaches a final state, by induction on the lexicographic measure `(n - 3 - rank, phase distance to .moveRa)`.

**On the shape of the termination statement:** `hreply` — the assumption that Black's chosen move is legal — is required only at *non-final* states. Quantifying it over all states would make the theorem vacuous: at a final state Black is checkmated, so no legal Black move exists and the hypothesis could never be satisfied. Correspondingly, `ladderCycleStep` treats final states as fixed points. `Black_HasLegalReply_NonFinal` (once proved) shows the restricted hypothesis is inhabited, i.e. that some Black strategy actually satisfies it.

## Dependencies

- **Lean 4** v4.30.0-rc2
- **Mathlib** v4.30.0-rc2
  - `Mathlib.Logic.ExistsUnique` — for the `∃!` quantifier in `IsLegalSetup`
  - `Mathlib.Data.List.Perm.Subperm` — for the rook-counting proof
  - `Mathlib.Data.List.FinRange` — for finite enumeration
  - `Mathlib.Data.Finset.Card` — for the white-piece counting argument

## Building

```bash
lake build
```

This compiles every library in `lakefile.toml` and runs all `#guard` tests at compile time. The build succeeds; it emits `declaration uses 'sorry'` warnings for the five open goals in `TRC_FinalState.lean`, `TRC_BlackHasLegalMove.lean`, and `TRC_Termination.lean`. Note that a declaration built *on top of* an open goal gets no warning of its own — use `#print axioms` to check whether a given theorem is genuinely sorry-free.

To build a single piece of the development, name its library, e.g.:

```bash
lake build HowManyRooks
lake build TRC_Invariant_Preservation
```
