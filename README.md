# Mini Chess in Lean 4

A formal verification project implementing a tiny chess variant (Kings and Rooks on an n×n board) in Lean 4, combining executable game logic with mathematical proofs about chess rules and combinatorics.

## Project Structure

```
Chess/
├── ChessRules.lean          # Core types, predicates, and game logic
├── ChessTests.lean          # Compile-time correctness tests (#guard)
└── proofs/
    ├── HowManyRooks.lean    # Proof: at most n non-attacking rooks fit on n×n board
    └── TwoKingNoCheckmate.lean  # Proof: checkmate is impossible with only two kings
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

**Rook attacks** (`RookAttacks b src tgt`): True when `src ≠ tgt`, they share a row or column, and no piece occupies any square strictly between them. The `Between a b x` helper handles either ordering of `a` and `b`.

**King attacks** (`KingAttacks src tgt`): True when `src ≠ tgt` and both coordinates are within one step (`WithinOne`), covering all 8 adjacent squares including diagonals.

### Check and Checkmate

**`IsCheck b c`**: Color `c`'s king is under attack by any opponent piece (Rook or King) anywhere on the board.

**`IsCheckmate b c`**: The king is in check and every legal move by every friendly piece (both kings and rooks) leaves the king still in check. This covers escape, capture, and interposition.

**`IsLegalSetup b`**: The board has exactly one White King, exactly one Black King (`∃!`), and the two kings do not attack each other.

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
   - **King:** The attacking king is unique (from `∃!`), so it must be the opponent's king. But `KingAttacks` is symmetric (`KingAttacks_comm`), contradicting `hno_attack`.
4. No check → no checkmate (by `not_check_implies_not_checkmate`).

## Dependencies

- **Lean 4** v4.30.0-rc2
- **Mathlib** v4.30.0-rc2
  - `Mathlib.Logic.ExistsUnique` — for the `∃!` quantifier in `IsLegalSetup`
  - `Mathlib.Data.List.Perm.Subperm` — for the rook-counting proof
  - `Mathlib.Data.List.FinRange` — for finite enumeration

## Building

```bash
lake build
```

This compiles all four targets (`ChessRules`, `ChessTests`, `HowManyRooks`, `TwoKingNoCheckmate`) and runs all `#guard` tests at compile time.
