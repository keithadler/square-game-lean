# The square achievement game, in Lean 4

A machine-checked proof that **the first player wins the square achievement game
on the `n × n` grid** for every size whose outcome was open: `6 ≤ n ≤ 14`.

Two players alternately mark cells of an `n × n` grid. The first to own four
cells at the corners of a square with horizontal and vertical sides wins; if the
board fills with neither doing so, the game is a draw. The problem is Martin
Erickson's, cataloged on
[Open Problem Garden](http://www.openproblemgarden.org/op/a_game_on_an_n_x_n_grid).
The outcome was known only for `n ≤ 5` (Jenrich 2012) and `n ≥ 15`
(Bacher–Eliahou 2010 plus strategy stealing). The nine sizes in between were
settled by search in
[keithadler/square-achievement-game](https://github.com/keithadler/square-achievement-game);
this repository is a proof of that result inside a proof assistant.

## What is proved

```lean
theorem first_player_wins_open_cases :
    Forces (squares 6) 36 15 0 0 ∧ Forces (squares 7) 49 15 0 0 ∧
    Forces (squares 8) 64 15 0 0 ∧ Forces (squares 9) 81 15 0 0 ∧
    Forces (squares 10) 100 15 0 0 ∧ Forces (squares 11) 121 15 0 0 ∧
    Forces (squares 12) 144 15 0 0 ∧ Forces (squares 13) 169 15 0 0 ∧
    Forces (squares 14) 196 15 0 0
```

`Forces sqs cells k a b` says that on a board whose cells are `0, …, cells - 1`
and whose winning sets are `sqs`, the player to move — owning the cells of `a`,
facing an opponent owning `b` — can force the completion of one of their own
squares within `k` further plies, whatever the opponent does. Instantiated at the
empty board, it says: *the first player, moving first, forces a square of their
own within 15 plies.*

`squares n` is defined in Lean as every axis-aligned square of the grid, from its
top-left corner and its side length. Its lengths agree with the solver's square
counts — 55, 91, 140, 204, 285, 385, 506, 650, 819 for `n = 6 … 14` — and for
`n = 6` the two enumerations agree as sets of cell quadruples.

### Why 15 plies and not 13

The original search reports a win "within 13 plies". That number counts the
search horizon, not the line. In `sq3.c` the immediate-win and double-threat
shortcuts are tested *before* the `rem <= 0` horizon check, so a node with no
remaining depth still reports a decided result — one ply later for an immediate
win, two for a double threat that cannot be blocked. A depth-`R` search therefore
certifies lines up to `R + 2` plies.

With the accounting corrected, a depth-13 search returns *undecided* on
`n = 6, 7, 8` and a depth-15 search returns a win, so 15 is the true bound there
and 14 is impossible by parity. The outcome — first player wins — is unaffected:
the shortcuts only fire on a genuinely forced win or loss, which is exactly the
argument the search rests on.

## How it works

Reproving a 700-million-node search inside a kernel is hopeless, so the strategy
is re-derived in a shape a kernel can check. In the certified strategy the first
player makes at most three moves that create no immediate threat; every other
move creates one, which forces the opponent's reply, or two, which cannot both be
blocked. Only the three unforced moves branch over all of the opponent's replies,
and because different move orders reach the same position, the strategy is stored
as a directed acyclic graph rather than a tree — 5,292 nodes for `n = 6` instead
of roughly 150,000. Each node is checked once.

| board | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| certificate nodes | 5,292 | 6,547 | 11,326 | 18,325 | 23,800 | 35,039 | 44,065 | 61,414 | 75,495 |

`SquareGame/Core.lean` holds the whole mathematical content:

| | |
|---|---|
| `squares` | the axis-aligned squares of the grid |
| `wins` | a cell set contains all four corners of some square |
| `Forces` | the inductive definition of a forced win within `k` plies |
| `Forces.mono` | a win within `j` plies is a win within any larger number |
| `Forces.not_of_no_squares` | with no squares nobody forces anything — a check against a vacuous definition |
| `no_reply_wins` | if no square has three of the opponent's cells and a free fourth, no reply of theirs wins |
| `checkNode`, `checkAll` | the local check on one certificate node, and on all of them |
| `forces_of_checkAll` | **soundness**: a certificate that passes really is a forced win |
| `first_player_forces` | the same, read off at the empty board |

Three traps are closed deliberately:

- `Forces.step` requires a witness that the opponent still has a legal reply, so
  "every reply loses" cannot be satisfied by a full board.
  `Forces.not_of_no_squares` is the sanity theorem that would fail if it could.
- `no_reply_wins` carries the hypothesis that the opponent has not already
  completed a square, without which the threat scan would miss a case.
- `rootOK` checks that the four corners of every square are four *different*
  cells. Without it, a square with a repeated corner would defeat the threat scan.

The checker is not decorative: it rejected the `n = 11` certificate, and the
rejection was a real bug — the generator's memo table had been switched to a
64-bit FNV fingerprint, FNV mixes a byte at a time, and fed whole 64-bit words it
left two positions colliding, so a node was linked to the wrong child.

## Trust

`Core.lean` depends only on Lean's own axioms (`propext`, `Classical.choice`,
`Quot.sound`) and on nothing outside the Lean 4 core library — no Mathlib.

Each board theorem additionally evaluates the checker on its certificate with
`native_decide`, which is performed by compiled code rather than by the kernel
and adds one axiom per board. `#print axioms first_player_wins_6` shows it.

Independently re-checked with [Tenet](https://github.com/keithadler/tenet), a
Lean 4 kernel on .NET that shares no code with Lean's own:

```
$ tenet check .
OK: 215 checked in 11 modules, 0 failed, 660 modules mapped, 4.8s
```

## Building

```sh
lake build
```

Lean 4.34.0, pinned in `lean-toolchain`. The certificates are large literals;
`Cert14` takes about an hour to elaborate and its `.olean` is 515 MB.
