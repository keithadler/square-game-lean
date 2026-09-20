/-!
# The square achievement game on an `n × n` grid

Two players alternately mark cells of an `n × n` grid.  The first to own four
cells forming the corners of a square with horizontal and vertical sides wins.

This file sets up the game, defines what it means for the player to move to have
a forced win within a given number of plies, and builds a checker for winning
strategies presented as certificates.  The strategies themselves are in the
`Cert*` files.

Nothing here depends on Mathlib; only the Lean 4 core library is used.
-/

namespace SquareGame

/-! ## Boards and squares -/

/-- The four corners of an axis-aligned square, as cell numbers. -/
structure Sq where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat

/-- Every axis-aligned square of the `n × n` grid.  The cell in row `r` and
column `c` is numbered `r * n + c`; a square is determined by its top-left
corner `(r, c)` and its side length `d + 1 ≥ 1`. -/
def squares (n : Nat) : List Sq :=
  (List.range n).flatMap fun d =>
    (List.range n).flatMap fun r =>
      (List.range n).filterMap fun c =>
        if r + d + 1 < n ∧ c + d + 1 < n then
          some ⟨r * n + c, r * n + (c + d + 1),
                (r + d + 1) * n + c, (r + d + 1) * n + (c + d + 1)⟩
        else none

/-- A set of cells is encoded as a natural number: cell `i` belongs to it exactly
when bit `i` is set.  `wins sqs x` holds when the cell set `x` contains all four corners of one of
the squares in `sqs`. -/
def wins (sqs : List Sq) (x : Nat) : Bool :=
  sqs.any fun q => x.testBit q.c0 && x.testBit q.c1 && x.testBit q.c2 && x.testBit q.c3

/-! ## Forced wins -/

/--
`Forces sqs cells k a b` says: in the position on the board with cells
`0, …, cells - 1` where the player to move owns exactly the cells of `a` and the
opponent owns exactly those of `b`, the player to move can force the completion
of one of their own squares within `k` further plies, whatever the opponent does.

* `imm` — the player to move has a legal move that completes a square at once.
* `step` — the player to move has a legal move `m` after which the opponent has
  at least one legal reply (witnessed by `t`, so the board is not full and this
  is not a vacuous claim), no reply of the opponent completes a square for them,
  and after every reply the player is again in a position they force within
  `k` plies.
-/
inductive Forces (sqs : List Sq) (cells : Nat) : Nat → Nat → Nat → Prop
  | imm {k a b m} :
      m < cells → a.testBit m = false → b.testBit m = false →
      wins sqs (a ||| 2 ^ m) = true →
      Forces sqs cells (k + 1) a b
  | step {k a b m} (t : Nat) :
      m < cells → a.testBit m = false → b.testBit m = false →
      t < cells → (a ||| 2 ^ m).testBit t = false → b.testBit t = false →
      (∀ c, c < cells → (a ||| 2 ^ m).testBit c = false → b.testBit c = false →
          wins sqs (b ||| 2 ^ c) = false) →
      (∀ c, c < cells → (a ||| 2 ^ m).testBit c = false → b.testBit c = false →
          Forces sqs cells k (a ||| 2 ^ m) (b ||| 2 ^ c)) →
      Forces sqs cells (k + 2) a b

/-- A forced win within `j` plies is a forced win within any larger number. -/
theorem Forces.mono {sqs cells} :
    ∀ {j a b}, Forces sqs cells j a b → ∀ {k}, j ≤ k → Forces sqs cells k a b := by
  intro j a b h
  induction h with
  | @imm k a b m h1 h2 h3 h4 =>
      intro k' hk
      match k', hk with
      | k'' + 1, _ => exact Forces.imm h1 h2 h3 h4
  | @step k a b m t h1 h2 h3 h4 h5 h6 h7 _ ih =>
      intro k' hk
      match k', hk with
      | k'' + 2, hk' =>
          exact Forces.step t h1 h2 h3 h4 h5 h6 h7
            (fun c hc1 hc2 hc3 => ih c hc1 hc2 hc3 (by omega))

/-- Sanity check against a vacuous definition: with no squares at all, nobody can
force anything.  (If `Forces` could be satisfied by, say, filling the board, this
would fail.) -/
theorem Forces.not_of_no_squares {cells k a b} : ¬ Forces [] cells k a b := by
  intro h
  induction h with
  | @imm k a b m _ _ _ h4 => exact Bool.noConfusion h4
  | @step k a b m t _ _ _ h4 h5 h6 _ _ ih => exact ih t h4 h5 h6

/-! ## Reading off immediate threats -/

/-- The four corners of a square are four different cells.  The checker verifies
this for the board it is handed; the threat scan below would miss a case without
it, so it is a hypothesis rather than an assumption. -/
def Sq.distinct (q : Sq) : Bool :=
  (q.c0 != q.c1) && (q.c0 != q.c2) && (q.c0 != q.c3) &&
  (q.c1 != q.c2) && (q.c1 != q.c3) && (q.c2 != q.c3)

def allDistinct (sqs : List Sq) : Bool := sqs.all Sq.distinct

/-- `hasThreat sqs b occ` is `true` if some square has three of its corners in the
cell set `b` and its fourth corner free (outside `occ`). -/
def hasThreat (sqs : List Sq) (b occ : Nat) : Bool :=
  sqs.any fun q =>
    (b.testBit q.c1 && b.testBit q.c2 && b.testBit q.c3 && !occ.testBit q.c0) ||
    (b.testBit q.c0 && b.testBit q.c2 && b.testBit q.c3 && !occ.testBit q.c1) ||
    (b.testBit q.c0 && b.testBit q.c1 && b.testBit q.c3 && !occ.testBit q.c2) ||
    (b.testBit q.c0 && b.testBit q.c1 && b.testBit q.c2 && !occ.testBit q.c3)

theorem corner_eq {b c x : Nat} (h : (b ||| 2 ^ c).testBit x = true)
    (hb : b.testBit x = false) : x = c := by
  rw [Nat.testBit_or, hb, Bool.false_or, Nat.testBit_two_pow] at h
  exact (of_decide_eq_true h).symm

theorem wins_singleton_of {q : Sq} {x : Nat}
    (h0 : x.testBit q.c0 = true) (h1 : x.testBit q.c1 = true)
    (h2 : x.testBit q.c2 = true) (h3 : x.testBit q.c3 = true) : wins [q] x = true := by
  simp [wins, h0, h1, h2, h3]

/-- If no square has three of the opponent's cells and a free fourth, then no
reply of theirs completes a square.  `hb` rules out the degenerate case in which
the opponent has already completed one; `hd` is what makes "three corners in `b`"
the right test, since without it two corners of a square could be the same cell. -/
theorem no_reply_wins {sqs b occ c} (hd : allDistinct sqs = true) (hb : wins sqs b = false)
    (hT : hasThreat sqs b occ = false) (hc : occ.testBit c = false) :
    wins sqs (b ||| 2 ^ c) = false := by
  cases hw : wins sqs (b ||| 2 ^ c) with
  | false => rfl
  | true =>
    exfalso
    rw [wins, List.any_eq_true] at hw
    match hw with
    | ⟨q, hq, hqt⟩ =>
      simp only [Bool.and_eq_true] at hqt
      have h0 := hqt.1.1.1
      have h1 := hqt.1.1.2
      have h2 := hqt.1.2
      have h3 := hqt.2
      -- the corners of `q` are four different cells
      have hdq : Sq.distinct q = true := by
        rw [allDistinct, List.all_eq_true] at hd; exact hd q hq
      rw [Sq.distinct] at hdq
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hdq
      -- any corner the opponent does not own must be the cell `c`
      have hc0 : b.testBit q.c0 = false → q.c0 = c := fun h => corner_eq h0 h
      have hc1 : b.testBit q.c1 = false → q.c1 = c := fun h => corner_eq h1 h
      have hc2 : b.testBit q.c2 = false → q.c2 = c := fun h => corner_eq h2 h
      have hc3 : b.testBit q.c3 = false → q.c3 = c := fun h => corner_eq h3 h
      have hfire : hasThreat sqs b occ = true := by
        rw [hasThreat, List.any_eq_true]
        refine ⟨q, hq, ?_⟩
        by_cases e0 : b.testBit q.c0 = true
        · by_cases e1 : b.testBit q.c1 = true
          · by_cases e2 : b.testBit q.c2 = true
            · by_cases e3 : b.testBit q.c3 = true
              · exfalso
                have : wins sqs b = true := by
                  rw [wins, List.any_eq_true]; exact ⟨q, hq, by simp [e0, e1, e2, e3]⟩
                rw [this] at hb; exact Bool.noConfusion hb
              · have h3c : q.c3 = c := hc3 (by simpa using e3)
                simp [e0, e1, e2, h3c, hc]
            · have h2c : q.c2 = c := hc2 (by simpa using e2)
              have e3 : b.testBit q.c3 = true := by
                cases h : b.testBit q.c3 with
                | true => rfl
                | false => exact absurd (h2c.trans (hc3 h).symm) hdq.2
              simp [e0, e1, e3, h2c, hc]
          · have h1c : q.c1 = c := hc1 (by simpa using e1)
            have e2 : b.testBit q.c2 = true := by
              cases h : b.testBit q.c2 with
              | true => rfl
              | false => exact absurd (h1c.trans (hc2 h).symm) hdq.1.1.2
            have e3 : b.testBit q.c3 = true := by
              cases h : b.testBit q.c3 with
              | true => rfl
              | false => exact absurd (h1c.trans (hc3 h).symm) hdq.1.2
            simp [e0, e2, e3, h1c, hc]
        · have h0c : q.c0 = c := hc0 (by simpa using e0)
          have e1 : b.testBit q.c1 = true := by
            cases h : b.testBit q.c1 with
            | true => rfl
            | false => exact absurd (h0c.trans (hc1 h).symm) hdq.1.1.1.1.1
          have e2 : b.testBit q.c2 = true := by
            cases h : b.testBit q.c2 with
            | true => rfl
            | false => exact absurd (h0c.trans (hc2 h).symm) hdq.1.1.1.1.2
          have e3 : b.testBit q.c3 = true := by
            cases h : b.testBit q.c3 with
            | true => rfl
            | false => exact absurd (h0c.trans (hc3 h).symm) hdq.1.1.1.2
          simp [e1, e2, e3, h0c, hc]
      rw [hfire] at hT
      exact Bool.noConfusion hT

end SquareGame

namespace SquareGame

/-! ## Certificates

A winning strategy is presented as a directed acyclic graph of positions.  Each
node records a position with the first player to move, the move the strategy
plays there, and the indices of the nodes reached afterwards.  Because the same
position is reached by many different move orders, the graph is far smaller than
the corresponding tree, and every node is checked exactly once.
-/

/-- One node of a strategy certificate. -/
structure Node where
  /-- cells owned by the player to move -/
  a : Nat
  /-- cells owned by the opponent -/
  b : Nat
  /-- the number of plies within which the win is claimed -/
  d : Nat
  /-- `0` the move completes a square, `1` it makes one threat, `2` it makes
      none, `3` it makes two -/
  kind : Nat
  /-- the move the strategy plays -/
  mv : Nat
  /-- a threat cell, or (for `kind = 2`) any free cell -/
  t1 : Nat
  /-- the second threat cell, when `kind = 3` -/
  t2 : Nat
  /-- the children, by index -/
  kids : List Nat

/-- The nodes, stored as a binary tree on the index.  Nothing below relies on the
tree being ordered: `find` is allowed to return any node it likes, and then the
checks on that node simply fail. -/
inductive NTree where
  | nil : NTree
  | bin : NTree → Nat → Node → NTree → NTree

def NTree.find : NTree → Nat → Option Node
  | nil, _ => none
  | bin l k v r, i => if i < k then find l i else if k < i then find r i else some v

def NTree.all (t : NTree) (p : Nat → Node → Bool) : Bool :=
  match t with
  | nil => true
  | bin l k v r => NTree.all l p && p k v && NTree.all r p

inductive NTree.Mem : Nat → Node → NTree → Prop
  | here {l k v r} : Mem k v (bin l k v r)
  | left {l r k v k' v'} : Mem k v l → Mem k v (bin l k' v' r)
  | right {l r k v k' v'} : Mem k v r → Mem k v (bin l k' v' r)

theorem NTree.find_mem : ∀ {t : NTree} {i : Nat} {v : Node}, t.find i = some v → Mem i v t := by
  intro t
  induction t with
  | nil => intro i v h; rw [NTree.find] at h; simp at h
  | bin l k w r ihl ihr =>
      intro i v h
      rw [NTree.find] at h
      split at h
      · exact Mem.left (ihl h)
      · split at h
        · exact Mem.right (ihr h)
        · have hik : i = k := by omega
          have : v = w := by injection h with h'; exact h'.symm
          subst hik; subst this; exact Mem.here

theorem NTree.all_spec : ∀ {t : NTree} {p : Nat → Node → Bool} {k v},
    t.all p = true → Mem k v t → p k v = true := by
  intro t
  induction t with
  | nil => intro p k v _ hm; cases hm
  | bin l k' w r ihl ihr =>
      intro p k v hall hm
      rw [NTree.all] at hall
      simp only [Bool.and_eq_true] at hall
      cases hm with
      | here => exact hall.1.2
      | left h => exact ihl hall.1.1 h
      | right h => exact ihr hall.2 h

/-! ## Bit helpers -/

theorem testBit_or_false {x y c : Nat} (hx : x.testBit c = false) (hy : y.testBit c = false) :
    (x ||| y).testBit c = false := by rw [Nat.testBit_or, hx, hy]; rfl

theorem testBit_pow_ne {c t : Nat} (h : ¬ c = t) : (2 ^ c).testBit t = false := by
  rw [Nat.testBit_two_pow]; exact decide_eq_false h

theorem testBit_add_ne {b c t : Nat} (hb : b.testBit t = false) (h : ¬ c = t) :
    (b ||| 2 ^ c).testBit t = false := testBit_or_false hb (testBit_pow_ne h)

/-! ## The checker -/

/-- Check that node `j`, which must have been checked already, is the position
`(a, b)` with `d` plies to go. -/
def checkChild (t : NTree) (i a b d : Nat) (j : Nat) : Bool :=
  decide (j < i) &&
  match t.find j with
  | none => false
  | some nd => (nd.a == a) && (nd.b == b) && (nd.d == d)

theorem checkChild_spec {t i a b d j} (h : checkChild t i a b d j = true) :
    j < i ∧ ∃ nd, t.find j = some nd ∧ nd.a = a ∧ nd.b = b ∧ nd.d = d := by
  rw [checkChild] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  cases hf : t.find j with
  | none => rw [hf] at h2; exact Bool.noConfusion h2
  | some nd =>
      rw [hf] at h2
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      exact ⟨nd, rfl, h2.1.1, h2.1.2, h2.2⟩

/-- Check that `kids` lists a child for every free cell among the `n` cells
starting at `c`, in increasing order. -/
def chkKids (t : NTree) (i a' b d : Nat) : Nat → Nat → List Nat → Bool
  | 0, _, ks => ks.isEmpty
  | n + 1, c, ks =>
      if a'.testBit c || b.testBit c then chkKids t i a' b d n (c + 1) ks
      else
        match ks with
        | [] => false
        | j :: ks' => checkChild t i a' (b ||| 2 ^ c) d j && chkKids t i a' b d n (c + 1) ks'

theorem chkKids_spec {t i a' b d} : ∀ {n c ks}, chkKids t i a' b d n c ks = true →
    ∀ c', c ≤ c' → c' < c + n → a'.testBit c' = false → b.testBit c' = false →
      ∃ j, j < i ∧ ∃ nd, t.find j = some nd ∧ nd.a = a' ∧ nd.b = b ||| 2 ^ c' ∧ nd.d = d := by
  intro n
  induction n with
  | zero => intro c ks _ c' h1 h2; omega
  | succ n ih =>
      intro c ks h c' h1 h2 h3 h4
      simp only [chkKids] at h
      by_cases hc' : c = c'
      · subst hc'
        have : (a'.testBit c || b.testBit c) = false := by rw [h3, h4]; rfl
        rw [this] at h
        simp only [Bool.false_eq_true, ite_false] at h
        revert h
        cases ks with
        | nil => intro h; exact Bool.noConfusion h
        | cons j ks' =>
            intro h
            simp only [Bool.and_eq_true] at h
            have := checkChild_spec h.1
            exact ⟨j, this.1, this.2⟩
      · have hlt : c + 1 ≤ c' := by omega
        split at h
        · exact ih h c' hlt (by omega) h3 h4
        · revert h
          cases ks with
          | nil => intro h; exact Bool.noConfusion h
          | cons j ks' =>
              intro h
              simp only [Bool.and_eq_true] at h
              exact ih h.2 c' hlt (by omega) h3 h4

/-- The local check on one node of a certificate. -/
def checkNode (sqs : List Sq) (cells : Nat) (t : NTree) (i : Nat) (nd : Node) : Bool :=
  let a := nd.a
  let b := nd.b
  let a' := a ||| 2 ^ nd.mv
  let occ := a' ||| b
  decide (nd.mv < cells) && (a.testBit nd.mv == false) && (b.testBit nd.mv == false) &&
  match nd.kind with
  | 0 => decide (1 ≤ nd.d) && wins sqs a'
  | 1 =>
      decide (3 ≤ nd.d) && (wins sqs b == false) && (hasThreat sqs b occ == false) &&
      decide (nd.t1 < cells) && (a'.testBit nd.t1 == false) && (b.testBit nd.t1 == false) &&
      wins sqs (a' ||| 2 ^ nd.t1) &&
      (match nd.kids with
       | [j] => checkChild t i a' (b ||| 2 ^ nd.t1) (nd.d - 2) j
       | _ => false)
  | 2 =>
      decide (2 ≤ nd.d) && (wins sqs b == false) && (hasThreat sqs b occ == false) &&
      decide (nd.t1 < cells) && (a'.testBit nd.t1 == false) && (b.testBit nd.t1 == false) &&
      chkKids t i a' b (nd.d - 2) cells 0 nd.kids
  | 3 =>
      decide (3 ≤ nd.d) && (wins sqs b == false) && (hasThreat sqs b occ == false) &&
      decide (nd.t1 < cells) && (a'.testBit nd.t1 == false) && (b.testBit nd.t1 == false) &&
      decide (nd.t2 < cells) && (a'.testBit nd.t2 == false) && (b.testBit nd.t2 == false) &&
      (nd.t1 != nd.t2) && wins sqs (a' ||| 2 ^ nd.t1) && wins sqs (a' ||| 2 ^ nd.t2)
  | _ => false

/-- A certificate is accepted when every one of its nodes passes the local check. -/
def checkAll (sqs : List Sq) (cells : Nat) (t : NTree) : Bool :=
  t.all (checkNode sqs cells t)

end SquareGame

namespace SquareGame

/-- **Soundness of the checker.**  If every node of a certificate passes its
local check, then every node really is a position that the player to move wins
by force within the number of plies it claims. -/
theorem forces_of_checkAll {sqs cells t} (hdis : allDistinct sqs = true)
    (h : checkAll sqs cells t = true) :
    ∀ n i, i < n → ∀ nd, t.find i = some nd → Forces sqs cells nd.d nd.a nd.b := by
  intro n
  induction n with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro i hi nd hfind
    have hc : checkNode sqs cells t i nd = true :=
      NTree.all_spec h (NTree.find_mem hfind)
    rw [checkNode] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    have hmv : nd.mv < cells := hc.1.1.1
    have hma : nd.a.testBit nd.mv = false := hc.1.1.2
    have hmb : nd.b.testBit nd.mv = false := hc.1.2
    have hkind := hc.2
    split at hkind
    all_goals (try simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
                              bne_iff_ne, ne_eq] at hkind)
    · -- the move completes a square
      match hkind with
      | ⟨hd, hw⟩ =>
        have hdd : nd.d = (nd.d - 1) + 1 := by omega
        rw [hdd]
        exact Forces.imm hmv hma hmb hw
    · -- the move makes one threat, so the opponent's reply is forced
      match hkind with
      | ⟨⟨⟨⟨⟨⟨⟨hd, hwb⟩, hth⟩, ht1c⟩, ht1a⟩, ht1b⟩, hw1⟩, hkid⟩ =>
        split at hkid
        · rename_i j _
          have hcs := checkChild_spec hkid
          match hcs.2 with
          | ⟨nd', hf', ha', hb', hd'⟩ =>
            have hchild : Forces sqs cells nd'.d nd'.a nd'.b := ih j (by omega) nd' hf'
            rw [ha', hb', hd'] at hchild
            have hdd : nd.d = (nd.d - 2) + 2 := by omega
            rw [hdd]
            refine Forces.step nd.t1 hmv hma hmb ht1c ht1a ht1b ?_ ?_
            · intro c _ hc2 hc3
              exact no_reply_wins hdis hwb hth (testBit_or_false hc2 hc3)
            · intro c _ _ _
              by_cases hct : c = nd.t1
              · subst hct; exact hchild
              · exact Forces.mono
                  (Forces.imm (k := nd.d - 2 - 1) ht1c ht1a (testBit_add_ne ht1b hct) hw1)
                  (by omega)
        · exact Bool.noConfusion hkid
    · -- the move makes no threat, so every reply of the opponent is answered
      match hkind with
      | ⟨⟨⟨⟨⟨⟨hd, hwb⟩, hth⟩, ht1c⟩, ht1a⟩, ht1b⟩, hkid⟩ =>
        have hdd : nd.d = (nd.d - 2) + 2 := by omega
        rw [hdd]
        refine Forces.step nd.t1 hmv hma hmb ht1c ht1a ht1b ?_ ?_
        · intro c _ hc2 hc3
          exact no_reply_wins hdis hwb hth (testBit_or_false hc2 hc3)
        · intro c hc1 hc2 hc3
          match chkKids_spec hkid c (Nat.zero_le c) (by omega) hc2 hc3 with
          | ⟨j, hji, nd', hf', ha', hb', hd'⟩ =>
            have hchild : Forces sqs cells nd'.d nd'.a nd'.b := ih j (by omega) nd' hf'
            rw [ha', hb', hd'] at hchild
            exact hchild
    · -- the move makes two threats at once and only one can be blocked
      match hkind with
      | ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd, hwb⟩, hth⟩, ht1c⟩, ht1a⟩, ht1b⟩, ht2c⟩, ht2a⟩, ht2b⟩, hne⟩, hw1⟩, hw2⟩ =>
        have hdd : nd.d = (nd.d - 2) + 2 := by omega
        rw [hdd]
        refine Forces.step nd.t1 hmv hma hmb ht1c ht1a ht1b ?_ ?_
        · intro c _ hc2 hc3
          exact no_reply_wins hdis hwb hth (testBit_or_false hc2 hc3)
        · intro c _ _ _
          by_cases hct : c = nd.t1
          · subst hct
            exact Forces.mono
              (Forces.imm (k := nd.d - 2 - 1) ht2c ht2a (testBit_add_ne ht2b hne) hw2)
              (by omega)
          · exact Forces.mono
              (Forces.imm (k := nd.d - 2 - 1) ht1c ht1a (testBit_add_ne ht1b hct) hw1)
              (by omega)
    · exact Bool.noConfusion hkind

/-- A certificate together with the claim that node `root` is the empty board
with a win in `d` plies. -/
def rootOK (sqs : List Sq) (cells : Nat) (t : NTree) (root d : Nat) : Bool :=
  allDistinct sqs && checkAll sqs cells t &&
  match t.find root with
  | none => false
  | some nd => (nd.a == 0) && (nd.b == 0) && (nd.d == d)

/-- **The statement the certificates establish.**  On the board with cells
`0, …, cells - 1` and the squares `sqs`, the player who moves first on the empty
board can force a square of their own within `d` plies. -/
theorem first_player_forces {sqs cells t root d} (h : rootOK sqs cells t root d = true) :
    Forces sqs cells d 0 0 := by
  rw [rootOK] at h
  simp only [Bool.and_eq_true] at h
  have hdist := h.1.1
  have hall := h.1.2
  have h2 := h.2
  cases hf : t.find root with
  | none => rw [hf] at h2; exact Bool.noConfusion h2
  | some nd =>
      rw [hf] at h2
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      have hF := forces_of_checkAll hdist hall (root + 1) root (Nat.lt_succ_self root) nd hf
      rw [h2.1.1, h2.1.2, h2.2] at hF
      exact hF

end SquareGame
