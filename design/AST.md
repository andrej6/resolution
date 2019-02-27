# AST design specification

(Considering only propositional logic for the time being; this will need to
be extended for first-order logic.)

## AST definition

The AST consists of the following node types:

- Conjunction (`&`) -- two children
- Disjunction (`|`) -- two children
- Negation (`~`) -- one child
- Implication (`->`) -- two children
- Biconditional (`<->`) -- two children
- Identifier (string) -- leaf node
- Tautology (`T`) -- leaf node
- Contradiction/bottom (`F`) -- leaf node

We will refer to ID nodes, tautology, and contradiction collectively as literals.
(This is a slight departure from the usual terminology for propositional logic,
in which a literal is either a proposition or a negation of a proposition.)

## AST transformations

We can translate various logical equivalences into transformations of the AST:

- Associativity and commutativity of `&`, `|`, and `<->`:
  ```
     [&]             [&]
     / \             / \
   [&]  R    <=>    P  [&]
   / \                 / \
  P   Q               Q   R

    [&]             [&]
    / \      <=>    / \
   P   Q           Q   P

  (Similar for [|] and [<->])
  ```

- Representation of `->` and `<->` in terms of `&`, `|`, and `~`:
  ```
   [->]           [|]
   /  \    <=>    / \
  P    Q        [~]  Q
                 |
                 P

  [<->]             [|]
   / \     <=>    ,--'--.
  P   Q         [&]     [&]
                / \     / \
               P   Q  [~] [~]
                       |   |
                       P   Q
  ```

- Distributivity of `&` and `|`:
  ```
   [&]                 [|]
   / \              ,---'---.
  P  [|]    <=>    [&]     [&]
     / \           / \     / \
    Q   R         P   Q   P   R

   [|]                 [&]
   / \              ,---'---.
  P  [&]    <=>    [|]     [|]
     / \           / \     / \
    Q   R         P   Q   P   R
  ```

- DeMorgan's laws:
  ```
   [~]             [|]
    |              / \
   [&]    <=>    [~] [~]
   / \            |   |
  P   Q           P   Q

   [~]             [&]
    |              / \
   [|]    <=>    [~] [~]
   / \            |   |
  P   Q           P   Q
  ```

- Double negation:
  ```
  [~]
   |
  [~]    <=>    P
   |
   P
  ```

## Canonical forms

We will say that the _canonical form_ of an AST `T` is the logically equivalent
tree `T_can`, produced by repeated application of the associativity transformations,
in which all chains of associative nodes are fully left-recursive. That is,
each `&` node may have at most one `&` node as a child, and that child must be the left
child; similar for `|` and `<->`. An algorithm for generating such a tree is:

- While the root node is of the form `P & (Q & R)`, (similar for `|` and `<->`,)
  apply the associativity transformation to make it `(P & Q) & R`.
- Recurse on the left and right subtrees.

We will usually be interested in transforming a statement into CNF. A canonical CNF tree
is defined by the following properties:
1. The tree contains no nodes except `&`, `|`, `~`, and literals (ID's, tautology, or contradiction).
2. No `&` node is an ancestor of any `|` node, (the tree is purely conjunctions of disjunctions,)
3. No `&` or `|` node is an ancestor of any `~` node, (only literals are negated,)
4. The tree is in canonical form.

Breaking it down further:
1. The root node is `&`, `|`, `~`, or a literal.
2. The left child of every `&` is one of `&`, `|`, `~`, or a literal.
3. The right child of every `&` is one of `|`, `~, or a literal.
4. The left child of every `|` is one of `|`, `~`, or a literal.
5. The right child of every `|` is one of `~` or a literal.
6. The child of every `~` is a literal.

An algorithm to convert from an arbitrary AST to a canonical CNF tree is as follows.
It proceeds in phases, each of which should be iterated on the root node until it
is no longer applicable, and then applied recursively to the root's subtrees, before
moving on to the next phase.
1. Destructure `->` and `<->` nodes:
  - `P -> Q  =>  ~P | Q`
  - `P <-> Q  =>  (P & Q) | (~P & ~Q)`

  (After this phase, the tree will consist only of `&`, `|`, and literal nodes.)

2. Apply DeMorgan's laws and eliminate double negation:
  - `~(P & Q)  =>  ~P | ~Q`
  - `~(P | Q)  =>  ~P & ~Q`
  - ~~P  =>  P

  After this phase, only literals will be children of `~` nodes.

3. Commute certain `&` and `|` nodes. Specifically:
  - `(P | Q) & R  =>  R & (P | Q)` where `R` is not a `|` node
  - `(P & Q) | R  =>  R | (P & Q)` where `R` is not a `&` node

  This phase is not strictly necessary, but it simplifies the next phase by
  limiting the number of patterns that need to be searched for.

3. Distribute `|` nodes and un-distribute `&` nodes:
  - `P | (Q & R)  => (P | Q) & (P | R)`
  - `(P & Q) | (P & R)  =>  P & (Q | R)`

  A node of the form `(P & Q) | (R & S)` should be handled by first
  checking if either of `P` or `Q` is equal to either of `R` or `S`.
  If so, the `&` should be un-distributed. Otherwise,
  `(P & Q)`, as a single node, should be distributed over `R & S`.

  After this phase, no `&` nodes will be ancestors of `|` nodes.

4. Canonicalize the tree, as described above.
