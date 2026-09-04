# Clairvoyance

Clairvoyance is a [symbolic
execution](https://en.wikipedia.org/wiki/Symbolic_execution) engine for the
[Clarity](https://docs.stacks.co/learn/clarity) programming language.  Because
Clarity is a decidable language, it always is possible (albeit in many cases,
intractable) to compute _all of_ the halting states of any Clarity program, and in
doing so, determine the following:

* The necessary and sufficient conditions for reaching a halting state, in
  terms of the transaction arguments, runtime environment, and data space state
(collectively, the "inputs"),

* A formula over the inputs which describes the value computed by reaching the
  halting state;

* The set of data variables and map entries written upon reaching a given
  halting state, as well as the formulae describing their values and
key/value pairs, respectively;

* The complete reachability graph of a Clarity program -- i.e. what functions
  are reachable from others;

* The set of data variable and map mutations that can be reached from a given
  function.

In addition to symbolic execution, Clairvoyance supports simple automated
theorem proving as a means of checking a Clarity program's correctness.
Specifically, the developer may annotate a given Clarity expression in a
Clarity program (usually, a function definition) with a description of each of
its halting states, and Clairvoyance will check that the computed halting states
match the developer-given ones.  In doing so, the developer can use Clairvoyance
to prove that the Clarity code behaves exactly as specified, without having to
write an expansive set of unit tests.

## Introduction

Below is a "hello world" example, in which Clairvoyance is used to both compute
the program's halting states, and later to check that the halting states are
preserved in the face of subsequent program modification:

```clarity
(define-public (hello-for-the-nth-time (name (string-utf8 128)) (n uint))
    (let (
        (suffix
            (if (is-eq (mod n u10) u1)
                u"st"
            (if (is-eq (mod n u10) u2)
                u"nd"
            (if (is-eq (mod n u10) u3)
                u"rd"
                u"th")))))

    (ok (concat u"Hello, " name u", for the " (int-to-utf8 n) suffix u" time"))))
```

What ought to happen is that this function should produce a string with the
correct (English) suffix for the given number -- "st", "nd", "rd", or "th.

For example:

```clarity
(hello-for-the-nth-time "Alice" u1)
```
Evaluates to:
```clarity
"Hello, Alice, for the 1st time"
```

Another example:

```clarity
(hello-for-the-nth-time "Bob" u23)
```
Evaluates to:
```clarity
"Hello, Bob, for the 23rd time"
```

How might the developer test that `hello-for-the-nth-time` produces the correct
string for each value of `n`?

Using Clairvoyance, we can first _explore_ each halting state of this function
as follows:

```bash
$ clairvoyance explore /tmp/hello-world.clar hello-for-the-nth-time
Halting description for hello-for-the-nth-time:
;;     (halt
;;       (result (ok (concat u"Hello, " (name (string-utf8 128)) u" for the " (int-to-utf8 (n uint)) u"st time")))
;;       (predicate (is-eq (mod (n uint) u10) u1))
;;     )

Halting description for hello-for-the-nth-time:
;;     (halt
;;       (result (ok (concat u"Hello, " (name (string-utf8 128)) u" for the " (int-to-utf8 (n uint)) u"nd time")))
;;       (predicate (is-eq (mod (n uint) u10) u2))
;;     )

Halting description for hello-for-the-nth-time:
;;     (halt
;;       (result (ok (concat u"Hello, " (name (string-utf8 128)) u" for the " (int-to-utf8 (n uint)) u"rd time")))
;;       (predicate (is-eq (mod (n uint) u10) u3))
;;     )

Halting description for hello-for-the-nth-time:
;;     (halt
;;       (result (ok (concat u"Hello, " (name (string-utf8 128)) u" for the " (int-to-utf8 (n uint)) u"th time")))
;;       (predicate (and (not (is-eq (mod (n uint) u10) u1)) (not (is-eq (mod (n uint) u10) u2)) (not (is-eq (mod (n uint) u10) u3))))
;;     )
```

Each `halt` expression contains two sub-expressions: `result` and `predicate`.
The `result` expression contains the formula produced by evaluating
`hello-for-the-nth-time`, and the `predicate` expression contains a logical
formula which must evaluate to `true` in order for the `result` formula to be
produced.

Here, there are four possible halting states for `hello-for-the-nth-time`:

* The first state is reached when `(n % 10) == 1`.  In this case, the function
  computes a string using the `"st"` suffix.

* The second state is reached when `(n % 10) == 2`.  In this case, the function
  computes a string using the `"nd"` suffix.

* The third state is reached when `(n % 10) == 3`.  In this case, the function
  computes a string using the `"rd"` suffix.

* The fourth and final state is reached only when `(n % 10) != 1`, `(n % 10) !=
  2`, and `(n % 10) != 3`.  In this case, the function computes a string using
the `"th"` suffix.

The developer can annotate `hello-for-the-nth-time` with these explored halting
state descriptions to have Clairvoyance _check_ them automatically.  The
annotation is as follows:

```clarity
;; (@clairvoyance
;;     (halt
;;       (result (ok (concat u"Hello, " (name (string-utf8 128)) u" for the " (int-to-utf8 (n uint)) u"st time")))
;;       (predicate (is-eq (mod (n uint) u10) u1))
;;     )
;;     (halt
;;       (result (ok (concat u"Hello, " (name (string-utf8 128)) u" for the " (int-to-utf8 (n uint)) u"nd time")))
;;       (predicate (is-eq (mod (n uint) u10) u2))
;;     )
;;     (halt
;;       (result (ok (concat u"Hello, " (name (string-utf8 128)) u" for the " (int-to-utf8 (n uint)) u"rd time")))
;;       (predicate (is-eq (mod (n uint) u10) u3))
;;     )
;;     (halt
;;       (result (ok (concat u"Hello, " (name (string-utf8 128)) u" for the " (int-to-utf8 (n uint)) u"th time")))
;;       (predicate (and (not (is-eq (mod (n uint) u10) u1)) (not (is-eq (mod (n uint) u10) u2)) (not (is-eq (mod (n uint) u10) u3))))
;;     )
;; )
(define-public (hello-for-the-nth-time (name (string-utf8 128)) (n uint))
    (let (
        (suffix
            (if (is-eq (mod n u10) u1)
                u"st"
            (if (is-eq (mod n u10) u2)
                u"nd"
            (if (is-eq (mod n u10) u3)
                u"rd"
                u"th")))))

    (ok (concat u"Hello, " name u" for the " (int-to-utf8 n) suffix u" time"))))
```

To have Clairvoyance prove that the given halting states are both correct and
constitute a complete description of the function's behavior, the developer
would run:

```bash
$ ./clairvoyance check /tmp/hello-world.clar hello-for-the-nth-time
checkes passed
```

Now, let us see what happens if the `hello-for-the-nth-time` function body is
modified, without updating the halting descriptions:

```clarity
;; (@clairvoyance
;;     (halt
;;       (result (ok (concat u"Hello, " (name (string-utf8 128)) u" for the " (int-to-utf8 (n uint)) u"st time")))
;;       (predicate (is-eq (mod (n uint) u10) u1))
;;     )
;;     (halt
;;       (result (ok (concat u"Hello, " (name (string-utf8 128)) u" for the " (int-to-utf8 (n uint)) u"nd time")))
;;       (predicate (is-eq (mod (n uint) u10) u2))
;;     )
;;     (halt
;;       (result (ok (concat u"Hello, " (name (string-utf8 128)) u" for the " (int-to-utf8 (n uint)) u"rd time")))
;;       (predicate (is-eq (mod (n uint) u10) u3))
;;     )
;;     (halt
;;       (result (ok (concat u"Hello, " (name (string-utf8 128)) u" for the " (int-to-utf8 (n uint)) u"th time")))
;;       (predicate (and (not (is-eq (mod (n uint) u10) u1)) (not (is-eq (mod (n uint) u10) u2)) (not (is-eq (mod (n uint) u10) u3))))
;;     )
;; )
(define-public (hello-for-the-nth-time (name (string-utf8 128)) (n uint))
    (let (
        (suffix
            (if (is-eq (mod n u10) u1)
                u"st"
            (if (is-eq (mod n u10) u2)
                ;; oops, this is the wrong suffix!
                u"rd"
            (if (is-eq (mod n u10) u3)
                u"rd"
                u"th")))))

    (ok (concat u"Hello, " name u" for the " (int-to-utf8 n) suffix u" time"))))
```

What happens when we check it now?

```bash
$ ./clairvoyance check /tmp/hello-world.clar hello-for-the-nth-time
Failed to check contract:
Clairvoyance encountered one or more errors while checking halting states:
Unchecked halting state:
ID:               183
Path:             hello-for-the-nth-time.return
Panicked:         false
Early return:     false
Caller:           (toplevel)
tx-sender:        (tx-sender principal)
contract-caller:  (contract-caller principal)
current-contract: SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance
Formula:          (ok (concat u"Hello, " (name (string-utf8 128)) u" for the " (int-to-utf8 (n uint)) u"rd time"))
Predicate: 
   (or
      (is-eq (mod (n uint) u10) u2)
      (is-eq (mod (n uint) u10) u3)
   )
Input vars explored:
   (empty)
Output vars computed:
   (empty)
Input map entries explored:
   (empty)
Output map entries computed:
   (empty)
Deleted map entries computed:
   (empty)
Possibly-read data vars:
   (none)
Possibly-written data vars:
   (none)
Possibly-read maps:
   (none)
Possibly-written maps:
   (none)

Unchecked halting description:
;;     (halt
;;       (result (ok (concat u"Hello, " (name (string-utf8 128)) u" for the " (int-to-utf8 (n uint)) u"rd time")))
;;       (predicate (or (is-eq (mod (n uint) u10) u2) (is-eq (mod (n uint) u10) u3)))
;;     )

Unmatched halting condition:
   (is-eq (mod (n uint) u10) u2)
Unmatched halting condition:
   (is-eq (mod (n uint) u10) u3)
```

What happened here?  The bug, as annotated in the code listing, was that the
code was changed so that if `(n % 10) == 2`, it will erroneously use the `"rd"`
suffix instead of `"nd"`.  That is, it behaves the same way as when `(n % 10) ==
3`.

Clairvoyance reports this as an "unchecked halting state," because it discovered a
terminating program state that was not accounted for in the `(@clairvoyance ...)`
annotation.  Specifically, the function now has a unique halting state which can be
reached if `(n % 10) == 2 || (n % 10) == 3`, whereas before, `(n % 10) == 2` and
`(n % 10) == 3` had distinct halting states (i.e. the function had different
`result` formulae)

Because of this bug, two of the given halting states are no longer match the
computed halting states:  the state reached when `(n % 10) == 2`, and the state
reached when `(n % 2) == 3`.  These are no longer reachable since the computed
halting state reached when `(n % 10) == 1 || (n % 10) == 2` subsumes them.

This information informs the developer that the code's behavior has deviated
from the behavior specified, and the correct course of action is to make it so
that the halting states reached when `(n % 10) == 2` and `(n % 10) == 3` are
once again distinct.

## Side Effects

Many real-world Clarity programs read and write data variables, map entries, and
token state.  Clairvoyance allows developers to declare these mutations
symbolically in a function's given halting states.  For example, consider this
program, which implements a guestbook:

```clarity
;; (@clairvoyance
;;      ;; name of this contract
;;      (contract-id 'SP1VFT1JBHP1QT88XCCY9HSB87PE0SSVY40D1NN3H.hello-world)
;; )

(define-map guestbook
    ;; name
    (string-utf8 128)
    ;; count
    uint)

;; total number of times `hello-again` has been called
(define-data-var total-hello-calls uint u0)

(define-private (update-guestbook (name (string-utf8 128)))
    (let (
        (total-hellos (var-get total-hello-calls))
        (hello-count (default-to u0 (map-get? guestbook name)))
        (new-hello-count (+ u1 hello-count))
    )
    (map-set guestbook name new-hello-count)
    (var-set total-hello-calls (+ u1 hello-count))
    new-hello-count))

(define-public (hello-again (name (string-utf8 128)))
    (let (
        (n (update-guestbook name))
    )
    (ok {
        name: name,
        greeted: n
    })))
```

This program's public function, `hello-again`, takes a name as input, and stores
both how many times `hello-again` has been called with this particular name,
as well as the total number of times `hello-again` has been called.

Exploring the halting states of `hello-again`, we have:

```bash
$ clairvoyance explore /tmp/hello-world-stateful.clar hello-again
Halting description for hello-again:
;;     (halt
;;       (result (ok { greeted: (+ (unwrap-panic (map-entry SP1VFT1JBHP1QT88XCCY9HSB87PE0SSVY40D1NN3H.hello-world.guestbook (name (string-utf8 128)))) u1), name: (name (string-utf8 128)) }))
;;       (predicate (is-some (map-entry SP1VFT1JBHP1QT88XCCY9HSB87PE0SSVY40D1NN3H.hello-world.guestbook (name (string-utf8 128)))))
;;       (var-write
;;         SP1VFT1JBHP1QT88XCCY9HSB87PE0SSVY40D1NN3H.hello-world.total-hello-calls
;;         (+ (loaded-var SP1VFT1JBHP1QT88XCCY9HSB87PE0SSVY40D1NN3H.hello-world.total-hello-calls (total-hello-calls uint)) u1))
;;       (map-write
;;         SP1VFT1JBHP1QT88XCCY9HSB87PE0SSVY40D1NN3H.hello-world.guestbook
;;           (name (string-utf8 128))
;;           (+ (unwrap-panic (map-entry SP1VFT1JBHP1QT88XCCY9HSB87PE0SSVY40D1NN3H.hello-world.guestbook (name (string-utf8 128)))) u1))
;;     )

Halting description for hello-again:
;;     (halt
;;       (result (ok { greeted: u1, name: (name (string-utf8 128)) }))
;;       (predicate (is-none (map-entry SP1VFT1JBHP1QT88XCCY9HSB87PE0SSVY40D1NN3H.hello-world.guestbook (name (string-utf8 128)))))
;;       (var-write
;;         SP1VFT1JBHP1QT88XCCY9HSB87PE0SSVY40D1NN3H.hello-world.total-hello-calls
;;         (+ (loaded-var SP1VFT1JBHP1QT88XCCY9HSB87PE0SSVY40D1NN3H.hello-world.total-hello-calls (total-hello-calls uint)) u1))
;;       (map-write
;;         SP1VFT1JBHP1QT88XCCY9HSB87PE0SSVY40D1NN3H.hello-world.guestbook
;;           (name (string-utf8 128))
;;           u1)
;;     )
```

There are two halting states for `hello-again`, and the state reached depends on
whether or not there exists a map entry in `guestbook` for the given `name`.

The first halting state, as asserted by the `predicate` expression, describes
the case where there is already a map entry present.  In this state, the value
written to `guestbook` under the key `name` is one plus the existing value in
the `guestbook` map under `name`.  The existing value is reported as the
`(unwrap-panic (map-entry ...))` expression.

The second halting state, as asserted in its `predicate`, describes the case
where there is not yet a map entry present.  In this state, the value `u1` is
written to `guestbook` under the key `name`.

In both halting states, the variable `total-hello-calls` is incremented by one.
Also, in both halting states, the formula of the `greeted` key in the resulting
tuple is equal (syntactically) to the formula written to the `guestbook` map.

## Bounding State Exploration

An evergreen difficulty with symbolic execution is that of path explosion.  The
number of execution paths grows at worse exponentially with the number of code
branches to explore.  While all Clarity programs are decidable and thus execute
finite code branches, there can nevertheless be an intractable amount of them
to explore.

To bound the search space, Clairvoyance employs the following heuristics by
default:

* **Skip read-only functions**.  If a function is read-only, then it is not
  evaluated by default.  Instead, Clairvoyance treats the read-only function
call as an opaque symbol.  Other halting state parameters may thus be defined in
terms of the called function, instead of the formulae the function could
evaluate to.

* **Skip causally-independent functions**.  If a function performs writes that
  are causally independent of the current path being explored, then Clairvoyance
does not explore the function.  Instead, it queries the callgraph and records
the variables and maps that _might_ be written by the call to this function.  A
function call is treated as causally-independent if it only reads data variable and map values
that have not been written in the current path.  A consequence of this heuristic
is that the computed halting state may not reflect the true formulae of data
variable and map state, in the event that a causally-independent function wrote
data that would later be read in the current path.  Instead, the formulae for
this state would be "stub" formulae, since Clairvoyance would treat their
symbolic values as unmodified inputs.

* **Combine halting states which differ only in their reachability condition predicates.**  Multiple
  code paths may reach the same halting state insofar as their resulting
formulae and written state are concerned.  The only difference between these halting
states are their respective logical predicates that determine the conditions
under how they are reached.  In such cases, Clairvoyance combines these halting
states into a single halting state, with a new predicate defined as the logical
OR-ing of each constituent halting states.

These heuristics can be disabled on a per-function or even a pure
Clarity expression basis via the `explore-all` keyword, among others.

## Keyword Reference

Clairvoyance is designed to be used iteratively and incrementally with
developing a Clarity program.  As the developer completes a function, they may
use `clairvoyance explore` to compute halting states for it, and annotate the
function with them via a `(@clairvoyance ..)` directive so that the behaviors
the halting states encode can be later checked via `clairvoyance check`.

The keywords supported so far are:

### `define-symbol`

**Signature**:  `(define-symbol name:symbol formula:symop)`

**Usage**: This keyword binds a formula to a name, so the name can be used in
place of the formula.

**Example**:

```clarity
;; (@clairvoyance
;;    (define-symbol x-is-even (is-eq (mod (x uint) u2) u0))
;;
;;    (halt
;;       (result (ok true))
;;       (predicate (x-is-even bool))))
```

**Notes**:
Clairvoyance naively substitutes the name with the corresponding formula.  It
does not typecheck the resulting expression.  However, because the formula name
is itself a symbol (i.e. not an atom), it must be written as a two-atom list,
where the first atom is the formula's name and the second atom is the formula's
type (for example, `(x-is-even bool)`).

`define-symbol` can be used to define formulae in any subsequent keyword
expression, including subsequent `define-symbol` expressions.

Name-to-formula substitutions are applied in the order in which the
`define-symbol` expressions are written.

The lexical scope of `define-symbol` is limited to the contained `(@clairvoyance
...)` expression.

### `halt`

**Signature**:  `(halt halt-exp0 halt-exp1 ...)`

**Usage**:  This keyword declares a testable halting state.  Clairvoyance will
examine the declared halting states for a given symbolic expression, and check
them against the computed halting states for the expression.  The `halt`
expression may contain the following sub-expressions:

* `(result formula:symop)`:  This is a formula computed by the Clarity code executed thus far.

* `(predicate formula:symop)`:  This is the _complete_ boolean predicate that must be true for
  the halting state to be reached.  It is not required if `condition` is given.

* `(condition formula:symop)`:  This is a _sufficient_ boolean predicate that must be _implied_
  by the halting state's complete predicate.  It is not required if `predicate`
is given.

* `(var-write name:fullname value:symop)`:  This describes the formula for a data var written.
  The `name` must be a fully-qualified name, in the form of
`<contract-address>.<contract-name>.<variable-name>`.

* `(map-write name:fullname key:symop value:symop)`:  This describes the formula
  for a data map entry written.

* `(map-delete name:fullname key:symop)`:  This describes the formula for a data
  map key that was deleted.

* `(panicking)`:  If present, then the halting state must have been reached via
  a runtime panic.

* `(early-return)`:  If present, then the halting state must have been reached
  via an early-return.

* `(reachable-var-write name:fullname)`: This describes a _possibly-reached_
  variable write that was not fully explored.

* `(reachable-map-write name:fullname)`:  This describes a _possibly-reached_
  data map write or deletion that was not fully explored.

**Notes**:
It is rare that one would write a `(halt ..)` expression by hand.  Please
consider using `clairvoyance check ...` to produce them for your code.

### `concretize-trait`

**Signature**:  `(concretize-trait name:fullname contract_id:principal)`

**Usage**:  This keyword re-binds a variable bound to a trait reference with a
concretization of that trait.  Clairvoyance will explore the concretized trait
code when processing a `contract-call?` to one of its functions.

**Example**:

```clarity
;; (@clairvoyance
;;      (concretize-trait
;;          calc
;;          'SP8H248H248H248H248H248H248H248H24ARTQ82.library)
;; )
;;
;; Here, 'SP8H248H248H248H248H248H248H248H24ARTQ82.library implements the
;; calc-trait.
(define-public (compute (calc <calc-trait>) (op uint) (a uint) (b uint))
   ...)
```

**Notes**:
The concretized trait identified by `contract_id` must first have been loaded as
a dependency (see `dependency`).

This keyword is only applicable for function-level Clairvoyance annotations.

### `skip-function-call`

**Signature**:  `(skip-function-call)` or `(skip-function-call name:fullname)`

**Usage**:  This keyword tells Clairvoyance to treat the given function like a
symbol.  The function will not be explored.  The first usage, with no argument, must annotate the callsite.
The second usage, with an argument, must annotate a function definition.

**Example**:

Usage 1:

```clarity
;; (@clairvoyance (skip-function-call))
(do-the-thing x y z)
```

Usage 2:

```clarity
;; (@clairvoyance
;;    (skip-function-call 'SP8H248H248H248H248H248H248H248H24ARTQ82.foo.do-the-thing))
;;
(define-public (do-stuff (x uint) (y uint) (z uint))
   (do-the-thing x y z))
```

### `skip-contract-call`

**Signature**:  `(skip-contract-call)` or `(skip-contract-call name:fullname)`

**Usage**:  This keyword tells Clairvoyance to treat a given contract call like
a symbol.  The function will not be explored.  The first usage, with no argument, must annotate the callsite.
The second usage, with an argument, must annotate a function definition.

**Example**:

Usage 1:

```clarity
;; (@clairvoyance (skip-contract-call))
(contract-call? .foo.do-the-thing x y z)
```

Usage 2:

```clarity
;; (@clairvoyance
;;    (skip-contract-call 'SP8H248H248H248H248H248H248H248H24ARTQ82.foo.do-the-thing))
;;
(define-public (do-stuff (x uint) (y uint) (z uint))
   (contract-call? .foo.do-the-thing x y z))
```

### `stop`

**Signature**: `(stop)`

**Usage**:  This stops Clairvoyance and causes it to exit.  It's useful for
debugging path explosions.

**Example**:

```clarity
;; (@clairvoyance (stop))
(do-very-expensive-thing)
```

### `drop-early-returns`

**Signature**:  `(drop-early-returns)`

**Usage**:  This causes all currently-explored paths that have encountered an
early-return to be dropped from future consideration.  It can be used to both
annotate functions as well as their callsites in a bid to prevent Clairvoyance
from exploring execution paths that will ultimately abort.

**Example**

As a function annotation:

```clarity
;; (@clairvoyance (drop-early-returns))
(define-public (do-the-thing (x uint) (y uint) (z uint))
   (if (is-eq x u0)
      ;; no halting state will be reported for this outcome
      (err u0)
   (if (is-eq y u0)
      ;; no halting state will be reported for this outcome
      (err u1)
   (if (is-eq z u0)
      ;; no halting state will be reported for this outcome
      (err u2)
   (ok (+ x y z))))))
```

As a callsite annotation:

```clarity
(define-public (do-the-things (x uint) (y uint) (z uint))
   (begin
      ;; (@clairvoyance (drop-early-returns))
      (try! (do-the-thing x y z))
      (ok true)))
```

### `explore-all`

**Signature**: `(explore-all)`

**Usage**:  This disables all path-pruning heuristics in Clairvoyance.  It
applies to all execution paths that logically descend from the annotated Clarity
expression.

**Example**:

```clarity
;; (@clairvoyance (explore-all))
;;
;; Without this annotation, `do-the-thing` will be treated as a read-only
;; function and will not otherwise be evaluated by Clairvoyance.
(define-public (do-the-thing (x uint) (y uint) (z uint))
   (if (is-eq x u0)
      ;; this is now a halting state for this function
      (err u0)
   (if (is-eq y u0)
      ;; this is now a halting state for this function
      (err u1)
   (if (is-eq z u0)
      ;; this is now a halting state for this function
      (err u2)
   ;; this is now a halting state for this function
   (ok (+ x y z))))))
```

### `dependency`

**Signature**: `(dependency contract_id:principal path:string)` or `(dependency
contract_id:principal path:string sponsor:principal)`

**Usage**:  This loads a Clarity program at the given `path` and instantiates it
as a contract under the given address `contract_id`.  In the second form, a
transaction sponsor address (i.e. `tx-sponsor?`) may be specified as the third
argument.  This keyword is used to instantiate contracts that the
currently-evaluated contract will call into, as well as instantiate trait
concretizations.

This is a top-level keyword.  It can occur only in comment blocks outside of
functions.

**Example**:

```clarity
;; (@clairvoyance
;;    (dependency 
;;       'SP8H248H248H248H248H248H248H248H24ARTQ82.library
;;       "/tmp/library.clar"))
```

**Notes**:  It is typical to declare all dependencies at the start of a Clarity
source file, much like how external module imports in most other programming language
are found at the head of the source file.  In the case of `concretize-trait`,
the referenced contract which implements the named trait must have already been
loaded by a prior `dependency` directive.

### `contract-id`

**Signature**: `(contract-id address:principal)`

**Usage**:  This sets the address of the evaluated contract.  It must be a
contract address.

**Example**:

```clarity
;; (@clairvoyance
;;    (contract-id 'SP8H248H248H248H248H248H248H248H24ARTQ82.main))
```

**Notes**:  This is a top-level directive.  It is typical to use it at the very
start of a Clarity source file.  It will be ignored if it is used in an
annotation a non-top-level Clarity expression.  It is an error to use this
directive more than once.

### `contract-sponsor`

**Signature**: `(contract-sponsor address:principal)`

**Usage**:  This sets the address of the evaluated contract's transaction
sponsor (i.e. the value of `tx-sponsor?`).  It must be a standard address.

**Example**:

```clarity
;; (@clairvoyance
;;    (contract-sponsor 'SP8H248H248H248H248H248H248H248H24ARTQ82))
```

**Notes**:  This is optional.  Most contract deployments are not sponsored.

### `default-trait-impl`

**Signature**:  `(default-trait-impl trait-id:field contract-id:principal)`

**Usage**:  This sets the default trait concretization for each trait
reference implementing the trait `trait-id`.  This is used to set program-wide
defaults once, instead of for each call-site with `concretize-trait`.

**Example**:

```clarity
;; (@clairvoyance
;;    (default-trait-impl
;;       'SP8H248H248H248H248H248H248H248H24ARTQ82.library.library-trait
;;       'SP8H248H248H248H248H248H248H248H24ARTQ82.my-library))
```

**Notes**:  This is a top-level directive, and is typically used at the start of
a Clarity source file (i.e. right after all requisite `dependency` directives
are listed).

### `println`

**Signature**:  `(println msg:symop)`

**Usage**:  This prints the given `msg` (which is a symbolic operation) to
standard error.  The `msg` argument can be a literal value, or a symbolic
formula.  It's used mainly for printf-debugging a Clairvoyance run in order to
deduce what kind of path explosions are happening.  Symbols in `msg` can
reference bound formulae in the ongoing continuation.

**Example**:

```clarity
(define-public (do-the-thing (x uint) (y uint) (z uint))
    (let (
        (w (if (is-eq x u0)
            (+ y z)
           (if (is-eq y u0)
            (* x z)
            (- x y))))
    )
    ;; (@clairvoyance
    ;;      (println "the value of w is:")
    ;;      ;; NOTE: we're printing the _symbol_ w, so it needs a type
    ;;      (println (w uint)))
    (ok w)))
```

The above, when evaluated, will print the following:

```bash
$ clairvoyance check /tmp/println-example.clar
"the value of w is:"
(+ (y uint) (z uint))
"the value of w is:"
(* (x uint) (z uint))
"the value of w is:"
(- (x uint) (y uint))
checks passed
```

**Notes**:  A `println` will be evaluated for each possible execution path, so
it's not uncommon to see the same `println` evaluated many times (as shown in
the example).

### `print-continuation`

**Signature**:  `(print-continuation)`

**Usage**:  This prints out the currently-evaluated symbolic continuation.  This
represents the state of symbolic execution _prior to_ the evaluation of the
annotated Clarity code.  This is mainly used for debugging Clairvoyance; the
output is quite verbose.  The information is printed to standard error.

**Example**:

```clarity
(define-public (do-the-thing (x uint) (y uint) (z uint))
    (let (
        (w (+ x y z))
    )
    ;; (@clairvoyance (print-continuation))
    (ok (if (> w (+ x y)) w (+ x z)))))
```

The above, when evaluated, will print the following:

```
$ clairvoyance check /tmp/print-continuation-example.clar
ID:               19
Path:             do-the-thing.body/let.expr[0]
Panicked:         false
Early return:     false
Caller:           do-the-thing.binding
tx-sender:        (tx-sender principal)
contract-caller:  (contract-caller principal)
current-contract: SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance
Formula:          (+ (x uint) (y uint) (z uint))
Predicate: 
   true
Input vars explored:
   (empty)
Output vars computed:
   (empty)
Input map entries explored:
   (empty)
Output map entries computed:
   (empty)
Deleted map entries computed:
   (empty)
Possibly-read data vars:
   (none)
Possibly-written data vars:
   (none)
Possibly-read maps:
   (none)
Possibly-written maps:
   (none)

Symbolic stack trace:
11: 19 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0])  
10: 18 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+/z) (w (+ (x uint) (y uint) (z uint))) 
9: 13 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+)  
8: 12 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+/y)  
7: 9 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+)  
6: 8 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+/x)  
5: 5 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+)  
4: 4 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w)  
3: 3 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:2 (do-the-thing.body)  
2: 2 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.:2 (do-the-thing.binding) (x (x uint)) (y (y uint)) (z (z uint)) 
1: 1 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.:0 ()  

Halt description:
;;     (halt
;;       (result (+ (x uint) (y uint) (z uint)))
;;       (predicate true)
;;     )

checks passed
```

**Notes**:  This prints the continuation of the currently-explored code path,
but because there may be many code paths that pass through this Clarity
expression, you may see many different continuation states printed.  The
continuation data is printed to standard error.

### `print-produced-continuations`

**Signature**:  `(print-produced-continuations)`

**Usage**:  This prints all continuations _produced_ by evaluating the annotated
Clarity statement.

**Example**:

```clarity
(define-public (do-the-thing (x uint) (y uint) (z uint))
    (let (
        (w (+ x y z))
    )
    ;; (@clairvoyance (print-produced-continuations))
    (ok (if (> w (+ x y)) w (+ x z)))))
```

When evaluated with Clairvoyance, the following two continuations will be
printed:
 
```
$ clairvoyance check /tmp/print-produced-continuations-example.clar
=========== Begin produced continuations for ( ok ( if ( > w ( + x y ) ) w ( + x z ) ) )
ID:               60
Path:             do-the-thing.body/let.expr[0]/ok.true/w
Panicked:         false
Early return:     false
Caller:           do-the-thing.binding
tx-sender:        (tx-sender principal)
contract-caller:  (contract-caller principal)
current-contract: SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance
Formula:          (ok (+ (x uint) (y uint) (z uint)))
Predicate:
   (> (+ (x uint) (y uint) (z uint)) (+ (x uint) (y uint)))
Input vars explored:
   (empty)
Output vars computed:
   (empty)
Input map entries explored:
   (empty)
Output map entries computed:
   (empty)
Deleted map entries computed:
   (empty)
Possibly-read data vars:
   (none)
Possibly-written data vars:
   (none)
Possibly-read maps:
   (none)
Possibly-written maps:
   (none)

Symbolic stack trace:
22: 60 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok.true/w)
21: 40 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok.true)
20: 39 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if/>/+/y)
19: 31 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if/>/+)
18: 30 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if/>/+/x)
17: 27 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if/>/+)
16: 26 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if/>)
15: 25 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if/>/w)
14: 22 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if/>)
13: 21 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if)
12: 20 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok)
11: 19 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0])
10: 18 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+/z) (w (+ (x uint) (y uint) (z uint)))
9: 13 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+)
8: 12 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+/y)
7: 9 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+)
6: 8 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+/x)
5: 5 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+)
4: 4 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w)
3: 3 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:2 (do-the-thing.body)
2: 2 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.:2 (do-the-thing.binding) (z (z uint)) (x (x uint)) (y (y uint))
1: 1 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.:0 ()

Halt description:
;;     (halt
;;       (result (ok (+ (x uint) (y uint) (z uint))))
;;       (predicate (> (+ (x uint) (y uint) (z uint)) (+ (x uint) (y uint))))
;;     )

--------------------------------------------------------------
ID:               61
Path:             do-the-thing.body/let.expr[0]/ok.false/+/z
Panicked:         false
Early return:     false
Caller:           do-the-thing.binding
tx-sender:        (tx-sender principal)
contract-caller:  (contract-caller principal)
current-contract: SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance
Formula:          (ok (+ (x uint) (z uint)))
Predicate:
   (<= (+ (x uint) (y uint) (z uint)) (+ (x uint) (y uint)))
Input vars explored:
   (empty)
Output vars computed:
   (empty)
Input map entries explored:
   (empty)
Output map entries computed:
   (empty)
Deleted map entries computed:
   (empty)
Possibly-read data vars:
   (none)
Possibly-written data vars:
   (none)
Possibly-read maps:
   (none)
Possibly-written maps:
   (none)

Symbolic stack trace:
25: 61 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok.false/+/z)
24: 48 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok.false/+)
23: 47 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok.false/+/x)
22: 44 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok.false/+)
21: 43 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok.false)
20: 39 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if/>/+/y)
19: 31 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if/>/+)
18: 30 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if/>/+/x)
17: 27 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if/>/+)
16: 26 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if/>)
15: 25 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if/>/w)
14: 22 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if/>)
13: 21 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok/if)
12: 20 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0]/ok)
11: 19 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:6 (do-the-thing.body/let.expr[0])
10: 18 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+/z) (w (+ (x uint) (y uint) (z uint)))
9: 13 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+)
8: 12 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+/y)
7: 9 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+)
6: 8 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+/x)
5: 5 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w/+)
4: 4 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:3 (do-the-thing.body/let.bind[0].w)
3: 3 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.do-the-thing:2 (do-the-thing.body)
2: 2 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.:2 (do-the-thing.binding) (z (z uint)) (x (x uint)) (y (y uint))
1: 1 SP8H248H248H248H248H248H248H248H24ARTQ82.clairvoyance.:0 ()

Halt description:
;;     (halt
;;       (result (ok (+ (x uint) (z uint))))
;;       (predicate (<= (+ (x uint) (y uint) (z uint)) (+ (x uint) (y uint))))
;;     )

=========== End of produced continuations for ( ok ( if ( > w ( + x y ) ) w ( + x z ) ) )
checks passed
```

### `pause`

**Signature**:  `(pause)`

**Usage**:  This pauses Clairvoyance execution, and waits for the user to press
the Return key.  It's used for stepping through Clairvoyance execution, in
conjunction with other debugging directives like `println`,
`print-continuation`, and `print-produced-continuations`.

**Example**:

```clarity
(define-public (do-the-thing (x uint) (y uint) (z uint))
    (let (
        (w (+ x y z))
    )
    ;; (@clairvoyance (pause))
    (ok (if (> w (+ x y)) w (+ x z)))))
```

When evaluated with Clairvoyance, the following output will be produced:

```
$ clairvoyance check /tmp/pause-example.clar
Symbolic execution paused at line 6
Current symbolic expression: ( ok ( if ( > w ( + x y ) ) w ( + x z ) ) )

Press Return to continue

checks passed
```

