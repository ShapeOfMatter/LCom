---
title: "Expression and Analysis of Synchronous Communication Plans"
subtitle: "Mid-term project report for cs395"
author: "Mako Bates"
date: "2021-11-14"

header-includes: |
  <style>
    body {
      
    }
    li:not(:last-child) {
      margin-bottom: .3em;
    }
    div.sourceCode {
      background-color: #f0f0f0;
      padding: .3em;
      margin: 0 2em;
    }
    code {
      background-color: #f0f0f0;
    }
  </style>
---

## Project Goals and Status
For this project I'm focusing on implementing a synchronous-communication DSL,
and building analysis tools against it.

The project is progressing much slower than I would like.
As proposed, there are four distinct goals for the semester:

- _A usable library for expressing a synchronous multi-party program in single-threaded style._  
  This is ~~plausibly complete~~ almost complete, but substantial ease-of-use refinements would be nice,
  and changes should be expected as part of the remaining work.
- _A corresponding handler/interpreter for simulating such a program
  in a single process and logging all the communication that happens._  
  The simplest possible handler is working;
  it differs from what's described here in that it does not log communication events, but that should be easy.
- _A corresponding system for querying the logs produced._  
  This will just be a couple of thin helper-functions.
  In the simplest implementation of logging (a list of messages),
  very little assistance navigating the logs will be possible.
  A more structured system of logging will be desirable,
  so that messages logged can be easily traced back to locations in the program code.
  The more structure we can build into the logs,
  the more structure we can encode in the log-querying tools
- _Some kind of analysis tool that can answer
  even limited questions about the logs that _could_ be produced,
  without access to real program inputs._  
  Given the pace of progress, this is not going to include any kind of symbolic execution.
  The existing packages [QuickCheck](https://hackage.haskell.org/package/QuickCheck),
  [testing-feat](https://hackage.haskell.org/package/testing-feat),
  and [lazysmallcheck](https://hackage.haskell.org/package/lazysmallcheck)
  are each promising leads for off-the-shelf enumeration of hypothetical inputs.
  Understanding their pros & cons and finding a solution that's practical for semi-realistic
  programs is a large remaining task. 

## Comparison to Existing Work
In the protocols I'm studying, a party receiving a message will always be _expecting_ 
the message and will know what the received value _represents_.
This means that (give-or-take laziness)
every communication event is a synchronization-point in the program.

Most work on communication protocols has focused on less constrained spaces of computation.
Asynchronous communication is particularly common in modern software development;
it allows high efficiency in many situations
but it's difficult to prove anything about the behavior of an unstructured asynchronous program.

Process calculi represent a variety of ways of representing concurrent computation.
**It is unlikley that the DSL I'm implementing is novel within this space.**
Finding a name and formalization of the kind of process I'm interested in would be quite valuable, 
but I haven't succeeded yet.

The π-calculus and the related language feature "Session Types" have received substantial attention lately;
these are good for reasoning about networks of communication who's structure may change during execution.
This is a useful contrast for the protocols I'm interested in,
in which the communication network is assumed to be fully connected and unchanging.

An earlier project of mine handled a highly symmetric situation,
in which every "send" event passed a value across every edge of the connected di-graph
and the computation performed by the parties between communication rounds were identical except for the specific values.
Breaking this symmetry turns out to cross a major threshold in the expressivity of Haskell's type system.

## DSL Goals and Progress

### Strategy
I'm building the DSL as an API within Haskell.
Programs should be _written_ as a single thread, and may be _executed_ as a single local thread
or concurrently by parties communicating over some unspecified network;
the semantics of the program must be the same either way. 
The motivation for using Haskell was to have a strong type-system capable of early detection of
programs that cannot be executed concurrently. 
**It is not clear that Haskell was a good choice for this.**

Programs are expressed as values of type `Sem '[Local i o, Communicate ps s] a`,
where `Sem` is the [polysemy](https://hackage.haskell.org/package/polysemy) constructor.
(`Sem rs` is the free monad on the effect constructors in `rs`.)
`Local` and `Communicate` are effect signatures described below;
they enable the creation and manipulation of `Located` values.
The wrapper/functor type `Located ps x` represents any value of type `x`
which is known among the parties `ps`.
The `Communication` effect is polymorphic over `s`,
the type of the values that can be communicated (_e.g_ `String` or `Int`).

### Control Flow
Consider a program interpreted in the distributed semantics;
a given party will execute some trace through the program.
To ensure the synchronization property (that all received messages are anticipated, and visa-versa),
it's necessary that at every point in the party's trace,
every other party to whom they _could_ send a message be at the same point in the program. 
(That a recipient may wait for a sender to catch up is ok;
whether senders need to wait for recipients isn't relevant.)
Normal control-flow operations like `if` statements threaten this. 

Various strategies for controlled control-flow are possible;
the one I'm implementing is that a `Located parties x` can be unwrapped into an `x`
only when the monadic context allows communication precisely to the parties `parties`.
Because the `Located` data-type constructor is not exposed as part of the API,
the only way to branch on a `Located` value  is using the `locally` effect constructor:
```haskell
locally :: Member (Communicate parties s) r =>
           Located parties a -> Sem r a
```
This would be very limiting if we were stuck with a single choice for `parties`.
To allow branching which affects only some parties,
the API exposes a "lifting" function `runClique` (name subject to change).
```haskell
runClique :: ( Subset clq parties,
               Member (Communicate clq s) r1,
               Member (Communicate parties s) r2
             ) =>
             Sem r1 a -> Sem r2 (Located clq a)
```
It is critical that `clq` be a subset of `parties`,
otherwise one could be referenced within a clique computation without knowing that one was supposed to be participating.
The problems introduced by `Subset` requirements are their own section below.

In some cases it may be more convenient to move computation into the space of `Located` values;
`Located ps` is an applicative functor.
Because the `Functor` and `Applicative` instance are declared for the partially-applied type `Located ps`,
they don't threaten synchronisity.
(A user is free to _construct_ a value of type `Located clq1 (Sem (Communicate clq2 s) a)` in this way,
but they won't be able to _execute_ it.)

### Subsets
Haskell's type system is poorly suited for handling type level sets and their properties.
I been seeking help with this problem
(mostly on [StackOverflow](https://stackoverflow.com/questions/69811647/transitive-subset-class-for-type-level-sets),
also [Reddit](https://www.reddit.com/r/haskell/comments/qlvs5i/transitive_subset_class_for_typelevelsets/))
and have basically concluded that no _good_ solution exists.

`runClique` implies the existence of parties that _are not_ part of the immediate computational environment.
Therefore, the type signature for `send` should enforce that all the
senders and recipients _are_ part of the immediate `parties`:
```haskell
send :: ( Subset recipients parties,
          Subset senders parties,
          Member (Communicate parties s) r
        ) =>
        Located senders s -> Sem r (Located recipients s)
```
Implementation of `runClique` relies on its own constraint `Subset clq parties`;
`clq`-level `send`s can be lifted to `parties`-level `send`s because "subset" is a transitive property. 
Unfortunately, the `Subset` class exposed by [type-level-sets](https://hackage.haskell.org/package/type-level-sets-0.8.9.0)
is _not_ transitive, and no way seems to exist in Haskell to _make_ it transitive. 

The workaround I've used is to represent the subset constraint
to the inner effect constructors using argument values of type `SubsetProof`. 
These values are vacuous in the sense that they have no contents (or if they do it isn't used);
it suffices for the type-checker to ensure their existence. 
Logical axioms, relations, and properties of relations such as I need for this are provided by 
[gdp](https://hackage.haskell.org/package/gdp-0.0.3.0).

### Inputs and Outputs
Protocols such as I'm describing would have no motivation
if all their inputs were available to all parties in the first place. 
Furthermore, since the API affords no direct way of unpacking a `Located` value,
relying on the terminal `return` of a program would not allow us to represent different parties getting different outputs.
A complementary effect signature `Local i o` represents that parties are expected to bring in inputs of type `i`,
and will get outputs of type `o`. 

This is not an elegant solution; it requires `i` and `o` to be uniform across parties. 
It also suggests that inputs and outputs would be symmetric when they are not;
absent a way to ensure each party only gets one output, each party outputs a list;
on the other hand all calls to `localInput @p` will yield a constant value.
(Allowing input lists would introduce a new class of error because the lists could be exhausted).

### Sendable Structures
The effect constructor behind `send` is actually `SendMaybe`.
This allows somewhat more complicated data structures to be sent.
A call to `send (x :: t)` will be evaluated to some number `n` of sequential `SendMaybe` effects,
each of which communicates a single `Maybe s`;
the exact `n` is determined by an `instance Sendable s t (n :: Nat)` that must exist.  
For example:
```haskell
instance ( Sendable s t1 n1,
           Sendable s t2 n2,
         ) =>
         Sendable s (t1, t2) (Plus n1 n2) where
  serialize (t1, t2) = (Vec.++) (serialize t1) (serialize t2)
  deserialize vv = let (v1, v2) = split @n1 @n2 vv
                   in (deserialize v1, deserialize v2)
```
This situation isn't great; `SendMaybe` does not afford as much flexibility as I'd hoped,
and I thought I was clever including an `instance Sendable s () Zero`,
which causes instance overlaps that have to be resolved by (more) type applications.
The good news is that this aspect of the system is mostly orthogonal to all the other problems;
I don't need to go back to fix it, and if I _do_ fix it then that shouldn't involve revisiting other design decisions.

### Handlers
Considerable work on handers for the `Communicate` effect has turned out to not be usable. 

The working handler turns all `send` and `locally` effects into identity functions.
The extra piece that's needed to generate the desired logs is just a temporary `Output` effect introduced into the stack;
this kind of effect-insertion is exactly what Polysemy is good at. 

A handler to cull a program down to a single party's perspective of the concurrent process remains elusive.
The fundamental problem is that Haskell has type erasure;
when a module (_e.g._ this API) is compiled the compiler needs to know exactly _how_ everything will happen at runtime.

- My first attempt involved a type parameter `p` which could be tested for membership in the `senders`, `recipients`, and `clq` lists.
  This didn't work because the `Member` class provided by Type-Level-Sets doesn't work as a _predicate_,
  and of course no `instance Member p recipients` exists for a parametric `p` (nor would we want it to). 
- My second attempt involved peeling parties out of the top-level `parties` environment.
  A full handler would be the composition of one handler for each party,
  only one of which would actually insert the _specific_ party's `Input` and `Output` effects for over-the-wire communication;
  a terminal handler would erase the residual `Communicate` effect. 
  This is still a viable strategy, but it hasn't worked yet because I haven't figured out how to have the one pass that 
  actually _does stuff_ identify which effects to handle or ignore.
- The situation can be somewhat simplified by including an initial pass of a handler to replace all `Communicate`
  effects with a pair of `Transmit` and `Recieve` effects.
  This will let subsequent passes consider the question of whether the specific party is in the `senders` set
  separately from whether they're in the `recipients` set.
  But it doesn't solve anything in itself.

The situation for the `Local i o` effects is a little simpler,
and I'm hopeful that a complete solution here will translate back into the `Communicate` case.

Simply making `Local` handler parametric on `p` doesn't work for the same reasons as in `Communicate`: 
type equality (`~`) isn't a predicate, it's a type-class,
and the convoluted strategies for type-level predicates just get one a _type_ of _kind_ `Bool`,
which isn't what's needed.
For the moment I've side-stepped the problem by having my `Local i o` handler take an argument of the bizarre type `forall p. Bool`.
This lets me simply pass in `True` to approximate the single-thread semantics.
I think I can get substantially closer to a real solution by updating that type to `forall p, IsMe p => Bool`.
The class `IsMe` can live in the library; the contextual requirement will propagate through the API,
and actual instances for all parties can be declared in user-code. 
This will be _very_ unwieldy, but I think it will work and I'm running low on ideas.

## Github
Most of the example code here has had minor simplifications to make it easier to read. 
The current code-base is [online](https://github.com/ShapeOfMatter/LCom).
