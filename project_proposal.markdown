---
title: "Queryable Synchronous Communication Plans"
subtitle: "Project proposal for cs395"
author: "Mako Bates"
date: "2021-10-15"
---

I've been working with formal DSLs for expressing synchronous multi-party computations, and proving properties of those programs.
For this project I'd like to focus on _implementing_ a synchronous-communication DSL, and building an open-ended analysis tool against it.

> **_Q:_** How do we answer questions about the communication log-data that _might_ happen during a multi-party computation,
> without actually running the computation? 
> 
> **_H:_** An appropriately crafted DSL would allow us to treat the hypothetical messages a protocol _might_ send as a data-structure,
> against which we could build a corresponding query system.

### Idea 

I'm proposing an effect-system based DSL for expressing synchronous communication. 
A wrapper type `Located ps a` would express the idea of an `a` known to parties in `ps`. 
`Located` values are not computed on directly in the host language;
DSL operators allow them to combine _and be communicated to new parties_ in a synchronous multi-party execution plan. 
Whether this enables any optimization to happen is not the point for this fall.
(**But benchmarking the communicaiton DSL itself is a vaible alternate project!**)
Instead the idea is that, in addition to the ability to simulate the entire process locally as a single thread,
or actually run the protocol over a network (optional for this fall), 
the system can also build a queryable view of all prospective communication without actually running the protocol. 

### Example

Parts of the following syntax are certainly possible;
I've modeled them on existing Haskell effect systems and an earlier comparable system I build for synchronous _symmetric_ communication.
That said, a lot of this remains speculative pseudo-code.

```haskell
Party = '[Alice, Bob, Charles]
getBobSecret :: SomeMonad Party String String String  -- Communicate among Party, with String secrets, String message-subjects, and return String.
getBobSecret = do  -- Everyone gets and returns Bob's Secret.
  alice <- readStdIn @Alice     :: Located '[Alice] Secret
  bob <- readStdIn @Bob         :: Located '[Bob] Secret
  alice' <- send @Bob {subject: "Under the table!",  -- This doesn't belong!
                       message: alice
                       } :: Located '[Alice, Bob] Secret
  bob' <- send @Party {subject: "Use this secret.",
                       message: bob
                       } :: Located Party Secret
  return bob'  -- In practice another op would be needed to unwrap the `Located Party Secret` into a `Secret`.

-- We can just run this locally
result1 = interpret (locally ("Alice's Secret", "Bob's Secret", "Charles's Secret")) getBobSecret
assert (=) result1 "Bob's Secret"

-- If we have peers, we can run this with them over the network
result2 = run (
  interpret (iAm Alice "My Secret") getBobSecret
) someNetworkConnection
print(result2)  -- What will it be? I don't know because I'm Alice, not Bob. 

-- Or we can skip all that and ask about the communication that happens. 
communication = analyze getBobSecret
-- This passes:
assert (=) 1 (query ("SELCET Count(*) from `communication` where to = `Charles`"))
-- This is where we'd expect to uncover the mistake in the above protocol:
assert (=) 0 (query ("SELECT Count(*) from `communication` where message = `readStdIn @Alice`"))
```
### Questions: 

> **_Q:_** Can we handle the space of possible traces of a computation as a queryable data-structure?
> 
> **_H:_** This question is clearly analogous to the problem presented above, and is more mature.
> I think the answer is technically "no", not with a turing-complete language.
> 
> **_H:_** Limitations to the DSL will make the problem more tractable. 
> 
> **_H:_** Stochastic exploration of query paths in the style of `quickcheck` can give useful answers to many queries in many contexts.

A lot of work on communication frameworks has focused on _asynchronous_ communication,
a context in which many important properties of the protocol cannot be proven. 

> **_Q:_** What do we lose or gain when we constrain communication to be synchronous?
> 
> **_H:_** Because synchronous communication is easier to reason about, writing complex protocols in it will be easier than in an asynchronous system.

### Goals:

The things I must complete this semester are:

- A usable library for expressing a synchronous multi-party program in single-threaded style.
- A corresponding handler/interpreter for simulating such a program in a single process and logging all the communication that happens.
- A corresponding system for querying the logs produced.
- Some kind of analysis tool that can answer even limited questions about the logs that _could_ be produced, without access to real program inputs.
  (This may fall back to stochastic techniques _a la_ quickcheck.)

Nice-to-haves:

- A best-theoretically possible system for answering questions about what logs _could_ be produced.
- An handler for the DSL that actually performs communication between parallel processes. 



