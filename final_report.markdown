---
title: "Expression and Analysis of Synchronous Communication Plans"
subtitle: "Final project report for cs395"
author: "Mako Bates"
date: "2021-12-16"

header-includes: |
  <style>
    body {
      
    }
    h2 {
      margin-top: 4em;
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
    td {
      padding: 0.5em;
    }
  </style>
---

## Problem Statement

The goal for this semester was to build a DSL for concisely expressing programs in which various parties must communicate. 
In particular, I've considered the case where issues of latency and network fallibility are handled by external systems,
and all branching is on shared data (so that all messages received are anticipated, and all anticipated messages are received). 
This is in contrast to the majority of work on communication protocols, where less synchronicity or reliability are assumed,
and so much less can be proven about the program in advance. 

As proposed, there were four core goals for the semester.
A couple other goals not specified from the beginning should also be considered.

| <span style="display: inline-block; width: 15em; margin-left: 1em;">Goal</span> | Status | <span style="display: inline-block; width: 25em; margin-left: 1em;">Notes</span> |
|:--|:--:|:--|
| A library for expressing a synchronous multi-party program in single-threaded style. | ✓ | One serious caveat is discussed in _Methods_, and a list of outstanding "nice to haves" is provided in _Future Work_. |
| A interpreter for simulating such a program in a single process and logging all the communication that happens. | ✓ | No caveats. |
| A corresponding system for querying the logs produced. | ✓ | Because the generated logs are just a list, off-the-shelf functions work fine. A couple helpers are provided. |
| An analysis tool that can answer questions about hypothetical logs, without access to real program inputs. | ? | I've demonstrated that QuickCheck works fine against this library, but have not built anything on top of that or exposed the underlying iteration process to allow non-assertion analysis. | 
| _Evaluation of a single party's view_ | ✓ | For the purpose of knowing if the system is sound, it's important to be able to run only the aspects of the program that are visible to a single party. This view should be executable in isolation, with messages performed over IO. Obviously this would also be important if the system were to actually be used for anything. |
| _Lazy evaluation of non-terminating programs._ | ✗ | In general, it should not be necessary to evaluate a program to completion when checking an assertion of the form "such'n'such happens". |

My own context for this project is my ongoing work to build a type system for verification of Secure Multi-Party Communication protocols. 
For that project, I'm using traditional lambda-calculus-style formal methods to prove the probabilistic meta-theory.
The _semantics_ of the language to which the type system will be applied will be basically the same, at least abstractly, as what I've built here.
For this purpose my semester project has been largely successful:
I've validated that my intended semantics are _viable_ and _useable_;
the semantics still seem to be sound and sensible,
and I've found some implementation pitfalls that I'll be able to avoid as the larger project progresses.


## Methods

Because my other work is still in the early theoretical stages, I did this project "implementation first". 
This has the advantage that I have an actual system now who's behavior and ergonomics I can investigate immediately.
The disadvantage is that I don't have any formal verification of the fundamental meta-theory we would hope for in a synchronous-communication system:
that well-typed programs can be fully evaluated (to the same value) in both single-threaded and parallel semantics. 
Indeed, I strongly suspect that the exposed API would allow programs to be compiled by GHC that would behave differently
when run in parallel vs a single-thread. (I mean without using the cheats Haskell has built into its type-system.)

The "DSL" is represented as an API in Haskell. 
Most functionality is represented as "effects" in the [polysemy](https://hackage.haskell.org/package/polysemy) effect system.
The _intended public_ API is in the module `LCom`. The core functionality is

```haskell
Party       -- A wrapper kind, internally just a Nat.
Located     -- A wrapper type for values known to some parties

-- A group of parties can send values between each other, unwrap a value if everyone knows it, or run a sub-program that only involves a subset of them.
Communicate :: [Party] -> messageType -> Effect
send        :: (Subset recipients parties,
                Subset senders parties,
                Member (Communicate parties s) r) =>
               Located senders t -> Sem r (Located recipients t)
locally     :: (Member (Communicate parties s) r) => Located parties a  -> Sem r a
runClique   :: (Subset clq parties) =>
               Sem (Communicate clq s ': r) a
               -> Sem (Communicate parties s ': r) (Located clq a)

-- Parties begin with some inputs known only to them, and can write private return-values.
Local       :: inputType -> outputType -> Effect
localInput  :: (Member (Local i o) r) => Sem r (Located p i)
localOutput :: (Member (Local i o) r) => Located '[p] o -> Sem r ()

-- Effect handlers:
  -- Run a communication program in a single thread:
noEffectSingleThread         :: Sem (Communicate parties s ': r) a -> Sem r a
  -- Run in a single thread, logging all the "communication":
logTransmissionsSingleThread :: Sem (Communicate parties s ': r) a
                                -> Sem r ([Transmission s], a)
  -- Run only the view of one party; all their communication becomes I/O:
runParty                     :: forall p∈parties.
                                Sem (Communicate parties s ': r) a
                                -> Sem (Input (Maybe s)
                                        ': Output ([Integer], Maybe s)
                                        ': r) a
  -- Provide the private inputs of all parties, and accumulate their private outputs:
runAllLocalIO                :: [i] -> Sem (Local i o ': r) a
                                -> Sem r ([(Integer, o)], a)
  -- Provide the private input of just one party, and log its output (use with runParty):
runLocalIO                   :: forall p.
                                i -> Sem (Local i o ': r) a
                                -> Sem r ([o], a)
```

The actual implementations of all of this is in the `LCom.Internal.` modules.
There is no _internal_ enforcement that programs be well-behaved.
For example, importing the _data constructor_ for `Located` from `LCom.Internal.Data`
would allow one to unpack `Located` values without regard to "where" they were located;
this would undoubtedly result in `undefined` errors when `runParty` was applied.
Forgoing "deep" enforcement of the meta-theory simplifies the implementation significantly,
in particular it moots the problem that the `Subset` typeclass isn't transitive. 

### Example: a simple dice game.

The `Examples` module contains some demonstrations of how the Effects are used in programs. 
In `app/Main.hs`, units demonstrate how to handle these effectful programs in different ways. 

Consider the example program `raceTo100`.
In this program, three parties take turns generating random numbers. 
The lower bound for each roll is just two less than the running maximum; whoever rolls 100 first wins.
(It's not a good game.)
Here's a simplified version of the program:

```haskell
raceTo100 :: Sem '[Local RNG String, Communicate Trio Int] Int
raceTo100 = (execState 0  -- Run the State counter from 0.
             (turn @Party1 @Party2 @Party3 2))  -- player 1 goes first.
  where turn :: forall p1 p2 p3. -- This progam recurses, cycling the players.
                Int ->  -- The running-max "base" sets the lower bound for rolls.
                Sem '[State Int, Communicate Trio Int, Local RNG String] ()
        turn base = do modify (+ 1)  -- Count the number of turns.
                       mRoll <- runClique (  -- Work with values only p1 has.
                         do let roll = randomR (base - 2, 100) localRNG
                            let progress = roll > base
                            localOutput @p1 (privateLog progress roll)
                            -- If p1 hasn't beat the running max, share Nothing.
                            return (if progress then Just roll else Nothing)
                         )
                       -- Broadcast and unwrap:
                       opened <- send @Trio mRoll >>= locally
                       let base' = maybe base (max base) opened
                       if base' < 100 then turn @p2 @p3 @p1 base' -- Recurse!
                                      else do localOutput @p1 "I won!"
        privateLog progress roll = "Rolled " <> (show roll) <> "; "
                                   <> if progress then "Progress!" else "Failure."
```

One problem with the system can be seen in this simplified version. 
The use of `State`, an off-the-shelf polysemy Effect, is textbook, and exactly how we would expect Effects to inter-operate. 
However, consider what would happen if the state were modified inside of the `runClique` block.
In single-threaded semantics, this would behave as expected,
but in parallel semantics each party would be maintaining their own state in parallel
and only performing updates for which they were "present".
The states would diverge, which could affect branching, which could cause communication to go out of synch. 

One would not need to use `runClique` to invoke this failure; `Located p` is `Applicative` and this is seen to be useful in other examples.
Neither would it help to try to place constraints on the ordering of Effects in the `Sem` stack; 
polysemy's `subsume_` function (intentionally and importantly) allows arbitrary re-ordering of the stack. 
The only viable "solution" would be to tighten the wrapper so that the exposed API is in terms of a monolithic concrete `Monad`. 
(The implementation would probably still use polysemy.)
On the other hand, full air-tightness is impossible in any genera-purpose language; it may not be advisable to aim higher than I have here.

Other problems require comparing the simplified version of `raceTo100` to the actual source code:

- There's a lot of type-level boiler-plate.  
  There are a couple of aspects of the system that require class-constraints to be copied everywhere a certain types are parametric.
  There's no way around this.
- A lot of extra complexity comes from taking PRNGs for each party as private input.  
  This is a great demonstration of why it is nice to have the full power of an effect system.
  All of this complexity could have been skipped or sequestered if I'd been able to use `Random` from `polysemy-zoo`,
  but sorting out the package dependencies looked like a chore so I skipped it.

The code to "run" this program in `Main.hs` is already pleasantly short:

```haskell
playGame :: IO ()
playGame = do log "roll random numbers" "Get to 100!"
              rng <- newStdGen
              (outputs, result) <- runM (
                runInputOutputAsIO (runParty @Party0 (runLocalIO @Party0 rng raceTo100))
                )
              logS "Outputs" outputs
              log "Result" result
```

Never mind that some details have been hidden in helper-functions; what does it look like to actually run that?

```javascript
roll random numbers: "Get to 100!"
Output:
([0],Just 3)                      // Party0 rolled poorly.
Input:
Just 3                            // We have to echo that back manually.
Input:
Just 98                           // Cheat and pretend Party1 got lucky.
Input:
Nothing                           // Party2 did not.
Output:
([0],Just 99)                     // Because of how the rolls work, making progress is normal.
Input:
Just 99                           // Again, we have to echo back Party0's message to themself.
Input:
Nothing                           // Be lazy making up rolls for Party1,
Input:
Nothing                           // and Party2.
Output:
([0],Just 100)                    // Party0 has a 1/3 chance to progress here.
Input:
Just 100                          // Echo it back again.
Outputs: "Rolled 3; Progress!"    // Now we see what Party0 logged during the game.
         "Rolled 99; Progress!"
         "Rolled 100; Progress!"
         "I won!"
Result: 7                         // The `State` counter says the game took 7 turns.
```

Obviously there are more problems:

- `runParty` leaves residual `Input` and `Output` Effects.
  The subsequent handler into proper `IO` no longer has access to information about who a message is going to or coming from;
  so trying to actually "play" the game is impossible without a complete understanding of what the computer is doing at each step.
  It also creates/fails to handle situations where a party is sending a message _to themself_. 
- `logTransmissionsSingleThread` generates a flat list of `Transmission` objects,
  which is fine but offers an analyst no help in determining what part of the program a given message came from.
- All of the handlers mask the open-ended nature of "Parties",
  instead assuming (and requiring) that the parties can be represented by integer addresses. 
  Party-wise inputs and outputs become address-indexed lists; `Transmissions` are annotated with lists of addresses.
  Some of this is fine (_e.g._ we would not want the list of `Transmissions` to be parametric), 
  but it should be possible to enforce better alignment between inputs and the participating parties.


## Future Work

I have a standing punch-list of items that would be immediately nice to have in this library:

- Enrich the API so that not everything has to be a _list_ of parties; certain operations are usually called on just one party.
- Utility functions for transposing located data structures.
  It's not clear if it's safe to make `Located p` `Traversable` or `Distributive`, but those may be good options.
- Maybe support heterogeneous inputs and outputs? I think this should be possible with a better understanding of how type-level-sets work.
- A more type-safe way of expressing inputs and outputs.
- A more machine-efficient way of handling inputs and outputs. Right now I'm using the `!!` operator a lot, which isn't great.
- Better naming, _e.g._ for `locally`. 
- Add labels to (and change name of) `runClique`, so it can be used to annotate where in a program logged communication happens. 
- Pretty printing of general output.
- Lazy evaluation of infinite programs.

In terms of semester goals, the biggest shortfall is _analysis_. 
Adding subject-lines to messages would help, as would naming `runClique` blocks. 
This would allow richer analysis of realized communication lists, and should also combine with lazy evaluation.
Exploring the _space of hypothetical communication lists_ would require better tools than QuickCheck. 
I believe the `Serial` interface exposed by [lazysmallcheck](https://hackage.haskell.org/package/lazysmallcheck-0.6) would be ideal,
but I haven't started unpacking that project. 

For the purpose of my ongoing MPC research, some of this library is usable as-is. 
The program `threePartyXOR` in `Examples` is precisely the "minimal example" I'm using for that work,
and the communication-logs it produces confirm that it's working as intended. 
A likely implementation of the full implementation of my target system would look like a three-layer sandwich:
A parser and type-checker for a stand-alone language, which yields programs in the `LCom` API,
which get passed to a more robust handler-system that can run the parties in parallel in separate threads. 

Assuming the formal methods I'm using for the larger project continue to "work",
I'm unlikely to return to the analysis aspect of this library.
On the other hand, another strategy I've discussed with my advisors is to "enforce" the language's meta-theory
by statistical analysis of random program runs;
this would require actually building the SmallCheck-based system, or something like it.


## Github
The current code-base is [online](https://github.com/ShapeOfMatter/LCom).
