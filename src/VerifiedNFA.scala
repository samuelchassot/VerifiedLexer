/** Author: Samuel Chassot
  */

import stainless.equations._
import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object VerifiedNFA {
  import RegularExpression._
  case class State(label: BigInt) {
    require(label >= 0)
  }
  abstract sealed class Transition[C]
  case class LabeledTransition[C](from: State, c: C, to: State)
      extends Transition[C]
  case class EpsilonTransition[C](from: State, to: State) extends Transition[C]

  case class NFA[C](
      startState: State,
      finalStates: List[State],
      errorState: State,
      transitions: List[Transition[C]],
      allStates: List[State]
  )

  def validNFA[C](nfa: NFA[C]): Boolean =
    nfa.allStates.contains(nfa.startState) &&
      nfa.allStates.contains(nfa.errorState) &&
      nfa.finalStates.forall(s => nfa.allStates.contains(s)) &&
      ListOps.noDuplicate(nfa.transitions) &&
      transitionsStates(nfa.transitions).forall(s => nfa.allStates.contains(s))

  /** Returns the list with no duplicates of the states in the list of
    * transitions
    *
    * @param transitions
    */
  def transitionsStates[C](transitions: List[Transition[C]]): List[State] = {
    transitions match {
      case Cons(hd, tl) =>
        hd match {
          case EpsilonTransition(from, to) =>
            ListUtils.concatWithoutDuplicates(
              transitionsStates(tl),
              List(to, from)
            )
          case LabeledTransition(from, _, to) =>
            ListUtils.concatWithoutDuplicates(
              transitionsStates(tl),
              List(to, from)
            )
        }
      case Nil() => Nil[State]()
    }
  } ensuring (res => ListOps.noDuplicate(res))

  def transitionsFrom[C](
      state: State,
      transitions: List[Transition[C]]
  ): List[Transition[C]] = {
    transitions match {
      case Cons(hd, tl) =>
        hd match {
          case EpsilonTransition(from, to) if from == state =>
            Cons(hd, transitionsFrom(state, tl))
          case LabeledTransition(from, c, to) if from == state =>
            Cons(hd, transitionsFrom(state, tl))
          case _ => transitionsFrom(state, tl)
        }
      case Nil() => Nil()
    }
  }

  // Romain's version
  @inline
  def fromRegexToNfa[C](r: Regex[C]): NFA[C] = {
    val finalState = getFreshState(Nil())
    val errorState = getFreshState(List(finalState))
    val states = List(errorState, finalState)
    val (startState, allStates, transitions) =
      go(r, finalState)(states, Nil(), errorState)
    NFA(startState, List(finalState), errorState, transitions, allStates)
  } ensuring (res => validNFA(res))
  def go[C](regex: Regex[C], cont: State)(
      allStates: List[State],
      transitions: List[Transition[C]],
      errorState: State
  ): (State, List[State], List[Transition[C]]) = {
    require(ListOps.noDuplicate(allStates))
    require(allStates.contains(cont))
    require(allStates.contains(errorState))

    regex match {
      case EmptyLang() => {
        ListUtils.lemmaSubseqRefl(allStates)
        (errorState, allStates, transitions)
      }
      case EmptyExpr() => {
        ListUtils.lemmaSubseqRefl(allStates)

        (cont, allStates, transitions)
      }
      case ElementMatch(c) => {
        val ste = getFreshState(allStates)
        val newAllStates = Cons(ste, allStates)
        val newTransitions = Cons(LabeledTransition(ste, c, cont), transitions)
        ListUtils.lemmaTailIsSubseqOfList(ste, allStates)

        (ste, newAllStates, newTransitions)

      }
      case Union(rOne, rTwo) => {
        val (steOne, statesAfterOne, transitionsAfterOne) =
          go(rOne, cont)(allStates, transitions, errorState)
        ListSpecs.subseqContains(allStates, statesAfterOne, errorState)
        val (steTwo, statesAfterTwo, transitionsAfterTwo) =
          go(rTwo, cont)(statesAfterOne, transitionsAfterOne, errorState)
        ListSpecs.subseqContains(statesAfterOne, statesAfterTwo, cont)
        val ste = getFreshState(statesAfterTwo)
        val newTransitions: List[Transition[C]] = Cons(
          EpsilonTransition(ste, steOne),
          Cons(EpsilonTransition(ste, steTwo), transitionsAfterTwo)
        )

        ListUtils.lemmaSubSeqTransitive(
          allStates,
          statesAfterOne,
          statesAfterTwo
        )
        ListSpecs.subseqContains(statesAfterOne, statesAfterTwo, steOne)

        (ste, Cons(ste, statesAfterTwo), newTransitions)

      }
      case Concat(rOne, rTwo) => {
        val (steTwo, statesAfterTwo, transitionsAfterTwo) =
          go(rTwo, cont)(allStates, transitions, errorState)
        ListSpecs.subseqContains(allStates, statesAfterTwo, errorState)
        val (ste, statesAfterOne, newTransitions) =
          go(rOne, steTwo)(statesAfterTwo, transitionsAfterTwo, errorState)

        assert(ListSpecs.subseq(allStates, statesAfterTwo)) // Cannot remove it

        ListUtils.lemmaSubSeqTransitive(
          allStates,
          statesAfterTwo,
          statesAfterOne
        )
        ListSpecs.subseqContains(allStates, statesAfterOne, cont)
        (ste, statesAfterOne, newTransitions)
      }
      case Star(r) => {
        val ste = getFreshState(allStates)
        val (innerSte, statesAfterInner, transitionsAfterInner) =
          go(r, ste)(Cons(ste, allStates), transitions, errorState)
        val newTransitions: List[Transition[C]] = Cons(
          EpsilonTransition(ste, innerSte),
          Cons(EpsilonTransition(ste, cont), transitionsAfterInner)
        )
        ListSpecs.subseqContains(Cons(ste, allStates), statesAfterInner, cont)
        ListSpecs.subseqContains(Cons(ste, allStates), statesAfterInner, ste)

        ListUtils.lemmaTailIsSubseqOfList(ste, allStates)
        ListUtils.lemmaSubSeqTransitive(
          allStates,
          Cons(ste, allStates),
          statesAfterInner
        )

        (ste, statesAfterInner, newTransitions)
      }
    }

  } ensuring (res =>
    ListOps.noDuplicate(res._2)
      && ListSpecs.subseq(allStates, res._2)
      && res._2.contains(cont)
      && res._2.contains(res._1)
  )

  def prefixSetNFA[C](nfa: NFA[C]): NFA[C] = {
    // case class NFA[C](startStates: List[State], finalStates: List[State], errorState: State, transitions: List[Transition[C]], allStates: List[State])
    NFA(
      nfa.startState,
      nfa.allStates.filter(_ != nfa.errorState),
      nfa.errorState,
      nfa.transitions,
      nfa.allStates
    )
  }

  // go function lemmas -------------------------------------------------------------------------------------------------------------------------------------------

  // Helper functions ---------------------------------------------------------------------------------------------------------------------------------------------
  def getFreshState(states: List[State]): State = {
    require(ListOps.noDuplicate(states))
    val newId = maxStateId(states) + 1
    lemmaMaxStatePlusOneNotInList(states)
    State(newId)
  } ensuring (s => ListOps.noDuplicate(Cons(s, states)))

  def maxStateId(states: List[State]): BigInt = {
    require(ListOps.noDuplicate(states))
    states match {
      case Nil() => -1
      case Cons(hd, tl) => {
        val tailMax = maxStateId(tl)
        if (hd.label > tailMax) {
          hd.label
        } else {
          tailMax
        }
      }
    }
  }
  def lemmaMaxStatePlusOneNotInList(states: List[State]): Unit = {
    require(ListOps.noDuplicate(states))
    states match {
      case Cons(hd, tl) => {
        lemmaMaxStatePlusOneNotInList(tl)
        if (maxStateId(states) == hd.label) {
          lemmaLabelBiggerThanMaxIdIsNotInList(tl, hd.label + 1)
        }
      }
      case Nil() => ()
    }
  } ensuring (!states.contains(State(maxStateId(states) + 1)))

  def lemmaLabelBiggerThanMaxIdIsNotInList(
      states: List[State],
      newLabel: BigInt
  ): Unit = {
    require(ListOps.noDuplicate(states))
    require(maxStateId(states) < newLabel)
    states match {
      case Nil()        => ()
      case Cons(hd, tl) => lemmaLabelBiggerThanMaxIdIsNotInList(tl, newLabel)
    }
  } ensuring (!states.contains(State(newLabel)))

}

object VerifiedNFAMatcher {
  import VerifiedNFA._
  import VerifiedRegexMatcher._
  import RegularExpression._
  import ListUtils._

  @inline
  def matchNFA[C](nfa: NFA[C], input: List[C]): Boolean = {
    require(validNFA(nfa))
    findLongestMatch(nfa, input)._2.isEmpty
  }

  @inline
  def findLongestMatch[C](nfa: NFA[C], input: List[C]): (List[C], List[C]) = {
    require(validNFA(nfa))
    findLongestMatchInner(nfa, nfa.startState, Nil(), input, Nil())
  }

  def findLongestMatchInner[C](
      nfa: NFA[C],
      currentState: State,
      pastChars: List[C],
      suffix: List[C],
      seenStatesSinceLastConsumption: List[State]
  ): (List[C], List[C]) = {
    require(validNFA(nfa))
    require(
      seenStatesSinceLastConsumption.forall(s => nfa.allStates.contains(s))
    )
    require(
      transitionsStates(nfa.transitions).contains(
        currentState
      ) || nfa.startState == currentState
    )
    decreases(suffix.size)
    (pastChars, suffix)
  } ensuring (res =>
    res._1.isEmpty || res._1.size >= pastChars.size && ListUtils.isPrefix(
      res._1,
      pastChars ++ suffix
    )
  )

  def epsilonClosure[C](
      nfa: NFA[C],
      startState: State,
      transitionsRec: List[Transition[C]],
      seen: List[State]
  ): List[State] = {
    require(validNFA(nfa))
    require(ListSpecs.subseq(transitionsRec, nfa.transitions))
    require(nfa.allStates.contains(startState))
    require(seen.forall(s => nfa.allStates.contains(s)))
    require(ListOps.noDuplicate(seen))
    decreases({
      lemmaForallContainsAndNoDuplicateThenSmallerList(nfa.allStates, seen)
      nfa.allStates.size - seen.size + transitionsRec.size
    })

    if (seen.contains(startState)) {
      seen
    } else {
      transitionsRec match {
        case Nil() => seen
        case Cons(hd, tl) => {
          ListUtils.lemmaSubseqRefl(transitionsRec)
          ListSpecs.subseqTail(transitionsRec, transitionsRec)
          ListUtils.lemmaSubSeqTransitive(tl, transitionsRec, nfa.transitions)

          hd match {
            case EpsilonTransition(from, to) => {
              if (from == startState) {
                val newSeen = Cons(startState, seen)
                ListSpecs.subseqContains(transitionsRec, nfa.transitions, hd)
                lemmaTransitionThenStatesInTransitionsStates(
                  nfa.transitions,
                  hd
                )
                ListUtils.lemmaSubseqRefl(nfa.transitions)
                lemmaInTransitionsStatesThenInAll(nfa, to)
                epsilonClosure(nfa, to, tl, newSeen)
              } else {
                epsilonClosure(nfa, startState, tl, seen)
              }
            }
            case LabeledTransition(from, c, to) => {
              epsilonClosure(nfa, startState, tl, seen)
            }
          }
        }
      }
    }
  } ensuring (res =>
    ListOps.noDuplicate(res) && res.forall(s => nfa.allStates.contains(s))
  )

  def lemmaInTransitionsStatesThenInAll[C](
      nfa: NFA[C],
      s: State
  ): Unit = {
    require(validNFA(nfa))
    require(transitionsStates(nfa.transitions).contains(s))

    ListUtils.lemmaForallContainsThenInOtherList(
      transitionsStates(nfa.transitions),
      nfa.allStates,
      s
    )

  } ensuring (nfa.allStates.contains(s))

  def lemmaTransitionThenStatesInTransitionsStates[C](
      transitions: List[Transition[C]],
      t: Transition[C]
  ): Unit = {
    require(transitions.contains(t))
    transitions match {
      case Nil() => check(false)
      case Cons(hd, tl) => {
        t match {
          case EpsilonTransition(from, to) => {
            if (hd != t) {
              lemmaTransitionThenStatesInTransitionsStates(tl, t)
            }
          }
          case LabeledTransition(from, _, to) => {
            if (hd != t) {
              lemmaTransitionThenStatesInTransitionsStates(tl, t)
            }
          }
        }
      }
    }

  } ensuring (t match {
    case EpsilonTransition(from, to) =>
      transitionsStates(transitions).contains(from) &&
      transitionsStates(transitions).contains(to)
    case LabeledTransition(from, _, to) =>
      transitionsStates(transitions).contains(from) &&
      transitionsStates(transitions).contains(to)
  })

  // @inlineOnce
  // @opaque
  // def getEpsilongTransitionsFrom[C](
  //     startState: State,
  //     nfa: NFA[C],
  //     transitionsListRec: List[Transition[C]]
  // ): List[Transition[C]] = {
  //   require(validNFA(nfa))
  //   require(ListSpecs.subseq(transitionsListRec, nfa.transitions))
  //   transitionsListRec match {
  //     case Cons(hd, tl) => {
  //       ListSpecs.subseqTail(transitionsListRec, nfa.transitions)
  //       hd match {
  //         case EpsilonTransition(from, to) if startState == from => {
  //           ListSpecs.subseqContains(transitionsListRec, nfa.transitions, hd)
  //           ListUtils.concatWithoutDuplicates(
  //             getEpsilongTransitionsFrom(startState, nfa, tl),
  //             List(hd)
  //           )
  //         }
  //         case _ => {
  //           getEpsilongTransitionsFrom(startState, nfa, tl)
  //         }

  //       }
  //     }
  //     case Nil() => Nil[Transition[C]]()
  //   }

  // } ensuring (res =>
  //   ListOps.noDuplicate(res) && res.forall(t =>
  //     nfa.transitions.contains(t)
  //   ) && res.size <= 2 && res.forall(t =>
  //     t match {
  //       case EpsilonTransition(from, to) => from == startState
  //       case _                           => false
  //     }
  //   )
  // )

  // @inlineOnce
  // @opaque
  // def getTransitionsFrom[C](
  //     startState: State,
  //     nfa: NFA[C],
  //     transitionsListRec: List[Transition[C]],
  //     c: C
  // ): List[Transition[C]] = {
  //   require(validNFA(nfa))
  //   require(ListSpecs.subseq(transitionsListRec, nfa.transitions))
  //   transitionsListRec match {
  //     case Cons(hd, tl) => {
  //       ListSpecs.subseqTail(transitionsListRec, nfa.transitions)
  //       hd match {
  //         case LabeledTransition(from, cInner, to)
  //             if startState == from && c == cInner => {
  //           ListSpecs.subseqContains(transitionsListRec, nfa.transitions, hd)

  //           ListUtils.concatWithoutDuplicates(
  //             getTransitionsFrom(startState, nfa, tl, c),
  //             List(hd)
  //           )
  //         }
  //         case EpsilonTransition(from, to) if startState == from => {
  //           ListSpecs.subseqContains(transitionsListRec, nfa.transitions, hd)
  //           ListUtils.concatWithoutDuplicates(
  //             getTransitionsFrom(startState, nfa, tl, c),
  //             List(hd)
  //           )
  //         }
  //         case _ => {
  //           getTransitionsFrom(startState, nfa, tl, c)
  //         }

  //       }
  //     }
  //     case Nil() => Nil[Transition[C]]()
  //   }

  // } ensuring (res =>
  //   ListOps.noDuplicate(res) && res.forall(t =>
  //     nfa.transitions.contains(t)
  //   ) && res.size <= 2
  // )

  // @inlineOnce
  // @opaque
  // def getStatesAfterChars[C](
  //     startStates: List[State],
  //     nfa: NFA[C],
  //     transitionsListRec: List[Transition[C]],
  //     c: C
  // ): List[State] = {
  //   require(validNFA(nfa))
  //   require(ListSpecs.subseq(transitionsListRec, nfa.transitions))
  //   decreases(transitionsListRec.size)
  //   transitionsListRec match {
  //     case Cons(hd, tl) => {
  //       ListSpecs.subseqTail(transitionsListRec, nfa.transitions)
  //       hd match {
  //         case LabeledTransition(from, cInner, to)
  //             if startStates.contains(from) && c == cInner => {
  //           ListSpecs.subseqContains(transitionsListRec, nfa.transitions, hd)
  //           lemmaTransitionInListThenToStatesInTransitionsStates(
  //             nfa.transitions,
  //             hd
  //           )
  //           assert(
  //             getStatesAfterChars(startStates, nfa, tl, c).forall(s =>
  //               transitionsStates(nfa.transitions).contains(
  //                 s
  //               ) || nfa.startStates.contains(s)
  //             )
  //           )
  //           ListUtils.concatWithoutDuplicates(
  //             getStatesAfterChars(startStates, nfa, tl, c),
  //             List(to)
  //           )
  //         }
  //         case _ => getStatesAfterChars(startStates, nfa, tl, c)
  //       }
  //     }
  //     case Nil() => Nil[State]()
  //   }

  // } ensuring (res =>
  //   ListOps.noDuplicate(res) && res.forall(s =>
  //     transitionsStates(nfa.transitions).contains(s) || nfa.startStates
  //       .contains(s)
  //   )
  // )

  def lemmaTransitionInListThenToStatesInTransitionsStates[C](
      l: List[Transition[C]],
      t: Transition[C]
  ): Unit = {
    require(l.contains(t))
    l match {
      case Cons(hd, tl) if hd == t => ()
      case Cons(hd, tl) =>
        lemmaTransitionInListThenToStatesInTransitionsStates(tl, t)
      case Nil() => check(false)
    }
  } ensuring (t match {
    case LabeledTransition(from, _, to) =>
      transitionsStates(l).contains(from) && transitionsStates(l).contains(to)
    case EpsilonTransition(from, to) =>
      transitionsStates(l).contains(from) && transitionsStates(l).contains(to)
  })

  @inline
  def isEpsilonTransition[C](t: Transition[C]): Boolean = t match {
    case EpsilonTransition(_, _) => true
    case _                       => false
  }

  // Longest match theorems
  def longestMatchIsAcceptedByMatchOrIsEmpty[C](
      nfa: NFA[C],
      input: List[C]
  ): Unit = {
    require(validNFA(nfa))
    // lemmaNfaStartStatesForallContainsStatesOrStartStates(nfa, nfa.startStates)
    // check(
    //   nfa.startStates.forall(s =>
    //     transitionsStates(nfa.transitions).contains(s) || nfa.startStates
    //       .contains(s)
    //   )
    // )
    // longestMatchIsAcceptedByMatchOrIsEmptyInner(
    //   nfa,
    //   input,
    //   findLongestMatchInner(nfa, nfa.startStates, Nil(), input)._1,
    //   Nil(),
    //   nfa.startStates
    // )

  } ensuring (findLongestMatchInner(
    nfa,
    nfa.startState,
    Nil(),
    input,
    Nil()
  )._1.isEmpty || matchNFA(
    nfa,
    findLongestMatchInner(nfa, nfa.startState, Nil(), input, Nil())._1
  ))

  // def longestMatchIsAcceptedByMatchOrIsEmptyInner[C](
  //     nfa: NFA[C],
  //     inputSuffix: List[C],
  //     matchedP: List[C],
  //     seenChars: List[C],
  //     startStates: List[State]
  // ): Unit = {
  //   require(validNFA(nfa))
  //   require(ListOps.noDuplicate(startStates))
  //   require(
  //     startStates.forall(s =>
  //       transitionsStates(nfa.transitions).contains(s) || nfa.startStates
  //         .contains(s)
  //     )
  //   )
  //   // require({
  //   //   ListUtils.lemmaSubseqRefl(nfa.startStates)
  //   //   lemmaNfaStartStatesForallContainsStatesOrStartStates(nfa, nfa.startStates)
  //   //   moveMultipleSteps(nfa, nfa.startStates, seenChars) == startStates
  //   // })
  //   require({
  //     ListUtils.lemmaSubseqRefl(nfa.startStates)
  //     lemmaNfaStartStatesForallContainsStatesOrStartStates(nfa, nfa.startStates)
  //     findLongestMatchInner(
  //       nfa,
  //       startStates,
  //       seenChars,
  //       inputSuffix
  //     )._1 == matchedP
  //   })

  //   decreases(inputSuffix.size)
  //   if (inputSuffix.isEmpty) {
  //     if (
  //       !nfa.finalStates
  //         .map(s => startStates.contains(s))
  //         .filter(_ == true)
  //         .isEmpty
  //     ) {
  //       ListUtils.lemmaConcatTwoListThenFirstIsPrefix(seenChars, inputSuffix)
  //       check(ListUtils.isPrefix(seenChars, seenChars ++ inputSuffix))
  //       assert(
  //         findLongestMatchInner(
  //           nfa,
  //           startStates,
  //           seenChars,
  //           inputSuffix
  //         ) == (seenChars, inputSuffix)
  //       )
  //       assert(matchedP == seenChars)
  //       // (pastChars, suffix)
  //     } else {
  //       assert(matchedP.isEmpty)
  //       // (Nil(), pastChars)
  //     }
  //   } else {
  //     if (seenChars == matchedP) {
  //       ()
  //     } else {
  //       if (matchedP.isEmpty) {
  //         ()
  //       } else {
  //         assert(
  //           findLongestMatchInner(
  //             nfa,
  //             startStates,
  //             seenChars,
  //             inputSuffix
  //           )._1 == matchedP
  //         )
  //         assert(seenChars.size <= matchedP.size)
  //         if (seenChars.size == matchedP.size) {
  //           ListUtils.lemmaIsPrefixSameLengthThenSameList(
  //             matchedP,
  //             seenChars,
  //             seenChars ++ inputSuffix
  //           )
  //         }
  //         assert(seenChars.size < matchedP.size)
  //       }
  //     }

  //   }

  // } ensuring (matchedP.isEmpty || matchNFA(nfa, matchedP))

  // @opaque
  // def lemmaFromStartOrFromMultipleStepsForwardWithSmallerPrefixSame[C](
  //     nfa: NFA[C],
  //     resultP: List[C],
  //     resultSuffix: List[C],
  //     smallerP: List[C],
  //     biggerSuffix: List[C]
  // ): Unit = {
  //   require(validNFA(nfa))
  //   require(ListUtils.isPrefix(smallerP, resultP))
  //   require(smallerP ++ biggerSuffix == resultP ++ resultSuffix)
  //   require({
  //     ListUtils.lemmaSubseqRefl(nfa.startStates)
  //     lemmaNfaStartStatesForallContainsStatesOrStartStates(nfa, nfa.startStates)
  //     findLongestMatchInner(
  //       nfa,
  //       nfa.startStates,
  //       Nil(),
  //       resultP ++ resultSuffix
  //     )._1 == resultP
  //   })
  //   require({
  //     ListUtils.lemmaSubseqRefl(nfa.startStates)
  //     lemmaNfaStartStatesForallContainsStatesOrStartStates(nfa, nfa.startStates)
  //     findLongestMatchInner(
  //       nfa,
  //       nfa.startStates,
  //       Nil(),
  //       resultP ++ resultSuffix
  //     )._2 == resultSuffix
  //   })
  //   decreases(smallerP.size)

  //   if (smallerP.isEmpty) {
  //     ()
  //   } else {
  //     if (smallerP.size == resultP.size) {
  //       ListUtils.lemmaIsPrefixRefl(resultP, resultP)
  //       ListUtils.lemmaIsPrefixSameLengthThenSameList(
  //         smallerP,
  //         resultP,
  //         resultP
  //       )
  //       // unfold(
  //       //   findLongestMatchInner(
  //       //     nfa,
  //       //     moveMultipleSteps(nfa, nfa.startStates, smallerP),
  //       //     smallerP,
  //       //     biggerSuffix
  //       //   )
  //       // )
  //       // check(
  //       //   findLongestMatchInner(
  //       //     nfa,
  //       //     moveMultipleSteps(nfa, nfa.startStates, smallerP),
  //       //     smallerP,
  //       //     biggerSuffix
  //       //   )._1 == resultP
  //       // )
  //     } else {
  //       val newSmallerP = smallerP ++ List(biggerSuffix.head)
  //       val newBiggerSuffix = biggerSuffix.tail
  //       check(
  //         findLongestMatchInner(
  //           nfa,
  //           moveMultipleSteps(nfa, nfa.startStates, smallerP),
  //           smallerP,
  //           biggerSuffix
  //         )._1 == resultP
  //       )
  //     }
  //     // val newSmallerP = ListUtils.removeLast(smallerP)
  //     // val newBigSuffix = Cons(smallerP.last, biggerSuffix)
  //     // ListUtils.lemmaRemoveLastConcatenatedPrefixStillPrefix(newSmallerP, smallerP.last, resultP)
  //     // assert(ListUtils.isPrefix(newSmallerP, resultP))

  //     // ListUtils.lemmaConcatAssociativity(newSmallerP, smallerP.last, biggerSuffix, resultP ++ resultSuffix)
  //     // assert(newSmallerP ++ newBigSuffix == resultP ++ resultSuffix)
  //     // lemmaFromStartOrFromMultipleStepsForwardWithSmallerPrefixSame(nfa, resultP, resultSuffix, newSmallerP, newBigSuffix)
  //     // // assert(
  //     // //   findLongestMatchInner(nfa, moveMultipleSteps(nfa, nfa.startStates, newSmallerP), newSmallerP, newBigSuffix) ==
  //     // //     findLongestMatchInner(nfa, moveMultipleSteps(nfa, nfa.startStates, smallerP), smallerP, biggerSuffix)
  //     // // )
  //     // assert(moveOneStep(nfa, moveMultipleSteps(nfa, nfa.startStates, newSmallerP), smallerP.last) == moveMultipleSteps(nfa, nfa.startStates, smallerP))
  //     // assert(newSmallerP ++ List(smallerP.last) == smallerP)

  //     // assert(findLongestMatchInner(nfa, moveMultipleSteps(nfa, nfa.startStates, newSmallerP), newSmallerP, newBigSuffix)._1 == resultP)
  //     // assert(
  //     //   findLongestMatchInner(nfa, moveOneStep(nfa, moveMultipleSteps(nfa, nfa.startStates, newSmallerP), smallerP.last), smallerP, biggerSuffix) ==
  //     //     findLongestMatchInner(nfa, moveMultipleSteps(nfa, nfa.startStates, newSmallerP), newSmallerP, newBigSuffix)
  //     // ) // TODO
  //   }

  // } ensuring (findLongestMatchInner(
  //   nfa,
  //   moveMultipleSteps(nfa, nfa.startStates, smallerP),
  //   smallerP,
  //   biggerSuffix
  // )._1 == resultP)

  // def lemmaFromAPrefixIsSameAsOneStepBehind[C](nfa: NFA[C], seenChars:List[C], remainingChars: List[C], resultP: List[C], resultSuffix: List[C]): Unit = {
  //   require(seenChars ++ remainingChars == resultP ++ resultSuffix)
  //   require(findLongestMatchInner(nfa, moveMultipleSteps(nfa, nfa.startStates, seenChars), seenChars, remainingChars)._1 == resultP)
  //   require(findLongestMatchInner(nfa, moveMultipleSteps(nfa, nfa.startStates, seenChars), seenChars, remainingChars)._2 == resultSuffix)
  // } ensuring(findLongestMatchInner(nfa, moveMultipleSteps(nfa, nfa.startStates, seenChars), seenChars, remainingChars) ==
  //   findLongestMatchInner(nfa, moveOneStep(moveMultipleSteps(nfa, nfa.startStates, seenChars), seenChars, remainingChars))

  // def lemmaNfaStartStatesForallContainsStatesOrStartStates[C](
  //     nfa: NFA[C],
  //     l: List[State]
  // ): Unit = {
  //   require(validNFA(nfa))
  //   require(ListSpecs.subseq(l, nfa.startStates))
  //   l match {
  //     case Cons(hd, tl) => {
  //       ListSpecs.subseqTail(l, nfa.startStates)
  //       ListSpecs.subseqContains(l, nfa.startStates, hd)

  //       lemmaNfaStartStatesForallContainsStatesOrStartStates(nfa, tl)
  //     }
  //     case Nil() => ()
  //   }

  // } ensuring (l.forall(s =>
  //   transitionsStates(nfa.transitions).contains(s) || nfa.startStates
  //     .contains(s)
  // ))

  def longestMatchNoBiggerStringMatch[C](
      baseNfa: NFA[C],
      input: List[C],
      returnP: List[C],
      bigger: List[C]
  ): Unit = {
    require(validNFA(baseNfa))
    require(ListUtils.isPrefix(returnP, input))
    require(ListUtils.isPrefix(bigger, input))
    require(bigger.size >= returnP.size)
    require(
      findLongestMatchInner(
        baseNfa,
        baseNfa.startState,
        Nil(),
        input,
        Nil()
      )._1 == returnP
    )

    if (bigger.size == returnP.size) {
      ListUtils.lemmaIsPrefixSameLengthThenSameList(bigger, returnP, input)
    } else {
      // if (matchR(baseR, bigger)) {
      //   lemmaKnownAcceptedStringThenFromSmallPAtLeastThat(baseR, baseR, input, Nil(), bigger)
      //   check(false)
      // }
    }

  } ensuring (bigger == returnP || !matchNFA(baseNfa, bigger))

  // Regex equivalence theorem
  @extern
  def equivalenceTheorem[C](r: Regex[C], s: List[C]): Unit = {
    require(validRegex(r))
    assume(
      findLongestMatch(fromRegexToNfa(r), s) == VerifiedRegexMatcher
        .findLongestMatch(r, s)
    )
  } ensuring (findLongestMatch(fromRegexToNfa(r), s) == VerifiedRegexMatcher
    .findLongestMatch(r, s))

}
