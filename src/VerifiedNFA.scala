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
  case class LabeledTransition[C](from: State, c: C, to: State) extends Transition[C]
  case class EpsilonTransition[C](from: State, to: State) extends Transition[C]

  case class NFA[C](
      startState: State,
      finalStates: List[State],
      errorState: State,
      transitions: List[Transition[C]],
      allStates: List[State]
  )

  @inline
  def validNFA[C](nfa: NFA[C]): Boolean =
    nfa.allStates.contains(nfa.startState) &&
      nfa.allStates.contains(nfa.errorState) &&
      nfa.finalStates.forall(s => nfa.allStates.contains(s)) &&
      transitionsStates(nfa.transitions).forall(s => nfa.allStates.contains(s)) &&
      noTransitionOutOfErrorState(nfa.transitions, nfa.errorState) &&
      !nfa.finalStates.contains(nfa.errorState) &&
      ListSpecs.noDuplicate(nfa.transitions)

  def noTransitionOutOfErrorState[C](
      l: List[Transition[C]],
      errorState: State
  ): Boolean = {
    l match {
      case Cons(hd, tl) =>
        hd match {
          case EpsilonTransition(from, to)    => from != errorState && noTransitionOutOfErrorState(tl, errorState)
          case LabeledTransition(from, _, to) => from != errorState && noTransitionOutOfErrorState(tl, errorState)
        }
      case Nil() => true
    }
  }

  def transitionsStates[C](transitions: List[Transition[C]]): List[State] = {
    transitions match {
      case Cons(hd, tl) =>
        hd match {
          case EpsilonTransition(from, to)    => Cons(from, Cons(to, transitionsStates(tl)))
          case LabeledTransition(from, _, to) => Cons(from, Cons(to, transitionsStates(tl)))
        }
      case Nil() => Nil[State]()
    }
  }

  @inline
  def isEpsilonTransition[C](t: Transition[C]): Boolean = t match {
    case EpsilonTransition(_, _) => true
    case _                       => false
  }

  @inline
  def isLabeledTransition[C](t: Transition[C]): Boolean = t match {
    case LabeledTransition(_, _, _) => true
    case _                          => false
  }

  def transitionsFrom[C](
      state: State,
      transitions: List[Transition[C]]
  ): List[Transition[C]] = {
    require(ListSpecs.noDuplicate(transitions))
    transitions match {
      case Cons(hd, tl) =>
        hd match {
          case EpsilonTransition(from, to) if from == state    => Cons(hd, transitionsFrom(state, tl))
          case LabeledTransition(from, c, to) if from == state => Cons(hd, transitionsFrom(state, tl))
          case _                                               => transitionsFrom(state, tl)
        }
      case Nil() => Nil()
    }
  } ensuring (res =>
    ListSpecs.subseq(res, transitions) &&
      res.forall(t =>
        t match {
          case EpsilonTransition(from, _)    => from == state
          case LabeledTransition(from, _, _) => from == state
        }
      )
  )

  def epsilonTransitionsFrom[C](
      state: State,
      transitions: List[Transition[C]]
  ): List[Transition[C]] = {
    require(ListSpecs.noDuplicate(transitions))
    transitions match {
      case Cons(hd, tl) =>
        hd match {
          case EpsilonTransition(from, to) if from == state => {
            ListSpecs.noDuplicateSubseq(Cons(hd, epsilonTransitionsFrom(state, tl)), transitions)
            Cons(hd, epsilonTransitionsFrom(state, tl))
          }
          case _ => epsilonTransitionsFrom(state, tl)
        }
      case Nil() => Nil()
    }
  } ensuring (res =>
    ListSpecs.subseq(res, transitions) &&
      res.forall(t => transitionFromEq(t, state)) &&
      ListSpecs.subseq(res, transitionsFrom(state, transitions)) &&
      ListSpecs.noDuplicate(res)
  )

  def labeledTransitionsFrom[C](
      state: State,
      transitions: List[Transition[C]]
  ): List[Transition[C]] = {
    require(ListSpecs.noDuplicate(transitions))
    transitions match {
      case Cons(hd, tl) =>
        hd match {
          case LabeledTransition(from, _, to) if from == state => Cons(hd, labeledTransitionsFrom(state, tl))
          case _                                               => labeledTransitionsFrom(state, tl)
        }
      case Nil() => Nil()
    }
  } ensuring (res =>
    ListSpecs.subseq(res, transitions) &&
      res.forall(t => transitionFromEq(t, state))
      && ListSpecs.subseq(res, transitionsFrom(state, transitions))
  )

  @inline
  def transitionFromEq[C](t: Transition[C], s: State): Boolean = t match {
    case EpsilonTransition(from, _)    => from == s
    case LabeledTransition(from, _, _) => from == s
  }

  // Romain's version
  @inline
  def fromRegexToNfa[C](r: Regex[C]): NFA[C] = {
    val finalState = getFreshState(Nil())
    val errorState = getFreshState(List(finalState))
    val states = List(errorState, finalState)
    val (startState, allStates, transitions) =
      go(r, finalState)(states, Nil(), errorState)
    // lemmaGoTransitionsNoDuplicate(r, finalState, states, Nil(), errorState)
    lemmaSameTransitionContentThenSameTransitionsStatesContent(transitions, ListUtils.removeDuplicates(transitions))
    ListUtils.lemmaForallContainsPreservedIfSameContent(transitionsStates(transitions), transitionsStates(ListUtils.removeDuplicates(transitions)), allStates)

    lemmaSameTransitionsContentOutOfErrorStatePreserved(transitions, ListUtils.removeDuplicates(transitions), errorState)
    assert(noTransitionOutOfErrorState(ListUtils.removeDuplicates(transitions), errorState)) // TODO

    NFA(startState, List(finalState), errorState, ListUtils.removeDuplicates(transitions), allStates)
  } ensuring (res => validNFA(res))

  def go[C](regex: Regex[C], cont: State)(
      allStates: List[State],
      transitions: List[Transition[C]],
      errorState: State
  ): (State, List[State], List[Transition[C]]) = {
    require(ListOps.noDuplicate(allStates))
    require(allStates.contains(cont))
    require(allStates.contains(errorState))
    require(transitionsStates(transitions).forall(s => allStates.contains(s)))
    require(noTransitionOutOfErrorState(transitions, errorState))

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
        val newTransition = LabeledTransition(ste, c, cont)
        val newTransitions = Cons(newTransition, transitions)
        ListUtils.lemmaTailIsSubseqOfList(ste, allStates)

        lemmaTransitionsWithNewStateCannotBeInList(transitions, allStates, ste, newTransition)

        lemmaAddNewTransitionWithOneNewStatePreservesForallStatesContained(transitions, newTransition, ste, cont, allStates)

        (ste, newAllStates, newTransitions)

      }
      case Union(rOne, rTwo) => {
        val (steOne, statesAfterOne, transitionsAfterOne) =
          go(rOne, cont)(allStates, transitions, errorState)

        ListSpecs.subseqContains(allStates, statesAfterOne, errorState)

        val (steTwo, statesAfterTwo, transitionsAfterTwo) = go(rTwo, cont)(statesAfterOne, transitionsAfterOne, errorState)

        ListSpecs.subseqContains(statesAfterOne, statesAfterTwo, cont)

        val ste = getFreshState(statesAfterTwo)
        val newTransitions: List[Transition[C]] = Cons(EpsilonTransition(ste, steOne), Cons(EpsilonTransition(ste, steTwo), transitionsAfterTwo))

        ListUtils.lemmaSubSeqTransitive(allStates, statesAfterOne, statesAfterTwo)
        ListSpecs.subseqContains(statesAfterOne, statesAfterTwo, steOne)

        ListUtils.lemmaForallContainsAddingInSndListPreserves(transitionsStates(transitionsAfterTwo), statesAfterTwo, ste)
        lemmaAddNewTransitionWithOneNewStatePreservesForallStatesContained(transitionsAfterTwo, EpsilonTransition(ste, steTwo), ste, steTwo, statesAfterTwo)

        (ste, Cons(ste, statesAfterTwo), newTransitions)

      }
      case Concat(rOne, rTwo) => {
        val (steTwo, statesAfterTwo, transitionsAfterTwo) = go(rTwo, cont)(allStates, transitions, errorState)
        ListSpecs.subseqContains(allStates, statesAfterTwo, errorState)

        val (ste, statesAfterOne, newTransitions) = go(rOne, steTwo)(statesAfterTwo, transitionsAfterTwo, errorState)

        assert(ListSpecs.subseq(allStates, statesAfterTwo)) // Cannot remove it

        ListUtils.lemmaSubSeqTransitive(allStates, statesAfterTwo, statesAfterOne)
        ListSpecs.subseqContains(allStates, statesAfterOne, cont)

        (ste, statesAfterOne, newTransitions)
      }
      case Star(r) => {
        val ste = getFreshState(allStates)
        ListUtils.lemmaForallContainsAddingInSndListPreserves(transitionsStates(transitions), allStates, ste)
        val (innerSte, statesAfterInner, transitionsAfterInner) = go(r, ste)(Cons(ste, allStates), transitions, errorState)

        val newTransitions: List[Transition[C]] = Cons(
          EpsilonTransition(ste, innerSte),
          Cons(EpsilonTransition(ste, cont), transitionsAfterInner)
        )

        ListSpecs.subseqContains(Cons(ste, allStates), statesAfterInner, cont)
        ListSpecs.subseqContains(Cons(ste, allStates), statesAfterInner, ste)

        ListUtils.lemmaTailIsSubseqOfList(ste, allStates)
        ListUtils.lemmaSubSeqTransitive(allStates, Cons(ste, allStates), statesAfterInner)

        (ste, statesAfterInner, newTransitions)
      }
    }

  } ensuring (res =>
    ListOps.noDuplicate(res._2)
      && ListSpecs.subseq(allStates, res._2)
      && res._2.contains(cont)
      && res._2.contains(res._1)
      && res._2.contains(errorState)
      && transitionsStates(res._3).forall(s => res._2.contains(s))
      && noTransitionOutOfErrorState(res._3, errorState)
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
  @inlineOnce
  @opaque
  def lemmaSameTransitionsContentOutOfErrorStatePreserved[C](transitions: List[Transition[C]], transitionsBis: List[Transition[C]], errorState: State): Unit = {
    require(transitionsBis.content.subsetOf(transitions.content))
    require(noTransitionOutOfErrorState(transitions, errorState))

    transitionsBis match {
      case Cons(hd, tl) =>
        hd match {
          case EpsilonTransition(from, to) => {
            assert(transitions.contains(hd))
            if (from == errorState) {
              lemmaNoTrOutOfErrorStateThenNotContains(transitions, errorState, hd)
              check(false)
            }
            lemmaSameTransitionsContentOutOfErrorStatePreserved(transitions, tl, errorState)
          }
          case LabeledTransition(from, _, to) => {
            assert(transitions.contains(hd))
            if (from == errorState) {
              lemmaNoTrOutOfErrorStateThenNotContains(transitions, errorState, hd)
              check(false)
            }
            lemmaSameTransitionsContentOutOfErrorStatePreserved(transitions, tl, errorState)
          }
        }
      case Nil() => ()
    }

  } ensuring (noTransitionOutOfErrorState(transitionsBis, errorState))

  @inlineOnce
  @opaque
  def lemmaNoTrOutOfErrorStateThenNotContains[C](transitions: List[Transition[C]], errorState: State, t: Transition[C]): Unit = {
    require(noTransitionOutOfErrorState(transitions, errorState))
    require(transitionFromEq(t, errorState))

    transitions match {
      case Cons(hd, tl) =>
        hd match {
          case EpsilonTransition(from, to) => {
            assert(from != errorState)
            assert(hd != t)
            lemmaNoTrOutOfErrorStateThenNotContains(tl, errorState, t)
          }
          case LabeledTransition(from, _, to) => {
            assert(from != errorState)
            assert(hd != t)
            lemmaNoTrOutOfErrorStateThenNotContains(tl, errorState, t)
          }
        }
      case Nil() => ()
    }
  } ensuring (!transitions.contains(t))

  @inlineOnce
  @opaque
  def lemmaSameTransitionContentThenSameTransitionsStatesContent[C](transitions: List[Transition[C]], transitionsBis: List[Transition[C]]): Unit = {
    require(transitionsBis.content.subsetOf(transitions.content))
    transitionsBis match {
      case Cons(hd, tl) =>
        hd match {
          case EpsilonTransition(from, to) => {
            lemmaTransitionInListThenToStatesInTransitionsStates(transitions, hd)
            lemmaSameTransitionContentThenSameTransitionsStatesContent(transitions, tl)
          }
          case LabeledTransition(from, _, to) => {
            lemmaTransitionInListThenToStatesInTransitionsStates(transitions, hd)
            lemmaSameTransitionContentThenSameTransitionsStatesContent(transitions, tl)
          }
        }
      case Nil() => ()
    }

  } ensuring (transitionsStates(transitionsBis).content.subsetOf(transitionsStates(transitions).content))

  @inlineOnce
  @opaque
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

  @inlineOnce
  @opaque
  def lemmaTransitionFromPreservedAddingOther[C](
      transitions: List[Transition[C]],
      t: Transition[C],
      from: State,
      otherFrom: State
  ): Unit = {
    require(ListSpecs.noDuplicate(transitions))
    require(from != otherFrom)
    require(transitionFromEq(t, otherFrom))
    require(!transitions.contains(t))

    transitions match {
      case Nil() => ()
      case Cons(hd, tl) =>
        lemmaTransitionFromPreservedAddingOther(tl, t, from, otherFrom)
    }

  } ensuring (transitionsFrom(from, Cons(t, transitions)) == transitionsFrom(from, transitions))

  @inlineOnce
  @opaque
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

  @inlineOnce
  @opaque
  def lemmaAddNewTransitionWithOneNewStatePreservesForallStatesContained[C](
      transitions: List[Transition[C]],
      t: Transition[C],
      s1: State,
      s2: State,
      oldStates: List[State]
  ): Unit = {
    require(transitionsStates(transitions).forall(s => oldStates.contains(s)))
    require(oldStates.contains(s2))
    require(t match {
      case EpsilonTransition(from, to)    => from == s1 && to == s2
      case LabeledTransition(from, _, to) => from == s1 && to == s2
    })

    ListUtils.lemmaForallContainsAddingInSndListPreserves(
      transitionsStates(transitions),
      oldStates,
      s1
    )

  } ensuring (transitionsStates(Cons(t, transitions)).forall(s => Cons(s1, oldStates).contains(s)))

  @inlineOnce
  @opaque
  def lemmaTransitionsWithNewStateCannotBeInList[C](
      transitions: List[Transition[C]],
      states: List[State],
      newState: State,
      newT: Transition[C]
  ): Unit = {
    require(ListOps.noDuplicate(states))
    require(transitionsStates(transitions).forall(s => states.contains(s)))
    require(!states.contains(newState))
    require(newT match {
      case EpsilonTransition(from, to)    => from == newState || to == newState
      case LabeledTransition(from, _, to) => from == newState || to == newState
    })
    if (transitions.contains(newT)) {
      lemmaTransitionThenStatesInTransitionsStates(transitions, newT)
      newT match {
        case EpsilonTransition(from, to) => {
          if (newState == from) {
            assert(transitionsStates(transitions).contains(from))
            ListSpecs.subsetContained(
              transitionsStates(transitions),
              states,
              from
            )
          } else {
            assert(newState == to)
            ListSpecs.subsetContained(
              transitionsStates(transitions),
              states,
              to
            )
          }
        }
        case LabeledTransition(from, _, to) => {
          if (newState == from) {
            assert(transitionsStates(transitions).contains(from))
            ListSpecs.subsetContained(
              transitionsStates(transitions),
              states,
              from
            )
          } else {
            assert(newState == to)
            ListSpecs.subsetContained(
              transitionsStates(transitions),
              states,
              to
            )
          }
        }
      }
      check(false)
    }

  } ensuring (!transitions.contains(newT))

  @inlineOnce
  @opaque
  def lemmaTransitionFromContainsAll[C](transitions: List[Transition[C]], state: State, t: Transition[C]): Unit = {
    require(transitionFromEq(t, state))
    require(ListSpecs.noDuplicate(transitions))
    require(!transitionsFrom(state, transitions).contains(t))

    transitions match {
      case Cons(hd, tl) =>
        lemmaTransitionFromContainsAll(tl, state, t)
      case Nil() => ()
    }

  } ensuring (!transitions.contains(t))

  @inlineOnce
  @opaque
  def lemmaEpsilonTransitionFromContainsAll[C](transitions: List[Transition[C]], state: State, t: Transition[C]): Unit = {
    require(transitionFromEq(t, state))
    require(isEpsilonTransition(t))
    require(ListSpecs.noDuplicate(transitions))
    require(!epsilonTransitionsFrom(state, transitions).contains(t))

    transitions match {
      case Cons(hd, tl) =>
        lemmaEpsilonTransitionFromContainsAll(tl, state, t)
      case Nil() => ()
    }

  } ensuring (!transitions.contains(t))

  @inlineOnce
  @opaque
  def lemmaEpsilonTransitionFromContainsNoLabeled[C](transitions: List[Transition[C]], state: State, t: Transition[C]): Unit = {
    require(isLabeledTransition(t))
    require(ListSpecs.noDuplicate(transitions))

    transitions match {
      case Cons(hd, tl) =>
        lemmaEpsilonTransitionFromContainsNoLabeled(tl, state, t)
      case Nil() => ()
    }

  } ensuring (!epsilonTransitionsFrom(state, transitions).contains(t))

  @inlineOnce
  @opaque
  def lemmaLabeledTransitionFromContainsAll[C](transitions: List[Transition[C]], state: State, t: Transition[C]): Unit = {
    require(transitionFromEq(t, state))
    require(isLabeledTransition(t))
    require(ListSpecs.noDuplicate(transitions))
    require(!labeledTransitionsFrom(state, transitions).contains(t))

    transitions match {
      case Cons(hd, tl) =>
        lemmaLabeledTransitionFromContainsAll(tl, state, t)
      case Nil() => ()
    }

  } ensuring (!transitions.contains(t))

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

  def epsilonClosure[C](nfa: NFA[C], toExplore: List[State], seen: List[State]): List[State] = {
    require(validNFA(nfa))
    require(toExplore.forall(s => nfa.allStates.contains(s)))
    require(seen.forall(s => nfa.allStates.contains(s)))
    require(ListOps.noDuplicate(seen))
    require(ListOps.noDuplicate(toExplore))
    require(ListOps.noDuplicate(toExplore ++ seen))
    decreases({
      lemmaForallContainsAndNoDuplicateThenSmallerList(nfa.allStates, seen)
      lemmaForallContainsAndNoDuplicateThenSmallerList(nfa.allStates, toExplore)
      (nfa.allStates.size - seen.size) * nfa.allStates.size + toExplore.size
    })

    toExplore match {
      case Nil() => seen
      case Cons(hd, tl) => {
        if (seen.contains(hd)) {
          epsilonClosure(nfa, tl, seen)
        } else {
          ListUtils.lemmaTailIsSubseqOfListBis(epsilonTransitionsFrom(hd, nfa.transitions))
          ListUtils.lemmaForallContainsConcatPreserves(toExplore, seen, nfa.allStates)
          val reachableFromHd: List[State] = unseenReachableStatesThroughEpsilon(nfa.transitions, epsilonTransitionsFrom(hd, nfa.transitions), hd, toExplore ++ seen, toExplore, nfa.allStates)
          val newToExplore = tl ++ reachableFromHd
          val newSeen = Cons(hd, seen)

          ListUtils.lemmaForallNotContainsForSubseq(reachableFromHd, toExplore, seen)
          assert(toExplore == List(hd) ++ tl) // it helps Stainless
          ListUtils.lemmaForallNotContainsForSubseq(reachableFromHd, List(hd), tl)
          ListUtils.noDuplicateConcatListNotContainedPreserves(tl, reachableFromHd)
          ListUtils.lemmaNoDuplicatePreservedSameContent(reachableFromHd ++ tl, tl ++ reachableFromHd)

          ListUtils.lemmaForallContainsConcatPreserves(tl, reachableFromHd, nfa.allStates)

          ListUtils.lemmaForallNotContainsCannotContain(reachableFromHd, toExplore, hd)
          ListUtils.lemmaNoDuplicateConcatThenForallNotContains(toExplore, seen)
          assert(tl.forall(s => !seen.contains(s)))
          assert(reachableFromHd.forall(s => !seen.contains(s)))
          ListUtils.lemmaForallNotContainsForConcat(tl, reachableFromHd, seen)
          assert(newToExplore.forall(s => !seen.contains(s)))
          ListUtils.lemmaForallNotContainsPreservedAddNewElmtInRefList(newToExplore, seen, hd)
          assert(newToExplore.forall(s => !newSeen.contains(s)))
          assert(ListSpecs.noDuplicate(newToExplore))
          assert(ListSpecs.noDuplicate(newSeen))
          ListUtils.lemmaForallNotContainedNoDupThenConcatNoDup(newToExplore, newSeen)
          assert(ListOps.noDuplicate(newToExplore ++ newSeen))

          epsilonClosure(nfa, newToExplore, newSeen)
        }
      }
    }

  } ensuring (res => ListOps.noDuplicate(res) && res.forall(s => nfa.allStates.contains(s)))

  def unseenReachableStatesThroughEpsilon[C](
      allTransitions: List[Transition[C]],
      transitions: List[Transition[C]],
      state: State,
      seen: List[State],
      toExplore: List[State],
      allStates: List[State]
  ): List[State] = {
    require(ListOps.noDuplicate(seen))
    require(ListOps.noDuplicate(toExplore))
    require(ListOps.noDuplicate(transitions))
    require(ListOps.noDuplicate(allTransitions))
    require(ListSpecs.subseq(transitions, epsilonTransitionsFrom(state, allTransitions)))
    require(toExplore.forall(s => allStates.contains(s)))
    require(seen.forall(s => allStates.contains(s)))
    require(transitionsStates(allTransitions).forall(s => allStates.contains(s)))

    transitions match {
      case Nil() => Nil()
      case Cons(hd, tl) =>
        ListUtils.lemmaTailIsSubseqOfList(hd, tl)
        ListUtils.lemmaSubSeqTransitive(tl, transitions, epsilonTransitionsFrom(state, allTransitions))
        hd match {
          case EpsilonTransition(from, to) => {
            ListSpecs.subseqContains(transitions, epsilonTransitionsFrom(state, allTransitions), hd)
            ListSpecs.forallContained(epsilonTransitionsFrom(state, allTransitions), t => transitionFromEq(t, state), hd)
            if (!seen.contains(to) && !toExplore.contains(to)) {
              // LEMMAS ---------------------------------------------------------------------------------------------------------------------
              ListUtils.lemmaSubSeqTransitive(transitions, epsilonTransitionsFrom(state, allTransitions), allTransitions)
              ListSpecs.subseqContains(transitions, allTransitions, hd)
              lemmaTransitionInListThenToStatesInTransitionsStates(allTransitions, hd)
              ListSpecs.forallContained(transitionsStates(allTransitions), s => allStates.contains(s), to)
              ListUtils.lemmaForallContainsAddingElmtInPreserves(unseenReachableStatesThroughEpsilon(allTransitions, tl, state, seen, toExplore, allStates), allStates, to)
              lemmaForallContainsTransitionToPreservedAddingInRef(unseenReachableStatesThroughEpsilon(allTransitions, tl, state, seen, toExplore, allStates), tl, hd, state)
              if (unseenReachableStatesThroughEpsilon(allTransitions, tl, state, seen, toExplore, allStates).contains(to)) {
                ListSpecs.forallContained(unseenReachableStatesThroughEpsilon(allTransitions, tl, state, seen, toExplore, allStates), s => tl.contains(EpsilonTransition(state, s)), to)
                check(false)
              }
              // LEMMAS ---------------------------------------------------------------------------------------------------------------------

              Cons(to, unseenReachableStatesThroughEpsilon(allTransitions, tl, state, seen, toExplore, allStates))
            } else {
              // LEMMAS ---------------------------------------------------------------------------------------------------------------------
              lemmaForallContainsTransitionToPreservedAddingInRef(unseenReachableStatesThroughEpsilon(allTransitions, tl, state, seen, toExplore, allStates), tl, hd, state)
              // LEMMAS ---------------------------------------------------------------------------------------------------------------------

              unseenReachableStatesThroughEpsilon(allTransitions, tl, state, seen, toExplore, allStates)
            }
          }
          case LabeledTransition(from, c, to) => {
            assert(transitions.contains(hd))
            ListSpecs.subseqContains(transitions, epsilonTransitionsFrom(state, allTransitions), hd)
            lemmaEpsilonTransitionFromContainsNoLabeled(allTransitions, state, hd)
            check(false)
            Nil()
          }
        }
    }
  } ensuring (res =>
    ListSpecs.noDuplicate(res) &&
      res.forall(s => allStates.contains(s)) &&
      res.forall(s => transitions.contains(EpsilonTransition(state, s))) &&
      res.forall(s => !seen.contains(s))
  )

  @inlineOnce
  @opaque
  def lemmaForallContainsTransitionToPreservedAddingInRef[C](l: List[State], lRef: List[Transition[C]], t: Transition[C], state: State): Unit = {
    require(l.forall(s => lRef.contains(EpsilonTransition(state, s))))
    l match {
      case Nil() => ()
      case Cons(hd, tl) => {
        lemmaForallContainsTransitionToPreservedAddingInRef(tl, lRef, t, state)
      }
    }
  } ensuring (l.forall(s => Cons(t, lRef).contains(EpsilonTransition(state, s))))

  def epsilonClosureFromOneState[C](
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
      (nfa.allStates.size - seen.size) * nfa.transitions.size + transitionsRec.size
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
                epsilonClosureFromOneState(nfa, to, nfa.transitions, newSeen)
              } else {
                epsilonClosureFromOneState(nfa, startState, tl, seen)
              }
            }
            case LabeledTransition(from, c, to) => {
              epsilonClosureFromOneState(nfa, startState, tl, seen)
            }
          }
        }
      }
    }
  } ensuring (res => ListOps.noDuplicate(res) && res.forall(s => nfa.allStates.contains(s)))

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
