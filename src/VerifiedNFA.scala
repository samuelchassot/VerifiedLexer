/** Author: Samuel Chassot
  */

/** Command to verify the whole project stainless-dotty VerifiedRegexMatcher.scala ListUtils.scala VerifiedNFA.scala -Dparallel=3 --config-file=stainless.conf --watch
  */

import stainless.collection._
import stainless.annotation._
import stainless.lang._
import stainless.proof._
import VerifiedNFA.LabeledTransition

object VerifiedNFA {
  import RegularExpression._
  case class State(label: String) {
    require(label != "")
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

  def isEpsilonTransition[C](t: Transition[C]): Boolean = t match {
    case EpsilonTransition(_, _) => true
    case _                       => false
  }

  def isLabeledTransition[C](t: Transition[C]): Boolean = t match {
    case LabeledTransition(_, _, _) => true
    case _                          => false
  }

  def transitionsFrom[C](
      state: State,
      transitions: List[Transition[C]]
  ): List[Transition[C]] = {
    require(ListSpecs.noDuplicate(transitions))
    decreases(transitions.size)
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
    decreases(transitions.size)
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

  def transitionFromEq[C](t: Transition[C], s: State): Boolean = t match {
    case EpsilonTransition(from, _)    => from == s
    case LabeledTransition(from, _, _) => from == s
  }
  def transitionToEq[C](t: Transition[C], s: State): Boolean = t match {
    case EpsilonTransition(_, to)    => to == s
    case LabeledTransition(_, _, to) => to == s
  }

  def labelEq[C](t: Transition[C], c: C): Boolean = {
    require(isLabeledTransition(t))
    t match {
      case LabeledTransition(_, cc, _) => cc == c
    }
  }

  def noEpsilonTransitionTo[C](transitions: List[Transition[C]], to: State): Boolean = {
    decreases(transitions.size)
    transitions match {
      case Cons(hd, tl) => {
        hd match {
          case EpsilonTransition(_, too) => too != to && noEpsilonTransitionTo(tl, to)
          case _                         => noEpsilonTransitionTo(tl, to)
        }
      }
      case Nil() => true
    }
  }

  
  
  def lemmaNoEpsilonTransitionToThenNoneInEpsilonTransitionsFrom[C](transitions: List[Transition[C]], to: State, from: State): Unit = {
    require(ListSpecs.noDuplicate(transitions))
    require(noEpsilonTransitionTo(transitions, to))
    decreases(transitions.size)

    transitions match {
      case Cons(hd, tl) =>
        hd match {
          case EpsilonTransition(fromm, too) if fromm == from => {
            ListSpecs.noDuplicateSubseq(Cons(hd, epsilonTransitionsFrom(from, tl)), transitions)
            lemmaNoEpsilonTransitionToThenNoneInEpsilonTransitionsFrom(tl, to, from)
          }
          case _ => {
            lemmaNoEpsilonTransitionToThenNoneInEpsilonTransitionsFrom(tl, to, from)
          }
        }
      case Nil() => ()
    }
  } ensuring (epsilonTransitionsFrom(from, transitions).forall(t => !transitionToEq(t, to)))

  
  
  def lemmaNoTransitionsOutOfErrorStateThenNotContained[C](@induct transitions: List[Transition[C]], t: Transition[C], errorState: State): Unit = {
    require(noTransitionOutOfErrorState(transitions, errorState))
    require(transitionFromEq(t, errorState))

  } ensuring (!transitions.contains(t))

  // Adapted from Romain's version
  def fromRegexToNfa[C](r: Regex[C]): NFA[C] = {
    val errorState = getFreshState(Nil())
    val states = List(errorState)
    val (startState, allStates, transitions, finalState) =
      go(r)(states, Nil(), errorState)
    // lemmaGoTransitionsNoDuplicate(r, finalState, states, Nil(), errorState)
    lemmaSameTransitionContentThenSameTransitionsStatesContent(transitions, ListUtils.removeDuplicates(transitions, transitions))
    ListUtils.lemmaForallContainsPreservedIfSameContent(transitionsStates(transitions), transitionsStates(ListUtils.removeDuplicates(transitions, transitions)), allStates)

    lemmaSameTransitionsContentOutOfErrorStatePreserved(transitions, ListUtils.removeDuplicates(transitions, transitions), errorState)
    assert(noTransitionOutOfErrorState(ListUtils.removeDuplicates(transitions, transitions), errorState))

    NFA(startState, List(finalState), errorState, ListUtils.removeDuplicates(transitions, transitions), allStates)
  } ensuring (res => validNFA(res))

  /** Returns the Start State, the list of allStates, the list of Transitions and the Final State Start state and final state are fresh or error State
    *
    * Cannot be inlined
    *
    * @param regex
    * @param errorState
    * @return
    */
  def go[C](regex: Regex[C])(errorState: State): (State, List[State], List[Transition[C]], State) = {
    decreases(regexDepth(regex))

    regex match {
      case EmptyLang() => {
        val stout = State("out")
        val ste = errorState
        val newAllStates = Cons(stout, Nil())
        // ListUtils.lemmaTailIsSubseqOfList(ste, allStates)
        // ListUtils.lemmaForallContainsAddingInSndListPreserves(transitionsStates(transitions), allStates, stout)

        (errorState, newAllStates, transitions, stout)
      }
      case EmptyExpr() => {
        // ListUtils.lemmaSubseqRefl(allStates)
        val ste = State("start")
        val stout = State("out")
        val newAllStates = Cons(stout, Cons(ste, Nil()))
        val newTransitions = Cons(EpsilonTransition(ste, stout), Nil())

        // ListUtils.lemmaTailIsSubseqOfList(ste, allStates)
        // ListUtils.lemmaTailIsSubseqOfList(stout, Cons(ste, allStates))
        // ListUtils.lemmaTailIsSubseqOfBiggerList(Cons(ste, allStates), newAllStates)

        // lemmaTransitionsWithNewStateCannotBeInList(transitions, allStates, ste, EpsilonTransition(ste, stout))

        // lemmaAddNewTransitionPreservesForallStatesContainedIfAddingStates(transitions, EpsilonTransition(ste, stout), ste, stout, allStates)

        (ste, newAllStates, newTransitions, stout)
      }
      case ElementMatch(c) => {
        val ste = State("start")
        val stout = State("out")
        val newAllStates = Cons(stout, Cons(ste, Nil()))
        val newTransition = LabeledTransition(ste, c, stout)
        val newTransitions = Cons(newTransition, Nil())
        // ListUtils.lemmaTailIsSubseqOfList(ste, allStates)
        // ListUtils.lemmaTailIsSubseqOfList(stout, Cons(ste, allStates))
        // ListUtils.lemmaTailIsSubseqOfBiggerList(Cons(ste, allStates), newAllStates)

        // ListUtils.lemmaTailIsSubseqOfList(ste, allStates)

        // lemmaTransitionsWithNewStateCannotBeInList(transitions, allStates, ste, newTransition)

        // lemmaAddNewTransitionPreservesForallStatesContainedIfAddingStates(transitions, newTransition, ste, stout, allStates)

        (ste, newAllStates, newTransitions, stout)

      }
      case Union(r1, r2) => {
        val (ste1, states1, transitions1, stout1) =
          go(r1)(errorState)

        // ListSpecs.subseqContains(allStates, statesAfter1, errorState)

        assert(regexDepth(r2) < regexDepth(Union(r1, r2)))

        val (ste2, states2, transitions2, stout2) = go(r2)(errorState)

        val stout = State("out")
        val ste = State("start")
        val newStates = Cons(ste, Cons(stout, combineStates(states1, states2, "l", "r")))
        val renamedSte1 = renameState(ste1, "l")
        val renamedSte2 = renameState(ste2, "r")
        val renamedStout1 = renameState(stout1, "l")
        val renamedStout2 = renameState(stout2, "r")

        val t1 = EpsilonTransition[C](ste, renamedSte1)
        val t2 = EpsilonTransition[C](ste, renamedSte2)
        val t3 = EpsilonTransition[C](renamedStout1, stout)
        val t4 = EpsilonTransition[C](renamedStout2, stout)
        val newTransitions: List[Transition[C]] = Cons(t1, Cons(t2, Cons(t3, Cons(t4, combineTransitions(transitions1, transitions2, "l", "r")))))

        // LEMMAS --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

        // ListUtils.lemmaSubSeqTransitive(allStates, statesAfter1, statesAfter2)
        // ListUtils.lemmaTailIsSubseqOfList(stout, statesAfter2)
        // ListUtils.lemmaTailIsSubseqOfListBis(newAllStates)
        // ListUtils.lemmaSubSeqTransitive(statesAfter2, Cons(stout, statesAfter2), newAllStates)
        // ListUtils.lemmaSubSeqTransitive(allStates, statesAfter2, newAllStates)

        // ListSpecs.subseqContains(statesAfter1, statesAfter2, ste1)
        // ListSpecs.subseqContains(statesAfter1, statesAfter2, stout1)
        // ListSpecs.subseqContains(statesAfter2, Cons(stout, statesAfter2), ste1)
        // ListSpecs.subseqContains(statesAfter2, Cons(stout, statesAfter2), stout1)
        // ListSpecs.subseqContains(statesAfter2, Cons(stout, statesAfter2), ste2)
        // ListSpecs.subseqContains(statesAfter2, Cons(stout, statesAfter2), stout2)
        // ListSpecs.subseqContains(statesAfter2, Cons(stout, statesAfter2), errorState)
        // ListSpecs.subseqContains(Cons(stout, statesAfter2), newAllStates, stout)
        // ListSpecs.subseqContains(Cons(stout, statesAfter2), newAllStates, ste1)
        // ListSpecs.subseqContains(Cons(stout, statesAfter2), newAllStates, stout1)
        // ListSpecs.subseqContains(Cons(stout, statesAfter2), newAllStates, ste2)
        // ListSpecs.subseqContains(Cons(stout, statesAfter2), newAllStates, stout2)
        // ListSpecs.subseqContains(Cons(stout, statesAfter2), newAllStates, errorState)

        // ListUtils.notContainsAThenTailNotContains(Cons(stout, statesAfter2), ste)

        // lemmaAddTransitionNotFromErrorStatePreserves(transitionsAfter2, t4, errorState)
        // lemmaAddTransitionNotFromErrorStatePreserves(Cons(t4, transitionsAfter2), t3, errorState)
        // lemmaAddTransitionNotFromErrorStatePreserves(Cons(t3, Cons(t4, transitionsAfter2)), t2, errorState)
        // lemmaAddTransitionNotFromErrorStatePreserves(Cons(t2, Cons(t3, Cons(t4, transitionsAfter2))), t1, errorState)

        // ListUtils.lemmaForallContainsAddingInSndListPreserves(transitionsStates(transitionsAfter2), statesAfter2, stout)
        // ListUtils.lemmaForallContainsAddingInSndListPreserves(transitionsStates(transitionsAfter2), Cons(stout, statesAfter2), ste)

        // lemmaAddNewTransitionPreservesForallStatesContainedIfAddingStates(transitionsAfter2, t4, stout2, stout, statesAfter2)
        // lemmaAddNewTransitionPreservesForallStatesContainedIfAddingStates(Cons(t4, transitionsAfter2), t3, stout1, stout, Cons(stout, statesAfter2))
        // lemmaAddNewTransitionPreservesForallStatesContainedIfAddingStates(Cons(t3, Cons(t4, transitionsAfter2)), t2, ste, ste2, Cons(stout, statesAfter2))

        // lemmaAddNewTransitionPreservesForallStatesContainedIfAddingStates(Cons(t2, Cons(t3, Cons(t4, transitionsAfter2))), t1, ste, ste1, Cons(ste, Cons(stout, statesAfter2)))

        // LEMMAS --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

        (ste, newAllStates, newTransitions, stout)

      }
      case Concat(r1, r2) => {
        val (ste1, states1, transitions1, stout1) = go(r1)(errorState)
        // ListSpecs.subseqContains(allStates, statesAfter1, errorState)
        val (ste2, states2, transitions2, stout2) = go(r2)(errorState)

        // ListUtils.lemmaSubSeqTransitive(allStates, statesAfter1, statesAfter2)

        val stout = State("out")
        val ste = State("start")
        val newStates = Cons(ste, Cons(stout, combineStates(states1, states2, "l", "r")))

        val renamedSte1 = renameState(ste1, "l")
        val renamedSte2 = renameState(ste2, "r")
        val renamedStout1 = renameState(stout1, "l")
        val renamedStout2 = renameState(stout2, "r")

        val t1 = EpsilonTransition[C](ste, renamedSte1)
        val t2 = EpsilonTransition[C](renamedStout2, stout)
        val t3 = EpsilonTransition[C](renamedStout1, renamedSte2)

        val newTransitions: List[Transition[C]] = Cons(t1, Cons(t2, Cons(t3, combineTransitions(transitions1, transitions2, "l", "r"))))

        // LEMMAS --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

        // ListUtils.lemmaSubSeqTransitive(allStates, statesAfter1, statesAfter2)
        // ListUtils.lemmaTailIsSubseqOfList(stout, statesAfter2)
        // ListUtils.lemmaTailIsSubseqOfListBis(newAllStates)
        // ListUtils.lemmaSubSeqTransitive(statesAfter2, Cons(stout, statesAfter2), newAllStates)
        // ListUtils.lemmaSubSeqTransitive(allStates, statesAfter2, newAllStates)

        // ListSpecs.subseqContains(statesAfter1, statesAfter2, ste1)
        // ListSpecs.subseqContains(statesAfter1, statesAfter2, stout1)
        // ListSpecs.subseqContains(statesAfter2, Cons(stout, statesAfter2), ste1)
        // ListSpecs.subseqContains(statesAfter2, Cons(stout, statesAfter2), stout1)
        // ListSpecs.subseqContains(statesAfter2, Cons(stout, statesAfter2), ste2)
        // ListSpecs.subseqContains(statesAfter2, Cons(stout, statesAfter2), stout2)
        // ListSpecs.subseqContains(statesAfter2, Cons(stout, statesAfter2), errorState)
        // ListSpecs.subseqContains(Cons(stout, statesAfter2), newAllStates, stout)
        // ListSpecs.subseqContains(Cons(stout, statesAfter2), newAllStates, ste1)
        // ListSpecs.subseqContains(Cons(stout, statesAfter2), newAllStates, stout1)
        // ListSpecs.subseqContains(Cons(stout, statesAfter2), newAllStates, ste2)
        // ListSpecs.subseqContains(Cons(stout, statesAfter2), newAllStates, stout2)
        // ListSpecs.subseqContains(Cons(stout, statesAfter2), newAllStates, errorState)

        // ListUtils.notContainsAThenTailNotContains(Cons(stout, statesAfter2), ste)

        // lemmaAddTransitionNotFromErrorStatePreserves(transitionsAfter2, t3, errorState)
        // lemmaAddTransitionNotFromErrorStatePreserves(Cons(t3, transitionsAfter2), t2, errorState)
        // lemmaAddTransitionNotFromErrorStatePreserves(Cons(t2, Cons(t3, transitionsAfter2)), t1, errorState)

        // lemmaAddNewTransitionPreservesForallStatesContainedIfAddingStates(transitionsAfter2, t3, stout1, ste2, statesAfter2)
        // lemmaAddNewTransitionPreservesForallStatesContainedIfAddingStates(Cons(t3, transitionsAfter2), t2, stout2, stout, statesAfter2)
        // lemmaAddNewTransitionPreservesForallStatesContainedIfAddingStates(Cons(t2, Cons(t3, transitionsAfter2)), t1, ste, ste1, Cons(stout, statesAfter2))

        // ListUtils.noDuplicateConcatNotContainedPreserves(statesAfter2, stout)
        // ListUtils.noDuplicateConcatNotContainedPreserves(Cons(stout, statesAfter2), ste)

        // LEMMAS --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

        (ste, newAllStates, newTransitions, stout)
      }
      case Star(r) => {
        val (innerSte, statesInner, transitionsInner, innerStout) = go(r)(errorState)

        val stout = getFreshState(statesAfterInner)
        val ste = getFreshState(Cons(stout, statesAfterInner))
        val newAllStates = Cons(ste, Cons(stout, renameStates(statesAfterInner, "i")))

        val renamedInnerSte = renameState(innerSte, "i")
        val renamedInnerStout = renameState(innerStout, "i")

        val t1 = EpsilonTransition[C](ste, renamedInnerSte)
        val t2 = EpsilonTransition[C](ste, stout)
        val t3 = EpsilonTransition[C](renamedInnerStout, stout)
        val t4 = EpsilonTransition[C](stout, ste)

        val newTransitions: List[Transition[C]] = Cons(t1, Cons(t2, Cons(t3, Cons(t4, renameStatesInTransitions(transitionsInner, "i")))))

        // ListUtils.lemmaTailIsSubseqOfList(stout, statesAfterInner)
        // ListUtils.lemmaTailIsSubseqOfListBis(newAllStates)
        // ListUtils.lemmaTailIsSubseqOfListBis(newAllStates)
        // ListUtils.lemmaSubSeqTransitive(statesAfterInner, Cons(stout, statesAfterInner), newAllStates)
        // ListUtils.lemmaSubSeqTransitive(allStates, statesAfterInner, newAllStates)

        // ListSpecs.subseqContains(statesAfterInner, newAllStates, innerSte)
        // ListSpecs.subseqContains(statesAfterInner, newAllStates, innerStout)
        // ListSpecs.subseqContains(statesAfterInner, newAllStates, errorState)
        // ListSpecs.subseqContains(statesAfterInner, Cons(stout, statesAfterInner), errorState)
        // ListSpecs.subseqContains(statesAfterInner, Cons(stout, statesAfterInner), innerStout)
        // ListSpecs.subseqContains(statesAfterInner, Cons(stout, statesAfterInner), innerSte)
        // ListSpecs.subseqContains(Cons(stout, statesAfterInner), newAllStates, stout)

        // ListUtils.notContainsAThenTailNotContains(Cons(stout, statesAfterInner), ste)

        // lemmaAddTransitionNotFromErrorStatePreserves(transitionsAfterInner, t4, errorState)
        // lemmaAddTransitionNotFromErrorStatePreserves(Cons(t4, transitionsAfterInner), t3, errorState)
        // lemmaAddTransitionNotFromErrorStatePreserves(Cons(t3, Cons(t4, transitionsAfterInner)), t2, errorState)
        // lemmaAddTransitionNotFromErrorStatePreserves(Cons(t2, Cons(t3, Cons(t4, transitionsAfterInner))), t1, errorState)

        // lemmaAddNewTransitionPreservesForallStatesContainedIfAddingStates(transitionsAfterInner, t4, stout, ste, statesAfterInner)
        // lemmaAddNewTransitionPreservesForallStatesContainedIfAddingStates(Cons(t4, transitionsAfterInner), t3, innerStout, stout, Cons(ste, Cons(stout, statesAfterInner)))
        // lemmaAddNewTransitionPreservesForallStatesContainedIfAddingStates(Cons(t3, Cons(t4, transitionsAfterInner)), t2, ste, stout, Cons(ste, Cons(stout, statesAfterInner)))
        // lemmaAddNewTransitionPreservesForallStatesContainedIfAddingStates(Cons(t2, Cons(t3, Cons(t4, transitionsAfterInner))), t1, ste, innerSte, Cons(ste, Cons(stout, statesAfterInner)))

        (ste, newAllStates, newTransitions, stout)
      }
    }

  } ensuring (res =>
    ListSpecs.noDuplicate(res._2)
      && ListSpecs.subseq(allStates, res._2)
      && res._2.contains(res._1)
      && res._2.contains(errorState)
      && res._2.contains(res._4)
      && transitionsStates(res._3).forall(s => res._2.contains(s))
      && noTransitionOutOfErrorState(res._3, errorState)
      && res._4 != errorState
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
  
  def lemmaAddTransitionNotFromErrorStatePreserves[C](@induct transitions: List[Transition[C]], t: Transition[C], errorState: State): Unit = {
    require(!transitionFromEq(t, errorState))
    require(noTransitionOutOfErrorState(transitions, errorState))

  } ensuring (noTransitionOutOfErrorState(Cons(t, transitions), errorState))
  
  
  def lemmaSameTransitionsContentOutOfErrorStatePreserved[C](transitions: List[Transition[C]], transitionsBis: List[Transition[C]], errorState: State): Unit = {
    require(transitionsBis.content.subsetOf(transitions.content))
    require(noTransitionOutOfErrorState(transitions, errorState))
    decreases(transitionsBis.size)

    transitionsBis match {
      case Cons(hd, tl) =>
        hd match {
          case EpsilonTransition(from, to) => {
            assert(transitions.contains(hd))
            if (from == errorState) {
              lemmaNoTransitionsOutOfErrorStateThenNotContained(transitions, hd, errorState)
              check(false)
            }
            lemmaSameTransitionsContentOutOfErrorStatePreserved(transitions, tl, errorState)
          }
          case LabeledTransition(from, _, to) => {
            assert(transitions.contains(hd))
            if (from == errorState) {
              lemmaNoTransitionsOutOfErrorStateThenNotContained(transitions, hd, errorState)
              check(false)
            }
            lemmaSameTransitionsContentOutOfErrorStatePreserved(transitions, tl, errorState)
          }
        }
      case Nil() => ()
    }

  } ensuring (noTransitionOutOfErrorState(transitionsBis, errorState))

  
  
  def lemmaSameTransitionContentThenSameTransitionsStatesContent[C](transitions: List[Transition[C]], transitionsBis: List[Transition[C]]): Unit = {
    require(transitionsBis.content.subsetOf(transitions.content))
    decreases(transitionsBis)
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

  
  
  def lemmaTransitionInListThenToStatesInTransitionsStates[C](
      l: List[Transition[C]],
      t: Transition[C]
  ): Unit = {
    require(l.contains(t))
    decreases(l)
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

  
  
  def lemmaTransitionThenStatesInTransitionsStates[C](
      transitions: List[Transition[C]],
      t: Transition[C]
  ): Unit = {
    require(transitions.contains(t))
    decreases(transitions)
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

  
  
  def lemmaAddNewTransitionPreservesForallStatesContainedIfAddingStates[C](
      transitions: List[Transition[C]],
      t: Transition[C],
      s1: State,
      s2: State,
      oldStates: List[State]
  ): Unit = {
    require(transitionsStates(transitions).forall(s => oldStates.contains(s)))
    require(t match {
      case EpsilonTransition(from, to)    => from == s1 && to == s2
      case LabeledTransition(from, _, to) => from == s1 && to == s2
    })

    if (oldStates.contains(s1) && oldStates.contains(s2)) {
      ()
    }
    if (oldStates.contains(s1) && !oldStates.contains(s2)) {
      ListUtils.lemmaForallContainsAddingInSndListPreserves(
        transitionsStates(transitions),
        oldStates,
        s2
      )
    }
    if (oldStates.contains(s2) && !oldStates.contains(s1)) {
      ListUtils.lemmaForallContainsAddingInSndListPreserves(
        transitionsStates(transitions),
        oldStates,
        s1
      )
    }
    if (!oldStates.contains(s1) && !oldStates.contains(s2)) {
      ListUtils.lemmaForallContainsAddingInSndListPreserves(
        transitionsStates(transitions),
        oldStates,
        s1
      )
      ListUtils.lemmaForallContainsAddingInSndListPreserves(
        transitionsStates(transitions),
        Cons(s1, oldStates),
        s2
      )
    }

  } ensuring ({
    oldStates.contains(s1) && oldStates.contains(s2) && transitionsStates(Cons(t, transitions)).forall(s => oldStates.contains(s)) ||
    oldStates.contains(s1) && !oldStates.contains(s2) && transitionsStates(Cons(t, transitions)).forall(s => Cons(s2, oldStates).contains(s)) ||
    oldStates.contains(s2) && !oldStates.contains(s1) && transitionsStates(Cons(t, transitions)).forall(s => Cons(s1, oldStates).contains(s)) ||
    !oldStates.contains(s1) && !oldStates.contains(s2) && transitionsStates(Cons(t, transitions)).forall(s => Cons(s2, Cons(s1, oldStates)).contains(s))
  })

  
  
  def lemmaTransitionsWithNewStateCannotBeInList[C](
      transitions: List[Transition[C]],
      states: List[State],
      newState: State,
      newT: Transition[C]
  ): Unit = {
    require(ListSpecs.noDuplicate(states))
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

  
  
  def lemmaTransitionFromContainsAll[C](transitions: List[Transition[C]], state: State, t: Transition[C]): Unit = {
    require(transitionFromEq(t, state))
    require(ListSpecs.noDuplicate(transitions))
    require(!transitionsFrom(state, transitions).contains(t))
    decreases(transitions.size)

    transitions match {
      case Cons(hd, tl) =>
        lemmaTransitionFromContainsAll(tl, state, t)
      case Nil() => ()
    }

  } ensuring (!transitions.contains(t))

  
  
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

  
  
  def lemmaEpsilonTransitionFromEmptyIfNoEpsilonTrInList[C](transitions: List[Transition[C]], state: State): Unit = {
    require(ListSpecs.noDuplicate(transitions))
    require(transitions.forall(t => !isEpsilonTransition(t)))
    decreases(transitions.size)

    transitions match {
      case Cons(hd, tl) =>
        lemmaEpsilonTransitionFromEmptyIfNoEpsilonTrInList(tl, state)
      case Nil() => ()
    }

  } ensuring (epsilonTransitionsFrom(state, transitions).isEmpty)

  
  
  def lemmaEpsilonTransitionFromContainsNoLabeled[C](@induct transitions: List[Transition[C]], state: State, t: Transition[C]): Unit = {
    require(isLabeledTransition(t))
    require(ListSpecs.noDuplicate(transitions))

  } ensuring (!epsilonTransitionsFrom(state, transitions).contains(t))

  
  
  def lemmaLabeledTransitionFromContainsAll[C](transitions: List[Transition[C]], state: State, t: Transition[C]): Unit = {
    require(transitionFromEq(t, state))
    require(isLabeledTransition(t))
    require(ListSpecs.noDuplicate(transitions))
    require(!labeledTransitionsFrom(state, transitions).contains(t))
    decreases(transitions.size)

    transitions match {
      case Cons(hd, tl) =>
        lemmaLabeledTransitionFromContainsAll(tl, state, t)
      case Nil() => ()
    }

  } ensuring (!transitions.contains(t))

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

  // Helper functions ---------------------------------------------------------------------------------------------------------------------------------------------
  def combineStates(states1: List[State], states2: List[State], prefix1: String, prefix2: String): List[State] = {
    require(ListSpecs.noDuplicate(states1))
    require(ListSpecs.noDuplicate(states2))
    require(prefix1 != prefix2)

    renameStates(states1, prefix1) ++ renameStates(states2, prefix2)
    // TODO proof

  } ensuring (res => ListSpecs.noDuplicate(res))

  def renameStates(states: List[State], prefix: String): List[State] = {
    states match {
      case Cons(hd, tl) => {
        val newHd = renameState(hd, prefix)
        Cons(newHd, renameStates(tl, prefix))
      }
      case Nil() => Nil()
    }
  } ensuring(res => res.forall(s => s.label.startsWith(prefix)))

def renameState(s: State, prefix: String): State = {
  State(prefix + s.label)
} ensuring (res => res.label.startsWith(prefix))

def combineTransitions[C](trs1: List[Transition[C]], trs2: List[Transition[C]], prefix1: String, prefix2: String): List[Transition[C]] = {
  require(ListSpecs.noDuplicate(trs1))
  require(ListSpecs.noDuplicate(trs2))
  require(prefix1 != prefix2)

  renameStatesInTransitions(trs1, prefix1) ++ renameStatesInTransitions(trs2, prefix2)
  // TODO proof

} ensuring (res => ListSpecs.noDuplicate(res)

def renameStatesInTransitions[C](trs: List[Transition[C]], prefix: String): List[Transition[C]] = {
  trs match {
    case Cons(hd, tl) => {
      hd match {
        case EpsilonTransition(from, to) => {
          val newFrom = State(prefix + from.label)
          val newTo = State(prefix + to.label)
          Cons(EpsilonTransition(newFrom, newTo), renameStatesInTransitions(tl, prefix))
        }
        case LabeledTransition(from, c, to) => {
          val newFrom = State(prefix + from.label)
          val newTo = State(prefix + to.label)
          Cons(LabeledTransition(newFrom, c, newTo), renameStatesInTransitions(tl, prefix))
        }
      }
    }
    case Nil() => Nil()
  }
}
}

// ----------------------------------------------------------------------------------------------------------------------------------------------------------------

object VerifiedNFAMatcher {
  import VerifiedNFA._
  import VerifiedRegexMatcher._
  import RegularExpression._
  import ListUtils._

  def matchNFA[C](nfa: NFA[C], input: List[C]): Boolean = {
    require(validNFA(nfa))
    matchNFAInner(nfa, input, List(nfa.startState), Nil(), input)
  }

  def matchNFAInner[C](nfa: NFA[C], input: List[C], currentStates: List[State], pastChars: List[C], suffix: List[C]): Boolean = {
    require(input == pastChars ++ suffix)
    require(validNFA(nfa))
    require(currentStates.forall(s => nfa.allStates.contains(s)))
    require(ListSpecs.noDuplicate(currentStates))
    decreases(suffix.size)

    val currentStatesEpsilonClosure = epsilonClosure(nfa, currentStates, Nil())
    if (suffix.isEmpty) {
      !currentStatesEpsilonClosure.filter(s => nfa.finalStates.contains(s)).isEmpty
    } else {
      ListUtils.lemmaSubseqRefl(nfa.transitions)

      val nextChar = suffix.head
      val newPastChars = pastChars ++ List(nextChar)
      val newSuffix = suffix.tail
      val afterConsumingNextChar = readOneChar(nfa, nfa.transitions, currentStatesEpsilonClosure, nextChar)

      assert(afterConsumingNextChar.forall(s => nfa.allStates.contains(s)))

      val afterEpsilon = epsilonClosure(nfa, afterConsumingNextChar)

      ListUtils.lemmaTwoListsConcatAssociativity(pastChars, List(nextChar), newSuffix)
      matchNFAInner(nfa, input, afterEpsilon, newPastChars, newSuffix)
    }

  }

  def epsilonClosure[C](nfa: NFA[C], toExplore: List[State], seen: List[State] = Nil()): List[State] = {
    require(validNFA(nfa))
    require(toExplore.forall(s => nfa.allStates.contains(s)))
    require(seen.forall(s => nfa.allStates.contains(s)))
    require(ListSpecs.noDuplicate(seen))
    require(ListSpecs.noDuplicate(toExplore))
    require(ListSpecs.noDuplicate(toExplore ++ seen))
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
          val seenArg = toExplore ++ seen
          val reachableFromHd: List[State] = unseenReachableStatesThroughEpsilon(nfa.transitions, epsilonTransitionsFrom(hd, nfa.transitions), hd, seenArg, nfa.allStates)
          val newToExplore = tl ++ reachableFromHd
          val newSeen = Cons(hd, seen)

          // LEMMAS ------------------------------------------------------------------------------------------------------------------------
          ListUtils.lemmaForallNotContainsForConcat(reachableFromHd, seenArg, toExplore, seen)
          check(reachableFromHd.forall(s => !(toExplore ++ seen).contains(s)))
          ListUtils.lemmaForallNotContainsForSubseq(reachableFromHd, toExplore, seen)
          
          assert(toExplore == List(hd) ++ tl) // it helps Stainless
          ListUtils.lemmaForallNotContainsForConcat(reachableFromHd, toExplore, List(hd), tl)
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
          assert(ListSpecs.noDuplicate(newToExplore ++ newSeen))

          // LEMMAS ------------------------------------------------------------------------------------------------------------------------

          epsilonClosure(nfa, newToExplore, newSeen)
        }
      }
    }

  } ensuring (res => ListSpecs.noDuplicate(res) && res.forall(s => nfa.allStates.contains(s)))

  def unseenReachableStatesThroughEpsilon[C](
      allTransitions: List[Transition[C]],
      transitions: List[Transition[C]],
      state: State,
      seen: List[State],
      // toExplore: List[State],
      allStates: List[State]
  ): List[State] = {
    require(ListSpecs.noDuplicate(seen))
    // require(ListSpecs.noDuplicate(toExplore))
    require(ListSpecs.noDuplicate(transitions))
    require(ListSpecs.noDuplicate(allTransitions))
    require(ListSpecs.subseq(transitions, epsilonTransitionsFrom(state, allTransitions)))
    // require(toExplore.forall(s => allStates.contains(s)))
    require(seen.forall(s => allStates.contains(s)))
    require(transitionsStates(allTransitions).forall(s => allStates.contains(s)))
    decreases(transitions)

    transitions match {
      case Nil() => Nil()
      case Cons(hd, tl) =>
        ListUtils.lemmaTailIsSubseqOfBiggerList(transitions, epsilonTransitionsFrom(state, allTransitions))
        hd match {
          case EpsilonTransition(from, to) => {
            ListSpecs.subseqContains(transitions, epsilonTransitionsFrom(state, allTransitions), hd)
            ListSpecs.forallContained(epsilonTransitionsFrom(state, allTransitions), t => transitionFromEq(t, state), hd)
            if (!seen.contains(to)) { // && !toExplore.contains(to)) {
              // LEMMAS ---------------------------------------------------------------------------------------------------------------------
              ListUtils.lemmaSubSeqTransitive(transitions, epsilonTransitionsFrom(state, allTransitions), allTransitions)
              ListSpecs.subseqContains(transitions, allTransitions, hd)
              lemmaTransitionInListThenToStatesInTransitionsStates(allTransitions, hd)
              ListSpecs.forallContained(transitionsStates(allTransitions), s => allStates.contains(s), to)
              ListUtils.lemmaForallContainsAddingElmtInPreserves(unseenReachableStatesThroughEpsilon(allTransitions, tl, state, seen, allStates), allStates, to)
              lemmaForallContainsTransitionToPreservedAddingInRef(unseenReachableStatesThroughEpsilon(allTransitions, tl, state, seen, allStates), tl, hd, state)
              if (unseenReachableStatesThroughEpsilon(allTransitions, tl, state, seen, allStates).contains(to)) {
                ListSpecs.forallContained(unseenReachableStatesThroughEpsilon(allTransitions, tl, state, seen, allStates), s => tl.contains(EpsilonTransition(state, s)), to)
                check(false)
              }
              // LEMMAS ---------------------------------------------------------------------------------------------------------------------

              Cons(to, unseenReachableStatesThroughEpsilon(allTransitions, tl, state, seen, allStates))
            } else {
              // LEMMAS ---------------------------------------------------------------------------------------------------------------------
              lemmaForallContainsTransitionToPreservedAddingInRef(unseenReachableStatesThroughEpsilon(allTransitions, tl, state, seen, allStates), tl, hd, state)
              // LEMMAS ---------------------------------------------------------------------------------------------------------------------

              unseenReachableStatesThroughEpsilon(allTransitions, tl, state, seen, allStates)
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

  def readOneChar[C](nfa: NFA[C], transitionsRec: List[Transition[C]], startStates: List[State], c: C, acc: List[State] = Nil()): List[State] = {
    require(validNFA(nfa))
    require(ListSpecs.noDuplicate(startStates))
    require(ListSpecs.noDuplicate(acc))
    require(acc.forall(s => nfa.allStates.contains(s)))
    require(ListSpecs.subseq(transitionsRec, nfa.transitions))
    decreases(transitionsRec)

    transitionsRec match {
      case Cons(hd, tl) =>
        ListUtils.lemmaTailIsSubseqOfBiggerList(transitionsRec, nfa.transitions)
        hd match {
          case LabeledTransition(from, cc, to) if cc == c && startStates.contains(from) && !acc.contains(to) => {
            ListSpecs.subseqContains(transitionsRec, nfa.transitions, hd)
            lemmaTransitionThenStatesInTransitionsStates(nfa.transitions, hd)
            lemmaInTransitionsStatesThenInAll(nfa, to)
            readOneChar(nfa, tl, startStates, c, Cons(to, acc))
          }
          case _ => readOneChar(nfa, tl, startStates, c, acc)
        }
      case Nil() => acc
    }
  } ensuring (res => ListSpecs.noDuplicate(res) && res.forall(s => nfa.allStates.contains(s)))

  // THEOREMS --------------------------------------------------------------------------------------------------------

  
  def equivalenceTheorem[C](r: Regex[C], s: List[C]): Unit = {
    require(validRegex(r))
    val nfa = fromRegexToNfa(r)
    r match {
      case EmptyExpr()        => lemmaEmptyExprRegexNFAEquiv(r, s)
      case EmptyLang()        => lemmaEmptyLangRegexNFAEquiv(r, s)
      case ElementMatch(c)    => lemmaElementMatchRegexNFAEquiv(r, s, c)
      case Union(rOne, rTwo)  => lemmaUnionMatchRegexNFAEquiv(r, rOne, rTwo, s)
      case Star(rInner)       => lemmaStarMatchRegexNFAEquiv(rInner, s)
      case Concat(rOne, rTwo) => lemmaConcatMatchRegexNFAEquiv(rOne, rTwo, s)
    }
  } ensuring (matchNFA(fromRegexToNfa(r), s) == VerifiedRegexMatcher.matchRSpec(r, s))

  // LEMMAS --------------------------------------------------------------------------------------------------------------------------------------

  // LEMMAS FOR UNION EQUIV -- BEGIN -------------------------------------------------------------------------------------------------------------

  
  
  def lemmaUnionMatchRegexNFAEquiv[C](r: Regex[C], r1: Regex[C], r2: Regex[C], s: List[C]): Unit = {
    require(validRegex(r1))
    require(validRegex(r2))
    require(validRegex(r))
    require(isUnion(r))
    require(unionInnersEquals(r, r1, r2))
    decreases(regexDepth(r))

    val nfa = fromRegexToNfa(r)

    val suffix = s
    val pastChars = Nil[C]()

    val errorState = getFreshState(Nil())
    val allStates = List(errorState)
    val goRes = go(r)(allStates, Nil(), errorState)

    val (ste1, statesAfter1, transitionsAfter1, stout1) =
      go(r1)(allStates, Nil(), errorState)

    val nfaR1 = fromRegexToNfa(r1)
    assert(nfaR1.transitions == ListUtils.removeDuplicates(transitionsAfter1, transitionsAfter1))
    assert(nfaR1.startState == ste1)
    assert(nfaR1.finalStates == List(stout1))
    assert(nfaR1.allStates == statesAfter1)

    r1 match {
      case EmptyExpr() => {
        lemmaEmptyExprRegexNFAEquiv(r1, s)
        check(matchNFA(fromRegexToNfa(r1), s) == matchRSpec(r1, s))
      }
      case EmptyLang() => {
        lemmaEmptyLangRegexNFAEquiv(r1, s)
        check(matchNFA(fromRegexToNfa(r1), s) == matchRSpec(r1, s))
      }
      case ElementMatch(c) => {
        lemmaElementMatchRegexNFAEquiv(r1, s, c)
        check(matchNFA(fromRegexToNfa(r1), s) == matchRSpec(r1, s))
      }
      case Union(rOne, rTwo) => {
        lemmaUnionMatchRegexNFAEquiv(r1, rOne, rTwo, s)
        check(matchNFA(fromRegexToNfa(r1), s) == matchRSpec(r1, s))
      }
      case Star(rInner) => {
        lemmaStarMatchRegexNFAEquiv(rInner, s)
        check(matchNFA(fromRegexToNfa(r1), s) == matchRSpec(r1, s))
      }
      case Concat(rOne, rTwo) => {
        lemmaConcatMatchRegexNFAEquiv(rOne, rTwo, s)
        check(matchNFA(fromRegexToNfa(r1), s) == matchRSpec(r1, s))
      }
    }
    check(matchNFA(fromRegexToNfa(r1), s) == matchRSpec(r1, s))

    val nfaR2 = fromRegexToNfa(r2)

    r2 match {
      case EmptyExpr() => {
        lemmaEmptyExprRegexNFAEquiv(r2, s)
        check(matchNFA(fromRegexToNfa(r2), s) == matchRSpec(r2, s))
      }
      case EmptyLang() => {
        lemmaEmptyLangRegexNFAEquiv(r2, s)
        check(matchNFA(fromRegexToNfa(r2), s) == matchRSpec(r2, s))
      }
      case ElementMatch(c) => {
        lemmaElementMatchRegexNFAEquiv(r2, s, c)
        check(matchNFA(fromRegexToNfa(r2), s) == matchRSpec(r2, s))
      }
      case Union(rOne, rTwo) => {
        lemmaUnionMatchRegexNFAEquiv(r2, rOne, rTwo, s)
        check(matchNFA(fromRegexToNfa(r2), s) == matchRSpec(r2, s))
      }
      case Star(rInner) => {
        lemmaStarMatchRegexNFAEquiv(rInner, s)
        check(matchNFA(fromRegexToNfa(r2), s) == matchRSpec(r2, s))
      }
      case Concat(rOne, rTwo) => {
        lemmaConcatMatchRegexNFAEquiv(rOne, rTwo, s)
        check(matchNFA(fromRegexToNfa(r2), s) == matchRSpec(r2, s))
      }
    }
    check(matchNFA(fromRegexToNfa(r2), s) == matchRSpec(r2, s))
    
    val (ste2, statesAfter2, transitionsAfter2, stout2) = go(r2)(statesAfter1, transitionsAfter1, errorState)
    
    // lemmaSameTransitionContentThenSameTransitionsStatesContent(transitions, ListUtils.removeDuplicates(transitions, transitions))
    // ListUtils.lemmaForallContainsPreservedIfSameContent(transitionsStates(transitions), transitionsStates(ListUtils.removeDuplicates(transitions, transitions)), allStates)

    // lemmaSameTransitionsContentOutOfErrorStatePreserved(transitions, ListUtils.removeDuplicates(transitions, transitions), errorState)
    // assert(noTransitionOutOfErrorState(ListUtils.removeDuplicates(transitions, transitions), errorState))

    // val nfaR2AfterR1 = NFA(ste2, List(finalState), errorState, ListUtils.removeDuplicates(transitionsAfter2, transitionsAfter2), statesAfter2)
    // check(matchNFA(nfaR2AfterR1, s) == matchRSpec(r2, s))
    
    
    assume(matchNFA(fromRegexToNfa(r), s) == matchRSpec(r, s))

  } ensuring (matchNFA(fromRegexToNfa(r), s) == matchRSpec(r, s))
  // LEMMAS FOR UNION EQUIV -- END ---------------------------------------------------------------------------------------------------------------

// LEMMAS FOR CONCAT EQUIV -- BEGIN ------------------------------------------------------------------------------------------------------------

// TODO
  
  def lemmaConcatMatchRegexNFAEquiv[C](r1: Regex[C], r2: Regex[C], s: List[C]): Unit = {
    require(validRegex(r1))
    require(validRegex(r2))

    val r = Concat(r1, r2)

    val nfa = fromRegexToNfa(r)

    val suffix = s
    val pastChars = Nil[C]()

    val errorState = getFreshState(Nil())
    val allStates = List(errorState)
    val goRes = go(r)(allStates, Nil(), errorState)

    val (ste1, statesAfter1, transitionsAfter1, stout1) =
      go(r1)(allStates, Nil(), errorState)

    val nfaR1 = fromRegexToNfa(r1)
    assert(nfaR1.transitions == ListUtils.removeDuplicates(transitionsAfter1, transitionsAfter1))
    assert(nfaR1.startState == ste1)
    assert(nfaR1.finalStates == List(stout1))
    assert(nfaR1.allStates == statesAfter1)

    val (ste2, statesAfter2, transitionsAfter2, stout2) = go(r2)(statesAfter1, transitionsAfter1, errorState)

    assume(matchNFA(fromRegexToNfa(Concat(r1, r2)), s) == matchRSpec(Concat(r1, r2), s))
  } ensuring (matchNFA(fromRegexToNfa(Concat(r1, r2)), s) == matchRSpec(Concat(r1, r2), s))
  // LEMMAS FOR CONCAT EQUIV -- END --------------------------------------------------------------------------------------------------------------

  // LEMMAS FOR STAR EQUIV -- BEGIN -------------------------------------------------------------------------------------------------------------

  // TODO
  
  def lemmaStarMatchRegexNFAEquiv[C](rI: Regex[C], s: List[C]): Unit = {
    require(validRegex(rI))
    require(!nullable(rI) && !isEmptyLang(rI))

    val r = Star(rI)

    val nfa = fromRegexToNfa(r)

    val suffix = s
    val pastChars = Nil[C]()

    val errorState = getFreshState(Nil())
    val allStates = List(errorState)
    val goRes = go(r)(allStates, Nil(), errorState)

    assume(matchNFA(fromRegexToNfa(Star(rI)), s) == matchRSpec(Star(rI), s))

  } ensuring (matchNFA(fromRegexToNfa(Star(rI)), s) == matchRSpec(Star(rI), s))
  // LEMMAS FOR STAR EQUIV -- END ---------------------------------------------------------------------------------------------------------------

  // LEMMAS FOR ELEMENT MATCH EQUIV -- BEGIN -----------------------------------------------------------------------------------------------------

  /** This lemma is really slow, it should be verified with >20sec timeout
    *
    * PASSES BUT NEEDS SOME OPTIMIZATIONS TO MAKE IT PRACTICAL
    *
    * @param r
    * @param s
    * @param c
    */
  
  def lemmaElementMatchRegexNFAEquiv[C](r: Regex[C], s: List[C], c: C): Unit = {
    require(validRegex(r))
    require(isElementMatch(r))
    require(elementMatchIsChar(r, c))

    val nfa = fromRegexToNfa(r)

    val suffix = s
    val pastChars = Nil[C]()

    val errorState = getFreshState(Nil())
    val allStates = List(errorState)
    val goRes = go(r)(allStates, Nil(), errorState)

    val ste = getFreshState(allStates)
    val stout = getFreshState(Cons(ste, allStates))
    val newAllStates = Cons(stout, Cons(ste, allStates))
    val newTransition = LabeledTransition(ste, c, stout)
    val newTransitions = Cons(newTransition, Nil())

    val currentStates = List(nfa.startState)

    val currentStatesEpsilonClosure = epsilonClosure(nfa, currentStates, Nil())

    lemmaEpsilonClosureContainsToExploreStates(nfa, currentStates, Nil(), ste)
    check(currentStatesEpsilonClosure.contains(ste))

    check(nfa.transitions == ListUtils.removeDuplicates(newTransitions, newTransitions))// helps stainless
    check(nfa.transitions == newTransitions) 
    check(!isEpsilonTransition(newTransition)) // helps stainless
    check(newTransitions.forall(t => !isEpsilonTransition(t))) // helps stainless
    ListUtils.lemmaForallThenDisjunction1(nfa.transitions, t => !isEpsilonTransition(t), t => !transitionToEq(t, stout))
    ListUtils.lemmaForallThenDisjunction1(nfa.transitions, t => !isEpsilonTransition(t), t => !transitionToEq(t, errorState))
    lemmaTransNotContainsEpsilonTrToThenClosureNotContains(nfa, currentStates, Nil(), stout)
    lemmaTransNotContainsEpsilonTrToThenClosureNotContains(nfa, currentStates, Nil(), errorState)

    check(!currentStatesEpsilonClosure.contains(stout))
    check(!currentStatesEpsilonClosure.contains(errorState))

    check(nfa.startState == ste)
    check(nfa.finalStates == Cons(stout, Nil()))

    s match {
      case Nil() => {
        ListUtils.lemmaListNotContainsThenFilterContainsEmpty(currentStatesEpsilonClosure, nfa.finalStates, stout)
        
        check(matchNFA(fromRegexToNfa(r), s) == matchNFAInner(fromRegexToNfa(r), s, List(ste), Nil(), s))
        check(matchNFA(fromRegexToNfa(r), s) == matchRSpec(r, s))
      }
      case Cons(cc, Nil()) if c == cc => {
        assert(s == List(c))
        assert(matchRSpec(r, s) == true)

        val nextChar = suffix.head
        val newPastChars = pastChars ++ List(nextChar)
        val newSuffix = suffix.tail
        val afterConsumingNextChar = readOneChar(nfa, nfa.transitions, currentStatesEpsilonClosure, nextChar)

        ListUtils.lemmaChangeCutStillConcatTotal(pastChars, suffix, s)

        lemmaReadOneCharContainsStateIfTransition(nfa, nfa.transitions, currentStatesEpsilonClosure, nextChar, Nil(), newTransition, ste, stout)
        assert(newSuffix.isEmpty)
        assert(nextChar == cc)
        assert(nextChar == c)

        val afterEpsilon = epsilonClosure(nfa, afterConsumingNextChar)

        lemmaEpsilonClosureContainsToExploreStates(nfa, afterConsumingNextChar, Nil(), stout)
        check(afterEpsilon.contains(stout))
        check(matchNFA(nfa, s) == matchNFAInner(nfa, s, List(nfa.startState), Nil(), s)) // helps
        check(matchNFA(nfa, s) == matchNFAInner(nfa, s, afterEpsilon, newPastChars, newSuffix)) // helps

        val currentStatesEpsilonClosure2 = epsilonClosure(nfa, afterEpsilon, Nil())
        lemmaEpsilonClosureContainsToExploreStates(nfa, afterEpsilon, Nil(), stout)
        assert(currentStatesEpsilonClosure2.contains(stout))
        lemmaListContainsThenFilterContainsNotEmpty(currentStatesEpsilonClosure2, nfa.finalStates, stout)
        assert(!currentStatesEpsilonClosure2.filter(s => nfa.finalStates.contains(s)).isEmpty)

        assert(matchNFA(fromRegexToNfa(r), s) == matchRSpec(r, s))
      }
      case Cons(cc, tl) if cc != c => {
        assert(matchRSpec(r, s) == false)
        assert(matchNFA(nfa, s) == matchNFAInner(nfa, s, currentStates, pastChars, suffix))

        val nextChar = suffix.head
        val newPastChars = pastChars ++ List(nextChar)
        val newSuffix = suffix.tail
        val afterConsumingNextChar = readOneChar(nfa, nfa.transitions, currentStatesEpsilonClosure, nextChar)

        ListUtils.lemmaChangeCutStillConcatTotal(pastChars, suffix, s)

        assert(nextChar != c)
        assert(afterConsumingNextChar.isEmpty)

        val afterEpsilon = epsilonClosure(nfa, afterConsumingNextChar)

        assert(afterEpsilon.isEmpty)
        lemmaFromNilMatchesNothing(nfa, s, newPastChars, newSuffix)
        assert(matchNFA(fromRegexToNfa(r), s) == matchRSpec(r, s))
      }

      case Cons(cc, tl) if cc == c => lemmaElementMatchRegexNFAEquivCorrectHeadNonEmptyTl(r, s, c)
    }

  } ensuring (matchNFA(fromRegexToNfa(r), s) == matchRSpec(r, s))

  
  def lemmaElementMatchRegexNFAEquivCorrectHeadNonEmptyTl[C](r: Regex[C], s: List[C], c: C): Unit = {
    require(validRegex(r))
    require(isElementMatch(r))
    require(elementMatchIsChar(r, c))
    require(!s.isEmpty)
    require(s.head == c)
    require(!s.tail.isEmpty)

    val nfa = fromRegexToNfa(r)

    val suffix = s
    val pastChars = Nil[C]()

    val errorState = getFreshState(Nil())
    val allStates = List(errorState)
    val goRes = go(r)(allStates, Nil(), errorState)

    val ste = getFreshState(allStates)
    val stout = getFreshState(Cons(ste, allStates))
    val newAllStates = Cons(stout, Cons(ste, allStates))
    val newTransition: Transition[C] = LabeledTransition(ste, c, stout)
    val newTransitions: List[Transition[C]] = List(newTransition)

    val currentStates = List(nfa.startState)

    val currentStatesEpsilonClosure = epsilonClosure(nfa, currentStates, Nil())

    lemmaEpsilonClosureContainsToExploreStates(nfa, currentStates, Nil(), ste)
    check(currentStatesEpsilonClosure.contains(ste))

    check(nfa.transitions == newTransitions) // helps stainless
    check(!isEpsilonTransition(newTransition)) // helps stainless
    check(!transitionFromEq(newTransition, stout)) // helps stainless

    newTransitions match {
      case Cons(hd, tl) => {
        assert(tl.isEmpty)
        assert(hd == newTransition)
        check(!isEpsilonTransition(newTransition)) // helps stainless
        check(!transitionFromEq(newTransition, stout)) // helps stainless
        check(tl.forall(t => !transitionFromEq(t, stout)))
        check(tl.forall(t => !isEpsilonTransition(t)))
      }
    }
    check(newTransitions.forall(t => !transitionFromEq(t, stout))) // helps stainless
    check(newTransitions.forall(t => !isEpsilonTransition(t))) // helps stainless

    check(ListSpecs.noDuplicate(currentStates)) // helps stainless

    ListUtils.lemmaForallThenDisjunction1(nfa.transitions, t => !isEpsilonTransition(t), t => !transitionToEq(t, stout))
    ListUtils.lemmaForallThenDisjunction1(nfa.transitions, t => !isEpsilonTransition(t), t => !transitionToEq(t, errorState))
    lemmaTransNotContainsEpsilonTrToThenClosureNotContains(nfa, currentStates, Nil(), stout)

    check(noEpsilonTransitionTo(nfa.transitions, errorState)) // helps stainless
    lemmaTransNotContainsEpsilonTrToThenClosureNotContains(nfa, currentStates, Nil(), errorState)

    check(!currentStatesEpsilonClosure.contains(stout))
    check(!currentStatesEpsilonClosure.contains(errorState))

    check(nfa.finalStates == Cons(stout, Nil()))

    val cc = s.head
    val tl = s.tail
    // assert(cc == c)
    // assert(!tl.isEmpty)
    // assert(matchRSpec(r, s) == false)

    // assert(pastChars.isEmpty)
    // assert(currentStates == List(nfa.startState))
    // assert(suffix == s)
    // assert(ListSpecs.noDuplicate(List(nfa.startState)))
    assert(matchNFA(nfa, s) == matchNFAInner(nfa, s, currentStates, pastChars, suffix)) // to optimise

    val nextChar = suffix.head
    val newPastChars = pastChars ++ List(nextChar)
    val newSuffix = suffix.tail
    val afterConsumingNextChar = readOneChar(nfa, nfa.transitions, currentStatesEpsilonClosure, nextChar)

    ListUtils.lemmaChangeCutStillConcatTotal(pastChars, suffix, s)
    lemmaReadOneCharContainsOneStateIfOneTransition(nfa, nfa.transitions, currentStatesEpsilonClosure, nextChar, Nil(), newTransition, ste, stout)
    // assert(nextChar == cc)
    // assert(nextChar == c)

    // assert(afterConsumingNextChar == List(stout))

    val afterEpsilon = epsilonClosure(nfa, afterConsumingNextChar)

    // assert(nfa.transitions.forall(t => !isEpsilonTransition(t)))
    lemmaEpsilonClosureWithNoEpsilonTrOnlyToExploreAndSeen(nfa, afterConsumingNextChar, Nil())

    ListUtils.lemmaSubsetContentThenForallContains(afterEpsilon, List(stout))
    ListUtils.lemmaSubsetContentThenForallContains(List(stout), afterEpsilon)
    ListUtils.lemmaForallContainsAndNoDuplicateThenSmallerList(afterEpsilon, List(stout))
    ListUtils.lemmaForallContainsAndNoDuplicateThenSmallerList(List(stout), afterEpsilon)
    ListUtils.lemmaSameContentSameSizeSmallerEqOneSameList(afterEpsilon, List(stout))

    // assert(afterEpsilon.size == List(stout).size)
    // assert(afterEpsilon == List(stout))

    assert(matchNFA(nfa, s) == matchNFAInner(nfa, s, afterEpsilon, newPastChars, newSuffix))

    if (newSuffix.isEmpty) {
      check(false)
    }

    val currentStatesEpsilonClosure2 = epsilonClosure(nfa, afterEpsilon, Nil())
    // assert(currentStatesEpsilonClosure2 == List(stout))

    val nextChar2 = newSuffix.head
    val newPastChars2 = newPastChars ++ List(nextChar2)
    val newSuffix2 = newSuffix.tail
    val afterConsumingNextChar2 = readOneChar(nfa, nfa.transitions, currentStatesEpsilonClosure2, nextChar2)

    ListUtils.lemmaChangeCutStillConcatTotal(newPastChars, newSuffix, s)

    check(nfa.transitions.forall(t => !transitionFromEq(t, stout)))
    lemmaReadOneCharEmptyIfNoTransitionsOutOfState(nfa, nfa.transitions, currentStatesEpsilonClosure2, nextChar2, Nil(), stout)
    // assert(afterConsumingNextChar2.isEmpty)

    val afterEpsilon2 = epsilonClosure(nfa, afterConsumingNextChar2)

    // assert(afterEpsilon2.isEmpty)

    // assert(newPastChars2 ++ newSuffix2 == s)
    // assert(newPastChars ++ newSuffix == s)

    assert(matchNFAInner(nfa, s, afterEpsilon, newPastChars, newSuffix) == matchNFAInner(nfa, s, afterEpsilon2, newPastChars2, newSuffix2))
    assert(matchNFA(nfa, s) == matchNFAInner(nfa, s, afterEpsilon2, newPastChars2, newSuffix2))

    lemmaFromNilMatchesNothing(nfa, s, newPastChars2, newSuffix2)

    assert(matchNFA(fromRegexToNfa(r), s) == matchRSpec(r, s))

  } ensuring (matchNFA(fromRegexToNfa(r), s) == matchRSpec(r, s))

  
  
  def lemmaReadOneCharEmptyIfNoTransitionsOutOfState[C](nfa: NFA[C], transitionsRec: List[Transition[C]], startStates: List[State], c: C, acc: List[State], from: State): Unit = {
    require(validNFA(nfa))
    require(ListSpecs.noDuplicate(startStates))
    require(ListSpecs.noDuplicate(acc))
    require(ListSpecs.subseq(transitionsRec, nfa.transitions))
    require(startStates == List(from))
    require(acc.isEmpty)
    require(transitionsRec.forall(t => !transitionFromEq(t, from)))

    decreases(transitionsRec)

    transitionsRec match {
      case Cons(hd, tl) =>
        ListUtils.lemmaTailIsSubseqOfBiggerList(transitionsRec, nfa.transitions)
        hd match {
          case LabeledTransition(fromm, cc, too) => {
            assert(from != fromm)
            ListSpecs.subseqContains(transitionsRec, nfa.transitions, hd)
            lemmaTransitionThenStatesInTransitionsStates(nfa.transitions, hd)
            lemmaReadOneCharEmptyIfNoTransitionsOutOfState(nfa, tl, startStates, c, acc, from)
          }
          case _ => lemmaReadOneCharEmptyIfNoTransitionsOutOfState(nfa, tl, startStates, c, acc, from)
        }
      case Nil() => ()
    }
  } ensuring (readOneChar(nfa, transitionsRec, startStates, c, acc).isEmpty)

  
  
  def lemmaEpsilonClosureWithNoEpsilonTrOnlyToExploreAndSeen[C](nfa: NFA[C], toExplore: List[State], seen: List[State]): Unit = {
    require(validNFA(nfa))
    require(toExplore.forall(s => nfa.allStates.contains(s)))
    require(seen.forall(s => nfa.allStates.contains(s)))
    require(ListSpecs.noDuplicate(seen))
    require(ListSpecs.noDuplicate(toExplore))
    require(ListSpecs.noDuplicate(toExplore ++ seen))
    require(nfa.transitions.forall(t => !isEpsilonTransition(t)))

    decreases({
      lemmaForallContainsAndNoDuplicateThenSmallerList(nfa.allStates, seen)
      lemmaForallContainsAndNoDuplicateThenSmallerList(nfa.allStates, toExplore)
      (nfa.allStates.size - seen.size) * nfa.allStates.size + toExplore.size
    })

    toExplore match {
      case Nil() => ()
      case Cons(hd, tl) => {
        if (seen.contains(hd)) {
          lemmaEpsilonClosureWithNoEpsilonTrOnlyToExploreAndSeen(nfa, tl, seen)
          assert((tl ++ seen).content == (toExplore ++ seen).content)
        } else {
          ListUtils.lemmaTailIsSubseqOfListBis(epsilonTransitionsFrom(hd, nfa.transitions))
          ListUtils.lemmaForallContainsConcatPreserves(toExplore, seen, nfa.allStates)

          lemmaEpsilonTransitionFromEmptyIfNoEpsilonTrInList(nfa.transitions, hd)
          assert(epsilonTransitionsFrom(hd, nfa.transitions).isEmpty) // TODO

          val seenArg = toExplore ++ seen
          val reachableFromHd: List[State] = unseenReachableStatesThroughEpsilon(nfa.transitions, epsilonTransitionsFrom(hd, nfa.transitions), hd, seenArg, nfa.allStates)
          val newToExplore = tl ++ reachableFromHd
          val newSeen = Cons(hd, seen)

          assert(reachableFromHd.isEmpty)

          ListUtils.lemmaForallNotContainsForConcat(reachableFromHd, seenArg, toExplore, seen)
          ListUtils.lemmaForallNotContainsForSubseq(reachableFromHd, toExplore, seen)
          
          assert(toExplore == List(hd) ++ tl) // it helps Stainless
          ListUtils.lemmaForallNotContainsForConcat(reachableFromHd, toExplore, List(hd), tl)
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
          assert(ListSpecs.noDuplicate(newToExplore ++ newSeen))

          lemmaEpsilonClosureWithNoEpsilonTrOnlyToExploreAndSeen(nfa, newToExplore, newSeen)
          assert((newToExplore ++ newSeen).content == (toExplore ++ seen).content)
        }
      }
    }

  } ensuring (epsilonClosure(nfa, toExplore, seen).content == (toExplore ++ seen).content)

  
  
  def lemmaReadOneCharContainsOneStateIfOneTransition[C](nfa: NFA[C], transitionsRec: List[Transition[C]], startStates: List[State], c: C, acc: List[State], t: Transition[C], fromState: State, toState: State): Unit = {
    require(validNFA(nfa))
    require(ListSpecs.noDuplicate(startStates))
    require(ListSpecs.noDuplicate(acc))
    require(acc.forall(s => nfa.allStates.contains(s)))
    require(ListSpecs.subseq(transitionsRec, nfa.transitions))
    require(transitionsRec == List(t) || acc == List(toState))
    require(acc.isEmpty)
    require(transitionFromEq(t, fromState))
    require(transitionToEq(t, toState))
    require(isLabeledTransition(t))
    require(labelEq(t, c))
    require(startStates.contains(fromState))

    decreases(transitionsRec)

    transitionsRec match {
      case Cons(hd, tl) =>
        ListUtils.lemmaTailIsSubseqOfBiggerList(transitionsRec, nfa.transitions)
        hd match {
          case LabeledTransition(from, cc, to) => {
            assert(hd == t)
            assert(tl.isEmpty)
            ListSpecs.subseqContains(transitionsRec, nfa.transitions, hd)
            lemmaTransitionThenStatesInTransitionsStates(nfa.transitions, hd)
            lemmaInTransitionsStatesThenInAll(nfa, to)
            lemmaReadOneCharContainsStateIfTransition(nfa, tl, startStates, c, Cons(to, acc), t, fromState, toState)
          }
        }
      case Nil() => ()
    }

  } ensuring (readOneChar(nfa, transitionsRec, startStates, c, acc) == List(toState))

  
  
  def lemmaReadOneCharContainsStateIfTransition[C](nfa: NFA[C], transitionsRec: List[Transition[C]], startStates: List[State], c: C, acc: List[State], t: Transition[C], fromState: State, toState: State): Unit = {
    require(validNFA(nfa))
    require(ListSpecs.noDuplicate(startStates))
    require(ListSpecs.noDuplicate(acc))
    require(acc.forall(s => nfa.allStates.contains(s)))
    require(ListSpecs.subseq(transitionsRec, nfa.transitions))
    require(transitionsRec.contains(t) || acc.contains(toState))
    require(transitionFromEq(t, fromState))
    require(transitionToEq(t, toState))
    require(isLabeledTransition(t))
    require(labelEq(t, c))
    require(startStates.contains(fromState))

    decreases(transitionsRec)

    transitionsRec match {
      case Cons(hd, tl) =>
        ListUtils.lemmaTailIsSubseqOfBiggerList(transitionsRec, nfa.transitions)
        hd match {
          case LabeledTransition(from, cc, to) if cc == c && startStates.contains(from) && !acc.contains(to) => {
            ListSpecs.subseqContains(transitionsRec, nfa.transitions, hd)
            lemmaTransitionThenStatesInTransitionsStates(nfa.transitions, hd)
            lemmaInTransitionsStatesThenInAll(nfa, to)
            lemmaReadOneCharContainsStateIfTransition(nfa, tl, startStates, c, Cons(to, acc), t, fromState, toState)
          }
          case _ => lemmaReadOneCharContainsStateIfTransition(nfa, tl, startStates, c, acc, t, fromState, toState)
        }
      case Nil() => ()
    }

  } ensuring (readOneChar(nfa, transitionsRec, startStates, c, acc).contains(toState))

  
  
  def lemmaEpsilonClosureContainsToExploreStates[C](nfa: NFA[C], toExplore: List[State], seen: List[State], st: State): Unit = {
    require(validNFA(nfa))
    require(toExplore.forall(s => nfa.allStates.contains(s)))
    require(seen.forall(s => nfa.allStates.contains(s)))
    require(ListSpecs.noDuplicate(seen))
    require(ListSpecs.noDuplicate(toExplore))
    require(ListSpecs.noDuplicate(toExplore ++ seen))
    require(toExplore.contains(st) || seen.contains(st))
    decreases({
      lemmaForallContainsAndNoDuplicateThenSmallerList(nfa.allStates, seen)
      lemmaForallContainsAndNoDuplicateThenSmallerList(nfa.allStates, toExplore)
      (nfa.allStates.size - seen.size) * nfa.allStates.size + toExplore.size
    })

    toExplore match {
      case Nil() => ()
      case Cons(hd, tl) => {
        if (seen.contains(hd)) {
          lemmaEpsilonClosureContainsToExploreStates(nfa, tl, seen, st)
        } else {
          ListUtils.lemmaTailIsSubseqOfListBis(epsilonTransitionsFrom(hd, nfa.transitions))
          ListUtils.lemmaForallContainsConcatPreserves(toExplore, seen, nfa.allStates)
          val seenArg = toExplore ++ seen
          val reachableFromHd: List[State] = unseenReachableStatesThroughEpsilon(nfa.transitions, epsilonTransitionsFrom(hd, nfa.transitions), hd, seenArg, nfa.allStates)
          val newToExplore = tl ++ reachableFromHd
          val newSeen = Cons(hd, seen)

          // LEMMAS ------------------------------------------------------------------------------------------------------------------------
          check(reachableFromHd.forall(s => !seenArg.contains(s)))
          assert(seenArg == toExplore ++ seen)
          ListUtils.lemmaForallNotContainsForConcat(reachableFromHd, seenArg, toExplore, seen)
          check(reachableFromHd.forall(s => !(toExplore ++ seen).contains(s)))
          ListUtils.lemmaForallNotContainsForSubseq(reachableFromHd, toExplore, seen)
          
          assert(toExplore == List(hd) ++ tl) // it helps Stainless
           ListUtils.lemmaForallNotContainsForConcat(reachableFromHd, toExplore, List(hd), tl)
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
          assert(ListSpecs.noDuplicate(newToExplore ++ newSeen))

          // LEMMAS ------------------------------------------------------------------------------------------------------------------------

          lemmaEpsilonClosureContainsToExploreStates(nfa, newToExplore, newSeen, st)
        }
      }
    }

  } ensuring (epsilonClosure(nfa, toExplore, seen).contains(st))

  
  
  def lemmaTransNotContainsEpsilonTrToThenClosureNotContains[C](nfa: NFA[C], toExplore: List[State], seen: List[State], sTo: State): Unit = {
    require(validNFA(nfa))
    require(noEpsilonTransitionTo(nfa.transitions, sTo))
    require(toExplore.forall(s => nfa.allStates.contains(s)))
    require(ListSpecs.noDuplicate(toExplore))
    require(ListSpecs.noDuplicate(seen))
    require(ListSpecs.noDuplicate(toExplore ++ seen))
    require(seen.forall(s => nfa.allStates.contains(s)))
    require(!seen.contains(sTo) && !toExplore.contains(sTo))
    decreases({
      lemmaForallContainsAndNoDuplicateThenSmallerList(nfa.allStates, seen)
      lemmaForallContainsAndNoDuplicateThenSmallerList(nfa.allStates, toExplore)
      (nfa.allStates.size - seen.size) * nfa.allStates.size + toExplore.size
    })

    toExplore match {
      case Nil() => ()
      case Cons(hd, tl) => {
        if (seen.contains(hd)) {
          lemmaTransNotContainsEpsilonTrToThenClosureNotContains(nfa, tl, seen, sTo)
        } else {
          ListUtils.lemmaTailIsSubseqOfListBis(epsilonTransitionsFrom(hd, nfa.transitions))
          ListUtils.lemmaForallContainsConcatPreserves(toExplore, seen, nfa.allStates)

          val seenArg = toExplore ++ seen
          val reachableFromHd: List[State] = unseenReachableStatesThroughEpsilon(nfa.transitions, epsilonTransitionsFrom(hd, nfa.transitions), hd, seenArg, nfa.allStates)
          val newToExplore = tl ++ reachableFromHd
          val newSeen = Cons(hd, seen)

          ListUtils.lemmaForallNotContainsForConcat(reachableFromHd, seenArg, toExplore, seen)
          ListUtils.lemmaForallNotContainsForSubseq(reachableFromHd, toExplore, seen)
          
          assert(toExplore == List(hd) ++ tl) // it helps Stainless
          ListUtils.lemmaForallNotContainsForConcat(reachableFromHd, toExplore, List(hd), tl)
          ListUtils.lemmaForallNotContainsForSubseq(reachableFromHd, List(hd), tl)
          
          ListUtils.noDuplicateConcatListNotContainedPreserves(tl, reachableFromHd)
          ListUtils.lemmaNoDuplicatePreservedSameContent(reachableFromHd ++ tl, tl ++ reachableFromHd)

          ListUtils.lemmaForallContainsConcatPreserves(tl, reachableFromHd, nfa.allStates)

          ListUtils.lemmaForallNotContainsCannotContain(reachableFromHd, toExplore, hd)
          ListUtils.lemmaNoDuplicateConcatThenForallNotContains(toExplore, seen)
          ListUtils.lemmaForallNotContainsForConcat(tl, reachableFromHd, seen)
          ListUtils.lemmaForallNotContainsPreservedAddNewElmtInRefList(newToExplore, seen, hd)
          ListUtils.lemmaForallNotContainedNoDupThenConcatNoDup(newToExplore, newSeen)

          lemmaNoEpsilonTransitionToThenNoneInEpsilonTransitionsFrom(nfa.transitions, sTo, hd)
          lemmaTransNotContainsEpsilonTrToThenUnseenReachableNotContains(nfa.transitions, epsilonTransitionsFrom(hd, nfa.transitions), hd, toExplore ++ seen, nfa.allStates, sTo)
          assert(!newSeen.contains(sTo))
          assert(!newToExplore.contains(sTo))
          lemmaTransNotContainsEpsilonTrToThenClosureNotContains(nfa, newToExplore, newSeen, sTo)

        }
      }
    }

  } ensuring (!epsilonClosure(nfa, toExplore, seen).contains(sTo))

  
  
  def lemmaTransNotContainsEpsilonTrToThenUnseenReachableNotContains[C](
      allTransitions: List[Transition[C]],
      transitions: List[Transition[C]],
      state: State,
      seen: List[State],
      allStates: List[State],
      sTo: State
  ): Unit = {
    require(ListSpecs.noDuplicate(seen))
    require(ListSpecs.noDuplicate(transitions))
    require(ListSpecs.noDuplicate(allTransitions))
    require(ListSpecs.subseq(transitions, epsilonTransitionsFrom(state, allTransitions)))
    require(seen.forall(s => allStates.contains(s)))
    require(transitionsStates(allTransitions).forall(s => allStates.contains(s)))
    require(transitions.forall(t => !transitionToEq(t, sTo)))

    decreases(transitions.size)

    transitions match {
      case Nil() => ()
      case Cons(hd, tl) =>
        ListUtils.lemmaTailIsSubseqOfBiggerList(transitions, epsilonTransitionsFrom(state, allTransitions))
        lemmaTransNotContainsEpsilonTrToThenUnseenReachableNotContains(allTransitions, tl, state, seen, allStates, sTo)
    }
  } ensuring (!unseenReachableStatesThroughEpsilon(allTransitions, transitions, state, seen, allStates).contains(sTo))

  // LEMMAS FOR ELEMENT MATCH EQUIV -- END   -----------------------------------------------------------------------------------------------------
  // LEMMAS FOR EMPTY EXPR EQUIV -- BEGIN --------------------------------------------------------------------------------------------------------

  
  
  def lemmaEmptyExprRegexNFAEquiv[C](r: Regex[C], s: List[C]): Unit = {
    require(validRegex(r))
    require(isEmptyExpr(r))

    val suffix = s
    val pastChars = Nil[C]()

    val errorState = getFreshState(Nil())
    val states = List(errorState)

    val goRes = go(r)(states, Nil(), errorState)

    val ste = getFreshState(states)
    val stout = getFreshState(Cons(ste, states))

    val nfa = fromRegexToNfa(r)
    val currentStates = List(nfa.startState)
    val currentStatesEpsilonClosure = epsilonClosure(nfa, currentStates, Nil())

    val finalState = nfa.finalStates.head

    assert(nfa.transitions.size == 1)
    val t = EpsilonTransition[C](nfa.startState, finalState)

    assert(nfa.transitions == List(t))

    lemmaTransContainsEpsilonTrThenClosureContainsState(nfa, currentStates, Nil(), nfa.startState, finalState, t)

    if (s.isEmpty) {
      lemmaListContainsThenFilterContainsNotEmpty(currentStatesEpsilonClosure, nfa.finalStates, finalState)
    } else {
      ListUtils.lemmaSubseqRefl(nfa.transitions)
      val nextChar = suffix.head
      val newPastChars = pastChars ++ List(nextChar)
      val newSuffix = suffix.tail
      val afterConsumingNextChar = readOneChar(nfa, nfa.transitions, currentStatesEpsilonClosure, nextChar)
      val afterEpsilon = epsilonClosure(nfa, afterConsumingNextChar)

      assert(afterConsumingNextChar.isEmpty)
      assert(afterEpsilon.isEmpty)
      lemmaFromNilMatchesNothing(nfa, s, newPastChars, newSuffix)
    }

  } ensuring (matchNFA(fromRegexToNfa(r), s) == matchRSpec(r, s))

  
  
  def lemmaTransContainsEpsilonTrThenClosureContainsState[C](nfa: NFA[C], toExplore: List[State], seen: List[State], sFrom: State, sTo: State, t: Transition[C]): Unit = {
    require(validNFA(nfa))
    require(nfa.transitions.contains(t))
    require(isEpsilonTransition(t))
    require(transitionFromEq(t, sFrom))
    require(transitionToEq(t, sTo))
    require(toExplore.forall(s => nfa.allStates.contains(s)))
    require(ListSpecs.noDuplicate(toExplore))
    require(ListSpecs.noDuplicate(seen))
    require(ListSpecs.noDuplicate(toExplore ++ seen))
    require(seen.forall(s => nfa.allStates.contains(s)))
    require(toExplore.contains(sFrom) || !toExplore.contains(sFrom) && toExplore.contains(sTo) && seen.contains(sFrom) || seen.contains(sTo) && seen.contains(sFrom))
    decreases({
      lemmaForallContainsAndNoDuplicateThenSmallerList(nfa.allStates, seen)
      lemmaForallContainsAndNoDuplicateThenSmallerList(nfa.allStates, toExplore)
      (nfa.allStates.size - seen.size) * nfa.allStates.size + toExplore.size
    })

    toExplore match {
      case Nil() => ()
      case Cons(hd, tl) => {
        if (seen.contains(hd)) {
          lemmaTransContainsEpsilonTrThenClosureContainsState(nfa, tl, seen, sFrom, sTo, t)

        } else {
          ListUtils.lemmaTailIsSubseqOfListBis(epsilonTransitionsFrom(hd, nfa.transitions))
          ListUtils.lemmaForallContainsConcatPreserves(toExplore, seen, nfa.allStates)

          val seenArg = toExplore ++ seen
          val reachableFromHd: List[State] = unseenReachableStatesThroughEpsilon(nfa.transitions, epsilonTransitionsFrom(hd, nfa.transitions), hd, seenArg, nfa.allStates)
          val newToExplore = tl ++ reachableFromHd
          val newSeen = Cons(hd, seen)

          ListUtils.lemmaForallNotContainsForConcat(reachableFromHd, seenArg, toExplore, seen)
          ListUtils.lemmaForallNotContainsForSubseq(reachableFromHd, toExplore, seen)
          
          
          ListUtils.lemmaForallNotContainsForConcat(reachableFromHd, toExplore, List(hd), tl)
          assert(toExplore == List(hd) ++ tl) // it helps Stainless
          check(reachableFromHd.forall(b => !(toExplore).contains(b)))
          check(toExplore == List(hd) ++ tl)
          check(reachableFromHd.forall(b => !(List(hd) ++ tl).contains(b)))
          ListUtils.lemmaForallNotContainsForSubseq(reachableFromHd, List(hd), tl)
          ListUtils.noDuplicateConcatListNotContainedPreserves(tl, reachableFromHd)
          ListUtils.lemmaNoDuplicatePreservedSameContent(reachableFromHd ++ tl, tl ++ reachableFromHd)

          ListUtils.lemmaForallContainsConcatPreserves(tl, reachableFromHd, nfa.allStates)

          ListUtils.lemmaForallNotContainsCannotContain(reachableFromHd, toExplore, hd)
          ListUtils.lemmaNoDuplicateConcatThenForallNotContains(toExplore, seen)
          ListUtils.lemmaForallNotContainsForConcat(tl, reachableFromHd, seen)
          ListUtils.lemmaForallNotContainsPreservedAddNewElmtInRefList(newToExplore, seen, hd)
          ListUtils.lemmaForallNotContainedNoDupThenConcatNoDup(newToExplore, newSeen)

          if (hd == sFrom) {
            lemmaTransitionsContainsEpsilonThenInEpsilonTransitionsFrom(sFrom, nfa.transitions, t)
            lemmaTransContainsEpsilonTrThenUnseenReachableContainsState(nfa.transitions, epsilonTransitionsFrom(hd, nfa.transitions), hd, toExplore ++ seen, nfa.allStates, sFrom, sTo, t)
            lemmaTransContainsEpsilonTrThenClosureContainsState(nfa, newToExplore, newSeen, sFrom, sTo, t)
          } else {
            if (hd == sTo) {
              lemmaTransContainsEpsilonTrThenClosureContainsState(nfa, newToExplore, newSeen, sFrom, sTo, t)
            } else {
              assert(hd != sTo && hd != sFrom)
              if (toExplore.contains(sFrom)) {
                assert(tl.contains(sFrom))
                assert(newToExplore.contains(sFrom))
                lemmaTransContainsEpsilonTrThenClosureContainsState(nfa, newToExplore, newSeen, sFrom, sTo, t)
              } else {
                if (!toExplore.contains(sFrom) && toExplore.contains(sTo) && seen.contains(sFrom)) {
                  assert(tl.contains(sTo))
                  assert(newToExplore.contains(sTo))
                  assert(newSeen.contains(sFrom))
                  lemmaTransContainsEpsilonTrThenClosureContainsState(nfa, newToExplore, newSeen, sFrom, sTo, t)
                } else {
                  assert(seen.contains(sTo) && seen.contains(sFrom))
                  lemmaTransContainsEpsilonTrThenClosureContainsState(nfa, newToExplore, newSeen, sFrom, sTo, t)
                }
              }

            }
          }

        }
      }
    }

  } ensuring (epsilonClosure(nfa, toExplore, seen).contains(sTo))

  
  
  def lemmaTransitionsContainsEpsilonThenInEpsilonTransitionsFrom[C](state: State, transitions: List[Transition[C]], t: Transition[C]): Unit = {
    require(ListSpecs.noDuplicate(transitions))
    require(transitions.contains(t))
    require(transitionFromEq(t, state))
    require(isEpsilonTransition(t))

    decreases(transitions.size)

    transitions match {
      case Cons(hd, tl) =>
        if (hd == t) {
          ()
        } else {
          lemmaTransitionsContainsEpsilonThenInEpsilonTransitionsFrom(state, tl, t)
        }

      case Nil() => ()
    }

  } ensuring (epsilonTransitionsFrom(state, transitions).contains(t))

  
  
  def lemmaTransContainsEpsilonTrThenUnseenReachableContainsState[C](
      allTransitions: List[Transition[C]],
      transitions: List[Transition[C]],
      state: State,
      seen: List[State],
      allStates: List[State],
      sFrom: State,
      sTo: State,
      t: Transition[C]
  ): Unit = {
    require(ListSpecs.noDuplicate(seen))
    require(ListSpecs.noDuplicate(transitions))
    require(ListSpecs.noDuplicate(allTransitions))
    require(ListSpecs.subseq(transitions, epsilonTransitionsFrom(state, allTransitions)))
    require(seen.forall(s => allStates.contains(s)))
    require(transitionsStates(allTransitions).forall(s => allStates.contains(s)))

    require(transitions.contains(t))
    require(isEpsilonTransition(t))
    require(transitionFromEq(t, sFrom))
    require(transitionToEq(t, sTo))

    decreases(transitions.size)

    transitions match {
      case Nil() => ()
      case Cons(hd, tl) =>
        ListUtils.lemmaTailIsSubseqOfBiggerList(transitions, epsilonTransitionsFrom(state, allTransitions))
        if (hd == t) {
          ()
        } else {
          assert(tl.contains(t))
          lemmaTransContainsEpsilonTrThenUnseenReachableContainsState(allTransitions, tl, state, seen, allStates, sFrom, sTo, t)
        }
    }
  } ensuring (unseenReachableStatesThroughEpsilon(allTransitions, transitions, state, seen, allStates).contains(sTo) || seen.contains(sTo))

  // LEMMAS FOR EMPTY EXPR EQUIV -- END ----------------------------------------------------------------------------------------------------------

  // LEMMAS FOR EMPTY LANG EQUIV -- BEGIN --------------------------------------------------------------------------------------------------------
  
  
  def lemmaFromErrorStateMatchesNothing[C](nfa: NFA[C], s: List[C], pastChars: List[C], suffix: List[C]): Unit = {
    require(validNFA(nfa))
    require(pastChars ++ suffix == s)

    val currentStates = List(nfa.errorState)

    val currentStatesEpsilonClosure = epsilonClosure(nfa, currentStates, Nil())
    lemmaEpsilonClosureFromErrorIsOnlyError(nfa, currentStates, Nil())
    assert(currentStatesEpsilonClosure == currentStates)

    if (suffix.isEmpty) {
      assert(!nfa.finalStates.contains(nfa.errorState))
    } else {
      ListUtils.lemmaSubseqRefl(nfa.transitions)
      val nextChar = suffix.head
      val newPastChars = pastChars ++ List(nextChar)
      val newSuffix = suffix.tail
      val afterConsumingNextChar = readOneChar(nfa, nfa.transitions, currentStatesEpsilonClosure, nextChar)
      lemmaReadOneCharFromErrorStateReturnsNil(nfa, nfa.transitions, currentStates, nextChar, Nil())
      assert(afterConsumingNextChar.isEmpty)
      val afterEpsilon = epsilonClosure(nfa, afterConsumingNextChar)
      assert(afterEpsilon.isEmpty)
      ListUtils.lemmaTwoListsConcatAssociativity(pastChars, List(nextChar), newSuffix)
      lemmaFromNilMatchesNothing(nfa, s, newPastChars, newSuffix)

    }

  } ensuring (!matchNFAInner(nfa, s, List(nfa.errorState), pastChars, suffix))

  
  
  def lemmaFromNilMatchesNothing[C](nfa: NFA[C], s: List[C], pastChars: List[C], suffix: List[C]): Unit = {
    require(validNFA(nfa))
    require(pastChars ++ suffix == s)

    decreases(suffix)

    val currentStates = Nil[State]()

    val currentStatesEpsilonClosure = epsilonClosure(nfa, currentStates, Nil())

    assert(currentStatesEpsilonClosure.isEmpty)

    if (suffix.isEmpty) {
      ()
    } else {
      ListUtils.lemmaSubseqRefl(nfa.transitions)
      val nextChar = suffix.head
      val newPastChars = pastChars ++ List(nextChar)
      val newSuffix = suffix.tail
      val afterConsumingNextChar = readOneChar(nfa, nfa.transitions, currentStatesEpsilonClosure, nextChar)
      lemmaReadOneCharFromNilReturnsNil(nfa, nfa.transitions, currentStates, nextChar, Nil())
      assert(afterConsumingNextChar.isEmpty)
      val afterEpsilon = epsilonClosure(nfa, afterConsumingNextChar)
      assert(afterEpsilon.isEmpty)
      ListUtils.lemmaTwoListsConcatAssociativity(pastChars, List(nextChar), newSuffix)
      lemmaFromNilMatchesNothing(nfa, s, newPastChars, newSuffix)
    }

  } ensuring (!matchNFAInner(nfa, s, Nil(), pastChars, suffix))

  
  
  def lemmaReadOneCharFromNilReturnsNil[C](nfa: NFA[C], transitionsRec: List[Transition[C]], startStates: List[State], c: C, acc: List[State]): Unit = {
    require(validNFA(nfa))
    require(ListSpecs.noDuplicate(startStates))
    require(ListSpecs.noDuplicate(acc))
    require(acc.forall(s => nfa.allStates.contains(s)))
    require(ListSpecs.subseq(transitionsRec, nfa.transitions))

    require(acc.isEmpty)
    require(startStates.isEmpty)

    decreases(transitionsRec)

    transitionsRec match {
      case Cons(hd, tl) =>
        ListUtils.lemmaTailIsSubseqOfBiggerList(transitionsRec, nfa.transitions)
        hd match {
          case LabeledTransition(from, cc, to) if cc == c && startStates.contains(from) && !acc.contains(to) => {
            check(false)
          }
          case _ => lemmaReadOneCharFromNilReturnsNil(nfa, tl, startStates, c, acc)
        }
      case Nil() => ()
    }
  } ensuring (readOneChar(nfa, transitionsRec, startStates, c, acc).isEmpty)

  
  
  def lemmaReadOneCharFromErrorStateReturnsNil[C](nfa: NFA[C], transitionsRec: List[Transition[C]], startStates: List[State], c: C, acc: List[State]): Unit = {
    require(validNFA(nfa))
    require(ListSpecs.noDuplicate(startStates))
    require(ListSpecs.noDuplicate(acc))
    require(acc.forall(s => nfa.allStates.contains(s)))
    require(ListSpecs.subseq(transitionsRec, nfa.transitions))

    require(acc.isEmpty)
    require(startStates == List(nfa.errorState))

    decreases(transitionsRec)

    transitionsRec match {
      case Cons(hd, tl) =>
        ListUtils.lemmaTailIsSubseqOfBiggerList(transitionsRec, nfa.transitions)
        hd match {
          case LabeledTransition(from, cc, to) if cc == c && startStates.contains(from) && !acc.contains(to) => {
            assert(from == nfa.errorState)
            ListSpecs.subseqContains(transitionsRec, nfa.transitions, hd)
            lemmaNoTransitionsOutOfErrorStateThenNotContained(nfa.transitions, hd, nfa.errorState)
            check(false)
          }
          case _ => lemmaReadOneCharFromErrorStateReturnsNil(nfa, tl, startStates, c, acc)
        }
      case Nil() => ()
    }
  } ensuring (readOneChar(nfa, transitionsRec, startStates, c, acc).isEmpty)

  
  
  def lemmaEpsilonClosureFromErrorIsOnlyError[C](nfa: NFA[C], toExplore: List[State], seen: List[State]): Unit = {
    require(validNFA(nfa))
    require(toExplore.forall(s => nfa.allStates.contains(s)))
    require(seen.forall(s => nfa.allStates.contains(s)))
    require(ListSpecs.noDuplicate(seen))
    require(ListSpecs.noDuplicate(toExplore))
    require(ListSpecs.noDuplicate(toExplore ++ seen))
    require(toExplore == List(nfa.errorState) && seen.isEmpty || toExplore.isEmpty && seen == List(nfa.errorState))
    decreases(toExplore)

    toExplore match {
      case Nil() => ()
      case Cons(hd, tl) => {
        if (seen.contains(hd)) {
          ()
        } else {
          ListUtils.lemmaTailIsSubseqOfListBis(epsilonTransitionsFrom(hd, nfa.transitions))
          ListUtils.lemmaForallContainsConcatPreserves(toExplore, seen, nfa.allStates)
          val reachableFromHd: List[State] = unseenReachableStatesThroughEpsilon(nfa.transitions, epsilonTransitionsFrom(hd, nfa.transitions), hd, toExplore ++ seen, nfa.allStates)
          val newToExplore = tl ++ reachableFromHd
          val newSeen = Cons(hd, seen)

          lemmaNotTransitionOutOfErrorStateThenTransFromErrorNil(nfa.errorState, nfa.transitions)
          ListUtils.lemmaSubseqOfEmptyIsEmpty(epsilonTransitionsFrom(hd, nfa.transitions), transitionsFrom(hd, nfa.transitions))
          lemmaEpsilonClosureFromErrorIsOnlyError(nfa, newToExplore, newSeen)
        }
      }
    }

  } ensuring (epsilonClosure(nfa, toExplore, seen) == List(nfa.errorState))

  
  
  def lemmaNotTransitionOutOfErrorStateThenTransFromErrorNil[C](errorState: State, @induct transitions: List[Transition[C]]): Unit = {
    require(noTransitionOutOfErrorState(transitions, errorState))
    require(ListSpecs.noDuplicate(transitions))

  } ensuring (transitionsFrom(errorState, transitions).isEmpty)

  
  
  def lemmaEmptyLangRegexNFAEquiv[C](r: Regex[C], s: List[C]): Unit = {
    require(validRegex(r))
    require(isEmptyLang(r))

    val nfa = fromRegexToNfa(r)

    lemmaFromErrorStateMatchesNothing(nfa, s, Nil(), s)

  } ensuring (matchNFA(fromRegexToNfa(r), s) == matchRSpec(r, s))

  // LEMMAS FOR EMPTY LANG EQUIV -- END --------------------------------------------------------------------------------------------------------

  
  
  def lemmaForallContainsTransitionToPreservedAddingInRef[C](@induct l: List[State], lRef: List[Transition[C]], t: Transition[C], state: State): Unit = {
    require(l.forall(s => lRef.contains(EpsilonTransition(state, s))))

  } ensuring (l.forall(s => Cons(t, lRef).contains(EpsilonTransition(state, s))))

  @extern
  def assume(b: Boolean): Unit = {
    ()
  } ensuring (b)


  def findLongestMatch[C](nfa: NFA[C], input: List[C]): (List[C], List[C]) = {
    require(validNFA(nfa))
    findLongestMatchInner(nfa, List(nfa.startState), Nil(), input)
  }

  def findLongestMatchInner[C](
      nfa: NFA[C],
      currentStates: List[State],
      pastChars: List[C],
      suffix: List[C]
  ): (List[C], List[C]) = {
    require(validNFA(nfa))
    // require(currentStates.forall(s => nfa.allStates.contains(s)))
    // require(currentStates == epsilonClosure(nfa, currentStates, Nil()))
    decreases(suffix.size)

    if (!currentStates.filter(s => nfa.finalStates.contains(s)).isEmpty) {
      // The NFA accepts pastChars
      // We then need to continue to see if it accepts a longer string or return pastChars

    } else {
      // The NFA does NOT accept pastChars
      // We then need to continue to see if it accepts a longer string or return None
    }
    (pastChars, suffix)
  }

  // Longest match theorems
  def longestMatchIsAcceptedByMatchOrIsEmpty[C](
      nfa: NFA[C],
      input: List[C]
  ): Unit = {
    require(validNFA(nfa))

  }

  def longestMatchNoBiggerStringMatch[C](
      baseNfa: NFA[C],
      input: List[C],
      returnP: List[C],
      bigger: List[C]
  ): Unit = {}

}
