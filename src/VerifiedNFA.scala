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

  case class NFA[C](startStates: List[State], finalStates: List[State], errorState: State, transitions: List[Transition[C]], allStates: List[State])

  def validNFA[C](nfa: NFA[C]): Boolean = { true }

  def isRoot[C](state: State, transitions: List[Transition[C]]): Boolean = {

    transitions match {
      case Cons(hd, tl) =>
        hd match {
          case EpsilonTransition(from, to)    => to != state && isRoot(state, tl)
          case LabeledTransition(from, _, to) => to != state && isRoot(state, tl)
        }
      case Nil() => true
    }
  }
  def isLeaf[C](state: State, transitions: List[Transition[C]]): Boolean = {

    transitions match {
      case Cons(hd, tl) =>
        hd match {
          case EpsilonTransition(from, to)    => from != state && isRoot(state, tl)
          case LabeledTransition(from, _, to) => from != state && isRoot(state, tl)
        }
      case Nil() => true
    }
  }
  def noLoopTransitions[C](transitions: List[Transition[C]]): Boolean = transitions match {
    case Cons(hd, tl) =>
      hd match {
        case EpsilonTransition(from, to)    => from != to && noLoopTransitions(tl)
        case LabeledTransition(from, _, to) => from != to && noLoopTransitions(tl)
      }
    case Nil() => true
  }

  /** Returns the list with no duplicates of the states in the list of transitions
    *
    * @param transitions
    */
  def transitionsStates[C](transitions: List[Transition[C]]): List[State] = {
    transitions match {
      case Cons(hd, tl) =>
        hd match {
          case EpsilonTransition(from, to)    => ListUtils.concatWithoutDuplicates(transitionsStates(tl), List(to, from))
          case LabeledTransition(from, _, to) => ListUtils.concatWithoutDuplicates(transitionsStates(tl), List(to, from))
        }
      case Nil() => Nil[State]()
    }
  } ensuring (res => ListOps.noDuplicate(res))

  def transitionsFrom[C](state: State, transitions: List[Transition[C]]): List[Transition[C]] = {
    transitions match {
      case Cons(hd, tl) =>
        hd match {
          case EpsilonTransition(from, to) if from == state    => Cons(hd, transitionsFrom(state, tl))
          case LabeledTransition(from, c, to) if from == state => Cons(hd, transitionsFrom(state, tl))
          case _                                               => transitionsFrom(state, tl)
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
    val (startState, allStates, transitions) = go(r, finalState)(states, Nil(), errorState)
    NFA(List(startState), List(finalState), errorState, transitions, allStates)
  }
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
        val (steOne, statesAfterOne, transitionsAfterOne) = go(rOne, cont)(allStates, transitions, errorState)
        ListSpecs.subseqContains(allStates, statesAfterOne, errorState)
        val (steTwo, statesAfterTwo, transitionsAfterTwo) = go(rTwo, cont)(statesAfterOne, transitionsAfterOne, errorState)
        ListSpecs.subseqContains(statesAfterOne, statesAfterTwo, cont)
        val ste = getFreshState(statesAfterTwo)
        val newTransitions: List[Transition[C]] = Cons(EpsilonTransition(ste, steOne), Cons(EpsilonTransition(ste, steTwo), transitionsAfterTwo))

        ListUtils.lemmaSubSeqTransitive(allStates, statesAfterOne, statesAfterTwo)
        ListSpecs.subseqContains(statesAfterOne, statesAfterTwo, steOne)

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
        val (innerSte, statesAfterInner, transitionsAfterInner) = go(r, ste)(Cons(ste, allStates), transitions, errorState)
        val newTransitions: List[Transition[C]] = Cons(EpsilonTransition(ste, innerSte), Cons(EpsilonTransition(ste, cont), transitionsAfterInner))
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
  )

  def prefixSetNFA[C](nfa: NFA[C]): NFA[C] = {
    // case class NFA[C](startStates: List[State], finalStates: List[State], errorState: State, transitions: List[Transition[C]], allStates: List[State])
    NFA(nfa.startStates, nfa.allStates.filter(_ != nfa.errorState), nfa.errorState, nfa.transitions, nfa.allStates)
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

  def lemmaLabelBiggerThanMaxIdIsNotInList(states: List[State], newLabel: BigInt): Unit = {
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
  def matchNFA[C](nfa: NFA[C], input: List[C]): Boolean = findLongestMatch(nfa, input)._2.isEmpty

  @inline
  def findLongestMatch[C](nfa: NFA[C], input: List[C]): (List[C], List[C]) = {

    findLongestMatchInner(nfa, nfa.startStates, Nil(), input)
  }

  def findLongestMatchInner[C](nfa: NFA[C], startStates: List[State], pastChars: List[C], suffix: List[C]): (List[C], List[C]) = {
    decreases(suffix.size)
    val startStatesWithEmpty = emptyClosure(startStates, nfa)
    if (suffix.isEmpty) {
      if (!nfa.finalStates.map(s => startStates.contains(s)).filter(_ == true).isEmpty) {
        (pastChars, suffix)
      } else {
        (Nil(), pastChars)
      }
    } else {
      val newChar = suffix.head

      val currentPrefix = pastChars ++ List(newChar)
      val statesAfterChar = nfa.transitions.flatMap(t =>
        t match {
          case LabeledTransition(from, c, to) if startStatesWithEmpty.contains(from) && c == newChar => List(to)
          case _                                                                                     => Nil[State]()
        }
      )
      val statesAfterEmpty = emptyClosure(statesAfterChar, nfa)
      if (!nfa.finalStates.map(s => statesAfterEmpty.contains(s)).filter(_ == true).isEmpty) {
        val recursive = findLongestMatchInner(nfa, statesAfterEmpty, currentPrefix, suffix.tail)
        if (recursive._1.size > currentPrefix.size) {
          recursive
        } else {
          (currentPrefix, suffix.tail)
        }
      } else {
        findLongestMatchInner(nfa, statesAfterEmpty, currentPrefix, suffix.tail)
      }
    }

  }

  def emptyClosure[C](startStates: List[State], nfa: NFA[C]): List[State] = {
    require(ListOps.noDuplicate(startStates))
    require(startStates.forall(s => transitionsStates(nfa.transitions).contains(s)))
    decreases({
      ListUtils.lemmaForallContainsAndNoDuplicateThenSmallerList(transitionsStates(nfa.transitions), startStates)
      transitionsStates(nfa.transitions).size - startStates.size
    })
    ListUtils.lemmaForallContainsAndNoDuplicateThenSmallerList(transitionsStates(nfa.transitions), startStates)
    assert(transitionsStates(nfa.transitions).size >= startStates.size)
    assert(transitionsStates(nfa.transitions).size - startStates.size >= 0)
    val newStates = nfa.transitions.flatMap(t =>
      t match {
        case EpsilonTransition(from, to) if startStates.contains(from) => List(to)
        case _                                                         => Nil[State]()
      }
    )
    if (newStates.forall(startStates.contains(_))) {
      ListUtils.removeDuplicates(startStates)
    } else {
      val newStartStates = ListUtils.removeDuplicates(startStates ++ newStates)
      emptyClosure(newStartStates, nfa)
    }
  }

  @inline
  def isEmptyTransition[C](t: Transition[C]): Boolean = t match {
    case EpsilonTransition(_, _) => true
    case _                       => false
  }

  // Longest match theorems
  def longestMatchIsAcceptedByMatchOrIsEmpty[C](nfa: NFA[C], input: List[C]): Unit = {
    require(validNFA(nfa))

  } ensuring (findLongestMatchInner(nfa, nfa.startStates, Nil(), input)._1.isEmpty || matchNFA(nfa, findLongestMatchInner(nfa, nfa.startStates, Nil(), input)._1))

  // def longestMatchNoBiggerStringMatch[C](baseR: Regex[C], input: List[C], returnP: List[C], bigger: List[C]): Unit = {
  //   require(validRegex(baseR))
  //   require(ListUtils.isPrefix(returnP, input))
  //   require(ListUtils.isPrefix(bigger, input))
  //   require(bigger.size >= returnP.size)
  //   require(findLongestMatchInner(baseR, Nil(), input)._1 == returnP)

  //   if (bigger.size == returnP.size) {
  //     ListUtils.lemmaIsPrefixSameLengthThenSameList(bigger, returnP, input)
  //   } else {
  //     if (matchR(baseR, bigger)) {
  //       lemmaKnownAcceptedStringThenFromSmallPAtLeastThat(baseR, baseR, input, Nil(), bigger)
  //       check(false)
  //     }
  //   }

  // } ensuring (bigger == returnP || !matchR(baseR, bigger))

  // Regex equivalence theorem
  @extern
  def equivalenceTheorem[C](r: Regex[C], s: List[C]): Unit = {
    require(validRegex(r))
    assume(findLongestMatch(fromRegexToNfa(r), s) == VerifiedRegexMatcher.findLongestMatch(r, s))
  } ensuring (findLongestMatch(fromRegexToNfa(r), s) == VerifiedRegexMatcher.findLongestMatch(r, s))

}
