/** Author: Samuel Chassot
  */

import stainless.equations._
import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._
import scala.compiletime.ops.long

object VerifiedDFA {
  case class State(label: BigInt) {
    require(label >= 0)
  }

  case class Transition[C](from: State, c: C, to: State)
  case class DFA[C](startState: State, finalStates: List[State], errorState: State, transitions: List[Transition[C]])

  def validDFA[C](dfa: DFA[C]): Boolean = uniqueStateCharTransitions(dfa.transitions, Nil())

  def uniqueStateCharTransitions[C](l: List[Transition[C]], seenStateCharPairs: List[(State, C)]): Boolean = {
    l match {
      case Cons(hd, tl) => !seenStateCharPairs.contains((hd.from, hd.c)) && uniqueStateCharTransitions(tl, Cons((hd.from, hd.c), seenStateCharPairs))
      case Nil()        => true
    }

  }

}

object VerifiedDFAMatcher {
  import VerifiedDFA._
  import ListUtils._

  @inline
  def matchDFA[C](dfa: DFA[C], input: List[C]): Boolean = {
    require(validDFA(dfa))
    findLongestMatch(dfa, input)._2.isEmpty
  } ensuring (res => !res || findLongestMatch(dfa, input)._1 == input)

  @inline
  def findLongestMatch[C](dfa: DFA[C], input: List[C]): (List[C], List[C]) = {
    require(validDFA(dfa))
    findLongestMatchInner(dfa, dfa.startState, Nil(), input)
  } ensuring (res => res._1 ++ res._2 == input)

  def findLongestMatchInner[C](dfa: DFA[C], from: State, pastChars: List[C], suffix: List[C]): (List[C], List[C]) = {
    require(validDFA(dfa))
    require(from == moveMultipleSteps(dfa, dfa.startState, pastChars))
    decreases(suffix.size)

    if (suffix.isEmpty) {
      if (dfa.finalStates.contains(from)) {
        ListUtils.lemmaConcatTwoListThenFirstIsPrefix(pastChars, suffix)
        (pastChars, suffix)
      } else {
        (Nil(), pastChars ++ suffix)
      }
    } else {

      val nextChar = suffix.head

      val newPrefix = pastChars ++ List(nextChar)
      val newSuffix = suffix.tail

      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(pastChars, suffix)
      ListUtils.lemmaAddHeadSuffixToPrefixStillPrefix(pastChars, pastChars ++ suffix)

      ListUtils.lemmaTwoListsConcatAssociativity(pastChars, List(nextChar), newSuffix)
      ListUtils.lemmaSubseqRefl(dfa.transitions)

      val nextState = moveOneStep(dfa, dfa.transitions, from, nextChar)

      lemmaMoveOneStepAfterMultipleIsSameAsMultipleWithNewChar(dfa, dfa.startState, pastChars, nextChar)

      val recursive = findLongestMatchInner(dfa, nextState, newPrefix, newSuffix)

      if (dfa.finalStates.contains(from)) {
        if (recursive._1.size > pastChars.size) {
          recursive
        } else {
          ListUtils.lemmaConcatTwoListThenFirstIsPrefix(newPrefix, newSuffix)
          assert(ListUtils.isPrefix(newPrefix, newPrefix ++ newSuffix))
          assert(ListUtils.isPrefix(newPrefix, pastChars ++ suffix))
          (pastChars, suffix)
        }
      } else {
        recursive
      }
    }

  } ensuring (res =>
    res._1.isEmpty && res._2 == pastChars ++ suffix || res._1.size >= pastChars.size && ListUtils.isPrefix(res._1, pastChars ++ suffix) && res._1 ++ res._2 == pastChars ++ suffix
  )

  def moveOneStep[C](dfa: DFA[C], transitionsListRec: List[Transition[C]], from: State, c: C): State = {
    require(validDFA(dfa))
    require(ListSpecs.subseq(transitionsListRec, dfa.transitions))

    transitionsListRec match {
      case Cons(hd, tl) if hd.from == from && hd.c == c => hd.to
      case Cons(hd, tl) => {
        ListUtils.lemmaTailIsSubseqOfList(hd, tl)
        ListUtils.lemmaSubSeqTransitive(tl, transitionsListRec, dfa.transitions)
        moveOneStep(dfa, tl, from, c)
      }
      case Nil() => dfa.errorState
    }

  } ensuring (res => true)

  def moveMultipleSteps[C](dfa: DFA[C], from: State, cs: List[C]): State = {
    require(validDFA(dfa))
    decreases(cs.size)
    cs match {
      case Cons(hd, tl) => {
        ListUtils.lemmaSubseqRefl(dfa.transitions)
        moveMultipleSteps(dfa, moveOneStep(dfa, dfa.transitions, from, hd), tl)
      }
      case Nil() => from
    }
  } ensuring (res => true)

  @opaque
  @inlineOnce
  def lemmaMoveOneStepAfterMultipleIsSameAsMultipleWithNewChar[C](dfa: DFA[C], from: State, cs: List[C], newC: C): Unit = {
    require(validDFA(dfa))
    decreases(cs.size)
    cs match {
      case Cons(hd, tl) => {
        ListUtils.lemmaSubseqRefl(dfa.transitions)
        lemmaMoveOneStepAfterMultipleIsSameAsMultipleWithNewChar(dfa, moveOneStep(dfa, dfa.transitions, from, hd), tl, newC)
      }
      case Nil() => ()
    }
  } ensuring ({
    ListUtils.lemmaSubseqRefl(dfa.transitions)
    moveMultipleSteps(dfa, from, cs ++ List(newC)) == moveOneStep(dfa, dfa.transitions, moveMultipleSteps(dfa, from, cs), newC)
  })

  // Longest match theorems
  def longestMatchIsAcceptedByMatchOrIsEmpty[C](dfa: DFA[C], input: List[C]): Unit = {
    require(validDFA(dfa))

    longestMatchIsAcceptedByMatchOrIsEmptyInner(dfa, Nil(), input, findLongestMatchInner(dfa, dfa.startState, Nil(), input)._1, dfa.startState)

  } ensuring (findLongestMatchInner(dfa, dfa.startState, Nil(), input)._1.isEmpty || matchDFA(dfa, findLongestMatchInner(dfa, dfa.startState, Nil(), input)._1))

  def longestMatchIsAcceptedByMatchOrIsEmptyInner[C](dfa: DFA[C], pastChars: List[C], suffix: List[C], matchedP: List[C], from: State): Unit = {
    require(validDFA(dfa))
    require(moveMultipleSteps(dfa, dfa.startState, pastChars) == from)
    require(findLongestMatchInner(dfa, from, pastChars, suffix)._1 == matchedP)
    decreases(suffix.size)

    if (suffix.isEmpty) {
      if (dfa.finalStates.contains(from)) {
        ListUtils.lemmaConcatTwoListThenFirstIsPrefix(pastChars, suffix)
        assert(matchedP == pastChars)
        assert(suffix.isEmpty)
        assert(findLongestMatchInner(dfa, from, pastChars, suffix)._1 == matchedP)
        findLongestMatchFromItThenFromSmaller(dfa, pastChars ++ suffix, pastChars, suffix, Nil(), pastChars ++ suffix)
        ()
      } else {
        ()
      }
    } else {

      val nextChar = suffix.head

      val newPrefix = pastChars ++ List(nextChar)
      val newSuffix = suffix.tail

      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(pastChars, suffix)
      ListUtils.lemmaAddHeadSuffixToPrefixStillPrefix(pastChars, pastChars ++ suffix)

      ListUtils.lemmaTwoListsConcatAssociativity(pastChars, List(nextChar), newSuffix)
      ListUtils.lemmaSubseqRefl(dfa.transitions)

      val nextState = moveOneStep(dfa, dfa.transitions, from, nextChar)

      lemmaMoveOneStepAfterMultipleIsSameAsMultipleWithNewChar(dfa, dfa.startState, pastChars, nextChar)

      val recursive = findLongestMatchInner(dfa, nextState, newPrefix, newSuffix)

      if (dfa.finalStates.contains(from)) {
        if (recursive._1.size > pastChars.size) {
          // recursive
          longestMatchIsAcceptedByMatchOrIsEmptyInner(dfa, newPrefix, newSuffix, matchedP, nextState)
          ()
        } else {
          ListUtils.lemmaConcatTwoListThenFirstIsPrefix(newPrefix, newSuffix)
          assert(ListUtils.isPrefix(newPrefix, newPrefix ++ newSuffix))
          assert(ListUtils.isPrefix(newPrefix, pastChars ++ suffix))

          assert(findLongestMatchInner(dfa, from, pastChars, suffix)._1 == matchedP)
          assert(pastChars.size == matchedP.size)
          assert(pastChars == matchedP)
          findLongestMatchFromItThenSameWithoutSuffixSame(dfa, pastChars ++ suffix, pastChars, suffix)
          findLongestMatchFromItThenFromSmaller(dfa, pastChars, pastChars, Nil(), Nil(), pastChars)
          // (pastChars, suffix)
          ()
        }
      } else {
        // recursive
        ListUtils.lemmaConcatTwoListThenFirstIsPrefix(newPrefix, newSuffix)
        longestMatchIsAcceptedByMatchOrIsEmptyInner(dfa, newPrefix, newSuffix, matchedP, nextState)
        ()
      }
    }

  } ensuring (matchedP.isEmpty || matchDFA(dfa, matchedP))

  def longestMatchNoBiggerStringMatch[C](dfa: DFA[C], input: List[C], returnP: List[C], bigger: List[C]): Unit = {
    require(validDFA(dfa))
    require(ListUtils.isPrefix(returnP, input))
    require(ListUtils.isPrefix(bigger, input))
    require(bigger.size >= returnP.size)
    require(findLongestMatchInner(dfa, dfa.startState, Nil(), input)._1 == returnP)

    if (bigger.size == returnP.size) {
      ListUtils.lemmaIsPrefixSameLengthThenSameList(bigger, returnP, input)
      ()
    } else {
      if (matchDFA(dfa, bigger)) {
        lemmaKnownAcceptedStringFromSmallerPrefixThenAtLeastThat(dfa, input, Nil(), input, bigger)
        check(false)
      }
    }

  } ensuring (bigger == returnP || !matchDFA(dfa, bigger))

  def lemmaKnownAcceptedStringFromSmallerPrefixThenAtLeastThat[C](dfa: DFA[C], input: List[C], testedP: List[C], testedSuffix: List[C], knownP: List[C]): Unit = {
    require(validDFA(dfa))
    require(ListUtils.isPrefix(knownP, input))
    require(ListUtils.isPrefix(testedP, input))
    require(testedP ++ testedSuffix == input)
    require(testedP.size <= knownP.size)
    require(matchDFA(dfa, knownP))
    decreases(testedSuffix.size)

    if (testedP.size == knownP.size) {
      ListUtils.lemmaIsPrefixSameLengthThenSameList(testedP, knownP, input)
      assert(testedP == knownP)
      lemmaFindLongestMatchStartFromStartSmallerPrefixThanResultSame(dfa, testedP, testedP, Nil(), testedP, Nil())
      assert(findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, testedP), testedP, Nil())._1 == testedP)

      assert(findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, testedP), testedP, Nil())._1 == testedP)
      lemmaFindLongestMatchWithAddedSuffixReturnedBiggerOrEqualMatch(dfa, knownP, testedSuffix)

      assert(findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, testedP), testedP, testedSuffix)._1.size >= knownP.size)
    } else {
      val newTestedP = testedP ++ List(testedSuffix.head)
      val newTestedS = testedSuffix.tail
      ListUtils.lemmaTwoListsConcatAssociativity(testedP, List(testedSuffix.head), newTestedS)
      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(newTestedP, newTestedS)
      lemmaKnownAcceptedStringFromSmallerPrefixThenAtLeastThat(dfa, input, newTestedP, newTestedS, knownP)
    }

  } ensuring (findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, testedP), testedP, testedSuffix)._1.size >= knownP.size)

  def lemmaFindLongestMatchWithAddedSuffixReturnedBiggerOrEqualMatch[C](dfa: DFA[C], longestM: List[C], newSuffix: List[C]): Unit = {
    require(validDFA(dfa))
    require(findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, longestM), longestM, Nil())._1 == longestM)

    val from = moveMultipleSteps(dfa, dfa.startState, longestM)

    if (newSuffix.isEmpty) {
      if (dfa.finalStates.contains(from)) {
        ListUtils.lemmaConcatTwoListThenFirstIsPrefix(longestM, newSuffix)
        // (longestM, newSuffix)
        ()
      } else {
        ()
      }
    } else {
      val nextChar = newSuffix.head

      val newPrefix = longestM ++ List(nextChar)
      val newSuffixIn = newSuffix.tail

      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(longestM, newSuffix)
      ListUtils.lemmaAddHeadSuffixToPrefixStillPrefix(longestM, longestM ++ newSuffix)

      ListUtils.lemmaTwoListsConcatAssociativity(longestM, List(nextChar), newSuffixIn)
      ListUtils.lemmaSubseqRefl(dfa.transitions)

      val nextState = moveOneStep(dfa, dfa.transitions, from, nextChar)

      lemmaMoveOneStepAfterMultipleIsSameAsMultipleWithNewChar(dfa, dfa.startState, longestM, nextChar)

      val recursive = findLongestMatchInner(dfa, nextState, newPrefix, newSuffixIn)

      if (dfa.finalStates.contains(from)) {
        if (recursive._1.size > longestM.size) {
          ()
          // recursive
        } else {
          ListUtils.lemmaConcatTwoListThenFirstIsPrefix(newPrefix, newSuffixIn)
          assert(ListUtils.isPrefix(newPrefix, newPrefix ++ newSuffixIn))
          assert(ListUtils.isPrefix(newPrefix, longestM ++ newSuffix))
          // (longestM, newSuffix)
          ()
        }
      } else {
        // recursive
        ()
      }
    }

  } ensuring (findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, longestM), longestM, newSuffix)._1.size >= longestM.size)

  def findLongestMatchFromItThenFromSmaller[C](dfa: DFA[C], input: List[C], longestM: List[C], suffix: List[C], smallerP: List[C], smallerPSuffix: List[C]): Unit = {
    require(validDFA(dfa))
    require(longestM ++ suffix == input)
    require(smallerP ++ smallerPSuffix == input)
    require(smallerP.size <= longestM.size)
    require(findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, longestM), longestM, suffix)._1 == longestM)
    decreases(smallerPSuffix.size)

    if (smallerP.size == longestM.size) {
      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(smallerP, smallerPSuffix)
      ListUtils.lemmaIsPrefixSameLengthThenSameList(smallerP, longestM, input)
      ListUtils.lemmaSamePrefixThenSameSuffix(smallerP, smallerPSuffix, longestM, suffix, input)
      ()
    } else {
      val newSmallerP = smallerP ++ List(smallerPSuffix.head)
      val newSmallerPSuff = smallerPSuffix.tail
      ListUtils.lemmaTwoListsConcatAssociativity(smallerP, List(smallerPSuffix.head), newSmallerPSuff)
      findLongestMatchFromItThenFromSmaller(dfa, input, longestM, suffix, newSmallerP, newSmallerPSuff)
      assert(findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, newSmallerP), newSmallerP, newSmallerPSuff)._1 == longestM)

      // findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, smallerP), smallerP, smallerPSuffix) ==

      val from = moveMultipleSteps(dfa, dfa.startState, smallerP)
      if (smallerPSuffix.isEmpty) {
        check(false)

      } else {

        val nextChar = smallerPSuffix.head

        val newPrefix = smallerP ++ List(nextChar)
        val newSuffix = smallerPSuffix.tail

        assert(newPrefix == newSmallerP)
        assert(newSmallerPSuff == newSuffix)

        ListUtils.lemmaConcatTwoListThenFirstIsPrefix(smallerP, smallerPSuffix)
        ListUtils.lemmaAddHeadSuffixToPrefixStillPrefix(smallerP, smallerP ++ smallerPSuffix)

        ListUtils.lemmaTwoListsConcatAssociativity(smallerP, List(nextChar), newSuffix)
        ListUtils.lemmaSubseqRefl(dfa.transitions)

        val nextState = moveOneStep(dfa, dfa.transitions, from, nextChar)

        lemmaMoveOneStepAfterMultipleIsSameAsMultipleWithNewChar(dfa, dfa.startState, smallerP, nextChar)

        val recursive = findLongestMatchInner(dfa, nextState, newPrefix, newSuffix)

        assert(recursive == findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, newSmallerP), newSmallerP, newSmallerPSuff))

        assert(recursive._1.size > smallerP.size)
        if (dfa.finalStates.contains(from)) {
          if (recursive._1.size > smallerP.size) {
            assert(findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, smallerP), smallerP, smallerPSuffix) == recursive)
            // recursive
          } else {
            ListUtils.lemmaConcatTwoListThenFirstIsPrefix(newPrefix, newSuffix)
            assert(ListUtils.isPrefix(newPrefix, newPrefix ++ newSuffix))
            assert(ListUtils.isPrefix(newPrefix, smallerP ++ smallerPSuffix))
            check(false)
            // (smallerP, smallerPSuffix)
          }
        } else {
          // recursive
        }
        assert(findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, smallerP), smallerP, smallerPSuffix) == recursive)
      }
      assert(findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, smallerP), smallerP, smallerPSuffix)._1 == longestM) // TODO
      ()
    }

  } ensuring (findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, smallerP), smallerP, smallerPSuffix)._1 == longestM)

  def findLongestMatchFromItThenSameWithoutSuffixSame[C](dfa: DFA[C], input: List[C], longestM: List[C], suffix: List[C]): Unit = {
    require(validDFA(dfa))
    require(longestM ++ suffix == input)
    require(findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, longestM), longestM, suffix)._1 == longestM)
  } ensuring (findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, longestM), longestM, Nil())._1 == longestM)

  @opaque
  @inlineOnce
  def lemmaFindLongestMatchStartFromStartSmallerPrefixThanResultSame[C](
      dfa: DFA[C],
      input: List[C],
      longestM: List[C],
      suffix: List[C],
      smallerP: List[C],
      smallerPSuffix: List[C]
  ): Unit = {
    require(validDFA(dfa))
    require(longestM ++ suffix == input)
    require(smallerP ++ smallerPSuffix == input)
    require(smallerP.size <= longestM.size)
    require(findLongestMatchInner(dfa, dfa.startState, Nil(), input)._1 == longestM)
    decreases(smallerPSuffix.size)

    if (smallerP.isEmpty) {
      ()
    } else {
      if (smallerP.size == longestM.size) {
        ListUtils.lemmaConcatTwoListThenFirstIsPrefix(smallerP, smallerPSuffix)
        ListUtils.lemmaIsPrefixSameLengthThenSameList(smallerP, longestM, input)
        assert(smallerP == longestM)
        lemmaFindLongestKnownPFromSmallerThenFromIt(dfa, input, longestM, suffix, Nil(), input)
        ListUtils.lemmaSamePrefixThenSameSuffix(smallerP, smallerPSuffix, longestM, suffix, input)
        assert(findLongestMatchInner(dfa, dfa.startState, Nil(), input)._1 == findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, longestM), longestM, suffix)._1)
      } else {
        val newSmallerP = smallerP ++ List(smallerPSuffix.head)
        val newSmallerPSuff = smallerPSuffix.tail
        ListUtils.lemmaTwoListsConcatAssociativity(smallerP, List(smallerPSuffix.head), newSmallerPSuff)
        lemmaFindLongestMatchStartFromStartSmallerPrefixThanResultSame(dfa, input, longestM, suffix, newSmallerP, newSmallerPSuff)
      }
    }

  } ensuring (findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, smallerP), smallerP, smallerPSuffix)._1 == longestM)

  @opaque
  @inlineOnce
  def lemmaFindLongestKnownPFromSmallerThenFromIt[C](dfa: DFA[C], input: List[C], longestM: List[C], suffix: List[C], smallerP: List[C], smallerPSuffix: List[C]): Unit = {
    require(validDFA(dfa))
    require(longestM ++ suffix == input)
    require(smallerP ++ smallerPSuffix == input)
    require(smallerP.size <= longestM.size)
    require(findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, smallerP), smallerP, smallerPSuffix)._1 == longestM)
    decreases(smallerPSuffix.size)

    if (longestM.size == smallerP.size) {
      ListUtils.lemmaIsPrefixSameLengthThenSameList(smallerP, longestM, input)
      ListUtils.lemmaSamePrefixThenSameSuffix(smallerP, smallerPSuffix, longestM, suffix, input)
      ()
    } else {
      val newSmallerP = smallerP ++ List(smallerPSuffix.head)
      val newSmallerPSuff = smallerPSuffix.tail
      ListUtils.lemmaTwoListsConcatAssociativity(smallerP, List(smallerPSuffix.head), newSmallerPSuff)
      lemmaFindLongestKnownPFromSmallerThenFromIt(dfa, input, longestM, suffix, newSmallerP, newSmallerPSuff)
    }

  } ensuring (findLongestMatchInner(dfa, moveMultipleSteps(dfa, dfa.startState, longestM), longestM, suffix)._1 == longestM)

}
