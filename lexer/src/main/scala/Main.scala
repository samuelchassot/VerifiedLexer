import lexer.VerifiedFunLexer._
import lexer.RegularExpression._
import lexer.VerifiedRegexMatcher._
import lexer.VerifiedNFAMatcher._
import lexer.VerifiedNFA._

import lexer.VerifiedFunLexer
import lexer.RegularExpression
import lexer.VerifiedRegexMatcher
import lexer.VerifiedNFAMatcher
import lexer.VerifiedNFA
import stainless.collection._

object Main extends App {
  def main(): Unit = {
    NFATests.tests()
  }
  main()
}

object NFATests {
  def matchManual(): Unit = {
    val r = Star(ElementMatch('a'))
    val nfa = fromRegexToNfa(r)
    println("Epsilon closure from 4: " + epsilonClosure(nfa, List(VerifiedNFA.State("4"))))
    println("Epsilon closure from epsilon from 4: " + epsilonClosure(nfa, epsilonClosure(nfa, List(VerifiedNFA.State("4")))))

    val input = List('a')
    val suffix = input
    val pastChars = Nil[Char]()
    val currentStatesEpsilonClosure = epsilonClosure(nfa, List(nfa.startState), Nil())

    println("CLOSURE 1: " + currentStatesEpsilonClosure)

    val nextChar = suffix.head
    val newPastChars = pastChars ++ List(nextChar)
    val newSuffix = suffix.tail
    val afterConsumingNextChar = readOneChar(nfa, nfa.transitions, currentStatesEpsilonClosure, nextChar)

    assert(afterConsumingNextChar.forall(s => nfa.allStates.contains(s)))

    println("AFTER Consuming char " + nextChar + " : " + afterConsumingNextChar)

    val afterEpsilon = epsilonClosure(nfa, afterConsumingNextChar)

    println("CLOSURE 2: " + afterEpsilon)

    println("MATCH FUCNTION: " + matchNFA(nfa, input))

  }
  def tests(): Unit = {
    def testNfaEpsilonClosureClosed(r: Regex[Char]): Boolean = {
      val nfa = fromRegexToNfa(r)
      val states = nfa.allStates
      states
        .map(s => {
          val epsilonFromS = epsilonClosure(nfa, List(s), Nil())
          val again = epsilonClosure(nfa, epsilonFromS, Nil())
          epsilonFromS.content == again.content
        })
        .foldLeft(true)((a, b) => a && b)
    }
    def testNfaMatch(testValues: List[List[Char]], r: Regex[Char]): Boolean = {
      def testOneValue(v: List[Char], r: Regex[Char]): Boolean = {
        println(
          "\n\nTEST BEGIN ----------------------------------------------------------------\n"
        )
        println("testing string: " + v)

        // DEBUG START ----------------------------------------------------------------
        println("\nDEBUG regex: " + r)
        val nfa = fromRegexToNfa(r)
        println("\nDEBUG nfa: " + nfa + "\n")

        // DEBUG END ------------------------------------------------------------------
        val matchRegex1 = VerifiedRegexMatcher.matchR(r, v)
        val matchNfa1 =
          VerifiedNFAMatcher.matchNFA(fromRegexToNfa(r), v)
        println("matched against regex: " + matchRegex1)
        println("matched against nfa: " + matchNfa1)
        val result = (matchRegex1 == matchNfa1)
        println("\n!!!!!!!!!!!!!!!!!!!!!!!!!!!! equal = " + result.toString)
        result
      }
      testValues match {
        case Cons(hd, tl) => testOneValue(hd, r) && testNfaMatch(tl, r)
        case Nil()        => true
      }
    }
    val r1 = Star(
      Union(
        Concat(Concat(ElementMatch('a'), ElementMatch('b')), Star(Concat(ElementMatch('a'), ElementMatch('b')))),
        Concat(ElementMatch('c'), Concat(ElementMatch('d'), ElementMatch('e')))
      )
    )
    val stringList1 = List(
      List('a', 'b', 'a', 'b'),
      List('a', 'b', 'a', 'b', 'c', 'd', 'e', 'c', 'd', 'e', 'c', 'd', 'e', 'a', 'b', 'a', 'b'),
      List('a', 'b', 'a', 'b', 'c', 'd', 'e', 'c', 'd', 'e', 'c', 'd', 'e', 'a', 'b', 'a', 'b', 'g', 'g', 'g'),
      List('a', 'b', 'a', 'b', 'c', 'd', 'e', 'c', 'd', 'e', 'c', 'd', 'e', 'a', 'b', 'a', 'b', 'a'),
      List('c', 'd', 'e', 'c', 'd', 'e'),
      List[Char](),
      List('a', 'b', 'a', 'b', 'a'),
      List('a', 'b', 'c', 'd', 'e'),
      List('a', 'c', 'd', 'b'),
      List('a', 'b', 'c', 'd', 'e', 'a', 'a', 'a', 'c', 'd', 'e')
    )

    val testResult1 = testNfaMatch(stringList1, r1)

    val r2 = Star(
      Union(
        Concat(
          Union(Concat(ElementMatch('a'), ElementMatch('b')), ElementMatch('f')),
          Star(
            Union(Concat(ElementMatch('a'), ElementMatch('b')), ElementMatch('f'))
          )
        ),
        Concat(ElementMatch('c'), Concat(ElementMatch('d'), ElementMatch('e')))
      )
    )
    val stringList2 = List(
      List('a', 'b', 'a', 'b'),
      List('a', 'b', 'a', 'b', 'c', 'd', 'e', 'c', 'd', 'e', 'c', 'd', 'e', 'a', 'b', 'a', 'b'),
      List('a', 'b', 'a', 'b', 'c', 'd', 'e', 'c', 'd', 'e', 'c', 'd', 'e', 'a', 'b', 'a', 'b', 'g', 'g', 'g'),
      List('a', 'b', 'a', 'b', 'c', 'd', 'e', 'c', 'd', 'e', 'c', 'd', 'e', 'a', 'b', 'a', 'b', 'a'),
      List('c', 'd', 'e', 'c', 'd', 'e'),
      List[Char](),
      List('a', 'b', 'a', 'b', 'a'),
      List('a', 'b', 'c', 'd', 'e'),
      List('a', 'c', 'd', 'b'),
      List('a', 'b', 'c', 'd', 'e', 'a', 'a', 'a', 'c', 'd', 'e'),
      List('a', 'b', 'a', 'b'),
      List('a', 'b', 'a', 'b', 'f', 'f', 'c', 'd', 'e', 'c', 'd', 'e', 'c', 'd', 'e', 'a', 'b', 'a', 'b'),
      List('a', 'b', 'a', 'b', 'c', 'd', 'e', 'c', 'd', 'e', 'c', 'd', 'e', 'a', 'b', 'a', 'b', 'g', 'g', 'g', 'f', 'f'),
      List('f', 'f', 'a', 'b', 'a', 'b', 'c', 'd', 'e', 'c', 'd', 'e', 'c', 'd', 'e', 'a', 'b', 'a', 'b', 'a'),
      List('f', 'f', 'c', 'd', 'e', 'c', 'd', 'e'),
      List('a', 'b', 'a', 'b', 'a', 'f', 'f'),
      List('a', 'b', 'c', 'd', 'e', 'f'),
      List('a', 'c', 'f', 'f', 'd', 'b'),
      List('a', 'b', 'f', 'a', 'b', 'f', 'c', 'd', 'e', 'a', 'a', 'a', 'c', 'd', 'e')
    )

    val testResult2 = testNfaMatch(stringList2, r2)

    val r3 = Star(ElementMatch('a'))
    val stringList3 = List(
      List[Char](),
      List('a'),
      List('a', 'a'),
      List('a', 'a', 'a', 'a', 'a', 'a', 'a', 'a', 'a', 'a', 'a', 'a', 'a', 'a'),
      List('a', 'b'),
      List('a', 'a', 'a', 'a', 'a', 'a', 'a', 'a', 'a', 'a', 'a', 'a', 'a', 'a', 'b'),
      List('a', 'a', 'a', 'a', 'a', 'a', 'a', 'a', 'a', 'b', 'a', 'a', 'a', 'a', 'a')
    )

    val testResult3 = testNfaMatch(stringList3, r3)

    val r4 = Concat(ElementMatch('a'), ElementMatch('b'))
    val stringList4 = List(
      List[Char](),
      List('a', 'b'),
      List('a'),
      List('a', 'b', 'a', 'b', 'a', 'b', 'a', 'b', 'a', 'b', 'a', 'b', 'a', 'b'),
      List('a', 'b', 'a', 'b', 'a', 'b', 'a', 'b', 'a', 'b', 'a', 'b', 'a', 'a'),
      List('a', 'b', 'a', 'b', 'a', 'b', 'a', 'b', 'a', 'b', 'a', 'b', 'a', 'b', 'a')
    )

    val testResult4 = testNfaMatch(stringList4, r4)

    println("TESTS RESULT 1 = " + testResult1.toString)
    println("TESTS RESULT 2 = " + testResult2.toString)
    println("TESTS RESULT 3 = " + testResult3.toString)
    println("TESTS RESULT 4 = " + testResult4.toString)

    println("TESTS NFA EPSILON CLOSURE")

    println("closure TESTS RESULT 1 = " + testNfaEpsilonClosureClosed(r1))
    println("closure TESTS RESULT 2 = " + testNfaEpsilonClosureClosed(r2))
    println("closure TESTS RESULT 3 = " + testNfaEpsilonClosureClosed(r3))
    println("closure TESTS RESULT 4 = " + testNfaEpsilonClosureClosed(r4))
  }
}
