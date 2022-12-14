/** Author: Samuel Chassot
  */

import stainless.annotation._
import stainless.collection._
import stainless.equations._
import stainless.lang._
import stainless.proof.check
import scala.annotation.tailrec
import scala.collection.immutable.Range.BigInt.apply

object MainTest {
  import VerifiedFunLexer._
  // import ComputableLanguage._
  import RegularExpression._
  import VerifiedRegexMatcher._
  import VerifiedNFAMatcher._
  import VerifiedNFA._
  import stainless.io.StdOut.println
  import stainless.io.State
  // import VerifiedNFA._
  import VerifiedFunLexer._
  @extern
  def main(args: Array[String]): Unit = {
    val rSep = ElementMatch(' ')
    val ruleSep = Rule(rSep, "sep", true)
    val sepToken = Token(List(' '), "sep", true)

    val rAb = Concat(Concat(ElementMatch('a'), ElementMatch('b')), Star(Concat(ElementMatch('a'), ElementMatch('b'))))
    val rule = Rule(rAb, "ab", false)

    val rC = Concat(ElementMatch('c'), Star(ElementMatch('c')))
    val ruleC = Rule(rC, "c", false)

    val t1 = Token(List('a', 'b'), "ab", false)
    val t2 = Token(List('c', 'c'), "c", false)

    val input: List[Token[Char]] = List(t1, t2, t1, t2, t1, t1)
    val rules = List(rule, ruleC, ruleSep)

    // Regex to NFA tests
    val state = State(BigInt(1))

    val output: List[Char] = Lexer.printWithSeparatorTokenWhenNeeded(rules, input, sepToken)
    println(output.foldLeft("")((s: String, c: Char) => s + c.toString))(state)
    // NFATests()(state)

  }
  @extern
  def NFATests()(implicit @ghost state: State): Unit = {

    def testNfaMatch(testValues: List[List[Char]], r: Regex[Char])(implicit @ghost state: State): Boolean = {
      def testOneValue(v: List[Char], r: Regex[Char])(implicit @ghost state: State): Boolean = {
        println("testing string: " + v)
        val longestMatchRegex1 = VerifiedRegexMatcher.findLongestMatch(r, v)
        val longestMatchNfa1 = VerifiedNFAMatcher.findLongestMatch(fromRegexToNfa(r), v)
        println("matched against regex: " + longestMatchRegex1)
        println("matched against nfa: " + longestMatchNfa1)
        val result = (longestMatchRegex1 == longestMatchNfa1)
        println("equal = " + result.toString)
        result
      }
      testValues match {
        case Cons(hd, tl) => testOneValue(hd, r) && testNfaMatch(tl, r)
        case Nil()        => true
      }
    }
    val r1 = Star(Union(Star(Concat(ElementMatch('a'), ElementMatch('b'))), Concat(ElementMatch('c'), Concat(ElementMatch('d'), ElementMatch('e')))))
    println(fromRegexToNfa(r1))
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
        Star(
          Union(Concat(ElementMatch('a'), ElementMatch('b')), ElementMatch('f'))
        ),
        Concat(ElementMatch('c'), Concat(ElementMatch('d'), ElementMatch('e')))
      )
    )
    println(fromRegexToNfa(r2))
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

    println("TESTS RESULT 1 = " + testResult1.toString)
    println("TESTS RESULT 2 = " + testResult2.toString)
  }

}
object VerifiedFunLexer {
  import RegularExpression._
  import VerifiedRegexMatcher._

  case class Token[C](characters: List[C], tag: String, isSep: Boolean) {
    def getCharacters = characters
    def getTag = tag
    def isSeparator = isSep
  }
  case class Rule[C](regex: Regex[C], tag: String, isSeparator: Boolean)

  object Lexer {

    @inline
    def ruleValid[C](r: Rule[C]): Boolean = {
      validRegex(r.regex) && !nullable(r.regex) && r.tag != ""
    }
    def noDuplicateTag[C](rules: List[Rule[C]], acc: List[String] = Nil()): Boolean = rules match {
      case Nil()        => true
      case Cons(hd, tl) => !acc.contains(hd.tag) && noDuplicateTag(tl, Cons(hd.tag, acc))
    }
    def rulesValid[C](rs: List[Rule[C]]): Boolean = {
      rs match {
        case Cons(hd, tl) => ruleValid(hd) && rulesValid(tl)
        case Nil()        => true
      }
    }

    def rulesProduceIndivualToken[C](rs: List[Rule[C]], t: Token[C]): Boolean = {
      require(!rs.isEmpty)
      require(rulesInvariant(rs))
      val (producedTs, suffix) = lex(rs, print(List(t)))
      producedTs.size == 1 && producedTs.head == t && suffix.isEmpty
    }

    def rulesProduceEachTokenIndividually[C](rs: List[Rule[C]], ts: List[Token[C]]): Boolean = {
      require(!rs.isEmpty)
      require(rulesInvariant(rs))
      ts match {
        case Cons(hd, tl) => rulesProduceIndivualToken(rs, hd) && rulesProduceEachTokenIndividually(rs, tl)
        case Nil()        => true
      }
    }

    def tokensUseDisjointCharsFromFirstCharsNextToken[C](rules: List[Rule[C]], tokens: List[Token[C]]): Boolean = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rulesProduceEachTokenIndividually(rules, tokens))
      decreases(tokens.size)

      lemmaRulesProduceEachTokenIndividuallyThenForall(rules, tokens)

      tokens match {
        case Cons(t1, Cons(t2, tl)) => {
          ListSpecs.forallContained(tokens, (t: Token[C]) => rulesProduceIndivualToken(rules, t), t1)
          lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, t1.getCharacters, t1)
          ListSpecs.forallContained(tokens, (t: Token[C]) => rulesProduceIndivualToken(rules, t), t2)
          lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, t2.getCharacters, t2)
          val r1 = getRuleFromTag(rules, t1.getTag).get
          val r2 = getRuleFromTag(rules, t2.getTag).get
          rulesFirstCharsAreNotUsedByTokenBefore(r1, r2) && tokensUseDisjointCharsFromFirstCharsNextToken(rules, Cons(t2, tl))
        }
        case _ => true // 1 or 0 token in the list
      }
    }

    def sepAndNonSepRulesDisjointChars[C](rules: List[Rule[C]], rulesRec: List[Rule[C]]): Boolean = {
      rulesRec match {
        case Cons(hd, tl) => ruleDisjointCharsFromAllFromOtherType(hd, rules) && sepAndNonSepRulesDisjointChars(rules, tl)
        case Nil()        => true
      }
    }

    def ruleDisjointCharsFromAllFromOtherType[C](r: Rule[C], rules: List[Rule[C]]): Boolean = {
      rules match {
        case Cons(hd, tl) if hd.isSeparator != r.isSeparator => rulesUseDisjointChars(r, hd) && ruleDisjointCharsFromAllFromOtherType(r, tl)
        case Cons(hd, tl)                                    => ruleDisjointCharsFromAllFromOtherType(r, tl)
        case Nil()                                           => true
      }

    }
    def rulesUseDisjointChars[C](r1: Rule[C], r2: Rule[C]): Boolean = {
      usedCharacters(r2.regex).forall(c => !usedCharacters(r1.regex).contains(c)) &&
      usedCharacters(r1.regex).forall(c => !usedCharacters(r2.regex).contains(c))
    }

    def rulesFirstCharsAreNotUsedByTokenBefore[C](r1: Rule[C], r2: Rule[C]): Boolean = {
      firstChars(r2.regex).forall(c => !usedCharacters(r1.regex).contains(c))
    }

    @inline
    def rulesInvariant[C](rules: List[Rule[C]]): Boolean =
      rulesValid(rules) && noDuplicateTag(rules, Nil())

    /** Main function of the lexer
      *
      * It lexes the input list of characters using the set of rules
      *
      * It returns the produced list of Tokens and the remaining untokenised characters (normally empty)
      *
      * @param rules
      * @param input
      */
    def lex[C](
        rules: List[Rule[C]],
        input: List[C]
    ): (List[Token[C]], List[C]) = {
      decreases(input.size)
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      val ret: (List[Token[C]], List[C]) = findMaxPrefix(rules, input) match {
        case Some((token, suffix)) => {
          val (followingTokens, nextSuffix) = lex(rules, suffix)
          assert(token.getCharacters ++ suffix == input)
          (Cons(token, followingTokens), nextSuffix)
        }
        case None() => (Nil(), input)
      }
      ret
    } ensuring (res =>
      if (res._1.size > 0) res._2.size < input.size && !res._1.isEmpty
      else res._2 == input
    )

    /** Prints back the tokens to a list of characters of the type C
      *
      * @param l
      */
    def print[C](l: List[Token[C]]): List[C] = {
      l match {
        case Cons(hd, tl) => hd.getCharacters ++ print(tl)
        case Nil()        => Nil[C]()
      }
    }

    /** Prints back the tokens to a list of characters of the type C, by adding a separatorToken between all of them, and after the last
      *
      * @param l
      * @param separatorToken
      */
    def printWithSeparatorToken[C](l: List[Token[C]], separatorToken: Token[C]): List[C] = {
      require(separatorToken.isSeparator)
      l match {
        case Cons(hd, tl) => hd.getCharacters ++ separatorToken.getCharacters ++ printWithSeparatorToken(tl, separatorToken)
        case Nil()        => Nil[C]()
      }
    }

    /** Prints back the tokens to a list of characters of the type C, by adding a separatorToken between tokens when the findMaxPrefix would return another token if printed back to
      * back.
      *
      * @param l
      * @param separatorToken
      */
    def printWithSeparatorTokenWhenNeeded[C](rules: List[Rule[C]], l: List[Token[C]], separatorToken: Token[C]): List[C] = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rulesProduceEachTokenIndividually(rules, l))
      require(rulesProduceIndivualToken(rules, separatorToken))
      require(separatorToken.isSeparator)
      require(l.forall(!_.isSeparator))
      require(sepAndNonSepRulesDisjointChars(rules, rules))

      l match {
        case Cons(hd, tl) => {
          val suffix = printWithSeparatorTokenWhenNeeded(rules, tl, separatorToken)
          val maxPrefWithoutSep = findMaxPrefix(rules, hd.getCharacters ++ suffix)
          maxPrefWithoutSep match {
            case Some((t, s)) if t == hd => hd.getCharacters ++ suffix
            case Some((t, s)) if t != hd => hd.getCharacters ++ separatorToken.getCharacters ++ suffix
            case None() => {
              lemmaLexIsDefinedWithStrThenLexWithSuffixIsDefined(rules, hd.getCharacters, suffix)
              check(false)
              Nil[C]()
            }
          }
        }
        case Nil() => Nil[C]()
      }
    }

    /** Finds the biggest prefix matching any rule in the input list of characters If nothing matched a rule, returns None Else, returns the matched prefix as Token and the
      * remaining suffix
      *
      * @param rulesArg
      * @param input
      */
    def findMaxPrefix[C](
        rulesArg: List[Rule[C]],
        input: List[C]
    ): Option[(Token[C], List[C])] = {
      require(rulesValid(rulesArg))
      require(!rulesArg.isEmpty)
      decreases(rulesArg.size)

      ListUtils.lemmaIsPrefixRefl(input, input)
      val ret: Option[(Token[C], List[C])] = rulesArg match {
        case Cons(hd, Nil()) => findMaxPrefixOneRule(hd, input)
        case Cons(hd, tl) => {
          val currentRulePref = findMaxPrefixOneRule(hd, input)
          val othersPrefix = findMaxPrefix(tl, input)
          (currentRulePref, othersPrefix) match {
            case (None(), None())                                                         => None()
            case (c, None())                                                              => c
            case (None(), o)                                                              => o
            case (Some(c), Some(o)) if c._1.getCharacters.size >= o._1.getCharacters.size => Some(c)
            case (Some(c), Some(o)) if c._1.getCharacters.size < o._1.getCharacters.size  => Some(o)
          }
        }
      }
      ret
    } ensuring (res => res.isEmpty || res.isDefined && (res.get._2.size < input.size && res.get._1.getCharacters ++ res.get._2 == input))

    /** Finds the biggest prefix matching any rule in the input list of characters If nothing matched a rule, returns None Else, returns the matched prefix and the remaining suffix
      *
      * @param rule
      * @param input
      */
    def findMaxPrefixOneRule[C](
        rule: Rule[C],
        input: List[C]
    ): Option[(Token[C], List[C])] = {
      require(ruleValid(rule))

      val (longestPrefix, suffix) = findLongestMatch(rule.regex, input)
      if (longestPrefix.isEmpty) {
        None[(Token[C], List[C])]()
      } else {
        longestMatchIsAcceptedByMatchOrIsEmpty(rule.regex, input)
        Some[(Token[C], List[C])]((Token(longestPrefix, rule.tag, rule.isSeparator), suffix))
      }

    } ensuring (res =>
      res.isEmpty || matchR(
        rule.regex,
        res.get._1.getCharacters
      ) && res.get._1.getCharacters ++ res.get._2 == input && res.get._2.size < input.size && res.get._1.getTag == rule.tag && res.get._1.isSeparator == rule.isSeparator
    )

    // Proofs --------------------------------------------------------------------------------------------------------------------------------

    // Correctness ---------------------------------------------------------------------------------------------------------------------------

    // The lexer is sound, i.e., if it produces a Tokenisation, it is valid w.r.t. the biggest prefix property
    def theoremLexIsSoundFirstChar[C](
        rules: List[Rule[C]],
        input: List[C],
        suffix: List[C],
        tokens: List[Token[C]],
        r: Rule[C],
        otherR: Rule[C],
        otherP: List[C]
    ): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rules.contains(r))
      require(rules.contains(otherR))
      require(lex(rules, input) == (tokens, suffix))

      require(tokens.isEmpty || tokens.head.getCharacters.size <= otherP.size)
      require(tokens.isEmpty || tokens.head.getTag == r.tag)
      require(tokens.isEmpty || tokens.head.isSeparator == r.isSeparator)
      require(ListUtils.isPrefix(otherP, input))
      require(r != otherR)
      val _ = lemmaRuleInListAndRulesValidThenRuleIsValid(r, rules)
      require(tokens.isEmpty || matchR(r.regex, tokens.head.getCharacters))

      lemmaRuleInListAndRulesValidThenRuleIsValid(otherR, rules)
      if (ListUtils.getIndex(rules, r) > ListUtils.getIndex(rules, otherR)) {

        tokens match {
          case Nil() => {
            lemmaMaxPrefixReturnsNoneThenAnyRuleReturnsNone(otherR, rules, input)
            lemmaMaxPrefOneRuleReturnsNoneThenNoPrefMaxRegex(otherR, otherP, input)
          }
          case Cons(hd, tl) => {
            val (tok, suf) = findMaxPrefix(rules, input).get
            assert(hd == tok)
            ListUtils.lemmaConcatTwoListThenFirstIsPrefix(hd.getCharacters, suf)
            ListUtils.lemmaSamePrefixThenSameSuffix(hd.getCharacters, suf, hd.getCharacters, ListUtils.getSuffix(input, hd.getCharacters), input)
            if (otherP.size == hd.getCharacters.size) {
              ListUtils.lemmaIsPrefixSameLengthThenSameList(hd.getCharacters, otherP, input)
              lemmaMaxPrefNoSmallerRuleMatches(rules, r, hd.getCharacters, input, otherR)
            } else {
              lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(rules, hd.getCharacters, input, suf, r)
              lemmaMaxPrefixOutputsMaxPrefix(rules, r, hd.getCharacters, input, otherP, otherR)
            }
          }
        }
      } else {
        if (ListUtils.getIndex(rules, r) == ListUtils.getIndex(rules, otherR)) {
          ListUtils.lemmaSameIndexThenSameElement(rules, r, otherR)
          check(false)
        }

        tokens match {
          case Nil() => {
            lemmaMaxPrefixReturnsNoneThenAnyRuleReturnsNone(otherR, rules, input)
            lemmaMaxPrefOneRuleReturnsNoneThenNoPrefMaxRegex(otherR, otherP, input)
          }
          case Cons(hd, tl) => {
            val (tok, suf) = findMaxPrefix(rules, input).get
            ListUtils.lemmaConcatTwoListThenFirstIsPrefix(hd.getCharacters, suf)
            ListUtils.lemmaSamePrefixThenSameSuffix(hd.getCharacters, suf, hd.getCharacters, ListUtils.getSuffix(input, hd.getCharacters), input)
            if (otherP.size > hd.getCharacters.size) {
              lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(rules, hd.getCharacters, input, suf, r)
              lemmaMaxPrefixOutputsMaxPrefix(rules, r, hd.getCharacters, input, otherP, otherR)
            }

          }
        }
      }

    } ensuring (if (ListUtils.getIndex(rules, otherR) < ListUtils.getIndex(rules, r)) !matchR(otherR.regex, otherP)
                else tokens.size > 0 && otherP.size <= tokens.head.getCharacters.size || !matchR(otherR.regex, otherP))

    // Invertability -------------------------------------------------------------------------------------------------------------------------

    def theoremInvertabilityFromTokensSepTokenWhenNeeded[C](rules: List[Rule[C]], tokens: List[Token[C]], separatorToken: Token[C]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rulesProduceEachTokenIndividually(rules, tokens))
      require(rulesProduceIndivualToken(rules, separatorToken))
      require(separatorToken.isSeparator)
      require(tokens.forall(!_.isSeparator))
      val _ = lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, separatorToken.getCharacters, separatorToken)
      require(getRuleFromTag(rules, separatorToken.getTag).get.isSeparator)
      require(sepAndNonSepRulesDisjointChars(rules, rules))

      tokens match {
        case Cons(hd, tl) => {
          val input = printWithSeparatorTokenWhenNeeded(rules, tokens, separatorToken)
          val suffixWithSep = separatorToken.getCharacters ++ printWithSeparatorTokenWhenNeeded(rules, tl, separatorToken)
          ListUtils.lemmaTwoListsConcatAssociativity(hd.getCharacters, separatorToken.getCharacters, printWithSeparatorTokenWhenNeeded(rules, tl, separatorToken))
          val suffixWithoutSep = printWithSeparatorTokenWhenNeeded(rules, tl, separatorToken)
          assert(input == hd.getCharacters ++ suffixWithSep || input == hd.getCharacters ++ suffixWithoutSep)

          if (input == hd.getCharacters ++ suffixWithSep) {
            val suffixAfterSep = printWithSeparatorTokenWhenNeeded(rules, tl, separatorToken)
            lemmaPrintWithSepTokenWhenNeededThenFindMaxPrefReturnsHead(rules, tokens, separatorToken)
            ListUtils.lemmaConcatTwoListThenFirstIsPrefix(hd.getCharacters, suffixWithSep)
            ListUtils.lemmaSamePrefixThenSameSuffix(hd.getCharacters, suffixWithSep, hd.getCharacters, findMaxPrefix(rules, input).get._2, input)

            val nextToken = tl.head
            val sepTokenOpt = findMaxPrefix(rules, suffixWithSep)
            if (tl.isEmpty) {
              assert(input == hd.getCharacters ++ separatorToken.getCharacters)
              check(false)
            }
            lemmaRulesProduceEachTokenIndividuallyThenForAnyToken(rules, tokens, nextToken)
            check(rulesProduceIndivualToken(rules, nextToken))
            lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, separatorToken.getCharacters, separatorToken)
            val separatorRule = getRuleFromTag(rules, separatorToken.getTag).get
            lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, tl.head.getCharacters, nextToken)
            val nextTokenRule = getRuleFromTag(rules, nextToken.getTag).get

            if (!usedCharacters(nextTokenRule.regex).contains(nextToken.getCharacters.head)) {
              lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(nextTokenRule.regex, nextToken.getCharacters, nextToken.getCharacters.head)
              check(false)
            }
            if (usedCharacters(separatorRule.regex).contains(suffixAfterSep.head)) {
              lemmaSepRuleNotContainsCharContainedInANonSepRule(rules, rules, nextTokenRule, separatorRule, suffixAfterSep.head)
              check(false)
            }
            lemmaMaxPrefWithOtherTypeUsedCharAtStartOfSuffixReturnSame(rules, separatorToken, separatorRule, suffixAfterSep, nextTokenRule)

            theoremInvertabilityFromTokensSepTokenWhenNeeded(rules, tl, separatorToken)
          } else {
            lemmaPrintWithSepTokenWhenNeededThenFindMaxPrefReturnsHead(rules, tokens, separatorToken)
            theoremInvertabilityFromTokensSepTokenWhenNeeded(rules, tl, separatorToken)
            ListUtils.lemmaConcatTwoListThenFirstIsPrefix(hd.getCharacters, suffixWithoutSep)
            ListUtils.lemmaSamePrefixThenSameSuffix(hd.getCharacters, suffixWithoutSep, hd.getCharacters, findMaxPrefix(rules, input).get._2, input)
          }
        }
        case Nil() => ()
      }
    } ensuring (lex(rules, printWithSeparatorTokenWhenNeeded(rules, tokens, separatorToken))._1.filter(!_.isSeparator) == tokens)

    def theoremInvertFromTokensSepTokenBetweenEach[C](rules: List[Rule[C]], tokens: List[Token[C]], separatorToken: Token[C]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rulesProduceEachTokenIndividually(rules, tokens))
      require(rulesProduceIndivualToken(rules, separatorToken))
      require(separatorToken.isSeparator)
      require(tokens.forall(!_.isSeparator))
      val _ = lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, separatorToken.getCharacters, separatorToken)
      require(getRuleFromTag(rules, separatorToken.getTag).get.isSeparator)
      require(sepAndNonSepRulesDisjointChars(rules, rules))
      decreases(tokens.size)

      tokens match {
        case Nil() => ()
        // case Cons(hd, Nil()) => ()
        case Cons(hd, Nil()) => {
          ListSpecs.forallContained(tokens, (t: Token[C]) => !t.isSeparator, hd)
          assert(!hd.isSeparator)
          val input = printWithSeparatorToken(tokens, separatorToken)
          assert(input == hd.getCharacters ++ separatorToken.getCharacters)
          ListUtils.lemmaGetSuffixOnListWithItSelfIsEmpty(hd.getCharacters)
          lemmaRulesProduceEachTokenIndividuallyThenForAnyToken(rules, tokens, hd)
          lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, hd.getCharacters, hd)
          val rule = getRuleFromTag(rules, hd.getTag).get
          assert(!rule.isSeparator)
          lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, separatorToken.getCharacters, separatorToken)
          val separatorRule = getRuleFromTag(rules, separatorToken.getTag).get
          lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(rules, hd.getCharacters, hd.getCharacters, Nil(), rule)

          if (!usedCharacters(separatorRule.regex).contains(separatorToken.getCharacters.head)) {
            lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(separatorRule.regex, separatorToken.getCharacters, separatorToken.getCharacters.head)
            check(false)
          }
          assert(usedCharacters(separatorRule.regex).contains(separatorToken.getCharacters.head))

          lemmaNonSepRuleNotContainsCharContainedInASepRule(rules, rules, rule, separatorRule, separatorToken.getCharacters.head)

          lemmaMaxPrefWithOtherTypeUsedCharAtStartOfSuffixReturnSame(rules, hd, rule, separatorToken.getCharacters, separatorRule)

          val suffix = findMaxPrefix(rules, input).get._2

          // needed
          val ret: (List[Token[C]], List[C]) = findMaxPrefix(rules, input) match {
            case Some((t, s)) => {
              assert(s == suffix)
              assert(t == hd)
              val (followingTokens, nextSuffix) = lex(rules, s)
              assert(nextSuffix.isEmpty)
              assert(t.getCharacters ++ s == input)
              (Cons(t, followingTokens), nextSuffix)
            }
            case None() => {
              check(false)
              (Nil(), input)
            }
          }

        }
        case Cons(hd, Cons(nextT, tl)) => {
          ListSpecs.forallContained(tokens, (t: Token[C]) => !t.isSeparator, hd)
          ListSpecs.forallContained(tokens, (t: Token[C]) => !t.isSeparator, nextT)
          assert(!hd.isSeparator)
          assert(!nextT.isSeparator)
          val input = printWithSeparatorToken(tokens, separatorToken)
          val suffixAfterSeparator = printWithSeparatorToken(Cons(nextT, tl), separatorToken)
          val suffix = separatorToken.getCharacters ++ suffixAfterSeparator
          assert(suffixAfterSeparator == nextT.getCharacters ++ separatorToken.getCharacters ++ printWithSeparatorToken(tl, separatorToken))
          assert(input == hd.getCharacters ++ separatorToken.getCharacters ++ suffixAfterSeparator)
          ListUtils.lemmaTwoListsConcatAssociativity(hd.getCharacters, separatorToken.getCharacters, suffixAfterSeparator)
          assert(input == hd.getCharacters ++ suffix)
          lemmaRulesProduceEachTokenIndividuallyThenForAnyToken(rules, tokens, hd)
          lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, hd.getCharacters, hd)
          val rule = getRuleFromTag(rules, hd.getTag).get
          assert(!rule.isSeparator)
          lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(rules, hd.getCharacters, hd.getCharacters, Nil(), rule)

          lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, separatorToken.getCharacters, separatorToken)
          val separatorRule = getRuleFromTag(rules, separatorToken.getTag).get

          if (!usedCharacters(separatorRule.regex).contains(separatorToken.getCharacters.head)) {
            lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(separatorRule.regex, separatorToken.getCharacters, separatorToken.getCharacters.head)
            check(false)
          }

          assert(suffixAfterSeparator == nextT.getCharacters ++ separatorToken.getCharacters ++ printWithSeparatorToken(tl, separatorToken))
          lemmaNonSepRuleNotContainsCharContainedInASepRule(rules, rules, rule, separatorRule, separatorToken.getCharacters.head)

          lemmaMaxPrefWithOtherTypeUsedCharAtStartOfSuffixReturnSame(rules, hd, rule, suffix, separatorRule)

          lemmaRulesProduceEachTokenIndividuallyThenForAnyToken(rules, tokens, nextT)
          assert(rulesProduceIndivualToken(rules, nextT))
          lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, nextT.getCharacters, nextT)
          val nextTRule = getRuleFromTag(rules, nextT.getTag).get
          assert(!nextTRule.isSeparator)
          lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(rules, nextT.getCharacters, nextT.getCharacters, Nil(), nextTRule)

          if (!usedCharacters(nextTRule.regex).contains(nextT.getCharacters.head)) {
            lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(nextTRule.regex, nextT.getCharacters, nextT.getCharacters.head)
            check(false)
          }

          lemmaSepRuleNotContainsCharContainedInANonSepRule(rules, rules, nextTRule, separatorRule, nextT.getCharacters.head)

          lemmaMaxPrefWithOtherTypeUsedCharAtStartOfSuffixReturnSame(rules, separatorToken, separatorRule, suffixAfterSeparator, nextTRule)

          theoremInvertFromTokensSepTokenBetweenEach(rules, Cons(nextT, tl), separatorToken)

        }
      }

    } ensuring (lex(rules, printWithSeparatorToken(tokens, separatorToken))._1.filter(!_.isSeparator) == tokens)

    def theoremInvertFromString[C](rules: List[Rule[C]], input: List[C]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      decreases(input.size)

      val (tokens, suffix) = lex(rules, input)
      if (suffix.isEmpty) {
        tokens match {
          case Cons(hd, Nil()) => ()
          case Cons(hd, tl)    => theoremInvertFromString(rules, findMaxPrefix(rules, input).get._2)
          case Nil()           => ()
        }
      } else {
        tokens match {
          case Cons(hd, Nil()) => assert(print(tokens) ++ suffix == input)
          case Cons(hd, tl) => {
            theoremInvertFromString(rules, findMaxPrefix(rules, input).get._2)
            lemmaRemovingFirstTokensCharactersPreservesLexSuffix(rules, input, tokens, suffix)

            assert(input == findMaxPrefix(rules, input).get._1.getCharacters ++ findMaxPrefix(rules, input).get._2)
            assert(input == findMaxPrefix(rules, input).get._1.getCharacters ++ (print(tl) ++ suffix))
            ListUtils.lemmaTwoListsConcatAssociativity(
              findMaxPrefix(rules, input).get._1.getCharacters,
              print(tl),
              suffix
            )
          }
          case Nil() => assert(print(tokens) ++ suffix == input)
        }
      }
    } ensuring ({
      val (tokens, suffix) = lex(rules, input)
      print(tokens) ++ suffix == input
    })

    // Functions -----------------------------------------------------------------------------------------------------------------------------

    def getRuleFromTag[C](rules: List[Rule[C]], tag: String): Option[Rule[C]] = {
      require(rulesInvariant(rules))
      rules match {
        case Cons(hd, tl) if hd.tag == tag => Some(hd)
        case Cons(hd, tl) if hd.tag != tag => {
          lemmaInvariantOnRulesThenOnTail(hd, tl)
          getRuleFromTag(tl, tag)
        }
        case Nil() => None[Rule[C]]()
      }
    } ensuring (res => res.isEmpty || rules.contains(res.get) && res.get.tag == tag)

    // Lemmas --------------------------------------------------------------------------------------------------------------------------------

    def lemmaPrintWithSepTokenWhenNeededThenFindMaxPrefReturnsHead[C](rules: List[Rule[C]], tokens: List[Token[C]], separatorToken: Token[C]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rulesProduceEachTokenIndividually(rules, tokens))
      require(rulesProduceIndivualToken(rules, separatorToken))
      require(separatorToken.isSeparator)
      require(tokens.forall(!_.isSeparator))
      require(sepAndNonSepRulesDisjointChars(rules, rules))

      tokens match {
        case Cons(hd, tl) => {
          lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, separatorToken.getCharacters, separatorToken)
          val separatorRule = getRuleFromTag(rules, separatorToken.getTag).get

          lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, hd.getCharacters, hd)
          val rule = getRuleFromTag(rules, hd.getTag).get

          val suffix = printWithSeparatorTokenWhenNeeded(rules, tl, separatorToken)
          val maxPrefWithoutSep = findMaxPrefix(rules, hd.getCharacters ++ suffix)
          maxPrefWithoutSep match {
            case Some((t, s)) if t == hd => ()
            case Some((t, s)) if t != hd => {
              ListUtils.lemmaTwoListsConcatAssociativity(hd.getCharacters, separatorToken.getCharacters, suffix)
              val resSuffix = separatorToken.getCharacters ++ suffix
              if (!usedCharacters(separatorRule.regex).contains(separatorToken.getCharacters.head)) {
                lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(separatorRule.regex, separatorToken.getCharacters, separatorToken.getCharacters.head)
                check(false)
              }
              lemmaNonSepRuleNotContainsCharContainedInASepRule(rules, rules, rule, separatorRule, separatorToken.getCharacters.head)

              lemmaMaxPrefWithOtherTypeUsedCharAtStartOfSuffixReturnSame(rules, hd, rule, resSuffix, separatorRule)
            }
            case None() => {
              lemmaLexIsDefinedWithStrThenLexWithSuffixIsDefined(rules, hd.getCharacters, suffix)
              check(false)
            }
          }
        }
        case Nil() => ()
      }

    } ensuring (tokens.isEmpty ||
      (!tokens.isEmpty &&
        findMaxPrefix(rules, printWithSeparatorTokenWhenNeeded(rules, tokens, separatorToken)).isDefined &&
        findMaxPrefix(rules, printWithSeparatorTokenWhenNeeded(rules, tokens, separatorToken)).get._1 == tokens.head))

    def lemmaMaxPrefWithOtherTypeUsedCharAtStartOfSuffixReturnSame[C](rules: List[Rule[C]], token: Token[C], rule: Rule[C], suffix: List[C], anOtherTypeRule: Rule[C]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rules.contains(rule))
      require(rules.contains(anOtherTypeRule))
      require(anOtherTypeRule.isSeparator != rule.isSeparator)
      require(findMaxPrefix(rules, token.getCharacters).isDefined)
      require(findMaxPrefix(rules, token.getCharacters).get._1 == token)
      require(findMaxPrefix(rules, token.getCharacters).get._2.isEmpty)
      require(token.getTag == rule.tag)
      require(token.isSeparator == rule.isSeparator)
      val _ = lemmaRuleInListAndRulesValidThenRuleIsValid(rule, rules)
      require(matchR(rule.regex, token.getCharacters))
      require(!suffix.isEmpty)
      require(!usedCharacters(rule.regex).contains(suffix.head))
      require(usedCharacters(anOtherTypeRule.regex).contains(suffix.head))
      require(sepAndNonSepRulesDisjointChars(rules, rules))

      val input = token.getCharacters ++ suffix
      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(token.getCharacters, suffix)
      val tokenOpt = findMaxPrefix(rules, input)
      lemmaLexIsDefinedWithStrThenLexWithSuffixIsDefined(rules, token.getCharacters, suffix)
      val foundToken = tokenOpt.get._1
      val foundSuffix = tokenOpt.get._2
      lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, input, foundToken)
      val foundRule = getRuleFromTag(rules, foundToken.getTag).get
      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(foundToken.getCharacters, foundSuffix)
      assert(ListUtils.isPrefix(foundToken.getCharacters, input))
      assert(foundRule.tag == foundToken.getTag)
      assert(matchR(foundRule.regex, foundToken.getCharacters))
      assert(foundRule.isSeparator == foundToken.isSeparator)

      lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(rules, foundToken.getCharacters, input, foundSuffix, foundRule)
      ListUtils.lemmaSamePrefixThenSameSuffix(foundToken.getCharacters, foundSuffix, foundToken.getCharacters, ListUtils.getSuffix(input, foundToken.getCharacters), input)
      assert(ListUtils.getSuffix(input, foundToken.getCharacters) == foundSuffix)
      assert(findMaxPrefixOneRule(foundRule, input) == Some((foundToken, ListUtils.getSuffix(input, foundToken.getCharacters))))

      if (!usedCharacters(rule.regex).contains(foundToken.getCharacters.head)) {
        lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(rule.regex, token.getCharacters, foundToken.getCharacters.head)
        check(false)
      }
      if (rule.isSeparator) {
        if (!foundRule.isSeparator) {
          assert(token.getCharacters.contains(foundToken.getCharacters.head))
          assert(usedCharacters(rule.regex).contains(foundToken.getCharacters.head))
          lemmaNonSepRuleNotContainsCharContainedInASepRule(rules, rules, foundRule, rule, foundToken.getCharacters.head)
          lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(foundRule.regex, foundToken.getCharacters, foundToken.getCharacters.head)
          check(false)
        }
      } else {
        if (foundRule.isSeparator) {
          assert(token.getCharacters.contains(foundToken.getCharacters.head))
          assert(usedCharacters(rule.regex).contains(foundToken.getCharacters.head))
          lemmaSepRuleNotContainsCharContainedInANonSepRule(rules, rules, rule, foundRule, foundToken.getCharacters.head)
          lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(foundRule.regex, foundToken.getCharacters, foundToken.getCharacters.head)
          check(false)
        }
      }

      if (foundToken.getCharacters.size > token.getCharacters.size) {
        ListUtils.lemmaLongerPrefixContainsHeadOfSuffixOfSmallerPref(token.getCharacters, suffix, foundToken.getCharacters, input)
        if (rule.isSeparator) {
          lemmaSepRuleNotContainsCharContainedInANonSepRule(rules, rules, anOtherTypeRule, foundRule, suffix.head)
          lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(foundRule.regex, foundToken.getCharacters, suffix.head)
          check(false)
        } else {
          lemmaNonSepRuleNotContainsCharContainedInASepRule(rules, rules, foundRule, anOtherTypeRule, suffix.head)
          lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(foundRule.regex, foundToken.getCharacters, suffix.head)
          check(false)
        }
      }
      if (foundToken.getCharacters.size < token.getCharacters.size) {
        lemmaMaxPrefixOutputsMaxPrefix(rules, foundRule, foundToken.getCharacters, input, token.getCharacters, rule)
        check(false)
      }
      ListUtils.lemmaIsPrefixSameLengthThenSameList(foundToken.getCharacters, token.getCharacters, input)

      assert(foundToken.getCharacters == token.getCharacters)

      if (foundToken.getTag != token.getTag) {
        assert(foundRule != rule)
        val foundRuleIndex = ListUtils.getIndex(rules, foundRule)
        val ruleIndex = ListUtils.getIndex(rules, rule)
        if (foundRuleIndex < ruleIndex) {
          ListUtils.lemmaGetSuffixOnListWithItSelfIsEmpty(token.getCharacters)
          assert(ListUtils.getSuffix(token.getCharacters, token.getCharacters).isEmpty)
          lemmaMaxPrefNoSmallerRuleMatches(rules, rule, token.getCharacters, token.getCharacters, foundRule)
          check(false)
        }
        if (ruleIndex < foundRuleIndex) {
          lemmaMaxPrefNoSmallerRuleMatches(rules, foundRule, token.getCharacters, input, rule)
          check(false)
        }

        ListUtils.lemmaSameIndexThenSameElement(rules, foundRule, rule)
        check(false)
      }
      assert(foundToken.getTag == token.getTag)
      assert(foundToken.getTag == rule.tag)

      lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(rules, token.getCharacters, input, ListUtils.getSuffix(input, token.getCharacters), rule)
      ListUtils.lemmaSamePrefixThenSameSuffix(token.getCharacters, ListUtils.getSuffix(input, token.getCharacters), foundToken.getCharacters, foundSuffix, input)
      ListUtils.lemmaSamePrefixThenSameSuffix(token.getCharacters, suffix, foundToken.getCharacters, foundSuffix, input)

    } ensuring (findMaxPrefix(rules, token.getCharacters ++ suffix) == Some((token, suffix)))

    // Deprecated: was combined in lemmaMaxPrefWithOtherTypeUsedCharAtStartOfSuffixReturnSame
    def lemmaMaxPrefWithNonSeparatorUsedCharAtStartOfSuffixReturnSame[C](rules: List[Rule[C]], token: Token[C], rule: Rule[C], suffix: List[C], aNSeparatorRule: Rule[C]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rules.contains(rule))
      require(rules.contains(aNSeparatorRule))
      require(!aNSeparatorRule.isSeparator)
      require(findMaxPrefix(rules, token.getCharacters).isDefined)
      require(findMaxPrefix(rules, token.getCharacters).get._1 == token)
      require(findMaxPrefix(rules, token.getCharacters).get._2.isEmpty)
      require(token.getTag == rule.tag)
      require(token.isSeparator == rule.isSeparator)
      require(token.isSeparator)
      val _ = lemmaRuleInListAndRulesValidThenRuleIsValid(rule, rules)
      require(matchR(rule.regex, token.getCharacters))
      require(!suffix.isEmpty)
      require(!usedCharacters(rule.regex).contains(suffix.head))
      require(usedCharacters(aNSeparatorRule.regex).contains(suffix.head))
      require(sepAndNonSepRulesDisjointChars(rules, rules))

      val input = token.getCharacters ++ suffix
      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(token.getCharacters, suffix)
      val tokenOpt = findMaxPrefix(rules, input)
      lemmaLexIsDefinedWithStrThenLexWithSuffixIsDefined(rules, token.getCharacters, suffix)
      val foundToken = tokenOpt.get._1
      val foundSuffix = tokenOpt.get._2
      lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, input, foundToken)
      val foundRule = getRuleFromTag(rules, foundToken.getTag).get
      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(foundToken.getCharacters, foundSuffix)
      assert(ListUtils.isPrefix(foundToken.getCharacters, input))
      assert(foundRule.tag == foundToken.getTag)
      assert(matchR(foundRule.regex, foundToken.getCharacters))
      assert(foundRule.isSeparator == foundToken.isSeparator)

      lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(rules, foundToken.getCharacters, input, foundSuffix, foundRule)
      ListUtils.lemmaSamePrefixThenSameSuffix(foundToken.getCharacters, foundSuffix, foundToken.getCharacters, ListUtils.getSuffix(input, foundToken.getCharacters), input)
      assert(ListUtils.getSuffix(input, foundToken.getCharacters) == foundSuffix)
      assert(findMaxPrefixOneRule(foundRule, input) == Some((foundToken, ListUtils.getSuffix(input, foundToken.getCharacters))))

      if (!usedCharacters(rule.regex).contains(foundToken.getCharacters.head)) {
        lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(rule.regex, token.getCharacters, foundToken.getCharacters.head)
        check(false)
      }

      if (!foundRule.isSeparator) {
        assert(token.getCharacters.contains(foundToken.getCharacters.head))
        assert(usedCharacters(rule.regex).contains(foundToken.getCharacters.head))
        lemmaNonSepRuleNotContainsCharContainedInASepRule(rules, rules, foundRule, rule, foundToken.getCharacters.head)
        lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(foundRule.regex, foundToken.getCharacters, foundToken.getCharacters.head)
        check(false)
      }

      if (foundToken.getCharacters.size > token.getCharacters.size) {
        ListUtils.lemmaLongerPrefixContainsHeadOfSuffixOfSmallerPref(token.getCharacters, suffix, foundToken.getCharacters, input)
        lemmaSepRuleNotContainsCharContainedInANonSepRule(rules, rules, aNSeparatorRule, foundRule, suffix.head)
        lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(foundRule.regex, foundToken.getCharacters, suffix.head)
        check(false)
      }
      if (foundToken.getCharacters.size < token.getCharacters.size) {
        lemmaMaxPrefixOutputsMaxPrefix(rules, foundRule, foundToken.getCharacters, input, token.getCharacters, rule)
        check(false)
      }
      ListUtils.lemmaIsPrefixSameLengthThenSameList(foundToken.getCharacters, token.getCharacters, input)

      assert(foundToken.getCharacters == token.getCharacters)

      if (foundToken.getTag != token.getTag) {
        assert(foundRule != rule)
        val foundRuleIndex = ListUtils.getIndex(rules, foundRule)
        val ruleIndex = ListUtils.getIndex(rules, rule)
        if (foundRuleIndex < ruleIndex) {
          ListUtils.lemmaGetSuffixOnListWithItSelfIsEmpty(token.getCharacters)
          assert(ListUtils.getSuffix(token.getCharacters, token.getCharacters).isEmpty)
          lemmaMaxPrefNoSmallerRuleMatches(rules, rule, token.getCharacters, token.getCharacters, foundRule)
          check(false)
        }
        if (ruleIndex < foundRuleIndex) {
          lemmaMaxPrefNoSmallerRuleMatches(rules, foundRule, token.getCharacters, input, rule)
          check(false)
        }

        ListUtils.lemmaSameIndexThenSameElement(rules, foundRule, rule)
        check(false)
      }
      assert(foundToken.getTag == token.getTag)
      assert(foundToken.getTag == rule.tag)

      lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(rules, token.getCharacters, input, ListUtils.getSuffix(input, token.getCharacters), rule)
      ListUtils.lemmaSamePrefixThenSameSuffix(token.getCharacters, ListUtils.getSuffix(input, token.getCharacters), foundToken.getCharacters, foundSuffix, input)
      ListUtils.lemmaSamePrefixThenSameSuffix(token.getCharacters, suffix, foundToken.getCharacters, foundSuffix, input)

    } ensuring (findMaxPrefix(rules, token.getCharacters ++ suffix) == Some((token, suffix)))

    // Deprecated: was combined in lemmaMaxPrefWithOtherTypeUsedCharAtStartOfSuffixReturnSame
    def lemmaMaxPrefWithSeparatorUsedCharAtStartOfSuffixReturnSame[C](rules: List[Rule[C]], token: Token[C], rule: Rule[C], suffix: List[C], aSeparatorRule: Rule[C]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rules.contains(rule))
      require(rules.contains(aSeparatorRule))
      require(aSeparatorRule.isSeparator)
      require(findMaxPrefix(rules, token.getCharacters).isDefined)
      require(findMaxPrefix(rules, token.getCharacters).get._1 == token)
      require(findMaxPrefix(rules, token.getCharacters).get._2.isEmpty)
      require(token.getTag == rule.tag)
      require(token.isSeparator == rule.isSeparator)
      require(!token.isSeparator)
      val _ = lemmaRuleInListAndRulesValidThenRuleIsValid(rule, rules)
      require(matchR(rule.regex, token.getCharacters))
      require(!suffix.isEmpty)
      require(!usedCharacters(rule.regex).contains(suffix.head))
      require(usedCharacters(aSeparatorRule.regex).contains(suffix.head))
      require(sepAndNonSepRulesDisjointChars(rules, rules))

      val input = token.getCharacters ++ suffix
      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(token.getCharacters, suffix)
      val tokenOpt = findMaxPrefix(rules, input)
      lemmaLexIsDefinedWithStrThenLexWithSuffixIsDefined(rules, token.getCharacters, suffix)
      val foundToken = tokenOpt.get._1
      val foundSuffix = tokenOpt.get._2
      lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, input, foundToken)
      val foundRule = getRuleFromTag(rules, foundToken.getTag).get
      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(foundToken.getCharacters, foundSuffix)
      assert(ListUtils.isPrefix(foundToken.getCharacters, input))
      assert(foundRule.tag == foundToken.getTag)
      assert(matchR(foundRule.regex, foundToken.getCharacters))
      assert(foundRule.isSeparator == foundToken.isSeparator)

      lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(rules, foundToken.getCharacters, input, foundSuffix, foundRule)
      ListUtils.lemmaSamePrefixThenSameSuffix(foundToken.getCharacters, foundSuffix, foundToken.getCharacters, ListUtils.getSuffix(input, foundToken.getCharacters), input)
      assert(ListUtils.getSuffix(input, foundToken.getCharacters) == foundSuffix)
      assert(findMaxPrefixOneRule(foundRule, input) == Some((foundToken, ListUtils.getSuffix(input, foundToken.getCharacters))))

      if (!usedCharacters(rule.regex).contains(foundToken.getCharacters.head)) {
        lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(rule.regex, token.getCharacters, foundToken.getCharacters.head)
        check(false)
      }

      if (foundRule.isSeparator) {
        assert(token.getCharacters.contains(foundToken.getCharacters.head))
        assert(usedCharacters(rule.regex).contains(foundToken.getCharacters.head))
        lemmaSepRuleNotContainsCharContainedInANonSepRule(rules, rules, rule, foundRule, foundToken.getCharacters.head)
        lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(foundRule.regex, foundToken.getCharacters, foundToken.getCharacters.head)
        check(false)
      }

      if (foundToken.getCharacters.size > token.getCharacters.size) {
        ListUtils.lemmaLongerPrefixContainsHeadOfSuffixOfSmallerPref(token.getCharacters, suffix, foundToken.getCharacters, input)
        lemmaNonSepRuleNotContainsCharContainedInASepRule(rules, rules, foundRule, aSeparatorRule, suffix.head)
        lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(foundRule.regex, foundToken.getCharacters, suffix.head)
        check(false)
      }
      if (foundToken.getCharacters.size < token.getCharacters.size) {
        lemmaMaxPrefixOutputsMaxPrefix(rules, foundRule, foundToken.getCharacters, input, token.getCharacters, rule)
        check(false)
      }
      ListUtils.lemmaIsPrefixSameLengthThenSameList(foundToken.getCharacters, token.getCharacters, input)

      assert(foundToken.getCharacters == token.getCharacters)

      if (foundToken.getTag != token.getTag) {
        assert(foundRule != rule)
        val foundRuleIndex = ListUtils.getIndex(rules, foundRule)
        val ruleIndex = ListUtils.getIndex(rules, rule)
        if (foundRuleIndex < ruleIndex) {
          ListUtils.lemmaGetSuffixOnListWithItSelfIsEmpty(token.getCharacters)
          assert(ListUtils.getSuffix(token.getCharacters, token.getCharacters).isEmpty)
          lemmaMaxPrefNoSmallerRuleMatches(rules, rule, token.getCharacters, token.getCharacters, foundRule)
          check(false)
        }
        if (ruleIndex < foundRuleIndex) {
          lemmaMaxPrefNoSmallerRuleMatches(rules, foundRule, token.getCharacters, input, rule)
          check(false)
        }

        ListUtils.lemmaSameIndexThenSameElement(rules, foundRule, rule)
        check(false)
      }
      assert(foundToken.getTag == token.getTag)
      assert(foundToken.getTag == rule.tag)

      lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(rules, token.getCharacters, input, ListUtils.getSuffix(input, token.getCharacters), rule)
      ListUtils.lemmaSamePrefixThenSameSuffix(token.getCharacters, ListUtils.getSuffix(input, token.getCharacters), foundToken.getCharacters, foundSuffix, input)
      ListUtils.lemmaSamePrefixThenSameSuffix(token.getCharacters, suffix, foundToken.getCharacters, foundSuffix, input)

    } ensuring (findMaxPrefix(rules, token.getCharacters ++ suffix) == Some((token, suffix)))

    def lemmaprintHeadIsPrefixOfprintList[C](ts: List[Token[C]]): Unit = {
      require(!ts.isEmpty)
      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(print(List(ts.head)), print(ts.tail))
    } ensuring (ListUtils.isPrefix(print(List(ts.head)), print(ts)))

    def lemmaLexIsDefinedWithStrThenLexWithSuffixIsDefined[C](rules: List[Rule[C]], input: List[C], suffix: List[C]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(!lex(rules, input)._1.isEmpty)

      val (tokens, _) = lex(rules, input)
      val firstT = tokens.head
      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(firstT.getCharacters, findMaxPrefix(rules, input).get._2)
      ListUtils.lemmaPrefixStaysPrefixWhenAddingToSuffix(firstT.getCharacters, input, suffix)
      lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, input, firstT)
      val rule: Rule[C] = getRuleFromTag(rules, firstT.getTag).get
      assert(matchR(rule.regex, firstT.getCharacters))

      if (findMaxPrefix(rules, input ++ suffix).isEmpty) {
        lemmaMaxPrefixReturnsNoneThenAnyRuleReturnsNone(rule, rules, input ++ suffix)
        lemmaMaxPrefOneRuleReturnsNoneThenNoPrefMaxRegex(rule, firstT.getCharacters, input ++ suffix)
        check(false)
      }

    } ensuring (findMaxPrefix(rules, input ++ suffix).isDefined)

    def lemmaMaxPrefReturnTokenSoItsTagBelongsToARule[C](rules: List[Rule[C]], input: List[C], token: Token[C]): Unit = {
      require(rulesInvariant(rules))
      require(!rules.isEmpty)
      require(findMaxPrefix(rules, input).isDefined && findMaxPrefix(rules, input).get._1 == token)

      rules match {
        case Cons(hd, tl) => {
          if (findMaxPrefixOneRule(hd, input).isDefined && findMaxPrefixOneRule(hd, input).get._1 == token) {
            assert(hd.tag == token.getTag)
            assert(matchR(hd.regex, token.getCharacters))
          } else {
            if (!tl.isEmpty) {
              lemmaInvariantOnRulesThenOnTail(hd, tl)
              lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(tl, input, token)
              lemmaGetRuleFromTagInListThenSameListWhenAddingARuleDiffTag(tl, hd, token.getTag)
            } else {
              check(false)
            }
          }
        }
        case Nil() => ()
      }
    } ensuring (getRuleFromTag(rules, token.getTag).isDefined && matchR(getRuleFromTag(rules, token.getTag).get.regex, token.getCharacters) &&
      token.isSeparator == getRuleFromTag(rules, token.getTag).get.isSeparator)

    def lemmaGetRuleFromTagInListThenSameListWhenAddingARuleDiffTag[C](rules: List[Rule[C]], newHd: Rule[C], tag: String): Unit = {
      require(rulesInvariant(Cons(newHd, rules)))
      val _ = lemmaInvariantOnRulesThenOnTail(newHd, rules)
      require(getRuleFromTag(rules, tag).isDefined)

      lemmaInvariantOnRulesThenOnTail(newHd, rules)
      lemmaNoDuplicateAndTagInAccThenRuleCannotHaveSame(rules, getRuleFromTag(rules, tag).get, newHd.tag, List(newHd.tag))

    } ensuring (getRuleFromTag(rules, tag).get == getRuleFromTag(Cons(newHd, rules), tag).get)

    def lemmaRemovingFirstTokensCharactersPreservesLexSuffix[C](
        rules: List[Rule[C]],
        input: List[C],
        producedTokens: List[Token[C]],
        suffix: List[C]
    ): Unit = {
      require(rulesInvariant(rules))
      require(!rules.isEmpty)
      require(producedTokens.size > 0)
      require(lex(rules, input) == (producedTokens, suffix))
    } ensuring (lex(rules, findMaxPrefix(rules, input).get._2) == (producedTokens.tail, suffix))

    def lemmaMaxPrefNoneThenNoRuleMatches[C](rules: List[Rule[C]], r: Rule[C], p: List[C], input: List[C]): Unit = {
      require(ListUtils.isPrefix(p, input))
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rules.contains(r))
      require(findMaxPrefix(rules, input) == None[(Token[C], List[C])]())

      lemmaRuleInListAndRulesValidThenRuleIsValid(r, rules)

      lemmaMaxPrefixReturnsNoneThenAnyRuleReturnsNone(r, rules, input)
      lemmaMaxPrefOneRuleReturnsNoneThenNoPrefMaxRegex(r, p, input)

    } ensuring (!matchR(r.regex, p))

    def lemmaMaxPrefNoSmallerRuleMatches[C](
        rules: List[Rule[C]],
        r: Rule[C],
        p: List[C],
        input: List[C],
        rBis: Rule[C]
    ): Unit = {
      require(ListUtils.isPrefix(p, input))
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rules.contains(r))
      require(rules.contains(rBis))
      require(findMaxPrefix(rules, input) == Some(Token(p, r.tag, r.isSeparator), ListUtils.getSuffix(input, p)))
      require(ListUtils.getIndex(rules, rBis) < ListUtils.getIndex(rules, r))
      require(ruleValid(r))
      require(matchR(r.regex, p))

      assert(ListUtils.getIndex(rules, rBis) < ListUtils.getIndex(rules, r))

      lemmaRuleInListAndRulesValidThenRuleIsValid(rBis, rules)
      lemmaRuleInListAndRulesValidThenRuleIsValid(r, rules)
      rules match {
        case Cons(hd, tl) if hd == rBis => {
          ListUtils.lemmaGetIndexBiggerAndHeadEqThenTailContains(rules, rBis, r)
          lemmaNoDuplicateTagAndDiffIndexThenNoTwoRulesEq(rules, rBis, r)

          val tokenSuffOpt = findMaxPrefixOneRule(rBis, input)
          if (tokenSuffOpt.isEmpty) {
            lemmaMaxPrefOneRuleReturnsNoneThenNoPrefMaxRegex(rBis, p, input)
          } else {
            val (token, suff) = tokenSuffOpt.get
            if (token.getCharacters.size > p.size) {
              lemmaRuleReturnsPrefixSmallerEqualThanGlobalMaxPref(
                rules,
                p,
                Token(p, r.tag, r.isSeparator),
                input,
                ListUtils.getSuffix(input, p),
                token.getCharacters,
                ListUtils.getSuffix(input, token.getCharacters),
                rBis,
                token
              )
              check(false)
              check(!matchR(rBis.regex, p))
            } else {
              if (token.getCharacters.size < p.size) {
                ListUtils.lemmaConcatTwoListThenFirstIsPrefix(token.getCharacters, suff)
                lemmaMaxPrefixOneRuleOutputsMaxPrefix(rBis, token.getCharacters, token, input, suff, p)
                check(!matchR(rBis.regex, p))
              } else {
                lemmaNoDuplicateTagAndDiffIndexThenNoTwoRulesTagsEq(rules, rBis, r)
                check(Some(token, suff) != Some(Token(p, r.tag, r.isSeparator), ListUtils.getSuffix(input, p)))
                check(!matchR(rBis.regex, p))
              }
            }
          }
        }
        case Cons(hd, tl) if hd != rBis => {
          assert(tl.contains(r))
          assert(tl.contains(rBis))

          val tokenSuffOpt = findMaxPrefixOneRule(hd, input)
          val tokenSuffTailOpt = findMaxPrefix(tl, input)

          lemmaInvariantOnRulesThenOnTail(hd, tl)
          lemmaNoDuplicateTagAndDiffIndexThenNoTwoRulesTagsEq(rules, hd, r)
          lemmaMaxPrefNoSmallerRuleMatches(tl, r, p, input, rBis)
        }
        case Nil() => check(false)
      }
    } ensuring (!matchR(rBis.regex, p))

    /** Lemma which proves that indeed the getMaxPrefix indeed returns the maximal prefix that matches any rules
      *
      * @param rules
      * @param r
      * @param p
      * @param input
      * @param pBis
      * @param rBis
      */
    def lemmaMaxPrefixOutputsMaxPrefix[C](
        rules: List[Rule[C]],
        r: Rule[C],
        p: List[C],
        input: List[C],
        pBis: List[C],
        rBis: Rule[C]
    ): Unit = {
      require(ListUtils.isPrefix(p, input))
      require(ListUtils.isPrefix(pBis, input))

      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rules.contains(r))
      require(rules.contains(rBis))

      require({
        lemmaRuleInListAndRulesValidThenRuleIsValid(r, rules)
        matchR(r.regex, p)
      })
      require({
        ListUtils.lemmaIsPrefixRefl(input, input)
        findMaxPrefixOneRule(r, input) == Some(Token(p, r.tag, r.isSeparator), ListUtils.getSuffix(input, p))
      })

      require(pBis.size > p.size)

      require(findMaxPrefix(rules, input) == Some(Token(p, r.tag, r.isSeparator), ListUtils.getSuffix(input, p)))

      // For preconditions
      lemmaRuleInListAndRulesValidThenRuleIsValid(r, rules)
      lemmaRuleInListAndRulesValidThenRuleIsValid(rBis, rules)
      ListUtils.lemmaIsPrefixRefl(input, input)

      // Main lemma
      lemmaMaxPrefixOutputsMaxPrefixInner(rules, r, p, input, pBis, rBis)

    } ensuring (!matchR(rBis.regex, pBis))

    def lemmaMaxPrefixOutputsMaxPrefixInner[C](
        rules: List[Rule[C]],
        r: Rule[C],
        p: List[C],
        input: List[C],
        pBis: List[C],
        rBis: Rule[C]
    ): Unit = {
      require(ListUtils.isPrefix(p, input))
      require(ListUtils.isPrefix(pBis, input))

      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rules.contains(r))
      require(rules.contains(rBis))

      require(validRegex(r.regex))
      require(matchR(r.regex, p))
      val _ = ListUtils.lemmaIsPrefixRefl(input, input)
      require(ruleValid(r))
      require(findMaxPrefixOneRule(r, input) == Some(Token(p, r.tag, r.isSeparator), ListUtils.getSuffix(input, p)))

      require(pBis.size > p.size)

      require(ruleValid(rBis))
      require(findMaxPrefix(rules, input) == Some(Token(p, r.tag, r.isSeparator), ListUtils.getSuffix(input, p)))

      assert(validRegex(r.regex))

      ListUtils.lemmaIsPrefixThenSmallerEqSize(pBis, input)
      lemmaRuleInListAndRulesValidThenRuleIsValid(rBis, rules)

      val bisTokenSuff = findMaxPrefixOneRule(rBis, input) // == Some(Token(pBis, rBis.tag), ListUtils.getSuffix(input, pBis))
      if (bisTokenSuff.isEmpty) {
        lemmaMaxPrefOneRuleReturnsNoneThenNoPrefMaxRegex(rBis, pBis, input)
        check(!matchR(rBis.regex, pBis))
      } else {
        val tBis = bisTokenSuff.get._1
        val suffixBis = bisTokenSuff.get._2
        ListUtils.lemmaConcatTwoListThenFirstIsPrefix(tBis.getCharacters, suffixBis)
        if (tBis.getCharacters == pBis) {
          lemmaRuleReturnsPrefixSmallerEqualThanGlobalMaxPref(
            rules,
            p,
            Token(p, r.tag, r.isSeparator),
            input,
            ListUtils.getSuffix(input, p),
            pBis,
            suffixBis,
            rBis,
            tBis
          )
          check(!matchR(rBis.regex, pBis))
        } else {
          if (tBis.getCharacters.size < pBis.size) {
            assert(ListUtils.isPrefix(tBis.getCharacters, input))
            lemmaMaxPrefixOneRuleOutputsMaxPrefix(rBis, tBis.getCharacters, tBis, input, suffixBis, pBis)
            check(!matchR(rBis.regex, pBis))
          } else {
            if (pBis.size == tBis.getCharacters.size) {
              ListUtils.lemmaIsPrefixSameLengthThenSameList(pBis, tBis.getCharacters, input)
              check(false)
            }
            assert(pBis.size < tBis.getCharacters.size)
            lemmaRuleReturnsPrefixSmallerEqualThanGlobalMaxPref(
              rules,
              p,
              Token(p, r.tag, r.isSeparator),
              input,
              ListUtils.getSuffix(input, p),
              tBis.getCharacters,
              suffixBis,
              rBis,
              tBis
            )
            assert(tBis.getCharacters.size <= p.size)
            check(false)
            check(!matchR(rBis.regex, pBis))

          }
        }

      }

    } ensuring (!matchR(rBis.regex, pBis))

    def lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule[C](
        rules: List[Rule[C]],
        p: List[C],
        input: List[C],
        suffix: List[C],
        r: Rule[C]
    ): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rules.contains(r))
      val _ = lemmaRuleInListAndRulesValidThenRuleIsValid(r, rules)
      require(input == p ++ suffix)
      require(findMaxPrefix(rules, input) == Some(Token(p, r.tag, r.isSeparator), suffix))
      require(matchR(r.regex, p))
      decreases(rules.size)

      rules match {
        case Cons(hd, tl) if hd == r => {
          lemmaInvariantOnRulesThenOnTail(hd, tl)
          if (tl.isEmpty) {
            check(findMaxPrefixOneRule(r, input) == Some(Token(p, r.tag, r.isSeparator), suffix))
          } else {
            lemmaNoDuplTagThenTailRulesCannotProduceHeadTagInTok(hd, tl, input)
            assert(findMaxPrefix(tl, input).isEmpty || findMaxPrefix(tl, input).get._1.getTag != r.tag)
            check(findMaxPrefixOneRule(r, input) == Some(Token(p, r.tag, r.isSeparator), suffix))
          }
        }
        case Cons(hd, tl) if hd != r => {
          lemmaInvariantOnRulesThenOnTail(hd, tl)
          val otherTokSufOpt = findMaxPrefixOneRule(hd, input)
          if (otherTokSufOpt.isEmpty) {
            lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(tl, p, input, suffix, r)
          } else {
            assert(otherTokSufOpt.get._1.getTag == hd.tag)
            if (otherTokSufOpt.get._1.getTag == r.tag) {
              assert(hd.tag == r.tag)
              lemmaNoDuplicateTagAndDiffIndexThenNoTwoRulesTagsEq(rules, hd, r)
              check(false)
            } else {
              assert(otherTokSufOpt.get._1.getTag != r.tag)
              assert(findMaxPrefixOneRule(hd, input) != Some(Token(p, r.tag, r.isSeparator), suffix))
              assert(findMaxPrefix(tl, input) == Some(Token(p, r.tag, r.isSeparator), suffix))
              lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(tl, p, input, suffix, r)
            }

          }
        }
        case Nil() => check(false)

      }

    } ensuring (findMaxPrefixOneRule(r, input) == Some(Token(p, r.tag, r.isSeparator), suffix))

    def lemmaNoDuplTagThenTailRulesCannotProduceHeadTagInTok[C](rHead: Rule[C], rTail: List[Rule[C]], input: List[C]): Unit = {
      require(!rTail.isEmpty)
      require(rulesInvariant(Cons(rHead, rTail)))

      rTail match {
        case Cons(hd, tl) => {
          lemmaNoDuplicateCanReorder(rHead, hd, tl)

          lemmaNoDuplicateTagAndDiffIndexThenNoTwoRulesTagsEq(Cons(rHead, rTail), rHead, hd)
          if (!tl.isEmpty) {
            lemmaNoDupTagThenAlsoWithSubListAcc(List(hd.tag), Nil(), Cons(rHead, tl))
            lemmaNoDuplTagThenTailRulesCannotProduceHeadTagInTok(rHead, tl, input)
          }
        }
        case Nil() => check(false)
      }

    } ensuring (findMaxPrefix(rTail, input).isEmpty || findMaxPrefix(rTail, input).get._1.getTag != rHead.tag)

    def lemmaRuleReturnsPrefixSmallerEqualThanGlobalMaxPref[C](
        rules: List[Rule[C]],
        p: List[C],
        t: Token[C],
        input: List[C],
        suffix: List[C],
        pBis: List[C],
        suffixBis: List[C],
        rBis: Rule[C],
        tBis: Token[C]
    ): Unit = {
      require(p ++ suffix == input)
      require(ListUtils.isPrefix(p, input))
      require(ListUtils.isPrefix(pBis, input))

      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rules.contains(rBis))
      require(findMaxPrefix(rules, input) == Some(t, suffix))
      val _ = ListUtils.lemmaIsPrefixRefl(input, input)
      require(ruleValid(rBis))
      require(findMaxPrefixOneRule(rBis, input) == Some(tBis, suffixBis))
      require(tBis.getTag == rBis.tag)
      require(tBis.getCharacters == pBis)
      require(pBis ++ suffixBis == input)

      rules match {
        case Cons(hd, Nil()) => ()
        case Cons(hd, tl) => {
          if (hd == rBis) {
            check(pBis.size <= p.size)
          } else {
            if (findMaxPrefixOneRule(hd, input) == Some(t, suffix)) {
              val othersPrefix = findMaxPrefix(tl, input)
              if (othersPrefix.isEmpty) {
                lemmaMaxPrefixReturnsNoneThenAnyRuleReturnsNone(rBis, tl, input)
                check(false)
              }
              val tokSuff = othersPrefix.get
              val oPref = tokSuff._1.getCharacters
              val suff = tokSuff._2
              ListUtils.lemmaConcatTwoListThenFirstIsPrefix(oPref, suff)
              lemmaInvariantOnRulesThenOnTail(hd, tl)
              lemmaRuleReturnsPrefixSmallerEqualThanGlobalMaxPref(tl, oPref, tokSuff._1, input, suff, pBis, suffixBis, rBis, tBis)
              check(pBis.size <= p.size)
            } else {
              lemmaInvariantOnRulesThenOnTail(hd, tl)
              lemmaRuleReturnsPrefixSmallerEqualThanGlobalMaxPref(tl, p, t, input, suffix, pBis, suffixBis, rBis, tBis)
            }
          }
        }
        case Nil() => check(false)
      }

    } ensuring (pBis.size <= p.size)

    def lemmaMaxPrefixReturnsNoneThenAnyRuleReturnsNone[C](
        r: Rule[C],
        rules: List[Rule[C]],
        input: List[C]
    ): Unit = {
      require(!rules.isEmpty)
      require(rulesValid(rules))
      require(rules.contains(r))

      require(findMaxPrefix(rules, input).isEmpty)

      lemmaRuleInListAndRulesValidThenRuleIsValid(r, rules)

      rules match {
        case Cons(hd, tl) if r == hd => ()
        case Cons(hd, tl) if r != hd => {

          lemmaMaxPrefixReturnsNoneThenAnyRuleReturnsNone(r, tl, input)
        }
        case Nil() => ()
      }

    } ensuring (findMaxPrefixOneRule(r, input).isEmpty)

    def lemmaMaxPrefixOneRuleOutputsMaxPrefix[C](
        r: Rule[C],
        p: List[C],
        t: Token[C],
        input: List[C],
        suffix: List[C],
        pBis: List[C]
    ): Unit = {
      decreases(input.size)

      require(p ++ suffix == input)
      require(ListUtils.isPrefix(p, input))
      require(ListUtils.isPrefix(pBis, input))
      require(pBis.size <= input.size)
      require(pBis.size > p.size)

      require(ruleValid(r))
      require(validRegex(r.regex))
      require(matchR(r.regex, p))
      require(t.getCharacters == p)
      val _ = ListUtils.lemmaIsPrefixRefl(input, input)
      require(findMaxPrefixOneRule(r, input) == Some(t, suffix))

      ListUtils.lemmaIsPrefixRefl(input, input)

      longestMatchNoBiggerStringMatch(r.regex, input, p, pBis)
    } ensuring (!matchR(r.regex, pBis))

    def lemmaMaxPrefOneRuleReturnsNoneThenNoPrefMaxRegex[C](
        r: Rule[C],
        p: List[C],
        input: List[C]
    ): Unit = {
      require(ListUtils.isPrefix(p, input))
      require(ruleValid(r))
      require(findMaxPrefixOneRule(r, input) == None[(Token[C], List[C])]())

      longestMatchNoBiggerStringMatch(r.regex, input, Nil(), p)

    } ensuring (!matchR(r.regex, p))

    def lemmaRuleInListAndRulesValidThenRuleIsValid[C](r: Rule[C], rules: List[Rule[C]]): Unit = {
      require(rules.contains(r))
      require(rulesValid(rules))
      rules match {
        case Cons(hd, tl) if (hd == r) => assert(ruleValid(r))
        case Cons(hd, tl) if (hd != r) => {
          assert(tl.contains(r))
          lemmaRuleInListAndRulesValidThenRuleIsValid(r, tl)
        }
        case Nil() => assert(false)
      }
    } ensuring (ruleValid(r))

    def lemmaInvariantOnRulesThenOnTail[C](r: Rule[C], rules: List[Rule[C]]): Unit = {
      require(rulesInvariant(Cons(r, rules)))
      assert(rulesValid(Cons(r, rules)) && noDuplicateTag(Cons(r, rules), Nil()))
      assert(rulesValid(rules))
      assert(noDuplicateTag(rules, List(r.tag)))

      lemmaNoDupTagThenAlsoWithSubListAcc(List(r.tag), Nil(), rules)
      assert(noDuplicateTag(rules, Nil()))

    } ensuring (rulesInvariant(rules))

    def lemmaNoDuplicateCanReorder[C](e1: Rule[C], e2: Rule[C], l: List[Rule[C]]): Unit = {
      require(noDuplicateTag(Cons(e1, Cons(e2, l)), List()))

      assert(noDuplicateTag(Cons(e1, Cons(e2, l)), List()) == noDuplicateTag(Cons(e2, l), List(e1.tag)))
      assert(noDuplicateTag(Cons(e2, l), List(e1.tag)) == noDuplicateTag(l, List(e2.tag, e1.tag)))
      assert(List(e2.tag, e1.tag).toSet == List(e1.tag, e2.tag).toSet)
      lemmaNoDuplicateSameWithAccWithSameContent(l, List(e2.tag, e1.tag), List(e1.tag, e2.tag))
      assert(noDuplicateTag(l, List(e2.tag, e1.tag)) == noDuplicateTag(l, List(e1.tag, e2.tag))) // TODO
    } ensuring (noDuplicateTag(Cons(e2, Cons(e1, l)), List()))

    def lemmaNoDuplicateSameWithAccWithSameContent[C](l: List[Rule[C]], acc: List[String], newAcc: List[String]): Unit = {
      require(noDuplicateTag(l, acc))
      require(acc.content == newAcc.content)

      l match {
        case Cons(hd, tl) => {
          ListSpecs.subsetContains(acc, newAcc)
          ListSpecs.subsetContains(newAcc, acc)
          assert(acc.contains(hd.tag) == newAcc.contains(hd.tag))
          lemmaNoDuplicateSameWithAccWithSameContent(tl, Cons(hd.tag, acc), Cons(hd.tag, newAcc))
        }
        case Nil() => ()
      }

    } ensuring (noDuplicateTag(l, newAcc))

    def lemmaNoDupTagThenAlsoWithSubListAcc[C](acc: List[String], newAcc: List[String], rules: List[Rule[C]]): Unit = {
      require(ListSpecs.subseq(newAcc, acc))
      require(noDuplicateTag(rules, acc))

      rules match {
        case Cons(hd, tl) => {
          lemmaNoDupTagThenAlsoWithSubListAcc(Cons(hd.tag, acc), Cons(hd.tag, newAcc), tl)
          ListSpecs.subseqNotContains(newAcc, acc, hd.tag)
        }
        case Nil() => ()
      }

    } ensuring (noDuplicateTag(rules, newAcc))

    def lemmaNoDuplicateTagAndDiffIndexThenNoTwoRulesEq[C](rules: List[Rule[C]], r1: Rule[C], r2: Rule[C]): Unit = {
      require(rules.contains(r1))
      require(rules.contains(r2))
      require(noDuplicateTag(rules))
      require(ListUtils.getIndex(rules, r1) < ListUtils.getIndex(rules, r2))

    } ensuring (r1 != r2)

    def lemmaNoDuplicateTagAndDiffIndexThenNoTwoRulesTagsEq[C](rules: List[Rule[C]], r1: Rule[C], r2: Rule[C]): Unit = {
      require(rules.contains(r1))
      require(rules.contains(r2))
      require(noDuplicateTag(rules))
      require(ListUtils.getIndex(rules, r1) < ListUtils.getIndex(rules, r2))

      if (rules.head == r1) {
        lemmaNoDuplicateAndTagInAccThenRuleCannotHaveSame(rules.tail, r2, r1.tag, List(r1.tag))
        assert(noDuplicateTag(rules) == noDuplicateTag(rules.tail, List(r1.tag)))
      } else {
        lemmaNoDupTagThenAlsoWithSubListAcc(List(rules.head.tag), Nil(), rules.tail)
        ListUtils.lemmaGetIndexBiggerAndHeadNotEqThenTailContains(rules, r1, r2)
        lemmaNoDuplicateTagAndDiffIndexThenNoTwoRulesTagsEq(rules.tail, r1, r2)
      }

    } ensuring (r1.tag != r2.tag)

    def lemmaNoDuplicateAndTagInAccThenRuleCannotHaveSame[C](rules: List[Rule[C]], r: Rule[C], tag: String, acc: List[String]): Unit = {
      require(acc.contains(tag))
      require(noDuplicateTag(rules, acc))
      require(rules.contains(r))

      rules match {
        case Nil()                   => check(false)
        case Cons(hd, tl) if hd == r => ()
        case Cons(hd, tl) if hd != r => lemmaNoDuplicateAndTagInAccThenRuleCannotHaveSame(tl, r, tag, Cons(hd.tag, acc))
      }
    } ensuring (r.tag != tag)

    def lemmaNonSepRuleNotContainsCharContainedInASepRule[C](rules: List[Rule[C]], rulesRec: List[Rule[C]], rNSep: Rule[C], rSep: Rule[C], c: C): Unit = {
      require(rulesInvariant(rules))
      require(rules.contains(rSep))
      require(rulesRec.contains(rNSep))
      require(rules.contains(rNSep))
      require(!rNSep.isSeparator)
      require(rSep.isSeparator)
      require(usedCharacters(rSep.regex).contains(c))
      require(sepAndNonSepRulesDisjointChars(rules, rulesRec))

      rulesRec match {
        case Cons(hd, tl) if hd == rNSep => lemmaNonSepRuleNotContainsCharContainedInASepRuleInner(rules, rNSep, rSep, c)
        case Cons(hd, tl)                => lemmaNonSepRuleNotContainsCharContainedInASepRule(rules, tl, rNSep, rSep, c)
        case Nil()                       => ()
      }

    } ensuring (!usedCharacters(rNSep.regex).contains(c))

    def lemmaNonSepRuleNotContainsCharContainedInASepRuleInner[C](rules: List[Rule[C]], rNSep: Rule[C], rSep: Rule[C], c: C): Unit = {
      require(rulesInvariant(rules))
      require(rules.contains(rSep))
      require(usedCharacters(rSep.regex).contains(c))
      require(!rNSep.isSeparator)
      require(rSep.isSeparator)
      require(ruleDisjointCharsFromAllFromOtherType(rNSep, rules))

      rules match {
        case Cons(hd, tl) if hd == rSep => ListSpecs.forallContained(usedCharacters(rSep.regex), (x: C) => !usedCharacters(rNSep.regex).contains(x), c)

        case Cons(hd, tl) => {
          lemmaInvariantOnRulesThenOnTail(hd, tl)
          lemmaNonSepRuleNotContainsCharContainedInASepRuleInner(tl, rNSep, rSep, c)
        }
        case Nil() => ()
      }

    } ensuring (!usedCharacters(rNSep.regex).contains(c))

    def lemmaSepRuleNotContainsCharContainedInANonSepRule[C](rules: List[Rule[C]], rulesRec: List[Rule[C]], rNSep: Rule[C], rSep: Rule[C], c: C): Unit = {
      require(rulesInvariant(rules))
      require(rules.contains(rSep))
      require(rulesRec.contains(rNSep))
      require(rules.contains(rNSep))
      require(!rNSep.isSeparator)
      require(rSep.isSeparator)
      require(usedCharacters(rNSep.regex).contains(c))
      require(sepAndNonSepRulesDisjointChars(rules, rulesRec))

      rulesRec match {
        case Cons(hd, tl) if hd == rNSep => lemmaSepRuleNotContainsCharContainedInANonSepRuleInner(rules, rNSep, rSep, c)
        case Cons(hd, tl)                => lemmaSepRuleNotContainsCharContainedInANonSepRule(rules, tl, rNSep, rSep, c)
        case Nil()                       => ()
      }

    } ensuring (!usedCharacters(rSep.regex).contains(c))

    def lemmaSepRuleNotContainsCharContainedInANonSepRuleInner[C](rules: List[Rule[C]], rNSep: Rule[C], rSep: Rule[C], c: C): Unit = {
      require(rulesInvariant(rules))
      require(rules.contains(rSep))
      require(usedCharacters(rNSep.regex).contains(c))
      require(!rNSep.isSeparator)
      require(rSep.isSeparator)
      require(ruleDisjointCharsFromAllFromOtherType(rNSep, rules))

      rules match {
        case Cons(hd, tl) if hd == rSep => ListSpecs.forallContained(usedCharacters(rNSep.regex), (x: C) => !usedCharacters(rSep.regex).contains(x), c)

        case Cons(hd, tl) => {
          lemmaInvariantOnRulesThenOnTail(hd, tl)
          lemmaSepRuleNotContainsCharContainedInANonSepRuleInner(tl, rNSep, rSep, c)
        }
        case Nil() => ()
      }

    } ensuring (!usedCharacters(rSep.regex).contains(c))

    def lemmaRulesProduceEachTokenIndividuallyThenForAnyToken[C](rules: List[Rule[C]], tokens: List[Token[C]], t: Token[C]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(tokens.contains(t))
      require(rulesProduceEachTokenIndividually(rules, tokens))

      tokens match {
        case Cons(hd, tl) if hd == t => ()
        case Cons(hd, tl)            => lemmaRulesProduceEachTokenIndividuallyThenForAnyToken(rules, tl, t)
        case Nil()                   => ()
      }
    } ensuring (rulesProduceIndivualToken(rules, t))

    def lemmaRulesProduceEachTokenIndividuallyThenForall[C](rules: List[Rule[C]], tokens: List[Token[C]]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rulesProduceEachTokenIndividually(rules, tokens))

      tokens match {
        case Cons(hd, tl) => lemmaRulesProduceEachTokenIndividuallyThenForall(rules, tl)
        case Nil()        => ()
      }

    } ensuring (tokens.forall(t => rulesProduceIndivualToken(rules, t)))

    def lemmaForallThenRulesProduceEachTokenIndividually[C](rules: List[Rule[C]], tokens: List[Token[C]]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(tokens.forall(t => rulesProduceIndivualToken(rules, t)))

      tokens match {
        case Cons(hd, tl) => lemmaForallThenRulesProduceEachTokenIndividually(rules, tl)
        case Nil()        => ()
      }

    } ensuring (rulesProduceEachTokenIndividually(rules, tokens))

    def lemmaConsecutiveTokensDisjointCharsFirstCharThenForAnyPair[C](rules: List[Rule[C]], tokens: List[Token[C]], t1: Token[C], t2: Token[C]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rulesProduceEachTokenIndividually(rules, tokens))
      require(tokensUseDisjointCharsFromFirstCharsNextToken(rules, tokens))
      require(ListUtils.consecutiveSubseq(List(t1, t2), tokens))

      tokens match {
        case Cons(hd1, Cons(hd2, tl)) if hd1 == t1 && hd2 == t2 => {
          ListSpecs.forallContained(tokens, (t: Token[C]) => rulesProduceIndivualToken(rules, t), t1)
          lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, t1.getCharacters, t1)
          ListSpecs.forallContained(tokens, (t: Token[C]) => rulesProduceIndivualToken(rules, t), t2)
          lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, t2.getCharacters, t2)
          val r1 = getRuleFromTag(rules, t1.getTag).get
          val r2 = getRuleFromTag(rules, t2.getTag).get
          assert(rulesFirstCharsAreNotUsedByTokenBefore(r1, r2))
        }
        case Cons(hd, tl) => lemmaConsecutiveTokensDisjointCharsFirstCharThenForAnyPair(rules, tl, t1, t2)
        case Nil()        => check(false)
      }

    } ensuring ({
      ListSpecs.subseqContains(List(t1, t2), tokens, t1)
      ListSpecs.subseqContains(List(t1, t2), tokens, t2)
      ListSpecs.forallContained(tokens, (t: Token[C]) => rulesProduceIndivualToken(rules, t), t1)
      lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, t1.getCharacters, t1)
      ListSpecs.forallContained(tokens, (t: Token[C]) => rulesProduceIndivualToken(rules, t), t2)
      lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, t2.getCharacters, t2)
      val r1 = getRuleFromTag(rules, t1.getTag).get
      val r2 = getRuleFromTag(rules, t2.getTag).get
      rulesFirstCharsAreNotUsedByTokenBefore(r1, r2)
    })
  }

}
