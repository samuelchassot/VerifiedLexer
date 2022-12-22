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
  import VerifiedDFAMatcher._
  import VerifiedDFA._
  import stainless.io.StdOut.println
  import stainless.io.State
  import VerifiedFunLexer._
  @extern
  def main(args: Array[String]): Unit = {
    // val rSep = ElementMatch(' ')
    // val ruleSep = Rule(rSep, "sep", true)
    // val sepToken = Token(List(' '), "sep", true)

    // val rAb = Concat(Concat(ElementMatch('a'), ElementMatch('b')), Star(Concat(ElementMatch('a'), ElementMatch('b'))))
    // val rule = Rule(rAb, "ab", false)

    // val rC = Concat(ElementMatch('c'), Star(ElementMatch('c')))
    // val ruleC = Rule(rC, "c", false)

    // val t1 = Token(List('a', 'b'), "ab", false)
    // val t2 = Token(List('c', 'c'), "c", false)

    // val input: List[Token[Char]] = List(t1, t2, t1, t2, t1, t1)
    // val rules = List(rule, ruleC, ruleSep)

    val state = State(BigInt(1))

    // val output: List[Char] = Lexer.printWithSeparatorTokenWhenNeeded(rules, input, sepToken)
    // println(output.foldLeft("")((s: String, c: Char) => s + c.toString))(state)
    DFATests()(state)

  }

  @extern
  def DFATests()(implicit @ghost state: State): Unit = {

    val startState = VerifiedDFA.State(0)
    val finalState = VerifiedDFA.State(5)
    val errState = VerifiedDFA.State(6)
    val transitions = List(
      Transition(startState, 'w', VerifiedDFA.State(1)),
      Transition(VerifiedDFA.State(1), 'h', VerifiedDFA.State(2)),
      Transition(VerifiedDFA.State(2), 'i', VerifiedDFA.State(3)),
      Transition(VerifiedDFA.State(3), 'l', VerifiedDFA.State(4)),
      Transition(VerifiedDFA.State(4), 'e', finalState)
    )
    val dfaWhile: DFA[Char] = DFA(startState, List(finalState), errState, transitions)
    val s1 = List('w', 'h', 'i', 'l', 'e')
    val s2 = List('w', 'h', 'i', 'l', 'e', 'w', 'h', 'i', 'l', 'e')
    val s3 = List('w', 'h', 'i', 'l')
    println("dfaWhile match s1: " + matchDFA(dfaWhile, s1).toString)
    println("dfaWhile longestmatch with s1: " + VerifiedDFAMatcher.findLongestMatch(dfaWhile, s1).toString)
    println("dfaWhile longestmatch with s2: " + VerifiedDFAMatcher.findLongestMatch(dfaWhile, s2).toString)
  }

}
object VerifiedFunLexer {
  import RegularExpression._
  import VerifiedRegexMatcher._
  import VerifiedDFA._
  import VerifiedDFAMatcher._

  case class Token[C](characters: List[C], tag: String, isSep: Boolean) {
    def getCharacters = characters
    def getTag = tag
    def isSeparator = isSep
  }
  case class Rule[C](dfa: DFA[C], tag: String, isSeparator: Boolean)

  object Lexer {

    @inline
    def ruleValid[C](r: Rule[C]): Boolean = {
      validDFA(r.dfa) && !matchDFA(r.dfa, Nil()) && r.tag != ""
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
      val ret: (List[Token[C]], List[C]) = maxPrefix(rules, input) match {
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

    /** Prints back the tokens to a list of characters of the type C, by adding a separatorToken between tokens when the maxPrefix would return another token if printed back to
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

      l match {
        case Cons(hd, tl) => {
          val suffix = printWithSeparatorTokenWhenNeeded(rules, tl, separatorToken)
          val maxPrefWithoutSep = maxPrefix(rules, hd.getCharacters ++ suffix)
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
    def maxPrefix[C](
        rulesArg: List[Rule[C]],
        input: List[C]
    ): Option[(Token[C], List[C])] = {
      require(rulesValid(rulesArg))
      require(!rulesArg.isEmpty)
      decreases(rulesArg.size)

      ListUtils.lemmaIsPrefixRefl(input, input)
      val ret: Option[(Token[C], List[C])] = rulesArg match {
        case Cons(hd, Nil()) => maxPrefixOneRule(hd, input)
        case Cons(hd, tl) => {
          val currentRulePref = maxPrefixOneRule(hd, input)
          val othersPrefix = maxPrefix(tl, input)
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
    def maxPrefixOneRule[C](
        rule: Rule[C],
        input: List[C]
    ): Option[(Token[C], List[C])] = {
      require(ruleValid(rule))

      val (longestPrefix, suffix) = VerifiedDFAMatcher.findLongestMatch(rule.dfa, input)
      if (longestPrefix.isEmpty) {
        None[(Token[C], List[C])]()
      } else {
        VerifiedDFAMatcher.longestMatchIsAcceptedByMatchOrIsEmpty(rule.dfa, input)
        Some[(Token[C], List[C])]((Token(longestPrefix, rule.tag, rule.isSeparator), suffix))
      }

    } ensuring (res =>
      res.isEmpty || matchDFA(
        rule.dfa,
        res.get._1.getCharacters
      ) && res.get._1.getCharacters ++ res.get._2 == input && res.get._2.size < input.size && res.get._1.getTag == rule.tag && res.get._1.isSeparator == rule.isSeparator
    )

    // Proofs --------------------------------------------------------------------------------------------------------------------------------

    // Correctness ---------------------------------------------------------------------------------------------------------------------------

    // The lexer is sound, i.e., if it produces a Tokenisation, it is valid w.r.t. the biggest prefix property
    def theoremLexSoundFirstChar[C](
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
      require({
        lemmaRuleInListAndRulesValidThenRuleIsValid(r, rules)
        tokens.isEmpty || matchDFA(r.dfa, tokens.head.getCharacters)
      })

      lemmaRuleInListAndRulesValidThenRuleIsValid(otherR, rules)
      if (ListUtils.getIndex(rules, r) > ListUtils.getIndex(rules, otherR)) {

        tokens match {
          case Nil() => {
            lemmaMaxPrefixReturnsNoneThenAnyRuleReturnsNone(otherR, rules, input)
            lemmaMaxPrefOneRuleReturnsNoneThenNoPrefMaxRegex(otherR, otherP, input)
          }
          case Cons(hd, tl) => {
            val (tok, suf) = maxPrefix(rules, input).get
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
            val (tok, suf) = maxPrefix(rules, input).get
            ListUtils.lemmaConcatTwoListThenFirstIsPrefix(hd.getCharacters, suf)
            ListUtils.lemmaSamePrefixThenSameSuffix(hd.getCharacters, suf, hd.getCharacters, ListUtils.getSuffix(input, hd.getCharacters), input)
            if (otherP.size > hd.getCharacters.size) {
              lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(rules, hd.getCharacters, input, suf, r)
              lemmaMaxPrefixOutputsMaxPrefix(rules, r, hd.getCharacters, input, otherP, otherR)
            }

          }
        }
      }

    } ensuring (if (ListUtils.getIndex(rules, otherR) < ListUtils.getIndex(rules, r)) !matchDFA(otherR.dfa, otherP)
                else tokens.size > 0 && otherP.size <= tokens.head.getCharacters.size || !matchDFA(otherR.dfa, otherP))

    // Invertability -------------------------------------------------------------------------------------------------------------------------

    def theoremInvertabilityFromTokensSepTokenWhenNeeded[C](rules: List[Rule[C]], tokens: List[Token[C]], separatorToken: Token[C]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rulesProduceEachTokenIndividually(rules, tokens))
      require(rulesProduceIndivualToken(rules, separatorToken))
      require(separatorToken.isSeparator)
      require(tokens.forall(!_.isSeparator))
      require({
        lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, separatorToken.getCharacters, separatorToken)
        getRuleFromTag(rules, separatorToken.getTag).get.isSeparator
      })

      tokens match {
        case Cons(hd, tl) => {
          val input = printWithSeparatorTokenWhenNeeded(rules, tokens, separatorToken)
          val suffixWithSep = separatorToken.getCharacters ++ printWithSeparatorTokenWhenNeeded(rules, tl, separatorToken)
          ListUtils.lemmaTwoListsConcatAssociativity(hd.getCharacters, separatorToken.getCharacters, printWithSeparatorTokenWhenNeeded(rules, tl, separatorToken))
          val suffixWithoutSep = printWithSeparatorTokenWhenNeeded(rules, tl, separatorToken)
          assert(input == hd.getCharacters ++ suffixWithSep || input == hd.getCharacters ++ suffixWithoutSep)

          if (input == hd.getCharacters ++ suffixWithSep) {
            val suffixAfterSep = printWithSeparatorTokenWhenNeeded(rules, tl, separatorToken)
            lemmaPrintWithSepTokenWhenNeededThenMaxPrefReturnsHead(rules, tokens, separatorToken)
            ListUtils.lemmaConcatTwoListThenFirstIsPrefix(hd.getCharacters, suffixWithSep)
            ListUtils.lemmaSamePrefixThenSameSuffix(hd.getCharacters, suffixWithSep, hd.getCharacters, maxPrefix(rules, input).get._2, input)

            val nextToken = tl.head
            val sepTokenOpt = maxPrefix(rules, suffixWithSep)
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

            // if (!usedCharacters(nextTokenRule.regex).contains(nextToken.getCharacters.head)) {
            //   lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(nextTokenRule.regex, nextToken.getCharacters, nextToken.getCharacters.head)
            //   check(false)
            // }
            // if (usedCharacters(separatorRule.regex).contains(suffixAfterSep.head)) {
            //   lemmaSepRuleNotContainsCharContainedInANonSepRule(rules, rules, nextTokenRule, separatorRule, suffixAfterSep.head)
            //   check(false)
            // }
            lemmaMaxPrefWithOtherTypeUsedCharAtStartOfSuffixReturnSame(rules, separatorToken, separatorRule, suffixAfterSep, nextTokenRule)

            theoremInvertabilityFromTokensSepTokenWhenNeeded(rules, tl, separatorToken)
          } else {
            lemmaPrintWithSepTokenWhenNeededThenMaxPrefReturnsHead(rules, tokens, separatorToken)
            theoremInvertabilityFromTokensSepTokenWhenNeeded(rules, tl, separatorToken)
            ListUtils.lemmaConcatTwoListThenFirstIsPrefix(hd.getCharacters, suffixWithoutSep)
            ListUtils.lemmaSamePrefixThenSameSuffix(hd.getCharacters, suffixWithoutSep, hd.getCharacters, maxPrefix(rules, input).get._2, input)
          }
        }
        case Nil() => ()
      }
    } ensuring (lex(rules, printWithSeparatorTokenWhenNeeded(rules, tokens, separatorToken))._1.filter(!_.isSeparator) == tokens)

    def theoremInvertFromString[C](rules: List[Rule[C]], input: List[C]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      decreases(input.size)

      val (tokens, suffix) = lex(rules, input)
      if (suffix.isEmpty) {
        tokens match {
          case Cons(hd, Nil()) => ()
          case Cons(hd, tl)    => theoremInvertFromString(rules, maxPrefix(rules, input).get._2)
          case Nil()           => ()
        }
      } else {
        tokens match {
          case Cons(hd, Nil()) => assert(print(tokens) ++ suffix == input)
          case Cons(hd, tl) => {
            theoremInvertFromString(rules, maxPrefix(rules, input).get._2)
            lemmaRemovingFirstTokensCharactersPreservesLexSuffix(rules, input, tokens, suffix)

            assert(input == maxPrefix(rules, input).get._1.getCharacters ++ maxPrefix(rules, input).get._2)
            assert(input == maxPrefix(rules, input).get._1.getCharacters ++ (print(tl) ++ suffix))
            ListUtils.lemmaTwoListsConcatAssociativity(
              maxPrefix(rules, input).get._1.getCharacters,
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

    def lemmaPrintWithSepTokenWhenNeededThenMaxPrefReturnsHead[C](rules: List[Rule[C]], tokens: List[Token[C]], separatorToken: Token[C]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rulesProduceEachTokenIndividually(rules, tokens))
      require(rulesProduceIndivualToken(rules, separatorToken))
      require(separatorToken.isSeparator)
      require(tokens.forall(!_.isSeparator))

      tokens match {
        case Cons(hd, tl) => {
          lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, separatorToken.getCharacters, separatorToken)
          val separatorRule = getRuleFromTag(rules, separatorToken.getTag).get

          lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, hd.getCharacters, hd)
          val rule = getRuleFromTag(rules, hd.getTag).get

          val suffix = printWithSeparatorTokenWhenNeeded(rules, tl, separatorToken)
          val maxPrefWithoutSep = maxPrefix(rules, hd.getCharacters ++ suffix)
          maxPrefWithoutSep match {
            case Some((t, s)) if t == hd => ()
            case Some((t, s)) if t != hd => {
              ListUtils.lemmaTwoListsConcatAssociativity(hd.getCharacters, separatorToken.getCharacters, suffix)
              val resSuffix = separatorToken.getCharacters ++ suffix
              // if (!usedCharacters(separatorRule.regex).contains(separatorToken.getCharacters.head)) {
              //   lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(separatorRule.regex, separatorToken.getCharacters, separatorToken.getCharacters.head)
              //   check(false)
              // }

              check(maxPrefix(rules, hd.getCharacters).isDefined)
              check(maxPrefix(rules, hd.getCharacters).get._1 == hd)
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
        maxPrefix(rules, printWithSeparatorTokenWhenNeeded(rules, tokens, separatorToken)).isDefined &&
        maxPrefix(rules, printWithSeparatorTokenWhenNeeded(rules, tokens, separatorToken)).get._1 == tokens.head))

    def lemmaMaxPrefWithOtherTypeUsedCharAtStartOfSuffixReturnSame[C](rules: List[Rule[C]], token: Token[C], rule: Rule[C], suffix: List[C], anOtherTypeRule: Rule[C]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rules.contains(rule))
      require(rules.contains(anOtherTypeRule))
      require(anOtherTypeRule.isSeparator != rule.isSeparator)
      require(maxPrefix(rules, token.getCharacters).isDefined)
      require(maxPrefix(rules, token.getCharacters).get._1 == token)
      require(maxPrefix(rules, token.getCharacters).get._2.isEmpty)
      require(token.getTag == rule.tag)
      require(token.isSeparator == rule.isSeparator)
      require({
        lemmaRuleInListAndRulesValidThenRuleIsValid(rule, rules)
        matchDFA(rule.dfa, token.getCharacters)
      })
      require(!suffix.isEmpty)

      val input = token.getCharacters ++ suffix
      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(token.getCharacters, suffix)
      val tokenOpt = maxPrefix(rules, input)
      lemmaLexIsDefinedWithStrThenLexWithSuffixIsDefined(rules, token.getCharacters, suffix)
      val foundToken = tokenOpt.get._1
      val foundSuffix = tokenOpt.get._2
      lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, input, foundToken)
      val foundRule = getRuleFromTag(rules, foundToken.getTag).get
      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(foundToken.getCharacters, foundSuffix)
      assert(ListUtils.isPrefix(foundToken.getCharacters, input))
      assert(foundRule.tag == foundToken.getTag)
      assert(matchDFA(foundRule.dfa, foundToken.getCharacters))
      assert(foundRule.isSeparator == foundToken.isSeparator)

      lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(rules, foundToken.getCharacters, input, foundSuffix, foundRule)
      ListUtils.lemmaSamePrefixThenSameSuffix(foundToken.getCharacters, foundSuffix, foundToken.getCharacters, ListUtils.getSuffix(input, foundToken.getCharacters), input)
      assert(ListUtils.getSuffix(input, foundToken.getCharacters) == foundSuffix)
      assert(maxPrefixOneRule(foundRule, input) == Some((foundToken, ListUtils.getSuffix(input, foundToken.getCharacters))))

      // if (!usedCharacters(rule.regex).contains(foundToken.getCharacters.head)) {
      //   lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(rule.regex, token.getCharacters, foundToken.getCharacters.head)
      //   check(false)
      // }
      // if (rule.isSeparator) {
      //   if (!foundRule.isSeparator) {
      //     assert(token.getCharacters.contains(foundToken.getCharacters.head))
      //     assert(usedCharacters(rule.regex).contains(foundToken.getCharacters.head))
      //     lemmaNonSepRuleNotContainsCharContainedInASepRule(rules, rules, foundRule, rule, foundToken.getCharacters.head)
      //     lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(foundRule.regex, foundToken.getCharacters, foundToken.getCharacters.head)
      //     check(false)
      //   }
      // } else {
      //   if (foundRule.isSeparator) {
      //     assert(token.getCharacters.contains(foundToken.getCharacters.head))
      //     assert(usedCharacters(rule.regex).contains(foundToken.getCharacters.head))
      //     lemmaSepRuleNotContainsCharContainedInANonSepRule(rules, rules, rule, foundRule, foundToken.getCharacters.head)
      //     lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(foundRule.regex, foundToken.getCharacters, foundToken.getCharacters.head)
      //     check(false)
      //   }
      // }

      if (foundToken.getCharacters.size > token.getCharacters.size) {
        ListUtils.lemmaLongerPrefixContainsHeadOfSuffixOfSmallerPref(token.getCharacters, suffix, foundToken.getCharacters, input)
        // if (rule.isSeparator) {
        //   lemmaSepRuleNotContainsCharContainedInANonSepRule(rules, rules, anOtherTypeRule, foundRule, suffix.head)
        //   lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(foundRule.regex, foundToken.getCharacters, suffix.head)
        //   check(false)
        // } else {
        //   lemmaNonSepRuleNotContainsCharContainedInASepRule(rules, rules, foundRule, anOtherTypeRule, suffix.head)
        //   lemmaRegexCannotMatchAStringContainingACharItDoesNotContain(foundRule.regex, foundToken.getCharacters, suffix.head)
        //   check(false)
        // }
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

    } ensuring (maxPrefix(rules, token.getCharacters ++ suffix) == Some((token, suffix)))

    def lemmaLexIsDefinedWithStrThenLexWithSuffixIsDefined[C](rules: List[Rule[C]], input: List[C], suffix: List[C]): Unit = {
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(!lex(rules, input)._1.isEmpty)

      val (tokens, _) = lex(rules, input)
      val firstT = tokens.head
      ListUtils.lemmaConcatTwoListThenFirstIsPrefix(firstT.getCharacters, maxPrefix(rules, input).get._2)
      ListUtils.lemmaPrefixStaysPrefixWhenAddingToSuffix(firstT.getCharacters, input, suffix)
      lemmaMaxPrefReturnTokenSoItsTagBelongsToARule(rules, input, firstT)
      val rule: Rule[C] = getRuleFromTag(rules, firstT.getTag).get
      assert(matchDFA(rule.dfa, firstT.getCharacters))

      if (maxPrefix(rules, input ++ suffix).isEmpty) {
        lemmaMaxPrefixReturnsNoneThenAnyRuleReturnsNone(rule, rules, input ++ suffix)
        lemmaMaxPrefOneRuleReturnsNoneThenNoPrefMaxRegex(rule, firstT.getCharacters, input ++ suffix)
        check(false)
      }

    } ensuring (maxPrefix(rules, input ++ suffix).isDefined)

    def lemmaMaxPrefReturnTokenSoItsTagBelongsToARule[C](rules: List[Rule[C]], input: List[C], token: Token[C]): Unit = {
      require(rulesInvariant(rules))
      require(!rules.isEmpty)
      require(maxPrefix(rules, input).isDefined && maxPrefix(rules, input).get._1 == token)

      rules match {
        case Cons(hd, tl) => {
          if (maxPrefixOneRule(hd, input).isDefined && maxPrefixOneRule(hd, input).get._1 == token) {
            assert(hd.tag == token.getTag)
            assert(matchDFA(hd.dfa, token.getCharacters))
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
    } ensuring (getRuleFromTag(rules, token.getTag).isDefined && matchDFA(getRuleFromTag(rules, token.getTag).get.dfa, token.getCharacters) &&
      token.isSeparator == getRuleFromTag(rules, token.getTag).get.isSeparator)

    def lemmaGetRuleFromTagInListThenSameListWhenAddingARuleDiffTag[C](rules: List[Rule[C]], newHd: Rule[C], tag: String): Unit = {
      require(rulesInvariant(Cons(newHd, rules)))
      require({
        lemmaInvariantOnRulesThenOnTail(newHd, rules)
        getRuleFromTag(rules, tag).isDefined
      })

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
    } ensuring (lex(rules, maxPrefix(rules, input).get._2) == (producedTokens.tail, suffix))

    def lemmaMaxPrefNoneThenNoRuleMatches[C](rules: List[Rule[C]], r: Rule[C], p: List[C], input: List[C]): Unit = {
      require(ListUtils.isPrefix(p, input))
      require(!rules.isEmpty)
      require(rulesInvariant(rules))
      require(rules.contains(r))
      require(maxPrefix(rules, input) == None[(Token[C], List[C])]())

      lemmaRuleInListAndRulesValidThenRuleIsValid(r, rules)

      lemmaMaxPrefixReturnsNoneThenAnyRuleReturnsNone(r, rules, input)
      lemmaMaxPrefOneRuleReturnsNoneThenNoPrefMaxRegex(r, p, input)

    } ensuring (!matchDFA(r.dfa, p))

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
      require(maxPrefix(rules, input) == Some(Token(p, r.tag, r.isSeparator), ListUtils.getSuffix(input, p)))
      require(ListUtils.getIndex(rules, rBis) < ListUtils.getIndex(rules, r))
      require(ruleValid(r))
      require(matchDFA(r.dfa, p))

      assert(ListUtils.getIndex(rules, rBis) < ListUtils.getIndex(rules, r))

      lemmaRuleInListAndRulesValidThenRuleIsValid(rBis, rules)
      lemmaRuleInListAndRulesValidThenRuleIsValid(r, rules)
      rules match {
        case Cons(hd, tl) if hd == rBis => {
          ListUtils.lemmaGetIndexBiggerAndHeadEqThenTailContains(rules, rBis, r)
          lemmaNoDuplicateTagAndDiffIndexThenNoTwoRulesEq(rules, rBis, r)

          val tokenSuffOpt = maxPrefixOneRule(rBis, input)
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
              check(!matchDFA(rBis.dfa, p))
            } else {
              if (token.getCharacters.size < p.size) {
                ListUtils.lemmaConcatTwoListThenFirstIsPrefix(token.getCharacters, suff)
                lemmaMaxPrefixOneRuleOutputsMaxPrefix(rBis, token.getCharacters, token, input, suff, p)
                check(!matchDFA(rBis.dfa, p))
              } else {
                lemmaNoDuplicateTagAndDiffIndexThenNoTwoRulesTagsEq(rules, rBis, r)
                check(Some(token, suff) != Some(Token(p, r.tag, r.isSeparator), ListUtils.getSuffix(input, p)))
                check(!matchDFA(rBis.dfa, p))
              }
            }
          }
        }
        case Cons(hd, tl) if hd != rBis => {
          assert(tl.contains(r))
          assert(tl.contains(rBis))

          val tokenSuffOpt = maxPrefixOneRule(hd, input)
          val tokenSuffTailOpt = maxPrefix(tl, input)

          lemmaInvariantOnRulesThenOnTail(hd, tl)
          lemmaNoDuplicateTagAndDiffIndexThenNoTwoRulesTagsEq(rules, hd, r)
          lemmaMaxPrefNoSmallerRuleMatches(tl, r, p, input, rBis)
        }
        case Nil() => check(false)
      }
    } ensuring (!matchDFA(rBis.dfa, p))

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
        !matchDFA(r.dfa, p)
      })
      require({
        ListUtils.lemmaIsPrefixRefl(input, input)
        maxPrefixOneRule(r, input) == Some(Token(p, r.tag, r.isSeparator), ListUtils.getSuffix(input, p))
      })

      require(pBis.size > p.size)

      require(maxPrefix(rules, input) == Some(Token(p, r.tag, r.isSeparator), ListUtils.getSuffix(input, p)))

      // For preconditions
      lemmaRuleInListAndRulesValidThenRuleIsValid(r, rules)
      lemmaRuleInListAndRulesValidThenRuleIsValid(rBis, rules)
      ListUtils.lemmaIsPrefixRefl(input, input)

      // Main lemma
      lemmaMaxPrefixOutputsMaxPrefixInner(rules, r, p, input, pBis, rBis)

    } ensuring (!matchDFA(rBis.dfa, pBis))

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

      require(validDFA(r.dfa))
      require(matchDFA(r.dfa, p))
      require(ruleValid(r))
      require({
        ListUtils.lemmaIsPrefixRefl(input, input)
        maxPrefixOneRule(r, input) == Some(Token(p, r.tag, r.isSeparator), ListUtils.getSuffix(input, p))
      })

      require(pBis.size > p.size)

      require(ruleValid(rBis))
      require(maxPrefix(rules, input) == Some(Token(p, r.tag, r.isSeparator), ListUtils.getSuffix(input, p)))

      assert(validDFA(r.dfa))

      ListUtils.lemmaIsPrefixThenSmallerEqSize(pBis, input)
      lemmaRuleInListAndRulesValidThenRuleIsValid(rBis, rules)

      val bisTokenSuff = maxPrefixOneRule(rBis, input) // == Some(Token(pBis, rBis.tag), ListUtils.getSuffix(input, pBis))
      if (bisTokenSuff.isEmpty) {
        lemmaMaxPrefOneRuleReturnsNoneThenNoPrefMaxRegex(rBis, pBis, input)
        check(!matchDFA(rBis.dfa, pBis))
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
          check(!matchDFA(rBis.dfa, pBis))
        } else {
          if (tBis.getCharacters.size < pBis.size) {
            assert(ListUtils.isPrefix(tBis.getCharacters, input))
            lemmaMaxPrefixOneRuleOutputsMaxPrefix(rBis, tBis.getCharacters, tBis, input, suffixBis, pBis)
            check(!matchDFA(rBis.dfa, pBis))
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
            check(!matchDFA(rBis.dfa, pBis))

          }
        }

      }

    } ensuring (!matchDFA(rBis.dfa, pBis))

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
      require(input == p ++ suffix)
      require(maxPrefix(rules, input) == Some(Token(p, r.tag, r.isSeparator), suffix))
      require({
        lemmaRuleInListAndRulesValidThenRuleIsValid(r, rules)
        matchDFA(r.dfa, p)
      })
      decreases(rules.size)

      rules match {
        case Cons(hd, tl) if hd == r => {
          lemmaInvariantOnRulesThenOnTail(hd, tl)
          if (tl.isEmpty) {
            check(maxPrefixOneRule(r, input) == Some(Token(p, r.tag, r.isSeparator), suffix))
          } else {
            lemmaNoDuplTagThenTailRulesCannotProduceHeadTagInTok(hd, tl, input)
            assert(maxPrefix(tl, input).isEmpty || maxPrefix(tl, input).get._1.getTag != r.tag)
            check(maxPrefixOneRule(r, input) == Some(Token(p, r.tag, r.isSeparator), suffix))
          }
        }
        case Cons(hd, tl) if hd != r => {
          lemmaInvariantOnRulesThenOnTail(hd, tl)
          val otherTokSufOpt = maxPrefixOneRule(hd, input)
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
              assert(maxPrefixOneRule(hd, input) != Some(Token(p, r.tag, r.isSeparator), suffix))
              assert(maxPrefix(tl, input) == Some(Token(p, r.tag, r.isSeparator), suffix))
              lemmaMaxPrefixTagSoFindMaxPrefOneRuleWithThisRule(tl, p, input, suffix, r)
            }

          }
        }
        case Nil() => check(false)

      }

    } ensuring (maxPrefixOneRule(r, input) == Some(Token(p, r.tag, r.isSeparator), suffix))

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

    } ensuring (maxPrefix(rTail, input).isEmpty || maxPrefix(rTail, input).get._1.getTag != rHead.tag)

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
      require(maxPrefix(rules, input) == Some(t, suffix))
      require(ruleValid(rBis))
      require({
        ListUtils.lemmaIsPrefixRefl(input, input)
        maxPrefixOneRule(rBis, input) == Some(tBis, suffixBis)
      })
      require(tBis.getTag == rBis.tag)
      require(tBis.getCharacters == pBis)
      require(pBis ++ suffixBis == input)

      rules match {
        case Cons(hd, Nil()) => ()
        case Cons(hd, tl) => {
          if (hd == rBis) {
            check(pBis.size <= p.size)
          } else {
            if (maxPrefixOneRule(hd, input) == Some(t, suffix)) {
              val othersPrefix = maxPrefix(tl, input)
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

      require(maxPrefix(rules, input).isEmpty)

      lemmaRuleInListAndRulesValidThenRuleIsValid(r, rules)

      rules match {
        case Cons(hd, tl) if r == hd => ()
        case Cons(hd, tl) if r != hd => {

          lemmaMaxPrefixReturnsNoneThenAnyRuleReturnsNone(r, tl, input)
        }
        case Nil() => ()
      }

    } ensuring (maxPrefixOneRule(r, input).isEmpty)

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
      require(validDFA(r.dfa))
      require(matchDFA(r.dfa, p))
      require(t.getCharacters == p)
      require({
        ListUtils.lemmaIsPrefixRefl(input, input)
        maxPrefixOneRule(r, input) == Some(t, suffix)
      })

      ListUtils.lemmaIsPrefixRefl(input, input)

      VerifiedDFAMatcher.longestMatchNoBiggerStringMatch(r.dfa, input, p, pBis)
    } ensuring (!matchDFA(r.dfa, pBis))

    def lemmaMaxPrefOneRuleReturnsNoneThenNoPrefMaxRegex[C](
        r: Rule[C],
        p: List[C],
        input: List[C]
    ): Unit = {
      require(ListUtils.isPrefix(p, input))
      require(ruleValid(r))
      require(maxPrefixOneRule(r, input) == None[(Token[C], List[C])]())

      VerifiedDFAMatcher.longestMatchNoBiggerStringMatch(r.dfa, input, Nil(), p)

    } ensuring (!matchDFA(r.dfa, p))

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
      assert(noDuplicateTag(l, List(e2.tag, e1.tag)) == noDuplicateTag(l, List(e1.tag, e2.tag)))
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

  }

}
