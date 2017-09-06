/*

    This file is part of the Maude 2 interpreter.

    Copyright 1997-2003 SRI International, Menlo Park, CA 94025, USA.

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307, USA.

*/

/*
 *	Commands.
 */
command		:	KW_SELECT		{ lexerCmdMode(); clear(); }
			cToken			{ store($3); }
			cTokensBarDot '.'
			{
			  lexerInitialMode();
			  interpreter.setCurrentModule(bubble);
			}
		|	KW_DUMP			{ lexerCmdMode(); clear(); }
			cToken			{ store($3); }
			cTokensBarDot '.'
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(bubble))
			    CM->dump();
			}
		|	KW_PARSE
			{
			  lexerCmdMode();
			  clear();
			  moduleExpr.contractTo(0);
			}
			moduleAndTerm
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(moduleExpr, 1))
			    interpreter.parse(bubble);
			}

		|	KW_CREDUCE
			{
			  lexerCmdMode();
			  clear();
			  moduleExpr.contractTo(0);
			}
			moduleAndTerm
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(moduleExpr, 1))
			    interpreter.creduce(bubble);
			}

		|	optDebug KW_REDUCE
			{
			  lexerCmdMode();
			  clear();
			  moduleExpr.contractTo(0);
			}
			moduleAndTerm
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(moduleExpr, 1))
			    interpreter.reduce(bubble, $1);
			}

		|	optDebug KW_REWRITE
			{
			  lexerCmdMode();
			  clear();
			  moduleExpr.contractTo(0);
			  number = NONE;
			}
			numberModuleTerm
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(moduleExpr, 1))
			    interpreter.rewrite(bubble, number, $1);
			}
		|	optDebug KW_EREWRITE
			{
			  lexerCmdMode();
			  clear();
			  moduleExpr.contractTo(0);
			  number = NONE;
			  number2 = NONE;
			}
			numbersModuleTerm
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(moduleExpr, 1))
			    interpreter.eRewrite(bubble, number, number2, $1);
			}
		|	optDebug KW_FREWRITE
			{
			  lexerCmdMode();
			  clear();
			  moduleExpr.contractTo(0);
			  number = NONE;
			  number2 = NONE;
			}
			numbersModuleTerm
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(moduleExpr, 1))
			    interpreter.fRewrite(bubble, number, number2, $1);
			}
		|	optDebug KW_SREWRITE
			{
			  lexerCmdMode();
			  clear();
			  moduleExpr.contractTo(0);
			  number = NONE;
			}
			numberModuleTerm
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(moduleExpr, 1))
			    interpreter.sRewrite(bubble, number, $1);
			}
		|	KW_SEARCH
			{
			  lexerCmdMode();
			  clear();
			  moduleExpr.contractTo(0);
			  number = NONE;
			  number2 = NONE;
			}
			numbersModuleTerm
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(moduleExpr, 1))
			    interpreter.search(bubble, number, number2);
			}
		|	match
			{
			  lexerCmdMode();
			  clear();
			  moduleExpr.contractTo(0);
			  number = NONE;
			}
			numberModuleTerm
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(moduleExpr, 1))
			    interpreter.match(bubble, $1, number);
			}
		|	unify
			{
			  lexerCmdMode();
			  clear();
			  moduleExpr.contractTo(0);
			  number = NONE;
			}
			numberModuleTerm
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(moduleExpr, 1))
			    interpreter.unify(bubble, $1, number);
			}
		|	optDebug KW_CONTINUE optNumber '.'
			{
			  interpreter.cont($3, $1);
			}
		|	KW_LOOP
			{
			  lexerCmdMode();
			  clear();
			  moduleExpr.contractTo(0);
			}
			moduleAndTerm
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(moduleExpr, 1))
			    interpreter.loop(bubble);
			}
		|	'('			{ lexerCmdMode(); clear(); }
			cTokens	')'
			{
			  lexerInitialMode();
			  moduleExpr.contractTo(0);
			  if (interpreter.setCurrentModule(moduleExpr))  // HACK
			    interpreter.contLoop(bubble);
			}

		|	KW_TRACE select		{ lexerCmdMode(); }
			cOpNameList '.'
			{
			  lexerInitialMode();
			  interpreter.traceSelect($2);
			}
		|	KW_TRACE exclude		{ lexerCmdMode(); }
			cOpNameList '.'
			{
			  lexerInitialMode();
			  interpreter.traceExclude($2);
			}
		|	KW_BREAK select		{ lexerCmdMode(); }
			cOpNameList '.'
			{
			  lexerInitialMode();
			  interpreter.breakSelect($2);
			}
		|	KW_PRINT conceal		{ lexerCmdMode(); }
			cOpNameList '.'
			{
			  lexerInitialMode();
			  interpreter.printConceal($2);
			}
		|	KW_DO KW_CLEAR KW_MEMO '.'
			{
			  if (CM != 0)  // HACK
			    CM->getFlatSignature()->clearMemo();
			}
/*
 *	Commands to show interpreter state.
 */
		|	KW_SHOW KW_MOD		{ lexerCmdMode(); clear(); }
			cTokensBarDot '.'
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(bubble))
			    CM->showModule();
			}
		|	KW_SHOW KW_MODULE	{ lexerCmdMode(); clear(); }
			cTokensBarDot '.'
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(bubble))
			    CM->showModule();
			}
		|	KW_SHOW KW_ALL		{ lexerCmdMode(); clear(); }
			cTokensBarDot '.'
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(bubble))
			    interpreter.showModule(true);
			}
		|	KW_SHOW KW_VIEW		{ lexerCmdMode(); clear(); }
			cTokensBarDot '.'
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentView(bubble))
			    interpreter.showView();
			}
		|	KW_SHOW KW_MODULES '.'
			{
			  interpreter.showModules(true);
			}
		|	KW_SHOW KW_VIEWS '.'
			{
			  interpreter.showNamedViews();
			}
		|	KW_SHOW KW_SORTS	{ lexerCmdMode(); clear(); }
			cTokensBarDot '.'
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(bubble))
			    interpreter.showSortsAndSubsorts();
			}
		|	KW_SHOW KW_OPS		{ lexerCmdMode(); clear(); }
			cTokensBarDot '.'
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(bubble))
			    interpreter.showOps();
			}
		|	KW_SHOW KW_VARS		{ lexerCmdMode(); clear(); }
			cTokensBarDot '.'
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(bubble))
			    interpreter.showVars();
			}
		|	KW_SHOW KW_MBS		{ lexerCmdMode(); clear(); }
			cTokensBarDot '.'
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(bubble))
			    interpreter.showMbs();
			}
		|	KW_SHOW KW_EQS		{ lexerCmdMode(); clear(); }
			cTokensBarDot '.'
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(bubble))
			    interpreter.showEqs();
			}
		|	KW_SHOW KW_RLS		{ lexerCmdMode(); clear(); }
			cTokensBarDot '.'
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(bubble))
			    interpreter.showRls();
			}
		|	KW_SHOW KW_SUMMARY	{ lexerCmdMode(); clear(); }
			cTokensBarDot '.'
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(bubble))
			    interpreter.showSummary();
			}
		|	KW_SHOW KW_KINDS	{ lexerCmdMode(); clear(); }
			cTokensBarDot '.'
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(bubble))
			    interpreter.showKinds();
			}
		|	KW_SHOW KW_PATH SIMPLE_NUMBER '.'
			{
			  interpreter.showSearchPath($3);
			}
		|	KW_SHOW KW_PATH KW_LABEL SIMPLE_NUMBER '.'
			{
			  interpreter.showSearchPathLabels($4);
			}
		|	KW_SHOW KW_SEARCH KW_GRAPH '.'
			{
			  interpreter.showSearchGraph();
			}
		|	KW_SHOW KW_PROFILE	{ lexerCmdMode(); clear(); }
			cTokensBarDot '.'
			{
			  lexerInitialMode();
			  if (interpreter.setCurrentModule(bubble))
			    interpreter.showProfile();
			}
/*
 *	Commands to set interpreter state variables.
 */
		|	KW_SET KW_SHOW KW_ADVISE polarity '.'
			{
			  globalAdvisoryFlag = $4;
			}
		|	KW_SET KW_SHOW KW_STATS polarity '.'
			{
			  interpreter.setFlag(Interpreter::SHOW_STATS, $4);
			}
		|	KW_SET KW_SHOW KW_LOOP KW_STATS polarity '.'
			{
			  interpreter.setFlag(Interpreter::SHOW_LOOP_STATS, $5);
			}
		|	KW_SET KW_SHOW KW_TIMING polarity '.'
			{
			  interpreter.setFlag(Interpreter::SHOW_TIMING, $4);
			}
		|	KW_SET KW_SHOW KW_BREAKDOWN polarity '.'
			{
			  interpreter.setFlag(Interpreter::SHOW_BREAKDOWN, $4);
			}
		|	KW_SET KW_SHOW KW_LOOP KW_TIMING polarity '.'
			{
			  interpreter.setFlag(Interpreter::SHOW_LOOP_TIMING, $5);
			}
		|	KW_SET KW_SHOW KW_CMD polarity '.'
			{
			  interpreter.setFlag(Interpreter::SHOW_COMMAND, $4);
			}
		|	KW_SET KW_SHOW KW_GC polarity '.'
			{
			  MemoryCell::setShowGC($4);
			}
		|	KW_SET KW_PRINT printOption polarity '.'
			{
			  interpreter.setPrintFlag($3, $4);
			}
		|	KW_SET KW_TRACE traceOption polarity '.'
			{
			  interpreter.setFlag($3, $4);
			}
		|	KW_SET KW_BREAK polarity '.'
			{
			  interpreter.setFlag(Interpreter::BREAK, $3);
			}
		|	KW_SET importMode		{ lexerCmdMode(); }
			cSimpleTokenBarDot		{ lexerInitialMode(); }
			polarity '.'
			{
			  interpreter.setAutoImport($2, $4, $6);
			}
		|	KW_SET KW_OMOD KW_INCLUDE	{ lexerCmdMode(); }
			cSimpleTokenBarDot		{ lexerInitialMode(); }
			polarity '.'
			{
			  interpreter.setOmodInclude($5, $7);
			}
		|	KW_SET KW_VERBOSE polarity '.'
			{
			  globalVerboseFlag = $3;
			}
		|	KW_SET KW_CLEAR KW_MEMO polarity '.'
			{
			  interpreter.setFlag(Interpreter::AUTO_CLEAR_MEMO, $4);
			}
		|	KW_SET KW_CLEAR KW_RLS polarity '.'
			{
			  interpreter.setFlag(Interpreter::AUTO_CLEAR_RULES, $4);
			}
		|	KW_SET KW_COMPILE KW_COUNT polarity '.'
			{
			  interpreter.setFlag(Interpreter::COMPILE_COUNT, $4);
			}
		|	KW_SET KW_PROFILE polarity '.'
			{
			  interpreter.setFlag(Interpreter::PROFILE, $3);
			}
		|	KW_SET KW_CLEAR KW_PROFILE polarity '.'
			{
			  interpreter.setFlag(Interpreter::AUTO_CLEAR_PROFILE, $4);
			}
/*
 *	Debugger mode commands
 */
		|	KW_RESUME '.'
			{
			  PARSE_RESULT = UserLevelRewritingContext::RESUME;
			}
		|	KW_ABORT '.'
			{
			  PARSE_RESULT = UserLevelRewritingContext::ABORT;
			}
		|	KW_STEP '.'
			{
			  PARSE_RESULT = UserLevelRewritingContext::STEP;
			}
		|	KW_WHERE '.'
			{
			  PARSE_RESULT = UserLevelRewritingContext::WHERE;
			}
/*
 *	OBJ3 legacy cruft.
 */
		|	KW_SET KW_GC KW_SHOW polarity '.'
			{
			  MemoryCell::setShowGC($4);
			}
		|	KW_SET KW_STATS polarity '.'
			{
			  interpreter.setFlag(Interpreter::SHOW_STATS, $3);
			}
/*
 *	Error recovery.
 */
		|	error			{ lexerInitialMode(); }
			'.'
		;

/*
 *	Options
 */
printOption	:	KW_MIXFIX		{ $$ = Interpreter::PRINT_MIXFIX; }
		|	KW_FLAT			{ $$ = Interpreter::PRINT_FLAT; }
		|	KW_WITH KW_ALIASES	{ $$ = Interpreter::PRINT_WITH_ALIASES; }
		|	KW_WITH KW_PARENS	{ $$ = Interpreter::PRINT_WITH_PARENS; }
		|	KW_GRAPH		{ $$ = Interpreter::PRINT_GRAPH; }
		|	KW_CONCEAL		{ $$ = Interpreter::PRINT_CONCEAL; }
		|	KW_NUMBER		{ $$ = Interpreter::PRINT_NUMBER; }
		|	KW_RAT			{ $$ = Interpreter::PRINT_RAT; }
		|	KW_COLOR		{ $$ = Interpreter::PRINT_COLOR; }
		|	KW_FORMAT		{ $$ = Interpreter::PRINT_FORMAT; }
		;

traceOption	:				{ $$ = Interpreter::TRACE; }
		|	KW_CONDITION		{ $$ = Interpreter::TRACE_CONDITION; }
		|	KW_WHOLE		{ $$ = Interpreter::TRACE_WHOLE; }
		|	KW_SUBSTITUTION		{ $$ = Interpreter::TRACE_SUBSTITUTION; }
		|	KW_SELECT		{ $$ = Interpreter::TRACE_SELECT; }
		|	KW_MBS			{ $$ = Interpreter::TRACE_MB; }
		|	KW_EQS			{ $$ = Interpreter::TRACE_EQ; }
		|	KW_RLS			{ $$ = Interpreter::TRACE_RL; }
		|	KW_REWRITE		{ $$ = Interpreter::TRACE_REWRITE; }
		|	KW_BODY			{ $$ = Interpreter::TRACE_BODY; }
		|	KW_BUILTIN		{ $$ = Interpreter::TRACE_BUILTIN; }
		;

polarity	:	KW_ON			{ $$ = true; }
		|	KW_OFF			{ $$ = false; }
		;

select		:	KW_SELECT		{ $$ = true; }
		|	KW_DESELECT		{ $$ = false; }
		;

exclude		:	KW_EXCLUDE	       	{ $$ = true; }
		|	KW_INCLUDE	       	{ $$ = false; }
		;

conceal		:	KW_CONCEAL		{ $$ = true; }
		|	KW_REVEAL		{ $$ = false; }
		;

match		:	KW_XMATCH		{ $$ = true; }
		|	KW_MATCH		{ $$ = false; }
		;

unify		:	KW_XUNIFY		{ $$ = true; }
		|	KW_UNIFY		{ $$ = false; }
		;

optDebug       	:	KW_DEBUG 	       	{ $$ = true; }
		|	       			{ $$ = false; }
		;

optNumber	:	SIMPLE_NUMBER	        { $$ = $1; }
		|				{ $$ = NONE; }
		;

importMode	:	KW_PROTECT		{ $$ = ImportModule::PROTECTING; }
		|	KW_EXTEND		{ $$ = ImportModule::EXTENDING; }
		|	KW_INCLUDE		{ $$ = ImportModule::INCLUDING; }
		;
/*
 *	Optional module expression followed by term followed by dot.
 *	{"in" <module expression> ":"} <term> "."
 *	<module expression> is a (possibly empty) bubble not containing ':' or '.'
 *	<term> is a (non-empty) bubble not containing '.' except as first token
 */
moduleAndTerm	:	KW_IN			{ store($1); }
			cTokensBarDotColon inEnd
		|	cTokenBarIn		{ store($1); }
			cTokensBarDot '.'
		;

inEnd		:	':'			{ moduleExpr = bubble; clear(); }
			cToken			{ store($3); }
			cTokensBarDot '.'	{}
		|	'.'			{}
		;

/*
 *	Optional [number] followed by optional module expression, followed
 *	by term, followed by dot.
 *	{"[" <number> "]"} {"in" <module expression> ":"} <term> "."
 */

numberModuleTerm
		:	'['			{ store($1); }
			numberModuleTerm1
		|	KW_IN			{ store($1); }
			cTokensBarDotColon inEnd
		|	cTokenBarLeftIn		{ store($1); }
			cTokensBarDot '.'
		;

numberModuleTerm1
		:	NUMERIC_ID		{ store($1); }
			numberModuleTerm2
		|	cTokenBarDotNumber	{ store($1); }
			cTokensBarDot '.'
		|	'.'			{}
		;

numberModuleTerm2
		:	']'
			{
			  number = Token::codeToInt64(bubble[1].code());
			  clear();
			}
			moduleAndTerm
		|	cTokenBarDotRight	{ store($1); }
			cTokensBarDot '.'
		|	'.'			{}
		;

/*
 *	Optional [number] or [number, number] followed by optional module
 *	expression, followed by term, followed by dot.
 *	{"[" <number> "]"} {"in" <module expression> ":"} <term> "."
 */

/*
 *	Seen <command>; looking for "[", "in", or start of term.
 */
numbersModuleTerm
		:	'['			{ store($1); }
			numbersModuleTerm1
		|	KW_IN			{ store($1); }
			cTokensBarDotColon inEnd
		|	cTokenBarLeftIn		{ store($1); }
			cTokensBarDot '.'
		;

/*
 *	Seen <command> "["; looking for <number>, ",", continuation of
 *	term or "." to end command.
 */
numbersModuleTerm1
		:	NUMERIC_ID		{ store($1); }
			numbersModuleTerm2
		|	','			{ store($1); }
			numbersModuleTerm5
		|	cTokenBarDotCommaNumber	{ store($1); }
			cTokensBarDot '.'
		|	'.'			{}
		;

/*
 *	Seen <command> "[" <number>; looking for "]", ",",
 *	continuation of term or "." to end command.
 */
numbersModuleTerm2
		:	']'
			{
			  number = Token::codeToInt64(bubble[1].code());
			  clear();
			}
			moduleAndTerm
		|	','			{ store($1); }
			numbersModuleTerm3
		|	cTokenBarDotCommaRight	{ store($1); }
			cTokensBarDot '.'
		|	'.'			{}
		;

/*
 *	Seen <command> "[" <number> ","; looking for <number>,
 *	continuation of term or "." to end command.
 */
numbersModuleTerm3
		:	NUMERIC_ID		{ store($1); }
			numbersModuleTerm4
		|	cTokenBarDotNumber	{ store($1); }
			cTokensBarDot '.'
		|	'.'			{}
		;

/*
 *	Seen <command> "[" <number> "," <number>; looking for "]",
 *	continuation of term or "." to end command.
 */
numbersModuleTerm4
		:	']'
			{
			  number = Token::codeToInt64(bubble[1].code());
			  number2 = Token::codeToInt64(bubble[3].code());
			  clear();
			}
			moduleAndTerm
		|	cTokenBarDotRight	{ store($1); }
			cTokensBarDot '.'
		|	'.'			{}
		;

/*
 *	Seen <command> "[" ","; looking for <number>, continuation of
 *	term or "." to end command. 
 */
numbersModuleTerm5
		:	NUMERIC_ID	{ store($1); }
			numbersModuleTerm6
		|	cTokenBarDotNumber	{ store($1); }
			cTokensBarDot '.'
		|	'.'			{}
		;

/*
 *	Seen <command> "[" "," <number>; looking for "]", continuation
 *	of term or "." to end command. 
 */
numbersModuleTerm6
		:	']'
			{
			  number2 = Token::codeToInt64(bubble[2].code());
			  clear();
			}
			moduleAndTerm
		|	cTokenBarDotRight	{ store($1); }
			cTokensBarDot '.'
		|	'.'			{}
		;

/*
 *	Command mode token trees.
 */
cTokens		:	cTokens cToken		{ store($2); }
		|
		;

cTokensBarDot	:	cTokensBarDot cTokenBarDot	{ store($2); }
		|
		;

cTokensBarDotColon
		:	cTokensBarDotColon cTokenBarDotColon	{ store($2); }
		|
		;

/*
 *	Command mode token types.
 */
cToken		:	IDENTIFIER | NUMERIC_ID | '[' | ']' | KW_IN | ':' | '.' | ','
		|	'('			{ store($1); }
			cTokens ')'		{ $$ = $4; }
		;

cTokenBarDot	:	IDENTIFIER | NUMERIC_ID | '[' | ']' | KW_IN | ':' | ','
		|	'('			{ store($1); }
			cTokens ')'		{ $$ = $4; }
		;

cTokenBarDotColon
		:	IDENTIFIER | NUMERIC_ID | '[' | ']' | KW_IN | ','
		|	'('			{ store($1); }
			cTokens ')'		{ $$ = $4; }
		;

cTokenBarIn	:	IDENTIFIER | NUMERIC_ID | '[' | ']' | ':' | '.' | ','
		|	'('			{ store($1); }
			cTokens ')'		{ $$ = $4; }
		;

cTokenBarLeftIn	:	IDENTIFIER | NUMERIC_ID | ']' | ':' | '.' | ','
		|	'('			{ store($1); }
			cTokens ')'		{ $$ = $4; }
		;

cTokenBarDotNumber
		:	IDENTIFIER | '[' | ']' | KW_IN | ':' | ','
		|	'('			{ store($1); }
			cTokens ')'		{ $$ = $4; }
		;

cTokenBarDotRight
		:	IDENTIFIER | NUMERIC_ID | '[' | KW_IN | ':' | ','
		|	'('			{ store($1); }	
			cTokens ')'		{ $$ = $4; }
		;

cTokenBarDotCommaRight
		:	IDENTIFIER | NUMERIC_ID | '[' | KW_IN | ':'
		|	'('			{ store($1); }	
			cTokens ')'		{ $$ = $4; }
		;

cTokenBarDotCommaNumber
		:	IDENTIFIER | '[' | ']' | KW_IN | ':'
		|	'('			{ store($1); }
			cTokens ')'		{ $$ = $4; }
		;
/*
 *	Lists of operator names.
 */
cOpNameList	:	cOpNameList cSimpleOpName
		|	cSimpleOpName
		;

cSimpleOpName	:	cSimpleTokenBarDot
			{
			  clear();
			  store($1);
			  interpreter.addSelected(bubble);
			}
		|	'(' 			{ clear(); }
			cTokens ')'
			{
			  interpreter.addSelected(bubble);
			}
		;

cSimpleTokenBarDot
		:	IDENTIFIER | NUMERIC_ID | '[' | ']' | KW_IN | ':' | ','
		;
