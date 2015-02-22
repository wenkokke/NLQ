/*****************************
 * Jeroen Bransen            *
 * Jeroen.Bransen@phil.uu.nl *
 * Master's Thesis           *
 * Utrecht University        *
 * May 2010                  *
 *****************************/
#ifndef RULES_H
#define RULES_H

#include "Settings.h"
#include "Representation.h"
#include <vector>

using namespace std;

/* For shorter notation of the rules */
#define TWOWAY_RULE(name, latexName, premisse, conclusion) \
	rules.push_back(new Rule(name, latexName, premisse, conclusion));\
	rules.push_back(new Rule(name, latexName, conclusion, premisse));

/* List of mapping from string to binary connectives */
vector<Rule*> createRules() 
{
	vector<Rule*> rules;

	/* Axioms */
	rules.push_back(new Rule("", "", new Sequent(new Formula('p'), new Structure(new Formula('p')))));
	rules.push_back(new Rule("", "", new Sequent(new Structure(new Formula('p')), new Formula('p'))));

	/* Focus left */
	rules.push_back(new Rule("F_l", "\\leftharpoondown",
		new Sequent(new Formula('A'), new Structure('X')),
		new Sequent(new Structure(new Formula('A')), new Structure('X'))));

	/* Focus right */
	rules.push_back(new Rule("F_r", "\\rightharpoondown",
		new Sequent(new Structure('X'), new Formula('A')),
		new Sequent(new Structure('X'), new Structure(new Formula('A')))));

	/* Defocus left */
	rules.push_back(new Rule("Df_l", "\\leftharpoonup",
		new Sequent(new Structure(new Formula('A')), new Structure('X')),
		new Sequent(new Formula('A'), new Structure('X'))));

	/* Defocus right */
	rules.push_back(new Rule("Df_r", "\\rightharpoonup",
		new Sequent(new Structure('X'), new Structure(new Formula('A'))),
		new Sequent(new Structure('X'), new Formula('A'))));

	/* Residuation */
	TWOWAY_RULE("r", "r",
		new Sequent(new Structure(new Structure('X'), OTIMES, new Structure('Y')), new Structure('P')),
		new Sequent(new Structure('X'), new Structure(new Structure('P'), SLASH, new Structure('Y'))));
	TWOWAY_RULE("r", "r",
		new Sequent(new Structure(new Structure('X'), OTIMES, new Structure('Y')), new Structure('P')),
		new Sequent(new Structure('Y'), new Structure(new Structure('X'), BACKSLASH, new Structure('P'))));
	TWOWAY_RULE("dr", "dr",
		new Sequent(new Structure('X'), new Structure(new Structure('P'), OPLUS, new Structure('Q'))),
		new Sequent(new Structure(new Structure('X'), OSLASH, new Structure('Q')), new Structure('P')));
	TWOWAY_RULE("dr", "dr",
		new Sequent(new Structure('X'), new Structure(new Structure('P'), OPLUS, new Structure('Q'))),
		new Sequent(new Structure(new Structure('P'), OBACKSLASH, new Structure('X')), new Structure('Q')));

	/* / R */
	rules.push_back(new Rule("/ R", "\\slash R",
		new Sequent(new Structure('X'), new Formula(new Formula('A'), SLASH, new Formula('B'))),
		new Sequent(new Structure('X'), new Structure(new Structure(new Formula('A')), SLASH, new Structure(new Formula('B'))))));

	/* \ R */
	rules.push_back(new Rule("\\ R", "\\backslash R",
		new Sequent(new Structure('X'), new Formula(new Formula('B'), BACKSLASH, new Formula('A'))),
		new Sequent(new Structure('X'), new Structure(new Structure(new Formula('B')), BACKSLASH, new Structure(new Formula('A'))))));
	
	/* (+) R */
	rules.push_back(new Rule("(+) R", "\\oplus R",
		new Sequent(new Structure('X'), new Formula(new Formula('B'), OPLUS, new Formula('A'))),
		new Sequent(new Structure('X'), new Structure(new Structure(new Formula('B')), OPLUS, new Structure(new Formula('A'))))));

	/* (/) L */
	rules.push_back(new Rule("(/) L", "\\oslash L",
		new Sequent(new Formula(new Formula('A'), OSLASH, new Formula('B')), new Structure('P')),
		new Sequent(new Structure(new Structure(new Formula('A')), OSLASH, new Structure(new Formula('B'))), new Structure('P'))));

	/* (*) L */
	rules.push_back(new Rule("(*) L", "\\otimes L",
		new Sequent(new Formula(new Formula('A'), OTIMES, new Formula('B')), new Structure('P')),
		new Sequent(new Structure(new Structure(new Formula('A')), OTIMES, new Structure(new Formula('B'))), new Structure('P'))));
	
	/* (\) L */
	rules.push_back(new Rule("(\\) L", "\\obslash L",
		new Sequent(new Formula(new Formula('B'), OBACKSLASH, new Formula('A')), new Structure('P')),
		new Sequent(new Structure(new Structure(new Formula('B')), OBACKSLASH, new Structure(new Formula('A'))), new Structure('P'))));

	/* \ L */
	rules.push_back(new Rule("\\ L", "\\backslash L",
		new Sequent(new Formula(new Formula('A'), BACKSLASH, new Formula('B')), new Structure(new Structure('X'), BACKSLASH, new Structure('P'))),
		new Sequent(new Structure('X'), new Formula('A')),
		new Sequent(new Formula('B'), new Structure('P'))));

	/* / L */
	rules.push_back(new Rule("/ L", "\\slash L",
		new Sequent(new Formula(new Formula('B'), SLASH, new Formula('A')), new Structure(new Structure('P'), SLASH, new Structure('X'))),
		new Sequent(new Structure('X'), new Formula('A')),
		new Sequent(new Formula('B'), new Structure('P'))));

	/* (+) L */
	rules.push_back(new Rule("(+) L", "\\oplus L",
		new Sequent(new Formula(new Formula('B'), OPLUS, new Formula('A')), new Structure(new Structure('P'), OPLUS, new Structure('Q'))),
		new Sequent(new Formula('A'), new Structure('Q')),
		new Sequent(new Formula('B'), new Structure('P'))));
	
	/* (/) R */
	rules.push_back(new Rule("(/) R", "\\oslash R",
		new Sequent(new Structure(new Structure('X'), OSLASH, new Structure('P')), new Formula(new Formula('B'), OSLASH, new Formula('A'))),
		new Sequent(new Structure('X'), new Formula('B')),
		new Sequent(new Formula('A'), new Structure('P'))));
	
	/* (\) R */
	rules.push_back(new Rule("(/) R", "\\obslash R",
		new Sequent(new Structure(new Structure('P'), OBACKSLASH, new Structure('X')), new Formula(new Formula('A'), OBACKSLASH, new Formula('B'))),
		new Sequent(new Structure('X'), new Formula('B')),
		new Sequent(new Formula('A'), new Structure('P'))));
	
	/* (*) R */
	rules.push_back(new Rule("(*) R", "\\obslash R",
		new Sequent(new Structure(new Structure('X'), OTIMES, new Structure('Y')), new Formula(new Formula('A'), OTIMES, new Formula('B'))),
		new Sequent(new Structure('X'), new Formula('A')),
		new Sequent(new Structure('Y'), new Formula('B'))));

	/* Grishin interaction principles */
	rules.push_back(new Rule("d (/) /", "d \\oslash \\slash",
		new Sequent(new Structure(new Structure('X'), OSLASH, new Structure('Q')), new Structure(new Structure('P'), SLASH, new Structure('Y'))),
		new Sequent(new Structure(new Structure('X'), OTIMES, new Structure('Y')), new Structure(new Structure('P'), OPLUS, new Structure('Q')))));
	rules.push_back(new Rule("d (/) \\", "d \\oslash \\backslash",
		new Sequent(new Structure(new Structure('Y'), OSLASH, new Structure('Q')), new Structure(new Structure('X'), BACKSLASH, new Structure('P'))),
		new Sequent(new Structure(new Structure('X'), OTIMES, new Structure('Y')), new Structure(new Structure('P'), OPLUS, new Structure('Q')))));
	rules.push_back(new Rule("d (\\) /", "d \\obslash \\slash",
		new Sequent(new Structure(new Structure('P'), OBACKSLASH, new Structure('X')), new Structure(new Structure('Q'), SLASH, new Structure('Y'))),
		new Sequent(new Structure(new Structure('X'), OTIMES, new Structure('Y')), new Structure(new Structure('P'), OPLUS, new Structure('Q')))));
	rules.push_back(new Rule("d (\\) \\", "d \\obslash \\backslash",
		new Sequent(new Structure(new Structure('P'), OBACKSLASH, new Structure('Y')), new Structure(new Structure('X'), BACKSLASH, new Structure('Q'))),
		new Sequent(new Structure(new Structure('X'), OTIMES, new Structure('Y')), new Structure(new Structure('P'), OPLUS, new Structure('Q')))));

	/*** Negations ***/

	/* gc */
	TWOWAY_RULE("gc", "gc",
		new Sequent(new Structure('X'), new Structure(new Structure('Y'), ZERO)),
		new Sequent(new Structure('Y'), new Structure(ZERO, new Structure('X'))));

	/* dgc */
	TWOWAY_RULE("dgc", "dgc",
		new Sequent(new Structure(ONE, new Structure('Q')), new Structure('P')),
		new Sequent(new Structure(new Structure('P'), ONE), new Structure('Q')));

	/* .0L */
	rules.push_back(new Rule(".0L", "\\rneg{.} L",
		new Sequent(new Formula(new Formula('A'), ZERO), new Structure(new Structure('X'), ZERO)),
		new Sequent(new Structure('X'), new Formula('A'))));

	/* .0R */
	rules.push_back(new Rule(".0R", "\\rneg{.} R",
		new Sequent(new Structure('X'), new Formula(new Formula('A'), ZERO)),
		new Sequent(new Structure('X'), new Structure(new Structure(new Formula('A')), ZERO))));

	/* 0.L */
	rules.push_back(new Rule("0.L", "\\lneg{.} L",
		new Sequent(new Formula(ZERO, new Formula('A')), new Structure(ZERO, new Structure('X'))),
		new Sequent(new Structure('X'), new Formula('A'))));

	/* 0.R */
	rules.push_back(new Rule("0.R", "\\lneg{.} R",
		new Sequent(new Structure('X'), new Formula(ZERO, new Formula('A'))),
		new Sequent(new Structure('X'), new Structure(ZERO, new Structure(new Formula('A'))))));
	
	/* .1R*/
	rules.push_back(new Rule(".1R", "\\rdneg{.} R",
		new Sequent(new Structure(new Structure('P'), ONE), new Formula(new Formula('A'), ONE)),
		new Sequent(new Formula('A'), new Structure('P'))));

	/* .1L */
	rules.push_back(new Rule(".1L", "\\rdneg{.} L",
		new Sequent(new Formula(new Formula('A'), ONE), new Structure('P')),
		new Sequent(new Structure(new Structure(new Formula('A')), ONE), new Structure('P'))));
	
	/* 1.R*/
	rules.push_back(new Rule("1.R", "\\ldneg{.} R",
		new Sequent(new Structure(ONE, new Structure('P')), new Formula(ONE, new Formula('A'))),
		new Sequent(new Formula('A'), new Structure('P'))));

	/* 1.L */
	rules.push_back(new Rule("1.L", "\\ldneg{.} L",
		new Sequent(new Formula(ONE, new Formula('A')), new Structure('P')),
		new Sequent(new Structure(ONE, new Structure(new Formula('A'))), new Structure('P'))));

	/* Galois distributivity principles */
	/* Two galois factors */
	rules.push_back(new Rule("", "",
		new Sequent(new Structure(ONE, new Structure('P')), new Structure(new Structure('X'), ZERO)),
		new Sequent(new Structure('X'), new Structure('P'))));
	rules.push_back(new Rule("", "",
		new Sequent(new Structure(ONE, new Structure('P')), new Structure(ZERO, new Structure('X'))),
		new Sequent(new Structure('X'), new Structure('P'))));
	rules.push_back(new Rule("", "",
		new Sequent(new Structure(new Structure('P'), ONE), new Structure(ZERO, new Structure('X'))),
		new Sequent(new Structure('X'), new Structure('P'))));
	rules.push_back(new Rule("", "",
		new Sequent(new Structure(new Structure('P'), ONE), new Structure(new Structure('X'), ZERO)),
		new Sequent(new Structure('X'), new Structure('P'))));

	/* One galois factor */
	rules.push_back(new Rule("", "",
		new Sequent(new Structure(new Structure('P'), ONE), new Structure(new Structure('X'), BACKSLASH, new Structure('Q'))),
		new Sequent(new Structure('X'), new Structure(new Structure('P'), OPLUS, new Structure('Q')))));
	rules.push_back(new Rule("", "",
		new Sequent(new Structure(new Structure('P'), ONE), new Structure(new Structure('Q'), SLASH, new Structure('X'))),
		new Sequent(new Structure('X'), new Structure(new Structure('P'), OPLUS, new Structure('Q')))));
	rules.push_back(new Rule("", "",
		new Sequent(new Structure(ONE, new Structure('Q')), new Structure(new Structure('X'), BACKSLASH, new Structure('P'))),
		new Sequent(new Structure('X'), new Structure(new Structure('P'), OPLUS, new Structure('Q')))));
	rules.push_back(new Rule("", "",
		new Sequent(new Structure(ONE, new Structure('Q')), new Structure(new Structure('P'), SLASH, new Structure('X'))),
		new Sequent(new Structure('X'), new Structure(new Structure('P'), OPLUS, new Structure('Q')))));
	
	rules.push_back(new Rule("", "",
		new Sequent(new Structure(new Structure('P'), OBACKSLASH, new Structure('X')), new Structure(ZERO, new Structure('Y'))),
		new Sequent(new Structure(new Structure('X'), OTIMES, new Structure('Y')), new Structure('P'))));
	rules.push_back(new Rule("", "",
		new Sequent(new Structure(new Structure('X'), OSLASH, new Structure('P')), new Structure(ZERO, new Structure('Y'))),
		new Sequent(new Structure(new Structure('X'), OTIMES, new Structure('Y')), new Structure('P'))));
	rules.push_back(new Rule("", "",
		new Sequent(new Structure(new Structure('P'), OBACKSLASH, new Structure('Y')), new Structure(new Structure('X'), ZERO)),
		new Sequent(new Structure(new Structure('X'), OTIMES, new Structure('Y')), new Structure('P'))));
	rules.push_back(new Rule("", "",
		new Sequent(new Structure(new Structure('Y'), OSLASH, new Structure('P')), new Structure(new Structure('X'), ZERO)),
		new Sequent(new Structure(new Structure('X'), OTIMES, new Structure('Y')), new Structure('P'))));

	return rules;
}
vector<Rule*> allRules = createRules();

#endif
