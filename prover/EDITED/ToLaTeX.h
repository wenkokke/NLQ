/*****************************
 * Jeroen Bransen            *
 * Jeroen.Bransen@phil.uu.nl *
 * Master's Thesis           *
 * Utrecht University        *
 * May 2010                  *
 *****************************/
#ifndef TOLATEX_H
#define TOLATEX_H

#include "Representation.h"
#include <map>
#include <vector>

using namespace std;

/* List of mapping from binary connectives to LaTeX */
map<BINARY_CONNECTIVE,char*> createBinaryToLaTeX() 
{ 
	map<BINARY_CONNECTIVE,char*> m;
	m[BACKSLASH] = "backslash";
	m[SLASH] = "slash";
	m[OTIMES] = "otimes";
	m[OSLASH] = "oslash";
	m[OBACKSLASH] = "obslash";
	m[OPLUS] = "oplus";
	return m; 
}
map<BINARY_CONNECTIVE,char*> binaryToLaTeX = createBinaryToLaTeX();

/* Print unary connectives to LaTeX */
void toLaTeXUnary(FILE *fout, UNARY_CONNECTIVE connective, bool prefix, bool structural) {
	if(connective == ONE || connective == ZERO)
		fprintf(fout, "%c%s%ceg", prefix ? 'l' : 'r', connective == ONE ? "d" : "", structural ? 'N' : 'n');
}

/* Print LaTeX representation of formula to fout */
void toLaTeXFormula(FILE *fout, Formula *formula, bool top) {
	switch(formula->type) {
		/* Literal */
		case PRIMITIVE:
			fprintf(fout, "lit(%s)", formula->name);
			if(SHOW_PRIMITIVE_INDEX && formula->literal_index > -1)
				fprintf(fout, "_{%d}", formula->literal_index);
			break;
		/* Binary connective */
		case BINARY:
			if(!top)
				fprintf(fout, "");
			fprintf(fout, binaryToLaTeX[formula->binary_connective]);
			fprintf(fout, ",");
			toLaTeXFormula(fout, formula->left, false);
			fprintf(fout, ",");
			toLaTeXFormula(fout, formula->right, false);
			if(!top)
				fprintf(fout, "");
			break;
		/* Unary */
		case UNARY:
			if(!top)
				fprintf(fout, "");
			toLaTeXUnary(fout, formula->unary_connective, formula->prefix, false);
			fprintf(fout, ",");
			toLaTeXFormula(fout, formula->inner, false);
			fprintf(fout, "");
			if(!top)
				fprintf(fout, "");
			break;
		/* Match */
		case MATCH:
			fprintf(fout, "%c", formula->matchChar);
			break;
	}
}

/* Print LaTeX representation of structure to fout */
void toLaTeXStructure(FILE *fout, Structure *structure, bool top) {
	switch(structure->type) {
		/* Primitive */
		case PRIMITIVE:
			if(top)
				fprintf(fout, "");
			toLaTeXFormula(fout, structure->formula, false);
			if(top)
				fprintf(fout, "");
			break;
		/* Binary connective */
		case BINARY:
			if(!top)
				fprintf(fout, "");
			fprintf(fout, "str_%s", binaryToLaTeX[structure->binary_connective]);
			fprintf(fout, ",");
			toLaTeXStructure(fout, structure->left, false);
			fprintf(fout, ",");
			toLaTeXStructure(fout, structure->right, false);
			if(!top)
				fprintf(fout, "");
			break;
		/* Unary */
		case UNARY:
			if(!top)
				fprintf(fout, "");
			toLaTeXUnary(fout, structure->unary_connective, structure->prefix, true);
			fprintf(fout, ",");
			toLaTeXStructure(fout, structure->inner, false);
			fprintf(fout, "");
			if(!top)
				fprintf(fout, "");
			break;
		/* Match */
		case MATCH:
			fprintf(fout, "%c", structure->matchChar);
			break;
	}
}

/* Print LaTeX representation of sequent to fout */
void toLaTeXSequent(FILE *fout, Sequent *sequent) {
	switch(sequent->type) {
		/* Formula left */
		case FORMULA_LEFT:
			fprintf(fout, "vdashleft,");
			toLaTeXFormula(fout, sequent->leftF, true);
			fprintf(fout, ",");
			toLaTeXStructure(fout, sequent->rightS, true);
			break;
		/* Formula right */
		case FORMULA_RIGHT:
			fprintf(fout, "vdashright,");
			toLaTeXStructure(fout, sequent->leftS, true);
			fprintf(fout, ",");
			toLaTeXFormula(fout, sequent->rightF, true);
			break;
		/* Structural */
		case STRUCTURAL:
			fprintf(fout, "vdash,");
			toLaTeXStructure(fout, sequent->leftS, true);
			fprintf(fout, ",");
			toLaTeXStructure(fout, sequent->rightS, true);
			break;	
	}
}

/* Return the name for this proofbox */
char* toLaTeXProofboxName(int proofBoxNum) {
	char *s = new char[10];
	int i = 0;
	do {
		s[i] = 'a' + (proofBoxNum % 26);
		proofBoxNum /= 26;
		i++;
	} while(proofBoxNum);
	s[i] = 0;
	return s;
}

/* Print LaTeX representation of derivation to fout */
void toLaTeXDerivation(FILE *fout, Derivation *derivation) {
	fprintf(fout, "infer,name('%s'),", derivation->rule->latexName);
	toLaTeXSequent(fout, derivation->conclusion);
	fprintf(fout, ",from");
	for(int i = 0; i < derivation->numPremisses; i++) {
		if(i > 0) {
			fprintf(fout, ",and");
		}
		fprintf(fout, ",");
		toLaTeXDerivation(fout, derivation->premisses[i]);
		fprintf(fout, "");
	}
	fprintf(fout, "");
}

/* Print LaTeX representation of derivation to fout in a proofbox */
void toLaTeXDerivation(FILE *fout, Derivation *derivation, int proofBoxNum, int numConnectives) {
	char *boxName = toLaTeXProofboxName(proofBoxNum);
	fprintf(fout, "proof(%s,[", boxName);
	toLaTeXDerivation(fout, derivation);
	fprintf(fout, "]).\n");
}

/* Print LaTeX header to fout */
void toLaTeXHeader(FILE *fout) {
	fprintf(fout, "/* Start derivations */\n");
}

/* Print LaTeX footer to fout */
void toLaTeXFooter(FILE *fout, int numBoxes) {
	fprintf(fout, "/* End derivations */\n");
}

/* Show this derivation as LaTeX */
void toLatexShowDerivation(Derivation *derivation, int numConnectives) {
	/* Write LaTeX to file */
	FILE *fout = fopen("lgproof.pl", "w");
	toLaTeXHeader(fout);
	toLaTeXDerivation(fout, derivation, 0, numConnectives);
	toLaTeXFooter(fout, 1);
	fclose(fout);

	/* Call pdflatex to parse and show */
	system("more lgproof.pl");
}

/* Show this derivation as LaTeX */
void toLatexShowDerivations(vector<Derivation *> derivations, int numConnectives) {
	/* Write LaTeX to file */
	FILE *fout = fopen("lgproof.pl", "w");
	toLaTeXHeader(fout);
	for(unsigned int i = 0; i < derivations.size(); i++)
		toLaTeXDerivation(fout, derivations[i], i, numConnectives);
	toLaTeXFooter(fout, derivations.size());
	fclose(fout);

	/* Call pdflatex to parse and show */
	system("more lgproof.pl");
}

#endif
