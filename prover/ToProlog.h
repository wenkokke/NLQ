/*****************************
 * Jeroen Bransen            *
 * Jeroen.Bransen@phil.uu.nl *
 * Master's Thesis           *
 * Utrecht University        *
 * May 2010                  *
 *****************************/
#ifndef TOPROLOG_H
#define TOPROLOG_H

#include "Representation.h"
#include <map>
#include <vector>

using namespace std;

/* List of mapping from binary connectives to Term */
map<BINARY_CONNECTIVE,char*> createBinaryToTerm()
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
map<BINARY_CONNECTIVE,char*> binaryToTerm = createBinaryToTerm();

/* Print unary connectives to Term */
void toPrologUnary(FILE *fout, UNARY_CONNECTIVE connective, bool prefix, bool structural) {
    if(connective == ONE || connective == ZERO)
        fprintf(fout, "%c%s%ceg", prefix ? 'l' : 'r', connective == ONE ? "d" : "", structural ? 'N' : 'n');
}

/* Print Term representation of formula to fout */
void toPrologFormula(FILE *fout, Formula *formula, bool top) {
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
            fprintf(fout, binaryToTerm[formula->binary_connective]);
            fprintf(fout, ",");
            toPrologFormula(fout, formula->left, false);
            fprintf(fout, ",");
            toPrologFormula(fout, formula->right, false);
            if(!top)
                fprintf(fout, "");
            break;
        /* Unary */
        case UNARY:
            if(!top)
                fprintf(fout, "");
            toPrologUnary(fout, formula->unary_connective, formula->prefix, false);
            fprintf(fout, ",");
            toPrologFormula(fout, formula->inner, false);
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

/* Print Term representation of structure to fout */
void toPrologStructure(FILE *fout, Structure *structure, bool top) {
    switch(structure->type) {
        /* Primitive */
        case PRIMITIVE:
            if(top)
                fprintf(fout, "");
            toPrologFormula(fout, structure->formula, false);
            if(top)
                fprintf(fout, "");
            break;
        /* Binary connective */
        case BINARY:
            if(!top)
                fprintf(fout, "");
            fprintf(fout, "str_%s", binaryToTerm[structure->binary_connective]);
            fprintf(fout, ",");
            toPrologStructure(fout, structure->left, false);
            fprintf(fout, ",");
            toPrologStructure(fout, structure->right, false);
            if(!top)
                fprintf(fout, "");
            break;
        /* Unary */
        case UNARY:
            if(!top)
                fprintf(fout, "");
            toPrologUnary(fout, structure->unary_connective, structure->prefix, true);
            fprintf(fout, ",");
            toPrologStructure(fout, structure->inner, false);
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

/* Print Term representation of sequent to fout */
void toPrologSequent(FILE *fout, Sequent *sequent) {
    switch(sequent->type) {
        /* Formula left */
        case FORMULA_LEFT:
            fprintf(fout, "vdashleft,");
            toPrologFormula(fout, sequent->leftF, true);
            fprintf(fout, ",");
            toPrologStructure(fout, sequent->rightS, true);
            break;
        /* Formula right */
        case FORMULA_RIGHT:
            fprintf(fout, "vdashright,");
            toPrologStructure(fout, sequent->leftS, true);
            fprintf(fout, ",");
            toPrologFormula(fout, sequent->rightF, true);
            break;
        /* Structural */
        case STRUCTURAL:
            fprintf(fout, "vdash,");
            toPrologStructure(fout, sequent->leftS, true);
            fprintf(fout, ",");
            toPrologStructure(fout, sequent->rightS, true);
            break;
    }
}

/* Return the name for this proofbox */
char* toPrologProofboxName(int proofBoxNum) {
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

/* Print Term representation of derivation to fout */
void toPrologDerivation(FILE *fout, Derivation *derivation) {
    fprintf(fout, "infer,name('%s'),", derivation->rule->name);
    toPrologSequent(fout, derivation->conclusion);
    fprintf(fout, ",from");
    for(int i = 0; i < derivation->numPremisses; i++) {
        if(i > 0) {
            fprintf(fout, ",and");
        }
        fprintf(fout, ",");
        toPrologDerivation(fout, derivation->premisses[i]);
        fprintf(fout, "");
    }
    fprintf(fout, "");
}

/* Print Term representation of derivation to fout in a proofbox */
void toPrologDerivation(FILE *fout, Derivation *derivation, int proofBoxNum, int numConnectives) {
    char *boxName = toPrologProofboxName(proofBoxNum);
    fprintf(fout, "proof(%s,[", boxName);
    toPrologDerivation(fout, derivation);
    fprintf(fout, "]).\n");
}

/* Print Term header to fout */
void toPrologHeader(FILE *fout) {
    fprintf(fout, "/* start prolog derivations */\n");
}

/* Print Term footer to fout */
void toPrologFooter(FILE *fout, int numBoxes) {
    fprintf(fout, "/* end prolog derivation */\n");
}

/* Show this derivation as Term */
void toPrologShowDerivation(Derivation *derivation, int numConnectives) {
    /* Write Term to file */
    FILE *fout = fopen("lgterm.pl", "w");
    toPrologHeader(fout);
    toPrologDerivation(fout, derivation, 0, numConnectives);
    toPrologFooter(fout, 1);
    fclose(fout);

    /* Call pdfTerm to parse and show */
    system("more lgterm.pl");
}

/* Show this derivation as Term */
void toPrologShowDerivations(vector<Derivation *> derivations, int numConnectives) {
    /* Write Term to file */
    FILE *fout = fopen("lgterm.pl", "w");
    toPrologHeader(fout);
    for(unsigned int i = 0; i < derivations.size(); i++)
        toPrologDerivation(fout, derivations[i], i, numConnectives);
    toPrologFooter(fout, derivations.size());
    fclose(fout);

    /* Call pdfTerm to parse and show */
    system("more lgterm.pl");
}

#endif
