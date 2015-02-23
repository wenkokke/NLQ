/*****************************
 * Pepijn Kokke              *
 * Pepijn.Kokke@gmail.com    *
 * Master's Thesis           *
 * Utrecht University        *
 * May 2015                  *
 *****************************/
#ifndef TOAGDA_H
#define TOAGDA_H

#include "Representation.h"
#include "ToString.h"
#include <map>
#include <vector>

using namespace std;

/* Return the name for this proofbox */
char* toAgdaProofboxame(int proofBoxNum) {
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
void toAgdaDerivation(FILE *fout, Derivation *derivation);

void toAgdaDerivationParens(FILE *fout, Derivation *derivation) {
    if (derivation->numPremisses > 0) {
        fprintf(fout, "(");
    }
    toAgdaDerivation(fout, derivation);
    if (derivation->numPremisses > 0) {
        fprintf(fout, ")");
    }
}

void toAgdaDerivation(FILE *fout, Derivation *derivation) {
    fprintf(fout, "%s", derivation->rule->name);
    for(int i = 0; i < derivation->numPremisses; i++) {
        fprintf(fout, " ");
        toAgdaDerivationParens(fout, derivation->premisses[i]);
    }
}

/* Print Term representation of derivation to fout */
void toAgdaDerivation(FILE *fout, Derivation *derivation, int proofboxNum, int numConnectives) {
    char *boxName = toAgdaProofboxame(proofboxNum);
    fprintf(fout, "%s : LG ", boxName);
    toStringSequent(fout, derivation->conclusion);
    fprintf(fout, "\n");
    fprintf(fout, "%s = ", boxName);
    toAgdaDerivation(fout, derivation);
    fprintf(fout, "\n");
}

/* Print Term header to fout */
void toAgdaHeader(FILE *fout) {
    fprintf(fout, "{- start agda terms -}\n");
}

/* Print Term footer to fout */
void toAgdaFooter(FILE *fout, int numBoxes) {
    fprintf(fout, "{- end agda terms -}\n");
}

/* Show this derivation as Term */
void toAgdaShowDerivation(Derivation *derivation, int numConnectives) {
    /* Write Term to file */
    FILE *fout = fopen("lgterm.agda", "w");
    toAgdaHeader(fout);
    toAgdaDerivation(fout, derivation, 1, numConnectives);
    toAgdaFooter(fout, 1);
    fclose(fout);
}

/* Show this derivation as Term */
void toAgdaShowDerivations(vector<Derivation *> derivations, int numConnectives) {
    /* Write Term to file */
    FILE *fout = fopen("lgterm.agda", "w");
    toAgdaHeader(fout);
    for(unsigned int i = 0; i < derivations.size(); i++)
        toAgdaDerivation(fout, derivations[i], i, numConnectives);
    toAgdaFooter(fout, derivations.size());
    fclose(fout);
}

#endif
