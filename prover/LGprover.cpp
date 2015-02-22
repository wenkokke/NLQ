/*****************************
 * Jeroen Bransen            *
 * Jeroen.Bransen@phil.uu.nl *
 * Master's Thesis           *
 * Utrecht University        *
 * May 2010                  *
 *****************************/
#include "Representation.h"
#include "Lexicon.h"
#include "ToString.h"
#include "ToLaTeX.h"
#include "ToProlog.h"
#include "ToAgda.h"
#include "Rules.h"
#include "Prover.h"

void showArguments() {
    printf("LGprover [lexicon file] [phrase] [type]\n");
}

int main(int argc, char **argv) {
    if(argc != 4) {
        showArguments();
        return 1;
    }
    printf("Parsing sequent...\n");
    if(!readLexicon(argv[1]))
        return 2;
    Structure *left = parsePhrase(argv[2]);
    if(!left)
        return 3;
    Formula *right = parseFormula(argv[3]);
    if(!right)
        return 3;

    Sequent *seq = new Sequent(left, right);
    printf("Proving ");
    toStringSequent(stdout, seq); printf("\n");

    int numConnectives;
    vector<Derivation *> der = deriveSequent(seq, &numConnectives);
    if(der.size() > 0) {
        printf("Found %d derivations!\n", der.size());
        toLatexShowDerivations(der, numConnectives);
        toPrologShowDerivations(der, numConnectives);
        toAgdaShowDerivations(der, numConnectives);
    } else {
        printf("No derivations found.\n");
    }

    return 0;
}
