/*****************************
 * Jeroen Bransen            *
 * Jeroen.Bransen@phil.uu.nl *
 * Master's Thesis           *
 * Utrecht University        *
 * May 2010                  *
 *****************************/
#ifndef TOSTRING_H
#define TOSTRING_H

#include "Representation.h"
#include <string>
#include <map>

using namespace std;

/* List of mapping from string to binary connectives */
map<string,BINARY_CONNECTIVE> createStringToBinary()
{
    map<string,BINARY_CONNECTIVE> m;
    m["⇒"] = BACKSLASH;
    m["⇐"] = SLASH;
    m["⊗"] = OTIMES;
    m["⇚"] = OSLASH;
    m["⇛"] = OBACKSLASH;
    m["⊕"] = OPLUS;
    return m;
}
map<string,BINARY_CONNECTIVE> stringToBinary = createStringToBinary();

/* List of mapping from binary connectives to string */
map<BINARY_CONNECTIVE,char*> createBinaryToString()
{
    map<BINARY_CONNECTIVE,char*> m;
    m[BACKSLASH]  = "⇒";
    m[SLASH]      = "⇐";
    m[OTIMES]     = "⊗";
    m[OSLASH]     = "⇚";
    m[OBACKSLASH] = "⇛";
    m[OPLUS]      = "⊕";
    return m;
}
map<BINARY_CONNECTIVE,char*> binaryToString = createBinaryToString();

/* List of mapping from string to unary connectives */
map<string,UNARY_CONNECTIVE> createStringToUnary()
{
    map<string,UNARY_CONNECTIVE> m;
    m["⁰"] = ZERO;
    m["¹"] = ONE;
    return m;
}
map<string,UNARY_CONNECTIVE> stringToUnary = createStringToUnary();

/* List of mapping from unary connectives to string */
map<UNARY_CONNECTIVE,char*> createUnaryToString()
{
    map<UNARY_CONNECTIVE,char*> m;
    m[ZERO] = "⁰";
    m[ONE]  = "¹";
    return m;
}
map<UNARY_CONNECTIVE,char*> unaryToString = createUnaryToString();

/* Print string representation of formula to fout */
void toStringFormula(FILE *fout, Formula *formula, bool top) {
    switch(formula->type) {
        /* Literal */
        case PRIMITIVE:
            fprintf(fout, "%s ", formula->name);
            if(SHOW_PRIMITIVE_INDEX && formula->literal_index > -1)
                fprintf(fout, "_%d", formula->literal_index);
            break;
        /* Binary connective */
        case BINARY:
            if(!top)
                fprintf(fout, "( ");
            toStringFormula(fout, formula->left, false);
            fprintf(fout, "%s ", binaryToString[formula->binary_connective]);
            toStringFormula(fout, formula->right, false);
            if(!top)
                fprintf(fout, ") ");
            break;
        /* Unary */
        case UNARY:
            if(!top)
                fprintf(fout, "( ");
            if(formula->prefix)
                fprintf(fout, "%s ", unaryToString[formula->unary_connective]);
            toStringFormula(fout, formula->inner, false);
            if(!formula->prefix)
                fprintf(fout, "%s ", unaryToString[formula->unary_connective]);
            if(!top)
                fprintf(fout, ") ");
            break;
        /* Match */
        case MATCH:
            fprintf(fout, "%c", formula->matchChar);
            break;
    }
}

/* Print string representation of structure to fout */
void toStringStructure(FILE *fout, Structure *structure, bool top) {
    switch(structure->type) {
        /* Primitive */
        case PRIMITIVE:
            // if(top)
            fprintf(fout, "· ");
            toStringFormula(fout, structure->formula, true);
            // if(top)
            fprintf(fout, "· ");
            break;
        /* Binary connective */
        case BINARY:
            if(!top)
                fprintf(fout, "( ");
            toStringStructure(fout, structure->left, false);
            fprintf(fout, "%s ", binaryToString[structure->binary_connective]);
            toStringStructure(fout, structure->right, false);
            if(!top)
                fprintf(fout, ") ");
            break;
        /* Unary */
        case UNARY:
            if(!top)
                fprintf(fout, "( ");
            if(structure->prefix)
                fprintf(fout, "%s ", unaryToString[structure->unary_connective]);
            toStringStructure(fout, structure->inner, false);
            if(!structure->prefix)
                fprintf(fout, "%s ", unaryToString[structure->unary_connective]);
            if(!top)
                fprintf(fout, ") ");
            break;
        /* Match */
        case MATCH:
            fprintf(fout, "%c", structure->matchChar);
            break;
    }
}

/* Print string representation of sequent to fout */
void toStringSequent(FILE *fout, Sequent *sequent) {
    switch(sequent->type) {
        /* Formula left */
        case FORMULA_LEFT:
            fprintf(fout, "[ ");
            toStringFormula(fout, sequent->leftF, true);
            fprintf(fout, "]⊢ ");
            toStringStructure(fout, sequent->rightS, true);
            break;
        /* Formula right */
        case FORMULA_RIGHT:
            toStringStructure(fout, sequent->leftS, true);
            fprintf(fout, "⊢[ ");
            toStringFormula(fout, sequent->rightF, true);
            fprintf(fout, "]");
            break;
        /* Structural */
        case STRUCTURAL:
            toStringStructure(fout, sequent->leftS, true);
            fprintf(fout, "⊢ ");
            toStringStructure(fout, sequent->rightS, true);
            break;
    }
}

#endif
