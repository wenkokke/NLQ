/*****************************
 * Jeroen Bransen            *
 * Jeroen.Bransen@phil.uu.nl *
 * Master's Thesis           *
 * Utrecht University        *
 * May 2010                  *
 *****************************/
#ifndef POLARITY_H
#define POLARITY_H

#include "Representation.h"
#include <cstring>

/* Does this connective change the polarity */
bool changePolarityBinary(BINARY_CONNECTIVE connective, bool left) {
    switch(connective) {
        case OPLUS:
        case OTIMES:
            return false;
        case SLASH:
        case OSLASH:
            return !left;
        case BACKSLASH:
        case OBACKSLASH:
            return  left;
    }
    return false;
}

/* Does this connective change the polarity */
bool changePolarityUnary(UNARY_CONNECTIVE connective) {
    switch(connective) {
        case BOX:
        case DIAMOND:
        case ZERO:
        case ONE:
            return true;
    }
    return false;
}

/* Can this connective be structural? */
bool structuralPolarityBinary(BINARY_CONNECTIVE connective, bool input) {
    switch(connective) {
        case OPLUS:
        case SLASH:
        case BACKSLASH:
            return !input;
        case OTIMES:
        case OSLASH:
        case OBACKSLASH:
            return input;
    }
    return false;
}

/* Can this connective be structural? */
bool structuralPolarityUnary(UNARY_CONNECTIVE connective, bool input) {
    switch(connective) {
        case BOX:
        case ZERO:
            return !input;
        case ONE:
        case DIAMOND:
            return  input;
    }
    return false;
}

/* Storage for polarity check */
int numLiterals = 0;
int literalCount[MAX_PRIMITIVES];
char literals[MAX_PRIMITIVES][MAX_PRIMITIVE_LENGTH];

/* Helper for checkPolarity, adds counts for all literals */
void countPolarityFormula(Formula *formula, bool positive) {
    int litNum;
    switch(formula->type) {
        /* Primitive */
        case PRIMITIVE:
            litNum = 0;
            while(litNum < numLiterals && strcmp(formula->name, literals[litNum]) != 0)
                litNum++;
            if(litNum == numLiterals) {
                literalCount[litNum] = 0;
                strcpy(literals[litNum], formula->name);
                numLiterals++;
            }
            literalCount[litNum] += positive ? 1 : -1;
            break;
        /* Binary */
        case BINARY:
            countPolarityFormula(formula->left, positive != changePolarityBinary(formula->binary_connective, true));
            countPolarityFormula(formula->right, positive != changePolarityBinary(formula->binary_connective, false));
            break;
        /* Unary */
        case UNARY:
            countPolarityFormula(formula->inner, positive != changePolarityUnary(formula->unary_connective));
            break;
        /* Match */
        case MATCH:
            break; /* To avoid compile warnings */
    }
}

/* Helper for checkPolarity, adds counts for all literals */
void countPolarityStructure(Structure *structure, bool positive) {
    switch(structure->type) {
        /* Primitive */
        case PRIMITIVE:
            countPolarityFormula(structure->formula, positive);
            break;
        /* Binary */
        case BINARY:
            countPolarityStructure(structure->left , positive != changePolarityBinary(structure->binary_connective, true ));
            countPolarityStructure(structure->right, positive != changePolarityBinary(structure->binary_connective, false));
            break;
        /* Unary */
        case UNARY:
            countPolarityStructure(structure->inner, positive != changePolarityUnary(structure->unary_connective));
            break;
        /* Match */
        case MATCH:
            break; /* To avoid compile warnings */
    }
}

/* Do a polarity check on this sequent */
bool checkPolarity(Sequent *sequent) {
    for(int i = 0; i < numLiterals; i++)
        literalCount[i] = 0;

    switch(sequent->type) {
        /* Formula left */
        case FORMULA_LEFT:
            countPolarityFormula(sequent->leftF, true);
            countPolarityStructure(sequent->rightS, false);
            break;
        /* Formula right */
        case FORMULA_RIGHT:
            countPolarityStructure(sequent->leftS, true);
            countPolarityFormula(sequent->rightF, false);
            break;
        /* Structural */
        case STRUCTURAL:
            countPolarityStructure(sequent->leftS, true);
            countPolarityStructure(sequent->rightS, false);
            break;
    }

    /* Check if all counts are 0 */
    for(int i = 0; i < numLiterals; i++)
        if(literalCount[i] != 0)
            return false;
    return true;
}

#endif
