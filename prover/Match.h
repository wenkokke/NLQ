/*****************************
 * Jeroen Bransen            *
 * Jeroen.Bransen@phil.uu.nl *
 * Master's Thesis           *
 * Utrecht University        *
 * May 2010                  *
 *****************************/
#ifndef MATCH_H
#define MATCH_H

#include "Representation.h"
#include "Polarity.h"
#include <map>

using namespace std;

/* Used for matching rules, defined globally for efficiency reasons */
map<char, Formula*> formulaMatches;
map<char, Structure*> structureMatches;

/* Try to match 2 formulas */
bool matchFormula(Formula *f1, Formula *f2, bool input, bool store, bool checkNum, int *connectiveNum) {
    /* Compare pointers */
    if(f1 == f2) return true;

    /* First check if this is formula match wildcard */
    if(f1->type == MATCH && (f1->matchChar != 'p' || f2->type == PRIMITIVE)) {
        if(!store)
            return true;

        if(formulaMatches.find(f1->matchChar) != formulaMatches.end()) {
            /* Match already found, check if they are the same */
            return matchFormula(formulaMatches[f1->matchChar], f2, input, store, checkNum, connectiveNum);
        }

        /* Add this to the match table */
        formulaMatches[f1->matchChar] = f2;
        return true;
    }

    /* Check if types are the same */
    if(f1->type != f2->type)
        return false;

    bool ret;
    switch(f1->type) {
        /* Primitive */
        case PRIMITIVE:
            return strcmp(f1->name, f2->name) == 0 && (!checkNum || f1->literal_index == f2->literal_index);
        /* Binary */
        case BINARY:
            ret = f1->binary_connective == f2->binary_connective && matchFormula(f1->left, f2->left, input != changePolarityBinary(f1->binary_connective, true), store, checkNum, connectiveNum) && matchFormula(f1->right, f2->right, input != changePolarityBinary(f1->binary_connective, false), store, checkNum, connectiveNum);
            if(ret && !structuralPolarityBinary(f2->binary_connective, input))
                *connectiveNum = f2->binary_index;
            return ret;
        /* Unary */
        case UNARY:
            ret = f1->unary_connective == f2->unary_connective && f1->prefix == f2->prefix && matchFormula(f1->inner, f2->inner, input != changePolarityUnary(f1->unary_connective), store, checkNum, connectiveNum);
            if(ret && !structuralPolarityUnary(f2->unary_connective, input))
                *connectiveNum = f2->unary_index;
            return ret;
        /* Match */
        case MATCH:
            break; /* Never handled, just to avoid compile warnings */
    }
    return false;
}

/* Try to match 2 structures */
bool matchStructure(Structure *s1, Structure *s2, bool input, bool store, bool checkNum, int *connectiveNum) {
    /* Compare pointers */
    if(s1 == s2) return true;

    /* First check if this is structure match wildcard */
    if(s1->type == MATCH) {
        if(!store)
            return true;

        if(structureMatches.find(s1->matchChar) != structureMatches.end()) {
            /* Match already found, check if they are the same */
            return matchStructure(structureMatches[s1->matchChar], s2, input, store, checkNum, connectiveNum);
        }

        /* Add this to the match table */
        structureMatches[s1->matchChar] = s2;
        return true;
    }

    /* Check if types are the same */
    if(s1->type != s2->type)
        return false;

    switch(s1->type) {
        /* Primitive */
        case PRIMITIVE:
            return matchFormula(s1->formula, s2->formula, input, store, checkNum, connectiveNum);
        /* Binary */
        case BINARY:
            return s1->binary_connective == s2->binary_connective && matchStructure(s1->left, s2->left, input != changePolarityBinary(s1->binary_connective, true), store, checkNum, connectiveNum) && matchStructure(s1->right, s2->right, input != changePolarityBinary(s1->binary_connective, false), store, checkNum, connectiveNum);
        /* Unary */
        case UNARY:
            return s1->unary_connective == s2->unary_connective && s1->prefix == s2->prefix && matchStructure(s1->inner, s2->inner, input != changePolarityUnary(s1->unary_connective), store, checkNum, connectiveNum);
        /* Match */
        case MATCH:
            break; /* Never handled, just to avoid compile warnings */
    }
    return false;
}

/* Try to match 2 sequents */
bool matchSequent(Sequent *s1, Sequent *s2, bool store, bool checkNum, int *connectiveNum) {
    /* Compare pointers */
    if(s1 == s2) return true;

    if(s1->type != s2->type)
        return false;

    switch(s1->type) {
        /* Formula left */
        case FORMULA_LEFT:
            return matchFormula(s1->leftF, s2->leftF, true, store, checkNum, connectiveNum) && matchStructure(s1->rightS, s2->rightS, false, store, checkNum, connectiveNum);
        /* Formula right */
        case FORMULA_RIGHT:
            return matchStructure(s1->leftS, s2->leftS, true, store, checkNum, connectiveNum) && matchFormula(s1->rightF, s2->rightF, false, store, checkNum, connectiveNum);
        /* Structural */
        case STRUCTURAL:
            return matchStructure(s1->leftS, s2->leftS, true, store, checkNum, connectiveNum) && matchStructure(s1->rightS, s2->rightS, false, store, checkNum, connectiveNum);
    }
    return false;
}

/* Try to match this rule to this sequent */
bool matchRule(Rule *rule, Sequent *sequent, bool store, bool checkNum, int *connectiveNum) {
    if(store) {
        formulaMatches.clear();
        structureMatches.clear();
    }
    return matchSequent(rule->conclusion, sequent, store, checkNum, connectiveNum);
}

/* Will be defined in Hashmap.h */
Formula *formulaCreate(Formula *formula);

/* Construct a formula based on this pattern an the matches */
Formula* constructFormula(Formula *formula) {
    switch(formula->type) {
        /* Primitive */
        case PRIMITIVE:
            return formula;
        /* Binary */
        case BINARY:
            return formulaCreate(new Formula(constructFormula(formula->left), formula->binary_connective, constructFormula(formula->right)));
        /* Unary */
        case UNARY:
            return formulaCreate(formula->prefix ? new Formula(formula->unary_connective, constructFormula(formula->inner)) : new Formula(constructFormula(formula->inner), formula->unary_connective));
        /* Match */
        case MATCH:
            return formulaMatches[formula->matchChar];
    }
    return NULL;
}

/* Will be defined in Hashmap.h */
Structure *structureCreate(Structure *structure);

/* Construct a structure based on this pattern an the matches */
Structure* constructStructure(Structure *structure) {
    switch(structure->type) {
        /* Primitive */
        case PRIMITIVE:
            return structureCreate(new Structure(constructFormula(structure->formula)));
        /* Binary */
        case BINARY:
            return structureCreate(new Structure(constructStructure(structure->left), structure->binary_connective, constructStructure(structure->right)));
        /* Unary */
        case UNARY:
            return structureCreate(structure->prefix ? new Structure(structure->unary_connective, constructStructure(structure->inner)) : new Structure(constructStructure(structure->inner), structure->unary_connective));
        /* Match */
        case MATCH:
            return structureMatches[structure->matchChar];
    }
    return NULL;
}

/* Will be defined in Hashmap.h */
Sequent *sequentCreate(Sequent *sequent);

/* Construct a sequent based on this pattern an the matches */
Sequent* constructSequent(Sequent *seq) {
    switch(seq->type) {
        /* Formula left */
        case FORMULA_LEFT:
            return sequentCreate(new Sequent(constructFormula(seq->leftF), constructStructure(seq->rightS)));
        /* Formula right */
        case FORMULA_RIGHT:
            return sequentCreate(new Sequent(constructStructure(seq->leftS), constructFormula(seq->rightF)));
        /* Structural */
        case STRUCTURAL:
            return sequentCreate(new Sequent(constructStructure(seq->leftS), constructStructure(seq->rightS)));
    }
    return NULL;
}

/* Construct the premisses based on this rule and the matches */
vector<Sequent*> constructPremisses(Rule *rule) {
    vector<Sequent*> ret;
    for(int i = 0; i < rule->numPremisses; i++) {
        ret.push_back(constructSequent(rule->premisses[i]));
    }
    return ret;
}

#include "Hashmap.h"

#endif
