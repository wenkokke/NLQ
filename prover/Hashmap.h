/*****************************
 * Jeroen Bransen            *
 * Jeroen.Bransen@phil.uu.nl *
 * Master's Thesis           *
 * Utrecht University        *
 * May 2010                  *
 *****************************/
#ifndef HASHMAP_H
#define HASHMAP_H
#include <stdlib.h>
#include "Representation.h"
#include "Match.h"
#include <ext/hash_map>
#include <ext/hash_set>
using namespace __gnu_cxx;

/* Global variable for connective order */
int hashmapConnectiveNum;

/* Structure for storing hashmap keys */
struct HashmapKey {
    Sequent *sequent;
    int *connectiveOrder;

    HashmapKey(Sequent *sequent, int *connectiveOrder) {
        this->sequent = sequent;
        this->connectiveOrder = connectiveOrder;
    }
};

/* Structure for storing hashmap items */
struct HashmapItem {
    int depth;
    bool depthLimit, inCall;
    vector<Derivation *> derivations;

    /* Constructor */
    HashmapItem() {
        this->depth = 0;
        this->depthLimit = true;
        this->inCall = false;
    }
};

/* Structure that defines a compare function for all items */
struct HashmapCompare {
    bool operator()(const Formula* f1, const Formula* f2) const {
        int num;
        return matchFormula(const_cast<Formula *>(f1), const_cast<Formula *>(f2), false, false, true, &num);
    }
    bool operator()(const Structure* s1, const Structure* s2) const {
        int num;
        return matchStructure(const_cast<Structure *>(s1), const_cast<Structure *>(s2), false, false, true, &num);
    }
    bool operator()(const Sequent* s1, const Sequent* s2) const {
        int num;
        return matchSequent(const_cast<Sequent *>(s1), const_cast<Sequent *>(s2), false, true, &num);
    }
    bool operator()(const HashmapKey* k1, const HashmapKey* k2) const {
        int num;
        if(EXHAUSTIVE_SEARCH && memcmp(k1->connectiveOrder, k2->connectiveOrder, sizeof(int) * hashmapConnectiveNum) != 0)
            return false;
        return matchSequent(k1->sequent, k2->sequent, false, true, &num);
    }
};

/* Hash function for binary connective */
size_t hashBinaryConnective(const BINARY_CONNECTIVE connective) {
    switch(connective) {
        case SLASH:
            return 2;
        case BACKSLASH:
            return 3;
        case OTIMES:
            return 5;
        case OSLASH:
            return 7;
        case OBACKSLASH:
            return 11;
        case OPLUS:
            return 13;
    }
    return 1;
}
size_t hashUnaryConnective(const UNARY_CONNECTIVE connective) {
    switch(connective) {
        case ZERO:
            return 2;
        case ONE:
            return 3;
    }
    return 1;
}

/* Hash function for Formula */
size_t hashFormula(const Formula *formula) {
    size_t ret = 0;
    switch(formula->type) {
        /* Primitive */
        case PRIMITIVE:
            for(int i = 0; formula->name[i]; i++)
                ret = ret * 37 + formula->name[i] - ' ';
            return ret;
        /* Binary */
        case BINARY:
            return (hashFormula(formula->left) * hashBinaryConnective(formula->binary_connective)) ^ hashFormula(formula->right);
        /* Unary */
        case UNARY:
            return hashFormula(formula->inner) * hashUnaryConnective(formula->unary_connective) + (formula->prefix ? 1 : 0);
        /* Match */
        case MATCH:
            return 0; /* should never happen, is here to avoid compile warnings */
    }
    return 1;
}

/* Hash function for Structure */
size_t hashStructure(const Structure *structure) {
    switch(structure->type) {
        /* Primitive */
        case PRIMITIVE:
            return hashFormula(structure->formula) + 1;
        /* Binary */
        case BINARY:
            return (hashStructure(structure->left) * hashBinaryConnective(structure->binary_connective)) ^ hashStructure(structure->right);
        /* Unary */
        case UNARY:
            return hashStructure(structure->inner) * hashUnaryConnective(structure->unary_connective) + (structure->prefix ? 1 : 0);
        /* Match */
        case MATCH:
            return 0; /* should never happen, is here to avoid compile warnings */
    }
    return 1;
}

/* Hash function for Sequent */
size_t hashSequent(const Sequent *sequent) {
    switch(sequent->type) {
        /* Formula left */
        case FORMULA_LEFT:
            return hashFormula(sequent->leftF) * 1007 + hashStructure(sequent->rightS);
        /* Formula right */
        case FORMULA_RIGHT:
            return hashStructure(sequent->leftS) * 1007 + hashFormula(sequent->rightF);
        /* Structural */
        case STRUCTURAL:
            return hashStructure(sequent->leftS) * 1007 + hashStructure(sequent->rightS);
    }
    return 1;
}

/* Structure that defines a hash function for formulas, structures and sequents */
struct HashmapHashFunction {
    size_t operator()(const Structure* structure) const {
        return hashStructure(structure);
    }
    size_t operator()(const Formula* formula) const {
        return hashFormula(formula);
    }
    size_t operator()(const Sequent* seq) const {
        return hashSequent(seq);
    }
    size_t operator()(const HashmapKey* key) const {
        int ret = hashSequent(key->sequent);
        if(EXHAUSTIVE_SEARCH) {
            for(int i = 0; i < hashmapConnectiveNum && key->connectiveOrder[i] != -1; i++)
                ret += key->connectiveOrder[i];
        }
        return ret;
    }
};

/* The storage for structures */
hash_set<Structure*, HashmapHashFunction, HashmapCompare> structureCache;

/* Makes sure there is only 1 instance of every structure (to use memory in an efficient way) */
Structure *structureCreate(Structure *structure) {
    hash_set<Structure*, HashmapHashFunction, HashmapCompare>::iterator it = structureCache.find(structure);
    if(it == structureCache.end()) {
        structureCache.insert(structure);
        return structure;
    } else {
        free(structure);
        return *it;
    }
}

/* The storage for formulas */
hash_set<Formula*, HashmapHashFunction, HashmapCompare> formulaCache;

/* Makes sure there is only 1 instance of every formula (to use memory in an efficient way) */
Formula *formulaCreate(Formula *formula) {
    hash_set<Formula*, HashmapHashFunction, HashmapCompare>::iterator it = formulaCache.find(formula);
    if(it == formulaCache.end()) {
        formulaCache.insert(formula);
        return formula;
    } else {
        free(formula);
        return *it;
    }
}

/* The storage for sequents */
hash_set<Sequent*, HashmapHashFunction, HashmapCompare> sequentCache;

/* Makes sure there is only 1 instance of every sequent (to use memory in an efficient way) */
Sequent *sequentCreate(Sequent *sequent) {
    hash_set<Sequent*, HashmapHashFunction, HashmapCompare>::iterator it = sequentCache.find(sequent);
    if(it == sequentCache.end()) {
        sequentCache.insert(sequent);
        return sequent;
    } else {
        free(sequent);
        return *it;
    }
}

/* The hashmap where all derivations will be stored */
hash_map<HashmapKey*, HashmapItem*, HashmapHashFunction, HashmapCompare> mainHashmap;

/* Get an existing item from the hashmap or create it if it doesn't exist */
HashmapItem *getHashmapItem(Sequent *sequent, int numConnectives, int *connectiveOrder) {
    hashmapConnectiveNum = numConnectives;
    HashmapKey *key = new HashmapKey(sequent, connectiveOrder);
    if(mainHashmap.find(key) != mainHashmap.end()) {
        HashmapItem *ret = mainHashmap[key];
        free(key);
        return ret;
    }
    if(EXHAUSTIVE_SEARCH) {
        key->connectiveOrder = new int[numConnectives];
        for(int i = 0; i < numConnectives; i++)
            key->connectiveOrder[i] = connectiveOrder[i];
    }
    HashmapItem *ret = new HashmapItem();
    mainHashmap[key] = ret;
    return ret;
}

#endif
