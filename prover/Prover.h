/*****************************
 * Jeroen Bransen            *
 * Jeroen.Bransen@phil.uu.nl *
 * Master's Thesis           *
 * Utrecht University        *
 * May 2010                  *
 *****************************/
#ifndef PROVER_H
#define PROVER_H

#include "Rules.h"
#include "Hashmap.h"
#include "Match.h"
#include "Polarity.h"
#include <vector>

using namespace std;

/* Number literals in a formula */
void assignLiteralIndexFormula(Formula *formula, int *next) {
	switch(formula->type) {
		/* Primitive */
		case PRIMITIVE:
			formula->literal_index = (*next)++;
			break;
		/* Binary */
		case BINARY:
			assignLiteralIndexFormula(formula->left, next);
			assignLiteralIndexFormula(formula->right, next);
			break;
		/* Unary */
		case UNARY:
			assignLiteralIndexFormula(formula->inner, next);
			break;
		/* Match */
		case MATCH: /* Here to avoid compile warnings */
			break;
	}
}

/* Number literals in a structure */
void assignLiteralIndexStructure(Structure *structure, int *next) {
	switch(structure->type) {
		/* Primitive */
		case PRIMITIVE:
			assignLiteralIndexFormula(structure->formula, next);
			break;
		/* Binary */
		case BINARY:
			assignLiteralIndexStructure(structure->left, next);
			assignLiteralIndexStructure(structure->right, next);
			break;
		/* Unary */
		case UNARY:
			assignLiteralIndexStructure(structure->inner, next);
			break;
		/* Match */
		case MATCH: /* Here to avoid compile warnings */
			break;
	}
}

/* Number all literals in order */
int assignLiteralIndex(Sequent *sequent) {
	int next = 0;
	switch(sequent->type) {
		/* Formula left */
		case FORMULA_LEFT:
			assignLiteralIndexFormula(sequent->leftF, &next);
			assignLiteralIndexStructure(sequent->rightS, &next);
			break;
		/* Formula Right */
		case FORMULA_RIGHT:
			assignLiteralIndexStructure(sequent->leftS, &next);
			assignLiteralIndexFormula(sequent->rightF, &next);
			break;
		/* Structural */
		case STRUCTURAL:
			assignLiteralIndexStructure(sequent->leftS, &next);
			assignLiteralIndexStructure(sequent->rightS, &next);
			break;
	}
	return next;
}

/* Number all logical connectives in order in a formula */
void assignConnectiveIndexFormula(Formula *formula, int *next) {
	switch(formula->type) {
		/* Primitive */
		case PRIMITIVE:
			break;
		/* Binary */
		case BINARY:
			assignConnectiveIndexFormula(formula->left, next);
			formula->binary_index = (*next)++;
			assignConnectiveIndexFormula(formula->right, next);
			break;
		/* Unary */
		case UNARY:
			if(formula->prefix)
				formula->unary_index = (*next)++;
			assignConnectiveIndexFormula(formula->inner, next);
			if(!formula->prefix)
				formula->unary_index = (*next)++;
			break;
		/* Match */
		case MATCH: /* Here to avoid compile warnings */
			break;
	}
}

/* Number all logical connectives in order in a structure */
void assignConnectiveIndexStructure(Structure *structure, int *next) {
	switch(structure->type) {
		/* Primitive */
		case PRIMITIVE:
			assignConnectiveIndexFormula(structure->formula, next);
			break;
		/* Binary */
		case BINARY:
			assignConnectiveIndexStructure(structure->left, next);
			assignConnectiveIndexStructure(structure->right, next);
			break;
		/* Unary */
		case UNARY:
			assignConnectiveIndexStructure(structure->inner, next);
			break;
		/* Match */
		case MATCH: /* Here to avoid compile warnings */
			break;
	}
}

/* Number all logical connectives in order */
int assignConnectiveIndex(Sequent *sequent) {
	int next = 0;
	switch(sequent->type) {
		/* Formula left */
		case FORMULA_LEFT:
			assignConnectiveIndexFormula(sequent->leftF, &next);
			assignConnectiveIndexStructure(sequent->rightS, &next);
			break;
		/* Formula Right */
		case FORMULA_RIGHT:
			assignConnectiveIndexStructure(sequent->leftS, &next);
			assignConnectiveIndexFormula(sequent->rightF, &next);
			break;
		/* Structural */
		case STRUCTURAL:
			assignConnectiveIndexStructure(sequent->leftS, &next);
			assignConnectiveIndexStructure(sequent->rightS, &next);
			break;
	}
	return next;
}

/* Helper function for allPremisseCombinations */
void allPremisseCombinationsHelper(unsigned int i, vector<vector<Derivation *> > &premisseDerivations, vector<Derivation *> &act, vector<vector<Derivation *> > &ret) {
	if(i == premisseDerivations.size()) {
		ret.push_back(act);
	} else {
		for(vector<Derivation *>::iterator it = premisseDerivations[i].begin(); it != premisseDerivations[i].end(); it++) {
			act.push_back(*it);
			allPremisseCombinationsHelper(i + 1, premisseDerivations, act, ret);
			act.pop_back();
		}
	}
}

/* From a vector that contains a list of possible derivations for each sequent, return a list of possible combinations */
vector<vector<Derivation *> > allPremisseCombinations(vector<vector<Derivation *> > &premisseDerivations) {
	vector<vector<Derivation *> > ret;
	vector<Derivation *> act;
	allPremisseCombinationsHelper(0, premisseDerivations, act, ret);
	return ret;
}

/* Predefine so we can call this function */
vector<Derivation *> deriveSequentStep(Sequent *sequent, int depth, int numConnectives, int *connectiveOrder, bool *depthLimit);

/* Try to find a derivation for this sequent of this depth, also returning wheter the search was cut off by the limit */
vector<Derivation *> deriveSequent(Sequent *seq, int depth, int numConnectives, int *connectiveOrder, bool *depthLimit) {
	vector<Derivation *> emptyRet;
	HashmapItem *hashItem = getHashmapItem(seq, numConnectives, connectiveOrder);

	*depthLimit = false;

	/* If we are in the current callstack, return an empty list */
	if(hashItem->inCall)
		return emptyRet;

	/* Check if there are already derivations found */
	if(!EXHAUSTIVE_SEARCH && hashItem->derivations.size() > 0)
		return hashItem->derivations;

	/* Check if we tried with a higher depth before */
	if(depth < hashItem->depth)
		return emptyRet;

	/* If we already searched this searchspace, return this */
	if(!hashItem->depthLimit)
		return hashItem->derivations;

	/* Check if we are too deep */
	if(depth <= 0) {
		*depthLimit = true;
		hashItem->depthLimit = true;
		return emptyRet;
	}

	/* Try to derive this sequent */
	hashItem->inCall = true;
	hashItem->depth = depth;
	hashItem->derivations = deriveSequentStep(seq, depth, numConnectives, connectiveOrder, depthLimit);
	hashItem->depthLimit = *depthLimit;
	hashItem->inCall = false;

	/* Return the derivations */
	return hashItem->derivations;
}

/* Do 1 derivation step */
vector<Derivation *> deriveSequentStep(Sequent *sequent, int depth, int numConnectives, int *connectiveOrder, bool *depthLimit) {
	vector<Derivation *> ret;

	/* Loop through all rules to see if there is a match */
	for(vector<Rule*>::iterator it = allRules.begin(); it != allRules.end(); it++) {
		int connectiveNum = -1;
		if(matchRule(*it, sequent, true, false, &connectiveNum)) {
			/* Construct all premisses for this rule */
			vector<Sequent*> premisses = constructPremisses(*it);

			/* Extra check for axioms */
			if(premisses.size() == 0) {
				Derivation *derivation = new Derivation(*it, sequent, numConnectives);
				ret.push_back(derivation);
				continue;
			}

			/* Do a polarity check */
			bool ok = true;
			for(unsigned int i = 1; i < premisses.size(); i++) {
				if(!checkPolarity(premisses[i])) {
					ok = false;
					break;
				}
			}
			if(!ok) continue;

			/* Set connective order */
			int connectiveIndex = 0;
			if(connectiveNum != -1) {
				while(connectiveOrder[connectiveIndex] != -1)
					connectiveIndex++;
				connectiveOrder[connectiveIndex] = connectiveNum;
			}

			/* Try to derive all premisses */
			vector<vector<Derivation *> > premisseDerivations;
			for(unsigned int i = 0; i < premisses.size(); i++) {
				bool thisDepthLimit = false;
				vector<Derivation *> thisPremisseDerivations = deriveSequent(premisses[i], depth - 1, numConnectives, connectiveOrder, &thisDepthLimit);
				if(thisDepthLimit)
					*depthLimit = true;
				if(thisPremisseDerivations.size() == 0)
					ok = false; /* Don't break, we want to check all premisses for the depth limit */
				else
					premisseDerivations.push_back(thisPremisseDerivations);
			}

			/* Restore connecctive order */
			if(connectiveNum != -1)
				connectiveOrder[connectiveIndex] = -1;
			if(!ok) continue;

			/* If this worked, we found a derivation! */
			vector<vector<Derivation *> > premisseCombinations = allPremisseCombinations(premisseDerivations);
			for(vector<vector<Derivation *> >::iterator it2 = premisseCombinations.begin(); it2 != premisseCombinations.end(); it2++) {
				/* Construct derivation and connective match */
				Derivation *derivation = new Derivation(*it, sequent, numConnectives, *it2);
				int nextCon = 0;
				for(vector<Derivation *>::iterator it3 = (*it2).begin(); it3 != (*it2).end(); it3++) {
					for(int i = 0; (*it3)->connectiveOrder[i] != -1 && i < numConnectives; i++) {
						derivation->connectiveOrder[nextCon++] = (*it3)->connectiveOrder[i];
					}
				}
				if(connectiveNum != -1)
					derivation->connectiveOrder[nextCon] = connectiveNum;

				/* Check if this atom match was not present yet */
				bool matchOk = true;
				for(vector<Derivation *>::iterator it3 = ret.begin(); it3 != ret.end(); it3++) {
					if(memcmp(derivation->connectiveOrder, (*it3)->connectiveOrder, sizeof(int) * numConnectives) == 0) {
						matchOk = false;
						break;
					}
				}
				if(matchOk) {
					ret.push_back(derivation);
					if(!EXHAUSTIVE_SEARCH)
						return ret;
				}
			}
		}
	}

	return ret;
}

/* Try to find a derivation for this sequent using iterative deepening */
vector<Derivation *> deriveSequent(Sequent *sequent, int *numConnectives) {
	vector<Derivation *>  ret;

	/* Check polarity of input */
	if(!checkPolarity(sequent)) {
		printf("Input polarity is not correct.\n");
		return ret;
	}

	/* Assign numbers to literals */
	assignLiteralIndex(sequent);
	*numConnectives = assignConnectiveIndex(sequent);
	int *connectiveOrder = new int[*numConnectives];
	memset(connectiveOrder, -1, sizeof(int) * (*numConnectives));

	/* Iterative deepening */
	bool depthLimit = true;
	for(int depth = 1; depthLimit; depth++) {
		ret = deriveSequent(sequent, depth, *numConnectives, connectiveOrder, &depthLimit);
		printf("Depth %d\n", depth);
		if(ret.size() > 0 && (!EXHAUSTIVE_SEARCH)) {
			return ret;
		}
	}

	return ret;
}

#endif
