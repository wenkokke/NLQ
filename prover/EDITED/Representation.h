/*****************************
 * Jeroen Bransen            *
 * Jeroen.Bransen@phil.uu.nl *
 * Master's Thesis           *
 * Utrecht University        *
 * May 2010                  *
 *****************************/
#ifndef REPRESENTATION_H
#define REPRESENTATION_H

#include "Settings.h"
#include <vector>

using namespace std;

/* The binary connectives */
enum BINARY_CONNECTIVE {
	OTIMES,		/* (*) */
	OBACKSLASH, /* (\) */
	OSLASH,		/* (/) */
	OPLUS,		/* (+) */
	BACKSLASH,	/*  \  */
	SLASH		/*  /  */
};

/* The unary connectives */
enum UNARY_CONNECTIVE {
	ZERO,		/* 0 */
	ONE			/* 1 */
};

/* The different types of formulas and structures */
enum FORMULA_STRUCTURE_TYPE {
	PRIMITIVE,
	BINARY,
	UNARY,
	MATCH /* For creation of generic style rules */
};

/* The different types of sequents */
enum SEQUENT_TYPE {
	FORMULA_LEFT,
	FORMULA_RIGHT,
	STRUCTURAL
};

/* Representation of a formula */
struct Formula {
	FORMULA_STRUCTURE_TYPE type;

	/* A formula can be one of those 4 */
	union {
		/* Primitive */
		struct {
			int literal_index;
			char *name;
		};
		/* Binary */
		struct {
			BINARY_CONNECTIVE binary_connective;
			int binary_index;
			Formula *left;
			Formula *right;
		};
		/* Unary */
		struct {
			UNARY_CONNECTIVE unary_connective;
			int unary_index;
			bool prefix;
			Formula *inner;
		};
		/* Match */
		struct {
			char matchChar;
		};
	};

	/* Constructors */
	/* Deep copy */
	Formula(Formula *formula) {
		this->type = formula->type;
		switch(formula->type) {
			/* Primitive */
			case PRIMITIVE:
				this->literal_index = formula->literal_index;
				this->name = formula->name;
				break;
			/* Binary */
			case BINARY:
				this->binary_connective = formula->binary_connective;
				this->binary_index = formula->binary_index;
				this->left = new Formula(formula->left);
				this->right = new Formula(formula->right);
				break;
			/* Unary */
			case UNARY:
				this->prefix = formula->prefix;
				this->unary_connective = formula->unary_connective;
				this->unary_index = formula->unary_index;
				this->inner = new Formula(formula->inner);
				break;
			/* Match */
			case MATCH:
				this->matchChar = formula->matchChar;
				break;
		}
	}

	/* Primitive */
	Formula(char *name) {
		this->type = PRIMITIVE;
		this->name = name;
		this->literal_index = -1;
	}
	
	/* Binary */
	Formula(Formula *left, BINARY_CONNECTIVE binary_connective, Formula *right) {
		this->type = BINARY;
		this->left = left;
		this->binary_connective = binary_connective;
		this->binary_index = -1;
		this->right = right;
	}
	
	/* Unary right */
	Formula(Formula *formula, UNARY_CONNECTIVE unary_connective) {
		this->type = UNARY;
		this->inner = formula;
		this->unary_connective = unary_connective;
		this->unary_index = -1;
		this->prefix = false;
	}
	
	/* Unary left */
	Formula(UNARY_CONNECTIVE unary_connective, Formula *formula) {
		this->type = UNARY;
		this->inner = formula;
		this->unary_connective = unary_connective;
		this->prefix = true;
	}
	
	/* Match */
	Formula(char matchChar) {
		this->type = MATCH;
		this->matchChar = matchChar;
	}
};

/* Representation of a structure */
struct Structure {
	FORMULA_STRUCTURE_TYPE type;

	/* A structure can be one of those 4 */
	union {
		/* Primitive */
		struct {
			Formula *formula;
		};
		/* Binary */
		struct {
			BINARY_CONNECTIVE binary_connective;
			Structure *left;
			Structure *right;
		};
		/* Unary */
		struct {
			UNARY_CONNECTIVE unary_connective;
			bool prefix;
			Structure *inner;
		};
		/* Match */
		struct {
			char matchChar;
		};
	};
	
	/* Constructors */
	/* Primitive */
	Structure(Formula *formula) {
		this->type = PRIMITIVE;
		this->formula = formula;
	}

	/* Binary */
	Structure(Structure *left, BINARY_CONNECTIVE binary_connective, Structure *right) {
		this->type = BINARY;
		this->left = left;
		this->binary_connective = binary_connective;
		this->right = right;
	}
	
	/* Unary right */
	Structure(Structure *structure, UNARY_CONNECTIVE unary_connective) {
		this->type = UNARY;
		this->inner = structure;
		this->unary_connective = unary_connective;
		this->prefix = false;
	}
	
	/* Unary left */
	Structure(UNARY_CONNECTIVE unary_connective, Structure *structure) {
		this->type = UNARY;
		this->inner = structure;
		this->unary_connective = unary_connective;
		this->prefix = true;
	}

	/* Match */
	Structure(char matchChar) {
		this->type = MATCH;
		this->matchChar = matchChar;
	}
};

/* Representation of sequent */
struct Sequent {
	SEQUENT_TYPE type;

	/* Left and right there can be a formula or structure */
	union {
		Formula *leftF;
		Structure *leftS;
	};
	union {
		Formula *rightF;
		Structure *rightS;
	};

	/* Constructors */
	Sequent(Formula *left, Structure *right) {
		this->type = FORMULA_LEFT;
		this->leftF = left;
		this->rightS = right;
	}

	Sequent(Structure *left, Formula *right) {
		this->type = FORMULA_RIGHT;
		this->leftS = left;
		this->rightF = right;
	}

	Sequent(Structure *left, Structure *right) {
		this->type = STRUCTURAL;
		this->leftS = left;
		this->rightS = right;
	}
};

/* Representation for a derivation rule */
struct Rule {
	char *name;
	char *latexName;
	Sequent *conclusion;
	int numPremisses;
	Sequent **premisses;

	/* Constructors */
	/* Zero premisse rule */
	Rule(char *name, char *latexName, Sequent *conclusion) {
		this->name = name;
		this->latexName = latexName;
		this->conclusion = conclusion;
		this->numPremisses = 0;
	}

	/* One premisse rule */
	Rule(char *name, char *latexName, Sequent *conclusion, Sequent *premisse) {
		this->name = name;
		this->latexName = latexName;
		this->conclusion = conclusion;
		this->numPremisses = 1;
		this->premisses = new Sequent*[1];
		this->premisses[0] = premisse;
	}

	/* Two premisse rule */
	Rule(char *name, char *latexName, Sequent *conclusion, Sequent *premisse1, Sequent *premisse2) {
		this->name = name;
		this->latexName = latexName;
		this->conclusion = conclusion;
		this->numPremisses = 2;
		this->premisses = new Sequent*[2];
		this->premisses[0] = premisse1;
		this->premisses[1] = premisse2;
	}
};

/* Representation for a whole derivation */
struct Derivation {
	Rule *rule;
	Sequent *conclusion;
	int numPremisses;
	Derivation **premisses;
	int *connectiveOrder;

	/* Constructors */
	/* No premisses */
	Derivation(Rule *rule, Sequent *conclusion, int numConnectives) {
		this->rule = rule;
		this->conclusion = conclusion;
		this->numPremisses = 0;
		this->connectiveOrder = new int[numConnectives];
		memset(this->connectiveOrder, -1, sizeof(int) * numConnectives);
	}

	/* With list of premisses */
	Derivation(Rule *rule, Sequent *conclusion, int numConnectives, vector<Derivation *> premisses) {
		this->rule = rule;
		this->conclusion = conclusion;
		this->connectiveOrder = new int[numConnectives];
		memset(this->connectiveOrder, -1, sizeof(int) * numConnectives);
		this->numPremisses = premisses.size();
		this->premisses = new Derivation*[premisses.size()];
		for(unsigned int i = 0; i < premisses.size(); i++)
			this->premisses[i] = premisses[i];
	}
};

#endif
