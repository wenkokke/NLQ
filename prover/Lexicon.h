/*****************************
 * Jeroen Bransen            *
 * Jeroen.Bransen@phil.uu.nl *
 * Master's Thesis           *
 * Utrecht University        *
 * May 2010                  *
 *****************************/
#ifndef LEXICON_H
#define LEXICON_H

#include "Representation.h"
#include "ToString.h"
#include <stdlib.h>
#include <cstdio>
#include <vector>
#include <map>
#include <string>

using namespace std;

/* Lexicon of all words with their types (lexical ambiguity is not supported) */
map<string,Formula*> lexicon;

/* All possible tokens (order in parsing order) */
char* possibleTokens[] = {":", "⊗", "⇚", "⇛", "⊕", ".", "⇐", "¹", "⁰", "⇒", "(", ")"};
int numPossibleTokens = 12;

/* Utility function, check if str[idx] matches the string token */
bool strMatch(string str, int idx, string token) {
    int i;
    for(i = 0; str[i + idx] && token[i]; i++)
        if(str[i + idx] != token[i])
            return false;
    if(!token[i])
        return true;
    return false;
}

/* Check if this character can be part of a literal name */
bool isLiteralChar(char c) {
    return !isspace(c) && c != '(' && c != ')' && c != '.';
}

/* Tokenize a string */
vector<string> tokenize(string str) {
    vector<string> ret;
    int idx = 0;
    while(str[idx]) {
        /* Skip all whitespace */
        while(str[idx] && isspace(str[idx])) idx++;

        /* If this is comment, ignore the rest of the line */
        if(str[idx] == '%')
            break;

        /* Check if one of the possible tokens matches */
        bool done = false;
        for(int i = 0; i < numPossibleTokens; i++) {
            if(strMatch(str, idx, possibleTokens[i])) {
                ret.push_back(possibleTokens[i]);
                idx += strlen(possibleTokens[i]);
                done = true;
                break;
            }
        }
        if(done) continue;

        /* Otherwise match the longest possible literal string */
        int start = idx;
        while (str[idx] && isLiteralChar(str[idx])) {
            idx++;
        }
        if(idx == start) {
            break;
        }
        ret.push_back(str.substr(start, idx - start));
    }
    return ret;
}

/* Parse a binary connective from this list of tokens */
bool parseBinaryConnective(vector<string>::iterator &it, BINARY_CONNECTIVE *connective) {
    if(stringToBinary.find(*it) != stringToBinary.end()) {
        *connective = stringToBinary[*it];
        it++;
        return true;
    }
    return false;
}

/* Parse a unary connective from this list of tokens */
bool parseUnaryConnective(vector<string>::iterator &it, UNARY_CONNECTIVE *connective) {
    if(stringToUnary.find(*it) != stringToUnary.end()) {
        *connective = stringToUnary[*it];
        it++;
        return true;
    }
    return false;
}

/* Parse a formula from this list of tokens */
Formula *parseFormula(vector<string>::iterator &it, vector<string>::iterator end) {
    Formula *first;
    UNARY_CONNECTIVE unary_connective;

    /* Bracketed formula */
    if((*it) == "(") {
        it++;
        first = parseFormula(it, end);
        if((*it) != ")" || first == NULL)
            return NULL;
        it++;
    } else if(parseUnaryConnective(it, &unary_connective)) { /* Unary */
        Formula *inner = parseFormula(it, end);
        if(inner == NULL)
            return NULL;
        first = new Formula(unary_connective, inner);
    } else {
        /* Literal */
        /* Allocate memory for new literal */
        char *name = (char *)malloc((*it).size()+1);
        (*it).copy(name, (*it).size());
        name[(*it).size()] = 0;

        /* Create formula */
        first = new Formula(name);
        it++;
    }

    /* Check if this is followed by a unary connective */
    if(it != end && parseUnaryConnective(it, &unary_connective))
        first = new Formula(first, unary_connective);

    /* Check if this is followed by a binary connective */
    BINARY_CONNECTIVE binary_connective;
    if(it == end || !parseBinaryConnective(it, &binary_connective))
        return first;

    /* Create return value */
    Formula *ret = new Formula(first, binary_connective, parseFormula(it, end));

    /* Check if righthand side of connective is parsed succesfully */
    if(ret->right == NULL)
        return NULL;

    return ret;
}

/* Parse a formula from this string */
Formula *parseFormula(char *form) {
    vector<string> tokens = tokenize(form);
    vector<string>::iterator it = tokens.begin();
    Formula *ret = parseFormula(it, tokens.end());
    if(ret == NULL || it != tokens.end()) {
        printf("Could not parse formula: %s\n", form);
        return NULL;
    }
    return ret;
}

/* Parse a single line of the lexicon */
bool parseLine(char *line) {
    vector<string> tokens = tokenize(line);

    /* Empty lines (or only comment) */
    if(tokens.size() == 0)
        return true;

    /* Check global markup */
    if(tokens.size() < 3 || tokens[1] != ":") {
        printf("Wrong lexicon format:\n%s", line);
        return false;
    }

    /* Check lexical ambiguity */
    if(lexicon.find(tokens[0]) != lexicon.end()) {
        printf("Multiple occurences in lexicon: %s\n", tokens[0].c_str());
        return false;
    }

    /* Parse the formula */
    vector<string>::iterator it = tokens.begin();
    it += 2; /* skip word and : */
    Formula *formula = parseFormula(it, tokens.end());
    if(formula == NULL || it == tokens.end() || (*it) != ".") {
        printf("Could not parse line:\n%s",line);
        return false;
    }

    /* Add to lexicon */
    lexicon[tokens[0]] = formula;

    return true;
}

/* Read and parse the lexicon file */
bool readLexicon(char *lexiconName) {
    /* Open the file */
    FILE *file = fopen(lexiconName, "r");
    if(!file) {
        printf("Could not open %s for reading!\n", lexiconName);
        return false;
    }

    /* Read and parse every line */
    char line[1024];
    while(fgets(line, sizeof(line), file)) {
        if(!parseLine(line)) {
            return false;
        }
    }

    /* Cleanup and return gracefully */
    fclose(file);
    return true;
}

/* Parse a phrase from the list of tokens */
Structure *parsePhraseTokens(vector<string>::iterator &it, vector<string>::iterator end) {
    Structure *first;

    /* Bracketed phrase */
    if((*it) == "(") {
        it++;
        first = parsePhraseTokens(it, end);
        if((*it) != ")" || first == NULL) {
            return NULL;
        }
        it++;
    } else { /* Primitive */
        if(lexicon.find(*it) == lexicon.end()) {
            printf("Could not find \"%s\" in lexicon.\n", (*it).c_str());
            return NULL;
        }
        first = new Structure(new Formula(lexicon[*it]));
        it++;
    }

    /* Check if we are done already */
    if(it == end || (*it) == ")")
        return first;

    /* More words follow, construct the return */
    Structure *ret = new Structure(first, OTIMES, parsePhraseTokens(it, end));

    /* Check if righthand side of connective is parsed succesfully */
    if(ret->right == NULL)
        return NULL;

    return ret;
}

/* Parse a phrase and assign the types based on the lexicon */
Structure *parsePhrase(char *sentence) {
    vector<string> tokens = tokenize(sentence);
    vector<string>::iterator it = tokens.begin();
    Structure *ret = parsePhraseTokens(it, tokens.end());
    if(ret == NULL || it != tokens.end()) {
        printf("Could not parse sentence: %s\n", sentence);
        return NULL;
    }
    return ret;
}

#endif
