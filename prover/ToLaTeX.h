/*****************************
 * Jeroen Bransen            *
 * Jeroen.Bransen@phil.uu.nl *
 * Master's Thesis           *
 * Utrecht University        *
 * May 2010                  *
 *****************************/
#ifndef TOLATEX_H
#define TOLATEX_H

#include "Representation.h"
#include <map>
#include <vector>

using namespace std;

/* List of mapping from binary connectives to LaTeX */
map<BINARY_CONNECTIVE,char*> createBinaryToLaTeX()
{
    map<BINARY_CONNECTIVE,char*> m;
    m[BACKSLASH]  = "\\Rightarrow ";
    m[SLASH]      = "\\Leftarrow ";
    m[OTIMES]     = "\\otimes ";
    m[OSLASH]     = "\\Lleftarrow ";
    m[OBACKSLASH] = "\\Rrightarrow ";
    m[OPLUS]      = "\\oplus ";
    return m;
}
map<BINARY_CONNECTIVE,char*> binaryToLaTeX = createBinaryToLaTeX();

char* unaryToLaTeX(UNARY_CONNECTIVE unary_connective, bool prefix) {
    switch (unary_connective)
    {
    case BOX:
        return "\\Box ";
    case DIAMOND:
        return "\\Diamond ";
    case ZERO:
        if (prefix)
            return "_0";
        else
            return "^0";
    case ONE:
        if (prefix)
            return "_1";
        else
            return "^1";
    }
}

/* Print unary connectives to LaTeX */
void toLaTeXUnary(FILE *fout, UNARY_CONNECTIVE connective, bool prefix, bool structural) {
    if(connective == BOX || connective == DIAMOND)
        fprintf(fout, "\\%c%s%ceg", prefix ? 'l' : 'r', connective == BOX ? "d" : "", structural ? 'N' : 'n');
}

/* Print LaTeX representation of formula to fout */
void toLaTeXFormula(FILE *fout, Formula *formula, bool top) {
    switch(formula->type) {
        /* Literal */
        case PRIMITIVE:
            fprintf(fout, "%s", formula->name);
            if(SHOW_PRIMITIVE_INDEX && formula->literal_index > -1)
                fprintf(fout, "_{%d}", formula->literal_index);
            break;
        /* Binary connective */
        case BINARY:
            if(!top)
                fprintf(fout, "(");
            toLaTeXFormula(fout, formula->left, false);
            fprintf(fout, binaryToLaTeX[formula->binary_connective]);
            toLaTeXFormula(fout, formula->right, false);
            if(!top)
                fprintf(fout, ")");
            break;
        /* Unary */
        case UNARY:
            if(!top)
                fprintf(fout, "(");
            if (formula->prefix)
                fprintf(fout, unaryToLaTeX(formula->unary_connective, formula->prefix));
            toLaTeXFormula(fout, formula->inner, false);
            if (!formula->prefix)
                fprintf(fout, unaryToLaTeX(formula->unary_connective, formula->prefix));
            if(!top)
                fprintf(fout, ")");
            break;
        /* Match */
        case MATCH:
            fprintf(fout, "%c", formula->matchChar);
            break;
    }
}

/* Print LaTeX representation of structure to fout */
void toLaTeXStructure(FILE *fout, Structure *structure, bool top) {
    switch(structure->type) {
        /* Primitive */
        case PRIMITIVE:
            if(top)
                fprintf(fout, "\\mathop{\\cdot} ");
            toLaTeXFormula(fout, structure->formula, false);
            if(top)
                fprintf(fout, "\\mathop{\\cdot} ");
            break;
        /* Binary connective */
        case BINARY:
            if(!top)
                fprintf(fout, "(");
            toLaTeXStructure(fout, structure->left, false);
            fprintf(fout, "\\cdot %s\\cdot ", binaryToLaTeX[structure->binary_connective]);
            toLaTeXStructure(fout, structure->right, false);
            if(!top)
                fprintf(fout, ")");
            break;
        /* Unary */
        case UNARY:
            switch (structure->unary_connective)
            {
            case BOX:
                fprintf(fout, "\\mathop{\\lbrack} ");
                toLaTeXStructure(fout, structure->inner, false);
                fprintf(fout, "\\mathop{\\rbrack} ");
                break;
            case DIAMOND:
                fprintf(fout, "\\mathop{\\langle} ");
                toLaTeXStructure(fout, structure->inner, false);
                fprintf(fout, "\\mathop{\\rangle} ");
                break;
            default:
                if(!top)
                    fprintf(fout, "(");
                if (structure->prefix)
                    fprintf(fout, unaryToLaTeX(structure->unary_connective, structure->prefix));
                toLaTeXStructure(fout, structure->inner, false);
                if (!structure->prefix)
                    fprintf(fout, unaryToLaTeX(structure->unary_connective, structure->prefix));
                if(!top)
                    fprintf(fout, ")");
            }
            break;
        /* Match */
        case MATCH:
            fprintf(fout, "%c", structure->matchChar);
            break;
    }
}

/* Print LaTeX representation of sequent to fout */
void toLaTeXSequent(FILE *fout, Sequent *sequent) {
    switch(sequent->type) {
        /* Formula left */
        case FORMULA_LEFT:
            toLaTeXFormula(fout, sequent->leftF, true);
            fprintf(fout, "\\vdash ");
            toLaTeXStructure(fout, sequent->rightS, true);
            break;
        /* Formula right */
        case FORMULA_RIGHT:
            toLaTeXStructure(fout, sequent->leftS, true);
            fprintf(fout, "\\vdash ");
            toLaTeXFormula(fout, sequent->rightF, true);
            break;
        /* Structural */
        case STRUCTURAL:
            toLaTeXStructure(fout, sequent->leftS, true);
            fprintf(fout, "\\vdash ");
            toLaTeXStructure(fout, sequent->rightS, true);
            break;
    }
}

/* Return the name for this proofbox */
char* toLaTeXProofboxName(int proofBoxNum) {
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

/* Print LaTeX representation of derivation to fout */
void toLaTeXDerivation(FILE *fout, Derivation *derivation) {
    fprintf(fout, "\\infer[%s]{\n", derivation->rule->latexName);
    toLaTeXSequent(fout, derivation->conclusion);
    fprintf(fout, "\n}{\n");
    for(int i = 0; i < derivation->numPremisses; i++) {
        if(i > 0) {
            fprintf(fout, "&\n");
        }
        toLaTeXDerivation(fout, derivation->premisses[i]);
        fprintf(fout, "\n");
    }
    fprintf(fout, "}");
}

/* Print LaTeX representation of derivation to fout in a proofbox */
void toLaTeXDerivation(FILE *fout, Derivation *derivation, int proofBoxNum, int numConnectives) {
    char *boxName = toLaTeXProofboxName(proofBoxNum);
    fprintf(fout, "\\newsavebox{\\proofbox%s}\n", boxName);
    fprintf(fout, "\\sbox{\\proofbox%s}{\n", boxName);
    fprintf(fout, "\\renewcommand{\\arraystretch}{1.5}");
    toLaTeXDerivation(fout, derivation);
    fprintf(fout, "}\n");
    fprintf(fout, "\\ifthenelse{\\wd\\proofbox%s > \\wdtotal}{\\setlength{\\wdtotal}{\\wd\\proofbox%s}}{}\n", boxName, boxName);
    fprintf(fout, "\\ifthenelse{\\ht\\proofbox%s > \\httotal}{\\setlength{\\httotal}{\\ht\\proofbox%s}}{}\n", boxName, boxName);
}

/* Print LaTeX header to fout */
void toLaTeXHeader(FILE *fout) {
    fprintf(fout, "\\documentclass[a4paper]{article}\n");
    fprintf(fout, "\\usepackage[utf8]{inputenc}\n");
    fprintf(fout, "\\DeclareUnicodeCharacter{207A}{^+}\n");
    fprintf(fout, "\\DeclareUnicodeCharacter{207B}{^-}\n");
    fprintf(fout, "\\usepackage{calc}\n");
    fprintf(fout, "\\usepackage{ifthen}\n");
    fprintf(fout, "\\usepackage{proof}\n");
    fprintf(fout, "\\usepackage{stmaryrd}\n");
    fprintf(fout, "\\usepackage{amssymb}\n");
    fprintf(fout, "\\newcommand{\\leftleftharpoons}{\\mathbin{\\ooalign{\\hfil\\raisebox{1pt}{$\\leftharpoonup$}\\hfil\\cr\\hfil\\raisebox{-1pt}{$\\leftharpoondown$}\\hfil\\crcr}}}\n");
    fprintf(fout, "\\newcommand{\\rightrightharpoons}{\\mathbin{\\ooalign{\\hfil\\raisebox{1pt}{$\\rightharpoonup$}\\hfil\\cr\\hfil\\raisebox{-1pt}{$\\rightharpoondown$}\\hfil\\crcr}}}\n");
    fprintf(fout, "\\newcommand{\\lneg}[1]{{}^{\\mathbf{0}}#1}\n");
    fprintf(fout, "\\newcommand{\\rneg}[1]{#1^{\\mathbf{0}}}\n");
    fprintf(fout, "\\newcommand{\\ldneg}[1]{{}^{\\mathbf{1}}#1}\n");
    fprintf(fout, "\\newcommand{\\rdneg}[1]{#1^{\\mathbf{1}}}\n");
    fprintf(fout, "\\newcommand{\\lNeg}[1]{{}^{0 \\cdot}#1}\n");
    fprintf(fout, "\\newcommand{\\rNeg}[1]{#1^{\\cdot 0}}\n");
    fprintf(fout, "\\newcommand{\\ldNeg}[1]{{}^{1 \\cdot}#1}\n");
    fprintf(fout, "\\newcommand{\\rdNeg}[1]{#1^{\\cdot 1}}\n");
    fprintf(fout, "\\RequirePackage[pdftex,pdfview=Fit,pdfstartview=Fit]{hyperref}\n");
    fprintf(fout, "\\pagestyle{empty}\n");
    fprintf(fout, "\\newlength{\\wdtotal}\n");
    fprintf(fout, "\\newlength{\\httotal}\n");
    fprintf(fout, "\\setlength{\\wdtotal}{1cm}\n");
    fprintf(fout, "\\setlength{\\httotal}{1cm}\n");
}

/* Print LaTeX footer to fout */
void toLaTeXFooter(FILE *fout, int numBoxes) {
    fprintf(fout, "\\setlength{\\paperwidth}{2in+\\wdtotal}\n");
    fprintf(fout, "\\setlength{\\paperheight}{2in+\\httotal}\n");
    fprintf(fout, "\\textwidth = \\wdtotal\n");
    fprintf(fout, "\\textheight = \\httotal\n");
    fprintf(fout, "\\oddsidemargin = 0.0 in\n");
    fprintf(fout, "\\evensidemargin = 0.0 in\n");
    fprintf(fout, "\\topmargin = 0.0 in\n");
    fprintf(fout, "\\headheight = 0.0 in\n");
    fprintf(fout, "\\headsep = 0.0 in\n");
    fprintf(fout, "\\parskip = 0.2in\n");
    fprintf(fout, "\\parindent = 0.0in\n");
    fprintf(fout, "\\begin{document}\n");
    for(int i = 0; i < numBoxes; i++) {
        if(i) fprintf(fout, "\\newpage");
        fprintf(fout, "\\usebox{\\proofbox%s}\n", toLaTeXProofboxName(i));
    }
    fprintf(fout, "\\end{document}\n");
}

/* Show this derivation as LaTeX */
void toLatexShowDerivation(Derivation *derivation, int numConnectives) {
    /* Write LaTeX to file */
    FILE *fout = fopen("proof.tex", "w");
    toLaTeXHeader(fout);
    toLaTeXDerivation(fout, derivation, 0, numConnectives);
    toLaTeXFooter(fout, 1);
    fclose(fout);

    /* Call pdflatex to parse and show */
    system(LATEX_COMMAND);
}

/* Show this derivation as LaTeX */
void toLatexShowDerivations(vector<Derivation *> derivations, int numConnectives) {
    /* Write LaTeX to file */
    FILE *fout = fopen("proof.tex", "w");
    toLaTeXHeader(fout);
    for(unsigned int i = 0; i < derivations.size(); i++)
        toLaTeXDerivation(fout, derivations[i], i, numConnectives);
    toLaTeXFooter(fout, derivations.size());
    fclose(fout);

    /* Call pdflatex to parse and show */
    system(LATEX_COMMAND);
}

#endif
