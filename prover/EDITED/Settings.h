/*****************************
 * Jeroen Bransen            *
 * Jeroen.Bransen@phil.uu.nl *
 * Master's Thesis           *
 * Utrecht University        *
 * May 2010                  *
 *****************************/
#ifndef SETTINGS_H
#define SETTINGS_H

/* Maximum number of unique primitive names in a sequent */
#define MAX_PRIMITIVES			10

/* Maximum string length of a primitive */
#define MAX_PRIMITIVE_LENGTH	10

/* Return only smallest derivation if false or search whole searchspace if true */
#define EXHAUSTIVE_SEARCH		true

/* Show the primitive indices in the output */
#define SHOW_PRIMITIVE_INDEX	false

/* The command to parse and show the latex file 'lgproof.tex' */
#define LATEX_COMMAND "pdflatex lgproof.tex 1> /dev/null && open lgproof.pdf"
//#define LATEX_COMMAND "texify.exe --quiet --clean --tex-option=--shell-escape --src --pdf --run-viewer lgproof.tex"

#endif
