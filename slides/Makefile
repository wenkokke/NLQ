main=main
agda=/usr/local/Cellar/agda/agda-latex/bin/agda


default: _build/$(main).pdf
	open _build/$(main).pdf

_build/$(main).pdf: _build/$(main).tex _build/preamble.tex _build/Joachim_Lambek.jpg
	cd _build/; pdflatex $(main).tex

_build/$(main).tex: _build/ _build/agda.sty $(main).lagda
ifeq ($(BUILD),fast)
	./remove_implicit_args.rb raw $(main).lagda _build/$(main).noimp_lagda
	lhs2tex --agda _build/$(main).noimp_lagda -o _build/$(main).tex
else
	$(agda) -i. -i$(AGDA_HOME) --latex --latex-dir=_build/ $(main).lagda
	mv _build/$(main).tex _build/$(main).imp_tex
	./remove_implicit_args.rb tex _build/$(main).imp_tex _build/$(main).tex
endif

_build/Joachim_Lambek.jpg: Joachim_Lambek.jpg
	cp Joachim_Lambek.jpg _build/

_build/preamble.tex: preamble.tex
	cp preamble.tex _build/

_build/agda.sty: agda.sty
	cp agda.sty _build/

_build/:
	mkdir _build

clean:
	rm -rf _build

.phony: clean
