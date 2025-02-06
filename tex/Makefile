OUTPUTDIR = .aux
LATEX = pdflatex --shell-escape -output-directory=$(OUTPUTDIR) -synctex=1 -file-line-error -recorder
FNAME = main

LATEX_BUILD_FULL = ${LATEX} ${FNAME}.tex -interaction=nonstopmode

main: clean
	mkdir -p $(OUTPUTDIR) && \
	echo "---------------- 0 --------------------" && \
	${LATEX_BUILD_FULL} && \
	echo "---------------- 1 --------------------" && \
	${MAKE} bib && \
	echo "---------------- 3 --------------------" && \
	${LATEX_BUILD_FULL} && \
	echo "---------------- 4 --------------------" && \
	${LATEX_BUILD_FULL}

bib:
	cp bib.bib ${OUTPUTDIR} && cp tlplike.bst ${OUTPUTDIR} && \
	cd ${OUTPUTDIR} && bibtex ${FNAME}

clean:
	rm -rf $(OUTPUTDIR)

.PHONY: main