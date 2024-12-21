OUTPUTDIR = .aux
LATEX = pdflatex --shell-escape -output-directory=$(OUTPUTDIR) -synctex=1 -file-line-error -recorder
BIBER = biber --output-directory=$(OUTPUTDIR)
FNAME = func

main: clean
	mkdir -p $(OUTPUTDIR) && \
	# make -C code/ && \
	echo "---------------- 0 --------------------" && \
	${LATEX} ${FNAME}.tex -interaction=nonstopmode && \
	echo "---------------- 1 --------------------" && \
	# read a && \
	${BIBER} ${FNAME} && \
	echo "---------------- 2 --------------------" && \
	# read a && \
	${LATEX} ${FNAME}.tex -f && \
	echo "---------------- 3 --------------------" && \
	# read a && \
	${LATEX} ${FNAME}.tex

clean:
	rm -rf $(OUTPUTDIR)

.PHONY: main