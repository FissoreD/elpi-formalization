OUTPUTDIR = .aux
FNAME = main
export TEXMF_OUTPUT_DIRECTORY=.out

main:
	latexmk -pdf ${FNAME} --shell-escape -f -outdir=${OUTPUTDIR}

clean:
	rm -rf $(OUTPUTDIR)

.PHONY: main