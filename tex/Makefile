OUTPUTDIR = .aux
FNAME = main

main:
	latexmk -pdf ${FNAME} --shell-escape -f -outdir=${OUTPUTDIR}

clean:
	rm -rf $(OUTPUTDIR)

.PHONY: main