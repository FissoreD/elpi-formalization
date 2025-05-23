OUTPUTDIR = .aux
FNAME = main
export TEXMF_OUTPUT_DIRECTORY=.out

IS2023 = $(shell latex --version | grep 'TeX Live 2023')

LATEXBUILD = latexmk -pdf ${FNAME} --shell-escape -f -outdir=${OUTPUTDIR} \
	-interaction=nonstopmode -halt-on-error -synctex=1

main:
ifeq ($(IS2023),)
	$(MAKE) latex2025
else
	$(MAKE) latex2023
endif

latex2023:
	$(LATEXBUILD)

latex2025:
	echo '{"security" : {"enable_cwd_config": true}}' > ~/.latexminted_config && \
	$(LATEXBUILD) -pretex="\def\istwentytwentyfive{1}" -usepretex main.tex;

clean:
	rm -rf $(OUTPUTDIR)

.PHONY: main