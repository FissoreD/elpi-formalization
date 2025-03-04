paper:
	cd tex && make

clean:
	cd tex && make clean

clean-all: clean
	rm -rf pdf

mv-pdf:
	mkdir -p pdf && \
	find -wholename '**/.aux/*.pdf' -exec cp "{}" pdf \;

all: paper

clean-docker:
	docker rm -v -f $$(docker ps -qa)

AUX_FOLDER = .aux
FNAME = main

ci:
	docker create --name latex dfissore/latex2023:latest && \
	docker cp tex/. latex:/data/ && docker ps -a && \
	docker start -i latex && docker cp latex:/data/${AUX_FOLDER}/${FNAME}.pdf . && \
	mkdir -p pdf && mv ${FNAME}.pdf pdf 