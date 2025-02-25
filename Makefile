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

ci:
	docker create --name latex dfissore/latex2023:latest && \
	docker cp tex/ latex:/data/ && docker ps -a && \
	mkdir pdf && \
	docker start -i latex && docker cp latex:/data/tex/.aux/main.pdf pdf