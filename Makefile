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

ci: all mv-pdf