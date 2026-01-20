import sys, re

OPEN_COMMENT = "(*"
END_COMMENT = "*)"

def get_file_cnt(lines):
    res = []
    try:
        indexBegin = lines.index(f"{OPEN_COMMENT}BEGIN{END_COMMENT}\n")
        indexEnd = lines.index(f"{OPEN_COMMENT}END{END_COMMENT}\n")
        res = lines[indexBegin+1:indexEnd]
    finally:
        return res

def print_tex(lines, fout, raw = False):
    with open(fout, "w") as f:
        if not raw:
            f.write("\\begin{elpicode}\n")
        for l in lines:
            l = re.sub(f"^ *% +.*\n","",l)   
            l = re.sub(f"%~(.*)",r"~\g<1>",l)   
            l = re.sub(f"^ *%SNIP.*\n","",l)   
            l = re.sub(f"^ *%ENDSNIP.*\n","",l)   
            l = re.sub(f"^ *%%%.*\n","",l)   
            l = re.sub(f"==l",r"~$\\Ue$~",l) 
            l = re.sub(f"===o",r"~$\\Uo$~",l)
            l = re.sub(f"==o",r"~$\\Eo$~",l)
            l = re.sub(f".*% *HIDE.*\n","",l)
            l = re.sub(f"% label: (.*).* cnt: (.*)",r"~\\customlabel{\g<1>}{(\g<2>)}~",l)
            l = re.sub(f"type \(~\$([^ ]+)\$~\) ([^\.]+)",r"~\\PYG{k+kd}{type} \\PYG{n+nf}{(\g<1>)} \\PYG{k+kt}{\g<2>}~",l)
            l = re.sub(f"type (\([^ ]+\)) ([^\.]+)",r"~\\PYG{k+kd}{type} \\PYG{n+nf}{\g<1>} \\PYG{k+kt}{\g<2>}~",l)
            f.write(l)
        if not raw:
            f.write("\\end{elpicode}\n")

def mk_fname(fname):
    return fname.split("/")[-1][:-4] + "tex"

def get_snippets(lines):
    snips = {}
    ingrp = False
    name = ""
    curgrp = []
    for l in lines:
        m = re.match(rf"^{re.escape(OPEN_COMMENT)}ENDSNIP",l)
        if not (m is None):
            print ("WOW")
            snips[name] = curgrp
            ingrp = False
            curgrp = []
        if ingrp is True:
            curgrp = curgrp + [l]
        m = re.match(rf"^{re.escape(OPEN_COMMENT)}SNIP: *(.*) *{re.escape(END_COMMENT)}$",l)
        if not (m is None):
            ingrp = True
            name = m.group(1)
            if name in snips:
                curgrp = snips[name]
            else:
                curgrp = []
    return snips

def read_file(fname):
    with open(fname) as f:
        lines = f.readlines()
        print_tex(get_file_cnt(lines), mk_fname(fname))
        snippets = get_snippets(lines)
        for fname in snippets:
            lines = snippets[fname]
            print_tex(lines, fname + ".tex")
            print_tex(lines, fname + "_raw.tex", True)

        
if __name__ == "__main__":
    fname = sys.argv[1]
    # print(sys.argv)
    read_file(fname)