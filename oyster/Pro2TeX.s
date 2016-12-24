# renaming of invisible predicate names.
# Entries should be of the form
# 	s/PROLOGNAME(\([^}]\)/PRINTNAME(\1/g
# as all the entries below the blank line show (hopefully!)
# > Notice that backslashed in TeX-commands in the PRINTNAME have to be doubled
# > Notice also that index entries in the Prolog file for predicates that are
# > to be renamed should be of the form \ulinv{PROLOGNAME(}, and not just
# > \ulinv{PROLOGNAME} as you would expect.
s/\$\>\$\$\>\$/\$\\gg\$/g
s/ ext / \\mbox{\\it ext} /g
s/(at(/(\\mbox{\\it at}(/g
s/ new\[/\\mbox{\\em new}\[/g
s/derived,/\{\\bf derived\},/g


s/cautotactic\([^}]\)/\$\\vartheta_{\\it autotactic}\$\1/g
s/cfringe\([^}]\)/\$\\vartheta_{\\it fringe}\$\1/g
s/convertible(\([^}]\)/\$\\alpha\$(\1/g
s/convertlist(\([^}]\)/\$\\alpha'\$(\1/g
s/cpos(\([^}]\)/\$\\vartheta_{\\it pos}\$(\1/g
s/cproblem\([^}]\)/\$\\vartheta_{\\pi}\$\1/g
s/cscreensize\([^}]\)/\$\\vartheta_{\\it screensize}\$\1/g
s/cshift\([^}]\)/\$\\vartheta_{\\it shift}\$\1/g
s/cstatus\([^}]\)/\$\\vartheta_{\\it status}\$\1/g
s/ctheorem(\([^}]\)/\$\\vartheta_{\\it theorem}\$(\1/g
s/cthm\([^}]\)/\$\\vartheta_{\\it thm}\$\1/g
s/cuniverse\([^}]\)/\$\\vartheta_{\\it universe}\$\1/g
s/decidearith(\([^}]\)/\${\\it decide}_{\\it arith}\$(\1/g
s/decideequal(\([^}]\)/\${\\it decide}_{=}\$(\1/g
s/dynvalue(\([^}]\)/\$\\vartheta\$(\1/g
s/extractarith(\([^}]\)/\$\\chi_{\\it arith}\$(\1/g
s/extractequal(\([^}]\)/\$\\chi_{=}\$(\1/g
s/extractterm(\([^}]\)/\$extract\$(\1/g
s/makesubgoals(\([^}]\)/\${\\it subgoals}\$(\1/g
s/polishl(\([^}]\)/${\\it polish}\'$(\1/g
s/problem(\([^}]\)/\$\\pi\$(\1/g
s/prove(\([^}]\)/\$\\models\$(\1/g
s/provearith(\([^}]\)/\$\\models_{\\it arith}\$(\1/g
s/provelist(\([^}]\)/\$\\models'\$(\1/g
s/proving(\([^}]\)/\$\\models_{0}\$(\1/g
s/reduce1(\([^}]\)/\$\\varrho_1\$(\1/g
s/reduce2(\([^}]\)/\$\\varrho_2\$(\1/g
s/reduce3(\([^}]\)/\$\\varrho_3\$(\1/g
s/reduce4(\([^}]\)/\$\\varrho_4\$(\1/g
s/reduce5(\([^}]\)/\$\\varrho_5\$(\1/g
s/reducearith(\([^}]\)/\$\\varrho\$(\1/g
s/rewrite(\([^}]\)/\$\\varphi\$(\1/g
s/rule(\([^}]\)/\$\\vdash\$(\1/g
s/status0(\([^}]\)/$status_0$(\1/g
s/unstoreall(\([^}]\)/$\\Theta_{-}^{'}$(\1/g
s/unstore(\([^}]\)/$\\Theta_-$(\1/g
s/stored(\([^}]\)/$\\Theta_?$(\1/g
s/store(\([^}]\)/$\\Theta_+$(\1/g
s/su(\([^}]\)/\$\\sigma\$(\1/g
s/substituted(\([^}]\)/\$\\sigma\$(\1/g
s/substitutedlist(\([^}]\)/\$\\sigma'\$(\1/g
s/treeassign(\([^}]\)/\$\\triangle_{:=}\$(\1/g
s/treepositioning(\([^}]\)/\$\\triangle_{=:}\$(\1/g
s/ttt(\([^}]\)/\$\\tau\$(\1/g
s/tttl(\([^}]\)/\$\\tau'\$(\1/g
s/tttl1(\([^}]\)/\$\\tau''\$(\1/g
s/ttvar(\([^}]\)/\$\\tau_{var}\$(\1/g
s/wdecl(\([^}]\)/\$\\omega\$(\1/g
s/wterm(\([^}]\)/\$\\omega\'\$(\1/g
s/wterml(\([^}]\)/\$\\omega\'\'\$(\1/g
