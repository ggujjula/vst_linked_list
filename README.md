# vst_linked_list
Follow-along of https://softwarefoundations.cis.upenn.edu/vc-current/Verif_stack.html

Build Instructions:
Install vst and compcert
Run:
```
clightgen -normalize linked_list.c
coq_makefile -f _CoqProject -o Makefile
make -j8
```
