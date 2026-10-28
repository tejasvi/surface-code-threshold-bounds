Run records of the certificate checks, the assemblies and the theorem files (copies of the logs written by the run
scripts). Every check module runs on one core (LEAN_NUM_THREADS=1) of an x86-64 server.

checks_<C>.log, kchecks_<C>[.part<i>].log: one line per check module, "MODULE STATUS SECONDS MAXRSS_KIB" (kernel
  records of KA8 and D2K6 part 2 are prefixed by the certificate name). A module listed more than once was rerun; the
  last OK line counts. part<i>: the records of the i-th machine of a run that was spread over several machines.
  Native (compiled evaluation): A10, D2, T8, R10, T10. Kernel: KA8, D2K6, A10K2, D2M8K2. The A10K2 records of
  part 1 include two pilot modules D<j> of an earlier layout that are not part of the certificate.
kasmA_*.log, kasmP_*.log: assembly modules of A10K2 and D2M8K2 ("MODULE rc=RC SECONDS s").
remeasure_kernel_assembly.txt: All.lean and theorem files of A10K2 and D2M8K2 elaborated once more (seconds, max RSS);
  the first two theorem-file lines failed because the files were not at that path, and are repeated below them.
remeasure_thm.txt: theorem files elaborated once more with #print axioms ("THM SECONDS MAXRSS_KIB RC native_axioms=N").
remeasure_lib.txt: proof-library sources and the assembly modules of the other certificates elaborated once more
  ("FILE ELAPSED_S USER_S SYS_S MAXRSS_KIB RC"; the elapsed time includes the guard's 5 s polling).
axioms_<THM>.out: the #print axioms output of each theorem file.
build_kdata_*.txt, build_data_T10.txt: lake output of the builds of the kernel data modules and of the T10 data.
run_T10.log: the T10 run (generation, data build, checks).
