Picinae Quick Start Instructions:

Put all .v files into a single, common working directory.  Ensure you're using Coq version 8.16.x.


Windows:
-------
You should be able to just run the "windows_built.bat" script.  (Edit the top line first if you installed Coq in a non-standard location.)


Linux:
-----
Rename "_CoqProject.bak" to "_CoqProject" (no filename extension).  Run the following two commands:

coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile


Mac/Other:
---------
Rename "_CoqProject.bak" to "_CoqProject" (no filename extension).  Load CoqIDE so that its current working directory is the folder containing all the files (e.g., launch one of the .v files in the folder instead of launching CoqIDE on its own).  Use the Compile menu to (1) generate the make file, and then (2) make the project.  This might or might not work, since CoqIDE needs make-tools that might not be installed on your system.  But it's worth a try.


If none of the above works:
--------------------------
Load each of the following into CoqIDE 8.16.x, and use the "Compile->Compile buffer" menu option to compile each file one at a time, IN THE FOLLOWING ORDER:

1. Picinae_core.v
2. Picinae_theory.v
3. Picinae_statics.v
4. Picinae_finterp.v
5. Picinae_simplifier_base.v
6. Picinae_simplifier_v1_1.v
5. Picinae_i386.v (optionally Picinae_armv7.v, Picinae_amd64.v, and/or Picinae_riscv.v)
6. strcmp_i386.v (optionally strlen_arm.v)


Sample proofs:
-------------
After compiling the above modules, load the "strcmp_proofs.v" (for x86 example) or "strlen_arm_proofs.v" (for ARM example) into CoqIDE and step through it to see the system in operation.  Note: Some of the examples take a while to finish while Coq checks the large proofs they generate; this is normal.
