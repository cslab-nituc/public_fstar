fstar.exe  --cache_dir _cache ET_OtherBase.fst --cache_checked_modules
fstar.exe  --cache_dir _cache  ET_Base.fst --cache_checked_modules
fstar.exe  --cache_dir _cache LengthMaxLemma.fst --cache_checked_modules
fstar.exe  --cache_dir _cache  ET_MakeRootBase.fst --cache_checked_modules
fstar.exe  --cache_dir _cache  ET_MakeRootBase2.fst --cache_checked_modules
fstar.exe  --cache_dir _cache  ET_MakeRootByBlock.fst --cache_checked_modules
fstar.exe  --cache_dir _cache  ET_MakeRootByCercle.fst --cache_checked_modules
fstar.exe  --cache_dir _cache  ET_MakeRootEval.fst --cache_checked_modules
fstar.exe  --cache_dir _cache  ET_MakeRootEval3.fst --cache_checked_modules
fstar.exe  --cache_dir _cache ET_Test.fst --cache_checked_modules

fstar.exe  --odir out --cache_dir _cache  ET_OtherBase.fst --codegen OCaml --extract_module ET_OtherBase
fstar.exe  --odir out --cache_dir _cache  ET_Base.fst --codegen OCaml --extract_module ET_Base
fstar.exe  --odir out --cache_dir _cache  LengthMaxLemma.fst --codegen OCaml --extract_module LengthMaxLemma
fstar.exe  --odir out --cache_dir _cache  ET_MakeRootBase.fst --codegen OCaml --extract_module ET_MakeRootBase
fstar.exe  --odir out --cache_dir _cache  ET_MakeRootBase2.fst --codegen OCaml --extract_module ET_MakeRootBase2
fstar.exe  --odir out --cache_dir _cache  ET_MakeRootByBlock.fst --codegen OCaml --extract_module ET_MakeRootByBlock
fstar.exe  --odir out --cache_dir _cache  ET_MakeRootByCercle.fst --codegen OCaml --extract_module ET_MakeRootByCercle
fstar.exe  --odir out --cache_dir _cache  ET_MakeRootEval.fst --codegen OCaml --extract_module ET_MakeRootEval
fstar.exe  --odir out --cache_dir _cache  ET_MakeRootEval3.fst --codegen OCaml --extract_module ET_MakeRootEval3
fstar.exe  --odir out --cache_dir _cache  ET_Test.fst --codegen OCaml --extract_module ET_Test

cd out

ocamlfind opt -package fstarlib -linkpkg  -c ET_OtherBase.ml
ocamlfind opt -package fstarlib -linkpkg ET_OtherBase.cmx  -c ET_Base.ml
ocamlfind opt -package fstarlib -linkpkg ET_OtherBase.cmx,ET_Base.cmx  -c ET_MakeRootBase.ml
ocamlfind opt -package fstarlib -linkpkg ET_OtherBase.cmx,ET_Base.cmx  -c ET_MakeRootBase2.ml
ocamlfind opt -package fstarlib -linkpkg ET_OtherBase.cmx,ET_Base.cmx,ET_MakeRootBase.cmx,ET_MakeRootBase2.cmx  -c ET_MakeRootByBlock.ml
ocamlfind opt -package fstarlib -linkpkg ET_OtherBase.cmx,ET_Base.cmx,ET_MakeRootBase.cmx,ET_MakeRootBase2.cmx  -c ET_MakeRootByCercle.ml
ocamlfind opt -package fstarlib -linkpkg ET_OtherBase.cmx,ET_Base.cmx,ET_MakeRootBase.cmx,ET_MakeRootBase2.cmx,ET_MakeRootByBlock.cmx,ET_MakeRootByCercle.cmx   -c ET_MakeRootEval.ml
ocamlfind opt -package fstarlib -linkpkg ET_OtherBase.cmx,ET_Base.cmx,ET_MakeRootBase.cmx,ET_MakeRootBase2.cmx,ET_MakeRootByBlock.cmx,ET_MakeRootByCercle.cmx   -c ET_MakeRootEval3.ml
ocamlfind opt -package fstarlib -linkpkg ET_OtherBase.cmx,ET_Base.cmx,ET_MakeRootBase.cmx,ET_MakeRootBase2.cmx,ET_MakeRootByBlock.cmx,ET_MakeRootByCercle.cmx,ET_MakeRootEval.cmx ET_MakeRootEval3.cmx  -c ET_Test.ml

ocamlfind opt -package fstarlib -linkpkg ET_OtherBase.cmx ET_Base.cmx ET_MakeRootBase.cmx ET_MakeRootBase2.cmx ET_MakeRootByBlock.cmx ET_MakeRootByCercle.cmx  ET_MakeRootEval.cmx ET_MakeRootEval3.cmx ET_Test.cmx  -o ET_Test.exe

