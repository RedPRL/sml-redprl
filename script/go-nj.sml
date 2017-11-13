val success = CM.make "src/frontend.cm";
val () = if success then () else OS.Process.exit OS.Process.failure;
SMLofNJ.exportFn ("bin/.heapimg", Main.main);
