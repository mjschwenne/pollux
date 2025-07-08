{
  pkgs,
  fstar,
  karamel,
  everparse,
  stdenv,
  ...
}:
stdenv.mkDerivation {
  pname = "dir-locals.el";
  version = "2025-04-08";

  dontUnpack = true;

  dirlocal =
    pkgs.writeText ".dir-locals.el"
    /*
    lisp
    */
    ''
      ((fstar-mode .
                   ((fstar-subp-prover-args .
                       ("--include"
                         "${fstar}/lib/fstar/ulib.checked"
                         "--include"
                         "${karamel}/krmllib"
                         "--include"
                         "${everparse}/lib/lowparse"
                         "--include"
                         "${everparse}/lib/asn1")
                       )))))
    '';

  installPhase = ''
    mkdir $out
    cp $dirlocal $out/dir-locals.el
  '';
}
