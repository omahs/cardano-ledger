{ system, compiler, flags, pkgs, hsPkgs, pkgconfPkgs, ... }:
  {
    flags = {};
    package = {
      specVersion = "2.0";
      identifier = { name = "cardano-mainnet-mirror"; version = "0.1.0.0"; };
      license = "MIT";
      copyright = "";
      maintainer = "operations@iohk.io";
      author = "IOHK";
      homepage = "";
      url = "";
      synopsis = "A convenient wrapper for the mirror of Cardano mainnet";
      description = "This package provides a list of FilePaths to the Cardano mainnet data files";
      buildType = "Simple";
      };
    components = {
      "library" = {
        depends = [ (hsPkgs.base) (hsPkgs.directory) (hsPkgs.filepath) ];
        };
      };
    } // {
    src = (pkgs.lib).mkDefault (pkgs.fetchgit {
      url = "https://github.com/input-output-hk/cardano-mainnet-mirror";
      rev = "4f8db35bb50e5417729fb8bdf455dbe6445a6695";
      sha256 = "1wr98g1n7rslnfk7qkzkn4fdyp81r98b551spl5lnmls9db6bn2z";
      });
    }