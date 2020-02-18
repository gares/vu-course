{withEmacs ? false,
 nixpkgs ? (fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/c4196cca9acd1c51f62baf10fcbe34373e330bb3.tar.gz";
  sha256 = "0jsisiw8yckq96r5rgdmkrl3a7y9vg9ivpw12h11m8w6rxsfn5m5";
}),
coq-version ? "8.10",
print-env ? false
}:
let
  mc = fetchGit {
    url = "https://github.com/gares/mathcomp";
    ref = "minimc";
    rev = "1773269a81268c503c8af8973f6db8596e813107";
   };
  config.packageOverrides = pkgs:

        let coqPackagesV = (with pkgs;{
              "8.7" = coqPackages_8_7;
              "8.8" = coqPackages_8_8;
              "8.9" = coqPackages_8_9;
              "8.10" = coqPackages_8_10;
            }."${coq-version}");
        in

    with pkgs; {
      coqPackages =
        coqPackagesV.overrideScope' (self: super: {
          coq = super.coq;
          mathcomp = (super.mathcompGenSingle mc).single;
          # mathcomp = self.mathcompPkgs.all;
          # ssreflect = self.mathcompPkgs.ssreflect;
          # mathcomp-ssreflect = self.mathcompPkgs.ssreflect;
          # mathcomp-fingroup = self.mathcompPkgs.fingroup;
          # mathcomp-algebra = self.mathcompPkgs.algebra;
          # mathcomp-field = self.mathcompPkgs.field;
          # mathcomp-solvable = self.mathcompPkgs.solvable;
          # mathcomp-character = self.mathcompPkgs.character;
          # mathcomp-ssreflect_1_9 = self.mathcompPkgs.ssreflect;
          # mathcomp-fingroup_1_9 = self.mathcompPkgs.fingroup;
          # mathcomp-algebra_1_9 = self.mathcompPkgs.algebra;
          # mathcomp-field_1_9 = self.mathcompPkgs.field;
          # mathcomp-solvable_1_9 = self.mathcompPkgs.solvable;
          # mathcomp-character_1_9 = self.mathcompPkgs.character;
        });
      coq = coqPackagesV.coq;
      emacs = emacsWithPackages (epkgs:
        with epkgs.melpaStablePackages; [proof-general]);
    };
in
with import nixpkgs {inherit config;};
stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [ coq ]
                ++ (with coqPackages; [mathcomp])
                ++ (with ocamlPackages; [dune stdlib-shims])
                ++ lib.optional withEmacs emacs;
  shellHook = ''
    nixEnv (){
      echo "Here is your work environement:"
      for x in $buildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
      echo "you can pass option '--argstr coq-version \"x.y\"' to nix-shell to change coq versions"
    }
  '' + lib.optionalString print-env "nixEnv";
}
