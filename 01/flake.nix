{
  description = "My Idris 2 package";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    idris2-pkgs.url = "github:claymager/idris2-pkgs";

    # Repo got renamed...
    idris2-pkgs.inputs.idris-server.url = "gitlab:avidela/recombine";

    # pipes.url = "github:QuentinDuval/IdrisPipes";
    #pipes.url = "path:/home/nixos/repos/IdrisPipes";
    #pipes.flake = false;

    nixpkgs.follows = "idris2-pkgs/nixpkgs";
  };

  outputs = { self, nixpkgs, idris2-pkgs, flake-utils }:
    flake-utils.lib.eachSystem [ "x86_64-darwin" "x86_64-linux" "i686-linux" ] (system:
      let
        pkgs = import nixpkgs { inherit system; overlays = [ idris2-pkgs.overlay ]; };
        inherit (pkgs.idris2-pkgs._builders) idrisPackage devEnv;
        #pipesPackage = idrisPackage pipes { };
        mypkg = idrisPackage ./. {
          extraPkgs = {
            #inherit pipesPackage;
          };
        };
        runTests = idrisPackage ./test {
          extraPkgs = {
            inherit mypkg;
            #inherit pipesPackage;
          };
        };
      in
      {
        defaultPackage = mypkg;

        packages = { inherit mypkg runTests; };

        devShell = pkgs.mkShell {
          buildInputs = [ (devEnv mypkg) ];
        };
      }
    );
}
