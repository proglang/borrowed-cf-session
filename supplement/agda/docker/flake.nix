{
  inputs.nixpkgs.url = "https://channels.nixos.org/nixpkgs-unstable/nixexprs.tar.zst";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.flake-utils.inputs.nixpkgs.follows = "nixpkgs";

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        formatter = pkgs.nixfmt;
        packages = rec {
          agda = pkgs.agda.withPackages {
            pkgs = p: [
              (p.standard-library.overrideAttrs {
                version = "2.4";
                src = pkgs.fetchFromGitHub {
                  repo = "agda-stdlib";
                  owner = "agda";
                  rev = "v2.4";
                  hash = "sha256-cnYKW/KRKVsTBupQo1DNnH5Cx7sh6W+NEsZPHRWIBjE=";
                };
              })
            ];
            ghc = null;
          };
          default = pkgs.buildEnv {
            name = "agda-borrowed-cf";
            paths = with pkgs; [
              agda
              nano
            ];
          };
        };
      }
    );
}
