{
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in
    {
      devShell.${system} = pkgs.stdenv.mkDerivation rec {
        name = "lean-kernel-arena";
        buildInputs = with pkgs; [
          (python3.withPackages (p : with p; [ jinja2 pyyaml jsonschema markdown ]))
          elan
          rustc 
          cargo
          perf
          libffi
          libffi.dev
          pkg-config
          just
          pypy
          monolith
        ];
      };
    };
}
