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
          python3
          python3Packages.jinja2
          python3Packages.pyyaml
          python3Packages.jsonschema
          python3Packages.markdown
          elan
          rustc 
          cargo
        ];
      };
    };
}
