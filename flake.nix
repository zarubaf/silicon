{
  description = "Silicon development shell";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs =
    { nixpkgs, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "aarch64-darwin"
      ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in
    {
      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          packages = with pkgs; [
            rustc
            cargo
            rustfmt
            clippy
            rust-analyzer
            cargo-nextest
            cargo-deny
            cargo-machete
            sccache
            lean4
            just
            lefthook
            vale
            lychee
            taplo
            nixfmt
            yamlfmt
            nodejs
            git
            circt
            z3
            llvmPackages.libllvm
            (python3.withPackages (ps: [
              ps.mdformat
              ps.mdformat-gfm
              ps.mdformat-frontmatter
            ]))
          ];
          RUSTC_WRAPPER = "sccache";
          SILICON_Z3_LIB = "${pkgs.z3.lib}/lib/libz3.so";
        };
      });

      formatter = forAllSystems (pkgs: pkgs.nixfmt);
    };
}
