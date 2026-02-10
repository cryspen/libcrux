#
#       Disclaimer: This nix environment is provided as-is.
#       None of this is officially supported and use is at your own risk.
#       We do not maintain or support nix environments.
#
{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    eurydice.url = "github:aeneasverif/eurydice";
    hax.url = "github:hacspec/hax";
    googletest = {
      url = "github:google/googletest/release-1.11.0";
      flake = false;
    };
    benchmark = {
      url = "github:google/benchmark/v1.8.4";
      flake = false;
    };
    json = {
      url = "github:nlohmann/json/v3.10.3";
      flake = false;
    };
    circus-green = {
      url = "github:Inria-Prosecco/circus-green";
      flake = false;
    };
  };

  outputs =
    { self, nixpkgs, flake-utils, eurydice, hax, googletest, benchmark, json, circus-green, ... } @ inputs:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
        charon = eurydice.inputs.charon;
        crane = charon.inputs.crane;
        # Use the overridden package exported by the eurydice flake.
        karamel = eurydice.packages.${system}.karamel;
        fstar = eurydice.inputs.karamel.inputs.fstar;

        tools-environment = {
          CHARON_HOME = charon.packages.${system}.charon;
          EURYDICE_HOME = pkgs.runCommand "eurydice-home" { } ''
            mkdir -p $out
            cp -r ${eurydice.packages.${system}.default}/bin/eurydice $out
            cp -r ${eurydice}/include $out
          '';
          FSTAR_HOME = fstar.packages.${system}.default;
          HAX_HOME = hax;
          KRML_HOME = karamel;

          CHARON_REV = charon.rev or "dirty";
          EURYDICE_REV = eurydice.rev or "dirty";
          KRML_REV = karamel.version;
          FSTAR_REV = fstar.rev or "dirty";
          LIBCRUX_REV = self.rev or "dirty";
        };

        rustToolchain = charon.packages.${system}.rustToolchain;
        craneLib = (crane.mkLib pkgs).overrideToolchain rustToolchain;
        # libcrux doesn't want to commit a Cargo.lock but flakes can only take
        # local inputs if they're committed. The circus-green CI maintains a
        # working Cargo.lock file for this repo, so we use it here.
        defaultCargoLock = "${circus-green}/libcrux-Cargo.lock";

        # Construct a copy of the current directory with the given `Cargo.lock` added.
        build_src = cargoLock:
          let
            src = builtins.filterSource (name: _: !(pkgs.lib.hasSuffix "flake.nix" name)) ./.;
          in
          pkgs.runCommand "libcrux-src" { }
            ''
              cp -r ${src} $out
              chmod u+w $out
              rm -f $out/Cargo.lock
              cp ${cargoLock} $out/Cargo.lock
            '';

        ml-kem = pkgs.callPackage
          ({ lib
           , clang-tools_18
           , cmake
           , mold-wrapped
           , ninja
           , git
           , python3
           , craneLib
           , hax
           , googletest
           , benchmark
           , json
           , tools-environment
           , cargoLock ? defaultCargoLock
           , checkHax ? true
           , runBenchmarks ? true
           }:
            let
              src = build_src cargoLock;
              cargoArtifacts = craneLib.buildDepsOnly { inherit src; };
            in
            craneLib.buildPackage (tools-environment // {
              name = "ml-kem";
              inherit src cargoArtifacts;

              nativeBuildInputs = [
                clang-tools_18
                # Alias `clang_format` to `clang-format-18`
                (pkgs.writeShellScriptBin "clang-format-18" ''exec ${clang-tools_18}/bin/clang-format "$@"'')
                cmake
                mold-wrapped
                ninja
                git
                python3
                fstar.packages.${system}.default
              ] ++ lib.optional checkHax [
                hax
              ];
              buildPhase = ''
                cd libcrux-ml-kem
                patchShebangs ./.
                ${lib.optionalString checkHax ''
                  python hax.py extract
                ''}
                ./c.sh
                cd c
                ${lib.optionalString runBenchmarks "LIBCRUX_BENCHMARKS=1"} \
                  cmake \
                  -DFETCHCONTENT_SOURCE_DIR_GOOGLETEST=${googletest} \
                  -DFETCHCONTENT_SOURCE_DIR_BENCHMARK=${benchmark} \
                  -DFETCHCONTENT_SOURCE_DIR_JSON=${json} \
                  -DCMAKE_EXE_LINKER_FLAGS="-fuse-ld=mold" \
                  -DCMAKE_SHARED_LINKER_FLAGS="-fuse-ld=mold" \
                  -G "Ninja Multi-Config" -B build
                cmake --build build --config Release
                rm -rf build/_deps
              '';
              checkPhase = ''
                build/Release/ml_kem_test
                build/Release/sha3_test
              '' + lib.optionalString runBenchmarks ''
                build/Release/ml_kem_bench
              '';
              installPhase = ''
                cd ./..
                cp -r . $out
              '';
            })
          )
          {
            inherit
              googletest benchmark json
              craneLib tools-environment;
            hax =
              hax.packages.${system}.default;
          };

        ml-dsa = pkgs.callPackage
          ({ lib
           , clang-tools_18
           , cmake
           , mold-wrapped
           , ninja
           , git
           , python3
           , perl
           , craneLib
           , hax
           , googletest
           , benchmark
           , json
           , tools-environment
           , cargoLock ? defaultCargoLock
           , checkHax ? true
           }:
            let
              src = build_src cargoLock;
              cargoArtifacts = craneLib.buildDepsOnly { inherit src; };
            in
            craneLib.buildPackage (tools-environment // {
              name = "ml-dsa";
              inherit src cargoArtifacts;

              nativeBuildInputs = [
                clang-tools_18
                # Alias `clang_format` to `clang-format-18`
                (pkgs.writeShellScriptBin "clang-format-18" ''exec ${clang-tools_18}/bin/clang-format "$@"'')
                cmake
                mold-wrapped
                ninja
                git
                python3
                fstar.packages.${system}.default
                perl
              ] ++ lib.optional checkHax [
                hax
              ];
              buildPhase = ''
                cd crates/algorithms/ml-dsa
                patchShebangs ./.
                ${lib.optionalString checkHax ''
                  ./hax.sh extract
                ''}
                ./boring.sh --no-clean
                cd cg
                cmake \
                  -DFETCHCONTENT_SOURCE_DIR_GOOGLETEST=${googletest} \
                  -DFETCHCONTENT_SOURCE_DIR_BENCHMARK=${benchmark} \
                  -DFETCHCONTENT_SOURCE_DIR_JSON=${json} \
                  -DCMAKE_EXE_LINKER_FLAGS="-fuse-ld=mold" \
                  -DCMAKE_SHARED_LINKER_FLAGS="-fuse-ld=mold" \
                  -G "Ninja Multi-Config" -B build
                cmake --build build --config Release
                rm -rf build/_deps
              '';
              checkPhase = ''
                build/Release/ml_dsa_test
              '';
              installPhase = ''
                cd ./..
                cp -r . $out
              '';
            })
          )
          {
            inherit
              googletest benchmark json
              craneLib tools-environment;
            hax =
              hax.packages.${system}.default;
          };
      in
      rec {
        packages = {
          inherit ml-kem ml-dsa;
        };
        devShells.default = craneLib.devShell (tools-environment // {
          packages = [
            pkgs.clang_18
            pkgs.openssl
            pkgs.pkg-config
            pkgs.jq
            fstar.packages.${system}.default
          ];
          inputsFrom = [ packages.ml-kem ];
          RUST_SRC_PATH = "${rustToolchain.outPath}/lib/rustlib/src/rust/library";
          LIBCLANG_PATH = "${pkgs.llvmPackages_18.libclang.lib}/lib";
        });
      }
    );
}
