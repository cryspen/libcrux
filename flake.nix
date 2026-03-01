#
#       Disclaimer: This nix environment is provided as-is.
#       None of this is officially supported and use is at your own risk.
#       We do not maintain or support nix environments.
#
{
  description = "libcrux - A formally verified cryptographic library";

  inputs = {
    # Follow eurydice's nixpkgs to reduce closure size
    nixpkgs.follows = "eurydice/nixpkgs";
    flake-utils.follows = "eurydice/flake-utils";

    # Core toolchain inputs
    eurydice.url = "github:aeneasverif/eurydice";
    hax.url = "github:hacspec/hax";

    # Non-flake dependencies
    hacl-star = {
      url = "github:hacl-star/hacl-star";
      flake = false;
    };

    # C++ testing and benchmarking dependencies
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
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      eurydice,
      hax,
      hacl-star,
      googletest,
      benchmark,
      json,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs { inherit system; };
        inherit (pkgs) lib;

        # Upstream toolchain dependencies (all derived from eurydice)
        charon = eurydice.inputs.charon;
        karamel = eurydice.packages.${system}.karamel;
        fstar = eurydice.inputs.karamel.inputs.fstar;
        fstarPkg = fstar.packages.${system}.default;
        haxPkg = hax.packages.${system}.default;

        # Rust toolchain setup
        rustToolchain = charon.packages.${system}.rustToolchain;
        craneLib = (charon.inputs.crane.mkLib pkgs).overrideToolchain rustToolchain;

        # Source directory
        src = lib.cleanSourceWith {
          src = ./.;
          filter = path: _: !(lib.hasSuffix "flake.nix" path) && !(lib.hasSuffix "flake.lock" path);
        };

        # Use eurydice's maintained Cargo.lock for libcrux
        cargoVendorDir = craneLib.vendorCargoDeps {
          cargoLock = "${eurydice}/libcrux-Cargo.lock";
        };

        # Cargo artifacts for dependency caching
        cargoArtifacts = craneLib.buildDepsOnly { inherit src cargoVendorDir; };

        # Clang tooling
        clangTools = pkgs.llvmPackages_18.clang-tools;

        # Clang format wrapper
        clangFormat18 = pkgs.writeShellScriptBin "clang-format-18" ''
          exec ${clangTools}/bin/clang-format "$@"
        '';

        # Environment variables for verification tools
        toolsEnv = {
          CHARON_HOME = charon.packages.${system}.charon;
          EURYDICE_HOME = pkgs.runCommand "eurydice-home" { } ''
            mkdir -p $out/bin
            cp ${eurydice.packages.${system}.default}/bin/eurydice $out/bin/
            cp -r ${eurydice}/include $out/
          '';
          FSTAR_HOME = fstarPkg;
          HACL_HOME = hacl-star;
          HAX_HOME = hax;
          KRML_HOME = karamel;

          # Revision tracking
          CHARON_REV = charon.rev or "dirty";
          EURYDICE_REV = eurydice.rev or "dirty";
          KRML_REV = karamel.version;
          FSTAR_REV = fstar.rev or "dirty";
          LIBCRUX_REV = self.rev or "dirty";
        };

        # Common C/C++ build dependencies
        cBuildInputs = with pkgs; [
          clangTools
          clangFormat18
          cmake
          mold-wrapped
          ninja
          git
        ];

        # CMake configuration for C++ test dependencies and linker
        cmakeFlags = lib.concatStringsSep " " [
          "-DFETCHCONTENT_SOURCE_DIR_GOOGLETEST=${googletest}"
          "-DFETCHCONTENT_SOURCE_DIR_BENCHMARK=${benchmark}"
          "-DFETCHCONTENT_SOURCE_DIR_JSON=${json}"
          "-DCMAKE_EXE_LINKER_FLAGS=-fuse-ld=mold"
          "-DCMAKE_SHARED_LINKER_FLAGS=-fuse-ld=mold"
        ];

        # Factory for crypto library packages
        mkCryptoPackage =
          {
            name,
            sourceDir,
            buildDir,
            haxCommand,
            buildCommand,
            testCommands,
            extraNativeBuildInputs ? [ ],
            benchmarkCommands ? [ ],
          }:
          let
            hasBenchmarks = benchmarkCommands != [ ];
          in
          craneLib.buildPackage (
            toolsEnv
            // {
              inherit
                name
                src
                cargoArtifacts
                cargoVendorDir
                ;

              nativeBuildInputs =
                cBuildInputs
                ++ [
                  pkgs.python3
                  fstarPkg
                  haxPkg
                ]
                ++ extraNativeBuildInputs;

              buildPhase = ''
                cd ${sourceDir}
                patchShebangs .
                ${haxCommand}
                ${buildCommand}
                cd ${buildDir}
                ${lib.optionalString hasBenchmarks "LIBCRUX_BENCHMARKS=1"} \
                  cmake ${cmakeFlags} -G "Ninja Multi-Config" -B build
                cmake --build build --config Release
                rm -rf build/_deps
              '';

              checkPhase = lib.concatLines (testCommands ++ benchmarkCommands);

              installPhase = ''
                cd ${sourceDir}/..
                cp -r . $out
              '';
            }
          );

        # ML-KEM package definition
        ml-kem = mkCryptoPackage {
          name = "ml-kem";
          sourceDir = "libcrux-ml-kem";
          buildDir = "c";
          haxCommand = "python hax.py extract";
          buildCommand = "./c.sh";
          testCommands = [
            "build/Release/ml_kem_test"
            "build/Release/sha3_test"
          ];
          benchmarkCommands = [ "build/Release/ml_kem_bench" ];
        };

        # ML-DSA package definition
        ml-dsa = mkCryptoPackage {
          name = "ml-dsa";
          sourceDir = "libcrux-ml-dsa";
          buildDir = "cg";
          haxCommand = "./hax.sh extract";
          buildCommand = "./boring.sh --no-clean";
          testCommands = [ "build/Release/ml_dsa_test" ];
          extraNativeBuildInputs = [ pkgs.perl ];
        };
      in
      {
        packages = { inherit ml-dsa ml-kem; };

        devShells.default = craneLib.devShell (
          toolsEnv
          // {
            packages = with pkgs; [
              clang_18
              fstarPkg
              jq
              openssl
              pkg-config
            ];
            inputsFrom = [
              ml-dsa
              ml-kem
            ];
            RUST_SRC_PATH = "${rustToolchain}/lib/rustlib/src/rust/library";
            LIBCLANG_PATH = "${pkgs.llvmPackages_18.libclang.lib}/lib";
          }
        );
      }
    );
}
