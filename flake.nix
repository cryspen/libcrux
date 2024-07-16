{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    crane = {
      url = "github:ipetkov/crane";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    charon = {
      url = "github:aeneasverif/charon";
      inputs.nixpkgs.follows = "eurydice/nixpkgs";
    };
    eurydice = {
      url = "github:aeneasverif/eurydice";
      inputs.charon.follows = "charon";
    };
    fstar.follows = "eurydice/fstar";
    karamel.follows = "eurydice/karamel";
    hax.url = "github:hacspec/hax";
  };

  outputs =
    inputs:
    inputs.flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import inputs.nixpkgs { inherit system; };
        googletest = pkgs.fetchFromGitHub {
          owner = "google";
          repo = "googletest";
          rev = "release-1.11.0";
          sha256 = "SjlJxushfry13RGA7BCjYC9oZqV4z6x8dOiHfl/wpF0=";
        };
        benchmark = pkgs.fetchFromGitHub {
          owner = "google";
          repo = "benchmark";
          rev = "v1.8.4";
          sha256 = "O+1ZHaNHSkKz3PlKDyI94LqiLtjyrKxjOIi8Q236/MI=";
        };
        json = pkgs.fetchFromGitHub {
          owner = "nlohmann";
          repo = "json";
          rev = "v3.10.3";
          sha256 = "EBzwaHyDWF8h/z3Zfq4p/n5Vpz7Ozlc3eoWDKXWv2YY=";
        };

        tools-environment = {
          CHARON_HOME = inputs.charon.packages.${system}.default;
          EURYDICE_HOME = pkgs.runCommand "eurydice-home" { } ''
            mkdir -p $out
            cp -r ${inputs.eurydice.packages.${system}.default}/bin/eurydice $out
            cp -r ${inputs.eurydice}/include $out
          '';
          FSTAR_HOME = inputs.fstar.packages.${system}.default;
          KRML_HOME = inputs.karamel.packages.${system}.default.home;

          CHARON_REV = inputs.charon.rev;
          EURYDICE_REV = inputs.eurydice.rev;
          KRML_REV = inputs.karamel.rev;
          FSTAR_REV = inputs.fstar.rev;
        };

        craneLib = inputs.crane.mkLib pkgs;
        src = ./.;
        cargoArtifacts = craneLib.buildDepsOnly { inherit src; };
        ml-kem = craneLib.buildPackage (tools-environment // {
          name = "ml-kem";
          inherit src cargoArtifacts;

          nativeBuildInputs = [
            pkgs.clang-tools
            pkgs.cmake
            pkgs.mold-wrapped
            pkgs.ninja
            pkgs.python3
            inputs.hax.packages.${system}.default
          ];
          buildPhase = ''
            cd libcrux-ml-kem
            python hax.py extract
            bash c.sh
            cd c
            cmake \
              -DFETCHCONTENT_SOURCE_DIR_GOOGLETEST=${googletest} \
              -DFETCHCONTENT_SOURCE_DIR_BENCHMARK=${benchmark} \
              -DFETCHCONTENT_SOURCE_DIR_JSON=${json} \
              -DCMAKE_EXE_LINKER_FLAGS="-fuse-ld=mold" \
              -DCMAKE_SHARED_LINKER_FLAGS="-fuse-ld=mold" \
              -G "Ninja Multi-Config" -B build
            cmake --build build --config Release
          '';
          checkPhase = ''
            build/Release/ml_kem_test
            build/Release/ml_kem_bench
          '';
          installPhase = ''
            cd ./..
            cp -r . $out
          '';
        });
      in
      rec {
        packages = {
          inherit ml-kem;
        };
        devShells.default = pkgs.mkShell (tools-environment // {
          packages = [
            pkgs.clang
            inputs.fstar.packages.${system}.default
          ];

          inputsFrom = [
            packages.ml-kem
          ];
        });
      }
    );
}
