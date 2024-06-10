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
  };

  outputs =
    inputs:
    inputs.flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import inputs.nixpkgs { inherit system; };
        googletest = pkgs.fetchzip {
          url = "https://github.com/google/googletest/archive/refs/tags/release-1.11.0.zip";
          sha256 = "SjlJxushfry13RGA7BCjYC9oZqV4z6x8dOiHfl/wpF0=";
        };
        json = pkgs.fetchzip {
          url = "https://github.com/nlohmann/json/archive/refs/tags/v3.10.3.zip";
          sha256 = "EBzwaHyDWF8h/z3Zfq4p/n5Vpz7Ozlc3eoWDKXWv2YY=";
        };
        craneLib = inputs.crane.mkLib pkgs;
        src = ./.;
        cargoArtifacts = craneLib.buildDepsOnly { inherit src; };
        ml-kem = craneLib.buildPackage {
          name = "ml-kem";
          inherit src cargoArtifacts;
          nativeBuildInputs = [
            pkgs.clang-tools
            pkgs.cmake
            pkgs.gbenchmark
            pkgs.mold-wrapped
            pkgs.ninja
            pkgs.python3
          ];
          buildPhase = ''
            cd libcrux-ml-kem
            bash c.sh
            cd c
            cmake \
              -DFETCHCONTENT_SOURCE_DIR_GOOGLETEST=${googletest} \
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
          installPhase = "cp -r . $out";
          CHARON_HOME = inputs.charon.packages.${system}.default;
          EURYDICE_HOME = pkgs.runCommand "eurydice-home" { } ''
            mkdir -p $out
            cp -r ${inputs.eurydice.packages.${system}.default}/bin/eurydice $out
            cp -r ${inputs.eurydice}/include $out
          '';
          FSTAR_HOME = inputs.fstar.packages.${system}.default;
          KRML_HOME = inputs.karamel.packages.${system}.default.home;
        };
      in
      {
        packages = {
          inherit ml-kem;
        };
      }
    );
}
