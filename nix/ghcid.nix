self: super:
{ ghcid = super.haskellPackages.callCabal2nix "ghcid" (
    super.pkgs.fetchFromGitHub {
      owner  = "ndmitchell";
      repo   = "ghcid";
      rev    = "f572318f32b1617f6054248e5888af68222f8e50";
      sha256 = "1icg3r70lg2kmd9gdc024ih1n9nrja98yav74z9nvykqygvv5w0n";
    }) {};
  }
