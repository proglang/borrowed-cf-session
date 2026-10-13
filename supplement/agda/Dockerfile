FROM nixos/nix:2.35.2

## GENERIC SETUP FROM NIX FLAKE ##

# Enable the nix command and flakes.
RUN set -ex; \
  mkdir -p "$HOME/.config/nix"; \
  echo 'experimental-features = nix-command flakes' >> "$HOME/.config/nix/nix.conf"; 

# Install tools as specified by docker/flake.nix.  docker/flake.lock pins the
# versions.
WORKDIR /workspace/setup
COPY docker .
RUN set -ex; \
  nix profile add -L .; \
  nix store gc;


## ADDITIONAL AGDA SPECIFIC SETUP ##

# RUN set -ex; \
#   mkdir -p "$HOME/.agda"; \
#   echo "standard-library" >> "$HOME/.agda/defaults";

# Copy agda files.
WORKDIR /workspace/borrowed-cf
COPY borrowed-cf.agda-lib .
COPY BorrowedCF BorrowedCF
