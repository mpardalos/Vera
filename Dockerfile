FROM nixos/nix:2.32.8

RUN echo "extra-experimental-features = nix-command flakes" >> /etc/nix/nix.conf
# Add editors for convenience
RUN nix profile add nixpkgs#vim nixpkgs#nano

COPY . /work
WORKDIR /work

ENTRYPOINT ["nix", "develop"]
