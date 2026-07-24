#!/usr/bin/env bash
# One-shot provisioning of a lean4web instance serving QECLean.
#
# Target: a fresh Ubuntu 22.04 LTS box (the only OS lean4web claims to
# support). Run as a sudo-capable non-root user. Idempotent enough to re-run.
#
# Usage:
#   ./install.sh                       # build + install, no TLS
#   DOMAIN=lean.example.org ./install.sh   # also request a Let's Encrypt cert
#
# What it does NOT do: provision the server, point DNS, or open the firewall.
# See README.md in this directory for the full runbook.
set -euo pipefail

DOMAIN="${DOMAIN:-}"
QECLEAN_REF="${QECLEAN_REF:-main}"
ROOT="${ROOT:-$HOME/lean4web}"

echo "==> Installing system packages"
sudo apt-get update
sudo apt-get install -y git curl bubblewrap build-essential

if ! command -v node >/dev/null; then
  echo "==> Installing Node.js 20"
  curl -fsSL https://deb.nodesource.com/setup_20.x | sudo -E bash -
  sudo apt-get install -y nodejs
fi

if ! command -v elan >/dev/null; then
  echo "==> Installing elan"
  curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
  export PATH="$HOME/.elan/bin:$PATH"
fi

echo "==> Cloning lean4web into $ROOT"
if [ ! -d "$ROOT" ]; then
  git clone --recurse-submodules https://github.com/leanprover-community/lean4web.git "$ROOT"
fi
cd "$ROOT"

echo "==> Adding QECLean as a project"
# lean4web requires the project folder name and its root .lean file to match.
# QECLean's root module is QEC.lean, so the folder must be named exactly QEC.
if [ ! -d Projects/QEC ]; then
  git clone --branch "$QECLEAN_REF" https://github.com/Stavan-Jain/QECLean.git Projects/QEC
else
  git -C Projects/QEC fetch origin "$QECLEAN_REF" && git -C Projects/QEC checkout "$QECLEAN_REF" && git -C Projects/QEC pull
fi

cp Projects/QEC/deploy/lean4web/leanweb-config.json Projects/QEC/leanweb-config.json
cp Projects/QEC/deploy/lean4web/leanweb-build.sh   Projects/QEC/leanweb-build.sh
chmod +x Projects/QEC/leanweb-build.sh

echo "==> Installing npm dependencies"
npm install

echo "==> Building server + projects (this compiles QECTutorial; expect a while)"
npm run build

if [ -n "$DOMAIN" ]; then
  echo "==> Requesting TLS certificate for $DOMAIN"
  sudo apt-get install -y certbot
  sudo certbot certonly --standalone -d "$DOMAIN" --agree-tos -n \
    -m "${CERT_EMAIL:-admin@$DOMAIN}"
  # lean4web reads the cert paths from the environment; pm2 picks these up
  # from ecosystem.config.cjs, so patch them in there rather than exporting.
  echo
  echo "Set these in $ROOT/ecosystem.config.cjs before starting:"
  echo "  SSL_CRT_FILE: '/etc/letsencrypt/live/$DOMAIN/fullchain.pem'"
  echo "  SSL_KEY_FILE: '/etc/letsencrypt/live/$DOMAIN/privkey.pem'"
  echo "  PORT: 443"
fi

echo
echo "==> Done. Start it with:"
echo "      cd $ROOT && npx pm2 start ecosystem.config.cjs"
echo "    and check it with:"
echo "      npx pm2 logs lean4web"
