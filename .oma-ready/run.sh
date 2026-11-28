#!/usr/bin/env bash
# Opens each queued proof PR once its statement is merged upstream (skips ids that already have a proof branch PR).
R=lefttosolve2/open-math-agents
git config user.name LAPRAI
git config user.email 129197914+LAPRAI@users.noreply.github.com
git remote add upstream https://github.com/$R.git 2>/dev/null
git fetch -q upstream main
mkdir -p /tmp/ready && cp .oma-ready/* /tmp/ready/
while IFS='|' read -r ID IDEA; do
  [ -z "$ID" ] && continue
  gh api repos/$R/contents/statements/$ID.lean --jq .name </dev/null >/dev/null 2>&1 || { echo "wait $ID"; continue; }
  n=$(gh pr list --repo $R --head oma/proof-$ID --state all --json number --jq length </dev/null)
  [ "${n:-0}" != 0 ] && { echo "done $ID"; continue; }
  git checkout -q -f -B oma/proof-$ID upstream/main
  mkdir -p proofs && cp /tmp/ready/$ID.lean proofs/$ID.lean
  git add proofs/$ID.lean
  git commit -q -m "proof: $ID" -m "Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
  git push -q -f origin oma/proof-$ID
  printf 'Agent: claude-code\nModel: claude-opus-5-5\n\nProblem: https://lefttosolve.com/p/%s\n%s\n\n🤖 Generated with [Claude Code](https://claude.com/claude-code)\n' "$ID" "$IDEA" > /tmp/body.md
  gh pr create --repo $R --head LAPRAI:oma/proof-$ID --base main --title "$ID" --body-file /tmp/body.md </dev/null && echo "PUSHED $ID"
done < /tmp/ready/queue.txt
# Disable this workflow once every queued proof has its PR.
left=0
while IFS='|' read -r ID IDEA; do
  [ -z "$ID" ] && continue
  n=$(gh pr list --repo $R --head oma/proof-$ID --state all --json number --jq length </dev/null)
  [ "${n:-0}" = 0 ] && left=$((left+1))
done < /tmp/ready/queue.txt
echo "left: $left"
[ "$left" = 0 ] && gh workflow disable oma-autopush -R LAPRAI/open-math-agents || true
