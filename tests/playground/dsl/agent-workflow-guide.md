# Building Lean Projects with Claude Code: A Workflow Guide

This guide describes how the Radix DSL was built using Claude Code with multiple
agent sessions. The Radix DSL — a small imperative language with heap allocation,
functions, and verified optimizations — was developed almost entirely through
agent sessions: implementation, tests, proofs, and PR management. This document
captures the workflow so others can replicate it for their own Lean projects.

## Project Setup

### Separate Repository for Experimentation

The Radix DSL lives inside the Lean 4 monorepo (`tests/playground/dsl/`) but has
its own GitHub repository (`leodemoura/radix`) for independent development. This
separation is important:

- The main repo (`leanprover/lean4`) has CI, review requirements, and protected
  branches. You don't want agent experiments triggering any of that.
- A separate repo gives you a clean issue tracker, PR history, and the freedom
  to merge quickly without gatekeeping.

**Setup:**
```bash
# In your lean4 checkout
cd tests/playground/dsl
git remote add radix https://github.com/yourname/your-project.git
```

The project uses `lake` for building:
```bash
cd tests/playground/dsl
lake build Radix
```

### CLAUDE.md: Teaching the Agent Your Project

The `.claude/CLAUDE.md` file is the single most important piece of infrastructure.
It persists across sessions and tells every new agent instance how your project
works. For a Lean project, include:

1. **Build commands**: Exact commands to build and test. Agents will guess wrong
   without this.
2. **Success criteria**: "Never report success unless the build passes with zero
   errors and zero sorry." Agents are prone to declaring victory prematurely.
3. **Safety rules**: "Never delete build directories." "Never force-push without
   asking." Agents will take destructive shortcuts when stuck.
4. **Commit conventions**: Title format, body format, changelog labels. Agents
   produce inconsistent commit messages without explicit rules.
5. **What NOT to do**: Negative constraints are often more useful than positive
   ones. "Never edit files under `stage0/`" prevents a class of mistakes that
   would otherwise happen repeatedly.

Example from this project's CLAUDE.md:
```markdown
## Success Criteria
*Never* report success on a task unless you have verified both a clean
build without errors, and that the relevant tests pass.

## Build System Safety
**NEVER manually delete build directories** even when builds fail.
```

### Hooks: Guardrails for Dangerous Operations

Claude Code supports hooks — shell scripts that run before tool calls. Use them
to prevent agents from doing things you'll regret.

The Radix project uses a `guard-gh.sh` hook that blocks any `gh` command not
targeting the correct repository:

```bash
#!/usr/bin/env bash
# .claude/hooks/guard-gh.sh
# PreToolUse hook: only allow `gh` commands that target your-org/your-repo.

INPUT=$(cat)
COMMAND=$(echo "$INPUT" | jq -r '.tool_input.command // empty')

# If not a gh command, allow it
if [[ ! "$COMMAND" =~ ^gh[[:space:]] ]]; then
  exit 0
fi

# Block shell operators (&&, ||, ;, |, $())
if echo "$COMMAND" | grep -qE '&&|\|\||;|\||\$\(|`'; then
  echo '{"decision": "block", "reason": "gh commands must not contain shell operators."}' >&2
  exit 2
fi

# Allow commands targeting the correct repo
if echo "$COMMAND" | grep -qE '(-R|--repo)[[:space:]]+your-org/your-repo'; then
  exit 0
fi

# Block everything else
echo '{"decision": "block", "reason": "gh commands must target your-org/your-repo."}' >&2
exit 2
```

**Why this matters**: Without this hook, an agent working inside a monorepo will
create PRs against the parent repository, close the wrong issues, or push to
branches you didn't intend. This happened during Radix development — the agent
tried to create a PR against `leanprover/lean4` instead of `leodemoura/radix`.

### Memory Files: Cross-Session Learning

Claude Code has a persistent memory directory
(`~/.claude/projects/<project>/memory/`). Use it to record:

- **Remote setup**: Which remotes exist, which one to target for PRs.
- **Workflow mistakes**: Things that went wrong and how to avoid them.
- **Project conventions**: Patterns the agent should follow.

Keep `MEMORY.md` as a short index (under 200 lines — it's loaded into every
conversation). Put details in topic-specific files.

**What NOT to put in memory**: Session-specific state, speculative conclusions,
anything that duplicates CLAUDE.md. Memory is for stable patterns confirmed
across multiple interactions.

## Git and PR Workflow

### Branch Discipline

Agents will create branches and leave them behind. Each new session may inherit
a stale branch from a previous session. Rules:

1. **Always verify the current branch** before committing. The agent should
   check `git branch` and confirm it's correct.
2. **Branch from the right upstream**. For a project with its own remote, branch
   from `radix/master`, not `origin/master`.
3. **One branch per PR**. Name branches `radix/<topic>` or `<project>/<topic>`.
4. **Never force-push as a first resort**. If push is rejected, investigate the
   divergence. Usually `git rebase <remote>/master` is the right fix.

### PR Flow

```bash
# 1. Fetch latest
git fetch radix master

# 2. Branch from the project's master
git checkout -b radix/my-feature radix/master

# 3. Work, commit
git add <files>
git commit -m "feat: description"

# 4. Push to the project remote
git push radix radix/my-feature

# 5. Create PR against the project repo
gh pr create --repo your-org/your-repo --base master \
  --head radix/my-feature --title "feat: description" \
  --body "Description of changes."
```

### Cherry-Picking Across Branches

When work was done on the wrong branch (this will happen), use cherry-pick:

```bash
git checkout -b radix/correct-branch radix/master
git cherry-pick <commit-hash>
git push radix radix/correct-branch
```

Don't try to rebase an entire feature branch with unrelated history onto a
different upstream. Cherry-pick the specific commits you need.

## Working with Multiple Agent Sessions

### Session Boundaries

Each Claude Code session starts fresh (no memory of previous sessions beyond
CLAUDE.md and memory files). Implications:

- **Don't assume context carries over**. If session 1 created a branch and
  partial implementation, session 2 won't know about it unless you tell it.
- **Review the starting state**. At the start of each session, have the agent
  check `git status`, `git branch`, and `git log` to understand where things
  stand.
- **Clean up between sessions**. Merge or delete branches from previous sessions
  before starting new work.

### Task Decomposition

Break work into PR-sized pieces that can be completed in a single session:

| Task size | Example | Approach |
|-----------|---------|----------|
| Small | Add a simp lemma | Single session, direct commit |
| Medium | Prove a theorem | Single session with plan mode |
| Large | Add a new optimization + proof | Multiple sessions, one PR per piece |

For the Radix project, the typical flow was:
1. Session 1: Implement the feature (e.g., fuel-based interpreter)
2. Session 2: Write tests
3. Session 3: Prove correctness (fuel monotonicity)
4. Session 4: Prove more correctness (completeness, soundness)

Each session produces a mergeable PR. Don't let work accumulate across sessions
without merging.

### Plan Mode for Non-Trivial Proofs

For proofs that require exploring the codebase first, use plan mode:

1. Agent reads the relevant definitions (BigStep, interpreter, etc.)
2. Agent proposes a proof strategy (induction on what, which helpers are needed)
3. You review and adjust
4. Agent executes the plan

This prevents the agent from diving into a proof attempt that's structurally
wrong. For the soundness proof, the plan identified the need for reverse helper
lemmas and the `toStmtResult` naming trick before any code was written.

### When Things Go Wrong

Agents make mistakes. Common failure modes and fixes:

| Failure | Fix |
|---------|-----|
| Wrong branch | Cherry-pick to correct branch |
| Wrong remote | Add the correct remote, push there |
| Force-push proposal | Say "rebase locally" — agents default to destructive ops |
| Premature success claim | CLAUDE.md: "Never report success without a clean build" |
| Stale branch from previous session | Check `git branch` at session start |
| PR against wrong repo | Hook to block `gh` commands targeting wrong repo |

**The most important rule**: When the agent proposes something destructive
(force-push, delete build dir, `git reset --hard`), say no and tell it what
to do instead. Then add the lesson to CLAUDE.md so future sessions don't
repeat it.

## Lean-Specific Tips

### Build Verification

Always end with `lake build <Project>` (or the appropriate build command). The
agent must see the build succeed before reporting completion. IDE diagnostics
(LSP) can be stale — trust the command-line build.

### Zero Sorry Policy

For proof-heavy projects, grep for `sorry` after every proof session:
```bash
grep -r sorry Radix/Proofs/
```
Add this to CLAUDE.md as a success criterion.

### Proof Workflow

When asking the agent to prove something:
1. Point it at the definitions it needs to understand
2. Let it use plan mode to design the proof strategy
3. Have it build incrementally — prove easy cases first, then tackle hard ones
4. If a case is stuck after two attempts, have it investigate (read the goal
   state, understand why the tactic fails) rather than guess

### Mutual Recursion and Proofs

If your definitions use `mutual`, your proofs don't have to follow the same
structure. The Radix project demonstrated two patterns:

- **Fuel-based interpreter**: Avoids mutual recursion entirely. Induction on
  `fuel : Nat` gives a universally quantified IH over all statements.
- **Optimization correctness**: The optimization (`Stmt.inline`) uses `mutual`,
  but the proof does induction on `BigStep` instead. The mutual recursion is
  just structural plumbing — `simp only [Stmt.inline]` unfolds it at each case.
