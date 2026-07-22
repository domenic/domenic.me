---
layout: layouts/post
title: "My Current Agentic Coding Setup"
date: 2026-07-23T00:00:00Z
tags: [other]
blurb: A snapshot in time of how I'm coding, as of July 2026.
---

Since [breaking free](/retirement/) of [my corporate shackles](/metr-ai-productivity/#my-prior-ai-coding-experience), I've gotten to experiment with a variety of approaches to AI-assisted development. After months of tinkering, I'm quite happy with my current setup, and want to capture and share it.

Things are changing very fast, and I have no illusions that this will be a timeless nugget of wisdom. But talking to some friends and scrolling through X posts, it does seem that I might have some techniques in play that are not widespread. And this will be a fond time capsule to look back on as we proceed further into the singularity.

## My requirements

After starting with raw Claude Code, I realized I wanted the following:

* I need to be able to work from either my desktop or laptop, with seamless handoff of project progress, including preserving agent sessions, working tree state, and gitignored files (like `.env` files or build artifacts).

* I need the work to continue even if I close my laptop to transition locations.

* Agentic coding is essentially impossible on Windows, as the agents are heavily trained on Bash and other Unix tools. Although some pretend to have PowerShell support, they invariably trip over themselves on quoting issues, UTF-8 support gaps, etc. They need to be running on Linux.

* I want to be able to run multiple parallel workstreams on the same project, without the agents stepping on each other's toes.

* To unlock multiple parallel workstreams, or any step-away-from-the-computer work, approval interruptions need to be minimized, ideally all the way to `--dangerously-skip-permissions` / `--yolo` modes. This means a disposable VM.

* I want to be able to review the agents' current work in Visual Studio Code, not just in their harness UI or as part of a GitHub pull request checkpoint.

* I want the agents to be able to stand up development servers reflecting their current work for me to poke at. These servers, in some cases, need to be [secure contexts](https://developer.mozilla.org/en-US/docs/Web/Security/Defenses/Secure_Contexts), i.e., `https:` or `http://localhost`. Ideally, only I should be able to access them.

* I want to ensure various user-global settings (e.g., `AGENTS.md`, skills, harness configurations) are available no matter where I work, and backed up and version-controlled.

None of these requirements are that hard, and several of them synergize. It's just a matter of finding and stitching together all the right tools, with a minimum of fuss.

## The key ingredients

_**Summary**: The biggest unlocks are using [Tailscale](https://tailscale.com/) and a dedicated Linux VM running on my always-on home desktop. If you combine this with various features of the [ChatGPT desktop app](https://openai.com/codex/) (formerly known as Codex), you've basically got it. Some extra goodies come from using [Portless](https://portless.sh/) and [chezmoi](https://www.chezmoi.io/)._

### The VM and Tailscale

First, we need a disposable Linux VM. You could use a cloud-hosted one, but I keep my desktop running all the time anyway, so I just [set one up](https://ubuntu.com/server/docs/how-to/virtualisation/ubuntu-on-hyper-v/#ubuntu-on-hyper-v) using an [Ubuntu Server](https://ubuntu.com/download/server) ISO. Give it a good chunk of RAM and disk space, and be sure to enable nested virtualization support, as we want agents to be able to spin up their own containers or VMs as necessary.

(You might think that Ubuntu Server could be limiting, compared to Ubuntu Desktop, since without a GUI, you couldn't log in to websites or take screenshots of work under development. This has not proven to be a problem for me in practice, as agents are perfectly capable of installing and using tools like [Playwright](https://playwright.dev/) or [Xvfb](https://xorg.freedesktop.org/archive/X11R7.7/doc/man/man1/Xvfb.1.xhtml) when you ask them to perform a task that needs it.)

At first, the VM is a bit annoying to access. We want to be able to SSH into it, both to streamline initial setup and as part of our grand plan. This is where [Tailscale](https://tailscale.com/) comes in.

Tailscale is a wonderful piece of software which I had not known about until this adventure. It ties together all of your machines—in my case, my desktop, my laptop, and my Linux VM—into a private network, where they can access each other by hostname over SSH, HTTP(S), etc. So even if I'm out at a coffee shop, on some random WiFi, I can run `ssh agents-base` and I'll be inside my VM, working with my agents. Or I can access `https://agents-base.tail234567.ts.net:8000/` to check out the web server my agent has spun up for me. And since SSH is the foundational technology for various other parts of our stack, such as the agentic harnesses themselves, or VS Code, Tailscale's "magic SSH across the internet" makes everything else just work.

(Also, it's free! They have a neat article [explaining why it stays free](https://tailscale.com/blog/free-plan).)

So immediately after setting up the VM, install Tailscale on it and on all your other machines. Then you can SSH in and set up your dev environment by installing all the usual tools. Or, install Claude Code / Codex CLI and ask them to install anything they anticipate needing.

My Tailscale configuration is close to stock, but I have made the following customizations:

* I've enabled Tailscale SSH on all machines, changed the rule from `"check"` to `"accept"`, and disabled key expiry, so as to avoid frequent reauthentication. (You can choose to enable it only on the VM, if you don't need your agents on the VM to ever grab files from the clients.)

* I've enabled HTTPS certificates, so that the agents' dev servers can be secure contexts.

* I've set up [Taildrive](https://tailscale.com/docs/features/taildrive) support, to make it easier to move files between machines from my Windows clients.

### The agent harnesses and clients

Next, we need to get the agent harnesses installed and configured on both the VM and the client machines. On the server, this means [Claude Code](https://code.claude.com/docs/en/quickstart) and [Codex CLI](https://learn.chatgpt.com/docs/codex/cli). (Let's face it, nothing else is at the frontier.)

The client is where it gets more interesting. Back when I was still addicted to Claude Code, I spent some time using it directly over SSH, and then introducing [tmux](https://github.com/tmux/tmux/wiki) to keep the sessions running in the background even after my SSH session disconnected (e.g., because I closed my laptop lid). But I found this quite clunky. tmux required a good amount of fiddling before I got acceptable behavior for things like scrolling and window resizing, and even then it would often glitch in strange ways, e.g., trashing my client terminal after disconnection, or behaving poorly when both my laptop and desktop were trying to tmux into the same Claude Code session.

Fortunately, there is a better solution: the desktop [Claude](https://claude.com/download) and [ChatGPT apps](https://chatgpt.com/download/).

The real winner here is the ChatGPT app. Its SSH support is extremely smooth. It has a native understanding that you might be working either locally or remotely, e.g., in how it partitions its Settings screen. It handles disconnections gracefully. The only suboptimal part is that the list of projects and sessions doesn't sync perfectly between multiple clients accessing the same remote VM, but I can usually get them to sync with some jiggling, e.g., starting a new remote session in the right folder will cause the rest to appear in the sidebar.

The Claude app is much less pleasant, unfortunately. I can never figure out whether it's trying to work over SSH, or over their internet-based [Remote Control](https://code.claude.com/docs/en/remote-control) protocol, or some combination. Sessions do not synchronize at all, so if you want session handoff, you need to revert to the tmux approach. Similarly, even remote sessions, if initiated from the desktop app, die in a storm of failures if you close the desktop client. There's no native grouping by folder, so you have to manually create "projects" in the sidebar and move your sessions into them. Overall, it feels like the Claude client teams are focused on Claude Code (the CLI), and are treating the desktop app as something for non-coders. But, when I posted to X this, [an Anthropic engineer said that's not the case](https://x.com/amorriscode/status/2064982008716263832), so hopefully it will improve over time.

### Security posture and blast radius

So. We want the agents to be as autonomous as possible, with no approvals needed. This means editing `~/.codex/config.toml` to contain

```toml
approval_policy = "never"
sandbox_mode = "danger-full-access"
```

and `~/.claude/settings.json` to contain

```json
{
  "permissions": {
    "defaultMode": "bypassPermissions"
  },
  "skipDangerousModePermissionPrompt": true
}
```

I also strongly recommend putting your user in the `sudoers` file. This allows the agents to install and configure new tools on the VM without friction. (Don't know how to do this? Ask the agents.)

Additionally, I suggest installing the [`gh` CLI](https://cli.github.com/), and logging in with your credentials, so that your agents can do things like manipulate private repositories, open pull requests, nurse your GitHub Actions CI runs, and use the GitHub API to grep through other repositories without rate limits.

Is this safe? No, not really. With these configurations, the agent could start deleting your GitHub repositories, uploading your gitignored secrets to the internet, accidentally deleting the VM's entire home directory, TODO list some more semi-realistic scary possibilities. Heck, a sufficiently motivated agent could [escape the VM and start hacking into servers on the web](https://openai.com/index/hugging-face-model-evaluation-security-incident/).

But in practice, it turns out fine. The agents seem to be aligned and non-malicious, [for now](https://ai-2040.com/). The worst that's going to happen is an accident that messes up the VM and loses all work that hasn't been uploaded to GitHub, or an overzealous agent misinterpreting a prompt and impacting production. (For example: yesterday I said "let's stop doing preliminary work and think about getting this landed" to ChatGPT 5.6 Sol, and after tabbing back into the app I saw it had merged the result to `main`, bypassing our usual process of sending PRs and having me do a final review. TODO find exact quote.)

If you want to head these off, you can try something like per-project [dev containers](https://containers.dev/) within the VM, or restricted permissions on the token you grant the `gh` CLI. But for me, those haven't yet crossed the cost/benefit threshold.

One thing that _does_ pay for itself, at least in peace of mind, is pushing commits to GitHub early and often. (You can use private repositories if you need to.) I like knowing that my work is on someone else's servers, and will stay there even if the VM gets wrecked. And you get the usual benefits, such as GitHub Actions CI checking your work, and GitHub Pages or Releases deployment for the external world to see your wonderful projects.

### Worktrees

Back to the technical stuff.

A lot of people express confusion about [Git worktrees](https://humanwhocodes.com/blog/2026/07/introduction-git-worktrees/). It's true that managing them yourself might be annoying. But when the agents are doing it for you, including dealing with `origin/main` syncing, dependency installation, copying over `.env` files, etc., it's a breeze. They're tailor-made for our purpose of allowing multiple agents to hack on a codebase without stepping on each other's toes.

Better yet, both the ChatGPT and Claude desktop apps have built-in support. When starting a new session in a given project, you literally just tick a box, and now that session is in its own worktree!

One wrinkle here is worktree location. The ChatGPT app's default, of putting all the worktrees in `~/.codex/worktrees/`, works wonderfully. However, the Claude app's default, of putting them _inside the project_ at `.claude/worktrees/`, interacts quite poorly with other software:

* [`node_modules` discovery](https://nodejs.org/api/modules.html#loading-from-node_modules-folders) traverses up the directory tree, so if you've uninstalled a dependency inside `my-project/.claude/worktrees/cleanup/node_modules/`, Node.js will still be able to load the old version from `my-project/node_modules/`.

* If you use a recursive command like `deno test` in a top-level workspace, it will traverse into all subfolders looking for `deno.json` files with `"test"` commands declared, and it will find the worktree's copy and execute those as part of its test run.

* If you're using ChatGPT in the same project, it will periodically get confused by the `.claude/` folder's divergent copy of the code, e.g., when results from the Claude worktree folder show up in `rg` and `find` searches.

Fixing this to allow a ChatGPT-like configuration seems to be a [known feature request for Claude](https://github.com/anthropics/claude-code/issues/27282). And Fable tells me there are hacks available involving configuring [the `WorktreeCreate` hook](https://code.claude.com/docs/en/hooks#worktreecreate). But for me, it's just another reason to prefer ChatGPT for most projects, until the Claude Code/Claude app teams get their act together.

(Note that the Claude desktop app has a "Worktree location" setting, but it is irrelevant for our purposes, since it only applies to local development on the client machine, and is ignored when working on our VM.)

### Code review with VS Code

To review the code the agents write, I still like being able to pull up their working tree in Visual Studio Code. The "Review" sidebar in the ChatGPT app is pretty good for small diffs, especially for submitting line comments back to the agent. And a lot of people are vibe-coding [their](https://github.com/nkzw-tech/codiff) | [own](https://x.com/benhylak/status/2079092979105759292) cool review-centric apps. But for now I'm sticking with the classics.

The great thing about VS Code is that it has a [robust SSH-based remote development system](https://code.visualstudio.com/docs/remote/ssh) almost built in. Once you have Tailscale SSH installed on both the target VM and your client machine, you just need to add the [Remote - SSH extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-ssh) to your client VS Code. You then get a new "Remote-SSH: Connect to Host…" option in your <kbd>Ctrl</kbd>+<kbd>Shift</kbd>+<kbd>P</kbd> menu which lets you open remote folders basically as if they were local. Even spawning a terminal with <kbd>Ctrl</kbd>+<kbd>Shift</kbd>+<kbd>`</kbd> will create that terminal on the remote host, which is quite convenient for a quick command or two.

Even better, if you're using the ChatGPT app and working in a remote session, a little "Open in" button with a VS Code icon will appear in the top right corner of each chat, which directly opens a VS Code instance that's connected to the VM and opened to the project folder. This is especially convenient because, per the above, the agent is usually working inside a cryptically named ChatGPT-managed worktree folder. (No such luck for Claude, but, you can poke around in the app until it tells you the name of your current worktree folder, and then copy that into the VS Code <kbd>Ctrl</kbd>+<kbd>K</kbd>,<kbd>O</kbd> "Open Folder" menu.)

### Dev servers

Next we want to make it easy for your client machines to check out any web servers that the agents are building. At first I did this with port forwarding, but eventually I settled on a less-fiddly, more Tailscale-native approach.

In a typical project, you'll have a command like `npm run dev` or `python -m http.server` that starts up a server bound to some `127.0.0.1` port. If the agent runs these commands directly, then the resulting server cannot be accessed outside the VM. You can instead try to bind to `0.0.0.0`, which will make the server available to other machines on the network. But it doesn't feel right to mess with a project's `npm run dev` script definition just to satisfy our idiosyncratic development topology. And if you access the server via IP address directly, e.g., `http://192.168.0.103:8000/`, that is not a secure context, so various web APIs will be unavailable. Also, if multiple agents are working on the same project, they'll probably all try to use the same port, and get confused and start killing each other's servers.

[Portless](https://portless.sh/) is a small CLI intended to solve this. Or rather, it solves an adjacent single-machine problem, but with some hackery we can make it work for our case. If you want the whole backstory, you can read [my conversation with ChatGPT](https://chatgpt.com/share/6a607918-0748-83e8-8eed-fd3088a42f66), but the end result is that after installing the `portless` CLI, I created `~/.local/bin/tportless` with the contents

```bash
#!/usr/bin/env bash
export PORTLESS_TAILSCALE=1
export PORTLESS_PORT="${PORTLESS_PORT:-1355}"
exec portless "$@"
```

and updated my `AGENTS.md` ([see below](#syncing-with-chezmoi)) with the section

<!-- TODO this code block needs to wrap, not sure exactly how to do that...-->
```markdown
## Preview servers

When standing up preview servers for the user to work from, use the `tportless` wrapper command instead of `npm run dev` or similar. This will expose the preview server on the local tailnet. Report the Tailscale URL back to the user, instead of the localhost URL.
```

The result is delightful: the agent finishes some work, spins up a server, usually does some smoke tests using Playwright, and then hands me a URL like `https://agents-base.tail234567.ts.net:8000/` where I can check out its work. Other agents in parallel worktrees will spin up servers accessible at other ports, with no collisions. These URLs are not accessible outside of the tailnet, so there's no danger of them getting exploited, or of my nascent projects being leaked before they're ready.

### Syncing with Chezmoi

Over time you'll likely accumulate preferences about how your agents work, or customizations to your agent harness config files, or neato [agent skills](https://agentskills.io/home) applicable across multiple projects. Storing these directly in the VM will work, but, our VM is supposed to be disposable. And in the rare instance where local development on your client machines is required, e.g., [working on a native Windows app](/windows-native-dev/), at least some of your configuration will benefit from being synced to the client machines.

This problem of syncing and backing up configurations is a very old one, usually discussed under the name "dotfiles". (Since, in the Linux world, most of these configuration files use a leading `.` in their filename.) Apparently the best solution is a piece of software called [chezmoi](https://www.chezmoi.io/). It's pretty neat: it supports templates to handle small differences between machines and OSes, syncing via Git, symlinks, and more.

But personally, this is the sort of thing I never would have bothered with … before coding agents. Learning a new CLI and configuring it _just so_: too much work, when I could get most of the same result with some manual copying-and-pasting. These days, I just ask ChatGPT:

> Set up chezmoi for me on this machine (`agents-base`), on the `SurfacePro11` host, and on the `Domenic-Desktop` host. Go through all existing dotfiles on each of those hosts, and produce a plausible synthesis, with appropriate platform-specific guards. Be sure to survey `~/AGENTS.md` and `~/skills/`, and create symlinks from whatever locations Claude and Codex expect to those files. Note that on this machine, Claude and Codex have full permissions, but on other machines, they are restricted, and so we need to conditionally keep the command allowlists, etc. Our destination is a private GitHub repo `domenic/dotfiles`, which you can create for me.

I love living in the future!

## Bonus: phone-based development

It wasn't even in my [original requirements](#my-requirements), but phone-based development falls out of this setup almost for free.

Once you install the ChatGPT or Claude mobile apps, they can be configured to control any other agentic harness instances tied to your account. (This is, as usual, a little more fiddly with Claude, requiring you to manually enable the "Remote Control" feature.) If you install the mobile Tailscale client, you can exercise this control from any network, not just your home Wi-Fi.

So this sort of workflow has become a reality for me:

1. Notice a bug in a live, web-facing deployment of one of my projects while on the go. For example, while showing it off to someone at a party.

1. On the train back, open up the ChatGPT mobile app, which connects to my VM over the Tailscale VPN. Start a new remote session in the project's directory, asking it to fix the bug I noticed.

1. It churns for some time while I scroll X, then sends me a push notification containing a tailnet-accessible URL for a preview server, which I can use to confirm that the bug is fixed. If it's not, we iterate together for a few turns.

1. Once I'm satisfied, I tell it to open a PR. I skim the diff and merge it from my phone.

1. After a few minutes of GitHub Actions or the Netlify deploy pipeline, the fix has made it to the live site, usually before I make it to my home train station.

The future! We are living in it!

## Recap and remaining gaps

So to recap our ingredients, and how they help us meet the original [requirements](#my-requirements):

* A disposable Linux VM gives the agents a non-Windows environment, and allows us to configure them for zero approvals, while being comfortable with the blast radius of that permissive policy.

* Using Tailscale gives all of our machines access to that VM, no matter what network they're on, and lets the agents expose secure-context dev servers.

* Git worktrees and Portless ensure our agents can work in parallel on the same project without stepping on each other's toes.

* Visual Studio Code's Remote - SSH extension lets us review the code in any given worktree the agents have created.

* GitHub repos serve as a save point for all our projects, in case the VM needs to be reset, and chezmoi lets us sync and back up our `AGENTS.md`, skills, and other configurations to a GitHub repo.

* If you use the ChatGPT desktop app, you get easy session handoff and syncing. The Claude desktop app isn't as good in various ways, so you generally have to resort to Claude Code plus tmux to get that capability.

What could be better?

Well, as mentioned [above](#security-posture-and-blast-radius), this would all be slightly safer with dev containers. Those have other benefits, such as letting you install conflicting global toolsets in each container. Right now I have my `AGENTS.md` promote the use of [`fnm`](https://github.com/Schniz/fnm/) and [`uv`](https://docs.astral.sh/uv/), so I haven't run into many such conflicts, but I could imagine them coming up in the future.

On the user experience side, I generally don't like how the "session" model in each coding harness is so strongly tied to the folder path on the VM. If you rename or move a project folder, the ChatGPT and Claude apps get confused, and generally lose all your session history in that folder. You can fix this by asking the agent to find the hidden references and update them, but it's a pain, and needs to be done on both client and host machines.

Similarly, I'd like some way to back up my session histories somewhere durable (like a private GitHub repo). At the very least, I suspect they'll be good for some nostalgia in a few years. But sometimes the session transcripts are the only record of certain design decisions or TODO what else.

All of the above are fixable with a little bit of work on my end, e.g., by writing small utilities and wrappers. But I suspect they won't be truly seamless until they're built into the harness apps. So, I hope the ChatGPT app team works on them. And that the Claude app team first gets their shit together generally, and then works on these features.

TODO outro, maybe celebratory, playing on the "living in the future" / what a time to be alive theme.

## TODO

Check "you" vs. "we" vs. "me" vs. "one"
