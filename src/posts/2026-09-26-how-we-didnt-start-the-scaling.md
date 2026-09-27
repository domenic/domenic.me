---
layout: layouts/post
title: "“We Didn't Start the Scaling”"
date: 2026-09-26T00:00:00Z
tags: [other]
blurb: Claude and I updated “We Didn't Start the Fire” to chronicle the singularity era.
---

_If you want to skip the narrative buildup and go straight to the songs and music videos, [here you go](/we-didnt-start-the-scaling/)._

---

I've always had a soft spot for music that chronicles history. I have a core memory of walking into the first day of my 20th-century world history class: my teacher had turned down the lights and was playing ["Russians" by Sting](https://www.youtube.com/watch?v=wHylQRVN2Qs).

A classic in the genre is, of course, Billy Joel's ["We Didn't Start the Fire"](https://www.youtube.com/watch?v=eFTLKWw542g), with its fast-paced chronicle of 1949–1989 via a series of rhyming allusions. A few months ago I was bopping along to the song in the bouldering gym, when I heard some unfamiliar lyrics:

> Nuclear accident, Fukushima Japan\
> Crimean peninsula\
> Cambridge Analytica\
> Kim Jong Un\
> Robert Downey Jr. Iron Man

That doesn't sound quite right…

That's when I found out Fall Out Boy had [updated the song](https://www.youtube.com/watch?v=2LkVKCWL0U4) for the period 1989–2023. Wikipedia says it was critically panned, but I liked it: FOB was telling the story of my generation.

---

The singularity era has given rise to an epidemic of "monitoring the situation". Like many others, I was glued to my phone during the OpenAI board saga weekend. When o3 was announced, proving that test-time compute was a viable scaling axis, that's when [we knew](https://x.com/nickcammarata/status/1870217709822324942) this wasn't slowing down. And indeed: the next year brought Mythos, the Hugging Face hack, and everything in between.

It was finally [one of the Twitter anons I follow](https://x.com/tautologer) who made the obvious move: to [document contemporary events](https://x.com/tautologer/status/2085048713014378646) in the style of Billy Joel.

> Mythos might be misaligned,\
> Jeff left Google just in time,\
> Claude disproved Jacobian,\
> Gwern gave up his pseudonym!
>
> We didn't start the fire...

I was captivated. Fable 5 and I jammed away, producing the first draft of "We Didn't Start the Scaling" in short order.

> "Attention" lit the fuse,\
> Scaling laws you can't refuse,\
> Gwern said "stack the compute high,"\
> Few-shot learners multiply.

I then got too ambitious. I wanted something that sounded like it was Fall Out Boy singing my lyrics. Suno refuses to do anything too close to an existing artist, so we spent a long time trying to hack together MiniMax Music, Whisper and Gemini judges, demucs stem separation, a WSL bridge to my GPU box, and eventually a from-scratch DiffSinger renderer. The melody was the sticking point: even with the vocals stripped out of FOB's cover, Suno wouldn't touch it, and MiniMax couldn't sing well enough to match it. In the end I went back to plain Suno, abandoning the goal of sounding like FOB, and put out [something I didn't hate](https://suno.com/song/1df45a3d-ff7f-4288-8bd8-3b40583db32f). I [tweeted it out](https://x.com/domenic/status/2085186224030097859), and mostly got crickets in response.

Oh well, I thought. Sometimes, the things I'm excited about just don't strike a chord. And I mean, it wasn't *that* good, anyway.

---

Then came [Opus 5.5](https://www.anthropic.com/claude-opus-5-5), and with it, "I'm Upping My P(Doom)".

The family tree here is a little tangled. The earliest version anyone can find is ["P(doom)"](https://www.youtube.com/watch?v=uEB5E67vcPA) on YouTube, by the mysterious [osmarks](https://osmarks.net/me/). We don't know how the music was generated, but Suno is a reasonable guess. On 2026-09-10, deckard a.k.a. @slimer48484 [tweeted](https://x.com/slimer48484/status/2097752569212756134) a more boppin' version with some 3D-animated flower-Claudes. ([deckard says](https://x.com/slimer48484/status/2102771604338200586) the music was Suno-generated, although not by deckard themselves.)

But things really took off with [the version by](https://x.com/other__reality/status/2102514581684052169) John Heibel (a.k.a. NotinReality a.k.a. @other__reality), on 2026-09-23. The novel ingredient was the animation created by Opus 5.5, with a cute Clawd mascot and per-line high-context visual gags. That got the coveted retweets from [Anthropic](https://x.com/Mononofu/status/2102559415572549801) and [OpenAI](https://x.com/tszzl/status/2102562178381619573) employees, and went appropriately viral. Others jumped on the bandwagon with their own Opus 5.5-generated music videos, of which my favorite is [Pleometric's](https://x.com/pleometric/status/2103082510607610023).

I was inspired. It was time to dust off "We Didn't Start the Scaling", and see what Opus 5.5 could do with it.

---

The results were excellent. The updated lyrics for the last month were, as they say, fire. The music video was essentially perfect out of the gate: creative, funny, and cute. Claude decided to try Lyria 3.5, and the results were pretty good, although pronunciation needed some iteration.

But I wanted to go bigger this time. For those not as terminally online as I, wouldn't it be nice to have a little website explaining all the references? ([Like "P(doom)" has!](https://docs.osmarks.net/hypha/p(doom)_song_objectively_correct_interpretation) But, y'know, Opus-ified.) And, why stop at Fall Out Boy-adjacent pop-punk? The lineage from Billy Joel to FOB has already experienced one genre shift. Why shouldn't the next link in the chain be … K-pop? Or Eurodance?

I spent the next few days in a frenzy, remote-controlling my Claude session from all over Tokyo. Opus commandeered my desktop's browser to manipulate Suno; monopolized its GPU to run Whisper judges and paint anime stills; ran an anime art-style bake-off; and self-audited to fix subagent hallucinations, find paywall-less news sources, and remove explaining-the-joke textual labels in the videos.

And so I present: ["We Didn't Start the Scaling"](/we-didnt-start-the-scaling/), an interactive album mini-site with six main tracks. We've got pop-punk, piano rock, K-pop, eurodance, anisong, and indie folk, each with its own original music video. The videos are all drawn live in the browser, and the page re-themes itself per video, [CSS Zen Garden](https://en.wikipedia.org/wiki/CSS_Zen_Garden)-style. Plus, we threw in eight more genres of bonus tracks, which I couldn't bear to leave on the cutting room floor.

Or, if you prefer the comforting embrace of the mega-aggregators instead of indie .me domains, [Claude uploaded everything to YouTube](https://youtube.com/playlist?list=PLVlkoGh161h0&si=X_93bYMFC1xjq40n).

Please enjoy! And if you think it's good, tell your friends. I'm pretty proud of this one, and would love for it to be shared widely.

<figure>
  <img src="/images/wdsts-desk-shot.jpg" width="4000" height="3000" alt="Me at my home office desk holding a Clawd plushie, with three monitors in the background displaying Claude busily prepping the site for publication">
  <figcaption>Hello, from me and Claude!</figcaption>
</figure>
