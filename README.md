# BOSS SP-202 // Cleanroom Workstation (v1.0 Gold Master)

A **zero-dependency, single-file HTML5/CSS3/Vanilla JS** clean-room workstation modeled after the public functional specifications of the Boss SP-202 sampler, engineered for the Web Audio API and Canvas API.

## Architecture Overview

* **Zero External Dependencies:** Runs directly from a single `.html` file (`index.html` or standalone) paired with `202skin.jpg` in the same directory—no bundlers, frameworks, or runtime network packages.
* **32-Pad Multi-Bank Engine:** Organized into **4 banks (`A`, `B`, `C`, `D`) × 8 pads (`1–8`)**, each maintaining independent audio buffers, processed buffer caches, trim markers, pitch/rate state, sample grade, and mixer channel parameters.
* **Strict Single-Trigger Mono Pad Behavior:** Re-triggering an active pad cleanly cuts/replaces its prior voice on that pad slot so overlapping tails on the same pad do not stack uncontrollably.

---

## Web Audio DSP & Real-Time Signal Chain

1. **Sample Grade Decimation & Bit Quantization (`getProcessedBuffer`):**
   * `HI-FI`: `31,250 Hz` / `12-bit`
   * `STANDARD`: `15,625 Hz` / `10-bit`
   * `LO-FI 1`: `7,812 Hz` / `8-bit` (soft-clipped via `Math.tanh`)
   * `LO-FI 2`: `3,906 Hz` / `6-bit` (heavier `Math.tanh` saturation)
   * Processed buffers are cached per pad by `${grade}_${reverse}` for instant recall.
2. **Real-Time Mode Hot-Swapping (`hotSwapVoice`):**
   * Toggling **Grade**, **Loop / One Shot**, **Normal / Reverse**, or **Hold** while a pad is playing computes the normalized playhead position (`getPlayheadNorm`), crossfades/resumes at that exact point, and updates the active voice without waiting for a retrigger.
   * **Mono / Stereo** adjusts channel routing (`channelCount` / `channelCountMode`) live on the active voice gain stage.
3. **Parallel Filter & Master FX Bus (`applyFxRealtime`):**
   * Per-pad `fxSend` routes pads either dry to `masterGain` or into the shared FX bus (`fxInput`).
   * **Filter 1 (LPF)** and **Filter 2 (HPF)** run in parallel with a dry/bypass path (`thruGain`) using smoothed `setTargetAtTime` transitions to avoid filter-mode switching clicks.
   * **Ring Mod** modulates post-filter signal gain via a continuous `OscillatorNode` (`40 Hz–940 Hz` mapped by `FX CONTROL`).
   * **Delay** routes through a `DelayNode` + `3,800 Hz` damping `BiquadFilterNode` + feedback loop with `0.14s` slew smoothing on delay time changes to prevent zipper noise during real-time sweeps.
   * **Pitch** and **Time** FX modes dynamically scale playback rates on FX-routed voices and update all active voices immediately when toggled on or off.
   * **Cancel (`btn-cancel` / `Escape`)** acts as an immediate panic kill: stops transport and auditions, clears active pad voices, zeros delay feedback/wet tails, and resets transient modes.

---

## Front Panel, Sequencer & Workstation Modules

* **Hardware Skin & Knurled Knobs:** `VOLUME` and `FX CONTROL` knobs feature 24-flute knurled grip rings, recessed inner bezels, red center caps, white pointer inlays, and support vertical drag, mousewheel fine adjustment, and double-click reset.
* **Canvas 7-Segment LED Display:** Renders master BPM or active loop BPM on an HTML5 `<canvas>` with glow and segment persistence across resize/DPR changes.
* **Dynamic Mode Display & 5 Mode Buttons:** Tracks active bank (`A–D`), sample grade, mono/stereo, trigger/gate, loop/one-shot, and normal/reverse states.
* **REMAIN & DEL Modes:** `REMAIN` toggles blue FX-bus assignment on pads; `DEL` arms pad deletion (select pad, press `DEL` again to clear).
* **Draggable Sample Explorer:** Opens via the top-right SP-202 skin hit-target (`#btn-sp-explorer`) or the rack `EXPLORER` button. Supports folder/file loading (`webkitdirectory` and multi-file audio input), click auditioning, and drag-and-drop assignment onto pads.
* **MARK Wave Editor:**
  * **Mini-Wave Navigator** for panning across long samples + **zoomable main waveform canvas** (mousewheel zoom, `+` / `-` / `FIT` controls, up to `2048x` depending on sample length).
  * **Start / End Chopping:** Left-drag or `START POINT` slider for start; right-drag or `END POINT` slider for end (with a `15 ms` minimum chop window and live white playhead).
  * **Per-Sample BPM & Pitch Stepper:** Pitch slider (`-12.00` to `+12.00 st`, double-click resets to `0.00 st`), `-` / `+` steppers by `1 BPM`, direct decimal BPM typing, beat-length cycling (`1B` / `2B` / `4B` / `8B` / `16B` / `32B`), `MATCH` (pitch sample to master BPM), and `→MST` (lock master BPM to sample BPM).
* **16-Step Velocity Sequencer:** 8 tracks per bank across 8 patterns (`P1–P8`) with swing control, `BOOM-BAP` preset, and per-step/per-track velocity (`15%–100%`):
  * **Click** a step to toggle on/off; **drag up/down** on a step to adjust velocity (dimmer LED for lower velocity, brighter glow for higher velocity).
  * **Drag up/down** on each track's velocity square (beside `M`) to set that track's paint velocity.
* **8-Track Mixer & 16-Bar Song Arranger:** Per-pad `PAN`, `TUNE`, vertical fader with grip cap, 12-segment peak meter, `FX`, `M` (mute), and `S` (solo), plus a 16-bar song arranger chaining patterns (`P1–P8`) and per-track bar mutes.

---

## Controls & Shortcuts

| Control / Input | Action |
| :--- | :--- |
| `1` – `8` (Keys) | Select and trigger Pads `1–8` in the active bank (respects `GATE` hold/release) |
| `Space` | Start / stop transport |
| `Escape` | Panic kill all audio, tails, and transport |
| `FX CONTROL` (Drag / Wheel / Dbl-Click) | Adjust active FX parameter (`0–100%`); double-click resets to `50%` |
| `VOLUME` (Drag / Wheel / Dbl-Click) | Adjust master output gain (`0–100%`); double-click resets to `85%` |
| Wave Canvas Left-Drag / Right-Drag | Set `START` (left-click drag) or `END` (right-click drag) trim point |
| Wave Canvas Scroll Wheel | Zoom in/out around cursor position |
| Sequencer Step Click / Vertical Drag | Click to toggle step; drag up/down to adjust step velocity |

---

## File Structure

* `sp202-workstation.html` — Complete self-contained HTML5, CSS3, and JavaScript application
* `202skin.jpg` — Front-panel SP-202 hardware skin image (placed alongside the HTML file)
