# Signal OPS

**A game played with the real Bluetooth devices around you.**

Signal OPS is a terminal game and passive Bluetooth Low Energy (BLE) scanner. It listens to the advertisements that phones, watches, earbuds, trackers, cars, cameras and smart-home gadgets broadcast all day long, works out what each device probably is, estimates how close it is, and turns it all into a game with XP, levels, quests, bounties and achievements.

Designed and tested on the **Steam Deck**. Free and open source. Developed by one person.

## It is a real scanner

Every device on the screen is a real device within radio range of you. The scanner uses your computer's own Bluetooth adapter. There are no simulated devices, no scripted encounters and no generated crowds. Walk down a street, through a store or into the woods and the list changes with you.

- **Passive only.** It listens. It never connects to, pairs with or sends anything to the devices it finds.
- **Local only.** Your scans and your profile stay in files on your own machine.
- **Honest about its guesses.** What a device is comes from its name, vendor ID and services. ALERT and POSSIBLE flags are educated guesses, not proof, and distances are rough estimates from signal strength.

## Features

### Scanning

- Layered identification that files devices into categories such as phones, wearables, trackers and smart home. Categories, vendors and rules live in an editable JSON config, so you never need to edit the script.
- Security-relevant gear such as body cameras, license-plate readers, police and fleet radios and drones is flagged **ALERT** (strong match) or **POSSIBLE** (weaker evidence). Trail cameras, hunting devices and other things found in the woods have their own categories.
- Live signal strength in dBm with a signal meter, an estimated distance in feet, and an arrow for closer, steady or moving away.
- **Ghost linking.** Many phones change their Bluetooth address every few minutes. Signal OPS links the changes back to one device, so you are not counted as meeting a new stranger each time.
- **Follower detection** warns you when a tracker keeps showing up around you.
- **Hunt mode** lets you pick any device and track it down with a hot and cold locator and a Geiger-counter click that gets faster and louder as you get closer.
- **Known devices.** Give devices permanent names, and ignore them by address or by advertised name.
- Optional classic Bluetooth (BR/EDR) discovery on Linux.

### Views

Twelve views plus one per category, switched with a single key:

Standard Grid, Top 5 Categories, Compact List, Tactical / Alert Focus, Security Watch, Proximity (closest first), Radar Sweep, New Arrivals, Statistics, MAC Rotation (ghosts), Known & Named Devices, and Sensors (decoded readings).

Layouts are dense so that as many devices as possible fit on a small screen without scrolling. Shortcuts stay visible on screen.

### The top bar

Your level and XP bar, scan time, devices seen, devices in range now, tactical devices in range, clock, battery time left, CPU temperature, a heartbeat trace and the Bluetooth adapter in use.

### The game

- **XP and levels:** 100 levels, with ranks from Static to Legend.
- **Quests:** a pool of 98 quest types, with 10 new daily quests.
- **Bounties:** 44 bounties that watch for specific kinds of devices.
- **Achievements:** 124 lifetime achievements.
- **Titles:** 68 titles you can unlock and equip.
- **Missions:** timed challenges such as "find 5 different vendors in 3 minutes".
- **Intel Coins:** a currency earned from quests, bounties, achievements, level-ups, streaks, hunts and scan time. Spend it in the Coin Exchange on hacker themes (Matrix, Amber CRT, Cyber Ice, Synthwave and more), neon mode and glitch effects. ALERT red stays red in every theme.
- **Daily hooks:** Daily Surge bonus XP, Streak Shields that cover a missed day, a streak coin ladder, Daily Caches, Weekly Ops with a Weekly Chest, and a Welcome Back bonus.

All game content is defined in `lookout_game.json`. You can edit it while the scanner runs and it reloads itself within about 5 seconds. Check your edits with `python3 scanner.py --check-game`.

### Presentation

- A boot sequence, full-screen celebrations for level-ups, quests and unlocks, and optional CRT scanlines. All of it can be switched off.
- Sound effects for new devices, alerts, unlocks and the hunt-mode Geiger click.
- An HTML session report written when you quit, plus a recap screen.

## Where it runs

| Device | Status |
| --- | --- |
| **Steam Deck** (OLED and LCD) | Tested. The reference device. |
| Other Linux handhelds such as the ROG Ally and Legion Go running SteamOS, Bazzite or another Linux | Should work great. Same BlueZ Bluetooth stack and a similar screen. |
| Linux laptops and mini PCs | Should work great. |
| Raspberry Pi 4 or 5 with a screen and keyboard | Should work well. |
| Windows and macOS | Basic scanning may work through the Bleak library. Adapter selection, classic Bluetooth and the CPU temperature readout are Linux-only. |

Only the Steam Deck is tested by the developer.

Signal OPS is keyboard-driven. On a Steam Deck, use the on-screen keyboard or a Steam Input layout that maps buttons to keys. There is no built-in controller layout yet.

## Requirements

- A computer with Bluetooth Low Energy support. On Linux this means BlueZ, which the Steam Deck already has.
- Python 3.
- The Python libraries `bleak` and `rich`.
- A terminal window, such as Konsole on the Steam Deck.

Optional:

- `bluetooth-numbers` for the full Bluetooth SIG company list.
- Sound files next to the script (`.wav`, `.mp3`, `.ogg` or `.flac`) and a sound player on your system such as `paplay`, `aplay`, `ffplay` or `mpg123`.

## Install on a Steam Deck

1. Switch to **Desktop Mode** and open **Konsole**.
2. Download this project into a folder, for example `~/lookout`. Use the green **Code** button on this page and choose **Download ZIP**, or clone it with git:

   ```bash
   git clone https://github.com/tonyispht/signalopsirl.git ~/lookout
   ```

3. Create a Python environment and install the libraries:

   ```bash
   python3 -m venv ~/lookout/venv
   source ~/lookout/venv/bin/activate
   pip install bleak rich bluetooth-numbers
   ```

4. Download the device databases once (this needs internet):

   ```bash
   cd ~/lookout
   python3 scanner.py --update-db
   ```

5. Start scanning. The Steam Deck's built-in Bluetooth is `hci0`:

   ```bash
   python3 scanner.py --adapter hci0
   ```

The default adapter is `hci1`. If you see an adapter error, list your adapters with `hciconfig` and pass the right one with `--adapter`.

Next time you only need:

```bash
cd ~/lookout
source venv/bin/activate
python3 scanner.py --adapter hci0
```

## Install on other Linux machines

The steps are the same. Install Python 3, create a virtual environment, install the libraries, run `--update-db` once, then start the scanner. Make sure Bluetooth is turned on and pick your adapter with `--adapter` if it is not `hci1`.

## Controls

Press `h` in the app for the full list and `b` to reopen the built-in guide, which also opens by itself on your first launch.

| Key | Action |
| --- | --- |
| `v` or `→` | Next view |
| `V` or `←` | Previous view |
| `w` | Choose a view from a list |
| `c` or `Enter` | Open the device inspector |
| `p` | Player profile |
| `e` | Coin Exchange |
| `y` | Missions |
| `m` | Mute or unmute sounds |
| `z` | Toggle effects and motion |
| `o` | Toggle CRT scanlines |
| `k` | Toggle classic Bluetooth discovery (Linux) |
| `$` | Support the developer |
| `h` | Help and key list |
| `b` | Guide |
| `q` or `Esc` | Quit |

## Command-line options

| Option | What it does |
| --- | --- |
| `--adapter HCIn` | Choose the Bluetooth adapter, for example `hci0` |
| `--view NAME` | Start in a view: `grid`, `top5`, `compact`, `tactical`, `security`, `proximity`, `radar`, `arrivals`, `stats`, `ghosts`, `known`, `sensors` or `cat:<category>` |
| `--update-db` | Download the IEEE OUI and Bluetooth SIG databases, then exit |
| `--min-rssi DBM` | Hide devices weaker than this signal |
| `--classic` | Also discover classic Bluetooth devices (Linux) |
| `--ignore-name PATTERN` | Ignore devices whose name matches |
| `--no-boot` | Skip the boot sequence for this run |
| `--no-fx` | Turn off celebrations and animations for this run |
| `--no-outro` | Skip the recap screen when you quit |
| `--no-report` | Do not write the end-of-session HTML report |
| `--report-dir DIR` | Folder for session reports (default `session_logs`) |
| `--player NAME` | Set your player name |
| `--no-game` | Turn off XP, quests and the profile |
| `--check-game` | Validate `lookout_game.json` and list usable metrics |
| `--check-config` | Validate `scanner_config.json` and print a summary |
| `--tutorial` | Open the guide at startup |
| `--test-fx`, `--test-outro` | Preview the effects or the recap screen |

Run `python3 scanner.py --help` for the complete list.

## Files

| File | Purpose |
| --- | --- |
| `scanner.py` | The program |
| `scanner_config.json` | Categories, vendors and device rules |
| `lookout_game.json` | Quests, bounties, achievements, titles, shop, missions and tuning |
| `lookout_settings.json` | Your settings (created on first run) |
| `lookout_profile.json` | Your progress (created on first run) |
| `lookout_known.json` | Devices you have named or ignored |
| `session_logs/` | HTML reports from your sessions |

Your profile, settings, known devices and session logs stay on your machine. Do not commit them if you fork the project.

## Troubleshooting

- **Adapter error or nothing found:** check that Bluetooth is on, list adapters with `hciconfig`, and pass the right one with `--adapter`.
- **Missing library:** activate your environment with `source ~/lookout/venv/bin/activate` and run the `pip install` line again.
- **No sound:** sound files are optional. Put them next to the script, and make sure a player such as `paplay` is installed. Press `m` to check you are not muted.
- **Too many unknown devices:** run `python3 scanner.py --update-db`, then add rules to `scanner_config.json` and check them with `--check-config`.
- **Screen looks cramped:** make your terminal window larger or try the Compact List view.

## Privacy and responsible use

Signal OPS only receives advertisements that devices already broadcast to everyone nearby, and it does not connect to anything. Even so, be considerate. Do not use it to track or harass individuals, and follow the laws where you live. Flags such as ALERT are guesses from public identifiers and can be wrong.

## Support the project

Signal OPS is free and open source, and every safety feature stays free for everyone. It is developed and maintained by just one person. If you enjoy it and want to help me keep building it, you can donate any amount:

**https://www.paypal.com/ncp/payment/9Z8GWNZFJLK7G**

Donating is optional. Supporters get a sparkling player name and a gold SUPPORTER badge in the game.

## License

See the `LICENSE` file in this repository.
