### Sweep.py
`sweep.py` is yet another command line fuzzy finder (fzf analog)

**NOTE**: that this project in maintanence mode, I've switched to rust based implementation [sweep-rs](https://github.com/aslpavel/sweep-rs) which looks and works very simplarly to this one so check it out. 
### Features
  - single source file
  - no dependencies apart from python
  - true/256 color support
  - beautifull defaults
  - easy to specify custom theme colors

### Installation
Just copy `sweep.py` to your `PATH`

### Bash history lookup
Put this in your `.bashrc` file
```bash
__sweep_history__() (
  local line
  shopt -u nocaseglob nocasematch
  line=$(
    HISTTIMEFORMAT= history |
    sweep.py --reversed --nth=2.. --prompt='HISTORY' |
    command grep '^ *[0-9]') &&
    if [[ $- =~ H ]]; then
      sed 's/^ *\([0-9]*\)\** .*/!\1/' <<< "$line"
    else
      sed 's/^ *\([0-9]*\)\** *//' <<< "$line"
    fi
)

bind '"\C-r": " \C-e\C-u\C-y\ey\C-u`__sweep_history__`\e\C-e\er\e^"'
```

### Demo
Dark/Light themes, 100000 words lookup:
![demo](/demo/demo.gif "demo")
