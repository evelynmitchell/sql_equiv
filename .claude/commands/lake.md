# /lake

Run common Lake commands.

## Usage

- `/lake build` - Build the project (same as `/build`)
- `/lake update` - Update dependencies
- `/lake exe <name>` - Run an executable
- `/lake env` - Show Lake environment info

## Instructions

Provide shortcuts for common Lake operations.

### Available Commands

| Command | Description |
|---------|-------------|
| `lake build` | Build all targets |
| `lake build <target>` | Build specific target |
| `lake exe <name>` | Run executable |
| `lake update` | Update dependencies |
| `lake resolve-deps` | Resolve without updating |
| `lake env printenv` | Show environment |

### Important

**Never run `lake clean`** unless explicitly requested and confirmed. It wipes the entire build cache and forces a full recompile (~20+ minutes).

### Example

```bash
source ~/.elan/env && lake build
```

All Lake commands should be prefixed with `source ~/.elan/env &&` to ensure the Lean toolchain is available.
