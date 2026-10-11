# Formal-Engine (Open Research)

![Rust](https://img.shields.io/badge/Language-Rust-orange.svg)
![Z3](https://img.shields.io/badge/Engine-Microsoft_Z3-blue.svg)
![License](https://img.shields.io/badge/License-GPLv3-blue.svg)

Formal-Engine contains Rust research demos of bounded SMT state solving and synthetic cryptographic constraints. The examples use generated inputs. They do not establish practical attacks against deployed AES or ML-KEM implementations or prove the correctness of arbitrary software.

## Interactive demo

The Rust example serves its own local web UI with `std::net::TcpListener`. Building it requires the crates in [Cargo.toml](Cargo.toml), including `z3`, and a system Z3 installation with headers. No separate web server or front-end package installation is needed.

### Visual demos

#### 1. SMT pipeline

![Full Pipeline Sequence](assets/demo_full_pipeline.png)

*Figure 1: A bounded state-machine inversion example followed by a guard check for the generated example.*

#### 2. Cryptographic constraint examples

![Encryption Hub Results](assets/demo_encryption_hub.png)

*Figure 2: Synthetic AES S-box constraints for a 32-bit round-key component and a bounded lattice-coefficient example. These are demonstrations, not attacks on complete cryptographic implementations.*

### Quick start (macOS / Linux)

1. Install a Rust toolchain and Microsoft Z3 with development headers. For example:

   ```sh
   # macOS with Homebrew
   brew install z3
   export Z3_SYS_Z3_HEADER="$(brew --prefix z3)/include/z3.h"
   export LIBRARY_PATH="$(brew --prefix z3)/lib"

   # Ubuntu/Debian
   sudo apt-get install libz3-dev
   ```

2. From the repository root, build and run the interactive example:

   ```sh
   cargo run --example dynamic_grail_demo
   ```

Open `http://127.0.0.1:8080` in a browser. The demo lets you explore a bounded state-machine example and two synthetic cryptographic constraint examples.

## Security and disclosure

See the [security policy](SECURITY.md) for disclosure guidance.
