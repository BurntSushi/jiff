mod generate;

const USAGE: &'static str = "\
A tool for interacting with the Jiff datetime library on the command line.

USAGE:
    jiff-cli <command> ...

COMMANDS:
    generate      Various generation tasks, e.g., data for jiff-tzdb
";

pub fn run(p: &mut lexopt::Parser) -> anyhow::Result<()> {
    let cmd = crate::args::next_as_command(USAGE, p)?;
    match &*cmd {
        "generate" => generate::run(p),
        unk => anyhow::bail!("unrecognized command '{}'", unk),
    }
}
