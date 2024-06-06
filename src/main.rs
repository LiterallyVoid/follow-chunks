use notify::{RecursiveMode, Watcher};
use rangecutter::RangeExt;
use std::{
    collections::{HashMap, HashSet},
    ops::Range,
    path::{Path, PathBuf},
    time::Duration,
};

use clap::Parser;

/// Split files into chunks, and stream new chunks in whenever files are changed.
///
/// A chunk ends wherever an empty line is followed by an unindented line.
///
/// Chunks are deduplicated ignoring leading and trailing whitespace, so that
/// when a new chunk is added to a file the empty lines separating it from the
/// previous chunk will not cause the previous chunk to be considered updated, even
/// though the previous chunk now contains trailing newlines.
#[derive(Parser, Debug, Clone)]
struct Args {
    path: PathBuf,

    #[arg(short, long)]
    include: Vec<String>,

    /// List of globs to exclude.
    #[arg(short, long)]
    exclude: Vec<String>,

    /// How long to wait after a file changes to re-index it, in seconds.
    #[arg(short, long, value_parser=parse_duration, default_value="0")]
    debounce: Duration,

    #[command(flatten)]
    behavior: Behavior,

    /// Instead of writing to standard out, write ``
    #[arg(trailing_var_arg = true)]
    command: Option<Vec<String>>,
}

#[derive(Parser, Debug, Clone)]
struct Behavior {
    // /// Print the first chunk of a file before any changed chunks from that file.
    // #[arg(short='H', long)]
    // header: bool,
    /// The string to start a metadata line with. For example, “// ” would emit metadata inside of a C-style line comment.
    #[arg(short, long)]
    metadata_line_prefix: Option<String>,

    /// The string to end a metadata line with.
    ///
    /// For example, if `metadata_line_prefix` is “/* ” and this is “ */”, metadata will be emitted inside of a C-style multiline comment.
    #[arg(short = 'M', long)]
    metadata_line_suffix: Option<String>,

    #[arg(short = 'E', long)]
    chunk_end_marker: Option<String>,
}

fn parse_duration(arg: &str) -> Result<std::time::Duration, std::num::ParseFloatError> {
    let seconds = arg.parse()?;
    Ok(std::time::Duration::from_secs_f64(seconds))
}

// Returns the range of the first `"\n"` or `"\r\n"` separator in `source`.
fn first_line_separator(source: &str) -> Option<Range<usize>> {
    let newline = source.find('\n')?;

    let end = newline + '\n'.len_utf8();
    let mut start = newline;

    if source[0..newline].ends_with('\r') {
        start -= '\r'.len_utf8();
    }

    Some(start..end)
}

/// Split a string into chunks.
///
/// A new chunk starts wherever an unindented line follows an empty line.
fn chunks(source: &str) -> impl Iterator<Item = &str> {
    let mut range = 0..source.len();

    std::iter::from_fn(move || {
        if range.is_empty() {
            return None;
        }

        let mut was_empty = false;

        let start = range.start;

        while !range.is_empty() {
            let separator =
                first_line_separator(&source[range.clone()]).map(|sep| range.compose(&sep));
            let (line, rest) = match separator {
                Some(sep) => range.clone().cut(&sep),
                None => (range.clone(), range.end..range.end),
            };

            let line_text = &source[line];
            if was_empty && line_text.chars().next().is_some_and(|c| !c.is_whitespace()) {
                break;
            }

            was_empty = line_text.trim().is_empty();

            range = rest;
        }

        Some(&source[start..range.start])
    })
}

#[test]
fn test_chunks() {
    let s = r#"

^def main(
    a,
    b,
):
    return add(a, b)

^def add(a, b):
    return a + b

^# two unindented lines...
# ...in a row

^# Comment
# Another comment, followed by two newlines

"#;

    let split = s.split('^').collect::<Vec<_>>();

    let chunks = chunks(s).collect::<Vec<_>>();

    assert_eq!(
        [
            chunks[0],
            // Remove `^` character
            &chunks[1][1..],
            // Remove `^` character
            &chunks[2][1..],
            // Remove `^` character
            &chunks[3][1..],
            // Remove `^` character
            &chunks[4][1..],
        ][..],
        split
    );
}

#[derive(Default, Debug)]
struct State {
    files: HashMap<PathBuf, HashSet<String>>,
}

/// The hash set contains the trimmed chunks of `source`.
fn ingest<'b>(old_chunks: &HashSet<String>, source: &'b str) -> (HashSet<String>, Vec<&'b str>) {
    let mut set = HashSet::new();
    let mut vec = Vec::new();

    for chunk in chunks(source) {
        let trimmed = chunk.trim();
        set.insert(trimmed.to_owned());

        if old_chunks.contains(trimmed) {
            continue;
        }

        vec.push(chunk);
    }

    (set, vec)
}

impl State {
    fn ingest<'b>(&mut self, path: PathBuf, source: &'b str) -> Vec<&'b str> {
        let entry = self.files.entry(path);

        let empty = HashSet::new();
        let old_chunk_set = match &entry {
            std::collections::hash_map::Entry::Occupied(entry) => entry.get(),
            std::collections::hash_map::Entry::Vacant(_) => &empty,
        };

        let (new_chunk_set, new_chunks) = ingest(old_chunk_set, source);

        match entry {
            std::collections::hash_map::Entry::Occupied(mut entry) => {
                entry.insert(new_chunk_set);
            }
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(new_chunk_set);
            }
        }

        new_chunks
    }
}

#[test]
fn test_state() {
    let mut state = State::default();

    assert_eq!(
        state.ingest("a.txt".into(), "foo\n\n\nbar"),
        ["foo\n\n\n", "bar",],
    );
    assert_eq!(
        state.ingest("a.txt".into(), "foo\n\n\nbar\nbaz\n\n"),
        ["bar\nbaz\n\n",],
    );
    assert_eq!(
        state.ingest("a.txt".into(), "foo\n\n\nbar\n\nbaz\n\n"),
        ["bar\n\n", "baz\n\n",],
    );
    assert_eq!(
        state.ingest("b.txt".into(), "foo\n\n\nbar\nbaz\n\n"),
        ["foo\n\n\n", "bar\nbaz\n\n",],
    );
}

fn walk_directory(
    exclude: &[glob::Pattern],
    behavior: &Behavior,
    state: &mut State,
    path: &Path,
) -> std::io::Result<()> {
    for pattern in exclude {
        if pattern.matches(&path.to_string_lossy()) {
            return Ok(());
        }
    }

    if let Ok(contents) = std::fs::read_to_string(path) {
        let chunks = state.ingest(path.to_owned(), &contents);

        for chunk in chunks {
            if behavior.metadata_line_prefix.is_some() || behavior.metadata_line_suffix.is_some() {
                #[derive(serde::Serialize, serde::Deserialize)]
                struct Metadata<'a> {
                    #[serde(bound(deserialize = "'de: 'a"))]
                    path: &'a Path,
                }

                let metadata = Metadata { path };

                println!(
                    "{}{}{}",
                    behavior
                        .metadata_line_prefix
                        .as_ref()
                        .unwrap_or(&String::new()),
                    serde_json::to_string(&metadata).unwrap(),
                    behavior
                        .metadata_line_suffix
                        .as_ref()
                        .unwrap_or(&String::new()),
                );
            }
            print!("{chunk}");

            if let Some(chunk_end_marker) = &behavior.chunk_end_marker {
                println!("{chunk_end_marker}");
            }
        }

        return Ok(());
    }

    let Ok(entries) = std::fs::read_dir(path) else {
        return Ok(());
    };

    for entry in entries {
        let entry = entry?;
        let subpath = &entry.path();

        walk_directory(exclude, behavior, state, subpath)?;
    }

    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    let mut state = State::default();

    let exclude = args
        .exclude
        .iter()
        .map(|s| glob::Pattern::new(s))
        .collect::<Result<Vec<_>, _>>()?;

    // @TODO: There's a race condition here, where files can change between the initial walk and the watcher starting up.
    walk_directory(&exclude, &args.behavior, &mut state, &args.path)?;

    let args2 = args.clone();

    let mut debouncer = notify_debouncer_full::new_debouncer(
        args2.debounce,
        None,
        move |res: notify_debouncer_full::DebounceEventResult| match res {
            Ok(events) => {
                for event in events {
                    for path in event.paths.iter() {
                        if let Err(e) = walk_directory(&exclude, &args.behavior, &mut state, path) {
                            eprintln!("walk error: {:?}", e);
                        }
                    }
                }
            }
            Err(e) => eprintln!("watch error: {:?}", e),
        },
    )?;

    debouncer
        .watcher()
        .watch(&args2.path, RecursiveMode::Recursive)?;
    debouncer
        .cache()
        .add_root(&args2.path, RecursiveMode::Recursive);

    loop {
        std::thread::yield_now();
    }
}
