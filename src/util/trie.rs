/*!
A bare-bones `const` compatible trie.

This is useful for parsing one of a small set of statically known strings.

See the [`Trie`] type for more details.
*/

/// The type used to encode the node IDs.
///
/// This should be as small as possible. Making it bigger increases the size of
/// a trie node, which can have a big impact on the total size of the trie. If
/// the type is too small for a given set of needles, then construction will
/// fail.
type TrieNodeId = u8;

/// A trie that can be used in a `const` context.
///
/// This trie can be constructed from a statically known set of needles. Once
/// constructed, a trie can be used to perform an anchored search on a haystack
/// for one of the needles given. Each needle may be associated with a value.
///
/// The main complexity of this implementation resides in making it work in
/// a `const` context. In Rust, at time of writing (Rust ~1.81 with a 1.70
/// MSRV), `const` is abstraction busting. Rust 1.83 will support mutable
/// borrows, which will, I believe, simplify the code below quite a bit. The
/// other complexity in this implementation is trying to use as little space
/// as possible while retaining fast performance characteristics.
///
/// At time of writing, a trie containing all 56 unit designators for the
/// "friendly" duration format occupies 2,232 bytes. Given that the input
/// data is 312 bytes (the sum of all the lengths of the needles plus one byte
/// per needle for its associated `Unit` value), this represents a 7x increase
/// in memory usage. This sounds bad, but could be a lot worse. For example, if
/// we used something bigger than `u8` for the trie node identifiers, it would
/// be substantially worse.
///
/// The main way to make this data structure smaller would be to switch from
/// the dense node representation that it currently uses to a sparse
/// representation. In the dense form, transition lookups are a couple of
/// memory loads, since every node has the same number of transitions defined
/// in memory. In the sparse form, we would omit all dead transitions
/// entirely. The downside is that transition lookups would require a binary
/// or linear scan, thus hurting lookup performance.
///
/// Overall, using 2KB seems worth it here, but it would be nice to be smaller.
///
/// # Motivation
///
/// The main motivation for this data structure is for matching one of a number
/// of possible literal strings. If all strings that you need to match are the
/// same length, then it probably makes sense to use a simple `match` statement.
/// But if they are variable length, this approach can come in handy.
///
/// # Searching
///
/// The `find` routine performs an anchored search that matches the longest
/// possible needle in the trie. So for example, if `quux` is a needle and
/// `quuxz` is the haystack, then `quux` will match with `z` unmatched. Notice
/// how this doesn't require one to split the parsed input beforehand. It just
/// matches what is possible.
///
/// If you could split on the parsed input instead, then it's conceivable you
/// don't need a trie data structure at all. Just do the split and then use a
/// `match` statement to look for the matching string. It will even work for
/// variable length needles. This does require visiting the bytes twice, and
/// probably also depends on how well the compiler optimizes a large `match`
/// statement.
///
/// # Case insensitivity
///
/// If you need full blown Unicode case insensitive matching, then this
/// technique is probably too simplistic. It would probably make more sense to
/// just lowercase everything if possible.
///
/// For ASCII-only case insensitive matching, it is possible to just add the
/// extra transitions when constructing the trie. But you also have to be
/// careful to tweak alphabet construction too. And there-in lies the rub:
/// it makes the alphabet bigger which makes the trie bigger. So, like the
/// Unicode case, it might just make sense to use lowercase needles and then
/// write a new `find_lowercase` routine that lowercases each byte it sees. For
/// ASCII, this is very cheap.
///
/// # Alternatives
///
/// Another way of tackling this problem is to generate Rust (or Assembly) code
/// that embeds the trie structure within it. I have an affinity for table
/// based automatons, so I chose this approach. I do idly wonder if codegen'ing
/// Rust code would be better. It would be cool to experiment with this via
/// regex-automata. regex-automata doesn't provide Rust codegen facilities,
/// but we could build a minimal DFA and then, I believe, generate Rust code
/// from that. But now we're starting to get into re2c/Ragel-style stuff.
///
/// # Type parameters
///
/// There are three type parameters:
///
/// * `NODE_CAPACITY` is a constant number corresponding to the total number of
/// nodes in the trie. Ideally this would be an implementation detail, but
/// remember, `const` is abstraction busting. This should ideally be set as
/// small as possible, otherwise, the `Trie` will be bigger than it needs to
/// be. To determine the minimal number, use trial and error.
/// * `ALPHABET_LEN` is a constant number corresponding to the total number of
/// distinct byte values across all needles given to `Trie::new`. This should
/// be computed automatically by calling `TrieNeedles::new` and then
/// `TrieNeedles::alphabet_len`. This can be done, of course, in a `const`
/// context.
/// * `V` corresponds to the type of the value associated with each needle.
/// Because of `const` limitations, it cannot contain borrows and must be
/// `Copy`.
///
/// # Example
///
/// Typical usage looks like this:
///
/// ```ignore
/// type FooTrie = Trie<11, { FOO_NEEDLES.alphabet_len() }, char>;
/// static FOO_TRIE: &'static FooTrie = &Trie::new(&FOO_NEEDLES);
/// const FOO_NEEDLES: TrieNeedles<char> =
///     TrieNeedles::new(&[("foo", 'a'), ("bar", 'b'), ("quux", 'c')]);
///
/// assert_eq!(FOO_TRIE.find(b""), None);
/// assert_eq!(FOO_TRIE.find(b"fo"), None);
/// assert_eq!(FOO_TRIE.find(b"foo"), Some(('a', 3)));
/// assert_eq!(FOO_TRIE.find(b"fooquux"), Some(('a', 3)));
/// ```
///
/// This setup ensures there is only one `FooTrie` in the program.
#[derive(Clone, Debug)]
pub(crate) struct Trie<
    const NODE_CAPACITY: usize,
    const ALPHABET_LEN: usize,
    V: 'static,
> {
    nodes: [TrieNode<ALPHABET_LEN, V>; NODE_CAPACITY],
    /// The number of nodes in this trie.
    len: usize,
    /// The alphabet of the trie.
    alphabet: TrieAlphabet,
}

impl<
        const NODE_CAPACITY: usize,
        const ALPHABET_LEN: usize,
        V: Copy + 'static,
    > Trie<NODE_CAPACITY, ALPHABET_LEN, V>
{
    /// The ID of the root node for this trie.
    const ROOT_ID: TrieNodeId = 0;
    /// The ID of the failure or "dead" node of this trie.
    ///
    /// This ID is a sentinel. It doesn't actually refer to a node that
    /// it exists. When a search using this trie enters this node, then the
    /// search must stop because it can never leave this node. That is,
    /// logically, this node is a node where every transition is a transition
    /// back to itself.
    const FAIL_ID: TrieNodeId = TrieNodeId::MAX;

    /// Create a new trie from the given set of needles.
    pub(crate) const fn new(
        needles: &TrieNeedles<V>,
    ) -> Trie<NODE_CAPACITY, ALPHABET_LEN, V> {
        let mut trie = Trie {
            nodes: [TrieNode {
                transitions: [Self::FAIL_ID; ALPHABET_LEN],
                value: None,
            }; NODE_CAPACITY],
            len: 1,
            alphabet: needles.alphabet(),
        };
        // The alphabet length inferred by the caller need to match the actual
        // alphabet length of the trie.
        assert!(trie.alphabet.len() == ALPHABET_LEN);
        // It must be impossible to construct a node ID that corresponds to the
        // failure node.
        assert!(NODE_CAPACITY <= Self::FAIL_ID as usize);

        let mut i = 0;
        while i < needles.map.len() {
            let (needle, unit) = needles.map[i];
            i += 1;

            let mut node_id = Self::ROOT_ID;
            let mut k = 0;
            while k < needle.len() {
                let byte = needle.as_bytes()[k];
                k += 1;

                // MSRV(1.83): Use `trie.next` here instead of manually
                // inlining it. At present, it's forbidden because rustc thinks
                // it could result in a borrow containing interior mutability,
                // which I think is rooted in `V` being generic.
                let mut next_id = trie.nodes[node_id as usize].transitions
                    [trie.alphabet.equiv_id(byte) as usize];
                if next_id == Self::FAIL_ID {
                    // If this assertion fails, then the Trie needs more
                    // capacity.
                    assert!(trie.len < NODE_CAPACITY);
                    next_id = trie.len as u8;
                    trie.len += 1;
                }
                let equiv_id = trie.alphabet.equiv_id(byte);
                trie.nodes[node_id as usize].transitions[equiv_id as usize] =
                    next_id;
                node_id = next_id;
            }
            // This assert prevents duplicate needles. That is, every needle
            // must map to one and precisely one value. We could support
            // "overwrite" semantics, but I think it's better to fail loudly
            // here.
            if let Some(_) = trie.nodes[node_id as usize].value {
                panic!("duplicate needle detected");
            }
            trie.nodes[node_id as usize].value = Some(unit);
        }
        trie
    }

    /// Returns the longest possible match for an item in this trie that is
    /// anchored to the beginning of `haystack`.
    ///
    /// This also returns the ending position of the match found. (The starting
    /// position is always zero since this trie only does anchored searches.)
    #[inline(always)]
    pub(crate) const fn find(&self, haystack: &[u8]) -> Option<(V, usize)> {
        let mut node_id = Self::ROOT_ID;
        let mut found = None;
        if let Some(value) = self.nodes[node_id as usize].value {
            found = Some((value, 0));
        }
        let mut i = 0;
        while i < haystack.len() {
            let next_id = self.next(node_id, haystack[i]);
            if next_id == Self::FAIL_ID {
                return found;
            }
            node_id = next_id;
            i += 1;
            if let Some(value) = self.nodes[node_id as usize].value {
                found = Some((value, i));
            }
        }
        found
    }

    /// Returns ID of the next node after transitioning from this node via the
    /// byte given.
    ///
    /// If the transition doesn't exist or if the byte given isn't in this
    /// trie's alphabet, then the ID of the failure node is returned.
    #[inline(always)]
    const fn next(&self, current_id: TrieNodeId, byte: u8) -> TrieNodeId {
        let equiv_id = self.alphabet.equiv_id(byte);
        self.nodes[current_id as usize].transitions[equiv_id as usize]
    }
}

/// A node in a trie.
///
/// It can be a match node or non-matching. Otherwise, it holds the transitions
/// to the next node. It's a leaf node when all of its transitions map to the
/// failure node.
#[derive(Clone, Copy, Debug)]
struct TrieNode<const ALPHABET_LEN: usize, V: 'static> {
    transitions: [TrieNodeId; ALPHABET_LEN],
    /// If this is a match node, then this corresponds to the value associated
    /// with the matching needle.
    value: Option<V>,
}

/// A map from needle to value. Used to construct a `Trie`.
///
/// There must be at most one value for each possible needle (i.e., duplicate
/// needles are not allowed). But there may be multiple needles for any one
/// value.
#[derive(Clone, Copy, Debug)]
pub(crate) struct TrieNeedles<V: 'static> {
    map: &'static [(&'static str, V)],
}

impl<V: Copy + 'static> TrieNeedles<V> {
    /// Returns a set of needles to search for and their corresponding values.
    pub(crate) const fn new(
        map: &'static [(&'static str, V)],
    ) -> TrieNeedles<V> {
        TrieNeedles { map }
    }

    /// Returns the number of elements in the alphabet formed by these needles.
    ///
    /// The alphabet size is determined by the number of distinct bytes
    /// occurring across all needles.
    pub(crate) const fn alphabet_len(&self) -> usize {
        self.alphabet().len()
    }

    /// Returns the alphabet corresponding to this set of needles.
    const fn alphabet(&self) -> TrieAlphabet {
        TrieAlphabet::new(self)
    }
}

/// The alphabet of a trie.
///
/// Naively, the alphabet of a byte based trie is just the 256 distinct
/// values of a `u8`. But we try to make things more compact by shrinking
/// the alphabet to just the set of distinct bytes that occur in the needles
/// used to construct the trie. This is much smaller than 256 or even 26.
/// But, to do this, we need a map from the 256 distinct `u8` values to
/// their corresponding values in the trie alphabet. We call those values
/// "equivalence class identifiers."
///
/// The fundamental invariant of an equivalence class is that it's impossible
/// for any byte in the equivalence class to differentiate between a specific
/// match of a needle with a match of any other needle or non-match.
///
/// The first equivalence class, corresponding to all bytes not in any of the
/// needles, is always `0`. That is, unless there are no such bytes, in which
/// case, equivalence classes map precisely to each singular distinct byte
/// value.
#[derive(Clone)]
struct TrieAlphabet {
    len: u16,
    equiv_classes: [u8; 256],
}

impl TrieAlphabet {
    /// Create a new alphabet from the given needles.
    const fn new<V: Copy>(needles: &TrieNeedles<V>) -> TrieAlphabet {
        let mut equiv_set = [false; 256];
        let mut i = 0;
        while i < needles.map.len() {
            let (needle, _) = needles.map[i];
            i += 1;

            let mut k = 0;
            while k < needle.len() {
                let byte = needle.as_bytes()[k];
                equiv_set[byte as usize] = true;
                k += 1;
            }
        }

        // Count the number of distinct bytes seen in the needles. If we get
        // to 256, then that's the number of equivalence classes since there
        // are no byte values that don't occur in the needles. But if we get
        // N<256, then the number of equivalence classes is N+1, where the +1
        // accounts for the equivalence class containing all byte values that
        // were not present in the needles.
        let mut len = 0;
        let mut i = 0;
        while i < equiv_set.len() {
            if equiv_set[i] {
                len += 1;
            }
            i += 1;
        }
        if len < 256 {
            len += 1;
        }

        let mut equiv_classes = [0x00; 256];
        let mut byte: u16 = 0;
        if len == 256 {
            // In this case, there are 256 distinct bytes present in the
            // needles. So there must be exactly 256 equivalence classes and
            // each class just maps to the corresponding byte value.
            while byte < 256 {
                equiv_classes[byte as usize] = byte as u8;
                byte += 1;
            }
        } else {
            // We start at 1 here since we know there must be at least some
            // bytes that are not in the alphabet, and all of those get
            // implicitly assigned to equivalent class identifier `0`.
            let mut equiv_id: u16 = 1;
            while byte < 256 {
                if equiv_set[byte as usize] {
                    // Correct because we are limited to 256 iterations. We do
                    // start at 1, which means we could get to 256 here (before
                    // incrementing to 257 below), but that would require
                    // 256 distinct bytes. And that case is handled above.
                    assert!(equiv_id < 256);
                    equiv_classes[byte as usize] = equiv_id as u8;
                    equiv_id += 1;
                }
                byte += 1;
            }
        }
        TrieAlphabet { len, equiv_classes }
    }

    /// Returns the number of distinct elements in this alphabet.
    #[inline(always)]
    const fn len(&self) -> usize {
        self.len as usize
    }

    /// Returns the equivalence class identifier for the given byte value.
    ///
    /// THe equivalence class identifier returned is guaranteed to be
    /// greater than or equal to `0` and less than `TrieAlphabet::len`.
    #[inline(always)]
    const fn equiv_id(&self, byte: u8) -> u8 {
        self.equiv_classes[byte as usize]
    }
}

impl core::fmt::Debug for TrieAlphabet {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TrieAlphabet").field("len", &self.len).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty() {
        type EmptyTrie = Trie<1, { EMPTY_NEEDLES.alphabet_len() }, char>;
        static EMPTY_TRIE: &'static EmptyTrie = &Trie::new(&EMPTY_NEEDLES);
        const EMPTY_NEEDLES: TrieNeedles<char> =
            TrieNeedles::new(&[("", 'z')]);

        assert_eq!(EMPTY_TRIE.find(b""), Some(('z', 0)));
    }

    #[test]
    fn fubar() {
        type FooTrie = Trie<11, { FOO_NEEDLES.alphabet_len() }, char>;
        static FOO_TRIE: &'static FooTrie = &Trie::new(&FOO_NEEDLES);
        const FOO_NEEDLES: TrieNeedles<char> =
            TrieNeedles::new(&[("foo", 'a'), ("bar", 'b'), ("quux", 'c')]);

        assert_eq!(FOO_TRIE.find(b""), None);
        assert_eq!(FOO_TRIE.find(b"fo"), None);
        assert_eq!(FOO_TRIE.find(b"foo"), Some(('a', 3)));
        assert_eq!(FOO_TRIE.find(b"fooquux"), Some(('a', 3)));
    }

    #[test]
    fn aaa() {
        type AaaTrie = Trie<11, { AAA_NEEDLES.alphabet_len() }, char>;
        static AAA_TRIE: &'static AaaTrie = &Trie::new(&AAA_NEEDLES);
        const AAA_NEEDLES: TrieNeedles<char> =
            TrieNeedles::new(&[("a", 'a'), ("aa", 'b'), ("aaa", 'c')]);

        assert_eq!(AAA_TRIE.find(b""), None);
        assert_eq!(AAA_TRIE.find(b"a"), Some(('a', 1)));
        assert_eq!(AAA_TRIE.find(b"aa"), Some(('b', 2)));
        assert_eq!(AAA_TRIE.find(b"aaa"), Some(('c', 3)));
        assert_eq!(AAA_TRIE.find(b"aaaa"), Some(('c', 3)));
    }
}
