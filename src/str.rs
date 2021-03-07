use std::borrow::{Borrow, Cow};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::ops::Deref;
use std::panic::{RefUnwindSafe, UnwindSafe};
use std::ptr::NonNull;
use std::slice;
use std::str;

/// A more efficient `Cow<'a, str>`.
pub struct Str<'a> {
    // `NonNull` allows the null-pointer optimization, reducing the size of `Option<Self>` by a `usize`.
    ptr: NonNull<u8>,
    // Using a `u32` for len and cap reduces the size by a `usize`. Combining them into one field means Rust treats it
    // as a "small struct", since it has two word-sized fields of `usize`, meaning it applies some function calling
    // optimizations too. See http://troubles.md/abusing-rustc.
    len_cap: usize,
    _a: &'a PhantomData<()>,
}

const MASK_LO: usize = u32::MAX as usize;
const MASK_HI: usize = !MASK_LO;

impl<'a> Str<'a> {
    /// Creates a new empty `Str`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use lowline::Str;
    ///
    /// let s = Str::new();
    /// assert_eq!(s, "");
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self::from_str("")
    }

    /// Creates a new `Str` from the given string slice.
    #[inline]
    pub const fn from_str(s: &'a str) -> Str<'a> {
        Str {
            // Safety: We check the null-pointer optimization holds for `&str` in tests.
            // Safety: When capacity is zero we only dereference this ptr as `*const`.
            ptr: unsafe { NonNull::new_unchecked(s.as_ptr() as *mut u8) },
            // This will silently truncate the str, which is safe for borrows, and we can't panic in a `const fn`.
            len_cap: if s.len() > MASK_LO { MASK_LO } else { s.len() },
            _a: &PhantomData,
        }
    }

    /// Returns the length of `self`.
    ///
    /// This length is in bytes, not [`char`]s or graphemes. In other words, it may not be what a human considers the
    /// length of the string.
    ///
    /// [`char`]: prim@char
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use lowline::Str;
    ///
    /// let len = Str::from("moo").len();
    /// assert_eq!(len, 3);
    /// ```
    #[inline]
    pub const fn len(&self) -> usize {
        self.len_cap & MASK_LO
    }

    /// Returns `true` if `self` has a length of zero bytes.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use lowline::Str;
    ///
    /// let s = Str::from("");
    /// assert!(s.is_empty());
    ///
    /// let s = Str::from("moo");
    /// assert!(!s.is_empty());
    /// ```
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// If the `str` is stored on the heap, returns the capacity in bytes. If the `str` is borred, returns `0`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use lowline::Str;
    ///
    /// let s = Str::from("moo");
    /// assert_eq!(s.capacity(), 0);
    ///
    /// let s = Str::from(String::from("moo"));
    /// assert_eq!(s.capacity(), 3);
    /// ```
    #[inline]
    pub const fn capacity(&self) -> usize {
        (self.len_cap & MASK_HI) >> 32
    }

    /// Returns `true` if the data is borrowed.
    ///
    /// # Examples.
    ///
    /// Basic usage:
    ///
    /// ```
    /// use lowline::Str;
    ///
    /// let s = Str::from("moo");
    /// assert!(s.is_borrowed());
    ///
    /// let s = Str::from(String::from("moo"));
    /// assert!(!s.is_borrowed());
    /// ```
    #[inline]
    pub const fn is_borrowed(&self) -> bool {
        self.capacity() == 0
    }

    /// Returns `true` if the data is owned.
    ///
    /// # Examples.
    ///
    /// Basic usage:
    ///
    /// ```
    /// use lowline::Str;
    ///
    /// let s = Str::from("moo");
    /// assert!(!s.is_owned());
    ///
    /// let s = Str::from(String::from("moo"));
    /// assert!(s.is_owned());
    /// ```
    #[inline]
    pub const fn is_owned(&self) -> bool {
        self.capacity() != 0
    }

    /// Extracts a string slice containing the entire `str`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use lowline::Str;
    ///
    /// let s = Str::from("moo");
    ///
    /// assert_eq!(s.as_str(), "moo");
    /// ```
    #[inline]
    pub fn as_str(&'a self) -> &'a str {
        // Safety: Since the returned slice cannot outlive `'a`, this is safe.
        unsafe { self.as_str_unchecked() }
    }

    /// Extracts a string slice containing the entire `str` without enforcing lifetime checks.
    ///
    /// # Safety
    ///
    /// The caller must ensure the returned reference does not outlive `&self`. Otherwise the owner of the data can be
    /// dropped and cause a dangling pointer.
    #[inline]
    unsafe fn as_str_unchecked(&self) -> &'a str {
        // Safety: This is safe so long as `ptr` and `len` refer to a valid utf-8 slice.
        str::from_utf8_unchecked(slice::from_raw_parts(self.ptr.as_ptr(), self.len()))
    }

    /// Extracts the owned `String`.
    ///
    /// Clones the `str` if it is not already owned.
    ///
    /// # Examples
    ///
    /// Calling `into_owned` on a borrowed `Str` clones the underlying data.
    ///
    /// ```
    /// use lowline::Str;
    ///
    /// let s = Str::from("moo");
    ///
    /// assert_eq!(s.into_owned(), String::from("moo"))
    /// ```
    ///
    /// Calling `into_owned` on an owned `Str` is a no-op:
    ///
    /// ```
    /// use lowline::Str;
    ///
    /// let s = Str::from(String::from("moo"));
    ///
    /// assert_eq!(s.into_owned(), String::from("moo"));
    /// ```
    #[inline]
    pub fn into_owned(self) -> String {
        if self.is_borrowed() {
            self.as_str().to_owned()
        } else {
            self.unwrap_owned()
        }
    }

    /// Extracts the owned `String`.
    ///
    /// # Panics
    ///
    /// In debug this panics if the data is not owned. In release this check is removed, so this API is private.
    #[inline]
    fn unwrap_owned(self) -> String {
        // Safety: We forget `self`, avoiding double-free.
        // Safety: The `debug_asset!` in `as_owned` prevents creating a `String` from non-heap data.
        unsafe { ManuallyDrop::new(self).as_owned() }
    }

    /// **Safety:** This function is unsafe because either `self` or the returned `String` must be forgotten to avoid a
    /// double-free.
    ///

    /// Extracts the owned string without consuming `self`.
    ///
    /// # Panics
    ///
    /// In debug this panics if the data is not owned. In release this check is removed, so this API is private.
    ///
    /// # Safety
    ///
    /// Either `self` or the returned `String` must be forgotten using `mem::forget` or `ManuallyDrop` to avoid a
    /// double-free.
    #[inline]
    unsafe fn as_owned(&mut self) -> String {
        // Safety: We check `is_owned` to ensure this refers to memory on the heap. Otherwise, `String::drop` will try
        // to free stack or static memory.
        // Safety: This is otherwise safe so long as `ptr`, `len` and `capacity` refer to a valid utf8 slice on the heap.
        debug_assert!(self.is_owned());
        String::from_raw_parts(self.ptr.as_ptr(), self.len(), self.capacity())
    }
}

impl<'a> AsRef<str> for Str<'a> {
    #[inline]
    fn as_ref(&self) -> &str {
        self.deref()
    }
}

impl<'a> Borrow<str> for Str<'a> {
    #[inline]
    fn borrow(&self) -> &str {
        self.deref()
    }
}

impl<'a> Clone for Str<'a> {
    #[inline]
    fn clone(&self) -> Self {
        if self.is_borrowed() {
            // Safety: Since the returned slice cannot outlive `'a`, this is safe.
            unsafe { self.as_str_unchecked().into() }
        } else {
            self.as_str().to_owned().into()
        }
    }
}

impl<'a> fmt::Debug for Str<'a> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl<'a> Default for Str<'a> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> Deref for Str<'a> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<'a> Drop for Str<'a> {
    #[inline]
    fn drop(&mut self) {
        if self.is_owned() {
            // Safety: `self` is being dropped, so the string will only be freed once.
            unsafe { self.as_owned(); }
        }
    }
}

impl<'a> fmt::Display for Str<'a> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl<'a> Eq for Str<'a> {}

impl<'a> From<&'a str> for Str<'a> {
    #[inline]
    fn from(s: &'a str) -> Self {
        Self::from_str(s)
    }
}

impl<'a> From<String> for Str<'a> {
    #[inline]
    fn from(s: String) -> Self {
        let mut s = ManuallyDrop::new(s);
        // Since we silently truncate in `from_str`, we do the same here.
        if s.capacity() > MASK_LO {
            s.truncate(MASK_LO);
            s.shrink_to_fit();
            debug_assert!(s.capacity() <= MASK_LO);
        }
        Self {
            // Safety: We check the null-pointer optimization holds for `String` in tests.
            // Safety: We avoid a double-free using `ManuallyDrop`.
            ptr: unsafe { NonNull::new_unchecked(s.as_mut_ptr()) },
            len_cap: (s.capacity() << 32) | s.len(),
            _a: &PhantomData,
        }
    }
}

impl<'a> From<Cow<'a, str>> for Str<'a> {
    #[inline]
    fn from(s: Cow<'a, str>) -> Self {
        match s {
            Cow::Borrowed(s) => s.into(),
            Cow::Owned(s) => s.into(),
        }
    }
}

impl<'a> From<Str<'a>> for String {
    #[inline]
    fn from(s: Str<'a>) -> Self {
        if s.is_borrowed() {
            s.as_str().to_owned()
        } else {
            s.unwrap_owned()
        }
    }
}

impl<'a> From<Str<'a>> for Cow<'a, str> {
    #[inline]
    fn from(s: Str<'a>) -> Self {
        if s.is_borrowed() {
            // Safety: Since the returned slice cannot outlive `'a`, this is safe.
            Cow::Borrowed(unsafe { s.as_str_unchecked() })
        } else {
            Cow::Owned(s.unwrap_owned())
        }
    }
}

impl<'a> Hash for Str<'a> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

impl<'a> Ord for Str<'a> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl<'a, S: Borrow<str>> PartialEq<S> for Str<'a> {
    #[inline]
    fn eq(&self, other: &S) -> bool {
        self.as_str() == other.borrow()
    }
}

impl<'a, S: Borrow<str>> PartialOrd<S> for Str<'a> {
    #[inline]
    fn partial_cmp(&self, other: &S) -> Option<Ordering> {
        self.as_str().partial_cmp(other.borrow())
    }
}

impl<'a> RefUnwindSafe for Str<'a> {}
unsafe impl<'a> Send for Str<'a> {}
unsafe impl<'a> Sync for Str<'a> {}
impl<'a> Unpin for Str<'a> {}
impl<'a> UnwindSafe for Str<'a> {}

#[cfg(test)]
mod test {
    use std::mem::size_of;
    use crate::test::alloc_count;
    use super::*;

    #[test]
    fn test_null_pointer_opt() {
        // If these types has null-pointer optimization, we know their returned pointers are safe to convert to
        // `NonNull` unchecked.
        debug_assert_eq!(size_of::<String>(), size_of::<Option<String>>());
        debug_assert_eq!(size_of::<&str>(), size_of::<Option<&str>>());
        // Make sure our own null-pointer optimization works.
        assert_eq!(size_of::<Str>(), size_of::<Option<Str>>());
    }

    fn assert_ptr<'a, S: Into<Str<'a>> + Deref<Target=str>>(
        s: S, expected_value: &'static str, expected_capacity: usize,
        is_borrowed: bool, is_borrowed_on_heap: bool,
    ) {
        let start_alloc_count = alloc_count();
        let ptr = s.as_ptr();
        let s = s.into();
        assert_eq!(s, expected_value);
        assert_eq!(s.capacity(), expected_capacity);
        assert_eq!(s.as_ptr(), ptr);  // To `Str` always preserves pointer.
        assert_eq!(s.is_borrowed(), is_borrowed);
        assert_eq!(s.is_owned(), !is_borrowed);
        // Convert to a `Cow`.
        let s = Cow::from(s);
        assert_eq!(matches!(s, Cow::Borrowed(s) if s == expected_value), is_borrowed);
        assert_eq!(matches!(s, Cow::Owned(ref s) if s == expected_value), !is_borrowed);
        assert_eq!(s.as_ptr(), ptr);  // To `Cow` always preserves pointer.
        // Convert back.
        let s = Str::from(s);
        assert_eq!(s, expected_value);
        assert_eq!(s.capacity(), expected_capacity);
        assert_eq!(s.as_ptr(), ptr);  // From `Cow` always preserves pointer.
        // Clone.
        let s2 = s.clone();
        assert_eq!(s, s2);
        assert_eq!(s.as_ptr() == s2.as_ptr(), is_borrowed);  // Cloning a borrowed value preserves the pointer.
        // Convert to a string.
        let s = String::from(s);
        assert_eq!(s, expected_value);
        assert_eq!(s.as_ptr() == ptr, is_borrowed_on_heap);
        // Ensure no memory leak.
        drop(s);
        assert_eq!(start_alloc_count, alloc_count());
        drop(s2);
        assert_eq!(start_alloc_count - if !is_borrowed && is_borrowed_on_heap { 1 } else { 0 }, alloc_count());
    }

    #[test]
    fn test_from_str_static_some() {
        assert_ptr("moo", "moo", 0, true, false);  // Borrowed from static, copied to heap.
    }

    #[test]
    fn test_from_str_static_empty() {
        assert_ptr("", "", 0, true, false);  // Borrowed from static, different empty pointer on heap.
    }

    #[test]
    fn test_from_str_borrowed_stack_some() {
        let s = [109, 111, 111];
        assert_ptr(str::from_utf8(&s).unwrap(), "moo", 0, true, false);  // Borrowed from stack, copied to heap.
    }

    #[test]
    fn test_from_str_borrowed_stack_empty() {
        let s = [];
        assert_ptr(str::from_utf8(&s).unwrap(), "", 0, true, false);  // Borrowed from stack, different empty pointer on heap.
    }

    #[test]
    fn test_from_str_borrowed_heap_some() {
        let s = String::from("moo");
        assert_ptr(s.as_str(), "moo", 0, true, false);  // Borrowed from heap, copied to heap.
    }

    #[test]
    fn test_from_str_borrowed_heap_empty() {
        let s = String::from("");
        assert_ptr(s.as_str(), "", 0, true, true);  // Borrowed from heap, re-use empty pointer on heap.
    }

    #[test]
    fn test_from_string_some() {
        assert_ptr(String::from("moo"), "moo", 3, false, true);  // Owned on heap, re-used owned pointer on heap.
    }

    #[test]
    fn test_from_string_empty() {
        assert_ptr(String::from(""), "", 0, true, true);  // Empty heap pointer becomes borrow, re-used same pointer on heap.
    }

    #[test]
    #[ignore]  // Allocates 4GB of memory, so don't run all the time!
    fn test_from_truncate() {
        let data = String::from_utf8(vec![b'a'; MASK_LO + 1]).unwrap();
        assert_eq!(data.len(), MASK_LO + 1);
        assert!(data.capacity() > MASK_LO);
        // Check borrowed truncates.
        let s = Str::from(data.as_str());
        assert_eq!(s.len(), MASK_LO);
        assert_eq!(s.capacity(), 0);
        // Check owned truncates.
        drop(s);
        let s = Str::from(data);
        assert_eq!(s.len(), MASK_LO);
        assert_eq!(s.capacity(), MASK_LO);
    }

    #[test]
    fn test_eq() {
        assert_eq!(Str::from("moo"), "moo");
    }

    #[test]
    fn test_ord() {
        assert!(Str::from("b") > "a");
        assert!(Str::from("a") < "b");
    }

    #[test]
    fn test_debug() {
        assert_eq!(format!("{:?}", Str::from("moo")), "\"moo\"");
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{}", Str::from("moo")), "moo");
    }
}
