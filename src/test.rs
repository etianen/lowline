use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

thread_local! {
    static ALLOC_COUNT: Cell<isize> = Cell::new(0);
}

/// Returns the number of heap allocations currently made by this thread.
pub fn alloc_count() -> isize {
    ALLOC_COUNT.with(|alloc_count| alloc_count.get())
}

#[global_allocator]
static ALLOC: TestAlloc = TestAlloc;

/// Counting allocator to check for memory leaks in tests.
struct TestAlloc;

unsafe impl GlobalAlloc for TestAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // println!("alloc");
        ALLOC_COUNT.with(|alloc_count| alloc_count.set(alloc_count.get() + 1));
        System.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // println!("dealloc");
        ALLOC_COUNT.with(|alloc_count| alloc_count.set(alloc_count.get() - 1));
        System.dealloc(ptr, layout)
    }
}
