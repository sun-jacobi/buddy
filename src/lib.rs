// This part of code is inspired by
// https://github.com/rcore-os/buddy_system_allocator/tree/master
// Thanks for the brilliant implementation

#![feature(strict_provenance)]
use core::cmp::min;
use core::ptr::{null_mut, NonNull};

pub mod ll;

use ll::{BareList, Node};

/// Buddy system allocator
/// L : number of size classes
/// G : granularity (i.e) the smallest size class
/// # Safety
///
/// Not thread safe.
/// User is reponsible for guarantee the memory address is correct.
/// User is also reponsible for guarantee the largest block size is enough to use.
pub struct BuddyAlloc<const L: usize, const G: u64> {
    free_list: [BareList; L],
    mem_start: u64,
    mem_end: u64,
}

impl<const L: usize, const G: u64> BuddyAlloc<L, G> {
    const GRANULARITY: u64 = G;
    const LEVELS: usize = L;

    /// Create a new buddy allocator
    /// # Safety
    ///
    /// Must be used after called init
    pub fn new() -> Self {
        Self {
            free_list: [BareList::default(); L],
            mem_start: 0,
            mem_end: 0,
        }
    }

    /// Insert the heap space into the allocator
    pub fn init(&mut self, mem_start: u64, mem_end: u64) {
        assert!(mem_start <= mem_end);
        self.mem_start = mem_start;
        self.mem_end = mem_end;
    }

    /// Allocate memory corresponding the layout
    pub fn alloc(&mut self, layout: core::alloc::Layout) -> *mut u8 {
        let size = layout.size();
        let align = layout.align();

        // if there is a suitable free block
        if let Some((ptr, level)) = self.search_block(size as u64) {
            let addr = ptr.addr().get();
            assert_eq!(addr & (align - 1), 0); // check the alignment

            // if necessary, split the block
            self.split_block(ptr, level, size);

            return addr as *mut u8;
        } else {
            // try to ask for more memory
            let addr = if let Some((_, addr)) = self.extend_heap(layout) {
                addr
            } else {
                return null_mut();
            };

            return addr as *mut u8;
        }
    }

    pub fn dealloc(&mut self, ptr: *mut u8, layout: core::alloc::Layout) {
        // Since layout is the same, we can recalculate the block size directly
        let size = layout.size() as u64;
        let align = layout.align() as u64;

        let addr = ptr as u64;
        assert_eq!(addr & (align - 1), 0); // check the alignment
        let (level, _block_size) = self
            .find_first_fit(size)
            .unwrap_or_else(|| panic!("layout should not be changed"));

        let node = Node::from_addr(addr);
        self.free_list[level].push(node);

        // if necessary, coalesce blocks
        self.coalesce_block(node, level);
    }

    // split the block
    fn split_block(&mut self, block: NonNull<Node>, level: usize, size: usize) {
        let max_level = level;
        let min_level = if let Some((min_level, _)) = self.find_first_fit(size as u64) {
            min_level
        } else {
            return;
        };

        let left_addr = block.addr().get() as u64;

        for l in (min_level + 1..max_level).rev() {
            let mid_addr = left_addr + Self::block_size(l) / 2;
            assert!(left_addr <= mid_addr);
            self.free_list[l].push(Node::from_addr(mid_addr));
        }
    }

    // coalesce the block
    fn coalesce_block(&mut self, block: NonNull<Node>, level: usize) {
        let addr = block.addr().get() as u64;
        let block_size = Self::block_size(level);

        // find the buddy
        let buddy_addr = addr ^ block_size;

        // Larger than the highest level
        if level + 1 >= Self::LEVELS {
            return;
        }

        // if free, then coalesce two blocks
        // TODO: use bitmap or boundary tag
        if self.free_list[level].remove(buddy_addr) {
            let min_addr = min(addr, buddy_addr);
            self.free_list[level + 1].push(Node::from_addr(min_addr));
        }
    }

    // Using a lazy method to only extend the heap if necessary
    fn extend_heap(&mut self, layout: core::alloc::Layout) -> Option<(usize, u64)> {
        let size = layout.size() as u64;
        let align = layout.align() as u64;

        let start = Self::round_up(self.mem_start, align);

        let end = self.mem_end;

        let (level, extended_size) = self.find_first_fit(size)?;

        self.mem_start += extended_size;

        if start > end {
            return None;
        }

        Some((level, start))
    }

    // Caculate the first fit block size
    fn find_first_fit(&self, size: u64) -> Option<(usize, u64)> {
        for l in 0..L {
            let block_size = Self::block_size(l);
            if block_size >= size {
                return Some((l, block_size));
            }
        }
        None
    }

    // search for the first fit block in O(logN)
    fn search_block(&mut self, size: u64) -> Option<(NonNull<Node>, usize)> {
        for l in 0..L {
            let block_size = Self::block_size(l);
            if block_size >= size && !self.free_list[l].is_empty() {
                if let Some(node) = self.free_list[l].pop() {
                    return Some((node, l));
                }
            }
        }
        None
    }

    fn block_size(level: usize) -> u64 {
        (1 << level as u64) << Self::GRANULARITY
    }

    fn round_up(addr: u64, align: u64) -> u64 {
        if addr == 0 {
            return addr;
        }

        (addr + (align - 1)) & (!(align - 1))
    }
}

#[cfg(test)]
mod test {
    use std::alloc::Layout;

    use crate::BuddyAlloc;

    #[test]
    fn init_test() {
        let pool: [u8; 4096] = [0; 4096];
        let mem_start = pool.as_ptr() as u64;
        let mem_end = mem_start + 4096;
        let mut buddy: BuddyAlloc<12, 4> = BuddyAlloc::new();
        buddy.init(mem_start, mem_end);
    }

    #[test]
    fn block_size_test() {
        for l in 0..12 {
            assert_eq!(BuddyAlloc::<12, 4>::block_size(l), 16 << l);
        }
    }

    #[test]
    fn round_up_test() {
        assert_eq!(BuddyAlloc::<12, 4>::round_up(4095, 4096), 4096);
        assert_eq!(BuddyAlloc::<12, 4>::round_up(0, 4096), 0);
        assert_eq!(BuddyAlloc::<12, 4>::round_up(4096, 4096), 4096);
    }

    #[test]
    fn malloc_free_test() {
        let pool: [u8; 4096] = [0; 4096];
        let mem_start = pool.as_ptr() as u64;
        let mem_end = mem_start + 4096;
        let mut buddy: BuddyAlloc<12, 4> = BuddyAlloc::new();
        buddy.init(mem_start, mem_end);
        let layout = Layout::from_size_align(16, 16).unwrap();
        for _ in 0..1000 {
            let ptr = buddy.alloc(layout);

            buddy.dealloc(ptr, layout);
        }
    }

    #[test]
    fn malloc_free_test_2() {
        let pool: [u8; 4096] = [0; 4096];
        let mem_start = pool.as_ptr() as u64;
        let mem_end = mem_start + 4096;
        let mut buddy: BuddyAlloc<12, 4> = BuddyAlloc::new();
        buddy.init(mem_start, mem_end);
        for l in 4..10 {
            let size = 1 << l;
            let align = 1 << l;
            let layout = Layout::from_size_align(size, align).unwrap();
            let ptr = buddy.alloc(layout);
            assert_eq!((ptr as u64) & ((align - 1) as u64), 0);
            buddy.dealloc(ptr, layout);
        }
    }
}
