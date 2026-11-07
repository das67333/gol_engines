use super::*;
use crate::quadtree::hashtable::CacheField;
use std::sync::atomic::Ordering;

#[test]
fn active_work_coexists_with_registration_and_notification() {
    let raw = Box::into_raw(Box::new(ProcessingData::<[u32; 2], u32>::new(SmallVec::new())));
    let cache = CacheField::<u32>::default();
    cache.set_ptr(raw);
    let data = unsafe { &*cache.get_ptr::<ProcessingData<[u32; 2], u32>>() };
    // Simulate ACTIVE ownership while DEPS_LOCK protects a registration.
    let active = unsafe { data.active_work() };
    active.work[0] = 7;
    active.waiting_cnt.store(1, Ordering::Relaxed);
    unsafe { data.push_dependent(42) };
    assert_eq!(data.waiting_cnt.fetch_sub(1, Ordering::AcqRel), 1);
    // The owner borrow stays live across both accesses to the shared payload.
    active.work[1] = active.work[0] + 1;
    assert_eq!(*active.work, [7, 8]);
    // The owner has now entered its finish barrier.
    assert_eq!(unsafe { data.take_dependents() }.as_slice(), &[42]);
    cache.set_value(8);
    unsafe { drop(Box::from_raw(raw)) };
    assert_eq!(cache.get_value(), 8);
}
