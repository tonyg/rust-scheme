inotifytest:
	inotifytest sh -c 'reset; cargo build && RUST_BACKTRACE=1 cargo test -- --nocapture'
