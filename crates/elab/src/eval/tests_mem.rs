// SPDX-License-Identifier: Apache-2.0
//! The address width of a memory port (section 7.6).

use super::mem::addr_width;

#[test]
fn the_address_width_is_the_ceiling_of_the_log_with_a_minimum_of_one() {
    for (depth, width) in [
        (1, 1),
        (2, 1),
        (3, 2),
        (4, 2),
        (5, 3),
        (8, 3),
        (9, 4),
        (1 << 20, 20),
        ((1 << 20) + 1, 21),
        (16_777_215, 24),
        (16_777_216, 24),
    ] {
        assert_eq!(addr_width(depth), width, "{depth}");
    }
}
