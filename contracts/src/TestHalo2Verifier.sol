// SPDX-License-Identifier: AGPL-3.0
pragma solidity ^0.8.0;

contract TestHalo2Verifier {
    function verifyProof(
        bytes calldata proof,
        uint256[] calldata instances
    ) public returns (bool) {
        return true;
    }
}