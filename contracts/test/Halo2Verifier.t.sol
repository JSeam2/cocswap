// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console} from "forge-std/Test.sol";
import {Halo2Verifier} from "../src/Halo2Verifier.sol";
import {COCSwap} from "../src/COCSwap.sol";
import {TestToken} from "../src/TestToken.sol";
contract Halo2VerifierTest is Test {
    Halo2Verifier public verifier;
    TestToken public token0;
    TestToken public token1;
    COCSwap public pair;
    uint[] public instances;

    function setUp() public {
        // Deploy the verifier contract
        verifier = new Halo2Verifier();
        // Deploy two new erc20 tokens
        token0 = new TestToken("test", "test");
        token1 = new TestToken("test", "test");
        // Deploy the pair contract
        pair = new COCSwap(address(token0), address(token1), address(verifier));
        instances = getInstancesFromFFI();
    }

    function getProofFromFFI() internal returns (bytes memory) {
        string[] memory input_proof = new string[](3);
        input_proof[0] = "echo";
        input_proof[1] = "-n";
        input_proof[
            2
        ] = "0x1543afa402666a6d8ba76b508e0d9a216d7b84b88e7f2117f1a7b61c3f536c9d0ab8e03c038ddaad4533160274a86d6ec62b80a26e1e03e97f34d9fe022eb3220fbb9ee6554fc7553502d73bde1b05ce74b36fe1b2cfece326d28634c9e0b79305f0692794e881b30a9142e210877d3ad3c8296b98ddf3fdfd0cc6752be9e1282a909dc879276298b2fa2f8b2c8b8ff578e7b80ecff01be2abc4dc396e9c745b0e56c39496b3a992aebb15ff7fc72e595346b10cf94e510e88e64dfa536b63141db19ac56e16c6e8bb08fc60a86c50e535201dfca1c983ec266cc54398a09b6f11be6a4f6fba1b05a59d0457672eda90ccc8fc04d6948496aff498bc89da8a321296aa1d9ad1a74889a53cbf75e7e4826d98b99ca1cc77fd3b76c2b1ab9ead4b1b58fe9f96af8cd6c8c61813b2400fed03a6e4dc1a260b66b3b5da57038cd81b10702593dcff00d39b733fb9aa70eb5a1387115de1c31cc53c279900a326de890c5f5d2fe8d3852a29eff4143580c85e04a2ae7a8af7d80ec9aaf66b439b2995171746471ce426911a92c2578d9ffe6ad83b4844b83e9719e947042b42fba08e250f670612d4b3a9acc0a937421018b042c5297c7599f1eb4f9bd928f9598a6714c65c992420bb97419de2809ee28affd28a99606fe88bc3ee34c72fb9d128ad1304429230cd9d6efd00a6310d921db77c1afc6d8a04277013a65d815f88c5670c4ff41417a9121b4b5a86aff427ac2a1c19aec3927d2e2ba1182be1f616dc922c08462175ad7d83106d3b4271527164fcb7cbd4db17234849772ef0d81afa101248e8ca91eb601f7e77ca21043d8a0b53001c4aaf4e365ebabdfe69bdd116480ce0844fa01f812ce9d68e5c0d9aff9f0f2f2c23a55fb18ae00f27999ef3949a03a882910f2f12c50495813ca70b03f1b14a2ce2cac3bc4f4bfa7f465d2e238e24af38269d021b9fcebdd52da717dc42bd35958d3582f41af48d70b59488b03d2f80150050e21e3fd043c7ea3ea245a8b4b601d5aa6356277ba7b1310092ba8504011e061f233cdd530e6318244cb1f29627d23b6d70336f5fbe42dd69ae3ea928034833fb96fb0c6b282b32941cafa05de77e516bd0ad15a805f326e88a807b242bc93c92b171b777c2aa2798419bcc60755c55f7f9260bcbc8ab4db667502e08e881cb0b012bf135d70166660a1b04778cd5aadc17ab313efdbfcd562d1ca228543e23e6d8f635ebd09a4639f073cf41e6add7267fa7c28e35f551546a9a9207a5dd8db1a62bc84df827a62446a98853f7e2217aff1814fda7046679d21f7f034639e2d15cb823a287cdfbf723c5f96b6f22d3020a6e58b7d85b10f658282d275afc52a1046788211b26b1f8f4990d106bbf890b6669d3cd70deb51b3f93dd16f7adfce8b96e3c587f8c062a58f9866f736266b9fcc241ee8b42d1dfb54a7a01f74607dfb49162ca81c460cc517a69c752fdea36206fe5201faa1aaf6cbbae0e34975c795083b71ee86adf976fe4c079dabe4a1acdef9c772d26f755f82eb8220319e20ffbc31e0b8280ce3889b9c1af534f2e35e54a37e5f91440385e7e3001736cfc5d7f1a161978574e6506016bd6347f72985c446058c7ac99dd13a5482d8d2385f7ebbf48a715b274307e1e2d4b7b44ccea4339cf299d4d10444864022d916ed741b8db90320f73820a2fffcc7c7d1d5572c5749ba3bfebe2bcc7fa7d0511f73e8c0ca39cc2d27c3ab86ccbefd4f99deece75a95cdf9bfa2760ad9b731547fd0264b6d300d15320df67bfcb04c47984f640e2199200d226f2d82cb5c515b4fc485845d0ea11db353c3fbcc390a195f64953b711f0f4048cc395be1b66199618e554a9fb2ece884f8bcde88d40603947818e3b4be152fc2af130835780145fc389a1d394636855a1f4799e46b70ac3cc14cf641bf319419273dcbd97272b5976dd82c3c59ef13ae9f838ebdbc6c8b24e37df335dbec0ff1405d1a82fb11b095f2e4d235aed3a3ffe56d55eda5f7dec907f50726a33e79d7d924ef2be591e4b606ac1922702cd8405e7c7e339f293935c812110a5a3cbf7d2d7fbdb09e40d30898b8f67825dc456222c3acdd9731d633560bcff0214b8d436814e2f5ac32841adffde8b3047273a284910580c157645405c936f60924a6cd7a92fda9ddc25a24f391732e04014efa9c2403ddf599a710d1ee32ec9ce44272c6c2018cb492867c31d7e72d3fbf6996555f08a56a625ec2c487d992059d3646cb324607e992f209cb7902f21ff30207b127f7b73313ddb48afc1b464aa12962df1dc439c8209085db97a911d80b1bdc20bdee4fec639f51c3770cbb29a1ed0e65ca2ec449119dffaa8ed1287d27cca88199934baec288d86900361fe89b952271ee9ac800b289cace4b85dbfe058c3b6a9dafccb7f9be97467b0641d0e995b302246e201a5244211cfc2d6666c3a2dd54e96bf13d00272b2941a5c1dccbcde0f05a63f7acc1e438af0629265b692b54dceff52b6e24ecfe3dec48dc52ddd5c11aed49e24750018b4f40f170b4b7bda58763e353715091bc3a12252f653dcd23917cdbabbce271b382e1294e6bfe3a4ebf9924372042b996431f24363bc11f44a1df339a2d412a0947f18a4a04ee4b7f6ad02feb0d028efb4b0e4d5589e2d1044166900c4cd16c0fdc3bb17fe8167f555f79c8ffdad4f00bab16a4b58fdba4eef92777cc4032cee1d1d9a9a1ded82d489b8a050009e006660c95d5d1db1ffb434e41de393600bd2074e31fae59d84c1c8463ce49c657764a292cb4c534aac7cd6303259103b2af709d599d3787bc49884207ffe9219f70f50ab1e645a2a02923b8618c79f5518e23370a27d9cc9de5ac07e3113f84c5c1688102936f7af266fcce7c1706fbe0fc858e813c4f72c96f89b229901b17389e65546a0dde9e9b144dc7379ad4f522b559534d41b6c774a7fa21db47ce0355166dc4bc89eaf3c3f22a8e9fa6ec01b0001ca9876239a03cc5b89d10ff3fc683b70579a12684b196af544ef43d47adb00000000000000000000000000000000000000000000000000000000000000000676bc38c95bb6e7684d58784e06454ec07d701887546b7a95398d11253f953f0d0fc532d61c32d8aa58a9b7f0b6e7f3b1666a0105db79f2f925904fa89482c01f5b474c88c463edf9c582eb5b571e6f3ade16b3323a2e9b3cb0b2758ae6995c10b9201e2d7b1cccbde8dc2821d473f059610a70a2fdc289aee1d29fdac891d324091a3e229d494c1669c5f4b9bc6226b059df252479abd33f490dab7e29e7070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007ab4b63cd7be53eca88ff4dd856be26b2e340d42ba1d1a9491cebff529388b4178ee4c79dd8dedcc769406ea44a4e1ebccee7b9341d87e911fff070908923b003962b4bfbf0b79fd8d892b26e08c6d890ee1ca169ad01ad581134a515d09e7410a68d99c897372b2d368b10fa10f3ecdb6800168d1ca0cfe9bdeb74b3f9ba000ad0db2f9a33a1313d0ba56f1e269872858f1801fa0561cbe5687b963340b42305465fef84051bc69632edc37a74ab45ec9889c2893d60fffa5ad17cf0a6f3b400936daeaa6ddff65cfdad95fe000c39b4327990efa8360e4b47cf289b2d41ef2b03ad30a433806f2ad75ee67ec2d5d687095cff810869e83899275f42074a8727a58d9d2be1866f873ab89ccb274adda487165591efe850a97a56e51066c7b80a6f1cad53d676b69c4ece7636e8420fe8f319926bc3217964e3a077fc27c29025ff94f98a563e321f8429ae8258cce8692e7ca26460b5863ae73be0d8ea31a8042bc492638097fff39b3ebe090748e14a7be9738b9d3b2bceae6a324f3e21490532e2b0d3d35c79a34975ace28b0c37ea80f13d8ad3f90ac20d90a20fa1427c13ba2f4f5f94a773055ef58898f75007718fade9d55dbed944477e09dc7909f9162e20db0c91ee087730bc697067882fb99718d97109dae0f20e85d3802c70c31cd0116b21178cac43eb8d6f736ed0463917f42e0e47b04e2071fee2288510010ebb61a0e0ac109eb0ff0192aa8354f12003d2fb8a470110f3d5e20a2447a878079924a659c1ecdfc09da033d43cd7768293509b2b343e00edd6738fbd3b2f351e82875da4ff25b0ca8b3c0ce39ef03c042f45d7524fbb2348544afe58ed753628e9fce3c987428976d2c19dd9938b43fd1737ccd28282e3a93e9074dab6453c06c494854760e80239644c07d17c8549fcb828311ce1f1078da57b95a15a02202ed853d038f09890b8cd4824b98b6ac7b567815e5c10b2a0b4738fe742b2da11062f2529b0b8281154c9692c05341e083bdfdbc38742ba8742c44e06ed0f2eef0f0afd5d554359adff5980b6c382a55933d5cb35fec6da1b1433f800a38a372f268e4d7a6ed6e674ecd2a2ed3387173fe180124486ef8381ec872e65c3065db80b241e7300b3c05307320eca4d6917f3c8b548f1d7ec12ff12efaba1a9d677a806dcf9e8e98479fdde41b13ed7cf2aeda4859f4a61e8328dde3c82373c3604bc23a393a3916fffcbd578c8209a5e5164a4cb89e89e8e1ce4a9224b14ce76a1f6301847618a4459c36aa679e520097379fe39783863cfba2b0289a79097d279db094699586c1eadb4a90f9fee6a3f115ac766ebc37a62fc11f41e70be97924afd16132ba33443296c9d88e4103aca78ab5725498413df051ab30abadf3d1309c00d4ddfc9f2a4eb97d876182e897a9f81fde323efc06dafb4a1291a727f2258780040ded00f9d63f292530451ed76064d8c6562a7c63d9d6f9b5c3933caabcb5428a64d6d77a2a33596f70435da5307453057440a193035ec26d2c601bae45d940c94ed224b62e2f71070f2f51e9c2619b271eb3f1155cdabf990e8c8da923b1c1f4f673a761b5b372e49961664c1abe0e55885c6523bbc70b9210aff44d822f80e3e28b04a80e0fc4fc7d3becc8ce259466e3d08e2b19841e2b43c520a6938ca24ad7f2da4c2e4d6638f0ed4c7f89f89d72b7a9d7f8ff5f376b8c5221b75d0681932d09d7fcfc339458e6a0eb52b1eb18005b4b6ad76b51eacc47794f3c9ee19";

        bytes memory proof = vm.ffi(input_proof);

        return proof;
    }

    function getInstancesFromFFI() internal returns (uint256[] memory) {
        uint256[] memory _instances = new uint256[](7);
        string[] memory baseInput = new string[](3);
        baseInput[0] = "echo";
        baseInput[1] = "-n";

        string[7] memory hexStrings = [
            "0x00000000000000000000000000000000000000000000000000000000000006c4",
            "0x0000000000000000000000000000000000000000000000000000000000000276",
            "0x0000000000000000000000000000000000000000000000000000000000000207",
            "0x000000000000000000000000000000000000000000000000000000000000031f",
            "0x0000000000000000000000000000000000000000000000000000000000000581",
            "0x0000000000000000000000000000000000000000000000000000000000000169",
            "0x00000000000000000000000000000000000000000000000000000000000001e5"
        ];

        for (uint256 i = 0; i < 7; i++) {
            baseInput[2] = hexStrings[i];
            bytes memory res = vm.ffi(baseInput);
            _instances[i] = abi.decode(res, (uint256));
        }

        return _instances;
    }

    function testVerify() public {
        // Values are obtained from test_proof.json
        assertTrue(
            verifier.verifyProof(getProofFromFFI(), getInstancesFromFFI())
        );
    }

    function testAddRemoveLiquidity() public {
        uint256 token0AmountInit = instances[0];
        uint256 token1AmountInit = instances[1];
        uint256 token0Amount = instances[5];
        uint256 token1Amount = instances[6];
        // uint256 expectedLiquidity = 2 ether;

        // Approve pair to spend tokens
        token0.approve(address(pair), token0AmountInit);
        token1.approve(address(pair), token1AmountInit);

        // Initialize liqudity
        uint256 shares_init = pair.addLiquidityInit(
            token0AmountInit,
            token1AmountInit
        );

        // Remove liquidity
        (uint256 amount0, uint256 amount1) = pair.removeLiquidity(
            shares_init,
            instances
        );

        // assert that the amounts are equal to the initial amounts
        assertEq(amount0, token0AmountInit);
        assertEq(amount1, token1AmountInit);

        // Approve pair to spend tokens
        token0.approve(address(pair), token0AmountInit);
        token1.approve(address(pair), token1AmountInit);

        // Initialize liqudity
        shares_init = pair.addLiquidityInit(token0AmountInit, token1AmountInit);

        // Approve pair to spend tokens for new amount of liquidity
        token0.approve(address(pair), token0Amount);
        token1.approve(address(pair), token1Amount);

        // Add liquidity
        uint256 shares = pair.addLiquidity(
            token0Amount,
            token1Amount,
            getProofFromFFI(),
            instances
        );

        // Check liquidity and token balances
        assertEq(
            token0.balanceOf(address(pair)),
            token0Amount + token0AmountInit
        );
        assertEq(
            token1.balanceOf(address(pair)),
            token1Amount + token1AmountInit
        );
    }
}
