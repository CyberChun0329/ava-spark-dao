// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {DeployAVACore} from "@ava-protocol/contracts/script/DeployAVACore.s.sol";
import {DeploySparkV15OnExistingCore} from "../script/DeploySparkV15OnExistingCore.s.sol";
import {SparkV15} from "../src/apps/spark/v15/SparkV15ApplicationModule.sol";
import {SparkV15Funds} from "../src/apps/spark/v15/SparkV15Funds.sol";
import {SparkV15MaterialProvisions} from "../src/apps/spark/v15/SparkV15MaterialProvisions.sol";
import {AVACapabilityKeys} from "@ava-protocol/contracts/src/core/AVACapabilityKeys.sol";
import {MockERC20} from "./spark/mocks/MockERC20.sol";

interface InstalledPreviewVm {
    function setEnv(string calldata name, string calldata value) external;
    function toString(address value) external pure returns (string memory);
    function chainId(uint256 value) external;
    function prank(address account) external;
}

contract InstalledPreviewTest {
    InstalledPreviewVm private constant vm = InstalledPreviewVm(address(uint160(uint256(keccak256("hevm cheat code")))));
    address private constant ADMIN = address(0xA0);
    address private constant PROVIDER = address(0xA1);
    address private constant CUSTOMER = address(0xB1);

    function testInstalledCoreAndSparkSupportCourseRecharge() public {
        vm.chainId(31337);
        DeployAVACore.Deployment memory core = new DeployAVACore().run(ADMIN);
        MockERC20 token = new MockERC20("Local test token", "TEST", 18);
        _env("AVA_EXISTING_KERNEL", address(core.kernel));
        _env("AVA_EXISTING_REQUESTS", address(core.requests));
        _env("AVA_ROOT_ADMIN", ADMIN);
        _env("SPARK_V15_TOKEN", address(token));
        _env("SPARK_V15_COURSE_PROVIDER", PROVIDER);
        _env("SPARK_V15_BOOKING_COORDINATOR", address(0xA2));
        _env("SPARK_V15_CORE_PARTNER", address(0xA3));
        _env("SPARK_V15_SOURCE", address(0xA4));
        _env("SPARK_V15_VERIFIER", address(0xA5));
        _env("SPARK_V15_ALLOCATOR", address(0xA6));
        _env("SPARK_V15_REVIEWER", address(0xA7));
        _env("SPARK_V15_ALTERNATIVE_CONTACT", address(0));
        _env("SPARK_V15_MATERIALS_DAO", address(0xA8));
        _env("SPARK_V15_SERVICE_RESERVE", address(0xA9));

        DeploySparkV15OnExistingCore.Deployment memory app = new DeploySparkV15OnExistingCore().run();
        SparkV15Funds funds = app.payments.FUNDS();
        SparkV15MaterialProvisions provisions = SparkV15MaterialProvisions(funds.materialProvisions());
        require(address(app.kernel) == address(core.kernel) && address(app.requests) == address(core.requests), "Core binding");
        require(address(app.payments.REQUEST_ALLOCATION()) == address(core.requests), "Payment request binding");
        require(core.packages.getActivePackageId(SparkV15.APP_ID, SparkV15.WORKFLOW) == app.packageId, "Active package");
        require(core.packages.getModule(app.packageId, AVACapabilityKeys.ALLOCATION) == address(app.requestPolicy), "Allocation policy");
        require(app.requestPolicy.REQUEST_ALLOCATION() == address(core.requests), "Policy requests");
        require(app.requestPolicy.EXECUTOR() == address(app.payments), "Policy executor");
        require(address(app.booking) != address(0) && address(app.cases) != address(0), "Course installation");
        require(address(provisions) != address(0) && address(provisions).code.length != 0, "Material provisions");
        require(funds.materialBookingCoverage() == address(provisions.FUNDING_CASES()), "Booking coverage");

        bytes32 authority = keccak256(abi.encode(SparkV15.APP_ID, funds.CREDIT_PROVIDER_ROLE(), PROVIDER));
        SparkV15Funds.RechargeTerms memory terms = SparkV15Funds.RechargeTerms({
            customer: CUSTOMER, amount: 10, returnCap: 0, returnThrough: 0, agreementRef: keccak256("test:agreement")
        });
        vm.prank(PROVIDER);
        bytes32 offer = funds.offerRecharge(terms, authority);
        token.mint(CUSTOMER, 10);
        vm.prank(CUSTOMER);
        token.approve(address(funds), 10);
        vm.prank(CUSTOMER);
        uint256 receipt = funds.recharge(offer);
        require(funds.getRechargeOffer(offer).packageId == app.packageId, "Offer package");
        require(funds.getRechargeOffer(offer).receiptId == receipt, "Offer receipt");
        require(funds.getRechargeReceipt(receipt).received == 10, "Receipt amount");
        require(funds.creditBalance(funds.creditAccount(CUSTOMER)) == 10, "Customer credit");
        require(token.balanceOf(address(funds)) == 10 && funds.reservedUnits() == 10, "Funded balance");
    }

    function _env(string memory name, address value) private {
        vm.setEnv(name, vm.toString(value));
    }
}
