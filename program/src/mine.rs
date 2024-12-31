use std::mem::size_of;

use drillx::Solution;
use ore_api::prelude::*;
use ore_boost_api::state::{Boost, Stake};
#[allow(deprecated)]
use solana_program::{
    keccak::hashv,
    sanitize::SanitizeError,
    serialize_utils::{read_pubkey, read_u16},
    slot_hashes::SlotHash,
};
use steel::*;

/// Mine validates hashes and increments a miner's claimable balance.
pub fn process_mine(accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
    // Parse args.
    let args = Mine::try_from_bytes(data)?;

    // Load accounts.
    let clock = Clock::get()?;
    let t: i64 = clock.unix_timestamp;
    let (required_accounts, optional_accounts) = accounts.split_at(6);
    let [signer_info, bus_info, config_info, proof_info, instructions_sysvar, slot_hashes_sysvar] =
        required_accounts
    else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };
    signer_info.is_signer()?;
    let bus = bus_info.is_bus()?.as_account_mut::<Bus>(&ore_api::ID)?;
    let config = config_info
        .is_config()?
        .as_account::<Config>(&ore_api::ID)?
        .assert_err(
            |c| c.last_reset_at.saturating_add(EPOCH_DURATION) > t,
            OreError::NeedsReset.into(),
        )?;
    let proof = proof_info
        .as_account_mut::<Proof>(&ore_api::ID)?
        .assert_mut_err(
            |p| p.miner == *signer_info.key,
            ProgramError::MissingRequiredSignature,
        )?;
    instructions_sysvar.is_sysvar(&sysvar::instructions::ID)?;
    slot_hashes_sysvar.is_sysvar(&sysvar::slot_hashes::ID)?;

    // Authenticate the proof account.
    authenticate(&instructions_sysvar.data.borrow(), proof_info.key)?;

    // Reject spam transactions.
    let t_target = proof.last_hash_at.saturating_add(ONE_MINUTE);
    let t_spam = t_target.saturating_sub(TOLERANCE);
    if t.lt(&t_spam) {
        return Err(OreError::Spam.into());
    }

    // Validate the hash digest.
    let solution = Solution::new(args.digest, args.nonce);
    if !solution.is_valid(&proof.challenge) {
        return Err(OreError::HashInvalid.into());
    }

    // Validate the hash satisfies the minimum difficulty.
    let hash = solution.to_hash();
    let difficulty = hash.difficulty();
    if difficulty.lt(&(config.min_difficulty as u32)) {
        return Err(OreError::HashTooEasy.into());
    }

    // Normalize the difficulty and calculate the total reward amount.
    let normalized_difficulty = difficulty
        .checked_sub(config.min_difficulty as u32)
        .unwrap();
    let total_reward = config
        .base_reward_rate
        .checked_mul(2u64.checked_pow(normalized_difficulty).unwrap())
        .unwrap();

    // Pool of miners who submitted valid proofs.
    let mut valid_miners: Vec<Pubkey> = Vec::new();

    // Add the current miner to the pool of valid miners.
    if !valid_miners.contains(&signer_info.key) {
        valid_miners.push(*signer_info.key);
    }

    // Graceful exit if no miners exist.
    let num_miners = valid_miners.len() as u64;
    if num_miners == 0 {
        return Ok(()); // Do nothing if no miners are found.
    }

    // Calculate the per-miner share based on the total number of miners.
    let per_miner_share = total_reward / num_miners;

    // Distribute 31% of the per-miner share to the current miner.
    let guaranteed_share = (per_miner_share as f64 * 0.31) as u64;
    proof.balance = proof.balance.checked_add(guaranteed_share).unwrap();
    bus.rewards = bus.rewards.checked_sub(guaranteed_share).unwrap();

    // Pool the remaining reward for the lottery.
    let pooled_share = (total_reward as f64 * 0.69) as u64;

    // Select one random miner from the pool using the block hash.
    let block_hash = hashv(&[slot_hashes_sysvar.data.borrow()]);
    let miner_index = (block_hash.as_ref()[0] as usize) % valid_miners.len();
    let selected_miner = valid_miners[miner_index];

    // Assign the pooled reward to the selected miner.
    if selected_miner == *signer_info.key {
        proof.balance = proof.balance.checked_add(pooled_share).unwrap();
        bus.rewards = bus.rewards.checked_sub(pooled_share).unwrap();
    }

    // Update stats.
    proof.last_hash = hash.h;
    proof.challenge = hashv(&[
        hash.h.as_slice(),
        &slot_hashes_sysvar.data.borrow()[0..size_of::<SlotHash>()],
    ])
    .0;

    proof.total_rewards = proof.total_rewards.saturating_add(total_reward);
    proof.total_hashes = proof.total_hashes.saturating_add(1);

    // Log the mining event.
    MineEvent {
        balance: proof.balance,
        difficulty: difficulty as u64,
        last_hash_at: proof.last_hash_at,
        timing: t.saturating_sub(t_target),
        reward: total_reward,
        boost_1: 0,
        boost_2: 0,
        boost_3: 0,
    }
    .log_return();

    Ok(())
}

/// Authenticate the proof account.
///
/// This process is necessary to prevent sybil attacks. If a user can pack multiple hashes into a single
/// transaction, then there is a financial incentive to mine across multiple keypairs and submit as many hashes
/// as possible in the same transaction to minimize fee / hash.
///
/// We prevent this by forcing every transaction to declare upfront the proof account that will be used for mining.
/// The authentication process includes passing the 32 byte pubkey address as instruction data to a CU-optimized noop
/// program. We parse this address through transaction introspection and use it to ensure the same proof account is
/// used for every `mine` instruction in a given transaction.
fn authenticate(data: &[u8], proof_address: &Pubkey) -> ProgramResult {
    if let Ok(Some(auth_address)) = parse_auth_address(data) {
        if proof_address.ne(&auth_address) {
            return Err(OreError::AuthFailed.into());
        }
    } else {
        return Err(OreError::AuthFailed.into());
    }
    Ok(())
}

/// Use transaction introspection to parse the authenticated pubkey.
fn parse_auth_address(data: &[u8]) -> Result<Option<Pubkey>, SanitizeError> {
    // Start the current byte index at 0
    let mut curr = 0;
    let num_instructions = read_u16(&mut curr, data)?;
    let pc = curr;

    // Iterate through the transaction instructions
    for i in 0..num_instructions as usize {
        // Shift pointer to correct positition
        curr = pc + i * 2;
        curr = read_u16(&mut curr, data)? as usize;

        // Skip accounts
        let num_accounts = read_u16(&mut curr, data)? as usize;
        curr += num_accounts * 33;

        // Read the instruction program id
        let program_id = read_pubkey(&mut curr, data)?;

        // Introspect on the first noop instruction
        if program_id.eq(&NOOP_PROGRAM_ID) {
            // Return address read from instruction data
            curr += 2;
            let address = read_pubkey(&mut curr, data)?;
            return Ok(Some(address));
        }
    }

    // Default return none
    Ok(None)
}
