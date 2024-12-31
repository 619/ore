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

    // Normalize the difficulty and calculate the reward amount.
    let normalized_difficulty = difficulty
        .checked_sub(config.min_difficulty as u32)
        .unwrap();
    let mut reward = config
        .base_reward_rate
        .checked_mul(2u64.checked_pow(normalized_difficulty).unwrap())
        .unwrap();

    // Apply boosts.
    let base_reward = reward;
    let mut boost_rewards = [0u64; 3];
    let mut applied_boosts = [Pubkey::new_from_array([0; 32]); 3];
    for i in 0..3 {
        if optional_accounts.len().gt(&(i * 2)) {
            let boost_info = optional_accounts[i * 2].clone();
            let stake_info = optional_accounts[i * 2 + 1].clone();
            let boost = boost_info.as_account::<Boost>(&ore_boost_api::ID)?;
            let stake = stake_info
                .as_account::<Stake>(&ore_boost_api::ID)?
                .assert(|s| s.authority == proof.authority)?
                .assert(|s| s.boost == *boost_info.key)?;

            if applied_boosts.contains(boost_info.key) {
                continue;
            }

            applied_boosts[i] = *boost_info.key;

            if boost.expires_at.gt(&t)
                && boost.total_stake.gt(&0)
                && stake.last_stake_at.saturating_add(ONE_MINUTE).le(&t)
            {
                let multiplier = boost.multiplier.checked_sub(1).unwrap();
                let boost_reward = (base_reward as u128)
                    .checked_mul(multiplier as u128)
                    .unwrap()
                    .checked_mul(stake.balance as u128)
                    .unwrap()
                    .checked_div(boost.total_stake as u128)
                    .unwrap() as u64;
                reward = reward.checked_add(boost_reward).unwrap();

                boost_rewards[i] = boost_reward;
            }
        }
    }

    // Apply liveness penalty.
    let reward_pre_penalty = reward;
    let t_liveness = t_target.saturating_add(TOLERANCE);
    if t.gt(&t_liveness) {
        let secs_late = t.saturating_sub(t_target) as u64;
        let mins_late = secs_late.saturating_div(ONE_MINUTE as u64);
        if mins_late.gt(&0) {
            reward = reward.saturating_div(2u64.saturating_pow(mins_late as u32));
        }

        let remainder_secs = secs_late.saturating_sub(mins_late.saturating_mul(ONE_MINUTE as u64));
        if remainder_secs.gt(&0) && reward.gt(&0) {
            let penalty = reward
                .saturating_div(2)
                .saturating_mul(remainder_secs)
                .saturating_div(ONE_MINUTE as u64);
            reward = reward.saturating_sub(penalty);
        }
    }

    // Apply bus limit.
    let reward_actual = reward.min(bus.rewards).min(1);
    
    // Apply bus limit.
    let reward_actual = reward.min(bus.rewards).min(ONE_ORE);

    // Each miner gets 31% of their earned reward based on difficulty
    let base_reward_portion = (reward_actual as u128)
        .checked_mul(31)
        .unwrap()
        .checked_div(100)
        .unwrap() as u64;

    let mut final_reward = base_reward_portion;

    // The pool is always 69% of ONE_ORE
    let pool_reward = (ONE_ORE as u128)
        .checked_mul(69)
        .unwrap()
        .checked_div(100)
        .unwrap() as u64;

    // Check if this is the only miner by looking at the total miners count in the bus
    let is_only_miner = bus.total_miners == 1;
    
    // If they're the only miner, they automatically win the pool
    if is_only_miner {
        final_reward = final_reward.saturating_add(pool_reward);
    } else if bus.total_miners > 1 {
        // If there are multiple miners, use the hash to pick a winner
        let is_winner = hash.h[0] <= (255 / bus.total_miners); // Probability of 1/total_miners
        
        if is_winner {
            final_reward = final_reward.saturating_add(pool_reward);
        }
    }
    // If there are 0 miners, we don't do anything with the pool
    // If there are 0 miners, we don't do anything with the pool

    // Update balances.
    bus.theoretical_rewards = bus.theoretical_rewards.checked_add(reward).unwrap();
    bus.rewards = bus.rewards.checked_sub(reward_actual).unwrap();
    proof.balance = proof.balance.checked_add(final_reward).unwrap();

    // Hash a recent slot hash into the next challenge to prevent pre-mining attacks.
    proof.last_hash = hash.h;
    proof.challenge = hashv(&[
        hash.h.as_slice(),
        &slot_hashes_sysvar.data.borrow()[0..size_of::<SlotHash>()],
    ])
    .0;

    // Update stats.
    let prev_last_hash_at = proof.last_hash_at;
    proof.last_hash_at = t.max(t_target);
    proof.total_hashes = proof.total_hashes.saturating_add(1);
    proof.total_rewards = proof.total_rewards.saturating_add(final_reward);

    // Log data.
    for i in 0..3 {
        boost_rewards[i] = (boost_rewards[i] as u128)
            .checked_mul(final_reward as u128)
            .unwrap()
            .checked_div(reward_pre_penalty as u128)
            .unwrap() as u64;
    }
    MineEvent {
        balance: proof.balance,
        difficulty: difficulty as u64,
        last_hash_at: prev_last_hash_at,
        timing: t.saturating_sub(t_liveness),
        reward: final_reward,
        boost_1: boost_rewards[0],
        boost_2: boost_rewards[1],
        boost_3: boost_rewards[2],
    }
    .log_return();

    Ok(())
}

/// Authenticate the proof account.
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
    let mut curr = 0;
    let num_instructions = read_u16(&mut curr, data)?;
    let pc = curr;

    for i in 0..num_instructions as usize {
        curr = pc + i * 2;
        curr = read_u16(&mut curr, data)? as usize;

        let num_accounts = read_u16(&mut curr, data)? as usize;
        curr += num_accounts * 33;

        let program_id = read_pubkey(&mut curr, data)?;

        if program_id.eq(&NOOP_PROGRAM_ID) {
            curr += 2;
            let address = read_pubkey(&mut curr, data)?;
            return Ok(Some(address));
        }
    }

    Ok(None)
}
