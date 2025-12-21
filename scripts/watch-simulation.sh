#!/bin/bash
# Watch simulation metrics from remote server

HOST="${1:-ubuntu-64@orb}"
PORT="${2:-9090}"

clear_screen() {
    printf "\033[H\033[2J"
}

format_number() {
    printf "%'d" "$1" 2>/dev/null || echo "$1"
}

while true; do
    clear_screen
    
    metrics=$(ssh -o ConnectTimeout=2 "$HOST" "curl -s http://localhost:$PORT/metrics" 2>/dev/null)
    
    if [ -z "$metrics" ]; then
        echo "Cannot connect to $HOST:$PORT"
        sleep 5
        continue
    fi
    
    # Parse metrics
    ops_total=$(echo "$metrics" | grep "^ubt_sim_operations_total " | awk '{print $2}')
    ops_sec=$(echo "$metrics" | grep "^ubt_sim_operations_per_second " | awk '{printf "%.0f", $2}')
    seeds_done=$(echo "$metrics" | grep "^ubt_sim_seeds_completed " | awk '{print $2}')
    seeds_fail=$(echo "$metrics" | grep "^ubt_sim_seeds_failed " | awk '{print $2}')
    seeds_total=$(echo "$metrics" | grep "^ubt_sim_seeds_total " | awk '{print $2}')
    progress=$(echo "$metrics" | grep "^ubt_sim_progress_percent " | awk '{printf "%.2f", $2}')
    uptime=$(echo "$metrics" | grep "^ubt_sim_uptime_seconds " | awk '{printf "%.0f", $2}')
    workers=$(echo "$metrics" | grep "^ubt_sim_active_workers " | awk '{print $2}')
    chaos_total=$(echo "$metrics" | grep "^ubt_sim_chaos_ops_total " | awk '{print $2}')
    
    # Chaos ops breakdown
    chaos_toggle=$(echo "$metrics" | grep "^ubt_sim_chaos_toggle_incremental_total " | awk '{print $2}')
    chaos_verify=$(echo "$metrics" | grep "^ubt_sim_chaos_verify_incremental_vs_full_total " | awk '{print $2}')
    chaos_clear=$(echo "$metrics" | grep "^ubt_sim_chaos_clear_caches_total " | awk '{print $2}')
    chaos_burst=$(echo "$metrics" | grep "^ubt_sim_chaos_burst_stem_write_total " | awk '{print $2}')
    chaos_storm=$(echo "$metrics" | grep "^ubt_sim_chaos_insert_delete_storm_total " | awk '{print $2}')
    chaos_root=$(echo "$metrics" | grep "^ubt_sim_chaos_root_stability_total " | awk '{print $2}')
    chaos_del=$(echo "$metrics" | grep "^ubt_sim_chaos_delete_stem_total " | awk '{print $2}')
    chaos_scan=$(echo "$metrics" | grep "^ubt_sim_chaos_get_scan_consistency_total " | awk '{print $2}')
    chaos_switch=$(echo "$metrics" | grep "^ubt_sim_chaos_mode_switch_storm_total " | awk '{print $2}')
    chaos_last=$(echo "$metrics" | grep "^ubt_sim_chaos_verify_last_root_total " | awk '{print $2}')
    
    # Regular ops
    op_insert=$(echo "$metrics" | grep "^ubt_sim_op_insert_total " | awk '{print $2}')
    op_get=$(echo "$metrics" | grep "^ubt_sim_op_get_total " | awk '{print $2}')
    op_delete=$(echo "$metrics" | grep "^ubt_sim_op_delete_total " | awk '{print $2}')
    op_sync=$(echo "$metrics" | grep "^ubt_sim_op_sync_total " | awk '{print $2}')
    
    # Calculate ETA
    if [ "$ops_sec" -gt 0 ] && [ "$seeds_total" -gt 0 ]; then
        remaining=$((seeds_total - seeds_done))
        ops_remaining=$((remaining * 1000))
        eta_sec=$((ops_remaining / ops_sec))
        eta_min=$((eta_sec / 60))
        eta_hr=$((eta_min / 60))
        eta_min=$((eta_min % 60))
    else
        eta_hr=0
        eta_min=0
    fi
    
    # Format uptime
    up_hr=$((uptime / 3600))
    up_min=$(((uptime % 3600) / 60))
    up_sec=$((uptime % 60))
    
    # Build progress bar
    bar_width=50
    filled=$((progress * bar_width / 100))
    empty=$((bar_width - filled))
    bar=$(printf "%${filled}s" | tr ' ' '#')
    bar="${bar}$(printf "%${empty}s" | tr ' ' '-')"
    
    # Display
    echo "=============================================================="
    echo "           UBT SIMULATION TESTING - LIVE DASHBOARD            "
    echo "=============================================================="
    echo ""
    echo "  Progress: [${bar}] ${progress}%"
    echo ""
    echo "  +------------------+------------------+------------------+"
    echo "  |    OPERATIONS    |      SEEDS       |      STATUS      |"
    echo "  +------------------+------------------+------------------+"
    printf "  | Total: %9s | Done: %9s | Workers: %7s |\n" "$(format_number ${ops_total:-0})" "$(format_number ${seeds_done:-0})" "${workers:-0}"
    printf "  | Rate: %7s/s | Fail: %9s | Uptime: %02d:%02d:%02d |\n" "$(format_number ${ops_sec:-0})" "${seeds_fail:-0}" "$up_hr" "$up_min" "$up_sec"
    printf "  | Chaos: %8s | Total: %8s | ETA: %02dh %02dm     |\n" "$(format_number ${chaos_total:-0})" "$(format_number ${seeds_total:-0})" "$eta_hr" "$eta_min"
    echo "  +------------------+------------------+------------------+"
    echo ""
    echo "  CHAOS OPERATIONS (BUGGIFY):"
    echo "  +----------------------------+-------------+"
    printf "  | Toggle Incremental Mode    | %11s |\n" "$(format_number ${chaos_toggle:-0})"
    printf "  | Verify Incr vs Full        | %11s |\n" "$(format_number ${chaos_verify:-0})"
    printf "  | Clear Caches               | %11s |\n" "$(format_number ${chaos_clear:-0})"
    printf "  | Burst Stem Write           | %11s |\n" "$(format_number ${chaos_burst:-0})"
    printf "  | Insert/Delete Storm        | %11s |\n" "$(format_number ${chaos_storm:-0})"
    printf "  | Root Stability Check       | %11s |\n" "$(format_number ${chaos_root:-0})"
    printf "  | Delete Entire Stem         | %11s |\n" "$(format_number ${chaos_del:-0})"
    printf "  | Get/Scan Consistency       | %11s |\n" "$(format_number ${chaos_scan:-0})"
    printf "  | Mode Switch Storm          | %11s |\n" "$(format_number ${chaos_switch:-0})"
    printf "  | Verify Last Root           | %11s |\n" "$(format_number ${chaos_last:-0})"
    echo "  +----------------------------+-------------+"
    echo ""
    echo "  REGULAR OPERATIONS:"
    printf "    Insert: %-10s  Get: %-10s  Delete: %-10s  Sync: %-10s\n" \
        "$(format_number ${op_insert:-0})" \
        "$(format_number ${op_get:-0})" \
        "$(format_number ${op_delete:-0})" \
        "$(format_number ${op_sync:-0})"
    echo ""
    echo "  Press Ctrl+C to exit"
    echo "=============================================================="
    
    sleep 2
done
