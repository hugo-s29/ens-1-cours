def max_matching_substrings(n, k, a, b):
    mismatch_indices = []

    # Find positions where a and b differ
    for i in range(n):
        if a[i] != b[i]:
            mismatch_indices.append(i)

    # If no mismatches, return max possible substring pairs
    if not mismatch_indices:
        return (n * (n + 1)) // 2

    left = 0
    max_match_length = 0
    unique_chars = set()

    for right in range(len(mismatch_indices)):
        unique_chars.add(a[mismatch_indices[right]])

        while len(unique_chars) > k:
            unique_chars.discard(a[mismatch_indices[left]])
            left += 1

        max_match_length = max(max_match_length, mismatch_indices[right] - mismatch_indices[left] + 1)

    total_matching = 0
    current_match_length = 0

    for i in range(n):
        if a[i] == b[i]:
            current_match_length += 1
        else:
            current_match_length = 0

        total_matching += current_match_length

    return total_matching + (max_match_length * (max_match_length + 1)) // 2

print(max_matching_substrings(4, 1, "abcd", "axcb"))
