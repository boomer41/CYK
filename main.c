/*
 * Program for checking hardcoded chomsky grammar with the CYK algorithm
 *
 * Copyright (c) 2017 Stephan Brunner <s.brunner@stephan-brunner.net>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdbool.h>

typedef char alpha_t;

typedef struct table_entry {
    struct table_entry *pNext;

    alpha_t entry_value;
} table_entry_t;

typedef struct {
    alpha_t non_terminal;
    alpha_t *pTerminals;
    bool single_char;
} grammar_entry_t;
typedef struct {
    size_t grammar_size;
    grammar_entry_t *grammar_entries;
} grammar_t;

#define GRAMMAR_ENTRY(pGrammarEntries, idx, _non_terminal, terminalList) { \
    const int _idx = (idx); /* To be able to use idx++ */ \
    (pGrammarEntries)[_idx].non_terminal = _non_terminal; \
    (pGrammarEntries)[_idx].pTerminals = malloc(sizeof(alpha_t) * strlen(terminalList) + 1); \
    assert((pGrammarEntries)[_idx].pTerminals != NULL); \
    strcpy((pGrammarEntries)[_idx].pTerminals, terminalList); \
    (pGrammarEntries)[_idx].single_char = strlen(terminalList) == 1; \
}

// This is index-1 based!
#define TABLE_IDX(word_len, sub_len, offset) \
    ((sub_len) - 1 + (((offset) - 1) * (word_len)))

// Define own grammar here.
static grammar_t *grammar_init() {
    const int grammar_size = 9;

    grammar_entry_t *pEntries = malloc(sizeof(grammar_entry_t) * grammar_size);
    int i = 0;
    GRAMMAR_ENTRY(pEntries, i++, 'S', "AB");
    GRAMMAR_ENTRY(pEntries, i++, 'A', "CD");
    GRAMMAR_ENTRY(pEntries, i++, 'A', "CF");
    GRAMMAR_ENTRY(pEntries, i++, 'B', "c");
    GRAMMAR_ENTRY(pEntries, i++, 'B', "EB");
    GRAMMAR_ENTRY(pEntries, i++, 'C', "a");
    GRAMMAR_ENTRY(pEntries, i++, 'D', "b");
    GRAMMAR_ENTRY(pEntries, i++, 'E', "c");
    GRAMMAR_ENTRY(pEntries, i++, 'F', "AD");

    /* Omit validation for chomsky normal form */

    grammar_t *pGrammar = malloc(sizeof(grammar_t));
    assert(pGrammar != NULL);

    pGrammar->grammar_entries = pEntries;
    pGrammar->grammar_size = grammar_size;

    return pGrammar;
}

static void grammar_destroy(grammar_t *pGrammar) {
    for (size_t i = 0; i < pGrammar->grammar_size; i++) {
        free(pGrammar->grammar_entries[i].pTerminals);
    }
    free(pGrammar->grammar_entries);
    free(pGrammar);
}

static void table_init(table_entry_t **pTable, size_t len) {
    for (size_t i = 0; i < len; i++) {
        pTable[i] = NULL;
    }
}

static void table_destroy(table_entry_t **pTable, size_t len) {
    for (size_t i = 0; i < len; i++) {
        table_entry_t* pEntry = pTable[i];
        while (pEntry != NULL) {
            table_entry_t* pTemp = pEntry->pNext;
            free(pEntry);
            pEntry = pTemp;
        }
    }
}

static table_entry_t *table_new_entry(alpha_t alpha_val) {
    table_entry_t *pNew = malloc(sizeof(table_entry_t));
    assert(pNew != NULL);
    pNew->pNext = NULL;
    pNew->entry_value = alpha_val;
    return pNew;
}

static bool table_char_exists(const table_entry_t *pEntry, const alpha_t alpha) {
    while (pEntry != NULL) {
        if (pEntry->entry_value == alpha) {
            return true;
        }
        pEntry = pEntry->pNext;
    }
    return false;
}

static void table_push_back(table_entry_t **pTable, size_t tableIdx, const alpha_t alpha) {
    table_entry_t *pEntry = pTable[tableIdx];
    table_entry_t **pDestination = NULL;
    if (pEntry == NULL) {
        pDestination = pTable + tableIdx;
    } else {
        while (pEntry != NULL) {
            pDestination = &pEntry->pNext;
            pEntry = pEntry->pNext;
        }
    }
    assert(pDestination != NULL);

    *pDestination = table_new_entry(alpha);
}

static bool cyk(const grammar_t *pGrammar, const alpha_t *pWord) {
    const size_t word_len = strlen(pWord);
    const size_t arr_size = word_len * word_len;

    table_entry_t **pTable = malloc(sizeof(table_entry_t*) * arr_size);
    assert(pTable != NULL);
    table_init(pTable, arr_size);

    for (size_t i = 1; i <= word_len; i++) {
        for (size_t ruleIdx = 0; ruleIdx < pGrammar->grammar_size; ruleIdx++) {
            grammar_entry_t *pRule = pGrammar->grammar_entries + ruleIdx;
            if (!pRule->single_char || pRule->pTerminals[0] != pWord[i - 1]) { // i is 1-based
                continue;
            }
            table_push_back(pTable, TABLE_IDX(word_len, 1, i), pRule->non_terminal);
        }
    }

    for (size_t j = 2; j <= word_len; j++) {
        for (size_t i = 1; i <= word_len - j + 1; i++) {
            for (size_t k = 1; k <= j - 1; k++) {
                for (size_t ruleIdx = 0; ruleIdx < pGrammar->grammar_size; ruleIdx++) {
                    grammar_entry_t *pRule = pGrammar->grammar_entries + ruleIdx;
                    if (pRule->single_char) {
                        continue;
                    }

                    alpha_t c1, c2;
                    c1 = pRule->pTerminals[0];
                    c2 = pRule->pTerminals[1];

                    if (table_char_exists(pTable[TABLE_IDX(word_len, k, i)], c1) &&
                        table_char_exists(pTable[TABLE_IDX(word_len, j - k, i + k)], c2)) {
                        table_push_back(pTable, TABLE_IDX(word_len, j, i), pRule->non_terminal);
                    }
                }
            }
        }
    }

    bool retVal = false;
    table_entry_t *pFinal = pTable[TABLE_IDX(word_len, word_len, 1)];
    while (pFinal != NULL) {
        if (pFinal->entry_value == 'S') {
            retVal = true;
            break;
        }
        pFinal = pFinal->pNext;
    }

    table_destroy(pTable, arr_size);
    free(pTable);

    return retVal;
}

int main() {
    grammar_t *pGrammar = grammar_init();

    printf("Please enter the word: ");

    size_t word_len = 0;
    size_t arr_len = 16;
    alpha_t *pWord = malloc(sizeof(alpha_t) * arr_len);
    assert(pWord != NULL);

    int c;
    while ((c = getc(stdin)) != EOF) {
        if (c == '\n' || c == '\r') {
            break;
        }
        // +2 because we need the new char and the null-terminator, which is never included in word_len
        if (word_len + 2 > arr_len) {
            alpha_t *pNew = realloc(pWord, arr_len * 2);
            assert(pNew != NULL);
            pWord = pNew;
            arr_len *= 2;
        }
        pWord[word_len++] = (char) c;
    }
    pWord[word_len] = '\0';

    printf("You entered \"%s\" with a length of %ld!\n", pWord, strlen(pWord));

    bool cykResult = cyk(pGrammar, pWord);
    printf("Word is valid: %s\n", cykResult ? "true" : "false");

    free(pWord);
    grammar_destroy(pGrammar);

    return cykResult ? EXIT_SUCCESS : EXIT_FAILURE;
}