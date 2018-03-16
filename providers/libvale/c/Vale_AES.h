/* MIT License
 *
 * Copyright (c) 2016-2018 INRIA and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

#ifndef __Vale_AES_H
#define __Vale_AES_H

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

#ifdef _WIN32
#define STDCALL __attribute__((stdcall))
#else
#define STDCALL
#endif

extern void STDCALL KeyExpansionStdcall(const void *key_ptr, void *expanded_key_ptr, void *placeholder);
extern void STDCALL AES128EncryptOneBlockStdcall(void *output_ptr, const void *input_ptr, const void *expanded_key_ptr, void *placeholder);

void Vale_AES_keyExpansion(uint8_t *k, uint8_t *w, uint8_t *sb);

void Vale_AES_cipher(uint8_t *out, uint8_t *in, uint8_t *w, uint8_t *sb);

#endif
