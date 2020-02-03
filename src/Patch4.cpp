#include "StdAfx.h"
#include "Patch.h"
#include "Helper.h"

#include <capstone/capstone.h>
#include <keystone/keystone.h>

DECLARE_TRAIT(cs_insn, cs_free, 1);

typedef struct
{
    uint64_t rip;
    const uint8_t* ptr; // addr of code
    size_t size;
    x86_reg reg_index;
    x86_reg reg_value;

} cs_ctx;

bool CheckMatch_amd64(CPatch *p, csh h, cs_ctx& ctx)
{
    CHelpPtr<cs_insn> insn = cs_malloc(h);
    int step = 0;
    while (cs_disasm_iter(h, &ctx.ptr, &ctx.size, &ctx.rip, insn))
    {
        ATLTRACE(_T("%hs %hs\n"), insn->mnemonic, insn->op_str);
        switch (++step)
        {
        case 7:
            if (_stricmp(insn->mnemonic, "movzx") == 0 &&
                insn->detail->x86.op_count == 2 &&
                insn->detail->x86.operands[0].type == X86_OP_REG &&
                insn->detail->x86.operands[1].type == X86_OP_MEM &&
                insn->detail->x86.operands[1].size == 1 &&
                insn->detail->x86.operands[1].mem.scale == 1)
            {
                ctx.reg_index = insn->detail->x86.operands[1].mem.index;
                break;
            }
            else
            {
                return false;
            }
        case 10:
            //
            // The previous instruction of "call sub_1806E65F0" should set RCX register.
            //
            return (_stricmp(insn->mnemonic, "mov") == 0 &&
                insn->detail->x86.op_count >= 1 &&
                insn->detail->x86.operands[0].type == X86_OP_REG &&
                insn->detail->x86.operands[0].reg == X86_REG_RCX);
        }
    }
    return false;
}

bool CheckMatch_x86(CPatch *p, csh h, cs_ctx& ctx)
{
    CHelpPtr<cs_insn> insn = cs_malloc(h);
    int step = 0;
    while (cs_disasm_iter(h, &ctx.ptr, &ctx.size, &ctx.rip, insn))
    {
        ATLTRACE(_T("%hs %hs\n"), insn->mnemonic, insn->op_str);
        switch (++step)
        {
        case 7:
            if (_stricmp(insn->mnemonic, "mov") == 0 &&
                insn->detail->x86.op_count == 2 &&
                insn->detail->x86.operands[0].type == X86_OP_REG &&
                insn->detail->x86.operands[1].type == X86_OP_MEM &&
                insn->detail->x86.operands[1].size == 1 &&
                insn->detail->x86.operands[1].mem.scale == 1)
            {
                ctx.reg_index = insn->detail->x86.operands[1].mem.index;
                break;
            }
            else
            {
                return false;
            }
        case 8:
            if (_stricmp(insn->mnemonic, "add") == 0 &&
                insn->detail->x86.op_count >= 1 &&
                insn->detail->x86.operands[0].type == X86_OP_REG &&
                insn->detail->x86.operands[0].size == 1)
            {
                ctx.reg_value = insn->detail->x86.operands[0].reg;
                return true;
            }
            return false;
        }
    }
    return false;
}

DECLARE_TRAIT(ks_engine, ks_close);

template <ks_mode mode>
bool GenerateCode(const char* assembly, uint64_t addr, unsigned char * patch, size_t size)
{
    CHelpPtr<ks_engine> ks = NULL;
    size_t code_size, inst_count;
    unsigned char *code = NULL;

    if (ks_open(KS_ARCH_X86, mode, &ks) != KS_ERR_OK) return false;
    if (ks_asm(ks, assembly, addr, &code, &code_size, &inst_count) != KS_ERR_OK) return false;

    if (code_size > size) return false;
    memcpy(patch, code, code_size);
    if (code_size < size) memset(patch + code_size, 0x90, size - code_size);
    ks_free(code);
    return true;
}

HRESULT CPatch::Patch4(LPCSTR pData, int nLen)
{
    PIMAGE_SECTION_HEADER pText = Section(".text");
    if (!pText) return ERROR_BAD_EXE_FORMAT;

    CHeapPtr<CHAR> pKey;
    PBYTE pRawText = pView + pText->PointerToRawData;

    pKey.Allocate(nLen);
    int nKey = TrimKey(pData, pKey, nLen);
    DWORD pPatch = Reserved(nKey);

    DWORD uCode = 0;
    if (pINH->FileHeader.Machine == IMAGE_FILE_MACHINE_AMD64)
    {
        for (DWORD i = 0; i < pText->SizeOfRawData; ++i)
        {
            PBYTE p = pRawText + i;
            if (p[0] == 0x48 && p[1] == 0x8d &&                     // prefix of "lea       rcx, [rbp+5Fh+var_38]"
                p[4] == 0x48 && p[5] == 0x83 &&                     // prefix of "cmp       [rbp+5Fh+var_20], 10h"
                p[9] == 0x48 && p[10] == 0x0f && p[11] == 0x43 &&   // prefix of "cmovnb    rcx, [rbp+5Fh+var_38]"
                p[14] == 0x48 && p[15] == 0x8d &&                   // prefix of "lea       rax, [rbp+5Fh+var_58]"
                p[18] == 0x48 && p[19] == 0x83 &&                   // prefix of "cmp       [rbp+5Fh+var_40], 10h"
                p[23] == 0x48 && p[24] == 0x0f && p[25] == 0x43 &&  // prefix of "cmovnb    rax, [rbp+5Fh+var_58]"
                p[28] == 0x44 && p[29] == 0x0f && p[30] == 0xb6 &&  // prefix of "movzx     r8d, byte ptr [rax+rdi]"
                p[33] == 0x44 && p[34] == 0x02 &&                   // prefix of "add       r8b, [rcx+rdi]"
                p[37] == 0xba &&                                    // prefix of "mov       edx, 1"
                p[42] == 0x48 && p[43] == 0x8b &&                   // prefix of "mov       rcx, rbx"
                p[45] == 0xe8)                                      // prefix of "call      sub_1806E65F0"
            {
                uCode = i;
                break;
            }
        }
        if (!uCode) return ERROR_NOT_FOUND;

        
        csh h;
        if (cs_open(CS_ARCH_X86, CS_MODE_64, &h) != CS_ERR_OK) return E_FAIL;
        if (cs_option(h, CS_OPT_DETAIL, CS_OPT_ON) != CS_ERR_OK) return E_FAIL;
        // Find patch offset
        cs_ctx ctx = { pText->VirtualAddress + uCode, pRawText + uCode, 45 };
        if (!CheckMatch_amd64(this, h, ctx))
        {
            cs_close(&h);
            return ERROR_NOT_FOUND;
        }
        char assembly[MAX_PATH] = {};
        sprintf_s(assembly, _countof(assembly),
            "lea rax, qword ptr[0x%.16lx];"
            "mov r8b, byte ptr[rax + %s];"
            "mov edx, 1;", pPatch, cs_reg_name(h, ctx.reg_index));
        cs_close(&h);

        // >>>>>>>>>>>> .text:00000001819B02C0 48 8D 4D 27       lea     rcx, [rbp + 5Fh + var_38]
        //              .text:00000001819B02C4 48 83 7D 3F 10    cmp[rbp + 5Fh + var_20], 10h
        //  42 BYTES    .text:00000001819B02C9 48 0F 43 4D 27    cmovnb  rcx, [rbp + 5Fh + var_38]
        //              .text:00000001819B02CE 48 8D 45 07       lea     rax, [rbp + 5Fh + var_58]
        //  THESE CODE  .text:00000001819B02D2 48 83 7D 1F 10    cmp[rbp + 5Fh + var_40], 10h
        //  WILL BE     .text:00000001819B02D7 48 0F 43 45 07    cmovnb  rax, [rbp + 5Fh + var_58]
        //  REPLACED    .text:00000001819B02DC 44 0F B6 04 38    movzx   r8d, byte ptr[rax + rdi]
        //              .text:00000001819B02E1 44 02 04 39       add     r8b, [rcx + rdi]
        // <<<<<<<<<<<< .text:00000001819B02E5 BA 01 00 00 00    mov     edx, 1
        //              .text:00000001819B02EA 48 8B CB          mov     rcx, rbx
        //              .text:00000001819B02ED E8 FE 62 D3 FE    call    sub_1806E65F0
        if (GenerateCode<KS_MODE_64>(assembly, pText->VirtualAddress + uCode, pRawText + uCode, 42))
        {
            // patch public key
            memcpy(RVA(pPatch), pKey, nKey);
        }
    }
    else if (pINH->FileHeader.Machine == IMAGE_FILE_MACHINE_I386)
    {
        for (DWORD i = 0; i < pText->SizeOfRawData; ++i)
        {
            PBYTE p = pRawText + i;
            if (p[0] == 0x83 &&                     // prefix of "cmp     [ebp+var_30], 10h"
                p[4] == 0x8d &&                     // prefix of "lea     ecx, [ebp+Dst]"
                p[7] == 0x8d &&                     // prefix of "lea     eax, [ebp+Memory]"
                p[10] == 0x0f && p[11] == 0x43 &&   // prefix of "cmovnb  ecx, [ebp+Dst]"
                p[14] == 0x83 &&                    // prefix of "cmp     [ebp+var_18], 10h"
                p[18] == 0x0f && p[19] == 0x43 &&   // prefix of "cmovnb  eax, [ebp+Memory]"
                p[22] == 0x8a &&                    // prefix of "mov     dl, [eax+ebx]"
                p[25] == 0x02)                      // prefix of "add     dl, [ecx+ebx]")
            {
                uCode = i;
                break;
            }
        }
        if (!uCode) return ERROR_NOT_FOUND;
        csh h;
        if (cs_open(CS_ARCH_X86, CS_MODE_32, &h) != CS_ERR_OK) return E_FAIL;
        if (cs_option(h, CS_OPT_DETAIL, CS_OPT_ON) != CS_ERR_OK) return E_FAIL;
        // Find patch offset
        cs_ctx ctx = { pText->VirtualAddress + uCode, pRawText + uCode, 28 };
        if (!CheckMatch_x86(this, h, ctx))
        {
            cs_close(&h);
            return ERROR_NOT_FOUND;
        }
        char assembly[MAX_PATH] = {};
        DWORD jump = pText->VirtualAddress + uCode + 5;
        sprintf_s(assembly, _countof(assembly),
            "call 0x%.8x;"
            "pop eax;"
            "add eax, 0x%.8x;"
            "mov %s, byte ptr [eax + %s];",
            jump, pPatch - jump,
            cs_reg_name(h, ctx.reg_value), cs_reg_name(h, ctx.reg_index));
        cs_close(&h);

        // >>>>>>>>>>>> .text:113FE4A0 83 7D D0 10  cmp     [ebp+var_30], 10h
        //   28 BYTES   .text:113FE4A4 8D 4D BC     lea     ecx, [ebp+Dst]
        //              .text:113FE4A7 8D 45 D4     lea     eax, [ebp+Memory]
        //  THESE CODE  .text:113FE4AA 0F 43 4D BC  cmovnb  ecx, [ebp+Dst]
        //  WILL BE     .text:113FE4AE 83 7D E8 10  cmp     [ebp+var_18], 10h
        //  REPLACED    .text:113FE4B2 0F 43 45 D4  cmovnb  eax, [ebp+Memory]
        //              .text:113FE4B6 8A 14 18     mov     dl, [eax+ebx]
        // <<<<<<<<<<<< .text:113FE4B9 02 14 19     add     dl, [ecx+ebx]
        if (GenerateCode<KS_MODE_32>(assembly, pText->VirtualAddress + uCode, pRawText + uCode, 28))
        {
            // patch public key
            memcpy(RVA(pPatch), pKey, nKey);
        }
    }
    else
    {
        return E_NOTIMPL;
    }
    return S_OK;
}