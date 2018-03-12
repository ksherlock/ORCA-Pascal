{$optimize 7}
{---------------------------------------------------------------}
{                                                               }
{  DAG Creation							}
{                                                               }
{  Places intermediate codes into DAGs and trees.		}
{                                                               }
{---------------------------------------------------------------}

unit DAG;

interface

{$segment 'cg'}

{$LibPrefix '0/obj/'}

uses PCommon, CGI, CGC, Gen;

{---------------------------------------------------------------}

procedure DAG (code: icptr);

{ place an op code in a DAG or tree				}
{                                                               }
{ parameters:                                                   }
{       code - opcode						}

{---------------------------------------------------------------}

implementation

const
   peepSpinRate = 20;			{PeepHoleOptimize spin rate}

var
   c_ind: iclist;			{vars that can be changed by indirect stores}
   maxLoc: integer;			{max local label number used by compiler}
   memberOp: icptr;			{operation found by Member}
   peepSpin: 0..peepSpinRate;		{spinner delay for PeepHoleOptimize}
   peepTablesInitialized: boolean;	{have the peephole tables been initialized?}
   prsFound: boolean;			{are there any pc_prs opcodes?}
   rescan: boolean;			{redo the optimization pass?}

{-- External unsigned math routines ----------------------------}

function udiv (x,y: longint): longint; extern;

function umod (x,y: longint): longint; extern;

function umul (x,y: longint): longint; extern;


{---------------------------------------------------------------}

procedure DAG {code: icptr};

{ place an op code in a DAG or tree				}
{                                                               }
{ parameters:                                                   }
{       code - opcode						}

var
   temp: icptr;				{temp node}


   procedure Generate;

   { generate the code for the current procedure		}

   var
      op: icptr;			{temp opcode pointers}


      procedure BasicBlocks;

      { Break the code up into basic blocks			}

      var
         blast: blockPtr;		{last block pointer}
         bp: blockPtr;			{current block pointer}
         cb: icptr;			{last code in block pointer}
         cp: icptr;			{current code pointer}

      begin {BasicBlocks}
      cp := DAGhead;
      DAGblocks := nil;
      if cp <> nil then begin
         bp := pointer(Calloc(sizeof(block)));
         DAGblocks := bp;
         blast := bp;
         bp^.code := cp;
         cb := cp;
         cp := cp^.next;
         cb^.next := nil;
         while cp <> nil do
					{labels start a new block}
            if cp^.opcode = dc_lab then begin
               Spin;
               bp := pointer(Calloc(sizeof(block)));
               bp^.last := blast;
               blast^.next := bp;
               blast := bp;
               bp^.code := cp;
               cb := cp;
               cp := cp^.next;
               cb^.next := nil;
               end {if}
					{conditionals are followed by a new block}
            else if cp^.opcode in [pc_fjp, pc_tjp, pc_ujp, pc_ret, pc_xjp] then
               begin
               Spin;
               while cp^.next^.opcode = pc_add do begin
                  cb^.next := cp;
        	  cb := cp;
        	  cp := cp^.next;
        	  cb^.next := nil;
                  end; {while}
               cb^.next := cp;
               cb := cp;
               cp := cp^.next;
               cb^.next := nil;
               bp := pointer(Calloc(sizeof(block)));
               bp^.last := blast;
               blast^.next := bp;
               blast := bp;
               bp^.code := cp;
               cb := cp;
               cp := cp^.next;
               cb^.next := nil;
               end {else if}
            else begin			{all other statements get added to a block}
               cb^.next := cp;
               cb := cp;
               cp := cp^.next;
               cb^.next := nil;
               end; {else}
         end; {if}
      end; {BasicBlocks}


   begin {Generate}             
   BasicBlocks;				{build the basic blocks}
   Gen(DAGblocks);			{generate native code}
   DAGhead := nil;			{reset the DAG pointers}
   end; {Generate}


   procedure Push (code: icptr);

   { place a node on the operation stack			}
   {								}
   { parameters:						}
   {    code - node						}

   begin {Push}
   code^.next := DAGhead;
   DAGhead := code;
   end; {Push}


   function Pop: icptr;

   { pop a node from the operation stack			}
   {								}
   { returns: node pointer or nil				}

   var
      node: icptr;			{node poped}
      tn: icptr;			{temp node}

   begin {Pop}
   node := DAGhead;
   if node = nil then
      Error(cge1)
   else begin
      DAGhead := node^.next;
      node^.next := nil;
      end; {else}
   if node^.opcode = dc_loc then begin
      tn := node;
      node := Pop;
      Push(tn);
      end; {if}
   Pop := node;
   end; {Pop}


   procedure Reverse;

   { Reverse the operation stack				}

   var
      list, temp: icptr;		{work pointers}

   begin {Reverse}
   list := nil;
   while DAGhead <> nil do begin
      temp := DAGhead;
      DAGhead := temp^.next;
      temp^.next := list;
      list := temp;
      end; {while}
   DAGhead := list;
   end; {Reverse}


begin {DAG}
case code^.opcode of

   pc_abi, pc_abl, pc_abr, pc_acs, pc_asn, pc_atn,
   pc_bnl, pc_bnt,
   pc_chk, pc_cos, pc_cnv, pc_csp, pc_cum,
   pc_cup, pc_dec, pc_exp, pc_fjp, pc_inc,
   pc_ind, pc_log, pc_ngi, pc_ngl, pc_ngr, pc_not, pc_odd,
   pc_odl, pc_pds, pc_rnd, pc_rn4, pc_sin,
   pc_siz, pc_sqi, pc_sql, pc_sqr, pc_sqt,
   pc_sro, pc_stk, pc_str, pc_tan, pc_tjp, pc_tl1, pc_tl2, pc_vct, pc_xjp:
      begin
      code^.left := Pop;
      Push(code);
      end;

   pc_adi, pc_adl, pc_adr, pc_and, pc_at2,
   pc_bal, pc_blr, pc_blx, pc_bnd, pc_bno, pc_bor, pc_bxr,
   pc_cui, pc_dif, pc_dvi, pc_dvl, pc_dvr, pc_equ,
   pc_geq, pc_grt, pc_inn, pc_int, pc_ior,
   pc_ixa, pc_leq, pc_les, pc_mdl, pc_mod, pc_mov, pc_mpi, pc_mpl, pc_mpr,
   pc_neq, pc_pwr, pc_sbi, pc_sbl, pc_sbr, pc_sgs,
   pc_shl, pc_shr, pc_sll, pc_slr, pc_sto, pc_udi, pc_udl, pc_uim, pc_ulm,
   pc_umi, pc_uml, pc_uni, pc_usr, pc_vsr:
      begin
      code^.right := Pop;
      code^.left := Pop;
      Push(code);
      end;

   dc_dst, dc_glb, dc_lab, dc_pin, dc_sym,
   pc_add, pc_ent, pc_fix, pc_lad, pc_lao, pc_lca, pc_lda, pc_ldc, pc_ldo,
   pc_lla, pc_lnm, pc_lod, pc_lsl, pc_nam, pc_nop, pc_ret, pc_ujp:
      Push(code);

   pc_prs:
      begin
      Push(code);
      prsFound := true;
      end;

   pc_cnn:
      begin
      code^.opcode := pc_cnv;
      temp := Pop;
      code^.left := Pop;
      Push(code);
      Push(temp);
      end;

   dc_fun, dc_loc: begin
      Push(code);
      if code^.r > maxLoc then
         maxLoc := code^.r;
      end;

   dc_prm: begin
      Push(code);
      if code^.s > maxLoc then
         maxLoc := code^.s;
      end;

   dc_str: begin
      Push(code);
      maxLoc := 0;
      prsFound := false;
      end;

   dc_enp: begin
      Push(code);
      Reverse;
      Generate;
      end;

   otherwise:
      Error(cge1);			{invalid opcode}
   end; {case}
end; {DAG}

end.

{$append 'dag.asm'}
