signature ASYMPTOTIC_BASIS = sig

type basis_info = {wf_thm : thm, head : term}
type basis_ln_info = {ln_thm : thm, trimmed_thm : thm}
datatype basis' = SSng of basis_info | SCons of (basis_info * basis_ln_info * basis')
datatype basis = SEmpty | SNE of basis'
type lifting = thm

exception BASIS of string * basis

val basis_size' : basis' -> int
val basis_size : basis -> int
val tl_basis' : basis' -> basis
val tl_basis : basis -> basis
val get_basis_wf_thm' : basis' -> thm
val get_basis_wf_thm : basis -> thm
val get_ln_info : basis -> basis_ln_info option
val get_basis_head' : basis' -> term
val get_basis_head : basis -> term
val split_basis' : basis' -> basis_info * basis_ln_info option * basis
val split_basis : basis -> (basis_info * basis_ln_info option * basis) option
val get_basis_list' : basis' -> term list
val get_basis_list : basis -> term list
val get_basis_term : basis -> term
val extract_basis_list : thm -> term list

val basis_eq' : basis' -> basis' -> bool
val basis_eq : basis -> basis -> bool

val mk_expansion_level_eq_thm' : basis' -> thm
val mk_expansion_level_eq_thm : basis -> thm

val check_basis' : basis' -> basis'
val check_basis : basis -> basis

val combine_lifts : lifting -> lifting -> lifting
val mk_lifting : term list -> basis -> lifting
val lift_expands_to_thm : lifting -> thm -> thm
val lift_trimmed_thm : lifting -> thm -> thm
val lift_trimmed_pos_thm : lifting -> thm -> thm
val lift : basis -> thm -> thm

val lift_modification' : basis' -> basis' -> basis'
val lift_modification : basis -> basis -> basis

val insert_ln' : basis' -> basis'
val insert_ln : basis -> basis

val default_basis : basis

end

structure Asymptotic_Basis : ASYMPTOTIC_BASIS = struct

type lifting = thm

val concl_of' = Thm.concl_of #> HOLogic.dest_Trueprop
val dest_fun = dest_comb #> fst
val dest_arg = dest_comb #> snd

type basis_info = {wf_thm : thm, head : term}
type basis_ln_info = {ln_thm : thm, trimmed_thm : thm}

datatype basis' = SSng of basis_info | SCons of (basis_info * basis_ln_info * basis')
datatype basis = SEmpty | SNE of basis'

val basis_size' =
  let
    fun go acc (SSng _) = acc
      | go acc (SCons (_, _, tl)) = go (acc + 1) tl
  in
    go 1
  end

fun basis_size SEmpty = 0
  | basis_size (SNE b) = basis_size' b

fun tl_basis' (SSng _) = SEmpty
  | tl_basis' (SCons (_, _, tl)) = SNE tl

fun tl_basis SEmpty = error "tl_basis"
  | tl_basis (SNE basis) = tl_basis' basis

fun get_basis_wf_thm' (SSng i) = #wf_thm i
  | get_basis_wf_thm' (SCons (i, _, _)) = #wf_thm i

fun get_basis_wf_thm SEmpty = @{thm basis_wf_Nil}
  | get_basis_wf_thm (SNE basis) = get_basis_wf_thm' basis

fun get_ln_info (SNE (SCons (_, info, _))) = SOME info
  | get_ln_info _ = NONE

fun get_basis_head' (SSng i) = #head i
  | get_basis_head' (SCons (i, _, _)) = #head i

fun get_basis_head SEmpty = error "get_basis_head"
  | get_basis_head (SNE basis') = get_basis_head' basis'

fun split_basis' (SSng i) = (i, NONE, SEmpty)
  | split_basis' (SCons (i, ln_thm, tl)) = (i, SOME ln_thm, SNE tl)

fun split_basis SEmpty = NONE
  | split_basis (SNE basis) = SOME (split_basis' basis)

fun get_basis_list' (SSng i) = [#head i]
  | get_basis_list' (SCons (i, _, tl)) = #head i :: get_basis_list' tl

fun get_basis_list SEmpty = []
  | get_basis_list (SNE basis) = get_basis_list' basis

val get_basis_term = HOLogic.mk_list @{typ "real => real"} o get_basis_list

fun extract_basis_list thm =
  let
    val basis =
      case HOLogic.dest_Trueprop (Thm.concl_of thm) of
        Const (@{const_name "is_expansion"}, _) $ _ $ basis => basis
      | Const (@{const_name "expands_to"}, _) $ _ $ _ $ basis => basis
      | Const (@{const_name "basis_wf"}, _) $ basis => basis
      | _ => raise THM ("get_basis", 1, [thm])
  in
    HOLogic.dest_list basis |> map Envir.eta_contract
  end

fun basis_eq' (SSng i) (SSng i') = #head i = #head i'
  | basis_eq' (SCons (i,_,tl)) (SCons (i',_,tl')) = #head i aconv #head i' andalso basis_eq' tl tl'
  | basis_eq' _ _ = false

fun basis_eq SEmpty SEmpty = true
  | basis_eq (SNE x) (SNE y) = basis_eq' x y
  | basis_eq _ _ = false

fun mk_expansion_level_eq_thm' (SSng _) = @{thm expansion_level_eq_Cons[OF expansion_level_eq_Nil]}
  | mk_expansion_level_eq_thm' (SCons (_, _, tl)) = 
      mk_expansion_level_eq_thm' tl RS @{thm expansion_level_eq_Cons}

fun mk_expansion_level_eq_thm SEmpty = @{thm expansion_level_eq_Nil}
  | mk_expansion_level_eq_thm (SNE basis) = mk_expansion_level_eq_thm' basis

fun dest_wf_thm_head thm = thm |> concl_of' |> dest_arg |> dest_fun |> dest_arg

fun abconv (t, t') = Envir.beta_eta_contract t aconv Envir.beta_eta_contract t'

exception BASIS of (string * basis)

fun check_basis' (basis as (SSng {head, wf_thm})) =
      if abconv (dest_wf_thm_head wf_thm, head) then basis 
        else raise BASIS ("Head mismatch", SNE basis)
  | check_basis' (basis' as (SCons ({head, wf_thm}, {ln_thm, trimmed_thm}, basis))) =
  case strip_comb (concl_of' ln_thm) of
    (_, [ln_fun, ln_exp, ln_basis]) =>
      let
        val _ = if abconv (dest_wf_thm_head wf_thm, head) then () else 
          raise BASIS ("Head mismatch", SNE basis')
        val _ = if eq_list abconv (HOLogic.dest_list ln_basis, get_basis_list' basis) 
          then () else raise BASIS ("Incorrect basis in ln_thm", SNE basis')
        val _ = if abconv (ln_fun, @{term "\<lambda>(f::real\<Rightarrow>real) x. ln (f x)"} $ head) then () else
          raise BASIS ("Wrong function in ln_expansion", SNE basis')
        val _ = if abconv (ln_exp, trimmed_thm |> concl_of' |> dest_arg) then () else
          raise BASIS ("Wrong expansion in trimmed_thm", SNE basis')
        val _ = check_basis' basis
      in
        basis'
      end
  | _ => raise BASIS ("Malformed ln_thm", SNE basis')

fun check_basis SEmpty = SEmpty
  | check_basis (SNE basis) = SNE (check_basis' basis)

fun combine_lifts thm1 thm2 = @{thm is_lifting_trans} OF [thm1, thm2]

fun mk_lifting bs basis =
  let
    fun mk_lifting_aux [] basis =
      (case split_basis basis of
         NONE => @{thm is_lifting_id}
       | SOME (_, _, basis') =>
           combine_lifts (mk_lifting_aux [] basis') 
             (get_basis_wf_thm basis RS @{thm is_lifting_lift}))
    | mk_lifting_aux (b :: bs) basis =
        (case split_basis basis of
           NONE => raise Match
         | SOME ({head = b', ...}, _, basis') =>
             if b aconv b' then
               if eq_list (op aconv) (get_basis_list basis', bs) then
                 @{thm is_lifting_id}
               else
                 @{thm is_lifting_map} OF
                   [mk_lifting_aux bs basis', mk_expansion_level_eq_thm basis']
             else
               combine_lifts (mk_lifting_aux (b :: bs) basis')
                 (get_basis_wf_thm basis RS @{thm is_lifting_lift}))
    val bs' = get_basis_list basis
    fun err () = raise TERM ("mk_lifting", map (HOLogic.mk_list @{typ "real => real"}) [bs, bs'])
  in
    if subset (op aconv) (bs, bs') then
      mk_lifting_aux bs basis handle Match => err ()
    else
      err ()
  end

fun lift_expands_to_thm lifting thm = @{thm expands_to_lift} OF [lifting, thm]
fun lift_trimmed_thm lifting thm = @{thm trimmed_lifting} OF [lifting, thm]
fun lift_trimmed_pos_thm lifting thm = @{thm trimmed_pos_lifting} OF [lifting, thm]
fun apply_lifting lifting thm = @{thm expands_to_lift} OF [lifting, thm]
fun lift basis thm = apply_lifting (mk_lifting (extract_basis_list thm) basis) thm

fun lift_modification' (SSng s) _ = raise BASIS ("lift_modification", SNE (SSng s))
  | lift_modification' (SCons ({wf_thm, head}, {ln_thm, trimmed_thm}, _)) new_tail =
      let
        val wf_thm' = @{thm basis_wf_lift_modification} OF [wf_thm, get_basis_wf_thm' new_tail]
        val lifting = mk_lifting (extract_basis_list ln_thm) (SNE new_tail)
        val ln_thm' = apply_lifting lifting ln_thm
        val trimmed_thm' = lift_trimmed_pos_thm lifting trimmed_thm
      in
        SCons ({wf_thm = wf_thm', head = head},
          {ln_thm = ln_thm', trimmed_thm = trimmed_thm'}, new_tail)
      end

fun lift_modification (SNE basis) (SNE new_tail) = SNE (lift_modification' basis new_tail)
  | lift_modification _ _ = raise BASIS ("lift_modification", SEmpty)

fun insert_ln' (SSng {wf_thm, head}) = 
      let
        val head' = Envir.eta_contract
          (Abs ("x", @{typ real}, @{term "ln :: real \<Rightarrow> real"} $ (betapply (head, Bound 0))))
        val info1 = {wf_thm = wf_thm RS @{thm basis_wf_insert_ln(2)}, head = head}
        val info2 = {wf_thm = wf_thm RS @{thm basis_wf_insert_ln(1)}, head = head'}
        val ln_thm = wf_thm RS @{thm expands_to_insert_ln}
        val trimmed_thm = wf_thm RS @{thm trimmed_pos_insert_ln}
      in 
       SCons (info1, {ln_thm = ln_thm, trimmed_thm = trimmed_thm}, SSng info2)
      end
  | insert_ln' (basis as (SCons (_, _, tail))) = lift_modification' basis (insert_ln' tail)

fun insert_ln SEmpty = raise BASIS ("Empty basis", SEmpty)
  | insert_ln (SNE basis) = check_basis (SNE (insert_ln' basis))

val default_basis = 
  SNE (SSng {head = @{term "\<lambda>x::real. x"}, wf_thm = @{thm default_basis_wf}})

end