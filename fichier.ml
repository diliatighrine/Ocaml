(*type 'a label_exparith = L_var of 'a | L_Cste of int | L_Plus | L_Mult | L_Div
 * | L_opp;;
 *
 *  type 'a btree =
         *     | Empty 
         *        | Node of 'a * ('a btree) * ('a btree) ;;
         *
         *         type 'a exparith_tree = ('a label_exparith) btree ;;
         *         (*AST*)
          let e = Node(L_Mult,Node(L_Plus,Node(L_Cste
          2,Empty,Empty),Node(L_opp,Node(L_var
          "x",Empty,Empty),Empty)),Node(L_var "y",Empty,Empty));;

          (*verification qu'un arbre binaire represente une expression
           * arithmetique *)

           let rec wellformed(e: 'a exparith_tree) : bool =
                      match e with
                         |Empty -> false
                            |Node(e,g,d)-> 
                                                   match e with 
                                                          |L_var(x)->g=Empty &&
                                                          d=Empty 
                                                                 |L_Cste(k)->g=Empty
                                                                 && d=Empty
                                                                        |L_opp->wellformed
                                                                        g &&
                                                                        d=Empty
                                                                               |_
                                                                               ->wellformed
                                                                               g
                                                                               &&
                                                                               wellformed
                                                                               d
          ;;

          (*exprimer directement ces contraintes dans la definition du type des
           * arbres representant des expressions arithmetiques :*)

          (*def d'un type specifique pour les AST *)

           type 'a exparith = 
                      |Var of 'a 
                         |Cste of int 
                            |Opp of 'a exparith
                               |Plus of 'a exparith * 'a exparith
                                  |Mult of 'a exparith * 'a exparith 
                                     |Div of 'a exparith * 'a exparith;; 


           let ex =
                      Mult(Plus(Cste 2,Opp(Var "x")),Var "y");;

           (* val ex : string exparith =....*)



           (*nombre d'occurrences de symboles de variable dans une expression
            * arithmetique *)

            let rec nb_var(e: 'a exparith) : int =
                      
                       match e with 
                          | Var x -> 1 
                             | Cste k -> 0
                                | Opp e0 -> nb_var e0 
                                   |Plus (e1,e2)->(nb_var e1) + (nb_var e2)
   |Mult (e1 , e2)->(nb_var e1) + (nb_var e2)
   |Div (e1,e2)-> (nb_var e1) + (nb_var e2);;


            nb_var ex ;;


           (*evaluation d'une expression arithmetique *)

            let envxy = [("x",2);("y",5)];;

             let rec eval_e (env : ('a*int) list ) (e : 'a exparith) : int=
                        match e with
                           |Var x -> List.assoc x env 
                              |Cste n -> n 
                                 |Opp e0 -> - (eval_e env e0)
   |Plus(e1,e2)->(eval_e env e1) + (eval_e env e2) 
   |Mult (e1,e2)->(eval_e env e1) * (eval_e env e2) 
   |Div (e1,e2)->(eval_e env e1 ) / (eval_e env e2);;

              eval_e envxy ex;;



             (*le cas ou la variable nest pas dans la liste des associations *)

              let eval_var (env : (string*int) list ) (x : string) : int=
                         try List.assoc x env with
                            |Not_found -> raise (Invalid_argument (x ^ "
                            indefini"));;


               let rec eval_invalid(env : ('a *int) list ) (e : 'a exparith) :
                       int= 
                                  match e with 
                                     |Var x -> eval_var env x 
                                        |Cste k -> k 
                                           |Opp e0 -> - (eval_invalid env e0)
   |Plus (e1,e2)-> (eval_invalid env e1) + (eval_invalid env e2)
   |Mult (e1,e2)-> (eval_invalid env e1) * (eval_invalid env e2) 
   |Div (e1,e2)-> (eval_invalid env e1) / (eval_invalid env e2);;

                (eval_invalid envxy (Plus(Var("x"),Var("z"))));;

               (*Arbres generaux *)


                type 'a gtree= GNode of 'a * (('a gtree) list) ;;

                 let gt =
                         GNode(5,[GNode(3,[GNode(9,[]);GNode(1,[])]);GNode(2,[]);GNode(4,[GNode(7,[]);GNode(6,[]);GNode(8,[]);GNode(0,[])])]);;

                   

                 (*recherche d'un element dans un arbre general *)
                 (*definition mutuellement recursive *)


                  let rec gtree_mem (x : 'a ) (t: 'a gtree) : bool= 
                             match t with
                                |GNode(e,lt)-> x=e || forest_mem x lt 
                                 and forest_mem (x : 'a) (f : ('a gtree) list )
: bool = 
           match f with 
              | [] ->false 
                 |hf :: tf -> gtree_mem x hf || forest_mem x tf ;;

                   type 'a formul = 
                              |Prop of 'a 
                                 |Vrai
                                    |Faux
                                       |Non of 'a formul 
                                          |Et of 'a formul * 'a formul 
                                             |Ou of 'a formul * 'a formul 
                                                |Impl of 'a formul * 'a formul
                   ;;


                    let f = Impl (Et (Non (Prop 'p'),Prop 'q') , Ou(Prop 'r' ,
                    Prop 's' ));;

                    (*evaluation d'une formule de la logique propositionnelle *)

                     let envpqrs =
                             [('p',true);('q',false);('r',true);('s',false)];;


                      let rec eval_f (env : ('a * bool) list ) (f: 'a formul) :
                              bool=
                                         match f with
                                            |Prop p -> List.assoc p env
                                               |Vrai-> true
                                                  |Faux->false
                                                     |Non f0-> not eval_f env f0
                                                        |Et (f1,f2)->(eval_f env
                                                        f1) && (eval_f env f2)
   |Ou (f1,f2)->(eval_f env f1) || (eval_f env f2)
   |Impl (f1,f2)->not (eval_f env f1) || (eval_f env f2);;*)

(* TD 5 : arbres de huffman  *)

type 'a htree=
          |Leaf of int * 'a 
            |Branch of int * 'a htree * 'a htree ;;





                      let code (m : 'a list ) (c : ('a * (int list)) list) : int
                      list =
                                List.flatten(List.map( fun x -> List.assoc x c)
                                m);;

                        
                      let msgt=[('A', [0]); ('C', [1; 0; 0; 0]); ('G', [1; 0; 0;
                      1]); ('H', [1; 0; 1; 0]);
                                ('F', [1; 0; 1; 1]); ('E', [1; 1; 0; 0]); ('D',
                                [1; 1; 0; 1]);
                                          ('B', [1; 1; 1])];;

                      let
                      msg=['A';'A';'B';'A';'C';'B';'A';'G';'H';'A';'A';'F';'E';'A';
                               'D';'B';'A'];;

                      code msg msgt ;;

                      let rec decode1 (l : int list ) (t: 'a htree) : ('a * (int
                      list))= 
                                match l,t with
                                  |l,Leaf (_,c) -> (c,l)
                                    |h::t , Branch (_,g,d) -> if h=0 then
                                            decode1 t g  else decode1 t d 
                                              |_,_-> raise(Invalid_argument
                                              "Code incorrect " );;



                      let rec decode (l: int list ) (t : 'a htree) : 'a list =
                                match l with 
                                  |[] -> []
                                    |_-> let (h,r) = decode1 l t in h :: decode
                                    r t ;;  


                      let freq_ht (t : 'a htree) : int=
                                match t with
                                  |Leaf (n,_)-> n 
                                    |Branch(n,_,_) -> n ;;

                      let ht_less (t1 : 'a htree) (t2 : 'a htree ) : bool = 
                                
                                if freq_ht t1 < freq_ht t2 then true else false
                      ;;

                      ht_less (Leaf(3,'B'))
                      (Branch(5,Leaf(2,'Z'),Leaf(3,'B')));;


                      let rec min_sauf_min (lt : ('a htree) list) : ('a htree) *
                      (('a htree) list)=
                                
                                match lt with
                                  |[]->raise (Invalid_argument "empty list")
                                    |[h]->(h,[])
                                      |h::t-> let (x,y) = min_sauf_min t in if
                                              ht_less h x then (h,x::y) else 
                                                              (x,h::y) ;;


                      let ht_branch (t1: 'a htree ) (t2 : 'a htree ) : 'a htree
                      =
                                
                                Branch(freq_ht t1 + freq_ht t2 , t1 , t2) ;;
                      ht_branch (Branch(5, Leaf(2, 'Z'), Leaf(3, 'W'))) (Leaf(3,
                      'B'));;


                      let rec leaf_list (f : ('a *int) list ) : ('a htree) list
                      =
                                match f with
                                  |[]->raise (Invalid_argument " empty list") 
                                    |[(a,n)]->[Leaf(n,a)]
                                      |(a,n)::t->Leaf(n,a)::leaf_list t ;;


                      leaf_list [('A', 8); ('B', 3); ('D', 1); ('E', 1); ('F',
                      1); ('H', 1);
                                 ('G', 1);('C', 1)];;


                      type 'a btree = 
                                |Empty
                                  |Node of 'a * 'a btree * 'a btree ;;

                      let rec cons_all (x : 'a ) (xss : ('a list) list) : ('a
                      list) list=
                                match xss with
                                  |[]->[]
                                    |h::t->(x::h) :: cons_all x t ;;

                      let rec cons_all2 (x:'a) (xss : ('a list) list) : ('a
                      list) list=
                                
                                List.map (fun y->x::y)  xss;;

                        
                        
                        
                      let rec branch_list (bt : 'a btree) : ('a list) list =
                                match bt with
                                  |Empty->[[]]
                                    |Node(a,g,d)-> (cons_all a ((branch_list
                                    g)@(branch_list d))) ;;  


                      let rec is_branch (xs: 'a list ) (bt : 'a btree) : bool=
                                
                                match xs , bt with
                                  |[],Empty -> true 
                                    |h::t ,Node(a,g,d)-> (h=a) && is_branch t g
                                    || is_branch t d 
                                      |_ ->false;;

                      (*exercice 2 *)

                      let rec sublist_tree(xs : 'a list ) : 'a btree = 
                                match xs with
                                  |[]->Empty 
                                    |h::t -> Node (h , sublist_tree t ,
                                    sublist_tree t ) ;;


                      sublist_tree [1;2;3];;


                      let rec sublist_list (bt : 'a btree) : ('a list) list =
                                match bt with
                                  |Empty -> [[]]
                                    |Node(a,g,d)->(cons_all  a (sublist_list g))
                                    @ (sublist_list d) ;;


                      let tree=Node (1, Node (2, Node (3, Empty, Empty), Node
                      (3, Empty, Empty)),
                                     Node (2, Node (3, Empty, Empty), Node (3,
                                     Empty, Empty))) in (sublist_list tree) 


                      let rec is_sublist (xs :'a list) (bt :'a btree) : bool = 
                                match xs,bt with
                                  |[],Empty->true 
                                    |h::t , Node(a,g,d)-> if (h=a)  then
                                            is_sublist t g else is_sublist xs d 
                                              |_->false ;;


                      (*exercice 3 : Listes 1*)

                      type dist_list = (string * string * float ) list ;;
                      (*liste de triplets *)

                      let rec dist (v1 : string ) (v2 : string) (ds :dist_list)
                      : float =
                                match ds with 
                                  |[]->raise Not_found 
                                    |(c1,c2,d)::t-> if ((v1=c1) && (v2=c2)) ||
                                    ((v1=c2) && (v2=c1))  then d else dist v1 v2
                                    t ;;  


                      type dist_tab = (string * (string * float ) list ) list ;;


                      let dist (v1 : string) (v2:string) (tds : dist_tab) :
                              float =
                                        let l=List.assoc v1 tds  in 
                                          List.assoc v2 l ;;

                      let rec add (k:'a) (v:'b) (kvss:('a * 'b list) list) : ('a
                      * 'b list ) list =
                              *   
                              *     match kvss with 
                              *       |[]->[(k,[v])]
                              *         |(e,l)::t->if e=k then (e,v::l)::t else
                                      *         (e,l) :: add k v t ;;
                      *
                      *
                      *         (add 'x' 42 [('y',[1;2]); ('x',[43])]);;
                      *
                      *         let add_dist (v1:string) (v2:string) (d:float)
                      *         (tds:dist_tab) : dist_tab=
                              *           add v1 (v2,d) (add v2 (v1,d) tds);;
                      *
                      *           let rec build (ds : dist_list) : dist_tab =
                              *             match ds with
                              *               |[]->[]
                              *                 |(v1,v2,d1)::t-> add_dist v1 v2
                              *                 d1 (build t);;  
                      *
                      *
                      *                 (build
                      *                 [("Paris","Marseille",660.91);("Toulouse","Paris",576.94)]);;
                      *
                      *                 let build2 (ds : dist_list) : dist_tab =
                              *                   List.fold_left (fun r
                              *                   (v1,v2,d) ->(add_dist v1 v2 d
                              *                   r)) [] ds;;
                      *
                      *                   let rec list_remove (x:'a ) (xs: 'a
                      *                   list) : 'a  list =
                              *                     match xs with
                              *                       |[]->[]
                              *                         |h::t-> if h=x then t
                              *                         else h::(list_remove x
                              *                         t);;
                      *
                      *
                      *                         let rec sub_assoc (xs : 'a list)
                      *                         (xvs : ('a * 'b ) list ) : ('a *
                      *                         'b) list= 
                              *                           match xvs with
                              *                             |[]->[]
                              *                               |(k,v)::t-> if
                                      *                               (List.mem
                                      *                               k xs) then
                                              *                               (k,v)::sub_assoc
                                              *                               xs
                                              *                               t
                                              *                               else
                                                      *                               sub_assoc
                                                      *                               xs
                                                      *                               t
                                                      *                               ;;
                      *
                      *
                      *
                      *                               let sub_assoc_it (xs : 'a
                      *                               list ) (xvs : ('a * 'b)
                      *                               list) : ('a * 'b) list =
                              *                                 
                              *                                   List.filter
                              *                                   (fun
                                      *                                   (x,_)->List.mem
                                      *                                   x xs)
                              *                                   xvs ;;
                      *
                      *
                      *
                      *                                   let rec min_val_key
                      *                                   (kvs:('a * 'b) list) :
                              *                                   'a =
                                      *                                     match
                                      *                                     kvs
                                      *                                     with 
                                      *                                       |[]->raise
                                      *                                       (Invalid_argument
                                      *                                       "min_val_key")
                                      *                                         |[(k,v)]->k
                                      *                                           |(k1,v1)::(k2,v2)::t->
                                              *                                           if
                                                      *                                           v1<v2
                                                      *                                           then
                                                              *                                           (min_val_key
                                                              *                                           ((k1,v1)::t))
                                                              *                                           else
                                                                      *                                           (min_val_key
                                                                      *                                           ((k2,v2)::t));;
                      *                                             
                      *                                                 
                      *                                                 min_val_key
                      *                                                 [("Paris",660.91);("Toulouse",319.79)]
                      *                                                 ;;  
                      *                                                     
                      *
                      *
                      *
                      *                                                     let
                      *                                                     rec
                      *                                                     access1
                      *                                                     (x:'a)
                      *                                                     (r:('a*'a)
                      *                                                     list):
                              *                                                     'a
                              *                                                     list=
                                      *                                                       match
                                      *                                                       r
                                      *                                                       with
                                      *                                                         |[]->[]
                                      *                                                           |(k,v)::t->
                                              *                                                           if
                                                      *                                                           k=x
                                                      *                                                           then
                                                              *                                                           v::(access1
                                                              *                                                           x
                                                              *                                                           t)
                                                              *                                                           else
                                                                      *                                                           access1
                                                                      *                                                           x
                                                                      *                                                           t
                                                                      *                                                           ;;
                      *
                      *                                                             
                      *                                                             let
                      *                                                             ex
                      *                                                             =
                              *                                                             [('a','b');('a','d');('b','c');('d','c');('d','e');('e','f');('c','f');('e','a')];;
                      *                                                             (access1
                      *                                                             'f'
                      *                                                             ex);;
                      *                                                             (access1
                      *                                                             'b'
                      *                                                             ex);;
                      *                                                             (access1
                      *                                                             'a'
                      *                                                             ex);;
                      *
                      *
                      *                                                             let
                      *                                                             rec
                      *                                                             list_access1
                      *                                                             (xs
                      *                                                             :
                              *                                                             'a
                              *                                                             list)
                      *                                                             (r
                      *                                                             :
                              *                                                             ('a*'a)
                              *                                                             list)
                      *                                                             :
                              *                                                             'a
                              *                                                             list
                              *                                                             =
                                      *                                                               match
                                      *                                                               xs
                                      *                                                               with
                                      *                                                                 |[]->[]
                                      *                                                                   |h::t->
                                              *                                                                   (access1
                                              *                                                                   h
                                              *                                                                   r)@(list_access1
                                              *                                                                   t
                                              *                                                                   r);;
                      *
                      *                                                                   (list_access1
                      *                                                                   ['a';'b']
                      *                                                                   ex);;
                      *                                                                       
                      *
                      *                                                                       let
                      *                                                                       access2(x:'a)(r:('a*'a)
                      *                                                                       list)
                      *                                                                       :
                              *                                                                       'a
                              *                                                                       list
                              *                                                                       =
                                      *                                                                         list_access1
                                      *                                                                         (access1
                                      *                                                                         x
                                      *                                                                         r)
                                      *                                                                         r
                                      *                                                                         ;; 
                      *
                      *
                      *                                                                         (access2
                      *                                                                         'b'
                      *                                                                         ex);;
                      *                                                                         (access2
                      *                                                                         'a'
                      *                                                                         ex);;
                      *                                                                           
                      *
                      *
                      *                                                                           let
                      *                                                                           rec
                      *                                                                           accessn
                      *                                                                           (x
                      *                                                                           :
                              *                                                                           'a)
                      *                                                                           (n
                      *                                                                           :
                              *                                                                           int)
                      *                                                                           (r
                      *                                                                           :('a
                      *                                                                           *
                      *                                                                           'a)
                      *                                                                           list)
                      *                                                                           :
                              *                                                                           'a
                              *                                                                           list
                              *                                                                           =
                                      *                                                                             if
                                              *                                                                             n
                                              *                                                                             <
                                              *                                                                             0
                                              *                                                                             then
                                                      *                                                                             []
                                                      *                                                                             else
                                                              *                                                                             if
                                                                      *                                                                             n
                                                                      *                                                                             =
                                                                              *                                                                             0
                                                                              *                                                                             then
                                                                                      *                                                                             [x]
                                                                                      *                                                                             else
                                                                                              *                                                                                 list_access1
                                                                                              *                                                                                 (accessn
                                                                                              *                                                                                 x
                                                                                              *                                                                                 (n-1)
                                                                                              *                                                                                 r)
                                                                                              *                                                                                 r
                                                                                              *                                                                                 ;;
                      *                                                                                     
                      *                                                                                     let
                      *                                                                                     rec
                      *                                                                                     access_infn
                      *                                                                                     (x:'a)
                      *                                                                                     (n
                      *                                                                                     :int)
                      *                                                                                     (r
                      *                                                                                     :
                              *                                                                                     ('a*'a)
                              *                                                                                     list)
                      *                                                                                     :
                              *                                                                                     'a
                              *                                                                                     list
                              *                                                                                     =
                                      *                                                                                       if
                                              *                                                                                       n
                                              *                                                                                       <=
                                                      *                                                                                       0
                                                      *                                                                                       then
                                                              *                                                                                       raise
                                                              *                                                                                       (Invalid_argument
                                                              *                                                                                       "list_access_infn")
                                                              *                                                                                       else 
                                                                      *                                                                                         if
                                                                              *                                                                                         n
                                                                              *                                                                                         =
                                                                                      *                                                                                         1
                                                                                      *                                                                                         then
                                                                                              *                                                                                         access1
                                                                                              *                                                                                         x
                                                                                              *                                                                                         r
                                                                                              *                                                                                         else 
                                                                                                      *                                                                                             (accessn
                                                                                                      *                                                                                             x
                                                                                                      *                                                                                             n
                                                                                                      *                                                                                             r)
                                                                                                      *                                                                                             @
                                                                                                      *                                                                                             (access_infn
                                                                                                      *                                                                                             x
                                                                                                      *                                                                                             (n-1)
                                                                                                      *                                                                                             r
                                                                                                      *                                                                                             );;
                      *
                      *
                      *                                                                                             let
                      *                                                                                             rec
                      *                                                                                             cycle_from
                      *                                                                                             (x
                      *                                                                                             :
                              *                                                                                             'a)
                      *                                                                                             (r
                      *                                                                                             :
                              *                                                                                             ('a
                              *                                                                                             *
                              *                                                                                             'a)
                              *                                                                                             list)
                      *                                                                                             :
                              *                                                                                             bool
                              *                                                                                             =
                                      *                                                                                               let
                                      *                                                                                               l
                                      *                                                                                               =
                                              *                                                                                               (access_infn
                                              *                                                                                               x
                                              *                                                                                               (List.length
                                              *                                                                                               r)
                                              *                                                                                               r
                                              *                                                                                               )
                                              *                                                                                               in 
                                      *                                                                                                 match
                                      *                                                                                                 l
                                      *                                                                                                 with 
                                      *                                                                                                   |[]->false 
                                      *                                                                                                     |h::t
                                      *                                                                                                     ->
                                              *                                                                                                     if
                                                      *                                                                                                     List.mem
                                                      *                                                                                                     x
                                                      *                                                                                                     l
                                                      *                                                                                                     then
                                                              *                                                                                                     true
                                                              *                                                                                                     else
                                                                      *                                                                                                     false;;
                      *
                      *
                      *                                                                                                     (*arbres
                      *                                                                                                     binaires
                      *                                                                                                     et
                      *                                                                                                     mots
                      *                                                                                                     binaires
                      *                                                                                                     *)
                      type bin = I | O
                      type 'a btree =
                                |Empty 
                                  |Node of 'a * 'a btree * 'a btree ;;


                      let rec btree_of_bin ( l : bin list) : (bool btree)=
                                match l with
                                  |[]->Node(true,Empty,Empty)
                                    |I::t-> Node(false,btree_of_bin t , Empty)
                                      |O::t->Node(false,Empty, btree_of_bin t)
                      ;; 


                      let rec appartient (m : bin list) (bt : bool btree) : bool
                      = 
                                match m , bt with
                                  |_,Empty -> false 
                                    |[],Node(a,_,_)->a
                                      |I::t , Node(a,g,d)-> appartient t g 
                                        |O::t , Node(a,g,d)->appartient t d ;;


                      let rec ajout (m : bin list) (bt : bool btree) : bool
                      btree = 
                                if (appartient m bt) then bt else 
                                            match bt with 
                                                |Empty -> btree_of_bin m 
                                                    |Node(a,g,d)->
                                                                            match
                                                                            m
                                                                            with
                                                                                    |[]->Node(true,g,d)
                                                                                            |I::t->
                                                                                                            Node(a,(ajout
                                                                                                            t
                                                                                                            g),d)
                                                                                                                    |O::t->Node(a,g,(ajout
                                                                                                                    t
                                                                                                                    d));;

                                
                      let rec retrait (m : bin list) (bt: bool btree) : (bool
                      btree) = 
                                
                                match bt with 
                                  |Empty->Empty
                                    |Node(a,g,d)->
                                                          match m with
                                                                |[]->Node(false
                                                                ,g,d)
                                                                      |I::t->Node(a,
                                                                      (retrait t
                                                                      g) , d)
                                                                            |O::t->Node(a,g,(retrait
                                                                            t
                                                                            d))
                      ;;



                      type value = B of bool | I of int ;;

                      exception TYPE_ERROR of int ;;

                      let not1 (v : value) : value =
                                match v with
                                  |B b -> B (not b) 
                                    |I i ->raise (TYPE_ERROR i );;

                      not1 (B true) ;; 
                      not1 (I 1);;


                      let not2 (v :value) : value =
                                try not1 v with
                                  |TYPE_ERROR i -> B(i=0);;


                      exception DIV_BY_0 of int ;;

                      let div1 (v1 : value) (v2 : value) : value = 
                                match (v1,v2) with
                                  |(I i1 , I i2)-> if i2=0 then raise (DIV_BY_0
                                  i2) else I (i1/i2)
                                    |_->raise(Invalid_argument "Booleen");;


                      let div2 (v1 : value) (v2 : value) : value option =
                                try Some (div1 v1 v2) with
                                  |DIV_BY_0 i -> None ;;

                        
                      type 'a option = None | Some of 'a ;;

                      type 'a btree = Empty | Node of 'a * 'a btree * 'a btree
                      ;;

                      let rec max_length_branch (t : 'a btree) : 'a list =
                                
                                match t with 
                                  |Empty -> []
                                    |Node(a,g,d)->if (List.length
                                    (a::max_length_branch g )) >
                                    (List.length(a::max_length_branch d )) then
                                            (a::max_length_branch g ) else
                                                            (a::max_length_branch
                                                            d );;

                                        
                      let
                      tr=Node(5,Node(3,Node(4,Empty,Empty),Node(5,Empty,Empty)),Node(2,Node(3,Empty,Node(7,Empty,Empty)),Empty));;

                      max_length_branch tr ;;



                      (*let rec max_flow_branch (t :'a btree ) : 'a list =
                              *    match t with
                              *       |Empty->[]
                              *          |Node(a,Empty,Empty)->[a]
                              *             |Node(a,Node(b,g1,d1),Node(c,g2,d2))->if
                                      *             b >= c then ( a ::
                                              *             (max_flow_branch
                                              *             (Node(b,g1,d1))))
                                              *             else ( a ::
                                                      *             (max_flow_branch
                                                      *             (Node(c,g2,d2))));;*)



                      let rec at_prof (n :int ) (x : 'a ) (t : 'a btree) : bool
                      = 
                                match t,n with 
                                  |Empty,_ -> false 
                                    |Node(a,_,_),0-> x=a
                                      |Node(a,g,d),_-> if (at_prof (n-1) x g)
                                      then true else (at_prof (n-1) x d);;



                      let rec at_prof_list (n : int) (t : 'a btree) : 'a list = 
                                match n,t with
                                  |_,Empty->[]
                                    |0,Node(a,_,_)->[a] 
                                      |_,Node(a,g,d)-> (at_prof_list (n-1) g) @
                                      (at_prof_list (n-1) d) ;;

