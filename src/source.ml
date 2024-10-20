(** 
    Cette partie du programme NE DOIT EN AUCUN CAS être modifiée sous peine
    de voir votre code ne pas passer les tests 
*)

let usage () =
  Format.fprintf
    Format.err_formatter
    "%s <options>

OPTIONS:
     -h : print this help and exit
     -o <file> : set output to <file>
     --output <file> : set output to <file>
     -ts <int> : set the size of the training set (default : 1000)
     --training-size <int> : set the size of the training set (default : 1000)
     -ds <int> : set the size of the testing data set (default : 10000)
     --training-size <int> : set the size of the testing data set (default : 10000)
     -md <int> : set the max tree depth (default : 10)
     --max-depth <int> : set the max tree depth (default : 10)
"
  Sys.argv.(0)
     
let parse_opts () =
  let rec parse l =
    match l with
    | "-h"::l ->
       let _ = usage () in
       exit 0
    | "-o"::output::l' | "--output"::output::l' ->
       ("output",output)::parse l'
    | "-ts"::size::l' | "--training-size"::size::l' ->
       (try
          let _ = int_of_string size in 
         ("training-size", size)::parse l'
       with Failure _ ->
             let _ = usage () in
             exit 127
       )     
    | "-ds"::size::l' | "--data-size"::size::l' ->
       (try
          let _ = int_of_string size in 
          ("data-size",size)::parse l'
       with Failure _ ->
             let _ = usage () in
             exit 127
       )
    | "-md"::size::l' | "--max-depth"::size::l' ->
       (try
          let _ = int_of_string size in 
          ("max-depth",size)::parse l'
       with Failure _ ->
             let _ = usage () in
             exit 127
       )
    | _::_ ->
       let _ = usage () in
       exit 127             
    | [] -> []
  in
  parse (List.tl (Array.to_list Sys.argv))

let raw_opts = parse_opts ()  

         
(* Une position dans le plan est donnée par son abscisse et son ordonnée *)
type pos = { x : float; y : float; };;

(* Une couleur est donnée par ses trois composantes *)
type color = {r:int;g:int;b:int};;


(* Un ensemble de données sera représenté ici
   par une liste de couple (pos,color).
   On pourra supposer qu'une position ne peut pas apparaître deux fois
   dans cette liste
 *)
type 'a dataset = (pos*color) list;;

let red  = { r = 255; g = 0; b = 0};;
let blue = { r = 0; g = 0; b = 255};;
let white = { r = 255; g = 255; b = 255};;
let black = { r = 0; g = 0; b = 0};;


(* fonction de génération pour la courbe de racine carrée.
   La partie sous la courbe est en [blue], celle au dessus de la
   courbe est en [red]
 *)
let generate_sqrt p =
  if p.y*.p.y < p.x then blue else red ;;

(* fonction de génération pour un cercle.
   La partie dans le cercle  est en [blue], celle à l'extérieur
   est en [red]
 *)
let generate_circle p =
  let x = p.x -. 0.5 and y = p.y -. 0.5 in 
  if x*.x +. y*.y < 0.5*.0.5 then blue else red ;;
  
(** Début de la partie à implanter *) 


(** Fonctions de tests *)

let generate_l_r p =
  if p.x < 0.5 then red else blue;;


(** Types *)

(** type [orientation] des séparations 
*)
type orientation =
  Horizontal | Vertical;;

(* type [tree] des predicteur de couleur en fonction
   du type de donnée d'entrainement. On choisi Empty comme arbre vide. int représente l'orientation si il y en a une (0 horizontale, 1 verticale)
 *)
type tree =
  Empty | Node of pos * orientation * tree * tree | Leaf of color;;


(** Fonctions auxiliaires *)

(* [most_point_color] renvoie la couleur majoritaire entre [col_a] et [col_b] dans une liste [list]
  @requires list to be a valid list and n_a and n_b to be equal to 0
  @ensures a color is returned 
  @raises nothing
*)
let rec most_point_color list col_a col_b n_a n_b =
  match list with
    | [] -> 
      if n_a > n_b then 
        col_a 
      else 
        col_b (**couleur majoritaire *)
    | (p,c) :: t -> 
      if c=col_a then 
        most_point_color t col_a col_b (n_a + 1) n_b 
      else 
        most_point_color t col_a col_b n_a (n_b + 1)
;; (**A chaque itéartion, on rajoute 1 à la couleur sur laquelle on est *)

(** [sort_color] renvoie deux listes [l_red] et [l_blue] correspondant aux points rouges et bleu (respectivements) de [list]
  @requires l_red and l_blue to be empty lists
  @ensures a tuple of two lists is returned
  @raises nothing
*)
let rec sort_color list l_red l_blue =
  match list with
    | [] -> 
      (l_red,l_blue)
    | (a,b) :: t -> 
      if b=red then 
        sort_color t ((a,b) :: l_red) l_blue (**On ajoute le point rouge à la liste des points rouges *)
      else 
        sort_color t l_red ((a,b) :: l_blue) (**Même chose avec le point si il est bleu *)
;;

(** [avg_x_y] renvoie un couple [res_x],[res_y] correspondant aux moyennes des positions x et y des pos dans [list]
  @requires res_x = 0, res_y = 0 and n = 0
  @ensures a tuple corresponding to the average of x and y if requires is verified.
  @raises nothing
*)
let rec avg_x_y list (res_x, res_y) n =
  match list with
  | [] -> 
    if n = 0 then 
      (res_x, res_y) 
    else 
      (res_x /. float_of_int n, res_y /. float_of_int n)
  | ({x; y}, _) :: q -> 
    avg_x_y q (res_x +. x, res_y +. y) (n + 1)
;;

(** [separe_vertical] sépare la liste [list] en [l_left] et [l_right] correspondant aux points à gauche de [x_ref] et aux points à droite de [x_ref]
  @requires l_left and l_right are empty lists
  @ensures a tuple of list is returned
  @raises nothing
*)
let rec separe_vertical list x_ref l_left l_right =
  match list with
  | [] -> (l_left, l_right)
  | ({x; y}, col) :: q ->
      if x < x_ref then
        separe_vertical q x_ref (({x; y}, col) :: l_left) l_right (**On ajoute les points à gauche de [[x_ref]] *)
      else
        separe_vertical q x_ref l_left (({x; y}, col) :: l_right) (**Même chose avec les points à droite *)
;;

(** [separe_horizontal] sépare la liste [list] en [l_down] et [l_up] correspondant aux points en dessous et au dessus de [y_ref]
  @requires l_down and l_up are empty lists
  @ensures a tuple of list is returned
  @raises nothing
*)
let rec separe_horizontal list y_ref l_down l_up =
  match list with
  | [] -> (l_down, l_up)
  | ({x; y}, col) :: q ->
      if y < y_ref then
        separe_horizontal q y_ref (({x; y}, col) :: l_down) l_up (**On ajoute les points en dessous de [y_ref] *)
      else
        separe_horizontal q y_ref l_down (({x; y}, col) :: l_up) (**Même chose avec les points au dessus *)
;;

(** [only_one_color] renvoie un couple int*color, 1*col si il n'y a qu'une couleur dans la liste (col la couleur en question) et 0*col sinon
  @requires res = 1 and col is the result of most_point_color
  @ensures res,col is returned, with res = 1 if there is only one color in list, and col the corresponding color. If res = 0, an incorrect result will be returned (same if col is not correct)
  @raises nothing
*)
let rec only_one_color list res col =
  if res = 0 then (0,col) (**res=0 si on a trouvé une couleur différente *)
  else 
  match list with
    | [] -> (res,col)
    | (_, c) :: q -> if c = col then only_one_color q 1 c else only_one_color q 0 c
;;

(** [best_separation] renvoie l'orientation de la séparation donnant la meilleure précision lorsqu'on sépare la liste [points] 
  @requires points is a valid dataset
  @ensures an orientation type is returned
  @raises nothing
*)
let best_separation points =
  let nb_points = List.length points in
  let (somme_x, somme_y) = List.fold_left (fun (acc_x, acc_y) (p, _) -> (acc_x +. p.x, acc_y +. p.y)) (0.0, 0.0) points in
  let moyenne_x = somme_x /. float_of_int nb_points in (**moyenne empirique *)
  let moyenne_y = somme_y /. float_of_int nb_points in
  let variance_x = List.fold_left (fun acc (p, _) -> acc +. (p.x -. moyenne_x) ** 2.0) 0.0 points /. float_of_int nb_points in (**variance empirique *)
  let variance_y = List.fold_left (fun acc (p, _) -> acc +. (p.y -. moyenne_y) ** 2.0) 0.0 points /. float_of_int nb_points in
  if variance_x > variance_y then (**On renvoie la séparation qui correspond à la plus petite variance *)
    Vertical
  else
    Horizontal
;;

(** [build_tree_aux] est la fonction qui permet de renvoyer l'arbre de prédiction si le dataset n'est pas vide et n est positif ou nul
  @requires n >= 0 and training is not empty
  @ensures a tree type is returned
  @raises nothing
*)
let rec build_tree_aux n training =
  if n = 0 then
    Leaf (most_point_color training blue red 0 0) (**Si on est à la profondeur maximale, on renvoie la couleur majoritaire *)
  else if only_one_color training 1 blue = (1, blue) then (**Si il n'y a qu'une couleur on la renvoie *)
    Leaf blue
  else if only_one_color training 1 red = (1, red) then
    Leaf red
  else
    let (l_red, l_blue) = sort_color training [] [] in
    let (avg_red_x, avg_red_y) = avg_x_y l_red (0., 0.) 0 in
    let (avg_blue_x, avg_blue_y) = avg_x_y l_blue (0., 0.) 0 in
    if best_separation training = Vertical then
      let (list_l, list_r) = separe_vertical training ((avg_blue_x +. avg_red_x) /. 2.0) [] [] in (**On sépare la liste *)

      if list_l = [] || list_r = [] then (**Si la séparation donne une liste vide, il ne reste qu'une seule liste donc on renvoie la couleur majoritaire *)
        Leaf (most_point_color training blue red 0 0)
      else (**Sinon on recommence l'algorithme en créant un noeud avec la position, l'orientation et les arbres à gauche et à droite *)
        Node ({x = (avg_blue_x +. avg_red_x) /. 2.; y = (avg_blue_y +. avg_red_y) /. 2.}, Vertical, build_tree_aux (n - 1) list_l, build_tree_aux (n - 1) list_r)
    
    else
      let (list_u, list_d) = separe_horizontal training ((avg_blue_y +. avg_red_y) /. 2.0) [] [] in

      if list_u = [] || list_d = [] then
        Leaf (most_point_color training blue red 0 0)
      else (**Même chose avec une séparation horizontale *)
        Node ({x = (avg_blue_x +. avg_red_x) /. 2.; y = (avg_blue_y +. avg_red_y) /. 2.}, Horizontal, build_tree_aux (n - 1) list_u, build_tree_aux (n - 1) list_d)
;;

(* [build_tree n training] retourne un predicteur de profondeur maximale [n]
   sur le jeu d'entrainement [training]
 *)
let build_tree n training =
  if n < 0 then (* Si n est négatif, on a une erreur, un arbre ne peut pas avoir de profondeur négative *)
    failwith "n cannot be negative"
  else if training = [] then (* Si le data set est vide on renvoie un arbre vide *)
    Empty
  else (* Enfin sinon on utilise la fonction de création d'arbre*)
    build_tree_aux n training 
;; 

(* [predict_color_aux] est la fonction récursive utilisée à l'intérieur de la fonction predict_color
  @requires tree and pos are both valid tree type and pos type
  @ensures a prediction color is returned
  @raises nothing
*)
let rec predict_color_aux tree pos =
  let x_pos = pos.x in
  let y_pos = pos.y in
  match tree with
  | Empty -> white (* Si l'arbre est vide, par convention le point n'aura pas de couleur, on considère qu'il sera blanc*)
  | Leaf col -> col 
  | Node ({x; y}, Vertical, tree_l, tree_r) -> (*Si l'arbre se sépare*)
    if x_pos < x then (*On continue de parcourir l'arbre en fonction de la position du point cherché*)
      predict_color_aux tree_l pos
    else
      predict_color_aux tree_r pos
  | Node ({x; y}, Horizontal, tree_d, tree_u) -> (*Même chose si l'arbre se sépare de manière horizontale*)
    if y_pos > y then
      predict_color_aux tree_u pos
    else
      predict_color_aux tree_d pos
;;

(* [predict_color tree pos] prédit la couleur du point [pos] à l'aide du
   prédicteur [tree]
*)
let predict_color tree pos =
  predict_color_aux tree pos
;;                               
(* [generate_using_function pos] retourne la couleur du point pos
   il vous est conseiller de tester vos résultats sur plusieurs generateurs
   il vous suffit simplement de changer la fonction de génération avant de
   recompiler/réévaluer le code
 *)
                                
let generate_using_function = generate_circle ;;


                        
(*
Si vous le souhaitez, vous pouvez changer les valeurs par défaut ici.

par exemple : pour prendre un jeu de données de taille 100 et définir un fichier de sortie.

let opts = ("training-size","100")::("output","/tmp/test.ppm")::raw_opts
*)
let opts = raw_opts
                        
                        
                        
(** fin de la partie à implanter
AUCUNE MODIFICATION NE DOIT ÊTRE FAITE À PARTIR DE CE COMMENATAIRE

Vous n'avez pas besoin de lire/comprendre cette partie du code
*)

let generate nb f  =
  let margin = 0.001 in
  List.init nb
    (fun _ ->
      let x = margin +. Random.float (1. -. 2. *. margin) in
      let y = margin +. Random.float (1. -. 2. *. margin) in
      let v = f {x;y} in
      ({x;y}, v)
    )


let ts =
  match List.assoc_opt "training-size" opts with
  | None -> 1000
  | Some s -> int_of_string s

let ds =
  match List.assoc_opt "data-size" opts with
  | None -> 10000
  | Some s -> int_of_string s
                        
let md =
  match List.assoc_opt "max-depth" opts with
  | None -> 10
  | Some s -> int_of_string s
  

let pnm h w tree testing_ds =
  let output = Array.make_matrix h w white in
  (* on commence par la couleur de fond *)
  Array.iteri
    (fun j line ->
      Array.iteri (fun i _ ->
          let x = float_of_int i /. float_of_int w in
          let y = float_of_int j /. float_of_int h in  
          let c = predict_color tree {x;y} in
          output.(h-j-1).(i) <- c
        )
        line
    )
    output;
  (* On imprime le vrai dataset *)
  List.iter
    (fun (pos,color) ->
      let j = h-1-int_of_float (pos.y*.float_of_int h) in
      let i = int_of_float (pos.x*.float_of_int w) in
      let color' = predict_color tree pos in
      output.(j).(i) <- if color=color' then white else black 
    )
    testing_ds;
  output
            
let output_graph h w tree testing_ds =
  match List.assoc_opt "output" opts with
  | None -> ()
  | Some output ->
     try
       let fd = open_out output in
       let fmt = Format.formatter_of_out_channel fd in
       let output = pnm h w tree testing_ds in   
       let _ = Format.fprintf fmt "P3@.%d %d@.255@." h w in
       let _ = Array.iter (Array.iter (fun color -> Format.fprintf fmt "%d %d %d@." color.r color.g color.b)) output in 
       let _ = Format.pp_print_flush fmt () in 
       close_out fd
     with Sys_error s ->
       let _ = Format.fprintf Format.err_formatter "%s@." s in
       exit 127
            
let main () = 
  let training_ds = generate ts generate_using_function in
  let testing_ds = generate ds generate_using_function in
  let tree = build_tree md training_ds in
  let nb_bad_prediction =
    List.fold_left
      (fun nb_bad_prediction (pos,color) -> 
        let color' = predict_color tree pos in
        if color = color'
        then nb_bad_prediction
        else nb_bad_prediction + 1
      )
      0
      testing_ds
  in
let _ =  Format.printf
"training-size = %d
test-size = %d
max-depth = %d
correctness = %03.1f%%@."
ts ds md (100.*.float_of_int (ds-nb_bad_prediction)/.float_of_int ds)
in
output_graph 400 400 tree testing_ds

let _ = main ()

