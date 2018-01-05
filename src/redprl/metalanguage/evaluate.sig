signature ML_EVALUATE = 
sig
  type env

  type syn_value
  type sem_value
  
  type syn_cmd
  type sem_cmd

  type exit_code = bool

  val evalVal : env -> syn_value -> sem_value
  val evalCmd : env -> syn_cmd -> sem_cmd * exit_code
end
