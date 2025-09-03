(* Hook for mymap *)
(* From elpi.apps Require Export derive.legacy. *)
From Trocq Require Export mymap.
From Trocq Extra Dependency "algo/elpi/mymap.elpi" as mymap.

Elpi Accumulate derive Db derive.mymap.db.
Elpi Accumulate derive File mymap.

Elpi Accumulate derive lp:{{

derivation (indt T) Prefix ff (derive "mymap" (derive.mymap.main T Prefix) (mymap-done T)).

}}.

(* Hook for injections *)
From elpi.apps.derive.elpi Extra Dependency "injection.elpi" as injection.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.
From Trocq Extra Dependency "algo/elpi/injection_lemmas.elpi" as injections.
From Trocq Extra Dependency "algo/elpi/utils.elpi" as algo_utils.

From Trocq Require Export injection_lemmas.
Elpi Accumulate derive Db derive.injections.db.
Elpi Accumulate derive File injection.
Elpi Accumulate derive File algo_utils.
Elpi Accumulate derive File injections.

Elpi Accumulate derive lp:{{

dep1 "injections" "projK".
derivation (indt T) Prefix ff (derive "injections" (derive.injections.main T Prefix) (injections-done T)).

}}.

(* Hook for mR *)
From Trocq Require Export mR.
From elpi.apps.derive.elpi Extra Dependency "discriminate.elpi" as discr.
From Trocq Extra Dependency "algo/elpi/common_algo.elpi" as common.
From Trocq Extra Dependency "algo/elpi/mR.elpi" as mR.


Elpi Accumulate derive Db derive.mR.db.
Elpi Accumulate derive File discr.
Elpi Accumulate derive File common.
Elpi Accumulate derive File injections.
Elpi Accumulate derive File mR.

Elpi Accumulate derive lp:{{

  dep1 "mR" "param2".
  dep1 "mR" "mymap".
  dep1 "mR" "injections".
  dep1 "mR" "isK".
  derivation (indt T) Prefix ff (derive "mR" (derive.mR.main T Prefix) (mR-done T)).

}}.

(* Hook for Rm *)
From Trocq Require Export Rm.
From Trocq Extra Dependency "algo/elpi/Rm.elpi" as Rm.
Elpi Accumulate derive Db Header derive.Rm.db.
Elpi Accumulate derive Db derive.Rm.db.
Elpi Accumulate derive File Rm.

Elpi Accumulate derive lp:{{
dep1 "Rm" "mymap".
dep1 "Rm" "param2".
derivation (indt T) Prefix ff (derive "Rm" (derive.Rm.main T Prefix) (rm-done T)).

}}.

(* injK hook into derive *)
From Trocq Require Export injK.
From Trocq Extra Dependency "algo/elpi/injK.elpi" as injK.

Elpi Accumulate derive Db derive.injectionsK.db.
Elpi Accumulate derive File algo_utils.
Elpi Accumulate derive File injK.

Elpi Accumulate derive lp:{{

dep1 "injK" "injections".
derivation (indt T) Prefix ff (derive "injK" (derive.injK.main T Prefix) (injectionsK-done T)).

}}.

(* mRRmK hook into derive *)
From Trocq Extra Dependency "algo/elpi/mRRmK.elpi" as mRRmK.
From Trocq Require Export mRRmK.
Elpi Accumulate derive Db derive.mRRmK.db.
Elpi Accumulate derive File common.
Elpi Accumulate derive File algo_utils.
Elpi Accumulate derive File mRRmK.

Elpi Accumulate derive lp:{{

dep1 "mRRmK" "param2".
dep1 "mRRmK" "mymap".
dep1 "mRRmK" "injK".
dep1 "mRRmK" "mR".
dep1 "mRRmK" "Rm".
derivation (indt T) Prefix ff (derive "mRRmK" (derive.mRRmK.main T Prefix) (mRRmK-done T)).

}}.

