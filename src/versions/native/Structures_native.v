Require Import PArray.


Section Trace.

  (* We use [array array step] to allow bigger trace *)
  Definition trace (step:Type) := array (array step).

  Definition trace_length {step:Type} (t:trace step) : int :=
    PArray.fold_left (fun l a => (l + (length a))%int63) 0%int63 t.

  Definition trace_get {step:Type} (t:trace step) (i:int) : step :=
    snd (PArray.fold_left (fun (jres:(option int) * step) a =>
                        let (j,res) := jres in
                        match j with
                        | Some j' =>
                          let l := length a in
                          if (j' < l)%int63 then
                            (None, get a j')
                          else
                            ((Some ((j' - l)%int63)),res)
                        | None => (None,res)
                        end
                     ) (Some i, (get (get t 0) 0)) t).

  Definition trace_fold {state step:Type} (transition: state -> step -> state) (s0:state) (t:trace step) :=
    PArray.fold_left (PArray.fold_left transition) s0 t.

  Lemma trace_fold_ind (state step : Type) (P : state -> Prop) (transition : state -> step -> state) (t : trace step)
      (IH: forall (s0 : state) (i : int), (i < trace_length t)%int63 = true -> P s0 -> P (transition s0 (trace_get t i))) :
      forall s0 : state, P s0 -> P (trace_fold transition s0 t).
  Proof.
    apply PArray.fold_left_ind.
    intros a i Hi Ha.
    apply PArray.fold_left_ind;trivial.
    intros a0 i0 Hi0 Ha0.       (* IH applied to a0 and (sum of the lengths of the first i arrays + i0) *)
  Admitted.

End Trace.
