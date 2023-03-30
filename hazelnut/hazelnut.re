open Sexplib.Std;
//open Monad_lib.Monad;
let compare_string = String.compare;
let compare_int = Int.compare;

[@deriving (sexp, compare)]
type htyp =
  | Arrow(htyp, htyp)
  | Num
  | Hole;

[@deriving (sexp, compare)]
type hexp =
  | Var(string)
  | Lam(string, hexp)
  | Ap(hexp, hexp)
  | Lit(int)
  | Plus(hexp, hexp)
  | Asc(hexp, htyp)
  | EHole
  | NEHole(hexp);

[@deriving (sexp, compare)]
type ztyp =
  | Cursor(htyp)
  | LArrow(ztyp, htyp)
  | RArrow(htyp, ztyp);

[@deriving (sexp, compare)]
type zexp =
  | Cursor(hexp)
  | Lam(string, zexp)
  | LAp(zexp, hexp)
  | RAp(hexp, zexp)
  | LPlus(zexp, hexp)
  | RPlus(hexp, zexp)
  | LAsc(zexp, htyp)
  | RAsc(hexp, ztyp)
  | NEHole(zexp);

[@deriving (sexp, compare)]
type child =
  | One
  | Two;

[@deriving (sexp, compare)]
type dir =
  | Child(child)
  | Parent;

[@deriving (sexp, compare)]
type shape =
  | Arrow
  | Num
  | Asc
  | Var(string)
  | Lam(string)
  | Ap
  | Lit(int)
  | Plus
  | NEHole;

[@deriving (sexp, compare)]
type action =
  | Move(dir)
  | Construct(shape)
  | Del
  | Finish;

module TypCtx = Map.Make(String);
type typctx = TypCtx.t(htyp);

exception Unimplemented;

let rec erase_typ = (zt: ztyp): htyp => {
  switch (zt) {
  | Cursor(ht) => ht
  | LArrow(zt, ht) => Arrow(erase_typ(zt), ht)
  | RArrow(ht, zt) => Arrow(ht, erase_typ(zt))
  };
};

let rec erase_exp = (e: zexp): hexp => {
  // Used to suppress unused variable warnings
  // Okay to remove
  switch (e) {
  | Cursor(h) => h
  | Lam(s, z) => Lam(s, erase_exp(z))
  | LAp(z, h) => Ap(erase_exp(z), h)
  | RAp(h, z) => Ap(h, erase_exp(z))
  | LPlus(z, h) => Plus(erase_exp(z), h)
  | RPlus(h, z) => Plus(h, erase_exp(z))
  | LAsc(z, ht) => Asc(erase_exp(z), ht)
  | RAsc(h, zt) => Asc(h, erase_typ(zt))
  | NEHole(z) => NEHole(erase_exp(z))
  };
};

let match = (t: htyp): option(htyp) => {
  switch (t) {
  | Num => None
  | Hole => Some(Arrow(Hole, Hole))
  | Arrow(a, b) => Some(Arrow(a, b))
  };
};

let rec consis = (t: htyp, t': htyp): bool =>
  if (t == Hole || t' == Hole || t == t') {
    true;
  } else {
    switch (t, t') {
    | (Arrow(t1, t1'), Arrow(t2, t2')) =>
      consis(t1, t2) && consis(t1', t2')
    | _ => false
    };
  };

let rec syn = (ctx: typctx, e: hexp): option(htyp) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  switch (e) {
  | Var(s) => TypCtx.find_opt(s, ctx)
  | Ap(e1, e2) =>
    switch (syn(ctx, e1)) {
    | Some(t1) =>
      switch (match(t1)) {
      | Some(Arrow(t2, t)) =>
        if (ana(ctx, e2, t2)) {
          Some(t);
        } else {
          None;
        }
      | _ => None
      }
    | _ => None
    }
  | Lit(_) => Some(Num)
  | Plus(e1, e2) =>
    if (ana(ctx, e1, Num) && ana(ctx, e2, Num)) {
      Some(Num);
    } else {
      None;
    }
  | EHole
  | NEHole(_) => Some(Hole)
  | Asc(e, t) =>
    if (ana(ctx, e, t)) {
      Some(t);
    } else {
      None;
    }
  | _ => None
  };
}

and ana = (ctx: typctx, e: hexp, t: htyp): bool => {
  // Used to suppress unused variable warnings
  // Okay to remove
  switch (e) {
  | Lam(s, h) =>
    switch (match(t)) {
    | Some(Arrow(t1, t2)) => ana(TypCtx.add(s, t1, ctx), h, t2)
    | _ => false
    }
  | _ =>
    switch (syn(ctx, e)) {
    | Some(t') => consis(t', t)
    | _ => false
    }
  };
};

let isc = (e: zexp): bool => {
  switch (e) {
  | Cursor(_) => true
  | _ => false
  };
};
let isc_t = (e: ztyp): bool => {
  switch (e) {
  | Cursor(_) => true
  | _ => false
  };
};

let rec mov = (e: zexp, d: dir): option(zexp) => {
  switch (d) {
  | Parent =>
    switch (e) {
    | Cursor(_) => None
    | Lam(s, z) =>
      if (isc(z)) {
        Some(Cursor(erase_exp(e)));
      } else {
        switch (mov(z, d)) {
        | None => None
        | Some(z) => Some(Lam(s, z))
        };
      }
    | LAp(z, h) =>
      if (isc(z)) {
        Some(Cursor(erase_exp(e)));
      } else {
        switch (mov(z, d)) {
        | None => None
        | Some(z) => Some(LAp(z, h))
        };
      }
    | RAp(h, z) =>
      if (isc(z)) {
        Some(Cursor(erase_exp(e)));
      } else {
        switch (mov(z, d)) {
        | None => None
        | Some(z) => Some(RAp(h, z))
        };
      }
    | LPlus(z, h) =>
      if (isc(z)) {
        Some(Cursor(erase_exp(e)));
      } else {
        switch (mov(z, d)) {
        | None => None
        | Some(z) => Some(LPlus(z, h))
        };
      }
    | RPlus(h, z) =>
      if (isc(z)) {
        Some(Cursor(erase_exp(e)));
      } else {
        switch (mov(z, d)) {
        | None => None
        | Some(z) => Some(RPlus(h, z))
        };
      }
    | LAsc(z, h) =>
      if (isc(z)) {
        Some(Cursor(erase_exp(e)));
      } else {
        switch (mov(z, d)) {
        | None => None
        | Some(z) => Some(LAsc(z, h))
        };
      }
    | RAsc(h, zt) =>
      if (isc_t(zt)) {
        Some(Cursor(erase_exp(e)));
      } else {
        switch (mov_t(zt, d)) {
        | None => None
        | Some(zt) => Some(RAsc(h, zt))
        };
      }
    | NEHole(z) =>
      if (isc(z)) {
        Some(Cursor(erase_exp(e)));
      } else {
        switch (mov(z, d)) {
        | None => None
        | Some(z) => Some(NEHole(z))
        };
      }
    }
  | Child(child) =>
    switch (e) {
    | Cursor(h) =>
      switch (h) {
      | Lam(s, h) =>
        if (child == One) {
          Some(Lam(s, Cursor(h)));
        } else {
          None;
        }
      | Ap(e1, e2) =>
        if (child == One) {
          Some(LAp(Cursor(e1), e2));
        } else {
          Some(RAp(e1, Cursor(e2)));
        }
      | Plus(e1, e2) =>
        if (child == One) {
          Some(LPlus(Cursor(e1), e2));
        } else {
          Some(RPlus(e1, Cursor(e2)));
        }
      | NEHole(e) =>
        if (child == One) {
          Some(NEHole(Cursor(e)));
        } else {
          None;
        }
      | Asc(h, ht) =>
        if (child == One) {
          Some(LAsc(Cursor(h), ht));
        } else {
          Some(RAsc(h, Cursor(ht)));
        }
      | _ => None
      }
    | Lam(s, z) =>
      switch (mov(z, d)) {
      | None => None
      | Some(z) => Some(Lam(s, z))
      }
    | LAp(z, h) =>
      switch (mov(z, d)) {
      | None => None
      | Some(z) => Some(LAp(z, h))
      }
    | RAp(h, z) =>
      switch (mov(z, d)) {
      | None => None
      | Some(z) => Some(RAp(h, z))
      }
    | LPlus(z, h) =>
      switch (mov(z, d)) {
      | None => None
      | Some(z) => Some(LPlus(z, h))
      }
    | RPlus(h, z) =>
      switch (mov(z, d)) {
      | None => None
      | Some(z) => Some(RPlus(h, z))
      }
    | LAsc(z, ht) =>
      switch (mov(z, d)) {
      | None => None
      | Some(z) => Some(LAsc(z, ht))
      }
    | RAsc(h, zt) =>
      switch (mov_t(zt, d)) {
      | None => None
      | Some(zt) => Some(RAsc(h, zt))
      }
    | NEHole(z) =>
      switch (mov(z, d)) {
      | None => None
      | Some(z) => Some(NEHole(z))
      }
    }
  };
}
and mov_t = (e: ztyp, d: dir): option(ztyp) => {
  switch (d) {
  | Parent =>
    switch (e) {
    | Cursor(_) => None
    | LArrow(z, h) =>
      if (isc_t(z)) {
        Some(Cursor(erase_typ(e)));
      } else {
        switch (mov_t(z, d)) {
        | None => None
        | Some(z) => Some(LArrow(z, h))
        };
      }
    | RArrow(h, z) =>
      if (isc_t(z)) {
        Some(Cursor(erase_typ(e)));
      } else {
        switch (mov_t(z, d)) {
        | None => None
        | Some(z) => Some(RArrow(h, z))
        };
      }
    }
  | Child(child) =>
    switch (e) {
    | Cursor(h) =>
      switch (h) {
      | Arrow(t1, t2) =>
        if (child == One) {
          Some(LArrow(Cursor(t1), t2));
        } else {
          Some(RArrow(t1, Cursor(t2)));
        }
      | _ => None
      }
    | LArrow(z, h) =>
      switch (mov_t(z, d)) {
      | None => None
      | Some(z) => Some(LArrow(z, h))
      }
    | RArrow(h, z) =>
      switch (mov_t(z, d)) {
      | None => None
      | Some(z) => Some(RArrow(h, z))
      }
    }
  };
};

let rec syn_action =
    (ctx: typctx, (e: zexp, t: htyp), a: action): option((zexp, htyp)) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  switch (a) {
  | Move(d) =>
    switch (mov(e, d)) {
    | Some(e') => Some((e', t))
    | _ => None
    }
  | _ => switch(e) {
    |Cursor(_)=>None 
    |LAp(z,h)=> switch(syn(ctx,erase_exp(z))){
      |None=>None 
      |Some(t2)=> switch(syn_action(ctx,(z,t2),a)){
        |None=>None 
        |Some((z',t3))=>switch(match(t3)){
          |Some(Arrow(t4,t5))=>
          if(ana(ctx,h,t4)){
            Some((LAp(z',h),t5))
          }
          else{None}
          |_=>None
        }
      }
    }
    |_=>None
  }
  };
}

and ana_action = (ctx: typctx, e: zexp, a: action, t: htyp): option(zexp) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = a;
  let _ = t;

  raise(Unimplemented);
};
