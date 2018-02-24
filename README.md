## Notes on bytecode

    (lambda (y) (f ((lambda (x) (g x)) (h y))))

    env: [f g h]
    args: [y]
    lits: [1 C2 [] 1 g]
    code: C1

    C1:
      0  FRAME 1
      1  ENV f
      2  FRAME 1
      3  CLO 1 C2 [] 1 g
      4  FRAME 1
      5  ENV h
      6  ARG y
      7  CALL
      8  CALL
      9  JUMP

    C2:
      0  FRAME 1
      1  ENV g
      2  ARG x
      3  JUMP


    (lambda () (f ((lambda () 123)) 234))

    F0 = [0 C3 [0 C4 [123] 0 234] f]

    C3:
      0  FRAME 2
      1  ENV f
      2  FRAME 0
      3  CLO 0 C4 [123] 0
      4  CALL
      5  LIT 234
      6  JUMP

    C4:
      0  LIT 123
      1  RET

Revised instruction list:

    LIT
    ENV
    ARG
    FRAME
    JUMP
    CALL
    RET
    CLO

Registers:

    A = args; A[0] = closure, A[0][1] = code, A[0][2] = lits, A[0][3..] = env
    I = instruction pointer
    F = frame
    T = target index in frame
    K = continuation

    A[0][1][I] = LIT n    ==> F[T++] <- A[0][2][n]; I++
    A[0][1][I] = ENV n    ==> F[T++] <- A[0][n+3];  I++
    A[0][1][I] = ARG n    ==> F[T++] <- A[n+1];     I++

    A[0][1][I] = FRAME n  ==> K <- [F,T,K]; F <- new vec length n; T <- 0; I++

    A[0][1][I] = JUMP     ==> T <- K[1];            A <- F; F <- K[0];            K <- K[2]; I <- 0
    A[0][1][I] = CALL     ==> T <- K[1]; K[1] <- A; A <- F; F <- K[0]; K[0] <- I;            I <- 0
    A[0][1][I] = RET      ==>            A <- K[1];                    I <- K[0]; K <- K[2]; I++

Before

    A=x I=y F=z T=n K=[u,v,w]

After `JUMP`

    A=z I=0 F=u T=v K=w

After `CALL`

    A=z I=0 F=u T=v K=[y,x,w]

So for `CALL`:

    A=x I=y F=z T=n K=[u,v,w]
    A=x I=y F=z T=v K=[u,v,w]   T <- K[1]
    A=x I=y F=z T=v K=[u,x,w]   K[1] <- A
    A=z I=y F=z T=v K=[u,x,w]   A <- F
    A=z I=y F=u T=v K=[u,x,w]   F <- K[0]
    A=z I=y F=u T=v K=[y,x,w]   K[0] <- I
    A=z I=0 F=u T=v K=[y,x,w]   I <- 0
    A=z I=0 F=u T=v K=[y,x,w]

OK, now let's try to squash K's slots into the frame.

F and T move together: T could be part of F. Let's do that first.

    T = F[F.len - 1], and F is overallocated by one slot.

    A = args; A[0] = closure, A[0][1] = code, A[0][2] = lits, A[0][3..] = env
    I = instruction pointer
    F = frame; F[F.len - 1] = target index in frame
    K = continuation

    A[0][1][I] = LIT n    ==> F[F[F.len-1]++] <- A[0][2][n]; I++
    A[0][1][I] = ENV n    ==> F[F[F.len-1]++] <- A[0][n+3];  I++
    A[0][1][I] = ARG n    ==> F[F[F.len-1]++] <- A[n+1];     I++

    A[0][1][I] = FRAME n  ==> K <- [F,0,K]; F <- new vec length n+1; F[F.len-1] <- 0; I++

    A[0][1][I] = JUMP     ==>            A <- F; F <- K[0];            K <- K[2]; I <- 0
    A[0][1][I] = CALL     ==> K[1] <- A; A <- F; F <- K[0]; K[0] <- I;            I <- 0
    A[0][1][I] = RET      ==> A <- K[1];                    I <- K[0]; K <- K[2]; I++

Now observe that allocation of K and allocation of F always happen together.

`A` is discarded without even being examined at every `JUMP`, `CALL`
and `RET`. Thus, its `T` slot must already be garbage.

Setting aside effects to the actual operator or operand slots in `F`,
the net effect of a `FRAME`..`CALL` sequence is (or rather, has to
be):

    A=x I=y+0 F=z K=w           FRAME n
    A=x I=y+1 F=u K=[z,0,w]     where u is a new vector length n+1
     ⋮
    A=x I=y+m F=u K=[z,0,w]     CALL
    A=u I=0   F=z K=[y+m,x,w]

That is,

 - `A` gets a new frame (and its `T` slot is immediately dead)
 - `I` becomes zero
 - `K` saves the `A` and `I` as of the moment of the `CALL`, plus the
   `K` as of the moment of the `FRAME`.

Then, a `RET` yields:

    A=u I=0     F=z K=[y+m,x,w]
     ⋮
    A=u I=v     F=z K=[y+m,x,w]   RET
    A=x I=y+m+1 F=z K=w

but `z` has been updated.

The net effect of a `FRAME`..`JUMP` is:

    A=x I=y+0 F=z K=w           FRAME n
    A=x I=y+1 F=u K=[z,0,w]     where u is a new vector length n+1
     ⋮
    A=x I=y+m F=u K=[z,0,w]     JUMP
    A=u I=0   F=z K=w

That is,

 - `A` gets a new frame (and its `T` slot is immediately dead)
 - `I` becomes zero

and that's all.

So for a `JUMP`, we don't have to save away anything, because any
eventual `RET` is paired with an earlier `CALL`.

But for a `CALL` we need space to save an `I`, an `A`, and a `K`.

Bearing in mind that `A`'s `T` slot is immediately dead - could we put
`I` and `K` in the `A`, taking that as the entire continuation?

    When a frame is being built:
      T = F[F.len - 1], and F is overallocated by two slots.
      F[F.len - 2] is a link to the previous frame.
    When a frame has transitioned to being active arguments,
      - it may be the result of a FRAME/JUMP, so its ultimate slots may be unused
      - it may be the result of a FRAME/CALL, and if so,
         - its penultimate slot is the saved I
         - its ultimate slot is the saved A (= K)

    A = args; A[0] = closure, A[0][1] = code, A[0][2] = lits, A[0][3..] = env
    I = instruction pointer
    F = frame; F[F.len - 1] = target index in frame

    A[0][1][I] = LIT n    ==> F[F[F.len-1]++] <- A[0][2][n]; I++
    A[0][1][I] = ENV n    ==> F[F[F.len-1]++] <- A[0][n+3];  I++
    A[0][1][I] = ARG n    ==> F[F[F.len-1]++] <- A[n+1];     I++

    A[0][1][I] = FRAME n  ==> F <- [0, 0, ...(n+1 times), F, 0]; I++

    A[0][1][I] = JUMP     ==> tmp <- F[F.len-2]; F[F.len-2] <- A[A.len-2]; F[F.len-1] <- A[A.len-1]; A <- F; F <- tmp; I <- 0
    A[0][1][I] = CALL     ==> F[F.len-1] <- A; A <- F; F <- A[A.len-2]; A[A.len-2] <- I; I <- 0
    A[0][1][I] = RET      ==> I <- A[A.len-2]; A <- A[A.len-1]; I++

Working through the net effect of `FRAME`/`CALL`/`RET` again:

    A=x             I=y+0   F=z              FRAME n
    A=x             I=y+1   F=[0,...,z,0]
     ⋮
    A=x             I=y+m   F=[q,...,z,n+1]  CALL
    A=[q,...,y+m,x] I=0     F=z
     ⋮
    A=[q,...,y+m,x] I=v     F=z              RET
    A=x             I=y+m+1 F=z

And `FRAME`/`JUMP`:

    A=[...,w,x]     I=y+0   F=z              FRAME n
    A=[...,w,x]     I=y+1   F=[0,...,z,0]
     ⋮
    A=[...,w,x]     I=y+m   F=[q,...,z,n+1]  JUMP
    A=[q,...,w,x]   I=0     F=z

Finally, the one instruction not yet treated, `CLO`. The argument to
the instruction points to a number of consecutive slots in the
literals vector, containing arity, codepointer, literalspointer,
capturecount, and capture specifications, in that order. Each capture
specification is a number: an environment reference to index x is
stored as (-1 - x), and an argument reference to x is stored as x.

    A[0][1][I] = CLO n    ==> F[T++] <- [A[0][2][n], A[0][2][n+1], A[0][2][n+2],
                                         f(0), ..., f(A[0][2][n+3] - 1)];
                              I++
                              where spec(i) = A[0][2][i+4]
                              where f(i) = / A[0][(-1 - spec(i))+3] if spec(i) < 0
                                           \ A[spec(i)+1]           if spec(i) >= 0
