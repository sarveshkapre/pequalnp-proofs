class Encoder:
    """Construct a relaxation that includes every circuit in the assigned model."""
    def __init__(self,path):
        self.path=path
        self.body=path.with_suffix('.body')
        self.f=self.body.open('w')
        self.variables=self.clauses=0
    def var(self):
        self.variables+=1
        return self.variables
    def clause(self,*lits):
        self.f.write(' '.join(map(str,lits))+' 0\n')
        self.clauses+=1
    def choose(self,n):
        xs=[self.var() for _ in range(n)]
        self.clause(*xs)
        prev=None
        for x in xs[:-1]:
            nxt=self.var()
            self.clause(-x,nxt)
            if prev: self.clause(-prev,nxt); self.clause(-x,-prev)
            prev=nxt
        if prev: self.clause(-xs[-1],-prev)
        return xs
    def finish(self):
        import shutil
        self.f.close()
        with self.path.open('wb') as dst,self.body.open('rb') as src:
            dst.write(f'p cnf {self.variables} {self.clauses}\n'.encode())
            shutil.copyfileobj(src,dst)
        self.body.unlink()
    def mux(self,selectors, row):
        y=self.var()
        for s,x in zip(selectors,row,strict=True):
            self.clause(-s,-x,y)
            self.clause(-s,x,-y)
        return y
