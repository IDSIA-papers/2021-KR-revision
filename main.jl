using LogicCircuits
using TikzPictures
using DataFrames
using Random
using Printf
using Plots
using CSV
using Statistics
TikzPictures.standaloneWorkaround(true)
include("revision.jl")

if false
        nvars = 4
        L = LogicCircuit(Lit(1))
        K = LogicCircuit(Lit(2))
        P = LogicCircuit(Lit(3))
        A = LogicCircuit(Lit(4))
        formula = ( !L & K  & P & A) | (L & ((!P & !A)|P)  ) | ( !L & !K & P )
        vtree2 = PlainVtree(nvars, :balanced)
        manager = SddMgr(vtree2)
        sdd = compile(manager, formula);
        mu = DataFrame(BitArray([ 0 1 0 1; 1 0 0 1]), :auto)
        revision = Any[]
        for i in 1:nvars
                target = dfs_vtree(vtree2,i)
                for j in [+1,-1]
                        resolvent = dfs_sdd(sdd,target,j)
                        push!(revision, satisfies(resolvent, mu))
                        resolvent_sdd = compile(manager, resolvent)
                end
        end
        println(revision)
end

df = DataFrame(n_vars=Int[], phi_size=Int[], mu_size=Int[], sat_size=Int[], revised_sdd=Int[], formula=Int[], sdd=Int[])
for n in [32]
        df_small = DataFrame(n_vars=Int[], phi_size=Int[], mu_size=Int[], sat_size=Int[], revised_sdd=Int[], formula=Int[], sdd=Int[])
        @time begin
        for k in 1:10 #100 50
                row = mysolver(n,Int(n/2),Int(n/2),3) #400
                println(row)
                push!(df,row)
                push!(df_small,row)
        end
        println("(",n,",",mean(df_small.revised_sdd),")+-(0.0,",std(df_small.revised_sdd),")")
        println("(",n,",",mean(df_small.formula),")+-(0.0,",std(df_small.formula),")")
        end
end
#print(df)
#df2 = df[df.revised_sdd .!=1,:]
CSV.write("/Users/antonucci/a.csv", df)
