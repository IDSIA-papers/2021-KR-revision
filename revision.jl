using LogicCircuits
using TikzPictures
TikzPictures.standaloneWorkaround(true)

function random_cnf(literals, d, n)
        clauses = rand(1:length(literals),d,n)
        formula = LogicCircuit(true)
        for j in 1:d
                clause = LogicCircuit(false)
                for i = 1:n
                        if rand(Bool, 1)[1]
                                clause |= literals[clauses[j,i]]
                        else
                                clause |= !literals[clauses[j,i]]
                        end
                end
                formula &= clause
        end
        return formula
end

function random_dnf(l, d)
        formula = LogicCircuit(true)
        for j in 1:d
                clause = LogicCircuit(true)
                for i in 1:length(l)
                        if rand(Bool, 1)[1]
                                clause &= l[i]
                        else
                                clause &= !l[i]
                        end
                end
                formula |= clause
        end
        return formula
end



function dfs_vtree(v, n) # Find leaf n in vtree v
        current = v
        visited = Any[]
        stopping_condition = false
        while !stopping_condition
                if typeof(current) == PlainVtreeLeafNode
                        found = 0
                        if current.var == n found = 1 end
                        if !(current in visited) push!(visited,current) end
                        current = current.parent
                        if found == 1
                                if current.left.var == n #&& found == 1
                                        return [0,current.variables]
                                elseif current.right.var == n #&& found == 1
                                        return [1,current.variables] #
                                end
                        end
                elseif typeof(current) == PlainVtreeInnerNode
                        if !(current in visited) push!(visited,current) end
                        if !(current.left in visited)
                                current = current.left
                        elseif !(current.right in visited)
                                current = current.right
                        else
                                current = current.parent
                                if current == v
                                        if (current.left in visited) && (current.right in visited)
                                                stopping_condition = true
                                        end
                                end
                        end
                end
        end
end

function compute_resolvent(t,s)
        r = 0
        cnt = 0
        for a in t[2]
                if cnt == t[1] r=s*a end
                cnt += 1
        end
        return r
end

function dfs_sdd(s,target,status)
        resolvent = compute_resolvent(target, status)
        s2 = PlainLogicCircuit(s)
        current = s
        parent = s
        current2 = s2
        parent2 = s2
        story2 = Any[]
        story = Any[]
        visited = Any[]
        good = Any[]
        stopping = false
        push!(story,current)
        push!(story2,current2)
        while !stopping
                if (typeof(current) == Sdd⋁Node) # typeof(current) ==  ||Sdd⋀Node
                        if current.vtree.variables == target[2]
                                if !(current in good)
                                        push!(good,current)
                                        if target[1] == 0
                                                ll = Any[]
                                                rr = Any[]
                                                if current.children[1].prime.literal==resolvent
                                                        new = current2.children[1].children[2]
                                                        s2 = replace_node(s2, current2.children[2].children[2], new)
                                                else
                                                        new = current2.children[2].children[2]
                                                        s2 = replace_node(s2, current2.children[1].children[2], new)
                                                end
                                        end
                                end
                        end
                end
                if typeof(current) == Sdd⋁Node
                        blockedspace = true
                        for (child,child2) in zip(reverse(current.children),reverse(current2.children))
                                if !(child in visited)
                                        parent = current
                                        current = child
                                        parent2 = current2
                                        current2 = child2
                                        blockedspace = false
                                        break
                                end
                        end
                        if blockedspace
                                if findfirst(isequal(current),story) > 1
                                        current = story[findfirst(isequal(current),story)-1]
                                        current2 = story2[findfirst(isequal(current2),story2)-1]
                                else
                                        stopping = true
                                end
                        end
                elseif typeof(current) == Sdd⋀Node
                        toselect = 0
                        if !(current.prime in visited)
                                toselect = 1
                        elseif !(current.sub in visited)
                                toselect = 2
                        end
                        if toselect == 1
                                parent = current
                                current = current.prime
                                parent2 = current2
                                current2 = current2.children[1]
                        elseif toselect == 2
                                parent = current
                                current = current.sub
                                parent2 = current2
                                current2 = current2.children[2]
                        else
                                if findfirst(isequal(current),story) > 1
                                        current = story[findfirst(isequal(current),story)-1]
                                        current2 = story2[findfirst(isequal(current2),story2)-1]
                                else
                                        stopping = true
                                end
                        end
                elseif typeof(current) == SddLiteralNode || typeof(current) == SddFalseNode || typeof(current) == SddTrueNode
                        if typeof(current) == SddLiteralNode
                                if abs(current.literal) == abs(resolvent)
                                        if target[1] == 1 # right node
                                                new = compile(PlainLogicCircuit, false)
                                                if current.literal == resolvent
                                                        new = compile(PlainLogicCircuit, true)
                                                end
                                                s2 = replace_node(s2, current2, new)
                                        end
                                end
                        end
                        current = parent
                        current2 = parent2
                end
                if !(current in visited) push!(visited,current) end
        push!(story,current)
        push!(story2,current2)
        end
        return s2
end

function compute_resolvents(v,s)
        for i in 1:length(s.vtree.variables)
                mytarget2 = dfs_vtree(v,i)
                for j in [+1,-1]
                        big_resolvent = dfs_sdd(s,mytarget2,j)
                        if i==1 && j==1
                                @printf "[RES SINGLE] %d nodes and %d edges\n" num_nodes(big_resolvent) num_edges(big_resolvent);
                                println(model_count(big_resolvent,length(s.vtree.variables)));
                        end
                #resolvent_sdd2 = compile(big_manager, big_resolvent)
                #satisfies(big_resolvent,dnf2[1,:])
                end
        end
end

function compute_plain_resolvents(f,d, l)
        formula = LogicCircuit(false)
        for i in 1:length(l)
                for j in [+1,-1]
                        if j == +1
                                a = conjoin(cnf,l[i])
                        else
                                a = conjoin(cnf,-l[i])
                        end
                        formula |= (a & d)
                        #if i==1 && j==1
                        #end
                end
        end
        sat_prob(formula)
        @printf "[PLAIN] %d nodes and %d edges\n" num_nodes(formula) num_edges(formula);
end

function mysolver(n_bools,phi_size,mu_size,sat_size)
        l = [LogicCircuit(Lit(i)) for i in 1:n_bools]
        bvtree = PlainVtree(n_bools, :balanced) #rightlinear,leftlinear,random #DEBUG
        big_manager = SddMgr(bvtree)
        psi = random_cnf(l,phi_size,sat_size)
        mu = random_cnf(l,mu_size,sat_size)
        phi_sdd = compile(big_manager, psi)
        f = LogicCircuit(false)
        f2 = LogicCircuit(false)
        f3 = LogicCircuit(false)
        f4 = LogicCircuit(false)
        for i in 1:n_bools
                 f |= ((psi & l[i]) & mu) | ((psi & !l[i]) & mu)
                 f2 |= (psi & l[i]) | (psi & !l[i])
                 sdd1 = dfs_sdd(phi_sdd,dfs_vtree(bvtree,i),1)
                 sdd2 = dfs_sdd(phi_sdd,dfs_vtree(bvtree,i),-1)
                 sdd3 = (sdd1 & mu) | (sdd2 & mu)
                 f3 |= sdd3
        end
        f2 &= mu
        sdd4 = compile(big_manager, f3);
        for i in 1:n_bools
                 sdd1 = dfs_sdd(phi_sdd,dfs_vtree(bvtree,i),1)
                 sdd2 = dfs_sdd(phi_sdd,dfs_vtree(bvtree,i),-1)
                 sdd3 = sdd1 | sdd2
                 f4 |= sdd3
        end
        f4 &= mu
        sdd5 = compile(big_manager, f4);
        sdd_f = compile(big_manager, f);
        sdd_f2 = compile(big_manager, f2);
        @assert num_nodes(sdd4)==num_nodes(sdd5)
        @assert num_edges(sdd4) == num_edges(sdd5)
        @assert num_nodes(sdd_f)==num_nodes(sdd_f2)
        @assert num_edges(sdd_f) == num_edges(sdd_f2)
        return [n_bools phi_size mu_size sat_size num_edges(sdd5) num_edges(sdd_f2) num_edges(phi_sdd)] #,"-",num_edges(f2))#,"-",num_edges(sdd5))
end
