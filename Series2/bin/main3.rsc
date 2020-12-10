module main3

import IO;
import Node;
import Type;
import List;
import Set;
import Map;

import util::Math;

import lang::java::m3::Core;
import lang::java::m3::AST;
import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;

list[Declaration] getASTs(loc projectLocation){
	M3 model = createM3FromEclipseProject(projectLocation);
	list[Declaration] asts = [];
	
	for (m <- model.containment, m[0].scheme == "java+compilationUnit"){
		asts += createAstFromFile(m[0], true);
	}
	
	return asts;
}


/*
Removal of variable, type, or function
identifiers.

This cleaning of the node is also used for hashing!
*/
node removeIdentifiers(node n){
	
	return visit(n){
		case \enum(str _, list[Type] implements, list[Declaration] constants, list[Declaration] body) => \enum("", implements, constants, body)
		case \enumConstant(str _, list[Expression] arguments, Declaration class) => \enumConstant("", arguments, class)
		case \enumConstant(str _, list[Expression] arguments) => \enumConstant("",  arguments)
		case \class(_, list[Type] extends, list[Type] implements, list[Declaration] body) => \class("",extends, implements, body)
		case \interface(_, list[Type] extends, list[Type] implements, list[Declaration] body) => \interface("", extends, implements, body)
		case \method(Type \return, _, list[Declaration] parameters, list[Expression] exceptions, Statement impl) => \method(string(), "", parameters,  exceptions, impl)
		case \method(Type \return, _, list[Declaration] parameters, list[Expression] exceptions) => \method(string(), "",  parameters, exceptions)
		case \constructor(_, list[Declaration] parameters, list[Expression] exceptions, Statement impl) => \constructor("", parameters, exceptions, impl)
		case \import(_) => \import("")
		case \package(_) => \package("")
		case \package(Declaration parentPackage, _) => \package(parentPackage, "")
		case \typeParameter(_, list[Type] extendsList) => \typeParameter("", extendsList)
		case \annotationType(_, list[Declaration] body) => \annotationType("", body)
		case \annotationTypeMember(_, _) => \annotationTypeMember(string(), "")
		case \annotationTypeMember(_, _, Expression defaultBlock) => \annotationTypeMember(string(), "", defaultBlock)
		case \parameter(_, _, int extraDimensions) => \parameter(string(), "", extraDimensions)
		case \vararg(_, _) =>  \vararg(string(), "")
		case \fieldAccess(bool isSuper, Expression expression, _) => \fieldAccess(isSuper, expression, "")
		case \fieldAccess(bool isSuper, _) => \fieldAccess(isSuper, "")
		case \methodCall(bool isSuper, _, list[Expression] arguments) => \methodCall(isSuper, "", arguments)
		case \methodCall(bool isSuper, Expression receiver, _, list[Expression] arguments) => \methodCall(isSuper, receiver, "", arguments)
		case \variable(_, int extraDimensions) => \variable("", extraDimensions)
		case \variable(_, int extraDimensions, Expression \initializer) => \variable("", extraDimensions, \initializer)
		case \simpleName(_) => \simpleName("")
		case \memberValuePair(_, Expression \value) => \memberValuePair("",  \value)
		case \label(_, Statement body) => \label("", body)
		case \field(_, list[Expression] fragments) => \field(string(), fragments)
		case \variables(_, list[Expression] \fragments) => \variables(string(), \fragments)
		case \break() => \break("")
		case \continue(_) => \continue("")
		
		case \newArray(_, list[Expression] dimensions, Expression init) => \newArray(string(), dimensions, init)
		case \newArray(_, list[Expression] dimensions) => \newArray(string(), dimensions)
		case \cast(_, Expression expression) => \cast(string(), expression)
		case \newObject(Expression expr, _, list[Expression] args, Declaration class) => \newObject(expr, string(), args, class)
		case \newObject(Expression expr, _, list[Expression] args) => \newObject(expr, string(), args)
		case \newObject(_, list[Expression] args, Declaration class) => \newObject(string(), args, class)
		case \newObject(_, list[Expression] args) => \newObject(string(), args)
		case arrayType(_) => arrayType(string())
		case parameterizedType(_) => parameterizedType(string())
		case upperbound(_) => upperbound(string())
		case lowerbound(_) => lowerbound(string())
		case \type(_) => \type(string())
		case \markerAnnotation(_) => \markerAnnotation("")
		case \normalAnnotation(_, list[Expression] memberValuePairs) => \normalAnnotation("", memberValuePairs)
		case \singleMemberAnnotation(_, Expression \value) => \singleMemberAnnotation("", \value)
	}
}

// Calculates the  subtree mass (number of nodes)
int nodeSize(node n) = (0 | it + 1 | /node _ := n);

str hashNode(node n) {
	list[str] hashCode = [getName(n)];
	
	visit (n){
		case node x: hashCode += getName(x);
	}
	
	return intercalate(" ", hashCode);
}

 //returns 0 if false; returns 1 if file 2 within file 1; returns 2 if file 1 within file 2
int checkIfPartOf(loc file1, loc file2){
	
	if (file2 < file1)	return 1;
	if (file1 < file2) return 2;
	
	return 0;
}

map[str, rel[node n, loc l]] makeCloneClasses(map[str, lrel[node, loc]] nodeMap){
	map [str class, rel[node n, loc l] nodes] cloneClasses = ();
	
	for (bucket <- nodeMap) {
		lrel[node n, loc l] nodes = dup(nodeMap[bucket]);
		if (size(nodes) > 1) {
			for (i <- [0 .. size(nodes)]) {	
				node node1 = nodes[i][0];
				loc src1 = nodes[i][1];
				list[node] nodeList1 = convertToList(node1);
				
				for (j <- [i+1 .. size(nodes)]){
					node node2 = nodes[j][0];
					loc src2 = nodes[j][1];
					list[node] nodeList2 = convertToList(node2);
					
					if (checkIfPartOf(src1, src2) != 0) continue;
					
					if (calculateSimilarity(nodeList1, nodeList2) == 1){
						str key = toString(node1);
						if (cloneClasses[key]?) cloneClasses[key] += {nodes[j]};
						else cloneClasses[key] = {nodes[i], nodes[j]};
					}
				}
			}
		}
	}	
	
	return cloneClasses;
}

// Takes all nodes found in node n, and adds them to a list
list[node] convertToList(node n) = [x | /node x := n];

/*
Similarity = 2 x S / (2 x S + L + R)
where:
S = number of shared nodes
L = number of different nodes in sub-tree 1
R = number of different nodes in sub-tree 2
*/
real calculateSimilarity(list[node] n1, list[node] n2){
	int S = size(n1 & n2);
	int L = size(n1) - S;
	int R = size(n2) - S;
	
	return 2 * S / toReal(2 * S + L + R);
}

// catagorizes the nodes in buckets based on their subtrees with identifiers and keyword parameters removed
map[str hashes, lrel[node n, loc l] nodes] catagorizeNodes(list[Declaration] asts, int minMass) {
	map[str hashes, lrel[node n, loc l] nodes] nodeMap = ();

	visit (asts){
		case node n: ({
			int nodeMass = nodeSize(n);
			if (nodeMass > minMass && n.src? && loc location := n.src) {
				node cleaned = unsetRec(n);
				str hash = toString(removeIdentifiers(cleaned));
							
				if (nodeMap[hash]?) nodeMap[hash] += [<cleaned, location>];
				else nodeMap[hash] = [<cleaned, location>];
			}
		});
	}
	
	return nodeMap;
}

// returns 0 if false; returns 1 if file 2 within file 1; returns 2 if file 1 within file 2
int checkIfPartOf(loc file1, loc file2){
	if (file1.file == file2.file){
		if (file1.begin.line <= file2.begin.line && file1.end.line >= file2.end.line) {
			return 1;
		};
		if (file2.begin.line <= file1.begin.line && file2.end.line >= file1.end.line) return 2;
	}
	
	return 0;
}

 //returns 0 if false; returns 1 if file 2 within file 1; returns 2 if file 1 within file 2
int checkIfPartOf(loc file1, loc file2){
	
	if (file2 < file1)	return 1;
	if (file1 < file2) return 2;
	
	return 0;
}

rel[tuple[node, loc], tuple[node, loc]] makeClonePairs(rel[node n, loc l] clones){
		clonesList = toList(clones);
		rel[tuple[node, loc], tuple[node, loc]] clonePairs = {};
		
		for (i <- [0..size(clonesList)]) {
			for (j <- [i+1 .. size(clonesList)]){
				clonePairs += {<clonesList[i],clonesList[j]>};
			}
		}
		
		return clonePairs;
}

map[str, rel[node n, loc l]] makeCloneClasses(map[str, lrel[node, loc]] nodeMap){
	map [str class, rel[node n, loc l] nodes] cloneClasses = ();
	
	for (bucket <- nodeMap) {
		lrel[node n, loc l] nodes = dup(nodeMap[bucket]);
		if (size(nodes) > 1) {
			for (i <- [0 .. size(nodes)]) {	
				node node1 = nodes[i][0];
				loc src1 = nodes[i][1];
				list[node] nodeList1 = convertToList(node1);
				
				for (j <- [i+1 .. size(nodes)]){
					node node2 = nodes[j][0];
					loc src2 = nodes[j][1];
					list[node] nodeList2 = convertToList(node2);
					
					if (checkIfPartOf(src1, src2) != 0) continue;
					
					if (calculateSimilarity(nodeList1, nodeList2) == 1){
						str key = toString(node1);
						if (cloneClasses[key]?) cloneClasses[key] += {nodes[j]};
						else cloneClasses[key] = {nodes[i], nodes[j]};
					}
				}
			}
		}
	}	
	
	return cloneClasses;
}

void main(){
	list[Declaration] projectAST = getASTs(|project://smallsql0.21_src|);
	
	int minimalMass = 10;
	map[str hashes, lrel[node n, loc l] nodes] nodeMap = ();

	visit (projectAST){
		case node n : ({
			node cleaned = unsetRec(n);
			if (nodeSize(cleaned) > minimalMass) {
				if (n.src? && loc location := n.src) {
					//str hash = toString(cleaned);
					str hash = hashNode(n);
					if (nodeMap[hash]?) nodeMap[hash] += [<cleaned, location>];
					else nodeMap[hash] = [<cleaned, location>];
				}
			}
		});
	}
	
	map [str class, rel[node n, loc l] nodes] cloneClasses = makeCloneClasses(nodeMap);
	
	int cloneCount = 0;
		
	for (class <- cloneClasses) {
		rel[node n, loc l] clones = cloneClasses[class];
		if (size(toList(clones)) > 2){
			println(nodeSize(getOneFrom(clones).n));
			
			for (clone <- clones) {
				println(clone.l);
				cloneCount += 1;
			}
			println("----------");
		}
	}
	
	println(cloneCount);
}