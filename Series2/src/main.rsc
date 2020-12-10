module main

import IO;
import Set;
import List;
import Type;
import Node;
import Location;

import util::Math;

import lang::java::m3::Core;
import lang::java::m3::AST;
import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;

import Helpers;

list[Declaration] getASTs(loc projectLocation){
	M3 model = createM3FromEclipseProject(projectLocation);
	list[Declaration] asts = [];
	
	for (m <- model.containment, m[0].scheme == "java+compilationUnit"){
		asts += createAstFromFile(m[0], true);
	}
	
	return asts;
}

// sort all nodes into buckets based on their names and the amount of children.
// Unsets keyword parameters from nodes as well!
map[str names, lrel[node, loc] nodes] sortBuckets(list[Declaration] asts, int minSize, int rounding, int minLoc) = 
			toMap([<"<getName(n)>-<arity(n)>-<roundToNearestX(nodeSize(n), rounding)>", <unsetRec(n), location>> |
																							 /node n := asts,
																							 nodeSize(n) > minSize,
																							 n.src?,
																							 loc location := n.src,
																							 countLinesOfCode(location) > minLoc]);

//map[str names, lrel[node, loc] nodes] sortBuckets(list[Declaration] asts, int minSize, int rounding, int minLoc) = 
//			toMap([<"<getName(n)>-<arity(n)>-<roundToNearestX(nodeSize(n), rounding)>", <unsetRec(n), location>> |
//																							 /node n := asts,
//																							 nodeSize(n) > 5,
//																							 n.src?,
//																							 loc location := n.src,
//																							 countLinesOfCode(location) > 2]);

// round to nearest x, used for catagorizing based on node size.
// checks if a modulo b is less then b / 2 ( which means it can be rounded down)
// else it is rounded up!
// example a:132, b:10, returns 130
// example a:138, b:10, returns 140												 
int roundToNearestX(int a, int b) = (a % b) < b / 2 ? a - (a % b) : a - (a % b) + b;


// Takes all nodes found in node n, and adds them to a list
list[node] convertToList(node n) = [x | /node x := n];

// Calculates the  subtree mass (number of nodes)
int nodeSize(node n) = (0 | it + 1 | /node _ := n);

/*
Similarity = 2 x S / (2 x S + L + R)
where:
S = number of shared nodes
L = number of different nodes in sub-tree 1
R = number of different nodes in sub-tree 2
*/
real calculateSimilarity(list[node] n1, list[node] n2){
	int S = size(n1 & n2);
	int L = size(n1 - n2);
	int R = size(n2 - n1);
	
	return 2 * S / toReal(2 * S + L + R);
}

// need src to be saved, even after cleaning!
void main(){
	list[Declaration] projectAST = getASTs(|project://smallsql0.21_src|);
	map[str names, lrel[node, loc] nodes] nodesMap = sortBuckets(projectAST, 25, 3, 2);
	//map[int id, lrel [node n, loc l] nodes] clonesMap = ();
	
	println(size(toList(nodesMap.names)));
	
	//int clones = 0;
	//int id = 0;
	//for (bucket <- nodesMap){
	//	lrel[node, loc] nodes = nodesMap[bucket];
	//	
	//	for (i <- [0 .. size(nodes)]) {	
	//		node node1 = nodes[i][0];
	//		list[node] nodeList1 = convertToList(node1);
	//		loc src1 = nodes[i][1];
	//		for (j <- [i+1 .. size(nodes)]) {
	//			node node2 = nodes[j][0];
	//			list[node] nodeList2 = convertToList(node2);
	//			loc src2 = nodes[j][1];
	//			
	//			if (src1.file == src2.file){
	//				if (src1.begin.line <= src2.begin.line && src1.end.line >= src2.end.line) continue;
	//				if (src2.begin.line <= src1.begin.line && src2.end.line >= src1.end.line) continue;
	//			}
	//			
	//			real similarity = calculateSimilarity(nodeList1, nodeList2);
	//			
	//			if (similarity == 1) {
	//				if (clonesMap[id]?) clonesMap[id] += [nodes[j]];
	//				else clonesMap[id] = [nodes[i], nodes[j]];
	//				clones+=1;
	//			};
	//		}
	//		id += 1;
	//	}
	//}
	//
	//println(clones);
}





