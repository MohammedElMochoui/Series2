module Type1

import IO;
import Node;
import List;
import Set;
import Map;
import String;
import Location;

import util::Math;

import Helpers;

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

// Calculates the  subtree mass (number of nodes)
int nodeSize(node n) = (0 | it + 1 | /node _ := n);

//rel[loc, loc] makePairs(set[loc] nodeList) {
//	list[loc] nodes = toList(nodeList);
//	rel[loc, loc] clonePairs = {};
//	
//	for (a <- nodeList, b <- nodeList, a != b){
//		clonePairs += {<a, b>};
//	}
//	
//	return clonePairs;
//}

rel[loc, loc] makePairs(set[loc] nodeList) {
	list[loc] nodes = toList(nodeList);
	rel[loc, loc] clonePairs = {};
	
	for (i <- [0 .. size(nodeList)], j <- [i+1 .. size(nodeList)]) {
		clonePairs += {<nodes[i], nodes[j]>};
	}
	
	return clonePairs;
}


str hash(node n) {

	str modifiers = "";
	
	if (getAnnotations(n)["modifiers"]? && list[value] annoMod := getAnnotations(n)["modifiers"]){
		modifiers = toString(annoMod);
	}

	node cleanedNode = delAnnotationsRec(n);
	return modifiers + toString(cleanedNode);
}

list[list[node]] makeSequences(list[node] x, int minLength) = [subsequence | j <- [minLength .. size(x)], i <-[0..size(x)-j+1], subsequence := x[i..i+j], size(subsequence)==j];

str hashSeq(list[node] nodeList) {

	list[str] hashes = [getHash(getAnnotations(n)["hash"]) | n <- nodeList];
	return intercalate("", hashes);
}

loc getLocation(value l) {
	switch(l) {
		case loc m: return m;
	}
	
	return |home:///path|;
}

str getHash(value s) {
	switch(s) {
		case str m: return m;
	}
	
	return "";
}

tuple[map[str keys, set[loc] nodeList], set[loc]] processSeq(list[node] x, map[str keys, set[loc] nodeList] nodeMap, set[loc] seenLocations) {
	map[str keys, set[loc] nodeList] nodeMap2 = nodeMap;
	set[loc] seenLocations2 = seenLocations;

	int minLength = 4;
	if (size(x) > minLength){		
	
		list[list[node]] subsequences = makeSequences(x, minLength);
		list[str] hashes = [getHash(getAnnotations(n)["hash"]) | n <- x ];
		
		for (j <- [minLength .. size(x)], i <-[0..size(x)-j+1]){
			subsequence = x[i..i+j];
			if (size(subsequence)==j){
				
				loc first = getLocation(getAnnotations(subsequence[0])["src"]);
        		loc last = getLocation(getAnnotations(subsequence[-1])["src"]);
				
				if (first.file  == last.file) {
					loc location = first.top(first.offset, last.offset + last.length - first.offset, 
		                           <first.begin.line, first.begin.column>,
		                           <last.end.line, last.end.column>);
									
					if(location notin seenLocations2 && (location.end.line - location.begin.line > 6)){
						str key = intercalate("", hashes[i .. i+j]);
						if (nodeMap2[key]?) nodeMap2[key] += {location};
						else nodeMap2[key] = {location};
						seenLocations2 += {location};
					}
				}
			}
		}
	}
	return <nodeMap2, seenLocations2>;
}

void type1(){
	list[Declaration] projectAST = getASTs(|project://smallsql0.21_src|);
	map[str keys, set[loc] nodeList] nodeMap = ();
	set[loc] seenLocations = {};
		
	cleanedAST = visit (projectAST){
		case node n: ({
			if (n.src?) {
				map[str keys , value values] keywords = getKeywordParameters(n);
				node cleanedNode = unset(n);
				loc location = getLocation(n.src);
				
				if (keywords["modifiers"]?) cleanedNode = setAnnotations(cleanedNode, ("modifiers":keywords["modifiers"]));
				
				str key = hash(cleanedNode);
				map[str, value] annotations = ("src":location, "hash":key);
				
				//cleanedNode = setAnnotations(cleanedNode, annotations);
							
				if (nodeSize(n) > 20){
					if (location notin seenLocations) {						
						if (nodeMap[key]?) nodeMap[key] += {location};
						else nodeMap[key] = {location};
						seenLocations += {location};
					}
				}
				
				if (keywords["modifiers"]?) annotations["modifiers"] = keywords["modifiers"];
				cleanedNode = setAnnotations(cleanedNode, annotations);
				insert cleanedNode;
			}
		});
	}
	
	//map[str keys, set[loc] nodeList] sequenceMap = ();
		
	//visit(cleanedAST){
	//	case \class(_, _, _, list[Declaration] body): ({
	//		tuple[map[str keys, set[loc] nodeList], set[loc]] mapseen = processSeq(body, nodeMap, seenLocations);
	//		nodeMap = mapseen[0];
	//		seenLocations = mapseen[1];
	//	});
	//	case \interface(_, _, _, list[Declaration] body): ({
	//		tuple[map[str keys, set[loc] nodeList], set[loc]] mapseen = processSeq(body, nodeMap, seenLocations);
	//		nodeMap = mapseen[0];
	//		seenLocations = mapseen[1];
	//	});
	//	case \enum(_, _, _, list[Declaration] body): ({
	//		tuple[map[str keys, set[loc] nodeList], set[loc]] mapseen = processSeq(body, nodeMap, seenLocations);
	//		nodeMap = mapseen[0];
	//		seenLocations = mapseen[1];
	//	});
	//	case \block(list[Statement] statements) : ({
	//		tuple[map[str keys, set[loc] nodeList], set[loc]] mapseen = processSeq(statements, nodeMap, seenLocations);
	//		nodeMap = mapseen[0];
	//		seenLocations = mapseen[1];
	//	});
	//	case \class(list[Declaration] body): ({
	//		tuple[map[str keys, set[loc] nodeList], set[loc]] mapseen = processSeq(body, nodeMap, seenLocations);
	//		nodeMap = mapseen[0];
	//		seenLocations = mapseen[1];
	//	});
	//}
	
	visit(cleanedAST){
		case \class(_, _, _, list[Declaration] body): ({
			list[node] x = body;
			int minLength = 4;
			if (size(x) > minLength){		
			
				list[list[node]] subsequences = makeSequences(x, minLength);
				list[str] hashes = [getHash(getAnnotations(n)["hash"]) | n <- x ];
				
				for (j <- [minLength .. size(x)], i <-[0..size(x)-j+1]){
					subsequence = x[i..i+j];
					if (size(subsequence)==j){
						
						loc first = getLocation(getAnnotations(subsequence[0])["src"]);
		        		loc last = getLocation(getAnnotations(subsequence[-1])["src"]);
						
						if (first.file  == last.file) {
							loc location = first.top(first.offset, last.offset + last.length - first.offset, 
				                           <first.begin.line, first.begin.column>,
				                           <last.end.line, last.end.column>);
											
							if(location notin seenLocations && (location.end.line - location.begin.line > 6)){
								str key = intercalate("", hashes[i .. i+j]);
								if (nodeMap[key]?) nodeMap[key] += {location};
								else nodeMap[key] = {location};
								seenLocations += {location};
							}
						}
					}
				}
			}
		});
		
		case \interface(_, _, _, list[Declaration] body): ({
			list[node] x = body;
			int minLength = 4;
			if (size(x) > minLength){		
			
				list[list[node]] subsequences = makeSequences(x, minLength);
				list[str] hashes = [getHash(getAnnotations(n)["hash"]) | n <- x ];
				
				for (j <- [minLength .. size(x)], i <-[0..size(x)-j+1]){
					subsequence = x[i..i+j];
					if (size(subsequence)==j){
						
						loc first = getLocation(getAnnotations(subsequence[0])["src"]);
		        		loc last = getLocation(getAnnotations(subsequence[-1])["src"]);
						
						if (first.file  == last.file) {
							loc location = first.top(first.offset, last.offset + last.length - first.offset, 
				                           <first.begin.line, first.begin.column>,
				                           <last.end.line, last.end.column>);
											
							if(location notin seenLocations && (location.end.line - location.begin.line > 6)){
								str key = intercalate("", hashes[i .. i+j]);
								if (nodeMap[key]?) nodeMap[key] += {location};
								else nodeMap[key] = {location};
								seenLocations += {location};
							}
						}
					}
				}
			}
		});

		case \enum(_, _, _, list[Declaration] body): ({
			list[node] x = body;
			int minLength = 4;
			if (size(x) > minLength){		
			
				list[list[node]] subsequences = makeSequences(x, minLength);
				list[str] hashes = [getHash(getAnnotations(n)["hash"]) | n <- x ];
				
				for (j <- [minLength .. size(x)], i <-[0..size(x)-j+1]){
					subsequence = x[i..i+j];
					if (size(subsequence)==j){
						
						loc first = getLocation(getAnnotations(subsequence[0])["src"]);
		        		loc last = getLocation(getAnnotations(subsequence[-1])["src"]);
						
						if (first.file  == last.file) {
							loc location = first.top(first.offset, last.offset + last.length - first.offset, 
				                           <first.begin.line, first.begin.column>,
				                           <last.end.line, last.end.column>);
											
							if(location notin seenLocations && (location.end.line - location.begin.line > 6)){
								str key = intercalate("", hashes[i .. i+j]);
								if (nodeMap[key]?) nodeMap[key] += {location};
								else nodeMap[key] = {location};
								seenLocations += {location};
							}
						}
					}
				}
			}
		});

		case \block(list[Statement] statements) : ({
			list[node] x = statements;
			int minLength = 4;
			if (size(x) > minLength){		
			
				list[list[node]] subsequences = makeSequences(x, minLength);
				list[str] hashes = [getHash(getAnnotations(n)["hash"]) | n <- x ];
				
				for (j <- [minLength .. size(x)], i <-[0..size(x)-j+1]){
					subsequence = x[i..i+j];
					if (size(subsequence)==j){
						
						loc first = getLocation(getAnnotations(subsequence[0])["src"]);
		        		loc last = getLocation(getAnnotations(subsequence[-1])["src"]);
						
						if (first.file  == last.file) {
							loc location = first.top(first.offset, last.offset + last.length - first.offset, 
				                           <first.begin.line, first.begin.column>,
				                           <last.end.line, last.end.column>);
											
							if(location notin seenLocations && (location.end.line - location.begin.line > 6)){
								str key = intercalate("", hashes[i .. i+j]);
								if (nodeMap[key]?) nodeMap[key] += {location};
								else nodeMap[key] = {location};
								seenLocations += {location};
							}
						}
					}
				}
			}
		});

		case \class(list[Declaration] body): ({
			list[node] x = body;
			int minLength = 4;
			if (size(x) > minLength){		
			
				list[list[node]] subsequences = makeSequences(x, minLength);
				list[str] hashes = [getHash(getAnnotations(n)["hash"]) | n <- x ];
				
				for (j <- [minLength .. size(x)], i <-[0..size(x)-j+1]){
					subsequence = x[i..i+j];
					if (size(subsequence)==j){
						
						loc first = getLocation(getAnnotations(subsequence[0])["src"]);
		        		loc last = getLocation(getAnnotations(subsequence[-1])["src"]);
						
						if (first.file  == last.file) {
							loc location = first.top(first.offset, last.offset + last.length - first.offset, 
				                           <first.begin.line, first.begin.column>,
				                           <last.end.line, last.end.column>);
											
							if(location notin seenLocations && (location.end.line - location.begin.line > 6)){
								str key = intercalate("", hashes[i .. i+j]);
								if (nodeMap[key]?) nodeMap[key] += {location};
								else nodeMap[key] = {location};
								seenLocations += {location};
							}
						}
					}
				}
			}
		});
	}
	
	map[str keys, set[loc] nodeList] removedSubCloneMap = ();
	for (class <- nodeMap) {
		set[loc] nodeList = nodeMap[class];
		if (size(nodeList) > 1) {
			rel[loc first, loc second] clonePairs = makePairs(nodeList);
			for (pair <- clonePairs) {
				bool addition = true;
				
				for (restClass <- delete(nodeMap, class)) {
					set[loc] restList = nodeMap[restClass];
					if (size(restList) > 1) {
						rel[loc first, loc second] restPairs = makePairs(restList);
						
						
						for (restPair <- restPairs) {
							if ((isContainedIn(pair.first, restPair.first) && isContainedIn(pair.second, restPair.second)) || 
								(isContainedIn(pair.first, restPair.second) && isContainedIn(pair.second, restPair.first))) {
								addition = false;
								//println(pair.first);
								//println(pair.second);
								//println(restPair.first);
								//println(restPair.second);
								//println("--------");
								break;
							}
						}
					}
					
					if (!addition) break;
				}
				
				if (addition) {
					if (removedSubCloneMap[class]?) removedSubCloneMap[class] += {pair.first, pair.second};
					else removedSubCloneMap[class] = {pair.first, pair.second};
				}
			}
		}
	}
	
	int cloneCount = 0;
	int classesCount = 0;
	
	for (class <- removedSubCloneMap) {
		set[loc] clones = removedSubCloneMap[class];
		if (size(clones) > 1){
			classesCount += 1;
			for(s <- clones){
				println(s);
				cloneCount += 1;
			}
			println("-----");
		}
	}
	
	println(size(removedSubCloneMap.keys));	
	println(cloneCount);
	println(classesCount);
	
}
