# 계획

이 프로젝트의 장기 목표는 Lean 4와 mathlib 위에서 Courcelle theorem을
형식화하는 것이다. MSO2 문법과 의미론은 그 자체가 최종 목적이라기보다,
유한 단순 그래프의 bounded treewidth 위에서 MSO2 model checking을 다루기 위한
기반 계층이다.

그래프 표현은 mathlib의 `SimpleGraph V`로 둔다. MSO2의 간선 1차 변수와
간선 집합 2차 변수는 `G : SimpleGraph V`가 주어졌을 때
`G.edgeSet : Set (Sym2 V)`의 subtype 위를 돈다. **source 의미론**(MSO2 over
`SimpleGraph`)에는 별도의 incidence graph compatibility layer를 두지 않는다.

증명 파이프라인은 고정 유한 vocabulary `τ_P = {adj} ∪ P` (그래프 + 유한 unary
predicate 집합 `P`) 위의 MSO를 다룬다(`Courcelle/lecture_note_expanded.tex`,
2026-06 개정). 평범한 그래프 경우는 `P = ∅`이다. 이 하나의 `τ_P` 파이프라인에
두 가지가 들어간다.

- `P = ∅`: `G` 위 **MSO1 over `{adj}`**를 직접 `Σ`-tree 위 MSO로 해석한 뒤
  regular tree language / finite tree automata를 사용한다(treewidth `ω`).
  MSO1-definable graph property는 incidence를 거치지 않는 이 직접 경로로 간다.
- `P = {Vert, EObj}`: **MSO2**는 coloured incidence structure `Î(G)`
  (universe `V ⊔ E`, vocabulary `τ_I = {adj, Vert, EObj}`)로 환원하여 얻는다.
  `Vert`/`EObj`는 vocabulary의 일부이며 adjacency에서 복원하지 않는다
  (treewidth `max(ω, 2)`).

따라서 장기 정리 단계는 core `SimpleGraph`/`G.edgeSet` source 의미론을 흔들지
않고, `τ_P` 위 번역 계층과 그 위에 MSO2용 incidence 환원만 얇게 얹는다.

## 현재 상태

- `lakefile.toml`
  - mathlib `v4.28.0-rc1`에 의존한다.
  - `lake-manifest.json`에는 mathlib와 transitive dependency들이 고정되어 있다.
- `GraphMSO.Syntax`
  - 1차 정점 변수 `FOVar`, 2차 정점 변수 `SOVar`, 1차 간선 변수 `EdgeFOVar`,
    2차 간선 변수 `EdgeSOVar`는 현재 모두 `Nat`이다.
  - 원자식은 `false_`, `equal`, `edge`, `inSet`, `equalEdge`, `inc`, `inEdgeSet`이다.
  - `Formula.FreeFO`, `Formula.FreeSO`, `Formula.FreeEdgeFO`, `Formula.FreeEdgeSO`,
    `Formula.Closed`가 있다.
- `GraphMSO.Semantics`
  - `Assignment V E` 하나가 free-variable 의미론과 닫힌 문장 의미론을 모두 담당한다.
  - 정점 1차 변수와 간선 1차 변수는 `Option V`, `Option E`로 해석한다. 값이 없는
    1차 변수는 원자식에서 false가 되며, 양화자는 update를 통해 값을 넣는다.
  - 정점 집합과 간선 집합 assignment는 별칭 없이 `Set V`, `Set E`로 표현한다.
  - `SimpleGraph V` 의미론에서는 edge sort를 `G.edgeSet`으로 특수화해
    `Assignment V G.edgeSet`을 사용한다.
  - `Semantics.SatisfiesAt : Formula -> (G : SimpleGraph V) -> Assignment V G.edgeSet -> Prop`가
    assignment-aware Tarski 의미론이다.
  - `Semantics.Satisfies G phi`가 닫힌 공식용 graph satisfaction 계층이다. 현재 정의는
    `phi.Closed`와 `SatisfiesAt phi G Assignment.empty`의 conjunction이다.
  - `edge x y`는 두 정점 변수가 값 `u`, `v`로 배정되어 있고 `G.Adj u v`일 때 참이다.
  - `inc x e`는 정점 변수 값 `v`와 간선 변수 값 `e : G.edgeSet`이 있고
    `v ∈ (e : Sym2 V)`일 때 참이다.
- `GraphMSO.Basic`
  - 삭제되었다. 각 모듈은 필요한 mathlib 모듈을 직접 import한다.
- `GraphMSO.Examples`
  - clique, independent set, dominating set, vertex cover, bipartite, perfect matching,
    connectivity, coloring, minor, Hamiltonian cycle 예제 공식이 있다.
  - 자유 변수가 있는 공식의 정확성 정리는 `SatisfiesAt`으로 서술한다.
  - 대표 정리 이름은 `satisfiesAt_*_iff` 명명 관례로 맞춘다.

## 빌드 원칙

- dependency가 바뀌었거나 새 checkout에서 시작할 때는 먼저 캐시를 받는다.

```bash
lake exe cache get
lake build
```

- `lake build`가 mathlib 전체를 직접 컴파일하는 상황은 피한다.
- CI를 추가할 때도 `lake exe cache get` 후 `lake build` 순서를 사용한다.
- `lake update`는 dependency를 바꿀 때만 실행한다. 실행 후 manifest 변경을 확인한다.

## 설계 원칙

- Courcelle theorem을 향한 주 경로는 mathlib `SimpleGraph V` 위에 둔다.
- `Assignment V E`는 단일 환경 타입으로 유지한다. `SimpleGraph` 위에서는
  `E := G.edgeSet`으로 instantiate한다.
- 1차 변수는 비어 있을 수 있으므로 `Option`을 사용하고, 집합 변수는 항상 `Set` 값을 가진다.
- 자유 변수가 있는 공식은 `SatisfiesAt phi G rho`로 다룬다.
- 닫힌 문장 또는 graph property는 `Satisfies G phi`로 다룬다.
- 유한성, 결정 가능성, treewidth bound는 그래프 구조체에 넣지 않고 필요한 정리에서
  `[Fintype V]`, `[DecidableEq V]`, `[DecidableRel G.Adj]`, tree decomposition 가정으로 둔다.
- Courcelle formalization은 다음 층위를 분리한다.
  - 순수 의미론: `SatisfiesAt`, 닫힌 공식 만족 관계 `Satisfies`.
  - `τ_P`-structure 계층: 그래프 + 유한 unary predicate `P`를 담는 구조와 그
    위의 MSO. 인코딩·번역·automata는 모두 이 `τ_P` 위에서 동작한다.
  - tree decomposition API: bags, width, nice decomposition.
  - 강의노트 경로: bounded-width decomposition과 bag-injective coloring을
    finite alphabet `Σ_ω`-tree로 인코딩한다. letter는 rooted `τ_P`-structure
    (인접 + 색별 unary tag)이다.
  - 해석 계층: `τ_P` 위 MSO 원자식(`adj`, `=`, `∈`, `P(x)`)과 양화자를
    `Σ`-tree 위 MSO 공식으로 번역한다.
  - incidence 환원 계층: MSO2를 coloured incidence `τ_I = {adj, Vert, EObj}`
    구조 위 MSO로 옮기는 theorem-level 번역. `GraphMSO/incidence.lean`이 기반.
  - automata 계층: MSO-definable tree language의 regularity와 bottom-up finite
    tree automata 실행을 연결한다.
  - 최종 정리: bounded treewidth graph class에서 MSO/MSO2 model checking 가능성.

## 1단계: 핵심 언어와 `SimpleGraph` 의미론 안정화

완료됨:

- 목표: MSO2 공식을 표현하는 핵심 문법을 둔다. 구현: `GraphMSO/Syntax.lean`의
  `inductive Formula`와 변수 별칭 `FOVar`, `SOVar`, `EdgeFOVar`, `EdgeSOVar`.
- 목표: 변수 해석을 담는 assignment와 shadowing update API를 둔다. 구현:
  `GraphMSO/Semantics.lean`의 `structure Assignment`, `Assignment.empty`,
  `Assignment.updateFO`, `Assignment.updateSO`, `Assignment.updateEdgeFO`,
  `Assignment.updateEdgeSO` 및 관련 `[simp]` 정리.
- 목표: 빈 환경에서 닫힌 문장을 해석할 수 있게 한다. 구현: 1차 변수 field를
  `Option`으로 두고, unassigned 원자식은 false가 되도록 `SatisfiesAt`을 정의한다.
- 목표: mathlib `SimpleGraph V` 위에서 MSO2 Tarski 의미론을 정의한다. 구현:
  `GraphMSO/Semantics.lean`의 `Semantics.SatisfiesAt`, edge sort는 `G.edgeSet`.
- 목표: 닫힌 공식 또는 graph property용 wrapper를 둔다. 구현:
  `GraphMSO/Semantics.lean`의 `Semantics.Satisfies`와
  `Semantics.satisfies_iff_satisfiesAt_of_closed`.
- 목표: MSO2의 incidence 원자식 `inc x e`를 `SimpleGraph` edge sort에 맞게 해석한다.
  구현: `SatisfiesAt`의 `Formula.inc` case에서 배정된 정점 값이 배정된 edge subtype의
  underlying `Sym2 V`에 속하는지 검사한다.
- 목표: `SatisfiesAt`를 예제 증명에서 바로 펼칠 수 있게 기본 simp API를 둔다. 구현:
  `GraphMSO/Semantics.lean`의 `satisfiesAt_conj`, `satisfiesAt_disj`,
  `satisfiesAt_impl`, `satisfiesAt_biimpl`, `satisfiesAt_existsFOs_*`,
  `satisfiesAt_forallFOs_*`, 그리고 `Assignment.update*` 관련 `[simp]` 정리.
- 목표: 대표 MSO 공식이 손으로 쓴 `SimpleGraph` 술어와 맞는지 확인한다. 구현:
  `GraphMSO/Examples.lean`의 `clique`, `independent`, `dominating`, `vertexCover`,
  `bipartite` 및 `satisfiesAt_clique_iff`, `satisfiesAt_independent_iff`,
  `satisfiesAt_dominating_iff`, `satisfiesAt_vertexCover_iff`, `satisfiesAt_bipartite_iff`.
- 목표: Courcelle theorem 경로에서 쓰지 않는 incidence graph compatibility layer를 제거한다.
  구현: `GraphMSO/Basic.lean` 삭제.
- 목표: `GraphMSO.Basic`에 의존하던 별칭과 import를 제거하고 `Set`을 직접 사용한다. 구현:
  `GraphMSO/Semantics.lean`은 `Set V`, `Set E`, `Set G.edgeSet`을 직접 쓰고,
  `GraphMSO.lean`과 `GraphMSO/decomp.lean`의 `GraphMSO.Basic` import를 제거.

남은 작업:

- 닫힌 공식 예제와 이후 Courcelle statement가 `Satisfies`를 직접 쓰도록 점진적으로 옮긴다.
- edge quantifier helper에 대한 simp lemma를 추가한다.
- 정리 이름과 statement가 `SatisfiesAt`/`Satisfies` 계층을 일관되게 드러내는지 계속 정리한다.

완료 기준:

- 핵심 정의에 `sorry`가 없다.
- `lake build`가 통과한다.
- 대표 예제 공식이 `SatisfiesAt`에서 직접 펼쳐져 증명 가능한 형태로 나온다.

## 2단계: 자유 변수, support, assignment independence

현재 문법은 이름 있는 numeric variable을 사용한다. 이 방식은 초기 예제에는 읽기 쉽지만,
Courcelle theorem 증명 자체에는 일반 치환과 알파 동치 메타이론이 핵심 경로가 아니다.
우선은 자유 변수 support와 assignment irrelevance만 증명한다. 일반적인 capture-avoiding
substitution, alpha-equivalence 정리는 formula normalization이나 user-facing DSL에서
실제로 필요해질 때 별도 단계로 미룬다.

완료됨:

- 목표: 정점 1차 자유 변수를 추적한다. 구현: `GraphMSO/Syntax.lean`의
  `Formula.FreeFO : Formula -> FOVar -> Prop`.
- 목표: 정점 집합 2차 자유 변수를 추적한다. 구현: `GraphMSO/Syntax.lean`의
  `Formula.FreeSO : Formula -> SOVar -> Prop`.
- 목표: 간선 1차 자유 변수를 추적한다. 구현: `GraphMSO/Syntax.lean`의
  `Formula.FreeEdgeFO : Formula -> EdgeFOVar -> Prop`.
- 목표: 간선 집합 2차 자유 변수를 추적한다. 구현: `GraphMSO/Syntax.lean`의
  `Formula.FreeEdgeSO : Formula -> EdgeSOVar -> Prop`.
- 목표: 네 종류의 자유 변수가 모두 없는 닫힌 공식을 표현한다. 구현:
  `GraphMSO/Syntax.lean`의 `Formula.Closed`.
- 목표: 실제 예제 공식이 닫혀 있음을 smoke test로 확인한다. 구현:
  `GraphMSO/Examples.lean`의 `Examples.hasNonemptyClique_closed`.
- 목표: 두 assignment가 공식의 자유 변수에서 같다는 관계를 정의한다. 구현:
  `GraphMSO/Semantics.lean`의 `Assignment.AgreeOnFree`.
- 목표: `SatisfiesAt`가 자유 변수 값에만 의존함을 증명한다. 구현:
  `GraphMSO/Semantics.lean`의 `Semantics.satisfiesAt_ext_on_free`. 보조 정리로
  `Assignment.AgreeOnFree.mono`와 sort별 update 보존 정리
  `Assignment.AgreeOnFree.updateFO`/`updateSO`/`updateEdgeFO`/`updateEdgeSO`를 둔다.
- 목표: 닫힌 공식의 `SatisfiesAt` 의미론이 assignment 선택과 무관함을 증명한다. 구현:
  `GraphMSO/Semantics.lean`의 `Semantics.satisfiesAt_closed_independent`. 임의 assignment에서
  `Satisfies`와 `SatisfiesAt`를 잇는 `Semantics.satisfies_iff_satisfiesAt`도 추가했다.

남은 작업:

- 필요하면 `FreeFO`/`FreeSO`/`FreeEdgeFO`/`FreeEdgeSO`의 `Finset` 버전 또는 computable support를 추가한다.
- 필요하면 `Satisfies G phi`용 notation 계층을 추가한다.

완료 기준:

- 닫힌 공식의 만족 관계를 assignment 선택 없이 사용할 수 있다.
- formula translation과 automata 계층에서 필요한 자유 변수 support를 사용할 수 있다.

## 3단계: `SimpleGraph` 그래프 술어와 MSO 명세 라이브러리

목표는 MSO 공식이 표준 graph-theoretic 의미와 같다는 것을 Lean에서 증명하는 것이다.
가능하면 mathlib의 기존 `SimpleGraph` 정의를 직접 목표로 삼고, 프로젝트-local 술어는
mathlib에 적절한 정의가 없거나 MSO2 edge-sort 표현과 맞추기 위한 wrapper로만 둔다.
이 경우에도 local 술어 자체가 최종 의미가 되지 않도록, 나중에 mathlib 정의 또는
문헌적으로 표준적인 정의와의 동치 정리를 추가한다.

완료됨:

각 예제 공식은 `Examples.<property>`와 동치 정리 `Examples.satisfiesAt_<property>_iff`
명명 관례를 따른다(`GraphMSO/Examples.lean`). mathlib에 대응 정의가 있는 술어는 모두
연결을 마쳤고, 없는 경우는 local 정의를 유지하되 사유를 비고에 남긴다.

| 술어 | mathlib 대상 | 다리 보조정리 / 비고 |
|---|---|---|
| clique | `IsClique` | 직접 |
| independent | `IsIndepSet` | local `IsIndependent` 제거; `ColorClassesIndependent`도 `IsIndepSet` 기준으로 정렬 |
| vertex cover | `IsVertexCover` | `isVertexCover_iff_forall_edge`; 동명 local 중복 제거 |
| bipartite | `IsBipartite` | `isBipartite_iff_forall_edge`; local `IsBipartiteByEdges` 제거 |
| connectivity | `Preconnected` | `isConnectedByPartition_iff_preconnected`, `isDisconnectedByPartition_iff_not_preconnected`; 빈 그래프에서 `Preconnected`와 일치(`Connected`는 `Nonempty V`를 추가로 요구). partition 특성화는 중간 단계로 유지 |
| coloring (`k`/3색) | `Colorable k` | `hasColoringBySetsOfSize_iff_colorable`, `isThreeColorableBySets_iff_colorable` (`Coloring (Fin k)` 직접 구성); set-list 특성화(`IsColoringBySets` 등)는 중간 단계로 유지 |
| perfect matching | `Subgraph.IsPerfectMatching` | `spanningSubgraphOfEdges` + `isPerfectMatching_spanningSubgraphOfEdges_iff`; `satisfiesAt_isLoop_false` 사용; local `HasPerfectMatching` 제거 |
| Hamiltonian | `Walk.IsHamiltonianCycle` | edge 중간 술어 `HasHamiltonianCycleByEdges` + `hasHamiltonianCycleByEdges_iff` (`[Fintype][DecidableEq][Nonempty]`, mathlib `IsCycles` 인프라); 재사용 core `exists_isHamiltonianCycle_of_ncard_neighborSet_eq_two_of_preconnected` (finite nonempty connected 2-regular → Hamiltonian cycle, mathlib에 없는 일반 정리); 따름정리 `satisfiesAt_hamiltonian_iff_isHamiltonianCycle` |
| dominating | (mathlib에 없음) | local `IsDominating` 유지 |
| minor (`K_3`) | (mathlib에 graph minor 관계 없음) | local `IsMinorModelBySets`/`HasK3MinorBySets`, `minorModelUsing`; 현재 `K_3` instance만 완전 증명 |

mathlib에 대응이 있는 술어(clique/independent/vertex cover/bipartite/connectivity/
coloring/perfect matching/Hamiltonian)의 연계는 마무리되었다. dominating과 minor는
mathlib에 대응 정의가 없어 local 정의를 유지한다.

남은 작업:

- 일반 fixed `H`-minor formula에 대해, partition 변수 freshness 조건 아래
  `minorModelUsing`과 `SimpleGraph.IsMinorModelBySets`의 일반 correctness theorem을
  추가한다. 현재는 `K_3` instance만 완전히 증명되어 있다.
- 앞으로 추가하는 project-local 술어는 `Is...ByEdges`처럼 표현 방식이 드러나는 이름을 쓰고,
  표준 정의와의 comparison theorem을 함께 둔다.

완료 기준:

- 주요 예제 공식마다 mathlib 또는 표준 graph-theoretic 술어와의 iff 정리가 있다.
- project-local wrapper만 있는 경우, wrapper와 표준 정의 사이의 iff 정리가 있거나
  mathlib에 적절한 정의가 없다는 이유가 문서화되어 있다.
- theorem statement가 이후 Courcelle 명세에서 재사용 가능한 모양이다.

## 4단계: tree decomposition과 treewidth

Courcelle theorem의 graph-theoretic 핵심 API를 만든다.

완료:

- decomposition tree와 tree decomposition predicate를 정의했다. 구현:
  `GraphMSO/decomp.lean`의 `DecompositionTree V`, `TreeDecomposition G T`.
  - tree node constructor: `DecompositionTree.node bag arity child`.
  - bag type: `Set V`.
  - finite bag condition: `T.BagsFinite`.
  - vertex coverage: `T.ContainsVertex v`.
  - edge coverage: `T.ContainsEdge u v`.
  - running intersection property: 각 `v : V`에 대해 recursive certificate
    `T.RunningIntersectionAt v`.
- tree recursion helper와 inductive predicate를 정의했다. 구현: `rootBag`, `arity`,
  `child`, `ContainsVertex`, `ContainsEdge`, `AllBags`, `BagsFinite`,
  `RunningIntersection`, `WidthAtMost`.
- treewidth bound API를 정의했다. 구현: `HasTreewidthAtMost`.
- finite graph에 대한 one-bag decomposition 예제를 추가했다. 구현:
  `singleBag`, `singleBag_decomposition`, `singleBag_widthAtMost_card`,
  `hasTreewidthAtMost_card`.
- nice tree decomposition의 4가지 node type을 root bag으로 인덱싱한 inductive로 정의했다.
  구현: `GraphMSO/decomp.lean`의 `NiceTreeDecomposition V (bag : Set V)` — `leaf`(빈 bag),
  `introduce`(`v ∉ bag`를 더해 `insert v bag`), `forget`(`insert v bag`에서 `v` 제거),
  `join`(같은 bag의 두 자식). 인덱스가 root bag을 추적한다. 현재는 그래프와 무관한 구조
  골격만 담는다(그래프 연결·유효성은 아래 남은 작업의 다리 정리 참고).
- width를 maximum bag cardinality로 계산하는 API를 추가했다. 구현:
  `DecompositionTree.maxBagCard`, `width`(= `maxBagCard - 1`), 그리고
  `widthAtMost_iff_maxBagCard_le`, `widthAtMost_iff_width_le`. `Set.ncard`가
  noncomputable이라 두 함수는 `noncomputable`이다.
- rooted decomposition의 노드 addressing API를 추가했다. 노드는 root에서의 child index
  리스트(`[]` = root)로 가리킨다. 구현: `nodeAt`, `IsNode`, `bagAt`, `coneAt`, `parent`,
  `IsChild`, `adhesionAt`, `BAGS`(+ `mem_BAGS`), `IsTopmost`, `IsConnectedNodeSet`. ancestor
  관계는 mathlib list-prefix `<+:`를 재사용한다.
- bag-injective `(ω + 1)`-coloring을 표현했다. 구현: `IsBagColoring`과, `Fin (n + 1)`로의
  bag-injective coloring이 `WidthAtMost n`을 함의하는 `widthAtMost_of_isBagColoring`
  (보조정리 `ncard_le_of_injOn_fin`).
- 예제·증명 재사용을 위한 leaf/unary 노드 보조정리를 추가했다. 구현: `allBags_node_iff`,
  `containsVertex_leaf_iff`, `containsEdge_leaf_iff`, `runningIntersectionAt_leaf`,
  `containsVertex_unary_iff`, `containsEdge_unary_iff`, `runningIntersectionAt_unary`.
- 작은 그래프 path decomposition 예제를 추가했다. 구현: `pathP3`(Fin 3 위 `0—1—2`),
  overlapping bag `{0,1}—{1,2}` 분해 `pathP3Decomp`, 유효성 `pathP3Decomp_decomposition`.
- `NiceTreeDecomposition`을 `DecompositionTree`로 해석하는 다리를 추가했다. 구현:
  `NiceTreeDecomposition.toDecompositionTree`와 root bag 보존 `toDecompositionTree_rootBag`.
- running intersection이 `BAGS(v)` 연결성을 함의함을 증명했다. 구현: `isConnectedNodeSet_bags`
  (running intersection ∧ `ContainsVertex` ⇒ 각 `v`의 `BAGS(v)`가 `IsConnectedNodeSet`)와
  topmost 유일성 `IsTopmost.unique`. 보조 API: `mem_bags_nil`, `mem_bags_cons_iff`,
  `mem_bags_cons_fin`, `RunningIntersectionAt.node_inv`, `containsVertex_of_mem_bags`,
  ancestor-closedness 보조정리 `bags_prefixClosed`.
- width `ω` decomposition의 bag-injective `(ω + 1)`-coloring 존재를 증명했다. 구현:
  `exists_isBagColoring` (running intersection ∧ `BagsFinite` ∧ `WidthAtMost ω` ⇒ 모든 bag에서
  injective인 `Fin (ω+1)` 색칠 존재)와 상대형 `exists_isBagColoring_extend` (root bag 색칠을
  부분트리 전체로 확장). 보조정리: `exists_injOn_extend` (부분집합 injective 색칠을 더 큰 유한집합으로
  확장), `isBagColoring_congr`, `AllBags.rootBag`.
- `lake build`가 통과한다.

남은 작업:

- binary decomposition을 위한 arity ≤ 2 술어와 adhesion/cone 관련 보조정리를 추가한다.
- cycle 등 추가 작은 그래프 decomposition 예제를 더한다(path 예제 `pathP3Decomp`는 완료).
- `toDecompositionTree`가 유효한 `TreeDecomposition G`임을 보이는 다리 정리. 현재는 구조 변환과
  root bag 보존(`toDecompositionTree_rootBag`)만 있다. 분석 결과 `TreeDecomposition.mk`의 네 조건
  상태는 다음과 같다:
  - `BagsFinite`: 구조적으로 공짜(모든 bag이 `∅`에서 insert/forget으로 생성되어 유한). →
    `toDecompositionTree_bagsFinite`로 바로 증명 가능(미구현).
  - `vertex coverage`(`∀ v : V, ContainsVertex`): 자동 아님. introduce되지 않은 V의 정점이 있을 수
    있어 spanning 가설이 필요(또는 covered-subtype로 제한).
  - `edge coverage`: 현재 `NiceTreeDecomposition`이 그래프·간선을 전혀 담지 않아 서술조차 불가 →
    아래 graph linkage 설계 필요.
  - `running intersection`: **자동 아님(발견).** 현재 inductive는 잊은 정점의 재-introduce를 막지
    않는다(`introduce`의 조건이 자식 root bag의 `v ∉ bag`일 뿐 서브트리 cone 전체가 아님). 반례:
    `introduce ∅ v _ (forget ∅ v _ (introduce ∅ v _ leaf))`의 bag 수열이 `{v}, ∅, {v}, ∅`이라 v가
    끊긴다. RI를 구조적으로 얻으려면 `introduce`에 `v ∉ cone(child)` 조건을 추가(타입 강화)해야 하고,
    그러지 않으면 RI는 가설로 둔다. (RI 도구는 이미 있음: `isConnectedNodeSet_bags` 등.)
- graph linkage 방식(**개정으로 방향 확정**): 2026-06 개정 note와
  `GraphMSO/Decomp/rootedGraph.lean`이 방향을 정했다. 각 node는 bag 위
  **induced `τ_P`-substructure**(node graph `H_t = G[β(t)]`)를 letter로 들고,
  cone은 명시적 gluing으로 복원한다. gluing은 proof-irrelevant data로 구현됨:
  `KRootedGraph`, 명시적 witness `GluingData A B C`, 그리고 술어용
  `IsGluing := Nonempty (GluingData ..)`. 아래 옛 후보는 기록으로만 남긴다.
  - (C1) decode 방식: `decodedGraph T := {(u,v) | u ≠ v ∧ T.ContainsEdge u v}`
    (co-occurrence 최대 그래프). 임의 sparse G를 분해 못 해 채택하지 않음.
  - (C2) induced node-graph baking: 각 node가 bag 위 induced 구조를 들고
    `G = ⋃ node 구조`. 임의 sparse G 가능, 강의노트 node-graph에 충실 → 채택.
- **`τ_P`-structure 일반화 (진행 중).**
  - 완료: 코어 `KRootedPGraph P`(= `SimpleGraph` + `pred : P → V → Prop`)를
    `GraphMSO/Decomp/KRootedPGraph.lean`에 정의. `Fintype`/`DecidableEq P`는
    구조체에 박지 않고 필요한 정리에서만 가정. incidence instance는 6단계 참조.
  - 남은 작업은 **단계적 리팩토링**이다(이미 컴파일되는 코드 다수를 변경·재증명).
    1. `sigmaTree`: `SigmaLetter P ω`에 `tag : P → verts → Prop`를 더하고
       `Compatible`에 공유 색의 tag 일치 조건을 추가한다.
    2. `rootedGraph`: `KRooted P k extends KRootedPGraph P`를 두고,
       `Gluable`/`LabelCompatibleOnRoots`/`GluingData`에 predicate 일치·상속 절을
       추가한다(gluing 코어 + 관련 보조정리 재증명).
    3. `nodeConeGraph`: node graph/cone graph가 `pred := G.pred`를 bag/cone으로
       제한해 운반하도록 한다.
  - **발견된 deep dependency:** 3을 하려면 node/cone의 밑그래프가 `SimpleGraph`가
    아니라 `τ_P`-structure여야 한다. 즉 `TreeDecomposition`의 밑그래프를
    `SimpleGraph V`에서 `KRootedPGraph P`로 **일반화**해야 하며, 이는 단순 일반화가
    아니라 `tree_decomp`/`bagColoring`/`nice` 등 decomposition·인코딩 파이프라인
    전체로 파급된다. 따라서 순서는 1(저위험) → 2 → `TreeDecomposition` 일반화 → 3.
- `NiceTreeDecomposition`을 별도 inductive로 둘지 `DecompositionTree.IsNice` 술어로 둘지 설계를
  확정한다(전자는 correct-by-construction, 후자는 기존 `TreeDecomposition` API 재사용에 유리).
  현재 `NiceTreeDecomposition`은 `V : Type`로 고정되어 있어, 유지한다면 `DecompositionTree`처럼
  `Type u`로 일반화하는 것을 검토한다.
- 기존 decomposition을 nice form으로 변환하는 정리를 검토한다.
- mathlib의 graph/tree/path/connectivity API를 최대한 재사용한다.

완료 기준:

- `TreeDecomposition G T`와 `width <= k`를 표현할 수 있다. 완료:
  `TreeDecomposition G T`, `T.WidthAtMost k`, `HasTreewidthAtMost G k`.
- 대표적인 작은 그래프의 decomposition 예제가 컴파일된다. 완료: finite graph의 `singleBag`
  decomposition과 path 그래프 예제 `pathP3Decomp`가 컴파일된다. cycle 등 추가 예제는 선택.

## 5단계: `Σ_ω`-tree 인코딩과 decoding

`Courcelle/lecture_note.pdf`의 주 증명 경로는 decomposition 위 직접 DP가 아니라
`Σ`-tree translation과 tree automata 경로를 따른다. 먼저 width `ω`의 binary tree
decomposition과 bag-injective `(ω + 1)`-coloring을 finite alphabet `Σ_ω` 위
labeled tree로 바꾼다. 여기서 `Σ_ω`의 문자는 `Fin (ω + 1)`의 부분집합 위
rooted **`τ_P`-structure** `(H, R)`로 본다. 즉 letter는 색별 induced 인접관계와
각 색의 unary predicate `P(x)` 성립 여부를 함께 기록한다(평범한 그래프 경우
`P = ∅`이면 종래의 rooted graph로 환원).

남은 작업:

- (설계 결정) 인코딩을 시작할 때 "증명형이냐 실행형이냐"를 먼저 정한다. bag을 `Set V`로 둔 채
  고전적 `Set.Finite`로 두면 인코딩(bag 정점 열거 → color rename → node label 생성)이
  `Set.Finite.toFinset` 때문에 noncomputable이 된다. 정리 증명이 목표면 그대로 충분하고,
  `#eval` 가능한 모델체커가 목표면 `Finset` bag 또는 `[Fintype V]`/`[DecidableEq V]` 경로로
  computable 인코딩을 둔다. width/treewidth는 가정·Prop으로만 쓰여 이 선택의 영향이 작다.
- `Fin (ω + 1)` 위 finite rooted `τ_P`-structure alphabet `Sigma omega`를 정의한다.
- 각 decomposition node의 node graph, root/adhesion, cone graph를 `τ_P`-structure로
  정의한다(`nodeConeGraph.lean`/`rootedGraph.lean`).
- coloring으로 vertex 이름을 색으로 rename하여 node label `(H_t, R_t) : Sigma omega`를 만든다.
- `Sigma`-tree의 local legality predicate를 정의한다. child label의 root가 parent
  label의 vertex set에 들어가고, 공유 색에서 **induced 인접관계와 모든 unary
  predicate가 일치**하며, **root node의 boundary는 `R = ∅`**이어야 한다.
- legal `Sigma`-tree를 gluing으로 decoding하여 graph, coloring, decomposition을 복원한다.
- encoding 후 decoding, legal tree 후 re-encoding equivalence를 증명한다.

완료 기준:

- bounded-width colored decomposition에서 legal `Sigma`-tree를 만들 수 있다.
- legal `Sigma`-tree에서 복원한 `(G, c, T)`가 tree decomposition 조건을 만족한다.
- encoding/decoding correctness가 이후 formula translation 정리에서 재사용 가능한 형태이다.

## 6단계: graph MSO를 tree MSO로 해석하기

강의노트의 변환은 graph vertex를 tree node set의 `(ω + 1)`-tuple로 표현한다.
vertex `v`는 `BAGS(v)`와 color의 defining tuple로, vertex set `S`는 각 color별
`BAGS(v)`들의 disjoint union으로 표현한다. 이 계층은 현재 MSO2 core syntax와 별도로,
`τ_P` 위 MSO를 대상으로 하며, 가장 작은 첫 마일스톤은 `P = ∅`인 **graph MSO1
over `{adj}`**(기존 `Syntax`의 edge-sort 변수·원자를 뺀 fragment)이다. MSO2는
`P = {Vert, EObj}`인 coloured incidence 환원으로 별도 연결한다.

남은 작업:

- tree vocabulary `τ_Σ = {child1, child2} ∪ {P_a | a ∈ Σ}`용 MSO syntax/semantics를
  정의하거나, 기존 `Formula`를 재사용할 수 있는 작은 relational-vocabulary abstraction을 검토한다.
- tree MSO helper formula를 정의한다: `parent`, `root`, `connected`, `top`, `dangle`.
- defining pair/tuple을 인식하는 formula를 만든다: `vtx_i`, `vtx`, `set`.
- `τ_P` atomic formula를 tree formula로 해석한다: `adj`(=`edge`), `equal`,
  `contain`(`∈`), 그리고 각 unary predicate에 대한 `P(x)`. unary case는 대표쌍
  top-letter의 tag 확인으로 단순하다.
- graph MSO1 formula의 quantifier를 `(ω + 1)`개의 tree set variable로 바꾸는 translation을 정의한다.
- translation correctness를 증명한다:
  `G |= phi` iff encoded `Sigma`-tree가 `legal ∧ translate phi`를 만족한다.
- 현재 MSO2 syntax와의 연결: ① `P = ∅`인 edge-sort-free **MSO1 over `{adj}`**
  fragment 정리를 먼저 완성한다(`G` 직접, treewidth `ω`). ② **MSO2는 coloured
  incidence 환원으로 확정**한다 — `Î(G)` over `τ_I = {adj, Vert, EObj}`로 옮기고
  typed quantifier를 `Vert`/`EObj`로 가드하는 `ψ†` 번역(2026-06 개정 note에서
  채택). 코어 구조는 완료: `GraphMSO/incidence.lean`의
  `colouredIncidence (G) : KRootedPGraph IncSort`(`IncSort = {vert, edgeObj}`,
  `Vert`/`EObj` = 생성자 유도 `IsVertex`/`IsEdgeObj` + `Decidable`). 남은 것은
  MSO-over-`τ_P` 의미론과 `ψ†` 번역 자체이다.

완료 기준:

- 강의노트 Lemma 14-19에 해당하는 Lean statement가 있다.
- `τ_P` sentence(우선 `P = ∅`인 MSO1 over `{adj}`)에 대해 graph satisfaction과
  encoded tree satisfaction의 iff가 있다.
- MSO2로 확장할 때 core `SimpleGraph`/`G.edgeSet` source 의미론을 바꾸지 않고
  coloured incidence 환원만 얹으면 된다는 경계가 문서화되어 있다.

## 7단계: finite tree automata와 Courcelle theorem statement

tree translation 다음에는 MSO-definable tree language가 regular라는 정리를 사용한다.
Lean에서 이 정리를 완전히 형식화하는 일은 크므로, 처음에는 명확한 interface theorem으로
분리하고, bottom-up automaton의 실행과 correctness를 먼저 갖추는 것이 좋다.

남은 작업:

- finite ranked alphabet과 deterministic bottom-up tree automaton을 정의한다.
- labeled binary tree에서 automaton run/evaluator와 acceptance를 정의한다.
- automaton evaluator가 tree 크기에 선형으로 실행된다는 statement를 준비한다. 복잡도 증명은
  약한 형태에서 시작해도 된다.
- MSO tree sentence마다 해당 tree automaton이 존재한다는 regularity theorem은 일단
  명시적 가정 또는 interface theorem으로 분리한다. 실제 regularity proof는 별도 장기 과제로 둔다.
- translation correctness와 automaton correctness를 조립해, decomposition이 주어진 경우의 Courcelle theorem을
  먼저 서술한다.

완료 기준:

- 고정된 `ω`와 (우선 `P = ∅`인) `τ_P` sentence `phi`에 대해, binary tree
  decomposition이 주어진 finite graph에서 `G |= phi`를 결정하는 automaton-based
  model checker statement가 있다.
- statement가 강의노트 Theorem 1(2026-06 개정)의 입력 구조와 정정된 런타임을
  따른다: 입력은 graph, binary tree decomposition, MSO sentence이고, 런타임은
  `f_P(ω, |φ|)·(|V(G)| + |N(T)|)`(정규화 분해에서 `|N(T)| = O(|V(G)|)`)이다.
- regularity theorem의 의존성이 명확히 분리되어 있다.

## 8단계: 도구화, 표기법, CI

남은 작업:

- `simp` 보조정리를 정리한다.
  - assignment update.
  - `SatisfiesAt`/`Satisfies`의 파생 연결자.
  - `Set` membership/subset/equality.
  - `SimpleGraph` 술어 unfolding.
  - 리스트 양화 helper.
- 사용자-facing notation을 검토한다.
  - `⊨`, `¬`, `∧`, `∨`, `∀'`, `∃'` 같은 표기법은 core API가 안정된 뒤 추가한다.
- 예제와 smoke test를 확장한다.
- CI를 추가한다.
  - 최소 CI는 `lake exe cache get` 후 `lake build`이다.

완료 기준:

- CI에서 `lake build`가 안정적으로 확인된다.

## 권장 작업 순서

완료됨:

1. 닫힌 공식용 `Satisfies` 계층을 정의한다.
2. 의미론을 `SatisfiesAt`/`Satisfies`로 통합하고 단일 `Assignment`를 사용한다.
3. 예제 정리 statement와 이름을 `SatisfiesAt` 기준으로 정리한다.
4. `Assignment.AgreeOnFree` 기반 assignment-independence 정리를 끝낸다.
   (`satisfiesAt_ext_on_free`, `satisfiesAt_closed_independent`, `satisfies_iff_satisfiesAt`.)

다음 작업:

1. tree decomposition API를 binary/rooted/adhesion/cone/`BAGS(v)` 방향으로 보강한다.
2. `(ω + 1)`-coloring과 `Σ_ω` alphabet, legal `Σ`-tree encoding을 정의한다.
3. `τ_P` 위 MSO(우선 `P = ∅`인 graph MSO1 over `{adj}`)에서 tree MSO로 가는
   translation correctness를 세운다. `KRootedGraph`/letter를 `τ_P`-structure로
   일반화하는 것이 선행 작업이다.
4. finite tree automata interface를 추가하고, decomposition-given Courcelle statement를 먼저 세운다.
5. `incidence.lean`을 coloured `τ_I`-structure로 승격하고, MSO2를 incidence 환원
   (`τ_I = {adj, Vert, EObj}`)으로 연결한다.
