# 계획

이 프로젝트의 장기 목표는 Lean 4와 mathlib 위에서 Courcelle theorem을
형식화하는 것이다. MSO2 문법과 의미론은 그 자체가 최종 목적이라기보다,
유한 단순 그래프의 bounded treewidth 위에서 MSO2 model checking을 다루기 위한
기반 계층이다.

그래프 표현은 mathlib의 `SimpleGraph V`로 둔다. MSO2의 간선 1차 변수와
간선 집합 2차 변수는 `G : SimpleGraph V`가 주어졌을 때
`G.edgeSet : Set (Sym2 V)`의 subtype 위를 돈다. 별도의 incidence graph
compatibility layer는 유지하지 않는다.

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
  - 대표 정리 이름은 `satisfiesAt_clique_iff`, `satisfiesAt_independent_iff`,
    `satisfiesAt_dominating_iff`, `satisfiesAt_vertexCover_iff`,
    `satisfiesAt_bipartite_iff`처럼 `SatisfiesAt` 기준으로 맞춘다.

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
  - 유한 실행 의미론: finite evaluator와 correctness.
  - tree decomposition API: bags, width, nice decomposition.
  - 동적 계획법/automata 계층: decomposition 위 model checking.
  - 최종 정리: bounded treewidth graph class에서 MSO2 model checking 가능성.

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

남은 작업:

- `SatisfiesAt`가 자유 변수 값에만 의존한다는 `Assignment.AgreeOnFree` 기반 정리를 증명한다.
- 닫힌 공식의 `SatisfiesAt` 의미론이 assignment 선택과 무관함을 증명한다.
- 필요하면 `FreeFO`/`FreeSO`/`FreeEdgeFO`/`FreeEdgeSO`의 `Finset` 버전 또는 computable support를 추가한다.
- 필요하면 `Satisfies G phi`용 notation 계층을 추가한다.

완료 기준:

- 닫힌 공식의 만족 관계를 assignment 선택 없이 사용할 수 있다.
- finite evaluator와 DP 상태공간에서 필요한 자유 변수 support를 사용할 수 있다.

## 3단계: `SimpleGraph` 그래프 술어와 MSO 명세 라이브러리

목표는 MSO 공식이 표준 graph-theoretic 의미와 같다는 것을 Lean에서 증명하는 것이다.
가능하면 mathlib의 기존 `SimpleGraph` 정의를 직접 목표로 삼고, 프로젝트-local 술어는
mathlib에 적절한 정의가 없거나 MSO2 edge-sort 표현과 맞추기 위한 wrapper로만 둔다.
이 경우에도 local 술어 자체가 최종 의미가 되지 않도록, 나중에 mathlib 정의 또는
문헌적으로 표준적인 정의와의 동치 정리를 추가한다.

완료됨:

- 목표: clique MSO 공식과 mathlib의 clique 술어를 연결한다. 구현:
  `GraphMSO/Examples.lean`의 `Examples.clique`와 `Examples.satisfiesAt_clique_iff`.
- 목표: independent set MSO 공식과 mathlib의 `SimpleGraph.IsIndepSet`를 연결한다. 구현:
  `GraphMSO/Examples.lean`의 `Examples.independent`와 `Examples.satisfiesAt_independent_iff`.
  (기존 local `SimpleGraph.IsIndependent`는 제거하고, 이를 쓰던 `ColorClassesIndependent`도
  `IsIndepSet` 기준으로 맞췄다.)
- 목표: dominating set MSO 공식과 표준 dominating-set 술어를 연결한다. 구현:
  `GraphMSO/Examples.lean`의 `SimpleGraph.IsDominating`, `Examples.dominating`,
  `Examples.satisfiesAt_dominating_iff`. 남은 정리: mathlib에 해당 술어가 있으면 그것으로
  대체하거나 local 정의와의 동치를 증명한다.
- 목표: vertex cover MSO2 공식과 mathlib의 `SimpleGraph.IsVertexCover`를 연결한다. 구현:
  `GraphMSO/Examples.lean`의 `Examples.vertexCover`, `Examples.satisfiesAt_vertexCover_iff`,
  그리고 edge 기반 특성화 보조정리 `SimpleGraph.isVertexCover_iff_forall_edge`.
  (동명의 local 중복 정의는 제거했다.)
- 목표: bipartite MSO2 공식과 mathlib의 `SimpleGraph.IsBipartite`를 연결한다. 구현:
  `GraphMSO/Examples.lean`의 `Examples.bipartite`, `Examples.satisfiesAt_bipartite_iff`,
  그리고 edge 기반 특성화 보조정리 `SimpleGraph.isBipartite_iff_forall_edge`.
  (기존 local `SimpleGraph.IsBipartiteByEdges`는 제거했다.)
- 목표: disconnectedness/connectivity 공식을 partition 기반 `SimpleGraph` 술어와 연결한다.
  구현: `GraphMSO/Examples.lean`의 `SimpleGraph.IsDisconnectedByPartition`,
  `SimpleGraph.IsConnectedByPartition`, `Examples.disconnected`, `Examples.connected`,
  `Examples.satisfiesAt_disconnected_iff`, `Examples.satisfiesAt_connected_iff`.
- 목표: fixed `k` coloring 공식을 color-class partition 기반 술어와 연결한다. 구현:
  `GraphMSO/Examples.lean`의 `SimpleGraph.IsColoringBySets`, `Examples.coloring`,
  `Examples.kColoring`, `Examples.satisfiesAt_coloring_iff`, `Examples.satisfiesAt_kColoring_iff`.
- 목표: closed 3-colorability sentence를 mathlib의 `SimpleGraph.Colorable 3`와 연결한다. 구현:
  `GraphMSO/Examples.lean`의 `Examples.kColorable`, `Examples.threeColorable`,
  `Examples.satisfiesAt_threeColorable_iff`, `Examples.satisfiesAt_kColorable_three_iff`
  (RHS가 `G.Colorable 3`). 다리 보조정리 `SimpleGraph.isThreeColorableBySets_iff_colorable`가
  set-list 기반 `IsThreeColorableBySets`와 mathlib `Colorable 3`의 동치를 준다.
- 목표: 일반 `k`에 대해 closed `kColorable k`를 mathlib의 `SimpleGraph.Colorable k`와 연결한다.
  구현: `GraphMSO/Examples.lean`의 `Examples.satisfiesAt_kColorable_iff` (RHS가 `G.Colorable k`)와
  다리 보조정리 `SimpleGraph.hasColoringBySetsOfSize_iff_colorable` (`k`개 독립 색류 분할 ↔ `Colorable k`,
  `Coloring (Fin k)` 직접 구성; 빈 색류 = 미사용 색). set-list 특성화 `SimpleGraph.HasColoringBySetsOfSize`,
  `IsColoringBySets`와 그 helper(`isInSomeColor_iff` 등)는 중간 정리로 유지한다.
- 목표: Hamiltonian cycle MSO2 sentence를 edge-set 기반 술어와 연결한다. 구현:
  `GraphMSO/Examples.lean`의 `SimpleGraph.HasHamiltonianCycleByEdges`,
  `Examples.hamiltonian`, `Examples.satisfiesAt_hamiltonian_iff`.
- 목표: fixed finite minor model 및 `K_t`-minor MSO2 sentence를 추가한다. 구현:
  `GraphMSO/Examples.lean`의 `SimpleGraph.IsMinorModelBySets`,
  `SimpleGraph.HasK3MinorBySets`, `Examples.minorModelUsing`,
  `Examples.completeGraphMinor`, `Examples.k3Minor`,
  `Examples.satisfiesAt_k3Minor_iff`, `Examples.satisfiesAt_completeGraphMinor_three_iff`.
- 목표: perfect matching MSO2 formula를 mathlib의 `SimpleGraph.Subgraph.IsPerfectMatching`와
  연결한다. 구현: `GraphMSO/Examples.lean`의 `Examples.perfectMatching`와
  `Examples.satisfiesAt_perfectMatching_iff`. 간선 집합이 만드는 spanning subgraph 구성
  `SimpleGraph.spanningSubgraphOfEdges`와 특성화 보조정리
  `SimpleGraph.isPerfectMatching_spanningSubgraphOfEdges_iff`, 그리고 `isLoop`가 `G.edgeSet`에서
  거짓임을 보이는 `Examples.satisfiesAt_isLoop_false`를 사용한다.
  (미사용 local 정의 `SimpleGraph.HasPerfectMatching`는 제거했다.)

남은 작업:

- mathlib에 이미 있는 정의와 프로젝트-local 정의를 구분하고 이름을 정리한다.
  (clique/independent/vertex cover/bipartite/perfect matching는 mathlib 정의
  `IsClique`/`IsIndepSet`/`IsVertexCover`/`IsBipartite`/`Subgraph.IsPerfectMatching`로 연결 완료.
  dominating은 mathlib에 대응 정의가 없어 local `IsDominating`를 유지한다. connectivity/coloring/
  minor/Hamiltonian 등 나머지 local 술어의 mathlib 연계 또는 표준 동치는 추후 단계로 둔다.)
- 일반 fixed `H`-minor formula에 대해, partition 변수 freshness 조건 아래
  `minorModelUsing`과 `SimpleGraph.IsMinorModelBySets`의 일반 correctness theorem을
  추가한다. 현재는 `K_3` instance만 완전히 증명되어 있다.
- project-local 술어가 필요한 경우 `Is...ByEdges`처럼 표현 방식이 드러나는 이름을 쓰고,
  circular하게 보이지 않도록 표준 정의와의 comparison theorem을 둔다. 이 역시 mathlib
  comparison 단계로 미룬다.

완료 기준:

- 주요 예제 공식마다 mathlib 또는 표준 graph-theoretic 술어와의 iff 정리가 있다.
- project-local wrapper만 있는 경우, wrapper와 표준 정의 사이의 iff 정리가 있거나
  mathlib에 적절한 정의가 없다는 이유가 문서화되어 있다.
- theorem statement가 이후 Courcelle 명세에서 재사용 가능한 모양이다.

## 4단계: 유한 model checking 의미론

Courcelle theorem으로 가려면, 순수 `Prop` 의미론과 별도로 유한 그래프에서 실행 가능한
model checker가 필요하다. 핵심 기준은 다음과 같다.

- 열린 공식 correctness는 `SatisfiesAt phi G rho`와 Boolean evaluator의 동치로 둔다.
- 닫힌 공식 model checking은 `Satisfies G phi`와 연결한다.
- evaluator의 assignment 타입도 `Assignment V G.edgeSet` 하나를 사용한다.
- FO/eFO 값이 `none`인 원자식은 false가 되며, 양화자는 finite enumeration을 통해 값을 채운다.

남은 작업:

- `[Fintype V]`, `[DecidableEq V]`, `[DecidableRel G.Adj]` 하에서 finite evaluator를 정의한다.
- edge sort `G.edgeSet`의 finite enumeration을 mathlib API와 연결한다.
- vertex set quantifier는 `Finset.powerset` 또는 finite `Set` enumeration과 연결한다.
- edge set quantifier는 `G.edgeSet`의 powerset enumeration과 연결한다.
- executable evaluator와 `SatisfiesAt` 사이의 correctness theorem을 증명한다.
- 닫힌 공식용 executable wrapper와 `Satisfies` 사이의 correctness theorem을 증명한다.

완료 기준:

- 유한 `SimpleGraph`와 assignment에 대해 executable Boolean evaluator가 있다.
- Boolean evaluator가 `SatisfiesAt`과 동치임을 증명한다.
- 닫힌 공식 wrapper가 `Satisfies`와 연결된다.

## 5단계: tree decomposition과 treewidth

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
- `lake build`가 통과한다.

남은 작업:

- 필요한 경우 실제 `width`를 maximum bag size로 계산하는 API를 추가한다.
  현재는 `T.WidthAtMost k` 형태의 bound predicate를 우선 사용한다.
- 대표적인 작은 그래프(path, cycle 등)의 decomposition 예제를 추가한다.
- nice tree decomposition을 정의하거나 기존 decomposition을 nice form으로 변환하는 정리를 검토한다.
- mathlib의 graph/tree/path/connectivity API를 최대한 재사용한다.

완료 기준:

- `TreeDecomposition G T`와 `width <= k`를 표현할 수 있다. 완료:
  `TreeDecomposition G T`, `T.WidthAtMost k`, `HasTreewidthAtMost G k`.
- 대표적인 작은 그래프의 decomposition 예제가 컴파일된다. 부분 완료:
  finite graph의 `singleBag` decomposition은 컴파일되며, 더 구체적인 작은 그래프 예제는 남았다.

## 6단계: bounded treewidth 위 MSO model checking

남은 작업:

- 공식의 quantifier rank 또는 상태 공간을 제한하는 measure를 정의한다.
- bag type 위 partial assignment/state를 정의한다. 여기서 partiality는 DP 상태가 bag 안의
  변수만 들고 있다는 뜻이며, core 의미론의 `Assignment`와는 별도의 실행 상태이다.
- nice tree decomposition node별 transition을 정의한다.
- transition의 local soundness/completeness를 증명한다.
- 전체 decomposition에 대한 dynamic-programming evaluator를 정의한다.
- evaluator correctness를 `SatisfiesAt` 또는 닫힌 공식 만족 관계 `Satisfies`와 연결한다.

완료 기준:

- 고정된 `phi`와 bounded width decomposition에 대해 model checking 절차를 표현할 수 있다.
- 절차의 correctness theorem이 있다.

## 7단계: Courcelle theorem statement

최종 정리는 구현 강도에 따라 여러 단계로 둔다.

- 약한 형식화 목표:
  - bounded treewidth decomposition이 주어진 유한 `SimpleGraph`에서 MSO2 sentence의 만족 여부가 결정 가능하다.
- 중간 목표:
  - 고정된 공식과 고정된 width bound에 대해 decomposition 크기에 대한 유한 model checking 절차가 있다.
- 강한 목표:
  - linear-time 또는 FPT 형태의 복잡도 statement를 Lean에서 표현하고 증명한다.

완료 기준:

- `Courcelle` 이름의 theorem statement가 프로젝트의 핵심 정의만으로 읽히는 형태가 된다.
- proof가 finite evaluator, tree decomposition, dynamic programming correctness 정리를 조립한다.

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

## 권장 작업 순서

완료됨:

1. 닫힌 공식용 `Satisfies` 계층을 정의한다.
2. 의미론을 `SatisfiesAt`/`Satisfies`로 통합하고 단일 `Assignment`를 사용한다.
3. 예제 정리 statement와 이름을 `SatisfiesAt` 기준으로 정리한다.

다음 작업:

1. finite executable evaluator와 `SatisfiesAt` correctness theorem을 만든다.
2. 닫힌 공식용 executable wrapper와 `Satisfies` correctness theorem을 만든다.
3. 필요하면 finite evaluator용 computable free-variable support를 추가한다.
4. tree decomposition 예제를 확장하고, 필요하면 finite-node `width` API를 추가한다.
5. nice decomposition 위 model checking dynamic programming을 형식화한다.
6. Courcelle theorem statement를 약한 형태부터 세운다.
