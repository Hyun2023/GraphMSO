# 계획

이 프로젝트의 장기 목표는 Lean 4와 mathlib 위에서 Courcelle theorem을
형식화하는 것이다. MSO2 문법과 의미론은 그 자체가 최종 목적이라기보다,
유한 단순 그래프의 bounded treewidth 위에서 MSO2 model checking을 다루기 위한
기반 계층이다.

현재 theorem-facing 그래프 표현은 mathlib의 `SimpleGraph V`로 둔다. MSO2의
간선 1차 변수와 간선 집합 2차 변수는 `G : SimpleGraph V`가 주어졌을 때
`G.edgeSet : Set (Sym2 V)`의 subtype 위를 돈다. 기존의 발생 관계 기반
`IncidenceGraph V E`는 이름 충돌을 피한 monomorphic compatibility layer이자,
명시적 incidence 표현이 필요할 때 쓰는 보조 표현으로 남긴다.

## 현재 상태

- `lakefile.toml`
  - mathlib `v4.28.0-rc1`에 의존한다.
  - `lake-manifest.json`에는 mathlib와 transitive dependency들이 고정되어 있다.
- `GraphMSO.Basic`
  - `IncidenceGraph V E`는 발생 관계 `inc : V -> E -> Prop`를 가진 구조체이다.
  - 이름은 mathlib의 `Graph`와 충돌하지 않도록 `IncidenceGraph`로 둔다.
  - 현재 API는 `V E : Type`인 monomorphic API이다.
  - `VSet V := Set V`, `ESet E := Set E`로 정점과 간선 집합을 표현한다.
  - mathlib `SimpleGraph`와의 변환이 있다.
    - `IncidenceGraph.fromSimpleGraph`
    - `IncidenceGraph.toSimpleGraph`
    - `IncidenceGraph.fromSimpleGraph_simple`
- `GraphMSO.Syntax`
  - 1차 정점 변수 `FOVar`, 2차 정점 변수 `SOVar`, 1차 간선 변수 `EdgeFOVar`,
    2차 간선 변수 `EdgeSOVar`는 현재 모두 `Nat`이다.
  - 원자식은 `false_`, `equal`, `edge`, `inSet`, `equalEdge`, `inc`, `inEdgeSet`이다.
  - `Formula.FreeFO`, `Formula.FreeSO`, `Formula.FreeEdgeFO`, `Formula.FreeEdgeSO`,
    `Formula.Closed`가 있다.
- `GraphMSO.Semantics`
  - `Assignment V E`는 삭제하지 않고 유지한다.
  - `SimpleGraph V` 의미론에서는 edge sort를 `G.edgeSet`으로 특수화해
    `Assignment V G.edgeSet`을 사용한다.
  - `Semantics.EvalAt : Formula -> (G : SimpleGraph V) -> Assignment V G.edgeSet -> Prop`가
    실제 assignment-aware Tarski 의미론이다.
  - `Semantics.Eval : Formula -> SimpleGraph V -> Prop`는 닫힌 공식용 graph-property
    wrapper이다. 현재는 assignment independence 정리 전 단계이므로 모든 assignment에서
    참이라는 형태로 정의한다.
  - `edge x y`는 `G.Adj (rho.fo x) (rho.fo y)`로, `inc x e`는
    `rho.fo x ∈ (rho.efo e : Sym2 V)`로 해석한다.
- `GraphMSO.Examples`
  - clique, independent set, dominating set, vertex cover, bipartite, perfect matching
    예제 공식이 있다.
  - 자유 변수가 있는 공식의 정확성 정리는 `EvalAt`으로 서술한다.
  - `eval_clique_iff`, `eval_independent_iff`, `eval_dominating_iff`,
    `eval_vertexCover_iff`, `eval_bipartite_iff`가 `SimpleGraph` 위에서 컴파일된다.

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
- `IncidenceGraph V E`는 explicit incidence가 필요한 보조 표현으로 유지하되,
  핵심 의미론과 예제 정리는 우선 `SimpleGraph`에 직접 붙인다.
- `Assignment V E`는 유지한다. `SimpleGraph` 위에서는 `E := G.edgeSet`으로 instantiate한다.
- 자유 변수가 있는 공식은 `EvalAt phi G rho`로 다룬다.
- 닫힌 문장 또는 graph property는 `Eval phi G`로 다루되, assignment independence 정리를
  증명하기 전까지는 현재의 `forall rho, EvalAt phi G rho` 정의를 사용한다.
- 정점 집합은 `Set V`, 간선 집합은 `Set G.edgeSet`을 기본으로 사용한다.
- 유한성, 결정 가능성, treewidth bound는 그래프 구조체에 넣지 않고 필요한 정리에서
  `[Fintype V]`, `[DecidableEq V]`, `[DecidableRel G.Adj]`, tree decomposition 가정으로 둔다.
- Courcelle formalization은 다음 층위를 분리한다.
  - 순수 의미론: `EvalAt`, `Eval`.
  - 유한 실행 의미론: finite evaluator와 correctness.
  - tree decomposition API: bags, width, nice decomposition.
  - 동적 계획법/automata 계층: decomposition 위 model checking.
  - 최종 정리: bounded treewidth graph class에서 MSO2 model checking 가능성.

## 1단계: 핵심 언어와 `SimpleGraph` 의미론 안정화

완료됨:

- `Formula`의 MSO2 문법.
- `Assignment V E`와 update API.
- `SimpleGraph` 기반 `EvalAt` 도입.
- 요청한 형태의 `Eval (phi : Formula) : SimpleGraph V -> Prop` 도입.
- `inc` 원자식을 `G.edgeSet`의 `Sym2 V` membership으로 해석.
- `EvalAt` 주변의 기본 simp-friendly lemma.
- 대표 예제 공식의 `SimpleGraph` 의미론 정리.

남은 작업:

- `EvalAt` lemma 이름과 `[simp]` 전략을 정리한다.
- edge quantifier helper에 대한 simp lemma를 추가한다.
- 기존 `IncidenceGraph` 변환 정리가 새 `SimpleGraph` 주 경로와 충돌하지 않도록 정리한다.

완료 기준:

- 핵심 정의에 `sorry`가 없다.
- `lake build`가 통과한다.
- 대표 예제 공식이 `EvalAt`에서 직접 펼쳐져 증명 가능한 형태로 나온다.

## 2단계: 바인딩, 자유 변수, assignment independence

현재 문법은 이름 있는 numeric variable을 사용한다. 이 방식은 초기 예제에는 읽기 쉽지만,
치환과 알파 동치 증명이 늘어나면 fresh-name side condition이 반복될 수 있다.

완료됨:

- `Formula.FreeFO : Formula -> FOVar -> Prop`.
- `Formula.FreeSO : Formula -> SOVar -> Prop`.
- `Formula.FreeEdgeFO : Formula -> EdgeFOVar -> Prop`.
- `Formula.FreeEdgeSO : Formula -> EdgeSOVar -> Prop`.
- `Formula.Closed : Formula -> Prop`.
- `hasNonemptyClique_closed` 예제.

남은 작업:

- 자유 변수가 아닌 값을 바꿔도 `EvalAt`이 변하지 않는다는 정리를 증명한다.
  - 정점 1차 변수.
  - 정점 집합 2차 변수.
  - 간선 1차 변수.
  - 간선 집합 2차 변수.
- 닫힌 공식의 assignment independence를 증명한다.
- `Eval phi G`가 닫힌 공식에 대해 임의의 한 assignment 선택과 동치임을 증명한다.
- 필요하면 `Satisfies G phi` 또는 notation 계층을 추가한다.
- 알파 변환 정리를 증명한다.
- fresh-name side condition이 병목이 되면 내부 표현을 de Bruijn index 또는 locally nameless로
  바꾸는 것을 검토한다. named syntax는 user-facing DSL로 남긴다.

완료 기준:

- 닫힌 공식의 만족 관계를 assignment 선택 없이 사용할 수 있다.
- 대표 공식의 bound variable 이름을 바꾼 버전이 의미론적으로 동치임을 증명할 수 있다.

## 3단계: `SimpleGraph` 그래프 술어와 MSO 명세 라이브러리

목표는 손으로 쓴 `SimpleGraph` 술어와 MSO 공식 사이의 동치성을 Lean에서 증명하는 것이다.

완료됨:

- mathlib `SimpleGraph.IsClique`와 `Examples.clique`의 동치.
- `SimpleGraph.IsIndependent`와 `Examples.independent`의 동치.
- `SimpleGraph.IsDominating`과 `Examples.dominating`의 동치.
- `SimpleGraph.IsVertexCover`와 `Examples.vertexCover`의 동치.
- `SimpleGraph.IsBipartiteByEdges`와 `Examples.bipartite`의 동치.

남은 작업:

- mathlib에 이미 있는 정의와 프로젝트-local 정의를 구분하고 이름을 정리한다.
- fixed `k` coloring, connectedness, disconnectedness 공식을 추가한다.
- MSO2가 필요한 spanning tree, Hamiltonian cycle, minor 관련 인코딩을 추가한다.
- `perfectMatching` 공식의 `SimpleGraph.HasPerfectMatching` 정확성 정리를 추가한다.
- 필요하면 `IncidenceGraph.fromSimpleGraph`를 통한 compatibility theorem을 별도로 제공한다.

완료 기준:

- 주요 예제 공식마다 손으로 쓴 `SimpleGraph` 술어와의 iff 정리가 있다.
- theorem statement가 이후 Courcelle 명세에서 재사용 가능한 모양이다.

## 4단계: 유한 model checking 의미론

Courcelle theorem으로 가려면, 순수 `Prop` 의미론과 별도로 유한 그래프에서 실행 가능한
model checker가 필요하다.

남은 작업:

- `[Fintype V]`, `[DecidableEq V]`, `[DecidableRel G.Adj]` 하에서 finite evaluator를 정의한다.
- edge sort `G.edgeSet`의 finite enumeration을 mathlib API와 연결한다.
- vertex set quantifier는 `Finset.powerset` 또는 finite `Set` enumeration과 연결한다.
- edge set quantifier는 `G.edgeSet`의 powerset enumeration과 연결한다.
- executable evaluator와 `EvalAt` 사이의 correctness theorem을 증명한다.

완료 기준:

- 유한 `SimpleGraph`와 assignment에 대해 executable Boolean evaluator가 있다.
- Boolean evaluator가 `EvalAt`과 동치임을 증명한다.

## 5단계: tree decomposition과 treewidth

Courcelle theorem의 graph-theoretic 핵심 API를 만든다.

남은 작업:

- tree decomposition 구조를 정의한다.
  - decomposition tree.
  - bag : node -> Finset V 또는 Set V.
  - vertex coverage.
  - edge coverage.
  - running intersection property.
- width와 treewidth bound를 정의한다.
- nice tree decomposition을 정의하거나 기존 decomposition을 nice form으로 변환하는 정리를 검토한다.
- mathlib의 graph/tree/path/connectivity API를 최대한 재사용한다.

완료 기준:

- `TreeDecomposition G`와 `width <= k`를 표현할 수 있다.
- 대표적인 작은 그래프의 decomposition 예제가 컴파일된다.

## 6단계: bounded treewidth 위 MSO model checking

남은 작업:

- 공식의 quantifier rank 또는 상태 공간을 제한하는 measure를 정의한다.
- bag type 위 partial assignment/state를 정의한다.
- nice tree decomposition node별 transition을 정의한다.
- transition의 local soundness/completeness를 증명한다.
- 전체 decomposition에 대한 dynamic-programming evaluator를 정의한다.
- evaluator correctness를 `Eval` 또는 닫힌 공식 만족 관계와 연결한다.

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
  - `EvalAt`/`Eval`의 파생 연결자.
  - `Set` membership/subset/equality.
  - `SimpleGraph` 술어 unfolding.
  - 리스트 양화 helper.
- 사용자-facing notation을 검토한다.
  - `⊨`, `¬`, `∧`, `∨`, `∀'`, `∃'` 같은 표기법은 core API가 안정된 뒤 추가한다.
- 예제와 smoke test를 확장한다.
- CI를 추가한다.
  - 최소 CI는 `lake exe cache get` 후 `lake build`이다.

## 권장 작업 순서

1. `EvalAt`의 edge quantifier 및 파생 연결자 simp lemma를 보강한다.
2. `FreeFO`/`FreeSO`/`FreeEdgeFO`/`FreeEdgeSO` 기반 assignment irrelevance를 증명한다.
3. 닫힌 공식의 assignment independence와 `Satisfies` 계층을 정의한다.
4. `perfectMatching`, connectedness, fixed-colorability 정리까지 `SimpleGraph` 예제를 확장한다.
5. finite executable evaluator와 correctness theorem을 만든다.
6. tree decomposition과 treewidth API를 설계한다.
7. nice decomposition 위 model checking dynamic programming을 형식화한다.
8. Courcelle theorem statement를 약한 형태부터 세운다.
