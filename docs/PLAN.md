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
  - `Assignment V E`는 삭제하지 않고 유지한다.
  - 정점 집합과 간선 집합 assignment는 별칭 없이 `Set V`, `Set E`로 표현한다.
  - `SimpleGraph V` 의미론에서는 edge sort를 `G.edgeSet`으로 특수화해
    `Assignment V G.edgeSet`을 사용한다.
  - `Semantics.EvalAt : Formula -> (G : SimpleGraph V) -> Assignment V G.edgeSet -> Prop`가
    실제 assignment-aware Tarski 의미론이다.
  - `Semantics.Eval : Formula -> SimpleGraph V -> Prop`는 닫힌 공식용 graph-property
    wrapper이다. 현재는 모든 assignment에서 참이라는 형태로 정의하며, 닫힌 공식에 대해서는
    임의의 한 assignment에서의 `EvalAt`과 동치임을 증명했다. 단, edge sort가 비어 있을 때
    vacuous truth가 생길 수 있으므로 Courcelle theorem statement에 쓰기 전에 교체해야 하는
    임시 정의이다.
  - `edge x y`는 `G.Adj (rho.fo x) (rho.fo y)`로, `inc x e`는
    `rho.fo x ∈ (rho.efo e : Sym2 V)`로 해석한다.
- `GraphMSO.Basic`
  - 삭제되었다. 각 모듈은 필요한 mathlib 모듈을 직접 import한다.
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
- `Assignment V E`는 유지한다. `SimpleGraph` 위에서는 `E := G.edgeSet`으로 instantiate한다.
- 정점 집합과 간선 집합은 `VSet`/`ESet` 별칭 없이 `Set V`, `Set G.edgeSet`을 직접 사용한다.
- 자유 변수가 있는 공식은 `EvalAt phi G rho`로 다룬다.
- 닫힌 문장 또는 graph property는 `Eval phi G` 또는 새 `Satisfies G phi` 계층으로 다루되,
  현재 `forall rho, EvalAt phi G rho` 형태의 `Eval`은 임시 정의로 본다.
- 유한성, 결정 가능성, treewidth bound는 그래프 구조체에 넣지 않고 필요한 정리에서
  `[Fintype V]`, `[DecidableEq V]`, `[DecidableRel G.Adj]`, tree decomposition 가정으로 둔다.
- Courcelle formalization은 다음 층위를 분리한다.
  - 순수 의미론: `EvalAt`, 닫힌 공식 만족 관계.
  - 유한 실행 의미론: finite evaluator와 correctness.
  - tree decomposition API: bags, width, nice decomposition.
  - 동적 계획법/automata 계층: decomposition 위 model checking.
  - 최종 정리: bounded treewidth graph class에서 MSO2 model checking 가능성.

## 1단계: 핵심 언어와 `SimpleGraph` 의미론 안정화

완료됨:

- 목표: MSO2 공식을 표현하는 핵심 문법을 둔다. 구현: `GraphMSO/Syntax.lean`의
  `inductive Formula`와 변수 별칭 `FOVar`, `SOVar`, `EdgeFOVar`, `EdgeSOVar`.
- 목표: 변수 해석을 담는 assignment와 shadowing update API를 둔다. 구현:
  `GraphMSO/Semantics.lean`의 `structure Assignment`, `Assignment.updateFO`,
  `Assignment.updateSO`, `Assignment.updateEdgeFO`, `Assignment.updateEdgeSO` 및 관련 `[simp]` 정리.
- 목표: mathlib `SimpleGraph V` 위에서 MSO2 Tarski 의미론을 정의한다. 구현:
  `GraphMSO/Semantics.lean`의 `Semantics.EvalAt`, edge sort는 `G.edgeSet`.
- 목표: 닫힌 공식 또는 graph property용 wrapper를 둔다. 구현:
  `GraphMSO/Semantics.lean`의 `Semantics.Eval`, 현재 정의는
  `∀ rho, EvalAt phi G rho`.
- 목표: MSO2의 incidence 원자식 `inc x e`를 `SimpleGraph` edge sort에 맞게 해석한다. 구현:
  `Semantics.EvalAt`의 `Formula.inc` case에서 `rho.fo x ∈ (rho.efo e : Sym2 V)`로 해석.
- 목표: `EvalAt`를 예제 증명에서 바로 펼칠 수 있게 기본 simp API를 둔다. 구현:
  `GraphMSO/Semantics.lean`의 `evalAt_notEqual`, `evalAt_conj`, `evalAt_disj`,
  `evalAt_impl`, `evalAt_biimpl`, `evalAt_existsFOs_*`, `evalAt_forallFOs_*`,
  그리고 `Assignment.update*` 관련 `[simp]` 정리.
- 목표: 대표 MSO 공식이 손으로 쓴 `SimpleGraph` 술어와 맞는지 확인한다. 구현:
  `GraphMSO/Examples.lean`의 `clique`, `independent`, `dominating`, `vertexCover`,
  `bipartite` 및 `eval_clique_iff`, `eval_independent_iff`, `eval_dominating_iff`,
  `eval_vertexCover_iff`, `eval_bipartite_iff`.
- 목표: Courcelle theorem 경로에서 쓰지 않는 incidence graph compatibility layer를 제거한다.
  구현: `GraphMSO/Basic.lean` 삭제.
- 목표: `GraphMSO.Basic`에 의존하던 별칭과 import를 제거하고 `Set`을 직접 사용한다. 구현:
  `GraphMSO/Semantics.lean`은 `Set V`, `Set E`, `Set G.edgeSet`을 직접 쓰고,
  `GraphMSO.lean`과 `GraphMSO/decomp.lean`의 `GraphMSO.Basic` import를 제거.

남은 작업:

- `Eval`의 vacuous truth 문제를 피하는 닫힌 공식 만족 관계를 정한다.
- `EvalAt` lemma 이름과 `[simp]` 전략을 정리한다.
- edge quantifier helper에 대한 simp lemma를 추가한다.

완료 기준:

- 핵심 정의에 `sorry`가 없다.
- `lake build`가 통과한다.
- 대표 예제 공식이 `EvalAt`에서 직접 펼쳐져 증명 가능한 형태로 나온다.

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
- 목표: 두 assignment가 공식의 자유 변수에서 같다는 관계를 정의하고, `EvalAt`가 그 값들에만
  의존함을 증명한다. 구현: `GraphMSO/Semantics.lean`의 `Assignment.AgreeOnFree`와
  `Semantics.evalAt_ext_on_free`.
- 목표: 닫힌 공식의 `EvalAt` 의미론이 assignment 선택과 무관함을 증명한다. 구현:
  `GraphMSO/Semantics.lean`의 `Semantics.evalAt_closed_independent`.
- 목표: 닫힌 공식에 대해 `Eval phi G`와 임의의 한 assignment에서의 `EvalAt phi G rho`를
  연결한다. 구현: `GraphMSO/Semantics.lean`의 `Semantics.eval_iff_evalAt_of_closed`.

남은 작업:

- 필요하면 `FreeFO`/`FreeSO`/`FreeEdgeFO`/`FreeEdgeSO`의 `Finset` 버전 또는 computable support를 추가한다.
- 필요하면 `Satisfies G phi` 또는 notation 계층을 추가한다.

완료 기준:

- 닫힌 공식의 만족 관계를 assignment 선택 없이 사용할 수 있다.
- finite evaluator와 DP 상태공간에서 필요한 자유 변수 support를 사용할 수 있다.

## 3단계: `SimpleGraph` 그래프 술어와 MSO 명세 라이브러리

목표는 손으로 쓴 `SimpleGraph` 술어와 MSO 공식 사이의 동치성을 Lean에서 증명하는 것이다.

완료됨:

- 목표: clique MSO 공식과 mathlib의 clique 술어를 연결한다. 구현:
  `GraphMSO/Examples.lean`의 `Examples.clique`와 `Examples.eval_clique_iff`.
- 목표: independent set MSO 공식과 `SimpleGraph` 술어를 연결한다. 구현:
  `GraphMSO/Examples.lean`의 `SimpleGraph.IsIndependent`, `Examples.independent`,
  `Examples.eval_independent_iff`.
- 목표: dominating set MSO 공식과 `SimpleGraph` 술어를 연결한다. 구현:
  `GraphMSO/Examples.lean`의 `SimpleGraph.IsDominating`, `Examples.dominating`,
  `Examples.eval_dominating_iff`.
- 목표: vertex cover MSO2 공식과 edge 기반 `SimpleGraph` 술어를 연결한다. 구현:
  `GraphMSO/Examples.lean`의 `SimpleGraph.IsVertexCover`, `Examples.vertexCover`,
  `Examples.eval_vertexCover_iff`.
- 목표: bipartite MSO2 공식과 edge 기반 `SimpleGraph` 술어를 연결한다. 구현:
  `GraphMSO/Examples.lean`의 `SimpleGraph.IsBipartiteByEdges`, `Examples.bipartite`,
  `Examples.eval_bipartite_iff`.

남은 작업:

- mathlib에 이미 있는 정의와 프로젝트-local 정의를 구분하고 이름을 정리한다.
- fixed `k` coloring, connectedness, disconnectedness 공식을 추가한다.
- MSO2가 필요한 spanning tree, Hamiltonian cycle, minor 관련 인코딩을 추가한다.
- `perfectMatching` 공식의 `SimpleGraph.HasPerfectMatching` 정확성 정리를 추가한다.

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

1. `Eval`의 임시 정의를 대체할 닫힌 공식 만족 관계를 정한다.
2. `EvalAt`의 edge quantifier 및 파생 연결자 simp lemma를 보강한다.
3. 닫힌 공식용 `Satisfies` 계층을 정의한다.
4. 필요하면 finite evaluator용 computable free-variable support를 추가한다.
5. `perfectMatching`, connectedness, fixed-colorability 정리까지 `SimpleGraph` 예제를 확장한다.
6. finite executable evaluator와 correctness theorem을 만든다.
7. tree decomposition과 treewidth API를 설계한다.
8. nice decomposition 위 model checking dynamic programming을 형식화한다.
9. Courcelle theorem statement를 약한 형태부터 세운다.
