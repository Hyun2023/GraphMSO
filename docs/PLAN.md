# 계획

이 프로젝트의 목표는 Lean 4와 mathlib 위에서 그래프에 대한 monadic
second-order logic(MSO2)을 형식화하는 것이다. 초기 목표였던 MSO1을 넘어서,
현재는 간선 집합을 2차 변수로 다루는 MSO2 형식화를 목표로 한다. 즉 1차 변수는 
정점이나 간선에 할당되고, 2차 변수는 정점 집합(`Set V`)과 간선 집합에 할당된다.

프로젝트는 이제 mathlib에 의존한다. 기본 그래프 표현은 정점 `V`와 간선 `E`를 갖는
`Graph V E` 구조체를 사용하며, 정점 집합은 `Set V`, 간선 집합은 `Set E`를 사용한다. mathlib `SimpleGraph`와
오가는 변환을 기본 API에 포함한다. 빌드할 때는 mathlib를 직접 컴파일하지
않도록 `lake exe cache get`을 먼저 실행한다.

## 현재 상태

- `lakefile.toml`
  - mathlib `v4.28.0-rc1`에 의존한다.
  - `lake-manifest.json`에는 mathlib와 transitive dependency들이 고정되어 있다.
- `GraphMSO.Basic`
  - `Graph V E`는 발생 관계 `inc : V -> E -> Prop`를 가진 구조체로 표현한다.
  - 각 간선은 최소 1개, 최대 2개의 정점과 연결된다는 제약을 공리로 포함한다.
  - 기존의 인접 관계는 `Adj u v := ∃ e, inc u e ∧ inc v e`로 파생된다.
  - 단순 무방향 그래프는 `Graph.Simple`로 표현한다.
  - `VSet V := Set V`, `ESet E := Set E`로 정점과 간선 집합을 표현한다.
  - mathlib `SimpleGraph`와의 변환이 있다.
    - `Graph.fromSimpleGraph`
    - `Graph.toSimpleGraph`
    - `Graph.fromSimpleGraph_simple`
  - `Graph.IsClique`, `Graph.IsIndependent`, `Graph.IsDominating`이 있다.
- `GraphMSO.Syntax`
  - 1차 변수 `FOVar`와 2차 변수 `SOVar`는 현재 모두 `Nat`이다.
  - 원자식은 `false_`, `equal`, `edge`, `inSet`이다.
  - 명제 연결자와 1차/2차 양화사를 포함하는 `Formula`가 정의되어 있다.
  - `true_`, `notEqual`, `subset`, `setEq`, `existsFOs`, `forallFOs` 같은 파생
    생성자가 있다.
  - `Formula.FreeFO`, `Formula.FreeSO`, `Formula.Closed`가 있다.
- `GraphMSO.Semantics`
  - `Assignment V`는 `fo : FOVar -> V`, `so : SOVar -> VSet V`를 가진다.
  - `updateFO`, `updateSO`로 바인더의 shadowing을 표현한다.
  - `Semantics.Eval`은 그래프와 할당에 대한 타르스키 의미론이다.
  - `inSet x X`의 의미론은 `rho.fo x ∈ rho.so X`이다.
  - assignment update에 대한 기본 `simp` lemma가 있다.
- `GraphMSO.Examples`
  - clique, independent set, dominating set, nonempty clique 예제 공식이 있다.
  - `eval_clique_iff`, `eval_independent_iff`, `eval_dominating_iff`가 있다.
  - `clique_no_freeFO`, `clique_freeSO_iff`, `hasNonemptyClique_closed`가 있다.

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

- MSO 의미론은 정점과 간선을 명시적으로 다루는 `Graph V E` 위에 둔다.
- mathlib와의 연결은 기본 API에서 제공한다. 특히 정점 집합은 항상 `Set V`를
  사용하고, 단순 그래프와 관련된 외부 API는 `SimpleGraph` wrapper를 통해 연결한다.
- 그래프 구조 자체에는 단순성, 유한성, 결정 가능성을 강제하지 않는다.
  필요한 정리에서 `Graph.Simple G`, `Fintype V`, decidable adjacency 등을 가정한다.
- 표기법과 매크로는 핵심 API와 정리 이름이 안정된 뒤에 추가한다.
- 각 단계의 완료 기준은 `lake exe cache get` 이후 `lake build` 성공과 대표 정리의
  컴파일이다.

## 1단계: 핵심 언어와 의미론 안정화 및 MSO2 확장

목표는 기존의 MSO1 기반 커널을 MSO2로 확장하고 안정화하는 것이다. 상당 부분은 
이미 구현되어 있으나, 간선 집합을 다루기 위한 문법 및 의미론 확장이 필요하다.

완료됨:

- `Graph V E`의 발생 관계 기반 표현으로 구조 변경.
- `VSet V := Set V`.
- `Graph.Simple`, `Graph.Irreflexive`, `Graph.Symmetric`.
- `Formula`의 핵심 문법.
- `Assignment`와 `Semantics.Eval`.
- assignment update 기본 `simp` lemma.
- `SimpleGraph` 기본 변환 정의.

남은 작업:

- MSO2 확장을 위한 문법과 의미론을 추가한다.
  - 간선 집합을 위한 2차 변수(`EdgeSOVar`)를 추가한다.
  - 간선 집합에 대한 소속성(membership) 및 발생(incidence) 관계를 나타내는 원자식을 추가한다.
  - `Assignment`를 확장하여 간선 집합에 대한 할당을 포함시킨다.
- `GraphMSO.Basic`의 그래프 API 및 증명을 보완한다.
  - MSO2(`Graph V E`) 확장을 위해 잠시 제거된 `induced`(유도 부분 그래프)와 `complete`(완전 그래프)를 명시적 간선 타입에 맞춰 다시 구현한다.
  - `fromSimpleGraph` 및 `fromSimpleGraph_simple` 등에 남아있는 `sorry` 증명을 채운다.
- `Eval` 주변의 기본 정리를 늘린다.
  - `Eval G rho (Formula.notEqual x y)`와 `rho.fo x != rho.fo y`의 관계.
  - `conj`, `disj`, `impl`, `biimpl`에 대한 simp-friendly lemma.
  - `existsFOs`, `forallFOs`의 의미론 정리.
- assignment update API를 보강한다.
  - 서로 다른 1차 변수 update 교환 법칙.
  - 서로 다른 2차 변수 update 교환 법칙.
  - 1차 update와 2차 update의 교환 법칙.

완료 기준:

- 핵심 정의에 `sorry`가 없다.
- `lake build`가 통과한다.
- 대표 예제 공식이 `Eval`에서 직접 펼쳐져 증명 가능한 형태로 나온다.

## 2단계: 바인딩, 자유 변수, 알파 변환

현재 문법은 이름 있는 numeric variable을 사용한다. 이 방식은 초기 예제에는
읽기 쉽지만, 치환과 알파 동치 증명이 늘어나면 fresh-name side condition이
반복될 수 있다.

완료됨:

- `Formula.FreeFO : Formula -> FOVar -> Prop`.
- `Formula.FreeSO : Formula -> SOVar -> Prop`.
- `Formula.Closed : Formula -> Prop`.
- `hasNonemptyClique_closed` 예제.

남은 작업:

- 할당 무관성 정리를 증명한다.
  - `x`가 `phi`의 자유 1차 변수가 아니면 `rho.fo x`를 바꾸어도
    `Eval G rho phi`가 변하지 않는다.
  - `X`가 `phi`의 자유 2차 변수가 아니면 `rho.so X`를 바꾸어도
    `Eval G rho phi`가 변하지 않는다.
  - 여러 변수에 대한 weakening 형태도 필요해지면 추가한다.
- 닫힌 공식의 assignment independence를 증명한다.
- 알파 변환 정리를 증명한다.
  - 바인딩된 1차 변수 이름을 fresh한 이름으로 바꿔도 의미론이 보존됨을 증명한다.
  - 바인딩된 2차 변수 이름에 대해서도 같은 정리를 증명한다.
- capture-avoiding substitution은 정규형 변환이나 공식 합성에서 실제로 필요해질
  때 추가한다.
- fresh-name side condition이 증명 병목이 되면 내부 표현을 de Bruijn index 또는
  locally nameless로 바꾸는 것을 검토한다. 이 경우 named syntax는 사용자-facing
  DSL로 남기는 방향을 우선한다.

완료 기준:

- 자유 변수와 assignment irrelevance 정리가 1차/2차 변수 모두에 대해 있다.
- 닫힌 공식의 `Eval`이 assignment 선택에 독립적임을 증명한다.
- 대표 공식의 bound variable 이름을 바꾼 버전이 의미론적으로 동치임을 증명할 수 있다.

## 3단계: 그래프 이론 API와 MSO 명세 라이브러리

목표는 손으로 쓴 그래프 술어와 MSO 공식 사이의 동치성을 Lean에서 증명하는
것이다. 예제 공식이 단순히 컴파일되는 수준을 넘어서, 그래프 성질의 정확한
명세로 사용할 수 있어야 한다.

완료됨:

- `Graph.IsClique`와 `Examples.clique`.
- `Graph.IsIndependent`와 `Examples.independent`.
- `Graph.IsDominating`과 `Examples.dominating`.
- 위 세 공식의 의미론적 정확성 정리.

남은 작업:

- 손으로 쓴 그래프 술어를 확장한다.
  - `Graph.IsVertexCover`.
  - `Graph.IsColoring` 또는 `Graph.IsKColoring`.
  - 연결성, 분리성, bipartite 같은 기본 성질.
      - Hamiltonicity, Eulerian circuit, Spanning tree 등 MSO2가 필요한 성질.
- 각 술어에 대응하는 MSO 공식을 만든다.
  - `Examples.vertexCover X`.
  - fixed `k`에 대한 `kColorable` 공식.
  - 단순 무방향 그래프에서의 connectedness 공식: 비어 있지 않은 proper subset과
    그 여집합 사이에 crossing edge가 존재한다는 형태를 우선 검토한다.
- 의미론적 정확성 정리를 추가한다.
  - vertex cover, coloring, connectedness에 대한 iff 정리.
  - 필요한 경우 `Graph.Simple G` 가정을 명확히 둔다.
- mathlib `SimpleGraph` wrapper theorem을 추가한다.
  - `Graph.fromSimpleGraph` 위의 MSO 정리를 `SimpleGraph` 문장으로 바로 사용할 수
    있게 한다.
  - mathlib의 기존 clique/independent 관련 API와 이름 및 방향을 맞춘다.

완료 기준:

- 주요 예제 공식마다 손으로 쓴 그래프 술어와의 iff 정리가 있다.
- 정리 이름과 namespace가 일관되어 이후 논문식 명세에서 재사용 가능하다.
- `Graph.Simple`이 필요한 정리와 필요 없는 정리가 구분되어 있다.
- `SimpleGraph` 사용자가 별도 변환 세부사항을 거의 의식하지 않아도 된다.

## 4단계: 닫힌 문장과 공식 동치성

MSO 공식이 그래프 성질을 표현한다는 말을 Lean에서 직접 다룰 수 있도록,
닫힌 문장과 그래프 클래스 위의 동치성을 정의한다.

- 닫힌 공식의 만족 관계를 정의한다.
  - assignment independence 정리 이후 `Satisfies G phi` 또는 `G ⊨ phi` 형태를 추가한다.
  - 닫힌 공식이 아닌 경우에는 기존 `Eval G rho phi`를 계속 사용한다.
- 공식 동치성을 정의한다.
  - 전체 그래프 위 동치: 모든 `G`, `rho`에 대해 `Eval G rho phi <-> Eval G rho psi`.
  - 그래프 클래스 위 동치: `C G`를 만족하는 그래프에 대해서만 동치.
  - 닫힌 문장 동치: assignment를 노출하지 않는 형태.
- 그래프 클래스 표현을 정리한다.
  - 초반에는 같은 vertex type 위의 predicate `Graph V -> Prop`로 시작한다.
  - 필요해질 때 universe-polymorphic graph class를 확장한다.
  - mathlib `SimpleGraph` 클래스와의 wrapper도 같은 방식으로 제공한다.
- Boolean algebra 법칙을 증명한다.
  - commutativity, associativity, distributivity, double negation 등 의미론적 동치 정리.
  - 이후 정규형 변환의 correctness proof에 재사용한다.

완료 기준:

- 닫힌 문장에 대해 assignment independence가 증명되어 있다.
- 그래프 클래스 위의 공식 동치성을 표현할 수 있다.
- 예제 공식의 간단한 변형들이 동치성 정리로 처리된다.

## 5단계: 정규형, 표현 가능성, 결정 가능성

핵심 의미론이 안정된 뒤에는 MSO 공식 변환과 model checking 쪽으로 확장한다.

- 정규형을 형식화한다.
  - negation normal form을 우선 구현한다.
  - 가능하면 prenex normal form을 검토한다.
  - 각 변환에 대해 `Eval` 보존 정리를 증명한다.
- 표현 가능성 예제를 모은다.
  - clique, independent set, dominating set, vertex cover, fixed-colorability.
  - connectedness, disconnectedness, bipartiteness 등 표준 그래프 성질.
      - MSO2를 적극 활용한 spanning tree, Hamiltonian cycle, minor 인코딩 예제를 추가한다.
- 비표현 가능성은 별도 장기 목표로 둔다.
  - 비표현 가능성 증명은 Ehrenfeucht-Fraisse game, locality, compactness 등 별도
    메타이론이 필요할 수 있다.
  - 초기 목표에서는 조사 항목으로 남기고, 기본 API를 비표현 가능성 증명에
    종속시키지 않는다.
- 유한 model checking을 검토한다.
  - `Fintype V`와 decidable adjacency가 주어졌을 때 executable evaluator를 만든다.
  - 2차 양화는 `Set V`의 finite enumeration 또는 `Finset V`/powerset API와 연결한다.
  - correctness theorem은 executable evaluator와 `Eval` 사이의 iff로 둔다.

완료 기준:

- NNF 변환과 의미론 보존 정리가 있다.
- finite model checking의 필요한 가정과 구현 방향이 문서화되어 있다.
- 표현 가능성 예제가 명세 라이브러리 형태로 축적되어 있다.

## 6단계: mathlib 활용 확장

mathlib 의존성은 이미 도입했다. 이 단계의 목표는 `Set`, `SimpleGraph`,
`Fintype`, `Finset` API를 더 적극적으로 이용해 그래프 이론 쪽 API를 키우는
것이다.

완료됨:

- `VSet V := Set V`로 정점 집합 표현을 mathlib와 맞췄다.
- `Graph V`와 mathlib `SimpleGraph V` 사이의 기본 변환을 정의했다.
- 빌드 절차에 `lake exe cache get`을 포함했다.

남은 작업:

- mathlib의 `Set` lemma를 적극적으로 활용해 membership, subset, equality 관련 증명을
  줄인다.
- `Graph.fromSimpleGraph`/`Graph.toSimpleGraph`에 대한 round-trip 성질을 추가한다.
- 기존 정리를 mathlib 그래프에서 바로 사용할 수 있는 wrapper theorem으로 제공한다.
- finite graph 결과를 mathlib의 `Fintype`, `Finset`, cardinality API와 연결한다.
- mathlib에 이미 있는 graph-theory 정의와 중복되는 이름은 의도적으로 wrapper인지,
  프로젝트 내부 술어인지 문서화한다.

완료 기준:

- mathlib `SimpleGraph` 예제 하나가 MSO 공식 의미론 정리까지 연결된다.
- finite graph API가 mathlib의 표준 finite/set/cardinality API와 자연스럽게 맞물린다.
- 새 정리를 추가할 때 mathlib search를 먼저 수행하는 관행이 자리 잡는다.

## 7단계: 도구화, 표기법, CI

증명과 예제가 늘어난 뒤에는 사용성을 높이는 계층을 추가한다.

- `simp` 보조정리를 정리한다.
  - assignment update.
  - `Eval`의 파생 연결자.
  - `Set` membership/subset/equality.
  - 그래프 술어 unfolding.
  - 리스트 양화 helper.
- 표기법을 추가한다.
  - 핵심 API가 안정된 뒤 `⊨`, `¬`, `∧`, `∨`, `∀'`, `∃'` 같은 표기법을 검토한다.
  - 표기법은 pretty syntax 용도로만 두고, theorem statement에는 기본 생성자 기반
    버전도 접근 가능하게 한다.
- 테스트와 예제를 확장한다.
  - 대표 공식이 빌드되는 smoke test.
  - 대표 공식의 의미론적 정확성 theorem.
  - 정규형 변환 correctness theorem.
- CI를 추가한다.
  - 최소 CI는 `lake exe cache get` 후 `lake build`이다.
  - dependency 변경 PR에서는 `lake-manifest.json` diff를 확인한다.

완료 기준:

- 새 공식과 새 그래프 술어를 추가하는 패턴이 문서와 예제로 분명하다.
- CI에서 mathlib cache 사용과 프로젝트 빌드가 항상 확인된다.
- 사용자-facing notation이 core theorem proving을 방해하지 않는다.

## 권장 작업 순서

1. `Eval`의 파생 연결자와 리스트 양화 helper에 대한 simp lemma를 추가한다.
2. `FreeFO`/`FreeSO` 기반 assignment irrelevance를 증명한다.
3. 닫힌 공식의 assignment independence와 `Satisfies`를 정의한다.
4. `SimpleGraph` wrapper theorem을 하나 추가해 mathlib 사용 경로를 검증한다.
5. vertex cover, coloring, connectedness 공식을 추가한다.
6. NNF 변환과 correctness theorem을 추가한다.
7. 유한 그래프와 mathlib `Fintype`/`Finset` 연결 계층을 실험한다.
