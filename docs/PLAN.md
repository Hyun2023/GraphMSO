# 계획

이 프로젝트의 목표는 Lean 4에서 그래프 위의 monadic second-order logic을
형식화하는 것이다. 현재 범위는 정점 집합을 2차 변수로 다루는 MSO1이다.
즉 1차 변수는 정점에 할당되고, 2차 변수는 `V -> Prop` 꼴의 정점 집합에
할당된다. 간선 집합을 2차 변수로 다루는 MSO2는 당장 목표로 삼지 않고,
필요해질 때 별도 확장으로 설계한다.

초기 버전은 mathlib 의존성 없이 작게 유지한다. 핵심 언어, 의미론, 예제
공식, 기본 증명 API가 안정된 뒤에 mathlib의 `SimpleGraph`, `Set`, finite
그래프 API와 연결하는 계층을 추가한다.

## 현재 상태

- `GraphMSO.Basic`
  - `Graph V`는 `Adj : V -> V -> Prop` 하나로 표현한다.
  - 기본 인코딩은 directed graph, looped graph, infinite graph를 모두 허용한다.
  - 단순 무방향 그래프는 별도 조건 `Graph.Simple`로 표현한다.
  - `VSet V := V -> Prop`를 사용해 mathlib 없이 정점 집합을 표현한다.
  - `Graph.IsClique`, `Graph.IsIndependent` 같은 손으로 쓴 그래프 술어가 있다.
- `GraphMSO.Syntax`
  - 1차 변수 `FOVar`와 2차 변수 `SOVar`는 현재 모두 `Nat`이다.
  - 원자식은 `false_`, `equal`, `edge`, `inSet`이다.
  - 명제 연결자와 1차/2차 양화사를 포함하는 `Formula`가 정의되어 있다.
  - `true_`, `notEqual`, `subset`, `setEq`, `existsFOs`, `forallFOs` 같은 파생
    생성자가 있다.
- `GraphMSO.Semantics`
  - `Assignment V`는 `fo : FOVar -> V`, `so : SOVar -> VSet V`를 가진다.
  - `updateFO`, `updateSO`로 바인더의 shadowing을 표현한다.
  - `Semantics.Eval`은 그래프와 할당에 대한 타르스키 의미론이다.
- `GraphMSO.Examples`
  - clique, independent set, dominating set, nonempty clique 예제 공식이 있다.
  - 현재 예제는 smoke test 중심이며, 손으로 쓴 그래프 술어와의 동치성 증명은
    아직 본격적으로 추가하지 않았다.

## 설계 원칙

- 핵심 정의는 가능한 한 작은 의존성 위에 둔다.
- 그래프 구조 자체에는 단순성, 유한성, 결정 가능성을 강제하지 않는다.
  필요한 정리에서 `Graph.Simple G`, finite graph 조건, decidable adjacency를
  가정한다.
- MSO 문법과 의미론은 그래프 이론 API와 느슨하게 결합한다.
  먼저 `Formula`와 `Eval`을 안정화하고, 이후 재사용 가능한 명세 라이브러리를
  쌓는다.
- 표기법과 매크로는 늦게 추가한다. 초반에는 명시적인 생성자를 사용해 증명
  목표가 예측 가능하게 보이도록 한다.
- 각 단계의 완료 기준은 `lake build` 성공과 대표 정리의 컴파일이다.

## 1단계: 핵심 언어와 의미론 안정화

목표는 현재 scaffold를 MSO1의 신뢰할 수 있는 최소 커널로 만드는 것이다.

- `Graph V`의 관계 기반 표현을 유지한다.
  - `Adj : V -> V -> Prop`를 기본 표현으로 둔다.
  - loop-free, symmetric, simple 조건은 `Graph.Irreflexive`,
    `Graph.Symmetric`, `Graph.Simple` 같은 보조 술어로 유지한다.
  - 이후 mathlib 연결 계층이 생겨도 이 커널은 독립적으로 빌드 가능해야 한다.
- `Formula`의 기본 문법을 정리한다.
  - MSO1 범위의 원자식은 `equal x y`, `edge x y`, `inSet x X`로 충분한지
    계속 점검한다.
  - `false_`, `neg`, `conj`, `disj`, `impl`, `biimpl`, `existsFO`, `forallFO`,
    `existsSO`, `forallSO`를 핵심 생성자로 유지한다.
  - `true_`, `notEqual`, `subset`, `setEq`, finite-list quantifier helper는
    파생 정의로 유지한다.
- `Eval` 주변의 기본 정리를 늘린다.
  - `eval_true`, `eval_equal_self` 같은 현재 정리를 확장한다.
  - `Eval G rho (Formula.notEqual x y)`와 `rho.fo x != rho.fo y`의 관계를
    쓰기 쉬운 형태로 정리한다.
  - `conj`, `disj`, `impl`, `biimpl`에 대한 simp-friendly lemma를 추가한다.
  - `existsFOs`, `forallFOs`가 리스트에 대해 기대한 의미론을 갖는다는 정리를
    추가한다.
- 할당 갱신 API를 보강한다.
  - `updateFO_here`, `updateSO_here`는 이미 있다.
  - `x != y`일 때 `(rho.updateFO x v).fo y = rho.fo y`를 증명한다.
  - `X != Y`일 때 `(rho.updateSO X S).so Y = rho.so Y`를 증명한다.
  - 서로 다른 변수에 대한 update 교환 법칙을 추가한다.

완료 기준:

- `lake build`가 통과한다.
- 핵심 정의에 `sorry`가 없다.
- 대표 예제 공식이 `Eval`에서 직접 펼쳐져 증명 가능한 형태로 나온다.

## 2단계: 바인딩, 자유 변수, 알파 변환

현재 문법은 이름 있는 numeric variable을 사용한다. 이 방식은 초기 예제에는
읽기 쉽지만, 치환과 알파 동치 증명이 늘어나면 불편해질 수 있다. 먼저 현재
표현 위에서 필요한 메타이론을 만들고, 부담이 커질 때 표현 변경을 판단한다.

- 자유 변수 술어를 정의한다.
  - `FreeFO : Formula -> FOVar -> Prop`
  - `FreeSO : Formula -> SOVar -> Prop`
  - 바인더 아래에서는 같은 이름의 변수가 shadowing됨을 정확히 반영한다.
- 할당 무관성 정리를 증명한다.
  - `x`가 `phi`의 자유 1차 변수가 아니면 `rho.fo x`를 바꾸어도
    `Eval G rho phi`가 변하지 않는다.
  - `X`가 `phi`의 자유 2차 변수가 아니면 `rho.so X`를 바꾸어도
    `Eval G rho phi`가 변하지 않는다.
  - 여러 변수에 대한 weakening 형태도 필요해지면 추가한다.
- 알파 변환 정리를 증명한다.
  - 바인딩된 1차 변수 이름을 fresh한 이름으로 바꿔도 의미론이 보존됨을
    증명한다.
  - 바인딩된 2차 변수 이름에 대해서도 같은 정리를 증명한다.
  - 이 정리들은 이후 정규형 변환과 매크로 생성 공식의 건전성에 필요하다.
- 치환은 필요할 때 추가한다.
  - 초반에는 assignment update와 알파 변환으로 충분한지 확인한다.
  - capture-avoiding substitution은 정규형 변환, 공식 합성, derived syntax
    자동화가 실제로 요구할 때 구현한다.
- 표현 변경 판단 기준을 둔다.
  - 알파 변환과 치환 증명에서 fresh-name side condition이 반복적으로 증명
    병목이 되면 de Bruijn index 또는 locally nameless 표현을 검토한다.
  - 변경할 경우 기존 named syntax를 사용자-facing DSL로 남기고, 내부 커널만
    de Bruijn으로 바꾸는 방식을 우선 검토한다.

완료 기준:

- 자유 변수와 assignment irrelevance 정리가 1차/2차 변수 모두에 대해 있다.
- 대표 공식의 bound variable 이름을 바꾼 버전이 의미론적으로 동치임을 증명할
  수 있다.

## 3단계: 그래프 이론 API와 MSO 명세 라이브러리

목표는 손으로 쓴 그래프 술어와 MSO 공식 사이의 동치성을 Lean에서 증명하는
것이다. 예제 공식이 단순히 컴파일되는 수준을 넘어서, 그래프 성질의 정확한
명세로 사용할 수 있어야 한다.

- 손으로 쓴 그래프 술어를 확장한다.
  - `Graph.IsClique`
  - `Graph.IsIndependent`
  - `Graph.IsDominating`
  - `Graph.IsVertexCover`
  - `Graph.IsColoring` 또는 `Graph.IsKColoring`
  - 연결성, 분리성, bipartite 같은 기본 성질
- 각 술어에 대응하는 MSO 공식을 만든다.
  - `Examples.clique X`
  - `Examples.independent X`
  - `Examples.dominating X`
  - `Examples.vertexCover X`
  - fixed `k`에 대한 `kColorable` 공식
  - 단순 무방향 그래프에서의 connectedness 공식: 비어 있지 않은 proper subset과
    그 여집합 사이에 crossing edge가 존재한다는 형태를 우선 검토한다.
- 의미론적 정확성 정리를 추가한다.
  - `Eval G rho (Examples.clique X) <-> Graph.IsClique G (rho.so X)`
  - `Eval G rho (Examples.independent X) <-> Graph.IsIndependent G (rho.so X)`
  - `Eval G rho (Examples.dominating X) <-> Graph.IsDominating G (rho.so X)`
  - vertex cover와 coloring에 대해서도 같은 형태의 정리를 추가한다.
- 단순 그래프 side condition을 정리한다.
  - 어떤 공식은 directed graph에서도 의미가 있고, 어떤 공식은
    `Graph.Simple G` 아래에서 일반적인 그래프 이론 의미와 맞는다.
  - 각 정리의 가정에 `Graph.Simple G`가 필요한지 명확히 표시한다.
- 유한 그래프 계층을 검토한다.
  - core에는 유한성을 강제하지 않는다.
  - model checking, cardinality, coloring 수식처럼 유한성이 필요한 부분은
    별도 namespace 또는 별도 파일로 분리한다.
  - mathlib 도입 후 `Fintype`, `Finset`, `Set` 기반 API와 연결하는 방식을
    검토한다.

완료 기준:

- 주요 예제 공식마다 손으로 쓴 그래프 술어와의 iff 정리가 있다.
- 정리 이름과 namespace가 일관되어 이후 논문식 명세에서 재사용 가능하다.
- `Graph.Simple`이 필요한 정리와 필요 없는 정리가 구분되어 있다.

## 4단계: 닫힌 문장과 공식 동치성

MSO 공식이 그래프 성질을 표현한다는 말을 Lean에서 직접 다룰 수 있도록,
닫힌 문장과 그래프 클래스 위의 동치성을 정의한다.

- 닫힌 공식 또는 문장 개념을 정의한다.
  - `Closed phi := forall x, Not (FreeFO phi x)`와
    `forall X, Not (FreeSO phi X)` 형태를 우선 고려한다.
  - 닫힌 공식의 `Eval`은 assignment에 독립적임을 증명한다.
  - assignment 선택을 숨긴 `Satisfies G phi` 또는 `G ⊨ phi` 형태의 정의를
    나중에 추가한다.
- 공식 동치성을 정의한다.
  - 전체 그래프 위 동치: 모든 `G`, `rho`에 대해 `Eval G rho phi <-> Eval G rho psi`.
  - 그래프 클래스 위 동치: `C G`를 만족하는 그래프에 대해서만 동치.
  - 닫힌 문장 동치: assignment를 노출하지 않는 형태.
- 그래프 클래스 표현을 정리한다.
  - `GraphClass := forall V, Graph V -> Prop` 같은 universe 문제가 있는 표현은
    신중히 설계한다.
  - 초반에는 같은 vertex type 위의 predicate `Graph V -> Prop`로 시작하고,
    필요해질 때 universe-polymorphic class를 확장한다.
- Boolean algebra 법칙을 증명한다.
  - commutativity, associativity, distributivity, double negation 등
    의미론적 동치 정리.
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
  - minor 관련 인코딩은 MSO1에서 직접 가능한 범위와 MSO2가 필요한 범위를
    구분한 뒤 진행한다.
- 비표현 가능성은 별도 장기 목표로 둔다.
  - 비표현 가능성 증명은 Ehrenfeucht-Fraisse game, locality, compactness 등
    별도 메타이론이 필요할 수 있다.
  - 초기 목표에서는 조사 항목으로 남기고, core API를 비표현 가능성 증명에
    종속시키지 않는다.
- 유한 model checking을 검토한다.
  - 유한 vertex type과 decidable adjacency가 주어졌을 때 `Eval`의 decidable
    instance 또는 executable evaluator를 만들 수 있는지 확인한다.
  - 2차 양화는 powerset enumeration이 필요하므로 mathlib 또는 별도 finite
    enumeration API가 필요할 가능성이 높다.
  - correctness theorem은 executable evaluator와 `Eval` 사이의 iff로 둔다.

완료 기준:

- NNF 변환과 의미론 보존 정리가 있다.
- finite model checking의 필요한 가정과 구현 방향이 문서화되어 있다.
- 표현 가능성 예제가 명세 라이브러리 형태로 축적되어 있다.

## 6단계: mathlib 연결 계층

초기 커널이 안정되면 mathlib 기반 계층을 별도로 추가한다. 이 단계는 core를
무겁게 만들 수 있으므로 브랜치나 별도 파일 구조로 시작한다.

- `VSet V := V -> Prop`와 mathlib `Set V`의 관계를 정리한다.
- `Graph V`와 mathlib `SimpleGraph V` 사이의 변환을 정의한다.
  - `SimpleGraph.toGraphMSO`
  - `Graph.toSimpleGraph`는 `Graph.Simple G` 가정 아래에서만 가능하게 한다.
- 기존 정리를 mathlib 그래프에서 사용할 수 있는 wrapper theorem으로 제공한다.
- finite graph 결과는 mathlib의 `Fintype`, `Finset`, cardinality API와 연결한다.
- core 파일은 가능한 한 mathlib 없이 유지하고, mathlib 의존 파일은 명시적으로
  분리한다.

완료 기준:

- mathlib `SimpleGraph` 예제 하나가 MSO 공식 의미론 정리까지 연결된다.
- core 빌드와 mathlib 확장 빌드의 경계가 명확하다.

## 7단계: 도구화, 표기법, CI

증명과 예제가 늘어난 뒤에는 사용성을 높이는 계층을 추가한다.

- `simp` 보조정리를 정리한다.
  - assignment update
  - `Eval`의 파생 연결자
  - 그래프 술어 unfolding
  - 리스트 양화 helper
- 표기법을 추가한다.
  - 핵심 API가 안정된 뒤 `⊨`, `⊢`, `¬`, `∧`, `∨`, `∀'`, `∃'` 같은 표기법을
    검토한다.
  - 표기법은 pretty syntax 용도로만 두고, theorem statement에는 기본 생성자
    기반 버전도 접근 가능하게 한다.
- 테스트와 예제를 확장한다.
  - 대표 공식이 빌드되는 smoke test.
  - 대표 공식의 의미론적 정확성 theorem.
  - 정규형 변환 correctness theorem.
- CI를 추가한다.
  - 저장소의 최종 호스팅 위치가 정해지면 GitHub Actions를 추가한다.
  - 최소 CI는 `lake build`이다.
  - mathlib 계층이 별도라면 core CI와 mathlib CI를 분리한다.

완료 기준:

- 새 공식과 새 그래프 술어를 추가하는 패턴이 문서와 예제로 분명하다.
- CI에서 core 빌드가 항상 확인된다.
- 사용자-facing notation이 core theorem proving을 방해하지 않는다.

## 권장 작업 순서

1. `updateFO`/`updateSO`의 나머지 simp lemma를 추가한다.
2. `FreeFO`/`FreeSO`를 정의하고 assignment irrelevance를 증명한다.
3. `clique`, `independent`, `dominating` 공식의 의미론적 정확성 정리를 추가한다.
4. 닫힌 공식과 `Satisfies`를 정의한다.
5. vertex cover, coloring, connectedness 공식을 추가한다.
6. NNF 변환과 correctness theorem을 추가한다.
7. 유한 그래프와 mathlib 연결 계층을 별도 단계로 실험한다.
