import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows56 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t56 = true := by
  decide +kernel

theorem tot56 : totK PA10K2 A10K2.t56 = [0, 0, 426063404824, 1712314150966, 1850284305554, 468708507120, 30954851499, 0, 0, 0] := by
  decide +kernel

theorem rows57 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t57 = true := by
  decide +kernel

theorem tot57 : totK PA10K2 A10K2.t57 = [0, 0, 0, 769901505161, 2249774481160, 1283677084089, 122895966298, 0, 0, 0] := by
  decide +kernel

theorem rows58 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t58 = true := by
  decide +kernel

theorem tot58 : totK PA10K2 A10K2.t58 = [0, 0, 779494084327, 2134576391779, 1629207468674, 384071454173, 82301551526, 5528811039, 0, 0] := by
  decide +kernel

theorem rows59 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t59 = true := by
  decide +kernel

theorem tot59 : totK PA10K2 A10K2.t59 = [0, 412800395519, 1271077156596, 1679878422223, 1238048693999, 371352274899, 29010686974, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
