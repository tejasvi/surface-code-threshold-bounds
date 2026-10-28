import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12964 = true := by
  decide +kernel

theorem tot12964 : totK PD2M8K2 D2M8K2.t12964 = [0, 0, 248286548411, 488512606230, 155589143821, 9404247146, 0, 0] := by
  decide +kernel

theorem rows12965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12965 = true := by
  decide +kernel

theorem tot12965 : totK PD2M8K2 D2M8K2.t12965 = [0, 138856288286, 382667137262, 301248509561, 65955078506, 2481160468, 0, 0] := by
  decide +kernel

theorem rows12966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12966 = true := by
  decide +kernel

theorem tot12966 : totK PD2M8K2 D2M8K2.t12966 = [0, 171881243556, 437987791133, 277534287727, 30251713087, 0, 0, 0] := by
  decide +kernel

theorem rows12967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12967 = true := by
  decide +kernel

theorem tot12967 : totK PD2M8K2 D2M8K2.t12967 = [0, 109500347387, 416572400257, 324770921170, 33312668193, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
