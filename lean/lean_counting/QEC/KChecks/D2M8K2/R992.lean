import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3968 = true := by
  decide +kernel

theorem tot3968 : totK PD2M8K2 D2M8K2.t3968 = [0, 0, 244675854945, 461702625085, 207898629219, 18044708413, 0, 0] := by
  decide +kernel

theorem rows3969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3969 = true := by
  decide +kernel

theorem tot3969 : totK PD2M8K2 D2M8K2.t3969 = [0, 0, 215394377713, 482245911891, 198085971041, 10597857724, 0, 0] := by
  decide +kernel

theorem rows3970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3970 = true := by
  decide +kernel

theorem tot3970 : totK PD2M8K2 D2M8K2.t3970 = [0, 0, 201588450779, 482790493533, 205732362932, 11380923020, 0, 0] := by
  decide +kernel

theorem rows3971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3971 = true := by
  decide +kernel

theorem tot3971 : totK PD2M8K2 D2M8K2.t3971 = [0, 0, 175059843225, 458100453052, 227820495389, 13515671070, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
