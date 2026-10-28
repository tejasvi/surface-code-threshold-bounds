import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6976 = true := by
  decide +kernel

theorem tot6976 : totK PD2M8K2 D2M8K2.t6976 = [0, 0, 171105130618, 478406040605, 230332300466, 15976849042, 0, 0] := by
  decide +kernel

theorem rows6977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6977 = true := by
  decide +kernel

theorem tot6977 : totK PD2M8K2 D2M8K2.t6977 = [0, 0, 180139994889, 454111964693, 227213879352, 15039864920, 0, 0] := by
  decide +kernel

theorem rows6978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6978 = true := by
  decide +kernel

theorem tot6978 : totK PD2M8K2 D2M8K2.t6978 = [0, 0, 77236326090, 358201830733, 365997433256, 64627519796, 1128585284, 0] := by
  decide +kernel

theorem rows6979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6979 = true := by
  decide +kernel

theorem tot6979 : totK PD2M8K2 D2M8K2.t6979 = [0, 0, 18157133904, 293354461930, 437872881041, 108441574122, 4006170569, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
