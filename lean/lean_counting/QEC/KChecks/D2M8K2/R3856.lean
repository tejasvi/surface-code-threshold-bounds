import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15424 = true := by
  decide +kernel

theorem tot15424 : totK PD2M8K2 D2M8K2.t15424 = [0, 0, 173075485837, 473678540606, 227590044816, 14691773714, 0, 0] := by
  decide +kernel

theorem rows15425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15425 = true := by
  decide +kernel

theorem tot15425 : totK PD2M8K2 D2M8K2.t15425 = [0, 0, 151465676402, 455738123562, 264936001871, 17821706616, 0, 0] := by
  decide +kernel

theorem rows15426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15426 = true := by
  decide +kernel

theorem tot15426 : totK PD2M8K2 D2M8K2.t15426 = [0, 0, 0, 297765602335, 481845526108, 85728564955, 1239866073, 0] := by
  decide +kernel

theorem rows15427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15427 = true := by
  decide +kernel

theorem tot15427 : totK PD2M8K2 D2M8K2.t15427 = [0, 0, 165745244471, 431257245351, 291522172102, 32766388781, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
