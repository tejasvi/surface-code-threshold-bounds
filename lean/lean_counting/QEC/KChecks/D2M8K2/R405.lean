import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1620 = true := by
  decide +kernel

theorem tot1620 : totK PD2M8K2 D2M8K2.t1620 = [0, 0, 271031727544, 497931540118, 115896873444, 1198073392, 0, 0] := by
  decide +kernel

theorem rows1621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1621 = true := by
  decide +kernel

theorem tot1621 : totK PD2M8K2 D2M8K2.t1621 = [0, 47290973909, 217401792810, 413058295356, 186072389318, 12052611869, 0, 0] := by
  decide +kernel

theorem rows1622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1622 = true := by
  decide +kernel

theorem tot1622 : totK PD2M8K2 D2M8K2.t1622 = [0, 181507687754, 459075291705, 244314616615, 20531811098, 0, 0, 0] := by
  decide +kernel

theorem rows1623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1623 = true := by
  decide +kernel

theorem tot1623 : totK PD2M8K2 D2M8K2.t1623 = [0, 185789737481, 463469176956, 236610724571, 17104814242, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
