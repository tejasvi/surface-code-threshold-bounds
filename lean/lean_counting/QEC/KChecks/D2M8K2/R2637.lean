import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10548 = true := by
  decide +kernel

theorem tot10548 : totK PD2M8K2 D2M8K2.t10548 = [0, 88830982688, 394429547277, 387518004805, 56847830684, 0, 0, 0] := by
  decide +kernel

theorem rows10549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10549 = true := by
  decide +kernel

theorem tot10549 : totK PD2M8K2 D2M8K2.t10549 = [0, 0, 184199668436, 490739239378, 206909357094, 7615388454, 0, 0] := by
  decide +kernel

theorem rows10550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10550 = true := by
  decide +kernel

theorem tot10550 : totK PD2M8K2 D2M8K2.t10550 = [0, 0, 180495253787, 438474744154, 271170855885, 31442555511, 0, 0] := by
  decide +kernel

theorem rows10551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10551 = true := by
  decide +kernel

theorem tot10551 : totK PD2M8K2 D2M8K2.t10551 = [0, 0, 176070554388, 473782112118, 244105840033, 12940973730, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
