import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13288 = true := by
  decide +kernel

theorem tot13288 : totK PD2M8K2 D2M8K2.t13288 = [0, 92963099499, 367926160102, 396712250134, 47064418418, 0, 0, 0] := by
  decide +kernel

theorem rows13289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13289 = true := by
  decide +kernel

theorem tot13289 : totK PD2M8K2 D2M8K2.t13289 = [0, 158616149040, 446442543346, 286649852461, 30470231449, 0, 0, 0] := by
  decide +kernel

theorem rows13290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13290 = true := by
  decide +kernel

theorem tot13290 : totK PD2M8K2 D2M8K2.t13290 = [0, 166329116705, 468115083287, 252844139978, 14882907245, 0, 0, 0] := by
  decide +kernel

theorem rows13291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13291 = true := by
  decide +kernel

theorem tot13291 : totK PD2M8K2 D2M8K2.t13291 = [0, 0, 204953707986, 464634379582, 219274420501, 21155208970, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
