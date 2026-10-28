import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8804 = true := by
  decide +kernel

theorem tot8804 : totK PD2M8K2 D2M8K2.t8804 = [0, 173278494500, 431250085221, 273540155440, 29641763786, 0, 0, 0] := by
  decide +kernel

theorem rows8805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8805 = true := by
  decide +kernel

theorem tot8805 : totK PD2M8K2 D2M8K2.t8805 = [0, 162481956503, 482688337221, 255154553283, 12656174787, 0, 0, 0] := by
  decide +kernel

theorem rows8806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8806 = true := by
  decide +kernel

theorem tot8806 : totK PD2M8K2 D2M8K2.t8806 = [0, 0, 216116304802, 458302974553, 210610226772, 21391863750, 0, 0] := by
  decide +kernel

theorem rows8807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8807 = true := by
  decide +kernel

theorem tot8807 : totK PD2M8K2 D2M8K2.t8807 = [0, 0, 173841037998, 469697116476, 230555745011, 9283897235, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
