import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8196 = true := by
  decide +kernel

theorem tot8196 : totK PD2M8K2 D2M8K2.t8196 = [0, 185037560225, 478181169600, 235786718181, 15775489898, 0, 0, 0] := by
  decide +kernel

theorem rows8197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8197 = true := by
  decide +kernel

theorem tot8197 : totK PD2M8K2 D2M8K2.t8197 = [0, 64042052726, 332528557057, 415125235961, 96238576528, 1268739303, 0, 0] := by
  decide +kernel

theorem rows8198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8198 = true := by
  decide +kernel

theorem tot8198 : totK PD2M8K2 D2M8K2.t8198 = [0, 0, 226958378530, 491222534100, 166412244305, 5812296316, 0, 0] := by
  decide +kernel

theorem rows8199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8199 = true := by
  decide +kernel

theorem tot8199 : totK PD2M8K2 D2M8K2.t8199 = [0, 0, 183794706961, 470109890208, 222204307671, 16337563977, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
