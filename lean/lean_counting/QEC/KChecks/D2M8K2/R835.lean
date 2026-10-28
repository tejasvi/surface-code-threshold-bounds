import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3340 = true := by
  decide +kernel

theorem tot3340 : totK PD2M8K2 D2M8K2.t3340 = [0, 0, 80226612636, 339227756801, 349179730095, 68182588356, 1217496766, 0] := by
  decide +kernel

theorem rows3341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3341 = true := by
  decide +kernel

theorem tot3341 : totK PD2M8K2 D2M8K2.t3341 = [0, 0, 92362131504, 391709904057, 361473068825, 37175262670, 0, 0] := by
  decide +kernel

theorem rows3342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3342 = true := by
  decide +kernel

theorem tot3342 : totK PD2M8K2 D2M8K2.t3342 = [0, 0, 189432732871, 457038464890, 247269270005, 21362736011, 0, 0] := by
  decide +kernel

theorem rows3343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3343 = true := by
  decide +kernel

theorem tot3343 : totK PD2M8K2 D2M8K2.t3343 = [0, 0, 219431343771, 484237105656, 174609213288, 9296248165, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
