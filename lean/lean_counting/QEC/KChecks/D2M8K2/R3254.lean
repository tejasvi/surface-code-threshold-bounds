import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13016 = true := by
  decide +kernel

theorem tot13016 : totK PD2M8K2 D2M8K2.t13016 = [0, 0, 177490986487, 478717935116, 227073867585, 12370590376, 0, 0] := by
  decide +kernel

theorem rows13017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13017 = true := by
  decide +kernel

theorem tot13017 : totK PD2M8K2 D2M8K2.t13017 = [0, 0, 165649841851, 466535963662, 240522096172, 13419997576, 0, 0] := by
  decide +kernel

theorem rows13018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13018 = true := by
  decide +kernel

theorem tot13018 : totK PD2M8K2 D2M8K2.t13018 = [0, 0, 191148052775, 469403465491, 225301985879, 13845291295, 0, 0] := by
  decide +kernel

theorem rows13019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13019 = true := by
  decide +kernel

theorem tot13019 : totK PD2M8K2 D2M8K2.t13019 = [0, 0, 190883837559, 472021282560, 217650449930, 15844255384, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
