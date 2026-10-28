import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13952 = true := by
  decide +kernel

theorem tot13952 : totK PD2M8K2 D2M8K2.t13952 = [0, 160842330922, 335665589650, 284102769732, 131778913619, 13326740810, 0, 0] := by
  decide +kernel

theorem rows13953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13953 = true := by
  decide +kernel

theorem tot13953 : totK PD2M8K2 D2M8K2.t13953 = [0, 179442016172, 471484930485, 240899080908, 15885214812, 0, 0, 0] := by
  decide +kernel

theorem rows13954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13954 = true := by
  decide +kernel

theorem tot13954 : totK PD2M8K2 D2M8K2.t13954 = [0, 105275039477, 435046031179, 343916225932, 38031935566, 0, 0, 0] := by
  decide +kernel

theorem rows13955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13955 = true := by
  decide +kernel

theorem tot13955 : totK PD2M8K2 D2M8K2.t13955 = [0, 0, 172896577810, 449128477734, 259568559989, 25373788367, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
