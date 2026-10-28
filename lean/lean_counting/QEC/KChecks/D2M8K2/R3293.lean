import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13172 = true := by
  decide +kernel

theorem tot13172 : totK PD2M8K2 D2M8K2.t13172 = [0, 92722817510, 409638328867, 343079598462, 47713942949, 1096505104, 0, 0] := by
  decide +kernel

theorem rows13173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13173 = true := by
  decide +kernel

theorem tot13173 : totK PD2M8K2 D2M8K2.t13173 = [0, 0, 309915084491, 527138073218, 88399422041, 0, 0, 0] := by
  decide +kernel

theorem rows13174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13174 = true := by
  decide +kernel

theorem tot13174 : totK PD2M8K2 D2M8K2.t13174 = [0, 0, 206931627821, 493457946207, 177730756510, 5253830308, 0, 0] := by
  decide +kernel

theorem rows13175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13175 = true := by
  decide +kernel

theorem tot13175 : totK PD2M8K2 D2M8K2.t13175 = [0, 0, 173191321074, 454886192356, 224066738312, 16891742343, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
