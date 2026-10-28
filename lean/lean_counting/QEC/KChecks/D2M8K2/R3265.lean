import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13060 = true := by
  decide +kernel

theorem tot13060 : totK PD2M8K2 D2M8K2.t13060 = [0, 85228556775, 336601729564, 383822691252, 87137093902, 1198073392, 0, 0] := by
  decide +kernel

theorem rows13061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13061 = true := by
  decide +kernel

theorem tot13061 : totK PD2M8K2 D2M8K2.t13061 = [0, 0, 218206667915, 480699047156, 170253371953, 9482920370, 0, 0] := by
  decide +kernel

theorem rows13062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13062 = true := by
  decide +kernel

theorem tot13062 : totK PD2M8K2 D2M8K2.t13062 = [0, 155955097358, 414210937042, 269548641857, 56537328605, 2569691499, 0, 0] := by
  decide +kernel

theorem rows13063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13063 = true := by
  decide +kernel

theorem tot13063 : totK PD2M8K2 D2M8K2.t13063 = [0, 164878139619, 433401432580, 265091244728, 27134800991, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
