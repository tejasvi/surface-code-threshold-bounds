import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13352 = true := by
  decide +kernel

theorem tot13352 : totK PD2M8K2 D2M8K2.t13352 = [0, 0, 0, 303901283408, 472498286285, 79900668903, 1053411165, 0] := by
  decide +kernel

theorem rows13353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13353 = true := by
  decide +kernel

theorem tot13353 : totK PD2M8K2 D2M8K2.t13353 = [0, 0, 163963065441, 379978363728, 252096538625, 71737519836, 3667207281, 0] := by
  decide +kernel

theorem rows13354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13354 = true := by
  decide +kernel

theorem tot13354 : totK PD2M8K2 D2M8K2.t13354 = [0, 0, 161012605395, 467713830821, 265164130190, 14041306411, 0, 0] := by
  decide +kernel

theorem rows13355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13355 = true := by
  decide +kernel

theorem tot13355 : totK PD2M8K2 D2M8K2.t13355 = [0, 198027408646, 478545805846, 205845487232, 15014219822, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
