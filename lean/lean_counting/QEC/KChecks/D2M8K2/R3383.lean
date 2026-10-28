import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13532 = true := by
  decide +kernel

theorem tot13532 : totK PD2M8K2 D2M8K2.t13532 = [0, 186982938029, 465010473501, 201692708821, 9757737807, 0, 0, 0] := by
  decide +kernel

theorem rows13533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13533 = true := by
  decide +kernel

theorem tot13533 : totK PD2M8K2 D2M8K2.t13533 = [0, 191198453373, 465888373377, 206221798684, 12403393969, 0, 0, 0] := by
  decide +kernel

theorem rows13534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13534 = true := by
  decide +kernel

theorem tot13534 : totK PD2M8K2 D2M8K2.t13534 = [0, 167599675215, 479694832842, 243847165351, 9495229574, 0, 0, 0] := by
  decide +kernel

theorem rows13535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13535 = true := by
  decide +kernel

theorem tot13535 : totK PD2M8K2 D2M8K2.t13535 = [0, 178987260804, 470527649256, 237525014163, 11616684087, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
