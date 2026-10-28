import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8420 = true := by
  decide +kernel

theorem tot8420 : totK PD2M8K2 D2M8K2.t8420 = [0, 0, 305502666299, 511147748178, 76415756453, 0, 0, 0] := by
  decide +kernel

theorem rows8421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8421 = true := by
  decide +kernel

theorem tot8421 : totK PD2M8K2 D2M8K2.t8421 = [0, 178066458620, 452680843744, 256623366758, 26637127453, 0, 0, 0] := by
  decide +kernel

theorem rows8422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8422 = true := by
  decide +kernel

theorem tot8422 : totK PD2M8K2 D2M8K2.t8422 = [0, 195197777409, 468010743129, 222597665749, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows8423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8423 = true := by
  decide +kernel

theorem tot8423 : totK PD2M8K2 D2M8K2.t8423 = [0, 51654843397, 324975145712, 427977437757, 85860001110, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
