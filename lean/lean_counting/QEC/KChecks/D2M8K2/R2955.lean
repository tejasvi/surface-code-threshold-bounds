import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11820 = true := by
  decide +kernel

theorem tot11820 : totK PD2M8K2 D2M8K2.t11820 = [0, 207786537624, 489924509502, 208645988029, 11227850199, 0, 0, 0] := by
  decide +kernel

theorem rows11821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11821 = true := by
  decide +kernel

theorem tot11821 : totK PD2M8K2 D2M8K2.t11821 = [0, 0, 262318072972, 480089602321, 164295171928, 9631076594, 0, 0] := by
  decide +kernel

theorem rows11822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11822 = true := by
  decide +kernel

theorem tot11822 : totK PD2M8K2 D2M8K2.t11822 = [0, 0, 225631073738, 493979511085, 182379910063, 5382912678, 0, 0] := by
  decide +kernel

theorem rows11823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11823 = true := by
  decide +kernel

theorem tot11823 : totK PD2M8K2 D2M8K2.t11823 = [0, 172251388467, 452693045986, 253478125539, 25173173182, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
