import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14092 = true := by
  decide +kernel

theorem tot14092 : totK PD2M8K2 D2M8K2.t14092 = [0, 0, 203330765945, 478824186860, 207025007412, 7897782202, 0, 0] := by
  decide +kernel

theorem rows14093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14093 = true := by
  decide +kernel

theorem tot14093 : totK PD2M8K2 D2M8K2.t14093 = [0, 78440106414, 249674008067, 384316507315, 175667626171, 8191059680, 0, 0] := by
  decide +kernel

theorem rows14094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14094 = true := by
  decide +kernel

theorem tot14094 : totK PD2M8K2 D2M8K2.t14094 = [0, 180300845383, 462520992899, 254601369296, 23001792254, 0, 0, 0] := by
  decide +kernel

theorem rows14095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14095 = true := by
  decide +kernel

theorem tot14095 : totK PD2M8K2 D2M8K2.t14095 = [0, 156127739741, 451487046007, 270434102834, 23528793030, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
