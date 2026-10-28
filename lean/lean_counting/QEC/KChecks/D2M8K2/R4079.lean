import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16316 = true := by
  decide +kernel

theorem tot16316 : totK PD2M8K2 D2M8K2.t16316 = [0, 0, 197763236220, 472082167685, 205654873148, 10833751948, 0, 0] := by
  decide +kernel

theorem rows16317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16317 = true := by
  decide +kernel

theorem tot16317 : totK PD2M8K2 D2M8K2.t16317 = [0, 0, 86944833919, 385267066022, 349959613353, 59600480517, 1369150432, 0] := by
  decide +kernel

theorem rows16318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16318 = true := by
  decide +kernel

theorem tot16318 : totK PD2M8K2 D2M8K2.t16318 = [0, 0, 0, 313249314492, 513628923464, 64824707449, 0, 0] := by
  decide +kernel

theorem rows16319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16319 = true := by
  decide +kernel

theorem tot16319 : totK PD2M8K2 D2M8K2.t16319 = [0, 0, 196286291092, 455987348044, 257932089282, 29585815552, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
