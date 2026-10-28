import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11972 = true := by
  decide +kernel

theorem tot11972 : totK PD2M8K2 D2M8K2.t11972 = [152982732611, 438984930966, 270006715832, 21307234316, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11973 = true := by
  decide +kernel

theorem tot11973 : totK PD2M8K2 D2M8K2.t11973 = [0, 276211104367, 501928050500, 110015323150, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows11974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11974 = true := by
  decide +kernel

theorem tot11974 : totK PD2M8K2 D2M8K2.t11974 = [125828629577, 389464192837, 351577250378, 48650850467, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11975 = true := by
  decide +kernel

theorem tot11975 : totK PD2M8K2 D2M8K2.t11975 = [189586260448, 468530805165, 232607850424, 16927251614, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
