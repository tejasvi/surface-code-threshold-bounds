import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15028 = true := by
  decide +kernel

theorem tot15028 : totK PD2M8K2 D2M8K2.t15028 = [0, 176045873872, 429833329094, 215417975436, 66056429981, 9758758476, 0, 0] := by
  decide +kernel

theorem rows15029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15029 = true := by
  decide +kernel

theorem tot15029 : totK PD2M8K2 D2M8K2.t15029 = [0, 203142483677, 478317048704, 199703847684, 7650820675, 0, 0, 0] := by
  decide +kernel

theorem rows15030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15030 = true := by
  decide +kernel

theorem tot15030 : totK PD2M8K2 D2M8K2.t15030 = [0, 37663951278, 310671327171, 447963104686, 91966905189, 1369150432, 0, 0] := by
  decide +kernel

theorem rows15031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15031 = true := by
  decide +kernel

theorem tot15031 : totK PD2M8K2 D2M8K2.t15031 = [0, 77284936559, 370732704514, 421424775983, 46375460534, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
