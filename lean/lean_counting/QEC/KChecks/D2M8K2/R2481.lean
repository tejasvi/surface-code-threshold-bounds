import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9924 = true := by
  decide +kernel

theorem tot9924 : totK PD2M8K2 D2M8K2.t9924 = [0, 0, 178542478942, 380596208129, 241374479174, 97006117932, 8997553167, 0] := by
  decide +kernel

theorem rows9925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9925 = true := by
  decide +kernel

theorem tot9925 : totK PD2M8K2 D2M8K2.t9925 = [0, 0, 174104837183, 464425098442, 238274619813, 17115888737, 0, 0] := by
  decide +kernel

theorem rows9926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9926 = true := by
  decide +kernel

theorem tot9926 : totK PD2M8K2 D2M8K2.t9926 = [0, 0, 87309021245, 389451998997, 361964158553, 52028951490, 1369150432, 0] := by
  decide +kernel

theorem rows9927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9927 = true := by
  decide +kernel

theorem tot9927 : totK PD2M8K2 D2M8K2.t9927 = [0, 0, 0, 300109633569, 511149252137, 88300398801, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
