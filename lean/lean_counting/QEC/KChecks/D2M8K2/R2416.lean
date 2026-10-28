import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9664 = true := by
  decide +kernel

theorem tot9664 : totK PD2M8K2 D2M8K2.t9664 = [0, 107138926974, 324985569355, 315021927991, 133496350264, 13329350693, 0, 0] := by
  decide +kernel

theorem rows9665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9665 = true := by
  decide +kernel

theorem tot9665 : totK PD2M8K2 D2M8K2.t9665 = [0, 201677040208, 464037558455, 207101320116, 12586739997, 0, 0, 0] := by
  decide +kernel

theorem rows9666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9666 = true := by
  decide +kernel

theorem tot9666 : totK PD2M8K2 D2M8K2.t9666 = [0, 86938149001, 390341120884, 351359890826, 52227049524, 1369150432, 0, 0] := by
  decide +kernel

theorem rows9667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9667 = true := by
  decide +kernel

theorem tot9667 : totK PD2M8K2 D2M8K2.t9667 = [0, 0, 295731028941, 510163893600, 81786066699, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
