import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11884 = true := by
  decide +kernel

theorem tot11884 : totK PD2M8K2 D2M8K2.t11884 = [0, 85094963948, 351089821818, 351561467379, 76048351171, 1369150432, 0, 0] := by
  decide +kernel

theorem rows11885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11885 = true := by
  decide +kernel

theorem tot11885 : totK PD2M8K2 D2M8K2.t11885 = [0, 0, 330780093781, 455356610527, 65197547034, 0, 0, 0] := by
  decide +kernel

theorem rows11886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11886 = true := by
  decide +kernel

theorem tot11886 : totK PD2M8K2 D2M8K2.t11886 = [0, 204790561139, 478378220189, 197252335971, 12496931999, 0, 0, 0] := by
  decide +kernel

theorem rows11887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11887 = true := by
  decide +kernel

theorem tot11887 : totK PD2M8K2 D2M8K2.t11887 = [0, 206416673094, 465092898020, 198709432389, 12593797338, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
