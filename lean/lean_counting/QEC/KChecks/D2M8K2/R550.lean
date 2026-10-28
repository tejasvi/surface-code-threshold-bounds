import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2200 = true := by
  decide +kernel

theorem tot2200 : totK PD2M8K2 D2M8K2.t2200 = [0, 209309670019, 480373672366, 196097095854, 9848247143, 0, 0, 0] := by
  decide +kernel

theorem rows2201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2201 = true := by
  decide +kernel

theorem tot2201 : totK PD2M8K2 D2M8K2.t2201 = [0, 168586412237, 466415617300, 241668291781, 13795945806, 0, 0, 0] := by
  decide +kernel

theorem rows2202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2202 = true := by
  decide +kernel

theorem tot2202 : totK PD2M8K2 D2M8K2.t2202 = [0, 0, 284828508760, 492612242386, 110486643239, 1369150432, 0, 0] := by
  decide +kernel

theorem rows2203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2203 = true := by
  decide +kernel

theorem tot2203 : totK PD2M8K2 D2M8K2.t2203 = [0, 90954164743, 377001644818, 389183215668, 53619274807, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
