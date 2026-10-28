import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5756 = true := by
  decide +kernel

theorem tot5756 : totK PD2M8K2 D2M8K2.t5756 = [0, 160334737954, 471883551174, 255335845988, 13916467904, 0, 0, 0] := by
  decide +kernel

theorem rows5757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5757 = true := by
  decide +kernel

theorem tot5757 : totK PD2M8K2 D2M8K2.t5757 = [0, 0, 281785440489, 514442751782, 100380976351, 1096505104, 0, 0] := by
  decide +kernel

theorem rows5758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5758 = true := by
  decide +kernel

theorem tot5758 : totK PD2M8K2 D2M8K2.t5758 = [0, 98530574372, 342852882597, 349826839797, 97044102368, 3884009855, 0, 0] := by
  decide +kernel

theorem rows5759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5759 = true := by
  decide +kernel

theorem tot5759 : totK PD2M8K2 D2M8K2.t5759 = [0, 179079797742, 450622149158, 232040109485, 16954357240, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
