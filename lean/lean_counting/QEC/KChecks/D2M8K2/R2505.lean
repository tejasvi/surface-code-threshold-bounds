import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10020 = true := by
  decide +kernel

theorem tot10020 : totK PD2M8K2 D2M8K2.t10020 = [0, 195663955325, 483443240976, 226610691390, 11830164347, 0, 0, 0] := by
  decide +kernel

theorem rows10021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10021 = true := by
  decide +kernel

theorem tot10021 : totK PD2M8K2 D2M8K2.t10021 = [0, 37745533432, 285865883798, 395514665488, 178434195226, 21400436502, 0, 0] := by
  decide +kernel

theorem rows10022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10022 = true := by
  decide +kernel

theorem tot10022 : totK PD2M8K2 D2M8K2.t10022 = [0, 0, 194699283366, 488848761703, 212716582869, 7994456143, 0, 0] := by
  decide +kernel

theorem rows10023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10023 = true := by
  decide +kernel

theorem tot10023 : totK PD2M8K2 D2M8K2.t10023 = [0, 51340655322, 251648819406, 402184817711, 182768198617, 8214505460, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
