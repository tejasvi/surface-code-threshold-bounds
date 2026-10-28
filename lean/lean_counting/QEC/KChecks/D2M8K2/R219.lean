import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t876 = true := by
  decide +kernel

theorem tot876 : totK PD2M8K2 D2M8K2.t876 = [0, 51897176554, 348330419707, 459272826858, 54897855790, 0, 0, 0] := by
  decide +kernel

theorem rows877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t877 = true := by
  decide +kernel

theorem tot877 : totK PD2M8K2 D2M8K2.t877 = [0, 181565958109, 447521928351, 257859083307, 27401769793, 0, 0, 0] := by
  decide +kernel

theorem rows878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t878 = true := by
  decide +kernel

theorem tot878 : totK PD2M8K2 D2M8K2.t878 = [0, 154634529979, 464716001028, 272700241624, 16503281760, 0, 0, 0] := by
  decide +kernel

theorem rows879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t879 = true := by
  decide +kernel

theorem tot879 : totK PD2M8K2 D2M8K2.t879 = [0, 0, 190639326660, 453443345605, 236942702197, 20729648156, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
