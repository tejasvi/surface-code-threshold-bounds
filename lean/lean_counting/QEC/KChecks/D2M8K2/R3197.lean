import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12788 = true := by
  decide +kernel

theorem tot12788 : totK PD2M8K2 D2M8K2.t12788 = [0, 0, 175096358341, 450915038980, 263275644214, 25478622528, 0, 0] := by
  decide +kernel

theorem rows12789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12789 = true := by
  decide +kernel

theorem tot12789 : totK PD2M8K2 D2M8K2.t12789 = [0, 74725294189, 231715077831, 372005289725, 205840974501, 13510166946, 0, 0] := by
  decide +kernel

theorem rows12790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12790 = true := by
  decide +kernel

theorem tot12790 : totK PD2M8K2 D2M8K2.t12790 = [0, 181534183308, 478890759153, 224531136654, 11084674549, 0, 0, 0] := by
  decide +kernel

theorem rows12791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12791 = true := by
  decide +kernel

theorem tot12791 : totK PD2M8K2 D2M8K2.t12791 = [0, 68751926367, 359449186928, 385068925396, 75891525475, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
