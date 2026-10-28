import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2152 = true := by
  decide +kernel

theorem tot2152 : totK PD2M8K2 D2M8K2.t2152 = [0, 171687669588, 449943293606, 259579486751, 20212664859, 0, 0, 0] := by
  decide +kernel

theorem rows2153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2153 = true := by
  decide +kernel

theorem tot2153 : totK PD2M8K2 D2M8K2.t2153 = [0, 91681601894, 361660582126, 361798359046, 73735200356, 1096156699, 0, 0] := by
  decide +kernel

theorem rows2154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2154 = true := by
  decide +kernel

theorem tot2154 : totK PD2M8K2 D2M8K2.t2154 = [0, 0, 310392135166, 511622652596, 88181647287, 1067382613, 0, 0] := by
  decide +kernel

theorem rows2155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2155 = true := by
  decide +kernel

theorem tot2155 : totK PD2M8K2 D2M8K2.t2155 = [0, 0, 180580466582, 464108939400, 252562869346, 24889893218, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
