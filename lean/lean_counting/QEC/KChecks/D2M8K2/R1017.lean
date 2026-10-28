import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4068 = true := by
  decide +kernel

theorem tot4068 : totK PD2M8K2 D2M8K2.t4068 = [0, 16504979279, 197665335988, 462428811172, 189758404536, 11885407614, 0, 0] := by
  decide +kernel

theorem rows4069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4069 = true := by
  decide +kernel

theorem tot4069 : totK PD2M8K2 D2M8K2.t4069 = [0, 183026296692, 454233067647, 246410844482, 23278879887, 0, 0, 0] := by
  decide +kernel

theorem rows4070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4070 = true := by
  decide +kernel

theorem tot4070 : totK PD2M8K2 D2M8K2.t4070 = [0, 199636437798, 459782814799, 226972619067, 15876609558, 0, 0, 0] := by
  decide +kernel

theorem rows4071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4071 = true := by
  decide +kernel

theorem tot4071 : totK PD2M8K2 D2M8K2.t4071 = [0, 7714136340, 330245534477, 472524010530, 81152471151, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
