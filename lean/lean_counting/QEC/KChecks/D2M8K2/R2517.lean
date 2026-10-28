import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10068 = true := by
  decide +kernel

theorem tot10068 : totK PD2M8K2 D2M8K2.t10068 = [0, 0, 207703008313, 479817942617, 182537241678, 11885407614, 0, 0] := by
  decide +kernel

theorem rows10069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10069 = true := by
  decide +kernel

theorem tot10069 : totK PD2M8K2 D2M8K2.t10069 = [0, 189698210248, 451925169373, 239815611328, 27579973432, 0, 0, 0] := by
  decide +kernel

theorem rows10070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10070 = true := by
  decide +kernel

theorem tot10070 : totK PD2M8K2 D2M8K2.t10070 = [0, 206381301797, 461635878708, 214231195854, 15876609558, 0, 0, 0] := by
  decide +kernel

theorem rows10071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10071 = true := by
  decide +kernel

theorem tot10071 : totK PD2M8K2 D2M8K2.t10071 = [0, 0, 368304905017, 476913658516, 57421320199, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
