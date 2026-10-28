import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12608 = true := by
  decide +kernel

theorem tot12608 : totK PD2M8K2 D2M8K2.t12608 = [0, 28464616062, 277500017136, 469693318243, 125369374221, 4234510686, 0, 0] := by
  decide +kernel

theorem rows12609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12609 = true := by
  decide +kernel

theorem tot12609 : totK PD2M8K2 D2M8K2.t12609 = [0, 194717066432, 463940282662, 227305176831, 20028342185, 0, 0, 0] := by
  decide +kernel

theorem rows12610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12610 = true := by
  decide +kernel

theorem tot12610 : totK PD2M8K2 D2M8K2.t12610 = [0, 174584958464, 468352184036, 238681315073, 13758549984, 0, 0, 0] := by
  decide +kernel

theorem rows12611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12611 = true := by
  decide +kernel

theorem tot12611 : totK PD2M8K2 D2M8K2.t12611 = [0, 0, 284014590270, 496577241516, 112102993865, 1198073392, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
