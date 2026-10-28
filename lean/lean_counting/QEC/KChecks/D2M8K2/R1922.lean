import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7688 = true := by
  decide +kernel

theorem tot7688 : totK PD2M8K2 D2M8K2.t7688 = [0, 0, 208764861238, 485079298012, 215412851082, 21987170963, 0, 0] := by
  decide +kernel

theorem rows7689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7689 = true := by
  decide +kernel

theorem tot7689 : totK PD2M8K2 D2M8K2.t7689 = [0, 0, 223267149863, 485866538121, 189646248364, 8689649832, 0, 0] := by
  decide +kernel

theorem rows7690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7690 = true := by
  decide +kernel

theorem tot7690 : totK PD2M8K2 D2M8K2.t7690 = [0, 0, 168317706404, 441333372928, 277302002593, 27391379627, 0, 0] := by
  decide +kernel

theorem rows7691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7691 = true := by
  decide +kernel

theorem tot7691 : totK PD2M8K2 D2M8K2.t7691 = [0, 0, 102067172304, 446584147167, 313053053164, 31841205312, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
