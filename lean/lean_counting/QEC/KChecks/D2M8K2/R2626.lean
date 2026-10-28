import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10504 = true := by
  decide +kernel

theorem tot10504 : totK PD2M8K2 D2M8K2.t10504 = [0, 174405477553, 453117366278, 241568248906, 13821495057, 0, 0, 0] := by
  decide +kernel

theorem rows10505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10505 = true := by
  decide +kernel

theorem tot10505 : totK PD2M8K2 D2M8K2.t10505 = [0, 65009544155, 322982181898, 416219169593, 84420568135, 1164319620, 0, 0] := by
  decide +kernel

theorem rows10506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10506 = true := by
  decide +kernel

theorem tot10506 : totK PD2M8K2 D2M8K2.t10506 = [0, 0, 199668438104, 468950618027, 177117222667, 11885407614, 0, 0] := by
  decide +kernel

theorem rows10507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10507 = true := by
  decide +kernel

theorem tot10507 : totK PD2M8K2 D2M8K2.t10507 = [0, 174553003194, 448204044882, 266600574323, 27661525797, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
