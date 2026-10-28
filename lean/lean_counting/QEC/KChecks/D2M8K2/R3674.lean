import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14696 = true := by
  decide +kernel

theorem tot14696 : totK PD2M8K2 D2M8K2.t14696 = [0, 176988785702, 430646911903, 268246236307, 29628510608, 0, 0, 0] := by
  decide +kernel

theorem rows14697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14697 = true := by
  decide +kernel

theorem tot14697 : totK PD2M8K2 D2M8K2.t14697 = [0, 163126882741, 480194443289, 256082048553, 13916467904, 0, 0, 0] := by
  decide +kernel

theorem rows14698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14698 = true := by
  decide +kernel

theorem tot14698 : totK PD2M8K2 D2M8K2.t14698 = [0, 0, 278911419285, 513261044188, 102585523445, 1096505104, 0, 0] := by
  decide +kernel

theorem rows14699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14699 = true := by
  decide +kernel

theorem tot14699 : totK PD2M8K2 D2M8K2.t14699 = [0, 0, 211096983004, 490930436083, 173115621598, 5253830308, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
