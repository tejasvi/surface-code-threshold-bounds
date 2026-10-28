import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14000 = true := by
  decide +kernel

theorem tot14000 : totK PD2M8K2 D2M8K2.t14000 = [0, 18294181168, 187012627078, 453121924081, 216827081494, 9288887403, 0, 0] := by
  decide +kernel

theorem rows14001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14001 = true := by
  decide +kernel

theorem tot14001 : totK PD2M8K2 D2M8K2.t14001 = [0, 190035439922, 464653266327, 240911762802, 23167094600, 0, 0, 0] := by
  decide +kernel

theorem rows14002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14002 = true := by
  decide +kernel

theorem tot14002 : totK PD2M8K2 D2M8K2.t14002 = [0, 185249574861, 473077732285, 225712606875, 12340935526, 0, 0, 0] := by
  decide +kernel

theorem rows14003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14003 = true := by
  decide +kernel

theorem tot14003 : totK PD2M8K2 D2M8K2.t14003 = [0, 40763117267, 324069591133, 434412068792, 92088317431, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
