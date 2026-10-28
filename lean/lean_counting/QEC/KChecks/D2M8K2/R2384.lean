import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9536 = true := by
  decide +kernel

theorem tot9536 : totK PD2M8K2 D2M8K2.t9536 = [0, 0, 202463780985, 462478420611, 184838323167, 11853261585, 0, 0] := by
  decide +kernel

theorem rows9537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9537 = true := by
  decide +kernel

theorem tot9537 : totK PD2M8K2 D2M8K2.t9537 = [0, 172292400984, 462182784655, 247278336816, 21315883420, 0, 0, 0] := by
  decide +kernel

theorem rows9538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9538 = true := by
  decide +kernel

theorem tot9538 : totK PD2M8K2 D2M8K2.t9538 = [0, 197391466565, 472784105206, 225794818087, 14332099299, 0, 0, 0] := by
  decide +kernel

theorem rows9539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9539 = true := by
  decide +kernel

theorem tot9539 : totK PD2M8K2 D2M8K2.t9539 = [133497357572, 343000338522, 274410104080, 134199454435, 13566920432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
