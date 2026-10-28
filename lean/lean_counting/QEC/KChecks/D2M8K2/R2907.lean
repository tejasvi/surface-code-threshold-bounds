import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11628 = true := by
  decide +kernel

theorem tot11628 : totK PD2M8K2 D2M8K2.t11628 = [0, 0, 273547207417, 503556272606, 127954781001, 1238673482, 0, 0] := by
  decide +kernel

theorem rows11629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11629 = true := by
  decide +kernel

theorem tot11629 : totK PD2M8K2 D2M8K2.t11629 = [90523122812, 221364108128, 166714051959, 255185230039, 135972968760, 8063697217, 0, 0] := by
  decide +kernel

theorem rows11630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11630 = true := by
  decide +kernel

theorem tot11630 : totK PD2M8K2 D2M8K2.t11630 = [192747307971, 453985583769, 224338851392, 17088807522, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11631 = true := by
  decide +kernel

theorem tot11631 : totK PD2M8K2 D2M8K2.t11631 = [125956823163, 432011647890, 293751905573, 24745373861, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
