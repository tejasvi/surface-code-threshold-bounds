import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13508 = true := by
  decide +kernel

theorem tot13508 : totK PD2M8K2 D2M8K2.t13508 = [177347542369, 467991555371, 225307370423, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13509 = true := by
  decide +kernel

theorem tot13509 : totK PD2M8K2 D2M8K2.t13509 = [0, 286063679300, 499060251633, 105459650328, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows13510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13510 = true := by
  decide +kernel

theorem tot13510 : totK PD2M8K2 D2M8K2.t13510 = [0, 192771436354, 465905023386, 188510467525, 11885407614, 0, 0, 0] := by
  decide +kernel

theorem rows13511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13511 = true := by
  decide +kernel

theorem tot13511 : totK PD2M8K2 D2M8K2.t13511 = [190466380195, 449599022523, 240322452008, 25733106392, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
