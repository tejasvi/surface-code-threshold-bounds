import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t576 = true := by
  decide +kernel

theorem tot576 : totK PD2M8K2 D2M8K2.t576 = [0, 178584235395, 459543305792, 249993830315, 22182623379, 0, 0, 0] := by
  decide +kernel

theorem rows577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t577 = true := by
  decide +kernel

theorem tot577 : totK PD2M8K2 D2M8K2.t577 = [0, 160227375603, 456421121964, 263612022893, 18910884877, 0, 0, 0] := by
  decide +kernel

theorem rows578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t578 = true := by
  decide +kernel

theorem tot578 : totK PD2M8K2 D2M8K2.t578 = [0, 0, 261105149607, 510460072642, 120836083486, 1164319620, 0, 0] := by
  decide +kernel

theorem rows579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t579 = true := by
  decide +kernel

theorem tot579 : totK PD2M8K2 D2M8K2.t579 = [0, 81955388392, 323070867661, 370922624334, 112863001673, 7274065870, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
