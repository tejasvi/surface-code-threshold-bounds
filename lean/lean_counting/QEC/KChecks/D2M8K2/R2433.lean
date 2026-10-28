import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9732 = true := by
  decide +kernel

theorem tot9732 : totK PD2M8K2 D2M8K2.t9732 = [0, 3757117624, 157613124795, 484855629410, 240267226903, 9251062635, 0, 0] := by
  decide +kernel

theorem rows9733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9733 = true := by
  decide +kernel

theorem tot9733 : totK PD2M8K2 D2M8K2.t9733 = [0, 184230869288, 446329399665, 241631424485, 22628876341, 0, 0, 0] := by
  decide +kernel

theorem rows9734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9734 = true := by
  decide +kernel

theorem tot9734 : totK PD2M8K2 D2M8K2.t9734 = [0, 214328113740, 476809597773, 195172049211, 9376704425, 0, 0, 0] := by
  decide +kernel

theorem rows9735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9735 = true := by
  decide +kernel

theorem tot9735 : totK PD2M8K2 D2M8K2.t9735 = [0, 0, 297783968418, 490913956437, 94860803258, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
