import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1632 = true := by
  decide +kernel

theorem tot1632 : totK PD2M8K2 D2M8K2.t1632 = [0, 0, 192094255965, 469119075087, 214925805845, 12370590376, 0, 0] := by
  decide +kernel

theorem rows1633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1633 = true := by
  decide +kernel

theorem tot1633 : totK PD2M8K2 D2M8K2.t1633 = [0, 0, 181277656593, 477666990272, 205730669756, 6780884142, 0, 0] := by
  decide +kernel

theorem rows1634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1634 = true := by
  decide +kernel

theorem tot1634 : totK PD2M8K2 D2M8K2.t1634 = [0, 0, 178976943830, 474093398319, 228927880182, 11029064239, 0, 0] := by
  decide +kernel

theorem rows1635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1635 = true := by
  decide +kernel

theorem tot1635 : totK PD2M8K2 D2M8K2.t1635 = [0, 0, 208066931647, 468225606191, 193462555922, 7902352020, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
