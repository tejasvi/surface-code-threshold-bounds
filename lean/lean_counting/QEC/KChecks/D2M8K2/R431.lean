import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1724 = true := by
  decide +kernel

theorem tot1724 : totK PD2M8K2 D2M8K2.t1724 = [0, 0, 0, 283987737754, 485306559537, 111527723780, 3699256714, 0] := by
  decide +kernel

theorem rows1725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1725 = true := by
  decide +kernel

theorem tot1725 : totK PD2M8K2 D2M8K2.t1725 = [0, 0, 159868807160, 381438396747, 233038148704, 83999716475, 8752647282, 0] := by
  decide +kernel

theorem rows1726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1726 = true := by
  decide +kernel

theorem tot1726 : totK PD2M8K2 D2M8K2.t1726 = [0, 0, 176188271610, 455771959706, 238713708068, 14959531823, 0, 0] := by
  decide +kernel

theorem rows1727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1727 = true := by
  decide +kernel

theorem tot1727 : totK PD2M8K2 D2M8K2.t1727 = [0, 0, 81499482564, 328458597965, 382946371110, 89746599679, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
