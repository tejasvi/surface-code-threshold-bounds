import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4624 = true := by
  decide +kernel

theorem tot4624 : totK PD2M8K2 D2M8K2.t4624 = [0, 0, 0, 229939990606, 477267880462, 185600119801, 10941248138, 0] := by
  decide +kernel

theorem rows4625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4625 = true := by
  decide +kernel

theorem tot4625 : totK PD2M8K2 D2M8K2.t4625 = [0, 0, 0, 235848706578, 475015926035, 186693607736, 6725739876, 0] := by
  decide +kernel

theorem rows4626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4626 = true := by
  decide +kernel

theorem tot4626 : totK PD2M8K2 D2M8K2.t4626 = [0, 0, 0, 205589903330, 468962785494, 193496174705, 10901505393, 0] := by
  decide +kernel

theorem rows4627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4627 = true := by
  decide +kernel

theorem tot4627 : totK PD2M8K2 D2M8K2.t4627 = [0, 0, 0, 189656346124, 467083555489, 211011299237, 12370590376, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
