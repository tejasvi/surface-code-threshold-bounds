import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13696 = true := by
  decide +kernel

theorem tot13696 : totK PD2M8K2 D2M8K2.t13696 = [0, 0, 167320524194, 462239623965, 211803217781, 14738434662, 0, 0] := by
  decide +kernel

theorem rows13697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13697 = true := by
  decide +kernel

theorem tot13697 : totK PD2M8K2 D2M8K2.t13697 = [0, 0, 243031635074, 487890556905, 156323154518, 7414397321, 0, 0] := by
  decide +kernel

theorem rows13698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13698 = true := by
  decide +kernel

theorem tot13698 : totK PD2M8K2 D2M8K2.t13698 = [0, 0, 167389147750, 468095848080, 205896008859, 13266036910, 0, 0] := by
  decide +kernel

theorem rows13699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13699 = true := by
  decide +kernel

theorem tot13699 : totK PD2M8K2 D2M8K2.t13699 = [0, 0, 218910777970, 473578995093, 165515378695, 8939935548, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
