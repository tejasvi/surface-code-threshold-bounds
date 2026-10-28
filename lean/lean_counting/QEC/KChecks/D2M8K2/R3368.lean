import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13472 = true := by
  decide +kernel

theorem tot13472 : totK PD2M8K2 D2M8K2.t13472 = [0, 0, 0, 280041086034, 497324975907, 97169826129, 1326647619, 0] := by
  decide +kernel

theorem rows13473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13473 = true := by
  decide +kernel

theorem tot13473 : totK PD2M8K2 D2M8K2.t13473 = [0, 0, 144171881247, 402014382298, 324306599016, 35907030481, 0, 0] := by
  decide +kernel

theorem rows13474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13474 = true := by
  decide +kernel

theorem tot13474 : totK PD2M8K2 D2M8K2.t13474 = [0, 0, 189337005369, 448835128363, 229212227588, 16903437389, 0, 0] := by
  decide +kernel

theorem rows13475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13475 = true := by
  decide +kernel

theorem tot13475 : totK PD2M8K2 D2M8K2.t13475 = [0, 0, 87214553039, 379485313464, 343648600257, 83663335705, 10368174490, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
