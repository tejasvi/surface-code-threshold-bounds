import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9756 = true := by
  decide +kernel

theorem tot9756 : totK PD2M8K2 D2M8K2.t9756 = [0, 0, 155094646364, 465227397139, 248379998368, 14002521971, 0, 0] := by
  decide +kernel

theorem rows9757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9757 = true := by
  decide +kernel

theorem tot9757 : totK PD2M8K2 D2M8K2.t9757 = [0, 0, 0, 267384476224, 468303396541, 106313157482, 2119229067, 0] := by
  decide +kernel

theorem rows9758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9758 = true := by
  decide +kernel

theorem tot9758 : totK PD2M8K2 D2M8K2.t9758 = [0, 0, 112783974867, 400009903140, 301017718672, 58587879051, 2719014351, 0] := by
  decide +kernel

theorem rows9759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9759 = true := by
  decide +kernel

theorem tot9759 : totK PD2M8K2 D2M8K2.t9759 = [0, 0, 180730119275, 455787114923, 246541279965, 21322691856, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
