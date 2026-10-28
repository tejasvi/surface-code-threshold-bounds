import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12784 = true := by
  decide +kernel

theorem tot12784 : totK PD2M8K2 D2M8K2.t12784 = [0, 0, 182340060862, 461598034034, 247805479174, 17998322742, 0, 0] := by
  decide +kernel

theorem rows12785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12785 = true := by
  decide +kernel

theorem tot12785 : totK PD2M8K2 D2M8K2.t12785 = [0, 0, 211164478470, 483661444570, 196728093308, 11003799003, 0, 0] := by
  decide +kernel

theorem rows12786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12786 = true := by
  decide +kernel

theorem tot12786 : totK PD2M8K2 D2M8K2.t12786 = [0, 0, 19168557488, 356035865159, 422668876425, 68717744062, 1021600638, 0] := by
  decide +kernel

theorem rows12787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12787 = true := by
  decide +kernel

theorem tot12787 : totK PD2M8K2 D2M8K2.t12787 = [0, 0, 83979965916, 340558434369, 346538067244, 81653061396, 3552795014, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
