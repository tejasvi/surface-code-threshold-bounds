import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t328 = true := by
  decide +kernel

theorem tot328 : totK PD2M8K2 D2M8K2.t328 = [176732270819, 466466750667, 260119362212, 23022408170, 0, 0, 0, 0] := by
  decide +kernel

theorem rows329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t329 = true := by
  decide +kernel

theorem tot329 : totK PD2M8K2 D2M8K2.t329 = [161146281423, 447723608826, 273562668721, 23828078599, 0, 0, 0, 0] := by
  decide +kernel

theorem rows330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t330 = true := by
  decide +kernel

theorem tot330 : totK PD2M8K2 D2M8K2.t330 = [0, 243690565707, 500622981909, 151052875488, 2300468944, 0, 0, 0] := by
  decide +kernel

theorem rows331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t331 = true := by
  decide +kernel

theorem tot331 : totK PD2M8K2 D2M8K2.t331 = [0, 180477108234, 449868409334, 235758957888, 19693502143, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
