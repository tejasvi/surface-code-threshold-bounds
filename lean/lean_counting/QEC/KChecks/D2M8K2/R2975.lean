import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11900 = true := by
  decide +kernel

theorem tot11900 : totK PD2M8K2 D2M8K2.t11900 = [153428177587, 457700627368, 272139967672, 20285505005, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11901 = true := by
  decide +kernel

theorem tot11901 : totK PD2M8K2 D2M8K2.t11901 = [0, 259593891851, 491585119684, 150517544850, 8390071763, 0, 0, 0] := by
  decide +kernel

theorem rows11902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11902 = true := by
  decide +kernel

theorem tot11902 : totK PD2M8K2 D2M8K2.t11902 = [161106450562, 386862495053, 273363859244, 77418519209, 3443453901, 0, 0, 0] := by
  decide +kernel

theorem rows11903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11903 = true := by
  decide +kernel

theorem tot11903 : totK PD2M8K2 D2M8K2.t11903 = [162945202539, 439630665462, 288511795238, 30618259789, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
