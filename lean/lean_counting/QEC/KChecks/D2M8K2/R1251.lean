import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5004 = true := by
  decide +kernel

theorem tot5004 : totK PD2M8K2 D2M8K2.t5004 = [0, 92963099499, 385299442174, 400842289772, 46463885183, 0, 0, 0] := by
  decide +kernel

theorem rows5005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5005 = true := by
  decide +kernel

theorem tot5005 : totK PD2M8K2 D2M8K2.t5005 = [0, 192023635949, 462926147761, 244676644237, 20043948722, 0, 0, 0] := by
  decide +kernel

theorem rows5006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5006 = true := by
  decide +kernel

theorem tot5006 : totK PD2M8K2 D2M8K2.t5006 = [0, 135022454494, 439360033040, 306076661552, 34178261441, 0, 0, 0] := by
  decide +kernel

theorem rows5007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5007 = true := by
  decide +kernel

theorem tot5007 : totK PD2M8K2 D2M8K2.t5007 = [0, 0, 173416578345, 449938616554, 259763168682, 25357676561, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
