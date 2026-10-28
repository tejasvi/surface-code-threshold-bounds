import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16032 = true := by
  decide +kernel

theorem tot16032 : totK PD2M8K2 D2M8K2.t16032 = [0, 0, 230418854304, 516168429698, 161378523825, 4171150629, 0, 0] := by
  decide +kernel

theorem rows16033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16033 = true := by
  decide +kernel

theorem tot16033 : totK PD2M8K2 D2M8K2.t16033 = [0, 0, 178767272008, 453552509922, 270904208681, 21163347655, 0, 0] := by
  decide +kernel

theorem rows16034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16034 = true := by
  decide +kernel

theorem tot16034 : totK PD2M8K2 D2M8K2.t16034 = [0, 0, 205283138869, 471243873573, 211867519151, 10620981360, 0, 0] := by
  decide +kernel

theorem rows16035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16035 = true := by
  decide +kernel

theorem tot16035 : totK PD2M8K2 D2M8K2.t16035 = [0, 0, 195132331125, 475789965154, 217970063283, 12748384098, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
