import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10760 = true := by
  decide +kernel

theorem tot10760 : totK PD2M8K2 D2M8K2.t10760 = [0, 0, 0, 255050010734, 484161626641, 156695283413, 5781885207, 0] := by
  decide +kernel

theorem rows10761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10761 = true := by
  decide +kernel

theorem tot10761 : totK PD2M8K2 D2M8K2.t10761 = [0, 0, 0, 282359571867, 472021038877, 125055701032, 2721632452, 0] := by
  decide +kernel

theorem rows10762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10762 = true := by
  decide +kernel

theorem tot10762 : totK PD2M8K2 D2M8K2.t10762 = [0, 0, 0, 219738184589, 472916060425, 162789671063, 7472323711, 0] := by
  decide +kernel

theorem rows10763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10763 = true := by
  decide +kernel

theorem tot10763 : totK PD2M8K2 D2M8K2.t10763 = [0, 0, 0, 204995897744, 483568606121, 182045648390, 10871000096, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
