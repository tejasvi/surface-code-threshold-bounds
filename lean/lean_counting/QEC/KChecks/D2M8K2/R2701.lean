import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10804 = true := by
  decide +kernel

theorem tot10804 : totK PD2M8K2 D2M8K2.t10804 = [0, 142535875563, 354583812238, 297342193644, 118140997593, 6804944647, 0, 0] := by
  decide +kernel

theorem rows10805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10805 = true := by
  decide +kernel

theorem tot10805 : totK PD2M8K2 D2M8K2.t10805 = [0, 155772243557, 461461172648, 275621154557, 19044872297, 0, 0, 0] := by
  decide +kernel

theorem rows10806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10806 = true := by
  decide +kernel

theorem tot10806 : totK PD2M8K2 D2M8K2.t10806 = [0, 87333051614, 355719980789, 386510947307, 75772975255, 1163840124, 0, 0] := by
  decide +kernel

theorem rows10807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10807 = true := by
  decide +kernel

theorem tot10807 : totK PD2M8K2 D2M8K2.t10807 = [0, 0, 221956690650, 485725777263, 172560757091, 8315984947, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
