import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5788 = true := by
  decide +kernel

theorem tot5788 : totK PD2M8K2 D2M8K2.t5788 = [171196667555, 462081682484, 244506794367, 16963313487, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5789 = true := by
  decide +kernel

theorem tot5789 : totK PD2M8K2 D2M8K2.t5789 = [0, 218570990405, 489109268450, 170437517981, 8354962430, 0, 0, 0] := by
  decide +kernel

theorem rows5790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5790 = true := by
  decide +kernel

theorem tot5790 : totK PD2M8K2 D2M8K2.t5790 = [64883141726, 308892605894, 388404628581, 101663324521, 3476815345, 0, 0, 0] := by
  decide +kernel

theorem rows5791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5791 = true := by
  decide +kernel

theorem tot5791 : totK PD2M8K2 D2M8K2.t5791 = [176680345251, 455888599114, 267491888827, 28056223255, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
