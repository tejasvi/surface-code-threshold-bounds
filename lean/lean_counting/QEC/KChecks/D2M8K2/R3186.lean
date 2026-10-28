import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12744 = true := by
  decide +kernel

theorem tot12744 : totK PD2M8K2 D2M8K2.t12744 = [0, 0, 65282323133, 314994540814, 390496675671, 101719241529, 2250452236, 0] := by
  decide +kernel

theorem rows12745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12745 = true := by
  decide +kernel

theorem tot12745 : totK PD2M8K2 D2M8K2.t12745 = [0, 0, 182309491354, 456329462352, 265389338465, 27925896374, 0, 0] := by
  decide +kernel

theorem rows12746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12746 = true := by
  decide +kernel

theorem tot12746 : totK PD2M8K2 D2M8K2.t12746 = [0, 0, 170862476745, 466922890247, 242246905571, 9951944660, 0, 0] := by
  decide +kernel

theorem rows12747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12747 = true := by
  decide +kernel

theorem tot12747 : totK PD2M8K2 D2M8K2.t12747 = [0, 0, 0, 274372702384, 478274832501, 130485900897, 4031931762, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
