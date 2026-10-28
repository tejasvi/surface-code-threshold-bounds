import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15724 = true := by
  decide +kernel

theorem tot15724 : totK PD2M8K2 D2M8K2.t15724 = [0, 0, 18547827660, 263900757336, 456800340397, 166695229779, 5675387547, 0] := by
  decide +kernel

theorem rows15725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15725 = true := by
  decide +kernel

theorem tot15725 : totK PD2M8K2 D2M8K2.t15725 = [0, 0, 190298276921, 457901313574, 244021867533, 22372773200, 0, 0] := by
  decide +kernel

theorem rows15726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15726 = true := by
  decide +kernel

theorem tot15726 : totK PD2M8K2 D2M8K2.t15726 = [0, 0, 186651385824, 477295434891, 228969047729, 12373752831, 0, 0] := by
  decide +kernel

theorem rows15727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15727 = true := by
  decide +kernel

theorem tot15727 : totK PD2M8K2 D2M8K2.t15727 = [0, 0, 44955820296, 321785815976, 442789968957, 89305842726, 1164319620, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
