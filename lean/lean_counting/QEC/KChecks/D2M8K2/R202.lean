import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t808 = true := by
  decide +kernel

theorem tot808 : totK PD2M8K2 D2M8K2.t808 = [0, 0, 284122795951, 501812191666, 96221727491, 1369150432, 0, 0] := by
  decide +kernel

theorem rows809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t809 = true := by
  decide +kernel

theorem tot809 : totK PD2M8K2 D2M8K2.t809 = [0, 92247437699, 384104635122, 389009947129, 47274651905, 0, 0, 0] := by
  decide +kernel

theorem rows810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t810 = true := by
  decide +kernel

theorem tot810 : totK PD2M8K2 D2M8K2.t810 = [0, 159879405080, 445051638363, 284483221239, 21425421678, 0, 0, 0] := by
  decide +kernel

theorem rows811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t811 = true := by
  decide +kernel

theorem tot811 : totK PD2M8K2 D2M8K2.t811 = [0, 150169159853, 445670484492, 268326719567, 27512644641, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
