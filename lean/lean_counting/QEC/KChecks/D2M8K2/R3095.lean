import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12380 = true := by
  decide +kernel

theorem tot12380 : totK PD2M8K2 D2M8K2.t12380 = [0, 181631387543, 465009207245, 260286116809, 23168844890, 0, 0, 0] := by
  decide +kernel

theorem rows12381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12381 = true := by
  decide +kernel

theorem tot12381 : totK PD2M8K2 D2M8K2.t12381 = [0, 164777486239, 458368541093, 256083721160, 16193159497, 0, 0, 0] := by
  decide +kernel

theorem rows12382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12382 = true := by
  decide +kernel

theorem tot12382 : totK PD2M8K2 D2M8K2.t12382 = [0, 0, 260863937089, 483309150767, 144634687687, 8417083954, 0, 0] := by
  decide +kernel

theorem rows12383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12383 = true := by
  decide +kernel

theorem tot12383 : totK PD2M8K2 D2M8K2.t12383 = [0, 66623131732, 319429442635, 393634422216, 97496059839, 3455941720, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
