import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1384 = true := by
  decide +kernel

theorem tot1384 : totK PD2M8K2 D2M8K2.t1384 = [0, 156315449797, 445869707251, 282515683726, 29934877963, 0, 0, 0] := by
  decide +kernel

theorem rows1385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1385 = true := by
  decide +kernel

theorem tot1385 : totK PD2M8K2 D2M8K2.t1385 = [0, 213879377620, 484809573599, 203574012151, 10346224807, 0, 0, 0] := by
  decide +kernel

theorem rows1386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1386 = true := by
  decide +kernel

theorem tot1386 : totK PD2M8K2 D2M8K2.t1386 = [0, 0, 259440659210, 442759644598, 194037792503, 21400436502, 0, 0] := by
  decide +kernel

theorem rows1387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1387 = true := by
  decide +kernel

theorem tot1387 : totK PD2M8K2 D2M8K2.t1387 = [0, 0, 184336309020, 486130002206, 209634338468, 7908366594, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
